use std::fmt::{self, Debug, Display};
use std::iter;
use std::rc::Rc;

use crate::iter::Linearizations;
use crate::relations::{
    EventRelation, PartialOrder, PartialOrderCycleError, Relation, ThreadIndex, TotalOrder,
    TotalOrderUnion,
};
use itertools::Itertools;
use roaring::RoaringBitmap;
use rustc_hash::FxHashMap;

pub type Location = usize;
pub type EventId = u32;

#[derive(Clone, Copy)]
pub struct Event {
    pub location: Location,
    pub event_type: EventType,
}

impl Display for Event {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.event_type, self.location)
    }
}

impl Debug for Event {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, strum::EnumString, strum::Display)]
pub enum EventType {
    #[strum(serialize = "R")]
    Read,
    #[strum(serialize = "W")]
    Write,
}

pub trait Execution {
    fn event(&self, event_id: EventId) -> Event;
    fn num_events(&self) -> usize;
    fn thread_of(&self, event_id: EventId) -> usize;
    fn po(&self, event_id: EventId) -> impl Iterator<Item = EventId>;
    fn rf(&self, event_id: EventId) -> impl Iterator<Item = EventId>;
    fn dob(&self, event_id: EventId) -> impl Iterator<Item = EventId>;
    fn mo(&self, event_id: EventId) -> impl Iterator<Item = EventId>;
    fn inverse_rf(&self, event_id: EventId) -> Option<EventId>;

    fn is_consistent(&self) -> bool {
        self.sc_per_location() && self.external_coherence()
    }

    fn sc_per_location(&self) -> bool {
        acyclic(self.num_events(), |e1| {
            let loc = self.event(e1).location;
            // TODO: We could use the fact that the PO is a total order to
            // reduce the number of edges we need to check. Problem: the last
            // initial write has multiple direct PO successors.
            self.po(e1)
                .chain(self.rf(e1))
                .chain(self.mo(e1))
                .chain(self.fr(e1))
                .filter(move |&e2| self.event(e2).location == loc)
        })
    }

    fn external_coherence(&self) -> bool {
        acyclic(self.num_events(), |e| self.ec(e))
    }

    fn fr(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        self.inverse_rf(event_id)
            .into_iter()
            .flat_map(|w| self.mo(w))
    }

    fn rfe(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        let thread = self.thread_of(event_id);
        self.rf(event_id)
            // External edges go between threads, except if going from the
            // special initial writes thread
            .filter(move |&e2| thread == 0 || self.thread_of(e2) != thread)
    }

    fn moe(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        let thread = self.thread_of(event_id);
        self.mo(event_id)
            // External edges go between threads, except if going from the
            // special initial writes thread
            .filter(move |&e2| thread == 0 || self.thread_of(e2) != thread)
    }

    fn fre(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        let thread = self.thread_of(event_id);
        self.fr(event_id)
            // External edges go between threads, except if going from the
            // special initial writes thread
            .filter(move |&e2| thread == 0 || self.thread_of(e2) != thread)
    }

    fn ec(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        self.dob(event_id)
            .chain(self.rfe(event_id))
            .chain(self.moe(event_id))
            .chain(self.fre(event_id))
    }
}

pub trait CheckableExecution: Execution {
    fn is_totally_consistent(&mut self) -> Option<TotalOrderUnion>;
    fn linearizations_checked(&self) -> usize;
}

fn acyclic<I>(num_events: usize, successors: impl Fn(EventId) -> I) -> bool
where
    I: IntoIterator<Item = EventId>,
{
    let mut visited = RoaringBitmap::new();
    let mut visiting = RoaringBitmap::new();
    let mut stack = vec![];
    for event_id in 0..num_events as EventId {
        if visited.contains(event_id) {
            continue;
        }

        stack.push((event_id, false));
        while let Some((event_id, backtracking)) = stack.pop() {
            if backtracking {
                visited.insert(event_id);
                visiting.remove(event_id);
                continue;
            }

            visiting.insert(event_id);
            stack.push((event_id, true));
            for succ in successors(event_id) {
                if visiting.contains(succ) {
                    return false;
                } else if visited.contains(succ) {
                    continue;
                }
                stack.push((succ, false));
            }
        }
    }
    true
}

/// A (partial) exection graph.
pub struct NaiveExecution {
    num_locations: usize,
    /// The events in the execution, in program order.
    events: Vec<Event>,
    thread_starts: Vec<EventId>,
    event_threads: Vec<usize>,
    rf: EventRelation,
    inverse_rf: FxHashMap<EventId, EventId>,
    dob: EventRelation,
    mo: TotalOrderUnion,
    linearizations_checked: usize,
}

impl NaiveExecution {
    pub fn new(threads: &[Vec<Event>], num_locations: usize) -> Self {
        // Initial writes
        let mut events: Vec<_> = (0..num_locations)
            .map(|loc| Event {
                location: loc,
                event_type: EventType::Write,
            })
            .collect();
        // Rest of the events
        events.extend(threads.iter().flatten().copied());

        // Initial writes get their owwn thread
        let mut thread_starts = vec![0];
        thread_starts.extend(
            threads
                .iter()
                .scan(num_locations as EventId, |acc, thread| {
                    let start = *acc;
                    *acc += thread.len() as EventId;
                    Some(start)
                }),
        );

        let mut event_threads = Vec::with_capacity(events.len());
        event_threads.extend(iter::repeat(0).take(num_locations));
        event_threads.extend(
            threads
                .iter()
                .enumerate()
                .flat_map(|(thread, events)| iter::repeat(thread + 1).take(events.len())),
        );

        Self {
            num_locations,
            events,
            thread_starts,
            event_threads,
            rf: EventRelation::default(),
            inverse_rf: FxHashMap::default(),
            dob: EventRelation::default(),
            mo: TotalOrderUnion::default(),
            linearizations_checked: 0,
        }
    }

    pub fn add_rf(&mut self, w: EventId, r: EventId) {
        self.rf.entry(w).or_default().insert(r);
        self.inverse_rf.insert(r, w);
    }

    pub fn add_dob(&mut self, e1: EventId, e2: EventId) {
        self.dob.entry(e1).or_default().insert(e2);
    }

    pub fn to_event_id(&self, (thread, idx): ThreadIndex) -> EventId {
        self.thread_starts[thread] + idx as EventId
    }

    pub fn close_rf(&mut self) {
        for event_id in 0..self.num_events() as EventId {
            let event = self.event(event_id);
            if event.event_type != EventType::Read {
                continue;
            }
            let initial_write = event.location as EventId;
            self.inverse_rf.entry(event_id).or_insert_with(|| {
                self.rf.entry(initial_write).or_default().insert(event_id);
                initial_write
            });
        }
    }

    fn thread_end(&self, thread: usize) -> EventId {
        self.thread_starts
            .get(thread + 1)
            .copied()
            .unwrap_or(self.events.len() as EventId)
    }

    pub fn with_sc(mut self) -> Self {
        for event in 0..self.num_events() as EventId {
            for succ in self.po(event).collect_vec() {
                self.add_dob(event, succ);
            }
        }
        self
    }

    pub fn with_tso(mut self) -> Self {
        for event in 0..self.num_events() as EventId {
            for succ in self.po(event).collect_vec() {
                if self.event(event).event_type == EventType::Write
                    && self.event(succ).event_type == EventType::Read
                {
                    continue;
                }
                self.add_dob(event, succ);
            }
        }
        self
    }

    pub fn with_relaxed(self) -> Self {
        self
    }
}

impl Execution for NaiveExecution {
    fn event(&self, event_id: EventId) -> Event {
        self.events[event_id as usize]
    }

    fn num_events(&self) -> usize {
        self.events.len()
    }

    fn thread_of(&self, event_id: EventId) -> usize {
        self.event_threads[event_id as usize]
    }

    fn po(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        if event_id < self.num_locations as EventId {
            return event_id + 1..self.events.len() as EventId;
        }

        let thread = self.thread_of(event_id);
        let next_thread_start = self
            .thread_starts
            .get(thread + 1)
            .copied()
            .unwrap_or_else(|| self.events.len() as EventId);

        event_id + 1..next_thread_start
    }

    fn rf(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        self.rf.get(&event_id).into_iter().flatten()
    }

    fn dob(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        self.dob.get(&event_id).into_iter().flatten()
    }

    fn mo(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        self.mo.successors(event_id, &self.events)
    }

    fn inverse_rf(&self, event_id: EventId) -> Option<EventId> {
        self.inverse_rf.get(&event_id).copied()
    }
}

impl CheckableExecution for NaiveExecution {
    fn is_totally_consistent(&mut self) -> Option<TotalOrderUnion> {
        // Generate all possible total orders for each location
        // TODO: We could check SC per location for each total order only once, instead
        // of checking it repeatedly for each combination of total orders.
        let mut mos = vec![];
        for loc in 0..self.num_locations {
            let mut writes = vec![vec![]; self.thread_starts.len()];
            let mut thread = 0;
            for w in self
                .events
                .iter()
                .enumerate()
                .filter(|(_, e)| e.location == loc && e.event_type == EventType::Write)
                .map(|(i, _)| i as EventId)
            {
                if w >= self.thread_end(thread) {
                    thread += 1;
                }
                writes[thread].push(w);
            }

            let permutations = writes
                .into_iter()
                .linearizations()
                .map(TotalOrder::new)
                .map(Rc::new);
            mos.push(permutations);
        }

        // Try all possible combinations of total orders
        for mo in mos.into_iter().multi_cartesian_product() {
            self.linearizations_checked += 1;
            self.mo = TotalOrderUnion { orders: mo };
            if self.is_consistent() {
                return Some(self.mo.clone());
            }
        }

        None
    }

    fn linearizations_checked(&self) -> usize {
        self.linearizations_checked
    }
}

pub struct SaturatingExecution {
    exec: NaiveExecution,
    reads_per_location: Vec<Vec<EventId>>,
    writes_per_location: Vec<Vec<EventId>>,
    writes_per_thread_per_location: Vec<Vec<Vec<EventId>>>,
    scpl: Scpl,
}

impl SaturatingExecution {
    fn reachable_ec(&self, from: EventId) -> impl Iterator<Item = EventId> + '_ {
        (|e| self.ec(e)).transitive(from, &self.exec.events)
    }

    pub fn edges_inserted(&self) -> usize {
        self.scpl.inserted
    }
}

impl From<NaiveExecution> for SaturatingExecution {
    fn from(exec: NaiveExecution) -> Self {
        let mut reads_per_location = vec![vec![]; exec.num_locations];
        let mut writes_per_location = vec![vec![]; exec.num_locations];
        let mut writes_per_thread_per_location =
            vec![vec![vec![]; exec.thread_starts.len()]; exec.num_locations];
        let mut events_per_thread_per_location =
            vec![vec![vec![]; exec.thread_starts.len()]; exec.num_locations];
        for (event_id, event) in exec.events.iter().enumerate() {
            let event_id = event_id as EventId;
            events_per_thread_per_location[event.location][exec.thread_of(event_id)].push(event_id);
            match event.event_type {
                EventType::Read => reads_per_location[event.location].push(event_id),
                EventType::Write => {
                    writes_per_location[event.location].push(event_id);
                    writes_per_thread_per_location[event.location][exec.thread_of(event_id)]
                        .push(event_id);
                }
            }
        }
        let scpl = Scpl::new(events_per_thread_per_location);

        Self {
            exec,
            reads_per_location,
            writes_per_location,
            writes_per_thread_per_location,
            scpl,
        }
    }
}

impl Execution for SaturatingExecution {
    fn event(&self, event_id: EventId) -> Event {
        self.exec.event(event_id)
    }

    fn num_events(&self) -> usize {
        self.exec.num_events()
    }

    fn thread_of(&self, event_id: EventId) -> usize {
        self.exec.thread_of(event_id)
    }

    fn po(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        self.exec.po(event_id)
    }

    fn rf(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        self.exec.rf(event_id)
    }

    fn dob(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        self.exec.dob(event_id)
    }

    fn mo(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        let event = self.event(event_id);
        let loc = event.location;
        (event.event_type == EventType::Write)
            .then(|| {
                self.writes_per_thread_per_location[loc]
                    .iter()
                    .enumerate()
                    .flat_map(move |(th, writes)| {
                        let first_event = self
                            .scpl
                            .first_reachable(loc, event_id, th)
                            .unwrap_or(EventId::MAX);
                        let first_write = writes.binary_search(&first_event).unwrap_or_else(|w| w);
                        writes[first_write..].iter().copied()
                    })
                    .filter(move |&w| w != event_id)
            })
            .into_iter()
            .flatten()
    }

    fn moe(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        let event = self.event(event_id);
        let loc = event.location;
        let thread = self.thread_of(event_id);
        (event.event_type == EventType::Write)
            .then(|| {
                self.writes_per_thread_per_location[loc]
                    .iter()
                    .enumerate()
                    .filter(move |(th, _)| *th != thread)
                    .flat_map(move |(th, writes)| {
                        let first_event = self
                            .scpl
                            .first_reachable(loc, event_id, th)
                            .unwrap_or(EventId::MAX);
                        let first_write = writes.binary_search(&first_event).unwrap_or_else(|w| w);
                        writes[first_write..].iter().copied()
                    })
                    .filter(move |&w| w != event_id)
            })
            .into_iter()
            .flatten()
    }

    fn inverse_rf(&self, event_id: EventId) -> Option<EventId> {
        self.exec.inverse_rf(event_id)
    }
}

impl CheckableExecution for SaturatingExecution {
    fn is_totally_consistent(&mut self) -> Option<TotalOrderUnion> {
        for (loc, r) in self
            .reads_per_location
            .iter()
            .enumerate()
            .flat_map(|(l, rs)| rs.iter().map(move |&r| (l, r)))
        {
            let w = self.inverse_rf(r).expect("r should have write");
            self.scpl.insert(loc, w, r).ok()?;
        }

        // Saturate first
        let mut changed = true;
        while changed {
            changed = false;

            for loc in 0..self.reads_per_location.len() {
                for &w_1 in &self.writes_per_location[loc] {
                    for &r in &self.reads_per_location[loc] {
                        // Find w_x [SCPL] r_x [rf^-1] w'_x
                        let w_2 = self.inverse_rf(r).expect("r_1 should have write");
                        if w_1 == w_2 || !self.scpl.query(loc, w_1, r) {
                            continue;
                        }
                        changed |= self.scpl.insert(loc, w_1, w_2).ok()?;
                    }
                }

                let mut inserts = vec![];
                for &w_1 in &self.writes_per_location[loc] {
                    let event_1 = self.event(w_1);
                    for e_2 in self.reachable_ec(w_1) {
                        let event_2 = self.event(e_2);
                        if self.thread_of(w_1) == self.thread_of(e_2)
                            || event_1.location != event_2.location
                        {
                            continue;
                        }

                        let w_2 = match self.event(e_2).event_type {
                            // Find w_x [ECe] r'_x [rf^-1] w'_x
                            EventType::Read => {
                                let w_2 = self.inverse_rf(e_2).expect("e_2 should have write");
                                if w_1 == w_2 {
                                    continue;
                                }
                                w_2
                            }
                            // Find w_x [ECe] w'_x
                            EventType::Write => e_2,
                        };
                        inserts.push((w_1, w_2));
                    }

                    for (w_1, w_2) in inserts.drain(..) {
                        changed |= self.scpl.insert(loc, w_1, w_2).ok()?;
                    }
                }
            }
        }

        if !self.is_consistent() {
            return None;
        }

        // Brute force the rest
        let num_threads = self.exec.thread_starts.len();
        let mut mos = vec![];
        for loc in 0..self.exec.num_locations {
            let writes = self.writes_per_thread_per_location[loc].clone();
            // Precompute the index of the first reachable write from each write for each
            // thread.
            let first_reachable: FxHashMap<(usize, usize, usize), usize> = writes
                .iter()
                .enumerate()
                .map(|(i, list)| list.iter().enumerate().map(move |(j, &w)| (i, j, w)))
                .flatten()
                .cartesian_product(0..num_threads)
                .map(|((i, j, w), th)| {
                    let first_event = self
                        .scpl
                        .first_reachable(loc, w, th)
                        .unwrap_or(EventId::MAX);
                    let first_write = writes[th].binary_search(&first_event).unwrap_or_else(|e| e);
                    ((i, j, th), first_write)
                })
                .collect();

            let permutations = writes
                .into_iter()
                .linearizations_with(move |i, j, th| first_reachable[&(i, j, th)])
                .map(TotalOrder::new)
                .map(Rc::new);
            mos.push(permutations);
        }

        // Try all possible combinations of total orders
        for mo in mos.into_iter().multi_cartesian_product() {
            self.exec.linearizations_checked += 1;
            self.exec.mo = TotalOrderUnion { orders: mo };
            if self.is_consistent() {
                return Some(self.exec.mo.clone());
            }
        }

        None
    }

    fn linearizations_checked(&self) -> usize {
        self.exec.linearizations_checked()
    }
}

struct Scpl {
    orders: Vec<PartialOrder>,
    inserted: usize,
}

impl Scpl {
    fn new(events_per_thread_per_location: Vec<Vec<Vec<EventId>>>) -> Self {
        let mut orders: Vec<_> = events_per_thread_per_location
            .clone()
            .into_iter()
            .map(PartialOrder::new)
            .collect();

        // Ensure that initial writes can see other threads
        for (loc, order) in orders.iter_mut().enumerate() {
            // Find the first event of location loc in each thread
            for &first_event in events_per_thread_per_location[loc][1..]
                .iter()
                .filter_map(|es| es.first())
            {
                order
                    .insert(loc as EventId, first_event)
                    .expect("Initial writes to other threads should not cause cycles");
            }
        }

        Self {
            orders,
            inserted: 0,
        }
    }

    fn query(&self, loc: usize, e_1: EventId, e_2: EventId) -> bool {
        self.orders[loc].query(e_1, e_2)
    }

    fn first_reachable(&self, loc: usize, e: EventId, thread: usize) -> Option<EventId> {
        self.orders[loc].first_reachable(e, thread)
    }

    fn insert(
        &mut self,
        loc: usize,
        e_1: EventId,
        e_2: EventId,
    ) -> Result<bool, PartialOrderCycleError> {
        let order = &mut self.orders[loc];
        if order.query(e_1, e_2) {
            return Ok(false);
        }
        self.inserted += 1;
        order.insert(e_1, e_2).map(|_| true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn store_buffer_execution() -> NaiveExecution {
        let threads = vec![
            vec![
                // e2
                Event {
                    location: 0,
                    event_type: EventType::Write,
                },
                // e3
                Event {
                    location: 1,
                    event_type: EventType::Read,
                },
            ],
            vec![
                // e4
                Event {
                    location: 1,
                    event_type: EventType::Write,
                },
                // e5
                Event {
                    location: 0,
                    event_type: EventType::Read,
                },
            ],
        ];
        NaiveExecution::new(&threads, 2)
    }

    fn two_rw_execution() -> NaiveExecution {
        let threads = vec![
            vec![
                // e2
                Event {
                    location: 0,
                    event_type: EventType::Read,
                },
                // e3
                Event {
                    location: 1,
                    event_type: EventType::Write,
                },
            ],
            vec![
                // e4
                Event {
                    location: 1,
                    event_type: EventType::Read,
                },
                // e5
                Event {
                    location: 0,
                    event_type: EventType::Write,
                },
            ],
        ];
        NaiveExecution::new(&threads, 2)
    }

    #[test]
    fn test_acyclic() {
        let exec = store_buffer_execution();
        // No edges
        assert!(acyclic(6, |_| []));
        // Self loops
        assert!(!acyclic(6, |e| [e]));
        // Simple cycle
        assert!(!acyclic(6, |e| [(e + 1) % exec.events.len() as EventId]));
        // Simple path
        assert!(acyclic(6, |e| if e == 0 { vec![] } else { vec![e - 1] }));
        // Complex DAG
        assert!(acyclic(6, |e| {
            if e == 0 {
                vec![1, 4]
            } else if e == 1 {
                vec![2, 4]
            } else if e == 2 {
                vec![3]
            } else if e == 3 {
                vec![4]
            } else if e == 4 {
                vec![]
            } else {
                vec![0]
            }
        }));
        // PO
        assert!(acyclic(6, |e| exec.po(e)));
        // PO + loop back edge
        assert!(!acyclic(6, |e| if e == 3 {
            vec![1, 4]
        } else {
            exec.po(e).collect()
        }));
    }

    #[test]
    fn store_buffer_sc_consistent() {
        let mut exec = store_buffer_execution().with_sc();
        exec.add_rf(0, 5);
        exec.add_rf(4, 3);

        exec.mo = TotalOrderUnion {
            orders: vec![
                Rc::new(TotalOrder::new(vec![0, 2])),
                Rc::new(TotalOrder::new(vec![1, 4])),
            ],
        };

        assert!(exec.is_consistent());
    }

    #[test]
    fn store_buffer_sc_consistent_total() {
        let mut exec = store_buffer_execution().with_sc();
        exec.add_rf(0, 5);
        exec.add_rf(4, 3);

        assert!(exec.is_totally_consistent().is_some());
        assert!(SaturatingExecution::from(exec)
            .is_totally_consistent()
            .is_some());
    }

    #[test]
    fn store_buffer_sc_inconsistent_total() {
        let mut exec = store_buffer_execution().with_sc();
        exec.add_rf(0, 5);
        exec.add_rf(1, 3);

        assert!(exec.is_totally_consistent().is_none());
        assert!(SaturatingExecution::from(exec)
            .is_totally_consistent()
            .is_none());
    }

    #[test]
    fn store_buffer_tso_consistent_total() {
        let mut exec = store_buffer_execution().with_tso();
        exec.add_rf(0, 5);
        exec.add_rf(1, 3);

        assert!(exec.is_totally_consistent().is_some());
        assert!(SaturatingExecution::from(exec)
            .is_totally_consistent()
            .is_some());
    }

    #[test]
    fn two_rw_tso_inconsistent_total() {
        let mut exec = two_rw_execution().with_tso();
        exec.add_rf(5, 2);
        exec.add_rf(3, 4);

        assert!(exec.is_totally_consistent().is_none());
        assert!(SaturatingExecution::from(exec)
            .is_totally_consistent()
            .is_none());
    }

    #[test]
    fn two_rw_tso_consistent_total() {
        let mut exec = two_rw_execution().with_tso();
        exec.add_rf(0, 2);
        exec.add_rf(3, 4);

        assert!(exec.is_totally_consistent().is_some());
        assert!(SaturatingExecution::from(exec)
            .is_totally_consistent()
            .is_some());
    }

    #[test]
    fn two_rw_relaxed_consistent_total() {
        let mut exec = two_rw_execution().with_relaxed();
        exec.add_rf(5, 2);
        exec.add_rf(3, 4);

        assert!(exec.is_totally_consistent().is_some());
        assert!(SaturatingExecution::from(exec)
            .is_totally_consistent()
            .is_some());
    }
}
