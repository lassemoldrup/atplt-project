use std::fmt::{self, Debug, Display};

use crate::iter::Linearizations;
use crate::relations::{
    EventRelation, PartialOrder, Relation, ThreadIndex, TotalOrder, TotalOrderUnion,
};
use itertools::Itertools;
use roaring::RoaringBitmap;
use rustc_hash::{FxHashMap, FxHashSet};

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

    fn ec(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        let thread = self.thread_of(event_id);
        self.dob(event_id).chain(
            self.rf(event_id)
                .chain(self.mo(event_id))
                .chain(self.fr(event_id))
                // External edges go between threads, except if going from the
                // special initial writes thread
                .filter(move |&e2| thread == 0 || self.thread_of(e2) != thread),
        )
    }
}

pub trait CheckableExecution: Execution {
    fn is_totally_consistent(&mut self) -> Option<TotalOrderUnion>;
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
    rf: EventRelation,
    inverse_rf: FxHashMap<EventId, EventId>,
    dob: EventRelation,
    mo: TotalOrderUnion,
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

        Self {
            num_locations,
            events,
            thread_starts,
            rf: EventRelation::default(),
            inverse_rf: FxHashMap::default(),
            dob: EventRelation::default(),
            mo: TotalOrderUnion::default(),
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
        for event in 0..self.num_events() as EventId {
            if self.event(event).event_type != EventType::Read {
                continue;
            }
            let initial_write = self.thread_of(event) as EventId;
            self.inverse_rf.entry(event).or_insert_with(|| {
                self.rf.entry(initial_write).or_default().insert(event);
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
        self.thread_starts
            .binary_search(&event_id)
            .unwrap_or_else(|e| e - 1)
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

            let permutations = writes.into_iter().linearizations().map(TotalOrder::new);
            mos.push(permutations);
        }

        // Try all possible combinations of total orders
        for mo in mos.into_iter().multi_cartesian_product() {
            self.mo = TotalOrderUnion { orders: mo };
            if self.is_consistent() {
                return Some(self.mo.clone());
            }
        }

        None
    }
}

pub struct SaturatingExecution {
    exec: NaiveExecution,
    reads: Vec<Vec<EventId>>,
    writes: Vec<Vec<EventId>>,
    mo: EventRelation,
    scpl_order: PartialOrder,
}

impl SaturatingExecution {
    fn reachable_ec(&self, from: EventId, to: EventId) -> bool {
        let mut seen = FxHashSet::default();
        let mut stack = vec![from];
        while let Some(e1) = stack.pop() {
            if e1 == to {
                return true;
            }
            seen.insert(e1);
            stack.extend(self.ec(e1).filter(|e2| !seen.contains(e2)));
        }
        false
    }
}

impl From<NaiveExecution> for SaturatingExecution {
    fn from(exec: NaiveExecution) -> Self {
        let scpl_order = PartialOrder::new(exec.thread_starts.clone(), exec.num_events());
        let mut reads = vec![vec![]; exec.num_locations];
        let mut writes = vec![vec![]; exec.num_locations];
        for (event_id, event) in exec.events.iter().enumerate() {
            match event.event_type {
                EventType::Read => reads[event.location].push(event_id as EventId),
                EventType::Write => writes[event.location].push(event_id as EventId),
            }
        }
        Self {
            exec,
            reads,
            writes,
            mo: EventRelation::default(),
            scpl_order,
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
        self.mo.successors(event_id, &self.exec.events)
    }

    fn inverse_rf(&self, event_id: EventId) -> Option<EventId> {
        self.exec.inverse_rf(event_id)
    }

    fn is_consistent(&self) -> bool {
        self.exec.is_consistent()
    }
}

impl CheckableExecution for SaturatingExecution {
    fn is_totally_consistent(&mut self) -> Option<TotalOrderUnion> {
        // Saturate first
        let mut changed = true;
        while changed {
            changed = false;

            for loc in 0..self.reads.len() {
                for &r_1 in &self.reads[loc] {
                    // Find w_x [rf] r_x [SCPL] r'_x [rf^-1] w'_x
                    for &r_2 in &self.reads[loc] {
                        if r_1 == r_2 || !self.scpl_order.query(r_1, r_2) {
                            continue;
                        }
                        let w_1 = self.inverse_rf(r_1).expect("r_1 should have write");
                        let w_2 = self.inverse_rf(r_2).expect("r_2 should have write");
                        if w_1 == w_2 || self.scpl_order.query(w_1, w_2) {
                            continue;
                        }
                        if self.scpl_order.insert(w_1, w_2).is_err() {
                            return None;
                        }
                        self.mo.entry(w_1).or_default().insert(w_2);
                        changed = true;
                    }

                    // Find w_x [rf] r_x [SCPL^-1] w'_x
                    for &w_2 in &self.writes[loc] {
                        if !self.scpl_order.query(w_2, r_1) {
                            continue;
                        }
                        let w_1 = self.inverse_rf(r_1).expect("r_1 should have write");
                        if w_1 == w_2 || self.scpl_order.query(w_1, w_2) {
                            continue;
                        }
                        if self.scpl_order.insert(w_1, w_2).is_err() {
                            return None;
                        }
                        self.mo.entry(w_1).or_default().insert(w_2);
                        changed = true;
                    }
                }

                // Find w_x [ECe] w'_x
                for &w_1 in &self.writes[loc] {
                    for &w_2 in &self.writes[loc] {
                        if self.thread_of(w_1) == self.thread_of(w_2)
                            || self.scpl_order.query(w_1, w_2)
                            || !self.reachable_ec(w_1, w_2)
                        {
                            continue;
                        }
                        if self.scpl_order.insert(w_1, w_2).is_err() {
                            return None;
                        }
                        self.mo.entry(w_1).or_default().insert(w_2);
                        changed = true;
                    }
                }
            }
        }

        // Brute force the rest
        let num_threads = self.exec.thread_starts.len();
        let mut mos = vec![];
        for loc in 0..self.exec.num_locations {
            let mut writes = vec![vec![]; num_threads];
            let mut thread = 0;
            for w in self
                .exec
                .events
                .iter()
                .enumerate()
                .filter(|(_, e)| e.location == loc && e.event_type == EventType::Write)
                .map(|(i, _)| i as EventId)
            {
                if w >= self.exec.thread_end(thread) {
                    thread += 1;
                }
                writes[thread].push(w);
            }

            // Precompute the index of the first reachable write from each write for each
            // thread.
            let first_reachable: FxHashMap<(usize, usize, usize), usize> = writes
                .iter()
                .enumerate()
                .map(|(i, list)| list.iter().enumerate().map(move |(j, &w)| (i, j, w)))
                .flatten()
                .cartesian_product(0..num_threads)
                .map(|((i, j, w), th)| {
                    let first_event = self.exec.thread_starts[th]
                        .saturating_add(self.scpl_order.first_reachable(w, th) as EventId);
                    let first_write = writes[th].binary_search(&first_event).unwrap_or_else(|e| e);
                    ((i, j, th), first_write)
                })
                .collect();

            let permutations = writes
                .into_iter()
                .linearizations_with(move |i, j, th| first_reachable[&(i, j, th)])
                .map(TotalOrder::new);
            mos.push(permutations);
        }

        // Try all possible combinations of total orders
        for mo in mos.into_iter().multi_cartesian_product() {
            self.exec.mo = TotalOrderUnion { orders: mo };
            if self.is_consistent() {
                return Some(self.exec.mo.clone());
            }
        }

        None
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
            orders: vec![TotalOrder::new(vec![0, 2]), TotalOrder::new(vec![1, 4])],
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
