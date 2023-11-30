#![feature(impl_trait_in_fn_trait_return)]

use std::collections::HashMap;

use iter::Linearizations;
use itertools::Itertools;
use relations::{EventRelation, PartialOrder, Relation, TotalOrder, TotalOrderUnion};
use roaring::RoaringBitmap;

mod fenwick;
mod iter;
mod relations;

pub type Location = usize;
pub type EventId = u32;

#[derive(Clone, Copy)]
pub struct Event {
    location: Location,
    event_type: EventType,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum EventType {
    Read,
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
        acyclic(self.num_events(), |e1| {
            let thread = self.thread_of(e1);
            self.dob(e1).chain(
                self.rf(e1)
                    .chain(self.mo(e1))
                    .chain(self.fr(e1))
                    // External edges go between threads, except if going from the
                    // special initial writes thread
                    .filter(move |&e2| thread == 0 || self.thread_of(e2) != thread),
            )
        })
    }

    fn fr(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
        self.inverse_rf(event_id)
            .into_iter()
            .flat_map(|w| self.mo(w))
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
struct NaiveExecution<Mo> {
    num_locations: usize,
    /// The events in the execution, in program order.
    events: Vec<Event>,
    thread_starts: Vec<EventId>,
    rf: EventRelation,
    inverse_rf: HashMap<EventId, EventId>,
    dob: EventRelation,
    mo: Mo,
}

impl<Mo> NaiveExecution<Mo>
where
    Mo: Relation,
{
    fn new(threads: &[Vec<Event>], num_locations: usize, mo: Mo) -> Self {
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
            rf: EventRelation::new(),
            inverse_rf: HashMap::new(),
            dob: EventRelation::new(),
            mo,
        }
    }

    fn add_rf(&mut self, w: EventId, r: EventId) {
        self.rf.entry(w).or_default().insert(r);
        self.inverse_rf.insert(r, w);
    }

    fn add_dob(&mut self, e1: EventId, e2: EventId) {
        self.dob.entry(e1).or_default().insert(e2);
    }

    fn fr(&self, event_id: EventId) -> impl Iterator<Item = EventId> + '_ {
        self.inverse_rf
            .get(&event_id)
            .into_iter()
            .flat_map(|&w| self.mo(w))
    }
    fn thread_end(&self, thread: usize) -> EventId {
        self.thread_starts
            .get(thread + 1)
            .copied()
            .unwrap_or(self.events.len() as EventId)
    }
}

impl<Mo> Execution for NaiveExecution<Mo>
where
    Mo: Relation,
{
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

    fn rf(&self, event_id: EventId) -> impl Iterator<Item = EventId> + '_ {
        self.rf.get(&event_id).into_iter().flatten()
    }

    fn dob(&self, event_id: EventId) -> impl Iterator<Item = EventId> + '_ {
        self.dob.get(&event_id).into_iter().flatten()
    }

    fn mo(&self, event_id: EventId) -> impl Iterator<Item = EventId> + '_ {
        self.mo.get(event_id, &self.events)
    }

    fn inverse_rf(&self, event_id: EventId) -> Option<EventId> {
        self.inverse_rf.get(&event_id).copied()
    }
}

impl CheckableExecution for NaiveExecution<TotalOrderUnion> {
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

struct SaturatingExecution {
    exec: NaiveExecution<EventRelation>,
    sc_order: PartialOrder,
}

impl SaturatingExecution {
    fn new(threads: &[Vec<Event>], num_locations: usize) -> Self {
        let exec = NaiveExecution::new(threads, num_locations, EventRelation::new());
        let sc_order = PartialOrder::new(exec.thread_starts.clone(), exec.num_events());
        Self { exec, sc_order }
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
        self.exec.mo(event_id)
    }

    fn inverse_rf(&self, event_id: EventId) -> Option<EventId> {
        self.exec.inverse_rf(event_id)
    }
}

impl CheckableExecution for SaturatingExecution {
    fn is_totally_consistent(&mut self) -> Option<TotalOrderUnion> {
        loop {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn store_buffer_execution() -> NaiveExecution<TotalOrderUnion> {
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
        NaiveExecution::new(&threads, 2, TotalOrderUnion::default())
    }

    fn store_buffer_sc_execution() -> NaiveExecution<TotalOrderUnion> {
        let mut exec = store_buffer_execution();
        // Set dob = po to get SC
        // Initial writes
        exec.add_dob(0, 1);
        exec.add_dob(0, 2);
        exec.add_dob(0, 3);
        exec.add_dob(0, 4);
        exec.add_dob(0, 5);
        exec.add_dob(1, 2);
        exec.add_dob(1, 3);
        exec.add_dob(1, 4);
        exec.add_dob(1, 5);
        // Rest of the events
        exec.add_dob(2, 3);
        exec.add_dob(4, 5);
        exec
    }

    fn store_buffer_tso_execution() -> NaiveExecution<TotalOrderUnion> {
        let mut exec = store_buffer_execution();
        // Set dob = po \ [W]; [R] to get TSO
        // Initial writes
        exec.add_dob(0, 1);
        exec.add_dob(0, 2);
        exec.add_dob(0, 4);
        exec.add_dob(1, 2);
        exec.add_dob(1, 4);
        exec
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
        let mut exec = store_buffer_sc_execution();
        exec.add_rf(0, 5);
        exec.add_rf(4, 3);

        exec.mo = TotalOrderUnion {
            orders: vec![TotalOrder::new(vec![0, 2]), TotalOrder::new(vec![1, 4])],
        };

        assert!(exec.is_consistent());
    }

    #[test]
    fn store_buffer_sc_consistent_total() {
        let mut exec = store_buffer_sc_execution();
        exec.add_rf(0, 5);
        exec.add_rf(4, 3);

        assert!(exec.is_totally_consistent().is_some());
    }

    #[test]
    fn store_buffer_sc_inconsistent_total() {
        let mut exec = store_buffer_sc_execution();
        exec.add_rf(0, 5);
        exec.add_rf(1, 3);

        assert!(exec.is_totally_consistent().is_none());
    }

    #[test]
    fn store_buffer_tso_consistent_total() {
        let mut exec = store_buffer_tso_execution();
        exec.add_rf(0, 5);
        exec.add_rf(1, 3);

        assert!(exec.is_totally_consistent().is_some())
    }
}

fn main() {
    println!("Hello, world!");
}
