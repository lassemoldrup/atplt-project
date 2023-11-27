use std::collections::HashMap;

use itertools::Itertools;
use relations::{EventRelation, Relation, TotalOrder, TotalOrderUnion};
use roaring::RoaringBitmap;

mod fenwick;
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

/// A (partial) exection graph.
struct Execution<Mo> {
    num_locations: usize,
    /// The events in the execution, in program order.
    events: Vec<Event>,
    thread_starts: Vec<EventId>,
    rf: EventRelation,
    inverse_rf: HashMap<EventId, EventId>,
    dob: EventRelation,
    mo: Mo,
}

impl<Mo> Execution<Mo>
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

    fn is_consistent(&self) -> bool {
        self.sc_per_location() && self.external_coherence()
    }

    fn sc_per_location(&self) -> bool {
        self.acyclic(|event_id| {
            let loc = self.events[event_id as usize].location;
            // TODO: We could use the fact that the PO is a total order to
            // reduce the number of edges we need to check. Problem: the last
            // initial write has multiple direct PO successors.
            self.po(event_id)
                .chain(self.rf(event_id))
                .chain(self.mo(event_id))
                .chain(self.fr(event_id))
                .filter(move |&e2| self.events[e2 as usize].location == loc)
        })
    }

    fn external_coherence(&self) -> bool {
        self.acyclic(|event_id| {
            let thread = self.thread_of(event_id);
            self.dob(event_id).chain(
                self.rf(event_id)
                    .chain(self.mo(event_id))
                    .chain(self.fr(event_id))
                    // External edges go between threads, except if going from the
                    // special initial writes thread
                    .filter(move |&e2| thread == 0 || self.thread_of(e2) != thread),
            )
        })
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

    fn fr(&self, event_id: EventId) -> impl Iterator<Item = EventId> + '_ {
        self.inverse_rf
            .get(&event_id)
            .into_iter()
            .flat_map(|&w| self.mo(w))
    }

    fn thread_of(&self, event_id: EventId) -> usize {
        self.thread_starts
            .binary_search(&event_id)
            .unwrap_or_else(|e| e - 1)
    }

    fn acyclic<I>(&self, successors: impl Fn(EventId) -> I) -> bool
    where
        I: IntoIterator<Item = EventId>,
    {
        let mut visited = RoaringBitmap::new();
        let mut visiting = RoaringBitmap::new();
        let mut stack = vec![];
        for event_id in 0..self.events.len() as u32 {
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
}

impl Execution<TotalOrderUnion> {
    fn is_totally_consistent(&mut self) -> Option<TotalOrderUnion> {
        // Generate all possible total orders for each location
        // TODO: Don't generate orders going against the PO. We could also
        // check SC per location for each total order only once, instead
        // of checking it repeatedly for each combination of total orders.
        let mut mos = vec![];
        for loc in 0..self.num_locations {
            let writes = self
                .events
                .iter()
                .enumerate()
                .filter(|(_, e)| e.location == loc && e.event_type == EventType::Write)
                .map(|(i, _)| i as EventId)
                .collect::<Vec<_>>();
            let num_writes = writes.len();
            let permutations = writes
                .into_iter()
                .permutations(num_writes)
                .map(|p| TotalOrder::new(p));
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

#[cfg(test)]
mod tests {
    use super::*;

    fn store_buffer_execution() -> Execution<TotalOrderUnion> {
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
        Execution::new(&threads, 2, TotalOrderUnion::default())
    }

    fn store_buffer_sc_execution() -> Execution<TotalOrderUnion> {
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

    fn store_buffer_tso_execution() -> Execution<TotalOrderUnion> {
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
        assert!(exec.acyclic(|_| []));
        // Self loops
        assert!(!exec.acyclic(|e| [e]));
        // Simple cycle
        assert!(!exec.acyclic(|e| [(e + 1) % exec.events.len() as EventId]));
        // Simple path
        assert!(exec.acyclic(|e| if e == 0 { vec![] } else { vec![e - 1] }));
        // Complex DAG
        assert!(exec.acyclic(|e| {
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
        assert!(exec.acyclic(|e| exec.po(e)));
        // PO + loop back edge
        assert!(!exec.acyclic(|e| if e == 3 {
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
