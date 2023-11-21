use std::collections::HashMap;

use roaring::RoaringBitmap;

/// A (partial) exection graph.
struct Execution {
    num_locations: usize,
    /// The events in the execution, in program order.
    events: Vec<Event>,
    thread_starts: Vec<EventId>,
    rf: Relation,
    inverse_rf: HashMap<EventId, EventId>,
    dob: Relation,
    mo: Relation,
}

impl Execution {
    fn is_consistent(&self) -> bool {
        self.sc_per_location() && self.external_coherence()
    }

    fn sc_per_location(&self) -> bool {
        self.asyclic(|event_id| {
            self.po(event_id)
                .chain(self.rf(event_id))
                .chain(self.mo(event_id))
                .chain(self.fr(event_id))
                .filter(move |&e2| {
                    self.events[e2 as usize].location == self.events[event_id as usize].location
                })
        })
    }

    fn external_coherence(&self) -> bool {
        self.asyclic(|event_id| {
            let thread = self.thread_of(event_id);
            self.dob(event_id).chain(
                self.rf(event_id)
                    .chain(self.mo(event_id))
                    .chain(self.fr(event_id))
                    .filter(move |&e2| self.thread_of(e2) != thread),
            )
        })
    }

    fn po(&self, event_id: EventId) -> impl Iterator<Item = EventId> {
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
        self.mo.get(&event_id).into_iter().flatten()
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

    fn asyclic<I>(&self, successors: impl Fn(EventId) -> I) -> bool
    where
        I: Iterator<Item = EventId>,
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

                stack.push((event_id, true));
                for succ in successors(event_id) {
                    if visiting.contains(succ) {
                        return false;
                    } else if visited.contains(succ) {
                        continue;
                    }
                    stack.push((succ, false));
                }
                visiting.insert(event_id);
            }
        }
        true
    }
}

struct Event {
    location: Location,
    value: Value,
    event_type: EventType,
}

enum EventType {
    Read,
    Write,
}

type Value = u64;
type Location = usize;
type EventId = u32;
type Relation = HashMap<EventId, RoaringBitmap>;

fn main() {
    println!("Hello, world!");
}
