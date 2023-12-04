use std::iter;

use itertools::Itertools;
use roaring::RoaringBitmap;
use rustc_hash::FxHashMap;

use crate::fenwick::MinFenwickTree;
use crate::{Event, EventId};

pub type EventRelation = FxHashMap<EventId, RoaringBitmap>;

pub trait Relation {
    fn successors(&self, event_id: EventId, events: &[Event]) -> impl Iterator<Item = EventId>;
}

impl Relation for EventRelation {
    fn successors(&self, event_id: EventId, _: &[Event]) -> impl Iterator<Item = EventId> {
        self.get(&event_id).into_iter().flatten()
    }
}

#[derive(Clone, Debug)]
pub struct TotalOrder {
    order: Vec<EventId>,
    indices: FxHashMap<EventId, usize>,
}

impl TotalOrder {
    pub fn new(order: Vec<EventId>) -> Self {
        let indices = order
            .iter()
            .enumerate()
            .map(|(i, &event_id)| (event_id, i))
            .collect();
        Self { order, indices }
    }
}

impl Relation for TotalOrder {
    fn successors<'a>(&'a self, event_id: EventId, _: &[Event]) -> impl Iterator<Item = EventId> {
        self.indices
            .get(&event_id)
            .map(|&i| &self.order[i + 1..])
            .into_iter()
            .flatten()
            .copied()
    }
}

#[derive(Clone, Default, Debug)]
pub struct TotalOrderUnion {
    pub orders: Vec<TotalOrder>,
}

impl Relation for TotalOrderUnion {
    fn successors<'a>(
        &'a self,
        event_id: EventId,
        events: &[Event],
    ) -> impl Iterator<Item = EventId> {
        let loc = events[event_id as usize].location;
        self.orders[loc].successors(event_id, events)
    }
}

pub type ThreadIndex = (usize, usize);

/// A data structure for storing partial orders over events. Parital orders
/// are always refinements of the program order. Supports `O(log n)` edge
/// insertion and `O(log n)` reachability queries.
pub struct PartialOrder {
    /// `edges[i][j]` holds all edges from thread `i` to thread `j`.
    edges: Vec<Vec<MinFenwickTree<usize>>>,
    thread_starts: Vec<EventId>,
}

impl PartialOrder {
    pub fn new(thread_starts: Vec<EventId>, num_events: usize) -> Self {
        let num_threads = thread_starts.len();
        let thread_lengths = thread_starts
            .iter()
            .zip(thread_starts.iter().skip(1).chain(&[num_events as EventId]))
            .map(|(&start, &end)| end as usize - start as usize)
            .collect_vec();
        let mut edges = vec![vec![]; num_threads];
        for i1 in 0..num_threads {
            for (i2, &len) in thread_lengths.iter().enumerate() {
                if i1 == i2 {
                    // Edges to the same thread point to the next event, or usize::MAX for
                    // the last event. This makes sure that events can reach other events
                    // in the same thread.
                    edges[i1].push(MinFenwickTree::build(
                        (1..len).chain(iter::once(usize::MAX)),
                    ));
                } else {
                    edges[i1].push(MinFenwickTree::build(iter::repeat(usize::MAX).take(len)));
                }
            }
        }

        Self {
            edges,
            thread_starts,
        }
    }

    pub fn insert(&mut self, e1: EventId, e2: EventId) -> Result<(), PartialOrderCycleError> {
        let e1 = self.to_thread_index(e1);
        let e2 = self.to_thread_index(e2);

        // Check for cycles.
        if self.successor(e2, e1.0) <= e1.1 {
            return Err(PartialOrderCycleError);
        }

        let num_threads = self.edges.len();
        for i1 in 0..num_threads {
            for i2 in 0..num_threads {
                let Some(j1) = self.predecessor(e1, i1) else {
                    continue;
                };
                let j2 = self.successor(e2, i2);
                self.edges[i1][i2].update(j1, j2);
            }
        }

        Ok(())
    }

    pub fn query(&self, e1: EventId, e2: EventId) -> bool {
        let e1 = self.to_thread_index(e1);
        let (i2, j2) = self.to_thread_index(e2);
        self.successor(e1, i2) <= j2
    }

    pub fn first_reachable(&self, e1: EventId, thread: usize) -> usize {
        let e1 = self.to_thread_index(e1);
        self.successor(e1, thread)
    }

    fn successor(&self, (i, j): ThreadIndex, thread: usize) -> usize {
        // TODO: Should we have self loops by default?
        if i == thread {
            j
        } else {
            self.edges[i][thread].query(j)
        }
    }

    fn predecessor(&self, (i, j): ThreadIndex, thread: usize) -> Option<usize> {
        if i == thread {
            Some(j)
        } else {
            self.edges[thread][i].arg_leq(j)
        }
    }

    fn to_thread_index(&self, event_id: EventId) -> (usize, usize) {
        let thread = self
            .thread_starts
            .binary_search(&event_id)
            .unwrap_or_else(|i| i - 1);
        (
            thread,
            event_id as usize - self.thread_starts[thread] as usize,
        )
    }
}

impl Relation for PartialOrder {
    fn successors(&self, event_id: EventId, events: &[Event]) -> impl Iterator<Item = EventId> {
        let (i1, j1) = self.to_thread_index(event_id);
        let last_thread_end = events.len() as EventId;
        (0..self.edges.len())
            .map(move |i2| {
                let j2 = self.edges[i1][i2].query(j1);
                let start = self.thread_starts[i2] + j2 as EventId;
                let end = self
                    .thread_starts
                    .get(i2 + 1)
                    .copied()
                    .unwrap_or(last_thread_end);
                start..end
            })
            .flatten()
    }
}

#[derive(Debug)]
pub struct PartialOrderCycleError;

#[cfg(test)]
mod test {
    use crate::EventType;

    use super::*;

    #[test]
    fn partial_order_two_thread_test() {
        // Two thread with indices 0, 1, 2, || 3, 4, 5
        let mut partial_order = PartialOrder::new(vec![0, 3], 6);
        assert!(partial_order.query(0, 2));
        assert!(!partial_order.query(0, 3));

        // Insert 0 -> 3
        assert!(partial_order.insert(0, 3).is_ok());
        assert!(partial_order.query(0, 3));
        assert!(partial_order.query(0, 5));
        assert!(!partial_order.query(1, 4));

        // Insert 1 -> 4
        assert!(partial_order.insert(1, 4).is_ok());
        assert!(partial_order.query(1, 4));
        assert!(partial_order.query(1, 5));
        assert!(!partial_order.query(2, 5));
        assert!(!partial_order.query(5, 2));

        // Insert 5 -> 2
        assert!(partial_order.insert(5, 2).is_ok());
        assert!(partial_order.query(5, 2));
        assert!(partial_order.query(3, 2));
        assert!(!partial_order.query(3, 1));
        assert!(!partial_order.query(2, 5));

        // Sanity check
        assert!(partial_order.query(0, 5));

        // Cycle checks
        assert!(partial_order.insert(0, 0).is_err());
        assert!(partial_order.insert(5, 3).is_err());
        assert!(partial_order.insert(2, 4).is_err());
    }

    #[test]
    fn partial_order_three_thread_test() {
        // Three thread with indices 0, 1, 2, || 3, 4, 5, || 6, 7, 8
        let mut partial_order = PartialOrder::new(vec![0, 3, 6], 9);
        assert!(partial_order.query(0, 2));
        assert!(!partial_order.query(0, 6));

        // 0----->3 ||  6
        //    ||--------^
        // 1----^ 4<----7
        //    ||    ||
        // 2  ||  5---->8
        assert!(partial_order.insert(0, 3).is_ok());
        assert!(partial_order.insert(1, 6).is_ok());
        assert!(partial_order.insert(7, 4).is_ok());
        assert!(partial_order.insert(5, 8).is_ok());

        // 0 can reach everything
        for i in 0..9 {
            assert!(partial_order.query(0, i));
        }

        assert!(partial_order.query(1, 7));
        assert!(partial_order.query(1, 5));
        assert!(!partial_order.query(1, 3));

        assert!(partial_order.query(6, 4));
        assert!(!partial_order.query(6, 2));

        // Cycle checks
        assert!(partial_order.insert(8, 3).is_err());
        assert!(partial_order.insert(8, 1).is_err());
        assert!(partial_order.insert(4, 0).is_err());
        assert!(partial_order.insert(4, 6).is_err());
    }

    #[test]
    fn partial_order_iter_test() {
        // Three thread with indices 0, 1, 2, || 3, 4, 5, || 6, 7, 8
        let mut partial_order = PartialOrder::new(vec![0, 3, 6], 9);

        // 0----->3 ||  6
        //    ||--------^
        // 1----^ 4<----7
        //    ||    ||
        // 2  ||  5---->8
        partial_order.insert(0, 3).unwrap();
        partial_order.insert(1, 6).unwrap();
        partial_order.insert(7, 4).unwrap();
        partial_order.insert(5, 8).unwrap();

        let events = [Event {
            location: 0,
            event_type: EventType::Read,
        }; 9];

        itertools::assert_equal(partial_order.successors(0, &events), 1..9);
        itertools::assert_equal(partial_order.successors(1, &events), vec![2, 4, 5, 6, 7, 8]);
        itertools::assert_equal(partial_order.successors(6, &events), vec![4, 5, 7, 8]);
    }
}
