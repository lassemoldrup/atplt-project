use std::collections::HashMap;
use std::{iter, option};

use roaring::RoaringBitmap;

use crate::{Event, EventId};

pub type EventRelation = HashMap<EventId, RoaringBitmap>;

pub trait Relation {
    type Iter<'a>: Iterator<Item = EventId>
    where
        Self: 'a;
    fn get<'a>(&'a self, event_id: EventId, events: &[Event]) -> Self::Iter<'a>;
}

impl Relation for EventRelation {
    type Iter<'a> = iter::Flatten<option::IntoIter<&'a RoaringBitmap>>;

    fn get<'a>(&'a self, event_id: EventId, _: &[Event]) -> Self::Iter<'a> {
        self.get(&event_id).into_iter().flatten()
    }
}

#[derive(Clone)]
pub struct TotalOrder {
    order: Vec<EventId>,
    indices: HashMap<EventId, usize>,
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
    type Iter<'a> = iter::Copied<iter::Flatten<option::IntoIter<&'a [EventId]>>>;

    fn get<'a>(&'a self, event_id: EventId, _: &[Event]) -> Self::Iter<'a> {
        self.indices
            .get(&event_id)
            .map(|&i| &self.order[i + 1..])
            .into_iter()
            .flatten()
            .copied()
    }
}

#[derive(Clone, Default)]
pub struct TotalOrderUnion {
    pub orders: Vec<TotalOrder>,
}

impl Relation for TotalOrderUnion {
    type Iter<'a> = <TotalOrder as Relation>::Iter<'a>;

    fn get<'a>(&'a self, event_id: EventId, events: &[Event]) -> Self::Iter<'a> {
        let loc = events[event_id as usize].location;
        self.orders[loc].get(event_id, events)
    }
}
