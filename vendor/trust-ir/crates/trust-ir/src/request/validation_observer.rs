// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Diagnostic counts at the actual canonical validator entry. No authority.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

thread_local! {
    static OBSERVERS: RefCell<Vec<Rc<Cell<usize>>>> = const { RefCell::new(Vec::new()) };
}

/// Counts validator entries on this thread until dropped, including failures.
/// Nested observers are independent, and unwinding drops their registrations.
/// This guard cannot be sent to another thread.
pub struct ValidationObservation {
    count: Rc<Cell<usize>>,
}

impl ValidationObservation {
    pub fn start() -> Self {
        let count = Rc::new(Cell::new(0));
        OBSERVERS.with_borrow_mut(|observers| observers.push(Rc::clone(&count)));
        Self { count }
    }

    pub fn calls(&self) -> usize {
        self.count.get()
    }
}

impl Drop for ValidationObservation {
    fn drop(&mut self) {
        OBSERVERS.with_borrow_mut(|observers| {
            observers.retain(|count| !Rc::ptr_eq(count, &self.count));
        });
    }
}

pub(super) fn record() {
    OBSERVERS.with_borrow(|observers| {
        for count in observers {
            count.set(count.get().saturating_add(1));
        }
    });
}
