// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original bottom-up exact constant classes, observed at their real work.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError, observed_btree,
};
use core::mem::{size_of, take};
use std::collections::BTreeMap;
mod fingerprint;
mod intern;
mod keys;
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use keys::Key;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
/// Diagnostic canonical-spelling data for one exact borrowed input, never a
/// constant/type/source/proof capability. Safe borrow keeps all recorded node
/// addresses stable; no cloned input or candidate membership map is accepted.
pub struct ObservedUniformElementLists<'c> {
    _root: &'c Constant,
    rows: Vec<usize>,
}
struct Frame<'a> {
    node: &'a Constant,
    children: ConstantChildren<'a>,
    first: usize,
}
#[derive(Default)]
struct State<'a> {
    stack: Vec<Frame<'a>>,
    current: Option<Frame<'a>>,
    results: Vec<usize>,
    classes: Vec<Key<'a>>,
    buckets: BTreeMap<[u8; 32], Vec<usize>>,
    pending_bucket: Vec<usize>,
    building: Option<Key<'a>>,
    pending_key: Option<Key<'a>>,
    uniform: Vec<usize>,
}
impl Constant {
    /// Same exact class algebra as uniform_element_lists: Array/Aggregate/raw
    /// Bytes(false) list aliases, bit-exact leaves, ordered record labels,
    /// closure IDs and Splat lengths. Each actual stored child is visited once
    /// (Splat once); raw byte Int classes are streamed. Fixed-width SHA buckets
    /// accelerate lookup ONLY: every hash collision gets full observed exact
    /// key equality. No hash result authenticates or admits a constant.
    /// All real tree/key/byte/class/collision/stack/growth/retirement work uses
    /// the SAME original session/site; no owner/grant/deadline/TLS/fuel/flag,
    /// normalization heuristic, permissive cap or accepting fallback.
    pub fn uniform_element_lists_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<ObservedUniformElementLists<'_>> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
        let mut state = State::default();
        let result = state.walk(self, &mut work);
        state.retire_scratch(&mut work);
        match result.and_then(|()| work.publication(size_of::<ObservedUniformElementLists<'_>>())) {
            Ok(()) => Ok(ObservedUniformElementLists {
                _root: self,
                rows: take(&mut state.uniform),
            }),
            Err(error) => {
                work.rows(take(&mut state.uniform));
                Err(work.terminal(error))
            }
        }
    }
}
impl ObservedUniformElementLists<'_> {
    pub fn contains_observed<O: ExecutionObserver>(
        &self,
        node: &Constant,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut work = Work { session, site };
        work.admit(2, size_of::<usize>())?;
        let address = node as *const Constant as usize;
        let mut at = 0;
        let result = loop {
            let Some(row) = work.at(&self.rows, at)? else {
                break false;
            };
            work.admit(1, size_of::<bool>())?;
            if *row == address {
                break true;
            }
            work.next(&mut at)?;
        };
        work.publication(size_of::<bool>())?;
        Ok(result)
    }
    pub fn retire_observed<O: ExecutionObserver>(
        mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        work.rows(take(&mut self.rows));
        work.publication(0)
    }
}
