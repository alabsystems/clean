// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The linearity engine's model of a LOOP (`tail_loop`): a join point whose
//! body jumps back to it.
//!
//! The engine names an object by the variable that bound it. A loop binds
//! the same variables again on every iteration, so three things keep one
//! iteration's facts from leaking into the next:
//!
//! * a binding forgets every fact about the id it binds ([`forget_binding`]);
//! * at a back edge, every object an entering parameter holds is renamed to
//!   that parameter's id ([`canonicalize_entering_objects`]), which no
//!   statement of the body binds, so it cannot collide with an object the
//!   next iteration makes, and successive iterations reach equal states (the
//!   per-join-point memo then terminates the walk);
//! * at every jump, exclusivity and taken-slot facts are kept only for
//!   objects a variable in scope still names ([`prune_unreachable_facts`]).

use std::collections::{BTreeMap, BTreeSet};

use super::{Origin, State};
use crate::ir::{IRType, VarId};

/// Drop every fact about the object and value a new binding of `var`
/// replaces (see the call in `vdecl`).
pub(super) fn forget_binding(st: &mut State, var: u32) {
    st.exclusive.remove(&var);
    st.taken.retain(|(obj, _)| *obj != var);
    st.known.remove(&var);
    st.shared_probe.remove(&var);
}

/// At a back edge, rename each object an entering join-point parameter holds
/// to that parameter's own id (the first parameter, in order, that holds it),
/// simultaneously everywhere the object is named: variable slots, field
/// origins, exclusivity, taken slots and sharing probes. A parameter id is
/// bound only on entry to its join point, never by a statement of its body,
/// so a renamed object cannot collide with one the next iteration binds.
/// Objects no entering parameter holds keep their ids: they belong to
/// variables bound before the join point, which its body never rebinds.
pub(super) fn canonicalize_entering_objects(st: &mut State, params: &[(VarId, IRType)]) {
    let mut rename: BTreeMap<u32, u32> = BTreeMap::new();
    for (param, _) in params {
        if let Some(slot) = st.vars.get(&param.0) {
            if slot.origin != Origin::Null {
                rename.entry(slot.obj).or_insert(param.0);
            }
        }
    }
    if rename.is_empty() {
        return;
    }
    let map = |obj: u32| *rename.get(&obj).unwrap_or(&obj);
    for slot in st.vars.values_mut() {
        if slot.origin == Origin::Null {
            continue;
        }
        slot.obj = map(slot.obj);
        if let Origin::Field { parent, idx } = slot.origin {
            slot.origin = Origin::Field {
                parent: map(parent),
                idx,
            };
        }
    }
    st.exclusive = st.exclusive.iter().map(|obj| map(*obj)).collect();
    st.taken = st
        .taken
        .iter()
        .map(|(obj, idx)| (map(*obj), *idx))
        .collect();
    for probed in st.shared_probe.values_mut() {
        *probed = map(*probed);
    }
}

/// Keep exclusivity and taken-slot facts only for objects some variable in
/// scope still names (as its object or as the parent of its field origin).
/// A fact about an object nothing names can never be consulted again, and in
/// a loop it would make the states of successive iterations differ forever.
pub(super) fn prune_unreachable_facts(st: &mut State) {
    let mut named: BTreeSet<u32> = BTreeSet::new();
    for slot in st.vars.values() {
        if slot.origin == Origin::Null {
            continue;
        }
        named.insert(slot.obj);
        if let Origin::Field { parent, .. } = slot.origin {
            named.insert(parent);
        }
    }
    st.exclusive.retain(|obj| named.contains(obj));
    st.taken.retain(|(obj, _)| named.contains(obj));
    st.shared_probe.retain(|_, obj| named.contains(obj));
}
