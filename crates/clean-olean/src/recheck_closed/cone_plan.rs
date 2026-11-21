// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dependency ordering for the expressions the NDJSON export writer serializes.
//!
//! This is not one of the replay's own source files
//! (`by_name_census_tests.rs`, `REPLAY_SOURCES`): nothing here calls the
//! kernel, and nothing the replay runs calls this.

use std::collections::BTreeSet;

use clean_kernel::env::{ConstantKind, Environment};
use clean_kernel::inductive::RecursorVal;
use clean_kernel::name::{Name, NameInner};

use super::family_index::FamilyIndex;
use super::{ConeInputs, ConePlanner, UnitId};

/// One unit of a cone, for a caller outside the replay.
#[derive(Debug, Clone)]
pub(crate) enum PlannedUnit {
    /// An ordinary constant, or one of the quotient primitives.
    Constant(Name),
    /// An inductive family block: its canonical head and every member (its
    /// types, their constructors, the recursors that eliminate them).
    Family {
        /// The block's canonical head.
        head: Name,
        /// Every name the block is responsible for.
        members: Vec<Name>,
    },
}

/// A cone in dependency order.
pub(crate) struct ConeOrder {
    /// The units, each after every unit it depends on.
    pub(crate) units: Vec<PlannedUnit>,
    /// Names the cone reaches that the environment does not hold.
    pub(crate) absent: BTreeSet<Name>,
    /// Reference cycles between units.
    pub(crate) cycles: Vec<Vec<String>>,
}

/// Clean's source inductive builder also indexes these definitions as fast
/// paths for native reduction. In Lean each is an ordinary definition whose
/// value unfolds to the family's primitive recursor. Check the owner and the
/// resident declaration before separating it from the primitive block.
pub(super) fn is_exported_eliminator_definition(env: &Environment, rec: &RecursorVal) -> bool {
    matches!(
        rec.name.inner(),
        NameInner::Str(parent, suffix)
            if **parent == rec.inductive_name && matches!(&**suffix, "casesOn" | "recOn")
    ) && env.get_const(&rec.name).is_some_and(|info| {
        info.kind == ConstantKind::Definition
            && info.value.is_some()
            && info.type_ == rec.type_
            && info.level_params == rec.level_params
    })
}

/// Order the records needed to serialize the targets, including resident
/// recursor terms and the support constants of actual literal leaves.
pub(crate) fn cone_order(env: &Environment, targets: &BTreeSet<Name>) -> ConeOrder {
    let index = FamilyIndex::build(env);
    let mut planner = ConePlanner::new(env, &index, ConeInputs::Export);
    for target in targets {
        planner.enqueue(target);
    }
    // The planner's own refusals are its absent names, which it also keeps.
    planner.run(None, &mut Vec::new());
    let ConePlanner {
        mut units,
        order,
        cycles,
        absent,
        ..
    } = planner;
    let units = order
        .into_iter()
        .filter_map(|id| {
            let unit = units.remove(&id)?;
            Some(match id {
                UnitId::Constant(name) => PlannedUnit::Constant(name),
                UnitId::Family(head) => PlannedUnit::Family {
                    head,
                    members: unit.members,
                },
            })
        })
        .collect();
    ConeOrder {
        units,
        absent,
        cycles,
    }
}
