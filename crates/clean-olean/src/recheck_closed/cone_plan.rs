// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The closed replay's cone, planned for a caller that replays nothing: the
//! NDJSON export writer (`crate::ndjson`) writes a cone in the order the
//! replay admits it.
//!
//! This is not one of the replay's own source files
//! (`by_name_census_tests.rs`, `REPLAY_SOURCES`): nothing here calls the
//! kernel, and nothing the replay runs calls this.

use std::collections::BTreeSet;

use clean_kernel::env::Environment;
use clean_kernel::name::Name;

use super::family_index::FamilyIndex;
use super::{ConePlanner, UnitId};

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

/// A cone in the order the closed replay admits it.
pub(crate) struct ConeOrder {
    /// The units, each after every unit it depends on.
    pub(crate) units: Vec<PlannedUnit>,
    /// Names the cone reaches that the environment does not hold.
    pub(crate) absent: BTreeSet<Name>,
    /// Reference cycles between units.
    pub(crate) cycles: Vec<Vec<String>>,
}

/// Plan `targets`' cone over `env` exactly as [`super::recheck_closed`] plans it:
/// the same walk, the same units, the same dependency order. The NDJSON
/// export writer (`crate::ndjson`) writes a cone in this order, so the file's
/// order is the order the fenced entry admits it in.
pub(crate) fn cone_order(env: &Environment, targets: &BTreeSet<Name>) -> ConeOrder {
    let index = FamilyIndex::build(env);
    let mut planner = ConePlanner::new(env, &index);
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
