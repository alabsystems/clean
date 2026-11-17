// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded metadata fixpoint using the existing runtime dependency planner.

use super::{budget::Budget, ExternalLeanProgram};
use clean_compiler::{runtime_lcnf::RuntimeSourceCaptureLimits, RuntimeBindingPlan};
use clean_kernel::{Name, RecursorVal};
use std::{cell::RefCell, collections::BTreeSet};

pub(super) fn discover<'program>(
    program: &'program ExternalLeanProgram,
    roots: &mut BTreeSet<Name>,
    budget: &RefCell<Budget>,
) -> Result<(RuntimeBindingPlan, Vec<&'program RecursorVal>, Vec<Name>), String> {
    // One whole-world walk. Retain references, never unchecked metadata copies.
    // Name work is charged before later family membership comparisons.
    let mut available = Vec::new();
    for rec in program.env.recursors() {
        let mut work = budget.borrow_mut();
        work.visit()?;
        work.name(&rec.inductive_name)?;
        available.push(rec);
    }
    let mut selected = Vec::new();
    let mut selected_names = BTreeSet::new();
    loop {
        for root in roots.iter() {
            budget.borrow_mut().name(root)?;
        }
        let root_names: Vec<_> = roots.iter().cloned().collect();
        let plan = RuntimeBindingPlan::discover(
            &program.env,
            &root_names,
            RuntimeSourceCaptureLimits::default().declarations,
        )
        .map_err(|e| e.to_string())?;
        let mut members = BTreeSet::new();
        for member in plan.members() {
            budget.borrow_mut().name(member)?;
            members.insert(member);
        }
        let mut expanded = false;
        for rec in &available {
            let mut work = budget.borrow_mut();
            work.name(&rec.inductive_name)?;
            if !members.contains(&rec.inductive_name) {
                continue;
            }
            work.name(&rec.name)?;
            if selected_names.contains(&rec.name) {
                continue;
            }
            // Include original recursors for EVERY reached family, including
            // metadata-only ones fresh family replay adds automatically.
            work.recursor(rec)?;
            selected_names.insert(&rec.name);
            selected.push(*rec);
            expanded |= roots.insert(rec.name.clone());
        }
        if !expanded {
            return Ok((plan, selected, root_names));
        }
        // Repeat only the shared planner over the expanded actual root set.
        // Every pass consumes this same cumulative owner budget; no row is
        // dropped and no kernel replay/digest is performed during discovery.
    }
}
