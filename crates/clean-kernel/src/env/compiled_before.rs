// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `@[implemented_by]` ORDER record: the constants whose compiled code an
//! `@[implemented_by]` binding came too late for (`docs/DECISIONS.md` R80
//! item 4, R149). Pinned Lean compiles a declaration when it is added, so code
//! added before an `attribute [implemented_by f] d` command keeps the body it
//! was compiled with, and which one that is depends on Lean's inliner, which
//! Clean does not model. While the record is not empty every compiled lane
//! refuses every root (`clean_compiler::implemented_by_order`).
//!
//! Kernel-irrelevant, like the `@[implemented_by]` registry beside it
//! ([`Environment::register_implemented_by`]): no type check reads it. It is
//! here because three crates meet on it and only this one is below all of
//! them: source elaboration writes it (`clean_elab`, for a late command in the
//! file it elaborates), `.olean` import writes it (`clean_olean`, from a Clean
//! payload, or inferred from a Lean-built module's compiled IR), and
//! `clean_compiler`, which depends on neither, reads it.
//!
//! Session state, like `Clean.elab.mutualLift`: the typed extension exports
//! nothing, so it stays out of the environment digest and out of every
//! `.olean` Clean writes in Lean's format. A Clean payload carries a module's
//! own rows explicitly (`clean_olean::CleanPayload::implemented_by_order`).

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, OnceLock};

use super::persistent_ext::{
    register_persistent_ext, ExtensionIdx, PersistentExtEntry, PersistentExtState,
};
use super::types::{ConstantKind, EnvExtensionEntry, EnvExtensionEntryData};
use super::Environment;
use crate::expr::UsedConstants;
use crate::name::Name;

/// The persisted name of the record's extension.
const ORDER_EXT_NAME: &str = "Clean.compiler.implementedByOrder";

/// Why a constant is in the order record: an `@[implemented_by]` binding
/// rebound a declaration its compiled code already reached.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompiledBefore {
    /// The declaration the binding rebound.
    pub rebound: Name,
    /// The constant this one's value names on its way to `rebound`:
    /// `rebound` itself for a direct reference, else a constant whose
    /// `@[implemented_by]` chain runs it or another recorded constant.
    pub via: Name,
}

/// One recorded constant.
#[derive(Debug, Clone)]
pub(crate) struct OrderEntry {
    referrer: Name,
    why: CompiledBefore,
}

impl PersistentExtEntry for OrderEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: self.referrer.clone(),
            data: EnvExtensionEntryData::Scalar(0),
        }
    }

    fn from_env_entry(_entry: &EnvExtensionEntry) -> Option<Self> {
        None
    }
}

/// The record of an environment. Nothing is exported (module docs).
#[derive(Debug, Clone, Default)]
pub(crate) struct OrderState {
    record: Arc<HashMap<Name, CompiledBefore>>,
}

impl PersistentExtState for OrderState {
    type Entry = OrderEntry;

    fn add_entry(&mut self, entry: &OrderEntry) {
        Arc::make_mut(&mut self.record).insert(entry.referrer.clone(), entry.why.clone());
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

static ORDER_IDX: OnceLock<ExtensionIdx> = OnceLock::new();

fn order_idx() -> ExtensionIdx {
    *ORDER_IDX
        .get_or_init(|| register_persistent_ext::<OrderState>(Name::from_string(ORDER_EXT_NAME)))
}

impl Environment {
    /// Add `found` (each constant and why) to the order record.
    pub fn record_compiled_before(&mut self, found: Vec<(Name, CompiledBefore)>) {
        for (referrer, why) in found {
            self.add_ext_entry::<OrderState>(order_idx(), &OrderEntry { referrer, why });
        }
    }

    /// The order record, keyed by the constant compiled too early; `None`
    /// when it is empty. Reading registers nothing: a record exists only once
    /// [`Self::record_compiled_before`] added one.
    #[must_use]
    pub fn compiled_before_record(&self) -> Option<&HashMap<Name, CompiledBefore>> {
        self.get_ext_state::<OrderState>(*ORDER_IDX.get()?)
            .map(|state| state.record.as_ref())
            .filter(|record| !record.is_empty())
    }

    /// The constants whose compiled code a binding of the declarations in
    /// `rebound` comes too late for, each with the declaration it reaches;
    /// `self` is the environment before the binding. With `scope`, only
    /// those constants are judged (an imported module's own constants: no
    /// other module's code can name a declaration it adds); without, every
    /// constant of `self`.
    ///
    /// Recorded, to a fixpoint, over the kernel values as written (no
    /// reduction): every value-bearing non-theorem constant whose value names
    /// a constant whose `@[implemented_by]` chain (it, its target, that
    /// target's, …) passes through `rebound` or through a constant already
    /// recorded. A theorem's value is a proof and never runs, and a constant
    /// whose own chain passes through `rebound` never runs its value after
    /// the binding, so neither is recorded. Auxiliary constants (`where`
    /// helpers, matchers) are judged like any other. Each round adds the
    /// constants one reference further out, judged against the record as the
    /// round before left it, so the result does not depend on scan order.
    ///
    /// The constants are scanned ONCE: a round judges only the constants
    /// that name something whose chain passes through what the round before
    /// recorded (the first round: through `rebound`). Every other constant
    /// keeps the answer it had, because a reference's chain changes only when
    /// a link of it joins the record, so the result is the one a rescan of
    /// every constant per round computes (`clean_elab`'s differential test
    /// against that rescan). Measured 2026-10-18, debug build, five commands
    /// after an `n`-deep caller chain over the builtin prelude: 26.3 s at
    /// `n` = 100 and 264.9 s at `n` = 800 with the rescan, 0.25 s and 0.32 s
    /// with this worklist.
    #[must_use]
    pub fn compiled_before_binding(
        &self,
        rebound: &HashSet<Name>,
        scope: Option<&HashSet<Name>>,
    ) -> Vec<(Name, CompiledBefore)> {
        let unrecorded = HashMap::new();
        let judged: Box<dyn Iterator<Item = &super::ConstantInfo>> = match scope {
            Some(names) => Box::new(names.iter().filter_map(|name| self.get_const(name))),
            None => Box::new(self.constants()),
        };
        // Each constant that may be recorded (a value-bearing non-theorem
        // whose own chain does not pass through `rebound`) with the constants
        // its value names, and each named constant with the constants that
        // name it.
        let mut uses: HashMap<&Name, HashSet<Name>> = HashMap::new();
        let mut named_by: HashMap<Name, Vec<&Name>> = HashMap::new();
        for info in judged {
            if info.kind == ConstantKind::Theorem {
                continue;
            }
            let Some(value) = &info.value else {
                continue;
            };
            if chain_reaches(self, rebound, &unrecorded, &info.name).is_some() {
                continue;
            }
            let mut used = HashSet::new();
            value.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
            for name in &used {
                named_by.entry(name.clone()).or_default().push(&info.name);
            }
            uses.insert(&info.name, used);
        }
        // Each link of a named constant's chain (it, its target, …, up to a
        // cycle) with the named constants whose chain passes through it.
        let mut through: HashMap<&Name, Vec<&Name>> = HashMap::new();
        for name in named_by.keys() {
            let mut visited: HashSet<&Name> = HashSet::new();
            let mut current = name;
            while visited.insert(current) {
                through.entry(current).or_default().push(name);
                match self.get_implemented_by(current) {
                    Some(next) => current = next,
                    None => break,
                }
            }
        }

        let mut recorded: HashMap<Name, CompiledBefore> = HashMap::new();
        let mut fresh: Vec<Name> = rebound.iter().cloned().collect();
        loop {
            let mut candidates: HashSet<&Name> = HashSet::new();
            for link in &fresh {
                for named in through.get(link).into_iter().flatten() {
                    for referrer in named_by.get(*named).into_iter().flatten() {
                        if !recorded.contains_key(*referrer) {
                            candidates.insert(*referrer);
                        }
                    }
                }
            }
            let mut round = Vec::new();
            for referrer in candidates {
                let reached = uses
                    .get(referrer)
                    .into_iter()
                    .flatten()
                    .filter_map(|name| {
                        chain_reaches(self, rebound, &recorded, name).map(|rebound| {
                            CompiledBefore {
                                rebound,
                                via: name.clone(),
                            }
                        })
                    })
                    .min_by_key(|why| (why.rebound.to_string(), why.via.to_string()));
                if let Some(why) = reached {
                    round.push((referrer.clone(), why));
                }
            }
            if round.is_empty() {
                break;
            }
            fresh = round.iter().map(|(referrer, _)| referrer.clone()).collect();
            recorded.extend(round);
        }
        let mut found: Vec<(Name, CompiledBefore)> = recorded.into_iter().collect();
        found.sort_by_key(|(referrer, _)| referrer.to_string());
        found
    }
}

/// The rebound declaration `name`'s `@[implemented_by]` chain reaches first:
/// walking `name` itself, then its target, and so on, the first link that is
/// a member of `rebound` or a constant already `recorded` (for which, the
/// declaration it was recorded for). A cycle ends the walk.
fn chain_reaches(
    env: &Environment,
    rebound: &HashSet<Name>,
    recorded: &HashMap<Name, CompiledBefore>,
    name: &Name,
) -> Option<Name> {
    let mut visited: HashSet<&Name> = HashSet::new();
    let mut current = name;
    loop {
        if rebound.contains(current) {
            return Some(current.clone());
        }
        if let Some(why) = recorded.get(current) {
            return Some(why.rebound.clone());
        }
        if !visited.insert(current) {
            return None;
        }
        current = env.get_implemented_by(current)?;
    }
}

#[cfg(test)]
#[path = "compiled_before_tests.rs"]
mod tests;
