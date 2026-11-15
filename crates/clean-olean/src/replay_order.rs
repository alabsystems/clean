// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's replay discipline for re-checking `.olean` declarations.
//!
//! The `.olean` re-check lanes (`verify_batch_full`, `clean mathverse
//! per-constant-verify`, `clean mathverse stamp-verified --parallel`) check a
//! module's declarations against an environment in which EVERY one of them is
//! already resident. Nothing stopped a declaration's value from mentioning
//! itself, or a module-mate whose own value mentions it. Measured 2026-09-23 on
//! a Lean-built `.olean` forged with `debug.skipKernelTC`: `forged3_self :
//! False := forged3_self` and the two-cycle `forged3_cycA := forged3_cycB`,
//! `forged3_cycB := forged3_cycA` were each stamped kernel-verified, while
//! `leanchecker` reports `(kernel) unknown constant 'forged3_self'`.
//!
//! This module is a port of `Lean.Environment.Replay.replayConstant`
//! (`src/lean/Lean/Replay.lean`, v4.30.0-rc2), the function `leanchecker`
//! runs. Lean adds each constant only AFTER its value checks, and before
//! adding it replays every constant it uses:
//!
//! ```text
//! partial def replayConstant (name : Name) : M Unit := do
//!   if ← isTodo name then                         -- remaining → pending
//!     let some ci := (← read).newConstants[name]? | unreachable!
//!     replayConstants ci.getUsedConstantsAsSet     -- dependencies first
//!     if (← get).pending.contains name then
//!       ... addDecl ...                            -- kernel check, then add
//! ```
//!
//! A reference to a constant that is still `pending` — the declaration itself,
//! or any member of a cycle through it — is skipped by `isTodo`, so the kernel
//! then meets a constant the environment does not hold and fails with
//! `unknown constant`. [`ReplayGraph::schedule`] runs that depth-first walk
//! over the module-LOCAL declarations (the imports are the trusted starting
//! environment, as in `replayFromImports`), and records exactly the
//! declarations Lean's kernel would refuse for that reason. The returned
//! [`ReplaySchedule::order`] lists every local declaration after all the local
//! declarations it uses, and [`ReplaySchedule::admission_gate`] refuses a
//! declaration whose local dependency was not admitted, which is what Lean's
//! replay does by aborting at the first failure.
//!
//! A mutual inductive block is ONE replay unit, as in Lean: `replayConstant`
//! of an `inductInfo` erases every type of the block from `pending`, replays
//! the constants all their constructors use, and sends one `inductDecl`. So
//! [`resident_refs`] gives every member of a block (types, constructors,
//! recursors) the union of the block's references minus the block itself: a
//! constructor mentioning its own type is no cycle, but a block whose
//! constructor mentions a definition that uses the block is one. Lean's
//! `replay` also never admits an `unsafe` or `partial` constant (it leaves
//! them out of `remaining`), so a safe declaration that uses one is refused.
//!
//! In a FIXED environment a declaration's kernel verdict does not depend on
//! which other declarations passed, so a caller may run the kernel checks in
//! any order (or in parallel) and combine them afterwards in `order()` —
//! [`ReplaySchedule::resolve`] does that. What makes the combination
//! Lean-faithful is that every local declaration a check can reach was
//! admitted first, and no check is ever satisfied by a declaration that
//! depends on it.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use clean_kernel::env::Environment;
use clean_kernel::expr::{Expr, UsedConstants};
use clean_kernel::name::Name;

/// Why a module-local declaration was not admitted by the replay discipline.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ReplayRefusal {
    /// The declaration's own type or value mentions it. Lean's replay skips
    /// the pending constant and its kernel then reports it unknown.
    #[error(
        "replay order: `{name}` refers to itself, and a declaration is not in the \
         environment while its own value is checked (Lean's replay: (kernel) unknown \
         constant '{name}')"
    )]
    SelfReference {
        /// The self-referential declaration.
        name: Name,
    },
    /// The declaration refers to `pending`, which is still being replayed: a
    /// dependency cycle through `name`.
    #[error(
        "replay order: `{name}` refers to `{pending}`, which is not admitted yet \
         (dependency cycle {cycle}; Lean's replay: (kernel) unknown constant '{pending}')"
    )]
    DependencyCycle {
        /// The declaration whose check would meet the pending constant.
        name: Name,
        /// The constant still being replayed.
        pending: Name,
        /// The cycle, rendered `a -> b -> a`.
        cycle: String,
    },
    /// A module-local declaration this one uses was not admitted.
    #[error("replay order: `{name}` depends on `{dependency}`, which was not admitted ({reason})")]
    DependsOnRefused {
        /// The dependent declaration.
        name: Name,
        /// The refused local dependency.
        dependency: Name,
        /// Why the dependency was refused.
        reason: String,
        /// The dependency was refused only because the heartbeat budget ran
        /// out (`ReplayRefusal::undecided`), and so was every other refused
        /// dependency: no finding stands behind this refusal.
        undecided: bool,
    },
    /// The declaration refers to a declaration of the replayed run that this
    /// replay does not admit: a module-mate that is not resident or was not
    /// replayed, or a declaration an earlier module of the same run refused. In
    /// Lean's replay it is not in the environment.
    #[error(
        "replay order: `{name}` refers to `{dependency}`, which this replay did not admit \
         (Lean's replay: (kernel) unknown constant '{dependency}')"
    )]
    DependsOnUnreplayed {
        /// The declaration being replayed.
        name: Name,
        /// The module-local declaration it mentions.
        dependency: Name,
    },
    /// The declaration is `unsafe` or `partial`. `Lean.Environment.replay`
    /// leaves both out of `remaining` (`!ci.isUnsafe && !ci.isPartial`), so
    /// neither is ever in the replay environment, and Lean's kernel bars a safe
    /// declaration from using one (`type_checker.cpp` `infer_constant`).
    #[error(
        "replay order: `{name}` is {safety}; Lean's replay does not admit {safety} \
         declarations, and no safe declaration may use one"
    )]
    NotReplayable {
        /// The unsafe or partial declaration.
        name: Name,
        /// `"unsafe"` or `"partial"`.
        safety: &'static str,
    },
    /// A value-bearing declaration has only its header resident. An elided
    /// proof or definition body cannot be kernel-replayed from its type alone.
    #[error("replay order: `{name}` has no stored value to replay")]
    MissingValue {
        /// The theorem, definition or opaque declaration with no body.
        name: Name,
    },
    /// The caller established that this replayed-run declaration was not
    /// admitted (for example a resident stub whose completion was refused).
    /// Residency cannot turn it back into an admitted local declaration.
    #[error("replay order: `{name}` was not admitted by the loader or an earlier replay")]
    NotAdmitted {
        /// The declaration whose resident representation is not authority.
        name: Name,
    },
    /// The declaration's name is already held by the environment it is
    /// replayed into: an import declares it, or another module of the run
    /// does, or the importer dropped this declaration in favour of a resident
    /// one. Lean's `addDecl` refuses a declaration whose name its environment
    /// holds, and a user of the name would otherwise be checked against a
    /// declaration that is not this module's.
    #[error(
        "replay order: `{name}` is already declared in the environment it is replayed \
         into ({reason}); Lean's replay refuses it (already declared)"
    )]
    AlreadyDeclared {
        /// The redeclared name.
        name: Name,
        /// Who holds it.
        reason: String,
    },
    /// A stored inductive type, constructor or recursor is not what the kernel
    /// generates from the block's stored types (Lean's replay:
    /// `checkPostponedConstructors` / `checkPostponedRecursors`, or the
    /// kernel's refusal of the rebuilt `inductDecl`).
    #[error("replay order: `{name}`: {reason}")]
    InductiveReplay {
        /// The refused family member.
        name: Name,
        /// The block replay's finding.
        reason: String,
    },
    /// The kernel rejected the declaration's own type or value.
    #[error("{message}")]
    KernelRejected {
        /// The rejected declaration.
        name: Name,
        /// The kernel's (or accounting's) message.
        message: String,
    },
    /// The kernel did not decide the declaration: every check of it that
    /// failed had spent its heartbeat budget when it failed. The kernel's
    /// `whnf`/`is_def_eq` stop silently once the budget is spent, so what such
    /// a check failed with (often a type mismatch) is no verdict that the
    /// declaration is ill-typed. Fail-closed: it is NOT admitted, and a
    /// declaration using it is refused as depending on it.
    #[error(
        "budget exhausted: `{name}` was not decided within the per-check heartbeat budget \
         ({limit}; 0 means only the ambient declaration budget), so it is not admitted; \
         this is no verdict that it is ill-typed: {message}"
    )]
    BudgetExhausted {
        /// The undecided declaration.
        name: Name,
        /// The checker's per-check heartbeat limit.
        limit: u32,
        /// What each starved check failed with.
        message: String,
    },
}

impl ReplayRefusal {
    /// The refusal is the heartbeat budget running out, not a finding: the
    /// declaration was not decided ([`Self::BudgetExhausted`]), or every
    /// dependency refusing it was in that state ([`Self::DependsOnRefused`]
    /// with `undecided`). Still not admitted.
    #[must_use]
    pub(crate) fn undecided(&self) -> bool {
        match self {
            Self::BudgetExhausted { .. } => true,
            Self::DependsOnRefused { undecided, .. } => *undecided,
            Self::SelfReference { .. }
            | Self::DependencyCycle { .. }
            | Self::DependsOnUnreplayed { .. }
            | Self::NotReplayable { .. }
            | Self::NotAdmitted { .. }
            | Self::MissingValue { .. }
            | Self::AlreadyDeclared { .. }
            | Self::InductiveReplay { .. }
            | Self::KernelRejected { .. } => false,
        }
    }
}

/// Every constant a type/value pair can make the kernel consult: Lean's
/// `getUsedConstants` (every `Const`), plus the structure of every `Proj`
/// node, whose declaration the kernel needs to type the projection. Walked as
/// a DAG (`Expr::used_constants_dag`).
#[must_use]
pub fn expr_refs(type_: &Expr, value: Option<&Expr>) -> BTreeSet<Name> {
    let mut found: HashSet<Name> = HashSet::new();
    type_.used_constants_dag(UsedConstants::WithProjectionStructures, &mut found);
    if let Some(value) = value {
        value.used_constants_dag(UsedConstants::WithProjectionStructures, &mut found);
    }
    found.into_iter().collect()
}

/// Everything a declaration resident in `env` mentions (see [`expr_refs`]).
///
/// A member of an inductive block — a type, a constructor, or a recursor —
/// gets the block's references as ONE unit: the types of every inductive of
/// the block and of their constructors (a recursor's type is built from those
/// and mentions nothing else), minus the block's own members. That is what Lean's `replayConstant` does for an `inductInfo`
/// before it sends the single `inductDecl`, so a constructor mentioning its own
/// type is no cycle, while a block whose constructor mentions a declaration
/// that uses the block is one.
#[must_use]
pub fn resident_refs(env: &Environment, name: &Name) -> BTreeSet<Name> {
    let mut found: HashSet<Name> = HashSet::new();
    let mut add =
        |e: &Expr| e.used_constants_dag(UsedConstants::WithProjectionStructures, &mut found);
    if let Some(ci) = env.get_const(name) {
        add(&ci.type_);
        if let Some(value) = &ci.value {
            add(value);
        }
    }
    let Some(block) = family_block(env, name) else {
        return found.into_iter().collect();
    };
    for ind_name in &block.types {
        if let Some(ind) = env.get_inductive(ind_name) {
            add(&ind.type_);
            for ctor in &ind.constructor_names {
                if let Some(cv) = env.get_constructor(ctor) {
                    add(&cv.type_);
                }
            }
        }
    }
    found
        .into_iter()
        .filter(|r| !block.contains(env, r))
        .collect()
}

/// The inductive block a type, constructor or recursor belongs to.
struct FamilyBlock {
    types: Vec<Name>,
}

impl FamilyBlock {
    fn contains(&self, env: &Environment, r: &Name) -> bool {
        self.types.contains(r)
            || env
                .get_constructor(r)
                .is_some_and(|cv| self.types.contains(&cv.inductive_name))
            || env
                .get_recursor(r)
                .is_some_and(|rv| self.types.contains(&rv.inductive_name))
    }
}

fn family_block(env: &Environment, name: &Name) -> Option<FamilyBlock> {
    let inductive = if env.get_inductive(name).is_some() {
        name.clone()
    } else if let Some(cv) = env.get_constructor(name) {
        cv.inductive_name.clone()
    } else {
        env.get_recursor(name)?.inductive_name.clone()
    };
    let types = env
        .get_inductive(&inductive)
        .map(|ind| ind.all_names.clone())
        .filter(|all| !all.is_empty())
        .unwrap_or_else(|| vec![inductive.clone()]);
    Some(FamilyBlock { types })
}

/// The module-local declarations of one replay and the constants each uses.
#[derive(Debug, Default, Clone)]
pub struct ReplayGraph {
    nodes: BTreeMap<Name, BTreeSet<Name>>,
    refusals: BTreeMap<Name, ReplayRefusal>,
    /// Declarations of the replayed run that are NOT nodes: a node that
    /// mentions one is refused (fail-closed), where a reference to any other
    /// non-node belongs to the trusted imports.
    unreplayed: BTreeSet<Name>,
}

impl ReplayGraph {
    /// An empty graph.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a local declaration with every constant its type and value use.
    /// References to non-local constants are kept here and ignored by the
    /// schedule: they belong to the trusted starting environment.
    pub fn insert(&mut self, name: Name, refs: impl IntoIterator<Item = Name>) {
        self.nodes.entry(name).or_default().extend(refs);
    }

    /// Refuse `name` before any check for a reason the caller established
    /// (e.g. [`ReplayRefusal::NotReplayable`]). The first refusal recorded wins.
    pub fn refuse(&mut self, name: Name, refusal: ReplayRefusal) {
        self.refusals.entry(name).or_insert(refusal);
    }

    /// Record that the replayed run declares `name` but this replay does not
    /// admit it (absent from the environment, not selected, or refused by an
    /// earlier module of the same run). A node whose type or value mentions it
    /// is refused with [`ReplayRefusal::DependsOnUnreplayed`]: in Lean's replay
    /// it would not be in the environment.
    ///
    /// Compared as a [`Name`] against the `Const` names the node's type and
    /// value carry. A caller holding only a display spelling must convert it
    /// with the conversion the `.olean` loader itself applies
    /// (`Name::from_string`, which `Name::interned` equals), so the set holds
    /// exactly the names the resident references carry. A conversion that
    /// produced a DIFFERENT name would make the reference miss this set and be
    /// served as a trusted import, which UNDER-refuses; there is no spelling
    /// comparison left that could fail in the safe direction only.
    pub fn mark_unreplayed(&mut self, name: Name) {
        self.unreplayed.insert(name);
    }

    /// Whether `name` is a local declaration of this replay.
    #[must_use]
    pub fn contains(&self, name: &Name) -> bool {
        self.nodes.contains_key(name)
    }

    /// Every constant `name` uses, local or not.
    pub fn refs(&self, name: &Name) -> impl Iterator<Item = &Name> {
        self.nodes.get(name).into_iter().flatten()
    }

    /// Run Lean's `replayConstant` walk over the local declarations, in name
    /// order, iteratively (a Mathlib module's dependency chains are far deeper
    /// than a thread stack).
    #[must_use]
    pub fn schedule(&self) -> ReplaySchedule {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Mark {
            Pending,
            Done,
        }
        let local_refs: BTreeMap<Name, Vec<Name>> = self
            .nodes
            .iter()
            .map(|(name, refs)| {
                let local = refs.iter().filter(|r| self.nodes.contains_key(*r)).cloned();
                (name.clone(), local.collect())
            })
            .collect();
        let mut marks: BTreeMap<Name, Mark> = BTreeMap::new();
        let mut order: Vec<Name> = Vec::with_capacity(local_refs.len());
        let mut structural = self.refusals.clone();
        if !self.unreplayed.is_empty() {
            for (name, refs) in &self.nodes {
                let missing = refs
                    .iter()
                    .find(|r| !self.nodes.contains_key(*r) && self.unreplayed.contains(*r));
                if let Some(dependency) = missing {
                    structural.entry(name.clone()).or_insert_with(|| {
                        ReplayRefusal::DependsOnUnreplayed {
                            name: name.clone(),
                            dependency: dependency.clone(),
                        }
                    });
                }
            }
        }
        for root in local_refs.keys() {
            if marks.contains_key(root) {
                continue;
            }
            marks.insert(root.clone(), Mark::Pending);
            let mut stack: Vec<(Name, usize)> = vec![(root.clone(), 0)];
            while let Some((node, next)) = stack.last_mut() {
                let refs = local_refs.get(node).map_or(&[][..], Vec::as_slice);
                let Some(r) = refs.get(*next).cloned() else {
                    let done = node.clone();
                    marks.insert(done.clone(), Mark::Done);
                    order.push(done);
                    stack.pop();
                    continue;
                };
                *next += 1;
                match marks.get(&r) {
                    None => {
                        marks.insert(r.clone(), Mark::Pending);
                        stack.push((r, 0));
                    }
                    Some(Mark::Pending) => {
                        let current = node.clone();
                        let refusal = if r == current {
                            ReplayRefusal::SelfReference {
                                name: current.clone(),
                            }
                        } else {
                            let start = stack.iter().position(|(n, _)| *n == r).unwrap_or(0);
                            let mut path: Vec<String> =
                                stack[start..].iter().map(|(n, _)| n.to_string()).collect();
                            path.push(r.to_string());
                            ReplayRefusal::DependencyCycle {
                                name: current.clone(),
                                pending: r,
                                cycle: path.join(" -> "),
                            }
                        };
                        structural.entry(current).or_insert(refusal);
                    }
                    Some(Mark::Done) => {}
                }
            }
        }
        ReplaySchedule {
            order,
            structural,
            local_refs,
        }
    }
}

/// The verdicts recorded so far in one replay.
pub type ReplayVerdicts = BTreeMap<Name, Result<(), ReplayRefusal>>;

/// The outcome of [`ReplayGraph::schedule`]: an admission order and the
/// declarations refused before any kernel check.
#[derive(Debug, Clone)]
pub struct ReplaySchedule {
    order: Vec<Name>,
    structural: BTreeMap<Name, ReplayRefusal>,
    local_refs: BTreeMap<Name, Vec<Name>>,
}

impl ReplaySchedule {
    /// Every local declaration, each after the local declarations it uses.
    #[must_use]
    pub fn order(&self) -> &[Name] {
        &self.order
    }

    /// The refusal fixed before any kernel check (self-reference, cycle, or a
    /// caller-established refusal), if any. Only the unit tests read it; the
    /// lanes consume [`Self::structurally_doomed`] and the admission gate.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn structural_refusal(&self, name: &Name) -> Option<&ReplayRefusal> {
        self.structural.get(name)
    }

    /// Whether `name` may reach the kernel given the verdicts recorded so far.
    /// Call it in [`Self::order`], after recording every earlier declaration.
    ///
    /// # Errors
    /// The refusal that keeps `name` out of the environment: a structural one,
    /// or [`ReplayRefusal::DependsOnRefused`] for the first local dependency
    /// that was not admitted on a finding, or, when every one that was not
    /// admitted is `ReplayRefusal::undecided`, for the first of those (then
    /// itself undecided). A dependency with no recorded verdict yet is treated
    /// as not admitted on a finding (fail-closed).
    pub fn admission_gate(
        &self,
        name: &Name,
        verdicts: &ReplayVerdicts,
    ) -> Result<(), ReplayRefusal> {
        if let Some(refusal) = self.structural.get(name) {
            return Err(refusal.clone());
        }
        let refusal =
            |dep: &Name, reason: String, undecided: bool| ReplayRefusal::DependsOnRefused {
                name: name.clone(),
                dependency: dep.clone(),
                reason,
                undecided,
            };
        let mut undecided = None;
        for dep in self.local_refs.get(name).map_or(&[][..], Vec::as_slice) {
            match verdicts.get(dep) {
                Some(Ok(())) => {}
                Some(Err(why)) if why.undecided() => {
                    if undecided.is_none() {
                        undecided = Some(refusal(dep, why.to_string(), true));
                    }
                }
                Some(Err(why)) => return Err(refusal(dep, why.to_string(), false)),
                None => {
                    return Err(refusal(
                        dep,
                        "no verdict recorded before its dependent".to_owned(),
                        false,
                    ))
                }
            }
        }
        undecided.map_or(Ok(()), Err)
    }

    /// The local declarations `roots` reach through local references, roots
    /// included: the only ones a replay of `roots` needs to check.
    #[must_use]
    pub(crate) fn local_closure<'a>(
        &self,
        roots: impl IntoIterator<Item = &'a Name>,
    ) -> BTreeSet<Name> {
        let mut seen: BTreeSet<Name> = BTreeSet::new();
        let mut stack: Vec<&Name> = roots.into_iter().collect();
        while let Some(name) = stack.pop() {
            if !self.local_refs.contains_key(name) || !seen.insert(name.clone()) {
                continue;
            }
            stack.extend(self.local_refs.get(name).map_or(&[][..], Vec::as_slice));
        }
        seen
    }

    /// Declarations that cannot be admitted whatever the kernel says: the
    /// structurally refused ones and every declaration that transitively uses
    /// one. A caller may skip their kernel checks.
    #[must_use]
    pub(crate) fn structurally_doomed(&self) -> BTreeSet<Name> {
        let mut doomed: BTreeSet<Name> = BTreeSet::new();
        for name in &self.order {
            let dead = self.structural.contains_key(name)
                || self
                    .local_refs
                    .get(name)
                    .is_some_and(|deps| deps.iter().any(|d| doomed.contains(d)));
            if dead {
                doomed.insert(name.clone());
            }
        }
        doomed
    }

    /// Combine kernel verdicts in replay order. `kernel` is called, in
    /// [`Self::order`], only for declarations that pass the admission gate;
    /// it returns the kernel's message on rejection.
    pub fn resolve(&self, mut kernel: impl FnMut(&Name) -> Result<(), String>) -> ReplayVerdicts {
        self.resolve_typed(|name| {
            kernel(name).map_err(|message| ReplayRefusal::KernelRejected {
                name: name.clone(),
                message,
            })
        })
    }

    /// Combine typed kernel verdicts through the same admission gate, retaining
    /// budget exhaustion as undecided when refusing dependent declarations.
    pub(crate) fn resolve_typed(
        &self,
        mut kernel: impl FnMut(&Name) -> Result<(), ReplayRefusal>,
    ) -> ReplayVerdicts {
        let mut verdicts = ReplayVerdicts::new();
        for name in &self.order {
            let verdict = self
                .admission_gate(name, &verdicts)
                .and_then(|()| kernel(name));
            verdicts.insert(name.clone(), verdict);
        }
        verdicts
    }
}

#[cfg(test)]
#[path = "replay_order_tests.rs"]
mod tests;
