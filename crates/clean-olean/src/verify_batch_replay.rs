// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The replay-ordered body of every `verify_batch_full` entry point.
//!
//! The environment a caller supplies holds every target (and every
//! prerequisite) already. Checking each in isolation against it let a value
//! lean on itself or on a module-mate that leans back on it, so the re-check
//! lanes stamped `forged3_self : False := forged3_self` kernel-verified
//! (measured 2026-09-23; `leanchecker`: `(kernel) unknown constant`). Here the
//! checked declarations are replayed the way `Lean.Environment.replay` does it
//! (`crate::replay_order`): dependencies first, a pending constant is not in
//! the environment, and a dependent of a refused declaration is refused.
//! Everything outside the checked set is the trusted starting environment,
//! as the imports are for Lean's `replayFromImports`.
//!
//! Every check runs in [`KernelTheory::Lean`](clean_kernel::env::KernelTheory::Lean)
//! (`clean_kernel::env::kernel_theory`): these lanes re-check Lean-built
//! `.olean`s, so a native reducer may only accelerate a δ-unfolding Lean's
//! kernel performs itself, and only one a differential battery has checked
//! against δι. Each check runs on a [`ReplayChecker`], which is replaced after
//! any check that spent its heartbeat budget, so no starved check's memoised
//! answers decide a later one.
//!
//! Two more of Lean's replay rules apply to the checked declarations. A stored
//! inductive block is rebuilt by the kernel from its stored types, and every
//! stored constructor and recursor must be the regenerated one
//! (`crate::replay_families`); and a declaration whose name the environment
//! already held before its module was added is refused as already declared
//! ([`ReplayScope::already_declared`]), since what the environment holds under
//! that name is not this module's declaration.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::{ConstantKind, Environment, ProofElisionStats, ProofValueElision};
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;

use super::local_roster::{self, CheckProblem, LocalCheckRoster, LocalDeclaration, ReplayChecker};
use crate::replay_families::inductive_block_refusals;
use crate::replay_order::{
    resident_refs, ReplayGraph, ReplayRefusal, ReplaySchedule, ReplayVerdicts,
};

/// The typed declarations of one replay: the requested targets (counted in the
/// result) and their prerequisites (checked and admitted in order, never
/// counted), with their schedule and the subset of it the targets reach.
struct ReplayPlan {
    targets: LocalCheckRoster,
    prerequisites: LocalCheckRoster,
    schedule: ReplaySchedule,
    /// The scheduled declarations to check, in replay order: the targets and
    /// the local declarations they reach (a prerequisite nothing requested
    /// uses is never checked).
    order: Vec<Name>,
    /// Inductive-family members of `order` whose block Lean's replay would not
    /// admit (`crate::replay_families`): refused instead of type-checked.
    families: BTreeMap<Name, ReplayRefusal>,
}

impl ReplayPlan {
    fn new(env: &Environment, targets: &BTreeSet<String>, scope: &ReplayScope<'_>) -> Self {
        let prerequisites = scope.prerequisites;
        let not_admitted = scope.not_admitted;
        let target_roster = local_roster::resolve_targets(env, targets);
        let prereq_labels: BTreeSet<String> = prerequisites.difference(targets).cloned().collect();
        let prereq_roster = local_roster::resolve_targets(env, &prereq_labels);
        let mut graph = ReplayGraph::new();
        for name in target_roster
            .declarations
            .keys()
            .chain(prereq_roster.declarations.keys())
        {
            graph.insert(name.clone(), resident_refs(env, name));
            // `Lean.Environment.replay` leaves unsafe and partial constants out
            // of `remaining` (`!ci.isUnsafe && !ci.isPartial`), so neither is
            // ever admitted. The loaders mark them (`load_register.rs`
            // `apply_declaration_safety_marks`).
            let safety = if env.is_unsafe(name) {
                Some("unsafe")
            } else if env.is_partial(name) {
                Some("partial")
            } else {
                None
            };
            if let Some(safety) = safety {
                graph.refuse(
                    name.clone(),
                    ReplayRefusal::NotReplayable {
                        name: name.clone(),
                        safety,
                    },
                );
            }
        }
        // Primitive family mirrors have no ordinary body. Every other
        // definition, opaque constant or theorem must supply its stored value;
        // a successful header check alone is not a replayed declaration.
        for name in target_roster
            .declarations
            .keys()
            .chain(prereq_roster.declarations.keys())
        {
            if env.get_inductive(name).is_none()
                && env.get_constructor(name).is_none()
                && env.get_recursor(name).is_none()
                && env.get_const(name).is_some_and(|row| {
                    row.value.is_none()
                        && matches!(
                            row.kind,
                            ConstantKind::Definition | ConstantKind::Opaque | ConstantKind::Theorem
                        )
                })
            {
                graph.refuse(
                    name.clone(),
                    ReplayRefusal::MissingValue { name: name.clone() },
                );
            }
        }
        // A requested label with no resident declaration is still a
        // declaration of the replayed module: a node that mentions it is
        // refused, never served by whatever else is resident.
        let resolved: BTreeSet<String> = target_roster
            .declarations
            .keys()
            .chain(prereq_roster.declarations.keys())
            .map(ToString::to_string)
            .collect();
        // A label is an `.olean` name spelling; `Name::from_string` is the
        // conversion the loader registers declarations and references under
        // (`replay_order::ReplayGraph::mark_unreplayed`).
        for label in targets.iter().chain(prereq_labels.iter()) {
            if !resolved.contains(label) {
                graph.mark_unreplayed(Name::from_string(label));
            }
        }
        // A loader refusal or earlier replay refusal is binding even when a
        // target/prerequisite has a resident representation (notably a stub).
        // Keep the node and its references, but refuse it before scheduling so
        // direct and transitive dependents cannot use its resident authority.
        for name in target_roster
            .declarations
            .keys()
            .chain(prereq_roster.declarations.keys())
        {
            if not_admitted.contains(&name.to_string()) {
                graph.refuse(
                    name.clone(),
                    ReplayRefusal::NotAdmitted { name: name.clone() },
                );
            }
        }
        for label in not_admitted {
            if !resolved.contains(label) {
                graph.mark_unreplayed(Name::from_string(label));
            }
        }
        // Declarations the caller established are already declared in the
        // environment this replay runs in (`ReplayScope::already_declared`).
        for name in target_roster
            .declarations
            .keys()
            .chain(prereq_roster.declarations.keys())
        {
            if let Some(reason) = scope.already_declared.get(&name.to_string()) {
                graph.refuse(
                    name.clone(),
                    ReplayRefusal::AlreadyDeclared {
                        name: name.clone(),
                        reason: reason.clone(),
                    },
                );
            }
        }
        // The replay's declarations, resident or not: a declared label with no
        // resident declaration (a family record the loader refused) still
        // names a member of its block, which then refuses the whole block.
        // Such a label arrives as a requested target (`verify-batch` requests
        // every name the module declares) or as not admitted (`clean olean
        // replay` refuses the loader's refusals itself and passes them here);
        // either way it is the replayed run's. Only a NON-resident
        // not-admitted label is added: a resident one is an earlier module's
        // declaration, which no block of this replay contains.
        let absent_not_admitted = not_admitted
            .iter()
            .filter(|label| !resolved.contains(*label))
            .map(|label| Name::from_string(label))
            .filter(|name| {
                env.get_const(name).is_none()
                    && env.get_inductive(name).is_none()
                    && env.get_constructor(name).is_none()
                    && env.get_recursor(name).is_none()
            });
        let all_local: BTreeSet<Name> = target_roster
            .declarations
            .keys()
            .chain(prereq_roster.declarations.keys())
            .cloned()
            .chain(
                targets
                    .iter()
                    .chain(prereq_labels.iter())
                    .filter(|label| !resolved.contains(*label))
                    .map(|label| Name::from_string(label)),
            )
            .chain(absent_not_admitted)
            .collect();
        let schedule = graph.schedule();
        let needed = schedule.local_closure(target_roster.declarations.keys());
        let order: Vec<Name> = schedule
            .order()
            .iter()
            .filter(|name| needed.contains(*name))
            .cloned()
            .collect();
        let families = inductive_block_refusals(env, &all_local, &needed);
        Self {
            schedule,
            order,
            families,
            targets: target_roster,
            prerequisites: prereq_roster,
        }
    }

    fn declaration(&self, name: &Name) -> Option<&LocalDeclaration> {
        self.targets
            .declarations
            .get(name)
            .or_else(|| self.prerequisites.declarations.get(name))
    }

    /// Fold replay refusals into the per-declaration problem lists, then count
    /// the TARGETS only.
    fn finish(
        &self,
        mut checks: BTreeMap<Name, Vec<String>>,
        verdicts: &ReplayVerdicts,
    ) -> (usize, usize, BTreeMap<String, String>) {
        for (name, verdict) in verdicts {
            // A kernel rejection's or budget exhaustion's problems (or its
            // accounting error) are already recorded; every other refusal is
            // new information.
            if let Err(refusal) = verdict {
                if !matches!(
                    refusal,
                    ReplayRefusal::KernelRejected { .. } | ReplayRefusal::BudgetExhausted { .. }
                ) {
                    checks
                        .entry(name.clone())
                        .or_default()
                        .push(refusal.to_string());
                }
            }
        }
        self.targets.finish(&checks)
    }
}

/// What a replay of some targets knows besides them: module-mates checked
/// first (`prerequisites`), names an earlier module of the same run refused
/// (`not_admitted`), and declarations of the replayed module whose name the
/// environment already held before the module was added (`already_declared`,
/// display spelling to who holds it). All keys are display spellings, like the
/// targets.
#[derive(Clone, Copy)]
pub struct ReplayScope<'a> {
    /// Module-mates admitted in replay order before any target that uses them,
    /// never counted.
    pub prerequisites: &'a BTreeSet<String>,
    /// Declarations of the replayed run this replay does not admit: refused by
    /// an earlier module of the same run, or not registered completely by the
    /// loader. This also refuses RESIDENT target/prerequisite representations,
    /// such as incomplete stubs; every dependent is refused. A non-resident
    /// member of an inductive block of this replay still refuses the block.
    pub not_admitted: &'a BTreeSet<String>,
    /// Declarations Lean's `addDecl` would refuse as already declared: an
    /// import (or another module of the run) holds the name, so the resident
    /// declaration of that name is not this module's.
    pub already_declared: &'a BTreeMap<String, String>,
}

/// Every represented type, then the value when the types checked.
///
/// Lean's `environment::add_theorem` (`src/kernel/environment.cpp`, v4.30.0-rc2,
/// lines 192-209) also requires a theorem's type to be a proposition
/// (`if (!checker.is_prop(type)) throw theorem_type_is_not_prop`), a check the
/// sort pass alone does not make: `forged_thm_nat : Nat := Nat.zero`, written
/// as a `thmInfo` with the kernel bypassed, passed both `infer_sort` and
/// `check_type`. Nor does it make `check_constant_val`'s `ensure_sort` (see
/// [`header_problem`]). The loader's structural tier already refuses the other
/// header checks of `check_constant_val` (duplicate universe parameters,
/// metavariables, free variables, undeclared universe parameters).
fn check_declaration(
    checker: &mut ReplayChecker<'_>,
    env: &Environment,
    name: &Name,
    declaration: &LocalDeclaration,
) -> Vec<CheckProblem> {
    let mut problems = declaration.check_sorts(checker);
    if problems.is_empty() {
        if let Some(error) = header_problem(checker, env, name) {
            problems.push(error);
        }
    }
    if problems.is_empty() && declaration.has_value() {
        if let Some(error) = local_roster::check_value(checker, env, name) {
            problems.push(error);
        }
    }
    problems
}

/// Lean's two header checks on a declaration's TYPE that `check_sorts` does
/// not make, both read off the same inferred sort (`src/kernel/environment.cpp`,
/// v4.30.0-rc2): `check_constant_val`'s `ensure_sort(checker.check(type))` —
/// the type's own type must reduce to a `Sort` — and, for a theorem,
/// `add_theorem`'s `is_prop(type)` (`whnf(infer_type(type)) == Prop`).
///
/// `check_sorts` runs `TypeChecker::infer_sort`, which also answers for a term
/// whose type is a FUNCTION type (its Pi fallback returns the `imax` of that
/// function type's sorts), so a declaration whose "type" is a lambda passed it.
/// Measured 2026-09-26 with the pinned `leanchecker`: `axiom rev_lam_ax : fun
/// (h : True) => h` is refused `(kernel) type expected`, while every
/// `verify_batch_full` lane, `clean olean replay` included, admitted it and a
/// theorem stated by it.
///
/// One known divergence stays, in the permissive direction and harmless in
/// meaning: Lean compares the sort with `Prop` STRUCTURALLY, so a theorem whose
/// type's sort is `max 0 0` (a `Sort (max 0 0)` binder, which Lean's level
/// smart constructors never rebuild) is refused there ("not a proposition") and
/// admitted here, where the level is compared up to normalisation, as Clean's
/// own `add_decl` does. Clean's inference does not build levels with Lean's
/// smart constructors, so a structural test here would refuse honest theorems.
fn header_problem(
    checker: &mut ReplayChecker<'_>,
    env: &Environment,
    name: &Name,
) -> Option<CheckProblem> {
    checker.check(|tc| header_failure(tc, env, name).map_or(Ok(()), Err))
}

/// [`header_problem`]'s check on one checker: `Some` with what it failed with.
fn header_failure(tc: &TypeChecker<'_>, env: &Environment, name: &Name) -> Option<String> {
    let constant = env.get_const(name)?;
    let sort_of_type = match tc.infer_type(&constant.type_) {
        Ok(ty) => tc.whnf(&ty),
        Err(error) => return Some(format!("infer_type: declaration type: {error:?}")),
    };
    let sort = match sort_of_type.kind() {
        ExprKind::Sort(level) => level.clone(),
        // `infer_sort`'s own reading; no Lean `.olean` decodes to `SProp`.
        ExprKind::SProp => Level::zero(),
        _ => {
            return Some(format!(
                "type expected: the declaration's type has type `{sort_of_type:?}`, not a \
                 sort (Lean's check_constant_val: ensure_sort)"
            ))
        }
    };
    if constant.kind == ConstantKind::Theorem && !(sort.is_zero() || sort.normalize().is_zero()) {
        return Some(format!(
            "theorem type is not a proposition: its sort is `Sort {sort:?}` (Lean's \
             add_theorem: theorem_type_is_not_prop)"
        ));
    }
    None
}

/// One gated step: refuse, or run the kernel and record its problems.
fn replay_one(
    plan: &ReplayPlan,
    checker: &mut ReplayChecker<'_>,
    env: &Environment,
    name: &Name,
    verdicts: &ReplayVerdicts,
    checks: &mut BTreeMap<Name, Vec<String>>,
) -> Result<(), ReplayRefusal> {
    plan.schedule.admission_gate(name, verdicts)?;
    if let Some(refusal) = plan.families.get(name) {
        return Err(refusal.clone());
    }
    let Some(declaration) = plan.declaration(name) else {
        return Err(ReplayRefusal::KernelRejected {
            name: name.clone(),
            message: "replay order: scheduled declaration has no typed row".to_owned(),
        });
    };
    let problems = check_declaration(checker, env, name, declaration);
    let verdict = verdict_of(
        name,
        &problems,
        declaration.accounting_valid(),
        checker.heartbeat_limit(),
    );
    checks.insert(
        name.clone(),
        problems.iter().map(CheckProblem::report).collect(),
    );
    verdict
}

/// A checked declaration's verdict from what its checks failed with.
///
/// Admitted when no check failed and its registry accounting is valid. Not
/// decided, [`ReplayRefusal::BudgetExhausted`], only when EVERY failed check
/// had spent its budget (and the accounting is valid): one failure with budget
/// to spare is the kernel's verdict, [`ReplayRefusal::KernelRejected`], and so
/// is invalid accounting. Neither refusal is admitted.
fn verdict_of(
    name: &Name,
    problems: &[CheckProblem],
    accounting_valid: bool,
    limit: u32,
) -> Result<(), ReplayRefusal> {
    if problems.is_empty() {
        return if accounting_valid {
            Ok(())
        } else {
            Err(ReplayRefusal::KernelRejected {
                name: name.clone(),
                message: "registry accounting is not valid for this declaration".to_owned(),
            })
        };
    }
    if accounting_valid && problems.iter().all(CheckProblem::budget_spent) {
        let errors: Vec<&str> = problems.iter().map(CheckProblem::error).collect();
        return Err(ReplayRefusal::BudgetExhausted {
            name: name.clone(),
            limit,
            message: errors.join("; "),
        });
    }
    let reports: Vec<String> = problems.iter().map(CheckProblem::report).collect();
    Err(ReplayRefusal::KernelRejected {
        name: name.clone(),
        message: reports.join("; "),
    })
}

/// Run the eager replay of `plan`: one long-lived checker over the fixed
/// environment (replaced only after a check that spent its budget), every
/// scheduled declaration in replay order.
fn run_eager(
    plan: &ReplayPlan,
    env: &Environment,
    max_heartbeats: u32,
) -> (BTreeMap<Name, Vec<String>>, ReplayVerdicts) {
    let mut checker = ReplayChecker::new(env, max_heartbeats);
    let mut checks = BTreeMap::new();
    let mut verdicts = ReplayVerdicts::new();
    for name in &plan.order {
        let verdict = replay_one(plan, &mut checker, env, name, &verdicts, &mut checks);
        verdicts.insert(name.clone(), verdict);
    }
    (checks, verdicts)
}

/// Eager replay: one long-lived checker over the fixed environment.
pub(super) fn full(
    env: &Environment,
    targets: &BTreeSet<String>,
    scope: &ReplayScope<'_>,
    max_heartbeats: u32,
) -> (usize, usize, BTreeMap<String, String>) {
    let plan = ReplayPlan::new(env, targets, scope);
    let (checks, verdicts) = run_eager(&plan, env, max_heartbeats);
    plan.finish(checks, &verdicts)
}

/// An eager replay's outcome with every scheduled declaration's verdict in
/// replay order, for a caller that reports the FIRST refusal the way
/// `leanchecker` does (`clean olean replay`, and the NDJSON front door).
pub(crate) struct OrderedReplay {
    /// Typed registry inconsistencies, even when safety refuses the node first.
    pub(crate) accounting_invalid: BTreeSet<Name>,
    /// Every scheduled declaration, in Lean's replay order, with its verdict.
    pub(crate) verdicts: Vec<(Name, Result<(), ReplayRefusal>)>,
    /// Targets admitted.
    pub(crate) pass: usize,
    /// Targets refused, including requested labels with no resident
    /// declaration and labels whose registry rows disagree.
    pub(crate) fail: usize,
    /// Every target's problems, by display name.
    pub(crate) errors: BTreeMap<String, String>,
}

/// [`full`], keeping each verdict in replay order.
pub(crate) fn full_ordered(
    env: &Environment,
    targets: &BTreeSet<String>,
    scope: &ReplayScope<'_>,
    max_heartbeats: u32,
) -> OrderedReplay {
    let plan = ReplayPlan::new(env, targets, scope);
    let (checks, verdicts) = run_eager(&plan, env, max_heartbeats);
    let ordered = plan
        .order
        .iter()
        .filter_map(|name| verdicts.get(name).map(|v| (name.clone(), v.clone())))
        .collect();
    let (pass, fail, errors) = plan.finish(checks, &verdicts);
    let accounting_invalid = plan
        .targets
        .declarations
        .iter()
        .filter(|(_, declaration)| !declaration.accounting_valid())
        .map(|(name, _)| name.clone())
        .collect();
    OrderedReplay {
        accounting_invalid,
        verdicts: ordered,
        pass,
        fail,
        errors,
    }
}

/// Streaming replay: the same order and gate, with the checker rebuilt every
/// `chunk_len` declarations so the just-admitted elidable proof values can be
/// freed (strictly post-success, as before: a value is dropped only after its
/// own check passed and its verdict was recorded).
pub(super) fn streaming(
    env: &mut Environment,
    targets: &BTreeSet<String>,
    scope: ReplayScope<'_>,
    max_heartbeats: u32,
    elide: ProofValueElision,
    chunk_len: usize,
) -> (usize, usize, BTreeMap<String, String>, ProofElisionStats) {
    let plan = ReplayPlan::new(env, targets, &scope);
    let order: Vec<Name> = plan.order.clone();
    let mut checks = BTreeMap::new();
    let mut verdicts = ReplayVerdicts::new();
    let mut stats = ProofElisionStats::default();
    for chunk in order.chunks(chunk_len.max(1)) {
        let mut to_free = Vec::new();
        {
            let mut checker = ReplayChecker::new(env, max_heartbeats);
            for name in chunk {
                let verdict = replay_one(&plan, &mut checker, env, name, &verdicts, &mut checks);
                if verdict.is_ok() && env.get_const(name).is_some_and(|ci| elide.elides(ci.kind)) {
                    to_free.push(name.clone());
                }
                verdicts.insert(name.clone(), verdict);
            }
        }
        let chunk_stats = env.forget_proof_values_for(to_free.iter(), elide);
        stats.opaque_elided += chunk_stats.opaque_elided;
        stats.theorem_elided += chunk_stats.theorem_elided;
        stats.retained += chunk_stats.retained;
        // The next chunk constructs a new checker. The lazy source's fresh
        // cache contract requires byte-identical materialized constants.
        env.refresh_constant_source_cache();
    }
    let (pass, fail, errors) = plan.finish(checks, &verdicts);
    (pass, fail, errors, stats)
}

/// Parallel replay: the kernel checks of every declaration not doomed by the
/// schedule run concurrently (in a fixed environment a check's verdict does
/// not depend on any other check), then the verdicts are combined in replay
/// order — identical to [`full`].
pub(crate) fn parallel(
    env: &Environment,
    targets: &BTreeSet<String>,
    scope: &ReplayScope<'_>,
    pool: &rayon::ThreadPool,
    max_heartbeats: u32,
) -> (usize, usize, BTreeMap<String, String>) {
    let plan = ReplayPlan::new(env, targets, scope);
    let (checks, verdicts) = run_parallel(&plan, env, pool, max_heartbeats);
    plan.finish(checks, &verdicts)
}

/// Keep typed kernel problems until replay-order admission has propagated the
/// same budget/refusal distinction as the serial lane.
fn run_parallel(
    plan: &ReplayPlan,
    env: &Environment,
    pool: &rayon::ThreadPool,
    max_heartbeats: u32,
) -> (BTreeMap<Name, Vec<String>>, ReplayVerdicts) {
    use rayon::prelude::*;
    let doomed = plan.schedule.structurally_doomed();
    let candidates: Vec<(&Name, &LocalDeclaration)> = plan
        .targets
        .declarations
        .iter()
        .filter(|(name, _)| !doomed.contains(*name) && !plan.families.contains_key(*name))
        .collect();
    let kernel: BTreeMap<Name, Vec<CheckProblem>> = pool.install(|| {
        candidates
            .par_iter()
            .map_init(
                || ReplayChecker::new(env, max_heartbeats),
                |checker, (name, row)| {
                    let problems = check_declaration(checker, env, name, row);
                    ((*name).clone(), problems)
                },
            )
            .collect()
    });
    let mut checks = BTreeMap::new();
    let verdicts = plan.schedule.resolve_typed(|name| {
        if let Some(refusal) = plan.families.get(name) {
            return Err(refusal.clone());
        }
        let Some(problems) = kernel.get(name) else {
            return Err(ReplayRefusal::KernelRejected {
                name: name.clone(),
                message: "replay order: declaration was not checked".to_owned(),
            });
        };
        checks.insert(
            name.clone(),
            problems.iter().map(CheckProblem::report).collect(),
        );
        let accounting = plan
            .declaration(name)
            .is_some_and(LocalDeclaration::accounting_valid);
        verdict_of(name, problems, accounting, max_heartbeats)
    });
    (checks, verdicts)
}

#[cfg(test)]
#[path = "verify_batch_replay_tests.rs"]
mod tests;
