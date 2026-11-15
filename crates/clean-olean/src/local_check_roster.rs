//! Exact identity accounting for LOCAL consistency checks in an assumed env.
//!
//! The specialized registries deliberately mirror ordinary constants. Their
//! common fields must agree, but every represented type is still checked. This
//! is not validation of inductive rules, dependency-closed replay, or admission.

use clean_kernel::env::{Environment, KernelTheory};
use clean_kernel::expr::Expr;
use clean_kernel::name::{Name, NameInner};
use clean_kernel::tc::TypeChecker;
use std::collections::{BTreeMap, BTreeSet};

/// The label a starved check's report starts with (and the category
/// `bootstrap_verify` files it under).
pub(crate) const BUDGET_EXHAUSTED: &str = "budget exhausted";

/// One failed kernel check of a declaration.
///
/// The kernel's `whnf` and `is_def_eq` stop SILENTLY once the heartbeat budget
/// is spent (`whnf` returns its input, `is_def_eq` answers `false`), so a check
/// that ran out of budget fails with whatever that under-reduction produced,
/// usually a type mismatch. A failure is a verdict on the declaration only when
/// the budget was NOT spent when the check ended ([`ReplayChecker::check`]
/// reads it then). Conservative in one direction only: a genuine rejection
/// that happened to spend the very last heartbeat is labelled a budget failure
/// too, and is still not admitted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CheckProblem {
    /// What the check failed with, as the kernel (or the roster) put it.
    error: String,
    /// The per-check heartbeat limit the check had spent when it ended
    /// (`0`: the ambient declaration budget); `None` for the kernel's verdict.
    starved_at: Option<u32>,
}

impl CheckProblem {
    /// A failure that is not the kernel's budget running out.
    pub(crate) fn verdict(error: String) -> Self {
        Self {
            error,
            starved_at: None,
        }
    }

    /// A failure of a check that had spent its budget of `limit`.
    fn starved(limit: u32, error: String) -> Self {
        Self {
            error,
            starved_at: Some(limit),
        }
    }

    /// The check had spent its budget: what it failed with is no verdict.
    pub(crate) fn budget_spent(&self) -> bool {
        self.starved_at.is_some()
    }

    /// What the check failed with, without the budget label.
    pub(crate) fn error(&self) -> &str {
        &self.error
    }

    /// The problem as a lane records it: a starved check's error behind the
    /// budget, so it never reads as the kernel's verdict.
    pub(crate) fn report(&self) -> String {
        let Some(limit) = self.starved_at else {
            return self.error.clone();
        };
        let budget = match limit {
            0 => "the ambient declaration heartbeat budget".to_owned(),
            limit => format!("its heartbeat budget of {limit}"),
        };
        format!(
            "{BUDGET_EXHAUSTED}: the check spent {budget} before it decided, so what it \
             failed with is no verdict on the declaration: {}",
            self.error
        )
    }
}

/// A checker for one replay: cache-enabled over the fixed environment (sound
/// because nothing mutates it while the checker lives), with the per-check
/// heartbeat budget, in Lean's kernel theory. That also puts it in Lean's SAFE
/// context: every declaration this replay admits is safe (unsafe and partial
/// ones are refused before the kernel), so a reference to an unsafe or partial
/// constant, local or imported, is the kernel's own error, as in Lean's
/// `infer_constant` ("invalid declaration, it uses unsafe declaration").
fn lean_checker(env: &Environment, max_heartbeats: u32) -> TypeChecker<'_> {
    let mut tc = TypeChecker::new(env);
    tc.set_kernel_theory(KernelTheory::Lean);
    tc.enable_type_cache_pub();
    tc.set_heartbeat_limit(max_heartbeats);
    tc
}

/// The kernel checker of one replay lane ([`lean_checker`]), REPLACED by a
/// fresh one after every check that spent its budget.
///
/// The replacement is what lets a later failure be a verdict. Once the budget
/// is spent the kernel's `whnf` returns its input unreduced and `is_def_eq`
/// answers `false`, and both are MEMOISED (`whnf_cache`, `def_eq_cache`, the
/// lazy-delta failure cache). `reset_heartbeat` and `reset_local_context`
/// clear no cache, so one long-lived checker answered LATER checks, each with
/// a fresh budget, from a starved check's answers. Measured 2026-09-30 on the
/// honest `ReplayHonestInd` fixture (admitted in full at `--max-heartbeats 0`
/// and at 100 and above): 60 of its 105 refusals at 2, 17 of 88 at 3, 11 of 78
/// at 5 and 8 of 65 at 8 failed with budget to spare, `HOd.succ` with
/// `TypeMismatch` (`outParam (Sort 1)` against `Sort 1`) right after the
/// starved `HEv.succ`. A fresh checker is the state every replay starts in, so
/// the cost is cache warm-up after a starved check only; the elaborator drops
/// an exhausted checker's caches the same way (clean-elab
/// `tactic/core/type_check.rs` `with_tc`).
pub(crate) struct ReplayChecker<'env> {
    env: &'env Environment,
    max_heartbeats: u32,
    tc: TypeChecker<'env>,
    profile_problem: Option<String>,
}

impl<'env> ReplayChecker<'env> {
    /// A fresh checker over `env` with a per-check budget of `max_heartbeats`
    /// (`0`: unlimited, as Lean's replay runs).
    pub(crate) fn new(env: &'env Environment, max_heartbeats: u32) -> Self {
        Self {
            env,
            max_heartbeats,
            tc: lean_checker(env, max_heartbeats),
            profile_problem: crate::import::validate_level_profile(env)
                .err()
                .map(|e| e.to_string()),
        }
    }

    /// The per-check heartbeat budget.
    pub(crate) fn heartbeat_limit(&self) -> u32 {
        self.max_heartbeats
    }

    /// Run one kernel check from an empty local context under a full budget;
    /// `None` when it passed. When the check spent its budget, passed or not,
    /// the checker is replaced before the next check, and a failure is
    /// reported as starved, never as the kernel's verdict.
    ///
    /// A check that met a universe instantiation whose Lean answer depends on
    /// `.olean` object sharing leaves the checker refusing everything after it
    /// (DECISIONS R150). That check is refused by name, even when it swallowed
    /// the error, and the checker is replaced, so the refusal decides no later
    /// check. It is a verdict whatever the budget: the instantiation was met.
    pub(crate) fn check(
        &mut self,
        run: impl FnOnce(&TypeChecker<'env>) -> Result<(), String>,
    ) -> Option<CheckProblem> {
        if let Some(error) = &self.profile_problem {
            return Some(CheckProblem::verdict(error.clone()));
        }
        self.tc.reset_local_context();
        self.tc.reset_heartbeat();
        let outcome = run(&self.tc);
        let sharing = self.tc.level_sharing_error();
        let starved = sharing.is_none() && self.tc.heartbeat_spent();
        if sharing.is_none() && !starved {
            return outcome.err().map(CheckProblem::verdict);
        }
        self.tc = lean_checker(self.env, self.max_heartbeats);
        let error = match (outcome, sharing) {
            (Err(error), _) => error,
            (Ok(()), Some(sharing)) => format!("{sharing:?}"),
            (Ok(()), None) => return None,
        };
        Some(if starved {
            CheckProblem::starved(self.max_heartbeats, error)
        } else {
            CheckProblem::verdict(error)
        })
    }

    /// This exact type check returns no generated metadata to choose between.
    /// Their exact original value/type may additionally be checked under ALL
    /// overapproximated sharing outcomes. Header/registry/generated-family
    /// comparisons remain mandatory in the surrounding replay and insertion.
    fn check_theorem_value(&mut self, value: &Expr, expected: &Expr) -> Option<CheckProblem> {
        if let Some(error) = &self.profile_problem {
            return Some(CheckProblem::verdict(error.clone()));
        }
        self.tc.reset_local_context();
        self.tc.reset_heartbeat();
        let outcome = self.tc.check_type(value, expected);
        let sharing = self.tc.level_sharing_error();
        let starved = self.tc.heartbeat_spent();
        if sharing.is_none() && !starved {
            return outcome
                .err()
                .map(|error| CheckProblem::verdict(format!("check_type: {error:?}")));
        }
        if sharing.is_some() && !starved {
            let invariant = self.tc.recheck_type_sharing_invariant(value, expected);
            self.tc = lean_checker(self.env, self.max_heartbeats);
            return match invariant {
                Ok(_) => None,
                Err(reason) => Some(CheckProblem::verdict(format!(
                    "check_type: {sharing:?}; exact sharing invariance not established: {reason}"
                ))),
            };
        }
        self.tc = lean_checker(self.env, self.max_heartbeats);
        let error = format!("check_type: {outcome:?}; sharing: {sharing:?}");
        Some(if sharing.is_some() {
            CheckProblem::verdict(error)
        } else {
            CheckProblem::starved(self.max_heartbeats, error)
        })
    }

    /// The checker the next check runs on.
    #[cfg(test)]
    pub(crate) fn kernel(&self) -> &TypeChecker<'env> {
        &self.tc
    }
}

pub(crate) struct LocalProjection {
    role: &'static str,
    type_: Expr,
    levels: Vec<Name>,
}

pub(crate) struct LocalDeclaration {
    projections: Vec<LocalProjection>,
    has_value: bool,
    accounting_valid: bool,
}

impl LocalDeclaration {
    /// Do not deduplicate check attempts, including after a mirror disagreement.
    pub(crate) fn check_sorts(&self, checker: &mut ReplayChecker<'_>) -> Vec<CheckProblem> {
        self.projections
            .iter()
            .filter_map(|projection| {
                checker.check(|tc| {
                    tc.infer_sort(&projection.type_).map(drop).map_err(|error| {
                        format!("infer_sort: {} registry: {error:?}", projection.role)
                    })
                })
            })
            .collect()
    }

    pub(crate) fn has_value(&self) -> bool {
        self.has_value
    }

    pub(crate) fn accounting_valid(&self) -> bool {
        self.accounting_valid
    }
}

/// Includes all exact candidates for ambiguous legacy display labels. No
/// strings are parsed back into a kernel name. Values are NOT cloned here so
/// the streaming checker can actually free its checked opaque values.
pub(crate) struct LocalCheckRoster {
    pub(crate) declarations: BTreeMap<Name, LocalDeclaration>,
    pub(crate) accounting_errors: BTreeMap<String, String>,
    missing_targets: usize,
}

fn append_error(errors: &mut BTreeMap<String, String>, label: String, error: String) {
    errors
        .entry(label)
        .and_modify(|prior| {
            prior.push_str("; ");
            prior.push_str(&error);
        })
        .or_insert(error);
}

/// Unambiguous diagnostic only: string components are quoted/escaped and
/// numeric components retain their variant. Never used as the identity key.
fn typed_name(mut name: &Name) -> String {
    let mut parts = Vec::new();
    loop {
        match name.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, value) => {
                parts.push(format!("Str({value:?})"));
                name = parent;
            }
            NameInner::Num(parent, value) => {
                parts.push(format!("Num({value})"));
                name = parent;
            }
        }
    }
    parts.reverse();
    format!("Anon/{}", parts.join("/"))
}

pub(crate) fn resolve_targets(env: &Environment, targets: &BTreeSet<String>) -> LocalCheckRoster {
    let mut declarations = BTreeMap::<Name, LocalDeclaration>::new();
    let mut add = |name: &Name, role, type_: &Expr, levels: &[Name], has_value| {
        if targets.contains(&name.to_string()) {
            let row = declarations
                .entry(name.clone())
                .or_insert(LocalDeclaration {
                    projections: Vec::new(),
                    has_value: false,
                    accounting_valid: true,
                });
            row.projections.push(LocalProjection {
                role,
                type_: type_.clone(),
                levels: levels.to_vec(),
            });
            row.has_value |= has_value;
        }
    };
    for row in env.constants() {
        add(
            &row.name,
            "constant",
            &row.type_,
            &row.level_params,
            row.value.is_some(),
        );
    }
    for row in env.inductives() {
        add(&row.name, "inductive", &row.type_, &row.level_params, false);
    }
    for row in env.constructors() {
        add(
            &row.name,
            "constructor",
            &row.type_,
            &row.level_params,
            false,
        );
    }
    for row in env.recursors() {
        add(&row.name, "recursor", &row.type_, &row.level_params, false);
    }
    let mut projected = BTreeMap::<String, Vec<Name>>::new();
    for name in declarations.keys() {
        projected
            .entry(name.to_string())
            .or_default()
            .push(name.clone());
    }
    let mut accounting_errors = BTreeMap::new();
    let mut missing_targets = 0;
    for label in targets {
        match projected.get(label) {
            None => {
                missing_targets += 1;
                append_error(&mut accounting_errors, label.clone(), "missing requested target from eager declaration registries (lazy closure unmeasured)".into());
            }
            Some(names) if names.len() > 1 => {
                append_error(
                    &mut accounting_errors,
                    label.clone(),
                    format!(
                        "ambiguous legacy display label: {}",
                        names.iter().map(typed_name).collect::<Vec<_>>().join(", ")
                    ),
                );
                for name in names {
                    if let Some(row) = declarations.get_mut(name) {
                        row.accounting_valid = false;
                    }
                }
            }
            Some(_) => {}
        }
    }
    for (name, row) in &mut declarations {
        let mut problems = Vec::new();
        let specialized = row
            .projections
            .iter()
            .filter(|p| p.role != "constant")
            .count();
        if specialized > 1 {
            problems.push("registry identity has multiple specialized roles".to_owned());
        }
        // Inductive types/constructors are primitive and have no definition.
        // Recursor-table entries can also have real checked DEFINITIONS:
        // add_inductive generates casesOn/recOn values plus fast-path rules.
        // Do not reject those by name or confuse absent rule-value metadata
        // with a requirement that the ordinary constant have no value.
        if row.has_value
            && row
                .projections
                .iter()
                .any(|p| matches!(p.role, "inductive" | "constructor"))
        {
            problems
                .push("registry specialized mirror unexpectedly has a constant value".to_owned());
        }
        if let Some(first) = row.projections.first() {
            for other in row.projections.iter().skip(1) {
                if first.type_ != other.type_ {
                    problems.push(format!(
                        "registry type mismatch: {} versus {}",
                        first.role, other.role
                    ));
                }
                if first.levels != other.levels {
                    problems.push(format!(
                        "registry universe telescope mismatch: {} versus {}",
                        first.role, other.role
                    ));
                }
            }
        }
        if !problems.is_empty() {
            row.accounting_valid = false;
            append_error(
                &mut accounting_errors,
                name.to_string(),
                format!("{}: {}", typed_name(name), problems.join("; ")),
            );
        }
    }
    LocalCheckRoster {
        declarations,
        accounting_errors,
        missing_targets,
    }
}

impl LocalCheckRoster {
    /// Counts exact declaration verdicts, not registry/check attempts. An
    /// absent requested label adds an explicit failure but no invented Name.
    pub(crate) fn finish(
        &self,
        checks: &BTreeMap<Name, Vec<String>>,
    ) -> (usize, usize, BTreeMap<String, String>) {
        let mut pass = 0;
        let mut fail = self.missing_targets;
        let mut errors = self.accounting_errors.clone();
        for (name, declaration) in &self.declarations {
            match checks.get(name) {
                Some(problems) => {
                    if declaration.accounting_valid && problems.is_empty() {
                        pass += 1;
                    } else {
                        fail += 1;
                    }
                    for problem in problems {
                        append_error(
                            &mut errors,
                            name.to_string(),
                            format!("{problem} [{}]", typed_name(name)),
                        );
                    }
                }
                None => {
                    fail += 1;
                    append_error(
                        &mut errors,
                        name.to_string(),
                        format!(
                            "local checker did not report a result [{}]",
                            typed_name(name)
                        ),
                    );
                }
            }
        }
        (pass, fail, errors)
    }
}

pub(crate) fn check_value(
    checker: &mut ReplayChecker<'_>,
    env: &Environment,
    name: &Name,
) -> Option<CheckProblem> {
    let Some(constant) = env.get_const(name) else {
        return Some(CheckProblem::verdict(
            "check_type: value-bearing constant disappeared".into(),
        ));
    };
    let Some(value) = &constant.value else {
        return Some(CheckProblem::verdict(
            "check_type: snapshotted value disappeared before checking".into(),
        ));
    };
    // The fallback proves only a unit-returning value judgement. A name with
    // generated-family metadata must retain its ordinary strict path: such a
    // judgement also has stored output/rules to compare, which this value-only
    // universal replay deliberately does not reconstruct or authorize.
    if constant.kind == clean_kernel::env::ConstantKind::Theorem
        && env.get_inductive(name).is_none()
        && env.get_constructor(name).is_none()
        && env.get_recursor(name).is_none()
    {
        return checker.check_theorem_value(value, &constant.type_);
    }
    checker.check(|tc| {
        tc.check_type(value, &constant.type_)
            .map_err(|error| format!("check_type: {error:?}"))
    })
}
