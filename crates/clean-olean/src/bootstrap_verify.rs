// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Local type/value rechecking of a structurally loaded bootstrap closure.
//!
//! This loads the bounded Init/Std lane into ONE assumed environment and checks
//! represented types/values there. It does NOT reconstruct declarations in a
//! fresh dependency-closed kernel: unchecked dependencies, cyclic references,
//! inductive reduction metadata and native reducers remain assumptions.
//!
//! Counters describe exact typed declaration identities, not registry visits.
//! Every represented registry type is checked; mirror disagreement, ambiguous
//! legacy display labels and missing targets are explicit accounting failures.
//!
//! The legacy `kernel_verified` / `KernelChecked` origin labels and promotion
//! loop remain compatibility behavior, NOT a new admission or proof grade.
//! Local success must not be consumed as dependency-closed import authority.
//! Failures retain their exact checker/accounting diagnostics.

use crate::load_modules_with_deps;
use crate::verify_batch_full::local_roster;
use crate::verify_batch_full::typecheck_constants_full;
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::time::Instant;

/// The canonical bootstrap module set: just `Init`.
///
/// `Init` is Lean's prelude closure — every downstream lane imports it, so it is
/// the minimal, always-present bootstrap lane. Callers that also want to certify
/// `Std` should pass `&["Init".into(), "Std".into()]` explicitly (see
/// [`verify_bootstrap_lane`]).
pub const INIT_BOOTSTRAP_MODULES: &[&str] = &["Init"];

/// A single constant that FAILED the bootstrap kernel re-check.
///
/// This is a FINDING, not noise: it names an imported bootstrap declaration that
/// Clean's own kernel does not accept (against the full loaded closure), and the
/// `error` is the verbatim kernel diagnostic (`infer_sort:` for a bad type,
/// `check_type:` for a value that does not inhabit its stated type).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BootstrapFailure {
    /// Fully-qualified constant name (e.g. `Nat.succ_le_succ`).
    pub name: String,
    /// Verbatim kernel error (`infer_sort: ...` or `check_type: ...`).
    pub error: String,
}

/// Result of re-type-checking a bootstrap lane.
///
/// `kernel_verified` is the legacy name for a LOCAL consistency-check count,
/// not dependency-closed verification. `failures` retains all display-keyed
/// diagnostics; use `failed_constants` for the exact failed population.
#[derive(Debug, Clone)]
#[must_use]
pub struct BootstrapVerifyReport {
    /// The bootstrap modules whose closure was loaded and re-checked.
    pub modules: Vec<String>,
    /// Exact typed candidates resolved for newly observed declaration names.
    /// Ambiguous legacy display labels retain every candidate, including a
    /// preexisting alias; accounting errors prevent a valid fraction.
    pub loaded_constants: usize,
    /// Failed exact declaration identities plus missing requested labels.
    /// This is not the length of the lossy legacy display-keyed error map.
    pub failed_constants: usize,
    /// Missing/ambiguous legacy targets or incoherent registry projections.
    pub local_check_accounting_errors: BTreeMap<String, String>,
    /// Exact identities passing every represented local check and registry
    /// coherence check. The field name is legacy, not an admission grade.
    pub kernel_verified: usize,
    /// Constants whose kernel TRUST LEDGER origin was PROMOTED from
    /// `needs_recheck` (unpinned structural import) to `KernelChecked` by this
    /// pass.
    ///
    /// **Always `0` since 2026-09-17.** This lane runs a LOCAL
    /// assumed-environment check, which does not meet
    /// `Environment::promote_origin_kernel_checked`'s stated precondition, and
    /// promoting on it cleared a blocking `NeedsRecheck` issue in
    /// `audit_certification`. Promotion now belongs to the dependency-closed
    /// replay: see
    /// [`crate::recheck_closed::promote_origins_after_closed_recheck`].
    /// The field is kept so a consumer reading it sees `0` rather than
    /// disappearing silently.
    pub origins_promoted: usize,
    /// Constants that FAILED the re-check (a FINDING — see [`BootstrapFailure`]).
    pub failures: Vec<BootstrapFailure>,
    /// Wall-clock time spent in the re-check phase (load time excluded).
    pub recheck_ms: u128,
    /// Wall-clock time spent loading the closure.
    pub load_ms: u128,
}

impl BootstrapVerifyReport {
    /// Whether all observed identities passed these local checks without
    /// accounting errors. This legacy accessor does not confer admission.
    #[must_use]
    pub fn all_verified(&self) -> bool {
        self.failures.is_empty()
            && self.failed_constants == 0
            && self.local_check_accounting_errors.is_empty()
            && self.kernel_verified == self.loaded_constants
    }

    /// Alias for the legacy `kernel_verified` LOCAL consistency count.
    #[must_use]
    pub fn kernel_verified_count(&self) -> usize {
        self.kernel_verified
    }
}

/// Load the requested bootstrap modules' full dependency closure into a FRESH
/// environment and re-type-check every loaded constant with the kernel's
/// local type/value checker, retaining the legacy `KernelVerified` label.
///
/// This is the high-level convenience entry point: it owns the environment. Use
/// [`verify_bootstrap_lane_in_env`] to re-check a caller-owned environment (e.g.
/// one already primed with native reducers or a prelude).
///
/// * `modules` — the bootstrap module names to measure (e.g.
///   [`INIT_BOOTSTRAP_MODULES`], or `["Init", "Std"]`). Their transitive imports
///   are loaded automatically.
/// * `search_paths` — directories holding the `.olean` files (typically
///   `<toolchain>/lib/lean`).
/// * `max_heartbeats` — per-constant kernel step budget (`0` = unlimited). This
///   is a pure RESOURCE limit, never a soundness gate: on exhaustion the kernel
///   conservatively REJECTS (surfacing as a `HeartbeatExceeded` failure), so
///   raising it can only let VALID constants complete, never accept an ill-typed
///   one. Use [`DEFAULT_HEARTBEAT_LIMIT`] unless you have a reason not to.
///
/// # SOUNDNESS
///
/// See the module docs: rechecking assumes the full populated environment,
/// including unchecked dependencies and targets. It is local consistency, not
/// dependency-closed verification. Failures are retained in the report.
///
/// # Errors
///
/// Returns [`ImportError`](crate::ImportError) only if the closure fails to LOAD
/// (a missing `.olean`, an I/O error, a policy rejection). A constant that loads
/// but fails the kernel re-check is NOT an error — it is a FINDING recorded in
/// [`BootstrapVerifyReport::failures`].
pub fn verify_bootstrap_lane(
    modules: &[String],
    search_paths: &[PathBuf],
    max_heartbeats: u32,
) -> Result<BootstrapVerifyReport, crate::ImportError> {
    let mut env = Environment::default();
    // Native reducers (Nat.decEq, String ops, …) are required for the closure's
    // constants to type-check — they back definitional equalities the kernel
    // computes during check_type. load_modules_with_deps installs them, but we
    // prime here too so a caller inspecting `env` mid-flight sees a consistent
    // state.
    env.ensure_native_reducers();
    verify_bootstrap_lane_in_env(&mut env, modules, search_paths, max_heartbeats)
}

/// Re-type-check the bootstrap lane into a CALLER-OWNED environment.
///
/// Loads `modules`' full closure into `env` (in addition to whatever is already
/// there), then re-type-checks ONLY the constants this call newly registered —
/// so a caller can prime `env` first (native reducers, an import prelude) and
/// the report's counts reflect exactly the bootstrap lane, not the prelude.
///
/// The re-check assumes the loaded environment, as [`verify_bootstrap_lane`]
/// does. Local checks are read-only; the existing subsequent origin-label
/// promotion is a legacy compatibility operation, not fresh kernel replay.
pub fn verify_bootstrap_lane_in_env(
    env: &mut Environment,
    modules: &[String],
    search_paths: &[PathBuf],
    max_heartbeats: u32,
) -> Result<BootstrapVerifyReport, crate::ImportError> {
    // Snapshot the names already present so we re-check ONLY this lane's newly
    // registered constants (not any prelude the caller pre-seeded).
    let before = all_decl_names(env);

    let load_start = Instant::now();
    // Load the WHOLE closure in ONE shared pass: every transitive import is
    // registered in dependency order into `env`, so the re-check below sees every
    // dependency (no spurious UnknownConst failures from missing context).
    let _summaries = load_modules_with_deps(env, modules, search_paths)?;
    let load_ms = load_start.elapsed().as_millis();

    // The lane's constants = everything registered by this load that was not
    // already present.
    let lane_names = new_lane_targets(env, &before);
    let roster = local_roster::resolve_targets(env, &lane_names);

    let recheck_start = Instant::now();
    // Local consistency against the whole ASSUMED environment, not fresh
    // dependency-closed admission. Each typed identity is counted once only
    // after every represented registry projection passed/cohered.
    let (pass, fail, errors) = typecheck_constants_full(env, &lane_names, max_heartbeats);
    let recheck_ms = recheck_start.elapsed().as_millis();

    // NO ORIGIN PROMOTION HAPPENS HERE (changed 2026-09-17).
    //
    // This lane used to promote every passing lane name through
    // `Environment::promote_origin_kernel_checked`, on the strength of the
    // `typecheck_constants_full` above. That promotion is not a label: it
    // clears `Environment::constant_needs_recheck`, which is a BLOCKING issue
    // in `Environment::audit_certification`. So a local, assumed-environment
    // check was silently buying a structural import its way past the
    // certification audit — while this function's own prose said the check was
    // "NOT dependency-closed kernel authority".
    //
    // `promote_origin_kernel_checked`'s stated precondition is an
    // `add_decl`-equivalent re-check. The check above is not one (see this
    // module's header and `verify_batch_full`'s). The lane that IS one is
    // `crate::recheck_closed::recheck_closed`; promote from it with
    // `crate::recheck_closed::promote_origins_after_closed_recheck`.
    let promoted = 0usize;
    let _ = pass;

    let failures = errors
        .into_iter()
        .map(|(name, error)| BootstrapFailure { name, error })
        .collect();

    Ok(BootstrapVerifyReport {
        modules: modules.to_vec(),
        loaded_constants: roster.declarations.len(),
        failed_constants: fail,
        local_check_accounting_errors: roster.accounting_errors,
        kernel_verified: pass,
        origins_promoted: promoted,
        failures,
        recheck_ms,
        load_ms,
    })
}

/// Convenience: re-type-check the canonical `Init` bootstrap lane with the
/// default heartbeat budget. See [`verify_bootstrap_lane`].
///
/// # Errors
///
/// Propagates [`ImportError`](crate::ImportError) if the `Init` closure cannot
/// be loaded from `search_paths`.
pub fn verify_init_bootstrap(
    search_paths: &[PathBuf],
) -> Result<BootstrapVerifyReport, crate::ImportError> {
    let modules: Vec<String> = INIT_BOOTSTRAP_MODULES
        .iter()
        .map(|s| (*s).to_string())
        .collect();
    verify_bootstrap_lane(&modules, search_paths, DEFAULT_HEARTBEAT_LIMIT)
}

/// Every declaration name registered in `env` (constants + inductives +
/// constructors + recursors), the exact set [`typecheck_constants_full`]
/// iterates over.
fn all_decl_names(env: &Environment) -> BTreeSet<Name> {
    let mut names = BTreeSet::new();
    for c in env.constants() {
        names.insert(c.name.clone());
    }
    for i in env.inductives() {
        names.insert(i.name.clone());
    }
    for c in env.constructors() {
        names.insert(c.name.clone());
    }
    for r in env.recursors() {
        names.insert(r.name.clone());
    }
    names
}

fn new_lane_targets(env: &Environment, before: &BTreeSet<Name>) -> BTreeSet<String> {
    all_decl_names(env)
        .difference(before)
        .map(ToString::to_string)
        .collect()
}

/// Format a report's findings for a human-readable audit line.
///
/// Reports local counts and legacy label updates separately. Every retained
/// checker/accounting finding is displayed; no imported proof grade is claimed.
#[must_use]
pub fn format_report(report: &BootstrapVerifyReport) -> String {
    let mut out = format!(
        "bootstrap lane {:?}: {} typed candidates, {} local-check passes, {} failed identities/targets, \
         {} trust-ledger origins promoted (always 0: this lane is not dependency-closed), \
         {} findings, {} accounting errors; \
         dependencies assumed; load {} ms, recheck {} ms",
        report.modules,
        report.loaded_constants,
        report.kernel_verified,
        report.failed_constants,
        report.origins_promoted,
        report.failures.len(),
        report.local_check_accounting_errors.len(),
        report.load_ms,
        report.recheck_ms,
    );
    if !report.failures.is_empty() {
        out.push_str("\n  FINDINGS (local checker/accounting refusals):");
        for f in &report.failures {
            out.push_str(&format!("\n    {}: {}", f.name, f.error));
        }
    }
    if !report.local_check_accounting_errors.is_empty() {
        out.push_str("\n  ACCOUNTING (fraction unavailable):");
        for (name, error) in &report.local_check_accounting_errors {
            out.push_str(&format!("\n    {name}: {error}"));
        }
    }
    out
}

/// Aggregate a set of per-constant errors into a `{category -> count}` map for
/// triage. The category is the leading `infer_sort` / `check_type` phase plus
/// the kernel error head, so a batch of `UnknownConst(Nat)` failures collapses
/// to one row.
#[must_use]
pub fn categorize_failures(failures: &[BootstrapFailure]) -> BTreeMap<String, usize> {
    let mut cats = BTreeMap::new();
    for f in failures {
        let cat = failure_category(&f.error);
        *cats.entry(cat).or_insert(0) += 1;
    }
    cats
}

/// The coarse category of a single kernel error string (phase + error head).
/// A check that spent its heartbeat budget is one category of its own,
/// whatever its under-reduced check failed with (`local_roster::CheckProblem`).
fn failure_category(error: &str) -> String {
    if error.starts_with(local_roster::BUDGET_EXHAUSTED) {
        return local_roster::BUDGET_EXHAUSTED.to_owned();
    }
    // Errors look like `infer_sort: UnknownConst(Name { ... })` or
    // `check_type: TypeMismatch { ... }`. Keep the phase + the variant head.
    let (phase, rest) = match error.split_once(": ") {
        Some((p, r)) => (p, r),
        None => ("unknown", error),
    };
    let head = rest.split(['(', ' ', '{']).next().unwrap_or(rest);
    format!("{phase}: {head}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::{Declaration, Environment};
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::level::Level;
    use clean_kernel::name::Name as KName;

    /// `(P : Prop) → P → P` and its identity proof `λ P p => p` — a
    /// kernel-real, dependency-free polymorphic identity every kind can carry.
    fn id_ty_val() -> (Expr, Expr) {
        let id_ty = Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        );
        let id_val = Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        );
        (id_ty, id_val)
    }

    /// The report helper accessors are consistent with their fields.
    #[test]
    fn test_report_accessors_consistent() {
        let clean = BootstrapVerifyReport {
            modules: vec!["Init".into()],
            loaded_constants: 3,
            failed_constants: 0,
            local_check_accounting_errors: BTreeMap::new(),
            kernel_verified: 3,
            origins_promoted: 3,
            failures: vec![],
            recheck_ms: 1,
            load_ms: 1,
        };
        assert!(clean.all_verified());
        assert_eq!(clean.kernel_verified_count(), 3);

        let dirty = BootstrapVerifyReport {
            modules: vec!["Init".into()],
            loaded_constants: 3,
            failed_constants: 1,
            local_check_accounting_errors: BTreeMap::new(),
            kernel_verified: 2,
            origins_promoted: 2,
            failures: vec![BootstrapFailure {
                name: "Bad".into(),
                error: "check_type: TypeMismatch { .. }".into(),
            }],
            recheck_ms: 1,
            load_ms: 1,
        };
        assert!(!dirty.all_verified());
        assert_eq!(dirty.kernel_verified_count(), 2);
    }

    #[test]
    fn local_accounting_bootstrap_delta_keeps_new_display_alias() {
        use clean_kernel::env::{ConstantInfo, ConstantKind, Reducibility};
        let mut env = Environment::default();
        let insert = |env: &mut Environment, name| {
            env.add_constant_unchecked_for_test(ConstantInfo::new_with_reducibility(
                name,
                vec![],
                Expr::sort(Level::zero()),
                None,
                Reducibility::Opaque,
                ConstantKind::Axiom,
            ));
        };
        insert(&mut env, KName::anon().str("A").str("B"));
        let before = all_decl_names(&env);
        insert(&mut env, KName::anon().str("A.B"));
        let targets = new_lane_targets(&env, &before);
        assert_eq!(targets, BTreeSet::from(["A.B".to_owned()]));
        let roster = local_roster::resolve_targets(&env, &targets);
        assert_eq!(roster.declarations.len(), 2);
        assert!(roster.accounting_errors["A.B"].contains("ambiguous"));
        let (pass, fail, errors) = typecheck_constants_full(&env, &targets, 2_000_000);
        assert_eq!((pass, fail), (0, 2));
        assert!(errors.contains_key("A.B"));
    }

    #[test]
    fn local_accounting_bootstrap_invalid_accounting_cannot_be_all_verified() {
        let report = BootstrapVerifyReport {
            modules: vec![],
            loaded_constants: 1,
            kernel_verified: 1,
            origins_promoted: 0,
            failed_constants: 0,
            local_check_accounting_errors: BTreeMap::from([(
                "ambiguous".into(),
                "retained".into(),
            )]),
            failures: vec![],
            recheck_ms: 0,
            load_ms: 0,
        };
        assert!(!report.all_verified());
    }

    /// CORE SOUNDNESS TEST (no toolchain needed): re-type-checking a set of
    /// kernel-real constants makes them KernelVerified (0 -> N), and a genuinely
    /// ill-typed constant is surfaced as a FINDING, never silently passed.
    ///
    /// This exercises the exact re-check the bootstrap-lane entry point runs
    /// (`typecheck_constants_full` over a loaded closure), using an in-memory
    /// environment so it runs everywhere — the real-Init 0->N number requires the
    /// Lean toolchain and is measured by `import_ac1_tests`.
    #[test]
    fn test_recheck_marks_verified_and_surfaces_ill_typed() {
        use clean_kernel::env::{ConstantInfo, ConstantKind, Reducibility};

        let mut env = Environment::default();
        env.ensure_native_reducers();
        let (id_ty, id_val) = id_ty_val();

        // Three genuinely well-typed constants (added through add_decl, so they
        // ARE kernel-valid; the re-check must confirm all three).
        env.add_decl(Declaration::Definition {
            name: KName::from_string("boot.D"),
            level_params: vec![],
            type_: id_ty.clone(),
            value: id_val.clone(),
            is_reducible: false,
        })
        .expect("add D");
        env.add_decl(Declaration::Theorem {
            name: KName::from_string("boot.T"),
            level_params: vec![],
            type_: id_ty.clone(),
            value: id_val.clone(),
        })
        .expect("add T");
        env.add_decl(Declaration::Opaque {
            name: KName::from_string("boot.O"),
            level_params: vec![],
            type_: id_ty.clone(),
            value: id_val.clone(),
        })
        .expect("add O");

        // One STRUCTURALLY-admitted but ill-typed constant: value is the id
        // function but the stated type is `Prop` — check_type MUST reject it.
        // This models a tampered/miscompiled import the structural path would
        // admit but the kernel re-check catches (the whole point of this task).
        env.add_constant_unchecked_for_test(ConstantInfo::new_with_reducibility(
            KName::from_string("boot.BAD"),
            vec![],
            Expr::sort(Level::zero()), // stated: Prop
            Some(id_val.clone()),      // value is a function, not a proof of Prop
            Reducibility::Opaque,
            ConstantKind::Opaque,
        ));

        let names: BTreeSet<String> = ["boot.D", "boot.T", "boot.O", "boot.BAD"]
            .into_iter()
            .map(str::to_string)
            .collect();

        let (pass, fail, errors) = typecheck_constants_full(&env, &names, DEFAULT_HEARTBEAT_LIMIT);

        // 0 -> N: the three genuine constants are now KernelVerified.
        assert_eq!(
            pass, 3,
            "the three well-typed bootstrap constants must verify"
        );
        assert_eq!(fail, 1, "the ill-typed constant must be a finding");
        // The finding is surfaced PRECISELY, never suppressed, and is a genuine
        // check_type (proof-value) failure.
        assert!(
            errors
                .get("boot.BAD")
                .is_some_and(|e| e.starts_with("check_type:")),
            "ill-typed BAD must surface as a check_type finding; errors={errors:?}"
        );
        // The env was NOT mutated by the re-check: BAD's (bad) value is still
        // present — the re-check is read-only and can only ADD trust knowledge.
        assert!(
            env.get_const(&KName::from_string("boot.BAD"))
                .unwrap()
                .value
                .is_some(),
            "re-check must not mutate the environment"
        );
    }

    /// G5 TRUST-LEDGER PROMOTION (no toolchain needed): a constant that entered
    /// via the STRUCTURAL import lane carries a `needs_recheck` origin; after it
    /// PASSES the kernel re-check its ledger origin is promoted to
    /// `KernelChecked`, while a FAILING structural import stays `needs_recheck`
    /// and is never promoted. This is the exact G5 fail-closed contract the
    /// bootstrap lane wires (`promote_origin_kernel_checked` on the passing set).
    #[test]
    fn test_structural_import_promoted_only_on_passing_recheck() {
        use clean_kernel::env::{ConstantInfo, ConstantKind, ConstantOrigin, Reducibility};

        let mut env = Environment::default();
        env.ensure_native_reducers();
        let (id_ty, id_val) = id_ty_val();

        // A genuinely well-typed constant admitted STRUCTURALLY (unchecked
        // insert + an unpinned `.olean` origin) — the shape the import lane
        // produces.
        env.add_constant_unchecked_for_test(ConstantInfo::new_with_reducibility(
            KName::from_string("boot.GOOD"),
            vec![],
            id_ty.clone(),
            Some(id_val.clone()),
            Reducibility::Regular(0),
            ConstantKind::Definition,
        ));
        // An ill-typed structural import (value is a function, stated type Prop).
        env.add_constant_unchecked_for_test(ConstantInfo::new_with_reducibility(
            KName::from_string("boot.EVIL"),
            vec![],
            Expr::sort(Level::zero()),
            Some(id_val.clone()),
            Reducibility::Opaque,
            ConstantKind::Opaque,
        ));
        for n in ["boot.GOOD", "boot.EVIL"] {
            assert!(env.set_constant_origin(
                KName::from_string(n),
                ConstantOrigin::olean_import(Some("Boot.Module".to_string())),
            ));
            assert!(
                env.constant_needs_recheck(&KName::from_string(n)),
                "{n} must start as a needs_recheck structural import"
            );
        }

        let names: BTreeSet<String> = ["boot.GOOD", "boot.EVIL"]
            .into_iter()
            .map(str::to_string)
            .collect();

        // Re-check, then promote exactly the passing set (mirrors the lane wiring).
        let (_pass, _fail, errors) =
            typecheck_constants_full(&env, &names, DEFAULT_HEARTBEAT_LIMIT);
        let failed: BTreeSet<&String> = errors.keys().collect();
        for name in &names {
            if !failed.contains(name) {
                // SOUNDNESS: promotion only for a constant that PASSED the
                // preceding kernel re-check.
                env.promote_origin_kernel_checked(&KName::from_string(name));
            }
        }

        // GOOD passed ⇒ promoted to KernelChecked (no longer needs_recheck).
        assert!(
            env.constant_is_kernel_checked(&KName::from_string("boot.GOOD")),
            "a passing structural import must be promoted to KernelChecked"
        );
        assert!(!env.constant_needs_recheck(&KName::from_string("boot.GOOD")));
        // EVIL failed ⇒ NOT promoted, stays needs_recheck (fail-closed).
        assert!(
            env.constant_needs_recheck(&KName::from_string("boot.EVIL")),
            "a failing structural import must NOT be promoted (fail-closed)"
        );
        assert!(!env.constant_is_kernel_checked(&KName::from_string("boot.EVIL")));
    }

    /// `categorize_failures` collapses a batch of same-cause errors into one row
    /// (the triage view a real Init/Std finding block needs).
    #[test]
    fn test_categorize_failures_collapses_same_cause() {
        let failures = vec![
            BootstrapFailure {
                name: "A".into(),
                error: "infer_sort: UnknownConst(Name { inner: Str })".into(),
            },
            BootstrapFailure {
                name: "B".into(),
                error: "infer_sort: UnknownConst(Name { other })".into(),
            },
            BootstrapFailure {
                name: "C".into(),
                error: "check_type: TypeMismatch { .. }".into(),
            },
        ];
        let cats = categorize_failures(&failures);
        assert_eq!(cats.get("infer_sort: UnknownConst"), Some(&2));
        assert_eq!(cats.get("check_type: TypeMismatch"), Some(&1));
    }

    /// A clean report formats to a single-line LOCAL summary; a report
    /// with findings appends the finding block (never hides a finding).
    #[test]
    fn test_format_report_surfaces_findings() {
        let clean = BootstrapVerifyReport {
            modules: vec!["Init".into()],
            loaded_constants: 100,
            failed_constants: 0,
            local_check_accounting_errors: BTreeMap::new(),
            kernel_verified: 100,
            origins_promoted: 100,
            failures: vec![],
            recheck_ms: 5,
            load_ms: 10,
        };
        let s = format_report(&clean);
        assert!(s.contains("100 local-check passes"));
        assert!(s.contains("dependencies assumed"));
        assert!(!s.contains("now KernelVerified"));
        assert!(!s.contains("FINDINGS"));

        let dirty = BootstrapVerifyReport {
            modules: vec!["Init".into()],
            loaded_constants: 100,
            failed_constants: 1,
            local_check_accounting_errors: BTreeMap::new(),
            kernel_verified: 99,
            origins_promoted: 99,
            failures: vec![BootstrapFailure {
                name: "Bad.decl".into(),
                error: "check_type: TypeMismatch".into(),
            }],
            recheck_ms: 5,
            load_ms: 10,
        };
        let s = format_report(&dirty);
        assert!(s.contains("FINDINGS"));
        assert!(s.contains("Bad.decl: check_type: TypeMismatch"));

        let mut ambiguous = dirty;
        ambiguous
            .local_check_accounting_errors
            .insert("A.B".into(), "two exact typed identities".into());
        let s = format_report(&ambiguous);
        assert!(s.contains("ACCOUNTING (fraction unavailable)"));
        assert!(s.contains("A.B: two exact typed identities"));
    }
}
