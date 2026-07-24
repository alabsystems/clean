// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Re-type-check the bootstrap `Init`/`Std` `.olean` lane so its constants
//! become genuinely `KernelVerified` — shrinking the import trust boundary.
//!
//! # The trust boundary this closes
//!
//! The `.olean` import path registers constants STRUCTURALLY: the loader runs
//! only the O(1) structural checks (`extend_constants_structural` in
//! `import/load_register.rs` — no free vars, no metavariables, level scope) and
//! then TRUSTS the imported type/value as already-checked-on-export. Those
//! constants are therefore admitted WITHOUT Clean-kernel type-checking, and the
//! soundness certificate lists ".olean/.mathverse import" as an explicit
//! external trust dependency (stored `KernelVerified`: 0). This is the residual,
//! reducible piece of the import TCB.
//!
//! For the SMALL, bounded bootstrap lane (`Init`, and optionally `Std`) that
//! residual is fully closeable: after loading the closure we simply run the
//! kernel's own `add_decl`-equivalent re-check ([`typecheck_constants_full`]:
//! `infer_sort` on every type + `check_type` on every value with
//! `infer_only=false`) over exactly the imported constants. Every constant that
//! PASSES is now genuinely `KernelVerified` — the Clean kernel accepted its
//! proof value against its stated type — so the count goes from `0` to `N` for
//! that lane and those declarations leave the trusted-but-unchecked set.
//!
//! # SOUNDNESS
//!
//! Re-type-checking only ever ADDS verification; it can NEVER admit a false
//! proof and can never LOWER trust:
//!
//! * A constant that PASSES the kernel checker is strictly MORE trusted than one
//!   admitted structurally — an unchecked assumption becomes a checked
//!   declaration. The environment itself is never mutated by the re-check (it
//!   runs against `&Environment`), so no verdict of any OTHER constant changes.
//! * A constant that FAILS the re-check is a genuine FINDING and is surfaced
//!   PRECISELY (name + the kernel error), never suppressed. A failing BOOTSTRAP
//!   constant is a real soundness signal — it means an imported `Init`/`Std`
//!   declaration Clean's own kernel does not accept — so callers must treat a
//!   non-empty [`BootstrapVerifyReport::failures`] as an alarm, not noise.
//!
//! # Why the FULL closure, not a single file
//!
//! A single `.olean` re-checked in isolation fails with `UnknownConst(Nat)` /
//! `UnknownConst(Eq)` — not a soundness signal, just missing context: the file
//! references base constants declared in its imports. So this entry point loads
//! the WHOLE dependency closure of the requested bootstrap modules
//! ([`load_modules_with_deps`], which registers every transitive import in
//! dependency order into ONE environment) and only then re-type-checks the union
//! of loaded constants — every dependency is present, so a failure is genuinely
//! the constant's own fault.
//!
//! # Scope: bootstrap ONLY
//!
//! This is deliberately scoped to the bounded `Init`/`Std` bootstrap lane
//! (~57K + ~80K constants). The large Mathverse / Isabelle lanes (millions of
//! declarations) stay on the structural import path — re-type-checking them is a
//! separate performance effort and is intentionally NOT done here.

use crate::load_modules_with_deps;
use crate::verify_batch_full::typecheck_constants_full;
use clean_kernel::env::Environment;
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
/// `kernel_verified` is the count that goes from `0` (structural import only) to
/// `N` (genuinely kernel-verified) for this lane — the trust-boundary shrink the
/// whole exercise is about. `failures` is the FINDING channel: any non-empty
/// value is a soundness signal that must be surfaced, never suppressed.
#[derive(Debug, Clone)]
#[must_use]
pub struct BootstrapVerifyReport {
    /// The bootstrap modules whose closure was loaded and re-checked.
    pub modules: Vec<String>,
    /// Number of distinct constant names loaded into the closure (the
    /// re-check denominator).
    pub loaded_constants: usize,
    /// Constants that PASSED the `add_decl`-equivalent kernel re-check — i.e.
    /// the count of bootstrap constants that are now genuinely `KernelVerified`.
    /// This is the `0 -> N` number.
    pub kernel_verified: usize,
    /// Constants whose kernel TRUST LEDGER origin was actually PROMOTED from
    /// `needs_recheck` (unpinned structural import) to `KernelChecked` by this
    /// pass (G5). This is a subset of `kernel_verified`: a passing constant that
    /// already carried a kernel-checked origin (or no structural-import origin)
    /// is counted as verified but not re-promoted. In a real bootstrap load
    /// (every lane constant enters via the structural `.olean` path) this equals
    /// `kernel_verified`.
    pub origins_promoted: usize,
    /// Constants that FAILED the re-check (a FINDING — see [`BootstrapFailure`]).
    pub failures: Vec<BootstrapFailure>,
    /// Wall-clock time spent in the re-check phase (load time excluded).
    pub recheck_ms: u128,
    /// Wall-clock time spent loading the closure.
    pub load_ms: u128,
}

impl BootstrapVerifyReport {
    /// Whether the whole bootstrap lane re-type-checked cleanly (every loaded
    /// constant is now `KernelVerified`, zero findings).
    #[must_use]
    pub fn all_verified(&self) -> bool {
        self.failures.is_empty() && self.kernel_verified == self.loaded_constants
    }

    /// The `KernelVerified` count for this lane — the `0 -> N` trust-boundary
    /// shrink. Alias for the `kernel_verified` field for call-site clarity.
    #[must_use]
    pub fn kernel_verified_count(&self) -> usize {
        self.kernel_verified
    }
}

/// Load the requested bootstrap modules' full dependency closure into a FRESH
/// environment and re-type-check every loaded constant with the kernel's
/// `add_decl`-equivalent checker, marking the passing set as `KernelVerified`.
///
/// This is the high-level convenience entry point: it owns the environment. Use
/// [`verify_bootstrap_lane_in_env`] to re-check a caller-owned environment (e.g.
/// one already primed with native reducers or a prelude).
///
/// * `modules` — the bootstrap module names to certify (e.g.
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
/// See the module docs: the re-check runs against an immutable `&Environment`,
/// so it can only ADD verification (a passing constant becomes `KernelVerified`)
/// and can never admit a false proof. FAILURES are surfaced in the returned
/// report's `failures`, never suppressed.
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
/// SOUNDNESS: identical to [`verify_bootstrap_lane`]. The re-check is read-only
/// over `env` (it runs against `&*env`), so loading then re-checking cannot
/// change any constant's verdict; a passing constant is genuinely
/// `KernelVerified`, a failing one is a surfaced FINDING.
pub fn verify_bootstrap_lane_in_env(
    env: &mut Environment,
    modules: &[String],
    search_paths: &[PathBuf],
    max_heartbeats: u32,
) -> Result<BootstrapVerifyReport, crate::ImportError> {
    // Snapshot the names already present so we re-check ONLY this lane's newly
    // registered constants (not any prelude the caller pre-seeded).
    let before: BTreeSet<String> = all_decl_names(env);

    let load_start = Instant::now();
    // Load the WHOLE closure in ONE shared pass: every transitive import is
    // registered in dependency order into `env`, so the re-check below sees every
    // dependency (no spurious UnknownConst failures from missing context).
    let _summaries = load_modules_with_deps(env, modules, search_paths)?;
    let load_ms = load_start.elapsed().as_millis();

    // The lane's constants = everything registered by this load that was not
    // already present.
    let after: BTreeSet<String> = all_decl_names(env);
    let lane_names: BTreeSet<String> = after.difference(&before).cloned().collect();

    let recheck_start = Instant::now();
    // SOUNDNESS: `typecheck_constants_full` is the kernel's `add_decl`-equivalent
    // re-check (`infer_sort` on types + `check_type` on values, `infer_only=false`).
    // It runs against the immutable `&*env`, so it only ADDS verification: a pass
    // is a genuine KernelVerified verdict; it can never make an ill-typed constant
    // pass, and never mutates the env or any other constant's verdict. A FAILURE
    // is recorded and returned as a finding, never suppressed.
    let (pass, _fail, errors) = typecheck_constants_full(env, &lane_names, max_heartbeats);
    let recheck_ms = recheck_start.elapsed().as_millis();

    // G5 (Pillar-2) trust-ledger promotion. The lane's constants were admitted
    // STRUCTURALLY (unpinned `.olean` origin ⇒ `needs_recheck == true`). Every
    // name that just PASSED the kernel re-check above has now genuinely been
    // re-derived by the Clean kernel, so we promote exactly those constants'
    // origins from `needs_recheck` to `KernelChecked` via the ONE sanctioned
    // gated path (`promote_origin_kernel_checked`).
    //
    // SOUNDNESS: the promotion is applied ONLY to the passing set (lane names
    // minus the error keys), strictly AFTER their own `check_type` returned Ok.
    // The gated promoter is a no-op for any constant that is not a
    // `needs_recheck` import, so a lane constant that was already kernel-checked
    // (or had no structural-import origin) is untouched. A FAILING constant is
    // never promoted — it stays `needs_recheck` and is surfaced as a finding.
    let failed_names: BTreeSet<&String> = errors.keys().collect();
    let promoted: usize = lane_names
        .iter()
        .filter(|name| !failed_names.contains(name))
        .map(|name| clean_kernel::name::Name::from_string(name))
        .filter(|kname| env.promote_origin_kernel_checked(kname))
        .count();
    // The promoted count can only be <= pass (a subset: names present in the
    // lane, passing, and carrying a needs_recheck origin). It is an accounting
    // detail, not a soundness gate; surfaced for audit visibility.
    debug_assert!(
        promoted <= pass,
        "promoted ({promoted}) must not exceed re-check passes ({pass})"
    );

    let failures = errors
        .into_iter()
        .map(|(name, error)| BootstrapFailure { name, error })
        .collect();

    Ok(BootstrapVerifyReport {
        modules: modules.to_vec(),
        loaded_constants: lane_names.len(),
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
fn all_decl_names(env: &Environment) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for c in env.constants() {
        names.insert(c.name.to_string());
    }
    for i in env.inductives() {
        names.insert(i.name.to_string());
    }
    for c in env.constructors() {
        names.insert(c.name.to_string());
    }
    for r in env.recursors() {
        names.insert(r.name.to_string());
    }
    names
}

/// Format a report's findings for a human-readable audit line.
///
/// Returns `Ok(count)` describing the `KernelVerified` shrink when clean, or a
/// multi-line finding block when there are failures. Pure formatting — never
/// suppresses a finding.
#[must_use]
pub fn format_report(report: &BootstrapVerifyReport) -> String {
    let mut out = format!(
        "bootstrap lane {:?}: {} constants loaded, {} now KernelVerified (0 -> {}), \
         {} origins promoted to KernelChecked, {} failures; load {} ms, recheck {} ms",
        report.modules,
        report.loaded_constants,
        report.kernel_verified,
        report.kernel_verified,
        report.origins_promoted,
        report.failures.len(),
        report.load_ms,
        report.recheck_ms,
    );
    if !report.failures.is_empty() {
        out.push_str("\n  FINDINGS (bootstrap constants the kernel rejected):");
        for f in &report.failures {
            out.push_str(&format!("\n    {}: {}", f.name, f.error));
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
fn failure_category(error: &str) -> String {
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

    /// A clean report formats to a single-line KernelVerified summary; a report
    /// with findings appends the finding block (never hides a finding).
    #[test]
    fn test_format_report_surfaces_findings() {
        let clean = BootstrapVerifyReport {
            modules: vec!["Init".into()],
            loaded_constants: 100,
            kernel_verified: 100,
            origins_promoted: 100,
            failures: vec![],
            recheck_ms: 5,
            load_ms: 10,
        };
        let s = format_report(&clean);
        assert!(s.contains("100 now KernelVerified"));
        assert!(!s.contains("FINDINGS"));

        let dirty = BootstrapVerifyReport {
            modules: vec!["Init".into()],
            loaded_constants: 100,
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
    }
}
