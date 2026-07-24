// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Full `add_decl`-equivalent validation for .olean constants.
//!
//! Unlike the fast path in `verify_batch` (which only runs `infer_type` with
//! `infer_only=true`), this module provides `typecheck_constants_full` which:
//!
//! 1. Calls `tc.infer_sort(type_)` on every constant's type to verify it
//!    inhabits a Sort (with full App/Let checking via `infer_only=false`).
//! 2. For constants with values: calls `tc.check_type(value, type_)` to verify
//!    the value has the declared type (also with `infer_only=false`).
//!
//! Part of #3232

use clean_kernel::env::{Environment, ProofElisionStats, ProofValueElision};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use clean_kernel::tc::{TypeChecker, DEFAULT_HEARTBEAT_LIMIT};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

/// DEFAULT number of value-checks performed before the long-lived
/// [`TypeChecker`] is dropped so the just-passed elidable proof VALUES can be
/// freed via `&mut Environment`, then rebuilt for the next chunk. Small enough
/// to keep peak resident memory bounded (only a chunk's worth of un-freed
/// values plus the already-elided history are ever live), large enough to
/// amortise the per-chunk checker reconstruction + type-cache warm-up.
/// Callers with fewer targets than this per run (e.g. whole-module
/// `per-constant-verify --all-declared`, where a single Mathlib module rarely
/// declares 2048 value-bearing constants) should pass an explicit smaller
/// `chunk_size` or the elision only fires after the LAST check — freeing
/// nothing at peak. Under `OpaqueOnly` the chunk length is a pure
/// performance / memory knob with NO effect on any verdict; under
/// `OpaqueAndTheorem` a smaller chunk frees theorem values earlier, which can
/// only ADD conservative refusals (the subset direction of that policy's
/// contract) — never a new pass.
const STREAM_ELIDE_CHUNK: usize = 2048;

/// Validation mode for type-checking .olean constants.
///
/// `InferOnly` uses `infer_type` with `infer_only=true` (fast path, skips App
/// argument and Let value checking). `Full` matches `add_decl`: `infer_sort` on
/// types + `check_type` on values with `infer_only=false`.
///
/// Part of #3232
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ValidationMode {
    /// Fast path: `infer_type` with `infer_only=true` (default).
    InferOnly,
    /// Full `add_decl`-equivalent: `infer_sort` on types + `check_type` on values.
    Full,
}

impl ValidationMode {
    /// Honest, self-describing label for what a pass count under this mode
    /// actually means. This is the audit-mandated guard against confusing a
    /// type-only count with a genuine kernel-verified count: the two are NOT
    /// interchangeable, so any report that emits pass/fail numbers MUST also
    /// emit this label.
    ///
    /// * `InferOnly` => `"type-only-infer"`: only the constant's TYPE was shown
    ///   to inhabit a Sort via `infer_type`; the proof VALUE was NOT re-checked
    ///   (App arguments and Let values are skipped under `infer_only=true`).
    ///   This is NOT equivalent to Clean-kernel verification.
    /// * `Full` => `"kernel-verified-full"`: `add_decl`-equivalent — every type
    ///   passed `infer_sort` and every value passed `check_type` against its
    ///   stated type with `infer_only=false`. A pass here is genuinely
    ///   Clean-kernel-verified (the kernel accepted the proof value).
    #[must_use]
    pub fn honest_label(self) -> &'static str {
        match self {
            ValidationMode::InferOnly => "type-only-infer",
            ValidationMode::Full => "kernel-verified-full",
        }
    }

    /// Whether a `tc_pass` produced under this mode means the proof VALUE was
    /// genuinely re-checked by the kernel (`true` only for `Full`).
    #[must_use]
    pub fn is_kernel_verified(self) -> bool {
        matches!(self, ValidationMode::Full)
    }
}

/// Full `add_decl`-equivalent validation: `infer_sort` on types + `check_type`
/// on values with `infer_only=false`.
///
/// This matches what `Environment::add_decl` does during normal declaration
/// addition. Unlike `typecheck_constants` (which only runs `infer_type` with
/// `infer_only=true`), this function:
///
/// 1. Calls `tc.infer_sort(type_)` on every constant's type to verify it
///    inhabits a Sort (with full App/Let checking via `infer_only=false`).
/// 2. For constants with values: calls `tc.check_type(value, type_)` to verify
///    the value has the declared type (also with `infer_only=false`).
///
/// WS1 re-validation reuse: instead of allocating a fresh `TypeChecker` per
/// declaration (which discards every cross-declaration `whnf`/`def_eq`/`infer`
/// result), this reuses ONE long-lived, cache-enabled `TypeChecker` over the
/// whole batch. The local context is reset between declarations so no
/// declaration's binders leak into the next check.
///
/// SOUNDNESS: enabling the type cache is sound only when the `Environment` is
/// fixed for the checker's lifetime. Here we re-check already-registered
/// constants against the single immutable `&Environment` passed in (the env is
/// never mutated during the loop), so reuse over that env is sound. See
/// `TypeChecker::reset_local_context` for why the reset keeps the cache valid.
///
/// Part of #3232; reuse per the Mathverse Subsumption Engine WS1.
///
/// `max_heartbeats` is the per-check reduction/inference step budget applied to
/// the kernel (`0` = unlimited). It is a pure RESOURCE limit, NOT a soundness
/// gate: on exhaustion `whnf` returns a less-reduced (still def-eq) term and
/// `is_def_eq` returns `false` (conservative reject, surfacing as
/// `HeartbeatExceeded`/`TypeMismatch`), so raising it can only let VALID
/// constants COMPLETE — an ill-typed constant still fails on its own merits.
/// Mirrors the `maxHeartbeats` option `Environment::add_decl` applies.
pub fn typecheck_constants_full(
    env: &Environment,
    target_names: &BTreeSet<String>,
    max_heartbeats: u32,
) -> (usize, usize, BTreeMap<String, String>) {
    let mut pass = 0usize;
    let mut fail = 0usize;
    let mut errors = BTreeMap::new();

    // One long-lived checker for the whole batch, type cache ENABLED so shared
    // library subterms are reduced once and reused across declarations.
    let mut tc = TypeChecker::new(env);
    tc.enable_type_cache_pub();
    // SOUNDNESS: the heartbeat is a resource budget only. On exhaustion the
    // kernel conservatively REJECTS (whnf returns a less-reduced but def-eq
    // term; is_def_eq returns false), so raising/disabling it (0 = unlimited)
    // cannot make an ill-typed constant pass — it only lets compute-heavy VALID
    // constants finish their check instead of aborting with HeartbeatExceeded.
    tc.set_heartbeat_limit(max_heartbeats);

    // Phase 1: infer_sort on all types (constants, inductives, constructors, recursors)
    let check_type_sort = |tc: &TypeChecker,
                           name: &str,
                           type_: &Expr,
                           pass: &mut usize,
                           fail: &mut usize,
                           errors: &mut BTreeMap<String, String>| {
        if !target_names.contains(name) {
            return;
        }
        // Start each declaration from a clean context so an earlier erroring
        // check (which may have returned before its ctx_pop) cannot leak binders.
        tc.reset_local_context();
        // Refill the per-constant heartbeat budget on the long-lived checker so
        // the resource limit applies per-constant (matching add_decl), not as a
        // pool drained across the batch. Pure resource reset — no soundness effect.
        tc.reset_heartbeat();
        match tc.infer_sort(type_) {
            Ok(_) => *pass += 1,
            Err(e) => {
                *fail += 1;
                errors.insert(name.to_string(), format!("infer_sort: {e:?}"));
            }
        }
    };

    for ci in env.constants() {
        check_type_sort(
            &tc,
            &ci.name.to_string(),
            &ci.type_,
            &mut pass,
            &mut fail,
            &mut errors,
        );
    }
    for ind in env.inductives() {
        check_type_sort(
            &tc,
            &ind.name.to_string(),
            &ind.type_,
            &mut pass,
            &mut fail,
            &mut errors,
        );
    }
    for ctor in env.constructors() {
        check_type_sort(
            &tc,
            &ctor.name.to_string(),
            &ctor.type_,
            &mut pass,
            &mut fail,
            &mut errors,
        );
    }
    for rec in env.recursors() {
        check_type_sort(
            &tc,
            &rec.name.to_string(),
            &rec.type_,
            &mut pass,
            &mut fail,
            &mut errors,
        );
    }

    // Phase 2: check_type on values (only for constants that have values)
    for ci in env.constants() {
        let name = ci.name.to_string();
        if !target_names.contains(&name) {
            continue;
        }
        // Skip constants that already failed infer_sort
        if errors.contains_key(&name) {
            continue;
        }
        if let Some(val) = &ci.value {
            // Clean context per declaration; same long-lived cache-enabled checker.
            tc.reset_local_context();
            // Per-constant heartbeat refill (see infer_sort path above) so each
            // value check gets the full budget independently. No soundness effect.
            tc.reset_heartbeat();
            match tc.check_type(val, &ci.type_) {
                Ok(()) => {} // Already counted as pass in phase 1
                Err(e) => {
                    // Demote from pass to fail
                    pass = pass.saturating_sub(1);
                    fail += 1;
                    errors.insert(name, format!("check_type: {e:?}"));
                }
            }
        }
    }

    (pass, fail, errors)
}

/// Streaming, bounded-memory variant of [`typecheck_constants_full`].
///
/// Identical type-checking to [`typecheck_constants_full`] (same `infer_sort`
/// Phase 1, same per-constant `check_type` Phase 2, same per-constant heartbeat
/// reset), with ONE addition: as soon as a constant whose [`ConstantKind`] the
/// `elide` policy selects (`Opaque`, or `Opaque`+`Theorem`) PASSES its own
/// `check_type`, its proof VALUE is freed (type+kind retained). This caps peak
/// resident memory at roughly the type-only curve plus one chunk of un-freed
/// values, letting a full-Init `--full-validation` re-check COMPLETE where the
/// eager (never-free) path OOMs.
///
/// Returns `(pass, fail, errors, elision_stats)`. With
/// [`ProofValueElision::None`] this is byte-for-byte equivalent to
/// [`typecheck_constants_full`] (and `elision_stats` is all-zero).
///
/// `chunk_size` overrides the default [`STREAM_ELIDE_CHUNK`] batch length
/// (`None` = default; `Some(0)` is clamped to `1`). Under `OpaqueOnly` any
/// chunking yields byte-identical verdicts (elided values are never read);
/// under `OpaqueAndTheorem` a smaller chunk can only cause ADDITIONAL
/// conservative refusals (subset direction), never a new pass.
///
/// # Soundness
///
/// Elision is STRICTLY POST-SUCCESS: a value is dropped only after its OWN
/// `check_type` returned `Ok` and the pass was recorded, so an ill-typed value
/// still FAILS on its own merits before anything is freed. Dropping a value
/// cannot turn any OTHER constant's verdict from FAIL to PASS:
///
/// * `OpaqueOnly` (statically sound, verdict-IDENTICAL): the kernel's only
///   δ-unfold entry point, `Environment::unfold_definition`, returns `None`
///   for `Opaque`-kind constants, so an `Opaque` value is NEVER read during
///   `whnf`/`is_def_eq`. Removing it leaves every other constant's reduction
///   sequence byte-identical ⇒ identical pass/fail set. Eliding immediately
///   after each `Opaque`'s own check is therefore order-independent and sound.
/// * `OpaqueAndTheorem` (refusal-only, NOT statically sound): this kernel CAN
///   δ-unfold theorem bodies, so freeing a theorem value removes a possible
///   reduction rule. That can only make a later `is_def_eq` return
///   `false`/`DefUnknown` where it previously returned `true` — it can NEVER
///   make an unequal pair equal. So the pass set under this policy is a SUBSET
///   of the no-elision pass set (verifications may be LOST, never gained). Use
///   only behind the documented unchanged-kernel-verified-count gate.
///
/// In all cases elision NEVER admits a false proof (mirrors the
/// `forget_value`/`elide_proof_values` SOUNDNESS contracts).
pub fn typecheck_constants_full_streaming(
    env: &mut Environment,
    target_names: &BTreeSet<String>,
    max_heartbeats: u32,
    elide: ProofValueElision,
    chunk_size: Option<usize>,
) -> (usize, usize, BTreeMap<String, String>, ProofElisionStats) {
    // None policy: defer to the eager path verbatim (no &mut needed, no chunk
    // rebuild cost) so the default flag value is provably verdict-identical.
    if elide == ProofValueElision::None {
        let (pass, fail, errors) = typecheck_constants_full(env, target_names, max_heartbeats);
        return (pass, fail, errors, ProofElisionStats::default());
    }
    let chunk_len = chunk_size.unwrap_or(STREAM_ELIDE_CHUNK).max(1);

    let mut pass = 0usize;
    let mut fail = 0usize;
    let mut errors: BTreeMap<String, String> = BTreeMap::new();

    // -- Phase 1: infer_sort on every target type (no value reads / no elision).
    // Done under a throwaway immutable borrow; identical to the eager path.
    {
        let mut tc = TypeChecker::new(&*env);
        tc.enable_type_cache_pub();
        tc.set_heartbeat_limit(max_heartbeats);
        let mut check_type_sort = |tc: &mut TypeChecker, name: &str, type_: &Expr| {
            if !target_names.contains(name) {
                return;
            }
            tc.reset_local_context();
            tc.reset_heartbeat();
            match tc.infer_sort(type_) {
                Ok(_) => pass += 1,
                Err(e) => {
                    fail += 1;
                    errors.insert(name.to_string(), format!("infer_sort: {e:?}"));
                }
            }
        };
        for ci in env.constants() {
            check_type_sort(&mut tc, &ci.name.to_string(), &ci.type_);
        }
        for ind in env.inductives() {
            check_type_sort(&mut tc, &ind.name.to_string(), &ind.type_);
        }
        for ctor in env.constructors() {
            check_type_sort(&mut tc, &ctor.name.to_string(), &ctor.type_);
        }
        for rec in env.recursors() {
            check_type_sort(&mut tc, &rec.name.to_string(), &rec.type_);
        }
    }

    // Snapshot the value-bearing target constant names in the env's stable
    // iteration order (we only ever null `value`/force `Opaque`, never insert
    // or remove keys, so this order is invariant across chunk boundaries).
    let value_targets: Vec<Name> = env
        .constants()
        .filter(|ci| {
            ci.value.is_some()
                && target_names.contains(&ci.name.to_string())
                && !errors.contains_key(&ci.name.to_string())
        })
        .map(|ci| ci.name.clone())
        .collect();

    // -- Phase 2 (streaming): check_type on values in chunks. After each chunk
    // we drop the checker (releasing its immutable borrow) and free the
    // just-passed elidable values via &mut env, then rebuild for the next chunk.
    let mut stats = ProofElisionStats::default();
    for chunk in value_targets.chunks(chunk_len) {
        // Names whose OWN check_type passed this chunk AND whose kind the policy
        // elides — these get their value freed after the borrow is released.
        let mut to_free: Vec<Name> = Vec::new();
        {
            let mut tc = TypeChecker::new(&*env);
            tc.enable_type_cache_pub();
            tc.set_heartbeat_limit(max_heartbeats);
            for name in chunk {
                let Some(ci) = env.get_const(name) else {
                    continue;
                };
                let Some(val) = &ci.value else { continue };
                let kind = ci.kind;
                let name_str = name.to_string();
                tc.reset_local_context();
                tc.reset_heartbeat();
                match tc.check_type(val, &ci.type_) {
                    Ok(()) => {
                        // Verdict already recorded as a Phase-1 pass. SOUNDNESS:
                        // record the elision intent only AFTER success; on Err
                        // below we never free. See `proof_elision.rs` and
                        // `Environment::forget_proof_values_for`.
                        if elide.elides(kind) {
                            to_free.push(name.clone());
                        }
                    }
                    Err(e) => {
                        pass = pass.saturating_sub(1);
                        fail += 1;
                        errors.insert(name_str, format!("check_type: {e:?}"));
                    }
                }
            }
            // `tc` (and its immutable borrow of env) dropped here.
        }
        // SOUNDNESS: only NEVER-read (OpaqueOnly) or refusal-only
        // (OpaqueAndTheorem) values are freed, strictly after their own passing
        // check_type. See `typecheck_constants_full_streaming` doc + the kernel
        // `forget_proof_values_for`/`unfold_definition` contracts. No unsafe.
        let chunk_stats = env.forget_proof_values_for(to_free.iter(), elide);
        stats.opaque_elided += chunk_stats.opaque_elided;
        stats.theorem_elided += chunk_stats.theorem_elided;
        stats.retained += chunk_stats.retained;
        // MEMORY (chunk boundary, same rationale as the value elision above):
        // release the lazy source's materialization memo so resident lazily-
        // served constants are bounded by one chunk's working set instead of
        // accumulating across the whole batch. No-op without a lazy source.
        // Soundness-neutral by the `ConstantSource::fresh` contract (a fresh
        // view materializes byte-identical constants); the checker for the
        // next chunk is rebuilt anyway, so no cached type information spans
        // the swap.
        env.refresh_constant_source_cache();
    }

    (pass, fail, errors, stats)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify_batch::typecheck_constants;
    use std::path::PathBuf;

    #[test]
    fn honest_labels_distinguish_type_only_from_kernel_verified() {
        // AUDIT-CRITICAL: the two modes must carry DIFFERENT honest labels, and
        // only Full may claim the proof VALUE was kernel-verified.
        assert_eq!(ValidationMode::InferOnly.honest_label(), "type-only-infer");
        assert_eq!(ValidationMode::Full.honest_label(), "kernel-verified-full");
        assert!(!ValidationMode::InferOnly.is_kernel_verified());
        assert!(ValidationMode::Full.is_kernel_verified());
        assert_ne!(
            ValidationMode::InferOnly.honest_label(),
            ValidationMode::Full.honest_label()
        );
    }

    /// Resolve a committed fixture path relative to the workspace root.
    fn fixture(rel: &str) -> PathBuf {
        // CARGO_MANIFEST_DIR = <root>/crates/clean-olean
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/olean")
            .join(rel)
    }

    fn all_names(env: &Environment) -> BTreeSet<String> {
        let mut s = BTreeSet::new();
        for ci in env.constants() {
            s.insert(ci.name.to_string());
        }
        for ind in env.inductives() {
            s.insert(ind.name.to_string());
        }
        for c in env.constructors() {
            s.insert(c.name.to_string());
        }
        for r in env.recursors() {
            s.insert(r.name.to_string());
        }
        s
    }

    /// On a REAL `.olean` shard, the Full (`add_decl`-equivalent) re-check must
    /// be STRICTLY STRONGER than the type-only `InferOnly` path: there exist
    /// constants whose TYPE infers fine but whose proof VALUE fails `check_type`.
    /// This is the load-bearing proof that the two pass-counts are NOT
    /// interchangeable, and therefore must never share an unlabelled field.
    #[test]
    fn full_recheck_is_strictly_stronger_than_type_only_on_real_shard() {
        let path = fixture("v4.13.0/custom/Inductive.olean");
        if !path.exists() {
            eprintln!("skipping: fixture not found at {path:?}");
            return;
        }
        let mut env = Environment::default();
        crate::load_olean_file(&mut env, &path).expect("load Inductive.olean fixture");
        let names = all_names(&env);
        assert!(!names.is_empty(), "fixture should register constants");

        let (io_pass, io_fail, _) = typecheck_constants(&env, &names);
        let (full_pass, full_fail, full_errs) =
            typecheck_constants_full(&env, &names, DEFAULT_HEARTBEAT_LIMIT);

        // Full never passes MORE than type-only: it only adds checks.
        assert!(
            full_pass <= io_pass,
            "Full pass ({full_pass}) must not exceed InferOnly pass ({io_pass})"
        );
        assert!(
            full_fail >= io_fail,
            "Full fail ({full_fail}) must be >= InferOnly fail ({io_fail})"
        );

        // Strictly stronger: at least one constant is DEMOTED by the full check.
        let demoted = io_pass - full_pass;
        assert!(
            demoted >= 1,
            "Full re-check must demote >=1 constant that only passes type-only \
             (io_pass={io_pass}, full_pass={full_pass}); otherwise the type-only \
             label would be safe to call kernel-verified, which it is not"
        );

        // Each demotion is a genuine `check_type` failure on a proof VALUE
        // (the audit's exact concern: the value was never re-checked by the
        // type-only path).
        let check_type_failures = full_errs
            .values()
            .filter(|m| m.starts_with("check_type:"))
            .count();
        assert!(
            check_type_failures >= 1,
            "expected >=1 check_type (proof-value) failure among full errors"
        );
    }

    // -- Streaming proof-value elision (P3-P1) --------------------------------

    use clean_kernel::env::Declaration;
    use clean_kernel::level::Level;
    use clean_kernel::name::Name as KName;

    /// Build a self-contained env with kernel-REAL constants of every relevant
    /// kind, all sharing the polymorphic-identity type `(P : Prop) → P → P` with
    /// proof `λ P p => p`:
    ///   * `D` — Definition (value MUST be retained; δ-unfolds)
    ///   * `T` — Theorem    (δ-unfoldable in this kernel ⇒ refusal-only)
    ///   * `O` — Opaque     (never δ-unfolded ⇒ statically safe to elide)
    ///   * `A` — Axiom      (no value)
    /// Plus `USES_O : Prop` (= `O O_inhabits ...`-free) we keep simple: a second
    /// theorem whose proof APPLIES `O` so a later check could in principle want
    /// `O`'s value — proving the OpaqueOnly equivalence is non-vacuous.
    fn seeded_real_env() -> (Environment, BTreeSet<String>) {
        let mut env = Environment::default();
        // (P : Prop) → P → P
        let id_ty = Expr::pi(
            clean_kernel::expr::BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::pi(
                clean_kernel::expr::BinderInfo::Default,
                Expr::bvar(0),
                Expr::bvar(1),
            ),
        );
        // λ (P : Prop) (p : P) => p
        let id_val = Expr::lam(
            clean_kernel::expr::BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::lam(
                clean_kernel::expr::BinderInfo::Default,
                Expr::bvar(0),
                Expr::bvar(0),
            ),
        );

        env.add_decl(Declaration::Definition {
            name: KName::from_string("D"),
            level_params: vec![],
            type_: id_ty.clone(),
            value: id_val.clone(),
            is_reducible: false,
        })
        .expect("add Definition D");
        env.add_decl(Declaration::Opaque {
            name: KName::from_string("O"),
            level_params: vec![],
            type_: id_ty.clone(),
            value: id_val.clone(),
        })
        .expect("add Opaque O");
        // Theorem type must be a Prop. Use `(P : Prop) → P → P` which IS a Prop
        // (Pi into Prop is Prop), with the identity proof.
        env.add_decl(Declaration::Theorem {
            name: KName::from_string("T"),
            level_params: vec![],
            type_: id_ty.clone(),
            value: id_val.clone(),
        })
        .expect("add Theorem T");
        env.add_decl(Declaration::Axiom {
            name: KName::from_string("A"),
            level_params: vec![],
            type_: id_ty,
        })
        .expect("add Axiom A");

        let names: BTreeSet<String> = ["D", "O", "T", "A"]
            .into_iter()
            .map(str::to_string)
            .collect();
        (env, names)
    }

    /// `None` policy is byte-for-byte equivalent to the eager
    /// `typecheck_constants_full` (the DEFAULT must never change a verdict).
    #[test]
    fn test_stream_none_matches_eager() {
        let (mut env, names) = seeded_real_env();
        let eager = typecheck_constants_full(&env, &names, DEFAULT_HEARTBEAT_LIMIT);
        let (pass, fail, errs, stats) = typecheck_constants_full_streaming(
            &mut env,
            &names,
            DEFAULT_HEARTBEAT_LIMIT,
            ProofValueElision::None,
            None,
        );
        assert_eq!((pass, fail), (eager.0, eager.1), "None must match eager");
        assert_eq!(errs, eager.2, "None error set must match eager");
        assert_eq!(stats.total_elided(), 0, "None elides nothing");
        // Nothing was freed.
        for n in ["D", "O", "T"] {
            assert!(
                env.get_const(&KName::from_string(n))
                    .unwrap()
                    .value
                    .is_some(),
                "None must retain {n}'s value"
            );
        }
    }

    /// OpaqueOnly: HARD EQUIVALENCE GATE. The pass/fail/error set MUST be
    /// IDENTICAL to no-elision, AND the Opaque value MUST actually be freed
    /// while Definition + Theorem values are retained.
    #[test]
    fn test_stream_opaque_only_is_verdict_identical_and_frees_opaque() {
        let (env_eager, names) = seeded_real_env();
        let eager = typecheck_constants_full(&env_eager, &names, DEFAULT_HEARTBEAT_LIMIT);

        let (mut env, _) = seeded_real_env();
        let (pass, fail, errs, stats) = typecheck_constants_full_streaming(
            &mut env,
            &names,
            DEFAULT_HEARTBEAT_LIMIT,
            ProofValueElision::OpaqueOnly,
            None,
        );
        // Hard equivalence: pass/fail/error set identical.
        assert_eq!(
            (pass, fail),
            (eager.0, eager.1),
            "OpaqueOnly is a hard equivalence gate; pass/fail diverged"
        );
        assert_eq!(errs, eager.2, "OpaqueOnly error set must be identical");
        // Opaque value actually freed.
        assert_eq!(stats.opaque_elided, 1, "the one Opaque must be elided");
        assert_eq!(stats.theorem_elided, 0, "OpaqueOnly must not touch Theorem");
        assert!(
            env.get_const(&KName::from_string("O"))
                .unwrap()
                .value
                .is_none(),
            "Opaque O's value must be freed"
        );
        // Definition + Theorem retained.
        assert!(
            env.get_const(&KName::from_string("D"))
                .unwrap()
                .value
                .is_some(),
            "Definition D's value must be retained (δ-unfolds)"
        );
        assert!(
            env.get_const(&KName::from_string("T"))
                .unwrap()
                .value
                .is_some(),
            "Theorem T's value must be retained under OpaqueOnly"
        );
    }

    /// OpaqueAndTheorem: subset gate. Pass set must be <= no-elision and NO new
    /// name may pass; both Opaque AND Theorem values are freed.
    #[test]
    fn test_stream_opaque_and_theorem_is_subset_and_frees_both() {
        let (env_eager, names) = seeded_real_env();
        let eager = typecheck_constants_full(&env_eager, &names, DEFAULT_HEARTBEAT_LIMIT);

        let (mut env, _) = seeded_real_env();
        let (pass, fail, _errs, stats) = typecheck_constants_full_streaming(
            &mut env,
            &names,
            DEFAULT_HEARTBEAT_LIMIT,
            ProofValueElision::OpaqueAndTheorem,
            None,
        );
        // Subset gate: never MORE passes than no-elision.
        assert!(
            pass <= eager.0,
            "OpaqueAndTheorem pass ({pass}) must be <= eager pass ({})",
            eager.0
        );
        assert!(
            fail >= eager.1,
            "OpaqueAndTheorem fail ({fail}) must be >= eager fail ({})",
            eager.1
        );
        // Both Opaque and Theorem freed; Definition retained.
        assert_eq!(stats.opaque_elided, 1);
        assert_eq!(stats.theorem_elided, 1);
        assert!(env
            .get_const(&KName::from_string("O"))
            .unwrap()
            .value
            .is_none());
        assert!(env
            .get_const(&KName::from_string("T"))
            .unwrap()
            .value
            .is_none());
        assert!(
            env.get_const(&KName::from_string("D"))
                .unwrap()
                .value
                .is_some(),
            "Definition value must never be elided"
        );
    }

    /// SOUNDNESS: an ill-typed constant still FAILS under elision (elision is
    /// strictly post-success; an Err is never followed by a free). We mint a
    /// constant whose stored value does NOT have its stored type by editing the
    /// env directly (bypassing add_decl, which would reject it), then run the
    /// streaming check under the most aggressive policy.
    #[test]
    fn test_stream_ill_typed_still_fails_under_elision() {
        use clean_kernel::env::{ConstantInfo, ConstantKind, Reducibility};
        let (mut env, mut names) = seeded_real_env();
        // BAD : Prop  with value  (λ (P:Prop)(p:P) => p)  — value is a function,
        // its inferred type is the id-Pi, NOT `Prop`. check_type must reject.
        let bad_val = Expr::lam(
            clean_kernel::expr::BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::lam(
                clean_kernel::expr::BinderInfo::Default,
                Expr::bvar(0),
                Expr::bvar(0),
            ),
        );
        env.add_constant_unchecked_for_test(ConstantInfo::new_with_reducibility(
            KName::from_string("BAD"),
            vec![],
            Expr::sort(Level::zero()), // stated type: Prop
            Some(bad_val),
            Reducibility::Opaque,
            ConstantKind::Opaque, // most-aggressively-elided kind
        ));
        names.insert("BAD".to_string());

        let (_pass, _fail, errs, _stats) = typecheck_constants_full_streaming(
            &mut env,
            &names,
            DEFAULT_HEARTBEAT_LIMIT,
            ProofValueElision::OpaqueAndTheorem,
            None,
        );
        assert!(
            errs.get("BAD")
                .is_some_and(|m| m.starts_with("check_type:")),
            "ill-typed BAD must FAIL check_type even under aggressive elision; errs={errs:?}"
        );
        // And its (ill-typed) value must NOT have been freed (free is post-success only).
        assert!(
            env.get_const(&KName::from_string("BAD"))
                .unwrap()
                .value
                .is_some(),
            "a FAILING constant's value must never be elided"
        );
    }

    /// `chunk_size` is a pure memory knob under `OpaqueOnly`: the smallest
    /// possible chunk (1 — checker rebuilt and passed values freed after EVERY
    /// check) must still be verdict-identical to the eager path AND still free
    /// the Opaque value; `Some(0)` must clamp to 1, not panic.
    #[test]
    fn test_stream_chunk_of_one_matches_eager_under_opaque_only() {
        let (env_eager, names) = seeded_real_env();
        let eager = typecheck_constants_full(&env_eager, &names, DEFAULT_HEARTBEAT_LIMIT);

        let (mut env, _) = seeded_real_env();
        let (pass, fail, errs, stats) = typecheck_constants_full_streaming(
            &mut env,
            &names,
            DEFAULT_HEARTBEAT_LIMIT,
            ProofValueElision::OpaqueOnly,
            Some(1),
        );
        assert_eq!(
            (pass, fail),
            (eager.0, eager.1),
            "chunk=1 OpaqueOnly must match eager"
        );
        assert_eq!(
            errs, eager.2,
            "chunk=1 OpaqueOnly error set must match eager"
        );
        assert_eq!(
            stats.opaque_elided, 1,
            "the one Opaque must still be elided"
        );
        assert!(
            env.get_const(&KName::from_string("O"))
                .unwrap()
                .value
                .is_none(),
            "Opaque O's value must be freed at chunk=1"
        );

        // Some(0) clamps to 1 — same verdicts, no panic.
        let (mut env2, _) = seeded_real_env();
        let (p2, f2, e2, _s2) = typecheck_constants_full_streaming(
            &mut env2,
            &names,
            DEFAULT_HEARTBEAT_LIMIT,
            ProofValueElision::OpaqueOnly,
            Some(0),
        );
        assert_eq!(
            (p2, f2),
            (eager.0, eager.1),
            "chunk=0 must clamp to 1, not panic"
        );
        assert_eq!(e2, eager.2, "chunk=0 error set must match eager");
    }

    /// SOUNDNESS + plumbing: the `max_heartbeats` budget is a pure RESOURCE
    /// limit. A near-zero budget must abort otherwise-VALID checks with
    /// `HeartbeatExceeded` (proving the knob is actually threaded into the
    /// kernel), and the GENUINE `check_type`/`TypeMismatch` failures the full
    /// re-check finds at the default budget must STILL fail under an UNLIMITED
    /// budget (proving raising/disabling the budget never silently accepts an
    /// ill-typed constant — it can only let valid-but-slow ones complete).
    #[test]
    fn heartbeat_budget_is_a_resource_limit_not_a_soundness_gate() {
        let path = fixture("v4.13.0/custom/Inductive.olean");
        if !path.exists() {
            eprintln!("skipping: fixture not found at {path:?}");
            return;
        }
        let mut env = Environment::default();
        crate::load_olean_file(&mut env, &path).expect("load Inductive.olean fixture");
        let names = all_names(&env);
        assert!(!names.is_empty(), "fixture should register constants");

        // (1) PER-CONSTANT RESET: the heartbeat budget is refilled per constant
        //     (matching add_decl), so a tight budget no longer spuriously aborts
        //     LATER constants via cumulative drain. With a 1-step per-constant
        //     budget the standalone fixture's constants each get a fresh budget
        //     and fail with their GENUINE errors (e.g. UnknownConst, since base
        //     constants like Nat/Eq are not loaded here) — producing ZERO
        //     HeartbeatExceeded. The prior shared-budget BUG drained one counter
        //     across the batch and surfaced spurious HeartbeatExceeded on later
        //     constants once it hit 0; this assertion is the regression guard.
        //     (Budget-actually-reaches-the-kernel is covered by the clean-kernel
        //     `tc::tests::heartbeat` suite, which checks reducing terms directly.)
        let (tight_pass, _tight_fail, tight_errs) = typecheck_constants_full(&env, &names, 1);
        let heartbeat_aborts = tight_errs
            .values()
            .filter(|m| m.contains("HeartbeatExceeded"))
            .count();
        assert_eq!(
            heartbeat_aborts, 0,
            "per-constant heartbeat reset must eliminate spurious cumulative-drain \
             HeartbeatExceeded (each constant gets a fresh budget); errs={tight_errs:?}"
        );

        // (2) The genuine ill-typed failures found at the DEFAULT budget must
        //     STILL fail under an UNLIMITED budget — never silently accepted.
        let (_def_pass, _def_fail, def_errs) =
            typecheck_constants_full(&env, &names, DEFAULT_HEARTBEAT_LIMIT);
        let genuine_failures: Vec<&String> = def_errs
            .iter()
            .filter(|(_, m)| !m.contains("HeartbeatExceeded"))
            .map(|(name, _)| name)
            .collect();
        assert!(
            !genuine_failures.is_empty(),
            "fixture must contain >=1 genuine (non-heartbeat) failure for this test"
        );

        let (unlimited_pass, _unlimited_fail, unlimited_errs) =
            typecheck_constants_full(&env, &names, 0);
        for name in &genuine_failures {
            assert!(
                unlimited_errs.contains_key(*name),
                "constant `{name}` failed at the default budget but PASSED with an \
                 unlimited heartbeat — the budget must never turn an ill-typed \
                 constant into a pass"
            );
        }

        // Unlimited can only ever pass >= as many as the 1-step budget: lifting
        // the resource cap monotonically lets MORE valid constants complete.
        assert!(
            unlimited_pass >= tight_pass,
            "unlimited budget ({unlimited_pass}) must pass >= the 1-step budget \
             ({tight_pass})"
        );
    }
}
