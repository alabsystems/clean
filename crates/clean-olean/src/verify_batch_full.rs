// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Full local type/value consistency checks for .olean declarations.
//!
//! Everything in the supplied environment that is NOT a checked declaration is
//! assumed (the trusted starting environment, as the imports are for Lean's
//! `replayFromImports`). The checked declarations themselves are REPLAYED in
//! Lean's order (`verify_batch_replay.rs`, porting `Lean/Replay.lean`): each
//! is admitted only after every checked declaration it uses, a declaration
//! that mentions itself or sits on a dependency cycle is refused, and so is
//! every dependent of a refused one. Every check runs in Lean's kernel theory
//! (`KernelTheory::Lean`). A checked inductive block is replayed as Lean's
//! replay does (`crate::replay_families`): rebuilt from its stored types by the
//! kernel, with every stored constructor and recursor required to equal the
//! regenerated one. This is still NOT import authority: declarations outside
//! the checked set are assumed as registered.
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
#[cfg(test)]
use clean_kernel::expr::Expr;
#[cfg(test)]
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

#[path = "local_check_roster.rs"]
pub(crate) mod local_roster;
#[path = "verify_batch_replay.rs"]
pub(crate) mod replay_check;

pub use replay_check::ReplayScope;

/// [`typecheck_constants_full`] with a caller-built [`ReplayScope`], keeping
/// every scheduled declaration's verdict in Lean's replay order: the engine of
/// `clean olean replay` (`crate::replay_module`), which reports the first
/// refusal as `leanchecker` does, and of the NDJSON front door
/// (`crate::ndjson`).
pub(crate) fn typecheck_constants_full_ordered(
    env: &Environment,
    target_names: &BTreeSet<String>,
    scope: &ReplayScope<'_>,
    max_heartbeats: u32,
) -> replay_check::OrderedReplay {
    replay_check::full_ordered(env, target_names, scope, max_heartbeats)
}

/// DEFAULT number of value-checks performed before the long-lived
/// `TypeChecker` is dropped so the just-passed elidable proof VALUES can be
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
/// argument and Let value checking). `Full` locally checks `infer_sort` on
/// types + `check_type` on values with `infer_only=false`.
///
/// Part of #3232
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ValidationMode {
    /// Fast path: `infer_type` with `infer_only=true` (default).
    InferOnly,
    /// Local `infer_sort` on types + `check_type` on values in an assumed env.
    Full,
}

impl ValidationMode {
    /// Honest, self-describing label for what a pass count under this mode
    /// actually means. Any report that emits pass/fail numbers MUST also emit
    /// this label.
    ///
    /// * `InferOnly` => `"type-only-infer"`: only the constant's TYPE was shown
    ///   to inhabit a Sort via `infer_type`; the proof VALUE was NOT re-checked
    ///   (App arguments and Let values are skipped under `infer_only=true`).
    /// * `Full` => `"local-assumed-env"`: every represented type and value
    ///   passed local checking with `infer_only=false`, IN THE ENVIRONMENT THAT
    ///   ALREADY HOLDS EVERY OTHER IMPORTED DECLARATION.
    ///
    /// # The label this used to emit
    ///
    /// Until 2026-09-17 `Full` emitted `"kernel-verified-full"`, and reports
    /// read that as "`add_decl`-equivalent". It is not: this function's own
    /// module doc says the check is "NOT fresh `add_decl`, dependency-closed
    /// replay, inductive-rule validation, or import authority". The label now
    /// matches [`crate::recheck_closed::RecheckLevel::LocalAssumedEnv`], whose
    /// [`proves`](crate::recheck_closed::RecheckLevel::proves) /
    /// [`does_not_prove`](crate::recheck_closed::RecheckLevel::does_not_prove)
    /// text is the sanctioned wording for a pass at this level, and the
    /// dependency-closed level has its own token.
    #[must_use]
    pub(crate) fn honest_label(self) -> &'static str {
        match self {
            ValidationMode::InferOnly => "type-only-infer",
            ValidationMode::Full => crate::recheck_closed::RecheckLevel::LocalAssumedEnv.token(),
        }
    }

    /// The re-check level this mode actually reaches.
    ///
    /// Neither mode is dependency-closed, so neither may ground a
    /// `Certified`-class claim: see
    /// [`RecheckLevel::may_ground_certified_class`](crate::recheck_closed::RecheckLevel::may_ground_certified_class)
    /// and [`crate::recheck_closed::recheck_closed`], which is the level that
    /// can.
    #[must_use]
    pub(crate) fn recheck_level(self) -> crate::recheck_closed::RecheckLevel {
        // `InferOnly` is strictly weaker than `Full`, and both are local: they
        // differ in how much of ONE declaration they re-derive, not in how much
        // of the cone they visit (neither visits any of it).
        crate::recheck_closed::RecheckLevel::LocalAssumedEnv
    }

    /// Whether a `tc_pass` produced under this mode means the proof VALUE was
    /// re-derived at all (`true` only for `Full`).
    ///
    /// This says "the value was re-derived **against the assumed
    /// environment**" and nothing more — in particular NOT that the
    /// declaration was freshly admitted, that its dependencies were checked, or
    /// that any inductive computation rule was validated. A caller that wants
    /// those must run [`crate::recheck_closed::recheck_closed`].
    #[must_use]
    pub(crate) fn rederives_values_locally(self) -> bool {
        matches!(self, ValidationMode::Full)
    }
}

/// Full LOCAL validation: `infer_sort` on types + `check_type` on values,
/// with `infer_only=false`, against the already-populated environment.
///
/// Returns one verdict per exact typed declaration identity, plus an explicit
/// failure per missing requested display label. Ambiguous display labels and
/// incoherent registry mirrors fail, without skipping represented type checks.
/// Unlike `typecheck_constants`' legacy type-projection count, this function:
///
/// 1. Calls `tc.infer_sort(type_)` on every constant's type to verify it
///    inhabits a Sort (with full App/Let checking via `infer_only=false`).
/// 2. For constants with values: calls `tc.check_type(value, type_)` to verify
///    the value has the declared type (also with `infer_only=false`).
///
/// The targets are checked in REPLAY ORDER (`Lean.Environment.replay`, see
/// `verify_batch_replay.rs`): a target is admitted only after every target it
/// uses; one that mentions itself, sits on a dependency cycle, is `unsafe`, or
/// uses a refused target fails with a `replay order:` error, even though the
/// supplied environment already holds it. Checks run in `KernelTheory::Lean`.
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
    let none = BTreeSet::new();
    let no_redeclarations = BTreeMap::new();
    let scope = ReplayScope {
        prerequisites: &none,
        not_admitted: &none,
        already_declared: &no_redeclarations,
    };
    replay_check::full(env, target_names, &scope, max_heartbeats)
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
    typecheck_constants_full_streaming_with_prerequisites(
        env,
        target_names,
        &BTreeSet::new(),
        max_heartbeats,
        elide,
        chunk_size,
    )
}

/// [`typecheck_constants_full_streaming`] with PREREQUISITES: declarations of
/// the same module that are checked and admitted in replay order before any
/// target that uses them, but are never counted in the result.
///
/// `Lean.Environment.Replay.replayConstant` replays every constant a
/// declaration uses before the declaration itself, so checking one target of a
/// module means checking the module-mates it reaches. A caller that re-checks a
/// SUBSET of a module (`clean mathverse per-constant-verify --constant`) passes
/// the module's other resident declarations here; otherwise a trusted
/// module-mate could vouch for a target it depends on (measured: `--constant
/// forged3_cycA` passed with `forged3_cycB := forged3_cycA` resident).
/// A target whose prerequisite is refused is refused, naming it.
pub(crate) fn typecheck_constants_full_streaming_with_prerequisites(
    env: &mut Environment,
    target_names: &BTreeSet<String>,
    prerequisites: &BTreeSet<String>,
    max_heartbeats: u32,
    elide: ProofValueElision,
    chunk_size: Option<usize>,
) -> (usize, usize, BTreeMap<String, String>, ProofElisionStats) {
    let scope = ReplayScope {
        prerequisites,
        not_admitted: &BTreeSet::new(),
        already_declared: &BTreeMap::new(),
    };
    streaming_in_scope(env, target_names, scope, max_heartbeats, elide, chunk_size)
}

/// [`typecheck_constants_full_streaming`] with a caller-built [`ReplayScope`]:
/// prerequisites, an earlier module's refusals, and the module's declarations
/// Lean's `addDecl` would refuse as already declared (the name was held before
/// the module was added: `clean mathverse per-constant-verify` finds them in
/// the target's import closure).
pub fn typecheck_constants_full_streaming_scoped(
    env: &mut Environment,
    target_names: &BTreeSet<String>,
    scope: ReplayScope<'_>,
    max_heartbeats: u32,
    elide: ProofValueElision,
    chunk_size: Option<usize>,
) -> (usize, usize, BTreeMap<String, String>, ProofElisionStats) {
    streaming_in_scope(env, target_names, scope, max_heartbeats, elide, chunk_size)
}

/// [`typecheck_constants_full_streaming`] for one module of a MULTI-module run
/// (`clean olean verify-batch --full-validation`, which loads module after
/// module into one environment). `not_admitted` holds the display spellings of
/// every declaration an earlier module of the run refused. Those stay resident
/// (the loader registered them), but in Lean's replay of the whole run they
/// were never added. So a target that mentions one is refused, where before it
/// type-checked against the refused declaration's type. Measured 2026-09-24:
/// `ReplayCrossB.cross_uses_forged : False := cross_forged` passed after
/// `ReplayCrossA.cross_forged` was refused in the same run;
/// `leanchecker --fresh` refuses it.
pub(crate) fn typecheck_constants_full_streaming_in_run(
    env: &mut Environment,
    target_names: &BTreeSet<String>,
    not_admitted: &BTreeSet<String>,
    already_declared: &BTreeMap<String, String>,
    max_heartbeats: u32,
    elide: ProofValueElision,
    chunk_size: Option<usize>,
) -> (usize, usize, BTreeMap<String, String>, ProofElisionStats) {
    let scope = ReplayScope {
        prerequisites: &BTreeSet::new(),
        not_admitted,
        already_declared,
    };
    streaming_in_scope(env, target_names, scope, max_heartbeats, elide, chunk_size)
}

fn streaming_in_scope(
    env: &mut Environment,
    target_names: &BTreeSet<String>,
    scope: ReplayScope<'_>,
    max_heartbeats: u32,
    elide: ProofValueElision,
    chunk_size: Option<usize>,
) -> (usize, usize, BTreeMap<String, String>, ProofElisionStats) {
    // None policy: the eager path verbatim (no chunk rebuild cost) so the
    // default flag value is provably verdict-identical.
    if elide == ProofValueElision::None {
        let (pass, fail, errors) = replay_check::full(env, target_names, &scope, max_heartbeats);
        return (pass, fail, errors, ProofElisionStats::default());
    }
    let chunk_len = chunk_size.unwrap_or(STREAM_ELIDE_CHUNK).max(1);
    replay_check::streaming(env, target_names, scope, max_heartbeats, elide, chunk_len)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify_batch::typecheck_constants;
    use std::path::PathBuf;

    #[test]
    fn honest_labels_distinguish_type_only_from_locally_rederived() {
        // AUDIT-CRITICAL: the two modes must carry DIFFERENT honest labels, and
        // only Full may claim the proof VALUE was re-derived at all.
        assert_eq!(ValidationMode::InferOnly.honest_label(), "type-only-infer");
        assert_eq!(ValidationMode::Full.honest_label(), "local-assumed-env");
        assert!(!ValidationMode::InferOnly.rederives_values_locally());
        assert!(ValidationMode::Full.rederives_values_locally());
        assert_ne!(
            ValidationMode::InferOnly.honest_label(),
            ValidationMode::Full.honest_label()
        );
    }

    /// The label this module emits must never claim a level it did not reach.
    ///
    /// `Full` reported `"kernel-verified-full"` until 2026-09-17, and reports
    /// read that as `add_decl`-equivalent. Neither mode is dependency-closed,
    /// so neither may ground a `Certified`-class claim.
    #[test]
    fn neither_mode_may_ground_a_certified_class_claim() {
        for mode in [ValidationMode::InferOnly, ValidationMode::Full] {
            assert!(!mode.recheck_level().may_ground_certified_class());
            assert!(!mode.honest_label().contains("kernel-verified"));
            assert!(!mode.honest_label().contains("full"));
        }
        assert!(crate::recheck_closed::RecheckLevel::ClosedReplay.may_ground_certified_class());
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

        // Each demotion is a genuine refusal of a proof VALUE the type-only path
        // never re-checked: the kernel's own `check_type` failure, or, since
        // P0_SOUND, a replay-order refusal that runs BEFORE the kernel. This
        // fixture loads into an empty environment, so `myNot.match_1` fails
        // `infer_sort` (no `Unit`), and Lean's replay never admits `myNot`,
        // which uses it. `myNot` used to be demoted by its own value's
        // `check_type` (UnknownConst `Unit`); it is now refused one step
        // earlier, naming the dependency. That is the stricter reason, pinned
        // here exactly.
        let value_refusals = full_errs
            .values()
            .filter(|m| m.starts_with("check_type:") || m.starts_with("replay order:"))
            .count();
        assert!(
            value_refusals >= 1,
            "expected >=1 proof-value refusal among full errors: {full_errs:?}"
        );
        assert!(
            full_errs["myNot"].starts_with(
                "replay order: `myNot` depends on `myNot.match_1`, which was not admitted"
            ),
            "{:?}",
            full_errs.get("myNot")
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
    #[test]
    fn not_admitted_resident_targets_and_prerequisites_refuse_transitive_users() {
        let (mut env, _) = seeded_real_env();
        let type_ = env
            .get_const(&KName::from_string("T"))
            .expect("real theorem")
            .type_
            .clone();
        let base = KName::anon().str("T.literal");
        assert_ne!(
            base,
            KName::from_string(&base.to_string()),
            "display text does not preserve exact Name components"
        );
        env.add_decl(Declaration::Theorem {
            name: base.clone(),
            level_params: vec![],
            type_: type_.clone(),
            value: Expr::const_(KName::from_string("T"), vec![]),
        })
        .expect("actual checked dotted-component base");
        for (name, dependency) in [
            ("DIRECT", base.clone()),
            ("TRANSITIVE", KName::from_string("DIRECT")),
        ] {
            env.add_decl(Declaration::Theorem {
                name: KName::from_string(name),
                level_params: vec![],
                type_: type_.clone(),
                value: Expr::const_(dependency, vec![]),
            })
            .expect("actual kernel-checked theorem chain");
        }
        let all: BTreeSet<String> = [
            base.to_string(),
            "DIRECT".to_owned(),
            "TRANSITIVE".to_owned(),
        ]
        .into_iter()
        .collect();
        let none = BTreeSet::new();
        let already_declared = BTreeMap::new();
        let baseline = typecheck_constants_full_ordered(
            &env,
            &all,
            &ReplayScope {
                prerequisites: &none,
                not_admitted: &none,
                already_declared: &already_declared,
            },
            DEFAULT_HEARTBEAT_LIMIT,
        );
        assert_eq!(
            (baseline.pass, baseline.fail),
            (3, 0),
            "genuine chain must admit without the refusal"
        );
        let not_admitted = BTreeSet::from([base.to_string()]);
        for targets in [&all, &BTreeSet::from(["TRANSITIVE".to_owned()])] {
            // Includes target/prerequisite overlap; the same declaration has
            // one node, and the pre-existing refusal is binding in either role.
            let replay = typecheck_constants_full_ordered(
                &env,
                targets,
                &ReplayScope {
                    prerequisites: &all,
                    not_admitted: &not_admitted,
                    already_declared: &already_declared,
                },
                DEFAULT_HEARTBEAT_LIMIT,
            );
            assert_eq!((replay.pass, replay.fail), (0, targets.len()));
            let verdicts: BTreeMap<_, _> = replay
                .verdicts
                .into_iter()
                .map(|(n, v)| (n.to_string(), v))
                .collect();
            assert!(
                matches!(&verdicts[&base.to_string()], Err(crate::replay_order::ReplayRefusal::NotAdmitted { name }) if *name == base)
            );
            for name in ["DIRECT", "TRANSITIVE"] {
                assert!(matches!(
                    verdicts[name],
                    Err(crate::replay_order::ReplayRefusal::DependsOnRefused { .. })
                ));
            }
        }
    }

    #[test]
    fn missing_value_targets_and_prerequisites_refuse_proof_chain_users() {
        let (mut env, _) = seeded_real_env();
        let base = KName::from_string("T");
        let type_ = env.get_const(&base).unwrap().type_.clone();
        for (label, dependency) in [
            ("DIRECT", base.clone()),
            ("TRANSITIVE", KName::from_string("DIRECT")),
        ] {
            env.add_decl(Declaration::Theorem {
                name: KName::from_string(label),
                level_params: vec![],
                type_: type_.clone(),
                value: Expr::const_(dependency, vec![]),
            })
            .expect("genuine checked proof chain before body removal");
        }
        let all = BTreeSet::from(["T".to_owned(), "DIRECT".to_owned(), "TRANSITIVE".to_owned()]);
        let none = BTreeSet::new();
        let already_declared = BTreeMap::new();
        let scope = ReplayScope {
            prerequisites: &all,
            not_admitted: &none,
            already_declared: &already_declared,
        };
        let baseline =
            typecheck_constants_full_ordered(&env, &all, &scope, DEFAULT_HEARTBEAT_LIMIT);
        assert_eq!(
            (baseline.pass, baseline.fail),
            (3, 0),
            "{:?}",
            baseline.verdicts
        );
        for kind in [
            clean_kernel::env::ConstantKind::Theorem,
            clean_kernel::env::ConstantKind::Definition,
            clean_kernel::env::ConstantKind::Opaque,
        ] {
            let mut changed = env.clone();
            let mut row = changed.get_const(&base).unwrap().clone();
            row.kind = kind;
            row.value = None;
            changed.add_constant_unchecked_for_test(row);
            for targets in [&all, &BTreeSet::from(["TRANSITIVE".to_owned()])] {
                let replay = typecheck_constants_full_ordered(
                    &changed,
                    targets,
                    &scope,
                    DEFAULT_HEARTBEAT_LIMIT,
                );
                assert_eq!(
                    (replay.pass, replay.fail),
                    (0, targets.len()),
                    "{:?}",
                    replay.verdicts
                );
                let verdicts: BTreeMap<_, _> = replay
                    .verdicts
                    .into_iter()
                    .map(|(name, verdict)| (name.to_string(), verdict))
                    .collect();
                assert!(
                    matches!(&verdicts["T"], Err(crate::replay_order::ReplayRefusal::MissingValue { name }) if *name == base)
                );
                for label in ["DIRECT", "TRANSITIVE"] {
                    assert!(
                        matches!(
                            &verdicts[label],
                            Err(crate::replay_order::ReplayRefusal::DependsOnRefused { .. })
                        ),
                        "{verdicts:?}"
                    );
                }
            }
        }
    }
}
