// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reflection backend for the SOLVER-BACKED bit-blast refutation: encode a
//! [`BvBlastProof`]'s clauses + resolution chain as KERNEL DATA and discharge
//! validity by `check_refutes <clauses> <refutation> = Bool.true` via `Eq.refl`.
//!
//! # Why (the #20 blowup, avoided)
//!
//! Replaying the 520-step refutation as a *monolithic* kernel `Or.rec` term is
//! intractable (>70 GB OOM — see the `theory_lemma_bv_compute_blast` module docs,
//! independently reproduced). The fix is *proof by reflection* (the standard
//! SAT/LRAT certificate technique): the resolution checker is a COMPUTATIONAL
//! kernel `Definition` ([`clean_kernel::resolution_check`]) the kernel *evaluates*
//! by a LINEAR ι-reduction over the proof DATA. The certificate term is then a
//! constant-size `Eq.refl`, and the kernel discharges it by reduction — never
//! building the exponential proof tree.
//!
//! This module converts the producer's [`BvBlastProof`] into that kernel data and
//! produces the `Eq.refl` certificate, so the 520-step check is genuinely
//! KERNEL-checked (the Rust `replay_resolution_chain` is no longer the authority).

use ay_proof::bv_blast_export::{BvBlastProof, Lit};
use clean_kernel::name::Name;
use clean_kernel::resolution_check::{
    check_refutes3_initialtrie_app, check_refutes_app, encode_clauses_lit, encode_refutation,
    encode_refutation_lit,
};
use clean_kernel::resolution_soundness::names as rsnames;
use clean_kernel::{Environment, Expr, Level, TypeChecker};

/// Error building / checking the reflection certificate.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ReflectionError {
    /// The producer's own validation rejected the proof.
    #[error("BvBlastProof failed validate(): {0}")]
    InvalidProof(String),
    /// The kernel did not accept the `Eq.refl` reflection certificate (the data
    /// did not reduce to `Bool.true`).
    #[error("kernel rejected reflection certificate (checkRefutes did not reduce to true): {0}")]
    CertificateRejected(String),
}

/// The reflection-certificate outcome.
pub struct ReflectionCertificate {
    /// The kernel `Bool` term `checkRefutes <clauses> <refutation>`.
    pub check_app: Expr,
    /// The `Eq.refl Bool.true` proof term (constant size).
    pub certificate: Expr,
    /// The goal `Eq Bool (checkRefutes …) Bool.true` the certificate inhabits.
    pub goal: Expr,
    /// Number of original clauses encoded.
    pub num_clauses: usize,
    /// Number of resolution steps encoded.
    pub num_steps: usize,
}

/// Convert a producer literal to the checker's `(var, neg)` pair.
fn lit_pair(l: Lit) -> (u32, bool) {
    (l.var, l.neg)
}

/// Build a `TypeChecker` for the reflection path whose heartbeat is governed by
/// the environment's `maxHeartbeats` option (mirroring [`Environment::add_decl`]),
/// defaulting to UNLIMITED (`0`) for this path.
///
/// The criterion-2 / lowering reflection check reduces the COMPUTATIONAL
/// `Clean.Res.checkRefutes <clauses> <refutation>` over the proof data. The cost of
/// that linear ι-reduction scales with `clauses + steps` and overshoots the kernel's
/// 2_000_000 default heartbeat at bit-width ≥ 6 (the width-6 reduction needs
/// ~2.3–2.5M ι-ticks; width-16 needs 16–32M). Under the default budget `whnf` BAILS
/// fail-CLOSED — it returns the STUCK (unreduced, non-`Bool`) term, so the `Eq.refl`
/// is REJECTED (a *sound* incompleteness; it never accepts an invalid refutation,
/// because a wrong refutation still reduces to `Bool.false`). Removing the heartbeat
/// only lets a VALID refutation COMPLETE its reduction to `Bool.true`; it can never
/// turn a `Bool.false` into a `Bool.true`. This matches the real Lean kernel, which
/// has no heartbeat. Callers that want to cap the reduction may set `maxHeartbeats`
/// on `env` to a width-scaled bound instead.
/// Whnf/def-eq memoization budget (cache entries) for a reflection reduction over a
/// refutation with `n_steps` resolution steps. ~O(steps) working set, clamped to
/// `[100k, 1M]` (≈8 GB peak at the cap). Returns the kernel default for `n_steps == 0`.
/// PURE PERFORMANCE — see [`reflection_tc_sized`]; sizing the cache has ZERO soundness
/// effect (it changes only what is memoized, never the reduction result).
pub(super) fn reflection_cache_budget(n_steps: usize) -> usize {
    const DEFAULT_BUDGET: usize = 100_000;
    const MAX_BUDGET: usize = 1_000_000;
    // Raise the budget ONLY in optimized builds. In debug, per-entry whnf-cache term
    // memory is several-fold larger (no Expr-layout optimization), so a 1M cache OOMs the
    // width-32 cert reduction (>100 GB); the SAME reduction in release fits in ~8 GB. The
    // debug/test path therefore stays at the safe 100k default (the width-32 e2e already
    // completes there in ~2.3 GB), while release consumers — including a `--release`
    // genesis reproduce — get the ~2.8× thrash-removal win. PURE PERFORMANCE either way.
    if n_steps == 0 || cfg!(debug_assertions) {
        DEFAULT_BUDGET
    } else {
        n_steps
            .saturating_mul(150)
            .clamp(DEFAULT_BUDGET, MAX_BUDGET)
    }
}

/// Build the reflection-cert `TypeChecker`, sizing the whnf/def-eq memoization
/// budget to the refutation's working set.
///
/// The `checkRefutes3` `go3` fold threads a TRIE accumulator that grows by one
/// resolvent per step; reducing the cert touches ~O(steps · log id) distinct trie
/// subterms. The kernel's 100k-entry default cache is far below that working set at
/// width ≥32 (≈7k steps), so the growing trie THRASHES the cache — hot subterms are
/// evicted and re-reduced — and the cert re-check degrades from ~O(steps·log) toward
/// O(steps²) (measured: the per-step whnf-miss count jumps 3.7× from width 16→32,
/// while trie DEPTH grows only ~1.2×; the inflation is re-computation, not depth).
///
/// Scaling the budget to the step count removes the thrash: at width 32 the proven
/// form drops from ≈85 s (100k) to ≈30 s (1M), a 2.8× win, plateauing past ~1M.
/// Clamped to `[100k, 1M]` to bound peak memory (~8 GB at the cap; the default-width
/// genesis-reproduce runs stay well under it). This is a PURE PERFORMANCE knob — the
/// reduction RESULT is bit-identical regardless of cache size, so it has ZERO
/// soundness effect (an under-budget cache merely re-derives the same normal form).
/// `n_steps == 0` leaves the kernel default untouched.
pub(super) fn reflection_tc_sized(env: &Environment, n_steps: usize) -> TypeChecker<'_> {
    let mut tc = TypeChecker::with_mode(env, env.mode());
    // Default to unlimited; honor an explicit `maxHeartbeats` override if present.
    let limit = match env.get_option("maxHeartbeats") {
        Some(Some(s)) => s.parse::<u32>().unwrap_or(0),
        _ => 0,
    };
    tc.set_heartbeat_limit(limit);
    if n_steps > 0 {
        tc.set_max_cache_entries(reflection_cache_budget(n_steps));
    }
    tc
}

/// Convert one clause's literals.
fn clause_pairs(lits: &[Lit]) -> Vec<(u32, bool)> {
    lits.iter().copied().map(lit_pair).collect()
}

/// Build the kernel `List (List Nat)` of the proof's ORIGINAL clauses (in id
/// order, which the producer guarantees is `0..clauses.len()`).
///
/// Clause literals are BigNat LITERALS ([`encode_clauses_lit`]), NOT unary
/// `Nat.succ^n Nat.zero`. This makes each literal a single compact node, so the
/// `Nat.beq`-/`Nat.div`-/`Nat.mod`-based comparison surface (`litBeq`, `clauseMem`,
/// `trieGet`/`trieIns` `key/2`+`key%2`) reduces NATIVELY, and — crucially for width 32 —
/// the `cs` term's MEMORY footprint collapses from ~4500-deep succ-chains per literal to
/// one node each, which is what lets the end-to-end encoding-fidelity bridge complete at
/// width 32 (previously OOM/SIGKILL). NOTE: it does NOT make the proven-form
/// `checkRefutes3` reduction faster, because `checkStep3`/`resolve`/`clauseTautFree` go
/// through `litNeg`, a `Nat.rec` (unary) recursor that peels any literal — BigNat or
/// unary — one `succ` at a time; that `litNeg` cost is the residual super-quadratic term
/// and is part of the `checkRefutes3` soundness-proved surface (unchanged here).
/// `checkRefutes3_sound` is `∀ cs`, so this representation change is soundness-invariant —
/// only the literal node shape in `cs` differs.
pub fn encode_proof_clauses(proof: &BvBlastProof) -> Expr {
    let clauses: Vec<Vec<(u32, bool)>> = proof
        .clauses
        .iter()
        .map(|c| clause_pairs(&c.lits))
        .collect();
    encode_clauses_lit(&clauses)
}

/// The proof's resolution chain as raw `(resolvent, prem1, prem2, pivot)` tuples — the
/// shared source for both the unary [`encode_refutation`] and the BigNat-id
/// [`clean_kernel::resolution_check::encode_refutation_lit`] step encoders.
pub(crate) fn proof_step_tuples(proof: &BvBlastProof) -> Vec<(Vec<(u32, bool)>, u32, u32, u32)> {
    proof
        .refutation
        .steps
        .iter()
        .map(|s| {
            (
                clause_pairs(&s.clause),
                s.premises[0],
                s.premises[1],
                s.pivot,
            )
        })
        .collect()
}

/// Build the kernel `List Clean.Res.Step` of the proof's resolution chain.
///
/// Each [`ay_proof::bv_blast_export::ResolutionStep`] becomes
/// `Step.mk <recorded resolvent> prem1 prem2 pivot`. Premise ids are passed
/// through unchanged: the kernel `checkRefutes` threads a DB of
/// `original clauses ++ recorded resolvents` and indexes it by the same id space
/// (clause ids `< clauses.len()`, step ids after) the producer uses.
pub fn encode_proof_refutation(proof: &BvBlastProof) -> Expr {
    encode_refutation(&proof_step_tuples(proof))
}

/// Build the kernel reflection certificate for `proof` and KERNEL-CHECK it.
///
/// Produces `Eq.refl Bool.true : checkRefutes <clauses> <refutation> = Bool.true`
/// and type-checks it against the goal. Success means the kernel REDUCED the
/// (linear) checker over the proof data to `Bool.true` — a tractable kernel check
/// of the full 520-step refutation.
///
/// # Errors
/// [`ReflectionError::InvalidProof`] if the producer's validation fails;
/// [`ReflectionError::CertificateRejected`] if the kernel does not accept the
/// `Eq.refl` (i.e. `checkRefutes` did not reduce to `Bool.true`).
pub fn certify_by_reflection(
    env: &Environment,
    proof: &BvBlastProof,
) -> Result<ReflectionCertificate, ReflectionError> {
    proof
        .validate()
        .map_err(|e| ReflectionError::InvalidProof(format!("{e}")))?;

    let clauses = encode_proof_clauses(proof);
    let refutation = encode_proof_refutation(proof);
    let check_app = check_refutes_app(clauses, refutation);

    let bool_ty = Expr::const_str("Bool");
    let btrue = Expr::const_str("Bool.true");
    let u1 = Level::succ(Level::zero());
    // Eq.refl.{1} Bool Bool.true : Eq Bool Bool.true Bool.true (and, by def-eq of the
    // reduced check_app, Eq Bool (checkRefutes …) Bool.true).
    let certificate = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1.clone()]),
        [bool_ty.clone(), btrue.clone()],
    );
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1]),
        [bool_ty, check_app.clone(), btrue],
    );

    let tc = reflection_tc_sized(env, proof.refutation.steps.len());
    tc.check_type(&certificate, &goal)
        .map_err(|e| ReflectionError::CertificateRejected(format!("{e:?}")))?;

    Ok(ReflectionCertificate {
        check_app,
        certificate,
        goal,
        num_clauses: proof.clauses.len(),
        num_steps: proof.refutation.steps.len(),
    })
}

/// The soundness-bridge constant name (`checkRefutes_sound`).
///
/// As of #22 this is a PROVED kernel `Theorem` (axiom closure ⊆ FOUNDATIONAL),
/// registered by `Environment::init_resolution_soundness` (or the back-compat
/// `register_check_refutes_sound_stmt`). [`certify_unsat_by_reflection`] applies it
/// to the reflection certificate to obtain a FULLY zero-trust `Unsat`-discharging
/// proof term.
#[must_use]
pub fn check_refutes_sound_name() -> &'static str {
    "Clean.Res.checkRefutes_sound"
}

/// Build the FULLY zero-trust `Unsat`-discharging term:
/// `checkRefutes_sound <clauses> <refutation> (Eq.refl Bool Bool.true)`.
///
/// Its type is the model-theoretic unsatisfiability of the original clause set,
/// and — because `checkRefutes_sound` is now a PROVED `Theorem` (closure ⊆
/// FOUNDATIONAL) — the assembled term carries ZERO residual domain axioms. The
/// `env` must have `init_resolution_soundness` run.
///
/// Returns `(unsat_term, unsat_goal)` after kernel-checking the term inhabits the
/// goal.
///
/// # Errors
/// [`ReflectionError::InvalidProof`] if the producer validation fails;
/// [`ReflectionError::CertificateRejected`] if the kernel rejects the assembled term.
pub fn certify_unsat_by_reflection(
    env: &Environment,
    proof: &BvBlastProof,
) -> Result<(Expr, Expr), ReflectionError> {
    let cert = certify_by_reflection(env, proof)?;
    let clauses = encode_proof_clauses(proof);
    let refutation = encode_proof_refutation(proof);
    // checkRefutes_sound clauses refutation (Eq.refl Bool Bool.true) : Unsat clauses
    let unsat_term = Expr::apps(
        Expr::const_str(check_refutes_sound_name()),
        [clauses.clone(), refutation, cert.certificate.clone()],
    );
    let tc = reflection_tc_sized(env, proof.refutation.steps.len());
    let unsat_goal = tc
        .infer_type(&unsat_term)
        .map_err(|e| ReflectionError::CertificateRejected(format!("{e:?}")))?;
    Ok((unsat_term, unsat_goal))
}

/// The PROVEN-SOUND sub-quadratic soundness-bridge constant name
/// (`checkRefutes3_sound`).
///
/// Like [`check_refutes_sound_name`] this is a PROVED kernel `Theorem` (axiom closure ⊆
/// FOUNDATIONAL), registered by `Environment::init_resolution_soundness`. It discharges
/// `Unsat cs` from the trie-backed `checkRefutes3 (initialTrie cs) (listLen cs) steps`
/// reduction, which is sub-quadratic where `checkRefutes` is O(steps²).
#[must_use]
pub fn check_refutes3_sound_name() -> &'static str {
    rsnames::CHECK_REFUTES3_SOUND
}

/// Build the `Eq.refl` reflection certificate for the SUB-QUADRATIC trie checker.
///
/// The cert inhabits `Eq Bool (checkRefutes3 (initialTrie cs) (listLen cs) steps)
/// Bool.true` — the EXACT hypothesis of [`check_refutes3_sound_name`]. `cs` is the same
/// UNARY [`encode_clauses`] clause DB used everywhere else in the bridge (so the eventual
/// `Unsat cs` is about the bridge's clause set), and the `initialTrie cs`/`listLen cs`
/// are the kernel DEFINITIONS the kernel reduces — matching `checkRefutes3_sound`
/// syntactically. The `steps` carry BigNat-id premises so the trie lookups reduce
/// natively (the sub-quadratic point). The `Eq.refl` type-checks because the kernel
/// reduces this proven form to `Bool.true` on a genuine refutation (`Bool.false` on a
/// forged one, so an invalid refutation is never accepted).
///
/// # Errors
/// [`ReflectionError::InvalidProof`] if the producer's validation fails;
/// [`ReflectionError::CertificateRejected`] if the kernel does not accept the `Eq.refl`.
pub fn certify3_by_reflection(
    env: &Environment,
    proof: &BvBlastProof,
) -> Result<ReflectionCertificate, ReflectionError> {
    proof
        .validate()
        .map_err(|e| ReflectionError::InvalidProof(format!("{e}")))?;

    // `cs` is the SAME UNARY clause DB the rest of the bridge is about (so `Unsat cs`
    // discharges the encoding-fidelity bridge's `allSat H cs`). `checkRefutes3_sound`
    // is parametric in `cs`, so the kernel reduces `initialTrie cs`/`listLen cs` itself.
    let clauses = encode_proof_clauses(proof);
    let check_app = check_refutes3_initialtrie_app(clauses, &proof_step_tuples(proof));

    let bool_ty = Expr::const_str("Bool");
    let btrue = Expr::const_str("Bool.true");
    let u1 = Level::succ(Level::zero());
    let certificate = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1.clone()]),
        [bool_ty.clone(), btrue.clone()],
    );
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1]),
        [bool_ty, check_app.clone(), btrue],
    );

    let tc = reflection_tc_sized(env, proof.refutation.steps.len());
    tc.check_type(&certificate, &goal)
        .map_err(|e| ReflectionError::CertificateRejected(format!("{e:?}")))?;

    Ok(ReflectionCertificate {
        check_app,
        certificate,
        goal,
        num_clauses: proof.clauses.len(),
        num_steps: proof.refutation.steps.len(),
    })
}

/// Build the FULLY zero-trust `Unsat`-discharging term via the SUB-QUADRATIC checker:
/// `checkRefutes3_sound <cs> <steps> (Eq.refl Bool Bool.true) : Unsat <cs>`.
///
/// Same `Unsat cs` conclusion (and same `cs` term) as [`certify_unsat_by_reflection`],
/// but discharged through the proven sub-quadratic `checkRefutes3_sound` instead of the
/// O(steps²) `checkRefutes_sound`. Because `checkRefutes3_sound` is a PROVED `Theorem`
/// (closure ⊆ FOUNDATIONAL), the assembled term still carries ZERO residual domain
/// axioms. The `env` must have `init_resolution_soundness` run.
///
/// Returns `(unsat_term, unsat_goal)` after kernel-checking the term inhabits the goal.
///
/// # Errors
/// [`ReflectionError::InvalidProof`] if the producer validation fails;
/// [`ReflectionError::CertificateRejected`] if the kernel rejects the assembled term.
pub fn certify_unsat3_by_reflection(
    env: &Environment,
    proof: &BvBlastProof,
) -> Result<(Expr, Expr), ReflectionError> {
    let cert = certify3_by_reflection(env, proof)?;
    // `cs` MUST be the SAME term as in `cert.check_app`'s `initialTrie cs`/`listLen cs`
    // and as the bridge's `allSat H cs`: the UNARY `encode_clauses` DB.
    let clauses = encode_proof_clauses(proof);
    // `steps` MUST be the SAME term `cert.check_app` baked into the `checkRefutes3` cert,
    // i.e. the BigNat-id `encode_refutation_lit` form — so the cert's `Eq … = Bool.true`
    // type matches `checkRefutes3_sound cs steps`'s hypothesis SYNTACTICALLY (no def-eq
    // reduction of two distinct `steps` encodings). `Unsat cs` is independent of `steps`.
    let steps = encode_refutation_lit(&proof_step_tuples(proof));
    // checkRefutes3_sound cs steps (Eq.refl Bool Bool.true) : Unsat cs
    let unsat_term = Expr::apps(
        Expr::const_str(check_refutes3_sound_name()),
        [clauses, steps, cert.certificate.clone()],
    );
    let tc = reflection_tc_sized(env, proof.refutation.steps.len());
    let unsat_goal = tc
        .infer_type(&unsat_term)
        .map_err(|e| ReflectionError::CertificateRejected(format!("{e:?}")))?;
    Ok((unsat_term, unsat_goal))
}

#[cfg(test)]
#[path = "tests_bv_blast_reflection.rs"]
mod tests;
