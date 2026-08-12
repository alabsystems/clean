// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-carrying ay, MILESTONE 2 — NATIVE kernel certification of a BITVECTOR
//! MULTIPLICATION UNSAT obligation.
//!
//! This is the BV-mul analogue of milestone-1's LIA composer
//! ([`super::certified_proof::reconstruct_and_certify_ay_proof`]): it takes a
//! `bvmul`-involving equality that ay refutes and produces a
//! [`CertifiedPayload`] whose soundness reduces to the CLEAN KERNEL alone —
//! `trust_count == 0`, exact rooted certification authority, NO trust in ay,
//! NO Carcara, and no caller-maintained axiom whitelist.
//!
//! # The gate-tree reconstruction (genuine, no `bvMul_comm` shortcut)
//!
//! ay's [`ay_proof::bv_blast_solver`] bit-blasts a `bvmul` obligation as a REAL,
//! truncated shift-and-add ARRAY MULTIPLIER, built from existing gate kinds only:
//!
//!   * **partial products** `pp[i][j] = a[i] ∧ b[j]` via `And2` gates, and
//!   * an **accumulation tree** of `n-1` ripple-carry adders (one per shifted
//!     partial-product row), each reusing the SAME `Xor3` (sum) +
//!     `FullAdderCarry` (majority/carry) + `ConstFalse` gates the `bvadd` blaster
//!     uses.
//!
//! The whole multiplier is materialised and CNF-encoded; its UNSAT resolution
//! refutation is surfaced from ay's SAT core (a pure resolution DAG — the BV
//! blast format has NO `:rule trust` escape hatch by construction). The Clean
//! kernel then re-checks that refutation NATIVELY, by *reflection*:
//! [`super::bv_blast_reflection::certify_unsat3_by_reflection`] encodes the
//! clauses + resolution chain as kernel DATA and discharges
//! `checkRefutes3 <clauses> <refutation> = Bool.true` by definitional reduction
//! (`Eq.refl`), then applies the PROVED bridge theorem
//! `Clean.Res.checkRefutes3_sound` (transitive axiom closure `⊆` FOUNDATIONAL) to
//! obtain `Clean.Res.Unsat <clauses>`. Because the clause set IS the bit-blast of
//! `not(lhs == rhs)` — every `And2` partial product and every `Xor3`/
//! `FullAdderCarry` adder-tree gate contributing its Tseitin clauses — the kernel
//! genuinely consumes the multiplier's gate tree. The identity is recovered SOLELY
//! from the clause set being unsatisfiable; the reconstruction NEVER cites a
//! `bvMul_comm` (or any BV) axiom, exactly like the `bvadd` reflection lane.
//!
//! AY proof production is bounded before this kernel work begins: the public,
//! opaque producer budget applies a 30-second deadline and the same 4,096-step
//! ceiling used by Clean's reflection policy. The kernel reduction itself uses
//! the SUB-QUADRATIC trie checker (`checkRefutes3_sound`). A producer resource
//! exhaustion and an unexpectedly over-cap returned proof are distinct typed,
//! fail-closed outcomes; neither is an alternate proof authority.
//!
//! # Signed multiplication (the `mul_*` overflow case)
//!
//! Two's-complement `bvmul` produces the SAME low `w` result bits for signed and
//! unsigned operands, so the sign is handled entirely inside the bit-blast: a
//! signed-mul-overflow VC is expressed COMPOSITIONALLY over the `BvExpr` fragment
//! (`sign_ext` + `mul` + `extract` + `eq`), and its refutation bit-blasts through
//! the same array multiplier. [`bvmul_widening_no_overflow_obligation`] builds
//! exactly the widening no-overflow disequality a signed `mul_*` overflow check
//! reduces to.
//!
//! # Fail-closed
//!
//! Every step is fail-closed: a satisfiable obligation surfaces
//! [`ay_proof::bv_blast_solver::BvExprExportError::NoRefutation`] (ay never
//! fabricates a proof) → [`BvMulCertifyError::NoRefutation`]; an exhausted AY
//! budget → [`BvMulCertifyError::ProducerResourceExhausted`]; a malformed /
//! tampered bit-blast fails the producer `validate()` or the kernel `check_type`
//! → not certified; a residual-trust or non-foundational axiom in the assembled
//! term is rejected. Only a genuine, kernel-re-checked, foundational-residue
//! `Unsat` term yields a [`CertifiedPayload`].

use std::time::Duration;

use ay_proof::bv_blast_solver::{
    export_bv_blast_proof_expr_bounded, BvExpr, BvExprExportError, BvExprProofBudget,
};
use clean_kernel::{Environment, LocalContext};

use super::bv_blast_reflection::{certify_unsat3_by_reflection, ReflectionError};
use super::certified_proof::{certify_kernel_term, CertifiedPayload, NotCertified};

/// Wall-clock ceiling for AY proof production. It does not cover the subsequent
/// Clean-kernel reflection, which is separately bounded by proof size below.
const PRODUCER_TIMEOUT: Duration = Duration::from_secs(30);

/// Operational ceiling for the always-on sub-quadratic trie reflection
/// (`checkRefutes3_sound`). Proof trace sizes are producer-dependent, so this is
/// enforced both by AY's opaque producer budget and on the actual returned
/// trace. This is a ROBUSTNESS cap, NOT a soundness relaxation: an over-cap
/// refutation is DECLINED (kept `SmtBacked`), never accepted.
pub const MAX_REFLECTION_STEPS: usize = 4_096;

/// Why a native BV-mul certification attempt did not yield a [`CertifiedPayload`].
///
/// Every variant is FAIL-CLOSED: the caller keeps the honest pre-certification
/// verdict (`SmtBacked`) rather than upgrading.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum BvMulCertifyError {
    /// The obligation is SATISFIABLE — ay found no refutation, so there is
    /// nothing to certify. This is the primary fail-closed guard against a
    /// false-PROVE of a satisfiable bvmul VC (ay never fabricates a proof).
    #[error("bvmul obligation is satisfiable; declined (no refutation to certify)")]
    NoRefutation,

    /// ay could not decide the obligation (solver returned unknown / could not
    /// surface a resolution refutation).
    #[error("bvmul obligation not decided by ay: {0}")]
    Undecided(String),

    /// The obligation could not be bit-blasted (width mismatch / malformed /
    /// unsupported width).
    #[error("bvmul obligation could not be bit-blasted: {0}")]
    NotBlastable(String),

    /// AY's bounded proof producer exhausted a preflight, construction, SAT,
    /// proof-surfacing, replay, or deadline resource. The obligation is declined
    /// before kernel reflection begins.
    #[error(
        "bvmul proof producer exhausted resource `{resource}` (limit {limit}, actual {actual}); capped-declined"
    )]
    ProducerResourceExhausted {
        /// Stable producer resource name.
        resource: &'static str,
        /// Configured maximum for that resource.
        limit: usize,
        /// Observed or conservatively estimated amount.
        actual: usize,
    },

    /// The producer returned a refutation larger than
    /// [`MAX_REFLECTION_STEPS`]. This defense-in-depth check protects the Clean
    /// reducer independently of the producer's bounded-export contract.
    #[error("bvmul refutation too large for the always-on reflection ({steps} > {cap} steps); capped-declined")]
    RefutationTooLarge {
        /// The refutation's resolution-step count.
        steps: usize,
        /// The [`MAX_REFLECTION_STEPS`] cap.
        cap: usize,
    },

    /// The producer's own bit-blast validation rejected the refutation, or the
    /// Clean kernel rejected the reflection certificate.
    #[error("bvmul refutation failed native kernel re-check: {0}")]
    KernelRejected(String),
}

fn bounded_producer_budget() -> Result<BvExprProofBudget, BvMulCertifyError> {
    BvExprProofBudget::conservative(PRODUCER_TIMEOUT, MAX_REFLECTION_STEPS).map_err(|error| {
        BvMulCertifyError::Undecided(format!(
            "ay rejected Clean's bounded proof-producer policy: {error}"
        ))
    })
}

fn map_export_error(error: BvExprExportError) -> BvMulCertifyError {
    match error {
        BvExprExportError::NoRefutation => BvMulCertifyError::NoRefutation,
        BvExprExportError::SolverUnknown => {
            BvMulCertifyError::Undecided("ay returned unknown".to_string())
        }
        BvExprExportError::RefutationNotSurfaceable(message) => {
            BvMulCertifyError::Undecided(message)
        }
        BvExprExportError::ResourceLimit {
            resource,
            limit,
            actual,
        } => BvMulCertifyError::ProducerResourceExhausted {
            resource,
            limit,
            actual,
        },
        other => BvMulCertifyError::NotBlastable(other.to_string()),
    }
}

fn enforce_reflection_step_cap(steps: usize) -> Result<(), BvMulCertifyError> {
    if steps > MAX_REFLECTION_STEPS {
        Err(BvMulCertifyError::RefutationTooLarge {
            steps,
            cap: MAX_REFLECTION_STEPS,
        })
    } else {
        Ok(())
    }
}

/// A kernel-CERTIFIED bvmul refutation.
///
/// Carries the [`CertifiedPayload`] (the serialized, kernel-re-checkable
/// `Unsat <clauses>` term) plus an honesty summary of the reconstructed
/// bit-blast.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct BvMulCertified {
    /// The kernel-checked, serializable payload. `trust_count == 0`; its term
    /// inhabits `Clean.Res.Unsat <clauses>` where `<clauses>` is the bit-blast of
    /// the negated bvmul goal.
    pub payload: CertifiedPayload,
    /// Number of CNF clauses in the reconstructed bit-blast (every partial-product
    /// `And2` and adder-tree `Xor3`/`FullAdderCarry` gate contributes its Tseitin
    /// clauses, plus the disequality clause).
    pub num_clauses: usize,
    /// Number of resolution steps in the refutation the kernel re-checked.
    pub num_resolution_steps: usize,
}

/// Build the widening no-overflow disequality a signed/unsigned `mul_*` overflow
/// check reduces to, over the `BvExpr` fragment: at result width `w`, the low `w`
/// bits of the widened product equal the low `w` bits of the truncated product,
/// so `not( extract(mul(zext a, zext b))[w-1:0] == mul(a, b) )` is UNSAT.
///
/// This is a REAL gate-shaped multiply obligation — both sides bit-blast the full
/// shift-and-add array multiplier through one shared gate cache, so the widened
/// readout fuses to the same low output bits as the bare multiply, making the
/// disequality unsatisfiable. It is genuinely distinct from add (`mul != add`),
/// so a multiply mis-lowered as an add would be refuted, never proved.
///
/// `leaf_a` / `leaf_b` are the free operand names; `width` is the operand width.
#[must_use]
pub fn bvmul_widening_no_overflow_obligation(
    leaf_a: &str,
    leaf_b: &str,
    width: u32,
) -> (BvExpr, BvExpr) {
    let a = BvExpr::leaf(leaf_a, width);
    let b = BvExpr::leaf(leaf_b, width);
    // machine: low `w` bits of the zero-extended (widened) product.
    let machine = BvExpr::extract(
        BvExpr::zero_ext(BvExpr::Mul(Box::new(a.clone()), Box::new(b.clone())), width),
        width - 1,
        0,
    );
    // spec: the bare truncated product.
    let spec = BvExpr::Mul(Box::new(a), Box::new(b));
    (machine, spec)
}

/// Natively certify a bvmul UNSAT obligation `not(lhs == rhs)` against the Clean
/// kernel, by reflecting ay's array-multiplier bit-blast refutation.
///
/// `env` must be an [`Environment`] with the resolution-soundness layer
/// initialised (see [`bvmul_certify_env`]).
///
/// Returns [`BvMulCertified`] IFF:
///   * ay bit-blasts and refutes `not(lhs == rhs)` within the finite producer
///     budget (a SAT or resource-exhausted obligation → declined),
///   * the returned refutation is within [`MAX_REFLECTION_STEPS`] (else
///     capped-declined independently of the producer),
///   * the Clean kernel re-checks the reflection `Unsat` cert (`check_type`,
///     `infer_only = false`), with `trust_count == 0`, AND
///   * the kernel's expression-rooted authority audit accepts the exact
///     goal/term dependency closure, provenance, and canonical foundations.
///
/// Any other outcome is a fail-closed [`BvMulCertifyError`].
///
/// # Errors
/// See [`BvMulCertifyError`].
pub fn certify_bvmul_unsat(
    env: &Environment,
    lhs: &BvExpr,
    rhs: &BvExpr,
) -> Result<BvMulCertified, BvMulCertifyError> {
    // (1) Bit-blast the negated goal `not(lhs == rhs)` into a gate-tree CNF and
    //     surface ay's REAL resolution refutation under a finite, opaque public
    //     producer budget. Fail-closed: SAT returns `NoRefutation`; resource or
    //     deadline exhaustion is typed distinctly; neither fabricates a proof.
    let budget = bounded_producer_budget()?;
    let proof = export_bv_blast_proof_expr_bounded(lhs, rhs, &budget).map_err(map_export_error)?;

    let num_clauses = proof.clauses.len();
    let num_resolution_steps = proof.refutation.steps.len();

    // (1a) Defense in depth: independently enforce Clean's reducer policy on
    //      the proof actually returned by AY. This remains even though the
    //      producer is configured with the same step ceiling.
    enforce_reflection_step_cap(num_resolution_steps)?;

    // (2) NATIVE kernel re-check: encode clauses + refutation as kernel data,
    //     discharge `checkRefutes3 = true` by reflection (`Eq.refl`), and apply
    //     the PROVED `checkRefutes3_sound` bridge to obtain `Unsat <clauses>`.
    //     This internally re-runs the producer `validate()` and
    //     kernel-`infer_type`s the assembled term (so a tampered bit-blast is
    //     rejected here).
    let (unsat_term, unsat_goal) =
        certify_unsat3_by_reflection(env, &proof).map_err(|e| match e {
            ReflectionError::InvalidProof(m) => BvMulCertifyError::KernelRejected(m),
            ReflectionError::CertificateRejected(m) => BvMulCertifyError::KernelRejected(m),
        })?;

    // (3) FAIL-CLOSED certification: independent residual-trust re-scan, full
    //     `check_type`, and the kernel's exact expression-rooted authority
    //     audit over the goal/term closure. No local name whitelist authorizes
    //     the payload.
    let ctx = LocalContext::new();
    let payload =
        certify_kernel_term(&unsat_term, &unsat_goal, env, &ctx).map_err(|e| match e {
            NotCertified::TrustedSubterms { count } => BvMulCertifyError::KernelRejected(format!(
                "reflection cert carried {count} residual-trust sub-term(s)"
            )),
            NotCertified::KernelRejected { message } => BvMulCertifyError::KernelRejected(message),
            other => BvMulCertifyError::KernelRejected(format!("{other}")),
        })?;

    Ok(BvMulCertified {
        payload,
        num_clauses,
        num_resolution_steps,
    })
}

/// Build an [`Environment`] ready for [`certify_bvmul_unsat`]: the kernel prelude
/// plus the resolution-soundness layer (`checkRefutes3_sound` and its
/// dependencies), which the reflection cert applies.
///
/// # Errors
/// Propagates an environment-construction failure as a `String`.
pub fn bvmul_certify_env() -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .map_err(|e| format!("init_resolution_soundness: {e:?}"))?;
    Ok(env)
}

#[cfg(test)]
#[path = "tests_pcay_bvmul.rs"]
mod tests;
