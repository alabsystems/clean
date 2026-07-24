// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-carrying ay, MILESTONE 3 — NATIVE kernel certification of a BITVECTOR
//! SHIFT UNSAT obligation (`bvshl` / `bvlshr` / `bvashr`).
//!
//! This is the BV-shift analogue of milestone-2's
//! [`super::pcay_bvmul::certify_bvmul_unsat`]: it takes a shift-involving equality
//! that ay refutes and produces a [`CertifiedPayload`] whose soundness reduces to
//! the CLEAN KERNEL alone — `trust_count == 0`, exact rooted certification
//! authority, NO trust in ay, NO Carcara, and no caller-maintained whitelist.
//!
//! # The reflection is OP-AGNOSTIC (verified, not asserted)
//!
//! Milestone-2's reconstruction reflects the RESOLUTION refutation of the
//! BIT-BLASTED CNF: it encodes `<clauses>` + `<refutation>` as kernel DATA and
//! discharges `checkRefutes <clauses> <refutation> = Bool.true` by a linear
//! ι-reduction, then applies a PROVED bridge theorem (transitive axiom closure
//! `⊆` FOUNDATIONAL) to obtain `Clean.Res.Unsat <clauses>`. NOTHING in that
//! pipeline mentions which BV op produced the clauses — it consumes only a
//! `BvBlastProof` (clauses + resolution steps). So a shift VC reuses the EXACT
//! SAME reflection: the new work is purely (1) surfacing ay's barrel-shifter
//! bit-blast refutation, which
//! [`ay_proof::bv_blast_solver::export_bv_blast_proof_expr`] already does for the
//! `BvExpr::{Shl, Lshr, Ashr}` fragment, and (2) the kernel re-check discipline
//! (identical to milestone 2).
//!
//! This lane uses the SUB-QUADRATIC trie variant
//! [`certify_unsat3_by_reflection`] (bridge `Clean.Res.checkRefutes3_sound`)
//! rather than milestone 2's O(steps²) `checkRefutes_sound`: a barrel shifter's
//! refutation is resolution-step-heavier than the array multiplier's for the same
//! clause count, and the O(steps²) reduction OOMs (~30 GB) at width 4, whereas the
//! trie reduction re-checks it in ~30 s / ~8 GB. Both bridges are PROVED Theorems
//! with an empty domain-axiom closure — the `Unsat` conclusion and its foundational
//! residue are identical; only the reduction complexity differs (ZERO soundness
//! effect).
//!
//! # The barrel-shifter bit-blast (genuine, no shift axiom)
//!
//! ay's [`ay_proof::bv_blast_solver`] bit-blasts a variable shift as a REAL BARREL
//! SHIFTER (`blast_shift`): `ceil(log2(n))` conditional constant-shift layers
//! (each a `mux` of the shifted-by-`2^i` wires vs. the un-shifted wires, keyed on
//! shift-amount bit `i`) plus an over-shift saturation mux (to zero for
//! `Shl`/`Lshr`, to the sign bit for `Ashr`). Every gate is an EXISTING
//! `BitLemmaKind` (`And2`/`Or2`/`Not`/`ConstFalse`), so the clause set the kernel
//! reflects is exactly the Tseitin encoding of that barrel shifter. The
//! reconstruction recovers unsatisfiability SOLELY from the clause set — it NEVER
//! cites a `bvShl_*` (or any BV) axiom, exactly like the `bvadd`/`bvmul` lanes.
//!
//! # Signed vs. unsigned (the `Ashr` distinction is real)
//!
//! Two's-complement is handled entirely inside the bit-blast: `Ashr` fills with
//! the sign bit where `Lshr` fills with zero, so an `Ashr`-lowered-as-`Lshr`
//! disequality is SATISFIABLE and ay REFUSES to fabricate a proof
//! ([`BvExprExportError::NoRefutation`] → [`BvShiftCertifyError::NoRefutation`]).
//! This is the exact signed/unsigned bug class the campaign turned on, so the
//! anti-vacuity is genuine, never a structural coincidence.
//!
//! # Honest budget (why width 4 is the always-on default)
//!
//! A WIDTH-`n` variable barrel shift bit-blasts to `O(n·log n)` gates. Measured
//! refutation sizes: width 2 = 66 clauses / 277 steps; width 4 = 172 clauses / 925
//! steps; width 8 = 430 clauses / 5356 steps. The sub-quadratic trie reflection is
//! tractable through width-4 shifts (~30 s / ~8 GB). A width-8 shift (5356 steps)
//! runs for MINUTES and is CAPPED fail-closed here
//! ([`BvShiftCertifyError::RefutationTooLarge`]) — see [`MAX_REFLECTION_STEPS`].
//! (This is the shift analogue of milestone 2 keeping wide multiplication out of
//! the always-on always-certify budget.)
//!
//! # Fail-closed
//!
//! Every step is fail-closed, identical to milestone 2: a satisfiable obligation
//! surfaces `NoRefutation` (ay never fabricates a proof); a malformed / tampered
//! bit-blast fails the producer `validate()` or the kernel `check_type`; a
//! residual-trust or non-foundational axiom in the assembled term is rejected; an
//! oversized refutation is capped-declined. Only a genuine, kernel-re-checked,
//! foundational-residue `Unsat` term yields a [`CertifiedPayload`].

use ay_proof::bv_blast_solver::{export_bv_blast_proof_expr, BvExpr, BvExprExportError};
use clean_kernel::{Environment, LocalContext};

use super::bv_blast_reflection::{certify_unsat3_by_reflection, ReflectionError};
use super::certified_proof::{certify_kernel_term, CertifiedPayload, NotCertified};

/// The sub-quadratic trie reflection (`checkRefutes3_sound`) is tractable up to
/// this many resolution steps for the ALWAYS-ON lane (calibrated: a width-4 barrel
/// shift is ~925 steps and re-checks in ~30 s / ~8 GB). A width-8 variable shift is
/// ~5356 steps, whose reflection runs for minutes — CAPPED fail-closed here rather
/// than hang the router. This is a ROBUSTNESS cap, NOT a soundness relaxation: an
/// over-cap refutation is DECLINED (kept `SmtBacked`), never accepted.
pub const MAX_REFLECTION_STEPS: usize = 4_096;

/// Why a native BV-shift certification attempt did not yield a [`CertifiedPayload`].
///
/// Every variant is FAIL-CLOSED: the caller keeps the honest pre-certification
/// verdict (`SmtBacked`) rather than upgrading.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum BvShiftCertifyError {
    /// The obligation is SATISFIABLE — ay found no refutation, so there is nothing
    /// to certify. The primary fail-closed guard against a false-PROVE of a
    /// satisfiable shift VC (e.g. `ashr` mis-lowered as `lshr`): ay never
    /// fabricates a proof.
    #[error("bvshift obligation is satisfiable; declined (no refutation to certify)")]
    NoRefutation,

    /// ay could not decide the obligation (solver returned unknown / could not
    /// surface a resolution refutation).
    #[error("bvshift obligation not decided by ay: {0}")]
    Undecided(String),

    /// The obligation could not be bit-blasted (width mismatch / malformed /
    /// unsupported width).
    #[error("bvshift obligation could not be bit-blasted: {0}")]
    NotBlastable(String),

    /// The refutation is larger than [`MAX_REFLECTION_STEPS`], so the always-on
    /// sub-quadratic `checkRefutes3_sound` reflection would run intractably long —
    /// capped fail-closed (decline; keep `SmtBacked`). This is a robustness cap,
    /// never a soundness relaxation.
    #[error("bvshift refutation too large for the always-on reflection ({steps} > {cap} steps); capped-declined")]
    RefutationTooLarge {
        /// The refutation's resolution-step count.
        steps: usize,
        /// The [`MAX_REFLECTION_STEPS`] cap.
        cap: usize,
    },

    /// The producer's own bit-blast validation rejected the refutation, or the
    /// Clean kernel rejected the reflection certificate.
    #[error("bvshift refutation failed native kernel re-check: {0}")]
    KernelRejected(String),
}

/// A kernel-CERTIFIED bvshift refutation.
///
/// Carries the [`CertifiedPayload`] (the serialized, kernel-re-checkable
/// `Unsat <clauses>` term) plus an honesty summary of the reconstructed
/// barrel-shifter bit-blast.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct BvShiftCertified {
    /// The kernel-checked, serializable payload. `trust_count == 0`; its term
    /// inhabits `Clean.Res.Unsat <clauses>` where `<clauses>` is the bit-blast of
    /// the negated shift goal.
    pub payload: CertifiedPayload,
    /// Number of CNF clauses in the reconstructed barrel-shifter bit-blast.
    pub num_clauses: usize,
    /// Number of resolution steps in the refutation the kernel re-checked.
    pub num_resolution_steps: usize,
}

/// Build the "identity readout" disequality for a shift node at operand width `w`:
/// `not( or(const 0, shift(value, amount)) == shift(value, amount) )`.
///
/// The `or(const 0, …)` wrapper is exactly the RAW identity wrapper the live M-POS
/// gate emits around a shift's `symbolic_machine_output`; both sides bit-blast the
/// SAME barrel shifter through one shared gate cache, so the wrapped readout fuses
/// to the bare shift's output bits and the disequality is UNSAT. It is genuinely
/// shift-shaped: an `ashr` mis-lowered as an `lshr` (or a wrong shift amount) is a
/// real disequality ay refutes, never proved.
///
/// `mk_shift` selects the shift kind (e.g. [`BvExpr::shl`]). `value_leaf` /
/// `amount_leaf` are the free operand names; `width` is the operand width.
#[must_use]
pub fn bvshift_identity_obligation(
    mk_shift: fn(BvExpr, BvExpr) -> BvExpr,
    value_leaf: &str,
    amount_leaf: &str,
    width: u32,
) -> (BvExpr, BvExpr) {
    let value = BvExpr::leaf(value_leaf, width);
    let amount = BvExpr::leaf(amount_leaf, width);
    let shift = mk_shift(value, amount);
    // machine: the RAW `or(0, shift)` identity wrapper the live gate emits.
    let machine = BvExpr::or(BvExpr::const_val(0, width), shift.clone());
    // spec: the bare shift.
    (machine, shift)
}

/// Natively certify a bvshift UNSAT obligation `not(lhs == rhs)` against the Clean
/// kernel, by reflecting ay's barrel-shifter bit-blast refutation.
///
/// `env` must be an [`Environment`] with the resolution-soundness layer
/// initialised (see [`super::pcay_bvmul::bvmul_certify_env`]).
///
/// Returns [`BvShiftCertified`] IFF:
///   * ay bit-blasts and refutes `not(lhs == rhs)` (a SAT obligation → declined),
///   * the refutation is within [`MAX_REFLECTION_STEPS`] (else capped-declined),
///   * the Clean kernel re-checks the reflection `Unsat` cert (`check_type`,
///     `infer_only = false`), with `trust_count == 0`, AND
///   * the kernel's expression-rooted authority audit accepts the exact
///     goal/term dependency closure, provenance, and canonical foundations.
///
/// Any other outcome is a fail-closed [`BvShiftCertifyError`].
///
/// # Errors
/// See [`BvShiftCertifyError`].
pub fn certify_bvshift_unsat(
    env: &Environment,
    lhs: &BvExpr,
    rhs: &BvExpr,
) -> Result<BvShiftCertified, BvShiftCertifyError> {
    // (1) Bit-blast the negated goal `not(lhs == rhs)` into the barrel-shifter CNF
    //     and surface ay's REAL resolution refutation. Fail-closed: a SAT
    //     obligation returns `NoRefutation` — no proof is fabricated.
    let proof = export_bv_blast_proof_expr(lhs, rhs).map_err(|e| match e {
        BvExprExportError::NoRefutation => BvShiftCertifyError::NoRefutation,
        BvExprExportError::SolverUnknown => {
            BvShiftCertifyError::Undecided("ay returned unknown".to_string())
        }
        BvExprExportError::RefutationNotSurfaceable(m) => BvShiftCertifyError::Undecided(m),
        other => BvShiftCertifyError::NotBlastable(other.to_string()),
    })?;

    let num_clauses = proof.clauses.len();
    let num_resolution_steps = proof.refutation.steps.len();

    // (1a) Size cap: the always-on sub-quadratic trie reflection is only tractable
    //      below the cap. An over-cap refutation is DECLINED (kept SmtBacked) — a
    //      robustness cap, never a soundness relaxation.
    if num_resolution_steps > MAX_REFLECTION_STEPS {
        return Err(BvShiftCertifyError::RefutationTooLarge {
            steps: num_resolution_steps,
            cap: MAX_REFLECTION_STEPS,
        });
    }

    // (2) NATIVE, OP-AGNOSTIC kernel re-check: encode clauses + refutation as
    //     kernel data, discharge `checkRefutes3 = true` by reflection (`Eq.refl`),
    //     and apply the PROVED sub-quadratic `checkRefutes3_sound` bridge to obtain
    //     `Unsat <clauses>`. This is the SAME op-agnostic reflection family
    //     milestone 2 uses — it consumes only the `BvBlastProof`, never the shift
    //     op. It internally re-runs the producer `validate()` and
    //     kernel-`infer_type`s the assembled term (so a tampered bit-blast is
    //     rejected here).
    let (unsat_term, unsat_goal) =
        certify_unsat3_by_reflection(env, &proof).map_err(|e| match e {
            ReflectionError::InvalidProof(m) => BvShiftCertifyError::KernelRejected(m),
            ReflectionError::CertificateRejected(m) => BvShiftCertifyError::KernelRejected(m),
        })?;

    // (3) FAIL-CLOSED certification: independent residual-trust re-scan, full
    //     `check_type`, and the kernel's exact expression-rooted authority
    //     audit over the goal/term closure. No local name whitelist authorizes
    //     the payload.
    let ctx = LocalContext::new();
    let payload =
        certify_kernel_term(&unsat_term, &unsat_goal, env, &ctx).map_err(|e| match e {
            NotCertified::TrustedSubterms { count } => BvShiftCertifyError::KernelRejected(
                format!("reflection cert carried {count} residual-trust sub-term(s)"),
            ),
            NotCertified::KernelRejected { message } => {
                BvShiftCertifyError::KernelRejected(message)
            }
            other => BvShiftCertifyError::KernelRejected(format!("{other}")),
        })?;

    Ok(BvShiftCertified {
        payload,
        num_clauses,
        num_resolution_steps,
    })
}

#[cfg(test)]
#[path = "tests_pcay_bvshift.rs"]
mod tests;
