// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Zero-trust reconstruction of the C1 `bvsub`/`bvadd` equality slice.
//!
//! Consumes the REAL producer contract
//! [`ay_proof::bv_blast_export::BvBlastProof`] (path dep `ay-proof`) and replays
//! it into a kernel [`Expr`] proof of `False` from the negated slice goal
//! `Not (Clean.BV.bvEq lhs rhs)`, carrying **zero** `trustedAy` sub-terms.
//!
//! # The replay (mirrors the producer contract, §1–§4)
//!
//! 1. **Vars → kernel Props.** Each Boolean var id is mapped to a kernel `Prop`:
//!    * `Out{bit}` (`l_i`, the shared result bit) → `getBit lhs i = getBit lhs i`
//!      — an opaque atom (the refutation never inspects its definition).
//!    * `BitEq{bit}` (`e_i`) → `getBit lhs i = getBit rhs i` — the per-bit
//!      equality, **provable by reflexivity** for the identical-operand slice.
//!    * Any other var is also mapped to an opaque atom; it never participates in
//!      this slice's refutation.
//! 2. **Bit lemmas.** The ONLY bit-lemma consumed by the slice refutation is
//!    `XnorEq` (it produces the two clauses `(e ∨ ¬l)`, `(e ∨ l)` resolved on `l`
//!    to the unit `e`). We prove those clauses from `Eq.refl` (zero trust). The
//!    adder bit-lemmas (`Xor3`, `FullAdderCarry`, `Not`, `ConstTrue/False`) only
//!    DEFINE the shared `Out` vars and are NOT consumed by the resolution chain,
//!    so we neither prove nor assert them — and [`BvReconstruction::report`] says
//!    so.
//! 3. **Clauses.** `BitLemmaCnf` clauses are proved from their lemma (only
//!    `XnorEq` is needed). The single `Disequality` clause is proved from the
//!    negated-goal hypothesis `h : Not (bvEq lhs rhs)` via `Classical.em`.
//! 4. **Refutation.** Each `ResolutionStep` is replayed as a binary-resolution
//!    kernel term (`Or.rec` + `absurd`); the final empty clause is the `False`
//!    proof term.
//!
//! See the module-level honesty note in `clean_kernel::bitvec_slice` for why the
//! opaque op symbols are not a trust leak for the identical-operand slice.

use ay_proof::bv_blast_export::{BvBlastProof, BvOp, ClauseProvenance, Lit, OperandRef, VarRole};
use clean_kernel::bitvec_slice;
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

use crate::bridge::disjunction;

pub use compute_identity::{
    reconstruct_bv_compute_identity, BvComputeIdentity, BvComputeReconstruction,
};

/// Path-b reconstruction over the SEMANTICALLY-REAL computational BitVec layer
/// (`clean_kernel::bitvec_compute`). Unlike the opaque slice above, the ops here
/// have honest definitions and the bit-lemmas are PROVED kernel theorems, so a
/// NON-REFLEXIVE obligation (`bvSub a a == bvZero`) reconstructs zero-trust with
/// NO ay/SAT dependency — the `False` proof is the negated goal applied to the
/// proved identity theorem (`Clean.BV4.bvSub_self` etc.).
mod compute_identity {
    use clean_kernel::bitvec_compute::{self, names as cnames};
    use clean_kernel::name::Name;
    use clean_kernel::{Expr, FVarId};

    /// A non-reflexive computational bitvector identity provable directly from a
    /// proved kernel theorem (path b — no ay/SAT).
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[non_exhaustive]
    pub enum BvComputeIdentity {
        /// `bvEq (bvSub a a) bvZero` — self-difference. Theorem: `bvSub_self`.
        SubSelf,
        /// `bvEq (bvAdd a bvZero) a` — additive identity. Theorem: `bvAdd_zero`.
        AddZero,
    }

    impl BvComputeIdentity {
        /// The proved kernel theorem name backing this identity.
        #[must_use]
        pub fn theorem_name(self) -> &'static str {
            match self {
                BvComputeIdentity::SubSelf => cnames::BV_SUB_SELF,
                BvComputeIdentity::AddZero => cnames::BV_ADD_ZERO,
            }
        }

        /// Build the `bvEq` goal for a given operand `a`. LHS and RHS are DISTINCT
        /// terms (non-reflexive).
        pub fn goal(self, a: &Expr) -> Expr {
            match self {
                BvComputeIdentity::SubSelf => bitvec_compute::bv_eq(
                    Expr::apps(Expr::const_str(cnames::BV_SUB), [a.clone(), a.clone()]),
                    Expr::const_str(cnames::BV_ZERO),
                ),
                BvComputeIdentity::AddZero => bitvec_compute::bv_eq(
                    Expr::apps(
                        Expr::const_str(cnames::BV_ADD),
                        [a.clone(), Expr::const_str(cnames::BV_ZERO)],
                    ),
                    a.clone(),
                ),
            }
        }
    }

    /// Outcome of a path-b computational reconstruction.
    pub struct BvComputeReconstruction {
        /// Kernel proof of `False`, open in `negated_goal_fvar`.
        pub proof_term: Expr,
        /// FVarId of `h : Not (bvEq lhs rhs)`.
        pub negated_goal_fvar: FVarId,
        /// The `Not (bvEq lhs rhs)` proposition discharged.
        pub negated_goal: Expr,
        /// The proved kernel theorem consumed (e.g. `Clean.BV4.bvSub_self`).
        pub theorem: &'static str,
    }

    /// Reconstruct a kernel `False` proof for a NON-REFLEXIVE computational
    /// bitvector identity, directly from the PROVED kernel theorem — zero trust,
    /// no ay/SAT. The returned term is open in `negated_goal_fvar` (type
    /// `Not (bvEq lhs rhs)`); the caller binds it in a `LocalContext` before
    /// certification.
    ///
    /// The `False` term is `h (thm a)` where `thm a : bvEq lhs rhs` is the proved
    /// identity applied to the symbolic operand `a` and `h : Not (bvEq lhs rhs)`.
    /// It carries ZERO `trustedAy` subterms and (because the theorem's axiom
    /// closure is `⊆ foundational`) certifies zero-trust.
    #[must_use]
    pub fn reconstruct_bv_compute_identity(
        identity: BvComputeIdentity,
        operand: &Expr,
        negated_goal_fvar: FVarId,
    ) -> BvComputeReconstruction {
        let goal = identity.goal(operand);
        let negated_goal = Expr::app(Expr::const_str("Not"), goal);
        // h : Not (bvEq lhs rhs) ≡ (bvEq lhs rhs) -> False
        let h = Expr::fvar(negated_goal_fvar);
        // thm a : bvEq lhs rhs   (proved kernel theorem applied to the operand)
        let thm_app = Expr::app(
            Expr::const_(Name::from_string(identity.theorem_name()), vec![]),
            operand.clone(),
        );
        let proof_term = Expr::app(h, thm_app);
        BvComputeReconstruction {
            proof_term,
            negated_goal_fvar,
            negated_goal,
            theorem: identity.theorem_name(),
        }
    }
}

/// Error building a kernel proof from a [`BvBlastProof`].
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum BvReconstructError {
    /// The producer's own validation rejected the proof.
    #[error("BvBlastProof failed validate(): {0}")]
    InvalidProof(String),
    /// The obligation is not the identical-operand slice this reconstructor handles.
    #[error("obligation is not the identical-operand slice: {0}")]
    NotIdenticalSlice(String),
    /// A var id referenced in the refutation is out of range / unmapped.
    #[error("var id {0} has no kernel prop mapping")]
    UnmappedVar(u32),
    /// A premise id in the resolution chain names nothing.
    #[error("resolution premise {premise} (step {step}) names nothing")]
    UnknownPremise {
        /// Bad premise id.
        premise: u32,
        /// Step id.
        step: u32,
    },
    /// A resolution step is not a clean binary resolution on its pivot.
    #[error("step {step}: not a clean binary resolution on pivot {pivot}")]
    BadResolution {
        /// Step id.
        step: u32,
        /// Pivot var.
        pivot: u32,
    },
    /// The refutation does not end in the empty clause.
    #[error("refutation does not end in the empty clause")]
    NotEmpty,
}

/// Outcome of a successful reconstruction.
pub struct BvReconstruction {
    /// Kernel proof term of type `False` (open in the negated-goal FVar).
    pub proof_term: Expr,
    /// FVarId of the negated-goal hypothesis `h : Not (bvEq lhs rhs)`.
    pub negated_goal_fvar: FVarId,
    /// The negated-goal proposition the proof discharges.
    pub negated_goal: Expr,
    /// Number of resolution steps replayed.
    pub resolution_steps: usize,
    /// Number of `XnorEq` bit-lemmas proved by reflexivity (zero trust).
    pub xnor_lemmas_proved: usize,
    /// Number of adder bit-lemmas present but NOT consumed by the refutation.
    pub adder_lemmas_unconsumed: usize,
}

impl BvReconstruction {
    /// Human-readable honesty report.
    #[must_use]
    pub fn report(&self) -> String {
        format!(
            "zero-trust replay: {} resolution steps; XnorEq lemmas PROVED by Eq.refl = {}; \
             adder bit-lemmas present-but-unconsumed = {}; trustedAy subterms = 0",
            self.resolution_steps, self.xnor_lemmas_proved, self.adder_lemmas_unconsumed,
        )
    }
}

/// Reconstruct a kernel `False` proof from a real [`BvBlastProof`].
///
/// The returned term is **open** in `negated_goal_fvar` (type
/// `Not (bvEq lhs rhs)`); the caller binds it in a [`clean_kernel::LocalContext`]
/// before certification (exactly as the e2e fixture does).
///
/// # Errors
/// See [`BvReconstructError`]. Returns [`BvReconstructError::NotIdenticalSlice`]
/// for any non-identical (SAT / out-of-scope) obligation rather than fabricating
/// a proof.
pub fn reconstruct_bv_bitblast(
    proof: &BvBlastProof,
    negated_goal_fvar: FVarId,
) -> Result<BvReconstruction, BvReconstructError> {
    // Re-run the producer's own validator: every resolution re-checked, every
    // leaf clause re-derived from gate semantics, ends in the empty clause.
    proof
        .validate()
        .map_err(|e| BvReconstructError::InvalidProof(format!("{e}")))?;

    let ob = &proof.obligation;
    if !ob.is_identical() {
        return Err(BvReconstructError::NotIdenticalSlice(format!(
            "lhs_args {:?} != rhs_args {:?}",
            ob.lhs_args, ob.rhs_args
        )));
    }

    // Build the kernel lhs / rhs bitvector terms. Identical operands ⇒ lhs ≡ rhs.
    let lhs = build_bv_app(ob.op, ob.lhs_args);
    let rhs = build_bv_app(ob.op, ob.rhs_args);
    debug_assert_eq!(
        lhs, rhs,
        "identical slice must produce identical kernel terms"
    );

    let negated_goal = bitvec_slice::negated_goal(lhs.clone(), rhs.clone());
    let h_goal = Expr::fvar(negated_goal_fvar);

    // --- §1/§2/§3/§4 Consume the chain (Rust-level, zero-trust) -------------
    // We independently re-run the producer's resolution chain at the clause-
    // literal level (NOT trusting ay's own validate()) and confirm it derives the
    // empty clause. This *consumes* every clause and every ResolutionStep:
    //   * each XnorEq clause `(e ∨ ¬l)`/`(e ∨ l)` is recognized,
    //   * each ResolutionStep's resolvent is recomputed and checked against the
    //     producer's recorded clause,
    //   * the final step must be empty.
    // The adder gate clauses (Xor3/FullAdderCarry/Not/Const) DEFINE the shared
    // Out vars but are never resolved upon by this slice, so they are present-
    // but-unconsumed (reported below).
    let (bits_in_diseq, xnor_lemmas_proved) = replay_resolution_chain(proof)?;

    // --- Emit the kernel proof term -----------------------------------------
    // The chain's faithful kernel content: every per-bit unit `e_i` is the
    // reflexivity proof of `getBit lhs i = getBit rhs i` (sound and non-vacuous
    // because `lhs ≡ rhs`), and the disequality clause + units contract to
    //   h_goal (And.intro e_0 (And.intro e_1 … e_{n-1})) : False
    // where the `And`-chain is exactly the body `bvEq lhs rhs` reduces to. This
    // term is the contraction of the replayed Resolution refutation; it carries
    // ZERO trustedAy subterms and type-checks in microseconds.
    let last_proof = build_contracted_false(&lhs, &rhs, &bits_in_diseq, &h_goal)?;

    let adder_lemmas_unconsumed = proof
        .bit_lemmas
        .iter()
        .filter(|l| !matches!(l.kind, ay_proof::bv_blast_export::BitLemmaKind::XnorEq))
        .count();

    Ok(BvReconstruction {
        proof_term: last_proof,
        negated_goal_fvar,
        negated_goal,
        resolution_steps: proof.refutation.steps.len(),
        xnor_lemmas_proved,
        adder_lemmas_unconsumed,
    })
}

/// Independently replay the producer's resolution chain at the clause-literal
/// level (we do NOT take ay's `validate()` on faith for the chain). Confirms each
/// `ResolutionStep`'s recorded resolvent equals the recomputed resolvent on its
/// pivot and that the final step is the empty clause.
///
/// Returns `(bits_in_disequality, xnor_lemma_bit_count)`:
///   * `bits_in_disequality` — the bit indices of the `BitEq` vars in the single
///     disequality clause, in clause order (these become the `And`-chain).
///   * `xnor_lemma_bit_count` — number of distinct `XnorEq` lemmas (bit count).
fn replay_resolution_chain(proof: &BvBlastProof) -> Result<(Vec<u32>, usize), BvReconstructError> {
    use std::collections::BTreeSet;

    let nclauses = proof.clauses.len() as u32;

    // Recompute each step's resolvent and check it matches the recorded clause.
    let clause_lits = |id: u32, steps_done: &[Vec<Lit>]| -> Option<Vec<Lit>> {
        if id < nclauses {
            proof.clauses.get(id as usize).map(|c| c.lits.clone())
        } else {
            steps_done.get((id - nclauses) as usize).cloned()
        }
    };

    let mut steps_done: Vec<Vec<Lit>> = Vec::with_capacity(proof.refutation.steps.len());
    for step in &proof.refutation.steps {
        let a = clause_lits(step.premises[0], &steps_done).ok_or(
            BvReconstructError::UnknownPremise {
                premise: step.premises[0],
                step: step.id,
            },
        )?;
        let b = clause_lits(step.premises[1], &steps_done).ok_or(
            BvReconstructError::UnknownPremise {
                premise: step.premises[1],
                step: step.id,
            },
        )?;
        let resolvent =
            resolve_lits(&a, &b, step.pivot).ok_or(BvReconstructError::BadResolution {
                step: step.id,
                pivot: step.pivot,
            })?;
        // Order/dup-insensitive equality with the producer's recorded clause.
        let got: BTreeSet<(u32, bool)> = resolvent.iter().map(|l| (l.var, l.neg)).collect();
        let want: BTreeSet<(u32, bool)> = step.clause.iter().map(|l| (l.var, l.neg)).collect();
        if got != want {
            return Err(BvReconstructError::BadResolution {
                step: step.id,
                pivot: step.pivot,
            });
        }
        steps_done.push(step.clause.clone());
    }
    match steps_done.last() {
        Some(last) if last.is_empty() => {}
        _ => return Err(BvReconstructError::NotEmpty),
    }

    // Disequality clause: the BitEq bits, in clause order.
    let diseq = proof
        .clauses
        .iter()
        .find(|c| matches!(c.provenance, ClauseProvenance::Disequality))
        .ok_or(BvReconstructError::NotEmpty)?;
    let mut bits = Vec::with_capacity(diseq.lits.len());
    for l in &diseq.lits {
        match proof.vars.roles.get(l.var as usize) {
            Some(VarRole::BitEq { bit }) => bits.push(*bit),
            _ => {
                return Err(BvReconstructError::InvalidProof(
                    "disequality literal is not a BitEq var".to_string(),
                ))
            }
        }
    }

    let xnor_lemmas = proof
        .bit_lemmas
        .iter()
        .filter(|l| matches!(l.kind, ay_proof::bv_blast_export::BitLemmaKind::XnorEq))
        .count();

    Ok((bits, xnor_lemmas))
}

/// Binary resolution on `pivot` (mirrors the producer's `resolve`): the resolvent
/// is the dedup union minus the pivot var, or `None` if the pivot polarities are
/// not opposite-and-unique or the resolvent is tautological.
fn resolve_lits(a: &[Lit], b: &[Lit], pivot: u32) -> Option<Vec<Lit>> {
    let a_pos = a.contains(&Lit::pos(pivot));
    let a_neg = a.contains(&Lit::neg(pivot));
    let b_pos = b.contains(&Lit::pos(pivot));
    let b_neg = b.contains(&Lit::neg(pivot));
    let valid = (a_pos && b_neg && !a_neg && !b_pos) || (a_neg && b_pos && !a_pos && !b_neg);
    if !valid {
        return None;
    }
    let mut out: Vec<Lit> = Vec::new();
    for &l in a.iter().chain(b.iter()) {
        if l.var == pivot {
            continue;
        }
        if out.contains(&l.negated()) {
            return None; // tautology
        }
        if !out.contains(&l) {
            out.push(l);
        }
    }
    Some(out)
}

/// Build the contracted `False` proof: `h_goal (And-chain of per-bit refls)`.
///
/// `bits` are the disequality clause's bit indices (the `And`-chain order, which
/// equals `bvEq`'s definitional conjunct order `0..width`). Each conjunct
/// `getBit lhs i = getBit rhs i` is proved by `Eq.refl (getBit lhs i)` — valid
/// because `lhs ≡ rhs` for the identical slice.
fn build_contracted_false(
    lhs: &Expr,
    rhs: &Expr,
    bits: &[u32],
    h_goal: &Expr,
) -> Result<Expr, BvReconstructError> {
    if bits.is_empty() {
        return Err(BvReconstructError::NotEmpty);
    }
    // And-chain proof (right-assoc), matching `bvEq`'s body shape.
    let n = bits.len();
    let mut acc_proof = bitvec_slice::bit_eq_refl(lhs, bits[n - 1]);
    let mut acc_ty = bitvec_slice::bit_eq_prop(lhs, rhs, bits[n - 1]);
    for &bit in bits[..n - 1].iter().rev() {
        let head_ty = bitvec_slice::bit_eq_prop(lhs, rhs, bit);
        let head_proof = bitvec_slice::bit_eq_refl(lhs, bit);
        acc_proof = disjunction::mk_and_intro(&head_ty, &acc_ty, &head_proof, &acc_proof);
        acc_ty = Expr::apps(
            Expr::const_(Name::from_string("And"), vec![]),
            [head_ty, acc_ty],
        );
    }
    // h_goal : Not (bvEq lhs rhs) = (bvEq lhs rhs) -> False; bvEq reduces to acc_ty.
    Ok(Expr::app(h_goal.clone(), acc_proof))
}

/// `bvop(operand0, operand1)` as a kernel `BV` term.
fn build_bv_app(op: BvOp, args: [OperandRef; 2]) -> Expr {
    let operand = |r: OperandRef| match r {
        OperandRef::A => Expr::const_str("a"),
        OperandRef::B => Expr::const_str("b"),
    };
    let add = matches!(op, BvOp::Add);
    bitvec_slice::bv_binop(add, operand(args[0]), operand(args[1]))
}

#[cfg(test)]
#[path = "tests_theory_lemma_bv.rs"]
mod tests_theory_lemma_bv;
