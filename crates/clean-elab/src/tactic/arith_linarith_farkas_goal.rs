// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! General Farkas-with-goal proof reconstruction for linear **Nat** inequality
//! goals (the hyp+neg_goal combination the certified-mathverse replay drops).
//!
//! ## The gap this closes
//!
//! The existing linarith / mathverse proof builders only combine *hypotheses*
//! with each other (`build_chain_proof`, `build_add_le_add_proof`,
//! `build_scaled_proof`). For a goal like `(h1 : a + b ≤ c) (h2 : c ≤ a) ⊢ b ≤ 0`
//! the genuine Farkas certificate mixes the hypotheses **and the negated goal**:
//! `1·h1 + 1·h2 + 1·(¬goal)` collapses to a literally-false inequality. None of
//! the hyp-only combiners introduce the negated goal, so the synthesized term is
//! never the target and `close_goal` rejects it (the reproduced t1/t2/t5 errors).
//!
//! ## The shared Farkas core
//!
//! 1. The goal is normalized to `Nat.le GL GR`, and the case in which it FAILS
//!    is a positive `Nat.le (GR+1) GL` fact — a [`NegGoalFact`].
//! 2. The hypotheses (each at its multiplier) and that fact (at its own
//!    multiplier) are folded with [`SortLeAcc::combine`] (which emits
//!    `Nat.add_le_add`), producing one `acc : Nat.le L R` whose summed endpoints
//!    are, by Farkas, a contradiction (`R + k ≤ R`, `k ≥ 1`).
//! 3. `L` is proved equal to `Nat.add R k` (`k` the positive Farkas gap) by the
//!    EXISTING linear-equality synthesizer
//!    [`super::arith_linarith_nat_eq::try_prove_nat_equality_direct`] — sound iff
//!    the two canonical linear forms match, which they do precisely when the
//!    multipliers are a genuine UNSAT witness. `acc` is transported along that
//!    equality (`Eq.ndrec`) to `acc' : Nat.le (R + k) R`, then handed to the
//!    EXISTING symbolic contradiction closer
//!    [`super::arith_linarith_close::try_close_contradictory_le_generic`], which
//!    derives `False` (shared core `R`, offsets `k > 0`).
//!
//! ## Two wrappers over that core — and why the order matters
//!
//! The core is choice-free. Only the wrapper that brings the failing case into
//! scope had a choice of routes:
//!
//! * [`try_build_constructive_goal_split_proof`] (tried FIRST) splits on
//!   `Nat.le_or_lt GL GR : Or (Nat.le GL GR) (Nat.le (succ GR) GL)` with
//!   `Or.rec`. That lemma is proved by double induction over `Nat.rec`
//!   (`env/algebra_nat_mul_cancel_proof.rs`), so the whole term is
//!   CONSTRUCTIVE, and the `inr` binder already HAS the type the core wants.
//! * [`try_build_farkas_goal_proof`] (the fallback) seals under
//!   `Classical.byContradiction` and manufactures the same fact from `¬G` with
//!   `Nat.not_le` + `Iff.mp`. In this kernel `Classical.byContradiction` is a
//!   Diaconescu-derived theorem, so its closure reaches `Classical.choice`.
//!   `Environment::axiom_deps` filters the foundational axioms out, so a row
//!   reconstructed this way still reports an EMPTY axiom closure there — the
//!   cost is visible only through `Environment::foundational_axiom_deps`.
//!
//! [`try_build_constructive_goal_proof_from_context`] runs the constructive
//! wrapper with no mathverse certificate at all, for the goals whose atoms the
//! `FVarId`-keyed mathverse parser cannot name.
//!
//! ## Soundness
//!
//! Fail-closed and axiom-free. The Farkas multipliers only *guide* assembly; the
//! assembled term is re-checked by `state.close_goal` (`infer_type` + WHNF +
//! `is_def_eq`) and ultimately by `add_decl`. A miscomputed gap yields either a
//! non-contradictory sum (the symbolic closer returns `None` → fail closed) or a
//! term whose type does not match the goal (`close_goal` rejects → fail closed).
//! A FALSE goal has no positive-constant Farkas gap under any enumerated
//! multiplier assignment, so no term is built for it at all. Every constant used
//! (`Nat.le_or_lt`, `Or.rec`, `Nat.add_le_add`, `Nat.le_trans`, `Nat.le.refl`,
//! `Nat.le.step`, `Nat.lt_irrefl`, `Nat.zero_le`, `Eq.ndrec`, `False.elim`, and
//! the `Nat.add_comm` / `Nat.add_assoc` / `congrArg` the equality synthesizer
//! emits) is a constructive prelude theorem or recursor — zero domain-specific
//! axioms and, on the constructive route, zero classical ones.

use clean_kernel::expr::BinderInfo;
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

use super::arith_linarith_chain::{detect_sort, extract_le_args_full};
use super::arith_linarith_close::try_close_contradictory_le_generic;
use super::arith_linarith_farkas_nat::{
    goal_multiplier_bound, inject_nonneg_to_cancel, mk_nat_eq, nat_add, nat_farkas_gap,
    nat_hyp_acc_candidates, neg_goal_lhs_endpoint, negated_goal_fact_classical,
    normalize_nat_goal_to_le, scale_nat_acc, transport_le_lhs,
};
use super::arith_linarith_scale::SortLeAcc;
use super::omega_tactic::MathverseCertificate;
use super::{Goal, ProofState};
use clean_auto::arith_proof::ArithSort;

/// Attempt the general Farkas-with-goal reconstruction for a Nat goal.
///
/// Returns a candidate proof of the ORIGINAL goal (`state.close_goal` re-checks
/// it). Returns `None` whenever any precondition fails — the caller then falls
/// through to the existing replay paths and ultimately fails closed.
///
/// REQUIRES: `certificate.uses_goal_negation` (the negated goal is part of the
///   Farkas witness); otherwise the hyp-only builders already suffice.
pub(crate) fn try_build_farkas_goal_proof(
    state: &mut ProofState,
    goal: &Goal,
    certificate: &MathverseCertificate,
    hypothesis_fvars: &[FVarId],
) -> Option<Expr> {
    if !certificate.uses_goal_negation {
        tracing::debug!("farkas_goal: no goal negation in certificate");
        return None;
    }

    // Required constants — bail (fail closed) if the environment lacks any.
    for c in [
        "Classical.byContradiction",
        "Nat.not_le",
        "Iff.mp",
        "Nat.add_le_add",
    ] {
        if state.env().get_const(&Name::from_string(c)).is_none() {
            tracing::debug!("farkas_goal: missing constant {c}");
            return None;
        }
    }

    // The goal must be a Nat comparison; extract `(GL, GR)` of the normalized
    // `Nat.le GL GR` and confirm Nat sort.
    let Some((goal_le_lhs, goal_le_rhs)) = normalize_nat_goal_to_le(&goal.target) else {
        tracing::debug!("farkas_goal: goal not a Nat comparison");
        return None;
    };

    let flagged: Vec<(usize, i128)> = certificate
        .coefficients
        .iter()
        .enumerate()
        .filter(|&(i, &c)| c > 0 && i < hypothesis_fvars.len())
        .map(|(i, &c)| (i, c))
        .collect();
    let assignments =
        candidate_assignments(&flagged, hypothesis_fvars, goal, &goal_le_lhs, &goal_le_rhs);

    // Fresh by-contradiction hypothesis `hg : ¬G`, converted to the positive
    // `Nat.le (GR+1) GL` fact the Farkas fold consumes.
    let hg_fvar = state.fresh_fvar();
    let neg_fact = negated_goal_fact_classical(&goal_le_lhs, &goal_le_rhs, hg_fvar)?;

    let false_proof = assignments
        .iter()
        .find_map(|a| build_false_from_farkas(goal, a, hypothesis_fvars, &neg_fact))?;

    // Seal under `Classical.byContradiction {G} (fun (hg : ¬G) => false_proof)`.
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let neg_goal = Expr::pi(BinderInfo::Default, goal.target.clone(), false_ty);
    let lambda = Expr::lam(
        BinderInfo::Default,
        neg_goal,
        false_proof.abstract_fvar(hg_fvar),
    );
    let by_contra = Expr::const_(Name::from_string("Classical.byContradiction"), vec![]);
    Some(Expr::app(Expr::app(by_contra, goal.target.clone()), lambda))
}

/// CONSTRUCTIVE Farkas-with-goal reconstruction — the choice-free sibling of
/// [`try_build_farkas_goal_proof`], and the one omega tries first.
///
/// ## Why a second wrapper at all
///
/// The Farkas *core* (fold the hypotheses and the refuted goal with
/// `Nat.add_le_add`, cancel the atoms with `Nat.zero_le`, transport along a
/// linear-form equality, close the constant gap with
/// `Nat.le_trans`/`Nat.lt_irrefl`) is already axiom-free. Only the WRAPPER that
/// puts `¬G` in scope was classical: `Classical.byContradiction` is, in this
/// kernel, a Diaconescu-derived theorem (`env/classical_em_proof.rs`), so every
/// row it reconstructs reaches `Classical.choice`, `propext` and `funext`.
/// `Environment::axiom_deps` FILTERS the foundational axioms out, so that
/// dependency does not show up there at all — it is visible only through
/// `Environment::foundational_axiom_deps`. A lane that reports
/// `axiom_closure: Empty` from `axiom_deps` would therefore have gone classical
/// silently.
///
/// ## The constructive wrapper
///
/// Over `Nat` the disjunction is DECIDABLE and already proved by double
/// induction over `Nat.rec`:
///
/// ```text
/// Nat.le_or_lt GL GR : Or (Nat.le GL GR) (Nat.le (Nat.succ GR) GL)
/// ```
///
/// (`env/algebra_nat_mul_cancel_proof.rs::register_nat_le_or_lt`). `Or.rec` on
/// it gives the same two cases a `byContradiction` would, with none of the
/// choice:
///
/// - `inl (hle : Nat.le GL GR)` — that IS the normalized goal; return it.
/// - `inr (hgt : Nat.le (succ GR) GL)` — the binder already has the type the
///   Farkas fold wants (the classical lane had to manufacture it from `¬G` with
///   `Nat.not_le` + `Iff.mp`), so the shared core builds `False` from it and
///   `False.elim` returns the goal.
///
/// The result is typed at the NORMALIZED `Nat.le GL GR`; `state.close_goal`
/// re-checks it against the original target (`Nat.lt a b` is the reducible
/// `Nat.le (succ a) b`, and `Nat.add a 1` reduces to `Nat.succ a`), which is the
/// soundness gate as everywhere else in this module.
///
/// Returns `None` whenever any precondition fails — the caller then falls
/// through to the classical lane and ultimately fails closed.
pub(crate) fn try_build_constructive_goal_split_proof(
    state: &mut ProofState,
    goal: &Goal,
    certificate: &MathverseCertificate,
    hypothesis_fvars: &[FVarId],
) -> Option<Expr> {
    let flagged: Vec<(usize, i128)> = certificate
        .coefficients
        .iter()
        .enumerate()
        .filter(|&(i, &c)| c > 0 && i < hypothesis_fvars.len())
        .map(|(i, &c)| (i, c))
        .collect();
    build_constructive_goal_split(state, goal, &flagged, hypothesis_fvars)
}

/// The same constructive builder, run WITHOUT a mathverse certificate — its own
/// Farkas-gap test is the decision procedure.
///
/// This exists because the certified mathverse path cannot always get here. The
/// mathverse linear parser names atoms by `FVarId`
/// (`arith_mathverse_parse::linear::expr_to_linear_direct` maps `ExprKind::FVar`
/// and nothing else), so a Nat term with an opaque application head —
/// `UInt32.toNat d`, `Nat.xor a b`, any function call — parses to NOTHING:
/// `extract_certified_mathverse_constraints` returns `None`, the certified
/// block never runs, and omega reports "could not extract linear constraints"
/// even though the goal is a one-step linear consequence of its hypotheses.
///
/// The Farkas builder does not share that limitation: its linear forms come
/// from `arith_linarith_nat_eq::parse_nat_linear_form`, which is keyed by
/// **`Expr`** and atomizes an unrecognized head as an opaque atom. So the whole
/// decision can be made here: fold the hypotheses and the refuted goal, and ask
/// whether the residual is a positive constant. No constant gap ⇒ `None`, and
/// `close_goal` re-checks whatever is built — fail-closed on both ends.
pub(crate) fn try_build_constructive_goal_proof_from_context(
    state: &mut ProofState,
    goal: &Goal,
) -> Option<Expr> {
    let hypothesis_fvars: Vec<FVarId> = goal
        .local_ctx
        .iter()
        .filter(|d| !nat_hyp_acc_candidates(goal, d.fvar).is_empty())
        .map(|d| d.fvar)
        .collect();
    if hypothesis_fvars.is_empty() {
        return None;
    }
    build_constructive_goal_split(state, goal, &[], &hypothesis_fvars)
}

fn build_constructive_goal_split(
    state: &mut ProofState,
    goal: &Goal,
    flagged: &[(usize, i128)],
    hypothesis_fvars: &[FVarId],
) -> Option<Expr> {
    // Required constants — bail (fail closed) if the environment lacks any.
    // `Nat.le_or_lt` is the constructive totality lemma; the rest are the
    // recursor/eliminator plumbing.
    for c in [
        "Nat.le_or_lt",
        "Or",
        "Or.rec",
        "False.elim",
        "Nat.add_le_add",
    ] {
        if state.env().get_const(&Name::from_string(c)).is_none() {
            tracing::debug!("constructive_goal_split: missing constant {c}");
            return None;
        }
    }

    let Some((goal_le_lhs, goal_le_rhs)) = normalize_nat_goal_to_le(&goal.target) else {
        tracing::debug!("constructive_goal_split: goal not a Nat comparison");
        return None;
    };

    // The two `Or` sides, spelled EXACTLY as `Nat.le_or_lt GL GR`'s type does
    // (`lt_of x y = le_of (succ x) y` in `algebra_nat_mul_cancel_proof.rs`).
    let side_le = nat_le_raw(&goal_le_lhs, &goal_le_rhs);
    let side_gt = nat_le_raw(&nat_succ(&goal_le_rhs), &goal_le_lhs);

    // The `inr` binder IS the positive refuted-goal fact — no conversion needed.
    let hgt_fvar = state.fresh_fvar();
    let neg_fact = NegGoalFact {
        lhs: neg_goal_lhs_endpoint(&goal_le_rhs)?,
        rhs: goal_le_lhs.clone(),
        proof: Expr::fvar(hgt_fvar),
    };

    let assignments =
        candidate_assignments(flagged, hypothesis_fvars, goal, &goal_le_lhs, &goal_le_rhs);
    let false_proof = assignments
        .iter()
        .find_map(|a| build_false_from_farkas(goal, a, hypothesis_fvars, &neg_fact))?;

    // `fun (hle : Nat.le GL GR) => hle`
    let case_inl = Expr::lam(BinderInfo::Default, side_le.clone(), Expr::bvar(0));
    // `fun (hgt : Nat.le (succ GR) GL) => False.elim (Nat.le GL GR) <false>`
    let case_inr = Expr::lam(
        BinderInfo::Default,
        side_gt.clone(),
        super::arith_linarith_close::wrap_false_elim(false_proof, &side_le).abstract_fvar(hgt_fvar),
    );
    // `fun (_ : Or A B) => Nat.le GL GR`
    let or_ty = Expr::apps(
        Expr::const_(Name::from_string("Or"), vec![]),
        [side_le.clone(), side_gt.clone()],
    );
    let motive = Expr::lam(BinderInfo::Default, or_ty, side_le.clone());
    let major = Expr::apps(
        Expr::const_(Name::from_string("Nat.le_or_lt"), vec![]),
        [goal_le_lhs, goal_le_rhs],
    );

    Some(Expr::apps(
        Expr::const_(Name::from_string("Or.rec"), vec![]),
        [side_le, side_gt, motive, case_inl, case_inr, major],
    ))
}

/// `Nat.le a b` in the raw (non-typeclass) spelling `Nat.le_or_lt` uses.
fn nat_le_raw(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.le"), vec![]),
        [a.clone(), b.clone()],
    )
}

/// `Nat.succ a`.
fn nat_succ(a: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        a.clone(),
    )
}

/// One positive `Nat.le` fact standing for the refuted goal: the declared
/// endpoints `(GR+1, GL)` plus a term whose type is def-eq to
/// `Nat.le (GR+1) GL`.
///
/// Two producers build one: [`negated_goal_fact_classical`] (from
/// `hg : ¬G` via `Nat.not_le` + `Iff.mp`, the `Classical.byContradiction` lane)
/// and [`negated_goal_fact_constructive`] (the `inr` binder of
/// `Nat.le_or_lt`, which already HAS that type). Everything downstream of this
/// struct is shared and choice-free.
pub(super) struct NegGoalFact {
    pub(super) lhs: Expr,
    pub(super) rhs: Expr,
    pub(super) proof: Expr,
}

/// A candidate Farkas multiplier assignment: one multiplier per active
/// hypothesis, plus the multiplier on the refuted goal.
///
/// The negated goal needs its own multiplier because the "divide the atom out"
/// family lives there and nowhere else: `(h : 2*n < 42) ⊢ n < 21` is
/// `1·h + 2·(¬goal)`, which no assignment that fixes the goal at 1 can express.
struct FarkasAssignment {
    hyps: Vec<(usize, i128)>,
    neg_goal: i128,
}

/// The multiplier assignments to try, in order.
///
/// 1. The certificate-flagged hypotheses at their certificate multipliers, goal
///    at 1 — the historical set, tried first so a certificate that already
///    carries real multipliers keeps its exact reconstruction.
/// 2. Every parseable hypothesis at a uniform `m`, goal at `g`, for every
///    `(m, g)` in `1..=bound`. The 0/1 certificate collapses the true Farkas
///    multiplier to 1, so the scaled families (`3*n < 63` from `n < 21`,
///    `n < 21` from `2*n < 42`) are only reachable by enumeration.
///
/// `bound` is the largest literal coefficient appearing in the goal or in any
/// parseable hypothesis, capped — so the search is small and data-driven rather
/// than a fixed grid. Soundness is unaffected by any of this: a wrong
/// multiplier leaves an uncancellable residual (the Farkas gap is then not a
/// positive constant) and the kernel re-check rejects any wrong term.
fn candidate_assignments(
    flagged: &[(usize, i128)],
    hypothesis_fvars: &[FVarId],
    goal: &Goal,
    goal_le_lhs: &Expr,
    goal_le_rhs: &Expr,
) -> Vec<FarkasAssignment> {
    let mut out: Vec<FarkasAssignment> = Vec::new();
    if !flagged.is_empty() {
        out.push(FarkasAssignment {
            hyps: flagged.to_vec(),
            neg_goal: 1,
        });
    }

    let bound = farkas_multiplier_bound(goal, goal_le_lhs, goal_le_rhs);
    for m in 1..=bound {
        for g in 1..=bound {
            let hyps: Vec<(usize, i128)> = (0..hypothesis_fvars.len()).map(|i| (i, m)).collect();
            // A hypothesis-free refutation (goal + implicit non-negativity only)
            // is legitimate, but only at `m == 1` — there is nothing to scale.
            if hyps.is_empty() && m != 1 {
                continue;
            }
            out.push(FarkasAssignment { hyps, neg_goal: g });
        }
    }
    out
}

/// Upper bound on the Farkas multipliers to enumerate: the largest literal
/// coefficient in the normalized goal endpoints or in any Nat comparison
/// hypothesis. Capped so the search stays cheap; a genuine
/// higher-coefficient problem simply fails closed (no wrong term is ever
/// emitted).
fn farkas_multiplier_bound(goal: &Goal, goal_le_lhs: &Expr, goal_le_rhs: &Expr) -> i128 {
    const CAP: i128 = 8;
    let mut bound = goal_multiplier_bound(goal_le_lhs, goal_le_rhs);
    for decl in &goal.local_ctx {
        let Some((alpha, _op, a, b)) = extract_le_args_full(&decl.ty) else {
            continue;
        };
        if detect_sort(&alpha) != Some(ArithSort::Nat) {
            continue;
        }
        let side_bound = goal_multiplier_bound(&a, &b);
        if side_bound > bound {
            bound = side_bound;
        }
    }
    bound.clamp(1, CAP)
}

/// Build the `False` proof from one multiplier assignment.
///
/// Folds the active hypotheses (each at its multiplier), the refuted goal (at
/// its own multiplier), and — crucially — the implicit Nat non-negativity facts
/// `0 ≤ v` needed to close the residual. Equality hypotheses are tried in both
/// orientations.
fn build_false_from_farkas(
    goal: &Goal,
    assignment: &FarkasAssignment,
    hypothesis_fvars: &[FVarId],
    neg_fact: &NegGoalFact,
) -> Option<Expr> {
    // Each active hypothesis contributes one (≤/<) or two (= : both orientations)
    // candidate `Nat.le` facts. Try every orientation combination; equality-heavy
    // goals are rare, and we bound the search to keep it cheap.
    let mut candidate_sets: Vec<Vec<SortLeAcc>> = Vec::with_capacity(assignment.hyps.len());
    let mut coeffs: Vec<i128> = Vec::with_capacity(assignment.hyps.len());
    for &(idx, coeff) in &assignment.hyps {
        let fvar = hypothesis_fvars[idx];
        let cands = nat_hyp_acc_candidates(goal, fvar);
        if cands.is_empty() {
            return None;
        }
        candidate_sets.push(cands);
        coeffs.push(coeff);
    }

    // Bound the orientation search (2^n over equality hypotheses).
    const MAX_ORIENTATION_COMBOS: usize = 64;
    let combos = candidate_sets.iter().map(Vec::len).product::<usize>();
    if combos > MAX_ORIENTATION_COMBOS {
        tracing::debug!("farkas_goal: too many equality orientations ({combos}); fail closed");
        return None;
    }

    for combo in 0..combos {
        if let Some(proof) = try_one_orientation(
            goal,
            &candidate_sets,
            &coeffs,
            neg_fact,
            assignment.neg_goal,
            combo,
        ) {
            return Some(proof);
        }
    }
    None
}

/// Try a single orientation assignment of the equality hypotheses (decoded from
/// `combo` as a mixed-radix index over `candidate_sets`).
fn try_one_orientation(
    goal: &Goal,
    candidate_sets: &[Vec<SortLeAcc>],
    coeffs: &[i128],
    neg_fact: &NegGoalFact,
    neg_coeff: i128,
    combo: usize,
) -> Option<Expr> {
    // Fold the chosen-orientation hypotheses (each at its certificate multiplier)
    // into one accumulator `hyp_acc : Nat.le H_lhs H_rhs`.
    let mut radix = combo;
    let mut hyp_acc: Option<SortLeAcc> = None;
    for (set, &coeff) in candidate_sets.iter().zip(coeffs) {
        let pick = radix % set.len();
        radix /= set.len();
        let chosen = &set[pick];
        // `SortLeAcc` is not `Clone`; rebuild from its parts.
        let base = SortLeAcc::nat_from_parts(
            chosen.lhs.clone(),
            chosen.rhs.clone(),
            chosen.proof.clone(),
        )?;
        let scaled = scale_nat_acc(base, coeff)?;
        hyp_acc = Some(match hyp_acc {
            None => scaled,
            Some(a) => a.combine(scaled)?,
        });
    }

    // Refuted-goal positive `Nat.le NG_lhs NG_rhs` (= `succ GR ≤ GL`), at its
    // own multiplier.
    let neg_goal_acc = scale_nat_acc(
        SortLeAcc::nat_from_parts(
            neg_fact.lhs.clone(),
            neg_fact.rhs.clone(),
            neg_fact.proof.clone(),
        )?,
        neg_coeff,
    )?;

    // Fold hyps (if any) with the negated goal. With no parseable hypotheses the
    // refutation is goal+nonneg only (e.g. the goal itself forces a Nat bound).
    let base_acc = match hyp_acc {
        Some(a) => a.combine(neg_goal_acc)?,
        None => neg_goal_acc,
    };
    if base_acc.sort != ArithSort::Nat {
        return None;
    }

    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    close_nat_le_by_farkas_gap(goal, base_acc, &false_ty)
}

/// The closing half of the Farkas core, shared with the hypothesis-only
/// builders (`arith_linarith_proof`): from `acc : Nat.le L R` whose residual
/// `L - R` is a non-negative combination of Nat atoms plus a positive
/// constant, prove `target` by `False.elim`.
///
/// Cancel every atom with a positive residual coefficient by `0 ≤ v`
/// ([`inject_nonneg_to_cancel`]), prove `L' = R' + k` for the constant gap
/// `k ≥ 1` with the linear-equality synthesizer, transport `acc` along it and
/// close `R' + k ≤ R'`. `None` when the residual has a negative atom
/// coefficient, a non-positive constant, or an atom no `0 ≤ v` fact covers.
/// The term is re-checked by the caller's `close_goal`.
pub(crate) fn close_nat_le_by_farkas_gap(
    goal: &Goal,
    acc: SortLeAcc,
    target: &Expr,
) -> Option<Expr> {
    if acc.sort != ArithSort::Nat {
        return None;
    }
    // Compute the residual `acc.lhs - acc.rhs` and cancel every positive
    // Nat-atom coefficient with the implicit `0 ≤ v` fact. This is the Farkas
    // positive combination that mixes a hypothesis with the implicit bound:
    // `(b - a - 2 ≥ 0 from hyp) + (a ≥ 0 implicit) ⟹ (b - 2 ≥ 0)`.
    let acc = inject_nonneg_to_cancel(goal, acc)?;

    // `acc : Nat.le L R`. By Farkas, `L` equals `R + k` for some `k ≥ 1` as
    // linear forms. Find `k` from the linear-form gap.
    let Some(k) = nat_farkas_gap(&acc.lhs, &acc.rhs) else {
        tracing::debug!("farkas_goal: summed endpoints not a positive-constant gap");
        return None;
    };
    if k < 1 {
        return None;
    }
    let k_lit = Expr::nat_lit(k);
    let r_plus_k = nat_add(&acc.rhs, &k_lit);

    // Prove `L = R + k` via the existing linear-equality synthesizer.
    let eq_goal = mk_nat_eq(&acc.lhs, &r_plus_k);
    let Some(eq_proof) = super::arith_linarith_nat_eq::try_prove_nat_equality_direct(&eq_goal)
    else {
        // Fail closed if the Farkas sum keeps an unreconstructible atom; the
        // caller falls through and no wrong term is emitted.
        tracing::debug!("farkas_goal: linear-equality synthesizer failed for L = R + k");
        return None;
    };

    // Transport `acc : Nat.le L R` along `eq_proof : L = R + k` to
    // `acc' : Nat.le (R + k) R` via `@Eq.ndrec Nat L (fun z => Nat.le z R) acc (R+k) eq_proof`.
    let acc_transported = transport_le_lhs(&acc.proof, &acc.lhs, &acc.rhs, &r_plus_k, &eq_proof);

    // Derive `False` via the symbolic closer (shared core `R`, offsets k, 0).
    let closed = try_close_contradictory_le_generic(
        ArithSort::Nat,
        &acc_transported,
        &r_plus_k,
        &acc.rhs,
        target,
    );
    if closed.is_none() {
        tracing::debug!("farkas_goal: symbolic contradiction closer returned None for (R+k, R)");
    }
    closed
}
