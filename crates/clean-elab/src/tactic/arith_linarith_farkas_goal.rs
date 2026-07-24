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
//! ## Construction (by-contradiction Farkas sum, Nat)
//!
//! 1. `Classical.byContradiction {G} (fun (hg : ¬G) => <False>)` wraps the goal,
//!    putting `hg : ¬G` (i.e. `G → False`) in scope.
//! 2. `¬G` is turned into a *positive* `Nat.le` via `Nat.not_le` + `Iff.mp`:
//!    `¬(GL ≤ GR)` ⟹ `GR < GL` ≡ `Nat.le (Nat.succ GR) GL`. (`Nat.lt b a` is the
//!    reducible def `Nat.le (Nat.succ b) a`.) This is the missing `from_negated_goal`
//!    accumulator.
//! 3. The hypotheses (each at its certificate multiplier) and the negated-goal
//!    accumulator are folded with the EXISTING [`SortLeAcc::combine`] (which emits
//!    `Nat.add_le_add`), producing one `acc : Nat.le L R` whose summed endpoints
//!    are, by Farkas, a contradiction (`R + k ≤ R`, `k ≥ 1`).
//! 4. `L` is proved equal to `Nat.add R k` (`k` the positive Farkas gap) by the
//!    EXISTING linear-equality synthesizer
//!    [`super::arith_linarith_nat_eq::try_prove_nat_equality_direct`] — sound iff
//!    the two canonical linear forms match, which they do precisely when the
//!    certificate is a genuine UNSAT witness. `acc` is transported along that
//!    equality (`Eq.ndrec`) to `acc' : Nat.le (R + k) R`, then handed to the
//!    EXISTING symbolic contradiction closer
//!    [`super::arith_linarith_close::try_close_contradictory_le_generic`], which
//!    derives `False` (shared core `R`, offsets `k > 0`).
//! 5. The `False` proof is sealed under the `byContradiction` lambda.
//!
//! ## Soundness
//!
//! Fail-closed and axiom-free. The Farkas multipliers only *guide* assembly; the
//! assembled term is re-checked by `state.close_goal` (`infer_type` + WHNF +
//! `is_def_eq`) and ultimately by `add_decl`. A miscomputed gap yields either a
//! non-contradictory sum (the symbolic closer returns `None` → fail closed) or a
//! term whose type does not match the goal (`close_goal` rejects → fail closed).
//! A FALSE goal has no UNSAT certificate, so this builder is never invoked for
//! it; even if it were, the linear-form equality gate would reject. Every
//! constant used (`Classical.byContradiction`, `Nat.not_le`, `Iff.mp`,
//! `Nat.add_le_add`, `Nat.le_trans`, `Nat.le.refl`, `Nat.le.step`,
//! `Nat.lt_irrefl`, `Eq.ndrec`, `False.elim`, and the `Nat.add_comm` /
//! `Nat.add_assoc` / `congrArg` the equality synthesizer emits) is a constructive
//! prelude theorem or recursor — zero domain-specific axioms.

use clean_kernel::expr::{BinderInfo, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

use super::arith_linarith_chain::{detect_sort, extract_le_args_full, CmpOp};
use super::arith_linarith_close::try_close_contradictory_le_generic;
use super::arith_linarith_proof::find_hyp_type;
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

    // Active hypotheses with positive multipliers, each a Nat `≤`/`<`/`=`.
    //
    // Primary set: those the certificate flagged with a positive coefficient.
    // Once the implicit `0 ≤ v` non-negativity constraints participate in the
    // certified refutation, the 0/1 coefficient attribution can drop a genuinely
    // contributing hypothesis (the UNSAT witness is credited to the synthetic
    // nonneg + negated-goal rows instead). So when the flagged set is empty —
    // *or* it fails to reconstruct — fall back to ALL parseable hypotheses, each
    // at multiplier 1. This never threatens soundness: an irrelevant hypothesis
    // leaves an uncancellable residual (the gap is then not a positive constant)
    // and the kernel re-check rejects any wrong term.
    let flagged: Vec<(usize, i128)> = certificate
        .coefficients
        .iter()
        .enumerate()
        .filter(|&(i, &c)| c > 0 && i < hypothesis_fvars.len())
        .map(|(i, &c)| (i, c))
        .collect();
    let all_at_one: Vec<(usize, i128)> = (0..hypothesis_fvars.len()).map(|i| (i, 1)).collect();

    // The 0/1 certificate collapses the true Farkas multiplier to 1, so a
    // *scaled*-monotonicity goal like `2*a ≤ 2*b` from `a ≤ b` (multiplier 2) is
    // not reconstructible from the flagged/all-at-one sets alone. Derive an upper
    // multiplier bound from the goal's linear coefficients and enumerate uniform
    // multiplier assignments `1..=bound` (each hypothesis at the same `m`). This
    // covers the `c·x ≤ c·y` family (single dominant multiplier) without an
    // unbounded search. Soundness is unaffected: a wrong multiplier leaves an
    // uncancellable residual (no positive-constant gap) and the kernel re-check
    // rejects any wrong term. The bound is capped to keep the search cheap.
    let mult_bound = goal_multiplier_bound(&goal_le_lhs, &goal_le_rhs);
    let scaled_sets: Vec<Vec<(usize, i128)>> = (2..=mult_bound)
        .map(|m| (0..hypothesis_fvars.len()).map(|i| (i, m)).collect())
        .collect();

    // Fresh by-contradiction hypothesis `hg : ¬G`.
    let hg_fvar = state.fresh_fvar();

    // Build the False proof inside the by-contra context, trying the flagged set
    // first (preserves certificate-supplied multipliers > 1), then all-at-one,
    // then the derived uniform-multiplier assignments (scaled monotonicity).
    let candidate_active: Vec<&[(usize, i128)]> = std::iter::once(flagged.as_slice())
        .chain(std::iter::once(all_at_one.as_slice()))
        .chain(scaled_sets.iter().map(Vec::as_slice))
        .collect();
    let false_proof = candidate_active
        .into_iter()
        .filter(|active| !active.is_empty())
        .find_map(|active| {
            build_false_from_farkas(
                goal,
                &goal_le_lhs,
                &goal_le_rhs,
                active,
                hypothesis_fvars,
                hg_fvar,
            )
        })?;

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

/// Build the `False` proof given the by-contra hypothesis `hg : ¬G`.
///
/// Folds the active hypotheses (each at its certificate multiplier), the negated
/// goal, and — crucially — the implicit Nat non-negativity facts `0 ≤ v` needed
/// to close the residual. Equality hypotheses are tried in both orientations.
fn build_false_from_farkas(
    goal: &Goal,
    goal_le_lhs: &Expr,
    goal_le_rhs: &Expr,
    active: &[(usize, i128)],
    hypothesis_fvars: &[FVarId],
    hg_fvar: FVarId,
) -> Option<Expr> {
    // Each active hypothesis contributes one (≤/<) or two (= : both orientations)
    // candidate `Nat.le` facts. Try every orientation combination; equality-heavy
    // goals are rare, and we bound the search to keep it cheap.
    let mut candidate_sets: Vec<Vec<SortLeAcc>> = Vec::with_capacity(active.len());
    let mut coeffs: Vec<i128> = Vec::with_capacity(active.len());
    for &(idx, coeff) in active {
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
            goal_le_lhs,
            goal_le_rhs,
            &candidate_sets,
            &coeffs,
            hg_fvar,
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
    goal_le_lhs: &Expr,
    goal_le_rhs: &Expr,
    candidate_sets: &[Vec<SortLeAcc>],
    coeffs: &[i128],
    hg_fvar: FVarId,
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

    // Negated-goal positive `Nat.le NG_lhs NG_rhs` (= `succ GR ≤ GL`) from `hg`.
    let neg_goal_acc = from_negated_nat_goal(goal_le_lhs, goal_le_rhs, hg_fvar)?;

    // Fold hyps (if any) with the negated goal. With no parseable hypotheses the
    // refutation is goal+nonneg only (e.g. the goal itself forces a Nat bound).
    let base_acc = match hyp_acc {
        Some(a) => a.combine(neg_goal_acc)?,
        None => neg_goal_acc,
    };
    if base_acc.sort != ArithSort::Nat {
        return None;
    }

    // Compute the residual `base_acc.lhs - base_acc.rhs` and cancel every
    // positive Nat-atom coefficient with the implicit `0 ≤ v` fact. This is the
    // Farkas positive combination that mixes a hypothesis with the implicit
    // bound: `(b - a - 2 ≥ 0 from hyp) + (a ≥ 0 implicit) ⟹ (b - 2 ≥ 0)`.
    let acc = inject_nonneg_to_cancel(goal, base_acc)?;

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
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let closed = try_close_contradictory_le_generic(
        ArithSort::Nat,
        &acc_transported,
        &r_plus_k,
        &acc.rhs,
        &false_ty,
    );
    if closed.is_none() {
        tracing::debug!("farkas_goal: symbolic contradiction closer returned None for (R+k, R)");
    }
    closed
}

/// Build a Nat accumulator from a hypothesis `fvar`, normalizing `<`/`>`/`≥` to
/// the canonical `Nat.le` orientation with correct endpoints.
///
/// - `a ≤ b` → endpoints `(a, b)`, proof `fvar`.
/// - `a < b` → endpoints `(a + 1, b)`; `fvar : Nat.lt a b` is def-eq
///   `Nat.le (Nat.succ a) b` ≡ `Nat.le (a + 1) b`, so the kernel accepts it.
/// - `a ≥ b` → `(b, a)`; `a > b` → `(b + 1, a)`.
///
/// Returns `None` for non-Nat hypotheses (the builder is Nat-only) or unparsable
/// comparison heads.
fn nat_hyp_acc(goal: &Goal, fvar: FVarId) -> Option<SortLeAcc> {
    let h_ty = find_hyp_type(goal, fvar)?;
    let head = h_ty.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let name_s = name.to_string();
    let (alpha, _op, a, b) = extract_le_args_full(&h_ty)?;
    if detect_sort(&alpha)? != ArithSort::Nat {
        return None;
    }
    let one = Expr::nat_lit(1);
    let proof = Expr::fvar(fvar);
    // `extract_le_args_full` reports GE/GT as Le/Lt WITHOUT swapping operands,
    // so reconstruct the `Nat.le` orientation from the surface head. An LT/GT
    // hypothesis `a < b` is `Nat.lt a b`, reducibly `Nat.le (a + 1) b`, so the
    // `fvar` proof kernel-checks against the declared `(a + 1, b)` endpoints.
    let (lhs, rhs) = match name_s.as_str() {
        "LE.le" | "Nat.le" => (a, b),
        "LT.lt" | "Nat.lt" => (nat_add(&a, &one), b),
        "GE.ge" => (b, a),
        "GT.gt" => (nat_add(&b, &one), a),
        _ => return None,
    };
    SortLeAcc::nat_from_parts(lhs, rhs, proof)
}

/// Candidate `Nat.le` orientations a hypothesis can contribute to the Farkas
/// sum. Inequalities give exactly one oriented fact; a Nat **equality**
/// `h : a = b` gives BOTH `a ≤ b` and `b ≤ a` (each provable from `h`), and the
/// residual solver picks whichever orientation cancels the goal/atoms.
///
/// The `Eq` orientations are built by transporting `Nat.le.refl a` along `h`:
/// - `a ≤ b`: `@Eq.ndrec Nat a (fun z => Nat.le a z) (Nat.le.refl a) b h`.
/// - `b ≤ a`: `@Eq.ndrec Nat a (fun z => Nat.le z a) (Nat.le.refl a) b h`.
/// Both use only `Nat.le.refl` and `Eq.ndrec` (constructive prelude); the kernel
/// re-check of the final term is the soundness gate.
fn nat_hyp_acc_candidates(goal: &Goal, fvar: FVarId) -> Vec<SortLeAcc> {
    if let Some(acc) = nat_hyp_acc(goal, fvar) {
        return vec![acc];
    }
    // Equality hypothesis path.
    let Some(h_ty) = find_hyp_type(goal, fvar) else {
        return Vec::new();
    };
    let head = h_ty.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return Vec::new();
    };
    if !name.to_string().contains("Eq") {
        return Vec::new();
    }
    let args = h_ty.get_app_args();
    // `@Eq Nat a b` has args [Nat, a, b].
    if args.len() != 3 || !is_nat_const(args[0]) {
        return Vec::new();
    }
    let a = args[1].clone();
    let b = args[2].clone();
    let h = Expr::fvar(fvar);
    let mut out = Vec::new();
    // a ≤ b
    if let Some(acc) = SortLeAcc::nat_from_parts(
        a.clone(),
        b.clone(),
        eq_to_le_le(&a, &b, &h, EqLeDir::Forward),
    ) {
        out.push(acc);
    }
    // b ≤ a
    if let Some(acc) = SortLeAcc::nat_from_parts(
        b.clone(),
        a.clone(),
        eq_to_le_le(&a, &b, &h, EqLeDir::Backward),
    ) {
        out.push(acc);
    }
    out
}

#[derive(Clone, Copy)]
enum EqLeDir {
    /// `h : a = b` ⟹ `Nat.le a b`.
    Forward,
    /// `h : a = b` ⟹ `Nat.le b a`.
    Backward,
}

/// Build a `Nat.le` proof from a Nat equality `h : a = b` by transporting
/// `Nat.le.refl a` along `h`.
fn eq_to_le_le(a: &Expr, b: &Expr, h: &Expr, dir: EqLeDir) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
    let le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
    // refl : Nat.le a a
    let refl = Expr::app(le_refl, a.clone());
    // motive : fun z => Nat.le a z   (Forward)  or  fun z => Nat.le z a (Backward)
    let motive = match dir {
        EqLeDir::Forward => {
            let body = Expr::apps(nat_le, [a.clone(), Expr::bvar(0)]);
            Expr::lam(BinderInfo::Default, nat_ty.clone(), body)
        }
        EqLeDir::Backward => {
            let body = Expr::apps(nat_le, [Expr::bvar(0), a.clone()]);
            Expr::lam(BinderInfo::Default, nat_ty.clone(), body)
        }
    };
    // @Eq.ndrec.{0,1} Nat a motive refl b h : motive[b]
    let eq_ndrec = Expr::const_(
        Name::from_string("Eq.ndrec"),
        vec![Level::zero(), Level::succ(Level::zero())],
    );
    Expr::apps(
        eq_ndrec,
        [nat_ty, a.clone(), motive, refl, b.clone(), h.clone()],
    )
}

fn is_nat_const(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat")
}

/// Scale a Nat accumulator by `coeff ≥ 1` via repeated self-addition
/// (`Nat.add_le_add`). `coeff == 1` returns it unchanged.
fn scale_nat_acc(base: SortLeAcc, coeff: i128) -> Option<SortLeAcc> {
    if coeff < 1 {
        return None;
    }
    if coeff == 1 {
        return Some(base);
    }
    // Rebuild `base` `coeff` times and fold; `SortLeAcc` is not `Clone`, so
    // capture its parts and reconstruct each summand.
    let SortLeAcc {
        lhs, rhs, proof, ..
    } = base;
    let mut acc = SortLeAcc::nat_from_parts(lhs.clone(), rhs.clone(), proof.clone())?;
    for _ in 1..coeff {
        let next = SortLeAcc::nat_from_parts(lhs.clone(), rhs.clone(), proof.clone())?;
        acc = acc.combine(next)?;
    }
    Some(acc)
}

/// Fold the implicit Nat non-negativity facts `0 ≤ v` into `acc` so every atom
/// with a *positive* residual coefficient is cancelled, leaving a pure constant
/// gap.
///
/// `acc : Nat.le L R` summarizes the hyp+neg_goal combination. Its residual is
/// `d = linearForm(L) − linearForm(R)`. The genuine UNSAT witness has, for every
/// atom `v`, a residual coefficient `d_v ≥ 0` (the negative direction can never
/// be cancelled by a `0 ≤ v` fact, which only *adds* `v` to the right side):
/// folding `d_v` copies of `0 ≤ v` adds `d_v·v` to `R`, zeroing the atom. If any
/// atom has `d_v < 0`, this is NOT a `hyp + nonneg` refutation — return `None`
/// and fail closed (the caller falls through).
///
/// Each `0 ≤ v` is `Nat.zero_le v : Nat.le 0 v`. The fold uses the same
/// `SortLeAcc::combine` (`Nat.add_le_add`); the assembled term is kernel-checked
/// by `close_goal`, so a wrong cancellation cannot be accepted.
///
/// Soundness: `0 ≤ v` holds for every Nat `v`. We only ever add it on the LHS as
/// a `0` and on the RHS as `v` (never subtract), so the combination stays a valid
/// `≤` and the only goals it can close are genuinely true ones.
fn inject_nonneg_to_cancel(goal: &Goal, acc: SortLeAcc) -> Option<SortLeAcc> {
    let diff = linear_diff(&acc.lhs, &acc.rhs)?;

    // Nat-typed atoms eligible for a `0 ≤ v` fact, keyed by atom Expr.
    let mut nat_atoms = std::collections::HashSet::new();
    for d in &goal.local_ctx {
        if matches!(d.ty.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat") {
            nat_atoms.insert(Expr::fvar(d.fvar));
        }
    }

    let mut result = acc;
    for (atom, &coeff) in &diff.coeffs {
        if coeff == 0 {
            continue;
        }
        // A leftover atom must be a Nat variable with a POSITIVE residual to be
        // cancellable by `0 ≤ v`. Anything else means this orientation/combo is
        // not a `hyp + nonneg` witness.
        if coeff < 0 || !nat_atoms.contains(atom) {
            return None;
        }
        let count = u64::try_from(coeff).ok()?;
        // Fold `count` copies of `Nat.zero_le atom : Nat.le 0 atom`.
        let zero = Expr::nat_lit(0);
        for _ in 0..count {
            let zero_le = Expr::const_(Name::from_string("Nat.zero_le"), vec![]);
            let proof = Expr::app(zero_le, atom.clone());
            let nonneg = SortLeAcc::nat_from_parts(zero.clone(), atom.clone(), proof)?;
            result = result.combine(nonneg)?;
        }
    }
    Some(result)
}

/// Linear-form difference `lhs - rhs` (atom coeffs and constant) using the
/// shared Nat linear-form parser.
fn linear_diff(lhs: &Expr, rhs: &Expr) -> Option<NatDiff> {
    let lf = super::arith_linarith_nat_eq::parse_nat_linear_form(lhs)?;
    let rf = super::arith_linarith_nat_eq::parse_nat_linear_form(rhs)?;
    let mut coeffs = std::collections::HashMap::new();
    for (atom, &c) in &lf.coeffs {
        *coeffs.entry(atom.clone()).or_insert(0_i128) += i128::from(c);
    }
    for (atom, &c) in &rf.coeffs {
        *coeffs.entry(atom.clone()).or_insert(0_i128) -= i128::from(c);
    }
    coeffs.retain(|_, c| *c != 0);
    Some(NatDiff {
        coeffs,
        constant: i128::from(lf.constant) - i128::from(rf.constant),
    })
}

struct NatDiff {
    coeffs: std::collections::HashMap<Expr, i128>,
    constant: i128,
}

/// Build the negated-goal accumulator `Nat.le (succ GR) GL` from `hg : ¬G`.
///
/// `Nat.not_le GL GR : Iff (Nat.le GL GR → False) (Nat.lt GR GL)` (tc form), so
/// `Iff.mp (Nat.not_le GL GR) hg : Nat.lt GR GL`, which is the reducible def
/// `Nat.le (Nat.succ GR) GL`. We declare the accumulator endpoints as
/// `(Nat.succ GR, GL)`; the `Nat.lt` proof is def-eq to `Nat.le (succ GR) GL`,
/// so the downstream `Nat.add_le_add` application kernel-checks.
fn from_negated_nat_goal(
    goal_le_lhs: &Expr,
    goal_le_rhs: &Expr,
    hg_fvar: FVarId,
) -> Option<SortLeAcc> {
    use super::tc_app::{nat_le_tc, nat_lt_tc};

    let not_le = Expr::const_(Name::from_string("Nat.not_le"), vec![]);
    // Nat.not_le GL GR : Iff (@LE.le Nat _ GL GR → False) (@LT.lt Nat _ GR GL)
    let iff = Expr::apps(not_le, [goal_le_lhs.clone(), goal_le_rhs.clone()]);

    // The two `Iff` Props (must be supplied explicitly — the kernel does NOT
    // auto-insert implicits in raw term application):
    //   a := (@LE.le Nat _ GL GR) → False   (the negated goal, = hg's type)
    //   b := @LT.lt Nat _ GR GL             (the positive consequence)
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let prop_a = Expr::pi(
        BinderInfo::Default,
        nat_le_tc(goal_le_lhs.clone(), goal_le_rhs.clone()),
        false_ty,
    );
    let prop_b = nat_lt_tc(goal_le_rhs.clone(), goal_le_lhs.clone());

    // @Iff.mp a b iff hg : b   (b ≡ Nat.le (succ GR) GL).
    let iff_mp = Expr::const_(Name::from_string("Iff.mp"), vec![]);
    let lt_proof = Expr::apps(iff_mp, [prop_a, prop_b, iff, Expr::fvar(hg_fvar)]);

    // Accumulator LHS endpoint: the collapsed literal `GR+1` when GR is a
    // concrete literal (so the constant is a single literal leaf), and the
    // additive form `Nat.add GR 1` when GR is symbolic. Both are def-eq to
    // `Nat.succ GR` (`Nat.add GR 1` reduces to `Nat.succ (GR + 0)` ≡ `Nat.succ
    // GR`), so the `Nat.lt`-typed `lt_proof` (= `Nat.le (succ GR) GL`)
    // kernel-checks against `Nat.le <endpoint> GL`. Using the `Nat.add` form
    // rather than a raw `Nat.succ` keeps the endpoint inside the linear-form
    // fragment the downstream equality synthesizer
    // (`try_prove_nat_equality_direct`) can canonicalize — a bare `Nat.succ`
    // atom would otherwise defeat it. The kernel re-check is the soundness gate.
    let neg_lhs = match super::nat_expr_eval::eval_nat_expr(goal_le_rhs) {
        Some(v) => Expr::nat_lit(v.checked_add(1)?),
        None => nat_add(goal_le_rhs, &Expr::nat_lit(1)),
    };

    SortLeAcc::nat_from_parts(neg_lhs, goal_le_lhs.clone(), lt_proof)
}

/// Normalize a Nat comparison goal `target` to `(GL, GR)` of `Nat.le GL GR`.
///
/// Mirrors the normalization in `arith_linarith_nat_direct::normalize_nat_comparison`:
/// - `a ≤ b` → `(a, b)`
/// - `a < b` → `(a + 1, b)`
/// - `a ≥ b` → `(b, a)`     (operands swapped)
/// - `a > b` → `(b + 1, a)` (operands swapped)
///
/// `extract_le_args_full` collapses GE/GT to Le/Lt *without* swapping operands,
/// so the swap is done here from the raw application args keyed on the surface
/// head. The orientation is the soundness-relevant part: the negated-goal proof
/// is built from `(GL, GR)`, and the whole term is kernel-rechecked, so a wrong
/// orientation fails closed rather than proving a false goal.
///
/// Returns `None` for non-Nat or non-comparison goals.
fn normalize_nat_goal_to_le(target: &Expr) -> Option<(Expr, Expr)> {
    let head = target.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let name_s = name.to_string();
    let args = target.get_app_args();

    // Typeclass forms `@Rel.{u} Nat inst a b` carry the sort in `args[0]`;
    // direct forms `Nat.{le,lt} a b` are implicitly Nat.
    let (a, b) = if args.len() == 4 {
        if !is_nat_const(args[0]) {
            return None;
        }
        match name_s.as_str() {
            "LE.le" | "LT.lt" | "GE.ge" | "GT.gt" => (args[2].clone(), args[3].clone()),
            _ => return None,
        }
    } else if args.len() == 2 {
        match name_s.as_str() {
            "Nat.le" | "Nat.lt" => (args[0].clone(), args[1].clone()),
            _ => return None,
        }
    } else {
        return None;
    };

    let one = Expr::nat_lit(1);
    match name_s.as_str() {
        "LE.le" | "Nat.le" => Some((a, b)),
        "LT.lt" | "Nat.lt" => Some((nat_add(&a, &one), b)),
        "GE.ge" => Some((b, a)),
        "GT.gt" => Some((nat_add(&b, &one), a)),
        _ => None,
    }
}

/// Upper bound on the uniform hypothesis multiplier to try for a scaled-
/// monotonicity goal, derived from the largest atom coefficient appearing in the
/// goal's (normalized) `Nat.le` endpoints. For `2*a ≤ 2*b` this is `2`; for a
/// coefficient-free goal it is `1` (no scaled set generated). Capped at a small
/// constant so the search stays cheap; a genuine higher-coefficient goal that
/// exceeds the cap simply fails closed (no wrong term is ever emitted).
fn goal_multiplier_bound(lhs: &Expr, rhs: &Expr) -> i128 {
    const CAP: i128 = 8;
    let mut bound: i128 = 1;
    for side in [lhs, rhs] {
        if let Some(form) = super::arith_linarith_nat_eq::parse_nat_linear_form(side) {
            for &c in form.coeffs.values() {
                let mag = i128::from(c).abs();
                if mag > bound {
                    bound = mag;
                }
            }
        }
    }
    bound.min(CAP)
}

/// Compute the Farkas gap `k = linearForm(lhs) - linearForm(rhs)` when it is a
/// pure non-negative constant (all atom coefficients cancel). Returns `None`
/// when the difference is not a constant (not a genuine contradiction shape).
fn nat_farkas_gap(lhs: &Expr, rhs: &Expr) -> Option<u64> {
    let lf = super::arith_linarith_nat_eq::parse_nat_linear_form(lhs)?;
    let rf = super::arith_linarith_nat_eq::parse_nat_linear_form(rhs)?;
    // Every atom coefficient must match (cancel in the difference).
    for (atom, &lc) in &lf.coeffs {
        if rf.coeffs.get(atom).copied().unwrap_or(0) != lc {
            return None;
        }
    }
    for (atom, &rc) in &rf.coeffs {
        if lf.coeffs.get(atom).copied().unwrap_or(0) != rc {
            return None;
        }
    }
    let diff = lf.constant.checked_sub(rf.constant)?;
    if diff < 1 {
        return None;
    }
    u64::try_from(diff).ok()
}

/// `@Eq.ndrec Nat L (fun z => Nat.le z R) proof newL eq : Nat.le newL R`
/// where `proof : Nat.le L R` and `eq : L = newL`.
fn transport_le_lhs(proof: &Expr, l: &Expr, r: &Expr, new_l: &Expr, eq: &Expr) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
    // motive : fun (z : Nat) => Nat.le z R
    let motive = {
        let body = Expr::apps(nat_le, [Expr::bvar(0), r.clone()]);
        Expr::lam(BinderInfo::Default, nat_ty.clone(), body)
    };
    // @Eq.ndrec.{0,1} Nat L motive proof newL eq
    let eq_ndrec = Expr::const_(
        Name::from_string("Eq.ndrec"),
        vec![Level::zero(), Level::succ(Level::zero())],
    );
    Expr::apps(
        eq_ndrec,
        [
            nat_ty,
            l.clone(),
            motive,
            proof.clone(),
            new_l.clone(),
            eq.clone(),
        ],
    )
}

/// `Nat.add a b`.
fn nat_add(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [a.clone(), b.clone()],
    )
}

/// `@Eq Nat l r`.
fn mk_nat_eq(l: &Expr, r: &Expr) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat_ty, l.clone(), r.clone()],
    )
}
