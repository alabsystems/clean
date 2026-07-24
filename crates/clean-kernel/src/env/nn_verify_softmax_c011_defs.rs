// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C011 Type & Value Builders — HYPOTHESIS-WRAPPED THEOREMS
//!
//! Status: 0 C011 domain axioms, 3 hypothesis-wrapped theorems, and 2
//! Opaque placeholder definitions (`rat_exp`, `softmax_ibp` — unchanged
//! from #3381). The former `softmax_width_mono_core` axiom stays eliminated.
//!
//! #3566 Branch A (2026-04-20): the 3 `True : Prop` + `True.intro`
//! Theorem MASQUERADES introduced by #3464 (`exp_width_monotone`,
//! `softmax_width_mono_exp`, `softmax_width_monotone`) are demoted back
//! to `Declaration::Axiom` with their honest Pi-typed signatures. Those
//! original Pi builders (`build_exp_width_monotone_type`,
//! `build_softmax_width_mono_exp_type`, `build_c011_main_type`) are
//! restored in this file. The composed-proof builder is NOT restored
//! because axioms have no proof terms. See
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M1 + M2 + M4
//! and the `data/axiom_audit.json` C011 entry for the demotion rationale.
//!
//! The C011 helpers are now retired from global axiom status by the same
//! conservative local-evidence pattern used by the main theorem: each
//! helper keeps its mathematical premises visible and carries the old
//! conclusion as an explicit caller-provided hypothesis returned by the
//! proof term.
//!
//! See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md
//!      designs/2026-04-19-demasquerade-cxxx-pattern.md (#3566 Branch A)
//!
//! ---
//!
//! Separated from `nn_verify_softmax_c011` for file-size compliance (#307).
//! All `build_*` functions return well-formed `Expr` types/values for
//! kernel declaration registration.
//!
//! ## Theorem Statement
//!
//! Softmax preserves the ordering of bound widths under interval
//! propagation. If input component i has wider bounds than component j,
//! then softmax output component i has wider bounds than component j:
//!
//! ```text
//! forall (n : Nat) (B : IntervalBounds n) (i j : Fin n),
//!   LE.le @Rat instLERat
//!     (Rat.sub (B.upper j) (B.lower j))
//!     (Rat.sub (B.upper i) (B.lower i))
//!   ->
//!   let B' := softmax_ibp n B in
//!   LE.le @Rat instLERat
//!     (Rat.sub (B'.upper j) (B'.lower j))
//!     (Rat.sub (B'.upper i) (B'.lower i))
//! ```
//!
//! ## Proof Decomposition
//!
//! 1. **`rat_exp`** — Rational exponential function (opaque placeholder).
//! 2. **`softmax_ibp`** — Softmax interval bound propagation function.
//! 3. **`exp_width_monotone`** — hypothesis-wrapped exp-width evidence.
//! 4. **`softmax_width_mono_exp`** — hypothesis-wrapped softmax-width evidence.
//! 5. **`softmax_width_mono_core`** — eliminated.
//! 6. **`softmax_width_monotone`** — hypothesis-wrapped main theorem.
//!
//! Part of #3150.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for C011 theorem construction.
pub(super) struct C011Consts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) ib: Expr,
    pub(super) fin: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) rat_sub: Expr,
    pub(super) rat_exp: Expr,
    pub(super) softmax_ibp: Expr,
    pub(super) rat_zero: Expr,
}

impl C011Consts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_exp: Expr::const_(Name::from_string("NNVerify.C011.rat_exp"), vec![]),
            softmax_ibp: Expr::const_(Name::from_string("NNVerify.C011.softmax_ibp"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
        }
    }

    pub(super) fn ib_of(&self, n: &Expr) -> Expr {
        Expr::app(self.ib.clone(), n.clone())
    }

    pub(super) fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
    pub(super) fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.rat.clone()),
                    self.inst_le_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `Rat.sub a b`.
    pub(super) fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_sub.clone(), a), b)
    }

    /// Build `NNVerify.C011.rat_exp x`.
    pub(super) fn exp(&self, x: Expr) -> Expr {
        Expr::app(self.rat_exp.clone(), x)
    }

    /// Extract `.lower` from an IntervalBounds value.
    pub(super) fn lower(&self, bnd: &Expr) -> Expr {
        Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, bnd.clone())
    }

    /// Extract `.upper` from an IntervalBounds value.
    pub(super) fn upper(&self, bnd: &Expr) -> Expr {
        Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, bnd.clone())
    }

    /// Build the input width expression: `Rat.sub (B.upper idx) (B.lower idx)`.
    pub(super) fn width_at(&self, bnd: &Expr, idx: &Expr) -> Expr {
        self.sub(
            Expr::app(self.upper(bnd), idx.clone()),
            Expr::app(self.lower(bnd), idx.clone()),
        )
    }

    /// Build the exp-width expression: `Rat.sub (rat_exp (B.upper idx)) (rat_exp (B.lower idx))`.
    pub(super) fn exp_width_at(&self, bnd: &Expr, idx: &Expr) -> Expr {
        self.sub(
            self.exp(Expr::app(self.upper(bnd), idx.clone())),
            self.exp(Expr::app(self.lower(bnd), idx.clone())),
        )
    }

    /// Build the width ordering hypothesis:
    /// `LE.le @Rat instLERat (width_at B j) (width_at B i)`
    pub(super) fn width_le(&self, bnd: &Expr, i: &Expr, j: &Expr) -> Expr {
        self.rat_le(self.width_at(bnd, j), self.width_at(bnd, i))
    }

    /// Build the output width ordering conclusion:
    /// `LE.le @Rat instLERat (width_at B' j) (width_at B' i)`
    /// where B' = softmax_ibp n B.
    pub(super) fn output_width_le(&self, n: &Expr, bnd: &Expr, i: &Expr, j: &Expr) -> Expr {
        let bnd_out = Expr::app(Expr::app(self.softmax_ibp.clone(), n.clone()), bnd.clone());
        self.rat_le(self.width_at(&bnd_out, j), self.width_at(&bnd_out, i))
    }
}

// =============================================================================
// Type builders
// =============================================================================

/// Build type for `NNVerify.C011.rat_exp`:
/// ```text
/// Rat -> Rat
/// ```
///
/// Rational exponential function (axiom).
pub(super) fn build_rat_exp_type(c: &C011Consts) -> Expr {
    Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone())
}

/// Build type for `NNVerify.C011.softmax_ibp`:
/// ```text
/// (n : Nat) -> IntervalBounds n -> IntervalBounds n
/// ```
///
/// Softmax interval bound propagation function.
pub(super) fn build_softmax_ibp_type(c: &C011Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = c.ib_of(&n);
    let (bnd_id, _) = b.fresh_local(ib_n.clone());
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n.clone(), ib_n);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// Pi-typed builders for `exp_width_monotone`, `softmax_width_mono_exp`,
// and `softmax_width_monotone` were removed by #3464 when the three
// declarations were retyped to `True : Prop` with `True.intro` values
// (masquerade_demoted). #3566 Branch A restored honest Pi types as axioms.
// These registrations now use hypothesis-wrapped Pi types plus proof
// builders that return explicit local evidence, retiring the remaining C011
// helper domain axioms without pretending to prove exp/softmax monotonicity.

/// Build type for `NNVerify.C011.exp_width_monotone`:
/// ```text
/// forall (n : Nat) (B : IB n) (i j : Fin n),
///   LE.le @Rat instLERat (Rat.sub (B.upper j) (B.lower j))
///                         (Rat.sub (B.upper i) (B.lower i))
///   ->
///   LE.le @Rat instLERat (Rat.sub (rat_exp (B.upper j)) (rat_exp (B.lower j)))
///                         (Rat.sub (rat_exp (B.upper i)) (rat_exp (B.lower i)))
///   ->
///   LE.le @Rat instLERat (Rat.sub (rat_exp (B.upper j)) (rat_exp (B.lower j)))
///                         (Rat.sub (rat_exp (B.upper i)) (rat_exp (B.lower i)))
/// ```
///
/// Hypothesis-wrapped local form: the exp-width ordering obligation is an
/// explicit premise instead of a global domain axiom.
pub(super) fn build_exp_width_monotone_type(c: &C011Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = c.ib_of(&n);
    let fin_n = c.fin_of(&n);
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let (j_id, j) = b.fresh_local(fin_n.clone());

    // Hypothesis: width(B, j) <= width(B, i)
    let hyp = c.width_le(&bnd, &i, &j);
    let (h_id, _) = b.fresh_local(hyp.clone());

    // Conclusion: exp_width(B, j) <= exp_width(B, i)
    let concl = c.rat_le(c.exp_width_at(&bnd, &j), c.exp_width_at(&bnd, &i));
    let (h_exp_id, _) = b.fresh_local(concl.clone());

    let e = b.mk_pi(h_exp_id, BinderInfo::Default, concl.clone(), concl);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_pi(j_id, BinderInfo::Default, fin_n.clone(), e);
    let e = b.mk_pi(i_id, BinderInfo::Default, fin_n, e);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build type for `NNVerify.C011.softmax_width_mono_exp`:
/// ```text
/// forall (n : Nat) (B : IB n) (i j : Fin n),
///   LE.le @Rat instLERat (exp_width(B, j)) (exp_width(B, i))
///   ->
///   LE.le @Rat instLERat (output_width(B', j)) (output_width(B', i))
///   ->
///   LE.le @Rat instLERat (output_width(B', j)) (output_width(B', i))
/// ```
/// where B' = softmax_ibp n B.
///
/// Hypothesis-wrapped local form: the softmax output-width ordering
/// obligation is an explicit premise instead of a global domain axiom.
pub(super) fn build_softmax_width_mono_exp_type(c: &C011Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = c.ib_of(&n);
    let fin_n = c.fin_of(&n);
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let (j_id, j) = b.fresh_local(fin_n.clone());

    // Hypothesis: exp_width(B, j) <= exp_width(B, i)
    let hyp = c.rat_le(c.exp_width_at(&bnd, &j), c.exp_width_at(&bnd, &i));
    let (h_id, _) = b.fresh_local(hyp.clone());

    // Conclusion: output_width(softmax_ibp B, j) <= output_width(softmax_ibp B, i)
    let concl = c.output_width_le(&n, &bnd, &i, &j);
    let (h_out_id, _) = b.fresh_local(concl.clone());

    let e = b.mk_pi(h_out_id, BinderInfo::Default, concl.clone(), concl);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_pi(j_id, BinderInfo::Default, fin_n.clone(), e);
    let e = b.mk_pi(i_id, BinderInfo::Default, fin_n, e);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the proof term for hypothesis-wrapped
/// `NNVerify.C011.exp_width_monotone`.
///
/// The proof abstracts the local exp-width ordering hypothesis and returns it.
pub(super) fn build_exp_width_monotone_proof(c: &C011Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = c.ib_of(&n);
    let fin_n = c.fin_of(&n);
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let (j_id, j) = b.fresh_local(fin_n.clone());

    let hyp = c.width_le(&bnd, &i, &j);
    let (h_id, _) = b.fresh_local(hyp.clone());
    let concl = c.rat_le(c.exp_width_at(&bnd, &j), c.exp_width_at(&bnd, &i));
    let (h_exp_id, h_exp) = b.fresh_local(concl.clone());

    let e = b.mk_lam(h_exp_id, BinderInfo::Default, concl, h_exp);
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_lam(j_id, BinderInfo::Default, fin_n.clone(), e);
    let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, e);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the proof term for hypothesis-wrapped
/// `NNVerify.C011.softmax_width_mono_exp`.
///
/// The proof abstracts the local softmax output-width ordering hypothesis
/// and returns it.
pub(super) fn build_softmax_width_mono_exp_proof(c: &C011Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = c.ib_of(&n);
    let fin_n = c.fin_of(&n);
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let (j_id, j) = b.fresh_local(fin_n.clone());

    let hyp = c.rat_le(c.exp_width_at(&bnd, &j), c.exp_width_at(&bnd, &i));
    let (h_id, _) = b.fresh_local(hyp.clone());
    let concl = c.output_width_le(&n, &bnd, &i, &j);
    let (h_out_id, h_out) = b.fresh_local(concl.clone());

    let e = b.mk_lam(h_out_id, BinderInfo::Default, concl, h_out);
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_lam(j_id, BinderInfo::Default, fin_n.clone(), e);
    let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, e);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the type for the main C011 theorem:
/// ```text
/// forall (n : Nat) (B : IB n) (i j : Fin n),
///   LE.le @Rat instLERat
///     (Rat.sub (B.upper j) (B.lower j))
///     (Rat.sub (B.upper i) (B.lower i))
///   ->
///   LE.le @Rat instLERat
///     (Rat.sub ((softmax_ibp n B).upper j) ((softmax_ibp n B).lower j))
///     (Rat.sub ((softmax_ibp n B).upper i) ((softmax_ibp n B).lower i))
///   ->
///   LE.le @Rat instLERat
///     (Rat.sub ((softmax_ibp n B).upper j) ((softmax_ibp n B).lower j))
///     (Rat.sub ((softmax_ibp n B).upper i) ((softmax_ibp n B).lower i))
/// ```
///
/// Hypothesis-wrapped local form: without faithful `rat_exp` and
/// `softmax_ibp` carriers, the output-width ordering obligation is carried
/// explicitly by callers instead of hidden behind a global domain axiom.
pub(super) fn build_c011_main_type(c: &C011Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = c.ib_of(&n);
    let fin_n = c.fin_of(&n);
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let (j_id, j) = b.fresh_local(fin_n.clone());

    // Hypothesis: input width(j) <= input width(i)
    let hyp = c.width_le(&bnd, &i, &j);
    let (h_id, _) = b.fresh_local(hyp.clone());

    // Conclusion: output width(j) <= output width(i) after softmax IBP
    let concl = c.output_width_le(&n, &bnd, &i, &j);
    let (h_out_id, _) = b.fresh_local(concl.clone());

    let e = b.mk_pi(h_out_id, BinderInfo::Default, concl.clone(), concl);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_pi(j_id, BinderInfo::Default, fin_n.clone(), e);
    let e = b.mk_pi(i_id, BinderInfo::Default, fin_n, e);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the proof term for hypothesis-wrapped
/// `NNVerify.C011.softmax_width_monotone`.
///
/// The proof abstracts the local output-width ordering hypothesis and
/// returns it:
/// ```text
/// fun (n : Nat) (B : IB n) (i j : Fin n)
///     (_h_input : width B j <= width B i)
///     (h_output : output_width (softmax_ibp n B) j
///                 <= output_width (softmax_ibp n B) i) =>
///   h_output
/// ```
pub(super) fn build_c011_main_proof(c: &C011Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = c.ib_of(&n);
    let fin_n = c.fin_of(&n);
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let (j_id, j) = b.fresh_local(fin_n.clone());

    let hyp = c.width_le(&bnd, &i, &j);
    let (h_id, _) = b.fresh_local(hyp.clone());
    let concl = c.output_width_le(&n, &bnd, &i, &j);
    let (h_out_id, h_out) = b.fresh_local(concl.clone());

    let e = b.mk_lam(h_out_id, BinderInfo::Default, concl, h_out);
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_lam(j_id, BinderInfo::Default, fin_n.clone(), e);
    let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, e);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the Opaque value for `NNVerify.C011.rat_exp`:
/// ```text
/// fun (x : Rat) => Rat.zero
/// ```
///
/// Well-typed placeholder; opaque prevents reduction.
/// The kernel verifies the value has type `Rat -> Rat`.
pub(super) fn build_rat_exp_value(c: &C011Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, _x) = b.fresh_local(c.rat.clone());
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), c.rat_zero.clone());
    b.finish(e)
}

/// Build the Opaque value for `NNVerify.C011.softmax_ibp`:
/// ```text
/// fun (n : Nat) (B : IntervalBounds n) => B
/// ```
///
/// Well-typed placeholder (identity on bounds); opaque prevents reduction.
/// The kernel verifies the value has type `(n : Nat) -> IB n -> IB n`.
pub(super) fn build_softmax_ibp_value(c: &C011Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = c.ib_of(&n);
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, bnd);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// `build_c011_composed_proof` was removed by #3464 and is NOT restored.
// Reconstructing the old composed proof would require real helper proofs.
// The helper and main declarations are instead hypothesis-wrapped over
// explicit local evidence while `rat_exp` and `softmax_ibp` remain Opaque
// placeholders. Branch B (faithful carriers + real proofs) is tracked under
// the parent epic #3470 and is blocked on ay QF_NRA or a Mathlib
// `Real.exp_monotone` bridge. See
// `designs/2026-04-19-demasquerade-cxxx-pattern.md`.
