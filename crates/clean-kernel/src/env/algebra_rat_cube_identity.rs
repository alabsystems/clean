// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — pure `Rat` CUBE lemmas (cube-root layer rungs 1 + 2).
//!
//! Mirrors `boolean_analysis_ring_identities` (`Rat.add_sq`) and the B1d
//! square-monotonicity toolkit (`Rat.le_of_sq_le_sq`), one cubic degree up. All
//! three lemmas are pure `Rat`-level facts the cube squeeze and the cube
//! identity consume; none touches `NNReal`.
//!
//! - **Rung 1** `Rat.add_cube : ∀ a b,
//!     ((a+b)·(a+b))·(a+b)
//!       = ((a·a)·a)
//!       + ( (1+1+1)·((a·a)·b)
//!         + ( (1+1+1)·((a·b)·b)
//!           + ((b·b)·b) ) )`.
//!   The cube expansion `(a+b)³ = a³ + 3a²b + 3ab² + b³`, in the `((·)·)`
//!   left-nested cube form that matches `CbrtSqueezeConsts::cube`. Built from
//!   `Rat.add_sq` (the `(a+b)²` expansion) + `left_distrib`/`right_distrib` +
//!   `mul_assoc`/`mul_comm`/`add_assoc` + `one_mul`. The `3·t` coefficients are
//!   `(1+1+1)·t`; the cross terms are grouped so the cube-squeeze error bound
//!   (`a≤1`, `b=iv≤1`) collapses each of the three trailing summands to `≤ iv`.
//!
//! - **Rung 2 helpers**
//!   - `Rat.cube_lt_cube_of_lt_of_nonneg : ∀ a b, 0≤b → b<a →
//!       ((b·b)·b) < ((a·a)·a)` (the contrapositive cube-monotone step; two
//!     chained `mul_le`/`mul_lt`).
//!   - `Rat.le_of_cube_le_cube : ∀ a b, 0≤a → 0≤b →
//!       ((a·a)·a) ≤ ((b·b)·b) → a ≤ b` (the `Classical.em` + `le_total`
//!     contradiction skeleton, identical to `Rat.le_of_sq_le_sq`).
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure for every lemma (`Classical.em`'s closure ⊆ FOUNDATIONAL_AXIOMS, so
//! `axiom_deps` filters it out). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the pure cube lemmas.
pub(crate) struct CubeConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_left_distrib: Expr,
    rat_right_distrib: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    rat_add_assoc: Expr,
    rat_add_comm: Expr,
    rat_one_mul: Expr,
    rat_add_sq: Expr,
    // order bricks
    rat_mul_le_right: Expr,
    rat_mul_le_left: Expr,
    rat_mul_lt_pos_left: Expr,
    rat_mul_pos: Expr,
    rat_mul_nonneg: Expr,
    rat_sq_lt_sq: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_lt_of_lt_of_le: Expr,
    rat_lt_iff_le_not_le: Expr,
    rat_le_total: Expr,
    // Eq toolkit (Rat is Sort 1)
    eq1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    eq_trans1: Expr,
    congr_arg11: Expr,
    // logic
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    not_c: Expr,
    iff_mp: Expr,
    iff_mpr: Expr,
    classical_em: Expr,
    or_rec: Expr,
    false_elim0: Expr,
}

impl CubeConsts {
    pub(crate) fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_left_distrib: k("Rat.left_distrib"),
            rat_right_distrib: k("Rat.right_distrib"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_add_comm: k("Rat.add_comm"),
            rat_one_mul: k("Rat.one_mul"),
            rat_add_sq: k("Rat.add_sq"),
            rat_mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            rat_mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            rat_mul_lt_pos_left: k("Rat.mul_lt_mul_of_pos_left"),
            rat_mul_pos: k("Rat.mul_pos"),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            rat_sq_lt_sq: k("Rat.sq_lt_sq_of_lt_of_nonneg"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_lt_of_lt_of_le: k("Rat.lt_of_lt_of_le"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_le_total: k("Rat.le_total"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg11: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            iff_mpr: k("Iff.mpr"),
            classical_em: k("Classical.em"),
            or_rec: k("Or.rec"),
            false_elim0: Expr::const_(Name::from_string("False.elim"), vec![l0]),
        }
    }

    // ── small constructors ──
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    /// `(a·a)·a`.
    fn cube(&self, a: Expr) -> Expr {
        let sq = self.mul(a.clone(), a.clone());
        self.mul(sq, a)
    }
    /// `1+1+1` as `(1+1)+1`.
    fn three(&self) -> Expr {
        self.add(
            self.add(self.rat_one.clone(), self.rat_one.clone()),
            self.rat_one.clone(),
        )
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, c, h1, h2])
    }
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg11.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    fn mul_assoc(&self, a: Expr, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, c])
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    fn add_assoc(&self, a: Expr, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, c])
    }
    /// `Rat.add_comm a b : a+b = b+a`. (`parent` unused; kept for call symmetry.)
    fn mul_comm_add(&self, _parent: &EnvDeclBuilder, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_add_comm.clone(), [a.clone(), b.clone()])
    }
    fn left_distrib(&self, a: Expr, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.rat_left_distrib.clone(), [a, b, c])
    }
    fn right_distrib(&self, a: Expr, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.rat_right_distrib.clone(), [a, b, c])
    }
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.rat_one_mul.clone(), a)
    }
    /// `Rat.add_sq a b : (a+b)·(a+b) = (a·a + (1+1)·(a·b)) + b·b`.
    fn add_sq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add_sq.clone(), [a, b])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (b≤c)(0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, c: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_right.clone(), [a, b, c, h, h0])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (b≤c)(0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, c: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_left.clone(), [a, b, c, h, h0])
    }
    /// `Rat.mul_lt_mul_of_pos_left a b c (b<c)(0<a) : a·b < a·c`.
    fn mul_lt_left(&self, a: Expr, b: Expr, c: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_lt_pos_left.clone(), [a, b, c, h, h0])
    }
    /// `Rat.mul_pos a b (0<a)(0<b) : 0 < a·b`.
    fn mul_pos(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_pos.clone(), [a, b, ha, hb])
    }
    /// `Rat.mul_nonneg a b (0≤a)(0≤b) : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `Rat.sq_lt_sq_of_lt_of_nonneg a b (0≤b)(b<a) : b·b < a·a`.
    fn sq_lt_sq(&self, a: Expr, b: Expr, hb: Expr, hlt: Expr) -> Expr {
        Expr::apps(self.rat_sq_lt_sq.clone(), [a, b, hb, hlt])
    }
    /// `a ≤ b` from `a < b`, via `lt_iff_le_not_le` + `And.left`.
    fn le_of_lt_generic(&self, a: Expr, b: Expr, hlt: Expr) -> Expr {
        let le_ab = self.le(a.clone(), b.clone());
        let not_le = self.not_c(self.le(b.clone(), a.clone()));
        let and_ty = self.and_ty(le_ab.clone(), not_le.clone());
        let lt_ab = self.lt(a.clone(), b.clone());
        let iff = self.lt_iff(a, b);
        let mp = self.iff_mp(lt_ab, and_ty, iff, hlt);
        self.and_left(le_ab, not_le, mp)
    }
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, c, h1, h2])
    }
    fn lt_of_lt_of_le(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_lt_of_le.clone(), [a, b, c, h1, h2])
    }
    fn and_ty(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [p, q, hp, hq])
    }
    fn and_left(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_left.clone(), [p, q, h])
    }
    fn and_right(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_right.clone(), [p, q, h])
    }
    fn lt_iff(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b])
    }
    fn iff_mp(&self, lhs: Expr, rhs: Expr, hiff: Expr, h: Expr) -> Expr {
        Expr::apps(self.iff_mp.clone(), [lhs, rhs, hiff, h])
    }
    fn iff_mpr(&self, lhs: Expr, rhs: Expr, hiff: Expr, h: Expr) -> Expr {
        Expr::apps(self.iff_mpr.clone(), [lhs, rhs, hiff, h])
    }
    /// `Not P` as a `Pi P False` (matches `Classical.em`'s negative branch shape).
    fn not_pi(&self, parent: &EnvDeclBuilder, p: Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let false_ = Expr::const_(Name::from_string("False"), vec![]);
        let (x_id, _) = ch.fresh_local(p.clone());
        ch.finish_child(ch.mk_pi(x_id, BinderInfo::Default, p, false_))
    }
    /// `Not P` (the `Not` constant applied).
    fn not_c(&self, p: Expr) -> Expr {
        Expr::app(self.not_c.clone(), p)
    }
    fn false_elim(&self, goal: Expr, h_false: Expr) -> Expr {
        Expr::apps(self.false_elim0.clone(), [goal, h_false])
    }
    /// `congrArg` of `fun t => t · r`.
    fn f_right(&self, parent: &EnvDeclBuilder, r: Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.rat.clone());
        let body = self.mul(w, r);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `congrArg` of `fun t => l · t`.
    fn f_left_mul(&self, parent: &EnvDeclBuilder, l: Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.rat.clone());
        let body = self.mul(l, w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `congrArg` of `fun t => l + t`.
    fn f_add_left(&self, parent: &EnvDeclBuilder, l: Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.rat.clone());
        let body = self.add(l, w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `congrArg` of `fun t => t + r`.
    fn f_add_right(&self, parent: &EnvDeclBuilder, r: Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.rat.clone());
        let body = self.add(w, r);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
    }
}

mod add_cube;
mod monotone;

impl Environment {
    /// Register the pure cube lemmas (rung 1 `add_cube` + rung 2 helpers).
    /// Idempotent; every lemma axiom-free.
    pub fn init_algebra_rat_cube_identity(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_and()?;
        self.init_iff()?;
        self.init_classical()?; // Classical.em + Or + Or.rec + False + False.elim
        self.init_boolean_analysis_ring_identities()?; // add_sq + ring surface (add_assoc, distrib, one_mul)
        self.init_rat_field_inst()?; // left/right_distrib, one_mul
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_order_proofs()?; // lt_iff_le_not_le, le_total
        self.init_rat_linear_order()?;
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_right
        self.init_boolean_analysis_order_toolkit_b1b()?; // mul_lt_mul_of_pos_left
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_le_of_lt, lt_of_lt_of_le
        self.init_boolean_analysis_order_toolkit_b1d()?; // sq_lt_sq_of_lt_of_nonneg (dep of cube_lt_cube)

        let c = CubeConsts::new();
        self.register_rat_add_cube(&c)?;
        self.register_rat_cube_lt_cube(&c)?;
        self.register_rat_le_of_cube_le_cube(&c)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "Rat.add_cube",
        "Rat.cube_lt_cube_of_lt_of_nonneg",
        "Rat.le_of_cube_le_cube",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_cube_identity()
            .expect("init_algebra_rat_cube_identity");
        env.init_algebra_rat_cube_identity().expect("idempotent");
        env
    }

    #[test]
    fn test_rat_cube_identity_kernel_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_rat_cube_identity_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
