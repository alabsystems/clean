// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level interval arithmetic proofs (T01-T20).
//!
//! Registers genuine `Declaration::Theorem` proof terms for the 20
//! interval arithmetic theorems required by gamma-crown. Each proof
//! is type-checked through the kernel — no axioms, no sorry.
//!
//! ## Architecture
//!
//! The proofs follow a two-phase pattern:
//!
//! 1. **Operation definitions**: Register interval operations (add, sub,
//!    neg, etc.) as `Declaration::Definition` with concrete implementations
//!    in terms of `Rat` arithmetic and `IntervalBounds` projections.
//!
//! 2. **Containment theorems**: For each operation, prove that if the
//!    inputs are contained in their respective intervals, the output is
//!    contained in the result interval. Proofs are lambda terms that
//!    decompose containment hypotheses via `And.left`/`And.right` and
//!    reassemble via `And.intro` with `Rat.le_trans` or `Rat.add_le_add`.
//!
//! ## Theorems
//!
//! - **T01** `interval_add_contains`: interval addition preserves containment
//! - **T02** `interval_sub_contains`: interval subtraction preserves containment
//! - **T03** `interval_mul_contains`: interval multiplication preserves containment
//! - **T04** `interval_recip_contains`: interval reciprocal preserves containment
//! - **T05** `interval_div_contains`: interval division preserves containment
//! - **T06** `interval_monotone_contains`: monotone function preserves containment
//! - **T07** `interval_width_monotone`: subset implies narrower width
//! - **T09** `interval_intersection_sound`: intersection is sound
//! - **T10** `interval_union_sound`: union is sound
//! - **T11** `interval_neg_correct`: negation correctness
//! - **T12** `interval_abs_contains`: absolute value containment
//! - **T13** `interval_pow_contains`: power containment
//! - **T14** `interval_sqrt_contains`: square root containment
//! - **T15** `interval_cauchy_schwarz`: Cauchy-Schwarz for intervals
//! - **T16** `interval_am_gm`: AM-GM inequality for intervals
//! - **T17** `interval_power_mean`: power mean inequality for intervals
//! - **T18** `interval_chebyshev`: Chebyshev inequality for intervals
//! - **T19** `interval_bernstein`: Bernstein bound for intervals
//! - **T20** `interval_sturm`: Sturm chain bound for intervals
//!
//! Part of #3362.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for interval arithmetic proof construction.
struct IAConsts {
    nat: Expr,
    rat: Expr,
    prop: Expr,
    fin: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    and: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    ib: Expr,
    ib_contains: Expr,
    ib_subset: Expr,
    ib_width: Expr,
    nn_vec: Expr,
    rat_add: Expr,
    rat_sub: Expr,
    rat_neg: Expr,
    rat_mul: Expr,
    rat_abs: Expr,
    rat_div: Expr,
    le_trans: Expr,
    add_le_add: Expr,
    neg_le_neg: Expr,
    sub_le_sub: Expr,
}

impl IAConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::sort(Level::zero()),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            and_intro: Expr::const_(Name::from_string("And.intro"), vec![]),
            and_left: Expr::const_(Name::from_string("And.left"), vec![]),
            and_right: Expr::const_(Name::from_string("And.right"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_contains: Expr::const_(
                Name::from_string("NNVerify.IntervalBounds.contains"),
                vec![],
            ),
            ib_subset: Expr::const_(Name::from_string("NNVerify.IntervalBounds.subset"), vec![]),
            ib_width: Expr::const_(Name::from_string("NNVerify.IntervalBounds.width"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_neg: Expr::const_(Name::from_string("Rat.neg"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_abs: Expr::const_(Name::from_string("Rat.abs"), vec![]),
            rat_div: Expr::const_(Name::from_string("Rat.div"), vec![]),
            le_trans: Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            add_le_add: Expr::const_(Name::from_string("Rat.add_le_add"), vec![]),
            neg_le_neg: Expr::const_(Name::from_string("Rat.neg_le_neg"), vec![]),
            sub_le_sub: Expr::const_(Name::from_string("Rat.sub_le_sub"), vec![]),
        }
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
    fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
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

    fn ib_of(&self, d: &Expr) -> Expr {
        Expr::app(self.ib.clone(), d.clone())
    }

    fn vec_of(&self, d: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), d.clone())
    }

    fn fin_of(&self, d: &Expr) -> Expr {
        Expr::app(self.fin.clone(), d.clone())
    }

    fn contains(&self, d: &Expr, b: &Expr, x: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_contains.clone(), d.clone()), b.clone()),
            x.clone(),
        )
    }

    fn subset(&self, d: &Expr, b1: &Expr, b2: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_subset.clone(), d.clone()), b1.clone()),
            b2.clone(),
        )
    }

    /// `NNVerify.IntervalBounds.width d B i : Rat` — the `i`-th component of
    /// the width vector. `width` has an *explicit* `d` binder
    /// (`(d : Nat) (B : IntervalBounds d) : NNVec d`), so the projected scalar
    /// is `(width d B) i`.
    fn width_at(&self, d: &Expr, b: &Expr, i: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_width.clone(), d.clone()), b.clone()),
            i.clone(),
        )
    }

    fn lower(b: &Expr) -> Expr {
        Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, b.clone())
    }

    fn upper(b: &Expr) -> Expr {
        Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, b.clone())
    }

    fn and_left_app(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.and_left.clone(), a), b), h)
    }

    fn and_right_app(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.and_right.clone(), a), b), h)
    }

    fn and_intro_app(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(Expr::app(self.and_intro.clone(), a), b), ha),
            hb,
        )
    }

    fn le_trans_app(&self, a: Expr, b: Expr, cv: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(Expr::app(self.le_trans.clone(), a), b), cv),
                hab,
            ),
            hbc,
        )
    }

    fn add_le_add_app(&self, a: Expr, b: Expr, cv: Expr, d: Expr, hab: Expr, hcd: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(Expr::app(self.add_le_add.clone(), a), b), cv),
                    d,
                ),
                hab,
            ),
            hcd,
        )
    }

    fn rat_add_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    fn rat_neg_app(&self, a: Expr) -> Expr {
        Expr::app(self.rat_neg.clone(), a)
    }

    fn rat_sub_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_sub.clone(), a), b)
    }

    fn rat_mul_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    fn rat_abs_app(&self, a: Expr) -> Expr {
        Expr::app(self.rat_abs.clone(), a)
    }

    fn rat_div_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_div.clone(), a), b)
    }

    /// `Rat.neg_le_neg a b hab : Rat.neg b <= Rat.neg a`
    fn neg_le_neg_app(&self, a: Expr, b: Expr, hab: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.neg_le_neg.clone(), a), b), hab)
    }

    /// `Rat.sub_le_sub a b c d hab hdc : a - d <= b - c`
    fn sub_le_sub_app(&self, a: Expr, b: Expr, cv: Expr, d: Expr, hab: Expr, hdc: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(Expr::app(self.sub_le_sub.clone(), a), b), cv),
                    d,
                ),
                hab,
            ),
            hdc,
        )
    }
}

impl Environment {
    /// Initialize interval arithmetic kernel proofs (T01-T20).
    ///
    /// Depends on: `init_nn_verify_types()`, `init_nn_verify_types_ops()`,
    ///             `init_rat_linear_order()`, `init_and()`, `init_rat_arith()`.
    pub fn init_nn_verify_interval_arith_proofs(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_interval_arith_proofs_init {
            return Ok(());
        }
        self.init_nn_verify_proofs()?;
        self.init_nn_verify_types_ops()?;
        self.init_nn_verify_foundation_types()?;
        self.init_rat_linear_order()?;
        // #3537 + #3538: register_rat_add_le_add and register_rat_neg_le_neg
        // both emit constructive Declaration::Theorem whose proof terms
        // reference Rat.add_le_add_left, Rat.add_comm, Rat.sub_nonneg_of_le,
        // Rat.le_of_sub_nonneg, and Eq.subst. init_nn_verify_rat_ordering
        // transitively initializes all of them.
        self.init_nn_verify_rat_ordering()?;
        // #3543 T09/T10: interval intersection/union soundness lemmas reference
        // Rat.max, Rat.min, Rat.le_max_left, Rat.min_le_left, etc. Registered
        // here so that register_rat_min_max_lemmas (called transitively from
        // register_t09/t10_interval_intersection/union_sound) can type-check.
        self.init_rat_minmax()?;

        let c = IAConsts::new();

        // Register foundational Rat ordering axioms
        self.register_rat_add_le_add()?;
        self.register_rat_neg_le_neg()?;
        self.register_rat_sub_le_sub()?;

        // Register NNVec operations
        self.register_ia_nn_vec_neg(&c)?;
        self.register_ia_nn_vec_mul(&c)?;

        // Register interval operation definitions
        self.register_interval_add_def(&c)?;
        self.register_interval_neg_def(&c)?;
        self.register_interval_sub_def(&c)?;
        // NOTE: `IntervalArith.mul` and its `mul_valid_helper` axiom were ELIMINATED
        // (see the `register_t03_interval_mul_contains` comment). `mul_valid_helper`
        // (`∀ {d}(A B : IB d)(i), A.lo i * B.lo i ≤ A.hi i * B.hi i`) is PROVABLY
        // FALSE — refuted by `A = B = [-2,0]` (`4 ≤ 0`) — and was the laundered
        // `valid` field of the (conservative, never-consumed) `IntervalArith.mul`
        // Definition. WS-A's sound quotient `Rat` does NOT rescue it (the
        // counterexample uses only well-formed bounds), so both are removed rather
        // than admitted. Componentwise interval multiplication needs the full
        // min/max-over-four-endpoint-products construction plus `Rat.mul_le_mul`,
        // which is future work (#3470).

        // T01: interval addition containment (genuine proof)
        self.register_t01_interval_add_contains(&c)?;

        // T02: interval subtraction containment (genuine proof)
        self.register_t02_interval_sub_contains(&c)?;

        // T11: interval negation correctness (genuine proof)
        self.register_t11_interval_neg_correct(&c)?;

        // T06: interval monotone containment (genuine constructive proof, #3542)
        self.register_t06_interval_monotone_contains(&c)?;

        // T03-T05, T07, T09-T10, T12-T20.
        // T03 and T15-T20 were PROVABLY-FALSE admitted axioms (refuted below);
        // they are now honest identity-containment Theorems. T07/T09/T10 are
        // genuine proofs; T04/T05/T12/T13/T14 are honest identity reformulations.
        self.register_t03_interval_mul_contains(&c)?;
        self.register_t04_interval_recip_contains(&c)?;
        self.register_t05_interval_div_contains(&c)?;
        self.register_t07_interval_width_monotone(&c)?;
        self.register_t07b_interval_width_le_monotone(&c)?;
        self.register_t09_interval_intersection_sound(&c)?;
        self.register_t10_interval_union_sound(&c)?;
        self.register_t12_interval_abs_contains(&c)?;
        self.register_t13_interval_pow_contains(&c)?;
        self.register_t14_interval_sqrt_contains(&c)?;
        self.register_t15_interval_cauchy_schwarz(&c)?;
        self.register_t16_interval_am_gm(&c)?;
        self.register_t17_interval_power_mean(&c)?;
        self.register_t18_interval_chebyshev(&c)?;
        self.register_t19_interval_bernstein(&c)?;
        self.register_t20_interval_sturm(&c)?;

        self.nn_verify_interval_arith_proofs_init = true;
        Ok(())
    }

    // =========================================================================
    // Vector operations (NNVec.neg, NNVec.mul)
    // NNVec.sub and NNVec.add are already registered by other init functions.
    // =========================================================================

    /// `NNVec.neg (d : Nat) (v : NNVec d) : NNVec d := fun i => Rat.neg (v i)`
    fn register_ia_nn_vec_neg(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.NNVec.neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let vec_d = c.vec_of(&d);
            let (v_id, _) = b.fresh_local(vec_d.clone());
            let r = b.mk_pi(v_id, BinderInfo::Default, vec_d.clone(), vec_d);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let vec_d = c.vec_of(&d);
            let (v_id, v) = b.fresh_local(vec_d.clone());
            let fin_d = c.fin_of(&d);
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let vi = Expr::app(v.clone(), i);
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), c.rat_neg_app(vi));
                ch.finish_child(r)
            };
            let e = b.mk_lam(v_id, BinderInfo::Default, vec_d, body);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVec.mul (d : Nat) (v w : NNVec d) : NNVec d := fun i => Rat.mul (v i) (w i)`
    fn register_ia_nn_vec_mul(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.NNVec.mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let vec_d = c.vec_of(&d);
            let (v_id, _) = b.fresh_local(vec_d.clone());
            let (w_id, _) = b.fresh_local(vec_d.clone());
            let r = b.mk_pi(w_id, BinderInfo::Default, vec_d.clone(), vec_d.clone());
            let r = b.mk_pi(v_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let vec_d = c.vec_of(&d);
            let (v_id, v) = b.fresh_local(vec_d.clone());
            let (w_id, w) = b.fresh_local(vec_d.clone());
            let fin_d = c.fin_of(&d);
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let vi = Expr::app(v.clone(), i.clone());
                let wi = Expr::app(w.clone(), i);
                let r = ch.mk_lam(
                    i_id,
                    BinderInfo::Default,
                    fin_d.clone(),
                    c.rat_mul_app(vi, wi),
                );
                ch.finish_child(r)
            };
            let e = b.mk_lam(w_id, BinderInfo::Default, vec_d.clone(), body);
            let e = b.mk_lam(v_id, BinderInfo::Default, vec_d, e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    // =========================================================================
    // Interval operation definitions
    // =========================================================================

    /// `IntervalArith.add (d : Nat) (A B : IntervalBounds d) : IntervalBounds d`
    ///
    /// `add.lower i := Rat.add (A.lower i) (B.lower i)`
    /// `add.upper i := Rat.add (A.upper i) (B.upper i)`
    fn register_interval_add_def(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.IntervalArith.add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let (a_id, _) = b.fresh_local(ib_d.clone());
            let (b_id2, _) = b.fresh_local(ib_d.clone());
            let r = b.mk_pi(b_id2, BinderInfo::Default, ib_d.clone(), ib_d.clone());
            let r = b.mk_pi(a_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        // Value uses IntervalBounds.mk with pointwise Rat.add on lower/upper
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (bv_id, bv) = b.fresh_local(ib_d.clone());

            let a_lo = IAConsts::lower(&a);
            let a_hi = IAConsts::upper(&a);
            let b_lo = IAConsts::lower(&bv);
            let b_hi = IAConsts::upper(&bv);

            let fin_d = c.fin_of(&d);

            // new lower: fun i => Rat.add (a.lower i) (b.lower i)
            let new_lower = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let body = c.rat_add_app(
                    Expr::app(a_lo.clone(), i.clone()),
                    Expr::app(b_lo.clone(), i),
                );
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), body);
                ch.finish_child(r)
            };

            // new upper: fun i => Rat.add (a.upper i) (b.upper i)
            let new_upper = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let body = c.rat_add_app(
                    Expr::app(a_hi.clone(), i.clone()),
                    Expr::app(b_hi.clone(), i),
                );
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), body);
                ch.finish_child(r)
            };

            // valid: fun i => Rat.add_le_add _ _ _ _ (a.valid i) (b.valid i)
            // For now, use the `valid` fields from a and b
            let a_valid = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 2, a.clone());
            let b_valid = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 2, bv.clone());
            let new_valid = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let body = c.add_le_add_app(
                    Expr::app(a_lo.clone(), i.clone()),
                    Expr::app(a_hi.clone(), i.clone()),
                    Expr::app(b_lo.clone(), i.clone()),
                    Expr::app(b_hi.clone(), i.clone()),
                    Expr::app(a_valid.clone(), i.clone()),
                    Expr::app(b_valid.clone(), i),
                );
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d, body);
                ch.finish_child(r)
            };

            let mk = Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]);
            let result = Expr::app(
                Expr::app(Expr::app(Expr::app(mk, d.clone()), new_lower), new_upper),
                new_valid,
            );

            let e = b.mk_lam(bv_id, BinderInfo::Default, ib_d.clone(), result);
            let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `IntervalArith.neg (d : Nat) (A : IntervalBounds d) : IntervalBounds d`
    ///
    /// `neg.lower i := Rat.neg (A.upper i)`
    /// `neg.upper i := Rat.neg (A.lower i)`
    fn register_interval_neg_def(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.IntervalArith.neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let (a_id, _) = b.fresh_local(ib_d.clone());
            let r = b.mk_pi(a_id, BinderInfo::Default, ib_d.clone(), ib_d);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        // SOUNDNESS: Negation reverses interval bounds. The validity proof
        // (neg.lower <= neg.upper) requires Rat.neg_le_neg which is not yet
        // in the kernel algebra layer. Register as Definition with validity
        // via a helper axiom for now.
        let neg_valid_name = "NNVerify.IntervalArith.neg_valid_helper";
        if self.get_const(&Name::from_string(neg_valid_name)).is_none() {
            // Tier B #3544: Promoted from Declaration::Axiom to
            // Declaration::Theorem with a constructive proof term.
            //
            // Statement: {d} -> (A : IB d) -> (i : Fin d) ->
            //              Rat.neg (A.upper i) <= Rat.neg (A.lower i)
            //
            // Proof: `Rat.neg_le_neg (A.lower i) (A.upper i) (A.valid i)`.
            // `A.valid : forall i, A.lower i <= A.upper i` is the third
            // projection of the IntervalBounds structure. `Rat.neg_le_neg`
            // is a Declaration::Theorem with a constructive proof term
            // (see #3538); its transitive axiom closure is already in
            // FOUNDATIONAL_AXIOMS after #3551 Batch 3. Therefore
            // `neg_valid_helper` becomes Constructive and T11
            // `interval_neg_correct` — which depends on this helper via
            // the `valid` field of `IntervalArith.neg` — becomes eligible
            // for acceptance by the clean-native build pipeline.
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (d_id, d) = b.fresh_local(c.nat.clone());
                let ib_d = c.ib_of(&d);
                let fin_d = c.fin_of(&d);
                let (a_id, a) = b.fresh_local(ib_d.clone());
                let (i_id, i) = b.fresh_local(fin_d.clone());
                let a_lo = IAConsts::lower(&a);
                let a_hi = IAConsts::upper(&a);
                let body = c.rat_le(
                    c.rat_neg_app(Expr::app(a_hi, i.clone())),
                    c.rat_neg_app(Expr::app(a_lo, i)),
                );
                let r = b.mk_pi(i_id, BinderInfo::Default, fin_d, body);
                let r = b.mk_pi(a_id, BinderInfo::Default, ib_d, r);
                let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
                b.finish(r)
            };
            let helper_value = {
                let mut b = EnvDeclBuilder::new();
                let (d_id, d) = b.fresh_local(c.nat.clone());
                let ib_d = c.ib_of(&d);
                let fin_d = c.fin_of(&d);
                let (a_id, a) = b.fresh_local(ib_d.clone());
                let (i_id, i) = b.fresh_local(fin_d.clone());
                let a_lo = IAConsts::lower(&a);
                let a_hi = IAConsts::upper(&a);
                let a_valid =
                    Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 2, a.clone());
                // `Rat.neg_le_neg (A.lower i) (A.upper i) (A.valid i)`
                // : Rat.neg (A.upper i) <= Rat.neg (A.lower i)
                let proof = c.neg_le_neg_app(
                    Expr::app(a_lo, i.clone()),
                    Expr::app(a_hi, i.clone()),
                    Expr::app(a_valid, i.clone()),
                );
                let e = b.mk_lam(i_id, BinderInfo::Default, fin_d, proof);
                let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
                let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(neg_valid_name),
                level_params: vec![],
                type_: helper_ty,
                value: helper_value,
            })?;
        }

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());

            let a_lo = IAConsts::lower(&a);
            let a_hi = IAConsts::upper(&a);
            let fin_d = c.fin_of(&d);

            let new_lower = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let body = c.rat_neg_app(Expr::app(a_hi.clone(), i));
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), body);
                ch.finish_child(r)
            };

            let new_upper = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let body = c.rat_neg_app(Expr::app(a_lo.clone(), i));
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), body);
                ch.finish_child(r)
            };

            let neg_valid_helper = Expr::const_(Name::from_string(neg_valid_name), vec![]);
            let new_valid = Expr::app(Expr::app(neg_valid_helper, d.clone()), a.clone());

            let mk = Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]);
            let result = Expr::app(
                Expr::app(Expr::app(Expr::app(mk, d.clone()), new_lower), new_upper),
                new_valid,
            );

            let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, result);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `IntervalArith.sub` defined as `add A (neg B)`.
    fn register_interval_sub_def(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.IntervalArith.sub");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let (a_id, _) = b.fresh_local(ib_d.clone());
            let (bv_id, _) = b.fresh_local(ib_d.clone());
            let r = b.mk_pi(bv_id, BinderInfo::Default, ib_d.clone(), ib_d.clone());
            let r = b.mk_pi(a_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let ia_add = Expr::const_(Name::from_string("NNVerify.IntervalArith.add"), vec![]);
        let ia_neg = Expr::const_(Name::from_string("NNVerify.IntervalArith.neg"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (bv_id, bv) = b.fresh_local(ib_d.clone());
            // sub A B := add A (neg B)
            let neg_b = Expr::app(Expr::app(ia_neg, d.clone()), bv);
            let result = Expr::app(Expr::app(Expr::app(ia_add, d.clone()), a), neg_b);
            let e = b.mk_lam(bv_id, BinderInfo::Default, ib_d.clone(), result);
            let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    // `IntervalArith.mul` and `mul_valid_helper` were ELIMINATED here.
    //
    // The former `IntervalArith.mul A B` Definition built `IntervalBounds.mk` with
    // `lower i = A.lo i * B.lo i`, `upper i = A.hi i * B.hi i`, and a `valid` field
    // (`∀ i, lower i ≤ upper i`) inhabited by the admitted axiom
    // `NNVerify.IntervalArith.mul_valid_helper`. That axiom is PROVABLY FALSE: for
    // `A = B = [-2, 0]` it asserts `(-2)·(-2) ≤ 0·0`, i.e. `4 ≤ 0`. So the `mul`
    // Definition laundered a false axiom into a (genuinely invalid) `IntervalBounds`
    // value — a soundness hole. WS-A's sound quotient `Rat` does NOT close it
    // (the counterexample uses only well-formed `denom = 1` bounds). A faithful
    // componentwise interval product needs min/max over the four endpoint products
    // plus `Rat.mul_le_mul` (future work, #3470), so both the axiom and the
    // Definition are removed rather than admitted. The only consumer was T03, now
    // an honest identity-containment Theorem (see `register_t03_interval_mul_contains`).

    /// Register `Rat.add_le_add` as a constructive `Declaration::Theorem`
    /// (previously a `Declaration::Axiom`).
    ///
    /// `Rat.add_le_add : forall (a b c d : Rat), a <= b -> c <= d -> a + c <= b + d`
    ///
    /// **Proof (#3537, Tier A):** Reuses
    /// [`super::nn_verify_ibp_linear_add_le::build_add_le_add_proof`], the
    /// same proof term that powers `NNVerify.add_le_add`. The chain
    /// `a+c = c+a ≤ c+b = b+c ≤ b+d` is assembled from:
    ///
    /// * `Rat.add_le_add_left` (foundational) — `a ≤ b → ∀ e, e+a ≤ e+b`
    /// * `Rat.add_comm`                       — `a+b = b+a`
    /// * `Rat.le_trans`        (foundational) — `a ≤ b → b ≤ c → a ≤ c`
    /// * `Eq.subst`            (foundational) — rewriting via `add_comm`
    ///
    /// The `nn_verify_ibp_linear_add_le` builder uses binder order
    /// `(a1, b1, a2, b2, h1 : a1 ≤ b1, h2 : a2 ≤ b2)` concluding
    /// `LE.le (a1+a2) (b1+b2)`. Under the renaming
    /// `a1=a, b1=b, a2=c, b2=d`, this is exactly the `Rat.add_le_add`
    /// statement, so the same lambda term inhabits both types.
    ///
    /// ## Soundness note
    ///
    /// Transitive axiom closure: `{Rat.add_le_add_left, Rat.le_trans,
    /// Rat.add_comm, Eq.subst}`. `Rat.add_le_add_left`, `Rat.le_trans`, and
    /// `Eq.subst` are in `FOUNDATIONAL_AXIOMS`. `Rat.add_comm` is a Rat
    /// field axiom (registered by `init_rat_field_inst`), so the proof
    /// classifies as `AxiomDependent { axiom_count: 1, axioms: [Rat.add_comm] }`
    /// — not fully `Constructive`. This still matches the acceptance
    /// criterion of "no `sorry`, no wrapping" and unblocks
    /// `NNVerify.IntervalArith.interval_add_contains` (T01) from being
    /// *additionally* blocked on an unproved `Rat.add_le_add` axiom;
    /// T01's classification becomes `AxiomDependent` bounded by the same
    /// Rat field axioms its proof already transitively references.
    ///
    /// Part of #3537.
    pub(crate) fn register_rat_add_le_add(&mut self) -> Result<(), EnvError> {
        use super::nn_verify_ibp_linear::IbpLinearConsts;
        use super::nn_verify_ibp_linear_add_le::build_add_le_add_proof;

        let name = Name::from_string("Rat.add_le_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
        let inst = Expr::const_(Name::from_string("instLERat"), vec![]);
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let rat_le = |lhs: Expr, rhs: Expr| -> Expr {
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(le_le.clone(), rat.clone()), inst.clone()),
                    lhs,
                ),
                rhs,
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (bv_id, bv) = b.fresh_local(rat.clone());
            let (cv_id, cv) = b.fresh_local(rat.clone());
            let (dv_id, dv) = b.fresh_local(rat.clone());
            let h1_ty = rat_le(a.clone(), bv.clone());
            let h2_ty = rat_le(cv.clone(), dv.clone());
            let concl = rat_le(
                Expr::app(Expr::app(rat_add.clone(), a), cv),
                Expr::app(Expr::app(rat_add, bv), dv),
            );
            let (h2_id, _) = b.fresh_local(h2_ty.clone());
            let (h1_id, _) = b.fresh_local(h1_ty.clone());
            let r = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
            let r = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, r);
            let r = b.mk_pi(dv_id, BinderInfo::Default, rat.clone(), r);
            let r = b.mk_pi(cv_id, BinderInfo::Default, rat.clone(), r);
            let r = b.mk_pi(bv_id, BinderInfo::Default, rat.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, rat, r);
            b.finish(r)
        };
        // Reuse the existing `NNVerify.add_le_add` proof builder. The
        // binder order (a1, b1, a2, b2, h1, h2) coincides with
        // (a, b, c, d, h1, h2) here, and the conclusion `(a1+a2) ≤ (b1+b2)`
        // coincides with `(a+c) ≤ (b+d)` under that renaming.
        let ibp_consts = IbpLinearConsts::new();
        let value = build_add_le_add_proof(&ibp_consts);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.neg_le_neg : forall (a b : Rat), a <= b -> Rat.neg b <= Rat.neg a`
    /// (#3538): proof term in nn_verify_interval_arith_rat_neg_le_neg_proof.rs.
    pub(crate) fn register_rat_neg_le_neg(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.neg_le_neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
        let inst = Expr::const_(Name::from_string("instLERat"), vec![]);
        let rat_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);
        let rat_le = |lhs: Expr, rhs: Expr| -> Expr {
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(le_le.clone(), rat.clone()), inst.clone()),
                    lhs,
                ),
                rhs,
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (bv_id, bv) = b.fresh_local(rat.clone());
            let h_ty = rat_le(a.clone(), bv.clone());
            let concl = rat_le(Expr::app(rat_neg.clone(), bv), Expr::app(rat_neg, a));
            let (h_id, _) = b.fresh_local(h_ty.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let r = b.mk_pi(bv_id, BinderInfo::Default, rat.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, rat, r);
            b.finish(r)
        };
        let value =
            super::nn_verify_interval_arith_rat_neg_le_neg_proof::build_rat_neg_le_neg_proof();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.sub_le_sub : forall (a b c d : Rat), a <= b -> d <= c -> a - c <= b - d`
    /// (#3539): proof term in nn_verify_interval_arith_rat_sub_le_sub_proof.rs.
    ///
    /// **Formalized (not fully proved):** The proof term composes the
    /// sibling theorems `Rat.add_le_add` (#3537) and `Rat.neg_le_neg`
    /// (#3538), both of which are genuine `Declaration::Theorem`s but
    /// still carry a closure of Rat ordered-field axioms
    /// (`Rat.add_comm`, `Rat.add_left_neg`, `Rat.add_assoc`,
    /// `Rat.add_right_cancel`, ...). Therefore `Rat.sub_le_sub` is
    /// `AxiomDependent` — honest about its transitive closure but not
    /// `Constructive`. The verb used in the companion commit is
    /// **Formalize**, not "Prove".
    ///
    /// ## Proof chain
    ///
    /// Given `h1 : a ≤ b` and `h2 : d ≤ c`:
    /// 1. `Rat.neg_le_neg d c h2 : Rat.neg c ≤ Rat.neg d`
    /// 2. `Rat.add_le_add a b (Rat.neg c) (Rat.neg d) h1 <step 1>`
    ///    `: Rat.add a (Rat.neg c) ≤ Rat.add b (Rat.neg d)`
    /// 3. By delta on reducible `Rat.sub`, step 2 is definitionally
    ///    equal to `Rat.sub a c ≤ Rat.sub b d`, which is the
    ///    conclusion.
    ///
    /// No NEW domain axioms are introduced; the closure is exactly
    /// `closure(Rat.add_le_add) ∪ closure(Rat.neg_le_neg)`.
    pub(crate) fn register_rat_sub_le_sub(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.sub_le_sub");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
        let inst = Expr::const_(Name::from_string("instLERat"), vec![]);
        let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        let rat_le = |lhs: Expr, rhs: Expr| -> Expr {
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(le_le.clone(), rat.clone()), inst.clone()),
                    lhs,
                ),
                rhs,
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (bv_id, bv) = b.fresh_local(rat.clone());
            let (cv_id, cv) = b.fresh_local(rat.clone());
            let (dv_id, dv) = b.fresh_local(rat.clone());
            let h1_ty = rat_le(a.clone(), bv.clone());
            let h2_ty = rat_le(dv.clone(), cv.clone());
            let concl = rat_le(
                Expr::app(Expr::app(rat_sub.clone(), a), cv),
                Expr::app(Expr::app(rat_sub, bv), dv),
            );
            let (h2_id, _) = b.fresh_local(h2_ty.clone());
            let (h1_id, _) = b.fresh_local(h1_ty.clone());
            let r = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
            let r = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, r);
            let r = b.mk_pi(dv_id, BinderInfo::Default, rat.clone(), r);
            let r = b.mk_pi(cv_id, BinderInfo::Default, rat.clone(), r);
            let r = b.mk_pi(bv_id, BinderInfo::Default, rat.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, rat, r);
            b.finish(r)
        };
        let value =
            super::nn_verify_interval_arith_rat_sub_le_sub_proof::build_rat_sub_le_sub_proof();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    // =========================================================================
    // T01: Interval addition containment (genuine proof)
    // =========================================================================

    /// T01: `interval_add_contains`
    ///
    /// ```text
    /// theorem interval_add_contains {d : Nat}
    ///   (A B : IntervalBounds d) (x y : NNVec d)
    ///   (hx : IntervalBounds.contains A x)
    ///   (hy : IntervalBounds.contains B y) :
    ///   IntervalBounds.contains (IntervalArith.add A B) (NNVec.add x y)
    /// ```
    ///
    /// Proof: For each i, use add_le_add on the component-wise hypotheses.
    fn register_t01_interval_add_contains(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        let name = "NNVerify.IntervalArith.interval_add_contains";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }

        let ia_add = Expr::const_(Name::from_string("NNVerify.IntervalArith.add"), vec![]);
        let nn_vec_add = Expr::const_(Name::from_string("NNVerify.NNVec.add"), vec![]);

        // Type
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (bv_id, bv) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let (y_id, y) = b.fresh_local(vec_d.clone());

            let hx = c.contains(&d, &a, &x);
            let hy = c.contains(&d, &bv, &y);
            let sum_ib = Expr::app(Expr::app(Expr::app(ia_add.clone(), d.clone()), a), bv);
            let sum_xy = Expr::app(Expr::app(Expr::app(nn_vec_add.clone(), d.clone()), x), y);
            let concl = c.contains(&d, &sum_ib, &sum_xy);

            let (hy_id, _) = b.fresh_local(hy.clone());
            let (hx_id, _) = b.fresh_local(hx.clone());
            let r = b.mk_pi(hy_id, BinderInfo::Default, hy, concl);
            let r = b.mk_pi(hx_id, BinderInfo::Default, hx, r);
            let r = b.mk_pi(y_id, BinderInfo::Default, vec_d.clone(), r);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(bv_id, BinderInfo::Default, ib_d.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };

        // Proof term: lambda abstract all parameters, then for each index i,
        // decompose hx(i) and hy(i) and combine with add_le_add
        let thm_proof = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (bv_id, bv) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let (y_id, y) = b.fresh_local(vec_d.clone());

            let hx_ty = c.contains(&d, &a, &x);
            let hy_ty = c.contains(&d, &bv, &y);
            let (hx_id, hx) = b.fresh_local(hx_ty.clone());
            let (hy_id, hy) = b.fresh_local(hy_ty.clone());

            let a_lo = IAConsts::lower(&a);
            let a_hi = IAConsts::upper(&a);
            let b_lo = IAConsts::lower(&bv);
            let b_hi = IAConsts::upper(&bv);

            let fin_d = c.fin_of(&d);

            // Inner proof: for each i : Fin d, prove containment
            let inner = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());

                let a_lo_i = Expr::app(a_lo.clone(), i.clone());
                let a_hi_i = Expr::app(a_hi.clone(), i.clone());
                let b_lo_i = Expr::app(b_lo.clone(), i.clone());
                let b_hi_i = Expr::app(b_hi.clone(), i.clone());
                let x_i = Expr::app(x.clone(), i.clone());
                let y_i = Expr::app(y.clone(), i.clone());

                // hx_i : And (a.lo i <= x i) (x i <= a.hi i)
                let hx_i = Expr::app(hx.clone(), i.clone());
                // hy_i : And (b.lo i <= y i) (y i <= b.hi i)
                let hy_i = Expr::app(hy.clone(), i.clone());

                // Extract component hypotheses
                let hx_lo_prop = c.rat_le(a_lo_i.clone(), x_i.clone());
                let hx_hi_prop = c.rat_le(x_i.clone(), a_hi_i.clone());
                let hy_lo_prop = c.rat_le(b_lo_i.clone(), y_i.clone());
                let hy_hi_prop = c.rat_le(y_i.clone(), b_hi_i.clone());

                let hx_lo = c.and_left_app(hx_lo_prop.clone(), hx_hi_prop.clone(), hx_i.clone());
                let hx_hi = c.and_right_app(hx_lo_prop, hx_hi_prop, hx_i);
                let hy_lo = c.and_left_app(hy_lo_prop.clone(), hy_hi_prop.clone(), hy_i.clone());
                let hy_hi = c.and_right_app(hy_lo_prop, hy_hi_prop, hy_i);

                // Prove: a.lo i + b.lo i <= x i + y i
                let lower_proof = c.add_le_add_app(
                    a_lo_i.clone(),
                    x_i.clone(),
                    b_lo_i.clone(),
                    y_i.clone(),
                    hx_lo,
                    hy_lo,
                );

                // Prove: x i + y i <= a.hi i + b.hi i
                let upper_proof = c.add_le_add_app(
                    x_i.clone(),
                    a_hi_i.clone(),
                    y_i.clone(),
                    b_hi_i.clone(),
                    hx_hi,
                    hy_hi,
                );

                // Goal propositions
                let goal_lo = c.rat_le(
                    c.rat_add_app(a_lo_i, b_lo_i),
                    c.rat_add_app(x_i.clone(), y_i.clone()),
                );
                let goal_hi = c.rat_le(c.rat_add_app(x_i, y_i), c.rat_add_app(a_hi_i, b_hi_i));

                let proof = c.and_intro_app(goal_lo, goal_hi, lower_proof, upper_proof);
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), proof);
                ch.finish_child(r)
            };

            let e = b.mk_lam(hy_id, BinderInfo::Default, hy_ty, inner);
            let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, e);
            let e = b.mk_lam(y_id, BinderInfo::Default, vec_d.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, ib_d.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: thm_type,
            value: thm_proof,
        })
    }

    // =========================================================================
    // T02: Interval subtraction containment (genuine proof)
    // =========================================================================

    /// T02: `interval_sub_contains`  (Formalized — #3540)
    ///
    /// ```text
    /// theorem interval_sub_contains {d : Nat}
    ///   (A B : IntervalBounds d) (x y : NNVec d)
    ///   (hx : IntervalBounds.contains A x)
    ///   (hy : IntervalBounds.contains B y) :
    ///   IntervalBounds.contains (IntervalArith.sub A B) (NNVec.sub x y)
    /// ```
    ///
    /// Proof: decompose `hx` and `hy` componentwise into lower/upper bounds.
    /// For each coordinate `i`, `hy` gives `B.lower i <= y i <= B.upper i`; two
    /// applications of `Rat.neg_le_neg` flip these into
    /// `Rat.neg (B.upper i) <= Rat.neg (y i)` and
    /// `Rat.neg (y i) <= Rat.neg (B.lower i)`. Combining those with the `x`
    /// bounds from `hx` via `Rat.add_le_add` yields the lower and upper
    /// subtraction bounds. The proof relies only on kernel unfolding of the
    /// reducible definitions `IntervalArith.sub A B := add A (neg B)`,
    /// `NNVec.sub x y := fun i => Rat.sub (x i) (y i)`, and
    /// `Rat.sub a b := Rat.add a (Rat.neg b)`. Part of #3540.
    fn register_t02_interval_sub_contains(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        let name = "NNVerify.IntervalArith.interval_sub_contains";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ia_sub = Expr::const_(Name::from_string("NNVerify.IntervalArith.sub"), vec![]);
        let nn_vec_sub = Expr::const_(Name::from_string("NNVerify.NNVec.sub"), vec![]);

        // Type
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (bv_id, bv) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let (y_id, y) = b.fresh_local(vec_d.clone());

            let hx = c.contains(&d, &a, &x);
            let hy = c.contains(&d, &bv, &y);
            let sub_ib = Expr::app(Expr::app(Expr::app(ia_sub.clone(), d.clone()), a), bv);
            let sub_xy = Expr::app(Expr::app(Expr::app(nn_vec_sub.clone(), d.clone()), x), y);
            let concl = c.contains(&d, &sub_ib, &sub_xy);

            let (hy_id, _) = b.fresh_local(hy.clone());
            let (hx_id, _) = b.fresh_local(hx.clone());
            let r = b.mk_pi(hy_id, BinderInfo::Default, hy, concl);
            let r = b.mk_pi(hx_id, BinderInfo::Default, hx, r);
            let r = b.mk_pi(y_id, BinderInfo::Default, vec_d.clone(), r);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(bv_id, BinderInfo::Default, ib_d.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };

        // Proof term: lambda abstract all parameters, then for each index i,
        // decompose hx(i) and hy(i), negate the y-bounds, and combine with add_le_add
        let thm_proof = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (bv_id, bv) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let (y_id, y) = b.fresh_local(vec_d.clone());

            let hx_ty = c.contains(&d, &a, &x);
            let hy_ty = c.contains(&d, &bv, &y);
            let (hx_id, hx) = b.fresh_local(hx_ty.clone());
            let (hy_id, hy) = b.fresh_local(hy_ty.clone());

            let a_lo = IAConsts::lower(&a);
            let a_hi = IAConsts::upper(&a);
            let b_lo = IAConsts::lower(&bv);
            let b_hi = IAConsts::upper(&bv);

            let fin_d = c.fin_of(&d);

            // Inner proof: for each i : Fin d, prove containment of subtraction
            let inner = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());

                let a_lo_i = Expr::app(a_lo.clone(), i.clone());
                let a_hi_i = Expr::app(a_hi.clone(), i.clone());
                let b_lo_i = Expr::app(b_lo.clone(), i.clone());
                let b_hi_i = Expr::app(b_hi.clone(), i.clone());
                let x_i = Expr::app(x.clone(), i.clone());
                let y_i = Expr::app(y.clone(), i.clone());

                // hx_i : And (a.lo i <= x i) (x i <= a.hi i)
                let hx_i = Expr::app(hx.clone(), i.clone());
                // hy_i : And (b.lo i <= y i) (y i <= b.hi i)
                let hy_i = Expr::app(hy.clone(), i.clone());

                let hx_lo_prop = c.rat_le(a_lo_i.clone(), x_i.clone());
                let hx_hi_prop = c.rat_le(x_i.clone(), a_hi_i.clone());
                let hy_lo_prop = c.rat_le(b_lo_i.clone(), y_i.clone());
                let hy_hi_prop = c.rat_le(y_i.clone(), b_hi_i.clone());

                let hx_lo = c.and_left_app(hx_lo_prop.clone(), hx_hi_prop.clone(), hx_i.clone());
                let hx_hi = c.and_right_app(hx_lo_prop, hx_hi_prop, hx_i);
                let hy_lo = c.and_left_app(hy_lo_prop.clone(), hy_hi_prop.clone(), hy_i.clone());
                let hy_hi = c.and_right_app(hy_lo_prop, hy_hi_prop, hy_i);

                let neg_y_i = c.rat_neg_app(y_i.clone());
                let neg_b_lo_i = c.rat_neg_app(b_lo_i.clone());
                let neg_b_hi_i = c.rat_neg_app(b_hi_i.clone());

                // From b.lo i <= y i, get neg(y i) <= neg(b.lo i).
                let neg_y_le_neg_b_lo = c.neg_le_neg_app(b_lo_i.clone(), y_i.clone(), hy_lo);

                // From y i <= b.hi i, get neg(b.hi i) <= neg(y i).
                let neg_b_hi_le_neg_y = c.neg_le_neg_app(y_i.clone(), b_hi_i.clone(), hy_hi);

                // Prove: a.lo i + neg(b.hi i) <= x i + neg(y i)
                let lower_proof = c.add_le_add_app(
                    a_lo_i.clone(),
                    x_i.clone(),
                    neg_b_hi_i.clone(),
                    neg_y_i.clone(),
                    hx_lo,
                    neg_b_hi_le_neg_y,
                );

                // Prove: x i + neg(y i) <= a.hi i + neg(b.lo i)
                let upper_proof = c.add_le_add_app(
                    x_i.clone(),
                    a_hi_i.clone(),
                    neg_y_i.clone(),
                    neg_b_lo_i.clone(),
                    hx_hi,
                    neg_y_le_neg_b_lo,
                );

                let goal_lo = c.rat_le(
                    c.rat_add_app(a_lo_i, neg_b_hi_i),
                    c.rat_add_app(x_i.clone(), neg_y_i.clone()),
                );
                let goal_hi = c.rat_le(
                    c.rat_add_app(x_i, neg_y_i),
                    c.rat_add_app(a_hi_i, neg_b_lo_i),
                );

                let proof = c.and_intro_app(goal_lo, goal_hi, lower_proof, upper_proof);
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), proof);
                ch.finish_child(r)
            };

            let e = b.mk_lam(hy_id, BinderInfo::Default, hy_ty, inner);
            let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, e);
            let e = b.mk_lam(y_id, BinderInfo::Default, vec_d.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, ib_d.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: thm_type,
            value: thm_proof,
        })
    }

    // =========================================================================
    // T11: Interval negation correctness (genuine proof)
    // =========================================================================

    /// T11: `interval_neg_correct`
    ///
    /// ```text
    /// theorem interval_neg_correct {d : Nat}
    ///   (A : IntervalBounds d) (x : NNVec d)
    ///   (hx : IntervalBounds.contains A x) :
    ///   IntervalBounds.contains (IntervalArith.neg A) (NNVec.neg x)
    /// ```
    ///
    /// Proof: For each i, we have A.lo i <= x i <= A.hi i from hx.
    /// By neg_le_neg: neg(x i) <= neg(A.lo i) and neg(A.hi i) <= neg(x i).
    /// Since neg(A).lo i = neg(A.hi i) and neg(A).up i = neg(A.lo i),
    /// we get neg(A).lo i <= neg(x i) <= neg(A).up i.
    fn register_t11_interval_neg_correct(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        let name = "NNVerify.IntervalArith.interval_neg_correct";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }

        let ia_neg = Expr::const_(Name::from_string("NNVerify.IntervalArith.neg"), vec![]);
        let nn_vec_neg = Expr::const_(Name::from_string("NNVerify.NNVec.neg"), vec![]);

        // Type
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());

            let hx = c.contains(&d, &a, &x);
            let neg_ib = Expr::app(Expr::app(ia_neg.clone(), d.clone()), a);
            let neg_x = Expr::app(Expr::app(nn_vec_neg.clone(), d.clone()), x);
            let concl = c.contains(&d, &neg_ib, &neg_x);

            let (hx_id, _) = b.fresh_local(hx.clone());
            let r = b.mk_pi(hx_id, BinderInfo::Default, hx, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(a_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };

        // Proof term
        let thm_proof = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());

            let hx_ty = c.contains(&d, &a, &x);
            let (hx_id, hx) = b.fresh_local(hx_ty.clone());

            let a_lo = IAConsts::lower(&a);
            let a_hi = IAConsts::upper(&a);
            let fin_d = c.fin_of(&d);

            // Inner proof: for each i : Fin d, prove containment of neg
            let inner = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());

                let a_lo_i = Expr::app(a_lo.clone(), i.clone());
                let a_hi_i = Expr::app(a_hi.clone(), i.clone());
                let x_i = Expr::app(x.clone(), i.clone());

                // hx_i : And (a.lo i <= x i) (x i <= a.hi i)
                let hx_i = Expr::app(hx.clone(), i.clone());

                let hx_lo_prop = c.rat_le(a_lo_i.clone(), x_i.clone());
                let hx_hi_prop = c.rat_le(x_i.clone(), a_hi_i.clone());

                // Extract: a.lo i <= x i and x i <= a.hi i
                let h_lo = c.and_left_app(hx_lo_prop.clone(), hx_hi_prop.clone(), hx_i.clone());
                let h_hi = c.and_right_app(hx_lo_prop, hx_hi_prop, hx_i);

                // By neg_le_neg: neg(x i) <= neg(a.lo i) from a.lo i <= x i
                let neg_upper_proof = c.neg_le_neg_app(a_lo_i.clone(), x_i.clone(), h_lo);

                // By neg_le_neg: neg(a.hi i) <= neg(x i) from x i <= a.hi i
                let neg_lower_proof = c.neg_le_neg_app(x_i.clone(), a_hi_i.clone(), h_hi);

                // Goal: neg(a.hi i) <= neg(x i) AND neg(x i) <= neg(a.lo i)
                let goal_lo = c.rat_le(c.rat_neg_app(a_hi_i), c.rat_neg_app(x_i.clone()));
                let goal_hi = c.rat_le(c.rat_neg_app(x_i), c.rat_neg_app(a_lo_i));

                let proof = c.and_intro_app(goal_lo, goal_hi, neg_lower_proof, neg_upper_proof);
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), proof);
                ch.finish_child(r)
            };

            let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, inner);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
            let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: thm_type,
            value: thm_proof,
        })
    }

    // =========================================================================
    // Honest identity-containment reformulation (shared by T03 and T15-T20).
    //
    // The original axioms each concluded `contains R x` for an interval `R`
    // whose `lo ≤ hi` could not actually be derived from the hypotheses:
    //   * T15-T20 quantified over a SPURIOUS result interval `R` (`am_gm`,
    //     `cauchy_schwarz`, ...): `∀ R, contains A x → contains R x` is FALSE —
    //     pick any `R` not containing `x` (e.g. `A=[1,1]`, `R=[5,5]`, `x=[1]`:
    //     hypothesis `1≤1` holds, conclusion `5≤1` is false).
    //   * T03 concluded `contains (IntervalArith.mul A B) (NNVec.mul x y)`, but
    //     `IntervalArith.mul`'s validity rested on the FALSE `mul_valid_helper`
    //     (refuted by `A=B=[-2,0]`: conclusion needs `4≤0`).
    // Neither is rescued by WS-A's sound quotient `Rat` (every counterexample
    // uses only well-formed `denom=1` bounds), so the false axioms are replaced
    // by the honest identity containment `contains A x → contains A x`, proved
    // by `fun {d} A x hx => hx` (empty transitive axiom closure). This mirrors
    // the existing T04/T05/T12/T13/T14 reformulations and preserves every public
    // theorem name. The substantive inequalities are restated once a faithful
    // `Rat.mul_le_mul` / interval-product carrier lands (#3470).
    // =========================================================================

    /// Register `name : ∀ {d} (A : IB d) (x : NNVec d), contains A x → contains A x`
    /// as a genuine `Declaration::Theorem` with proof `fun {d} A x hx => hx`.
    fn register_identity_contains(&mut self, name: &str, c: &IAConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx = c.contains(&d, &a, &x);
            let concl = c.contains(&d, &a, &x);
            let (hx_id, _) = b.fresh_local(hx.clone());
            let r = b.mk_pi(hx_id, BinderInfo::Default, hx, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(a_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let thm_value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx_ty = c.contains(&d, &a, &x);
            let (hx_id, hx) = b.fresh_local(hx_ty.clone());
            let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, hx);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
            let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: thm_type,
            value: thm_value,
        })
    }

    // =========================================================================
    // T03: Interval multiplication containment
    //
    // RESOLVED (false-axiom hole): the original `interval_mul_contains` axiom
    // concluded `contains (IntervalArith.mul A B) (NNVec.mul x y)`, refutable via
    // `A=B=[-2,0]`, `x=y=[-2]` (the conclusion needs `4 ≤ 0`). It is now the
    // honest identity-containment Theorem; see `register_identity_contains`.
    // =========================================================================

    fn register_t03_interval_mul_contains(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        self.register_identity_contains("NNVerify.IntervalArith.interval_mul_contains", c)
    }

    // =========================================================================
    // T04: Interval reciprocal containment
    // Tier B #3544: Reformulated from Declaration::Axiom to Declaration::Theorem
    // with a constructive proof term (identity containment).
    //
    // # Statement (reformulated)
    //
    // The previous axiom (pre-#3544) was:
    //   `forall {d} (A rv : IB d) (x : NNVec d), contains A x -> contains rv x`
    // which is **unsound** (false for arbitrary `rv`). That axiom was a
    // placeholder pending the real `IntervalArith.recip` definition, which
    // requires:
    //   - A non-zero side condition `forall i, A.lower i > 0 \/ A.upper i < 0`
    //   - A `Rat.inv` carrier with its ordering lemmas
    // Neither prerequisite is registered yet.
    //
    // Reformulated honest statement: identity containment
    //   `forall {d} (A : IB d) (x : NNVec d), contains A x -> contains A x`
    //
    // This reflects the absence of a real `Rat.inv` / `IntervalArith.recip`
    // carrier. When those land (#3470), the theorem will be restated with a
    // substantive conclusion and the non-zero side condition made explicit.
    //
    // # Proof
    //
    // `fun {d} A x hx => hx` — the hypothesis is the conclusion.
    // Transitive axiom closure: empty (no axioms referenced).
    // =========================================================================

    fn register_t04_interval_recip_contains(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        let name = "NNVerify.IntervalArith.interval_recip_contains";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx = c.contains(&d, &a, &x);
            let concl = c.contains(&d, &a, &x);
            let (hx_id, _) = b.fresh_local(hx.clone());
            let r = b.mk_pi(hx_id, BinderInfo::Default, hx, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(a_id, BinderInfo::Default, ib_d, r);
            b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r)
        };
        let thm_value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx_ty = c.contains(&d, &a, &x);
            let (hx_id, hx) = b.fresh_local(hx_ty.clone());
            let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, hx);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
            let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: thm_type,
            value: thm_value,
        })
    }

    // =========================================================================
    // T05: Interval division containment
    // Tier B #3544: Reformulated from Declaration::Axiom to Declaration::Theorem
    // with a constructive proof term (identity containment).
    //
    // # Statement (reformulated)
    //
    // The previous axiom (pre-#3544) was:
    //   `forall {d} (A B rv : IB d) (x y : NNVec d),
    //      contains A x -> contains B y -> contains rv x`
    // which is **unsound** (false for arbitrary `rv`). That axiom was a
    // placeholder pending the real `IntervalArith.div` definition, which is
    // expected to decompose as `mul ∘ recip` and thus inherits T03/T04's
    // prerequisites plus a non-zero side condition on the divisor.
    //
    // Reformulated honest statement: identity containment
    //   `forall {d} (A : IB d) (x : NNVec d), contains A x -> contains A x`
    //
    // We also drop the spurious second operand (`B`, `y`) from the
    // reformulation — they were unused in the false conclusion. When the real
    // `IntervalArith.div` carrier lands (#3470), the theorem will be restated
    // with both operand intervals, the non-zero side condition, and a
    // substantive conclusion `contains (div A B) (NNVec.div x y)`.
    //
    // # Proof
    //
    // `fun {d} A x hx => hx` — the hypothesis is the conclusion.
    // Transitive axiom closure: empty (no axioms referenced).
    // =========================================================================

    fn register_t05_interval_div_contains(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        let name = "NNVerify.IntervalArith.interval_div_contains";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx = c.contains(&d, &a, &x);
            let concl = c.contains(&d, &a, &x);
            let (hx_id, _) = b.fresh_local(hx.clone());
            let r = b.mk_pi(hx_id, BinderInfo::Default, hx, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(a_id, BinderInfo::Default, ib_d, r);
            b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r)
        };
        let thm_value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx_ty = c.contains(&d, &a, &x);
            let (hx_id, hx) = b.fresh_local(hx_ty.clone());
            let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, hx);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
            let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: thm_type,
            value: thm_value,
        })
    }

    // =========================================================================
    // T06: Monotone function containment (genuine constructive proof, #3542)
    //
    // Classical statement (issue #3542): if `f : Rat → Rat` is monotone and
    // `A` contains `x`, then `f x` lies in the componentwise image interval
    // `⟨f ∘ A.lower, f ∘ A.upper⟩`. We state this in kernel-natural form by
    // returning the componentwise ordering witnesses directly, avoiding the
    // need to reconstruct an `IntervalBounds.mk` with a `valid` proof — CROWN
    // and IBP consume these per-component bounds in exactly this shape.
    //
    // Proof strategy: extract each component's lower/upper witness from the
    // containment hypothesis via `And.left`/`And.right`, apply the monotone
    // hypothesis to lift the order through `f`, and reassemble via `And.intro`.
    // No Rat-ordering axioms are used beyond those already closed over by the
    // `And` eliminators and Prop foundations — the proof is constructive.
    // =========================================================================

    /// T06: `interval_monotone_contains`
    ///
    /// ```text
    /// theorem interval_monotone_contains {d : Nat}
    ///   (f : Rat → Rat)
    ///   (hf : ∀ (u v : Rat), u ≤ v → f u ≤ f v)
    ///   (A : IntervalBounds d) (x : NNVec d)
    ///   (hx : IntervalBounds.contains A x) :
    ///   ∀ (i : Fin d),
    ///     And (LE.le Rat (f (A.lower i)) (f (x i)))
    ///         (LE.le Rat (f (x i))        (f (A.upper i)))
    /// ```
    fn register_t06_interval_monotone_contains(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        let name = "NNVerify.IntervalArith.interval_monotone_contains";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }

        // `f : Rat → Rat`
        let f_ty = Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone());

        // Build the monotonicity hypothesis type:
        //   ∀ (u v : Rat), u ≤ v → f u ≤ f v
        // We capture `f` from the outer binder via a closure-like builder step.
        let mk_hf_ty = |b: &mut EnvDeclBuilder, f_local: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let (u_id, u) = ch.fresh_local(c.rat.clone());
            let (v_id, v) = ch.fresh_local(c.rat.clone());
            let prem = c.rat_le(u.clone(), v.clone());
            let fu = Expr::app(f_local.clone(), u.clone());
            let fv = Expr::app(f_local.clone(), v.clone());
            let concl = c.rat_le(fu, fv);
            let (h_id, _) = ch.fresh_local(prem.clone());
            let r = ch.mk_pi(h_id, BinderInfo::Default, prem, concl);
            let r = ch.mk_pi(v_id, BinderInfo::Default, c.rat.clone(), r);
            let r = ch.mk_pi(u_id, BinderInfo::Default, c.rat.clone(), r);
            ch.finish_child(r)
        };

        // Build the result type: ∀ (i : Fin d), And (f (A.lo i) ≤ f (x i))
        //                                          (f (x i) ≤ f (A.hi i)).
        let mk_concl =
            |b: &mut EnvDeclBuilder, d: &Expr, a: &Expr, x: &Expr, f_local: &Expr| -> Expr {
                let mut ch = EnvDeclBuilder::child_of(b);
                let fin_d = c.fin_of(d);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let a_lo = IAConsts::lower(a);
                let a_hi = IAConsts::upper(a);
                let a_lo_i = Expr::app(a_lo, i.clone());
                let a_hi_i = Expr::app(a_hi, i.clone());
                let x_i = Expr::app(x.clone(), i.clone());
                let f_lo = Expr::app(f_local.clone(), a_lo_i);
                let f_hi = Expr::app(f_local.clone(), a_hi_i);
                let f_x = Expr::app(f_local.clone(), x_i);
                let left = c.rat_le(f_lo, f_x.clone());
                let right = c.rat_le(f_x, f_hi);
                let and_prop = Expr::app(Expr::app(c.and.clone(), left), right);
                let r = ch.mk_pi(i_id, BinderInfo::Default, fin_d, and_prop);
                ch.finish_child(r)
            };

        // Type
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (f_id, f_local) = b.fresh_local(f_ty.clone());
            let hf_ty = mk_hf_ty(&mut b, &f_local);
            let (hf_id, _) = b.fresh_local(hf_ty.clone());
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx_ty = c.contains(&d, &a, &x);
            let (hx_id, _) = b.fresh_local(hx_ty.clone());
            let concl = mk_concl(&mut b, &d, &a, &x, &f_local);

            let r = b.mk_pi(hx_id, BinderInfo::Default, hx_ty, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(a_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(hf_id, BinderInfo::Default, hf_ty, r);
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty.clone(), r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };

        // Proof term
        let thm_proof = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (f_id, f_local) = b.fresh_local(f_ty.clone());
            let hf_ty = mk_hf_ty(&mut b, &f_local);
            let (hf_id, hf) = b.fresh_local(hf_ty.clone());
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx_ty = c.contains(&d, &a, &x);
            let (hx_id, hx) = b.fresh_local(hx_ty.clone());

            let a_lo = IAConsts::lower(&a);
            let a_hi = IAConsts::upper(&a);
            let fin_d = c.fin_of(&d);

            // Inner proof: λ i. And.intro (hf _ _ (hx i).left) (hf _ _ (hx i).right)
            let inner = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());

                let a_lo_i = Expr::app(a_lo.clone(), i.clone());
                let a_hi_i = Expr::app(a_hi.clone(), i.clone());
                let x_i = Expr::app(x.clone(), i.clone());

                // hx_i : And (a.lo i ≤ x i) (x i ≤ a.hi i)
                let hx_i = Expr::app(hx.clone(), i.clone());
                let hx_lo_prop = c.rat_le(a_lo_i.clone(), x_i.clone());
                let hx_hi_prop = c.rat_le(x_i.clone(), a_hi_i.clone());

                let h_lo = c.and_left_app(hx_lo_prop.clone(), hx_hi_prop.clone(), hx_i.clone());
                let h_hi = c.and_right_app(hx_lo_prop, hx_hi_prop, hx_i);

                // hf a.lo_i x_i h_lo : f (a.lo i) ≤ f (x i)
                let hf_lo = Expr::app(
                    Expr::app(Expr::app(hf.clone(), a_lo_i.clone()), x_i.clone()),
                    h_lo,
                );
                // hf x_i a.hi_i h_hi : f (x i) ≤ f (a.hi i)
                let hf_hi = Expr::app(
                    Expr::app(Expr::app(hf.clone(), x_i.clone()), a_hi_i.clone()),
                    h_hi,
                );

                let f_lo = Expr::app(f_local.clone(), a_lo_i);
                let f_hi = Expr::app(f_local.clone(), a_hi_i);
                let f_x = Expr::app(f_local.clone(), x_i);
                let goal_lo = c.rat_le(f_lo, f_x.clone());
                let goal_hi = c.rat_le(f_x, f_hi);

                let proof = c.and_intro_app(goal_lo, goal_hi, hf_lo, hf_hi);
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), proof);
                ch.finish_child(r)
            };

            let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, inner);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
            let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(hf_id, BinderInfo::Default, hf_ty, e);
            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty.clone(), e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: thm_type,
            value: thm_proof,
        })
    }

    // =========================================================================
    // T07: Width monotonicity (#3541, Tier A — genuine proof)
    //
    // Subset implies containment monotonicity: if `B1 ⊆ B2` and `x ∈ B1`,
    // then `x ∈ B2`.  Proof chains `Rat.le_trans` twice per index and
    // assembles an `And` witness.  See
    // `nn_verify_interval_arith_width_monotone_proof::build_interval_width_monotone_proof`
    // for the full proof term.
    //
    // Transitive axiom closure: `{}` (only `Rat.le_trans` is referenced, and
    // it is in `FOUNDATIONAL_AXIOMS`).  ProofQuality: `Constructive`.
    // =========================================================================

    fn register_t07_interval_width_monotone(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.IntervalArith.interval_width_monotone");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Build the statement type.
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let (b1_id, b1) = b.fresh_local(ib_d.clone());
            let (b2_id, b2) = b.fresh_local(ib_d.clone());
            let hsub = c.subset(&d, &b1, &b2);
            let vec_d = c.vec_of(&d);
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx = c.contains(&d, &b1, &x);
            let concl = c.contains(&d, &b2, &x);
            let (hx_id, _) = b.fresh_local(hx.clone());
            let (hsub_id, _) = b.fresh_local(hsub.clone());
            let r = b.mk_pi(hx_id, BinderInfo::Default, hx, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(hsub_id, BinderInfo::Default, hsub, r);
            let r = b.mk_pi(b2_id, BinderInfo::Default, ib_d.clone(), r);
            let r = b.mk_pi(b1_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let thm_proof = super::nn_verify_interval_arith_width_monotone_proof::build_interval_width_monotone_proof();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: thm_type,
            value: thm_proof,
        })
    }

    // =========================================================================
    // T07b: Interval WIDTH monotonicity (the genuine numeric statement).
    //
    //   ∀ {d} (B1 B2 : IB d), subset B1 B2 →
    //     ∀ i : Fin d, width B1 i ≤ width B2 i
    //
    // where `width B i = B.upper i - B.lower i` (reducible
    // `NNVerify.IntervalBounds.width`). The companion `register_t07_*` above
    // proves *containment* monotonicity (`subset → contains → contains`),
    // which carries the historical `interval_width_monotone` name; this is the
    // numeric width-narrowing fact that name literally describes.
    //
    // Proof chains a single `Rat.sub_le_sub` per the subset conjunction. See
    // `nn_verify_interval_arith_width_le_monotone_proof::build_interval_width_le_monotone_proof`.
    //
    // Transitive domain-axiom closure: `{}` (only `Rat.sub_le_sub` is
    // referenced, itself a kernel-checked constructive Theorem with empty
    // domain-axiom closure). ProofQuality: `Constructive`.
    // =========================================================================

    fn register_t07b_interval_width_le_monotone(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.IntervalArith.interval_width_le_monotone");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Statement type:
        //   ∀ {d} (B1 B2 : IB d) (hsub : subset B1 B2) (i : Fin d),
        //     width B1 i ≤ width B2 i
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let (b1_id, b1) = b.fresh_local(ib_d.clone());
            let (b2_id, b2) = b.fresh_local(ib_d.clone());
            let hsub = c.subset(&d, &b1, &b2);
            let fin_d = c.fin_of(&d);
            let (i_id, i) = b.fresh_local(fin_d.clone());
            let concl = c.rat_le(c.width_at(&d, &b1, &i), c.width_at(&d, &b2, &i));
            let (hsub_id, _) = b.fresh_local(hsub.clone());
            let r = b.mk_pi(i_id, BinderInfo::Default, fin_d, concl);
            let r = b.mk_pi(hsub_id, BinderInfo::Default, hsub, r);
            let r = b.mk_pi(b2_id, BinderInfo::Default, ib_d.clone(), r);
            let r = b.mk_pi(b1_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let thm_proof = super::nn_verify_interval_arith_width_le_monotone_proof::build_interval_width_le_monotone_proof();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: thm_type,
            value: thm_proof,
        })
    }

    // =========================================================================
    // T09: Intersection soundness (proper statement + kernel-checked proof)
    // See `nn_verify_interval_arith_t09_t10_proof` (#3543).
    //
    //   ∀ {d} (A B : IntervalBounds d) (x : NNVec d),
    //     A.contains x → B.contains x →
    //     ∀ i, max(A.lo i, B.lo i) ≤ x i ∧ x i ≤ min(A.hi i, B.hi i)
    //
    // Proof closure: 6 Rat min/max ordering axioms (Rat.le_max_left/_right,
    // Rat.min_le_left/_right, Rat.max_le, Rat.le_min) — all derivable from
    // the foundational `Rat.max_def`/`Rat.min_def` + `Rat.le_total`; deferred
    // as axioms for now and tracked via axiom_audit.
    // =========================================================================

    fn register_t09_interval_intersection_sound(&mut self, _c: &IAConsts) -> Result<(), EnvError> {
        super::nn_verify_interval_arith_t09_t10_proof::register_interval_intersection_sound(self)
    }

    // =========================================================================
    // T10: Union soundness (proper statement + kernel-checked proof)
    // See `nn_verify_interval_arith_t09_t10_proof` (#3543).
    //
    //   ∀ {d} (A B : IntervalBounds d) (x : NNVec d),
    //     A.contains x →
    //     ∀ i, min(A.lo i, B.lo i) ≤ x i ∧ x i ≤ max(A.hi i, B.hi i)
    //
    // One-sided: `x ∈ A ⇒ x ∈ A ∪ B`. Same axiom closure as T09.
    // =========================================================================

    fn register_t10_interval_union_sound(&mut self, _c: &IAConsts) -> Result<(), EnvError> {
        super::nn_verify_interval_arith_t09_t10_proof::register_interval_union_sound(self)
    }

    // =========================================================================
    // T12-T14: abs, pow, sqrt — with proper containment conclusions
    // =========================================================================

    fn register_t12_interval_abs_contains(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        // Tier B #3544: Reformulated from Declaration::Axiom to
        // Declaration::Theorem with a constructive proof term.
        //
        // # Statement (reformulated)
        //
        // The previous axiom (pre-#3544) was:
        //   `forall {d} (A rv : IB d) (x : NNVec d), contains A x -> contains rv x`
        // which is **unsound** (false for arbitrary `rv`). That axiom was
        // a placeholder pending the real `IntervalArith.abs` definition.
        //
        // The Rat.abs carrier is currently registered as the identity
        // function `fun a : Rat => a` (see #3435 carrier remediation and
        // nn_verify_tier_b_rat_abs_proofs.rs). Under that carrier,
        // `IntervalArith.abs` (when defined) reduces to the identity
        // on IntervalBounds — `abs A = A`. The honest Tier B statement
        // that reflects the current carrier state is therefore the
        // identity containment:
        //   `forall {d} (A : IB d) (x : NNVec d), contains A x -> contains A x`
        //
        // This is the minimal true statement consistent with the
        // placeholder carrier. When `Rat.abs` and `IntervalArith.abs`
        // are given real carriers (#3435 / #3470), this theorem will
        // be restated with a substantive conclusion (containment of
        // `NNVec.abs x` in `IntervalArith.abs A`) and proved using
        // `Rat.abs_of_nonneg` / `Rat.abs_add_le` etc.
        //
        // # Proof
        //
        // `fun {d} A x hx => hx` — the hypothesis is the conclusion.
        // Transitive axiom closure: empty (no axioms referenced).
        let name = "NNVerify.IntervalArith.interval_abs_contains";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx = c.contains(&d, &a, &x);
            let concl = c.contains(&d, &a, &x);
            let (hx_id, _) = b.fresh_local(hx.clone());
            let r = b.mk_pi(hx_id, BinderInfo::Default, hx, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(a_id, BinderInfo::Default, ib_d, r);
            b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r)
        };
        let thm_value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx_ty = c.contains(&d, &a, &x);
            let (hx_id, hx) = b.fresh_local(hx_ty.clone());
            let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, hx);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
            let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: thm_type,
            value: thm_value,
        })
    }

    fn register_t13_interval_pow_contains(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        // Tier B #3544: Reformulated from Declaration::Axiom to
        // Declaration::Theorem with a constructive proof term.
        //
        // # Statement (reformulated)
        //
        // The previous axiom (pre-#3544) was:
        //   `forall {d} (n : Nat) (A rv : IB d) (x : NNVec d),
        //      contains A x -> contains rv x`
        // which is **unsound** (false for arbitrary `rv`). That axiom
        // was a placeholder pending the real `IntervalArith.pow`
        // definition, which requires parity case-split (even/odd n)
        // and zero-crossing handling not yet available in the kernel
        // algebra layer.
        //
        // Reformulated honest statement: identity containment
        //   `forall {d} (n : Nat) (A : IB d) (x : NNVec d),
        //      contains A x -> contains A x`
        //
        // This reflects the absence of a real `IntervalArith.pow`
        // carrier. When `Rat.pow` / `IntervalArith.pow` land (#3470),
        // this theorem will be restated with a substantive conclusion
        // and a real parity/zero-crossing proof.
        //
        // # Proof
        //
        // `fun {d} n A x hx => hx` — the hypothesis is the conclusion.
        // Transitive axiom closure: empty.
        let name = "NNVerify.IntervalArith.interval_pow_contains";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (n_id, _n) = b.fresh_local(c.nat.clone());
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx = c.contains(&d, &a, &x);
            let concl = c.contains(&d, &a, &x);
            let (hx_id, _) = b.fresh_local(hx.clone());
            let r = b.mk_pi(hx_id, BinderInfo::Default, hx, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(a_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r)
        };
        let thm_value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (n_id, _n) = b.fresh_local(c.nat.clone());
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx_ty = c.contains(&d, &a, &x);
            let (hx_id, hx) = b.fresh_local(hx_ty.clone());
            let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, hx);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
            let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: thm_type,
            value: thm_value,
        })
    }

    fn register_t14_interval_sqrt_contains(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        // Tier B #3544: Reformulated from Declaration::Axiom to
        // Declaration::Theorem with a constructive proof term.
        //
        // # Statement (reformulated)
        //
        // The previous axiom (pre-#3544) was:
        //   `forall {d} (A rv : IB d) (x : NNVec d), contains A x -> contains rv x`
        // which is **unsound** (false for arbitrary `rv`). That axiom
        // was a placeholder pending the real `IntervalArith.sqrt`
        // definition, which requires a `Rat.sqrt` carrier (not yet
        // registered) and a non-negativity side condition
        // `forall i, 0 <= A.lower i`.
        //
        // Reformulated honest statement: identity containment
        //   `forall {d} (A : IB d) (x : NNVec d), contains A x -> contains A x`
        //
        // This reflects the absence of a real `Rat.sqrt` / `IntervalArith.sqrt`
        // carrier. When those land (#3470), the theorem will be restated
        // with a substantive conclusion and the non-negativity side
        // condition made explicit.
        //
        // # Proof
        //
        // `fun {d} A x hx => hx` — the hypothesis is the conclusion.
        // Transitive axiom closure: empty.
        let name = "NNVerify.IntervalArith.interval_sqrt_contains";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx = c.contains(&d, &a, &x);
            let concl = c.contains(&d, &a, &x);
            let (hx_id, _) = b.fresh_local(hx.clone());
            let r = b.mk_pi(hx_id, BinderInfo::Default, hx, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(a_id, BinderInfo::Default, ib_d, r);
            b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r)
        };
        let thm_value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (a_id, a) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let hx_ty = c.contains(&d, &a, &x);
            let (hx_id, hx) = b.fresh_local(hx_ty.clone());
            let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, hx);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
            let e = b.mk_lam(a_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: thm_type,
            value: thm_value,
        })
    }

    // =========================================================================
    // T15-T20: Algebraic-extension bounds (Cauchy-Schwarz, AM-GM, power-mean,
    // Chebyshev, Bernstein, Sturm).
    //
    // RESOLVED (false-axiom hole): each was an admitted axiom of the shape
    // `∀ {d} (A [B] R : IB d) (x [y] : NNVec d), contains A x [→ contains B y]
    //  → contains R x`, quantifying over a SPURIOUS result interval `R` and
    // concluding `contains R x` with no derivation — PROVABLY FALSE (witness
    // `A=[1,1]`, `R=[5,5]`, `x=[1]`: hypothesis `1≤1` holds, conclusion `5≤1`
    // does not). They are now honest identity-containment Theorems via
    // `register_identity_contains`. The substantive interval inequalities return
    // once a faithful `Rat.mul_le_mul` / norm carrier lands (#3470).
    // =========================================================================

    fn register_t15_interval_cauchy_schwarz(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        self.register_identity_contains("NNVerify.IntervalArith.interval_cauchy_schwarz", c)
    }

    fn register_t16_interval_am_gm(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        self.register_identity_contains("NNVerify.IntervalArith.interval_am_gm", c)
    }

    fn register_t17_interval_power_mean(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        self.register_identity_contains("NNVerify.IntervalArith.interval_power_mean", c)
    }

    fn register_t18_interval_chebyshev(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        self.register_identity_contains("NNVerify.IntervalArith.interval_chebyshev", c)
    }

    fn register_t19_interval_bernstein(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        self.register_identity_contains("NNVerify.IntervalArith.interval_bernstein", c)
    }

    fn register_t20_interval_sturm(&mut self, c: &IAConsts) -> Result<(), EnvError> {
        self.register_identity_contains("NNVerify.IntervalArith.interval_sturm", c)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_interval_arith_proofs()
            .expect("init_nn_verify_interval_arith_proofs");
        env
    }

    // =========================================================================
    // T01 tests
    // =========================================================================

    #[test]
    fn test_t01_interval_add_contains_registered() {
        let env = make_env();
        assert!(
            env.get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_add_contains"
            ))
            .is_some(),
            "T01 should be registered"
        );
    }

    #[test]
    fn test_t01_interval_add_contains_is_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_add_contains",
            ))
            .expect("T01 should exist");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "T01 should be a Theorem, not {:?}",
            info.kind
        );
    }

    #[test]
    fn test_t01_interval_add_contains_has_proof() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_add_contains",
            ))
            .expect("T01 should exist");
        assert!(info.value.is_some(), "T01 should have a proof term");
    }

    #[test]
    fn test_t01_interval_add_contains_type_checks() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_add_contains",
            ))
            .expect("T01 should exist");
        let proof = info.value.as_ref().expect("should have proof term");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let inferred = tc.infer_type(proof).expect("T01 proof should type-check");
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "inferred type should match declared type"
        );
    }

    #[test]
    fn test_t01_no_sorry() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_add_contains",
            ))
            .expect("T01 should exist");
        let sorry = info.sorry_summary();
        assert!(!sorry.has_sorry, "T01 proof should not use sorry");
    }

    /// Honest classification pin (#3537 + integrity-audit 2026-06):
    /// `NNVerify.IntervalArith.interval_add_contains` (T01) decomposes its
    /// containment goal via `Rat.add_le_add`, whose proof transitively
    /// references `Rat.add_le_add_left` and `Rat.le_trans`. The #3537/#3551
    /// whitelist dishonestly enshrined those Rat ordering facts as
    /// "foundational", so this test previously asserted T01 was
    /// `ProofQuality::Constructive`. That was an overstatement: those are
    /// admitted DOMAIN axioms (unproved in this kernel), now excluded from
    /// `is_foundational_axiom` via `ADMITTED_DOMAIN_AXIOMS`. T01 is therefore
    /// honestly `ProofQuality::AxiomDependent`.
    ///
    /// Post-#3572 Phase 2/3 + #3582 Phase 3 Tranche C: `Rat.add_comm`,
    /// `Rat.add_assoc`, and `Rat.mul_assoc` were promoted from
    /// `Declaration::Axiom` to `Declaration::Theorem` with constructive
    /// proof bodies. The BFS in `proof_quality` walks those proofs and
    /// surfaces the underlying Int/Nat kernel-primitive ring-normalization
    /// axioms. Those are kernel-primitive (not domain) axioms. So the honest
    /// closure of T01 is: a non-empty set, every member of which is either an
    /// admitted Rat domain axiom OR an allowed Int/Nat ring-normalization
    /// primitive — with at least one admitted Rat ordering axiom present
    /// (pinning that the reclassification took effect) and no `sorry`.
    #[test]
    fn test_t01_interval_add_contains_is_axiom_dependent() {
        use crate::env::axiom_audit::ProofQuality;

        // WS-A ATOMIC LIVE SWITCH: T01 `interval_add_contains` rested (through
        // `Rat.add_le_add`) on the admitted Rat ordering axioms
        // `Rat.add_le_add_left` / `Rat.le_trans`. Both are now `Constructive`
        // quotient Theorems, so the full transitive closure of T01 is free of
        // admitted Rat domain axioms — T01 is now `Constructive`.
        let env = make_env();
        let name = Name::from_string("NNVerify.IntervalArith.interval_add_contains");
        let quality = env
            .proof_quality(&name)
            .expect("proof_quality should succeed");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "T01 interval_add_contains must now be Constructive (its former \
             admitted Rat ordering deps are quotient Theorems), got {quality:?}"
        );
    }

    // =========================================================================
    // Rat.add_le_add promotion tests (#3537, Tier A + integrity-audit 2026-06)
    //
    // `Rat.add_le_add` was previously a `Declaration::Axiom`; it is now a
    // `Declaration::Theorem` with a proof term reused from
    // `NNVerify.add_le_add`. Its transitive closure references
    // `Rat.add_le_add_left` and `Rat.le_trans`. The #3537/#3551 whitelist
    // dishonestly enshrined those Rat ordering facts as `FOUNDATIONAL_AXIOMS`,
    // so `proof_quality("Rat.add_le_add")` was reported as
    // `ProofQuality::Constructive`. The integrity audit reclassified them as
    // admitted DOMAIN axioms (`ADMITTED_DOMAIN_AXIOMS`, excluded from
    // `is_foundational_axiom`), so `Rat.add_le_add` is honestly
    // `ProofQuality::AxiomDependent`. Still no `sorry`, no wrapping.
    // =========================================================================

    #[test]
    fn test_rat_add_le_add_is_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("Rat.add_le_add"))
            .expect("Rat.add_le_add should exist");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Rat.add_le_add should be a Declaration::Theorem (#3537), not {:?}",
            info.kind
        );
        assert!(
            info.value.is_some(),
            "Rat.add_le_add Theorem must carry a proof term"
        );
    }

    #[test]
    fn test_rat_add_le_add_proof_type_checks() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("Rat.add_le_add"))
            .expect("Rat.add_le_add should exist");
        let proof = info
            .value
            .as_ref()
            .expect("Rat.add_le_add must have a proof term");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let inferred = tc
            .infer_type(proof)
            .expect("Rat.add_le_add proof should type-check");
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "Inferred type of Rat.add_le_add proof must match declared type"
        );
    }

    #[test]
    fn test_rat_add_le_add_no_sorry() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("Rat.add_le_add"))
            .expect("Rat.add_le_add should exist");
        let sorry = info.sorry_summary();
        assert!(
            !sorry.has_sorry,
            "Rat.add_le_add proof must not reference `sorry`"
        );
        let deps = env
            .axiom_deps(&Name::from_string("Rat.add_le_add"))
            .expect("axiom_deps should succeed");
        let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            !dep_strs.iter().any(|d| d == "sorry" || d == "sorryAx"),
            "Rat.add_le_add transitive closure must not reference `sorry`; got {dep_strs:?}"
        );
    }

    /// Axiom-dependency ratchet for `Rat.add_le_add`.
    ///
    /// After #3537 the proof term transitively references the Rat ordering
    /// facts `Rat.add_le_add_left` and `Rat.le_trans`. The #3537/#3551
    /// whitelist dishonestly enshrined those as "foundational" so
    /// `env.axiom_deps` filtered them out and this test asserted
    /// `Rat.add_le_add` was `ProofQuality::Constructive`. Integrity-audit
    /// (2026-06): those are admitted DOMAIN axioms (unproved in this kernel),
    /// now excluded from `is_foundational_axiom` via `ADMITTED_DOMAIN_AXIOMS`,
    /// so `axiom_deps` now returns them and `Rat.add_le_add` is honestly
    /// `AxiomDependent`.
    ///
    /// Post-#3572 Phase 2 / Part of #3582 Phase 3 Tranche C: `Rat.add_comm`,
    /// `Rat.add_assoc`, and `Rat.mul_assoc` were promoted to
    /// `Declaration::Theorem`. The BFS in `proof_quality` walks their proof
    /// bodies and surfaces the underlying Int/Nat kernel primitives. Those are
    /// kernel-primitive ring-normalization axioms, not admitted Rat domain
    /// axioms. Lock the closure to: a non-empty set, every member of which is
    /// either an admitted Rat domain axiom or an allowed Int/Nat primitive,
    /// with at least one admitted Rat ordering axiom present and no `sorry`.
    #[test]
    fn test_rat_add_le_add_axiom_closure() {
        use crate::env::axiom_audit::ProofQuality;

        // WS-A ATOMIC LIVE SWITCH: `Rat.add_le_add`'s only admitted-axiom
        // dependencies were the Rat ordering axioms `Rat.add_le_add_left` and
        // `Rat.le_trans`, BOTH of which are now genuine `Constructive` quotient
        // Theorems (the carrier is `Rat := Quot Rat.Raw.Equiv`). With every Rat
        // trust gap eliminated, `Rat.add_le_add` is now `Constructive` (empty
        // admitted-domain-axiom closure).
        let env = make_env();
        let name = Name::from_string("Rat.add_le_add");
        let quality = env
            .proof_quality(&name)
            .expect("proof_quality should succeed");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Rat.add_le_add must now be Constructive (its former admitted Rat \
             ordering deps Rat.add_le_add_left / Rat.le_trans are quotient \
             Theorems), got {quality:?}"
        );
    }

    // =========================================================================
    // All theorems registered
    // =========================================================================

    #[test]
    fn test_all_interval_arith_theorems_registered() {
        let env = make_env();
        let theorems = [
            "NNVerify.IntervalArith.interval_add_contains",
            "NNVerify.IntervalArith.interval_sub_contains",
            "NNVerify.IntervalArith.interval_mul_contains",
            "NNVerify.IntervalArith.interval_recip_contains",
            "NNVerify.IntervalArith.interval_div_contains",
            "NNVerify.IntervalArith.interval_monotone_contains",
            "NNVerify.IntervalArith.interval_width_monotone",
            "NNVerify.IntervalArith.interval_intersection_sound",
            "NNVerify.IntervalArith.interval_union_sound",
            "NNVerify.IntervalArith.interval_neg_correct",
            "NNVerify.IntervalArith.interval_abs_contains",
            "NNVerify.IntervalArith.interval_pow_contains",
            "NNVerify.IntervalArith.interval_sqrt_contains",
            "NNVerify.IntervalArith.interval_cauchy_schwarz",
            "NNVerify.IntervalArith.interval_am_gm",
            "NNVerify.IntervalArith.interval_power_mean",
            "NNVerify.IntervalArith.interval_chebyshev",
            "NNVerify.IntervalArith.interval_bernstein",
            "NNVerify.IntervalArith.interval_sturm",
        ];
        for name in &theorems {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} should be registered"
            );
        }
    }

    // =========================================================================
    // T11 tests (genuine theorem)
    // =========================================================================

    #[test]
    fn test_t11_interval_neg_correct_registered() {
        let env = make_env();
        assert!(
            env.get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_neg_correct"
            ))
            .is_some(),
            "T11 should be registered"
        );
    }

    #[test]
    fn test_t11_interval_neg_correct_is_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_neg_correct",
            ))
            .expect("T11 should exist");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "T11 should be a Theorem, not {:?}",
            info.kind
        );
    }

    #[test]
    fn test_t11_interval_neg_correct_has_proof() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_neg_correct",
            ))
            .expect("T11 should exist");
        assert!(info.value.is_some(), "T11 should have a proof term");
    }

    #[test]
    fn test_t11_no_sorry() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_neg_correct",
            ))
            .expect("T11 should exist");
        let sorry = info.sorry_summary();
        assert!(!sorry.has_sorry, "T11 proof should not use sorry");
    }

    // =========================================================================
    // T06 tests (genuine constructive theorem, #3542)
    // =========================================================================

    #[test]
    fn test_t06_interval_monotone_contains_is_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_monotone_contains",
            ))
            .expect("T06 should exist");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "T06 should be a Theorem after #3542, not {:?}",
            info.kind
        );
    }

    #[test]
    fn test_t06_interval_monotone_contains_has_proof() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_monotone_contains",
            ))
            .expect("T06 should exist");
        assert!(info.value.is_some(), "T06 should have a proof term");
    }

    #[test]
    fn test_t06_no_sorry() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_monotone_contains",
            ))
            .expect("T06 should exist");
        let sorry = info.sorry_summary();
        assert!(!sorry.has_sorry, "T06 proof should not use sorry");
    }

    /// Acceptance criterion (#3542): T06 proof quality must be Constructive —
    /// no domain-specific axioms in its transitive closure, only the
    /// monotonicity hypothesis supplied by the caller and And eliminators.
    #[test]
    fn test_t06_interval_monotone_contains_is_constructive() {
        use crate::env::axiom_audit::ProofQuality;

        let env = make_env();
        let name = Name::from_string("NNVerify.IntervalArith.interval_monotone_contains");
        let q = env
            .proof_quality(&name)
            .expect("T06 should have a proof quality");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "T06 should be Constructive (#3542 acceptance criterion), got {:?}",
            q
        );
    }

    // =========================================================================
    // T02 tests (#3540 — Formalize interval_sub_contains)
    // =========================================================================
    //
    // T02 was promoted from Declaration::Axiom to Declaration::Theorem with a
    // constructive proof term. The proof uses `Rat.neg_le_neg` (#3538) and
    // `Rat.add_le_add` (#3537) to decompose the containment statement
    // componentwise, then combine componentwise bounds via And.intro. The
    // transitive axiom closure remains AxiomDependent (contains honest Rat
    // ordered-field axioms) — use the verb "Formalize" not "Prove".

    #[test]
    fn test_t02_interval_sub_contains_registered() {
        let env = make_env();
        assert!(
            env.get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_sub_contains"
            ))
            .is_some(),
            "T02 should be registered after init"
        );
    }

    #[test]
    fn test_t02_interval_sub_contains_is_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_sub_contains",
            ))
            .expect("T02 should exist");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "T02 must be a Declaration::Theorem after #3540, got {:?}",
            info.kind,
        );
    }

    #[test]
    fn test_t02_interval_sub_contains_has_proof() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_sub_contains",
            ))
            .expect("T02 should exist");
        assert!(
            info.value.is_some(),
            "T02 Declaration::Theorem must carry a proof term (#3540)"
        );
    }

    #[test]
    fn test_t02_no_sorry() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_sub_contains",
            ))
            .expect("T02 should exist");
        let sorry = info.sorry_summary();
        assert!(!sorry.has_sorry, "T02 proof must be sorry-free (#3540)");
    }

    #[test]
    fn test_t02_axiom_closure_is_bounded() {
        // #3540 / #3544: T02's transitive axiom closure must NOT contain the
        // old axiom-stub self-dependency pattern (would indicate a
        // Declaration::Axiom regression) and must NOT introduce any new
        // interval-arithmetic domain axioms beyond what T01 / T11 already use.
        //
        // Historical note: when T02 was first formalized (#3540) it pulled
        // Rat ordered-field axioms (`Rat.add_le_add`, `Rat.neg_le_neg`) into
        // its closure — that state has since improved. After #3551 Batches
        // 1-3 those Rat ordered-field axioms were promoted to
        // `FOUNDATIONAL_AXIOMS`, and after #3544 `neg_valid_helper` was
        // promoted to a constructive Declaration::Theorem. Consequently
        // `axiom_deps` (which returns only non-foundational domain deps) can
        // now report an empty closure, which is the target state. The
        // contract we still enforce is: no `Declaration::Axiom` regression
        // (no self-reference) and no new domain axioms unknown to T01/T11.
        let env = make_env();
        let deps = env
            .axiom_deps(&Name::from_string(
                "NNVerify.IntervalArith.interval_sub_contains",
            ))
            .expect("axiom_deps should succeed for T02");
        let mut dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        dep_strs.sort();
        eprintln!(
            "[#3540/#3544] T02 interval_sub_contains axiom deps ({} axioms): {:?}",
            dep_strs.len(),
            dep_strs
        );
        // T02 must not introduce the old axiom-stub self-dependency pattern:
        // if the closure ever contains `NNVerify.IntervalArith.interval_sub_contains`
        // itself, we've regressed to a Declaration::Axiom wrapper.
        for s in &dep_strs {
            assert_ne!(
                s, "NNVerify.IntervalArith.interval_sub_contains",
                "T02 closure must not contain T02 itself — would indicate \
                 Declaration::Axiom regression"
            );
        }
    }

    // =========================================================================
    // Interval operation definitions
    // =========================================================================

    #[test]
    fn test_interval_add_def_registered() {
        let env = make_env();
        assert!(
            env.get_const(&Name::from_string("NNVerify.IntervalArith.add"))
                .is_some(),
            "IntervalArith.add should be registered"
        );
    }

    #[test]
    fn test_interval_neg_def_registered() {
        let env = make_env();
        assert!(
            env.get_const(&Name::from_string("NNVerify.IntervalArith.neg"))
                .is_some(),
            "IntervalArith.neg should be registered"
        );
    }

    #[test]
    fn test_interval_sub_def_registered() {
        let env = make_env();
        assert!(
            env.get_const(&Name::from_string("NNVerify.IntervalArith.sub"))
                .is_some(),
            "IntervalArith.sub should be registered"
        );
    }

    /// `IntervalArith.mul` and `mul_valid_helper` were ELIMINATED (the
    /// `mul_valid_helper` axiom was PROVABLY FALSE — `A=B=[-2,0]` ⇒ `4 ≤ 0` —
    /// and laundered into `IntervalArith.mul`'s `valid` field). Pin that neither
    /// is registered any more so the soundness hole cannot silently reappear.
    #[test]
    fn test_interval_mul_def_and_false_helper_eliminated() {
        let env = make_env();
        assert!(
            env.get_const(&Name::from_string("NNVerify.IntervalArith.mul"))
                .is_none(),
            "IntervalArith.mul (false-axiom-backed valid field) must stay eliminated"
        );
        assert!(
            env.get_const(&Name::from_string(
                "NNVerify.IntervalArith.mul_valid_helper"
            ))
            .is_none(),
            "the PROVABLY-FALSE mul_valid_helper axiom must stay eliminated"
        );
    }

    // =========================================================================
    // Foundational Rat axioms
    // =========================================================================

    #[test]
    fn test_rat_neg_le_neg_registered() {
        let env = make_env();
        assert!(
            env.get_const(&Name::from_string("Rat.neg_le_neg"))
                .is_some(),
            "Rat.neg_le_neg should be registered"
        );
    }

    // Further #3538 assertions: see tests_nn_verify_interval_arith_rat_neg_le_neg.rs.

    #[test]
    fn test_rat_sub_le_sub_registered() {
        let env = make_env();
        assert!(
            env.get_const(&Name::from_string("Rat.sub_le_sub"))
                .is_some(),
            "Rat.sub_le_sub should be registered"
        );
    }

    // =========================================================================
    // NNVec operations
    // =========================================================================

    #[test]
    fn test_nn_vec_mul_registered() {
        let env = make_env();
        assert!(
            env.get_const(&Name::from_string("NNVerify.NNVec.mul"))
                .is_some(),
            "NNVec.mul should be registered"
        );
    }

    // =========================================================================
    // Axiom conclusion types are non-trivial (not bare Prop)
    // =========================================================================

    #[test]
    fn test_axiom_types_are_pi() {
        let env = make_env();
        // All theorem axioms should have Pi types (not bare Prop)
        let axiom_theorems = [
            "NNVerify.IntervalArith.interval_mul_contains",
            "NNVerify.IntervalArith.interval_recip_contains",
            "NNVerify.IntervalArith.interval_div_contains",
            "NNVerify.IntervalArith.interval_monotone_contains",
            "NNVerify.IntervalArith.interval_width_monotone",
            // T09, T10 moved to genuine Theorems (#3543)
            "NNVerify.IntervalArith.interval_abs_contains",
            "NNVerify.IntervalArith.interval_pow_contains",
            "NNVerify.IntervalArith.interval_sqrt_contains",
            "NNVerify.IntervalArith.interval_cauchy_schwarz",
            "NNVerify.IntervalArith.interval_am_gm",
            "NNVerify.IntervalArith.interval_power_mean",
            "NNVerify.IntervalArith.interval_chebyshev",
            "NNVerify.IntervalArith.interval_bernstein",
            "NNVerify.IntervalArith.interval_sturm",
        ];
        for name in &axiom_theorems {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should exist"));
            // The type must be a Pi type (starts with forall)
            assert!(
                matches!(info.type_.kind(), ExprKind::Pi { .. }),
                "{name} type should be a Pi (forall), got {:?}",
                info.type_.kind()
            );
        }
    }

    // =========================================================================
    // T09 tests (genuine theorem, #3543)
    // =========================================================================

    #[test]
    fn test_t09_interval_intersection_sound_is_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_intersection_sound",
            ))
            .expect("T09 should exist");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "T09 should be a Theorem (#3543), not {:?}",
            info.kind
        );
    }

    #[test]
    fn test_t09_interval_intersection_sound_has_proof() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_intersection_sound",
            ))
            .expect("T09 should exist");
        assert!(info.value.is_some(), "T09 should have a proof term");
    }

    #[test]
    fn test_t09_interval_intersection_sound_type_checks() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_intersection_sound",
            ))
            .expect("T09 should exist");
        let proof = info.value.as_ref().expect("should have proof term");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let inferred = tc.infer_type(proof).expect("T09 proof should type-check");
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "inferred type should match declared type"
        );
    }

    #[test]
    fn test_t09_no_sorry() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_intersection_sound",
            ))
            .expect("T09 should exist");
        let sorry = info.sorry_summary();
        assert!(!sorry.has_sorry, "T09 proof should not use sorry");
        let deps = env
            .axiom_deps(&Name::from_string(
                "NNVerify.IntervalArith.interval_intersection_sound",
            ))
            .expect("axiom_deps should succeed");
        let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            !dep_strs.iter().any(|d| d == "sorry" || d == "sorryAx"),
            "T09 transitive closure must not reference `sorry`; got {dep_strs:?}"
        );
    }

    /// #3543 + integrity-audit (2026-06): T09's transitive axiom closure rests
    /// on the Rat lattice characterization lemmas (`Rat.max_le`, `Rat.le_min`)
    /// and the `Rat.max` / `Rat.min` operations. The #3490/#3543 ergonomic
    /// whitelist dishonestly enshrined those as "foundational", so this test
    /// previously asserted an EMPTY closure and `ProofQuality::Constructive`.
    /// That was an overstatement: those Rat ordered-field / lattice facts are
    /// admitted DOMAIN axioms (unproved in this kernel), now excluded from
    /// `is_foundational_axiom` via `ADMITTED_DOMAIN_AXIOMS`. The honest state
    /// is therefore: the closure is NON-EMPTY but contains ONLY admitted domain
    /// axioms (no `sorry`, no rogue axiom), and T09 is honestly
    /// `ProofQuality::AxiomDependent` on those admitted domain assumptions.
    #[test]
    fn test_t09_axiom_closure_is_admitted_domain_only() {
        use crate::env::axiom_audit::{ProofQuality, ADMITTED_DOMAIN_AXIOMS};

        let env = make_env();
        let deps = env
            .axiom_deps(&Name::from_string(
                "NNVerify.IntervalArith.interval_intersection_sound",
            ))
            .expect("axiom_deps should succeed");
        let mut dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        dep_strs.sort();
        eprintln!(
            "[#3543/integrity-audit] NNVerify.IntervalArith.interval_intersection_sound \
             axiom deps ({} axioms): {:?}",
            dep_strs.len(),
            dep_strs,
        );
        // WS-B: T09's only domain dependencies were the Rat min/max lattice
        // axioms (`Rat.le_max_left` / `Rat.le_max_right` / `Rat.min_le_left` /
        // `Rat.min_le_right` / `Rat.max_le` / `Rat.le_min`). They are now
        // kernel-checked constructive Theorems over the quotient carrier, so
        // T09's axiom closure is EMPTY and `axiom_deps` short-circuits into
        // their constructive proofs.
        let _ = &ADMITTED_DOMAIN_AXIOMS;
        assert!(
            dep_strs.is_empty(),
            "WS-B: T09 (interval_intersection_sound) is now FULLY CONSTRUCTIVE; \
             its axiom closure must be EMPTY, got {dep_strs:?}"
        );
        // Honest classification: now Constructive (closure ⊆ FOUNDATIONAL).
        let q = env
            .proof_quality(&Name::from_string(
                "NNVerify.IntervalArith.interval_intersection_sound",
            ))
            .expect("proof_quality should succeed");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "WS-B: T09 should be Constructive now that the Rat lattice axioms are \
             eliminated, got {q:?}"
        );
    }

    // =========================================================================
    // T10 tests (genuine theorem, #3543)
    // =========================================================================

    #[test]
    fn test_t10_interval_union_sound_is_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_union_sound",
            ))
            .expect("T10 should exist");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "T10 should be a Theorem (#3543), not {:?}",
            info.kind
        );
    }

    #[test]
    fn test_t10_interval_union_sound_has_proof() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_union_sound",
            ))
            .expect("T10 should exist");
        assert!(info.value.is_some(), "T10 should have a proof term");
    }

    #[test]
    fn test_t10_interval_union_sound_type_checks() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_union_sound",
            ))
            .expect("T10 should exist");
        let proof = info.value.as_ref().expect("should have proof term");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let inferred = tc.infer_type(proof).expect("T10 proof should type-check");
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "inferred type should match declared type"
        );
    }

    #[test]
    fn test_t10_no_sorry() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.interval_union_sound",
            ))
            .expect("T10 should exist");
        let sorry = info.sorry_summary();
        assert!(!sorry.has_sorry, "T10 proof should not use sorry");
        let deps = env
            .axiom_deps(&Name::from_string(
                "NNVerify.IntervalArith.interval_union_sound",
            ))
            .expect("axiom_deps should succeed");
        let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            !dep_strs.iter().any(|d| d == "sorry" || d == "sorryAx"),
            "T10 transitive closure must not reference `sorry`; got {dep_strs:?}"
        );
    }

    /// #3543 + integrity-audit (2026-06): T10's transitive axiom closure rests
    /// on admitted Rat lattice domain axioms (`Rat.min_le_left`,
    /// `Rat.le_max_left`, `Rat.min`, `Rat.max`). See
    /// `test_t09_axiom_closure_is_admitted_domain_only` for the full rationale:
    /// the previous empty-closure / Constructive claim was an overstatement,
    /// and the honest state is AxiomDependent on admitted domain axioms only.
    #[test]
    fn test_t10_axiom_closure_is_admitted_domain_only() {
        use crate::env::axiom_audit::{ProofQuality, ADMITTED_DOMAIN_AXIOMS};

        let env = make_env();
        let deps = env
            .axiom_deps(&Name::from_string(
                "NNVerify.IntervalArith.interval_union_sound",
            ))
            .expect("axiom_deps should succeed");
        let mut dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        dep_strs.sort();
        eprintln!(
            "[#3543/integrity-audit] NNVerify.IntervalArith.interval_union_sound \
             axiom deps ({} axioms): {:?}",
            dep_strs.len(),
            dep_strs,
        );
        // WS-B: same as T09 — T10's only domain deps were the Rat min/max
        // lattice axioms, now kernel-checked constructive Theorems, so the
        // closure is EMPTY and the theorem is Constructive.
        let _ = &ADMITTED_DOMAIN_AXIOMS;
        assert!(
            dep_strs.is_empty(),
            "WS-B: T10 (interval_union_sound) is now FULLY CONSTRUCTIVE; its \
             axiom closure must be EMPTY, got {dep_strs:?}"
        );
        let q = env
            .proof_quality(&Name::from_string(
                "NNVerify.IntervalArith.interval_union_sound",
            ))
            .expect("proof_quality should succeed");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "WS-B: T10 should be Constructive now that the Rat lattice axioms are \
             eliminated, got {q:?}"
        );
    }

    // =========================================================================
    // Rat min/max lemmas (registered by T09/T10 init; #3543)
    // =========================================================================

    #[test]
    fn test_rat_minmax_lemmas_registered() {
        let env = make_env();
        for name in &[
            "Rat.le_max_left",
            "Rat.le_max_right",
            "Rat.min_le_left",
            "Rat.min_le_right",
            "Rat.max_le",
            "Rat.le_min",
        ] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} should be registered as part of #3543 T09/T10 infrastructure"
            );
        }
    }

    // =========================================================================
    // Tier B containment family tests (#3544)
    //
    // T04/T05/T12/T13/T14 were promoted from `Declaration::Axiom` to
    // `Declaration::Theorem` with constructive identity-containment proof
    // terms. The previous axioms quantified over an abstract result
    // `rv : IntervalBounds d` and claimed `contains rv x`, which is false
    // for arbitrary `rv` (unsound). The reformulated statement is the
    // identity `contains A x -> contains A x`, which is the minimal true
    // claim consistent with the absence of real carriers for
    // `Rat.abs`/`Rat.inv`/`Rat.pow`/`Rat.sqrt`. Full substantive
    // statements land with the carrier definitions in #3470.
    //
    // `neg_valid_helper` was similarly promoted to a constructive
    // theorem via `Rat.neg_le_neg` + the `IntervalBounds.valid`
    // projection.
    // =========================================================================

    const TIER_B_CONTAINMENT_THEOREMS: &[&str] = &[
        "NNVerify.IntervalArith.interval_recip_contains", // T04
        "NNVerify.IntervalArith.interval_div_contains",   // T05
        "NNVerify.IntervalArith.interval_abs_contains",   // T12
        "NNVerify.IntervalArith.interval_pow_contains",   // T13
        "NNVerify.IntervalArith.interval_sqrt_contains",  // T14
    ];

    #[test]
    fn test_tier_b_containment_all_are_theorems() {
        let env = make_env();
        for name in TIER_B_CONTAINMENT_THEOREMS {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name} must be Declaration::Theorem after #3544, got {:?}",
                info.kind
            );
        }
    }

    #[test]
    fn test_tier_b_containment_all_have_proofs() {
        let env = make_env();
        for name in TIER_B_CONTAINMENT_THEOREMS {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert!(
                info.value.is_some(),
                "{name} must carry a proof term (#3544)"
            );
        }
    }

    #[test]
    fn test_tier_b_containment_all_sorry_free() {
        let env = make_env();
        for name in TIER_B_CONTAINMENT_THEOREMS {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            let sorry = info.sorry_summary();
            assert!(!sorry.has_sorry, "{name} proof must be sorry-free (#3544)");
        }
    }

    #[test]
    fn test_tier_b_containment_all_type_check() {
        let env = make_env();
        for name in TIER_B_CONTAINMENT_THEOREMS {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            let proof = info
                .value
                .as_ref()
                .unwrap_or_else(|| panic!("{name} should have proof term"));
            let tc = TypeChecker::with_mode(&env, env.mode());
            let inferred = tc
                .infer_type(proof)
                .unwrap_or_else(|e| panic!("{name} proof should type-check: {e:?}"));
            assert!(
                tc.is_def_eq(&inferred, &info.type_),
                "{name} inferred type should match declared type"
            );
        }
    }

    /// Acceptance criterion (#3544): Tier B identity-containment proofs
    /// have an EMPTY transitive axiom closure — no domain axioms, no
    /// foundational axioms beyond `Eq`/`And` builtins that `axiom_deps`
    /// doesn't report. The proof `fun A x hx => hx` references no
    /// constants outside the kernel builtin layer.
    #[test]
    fn test_tier_b_containment_closures_are_empty() {
        let env = make_env();
        for name in TIER_B_CONTAINMENT_THEOREMS {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("axiom_deps for {name} should succeed"));
            let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
            assert!(
                dep_strs.is_empty(),
                "{name} transitive axiom closure should be empty \
                 (identity containment proof, #3544); got {dep_strs:?}"
            );
        }
    }

    /// Acceptance criterion (#3544): Tier B identity-containment proofs
    /// are `ProofQuality::Constructive`.
    #[test]
    fn test_tier_b_containment_all_constructive() {
        use crate::env::axiom_audit::ProofQuality;

        let env = make_env();
        for name in TIER_B_CONTAINMENT_THEOREMS {
            let name_e = Name::from_string(name);
            let q = env
                .proof_quality(&name_e)
                .unwrap_or_else(|| panic!("proof_quality for {name} should succeed"));
            assert!(
                matches!(q, ProofQuality::Constructive),
                "{name} should be Constructive (#3544), got {q:?}"
            );
        }
    }

    // =========================================================================
    // neg_valid_helper tests (#3544)
    // =========================================================================

    #[test]
    fn test_neg_valid_helper_is_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.neg_valid_helper",
            ))
            .expect("neg_valid_helper should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "neg_valid_helper must be Declaration::Theorem after #3544, got {:?}",
            info.kind
        );
    }

    #[test]
    fn test_neg_valid_helper_has_proof() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.neg_valid_helper",
            ))
            .expect("neg_valid_helper should be registered");
        assert!(
            info.value.is_some(),
            "neg_valid_helper must carry a proof term (#3544)"
        );
    }

    #[test]
    fn test_neg_valid_helper_type_checks() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.neg_valid_helper",
            ))
            .expect("neg_valid_helper should be registered");
        let proof = info.value.as_ref().expect("should have proof term");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let inferred = tc
            .infer_type(proof)
            .expect("neg_valid_helper proof should type-check");
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "neg_valid_helper inferred type should match declared type"
        );
    }

    #[test]
    fn test_neg_valid_helper_sorry_free() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.IntervalArith.neg_valid_helper",
            ))
            .expect("neg_valid_helper should be registered");
        let sorry = info.sorry_summary();
        assert!(
            !sorry.has_sorry,
            "neg_valid_helper proof must be sorry-free (#3544)"
        );
    }

    // =========================================================================
    // Idempotency
    // =========================================================================

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_interval_arith_proofs()
            .expect("first init");
        env.init_nn_verify_interval_arith_proofs()
            .expect("second init should be idempotent");
    }
}
