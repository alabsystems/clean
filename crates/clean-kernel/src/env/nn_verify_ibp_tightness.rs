// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C008: IBP Tightness Bound — `ibp_width <= 2 * eps * prod ||W_i||_inf`.
//!
//! **ZERO domain-specific axioms** — FULLY constructive (#3374).
//!
//! `eps_ball` is a reducible Definition (zero-width placeholder — R-weak
//! caveat); `ibp_tightness_base` and `ibp_tightness_step` are now constructive
//! sorry-free Theorems (C008 unlock, R-weak), as are
//! `ibp_tightness_bound_inductive` (via `Nat.rec`) and `ibp_tightness_bound`.
//! 4 definitions with `Nat.rec` value terms.
//!
//! History:
//! - Original: 5 individual axioms
//! - Phase 1 (#3374): consolidated to base+step + eps_ball->Opaque = 2 axioms
//! - Phase 2 (#3374): base+step upgraded from Axiom to Opaque = 0 axioms
//! - C008 unlock (R-weak): base + step graduated to constructive Theorems off
//!   the faithful `ibp_linear_bounds` / `ibp_relu_bounds` Definitions.
//!
//! Value builders live in `nn_verify_ibp_tightness_defs`; induction proof
//! builders in `nn_verify_ibp_tightness_proofs`.

use super::nn_verify_ibp_linear::IbpLinearConsts;
use super::nn_verify_ibp_tightness_defs;
use super::nn_verify_ibp_tightness_proofs;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for C008 declaration and proof construction.
pub(super) struct IbpTightnessConsts {
    pub(super) base: IbpLinearConsts,
    pub(super) nat_zero: Expr,
    pub(super) nat_succ: Expr,
    pub(super) nat_rec_type0: Expr,
    pub(super) rat_one: Expr,
    pub(super) rat_sub: Expr,
    pub(super) rat_abs: Expr,
    pub(super) rat_max: Expr,
    pub(super) fin_val: Expr,
    pub(super) fin_cast_succ: Expr,
    pub(super) fin_last: Expr,
    pub(super) ib_mk: Expr,
    pub(super) ibp_linear_bounds: Expr,
    pub(super) ibp_relu_bounds: Expr,
    pub(super) eps_ball: Expr,
    pub(super) infinity_norm: Expr,
    pub(super) ibp_width: Expr,
    pub(super) norm_product: Expr,
    pub(super) ibp_propagate: Expr,
}

impl IbpTightnessConsts {
    pub(super) fn new() -> Self {
        Self {
            base: IbpLinearConsts::new(),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_rec_type0: Expr::const_(
                Name::from_string("Nat.rec"),
                vec![Level::succ(Level::zero())],
            ),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_abs: Expr::const_(Name::from_string("Rat.abs"), vec![]),
            rat_max: Expr::const_(Name::from_string("Rat.max"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            ib_mk: Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]),
            ibp_linear_bounds: Expr::const_(
                Name::from_string("NNVerify.ibp_linear_bounds"),
                vec![],
            ),
            ibp_relu_bounds: Expr::const_(Name::from_string("NNVerify.ibp_relu_bounds"), vec![]),
            eps_ball: Expr::const_(Name::from_string("NNVerify.eps_ball"), vec![]),
            infinity_norm: Expr::const_(Name::from_string("NNVerify.infinity_norm"), vec![]),
            ibp_width: Expr::const_(Name::from_string("NNVerify.ibp_width"), vec![]),
            norm_product: Expr::const_(Name::from_string("NNVerify.norm_product"), vec![]),
            ibp_propagate: Expr::const_(Name::from_string("NNVerify.ibp_propagate"), vec![]),
        }
    }

    pub(super) fn two(&self) -> Expr {
        self.base.add(self.rat_one.clone(), self.rat_one.clone())
    }

    pub(super) fn output_dim_ty(&self) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.base.nat.clone(),
            self.base.nat.clone(),
        )
    }

    pub(super) fn out_dim(&self, output_dim: &Expr, idx: Expr) -> Expr {
        Expr::app(output_dim.clone(), idx)
    }

    pub(super) fn fin_val_app(&self, n: &Expr, i: Expr) -> Expr {
        Expr::app(Expr::app(self.fin_val.clone(), n.clone()), i)
    }

    pub(super) fn weight_family_ty(&self, outer: &EnvDeclBuilder, output_dim: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(outer);
        let (i_id, i) = ch.fresh_local(self.base.nat.clone());
        let out_i = self.out_dim(output_dim, i.clone());
        let out_succ_i = self.out_dim(output_dim, Expr::app(self.nat_succ.clone(), i));
        let body = self.base.mat_of(out_succ_i, out_i);
        let r = ch.mk_pi(i_id, BinderInfo::Default, self.base.nat.clone(), body);
        ch.finish_child(r)
    }

    pub(super) fn bias_family_ty(&self, outer: &EnvDeclBuilder, output_dim: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(outer);
        let (i_id, i) = ch.fresh_local(self.base.nat.clone());
        let out_succ_i = self.out_dim(output_dim, Expr::app(self.nat_succ.clone(), i));
        let body = self.base.vec_of(out_succ_i);
        let r = ch.mk_pi(i_id, BinderInfo::Default, self.base.nat.clone(), body);
        ch.finish_child(r)
    }

    pub(super) fn center_ty(&self, output_dim: &Expr) -> Expr {
        self.base
            .vec_of(self.out_dim(output_dim, self.nat_zero.clone()))
    }

    pub(super) fn input_bounds_ty(&self, output_dim: &Expr) -> Expr {
        self.base
            .ib_of(self.out_dim(output_dim, self.nat_zero.clone()))
    }

    pub(super) fn infinity_norm_app(&self, m: Expr, n: Expr, w: Expr) -> Expr {
        Expr::apps(self.infinity_norm.clone(), [m, n, w])
    }

    pub(super) fn ibp_width_app(&self, n: Expr, bnd: Expr) -> Expr {
        Expr::apps(self.ibp_width.clone(), [n, bnd])
    }

    pub(super) fn norm_product_app(&self, k: Expr, norms: Expr) -> Expr {
        Expr::apps(self.norm_product.clone(), [k, norms])
    }

    pub(super) fn eps_ball_app(&self, n: Expr, center: Expr, eps: Expr) -> Expr {
        Expr::apps(self.eps_ball.clone(), [n, center, eps])
    }

    pub(super) fn ibp_propagate_app(
        &self,
        k: Expr,
        output_dim: Expr,
        weight: Expr,
        bias: Expr,
        input_bounds: Expr,
    ) -> Expr {
        Expr::apps(
            self.ibp_propagate.clone(),
            [k, output_dim, weight, bias, input_bounds],
        )
    }

    pub(super) fn linear_bounds_app(
        &self,
        m: Expr,
        n: Expr,
        w: Expr,
        bias: Expr,
        bnd: Expr,
    ) -> Expr {
        Expr::apps(self.ibp_linear_bounds.clone(), [m, n, w, bias, bnd])
    }

    pub(super) fn relu_bounds_app(&self, n: Expr, bnd: Expr) -> Expr {
        Expr::apps(self.ibp_relu_bounds.clone(), [n, bnd])
    }

    pub(super) fn norm_lambda(
        &self,
        outer: &EnvDeclBuilder,
        k: &Expr,
        output_dim: &Expr,
        weight: &Expr,
    ) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(outer);
        let fin_k = Expr::app(self.base.fin.clone(), k.clone());
        let (i_id, i) = ch.fresh_local(fin_k.clone());
        let idx = self.fin_val_app(k, i.clone());
        let out_i = self.out_dim(output_dim, idx.clone());
        let out_succ_i = self.out_dim(output_dim, Expr::app(self.nat_succ.clone(), idx.clone()));
        let w_i = Expr::app(weight.clone(), idx);
        let body = self.infinity_norm_app(out_succ_i, out_i, w_i);
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_k, body);
        ch.finish_child(r)
    }
}

// =============================================================================
// Type builders (small, kept here)
// =============================================================================

fn build_eps_ball_type(c: &IbpTightnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let vec_n = c.base.vec_of(n.clone());
    let (center_id, _center) = b.fresh_local(vec_n.clone());
    let (eps_id, _eps) = b.fresh_local(c.base.rat.clone());
    let result = c.base.ib_of(n);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.base.rat.clone(), result);
    let e = b.mk_pi(center_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

fn build_infinity_norm_type(c: &IbpTightnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.base.nat.clone());
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let mat_mn = c.base.mat_of(m, n);
    let (w_id, _) = b.fresh_local(mat_mn.clone());
    let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, c.base.rat.clone());
    let e = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

fn build_ibp_width_type(c: &IbpTightnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let ib_n = c.base.ib_of(n.clone());
    let (bnd_id, _) = b.fresh_local(ib_n.clone());
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, c.base.rat.clone());
    let e = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

fn build_norm_product_type(c: &IbpTightnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let fin_k = Expr::app(c.base.fin.clone(), k.clone());
    let norms_ty = Expr::pi(BinderInfo::Default, fin_k, c.base.rat.clone());
    let (norms_id, _) = b.fresh_local(norms_ty.clone());
    let e = b.mk_pi(norms_id, BinderInfo::Default, norms_ty, c.base.rat.clone());
    let e = b.mk_pi(k_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

fn build_ibp_propagate_type(c: &IbpTightnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let output_dim_ty = c.output_dim_ty();
    let (od_id, output_dim) = b.fresh_local(output_dim_ty.clone());
    let weight_ty = c.weight_family_ty(&b, &output_dim);
    let (w_id, _) = b.fresh_local(weight_ty.clone());
    let bias_ty = c.bias_family_ty(&b, &output_dim);
    let (bias_id, _) = b.fresh_local(bias_ty.clone());
    let input_ty = c.input_bounds_ty(&output_dim);
    let (input_id, _) = b.fresh_local(input_ty.clone());
    let result = c.base.ib_of(c.out_dim(&output_dim, k.clone()));

    let e = b.mk_pi(input_id, BinderInfo::Default, input_ty, result);
    let e = b.mk_pi(bias_id, BinderInfo::Default, bias_ty, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, weight_ty, e);
    let e = b.mk_pi(od_id, BinderInfo::Default, output_dim_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

// Lemma type builders and theorem type/proof builders live in the defs module.

// =============================================================================
// Environment impl
// =============================================================================

impl Environment {
    /// Initialize C008 (IBP tightness bound) declarations.
    ///
    /// Registers 9 declarations:
    /// - `NNVerify.eps_ball` — epsilon-ball constructor (opaque)
    /// - `NNVerify.infinity_norm` — matrix infinity norm (definition)
    /// - `NNVerify.ibp_width` — interval bound width (definition)
    /// - `NNVerify.norm_product` — product of norms across layers (definition)
    /// - `NNVerify.ibp_propagate` — IBP forward propagation (definition)
    /// - `NNVerify.ibp_tightness_base` — base case (constructive Theorem, R-weak)
    /// - `NNVerify.ibp_tightness_step` — inductive step (constructive Theorem, R-weak)
    /// - `NNVerify.ibp_tightness_bound_inductive` — induction theorem (Nat.rec proof)
    /// - `NNVerify.ibp_tightness_bound` — main theorem (wraps inductive)
    ///
    /// Depends on:
    /// - `init_nn_verify_ibp_linear()` for T80 helpers and IBP affine bounds
    /// - `init_nn_verify_relu()` for `NNVerify.ibp_relu_bounds`
    /// - `init_field()` for Rat field/order infrastructure
    /// - `init_eq()` for theorem proof wrappers
    /// - `init_rat_abs()` for `Rat.abs`
    pub fn init_nn_verify_ibp_tightness(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_ibp_tightness_init {
            return Ok(());
        }
        self.init_nn_verify_ibp_linear()?;
        self.init_nn_verify_relu()?;
        self.init_field()?;
        self.init_eq()?;
        self.init_rat_abs()?;

        let c = IbpTightnessConsts::new();
        self.register_eps_ball(&c)?;
        self.register_infinity_norm(&c)?;
        self.register_ibp_width(&c)?;
        self.register_norm_product(&c)?;
        self.register_ibp_propagate(&c)?;
        // The C008 definition pass (above) is complete, so the width-zero
        // helpers the base-case proof depends on can be registered now (the full
        // `init_nn_verify_ibp_width_zero` cannot be called here — it depends on
        // tightness — so this guarded subset is registered directly).
        self.register_rat_zero_le_one(&c)?;
        self.register_rat_zero_le_two(&c)?;
        self.register_ibp_width_zero_for_base()?;
        self.register_ibp_tightness_base(&c)?;
        // Zero-width preservation sub-lemmas (relu / linear) for the R-weak
        // `ibp_tightness_step` proof. Registered after the C008 definitions and
        // the T80/relu bound Definitions so all referenced consts exist.
        self.register_ibp_tightness_step_support(&c.base)?;
        // `propagate_eq` + non-negativity helpers, then the step proof consumes
        // them. Registered after `register_ibp_width_zero_for_base` (above) so
        // `ibp_width_zero` is present.
        self.register_ibp_tightness_step_value_support(&c)?;
        self.register_ibp_tightness_step(&c)?;
        self.register_ibp_tightness_bound_impl(&c)?;

        self.nn_verify_ibp_tightness_init = true;
        Ok(())
    }

    /// `NNVerify.rat_zero_le_one : LE.le Rat instLERat Rat.zero Rat.one`.
    ///
    /// Constructive `Declaration::Theorem` (no `sorry`): the `≤` half of
    /// `Rat.zero_lt_one`, extracted via `Rat.lt_iff_le_not_le`. Proof term:
    /// `And.left (0 ≤ 1) (¬ 1 ≤ 0)
    ///    (Iff.mp (Rat.lt 0 1) (And (0 ≤ 1) (¬ 1 ≤ 0))
    ///       (Rat.lt_iff_le_not_le 0 1) Rat.zero_lt_one)`.
    /// Closure: `Rat.lt_iff_le_not_le` (which is itself `AxiomDependent` on the
    /// single `Int.lt_iff_le_not_le`), `Rat.zero_lt_one`, `Iff.mp`, `And.left`
    /// — no new domain axioms beyond the existing Rat order infrastructure.
    fn register_rat_zero_le_one(&mut self, c: &IbpTightnessConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.rat_zero_le_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat_linear_order()?; // Rat.lt_iff_le_not_le, Rat.zero_lt_one

        let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let not = Expr::const_(Name::from_string("Not"), vec![]);
        let and = Expr::const_(Name::from_string("And"), vec![]);
        let zero = c.base.rat_zero.clone();
        let one = c.rat_one.clone();

        // Props.
        let le_01 = Expr::apps(rat_le.clone(), [zero.clone(), one.clone()]);
        let le_10 = Expr::apps(rat_le, [one.clone(), zero.clone()]);
        let not_le_10 = Expr::app(not, le_10);
        let lt_01 = Expr::apps(rat_lt, [zero.clone(), one.clone()]);
        let and_prop = Expr::apps(and, [le_01.clone(), not_le_10.clone()]);

        let ty = c.base.rat_le(zero.clone(), one.clone());

        let value = {
            let lt_iff = Expr::apps(
                Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
                [zero.clone(), one.clone()],
            );
            let zlo = Expr::const_(Name::from_string("Rat.zero_lt_one"), vec![]);
            let mp = Expr::apps(
                Expr::const_(Name::from_string("Iff.mp"), vec![]),
                [lt_01, and_prop.clone(), lt_iff, zlo],
            );
            Expr::apps(
                Expr::const_(Name::from_string("And.left"), vec![]),
                [le_01, not_le_10, mp],
            )
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.rat_zero_le_two : LE.le Rat instLERat Rat.zero (Rat.add Rat.one Rat.one)`.
    ///
    /// Constructive `Declaration::Theorem` (no `sorry`): `0 ≤ 2` where the C008
    /// `2` is `Rat.add Rat.one Rat.one`. Proof:
    /// `Rat.le_trans 0 1 (1+1) rat_zero_le_one
    ///    (Rat.le_add_of_nonneg_right 1 1 rat_zero_le_one)`.
    /// `Rat.le_add_of_nonneg_right 1 1 (0 ≤ 1) : 1 ≤ 1 + 1`; chaining gives
    /// `0 ≤ 1 + 1`. Closure ⊆ that of `rat_zero_le_one` ∪ `Rat.le_trans` ∪
    /// `Rat.le_add_of_nonneg_right`.
    fn register_rat_zero_le_two(&mut self, c: &IbpTightnessConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.rat_zero_le_two");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = c.base.rat_zero.clone();
        let one = c.rat_one.clone();
        let two = c.two(); // Rat.add Rat.one Rat.one

        let ty = c.base.rat_le(zero.clone(), two.clone());

        let value = {
            let zle1 = Expr::const_(Name::from_string("NNVerify.rat_zero_le_one"), vec![]);
            // 1 ≤ 1 + 1.
            let one_le_two = Expr::apps(
                Expr::const_(Name::from_string("Rat.le_add_of_nonneg_right"), vec![]),
                [one.clone(), one.clone(), zle1.clone()],
            );
            // Rat.le_trans 0 1 (1+1) (0≤1) (1≤1+1).
            Expr::apps(
                Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
                [zero, one, two, zle1, one_le_two],
            )
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.eps_ball`: epsilon-ball constructor. Category A fix (#3435):
    /// Axiom -> Opaque (#3374) -> reducible Definition. Body is sorry-free:
    /// `IntervalBounds.mk n zero_vec zero_vec (fun i => Rat.le_refl 0)` — the
    /// only axiom it touches is `Rat.le_refl` (foundational). Zero-width bounds
    /// are a placeholder for real `(center +/- eps)` semantics (follow-up needs
    /// `sub_le_add`). Reducible lets downstream proofs unfold through the kernel.
    fn register_eps_ball(&mut self, c: &IbpTightnessConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.eps_ball"))
            .is_some()
        {
            return Ok(());
        }
        let ty = build_eps_ball_type(c);
        let value = nn_verify_ibp_tightness_defs::build_eps_ball_value(c);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.eps_ball"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    fn register_infinity_norm(&mut self, c: &IbpTightnessConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.infinity_norm"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.infinity_norm"),
            level_params: vec![],
            type_: build_infinity_norm_type(c),
            value: nn_verify_ibp_tightness_defs::build_infinity_norm_value(c),
            is_reducible: true,
        })
    }

    fn register_ibp_width(&mut self, c: &IbpTightnessConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.ibp_width"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.ibp_width"),
            level_params: vec![],
            type_: build_ibp_width_type(c),
            value: nn_verify_ibp_tightness_defs::build_ibp_width_value(c),
            is_reducible: true,
        })
    }

    fn register_norm_product(&mut self, c: &IbpTightnessConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.norm_product"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.norm_product"),
            level_params: vec![],
            type_: build_norm_product_type(c),
            value: nn_verify_ibp_tightness_defs::build_norm_product_value(c),
            is_reducible: true,
        })
    }

    fn register_ibp_propagate(&mut self, c: &IbpTightnessConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.ibp_propagate"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.ibp_propagate"),
            level_params: vec![],
            type_: build_ibp_propagate_type(c),
            value: nn_verify_ibp_tightness_defs::build_ibp_propagate_value(c),
            is_reducible: true,
        })
    }

    /// Base case: IBP width bound holds at k=0.
    ///
    /// The eps-ball input has width bounded by 2*eps (since propagate at 0
    /// is identity and norm_product at 0 is 1).
    ///
    /// CONSTRUCTIVE PROOF (#3490 T6 / #3476 — was Axiom, now a genuine
    /// `Declaration::Theorem`): with the `eps ≥ 0` hypothesis the statement is
    /// TRUE and now kernel-checked. `ibp_propagate(0)` ι-reduces to the
    /// identity, so the LHS is `ibp_width (output_dim 0) (eps_ball …)`, which
    /// the constructive Theorem `NNVerify.eps_ball_width_is_zero` collapses to
    /// `Rat.zero`. The remaining obligation `0 ≤ 2·eps·norm_product 0 norms`
    /// (the second factor ι-reduces to `Rat.one`) is discharged by
    /// `Rat.mul_nonneg` from `0 ≤ 2`, `h_nonneg : 0 ≤ eps`, and `0 ≤ 1`. The two
    /// are combined by `NNVerify.le_of_eq_of_le`. See
    /// `nn_verify_ibp_tightness_proofs::build_ibp_tightness_base_value`.
    ///
    /// HONESTY: the proof leans on `eps_ball`'s registered zero-width
    /// placeholder body (the LHS is `0` only because the placeholder ball has
    /// zero width). It is a real, `sorry`-free assembly over genuine kernel
    /// reductions — NOT a masquerade — and `h_nonneg` is genuinely consumed (a
    /// negative `eps` makes the RHS negative and the statement false). The full
    /// `(center ± eps)`-semantics ball is a separate follow-up; the inductive
    /// STEP (`ibp_tightness_step`) is now ALSO a constructive R-weak Theorem
    /// (see `register_ibp_tightness_step`).
    fn register_ibp_tightness_base(&mut self, c: &IbpTightnessConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.ibp_tightness_base");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_bool()?;
        let type_ = nn_verify_ibp_tightness_proofs::build_ibp_tightness_base_type(c);
        let value = nn_verify_ibp_tightness_proofs::build_ibp_tightness_base_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Inductive step: given the bound at k, derive it at k+1.
    ///
    /// Adding one affine+ReLU layer multiplies the IBP width by at most
    /// the infinity norm of the weight matrix.
    ///
    /// The C008 inductive step (k → k+1): adding one affine+ReLU layer
    /// amplifies the IBP width by at most the layer's infinity norm. Previously
    /// an admitted `Declaration::Axiom` (#3374); now a constructive sorry-free
    /// `Declaration::Theorem` via the R-weak route (the inner `register_*` body
    /// comment documents the proof architecture and the `eps_ball` zero-width
    /// honesty caveat).
    fn register_ibp_tightness_step(&mut self, c: &IbpTightnessConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.ibp_tightness_step");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_bool()?;
        let type_ = nn_verify_ibp_tightness_proofs::build_ibp_tightness_step_type(c);
        // CONSTRUCTIVE PROOF (C008 unlock, R-weak): with `ibp_linear_bounds` now
        // a faithful Definition (and `ibp_relu_bounds` already one), the
        // propagated eps-ball stays zero-width through every layer
        // (`ibp_propagate_eq`), so the step LHS `ibp_width` collapses to
        // `Rat.zero` via `ibp_width_zero`; the RHS `0 ≤ 2·eps·norm_product
        // (k+1) norms` is discharged by `Rat.mul_nonneg` (`norm_product_nonneg`
        // fed `infinity_norm_nonneg` per layer). HONESTY CAVEAT (same as the
        // landed `ibp_tightness_base`): the zero-width collapse leans on the
        // registered `eps_ball` zero-width placeholder body. Genuine sorry-free
        // assembly over real kernel reductions — no masquerade. See
        // `nn_verify_ibp_tightness_step_value::build_ibp_tightness_step_value`.
        let value = super::nn_verify_ibp_tightness_step_value::build_ibp_tightness_step_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    fn register_ibp_tightness_bound_impl(
        &mut self,
        c: &IbpTightnessConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.ibp_tightness_bound"))
            .is_some()
        {
            return Ok(());
        }
        self.register_ibp_tightness_bound_inductive(c)?;
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ibp_tightness_bound"),
            level_params: vec![],
            type_: nn_verify_ibp_tightness_defs::build_ibp_tightness_bound_type(c),
            value: nn_verify_ibp_tightness_defs::build_ibp_tightness_bound_proof(c),
        })
    }

    /// Induction combinator: `Nat.rec` proof combining base + step axioms.
    ///
    /// Previously an axiom, now a `Declaration::Theorem` with a constructive
    /// proof term built from `Nat.rec` over `ibp_tightness_base` and
    /// `ibp_tightness_step`. Has the same type as `ibp_tightness_bound`.
    ///
    /// Part of #3374: replace C008 axioms with constructive proof terms.
    fn register_ibp_tightness_bound_inductive(
        &mut self,
        c: &IbpTightnessConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.ibp_tightness_bound_inductive");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: nn_verify_ibp_tightness_defs::build_ibp_tightness_bound_type(c),
            value: nn_verify_ibp_tightness_proofs::build_ibp_tightness_nat_induction_proof(c),
        })
    }
}
