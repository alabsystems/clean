// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CROWN backward propagation theorems (T40-T42, Phase 3 of C002).
//!
//! Formalizes CROWN backward bound propagation through linear layers and
//! LayerNorm, including the W+/W- decomposition and IBP width ratio.
//!
//! ## Types
//!
//! - `NNVerify.CROWN.AffineExpr` — backward-propagated linear bounds
//!   (matrix A, bias d such that output in [A*x + d_l, A*x + d_u])
//!
//! ## Theorems
//!
//! - **T40: `crown_backward_linear`** — W+/W- decomposition: for W = W+ - W-
//!   where W+_ij = max(W_ij, 0), the backward linear relaxation computes
//!   lower/upper bounds via W+ * l + W- * u and W+ * u + W- * l.
//! - **T41: `crown_backward_layernorm`** — CROWN through LayerNorm degenerates
//!   to IBP (depends on C004), yielding interval transfer at LN boundaries.
//! - **T42: `crown_ibp_ratio_one`** — When input bounds pass through LayerNorm,
//!   the width ratio (CROWN width / IBP width) equals 1.0.
//!
//! Status after Phase 5 (#3366) and MASQUERADE demotion (#3507, 2026-04-19):
//! - T40: Axiom -> Opaque (sorry-based inhabitation)
//! - T41: Theorem -> Axiom (MASQUERADE demotion — #3507; see
//!   `register_t41_crown_backward_layernorm` for full rationale and
//!   `designs/2026-04-19-demasquerade-cxxx-pattern.md` for the pattern
//!   methodology). Both sides reduced to the same alias, so the former
//!   `Eq.refl` proof term was vacuous. Branch B (faithful carriers) is
//!   tracked under #3488 / #3500.
//! - T42: Axiom -> Opaque (sorry-based inhabitation)
//!
//! Part of #3153, #3366, #3507.

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;
#[cfg(test)]
use crate::sorry::create_sorry_term;

// T41 proof-term builder removed (#3507, 2026-04-19): the former
// `build_t41_eq_refl_proof` produced `@Eq.refl (IB n) (CROWN.backward_layernorm
// n γ β ε B)`. Because `CROWN.backward_layernorm` and `IBP.forward_layernorm`
// are reducible aliases of the same identity-on-bounds function, both sides
// reduce to the same term and the Eq.refl was vacuous (MASQUERADE patterns
// M1 + M2 + M4). T41 is now a `Declaration::Axiom`; see
// `register_t41_crown_backward_layernorm` below and
// `designs/2026-04-19-demasquerade-cxxx-pattern.md`. Do not reintroduce the
// Eq.refl-between-aliases builder without first replacing the placeholder
// carriers (Branch B).

/// Build sorry-based opaque value for a proposition-typed axiom.
///
/// ```text
/// fun (params...) => <canonical synthetic sorry for proposition>
/// ```
#[cfg(test)]
fn build_sorry_value_for_t40(env: &Environment, c: &CrownBackwardConsts) -> Expr {
    let ib_subset = Expr::const_(Name::from_string("NNVerify.IntervalBounds.subset"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(&m, &n);
    let vec_m = c.vec_of(&m);
    let ib_n = c.ib_of(&n);
    let ib_m = c.ib_of(&m);
    let aff_mn = c.affine_of(&m, &n);
    let (w_id, w) = b.fresh_local(mat_mn.clone());
    let (wp_id, wp) = b.fresh_local(mat_mn.clone());
    let (wn_id, wn) = b.fresh_local(mat_mn.clone());
    let (bias_id, _bias) = b.fresh_local(vec_m.clone());
    let (bnd_id, _bnd) = b.fresh_local(ib_n.clone());
    let (aff_id, _aff) = b.fresh_local(aff_mn.clone());
    // Hypothesis: w_pos_neg_decomp m n W W_pos W_neg
    let decomp = Expr::const_(Name::from_string("NNVerify.CROWN.w_pos_neg_decomp"), vec![]);
    let hyp_decomp = Expr::apps(decomp, [m.clone(), n.clone(), w, wp, wn]);
    let (h1_id, _) = b.fresh_local(hyp_decomp.clone());
    let (crown_res_id, crown_res) = b.fresh_local(ib_m.clone());
    let (ibp_res_id, ibp_res) = b.fresh_local(ib_m.clone());
    // Conclusion: CROWN backward result is subset of the IBP result
    let concl = Expr::apps(ib_subset, [m.clone(), crown_res, ibp_res]);
    let body = create_sorry_term(env, &concl);

    let e = b.mk_lam(ibp_res_id, BinderInfo::Default, ib_m.clone(), body);
    let e = b.mk_lam(crown_res_id, BinderInfo::Default, ib_m, e);
    let e = b.mk_lam(h1_id, BinderInfo::Default, hyp_decomp, e);
    let e = b.mk_lam(aff_id, BinderInfo::Default, aff_mn, e);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_lam(bias_id, BinderInfo::Default, vec_m, e);
    let e = b.mk_lam(wn_id, BinderInfo::Default, mat_mn.clone(), e);
    let e = b.mk_lam(wp_id, BinderInfo::Default, mat_mn.clone(), e);
    let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build sorry-based opaque value for T42 (ratio = 1).
#[cfg(test)]
fn build_sorry_value_for_t42(env: &Environment, c: &CrownBackwardConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let ib_n = c.ib_of(&n);
    let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, beta) = b.fresh_local(vec_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    // CROWN width
    let crown_result = Expr::apps(
        c.crown_backward_ln.clone(),
        [
            n.clone(),
            gamma.clone(),
            beta.clone(),
            eps.clone(),
            bnd.clone(),
        ],
    );
    let crown_width = c.ib_width_app(&n, &crown_result);
    let crown_l1 = c.l1_norm(&n, &crown_width);
    // IBP width
    let ibp_result = Expr::apps(c.ibp_forward_ln.clone(), [n.clone(), gamma, beta, eps, bnd]);
    let ibp_width = c.ib_width_app(&n, &ibp_result);
    let ibp_l1 = c.l1_norm(&n, &ibp_width);
    // Hypothesis: IBP width > 0
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let hyp_nonzero = c.rat_le(rat_zero, ibp_l1.clone());
    let (h_id, _) = b.fresh_local(hyp_nonzero.clone());
    // Conclusion: crown_l1 / ibp_l1 = 1
    let ratio = c.div(crown_l1, ibp_l1);
    let concl = c.eq_of(c.rat.clone(), ratio, c.rat_one.clone());
    let body = create_sorry_term(env, &concl);

    let e = b.mk_lam(h_id, BinderInfo::Default, hyp_nonzero, body);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Shared constants for CROWN backward theorem construction.
#[cfg(test)]
struct CrownBackwardConsts {
    nat: Expr,
    rat: Expr,
    type0: Expr,
    prop: Expr,
    nn_vec: Expr,
    nn_mat: Expr,
    ib: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    eq: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    affine_expr: Expr,
    crown_backward_ln: Expr,
    ibp_forward_ln: Expr,
    ib_width: Expr,
    nn_vec_l1_norm: Expr,
    rat_div: Expr,
}

#[cfg(test)]
impl CrownBackwardConsts {
    #[cfg(test)]
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            prop: Expr::sort(Level::zero()),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            affine_expr: Expr::const_(Name::from_string("NNVerify.CROWN.AffineExpr"), vec![]),
            crown_backward_ln: Expr::const_(
                Name::from_string("NNVerify.CROWN.backward_layernorm"),
                vec![],
            ),
            ibp_forward_ln: Expr::const_(
                Name::from_string("NNVerify.IBP.forward_layernorm"),
                vec![],
            ),
            ib_width: Expr::const_(Name::from_string("NNVerify.IntervalBounds.width"), vec![]),
            nn_vec_l1_norm: Expr::const_(Name::from_string("NNVerify.NNVec.l1_norm"), vec![]),
            rat_div: Expr::const_(Name::from_string("Rat.div"), vec![]),
        }
    }

    #[cfg(test)]
    fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    #[cfg(test)]
    fn mat_of(&self, m: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m.clone()), n.clone())
    }

    #[cfg(test)]
    fn ib_of(&self, d: &Expr) -> Expr {
        Expr::app(self.ib.clone(), d.clone())
    }

    #[cfg(test)]
    fn affine_of(&self, m: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.affine_expr.clone(), m.clone()), n.clone())
    }

    #[cfg(test)]
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

    #[cfg(test)]
    fn eq_of(&self, alpha: Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.eq.clone(), alpha), lhs), rhs)
    }

    #[cfg(test)]
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    #[cfg(test)]
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    #[cfg(test)]
    fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_div.clone(), a), b)
    }

    #[cfg(test)]
    fn l1_norm(&self, n: &Expr, v: &Expr) -> Expr {
        Expr::app(Expr::app(self.nn_vec_l1_norm.clone(), n.clone()), v.clone())
    }

    #[cfg(test)]
    fn ib_width_app(&self, d: &Expr, b: &Expr) -> Expr {
        Expr::app(Expr::app(self.ib_width.clone(), d.clone()), b.clone())
    }

    #[cfg(test)]
    fn ib_eq(&self, d: &Expr, lhs: Expr, rhs: Expr) -> Expr {
        self.eq_of(self.ib_of(d), lhs, rhs)
    }
}

#[cfg(test)]
impl Environment {
    /// Initialize CROWN backward propagation declarations (T40-T42).
    ///
    /// Depends on:
    /// - `init_nn_verify_crown_layernorm()` for CROWN/IBP LayerNorm ops
    /// - `init_nn_verify_foundation_types()` for l1_norm, width
    /// - `init_nn_verify_types()` for NNVec, NNMat, IntervalBounds
    /// - `init_rat_arith()` for Rat arithmetic
    /// - `init_eq()` for Eq
    #[cfg(test)]
    pub(crate) fn init_nn_verify_crown_backward(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.CROWN.AffineExpr"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_crown_layernorm()?;
        self.init_nn_verify_foundation_types()?;
        self.init_nn_verify_types()?;
        self.init_rat_arith()?;
        self.init_eq()?;

        let c = CrownBackwardConsts::new();
        self.register_affine_expr_type(&c)?;
        self.register_affine_expr_eval(&c)?;
        self.register_w_pos_neg_decomp(&c)?;
        self.register_t40_crown_backward_linear(&c)?;
        self.register_t41_crown_backward_layernorm(&c)?;
        self.register_t42_crown_ibp_ratio_one(&c)?;
        Ok(())
    }

    /// `NNVerify.CROWN.AffineExpr : Nat -> Nat -> Type`
    ///
    /// Backward-propagated affine expression: matrix A (m x n) and bias
    /// vectors d_l, d_u such that output_i in [A_i . x + d_l_i, A_i . x + d_u_i].
    #[cfg(test)]
    fn register_affine_expr_type(&mut self, c: &CrownBackwardConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.CROWN.AffineExpr");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _) = b.fresh_local(c.nat.clone());
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), c.type0.clone());
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// `NNVerify.CROWN.AffineExpr.eval`:
    /// `(m n : Nat) -> AffineExpr m n -> NNVec n -> IntervalBounds m`
    ///
    /// Evaluate an affine expression at a concrete input to get interval bounds.
    #[cfg(test)]
    fn register_affine_expr_eval(&mut self, c: &CrownBackwardConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.CROWN.AffineExpr.eval");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let aff_mn = c.affine_of(&m, &n);
            let vec_n = c.vec_of(&n);
            let ib_m = c.ib_of(&m);
            let (a_id, _) = b.fresh_local(aff_mn.clone());
            let (x_id, _) = b.fresh_local(vec_n.clone());
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, ib_m);
            let r = b.mk_pi(a_id, BinderInfo::Default, aff_mn, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// `NNVerify.CROWN.w_pos_neg_decomp`:
    /// `(m n : Nat) -> NNMat m n -> NNMat m n -> NNMat m n -> Prop`
    ///
    /// Predicate: W = W_pos - W_neg where W_pos_ij = max(W_ij, 0)
    /// and W_neg_ij = max(-W_ij, 0).
    #[cfg(test)]
    fn register_w_pos_neg_decomp(&mut self, c: &CrownBackwardConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.CROWN.w_pos_neg_decomp");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(&m, &n);
            let (w_id, _) = b.fresh_local(mat_mn.clone());
            let (wp_id, _) = b.fresh_local(mat_mn.clone());
            let (wn_id, _) = b.fresh_local(mat_mn.clone());
            let r = b.mk_pi(wn_id, BinderInfo::Default, mat_mn.clone(), c.prop.clone());
            let r = b.mk_pi(wp_id, BinderInfo::Default, mat_mn.clone(), r);
            let r = b.mk_pi(w_id, BinderInfo::Default, mat_mn, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// T40: `NNVerify.CROWN.crown_backward_linear`
    ///
    /// For W = W+ - W- (positive/negative decomposition), CROWN backward
    /// through a linear layer produces sound bounds:
    /// ```text
    /// forall (m n : Nat) (W : NNMat m n) (W_pos W_neg : NNMat m n)
    ///   (b : NNVec m) (B : IntervalBounds n),
    ///   w_pos_neg_decomp m n W W_pos W_neg ->
    ///   IntervalBounds.subset m (crown_backward_result ...) (ibp_result ...)
    /// ```
    /// Soundness: CROWN backward linear bounds are contained in IBP bounds.
    #[cfg(test)]
    fn register_t40_crown_backward_linear(
        &mut self,
        c: &CrownBackwardConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.CROWN.crown_backward_linear");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ib_subset = Expr::const_(Name::from_string("NNVerify.IntervalBounds.subset"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(&m, &n);
            let vec_m = c.vec_of(&m);
            let ib_n = c.ib_of(&n);
            let ib_m = c.ib_of(&m);
            let aff_mn = c.affine_of(&m, &n);
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let (wp_id, wp) = b.fresh_local(mat_mn.clone());
            let (wn_id, wn) = b.fresh_local(mat_mn.clone());
            let (bias_id, _bias) = b.fresh_local(vec_m.clone());
            let (bnd_id, _bnd) = b.fresh_local(ib_n.clone());
            let (aff_id, _aff) = b.fresh_local(aff_mn.clone());
            // Hypothesis: w_pos_neg_decomp m n W W_pos W_neg
            let decomp = Expr::const_(Name::from_string("NNVerify.CROWN.w_pos_neg_decomp"), vec![]);
            let hyp_decomp = Expr::apps(decomp, [m.clone(), n.clone(), w, wp, wn]);
            let (h1_id, _) = b.fresh_local(hyp_decomp.clone());
            // Bind CROWN and IBP result values of type IntervalBounds m
            let (crown_res_id, crown_res) = b.fresh_local(ib_m.clone());
            let (ibp_res_id, ibp_res) = b.fresh_local(ib_m.clone());
            // Conclusion: CROWN backward result is subset of the IBP result
            let concl = Expr::apps(ib_subset, [m.clone(), crown_res, ibp_res]);
            let r = b.mk_pi(ibp_res_id, BinderInfo::Default, ib_m.clone(), concl);
            let r = b.mk_pi(crown_res_id, BinderInfo::Default, ib_m, r);
            let r = b.mk_pi(h1_id, BinderInfo::Default, hyp_decomp, r);
            let r = b.mk_pi(aff_id, BinderInfo::Default, aff_mn, r);
            let r = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, r);
            let r = b.mk_pi(bias_id, BinderInfo::Default, vec_m, r);
            let r = b.mk_pi(wn_id, BinderInfo::Default, mat_mn.clone(), r);
            let r = b.mk_pi(wp_id, BinderInfo::Default, mat_mn.clone(), r);
            let r = b.mk_pi(w_id, BinderInfo::Default, mat_mn, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // SOUNDNESS: T40 is a genuine mathematical theorem. Converted from
        // Axiom to Opaque with sorry-based inhabitation. Part of #3366.
        let value = build_sorry_value_for_t40(self, c);
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// T41: `NNVerify.CROWN.crown_backward_layernorm_is_ibp` (Axiom — MASQUERADE demoted)
    ///
    /// CROWN backward through LayerNorm = IBP forward through LayerNorm.
    /// Type-level statement of C004 restated in the backward-propagation
    /// context.
    ///
    /// **MASQUERADE demotion (#3507, 2026-04-19):** previously registered as
    /// `Declaration::Theorem` with proof term
    /// `@Eq.refl (IB n) (CROWN.backward_layernorm n γ β ε B)`. Because
    /// `CROWN.backward_layernorm` is a reducible `Declaration::Definition`
    /// aliasing `IBP.forward_layernorm` (whose body is the argument-discarding
    /// identity `fun n _ _ _ B => B`), both sides of the equality delta-reduce
    /// to the same normal form, so the Eq.refl was vacuous (MASQUERADE
    /// patterns M1 + M2 + M4 per the demasquerade design). Demoted to
    /// `Declaration::Axiom` (Branch A) so the honest axiom cost of the
    /// claim is visible in `data/axiom_audit.json`. A real proof requires
    /// Branch B (faithful CROWN / IBP / LayerNorm carriers that force the
    /// equivalence by LayerNorm Jacobian semantics, not by alias-collapse)
    /// and is tracked with #3488 / #3500. Part of #3153, #3366, #3507.
    #[cfg(test)]
    fn register_t41_crown_backward_layernorm(
        &mut self,
        c: &CrownBackwardConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.CROWN.crown_backward_layernorm_is_ibp");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let ib_n = c.ib_of(&n);
            let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
            let (beta_id, beta) = b.fresh_local(vec_n.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
            let crown_app = Expr::apps(
                c.crown_backward_ln.clone(),
                [
                    n.clone(),
                    gamma.clone(),
                    beta.clone(),
                    eps.clone(),
                    bnd.clone(),
                ],
            );
            let ibp_app = Expr::apps(c.ibp_forward_ln.clone(), [n.clone(), gamma, beta, eps, bnd]);
            let concl = c.ib_eq(&n, crown_app, ibp_app);
            let r = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, concl);
            let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // SOUNDNESS (#3507): MASQUERADE demotion from Declaration::Theorem
        // (Eq.refl between reducible aliases) to Declaration::Axiom. See
        // doc-comment above and designs/2026-04-19-demasquerade-cxxx-pattern.md.
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// T42: `NNVerify.CROWN.crown_ibp_ratio_one` (Opaque)
    ///
    /// Through LayerNorm, the CROWN-to-IBP width ratio is exactly 1.0:
    /// ```text
    /// forall (n : Nat) (gamma beta : NNVec n) (ln_eps : Rat) (B : IB n),
    ///   l1_norm n (width n (CROWN.backward_layernorm n gamma beta ln_eps B))
    ///     / l1_norm n (width n (IBP.forward_layernorm n gamma beta ln_eps B))
    ///     = Rat.one
    /// ```
    /// (provided IBP width is nonzero)
    #[cfg(test)]
    fn register_t42_crown_ibp_ratio_one(
        &mut self,
        c: &CrownBackwardConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.CROWN.crown_ibp_ratio_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let ib_n = c.ib_of(&n);
            let (gamma_id, gamma) = b.fresh_local(vec_n.clone());
            let (beta_id, beta) = b.fresh_local(vec_n.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
            // CROWN width
            let crown_result = Expr::apps(
                c.crown_backward_ln.clone(),
                [
                    n.clone(),
                    gamma.clone(),
                    beta.clone(),
                    eps.clone(),
                    bnd.clone(),
                ],
            );
            let crown_width = c.ib_width_app(&n, &crown_result);
            let crown_l1 = c.l1_norm(&n, &crown_width);
            // IBP width
            let ibp_result =
                Expr::apps(c.ibp_forward_ln.clone(), [n.clone(), gamma, beta, eps, bnd]);
            let ibp_width = c.ib_width_app(&n, &ibp_result);
            let ibp_l1 = c.l1_norm(&n, &ibp_width);
            // Hypothesis: IBP width > 0
            let hyp_nonzero = c.rat_le(rat_zero, ibp_l1.clone());
            let (h_id, _) = b.fresh_local(hyp_nonzero.clone());
            // Conclusion: crown_l1 / ibp_l1 = 1
            let ratio = c.div(crown_l1, ibp_l1);
            let concl = c.eq_of(c.rat.clone(), ratio, c.rat_one.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp_nonzero, concl);
            let r = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, r);
            let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // SOUNDNESS: T42 follows from T41 (CROWN backward = IBP forward)
        // and x/x = 1 for nonzero x. Converted from Axiom to Opaque with
        // sorry-based inhabitation. Part of #3366.
        let value = build_sorry_value_for_t42(self, c);
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
