// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T80: IBP linear layer soundness — W+/W- decomposition proof.
//!
//! For linear layer y = W*x + b with W = W+ + W-, IBP bounds are:
//! - Lower: W+*lo + W-*hi + b, Upper: W+*hi + W-*lo + b
//!
//! ## Definitions
//!
//! - `NNVerify.w_pos` — W+ = max(W, 0) element-wise (positive part)
//! - `NNVerify.w_neg` — W- = min(W, 0) element-wise (negative part)
//! - `NNVerify.linear_output` — y = W*x + b (matrix-vector multiply + bias)
//! - `NNVerify.ibp_linear_bounds` — IBP bound computation for linear layer
//!
//! ## Lemmas (Opaque, sorry-inhabited — mathematically sound)
//!
//! - `NNVerify.w_decompose` — W[i,j] = W+[i,j] + W-[i,j]
//! - `NNVerify.w_pos_nonneg` — W+[i,j] >= 0
//! - `NNVerify.w_neg_nonpos` — W-[i,j] <= 0
//! - `NNVerify.mul_nonneg_le_left` — 0 <= w -> a <= b -> w*a <= w*b
//! - `NNVerify.mul_nonpos_le_left` — w <= 0 -> a <= b -> w*b <= w*a
//! - `NNVerify.add_le_add` — a1 <= b1 -> a2 <= b2 -> a1+a2 <= b1+b2
//! - `NNVerify.le_of_eq_of_le` — a = b -> b <= c -> a <= c
//! - `NNVerify.le_of_le_of_eq` — a <= b -> b = c -> a <= c
//!
//! ## Theorem
//!
//! - `NNVerify.ibp_linear_sound` — T80: contains B x -> contains (ibp_bounds W b B) (W*x+b)
//!
//! Proof by Fin.sum decomposition and sum_le monotonicity via
//! `ibp_linear_per_component` helper axiom.
//!
//! Part of #3244, #3265.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::sorry::create_sorry_term;

/// Build a sorry-inhabited lambda term from a Pi (forall) type.
///
/// Given a type `forall (x1 : A1) ... (xn : An), P`, produces:
/// ```text
/// fun (x1 : A1) ... (xn : An) => <canonical synthetic sorry for P>
/// ```
///
/// This is used to convert mathematical axioms to Opaque declarations
/// with canonical sorry-based proof inhabitation. The Opaque wrapper prevents
/// reduction, so the sorryAx/sorry marker is never exposed during type checking.
///
/// The function walks the Pi spine, building corresponding lambda
/// binders, and routes the innermost proposition through the centralized
/// sorry constructor so DENY_SORRY and provenance accounting apply.
#[track_caller]
pub(super) fn sorry_inhabit_pi(env: &Environment, ty: &Expr) -> Expr {
    sorry_inhabit_pi_inner(env, ty)
}

#[track_caller]
fn sorry_inhabit_pi_inner(env: &Environment, ty: &Expr) -> Expr {
    match ty.kind() {
        ExprKind::Pi(bi, param_ty, body) => {
            let inner = sorry_inhabit_pi_inner(env, body);
            Expr::lam(*bi, (**param_ty).clone(), inner)
        }
        _ => create_sorry_term(env, ty),
    }
}

/// Shared constants for IBP linear proof construction.
pub(super) struct IbpLinearConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) fin: Expr,
    pub(super) nn_vec: Expr,
    pub(super) nn_mat: Expr,
    pub(super) ib: Expr,
    pub(super) ib_contains: Expr,
    pub(super) fin_sum: Expr,
    pub(super) rat_add: Expr,
    pub(super) rat_mul: Expr,
    pub(super) rat_zero: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) eq: Expr,
}

impl IbpLinearConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_contains: Expr::const_(
                Name::from_string("NNVerify.IntervalBounds.contains"),
                vec![],
            ),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        }
    }

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

    pub(super) fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.rat.clone()), lhs),
            rhs,
        )
    }

    pub(super) fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    pub(super) fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::app(Expr::app(self.fin_sum.clone(), n), f)
    }

    pub(super) fn vec_of(&self, n: Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n)
    }

    pub(super) fn mat_of(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m), n)
    }

    pub(super) fn ib_of(&self, d: Expr) -> Expr {
        Expr::app(self.ib.clone(), d)
    }

    pub(super) fn contains(&self, d: &Expr, b: &Expr, x: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_contains.clone(), d.clone()), b.clone()),
            x.clone(),
        )
    }
}

impl Environment {
    /// Initialize T80 (IBP linear soundness) declarations.
    ///
    /// Depends on: `init_nn_verify_types()`, `init_fin_sum()`,
    ///             `init_rat_arith()`, `init_rat_ord()`, `init_and()`,
    ///             `init_nn_verify_proofs()` (for le_trans).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.nn_verify_ibp_linear_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_ibp_linear(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_ibp_linear_init {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_fin_sum()?;
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.init_rat_linear_order()?;
        self.init_rat_minmax()?;
        self.init_and()?;
        self.init_eq()?; // Required for `Eq.subst` / `Eq.symm` in T2 proofs (#3490)
                         // Required for `Rat.sub_nonneg_of_le` / `Rat.mul_sub` /
                         // `Rat.le_of_sub_nonneg` in T3 constructive `mul_nonneg_le_left`
                         // (#3490 T3, #3503).
        self.init_nn_verify_rat_ordering()?;
        self.init_nn_verify_proofs()?;
        // The W+/W- decomposition lemmas are proved constructively from the
        // foundational Rat min/max lattice lemmas (`Rat.le_max_left`,
        // `Rat.min_le_left`). Register them here (idempotent) so the proof
        // terms in `nn_verify_ibp_linear_decomp` resolve regardless of seed
        // ordering. See #3366 / soundness-certificate capstone.
        super::nn_verify_interval_arith_t09_t10_proof::register_rat_min_max_lemmas(self)?;

        let c = IbpLinearConsts::new();
        self.register_mul_nonneg_le_left(&c)?;
        self.register_mul_nonpos_le_left(&c)?;
        self.register_add_le_add(&c)?;
        self.register_le_of_eq_of_le(&c)?;
        self.register_le_of_le_of_eq(&c)?;
        self.register_w_decomp()?;
        self.register_ibp_linear_bounds(&c)?;
        self.register_ibp_linear_sound_impl(&c)?;

        self.nn_verify_ibp_linear_init = true;
        Ok(())
    }

    /// `NNVerify.mul_nonneg_le_left`:
    /// `forall (w a b : Rat), LE.le Rat.zero w -> LE.le a b -> LE.le (Rat.mul w a) (Rat.mul w b)`
    ///
    /// Multiplication by a nonnegative scalar preserves order.
    ///
    /// **Constructive proof (#3490 T3, unblocked by #3503):** Built from
    /// `Rat.sub_nonneg_of_le`, `Rat.mul_nonneg`, `Rat.mul_sub`,
    /// `Eq.subst`, and `Rat.le_of_sub_nonneg`. Zero `sorry` in the proof
    /// term; transitive closure contains only honest Rat ordered-field
    /// axioms. Previously sorry-inhabited `Declaration::Opaque` (#3366).
    ///
    /// Proof sketch: `w*a ≤ w*b ⟺ 0 ≤ w*b - w*a = w*(b-a)`, and the
    /// RHS is non-negative by `Rat.mul_nonneg` applied to `h_w_nn` and
    /// `Rat.sub_nonneg_of_le a b h_ab`.
    ///
    /// See `nn_verify_ibp_linear_mul_le::build_mul_nonneg_le_left_proof`
    /// for the proof term builder.
    fn register_mul_nonneg_le_left(&mut self, c: &IbpLinearConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.mul_nonneg_le_left"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(c.rat.clone());
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let h_nonneg = c.rat_le(c.rat_zero.clone(), w.clone());
            let h_le = c.rat_le(a.clone(), bv.clone());
            let concl = c.rat_le(c.mul(w.clone(), a), c.mul(w, bv));
            let (h2_id, _) = b.fresh_local(h_le.clone());
            let (h1_id, _) = b.fresh_local(h_nonneg.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, h_le, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h_nonneg, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(w_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = super::nn_verify_ibp_linear_mul_le::build_mul_nonneg_le_left_proof(c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.mul_nonneg_le_left"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.mul_nonpos_le_left`:
    /// `forall (w a b : Rat), LE.le w Rat.zero -> LE.le a b -> LE.le (Rat.mul w b) (Rat.mul w a)`
    ///
    /// Multiplication by a nonpositive scalar reverses order.
    fn register_mul_nonpos_le_left(&mut self, c: &IbpLinearConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.mul_nonpos_le_left"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(c.rat.clone());
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let h_nonpos = c.rat_le(w.clone(), c.rat_zero.clone());
            let h_le = c.rat_le(a.clone(), bv.clone());
            let concl = c.rat_le(c.mul(w.clone(), bv), c.mul(w, a));
            let (h2_id, _) = b.fresh_local(h_le.clone());
            let (h1_id, _) = b.fresh_local(h_nonpos.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, h_le, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h_nonpos, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(w_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        // Constructive proof (#3490 Batch 0 final): built from `mul_nonneg_le_left`
        // applied to `(-w)`, then transformed via `add_right_cancel` identities
        // for `-(-x) = x`. No `sorry`. See `nn_verify_ibp_linear_mul_nonpos_le.rs`
        // for the full proof outline.
        let value = super::nn_verify_ibp_linear_mul_nonpos_le::build_mul_nonpos_le_left_proof(c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.mul_nonpos_le_left"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.add_le_add`:
    /// `forall (a1 b1 a2 b2 : Rat), LE.le a1 b1 -> LE.le a2 b2 ->
    ///     LE.le (Rat.add a1 a2) (Rat.add b1 b2)`
    ///
    /// Addition preserves order on both arguments.
    ///
    /// **Constructive proof (#3490 Batch 0):** Built from the foundational
    /// order axiom `Rat.add_le_add_left`, the field axiom `Rat.add_comm`,
    /// the transitive axiom `Rat.le_trans`, and `Eq.subst`. Zero `sorry`
    /// in the proof term; transitive closure references only honest Rat
    /// ordered-field axioms. Previously sorry-inhabited `Declaration::Opaque`
    /// (#3366).
    ///
    /// Proof sketch: chain
    /// `a1+a2 = a2+a1 ≤ a2+b1 = b1+a2 ≤ b1+b2` via `Rat.add_le_add_left`
    /// at both ends + `Rat.add_comm`-driven `Eq.subst` rewrites +
    /// `Rat.le_trans` to collapse the two inequalities.
    ///
    /// See `nn_verify_ibp_linear_add_le::build_add_le_add_proof` for the
    /// proof term builder.
    fn register_add_le_add(&mut self, c: &IbpLinearConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.add_le_add"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a1_id, a1) = b.fresh_local(c.rat.clone());
            let (b1_id, b1v) = b.fresh_local(c.rat.clone());
            let (a2_id, a2) = b.fresh_local(c.rat.clone());
            let (b2_id, b2v) = b.fresh_local(c.rat.clone());
            let h1 = c.rat_le(a1.clone(), b1v.clone());
            let h2 = c.rat_le(a2.clone(), b2v.clone());
            let concl = c.rat_le(c.add(a1, a2), c.add(b1v, b2v));
            let (h2_id, _) = b.fresh_local(h2.clone());
            let (h1_id, _) = b.fresh_local(h1.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1, e);
            let e = b.mk_pi(b2_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a2_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(b1_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a1_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = super::nn_verify_ibp_linear_add_le::build_add_le_add_proof(c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.add_le_add"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.le_of_eq_of_le`:
    /// `forall (a b c : Rat), Eq @Rat a b -> LE.le b c -> LE.le a c`
    ///
    /// Transport LE across an equality on the left.
    ///
    /// **Constructive proof (#3490 T2):** Built from `Eq.subst` + `Eq.symm`
    /// — zero domain axioms, only foundational `Eq.subst`/`Eq.symm`.
    ///
    /// Proof term:
    /// ```text
    /// fun a b c (h_eq : Eq a b) (h_le : b ≤ c) =>
    ///   Eq.subst.{1} (α := Rat) (motive := fun x => x ≤ c)
    ///                (a := b) (b := a) (Eq.symm.{1} a b h_eq) h_le
    /// ```
    fn register_le_of_eq_of_le(&mut self, c: &IbpLinearConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.le_of_eq_of_le"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let (cv_id, cv) = b.fresh_local(c.rat.clone());
            let h_eq = c.rat_eq(a.clone(), bv.clone());
            let h_le = c.rat_le(bv, cv.clone());
            let concl = c.rat_le(a, cv);
            let (h2_id, _) = b.fresh_local(h_le.clone());
            let (h1_id, _) = b.fresh_local(h_eq.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, h_le, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h_eq, e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = super::nn_verify_ibp_linear_transport::build_le_of_eq_of_le_proof(c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.le_of_eq_of_le"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.le_of_le_of_eq`:
    /// `forall (a b c : Rat), LE.le a b -> Eq @Rat b c -> LE.le a c`
    ///
    /// Transport LE across an equality on the right.
    ///
    /// **Constructive proof (#3490 T2):** Built from `Eq.subst` — zero
    /// domain axioms, only foundational `Eq.subst`.
    ///
    /// Proof term:
    /// ```text
    /// fun a b c (h_le : a ≤ b) (h_eq : Eq b c) =>
    ///   Eq.subst.{1} (α := Rat) (motive := fun x => a ≤ x)
    ///                (a := b) (b := c) h_eq h_le
    /// ```
    fn register_le_of_le_of_eq(&mut self, c: &IbpLinearConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.le_of_le_of_eq"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let (cv_id, cv) = b.fresh_local(c.rat.clone());
            let h_le = c.rat_le(a.clone(), bv.clone());
            let h_eq = c.rat_eq(bv, cv.clone());
            let concl = c.rat_le(a, cv);
            let (h2_id, _) = b.fresh_local(h_eq.clone());
            let (h1_id, _) = b.fresh_local(h_le.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, h_eq, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h_le, e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = super::nn_verify_ibp_linear_transport::build_le_of_le_of_eq_proof(c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.le_of_le_of_eq"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Register `NNVerify.ibp_linear_bounds`:
    /// `(m n : Nat) -> NNMat m n -> NNVec m -> IntervalBounds n -> IntervalBounds m`
    ///
    /// Computes the IBP output bounds for a linear layer `y = W·x + b` via the
    /// W+/W- decomposition. Now a faithful reducible `Declaration::Definition`
    /// (was an uninterpreted `Declaration::Axiom`):
    /// ```text
    /// lo' j = Σ_i (w_pos j i · B.lower i + w_neg j i · B.upper i) + b j
    /// hi' j = Σ_i (w_neg j i · B.lower i + w_pos j i · B.upper i) + b j
    /// ```
    /// with `valid : ∀ j, lo' j ≤ hi' j` proved CONSTRUCTIVELY (no `sorry`) from
    /// per-summand monotonicity (`w_pos_nonneg` / `w_neg_nonpos` / `B.valid` +
    /// `mul_nonneg_le_left` / `mul_nonpos_le_left` + `Fin.sum_le`). See
    /// `nn_verify_ibp_linear_define::build_ibp_linear_bounds_value`.
    fn register_ibp_linear_bounds(&mut self, c: &IbpLinearConsts) -> Result<(), EnvError> {
        // GUARDED SWAP: if a prior init registered this as the legacy Axiom,
        // leave it (idempotent). A fresh env registers the Definition.
        if self
            .get_const(&Name::from_string("NNVerify.ibp_linear_bounds"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let vec_m = c.vec_of(m.clone());
            let ib_n = c.ib_of(n.clone());
            let ib_m = c.ib_of(m.clone());
            let (w_id, _) = b.fresh_local(mat_mn.clone());
            let (bias_id, _) = b.fresh_local(vec_m.clone());
            let (ib_id, _) = b.fresh_local(ib_n.clone());
            let e = b.mk_pi(ib_id, BinderInfo::Default, ib_n, ib_m);
            let e = b.mk_pi(bias_id, BinderInfo::Default, vec_m, e);
            let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        let value = super::nn_verify_ibp_linear_define::build_ibp_linear_bounds_value(c);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.ibp_linear_bounds"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}
