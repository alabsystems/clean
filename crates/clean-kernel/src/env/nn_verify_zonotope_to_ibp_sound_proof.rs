// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof term for **T12 `NNVerify.Zonotope.to_ibp_sound`**.
//!
//! `∀ (n k : Nat) (z : Zonotope n k) (x : NNVec n),
//!    Zonotope.contains n k z x → IntervalBounds.contains n (to_ibp n k z) x`.
//!
//! With the faithful `to_ibp` (`nn_verify_zonotope_to_ibp_faithful`):
//! `(to_ibp z).lower i ≡ center i − radius i`, `(to_ibp z).upper i ≡ center i +
//! radius i`, `radius i ≡ Σⱼ |G i j|`. `Zonotope.contains` and
//! `IntervalBounds.contains` are both REDUCIBLE, so the goal δ-unfolds to
//! `∀ i, (center i − radius i) ≤ x i ∧ x i ≤ (center i + radius i)` and the
//! hypothesis to `∃ ε, (∀ j, −1 ≤ εⱼ ∧ εⱼ ≤ 1) ∧ x = center + G·ε`.
//!
//! ## Proof outline
//!
//! `Exists.elim` the hypothesis to obtain `ε`, `hbound`, `hxeq : x = RHS`
//! (`RHS i ≡ center i + Σⱼ (G i j · εⱼ)`). Prove the goal for `RHS` and
//! transport it to `x` via `Eq.subst (Eq.symm hxeq)`.
//!
//! For the `RHS` goal, per `i` (writing `s := Σⱼ (G i j · εⱼ)`,
//! `r := Σⱼ |G i j|`):
//!   * **upper** `center i + s ≤ center i + r`: by `add_le_add_left`, reduce to
//!     `s ≤ r`, then `Fin.sum_le` pointwise `G i j · εⱼ ≤ |G i j|`.
//!   * **lower** `center i − r ≤ center i + s`: `center i − r ≡ center i + (−r)`,
//!     and `−r ≡ −Σ|G| = Σ(−|G|)` (`Fin.sum_neg` ⇒ transport), so by
//!     `add_le_add_left` reduce to `Σⱼ (−|G i j|) ≤ s`, then `Fin.sum_le`
//!     pointwise `−|G i j| ≤ G i j · εⱼ`.
//!
//! The two pointwise facts come from the per-summand bound `|G i j · εⱼ| ≤
//! |G i j|` (built in `nn_verify_zonotope_to_ibp_summand`): `t ≤ |t|`
//! (`Rat.le_abs_self`) and `−|t| ≤ t` (`Rat.neg_abs_le`) with `t := G i j · εⱼ`,
//! chained through `|G i j · εⱼ| ≤ |G i j|`.

use super::nn_verify_zonotope::ZonotopeConsts;
use super::nn_verify_zonotope_to_ibp_summand::SummandConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached constants for the T12 proof term.
pub(super) struct T12Consts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) fin: Expr,
    pub(super) rat_add: Expr,
    pub(super) rat_neg: Expr,
    pub(super) rat_abs: Expr,
    pub(super) rat_mul: Expr,
    pub(super) fin_sum: Expr,
    pub(super) and_intro: Expr,
    pub(super) and_left: Expr,
    pub(super) and_right: Expr,
    pub(super) exists_elim: Expr,
    pub(super) eq_symm: Expr,
    pub(super) eq_subst: Expr,
    pub(super) add_le_add_left: Expr,
    pub(super) fin_sum_le: Expr,
    pub(super) fin_sum_neg: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    /// `NNVerify.NNVec.add`, `NNVerify.NNMat.mulVec` for the RHS term.
    pub(super) nn_vec_add: Expr,
    pub(super) nn_mat_mul_vec: Expr,
    pub(super) summand: SummandConsts,
}

impl T12Consts {
    pub(super) fn new() -> Self {
        let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let l1 = Level::succ(Level::zero());
        Self {
            nat: c("Nat"),
            rat: c("Rat"),
            fin: c("Fin"),
            rat_add: c("Rat.add"),
            rat_neg: c("Rat.neg"),
            rat_abs: c("Rat.abs"),
            rat_mul: c("Rat.mul"),
            fin_sum: c("Fin.sum"),
            and_intro: c("And.intro"),
            and_left: c("And.left"),
            and_right: c("And.right"),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1]),
            add_le_add_left: c("Rat.add_le_add_left"),
            fin_sum_le: c("Fin.sum_le"),
            fin_sum_neg: c("Fin.sum_neg"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: c("instLERat"),
            nn_vec_add: c("NNVerify.NNVec.add"),
            nn_mat_mul_vec: c("NNVerify.NNMat.mulVec"),
            summand: SummandConsts::new(),
        }
    }

    /// `LE.le @Rat instLERat a b`.
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }

    fn sum(&self, k: &Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [k.clone(), f])
    }
}

/// Build the T12 proof value.
pub(super) fn build_to_ibp_sound_value(c: &ZonotopeConsts) -> Expr {
    let h = T12Consts::new();
    let zono_name = Name::from_string("NNVerify.Zonotope");

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(h.nat.clone());
    let (k_id, k) = b.fresh_local(h.nat.clone());
    let zono_nk = c.zono_of(n.clone(), k.clone());
    let vec_n = c.vec_of(n.clone());
    let vec_k = c.vec_of(k.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());
    let (x_id, x) = b.fresh_local(vec_n.clone());

    let center = Expr::proj(zono_name.clone(), 0, z.clone());
    let gens = Expr::proj(zono_name.clone(), 1, z.clone());

    // h_contains : Zonotope.contains n k z x.
    let h_contains_ty = c.contains(&n, &k, &z, &x);
    let (hc_id, hc) = b.fresh_local(h_contains_ty.clone());

    // Goal motive Q : NNVec n → Prop := fun y => IntervalBounds.contains n (to_ibp n k z) y.
    let to_ibp_app = Expr::apps(
        Expr::const_(Name::from_string("NNVerify.Zonotope.to_ibp"), vec![]),
        [n.clone(), k.clone(), z.clone()],
    );
    let q_motive = build_contains_motive(c, &b, &n, &to_ibp_app, &vec_n);

    // P_eps : NNVec k → Prop := the body of `contains z x`'s existential.
    let p_eps = build_contains_eps_pred(c, &h, &b, &n, &k, &center, &gens, &x, &vec_n, &vec_k);

    // elim_fn : ∀ (ε : NNVec k), P_eps ε → Q x.
    let elim_fn = build_elim_fn(
        c, &h, &b, &n, &k, &center, &gens, &x, &vec_n, &vec_k, &q_motive,
    );

    // @Exists.elim.{1} (NNVec k) P_eps (Q x) h_contains elim_fn.
    let goal_at_x = c.ib_contains_app(&n, &to_ibp_app, &x);
    let body = Expr::apps(
        h.exists_elim.clone(),
        [vec_k, p_eps, goal_at_x, hc, elim_fn],
    );

    let e = b.mk_lam(hc_id, BinderInfo::Default, h_contains_ty, body);
    let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, h.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, h.nat.clone(), e);
    b.finish(e)
}

/// `Q : NNVec n → Prop := fun y => IntervalBounds.contains n (to_ibp n k z) y`.
fn build_contains_motive(
    c: &ZonotopeConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    to_ibp_app: &Expr,
    vec_n: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(parent);
    let (y_id, y) = ch.fresh_local(vec_n.clone());
    let body = c.ib_contains_app(n, to_ibp_app, &y);
    ch.finish_child(ch.mk_lam(y_id, BinderInfo::Default, vec_n.clone(), body))
}

/// `P_eps : NNVec k → Prop` — byte-identical to the lambda body of the reducible
/// `Zonotope.contains n k z x` existential, so `Exists.elim`'s implicit `p`
/// matches the hypothesis type.
#[allow(clippy::too_many_arguments)]
fn build_contains_eps_pred(
    c: &ZonotopeConsts,
    h: &T12Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    center: &Expr,
    gens: &Expr,
    x: &Expr,
    vec_n: &Expr,
    vec_k: &Expr,
) -> Expr {
    let neg_one = Expr::app(
        h.rat_neg.clone(),
        Expr::const_(Name::from_string("Rat.one"), vec![]),
    );
    let fin_k = Expr::app(h.fin.clone(), k.clone());
    let mut ch = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = ch.fresh_local(vec_k.clone());

    // bounds(ε) = ∀ j : Fin k, (-1 ≤ ε j) ∧ (ε j ≤ 1).
    let bounds = {
        let mut d = EnvDeclBuilder::child_of(&ch);
        let (j_id, j) = d.fresh_local(fin_k.clone());
        let eps_j = Expr::app(eps.clone(), j);
        let conj = Expr::app(
            Expr::app(c.and.clone(), c.rat_le(neg_one.clone(), eps_j.clone())),
            c.rat_le(eps_j, c.rat_one.clone()),
        );
        d.finish_child(d.mk_pi(j_id, BinderInfo::Default, fin_k.clone(), conj))
    };
    let rhs = rhs_term(h, n, k, center, gens, &eps);
    let eq_x = c.eq_of(vec_n.clone(), x.clone(), rhs);
    let conj_body = Expr::app(Expr::app(c.and.clone(), bounds), eq_x);
    ch.finish_child(ch.mk_lam(eps_id, BinderInfo::Default, vec_k.clone(), conj_body))
}

/// `NNVec.add n center (NNMat.mulVec n k gens eps)`.
fn rhs_term(h: &T12Consts, n: &Expr, k: &Expr, center: &Expr, gens: &Expr, eps: &Expr) -> Expr {
    let mul = Expr::apps(
        h.nn_mat_mul_vec.clone(),
        [n.clone(), k.clone(), gens.clone(), eps.clone()],
    );
    Expr::apps(h.nn_vec_add.clone(), [n.clone(), center.clone(), mul])
}

/// `elim_fn : ∀ (ε : NNVec k), P_eps ε → Q x`.
#[allow(clippy::too_many_arguments)]
fn build_elim_fn(
    c: &ZonotopeConsts,
    h: &T12Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    center: &Expr,
    gens: &Expr,
    x: &Expr,
    vec_n: &Expr,
    vec_k: &Expr,
    q_motive: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = ch.fresh_local(vec_k.clone());
    let p_eps_ty = {
        // P_eps ε (the conj type) — recompute its body inline.
        let pred = build_contains_eps_pred(c, h, &ch, n, k, center, gens, x, vec_n, vec_k);
        Expr::app(pred, eps.clone())
    };
    let (hand_id, hand) = ch.fresh_local(p_eps_ty.clone());

    // hxeq : x = RHS  (And.right of hand). The conj props are needed explicitly.
    let rhs = rhs_term(h, n, k, center, gens, &eps);
    let bounds_prop = bounds_prop_of(c, h, &ch, k, &eps);
    let eqx_prop = c.eq_of(vec_n.clone(), x.clone(), rhs.clone());
    let hxeq = Expr::apps(
        h.and_right.clone(),
        [bounds_prop.clone(), eqx_prop.clone(), hand.clone()],
    );
    let hbound = Expr::apps(h.and_left.clone(), [bounds_prop, eqx_prop, hand.clone()]);

    // proof_rhs : Q RHS  (the goal with x replaced by RHS).
    let proof_rhs = super::nn_verify_zonotope_to_ibp_sound_rhs::build_q_at_rhs(
        h, &ch, n, k, center, gens, &eps, &hbound,
    );

    // Transport Q RHS → Q x via Eq.subst (Eq.symm hxeq).
    // @Eq.symm.{1} (NNVec n) x RHS hxeq : RHS = x.
    let h_symm = Expr::apps(
        h.eq_symm.clone(),
        [vec_n.clone(), x.clone(), rhs.clone(), hxeq],
    );
    // @Eq.subst.{1} (NNVec n) Q RHS x (RHS = x) (Q RHS) : Q x.
    let q_at_x = Expr::apps(
        h.eq_subst.clone(),
        [
            vec_n.clone(),
            q_motive.clone(),
            rhs,
            x.clone(),
            h_symm,
            proof_rhs,
        ],
    );

    let inner = ch.mk_lam(hand_id, BinderInfo::Default, p_eps_ty, q_at_x);
    ch.finish_child(ch.mk_lam(eps_id, BinderInfo::Default, vec_k.clone(), inner))
}

/// `bounds(ε) = ∀ j, (-1 ≤ ε j) ∧ (ε j ≤ 1)` — the first conjunct's PROP.
fn bounds_prop_of(
    c: &ZonotopeConsts,
    h: &T12Consts,
    parent: &EnvDeclBuilder,
    k: &Expr,
    eps: &Expr,
) -> Expr {
    let neg_one = Expr::app(
        h.rat_neg.clone(),
        Expr::const_(Name::from_string("Rat.one"), vec![]),
    );
    let fin_k = Expr::app(h.fin.clone(), k.clone());
    let mut d = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = d.fresh_local(fin_k.clone());
    let eps_j = Expr::app(eps.clone(), j);
    let conj = Expr::app(
        Expr::app(c.and.clone(), c.rat_le(neg_one.clone(), eps_j.clone())),
        c.rat_le(eps_j, c.rat_one.clone()),
    );
    d.finish_child(d.mk_pi(j_id, BinderInfo::Default, fin_k.clone(), conj))
}

// Re-export the consts helpers for the rhs/summand submodules.
impl T12Consts {
    pub(super) fn rat_le_pub(&self, a: Expr, b: Expr) -> Expr {
        self.rat_le(a, b)
    }
    pub(super) fn add_pub(&self, a: Expr, b: Expr) -> Expr {
        self.add(a, b)
    }
    pub(super) fn sum_pub(&self, k: &Expr, f: Expr) -> Expr {
        self.sum(k, f)
    }
}
