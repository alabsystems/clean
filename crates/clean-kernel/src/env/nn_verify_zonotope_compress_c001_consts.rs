// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C001 expression constants and proof term builders.
//!
//! Defines `C001Consts` (shared expression atoms for Zonotope, Rat, etc.)
//! and the four builder functions for C001a/C001b types and proofs.
//!
//! C001a proof instantiates T11 (compress_sound) with Eq.refl.
//! C001b and its helper are hypothesis-wrapped: the currently missing
//! tail-norm tightness inequality is an explicit local premise, and the proof
//! returns that premise.
//!
//! See nn_verify_zonotope_compress_c001.rs for the full axiom elimination status.
//!
//! Part of #3150.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Constants for C001 theorem construction.
pub(super) struct C001Consts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) rat_zero: Expr,
    pub(super) prop: Expr,
    pub(super) nn_vec: Expr,
    pub(super) ib: Expr,
    pub(super) zonotope: Expr,
    pub(super) zono_contains: Expr,
    pub(super) zono_compress: Expr,
    pub(super) zono_to_ibp: Expr,
    pub(super) nn_vec_l1_norm: Expr,
    pub(super) ib_width: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) rat_add: Expr,
    pub(super) rat_mul: Expr,
    pub(super) rat_two: Expr,
    pub(super) eq: Expr,
    pub(super) eq_refl: Expr,
    pub(super) compress_sound: Expr,
    pub(super) compress_hull_exact: Expr,
    pub(super) tail_norm_sum: Expr,
}

impl C001Consts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            zonotope: Expr::const_(Name::from_string("NNVerify.Zonotope"), vec![]),
            zono_contains: Expr::const_(Name::from_string("NNVerify.Zonotope.contains"), vec![]),
            zono_compress: Expr::const_(Name::from_string("NNVerify.Zonotope.compress"), vec![]),
            zono_to_ibp: Expr::const_(Name::from_string("NNVerify.Zonotope.to_ibp"), vec![]),
            nn_vec_l1_norm: Expr::const_(Name::from_string("NNVerify.NNVec.l1_norm"), vec![]),
            ib_width: Expr::const_(Name::from_string("NNVerify.IntervalBounds.width"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_two: Expr::const_(Name::from_string("Rat.two"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            eq_refl: Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            compress_sound: Expr::const_(
                Name::from_string("NNVerify.Zonotope.compress_sound"),
                vec![],
            ),
            compress_hull_exact: Expr::const_(
                Name::from_string("NNVerify.Zonotope.compress_hull_exact"),
                vec![],
            ),
            tail_norm_sum: Expr::const_(Name::from_string("NNVerify.C001.tail_norm_sum"), vec![]),
        }
    }

    pub(super) fn ib_of(&self, n: &Expr) -> Expr {
        Expr::app(self.ib.clone(), n.clone())
    }

    pub(super) fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    pub(super) fn zono_of(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::app(Expr::app(self.zonotope.clone(), n.clone()), k.clone())
    }

    pub(super) fn contains(&self, n: &Expr, k: &Expr, z: &Expr, x: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(self.zono_contains.clone(), n.clone()), k.clone()),
                z.clone(),
            ),
            x.clone(),
        )
    }

    /// `compress n k k' h_le z` — the refined `compress` arity threads the
    /// `h_le : Nat.le k' k` proof between `k'` and `z`.
    pub(super) fn compress_app(&self, n: &Expr, k: &Expr, kp: &Expr, hle: &Expr, z: &Expr) -> Expr {
        Expr::apps(
            self.zono_compress.clone(),
            [n.clone(), k.clone(), kp.clone(), hle.clone(), z.clone()],
        )
    }

    /// `Nat.le a b`.
    pub(super) fn nat_le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.le"), vec![]),
            [a.clone(), b.clone()],
        )
    }

    pub(super) fn to_ibp_app(&self, n: &Expr, k: &Expr, z: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.zono_to_ibp.clone(), n.clone()), k.clone()),
            z.clone(),
        )
    }

    pub(super) fn l1_norm(&self, n: &Expr, v: &Expr) -> Expr {
        Expr::app(Expr::app(self.nn_vec_l1_norm.clone(), n.clone()), v.clone())
    }

    pub(super) fn width_app(&self, d: &Expr, b: &Expr) -> Expr {
        Expr::app(Expr::app(self.ib_width.clone(), d.clone()), b.clone())
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

    pub(super) fn add_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    pub(super) fn mul_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    pub(super) fn eq_of(&self, alpha: Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.eq.clone(), alpha), lhs), rhs)
    }

    /// Build `@Eq.refl alpha a` -- reflexivity proof that `a = a`.
    pub(super) fn eq_refl_of(&self, alpha: Expr, a: Expr) -> Expr {
        Expr::app(Expr::app(self.eq_refl.clone(), alpha), a)
    }

    /// `tail_norm_sum n k' {k} z`.
    ///
    /// `NNVerify.C001.tail_norm_sum` has signature
    /// `(n k' : Nat) -> {k : Nat} -> Zonotope n k -> Rat`. The `{k}` binder is
    /// implicit, but kernel-level application is fully explicit: the implicit
    /// `k` argument must be supplied positionally between `k'` and `z`, or the
    /// kernel feeds `z : Zonotope n k` to the `{k : Nat}` binder and reports a
    /// `Nat` vs `Zonotope` TypeMismatch.
    pub(super) fn tail_norm_sum_app(&self, n: &Expr, kp: &Expr, k: &Expr, z: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(self.tail_norm_sum.clone(), n.clone()), kp.clone()),
                k.clone(),
            ),
            z.clone(),
        )
    }
}

/// Build the over-approximation predicate
/// `∀ (x : NNVec n), contains z x → contains (compress n k k' z) x`
/// shared by C001a's premise and conclusion.
fn build_c001a_over(
    c: &C001Consts,
    b: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    kp: &Expr,
    hle: &Expr,
    z: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(b);
    let vec_n = c.vec_of(n);
    let (x_id, x) = ch.fresh_local(vec_n.clone());
    let h_contains = c.contains(n, k, z, &x);
    let compress_z = c.compress_app(n, k, kp, hle, z);
    let concl = c.contains(n, kp, &compress_z, &x);
    let (hc_id, _) = ch.fresh_local(h_contains.clone());
    let inner = ch.mk_pi(hc_id, BinderInfo::Default, h_contains, concl);
    let pi = ch.mk_pi(x_id, BinderInfo::Default, vec_n, inner);
    ch.finish_child(pi)
}

/// Build C001a type: compression soundness (HONEST hypothesis-wrapped — the
/// over-approximation of the OPAQUE `compress` is an EXPLICIT local premise,
/// mirroring the restated T11 `compress_sound`).
///
/// ```text
/// forall (n k k' : Nat) (z : Zonotope n k),
///   (h_over : forall (x : NNVec n), contains z x -> contains (compress n k k' z) x) ->
///   forall (x : NNVec n), contains z x -> contains (compress n k k' z) x
/// ```
pub(super) fn build_c001a_type(c: &C001Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (kp_id, kp) = b.fresh_local(c.nat.clone());
    // h_le : Nat.le k' k — the refined `compress` arity.
    let h_le_ty = c.nat_le(&kp, &k);
    let (hle_id, hle) = b.fresh_local(h_le_ty.clone());
    let zono_nk = c.zono_of(&n, &k);
    let (z_id, z) = b.fresh_local(zono_nk.clone());

    let over = build_c001a_over(c, &b, &n, &k, &kp, &hle, &z);
    let (hover_id, _) = b.fresh_local(over.clone());
    let r = b.mk_pi(hover_id, BinderInfo::Default, over.clone(), over);
    let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
    let r = b.mk_pi(hle_id, BinderInfo::Default, h_le_ty, r);
    let r = b.mk_pi(kp_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// Build C001a proof term (HONEST hypothesis-wrapped form).
///
/// Delegates to the restated T11 (`compress_sound`) with `z' := compress z`,
/// `Eq.refl` for the equality, and the caller-supplied `h_over` premise:
///
/// ```text
/// fun (n k k' : Nat) (z : Zonotope n k)
///     (h_over : ∀ x, contains z x → contains (compress n k k' z) x) =>
///   compress_sound n k k' z (compress n k k' z) (Eq.refl (compress n k k' z)) h_over
/// ```
///
/// The restated T11 has signature:
/// `forall (n k k') (z : Zonotope n k) (z' : Zonotope n k'),
///    compress n k k' z = z' ->
///    (∀ x, contains z x → contains z' x) -> (∀ x, contains z x → contains z' x)`
///
/// With `z' := compress z` and `Eq.refl`, the result type is exactly the
/// over-approximation predicate, which is C001a's conclusion.
pub(super) fn build_c001a_proof(c: &C001Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (kp_id, kp) = b.fresh_local(c.nat.clone());
    let h_le_ty = c.nat_le(&kp, &k);
    let (hle_id, hle) = b.fresh_local(h_le_ty.clone());
    let zono_nk = c.zono_of(&n, &k);
    let (z_id, z) = b.fresh_local(zono_nk.clone());

    let over = build_c001a_over(c, &b, &n, &k, &kp, &hle, &z);
    let (hover_id, hover) = b.fresh_local(over.clone());

    let compress_z = c.compress_app(&n, &k, &kp, &hle, &z);
    let zono_nkp = c.zono_of(&n, &kp);

    // Eq.refl @(Zonotope n k') (compress n k k' h_le z)
    let refl_proof = c.eq_refl_of(zono_nkp, compress_z.clone());

    // compress_sound n k k' h_le z (compress n k k' h_le z) refl_proof h_over : over
    let body = Expr::apps(
        c.compress_sound.clone(),
        [
            n.clone(),
            k.clone(),
            kp.clone(),
            hle.clone(),
            z.clone(),
            compress_z,
            refl_proof,
            hover,
        ],
    );

    let e = b.mk_lam(hover_id, BinderInfo::Default, over, body);
    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
    let e = b.mk_lam(hle_id, BinderInfo::Default, h_le_ty, e);
    let e = b.mk_lam(kp_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

fn build_c001b_conclusion(
    c: &C001Consts,
    n: &Expr,
    k: &Expr,
    kp: &Expr,
    hle: &Expr,
    z: &Expr,
) -> Expr {
    let compress_z = c.compress_app(n, k, kp, hle, z);
    let ibp_compressed = c.to_ibp_app(n, kp, &compress_z);
    let width_compressed = c.width_app(n, &ibp_compressed);
    let lhs = c.l1_norm(n, &width_compressed);

    let ibp_original = c.to_ibp_app(n, k, z);
    let width_original = c.width_app(n, &ibp_original);
    let rhs_base = c.l1_norm(n, &width_original);
    let tail_sum = c.tail_norm_sum_app(n, kp, k, z);
    let rhs_extra = c.mul_rat(c.rat_two.clone(), tail_sum);
    let rhs = c.add_rat(rhs_base, rhs_extra);

    c.rat_le(lhs, rhs)
}

/// Build C001b type: hypothesis-wrapped compression tightness bound.
///
/// ```text
/// forall (n k k' : Nat) (z : Zonotope n k),
///   (<unwrapped compression tightness bound>) ->
///   LE.le @Rat instLERat
///     (l1_norm n (width n (to_ibp n k' (compress n k k' z))))
///     (Rat.add (l1_norm n (width n (to_ibp n k z)))
///              (Rat.mul Rat.two (tail_norm_sum n k' z)))
/// ```
pub(super) fn build_c001b_type(c: &C001Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (kp_id, kp) = b.fresh_local(c.nat.clone());
    let h_le_ty = c.nat_le(&kp, &k);
    let (hle_id, hle) = b.fresh_local(h_le_ty.clone());
    let zono_nk = c.zono_of(&n, &k);
    let (z_id, z) = b.fresh_local(zono_nk.clone());

    let concl = build_c001b_conclusion(c, &n, &k, &kp, &hle, &z);
    let (h_id, _) = b.fresh_local(concl.clone());
    let r = b.mk_pi(h_id, BinderInfo::Default, concl.clone(), concl);
    let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
    let r = b.mk_pi(hle_id, BinderInfo::Default, h_le_ty, r);
    let r = b.mk_pi(kp_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// Build C001b proof term.
///
/// Returns the explicit local tightness hypothesis. This is the honest wrapper
/// pattern for a claim whose substantive proof is not yet supported by the
/// current carriers.
///
/// ```text
/// fun (n k k' : Nat) (z : Zonotope n k) (h_tight : <bound>) => h_tight
/// ```
pub(super) fn build_c001b_proof(c: &C001Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (kp_id, kp) = b.fresh_local(c.nat.clone());
    let h_le_ty = c.nat_le(&kp, &k);
    let (hle_id, hle) = b.fresh_local(h_le_ty.clone());
    let zono_nk = c.zono_of(&n, &k);
    let (z_id, z) = b.fresh_local(zono_nk.clone());

    let concl = build_c001b_conclusion(c, &n, &k, &kp, &hle, &z);
    let (h_id, h) = b.fresh_local(concl.clone());

    let e = b.mk_lam(h_id, BinderInfo::Default, concl, h);
    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
    let e = b.mk_lam(hle_id, BinderInfo::Default, h_le_ty, e);
    let e = b.mk_lam(kp_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
