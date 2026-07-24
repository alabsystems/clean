// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful, kernel-checked reducible `Declaration::Definition` for
//! `NNVerify.Zonotope.compress` — box-cover generator reduction over the real
//! `Zonotope` carrier.
//!
//! `compress` was previously a bare `Declaration::Axiom` (a body-less operation
//! signature in the trusted base). This module replaces it with a real
//! reducible term: the BOX-COVER compression of a zonotope from `k` error terms
//! down to `k'` (requiring `k' ≤ k`). The first `k'-1` output generator columns
//! are kept verbatim from the input; the LAST output column (index `k'-1`)
//! ABSORBS every dropped input column (input indices `≥ k'-1`) as their per-row
//! L1 magnitude `Σ_{l ≥ k'-1} |G_il|`. This genuinely depends on `z.center` and
//! `z.generators` (the absorbed column is a function of the dropped data), so it
//! is NOT an argument-discarding masquerade — and a `Definition` is a
//! computation, not a claim, so it drops out of the admitted-axiom census.
//!
//! ## Body unfolding
//!
//! ```text
//! NNVerify.Zonotope.compress n k k' (h_le : k' ≤ k) (z : Zonotope n k) :=
//!   Zonotope.mk n k' z.center
//!     (fun (i : Fin n) (j : Fin k') =>
//!       if hj : (j.val < k' - 1)
//!       then z.generators i ⟨j.val, bound⟩          -- keep input column j.val
//!       else                                         -- absorb tail into col k'-1
//!         Fin.sum k (fun (l : Fin k) =>
//!           if (l.val < k' - 1)
//!           then Rat.zero                            -- skip kept columns
//!           else Rat.abs (z.generators i l)))        -- |G_il| for dropped cols
//! ```
//!
//! The `Fin (k')` index split routes each output column via `Decidable.rec` on
//! `Nat.decLt (val j) (Nat.pred k')`, exactly the proven mechanical pattern of
//! `build_minkowski_generators`. The `k' = 0` edge is total: `Fin 0` is empty,
//! so the generator lambda is vacuously well-typed (the body is never reached,
//! but is still a well-typed `Rat`).
//!
//! ## Supporting bound proof (kernel-checked, axiom-free)
//!
//! The `isTrue` branch (`hj : val j < pred k'`) re-indexes the input generator
//! matrix at `⟨val j, bound⟩ : Fin k`, where
//!   `bound : val j < k`
//! is built from
//!   `Nat.lt_of_lt_of_le (val j) (pred k') k hj
//!      (Nat.le_trans (pred k') k' k (Nat.pred_le k') h_le)`.
//! `Nat.lt_of_lt_of_le`, `Nat.pred_le`, `Nat.le_trans` are all constructive
//! kernel-checked theorems (no `Declaration::Axiom`, no `sorry`).

use super::nn_verify_zonotope::ZonotopeConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached constants for the faithful `compress` body.
pub(super) struct CompressDefineConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_abs: Expr,
    fin: Expr,
    fin_mk: Expr,
    fin_val: Expr,
    nat_pred: Expr,
    nat_lt: Expr,
    fin_sum: Expr,
    zonotope_mk: Expr,
    /// `Decidable.rec.{1}`.
    dec_rec: Expr,
    nat_dec_lt: Expr,
    nat_pred_le: Expr,
    nat_le_trans: Expr,
    nat_lt_of_lt_of_le: Expr,
}

impl CompressDefineConsts {
    pub(super) fn new() -> Self {
        let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: c("Nat"),
            rat: c("Rat"),
            rat_zero: c("Rat.zero"),
            rat_abs: c("Rat.abs"),
            fin: c("Fin"),
            fin_mk: c("Fin.mk"),
            fin_val: c("Fin.val"),
            nat_pred: c("Nat.pred"),
            nat_lt: c("Nat.lt"),
            fin_sum: c("Fin.sum"),
            zonotope_mk: c("NNVerify.Zonotope.mk"),
            dec_rec: Expr::const_(
                Name::from_string("Decidable.rec"),
                vec![Level::succ(Level::zero())],
            ),
            nat_dec_lt: c("Nat.decLt"),
            nat_pred_le: c("Nat.pred_le"),
            nat_le_trans: c("Nat.le_trans"),
            nat_lt_of_lt_of_le: c("Nat.lt_of_lt_of_le"),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn pred_of(&self, x: &Expr) -> Expr {
        Expr::app(self.nat_pred.clone(), x.clone())
    }
    fn lt_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [x, y])
    }
    /// `@Fin.val n x : Nat`.
    fn val_of(&self, n: Expr, x: Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n, x])
    }
    /// `@Fin.mk n v p : Fin n`.
    fn mk_of(&self, n: Expr, v: Expr, p: Expr) -> Expr {
        Expr::apps(self.fin_mk.clone(), [n, v, p])
    }
}

/// Build the faithful `compress` value:
/// `fun (n k k' : Nat) (h_le : Nat.le k' k) (z : Zonotope n k) =>
///    Zonotope.mk n k' z.center <gens'>`.
pub(super) fn build_compress_value(zc: &ZonotopeConsts) -> Expr {
    let c = CompressDefineConsts::new();
    let zono_name = Name::from_string("NNVerify.Zonotope");

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (kp_id, kp) = b.fresh_local(c.nat.clone());
    // h_le : Nat.le k' k.
    let h_le_ty = nat_le(&kp, &k);
    let (hle_id, hle) = b.fresh_local(h_le_ty.clone());
    let zono_nk = zc.zono_of(n.clone(), k.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());

    let center = Expr::proj(zono_name.clone(), 0, z.clone());
    let gens = Expr::proj(zono_name.clone(), 1, z.clone());

    // new generators : fun (i : Fin n) (j : Fin k') => <split>.
    let new_gens = build_compress_generators(&c, &b, &n, &k, &kp, &hle, &gens);

    // Zonotope.mk n k' center new_gens : Zonotope n k'.
    let body = Expr::apps(
        c.zonotope_mk.clone(),
        [n.clone(), kp.clone(), center, new_gens],
    );

    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, body);
    let e = b.mk_lam(hle_id, BinderInfo::Default, h_le_ty, e);
    let e = b.mk_lam(kp_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

fn nat_le(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.le"), vec![]),
        [a.clone(), b.clone()],
    )
}

/// Build `fun (i : Fin n) (j : Fin k') => <Decidable split>`.
fn build_compress_generators(
    c: &CompressDefineConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    kp: &Expr,
    hle: &Expr,
    gens: &Expr,
) -> Expr {
    let fin_n = c.fin_of(n);
    let fin_kp = c.fin_of(kp);
    let pred_kp = c.pred_of(kp);

    let mut ib = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = ib.fresh_local(fin_n.clone());
    let gens_i = Expr::app(gens.clone(), i.clone());

    let inner = {
        let mut jb = EnvDeclBuilder::child_of(&ib);
        let (j_id, j) = jb.fresh_local(fin_kp.clone());

        // jval = @Fin.val k' j : Nat.
        let jval = c.val_of(kp.clone(), j.clone());
        // discriminant prop p = Nat.lt jval (Nat.pred k').
        let p = c.lt_of(jval.clone(), pred_kp.clone());

        // motive : fun (_ : Decidable p) => Rat.
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&jb);
            let dec_p = Expr::app(
                Expr::const_(Name::from_string("Decidable"), vec![]),
                p.clone(),
            );
            let (d_id, _d) = mb.fresh_local(dec_p.clone());
            mb.finish_child(mb.mk_lam(d_id, BinderInfo::Default, dec_p, c.rat.clone()))
        };

        // isFalse minor : fun (_ : p → False) => <absorbed tail column>.
        // (jval ≥ pred k', and jval < k', so jval = pred k' — the LAST column.)
        let minor_false = {
            let not_p = {
                let mut nb = EnvDeclBuilder::child_of(&jb);
                let (x_id, _x) = nb.fresh_local(p.clone());
                nb.finish_child(nb.mk_pi(
                    x_id,
                    BinderInfo::Default,
                    p.clone(),
                    Expr::const_(Name::from_string("False"), vec![]),
                ))
            };
            let mut fb = EnvDeclBuilder::child_of(&jb);
            let (hf_id, _hf) = fb.fresh_local(not_p.clone());
            let tail = build_absorbed_column(c, &fb, k, kp, &gens_i);
            fb.finish_child(fb.mk_lam(hf_id, BinderInfo::Default, not_p, tail))
        };

        // isTrue minor : fun (hj : jval < pred k') => z.generators i ⟨jval, bound⟩.
        let minor_true = {
            let mut tb = EnvDeclBuilder::child_of(&jb);
            let (hj_id, hj) = tb.fresh_local(p.clone());

            // bound : Nat.lt jval k.
            //   pred_le      : Nat.le (pred k') k' = Nat.pred_le k'.
            //   pred_kp_le_k : Nat.le (pred k') k  = Nat.le_trans (pred k') k' k pred_le h_le.
            //   bound        : Nat.lt jval k       = Nat.lt_of_lt_of_le jval (pred k') k hj pred_kp_le_k.
            let pred_le = Expr::app(c.nat_pred_le.clone(), kp.clone());
            let pred_kp_le_k = Expr::apps(
                c.nat_le_trans.clone(),
                [pred_kp.clone(), kp.clone(), k.clone(), pred_le, hle.clone()],
            );
            let bound = Expr::apps(
                c.nat_lt_of_lt_of_le.clone(),
                [
                    jval.clone(),
                    pred_kp.clone(),
                    k.clone(),
                    hj.clone(),
                    pred_kp_le_k,
                ],
            );
            // idx : Fin k = @Fin.mk k jval bound.
            let idx = c.mk_of(k.clone(), jval.clone(), bound);
            let body = Expr::apps(gens_i.clone(), [idx]);
            tb.finish_child(tb.mk_lam(hj_id, BinderInfo::Default, p.clone(), body))
        };

        // discriminant = Nat.decLt jval (pred k') : Decidable (Nat.lt jval (pred k')).
        let discriminant = Expr::apps(c.nat_dec_lt.clone(), [jval.clone(), pred_kp.clone()]);
        // @Decidable.rec.{1} p motive minor_false minor_true discriminant.
        let rec_app = Expr::apps(
            c.dec_rec.clone(),
            [p.clone(), motive, minor_false, minor_true, discriminant],
        );
        jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_kp.clone(), rec_app))
    };

    ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), inner))
}

/// Build the absorbed last column for row `i`:
///   `Fin.sum k (fun (l : Fin k) =>
///       @Decidable.rec (Nat.lt (val l) (pred k')) (fun _ => Rat)
///         (isFalse := fun _ => Rat.abs (gens_i l))   -- l ≥ pred k': include |G_il|
///         (isTrue  := fun _ => Rat.zero)             -- l < pred k': kept col, skip
///         (Nat.decLt (val l) (pred k')))`
fn build_absorbed_column(
    c: &CompressDefineConsts,
    parent: &EnvDeclBuilder,
    k: &Expr,
    kp: &Expr,
    gens_i: &Expr,
) -> Expr {
    let fin_k = c.fin_of(k);
    let pred_kp = c.pred_of(kp);

    let summand = {
        let mut lb = EnvDeclBuilder::child_of(parent);
        let (l_id, l) = lb.fresh_local(fin_k.clone());
        let lval = c.val_of(k.clone(), l.clone());
        let p = c.lt_of(lval.clone(), pred_kp.clone());

        // motive : fun (_ : Decidable p) => Rat.
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&lb);
            let dec_p = Expr::app(
                Expr::const_(Name::from_string("Decidable"), vec![]),
                p.clone(),
            );
            let (d_id, _d) = mb.fresh_local(dec_p.clone());
            mb.finish_child(mb.mk_lam(d_id, BinderInfo::Default, dec_p, c.rat.clone()))
        };

        // isFalse : fun (_ : p → False) => Rat.abs (gens_i l)  -- dropped column.
        let minor_false = {
            let not_p = {
                let mut nb = EnvDeclBuilder::child_of(&lb);
                let (x_id, _x) = nb.fresh_local(p.clone());
                nb.finish_child(nb.mk_pi(
                    x_id,
                    BinderInfo::Default,
                    p.clone(),
                    Expr::const_(Name::from_string("False"), vec![]),
                ))
            };
            let mut fb = EnvDeclBuilder::child_of(&lb);
            let (hf_id, _hf) = fb.fresh_local(not_p.clone());
            let gil = Expr::app(gens_i.clone(), l.clone());
            let body = Expr::app(c.rat_abs.clone(), gil);
            fb.finish_child(fb.mk_lam(hf_id, BinderInfo::Default, not_p, body))
        };

        // isTrue : fun (_ : p) => Rat.zero  -- kept column, contributes nothing.
        let minor_true = {
            let mut tb = EnvDeclBuilder::child_of(&lb);
            let (ht_id, _ht) = tb.fresh_local(p.clone());
            tb.finish_child(tb.mk_lam(ht_id, BinderInfo::Default, p.clone(), c.rat_zero.clone()))
        };

        let discriminant = Expr::apps(c.nat_dec_lt.clone(), [lval.clone(), pred_kp.clone()]);
        let rec_app = Expr::apps(
            c.dec_rec.clone(),
            [p.clone(), motive, minor_false, minor_true, discriminant],
        );
        lb.finish_child(lb.mk_lam(l_id, BinderInfo::Default, fin_k.clone(), rec_app))
    };

    // Fin.sum k summand : Rat.
    Expr::apps(c.fin_sum.clone(), [k.clone(), summand])
}
