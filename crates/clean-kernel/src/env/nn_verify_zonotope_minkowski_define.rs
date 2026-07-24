// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful, kernel-checked reducible `Declaration::Definition` for
//! `NNVerify.Zonotope.minkowski_add` — generator concatenation over the real
//! `Zonotope` carrier.
//!
//! `minkowski_add` was previously a bare `Declaration::Axiom`. This module
//! replaces it with a real reducible term: the Minkowski sum of two zonotopes
//! (same center addition, generator matrices side-by-side concatenated along
//! the `Fin (k1 + k2)` index). The `Fin` index split routes each output
//! generator column to `z1` (when the index `< k1`) or `z2` (when `≥ k1`), via
//! `Decidable.rec` on `Nat.decLt`, with the `z2` branch's `Fin k2` re-index
//! built from a kernel-checked bound proof.
//!
//! ## Body unfolding
//!
//! ```text
//! NNVerify.Zonotope.minkowski_add {n k1 k2} z1 z2 :=
//!   Zonotope.mk (NNVec.add n z1.center z2.center)
//!     (fun (i : Fin n) (j : Fin (k1 + k2)) =>
//!       if h : (j.val < k1)
//!       then z1.generators i ⟨j.val, h⟩
//!       else z2.generators i ⟨j.val - k1, bound⟩)
//! ```
//!
//! ## Supporting Nat lemmas (all kernel-checked, axiom-free)
//!
//! - `Nat.add_sub_cancel_left : ∀ a b, (a + b) - a = b`
//! - `Nat.succ_sub_self        : ∀ k, (succ k) - k = succ 0`
//! - `Nat.succ_sub             : ∀ a b, b ≤ a → (succ a) - b = succ (a - b)`
//! - `Nat.sub_lt_of_lt_add     : ∀ a b c, a < (b + c) → b ≤ a → (a - b) < c`
//!
//! These compose only foundational deps (`Eq.refl`, `Eq.trans`, `Eq.symm`,
//! `congrArg`, `Nat.rec`) and already-constructive registered theorems
//! (`Nat.succ_sub_succ`, `Nat.succ_pred_of_pos`, `Nat.sub_le_sub_right`,
//! `Nat.not_lt`). No `Declaration::Axiom`, no `sorry`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Kernel constants reused across the Minkowski-add proof and definition terms.
struct MinkowskiConsts {
    nat: Expr,
    rat: Expr,
    zero: Expr,
    succ: Expr,
    add: Expr,
    sub: Expr,
    pred: Expr,
    fin: Expr,
    nat_lt: Expr,
    nat_le: Expr,
    /// `Nat.rec.{0}` — `Prop`-valued motive.
    nat_rec: Expr,
    fin_mk: Expr,
    fin_val: Expr,
    fin_islt: Expr,
    zonotope: Expr,
    zonotope_mk: Expr,
    nn_vec_add: Expr,
    /// `Eq.{1}` (`Nat : Sort 1`).
    eq: Expr,
    eq_refl: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    /// `congrArg.{1,1}`.
    congr_arg: Expr,
    /// `Decidable.rec.{1}`.
    dec_rec: Expr,
    nat_dec_lt: Expr,
    // Registered helper theorems (raw `Nat.le` / `Nat.lt` forms).
    succ_sub_succ: Expr,
    succ_pred_of_pos: Expr,
    sub_le_sub_right: Expr,
    not_lt: Expr,
}

impl MinkowskiConsts {
    fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            sub: Expr::const_(Name::from_string("Nat.sub"), vec![]),
            pred: Expr::const_(Name::from_string("Nat.pred"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat_lt: Expr::const_(Name::from_string("Nat.lt"), vec![]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            fin_mk: Expr::const_(Name::from_string("Fin.mk"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            fin_islt: Expr::const_(Name::from_string("Fin.isLt"), vec![]),
            zonotope: Expr::const_(Name::from_string("NNVerify.Zonotope"), vec![]),
            zonotope_mk: Expr::const_(Name::from_string("NNVerify.Zonotope.mk"), vec![]),
            nn_vec_add: Expr::const_(Name::from_string("NNVerify.NNVec.add"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![lvl1.clone(), lvl1]),
            dec_rec: Expr::const_(
                Name::from_string("Decidable.rec"),
                vec![Level::succ(Level::zero())],
            ),
            nat_dec_lt: Expr::const_(Name::from_string("Nat.decLt"), vec![]),
            succ_sub_succ: Expr::const_(Name::from_string("Nat.succ_sub_succ"), vec![]),
            succ_pred_of_pos: Expr::const_(Name::from_string("Nat.succ_pred_of_pos"), vec![]),
            sub_le_sub_right: Expr::const_(Name::from_string("Nat.sub_le_sub_right"), vec![]),
            not_lt: Expr::const_(Name::from_string("Nat.not_lt"), vec![]),
        }
    }

    fn add_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.add.clone(), [x, y])
    }
    fn sub_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.sub.clone(), [x, y])
    }
    fn succ_of(&self, x: Expr) -> Expr {
        Expr::app(self.succ.clone(), x)
    }
    fn pred_of(&self, x: Expr) -> Expr {
        Expr::app(self.pred.clone(), x)
    }
    fn le_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [x, y])
    }
    fn lt_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [x, y])
    }
    fn eq_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.nat.clone(), x, y])
    }
    fn eq_refl_app(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.nat.clone(), x])
    }
    /// `Eq.trans.{1} Nat x y z h1 h2 : Eq x z`.
    fn eq_trans_app(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.nat.clone(), x, y, z, h1, h2])
    }
    /// `Eq.symm.{1} Nat x y h : Eq y x`.
    fn eq_symm_app(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.nat.clone(), x, y, h])
    }
    /// `congrArg.{1,1} Nat Nat a b f h : Eq (f a) (f b)`.
    fn congr_arg_app(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nat.clone(), self.nat.clone(), a, b, f, h],
        )
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn zono_of(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.zonotope.clone(), [n.clone(), k.clone()])
    }
    /// `@Fin.val n x : Nat`.
    fn val_of(&self, n: Expr, x: Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n, x])
    }
    /// `@Fin.isLt n x : Nat.lt (Fin.val x) n`.
    fn islt_of(&self, n: Expr, x: Expr) -> Expr {
        Expr::apps(self.fin_islt.clone(), [n, x])
    }
    /// `@Fin.mk n v p : Fin n`.
    fn mk_of(&self, n: Expr, v: Expr, p: Expr) -> Expr {
        Expr::apps(self.fin_mk.clone(), [n, v, p])
    }
}

impl Environment {
    /// Register `NNVerify.Zonotope.minkowski_add` as a faithful reducible
    /// `Declaration::Definition` (generator concatenation over the real carrier),
    /// together with its supporting kernel-checked, axiom-free Nat lemmas.
    ///
    /// Idempotent. The new define and its bound-proof helpers depend only on
    /// foundational symbols and already-constructive registered theorems.
    pub(crate) fn register_zonotope_minkowski_add_define(&mut self) -> Result<(), EnvError> {
        // Dependencies for the bound proofs and the Decidable index split.
        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_eq()?;
        self.init_fin()?;
        self.init_iff()?;
        self.init_true_false()?;
        self.init_decidable()?;
        // `Nat.decLt`, `instDecidableNatLt` (the decision procedure for `<`).
        self.init_nat_decidable_ord()?;
        // `Fin.mk` / `Fin.val` / `Fin.isLt` + `Decidable` constructors.
        self.register_fin_dec_eq_proof()?;
        // `Nat.succ_sub_succ`, `Nat.succ_pred_of_pos`, `Nat.sub_le_sub_right`.
        self.register_nat_sub_order_remaining_proofs()?;
        // `Nat.not_lt` (constructive `Iff` form).
        self.init_nat_totality_proofs()?;

        let c = MinkowskiConsts::new();
        self.register_nat_succ_sub_self(&c)?;
        self.register_nat_succ_sub(&c)?;
        self.register_nat_sub_lt_of_lt_add(&c)?;
        self.register_minkowski_add_body(&c)?;
        Ok(())
    }

    /// `Nat.succ_sub_self : ∀ k, Eq Nat (Nat.sub (Nat.succ k) k) (Nat.succ Nat.zero)`.
    ///
    /// By `Nat.rec` on `k`:
    /// - base: `succ 0 - 0 ≡ succ 0`, so `Eq.refl (succ 0)`.
    /// - step: `succ (succ k) - succ k = succ k - k` (`Nat.succ_sub_succ`),
    ///   then `= succ 0` by ih, chained with `Eq.trans`.
    fn register_nat_succ_sub_self(&mut self, c: &MinkowskiConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.succ_sub_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let one = c.succ_of(c.zero.clone());

        let mut b = EnvDeclBuilder::new();
        let (k_id, k) = b.fresh_local(c.nat.clone());

        let type_ = {
            let concl = c.eq_of(c.sub_of(c.succ_of(k.clone()), k.clone()), one.clone());
            b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl))
        };

        // motive: fun (t : Nat) => Eq (succ t - t) (succ 0)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.eq_of(c.sub_of(c.succ_of(t.clone()), t.clone()), one.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body))
        };
        // base (t = 0): `succ 0 - 0 ≡ succ 0`, so `Eq.refl (succ 0)`.
        let base = c.eq_refl_app(one.clone());
        // step: fun (j : Nat) (ih : Eq (succ j - j) (succ 0)) =>
        //   Eq.trans (succ (succ j) - succ j) (succ j - j) (succ 0)
        //     (Nat.succ_sub_succ (succ j) j) ih
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = sb.fresh_local(c.nat.clone());
            let lhs = c.sub_of(c.succ_of(c.succ_of(j.clone())), c.succ_of(j.clone()));
            let mid = c.sub_of(c.succ_of(j.clone()), j.clone());
            let ih_type = c.eq_of(mid.clone(), one.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            // Nat.succ_sub_succ (succ j) j : Eq (succ (succ j) - succ j) (succ j - j)
            let sss = Expr::apps(c.succ_sub_succ.clone(), [c.succ_of(j.clone()), j.clone()]);
            let body = c.eq_trans_app(lhs, mid, one.clone(), sss, ih);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            sb.finish_child(sb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam_ih))
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, k.clone()]);
            b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), rec_app))
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term; deps are the foundational
        // `Eq.refl` / `Eq.trans` and the constructive `Nat.succ_sub_succ`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.succ_sub : ∀ a b, Nat.le b a → Eq Nat (Nat.sub (Nat.succ a) b)
    ///                        (Nat.succ (Nat.sub a b))`.
    ///
    /// By `Nat.rec` on `b` (the subtrahend, on which `Nat.sub` recurses), with
    /// the motive quantified over `a` and the hypothesis:
    ///   `P(b) := ∀ a, Nat.le b a → Eq (succ a - b) (succ (a - b))`.
    /// - base `P(0)`: `succ a - 0 ≡ succ a`, `succ (a - 0) ≡ succ a`, so refl.
    /// - step `P(k) → P(succ k)`: for `a` with `h : succ k ≤ a`,
    ///     `succ a - succ k = a - k` (`Nat.succ_sub_succ a k`),
    ///     `a - succ k ≡ pred (a - k)` (δ/ι), so the goal RHS is
    ///     `succ (pred (a - k))`; and `succ (pred (a - k)) = a - k` by
    ///     `Nat.succ_pred_of_pos (a - k) pos`, where `pos : 0 < a - k` comes from
    ///     `Nat.sub_le_sub_right (succ k) a k h : (succ k - k) ≤ (a - k)` rewritten
    ///     by `Nat.succ_sub_self k : succ k - k = succ 0` (≡ `0 < a - k`).
    fn register_nat_succ_sub(&mut self, c: &MinkowskiConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.succ_sub");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let h_type = c.le_of(bb.clone(), a.clone());
        let (h_id, _h) = b.fresh_local(h_type.clone());

        let type_ = {
            let concl = c.eq_of(
                c.sub_of(c.succ_of(a.clone()), bb.clone()),
                c.succ_of(c.sub_of(a.clone(), bb.clone())),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (t : Nat) =>
        //   ∀ (a : Nat), Nat.le t a → Eq (succ a - t) (succ (a - t))
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&mb);
                let (ma_id, ma) = ib.fresh_local(c.nat.clone());
                let mh_ty = c.le_of(t.clone(), ma.clone());
                let (mh_id, _mh) = ib.fresh_local(mh_ty.clone());
                let concl = c.eq_of(
                    c.sub_of(c.succ_of(ma.clone()), t.clone()),
                    c.succ_of(c.sub_of(ma.clone(), t.clone())),
                );
                let e = ib.mk_pi(mh_id, BinderInfo::Default, mh_ty, concl);
                let e = ib.mk_pi(ma_id, BinderInfo::Default, c.nat.clone(), e);
                ib.finish_child(e)
            };
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), inner))
        };

        // base (t = 0): fun (a : Nat) (_ : Nat.le 0 a) => Eq.refl (succ a).
        // `succ a - 0 ≡ succ a` and `succ (a - 0) ≡ succ a`.
        let base = {
            let mut cb = EnvDeclBuilder::child_of(&b);
            let (ba_id, ba) = cb.fresh_local(c.nat.clone());
            let bh_ty = c.le_of(c.zero.clone(), ba.clone());
            let (bh_id, _bh) = cb.fresh_local(bh_ty.clone());
            let refl = c.eq_refl_app(c.succ_of(ba.clone()));
            let lam_h = cb.mk_lam(bh_id, BinderInfo::Default, bh_ty, refl);
            cb.finish_child(cb.mk_lam(ba_id, BinderInfo::Default, c.nat.clone(), lam_h))
        };

        // step: fun (k : Nat) (_ih : P(k)) (a : Nat) (h : succ k ≤ a) => ...
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let ih_ty = {
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (ia_id, ia) = ib.fresh_local(c.nat.clone());
                let ih_h = c.le_of(k.clone(), ia.clone());
                let (ihh_id, _ihh) = ib.fresh_local(ih_h.clone());
                let concl = c.eq_of(
                    c.sub_of(c.succ_of(ia.clone()), k.clone()),
                    c.succ_of(c.sub_of(ia.clone(), k.clone())),
                );
                let e = ib.mk_pi(ihh_id, BinderInfo::Default, ih_h, concl);
                let e = ib.mk_pi(ia_id, BinderInfo::Default, c.nat.clone(), e);
                ib.finish_child(e)
            };
            let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
            let (sa_id, sa) = sb.fresh_local(c.nat.clone());
            let sh_ty = c.le_of(c.succ_of(k.clone()), sa.clone());
            let (sh_id, sh) = sb.fresh_local(sh_ty.clone());

            // a_minus_k = a - k
            let a_minus_k = c.sub_of(sa.clone(), k.clone());

            // pos : Nat.lt 0 (a - k) ≡ Nat.le (succ 0) (a - k).
            //   le1 : Nat.le (succ k - k) (a - k)
            //       = Nat.sub_le_sub_right (succ k) a k h
            let le1 = Expr::apps(
                c.sub_le_sub_right.clone(),
                [c.succ_of(k.clone()), sa.clone(), k.clone(), sh.clone()],
            );
            //   eq1 : Eq (succ k - k) (succ 0) = Nat.succ_sub_self k.
            let succ_sub_self_k = Expr::app(
                Expr::const_(Name::from_string("Nat.succ_sub_self"), vec![]),
                k.clone(),
            );
            //   pos = Eq.subst (motive := fun z => Nat.le z (a - k))
            //                  (succ k - k) (succ 0) eq1 le1
            //       : Nat.le (succ 0) (a - k)  ≡  Nat.lt 0 (a - k)
            let eq_subst = Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            );
            let pos_motive = {
                let mut pm = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = pm.fresh_local(c.nat.clone());
                let body = c.le_of(z.clone(), a_minus_k.clone());
                pm.finish_child(pm.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let pos = Expr::apps(
                eq_subst,
                [
                    c.nat.clone(),
                    pos_motive,
                    c.sub_of(c.succ_of(k.clone()), k.clone()),
                    c.succ_of(c.zero.clone()),
                    succ_sub_self_k,
                    le1,
                ],
            );

            // spp : Eq (succ (pred (a - k))) (a - k) = Nat.succ_pred_of_pos (a - k) pos
            let spp = Expr::apps(c.succ_pred_of_pos.clone(), [a_minus_k.clone(), pos]);
            // spp_symm : Eq (a - k) (succ (pred (a - k)))
            let spp_symm = c.eq_symm_app(
                c.succ_of(c.pred_of(a_minus_k.clone())),
                a_minus_k.clone(),
                spp,
            );

            // ssa : Eq (succ a - succ k) (a - k) = Nat.succ_sub_succ a k
            let ssa = Expr::apps(c.succ_sub_succ.clone(), [sa.clone(), k.clone()]);

            // body : Eq (succ a - succ k) (succ (pred (a - k)))
            //   = Eq.trans (succ a - succ k) (a - k) (succ (pred (a - k))) ssa spp_symm
            // and `succ (pred (a - k)) ≡ succ (a - succ k)` (a - succ k ≡ pred (a - k)),
            // so this has the goal type `Eq (succ a - succ k) (succ (a - succ k))`.
            let lhs = c.sub_of(c.succ_of(sa.clone()), c.succ_of(k.clone()));
            let rhs = c.succ_of(c.pred_of(a_minus_k.clone()));
            let body = c.eq_trans_app(lhs, a_minus_k.clone(), rhs, ssa, spp_symm);

            let lam_sh = sb.mk_lam(sh_id, BinderInfo::Default, sh_ty, body);
            let lam_sa = sb.mk_lam(sa_id, BinderInfo::Default, c.nat.clone(), lam_sh);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam_sa);
            sb.finish_child(sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih))
        };

        let value = {
            // @Nat.rec motive base step b a h
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, bb.clone()]);
            // rec_app : ∀ a, Nat.le b a → Eq (succ a - b) (succ (a - b))
            let applied = Expr::apps(rec_app, [a.clone(), _h.clone()]);
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, applied);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term; deps are foundational
        // (`Eq.refl` / `Eq.trans` / `Eq.symm` / `Eq.subst`) plus the constructive
        // `Nat.succ_sub_succ`, `Nat.succ_pred_of_pos`, `Nat.sub_le_sub_right`,
        // `Nat.succ_sub_self`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.sub_lt_of_lt_add : ∀ a b c, Nat.lt a (Nat.add b c) → Nat.le b a
    ///                          → Nat.lt (Nat.sub a b) c`.
    ///
    /// `Nat.lt x y ≡ Nat.le (succ x) y` reducibly. So the goal is
    ///   `Nat.le (succ (a - b)) c`.
    /// - `Nat.succ_sub a b h_le : succ a - b = succ (a - b)`, so
    ///   `succ (a - b) ≡ (succ a) - b` (rewrite, via `Eq.symm`).
    /// - `Nat.sub_le_sub_right (succ a) (b + c) b h_lt : (succ a - b) ≤ ((b+c)-b)`
    ///   (using `h_lt : Nat.lt a (b+c) ≡ Nat.le (succ a) (b+c)`).
    /// - `(b + c) - b ≡ c`? Not definitional — use `Nat.add_sub_cancel_left b c`.
    ///   Transport the `≤` along both rewrites with `Eq.subst`.
    fn register_nat_sub_lt_of_lt_add(&mut self, c: &MinkowskiConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.sub_lt_of_lt_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Dependency: `Nat.add_sub_cancel_left`.
        self.register_nat_add_sub_cancel_left(c)?;

        let succ_sub = Expr::const_(Name::from_string("Nat.succ_sub"), vec![]);
        let add_sub_cancel = Expr::const_(Name::from_string("Nat.add_sub_cancel_left"), vec![]);
        let eq_subst = Expr::const_(
            Name::from_string("Eq.subst"),
            vec![Level::succ(Level::zero())],
        );

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());
        let h_lt_ty = c.lt_of(a.clone(), c.add_of(bb.clone(), cc.clone()));
        let (hlt_id, hlt) = b.fresh_local(h_lt_ty.clone());
        let h_le_ty = c.le_of(bb.clone(), a.clone());
        let (hle_id, hle) = b.fresh_local(h_le_ty.clone());

        let type_ = {
            let concl = c.lt_of(c.sub_of(a.clone(), bb.clone()), cc.clone());
            let e = b.mk_pi(hle_id, BinderInfo::Default, h_le_ty.clone(), concl);
            let e = b.mk_pi(hlt_id, BinderInfo::Default, h_lt_ty.clone(), e);
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            // le_raw : Nat.le (succ a - b) ((b + c) - b)
            //        = Nat.sub_le_sub_right (succ a) (b + c) b hlt
            // (hlt : Nat.lt a (b+c) ≡ Nat.le (succ a) (b+c) accepted by defeq).
            let le_raw = Expr::apps(
                c.sub_le_sub_right.clone(),
                [
                    c.succ_of(a.clone()),
                    c.add_of(bb.clone(), cc.clone()),
                    bb.clone(),
                    hlt.clone(),
                ],
            );

            // Step 1: rewrite RHS `(b + c) - b → c` using
            //   cancel : Eq ((b + c) - b) c = Nat.add_sub_cancel_left b c.
            // motive1 z := Nat.le (succ a - b) z.
            let cancel = Expr::apps(add_sub_cancel.clone(), [bb.clone(), cc.clone()]);
            let motive1 = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = m.fresh_local(c.nat.clone());
                let body = c.le_of(c.sub_of(c.succ_of(a.clone()), bb.clone()), z.clone());
                m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let le_mid = Expr::apps(
                eq_subst.clone(),
                [
                    c.nat.clone(),
                    motive1,
                    c.sub_of(c.add_of(bb.clone(), cc.clone()), bb.clone()),
                    cc.clone(),
                    cancel,
                    le_raw,
                ],
            );
            // le_mid : Nat.le (succ a - b) c.

            // Step 2: rewrite LHS `succ a - b → succ (a - b)` using
            //   ss : Eq (succ a - b) (succ (a - b)) = Nat.succ_sub a b hle.
            // motive2 z := Nat.le z c.
            let ss = Expr::apps(succ_sub.clone(), [a.clone(), bb.clone(), hle.clone()]);
            let motive2 = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = m.fresh_local(c.nat.clone());
                let body = c.le_of(z.clone(), cc.clone());
                m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let le_final = Expr::apps(
                eq_subst,
                [
                    c.nat.clone(),
                    motive2,
                    c.sub_of(c.succ_of(a.clone()), bb.clone()),
                    c.succ_of(c.sub_of(a.clone(), bb.clone())),
                    ss,
                    le_mid,
                ],
            );
            // le_final : Nat.le (succ (a - b)) c  ≡  Nat.lt (a - b) c.

            let e = b.mk_lam(hle_id, BinderInfo::Default, h_le_ty, le_final);
            let e = b.mk_lam(hlt_id, BinderInfo::Default, h_lt_ty, e);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked term; deps are foundational `Eq.subst` plus
        // the constructive `Nat.sub_le_sub_right`, `Nat.succ_sub`,
        // `Nat.add_sub_cancel_left`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.add_sub_cancel_left : ∀ a b, Eq Nat (Nat.sub (Nat.add a b) a) b`.
    ///
    /// By `Nat.rec` on `a`:
    /// - base `a = 0`: `(0 + b) - 0 ≡ 0 + b`; `0 + b = b` by `Nat.zero_add b`.
    /// - step `a = succ k` (ih : `(k + b) - k = b`):
    ///     `(succ k + b) - succ k = (succ (k + b)) - succ k` (`Nat.succ_add k b`,
    ///       via `congrArg (· - succ k)` ... built with `Eq.subst`),
    ///     `(succ (k + b)) - succ k = (k + b) - k` (`Nat.succ_sub_succ (k+b) k`),
    ///     `= b` by ih. Chained with `Eq.trans`.
    fn register_nat_add_sub_cancel_left(&mut self, c: &MinkowskiConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.add_sub_cancel_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Dependencies: `Nat.zero_add`, `Nat.succ_add`.
        self.register_nat_zero_add_proof()?;
        self.register_nat_succ_add_proof()?;

        let zero_add = Expr::const_(Name::from_string("Nat.zero_add"), vec![]);
        let succ_add = Expr::const_(Name::from_string("Nat.succ_add"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());

        let type_ = {
            let concl = c.eq_of(
                c.sub_of(c.add_of(a.clone(), bb.clone()), a.clone()),
                bb.clone(),
            );
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Eq ((t + b) - t) b
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.eq_of(
                c.sub_of(c.add_of(t.clone(), bb.clone()), t.clone()),
                bb.clone(),
            );
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body))
        };

        // base (t = 0): `(0 + b) - 0 ≡ 0 + b`, goal `Eq (0 + b) b` = Nat.zero_add b.
        let base = Expr::app(zero_add.clone(), bb.clone());

        // step: fun (k : Nat) (ih : Eq ((k + b) - k) b) =>
        //   Eq.trans ((succ k + b) - succ k) ((k + b) - k) b
        //     step1  ih
        //   where step1 : Eq ((succ k + b) - succ k) ((k + b) - k).
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let ih_lhs = c.sub_of(c.add_of(k.clone(), bb.clone()), k.clone());
            let ih_ty = c.eq_of(ih_lhs.clone(), bb.clone());
            let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

            // sa : Eq (succ k + b) (succ (k + b)) = Nat.succ_add k b
            let sa = Expr::apps(succ_add.clone(), [k.clone(), bb.clone()]);
            // step1a : Eq ((succ k + b) - succ k) ((succ (k + b)) - succ k)
            //   = congrArg (fun z => z - succ k) sa
            let f1 = {
                let mut fb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = fb.fresh_local(c.nat.clone());
                let body = c.sub_of(z.clone(), c.succ_of(k.clone()));
                fb.finish_child(fb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let step1a = c.congr_arg_app(
                c.add_of(c.succ_of(k.clone()), bb.clone()),
                c.succ_of(c.add_of(k.clone(), bb.clone())),
                f1,
                sa,
            );
            // step1b : Eq ((succ (k + b)) - succ k) ((k + b) - k)
            //   = Nat.succ_sub_succ (k + b) k
            let step1b = Expr::apps(
                c.succ_sub_succ.clone(),
                [c.add_of(k.clone(), bb.clone()), k.clone()],
            );
            // step1 : Eq ((succ k + b) - succ k) ((k + b) - k)
            let lhs0 = c.sub_of(
                c.add_of(c.succ_of(k.clone()), bb.clone()),
                c.succ_of(k.clone()),
            );
            let mid0 = c.sub_of(
                c.succ_of(c.add_of(k.clone(), bb.clone())),
                c.succ_of(k.clone()),
            );
            let step1 = c.eq_trans_app(lhs0.clone(), mid0, ih_lhs.clone(), step1a, step1b);
            // body : Eq ((succ k + b) - succ k) b
            let body = c.eq_trans_app(lhs0, ih_lhs, bb.clone(), step1, ih);

            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
            sb.finish_child(sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih))
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, a.clone()]);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), rec_app);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term; deps are foundational
        // (`Eq.trans` / `congrArg`) plus the constructive `Nat.zero_add`,
        // `Nat.succ_add`, `Nat.succ_sub_succ`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Register `NNVerify.Zonotope.minkowski_add` as a reducible Definition.
    ///
    /// Type: `{n k1 k2 : Nat} → Zonotope n k1 → Zonotope n k2
    ///         → Zonotope n (Nat.add k1 k2)`.
    fn register_minkowski_add_body(&mut self, c: &MinkowskiConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.minkowski_add");
        // The legacy axiom (if present) must be replaced; only short-circuit when
        // the faithful Definition is already in place.
        if self
            .get_const(&name)
            .is_some_and(|ci| ci.kind == crate::env::types::ConstantKind::Definition)
        {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k1_id, k1) = b.fresh_local(c.nat.clone());
            let (k2_id, k2) = b.fresh_local(c.nat.clone());
            let zono_nk1 = c.zono_of(&n, &k1);
            let zono_nk2 = c.zono_of(&n, &k2);
            let k_sum = c.add_of(k1.clone(), k2.clone());
            let result = c.zono_of(&n, &k_sum);
            let (z1_id, _) = b.fresh_local(zono_nk1.clone());
            let (z2_id, _) = b.fresh_local(zono_nk2.clone());
            let r = b.mk_pi(z2_id, BinderInfo::Default, zono_nk2, result);
            let r = b.mk_pi(z1_id, BinderInfo::Default, zono_nk1, r);
            let r = b.mk_pi(k2_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(k1_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };

        let val = build_minkowski_value(c);

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }
}

/// Build the reducible body of `minkowski_add`:
///
/// ```text
/// fun {n k1 k2} (z1 : Zonotope n k1) (z2 : Zonotope n k2) =>
///   Zonotope.mk n (k1 + k2)
///     (NNVec.add n z1.center z2.center)
///     (fun (i : Fin n) (j : Fin (k1 + k2)) =>
///        @Decidable.rec.{1} (Nat.lt (Fin.val j) k1) (fun _ => Rat)
///          (isFalse := fun (h' : Nat.lt (val j) k1 → False) =>
///             z2.generators i ⟨val j - k1, bound⟩)
///          (isTrue  := fun (h : Nat.lt (val j) k1) =>
///             z1.generators i ⟨val j, h⟩)
///          (Nat.decLt (val j) k1))
/// ```
fn build_minkowski_value(c: &MinkowskiConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k1_id, k1) = b.fresh_local(c.nat.clone());
    let (k2_id, k2) = b.fresh_local(c.nat.clone());
    let zono_nk1 = c.zono_of(&n, &k1);
    let zono_nk2 = c.zono_of(&n, &k2);
    let (z1_id, z1) = b.fresh_local(zono_nk1.clone());
    let (z2_id, z2) = b.fresh_local(zono_nk2.clone());

    let k_sum = c.add_of(k1.clone(), k2.clone());

    // centers
    let zono_name = Name::from_string("NNVerify.Zonotope");
    let center1 = Expr::proj(zono_name.clone(), 0, z1.clone());
    let center2 = Expr::proj(zono_name.clone(), 0, z2.clone());
    // generators
    let gens1 = Expr::proj(zono_name.clone(), 1, z1.clone());
    let gens2 = Expr::proj(zono_name.clone(), 1, z2.clone());

    // new center : NNVec.add n z1.center z2.center  (NNVec.add has implicit {n}).
    let new_center = Expr::apps(c.nn_vec_add.clone(), [n.clone(), center1, center2]);

    // new generators : fun (i : Fin n) (j : Fin (k1+k2)) => <split>.
    let new_gens = build_minkowski_generators(c, &b, &n, &k1, &k2, &k_sum, gens1, gens2);

    // Zonotope.mk n (k1+k2) new_center new_gens : Zonotope n (k1+k2).
    let body = Expr::apps(
        c.zonotope_mk.clone(),
        [n.clone(), k_sum.clone(), new_center, new_gens],
    );

    let e = b.mk_lam(z2_id, BinderInfo::Default, zono_nk2, body);
    let e = b.mk_lam(z1_id, BinderInfo::Default, zono_nk1, e);
    let e = b.mk_lam(k2_id, BinderInfo::Implicit, c.nat.clone(), e);
    let e = b.mk_lam(k1_id, BinderInfo::Implicit, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
    b.finish(e)
}

/// Build `fun (i : Fin n) (j : Fin (k1+k2)) => <Decidable split>`.
#[allow(clippy::too_many_arguments)]
fn build_minkowski_generators(
    c: &MinkowskiConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k1: &Expr,
    k2: &Expr,
    k_sum: &Expr,
    gens1: Expr,
    gens2: Expr,
) -> Expr {
    let fin_n = c.fin_of(n);
    let fin_ksum = c.fin_of(k_sum);

    let mut ib = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = ib.fresh_local(fin_n.clone());

    let inner = {
        let mut jb = EnvDeclBuilder::child_of(&ib);
        let (j_id, j) = jb.fresh_local(fin_ksum.clone());

        // jval = @Fin.val (k1+k2) j : Nat
        let jval = c.val_of(k_sum.clone(), j.clone());
        // discriminant prop p = Nat.lt jval k1
        let p = c.lt_of(jval.clone(), k1.clone());

        // motive : fun (_ : Decidable p) => Rat
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&jb);
            let dec_p = Expr::app(
                Expr::const_(Name::from_string("Decidable"), vec![]),
                p.clone(),
            );
            let (d_id, _d) = mb.fresh_local(dec_p.clone());
            mb.finish_child(mb.mk_lam(d_id, BinderInfo::Default, dec_p, c.rat.clone()))
        };

        // isFalse minor : fun (h' : p → False) =>
        //   z2.generators i ⟨jval - k1, bound⟩
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
            let (hf_id, hf) = fb.fresh_local(not_p.clone());

            // h_le : Nat.le k1 jval = Iff.mp (Nat.not_lt jval k1) hf.
            //   Nat.not_lt jval k1 : Iff (Nat.lt jval k1 → False) (Nat.le k1 jval).
            let not_lt_app = Expr::apps(c.not_lt.clone(), [jval.clone(), k1.clone()]);
            let iff_a = {
                // (Nat.lt jval k1 → False)
                let mut tb = EnvDeclBuilder::child_of(&fb);
                let (x_id, _x) = tb.fresh_local(p.clone());
                tb.finish_child(tb.mk_pi(
                    x_id,
                    BinderInfo::Default,
                    p.clone(),
                    Expr::const_(Name::from_string("False"), vec![]),
                ))
            };
            let iff_b = c.le_of(k1.clone(), jval.clone());
            let h_le = Expr::apps(
                Expr::const_(Name::from_string("Iff.mp"), vec![]),
                [iff_a, iff_b, not_lt_app, hf.clone()],
            );

            // bound : Nat.lt (jval - k1) k2 = Nat.sub_lt_of_lt_add jval k1 k2 isLt h_le.
            //   isLt = @Fin.isLt (k1+k2) j : Nat.lt jval (k1+k2).
            let islt = c.islt_of(k_sum.clone(), j.clone());
            let bound = Expr::apps(
                Expr::const_(Name::from_string("Nat.sub_lt_of_lt_add"), vec![]),
                [jval.clone(), k1.clone(), k2.clone(), islt, h_le],
            );

            // idx2 : Fin k2 = @Fin.mk k2 (jval - k1) bound.
            let idx2 = c.mk_of(k2.clone(), c.sub_of(jval.clone(), k1.clone()), bound);
            // z2.generators i idx2 : Rat.
            let body = Expr::apps(gens2.clone(), [i.clone(), idx2]);
            fb.finish_child(fb.mk_lam(hf_id, BinderInfo::Default, not_p, body))
        };

        // isTrue minor : fun (h : p) =>
        //   z1.generators i ⟨jval, h⟩
        let minor_true = {
            let mut tb = EnvDeclBuilder::child_of(&jb);
            let (ht_id, ht) = tb.fresh_local(p.clone());
            // idx1 : Fin k1 = @Fin.mk k1 jval h.
            let idx1 = c.mk_of(k1.clone(), jval.clone(), ht.clone());
            let body = Expr::apps(gens1.clone(), [i.clone(), idx1]);
            tb.finish_child(tb.mk_lam(ht_id, BinderInfo::Default, p.clone(), body))
        };

        // discriminant = Nat.decLt jval k1 : Decidable (Nat.lt jval k1).
        let discriminant = Expr::apps(c.nat_dec_lt.clone(), [jval.clone(), k1.clone()]);
        // @Decidable.rec.{1} p motive minor_false minor_true discriminant
        let rec_app = Expr::apps(
            c.dec_rec.clone(),
            [p.clone(), motive, minor_false, minor_true, discriminant],
        );
        jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_ksum.clone(), rec_app))
    };

    ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), inner))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_foundation_types()
            .expect("init_nn_verify_foundation_types");
        env
    }

    #[test]
    fn test_minkowski_add_is_definition() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("NNVerify.Zonotope.minkowski_add"))
            .expect("minkowski_add should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "minkowski_add should be a faithful Definition, got {:?}",
            info.kind
        );
    }

    #[test]
    fn test_minkowski_add_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let expr = Expr::const_(Name::from_string("NNVerify.Zonotope.minkowski_add"), vec![]);
        let _ty = tc
            .infer_type(&expr)
            .unwrap_or_else(|e| panic!("minkowski_add should type-check, got {e:?}"));
    }

    /// The faithful Definition (and its bound-proof helpers) must not smuggle in
    /// any `NNVerify.*` domain axiom. Only foundational axioms (`propext`,
    /// `Quot.sound`, `Classical.choice`, `Eq` built-ins) may appear.
    #[test]
    fn test_minkowski_add_axiom_free_of_domain_axioms() {
        let env = make_env();
        let deps = env
            .axiom_deps(&Name::from_string("NNVerify.Zonotope.minkowski_add"))
            .expect("minkowski_add registered");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        let domain_axioms: Vec<&String> = names
            .iter()
            .filter(|nm| nm.starts_with("NNVerify."))
            .collect();
        assert!(
            domain_axioms.is_empty(),
            "minkowski_add must carry no NNVerify.* domain axioms, got {domain_axioms:?} \
             (full deps: {names:?})"
        );
    }

    /// The supporting Nat lemmas must themselves be fully axiom-free.
    #[test]
    fn test_minkowski_nat_helpers_axiom_free() {
        let env = make_env();
        for name in [
            "Nat.add_sub_cancel_left",
            "Nat.succ_sub_self",
            "Nat.succ_sub",
            "Nat.sub_lt_of_lt_add",
        ] {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
            assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
        }
    }
}
