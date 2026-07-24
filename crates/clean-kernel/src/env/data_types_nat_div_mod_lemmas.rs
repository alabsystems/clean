// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive prelude proofs of the two Nat div/mod value-properties:
//!
//!   `Nat.mod_lt      : ∀ (a n : Nat), Nat.lt 0 n → Nat.lt (Nat.mod a n) n`
//!   `Nat.div_add_mod : ∀ (a n : Nat),
//!        @Eq Nat (Nat.add (Nat.mul (Nat.div a n) n) (Nat.mod a n)) a`
//!
//! Both are proven down to the foundational axioms only (`propext` /
//! `Quot.sound` / `Classical.choice`): `env.axiom_deps` is EMPTY for each.
//!
//! These are reachable because `Nat.div` / `Nat.mod` are registered as GENUINE
//! structural fuel-recursive definitions (`Nat.divCore` / `Nat.modCore`) in
//! `data_types_nat.rs`, not opaque placeholders:
//!
//! ```text
//!   Nat.divCore 0        a n = 0
//!   Nat.divCore (succ f) a n
//!     = @Nat.rec (fun _ => Nat) (succ (divCore f (a-n) n)) (fun _ _ => 0) (n - a)
//!   Nat.div a 0        = 0
//!   Nat.div a (succ k) = Nat.divCore a a (succ k)
//!   Nat.modCore 0        a n = a
//!   Nat.modCore (succ f) a n
//!     = @Nat.rec (fun _ => Nat) (modCore f (a-n) n) (fun _ _ => a) (n - a)
//!   Nat.mod a n = Nat.modCore a a n
//! ```
//!
//! The proof terms here are a hand-translation of the elaborated Lean proofs
//! that pass in `clean-elab/tests/nat_mod_lt_e2e.rs` and
//! `clean-elab/tests/nat_div_e2e.rs`. Because the elaborator inserts implicit
//! arguments that we must supply explicitly here, every `Eq.symm` / `Eq.trans`
//! / `congrArg` / `Eq.subst` / `False.elim` application carries its full
//! explicit argument list.
//!
//! All helper lemmas are registered under the private `Nat.divmodAux.`
//! namespace so they do not collide with any existing `Nat.le_zero` / `Nat.key`
//! etc. The two headlines are `Nat.mod_lt` and `Nat.div_add_mod`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Bundle of the constants and small term-builders the div/mod proofs need.
///
/// Everything is `Nat`-monomorphic, so `Eq`/`Eq.refl`/`Eq.symm`/`Eq.trans`/
/// `Eq.subst`/`congrArg` are pre-specialized to `Sort 1` (Nat lives in
/// `Type = Sort 1`), and `False.elim` to `Sort 0` (Prop goals).
struct Nat {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    add: Expr,
    mul: Expr,
    sub: Expr,
    pred: Expr,
    le: Expr,
    lt: Expr,
    // `fun _ : Nat => Nat`  — the `Nat.rec` motive for `Nat`-valued recursions.
    nat_motive: Expr,
    // `Nat.rec.{0}` (Prop-valued motives) and `Nat.rec.{1}` (Nat/Sort-valued).
    rec0: Expr,
    rec1: Expr,
    eq: Expr,         // @Eq.{1}
    eq_refl: Expr,    // @Eq.refl.{1}
    eq_symm: Expr,    // @Eq.symm.{1}
    eq_trans: Expr,   // @Eq.trans.{1}
    eq_subst: Expr,   // @Eq.subst.{1}
    congr_arg: Expr,  // @congrArg.{1,1}
    false_elim: Expr, // @False.elim.{0}
}

impl Nat {
    fn new() -> Self {
        let n = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let l1 = Level::succ(Level::zero());
        let nat = n("Nat");
        let nat_motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
        Self {
            zero: n("Nat.zero"),
            succ: n("Nat.succ"),
            add: n("Nat.add"),
            mul: n("Nat.mul"),
            sub: n("Nat.sub"),
            pred: n("Nat.pred"),
            le: n("Nat.le"),
            lt: n("Nat.lt"),
            nat_motive,
            rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            rec1: Expr::const_(Name::from_string("Nat.rec"), vec![l1.clone()]),
            eq: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            nat,
        }
    }

    fn succ_of(&self, x: Expr) -> Expr {
        Expr::app(self.succ.clone(), x)
    }
    fn add_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.add.clone(), [a, b])
    }
    fn mul_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul.clone(), [a, b])
    }
    fn sub_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.sub.clone(), [a, b])
    }
    /// `@Nat.le a b : Prop`
    fn le_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.le.clone(), [a, b])
    }
    /// `@Nat.lt a b : Prop`  (defeq `Nat.le (succ a) b`)
    fn lt_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.lt.clone(), [a, b])
    }
    /// `@Eq.{1} Nat lhs rhs : Prop`
    fn eq_of(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.nat.clone(), lhs, rhs])
    }
    /// `@Eq.refl.{1} Nat x : @Eq Nat x x`
    fn refl(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.nat.clone(), x])
    }
    /// `@Eq.symm.{1} Nat a b h : @Eq Nat b a`   (h : @Eq Nat a b)
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.nat.clone(), a, b, h])
    }
    /// `@Eq.trans.{1} Nat a b c h1 h2 : @Eq Nat a c`
    fn trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.nat.clone(), a, b, c, h1, h2])
    }
    /// `@Eq.subst.{1} Nat motive a b h h2 : motive b`
    ///   motive : Nat → Prop, h : @Eq Nat a b, h2 : motive a.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.nat.clone(), motive, a, b, h, h2],
        )
    }
    /// `@congrArg.{1,1} Nat Nat a1 a2 f h : @Eq Nat (f a1) (f a2)`
    fn congr_arg(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nat.clone(), self.nat.clone(), a1, a2, f, h],
        )
    }
    /// `@congrArg.{1,1} Nat Nat a1 a2 Nat.succ h`
    fn congr_succ(&self, a1: Expr, a2: Expr, h: Expr) -> Expr {
        self.congr_arg(a1, a2, self.succ.clone(), h)
    }
    /// `@congrArg.{1,1} Nat Nat a1 a2 Nat.pred h`
    fn congr_pred(&self, a1: Expr, a2: Expr, h: Expr) -> Expr {
        self.congr_arg(a1, a2, self.pred.clone(), h)
    }
    /// `@False.elim.{0} C h : C`   (C : Prop)
    fn false_elim(&self, c: Expr, h: Expr) -> Expr {
        Expr::apps(self.false_elim.clone(), [c, h])
    }
    /// `@Nat.rec.{0} motive base step major`  (Prop motive)
    fn rec0(&self, motive: Expr, base: Expr, step: Expr, major: Expr) -> Expr {
        Expr::apps(self.rec0.clone(), [motive, base, step, major])
    }
    /// `@Nat.rec.{1} motive base step major`  (Sort 1 / Nat motive)
    fn rec1(&self, motive: Expr, base: Expr, step: Expr, major: Expr) -> Expr {
        Expr::apps(self.rec1.clone(), [motive, base, step, major])
    }
    /// `@Nat.rec.{1} (fun _ => Nat) zcase scase major` — the inline
    /// `Nat`-valued case split used by `divCore` / `modCore` on `n - a`.
    fn nat_rec_case(&self, zcase: Expr, scase: Expr, major: Expr) -> Expr {
        self.rec1(self.nat_motive.clone(), zcase, scase, major)
    }

    fn const_(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }
}

/// Names of the private helper lemmas (under `Nat.divmodAux.`).
mod names {
    pub(super) const LE_ZERO: &str = "Nat.divmodAux.le_zero";
    pub(super) const SUCC_SUB_SUCC: &str = "Nat.divmodAux.succ_sub_succ";
    pub(super) const ZERO_SUB: &str = "Nat.divmodAux.zero_sub";
    pub(super) const SUB_POS_LT: &str = "Nat.divmodAux.sub_pos_lt";
    pub(super) const KEY: &str = "Nat.divmodAux.key";
    pub(super) const MODCORE_LT: &str = "Nat.divmodAux.modCore_lt";
    pub(super) const SUB_ZERO_LE: &str = "Nat.divmodAux.sub_zero_le";
    pub(super) const NMUL_ZERO_LEFT: &str = "Nat.divmodAux.nmul_zero_left";
    pub(super) const ADD_RIGHT_COMM: &str = "Nat.divmodAux.add_right_comm";
    pub(super) const NMUL_SUCC_LEFT: &str = "Nat.divmodAux.nmul_succ_left";
    pub(super) const SUB_ADD_CANCEL: &str = "Nat.divmodAux.sub_add_cancel";
    pub(super) const MODCORE_ZERO: &str = "Nat.divmodAux.modCore_zero";
    pub(super) const MOD_ZERO: &str = "Nat.divmodAux.mod_zero";
    pub(super) const DIVMOD_ID: &str = "Nat.divmodAux.divmod_id";
}

impl Environment {
    /// Register the two Nat div/mod value-properties (`Nat.mod_lt`,
    /// `Nat.div_add_mod`) as constructive `Declaration::Theorem`s, along with
    /// their supporting helper lemmas under the `Nat.divmodAux.` namespace.
    ///
    /// # Contract
    ///
    /// REQUIRES: `Nat`, `Nat.zero/succ/add/mul/sub/pred/div/mod/divCore/modCore`,
    ///   `Nat.rec`, `Nat.le/lt`, `Eq`, `Eq.refl/symm/trans/subst`, `congrArg`,
    ///   `False.elim`, and the ordering lemmas (`Nat.le_refl`,
    ///   `Nat.not_succ_le_zero`, `Nat.sub_le`, `Nat.le_of_succ_le_succ`,
    ///   `Nat.le_trans`, `Nat.succ_le_succ`, `Nat.zero_le`, `Nat.zero_lt_succ`,
    ///   `Nat.add_assoc`, `Nat.add_comm`, `Nat.zero_add`) are registered. In a
    ///   full `with_prelude()` they all are.
    /// ENSURES: On success, `Nat.mod_lt` and `Nat.div_add_mod` are
    ///   `Declaration::Theorem`s with empty (foundational-only) axiom closures.
    /// ENSURES: Idempotent — early-returns if both headlines already exist.
    pub(crate) fn init_nat_div_mod_lemmas(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate (v4.30 census
        // 2026-07-06) — the whole family (Nat.mod_lt, Nat.divmodAux.* helpers,
        // Nat.div_add_mod) is stated over and proven through the import-gated
        // Nat.add/mul/sub/div/mod/divCore/modCore seeds (see
        // data_types_nat.rs::init_nat); the seeded Nat.mod_lt/modCore_lt were
        // 2 of the 11 Init.Prelude dup rows blocking the genuine olean
        // theorems. The genuine lemmas import through the checked path.
        // Default lane byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // IMPORT MODE (`suppress_lossy_structure_stubs`): the divergent
        // `Nat.div_add_mod` is intentionally NOT registered (see the gate on
        // `register_divmod_div_add_mod` below), so the idempotency guard keys on
        // `Nat.mod_lt` alone — the divergent constant must never be the trigger
        // for the early return, or this would loop-re-register the helpers.
        let divergent_done = self.suppress_lossy_structure_stubs
            || self
                .get_const(&Name::from_string("Nat.div_add_mod"))
                .is_some();
        if divergent_done && self.get_const(&Name::from_string("Nat.mod_lt")).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;

        let c = Nat::new();

        self.register_divmod_le_zero(&c)?;
        self.register_divmod_succ_sub_succ(&c)?;
        self.register_divmod_zero_sub(&c)?;
        self.register_divmod_sub_pos_lt(&c)?;
        self.register_divmod_key(&c)?;
        self.register_divmod_modcore_lt(&c)?;
        self.register_divmod_mod_lt(&c)?;
        self.register_divmod_sub_zero_le(&c)?;
        self.register_divmod_nmul_zero_left(&c)?;
        self.register_divmod_add_right_comm(&c)?;
        self.register_divmod_nmul_succ_left(&c)?;
        self.register_divmod_sub_add_cancel(&c)?;
        self.register_divmod_modcore_zero(&c)?;
        self.register_divmod_mod_zero(&c)?;
        self.register_divmod_divmod_id(&c)?;
        // IMPORT MODE: `Nat.div_add_mod` is the orientation-divergent factor —
        // Clean spells `(m/n)*n + m%n = m`, Lean 4 v4.8.0 core spells
        // `n*(m/n) + m%n = m` (factors SWAPPED). The `.olean` loader dedups by
        // name, so registering the commuted form first SHADOWS the genuine
        // canonical Mathlib `Nat.div_add_mod`, masking every imported proof
        // (`Nat.div_add_mod'`, `Nat.dvd_sub_mod`, `Nat.mul_div_eq_iff_dvd`) that
        // demands the canonical orientation. Withholding it in import mode lets
        // the genuine canonical lemma register through the checked import path
        // (measured +3 KernelVerified on `Mathlib/Data/Nat/Defs`). The
        // non-divergent `Nat.mod_lt` + all `Nat.divmodAux.` helpers above still
        // register (they are canonical inequalities, no orientation collision).
        // SOUNDNESS-NEUTRAL: only WITHHOLDS a Clean-native theorem in import mode;
        // the non-import lane (nn-verify IEEE754 ulp, PB algebra) is UNCHANGED.
        if !self.suppress_lossy_structure_stubs {
            self.register_divmod_div_add_mod(&c)?;
        }

        Ok(())
    }

    /// `theorem le_zero (a : Nat) (h : Nat.le a 0) : a = Nat.zero`
    ///
    /// ```text
    /// @Nat.rec (fun k => Nat.le k 0 -> (k = Nat.zero))
    ///   (fun _h0 => rfl)
    ///   (fun a' _ih hs => @False.elim (Nat.succ a' = Nat.zero) (Nat.not_succ_le_zero a' hs))
    ///   a h
    /// ```
    fn register_divmod_le_zero(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::LE_ZERO);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let not_succ_le_zero = Nat::const_("Nat.not_succ_le_zero");

        // Type: ∀ (a : Nat), Nat.le a 0 -> @Eq Nat a Nat.zero
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let hyp_ty = c.le_of(a.clone(), c.zero.clone());
        let (h_id, _h) = b.fresh_local(hyp_ty.clone());
        let concl = c.eq_of(a.clone(), c.zero.clone());
        let ty = b.mk_pi(h_id, BinderInfo::Default, hyp_ty, concl);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        // motive: fun k => Nat.le k 0 -> @Eq Nat k Nat.zero
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = mb.fresh_local(c.nat.clone());
            let body = Expr::pi(
                BinderInfo::Default,
                c.le_of(k.clone(), c.zero.clone()),
                // body of the pi must abstract over the hyp; it does not
                // mention it, so just the (shifted-free) conclusion.
                c.eq_of(k.clone(), c.zero.clone()),
            );
            mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
        };

        // base: fun (_h0 : Nat.le 0 0) => @Eq.refl Nat Nat.zero
        let base = {
            let mut bb = EnvDeclBuilder::child_of(&b);
            let (h0_id, _h0) = bb.fresh_local(c.le_of(c.zero.clone(), c.zero.clone()));
            let body = c.refl(c.zero.clone());
            bb.finish_child(bb.mk_lam(
                h0_id,
                BinderInfo::Default,
                c.le_of(c.zero.clone(), c.zero.clone()),
                body,
            ))
        };

        // step: fun (a' : Nat) (_ih : motive a') (hs : Nat.le (succ a') 0) =>
        //   @False.elim (@Eq Nat (succ a') Nat.zero) (Nat.not_succ_le_zero a' hs)
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (ap_id, ap) = sb.fresh_local(c.nat.clone());
            // ih : motive a'  =  Nat.le a' 0 -> @Eq Nat a' Nat.zero
            let ih_ty = Expr::pi(
                BinderInfo::Default,
                c.le_of(ap.clone(), c.zero.clone()),
                c.eq_of(ap.clone(), c.zero.clone()),
            );
            let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
            let hs_ty = c.le_of(c.succ_of(ap.clone()), c.zero.clone());
            let (hs_id, hs) = sb.fresh_local(hs_ty.clone());
            let goal = c.eq_of(c.succ_of(ap.clone()), c.zero.clone());
            let absurd = Expr::apps(not_succ_le_zero.clone(), [ap.clone(), hs]);
            let body = c.false_elim(goal, absurd);
            let lam = sb.mk_lam(hs_id, BinderInfo::Default, hs_ty, body);
            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
            sb.finish_child(sb.mk_lam(ap_id, BinderInfo::Default, c.nat.clone(), lam))
        };

        // value: fun (a : Nat) (h : Nat.le a 0) => @Nat.rec.{0} motive base step a h
        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vh_id, vh) = vb.fresh_local(c.le_of(va.clone(), c.zero.clone()));
            let rec = c.rec0(motive, base, step, va.clone());
            let body = Expr::app(rec, vh);
            let lam = vb.mk_lam(
                vh_id,
                BinderInfo::Default,
                c.le_of(va.clone(), c.zero.clone()),
                body,
            );
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem succ_sub_succ (x m : Nat) : sub (succ x) (succ m) = sub x m`
    ///
    /// ```text
    /// fun (x m : Nat) =>
    ///   @Nat.rec (fun k => @Eq Nat (sub (succ x) (succ k)) (sub x k))
    ///     (@Eq.refl Nat (sub x 0))
    ///     (fun j ih => congrArg Nat.pred ih)
    ///     m
    /// ```
    fn register_divmod_succ_sub_succ(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::SUCC_SUB_SUCC);
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Type: ∀ (x m : Nat), @Eq Nat (sub (succ x) (succ m)) (sub x m)
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(c.nat.clone());
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let lhs = c.sub_of(c.succ_of(x.clone()), c.succ_of(m.clone()));
        let rhs = c.sub_of(x.clone(), m.clone());
        let concl = c.eq_of(lhs, rhs);
        let ty = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(x_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        // value: fun (x m) => Nat.rec motive base step m
        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vx_id, vx) = vb.fresh_local(c.nat.clone());
            let (vm_id, vm) = vb.fresh_local(c.nat.clone());

            // motive: fun k => @Eq Nat (sub (succ x) (succ k)) (sub x k)
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let body = c.eq_of(
                    c.sub_of(c.succ_of(vx.clone()), c.succ_of(k.clone())),
                    c.sub_of(vx.clone(), k.clone()),
                );
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // base: @Eq.refl Nat (sub x 0)
            let base = c.refl(c.sub_of(vx.clone(), c.zero.clone()));
            // step: fun (j : Nat) (ih : motive j) =>
            //   congrArg Nat.pred (sub (succ x) (succ j)) (sub x j) ih
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (j_id, j) = sb.fresh_local(c.nat.clone());
                let ih_ty = c.eq_of(
                    c.sub_of(c.succ_of(vx.clone()), c.succ_of(j.clone())),
                    c.sub_of(vx.clone(), j.clone()),
                );
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let body = c.congr_pred(
                    c.sub_of(c.succ_of(vx.clone()), c.succ_of(j.clone())),
                    c.sub_of(vx.clone(), j.clone()),
                    ih,
                );
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                sb.finish_child(sb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam))
            };
            let rec = c.rec0(motive, base, step, vm.clone());
            let lam = vb.mk_lam(vm_id, BinderInfo::Default, c.nat.clone(), rec);
            let lam = vb.mk_lam(vx_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem zero_sub (m : Nat) : sub 0 m = 0`
    ///
    /// ```text
    /// fun (m : Nat) =>
    ///   @Nat.rec (fun k => @Eq Nat (sub 0 k) 0)
    ///     (@Eq.refl Nat (sub 0 0))
    ///     (fun j ih => congrArg Nat.pred ih)
    ///     m
    /// ```
    fn register_divmod_zero_sub(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::ZERO_SUB);
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Type: ∀ (m : Nat), @Eq Nat (sub 0 m) 0
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(c.sub_of(c.zero.clone(), m.clone()), c.zero.clone());
        let ty = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), concl);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vm_id, vm) = vb.fresh_local(c.nat.clone());

            // motive: fun k => @Eq Nat (sub 0 k) 0
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let body = c.eq_of(c.sub_of(c.zero.clone(), k.clone()), c.zero.clone());
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // base: @Eq.refl Nat (sub 0 0)
            let base = c.refl(c.sub_of(c.zero.clone(), c.zero.clone()));
            // step: fun (j ih) => congrArg Nat.pred (sub 0 j) 0 ih
            //   ih : @Eq Nat (sub 0 j) 0
            //   result : @Eq Nat (pred (sub 0 j)) (pred 0) = @Eq Nat (sub 0 (succ j)) 0
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (j_id, j) = sb.fresh_local(c.nat.clone());
                let ih_ty = c.eq_of(c.sub_of(c.zero.clone(), j.clone()), c.zero.clone());
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let body = c.congr_pred(c.sub_of(c.zero.clone(), j.clone()), c.zero.clone(), ih);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                sb.finish_child(sb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam))
            };
            let rec = c.rec0(motive, base, step, vm.clone());
            let lam = vb.mk_lam(vm_id, BinderInfo::Default, c.nat.clone(), rec);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem sub_pos_lt (a n : Nat) (h : Nat.lt 0 (sub n a)) : Nat.lt a n`
    ///
    /// Proven in the generalized-over-`n` form by induction on `a`. See the
    /// module-level reference; the threaded `@Eq.subst` rewrites transport the
    /// positivity hypothesis across `zero_sub` / `succ_sub_succ`.
    fn register_divmod_sub_pos_lt(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::SUB_POS_LT);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let not_succ_le_zero = Nat::const_("Nat.not_succ_le_zero");
        let succ_le_succ = Nat::const_("Nat.succ_le_succ");
        let zero_sub = Nat::const_(names::ZERO_SUB);
        let succ_sub_succ = Nat::const_(names::SUCC_SUB_SUCC);

        // Type: ∀ (a n : Nat), Nat.lt 0 (sub n a) -> Nat.lt a n
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let hyp_ty = c.lt_of(c.zero.clone(), c.sub_of(n.clone(), a.clone()));
        let (h_id, _h) = b.fresh_local(hyp_ty.clone());
        let concl = c.lt_of(a.clone(), n.clone());
        let ty = b.mk_pi(h_id, BinderInfo::Default, hyp_ty, concl);
        let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        // outer motive: fun k => ∀ (m : Nat), Nat.lt 0 (sub m k) -> Nat.lt k m
        let outer_motive = |bld: &EnvDeclBuilder| {
            let mut mb = EnvDeclBuilder::child_of(bld);
            let (k_id, k) = mb.fresh_local(c.nat.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&mb);
                let (m_id, m) = ib.fresh_local(c.nat.clone());
                let body = Expr::pi(
                    BinderInfo::Default,
                    c.lt_of(c.zero.clone(), c.sub_of(m.clone(), k.clone())),
                    c.lt_of(k.clone(), m.clone()),
                );
                ib.finish_child(ib.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), body))
            };
            mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), inner))
        };

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (vh_id, vh) =
                vb.fresh_local(c.lt_of(c.zero.clone(), c.sub_of(vn.clone(), va.clone())));

            let motive = outer_motive(&vb);

            // base: fun (m : Nat) (hm : Nat.lt 0 (sub m 0)) => hm
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&vb);
                let (m_id, m) = bb.fresh_local(c.nat.clone());
                let hm_ty = c.lt_of(c.zero.clone(), c.sub_of(m.clone(), c.zero.clone()));
                let (hm_id, hm) = bb.fresh_local(hm_ty.clone());
                let lam = bb.mk_lam(hm_id, BinderInfo::Default, hm_ty, hm);
                bb.finish_child(bb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // step: fun (a' : Nat) (ih : motive a') => fun (m : Nat) =>
            //   @Nat.rec inner_motive zcase scase m
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (ap_id, ap) = sb.fresh_local(c.nat.clone());
                // ih : ∀ (m : Nat), lt 0 (sub m a') -> lt a' m
                let ih_ty = {
                    let mut ihb = EnvDeclBuilder::child_of(&sb);
                    let (m_id, m) = ihb.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.lt_of(c.zero.clone(), c.sub_of(m.clone(), ap.clone())),
                        c.lt_of(ap.clone(), m.clone()),
                    );
                    ihb.finish_child(ihb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let (m_id, m) = sb.fresh_local(c.nat.clone());

                // inner motive: fun mm => lt 0 (sub mm (succ a')) -> lt (succ a') mm
                let inner_motive = {
                    let mut imb = EnvDeclBuilder::child_of(&sb);
                    let (mm_id, mm) = imb.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.lt_of(c.zero.clone(), c.sub_of(mm.clone(), c.succ_of(ap.clone()))),
                        c.lt_of(c.succ_of(ap.clone()), mm.clone()),
                    );
                    imb.finish_child(imb.mk_lam(mm_id, BinderInfo::Default, c.nat.clone(), body))
                };

                // zcase (mm=0): fun (h0 : lt 0 (sub 0 (succ a'))) =>
                //   @False.elim (lt (succ a') 0)
                //     (Nat.not_succ_le_zero 0
                //       (@Eq.subst Nat (fun z => lt 0 z)
                //          (sub 0 (succ a')) 0 (zero_sub (succ a')) h0))
                let zcase = {
                    let mut zb = EnvDeclBuilder::child_of(&sb);
                    let h0_ty = c.lt_of(
                        c.zero.clone(),
                        c.sub_of(c.zero.clone(), c.succ_of(ap.clone())),
                    );
                    let (h0_id, h0) = zb.fresh_local(h0_ty.clone());
                    // motive for subst: fun z => Nat.lt 0 z
                    let lt0_motive = {
                        let mut lb = EnvDeclBuilder::child_of(&zb);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        let body = c.lt_of(c.zero.clone(), z.clone());
                        lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                    };
                    // zero_sub (succ a') : @Eq Nat (sub 0 (succ a')) 0
                    let zs = Expr::app(zero_sub.clone(), c.succ_of(ap.clone()));
                    let transported = c.subst(
                        lt0_motive,
                        c.sub_of(c.zero.clone(), c.succ_of(ap.clone())),
                        c.zero.clone(),
                        zs,
                        h0,
                    );
                    // Nat.not_succ_le_zero 0 transported : False
                    let false_pf =
                        Expr::apps(not_succ_le_zero.clone(), [c.zero.clone(), transported]);
                    let goal = c.lt_of(c.succ_of(ap.clone()), c.zero.clone());
                    let body = c.false_elim(goal, false_pf);
                    zb.finish_child(zb.mk_lam(h0_id, BinderInfo::Default, h0_ty, body))
                };

                // scase (mm=succ n'): fun (n' : Nat) (_ihn : inner_motive n')
                //     (hn : lt 0 (sub (succ n') (succ a'))) =>
                //   Nat.succ_le_succ (succ a') n'
                //     (ih n'
                //       (@Eq.subst Nat (fun z => lt 0 z)
                //          (sub (succ n') (succ a')) (sub n' a')
                //          (succ_sub_succ n' a') hn))
                let scase = {
                    let mut nb = EnvDeclBuilder::child_of(&sb);
                    let (np_id, np) = nb.fresh_local(c.nat.clone());
                    // _ihn : inner_motive n' = lt 0 (sub n' (succ a')) -> lt (succ a') n'
                    let ihn_ty = Expr::pi(
                        BinderInfo::Default,
                        c.lt_of(c.zero.clone(), c.sub_of(np.clone(), c.succ_of(ap.clone()))),
                        c.lt_of(c.succ_of(ap.clone()), np.clone()),
                    );
                    let (ihn_id, _ihn) = nb.fresh_local(ihn_ty.clone());
                    let hn_ty = c.lt_of(
                        c.zero.clone(),
                        c.sub_of(c.succ_of(np.clone()), c.succ_of(ap.clone())),
                    );
                    let (hn_id, hn) = nb.fresh_local(hn_ty.clone());

                    let lt0_motive = {
                        let mut lb = EnvDeclBuilder::child_of(&nb);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        let body = c.lt_of(c.zero.clone(), z.clone());
                        lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                    };
                    // succ_sub_succ n' a' : @Eq Nat (sub (succ n')(succ a')) (sub n' a')
                    let sss = Expr::apps(succ_sub_succ.clone(), [np.clone(), ap.clone()]);
                    let transported = c.subst(
                        lt0_motive,
                        c.sub_of(c.succ_of(np.clone()), c.succ_of(ap.clone())),
                        c.sub_of(np.clone(), ap.clone()),
                        sss,
                        hn,
                    );
                    // ih n' transported : lt a' n'  =  le (succ a') n'
                    let ih_app = Expr::apps(ih.clone(), [np.clone(), transported]);
                    // Nat.succ_le_succ (succ a') n' (ih ...) : le (succ(succ a'))(succ n')
                    let body = Expr::apps(
                        succ_le_succ.clone(),
                        [c.succ_of(ap.clone()), np.clone(), ih_app],
                    );
                    let lam = nb.mk_lam(hn_id, BinderInfo::Default, hn_ty, body);
                    let lam = nb.mk_lam(ihn_id, BinderInfo::Default, ihn_ty, lam);
                    nb.finish_child(nb.mk_lam(np_id, BinderInfo::Default, c.nat.clone(), lam))
                };

                // @Nat.rec.{0} inner_motive zcase scase m
                let inner_rec = c.rec0(inner_motive, zcase, scase, m.clone());
                let lam_m = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), inner_rec);
                let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam_m);
                sb.finish_child(sb.mk_lam(ap_id, BinderInfo::Default, c.nat.clone(), lam_ih))
            };

            // @Nat.rec.{0} motive base step a   then apply  n  then  h
            let rec = c.rec0(motive, base, step, va.clone());
            let body = Expr::apps(rec, [vn.clone(), vh.clone()]);
            let lam = vb.mk_lam(
                vh_id,
                BinderInfo::Default,
                c.lt_of(c.zero.clone(), c.sub_of(vn.clone(), va.clone())),
                body,
            );
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem key (a n f : Nat) (ha : le a (succ f)) (hn : lt 0 n)
    ///   : le (sub a n) f`
    ///
    /// The decrease bound for the recursive call. Outer induction on `n`,
    /// inner induction on `a`; both branches transport along
    /// `zero_sub` / `succ_sub_succ` with `Eq.symm` + `Eq.subst`.
    fn register_divmod_key(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::KEY);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let not_succ_le_zero = Nat::const_("Nat.not_succ_le_zero");
        let zero_le = Nat::const_("Nat.zero_le");
        let le_trans = Nat::const_("Nat.le_trans");
        let sub_le = Nat::const_("Nat.sub_le");
        let le_of_succ_le_succ = Nat::const_("Nat.le_of_succ_le_succ");
        let zero_sub = Nat::const_(names::ZERO_SUB);
        let succ_sub_succ = Nat::const_(names::SUCC_SUB_SUCC);

        // Type: ∀ (a n f : Nat), le a (succ f) -> lt 0 n -> le (sub a n) f
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (f_id, f) = b.fresh_local(c.nat.clone());
        let ha_ty = c.le_of(a.clone(), c.succ_of(f.clone()));
        let (ha_id, _ha) = b.fresh_local(ha_ty.clone());
        let hn_ty = c.lt_of(c.zero.clone(), n.clone());
        let (hn_id, _hn) = b.fresh_local(hn_ty.clone());
        let concl = c.le_of(c.sub_of(a.clone(), n.clone()), f.clone());
        let ty = b.mk_pi(hn_id, BinderInfo::Default, hn_ty, concl);
        let ty = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, ty);
        let ty = b.mk_pi(f_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (vf_id, vf) = vb.fresh_local(c.nat.clone());
            let (vha_id, vha) = vb.fresh_local(c.le_of(va.clone(), c.succ_of(vf.clone())));
            let (vhn_id, vhn) = vb.fresh_local(c.lt_of(c.zero.clone(), vn.clone()));

            // outer motive: fun nn => lt 0 nn -> le (sub a nn) f
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (nn_id, nn) = mb.fresh_local(c.nat.clone());
                let body = Expr::pi(
                    BinderInfo::Default,
                    c.lt_of(c.zero.clone(), nn.clone()),
                    c.le_of(c.sub_of(va.clone(), nn.clone()), vf.clone()),
                );
                mb.finish_child(mb.mk_lam(nn_id, BinderInfo::Default, c.nat.clone(), body))
            };

            // base (nn=0): fun (h0 : lt 0 0) =>
            //   @False.elim (le (sub a 0) f) (Nat.not_succ_le_zero 0 h0)
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&vb);
                let h0_ty = c.lt_of(c.zero.clone(), c.zero.clone());
                let (h0_id, h0) = bb.fresh_local(h0_ty.clone());
                let goal = c.le_of(c.sub_of(va.clone(), c.zero.clone()), vf.clone());
                let false_pf = Expr::apps(not_succ_le_zero.clone(), [c.zero.clone(), h0]);
                let body = c.false_elim(goal, false_pf);
                bb.finish_child(bb.mk_lam(h0_id, BinderInfo::Default, h0_ty, body))
            };

            // step (nn=succ m): fun (m : Nat) (_ihn : motive m) (_hsm : lt 0 (succ m)) =>
            //   @Nat.rec inner_motive izcase iscase a ha
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (m_id, m) = sb.fresh_local(c.nat.clone());
                let ihn_ty = Expr::pi(
                    BinderInfo::Default,
                    c.lt_of(c.zero.clone(), m.clone()),
                    c.le_of(c.sub_of(va.clone(), m.clone()), vf.clone()),
                );
                let (ihn_id, _ihn) = sb.fresh_local(ihn_ty.clone());
                let hsm_ty = c.lt_of(c.zero.clone(), c.succ_of(m.clone()));
                let (hsm_id, _hsm) = sb.fresh_local(hsm_ty.clone());

                // inner motive: fun aa => le aa (succ f) -> le (sub aa (succ m)) f
                let inner_motive = {
                    let mut imb = EnvDeclBuilder::child_of(&sb);
                    let (aa_id, aa) = imb.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(aa.clone(), c.succ_of(vf.clone())),
                        c.le_of(c.sub_of(aa.clone(), c.succ_of(m.clone())), vf.clone()),
                    );
                    imb.finish_child(imb.mk_lam(aa_id, BinderInfo::Default, c.nat.clone(), body))
                };

                // izcase (aa=0): fun (_haa : le 0 (succ f)) =>
                //   @Eq.subst Nat (fun z => le z f) 0 (sub 0 (succ m))
                //     (Eq.symm (zero_sub (succ m))) (Nat.zero_le f)
                let izcase = {
                    let mut zb = EnvDeclBuilder::child_of(&sb);
                    let haa_ty = c.le_of(c.zero.clone(), c.succ_of(vf.clone()));
                    let (haa_id, _haa) = zb.fresh_local(haa_ty.clone());
                    let le_z_motive = {
                        let mut lb = EnvDeclBuilder::child_of(&zb);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        let body = c.le_of(z.clone(), vf.clone());
                        lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                    };
                    // zero_sub (succ m) : @Eq Nat (sub 0 (succ m)) 0
                    let zs = Expr::app(zero_sub.clone(), c.succ_of(m.clone()));
                    // Eq.symm : @Eq Nat 0 (sub 0 (succ m))
                    let zs_sym = c.symm(
                        c.sub_of(c.zero.clone(), c.succ_of(m.clone())),
                        c.zero.clone(),
                        zs,
                    );
                    let zle = Expr::app(zero_le.clone(), vf.clone()); // le 0 f
                    let body = c.subst(
                        le_z_motive,
                        c.zero.clone(),
                        c.sub_of(c.zero.clone(), c.succ_of(m.clone())),
                        zs_sym,
                        zle,
                    );
                    zb.finish_child(zb.mk_lam(haa_id, BinderInfo::Default, haa_ty, body))
                };

                // iscase (aa=succ a'): fun (a' : Nat) (_iha : inner_motive a')
                //     (haa : le (succ a') (succ f)) =>
                //   @Eq.subst Nat (fun z => le z f) (sub a' m) (sub (succ a')(succ m))
                //     (Eq.symm (succ_sub_succ a' m))
                //     (Nat.le_trans (sub a' m) a' f (Nat.sub_le a' m)
                //       (Nat.le_of_succ_le_succ a' f haa))
                let iscase = {
                    let mut ab = EnvDeclBuilder::child_of(&sb);
                    let (ap_id, ap) = ab.fresh_local(c.nat.clone());
                    let iha_ty = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(ap.clone(), c.succ_of(vf.clone())),
                        c.le_of(c.sub_of(ap.clone(), c.succ_of(m.clone())), vf.clone()),
                    );
                    let (iha_id, _iha) = ab.fresh_local(iha_ty.clone());
                    let haa_ty = c.le_of(c.succ_of(ap.clone()), c.succ_of(vf.clone()));
                    let (haa_id, haa) = ab.fresh_local(haa_ty.clone());

                    let le_z_motive = {
                        let mut lb = EnvDeclBuilder::child_of(&ab);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        let body = c.le_of(z.clone(), vf.clone());
                        lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                    };
                    // succ_sub_succ a' m : @Eq Nat (sub (succ a')(succ m)) (sub a' m)
                    let sss = Expr::apps(succ_sub_succ.clone(), [ap.clone(), m.clone()]);
                    // Eq.symm : @Eq Nat (sub a' m) (sub (succ a')(succ m))
                    let sss_sym = c.symm(
                        c.sub_of(c.succ_of(ap.clone()), c.succ_of(m.clone())),
                        c.sub_of(ap.clone(), m.clone()),
                        sss,
                    );
                    // Nat.le_of_succ_le_succ a' f haa : le a' f
                    let lossh =
                        Expr::apps(le_of_succ_le_succ.clone(), [ap.clone(), vf.clone(), haa]);
                    // Nat.sub_le a' m : le (sub a' m) a'
                    let subl = Expr::apps(sub_le.clone(), [ap.clone(), m.clone()]);
                    // Nat.le_trans (sub a' m) a' f subl lossh : le (sub a' m) f
                    let trans = Expr::apps(
                        le_trans.clone(),
                        [
                            c.sub_of(ap.clone(), m.clone()),
                            ap.clone(),
                            vf.clone(),
                            subl,
                            lossh,
                        ],
                    );
                    // subst (fun z => le z f) (sub a' m) (sub (succ a')(succ m)) sym trans
                    let body = c.subst(
                        le_z_motive,
                        c.sub_of(ap.clone(), m.clone()),
                        c.sub_of(c.succ_of(ap.clone()), c.succ_of(m.clone())),
                        sss_sym,
                        trans,
                    );
                    let lam = ab.mk_lam(haa_id, BinderInfo::Default, haa_ty, body);
                    let lam = ab.mk_lam(iha_id, BinderInfo::Default, iha_ty, lam);
                    ab.finish_child(ab.mk_lam(ap_id, BinderInfo::Default, c.nat.clone(), lam))
                };

                // @Nat.rec.{0} inner_motive izcase iscase a ha
                let inner_rec = c.rec0(inner_motive, izcase, iscase, va.clone());
                let inner = Expr::app(inner_rec, vha.clone());
                let lam = sb.mk_lam(hsm_id, BinderInfo::Default, hsm_ty, inner);
                let lam = sb.mk_lam(ihn_id, BinderInfo::Default, ihn_ty, lam);
                sb.finish_child(sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // @Nat.rec.{0} motive base step n   then apply  hn
            let rec = c.rec0(motive, base, step, vn.clone());
            let body = Expr::app(rec, vhn.clone());
            let lam = vb.mk_lam(
                vhn_id,
                BinderInfo::Default,
                c.lt_of(c.zero.clone(), vn.clone()),
                body,
            );
            let lam = vb.mk_lam(
                vha_id,
                BinderInfo::Default,
                c.le_of(va.clone(), c.succ_of(vf.clone())),
                lam,
            );
            let lam = vb.mk_lam(vf_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem modCore_lt (fuel : Nat)
    ///   : ∀ (a n : Nat), le a fuel -> lt 0 n -> lt (modCore fuel a n) n`
    ///
    /// The fuel induction. The step case case-splits the inline
    /// `Nat.rec (fun _ => Nat) … (n - a)` that `modCore (succ f) a n` reduces to,
    /// threading the `@Eq Nat (sub n a) s` equation through the inner motive.
    fn register_divmod_modcore_lt(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::MODCORE_LT);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let modcore = Nat::const_("Nat.modCore");
        let le_zero = Nat::const_(names::LE_ZERO);
        let key = Nat::const_(names::KEY);
        let sub_pos_lt = Nat::const_(names::SUB_POS_LT);
        let zero_lt_succ = Nat::const_("Nat.zero_lt_succ");

        // modCore fuel a n
        let modcore_of = |fuel: Expr, a: Expr, n: Expr| Expr::apps(modcore.clone(), [fuel, a, n]);

        // Type: ∀ (fuel a n : Nat), le a fuel -> lt 0 n -> lt (modCore fuel a n) n
        let mut b = EnvDeclBuilder::new();
        let (fuel_id, fuel) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let ha_ty = c.le_of(a.clone(), fuel.clone());
        let (ha_id, _ha) = b.fresh_local(ha_ty.clone());
        let hn_ty = c.lt_of(c.zero.clone(), n.clone());
        let (hn_id, _hn) = b.fresh_local(hn_ty.clone());
        let concl = c.lt_of(modcore_of(fuel.clone(), a.clone(), n.clone()), n.clone());
        let ty = b.mk_pi(hn_id, BinderInfo::Default, hn_ty, concl);
        let ty = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, ty);
        let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(fuel_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        // helper to build `∀ (a n : Nat), le a F -> lt 0 n -> lt (modCore F a n) n`
        // for a given fuel term F, as a child of the given builder.
        let mk_forall_body = |bld: &EnvDeclBuilder, fuel_term: Expr| {
            let mut fb = EnvDeclBuilder::child_of(bld);
            let (fa_id, fa) = fb.fresh_local(c.nat.clone());
            let (fn_id, fnn) = fb.fresh_local(c.nat.clone());
            let inner = c.lt_of(
                modcore_of(fuel_term.clone(), fa.clone(), fnn.clone()),
                fnn.clone(),
            );
            let inner = Expr::pi(
                BinderInfo::Default,
                c.lt_of(c.zero.clone(), fnn.clone()),
                inner,
            );
            let inner = Expr::pi(
                BinderInfo::Default,
                c.le_of(fa.clone(), fuel_term.clone()),
                inner,
            );
            let inner = fb.mk_pi(fn_id, BinderInfo::Default, c.nat.clone(), inner);
            let inner = fb.mk_pi(fa_id, BinderInfo::Default, c.nat.clone(), inner);
            fb.finish_child(inner)
        };

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vfuel_id, vfuel) = vb.fresh_local(c.nat.clone());

            // outer motive: fun f => ∀ (a n : Nat), le a f -> lt 0 n -> lt (modCore f a n) n
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (f_id, f) = mb.fresh_local(c.nat.clone());
                let body = mk_forall_body(&mb, f.clone());
                mb.finish_child(mb.mk_lam(f_id, BinderInfo::Default, c.nat.clone(), body))
            };

            // base (f=0): fun (a n : Nat) (ha : le a 0) (hn : lt 0 n) =>
            //   @Eq.subst Nat (fun z => lt z n) 0 a (Eq.symm (le_zero a ha)) hn
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&vb);
                let (ba_id, ba) = bb.fresh_local(c.nat.clone());
                let (bn_id, bn) = bb.fresh_local(c.nat.clone());
                let ha_ty = c.le_of(ba.clone(), c.zero.clone());
                let (bha_id, bha) = bb.fresh_local(ha_ty.clone());
                let hn_ty = c.lt_of(c.zero.clone(), bn.clone());
                let (bhn_id, bhn) = bb.fresh_local(hn_ty.clone());
                // motive: fun z => lt z n
                let lt_z_motive = {
                    let mut lb = EnvDeclBuilder::child_of(&bb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.lt_of(z.clone(), bn.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                // le_zero a ha : @Eq Nat a 0 ; Eq.symm : @Eq Nat 0 a
                let lz = Expr::apps(le_zero.clone(), [ba.clone(), bha]);
                let lz_sym = c.symm(ba.clone(), c.zero.clone(), lz);
                let body = c.subst(lt_z_motive, c.zero.clone(), ba.clone(), lz_sym, bhn);
                let lam = bb.mk_lam(bhn_id, BinderInfo::Default, hn_ty, body);
                let lam = bb.mk_lam(bha_id, BinderInfo::Default, ha_ty, lam);
                let lam = bb.mk_lam(bn_id, BinderInfo::Default, c.nat.clone(), lam);
                bb.finish_child(bb.mk_lam(ba_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // step (f=succ): fun (f : Nat) (ih : motive f) =>
            //   fun (a n : Nat) (ha : le a (succ f)) (hn : lt 0 n) =>
            //     @Nat.rec inner_motive zcase scase (sub n a) (@Eq.refl Nat (sub n a))
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (f_id, f) = sb.fresh_local(c.nat.clone());
                let ih_ty = mk_forall_body(&sb, f.clone());
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let (a_id, a) = sb.fresh_local(c.nat.clone());
                let (n_id, n) = sb.fresh_local(c.nat.clone());
                let ha_ty = c.le_of(a.clone(), c.succ_of(f.clone()));
                let (ha_id, ha) = sb.fresh_local(ha_ty.clone());
                let hn_ty = c.lt_of(c.zero.clone(), n.clone());
                let (hn_id, hn) = sb.fresh_local(hn_ty.clone());

                // The inline Nat-valued case-split term used in the inner motive,
                // parameterized over the case scrutinee `s`:
                //   @Nat.rec (fun _ => Nat) (modCore f (sub a n) n) (fun _ _ => a) s
                let recz = modcore_of(f.clone(), c.sub_of(a.clone(), n.clone()), n.clone());
                let recs = {
                    // fun (_ _ : Nat) => a
                    let mut rb = EnvDeclBuilder::child_of(&sb);
                    let (k1_id, _k1) = rb.fresh_local(c.nat.clone());
                    let (k2_id, _k2) = rb.fresh_local(c.nat.clone());
                    let lam = rb.mk_lam(k2_id, BinderInfo::Default, c.nat.clone(), a.clone());
                    rb.finish_child(rb.mk_lam(k1_id, BinderInfo::Default, c.nat.clone(), lam))
                };
                let case_term = |s: Expr| c.nat_rec_case(recz.clone(), recs.clone(), s);

                // inner motive: fun s =>
                //   (@Eq Nat (sub n a) s) -> lt (case_term s) n
                let inner_motive = {
                    let mut imb = EnvDeclBuilder::child_of(&sb);
                    let (s_id, s) = imb.fresh_local(c.nat.clone());
                    let eq_hyp = c.eq_of(c.sub_of(n.clone(), a.clone()), s.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        eq_hyp,
                        c.lt_of(case_term(s.clone()), n.clone()),
                    );
                    imb.finish_child(imb.mk_lam(s_id, BinderInfo::Default, c.nat.clone(), body))
                };

                // zcase (s=0): fun (_heq : @Eq Nat (sub n a) 0) =>
                //   ih (sub a n) n (key a n f ha hn) hn
                let zcase = {
                    let mut zb = EnvDeclBuilder::child_of(&sb);
                    let heq_ty = c.eq_of(c.sub_of(n.clone(), a.clone()), c.zero.clone());
                    let (heq_id, _heq) = zb.fresh_local(heq_ty.clone());
                    // key a n f ha hn : le (sub a n) f
                    let key_app = Expr::apps(
                        key.clone(),
                        [a.clone(), n.clone(), f.clone(), ha.clone(), hn.clone()],
                    );
                    // ih (sub a n) n key_app hn : lt (modCore f (sub a n) n) n
                    let body = Expr::apps(
                        ih.clone(),
                        [
                            c.sub_of(a.clone(), n.clone()),
                            n.clone(),
                            key_app,
                            hn.clone(),
                        ],
                    );
                    zb.finish_child(zb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body))
                };

                // scase (s=succ k): fun (k : Nat) (_ihk : inner_motive k)
                //     (heq : @Eq Nat (sub n a) (succ k)) =>
                //   sub_pos_lt a n
                //     (@Eq.subst Nat (fun z => lt 0 z) (succ k) (sub n a)
                //        (Eq.symm heq) (Nat.zero_lt_succ k))
                let scase = {
                    let mut kb = EnvDeclBuilder::child_of(&sb);
                    let (k_id, k) = kb.fresh_local(c.nat.clone());
                    let ihk_ty = Expr::pi(
                        BinderInfo::Default,
                        c.eq_of(c.sub_of(n.clone(), a.clone()), k.clone()),
                        c.lt_of(case_term(k.clone()), n.clone()),
                    );
                    let (ihk_id, _ihk) = kb.fresh_local(ihk_ty.clone());
                    let heq_ty = c.eq_of(c.sub_of(n.clone(), a.clone()), c.succ_of(k.clone()));
                    let (heq_id, heq) = kb.fresh_local(heq_ty.clone());
                    // motive: fun z => lt 0 z
                    let lt0_motive = {
                        let mut lb = EnvDeclBuilder::child_of(&kb);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        let body = c.lt_of(c.zero.clone(), z.clone());
                        lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                    };
                    // Eq.symm heq : @Eq Nat (succ k) (sub n a)
                    let heq_sym = c.symm(c.sub_of(n.clone(), a.clone()), c.succ_of(k.clone()), heq);
                    // Nat.zero_lt_succ k : lt 0 (succ k)
                    let zls = Expr::app(zero_lt_succ.clone(), k.clone());
                    // subst (fun z => lt 0 z) (succ k) (sub n a) (Eq.symm heq) zls : lt 0 (sub n a)
                    let transported = c.subst(
                        lt0_motive,
                        c.succ_of(k.clone()),
                        c.sub_of(n.clone(), a.clone()),
                        heq_sym,
                        zls,
                    );
                    // sub_pos_lt a n transported : lt a n
                    let body = Expr::apps(sub_pos_lt.clone(), [a.clone(), n.clone(), transported]);
                    let lam = kb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
                    let lam = kb.mk_lam(ihk_id, BinderInfo::Default, ihk_ty, lam);
                    kb.finish_child(kb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam))
                };

                // @Nat.rec.{0} inner_motive zcase scase (sub n a) (@Eq.refl Nat (sub n a))
                let inner_rec = c.rec0(inner_motive, zcase, scase, c.sub_of(n.clone(), a.clone()));
                let refl_eq = c.refl(c.sub_of(n.clone(), a.clone()));
                let inner = Expr::app(inner_rec, refl_eq);

                let lam = sb.mk_lam(hn_id, BinderInfo::Default, hn_ty, inner);
                let lam = sb.mk_lam(ha_id, BinderInfo::Default, ha_ty, lam);
                let lam = sb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
                let lam = sb.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), lam);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
                sb.finish_child(sb.mk_lam(f_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // @Nat.rec.{0} motive base step fuel
            let rec = c.rec0(motive, base, step, vfuel.clone());
            let lam = vb.mk_lam(vfuel_id, BinderInfo::Default, c.nat.clone(), rec);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem Nat.mod_lt (a n : Nat) (h : Nat.lt 0 n) : Nat.lt (Nat.mod a n) n`
    ///
    /// `Nat.mod a n ≡ Nat.modCore a a n` (fuel = a) and `a ≤ a` (`Nat.le_refl`).
    fn register_divmod_mod_lt(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mod_lt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nat_mod = Nat::const_("Nat.mod");
        let le_refl = Nat::const_("Nat.le_refl");
        let modcore_lt = Nat::const_(names::MODCORE_LT);

        // Type: ∀ (a n : Nat), Nat.lt 0 n -> Nat.lt (Nat.mod a n) n
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let h_ty = c.lt_of(c.zero.clone(), n.clone());
        let (h_id, _h) = b.fresh_local(h_ty.clone());
        let concl = c.lt_of(
            Expr::apps(nat_mod.clone(), [a.clone(), n.clone()]),
            n.clone(),
        );
        let ty = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        // value: fun (a n : Nat) (h : lt 0 n) =>
        //   modCore_lt a a n (Nat.le_refl a) h
        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let vh_ty = c.lt_of(c.zero.clone(), vn.clone());
            let (vh_id, vh) = vb.fresh_local(vh_ty.clone());
            let lerefl = Expr::app(le_refl.clone(), va.clone());
            let body = Expr::apps(
                modcore_lt.clone(),
                [va.clone(), va.clone(), vn.clone(), lerefl, vh],
            );
            let lam = vb.mk_lam(vh_id, BinderInfo::Default, vh_ty, body);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem sub_zero_le (n a : Nat) (h : sub n a = 0) : Nat.le n a`
    ///
    /// Induction on `a`, generalized over `n`.
    fn register_divmod_sub_zero_le(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::SUB_ZERO_LE);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero_le = Nat::const_("Nat.zero_le");
        let succ_le_succ = Nat::const_("Nat.succ_le_succ");
        let succ_sub_succ = Nat::const_(names::SUCC_SUB_SUCC);

        // Type: ∀ (n a : Nat), @Eq Nat (sub n a) 0 -> Nat.le n a
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let h_ty = c.eq_of(c.sub_of(n.clone(), a.clone()), c.zero.clone());
        let (h_id, _h) = b.fresh_local(h_ty.clone());
        let concl = c.le_of(n.clone(), a.clone());
        let ty = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vh_id, vh) =
                vb.fresh_local(c.eq_of(c.sub_of(vn.clone(), va.clone()), c.zero.clone()));

            // outer motive: fun k => ∀ (m : Nat), @Eq Nat (sub m k) 0 -> Nat.le m k
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let inner = {
                    let mut ib = EnvDeclBuilder::child_of(&mb);
                    let (m_id, m) = ib.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.eq_of(c.sub_of(m.clone(), k.clone()), c.zero.clone()),
                        c.le_of(m.clone(), k.clone()),
                    );
                    ib.finish_child(ib.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), body))
                };
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), inner))
            };

            // base (k=0): fun (m : Nat) (hm : @Eq Nat (sub m 0) 0) =>
            //   @Eq.subst Nat (fun z => Nat.le z 0) 0 m (Eq.symm hm) (Nat.zero_le 0)
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&vb);
                let (m_id, m) = bb.fresh_local(c.nat.clone());
                let hm_ty = c.eq_of(c.sub_of(m.clone(), c.zero.clone()), c.zero.clone());
                let (hm_id, hm) = bb.fresh_local(hm_ty.clone());
                let le_z_motive = {
                    let mut lb = EnvDeclBuilder::child_of(&bb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.le_of(z.clone(), c.zero.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                // hm : @Eq Nat (sub m 0) 0  (defeq @Eq Nat m 0); Eq.symm with sides m,0
                let hm_sym = c.symm(m.clone(), c.zero.clone(), hm);
                let z0 = Expr::app(zero_le.clone(), c.zero.clone()); // le 0 0
                let body = c.subst(le_z_motive, c.zero.clone(), m.clone(), hm_sym, z0);
                let lam = bb.mk_lam(hm_id, BinderInfo::Default, hm_ty, body);
                bb.finish_child(bb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // step (k=succ a'): fun (a' : Nat) (ih : motive a') => fun (m : Nat) =>
            //   @Nat.rec inner_motive izcase iscase m
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (ap_id, ap) = sb.fresh_local(c.nat.clone());
                let ih_ty = {
                    let mut ihb = EnvDeclBuilder::child_of(&sb);
                    let (m_id, m) = ihb.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.eq_of(c.sub_of(m.clone(), ap.clone()), c.zero.clone()),
                        c.le_of(m.clone(), ap.clone()),
                    );
                    ihb.finish_child(ihb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let (m_id, m) = sb.fresh_local(c.nat.clone());

                // inner motive: fun mm => @Eq Nat (sub mm (succ a')) 0 -> Nat.le mm (succ a')
                let inner_motive = {
                    let mut imb = EnvDeclBuilder::child_of(&sb);
                    let (mm_id, mm) = imb.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.eq_of(c.sub_of(mm.clone(), c.succ_of(ap.clone())), c.zero.clone()),
                        c.le_of(mm.clone(), c.succ_of(ap.clone())),
                    );
                    imb.finish_child(imb.mk_lam(mm_id, BinderInfo::Default, c.nat.clone(), body))
                };

                // izcase (mm=0): fun (_h0 : ...) => Nat.zero_le (succ a')
                let izcase = {
                    let mut zb = EnvDeclBuilder::child_of(&sb);
                    let h0_ty = c.eq_of(
                        c.sub_of(c.zero.clone(), c.succ_of(ap.clone())),
                        c.zero.clone(),
                    );
                    let (h0_id, _h0) = zb.fresh_local(h0_ty.clone());
                    let body = Expr::app(zero_le.clone(), c.succ_of(ap.clone()));
                    zb.finish_child(zb.mk_lam(h0_id, BinderInfo::Default, h0_ty, body))
                };

                // iscase (mm=succ n'): fun (n' : Nat) (_ihn : inner_motive n')
                //     (hn : @Eq Nat (sub (succ n')(succ a')) 0) =>
                //   Nat.succ_le_succ n' a'
                //     (ih n' (@Eq.subst Nat (fun z => @Eq Nat z 0)
                //        (sub (succ n')(succ a')) (sub n' a') (succ_sub_succ n' a') hn))
                let iscase = {
                    let mut nb = EnvDeclBuilder::child_of(&sb);
                    let (np_id, np) = nb.fresh_local(c.nat.clone());
                    let ihn_ty = Expr::pi(
                        BinderInfo::Default,
                        c.eq_of(c.sub_of(np.clone(), c.succ_of(ap.clone())), c.zero.clone()),
                        c.le_of(np.clone(), c.succ_of(ap.clone())),
                    );
                    let (ihn_id, _ihn) = nb.fresh_local(ihn_ty.clone());
                    let hn_ty = c.eq_of(
                        c.sub_of(c.succ_of(np.clone()), c.succ_of(ap.clone())),
                        c.zero.clone(),
                    );
                    let (hn_id, hn) = nb.fresh_local(hn_ty.clone());
                    // motive: fun z => @Eq Nat z 0
                    let eqz_motive = {
                        let mut lb = EnvDeclBuilder::child_of(&nb);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        let body = c.eq_of(z.clone(), c.zero.clone());
                        lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                    };
                    let sss = Expr::apps(succ_sub_succ.clone(), [np.clone(), ap.clone()]);
                    let transported = c.subst(
                        eqz_motive,
                        c.sub_of(c.succ_of(np.clone()), c.succ_of(ap.clone())),
                        c.sub_of(np.clone(), ap.clone()),
                        sss,
                        hn,
                    );
                    let ih_app = Expr::apps(ih.clone(), [np.clone(), transported]);
                    let body = Expr::apps(succ_le_succ.clone(), [np.clone(), ap.clone(), ih_app]);
                    let lam = nb.mk_lam(hn_id, BinderInfo::Default, hn_ty, body);
                    let lam = nb.mk_lam(ihn_id, BinderInfo::Default, ihn_ty, lam);
                    nb.finish_child(nb.mk_lam(np_id, BinderInfo::Default, c.nat.clone(), lam))
                };

                let inner_rec = c.rec0(inner_motive, izcase, iscase, m.clone());
                let lam = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), inner_rec);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
                sb.finish_child(sb.mk_lam(ap_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // @Nat.rec.{0} motive base step a  then apply  n  then  h
            let rec = c.rec0(motive, base, step, va.clone());
            let body = Expr::apps(rec, [vn.clone(), vh.clone()]);
            let lam = vb.mk_lam(
                vh_id,
                BinderInfo::Default,
                c.eq_of(c.sub_of(vn.clone(), va.clone()), c.zero.clone()),
                body,
            );
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem nmul_zero_left (n : Nat) : @Eq Nat (mul 0 n) 0`
    ///   `@Nat.rec (fun k => @Eq Nat (mul 0 k) 0) rfl (fun _ ih => ih) n`.
    fn register_divmod_nmul_zero_left(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::NMUL_ZERO_LEFT);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Type: ∀ (n : Nat), @Eq Nat (mul 0 n) 0
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(c.mul_of(c.zero.clone(), n.clone()), c.zero.clone());
        let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let body = c.eq_of(c.mul_of(c.zero.clone(), k.clone()), c.zero.clone());
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let base = c.refl(c.mul_of(c.zero.clone(), c.zero.clone()));
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (j_id, _j) = sb.fresh_local(c.nat.clone());
                let ih_ty = {
                    // ih : @Eq Nat (mul 0 j) 0
                    let j_again = _j.clone();
                    c.eq_of(c.mul_of(c.zero.clone(), j_again), c.zero.clone())
                };
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, ih);
                sb.finish_child(sb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam))
            };
            let rec = c.rec0(motive, base, step, vn.clone());
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), rec);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem add_right_comm (a b c : Nat)
    ///   : @Eq Nat (add (add a b) c) (add (add a c) b)`
    ///
    /// Pure equational; no induction.
    fn register_divmod_add_right_comm(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::ADD_RIGHT_COMM);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let add_assoc = Nat::const_("Nat.add_assoc");
        let add_comm = Nat::const_("Nat.add_comm");

        // Type: ∀ (a b c : Nat), @Eq Nat (add (add a b) c) (add (add a c) b)
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bv) = b.fresh_local(c.nat.clone());
        let (cc_id, cv) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(
            c.add_of(c.add_of(a.clone(), bv.clone()), cv.clone()),
            c.add_of(c.add_of(a.clone(), cv.clone()), bv.clone()),
        );
        let ty = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vb2_id, vbv) = vb.fresh_local(c.nat.clone());
            let (vc_id, vcv) = vb.fresh_local(c.nat.clone());

            // add_assoc a b c : @Eq Nat (add (add a b) c) (add a (add b c))
            let aa1 = Expr::apps(add_assoc.clone(), [va.clone(), vbv.clone(), vcv.clone()]);
            // congrArg (fun z => add a z) (add_comm b c)
            //   : @Eq Nat (add a (add b c)) (add a (add c b))
            let add_a_motive = {
                let mut lb = EnvDeclBuilder::child_of(&vb);
                let (z_id, z) = lb.fresh_local(c.nat.clone());
                let body = c.add_of(va.clone(), z.clone());
                lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let comm_bc = Expr::apps(add_comm.clone(), [vbv.clone(), vcv.clone()]);
            let cg = c.congr_arg(
                c.add_of(vbv.clone(), vcv.clone()),
                c.add_of(vcv.clone(), vbv.clone()),
                add_a_motive,
                comm_bc,
            );
            // add_assoc a c b : @Eq Nat (add (add a c) b) (add a (add c b))
            let aa2 = Expr::apps(add_assoc.clone(), [va.clone(), vcv.clone(), vbv.clone()]);
            // Eq.symm aa2 : @Eq Nat (add a (add c b)) (add (add a c) b)
            let aa2_sym = c.symm(
                c.add_of(c.add_of(va.clone(), vcv.clone()), vbv.clone()),
                c.add_of(va.clone(), c.add_of(vcv.clone(), vbv.clone())),
                aa2,
            );
            // Eq.trans cg aa2_sym
            //   : @Eq Nat (add a (add b c)) (add (add a c) b)
            let inner_trans = c.trans(
                c.add_of(va.clone(), c.add_of(vbv.clone(), vcv.clone())),
                c.add_of(va.clone(), c.add_of(vcv.clone(), vbv.clone())),
                c.add_of(c.add_of(va.clone(), vcv.clone()), vbv.clone()),
                cg,
                aa2_sym,
            );
            // Eq.trans aa1 inner_trans
            //   : @Eq Nat (add (add a b) c) (add (add a c) b)
            let body = c.trans(
                c.add_of(c.add_of(va.clone(), vbv.clone()), vcv.clone()),
                c.add_of(va.clone(), c.add_of(vbv.clone(), vcv.clone())),
                c.add_of(c.add_of(va.clone(), vcv.clone()), vbv.clone()),
                aa1,
                inner_trans,
            );
            let lam = vb.mk_lam(vc_id, BinderInfo::Default, c.nat.clone(), body);
            let lam = vb.mk_lam(vb2_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem nmul_succ_left (a n : Nat)
    ///   : @Eq Nat (mul (succ a) n) (add (mul a n) n)`  (induction on `n`).
    fn register_divmod_nmul_succ_left(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::NMUL_SUCC_LEFT);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let add_right_comm = Nat::const_(names::ADD_RIGHT_COMM);

        // Type: ∀ (a n : Nat), @Eq Nat (mul (succ a) n) (add (mul a n) n)
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(
            c.mul_of(c.succ_of(a.clone()), n.clone()),
            c.add_of(c.mul_of(a.clone(), n.clone()), n.clone()),
        );
        let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());

            // motive: fun k => @Eq Nat (mul (succ a) k) (add (mul a k) k)
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let body = c.eq_of(
                    c.mul_of(c.succ_of(va.clone()), k.clone()),
                    c.add_of(c.mul_of(va.clone(), k.clone()), k.clone()),
                );
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // base (n=0): @Eq.refl Nat (mul (succ a) 0)
            let base = c.refl(c.mul_of(c.succ_of(va.clone()), c.zero.clone()));
            // step: fun (k : Nat)(ih : motive k) =>
            //   Eq.trans (congrArg (fun z => add z (succ a)) ih)
            //            (congrArg (fun z => succ z) (add_right_comm (mul a k) k a))
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = sb.fresh_local(c.nat.clone());
                let ih_ty = c.eq_of(
                    c.mul_of(c.succ_of(va.clone()), k.clone()),
                    c.add_of(c.mul_of(va.clone(), k.clone()), k.clone()),
                );
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                // f1 = fun z => add z (succ a)
                let f1 = {
                    let mut lb = EnvDeclBuilder::child_of(&sb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.add_of(z.clone(), c.succ_of(va.clone()));
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                // congrArg f1 (mul (succ a) k) (add (mul a k) k) ih
                //   : @Eq Nat (add (mul (succ a) k)(succ a)) (add (add (mul a k) k)(succ a))
                let cg1 = c.congr_arg(
                    c.mul_of(c.succ_of(va.clone()), k.clone()),
                    c.add_of(c.mul_of(va.clone(), k.clone()), k.clone()),
                    f1,
                    ih,
                );
                // add_right_comm (mul a k) k a
                //   : @Eq Nat (add (add (mul a k) k) a) (add (add (mul a k) a) k)
                let arc = Expr::apps(
                    add_right_comm.clone(),
                    [c.mul_of(va.clone(), k.clone()), k.clone(), va.clone()],
                );
                // congrArg succ arc
                //   : @Eq Nat (succ (add (add (mul a k) k) a)) (succ (add (add (mul a k) a) k))
                let cg2 = c.congr_succ(
                    c.add_of(
                        c.add_of(c.mul_of(va.clone(), k.clone()), k.clone()),
                        va.clone(),
                    ),
                    c.add_of(
                        c.add_of(c.mul_of(va.clone(), k.clone()), va.clone()),
                        k.clone(),
                    ),
                    arc,
                );
                // Eq.trans cg1 cg2 — the middle term is the shared defeq point.
                //   cg1 : LHS=mul(succ a)(succ k)  ~  add (add (mul a k) k)(succ a)
                //   cg2 : succ (add (add (mul a k) k) a)  ~  add (mul a (succ k))(succ k)
                // The trans middle term is `add (add (mul a k) k)(succ a)` which is
                // defeq to `succ (add (add (mul a k) k) a)` (add _ (succ _) reduction).
                let mid = c.add_of(
                    c.add_of(c.mul_of(va.clone(), k.clone()), k.clone()),
                    c.succ_of(va.clone()),
                );
                let lhs = c.mul_of(c.succ_of(va.clone()), c.succ_of(k.clone()));
                let rhs = c.add_of(
                    c.mul_of(va.clone(), c.succ_of(k.clone())),
                    c.succ_of(k.clone()),
                );
                let body = c.trans(lhs, mid, rhs, cg1, cg2);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                sb.finish_child(sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam))
            };
            let rec = c.rec0(motive, base, step, vn.clone());
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), rec);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem sub_add_cancel (a n : Nat) (h : Nat.le n a)
    ///   : @Eq Nat (add (sub a n) n) a`  (induction on `n` generalized over `a`).
    fn register_divmod_sub_add_cancel(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::SUB_ADD_CANCEL);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let not_succ_le_zero = Nat::const_("Nat.not_succ_le_zero");
        let le_of_succ_le_succ = Nat::const_("Nat.le_of_succ_le_succ");
        let succ_sub_succ = Nat::const_(names::SUCC_SUB_SUCC);

        // Type: ∀ (a n : Nat), Nat.le n a -> @Eq Nat (add (sub a n) n) a
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let h_ty = c.le_of(n.clone(), a.clone());
        let (h_id, _h) = b.fresh_local(h_ty.clone());
        let concl = c.eq_of(
            c.add_of(c.sub_of(a.clone(), n.clone()), n.clone()),
            a.clone(),
        );
        let ty = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());
            let (vh_id, vh) = vb.fresh_local(c.le_of(vn.clone(), va.clone()));

            // outer motive: fun k => ∀ (m : Nat), Nat.le k m -> @Eq Nat (add (sub m k) k) m
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = mb.fresh_local(c.nat.clone());
                let inner = {
                    let mut ib = EnvDeclBuilder::child_of(&mb);
                    let (m_id, m) = ib.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(k.clone(), m.clone()),
                        c.eq_of(
                            c.add_of(c.sub_of(m.clone(), k.clone()), k.clone()),
                            m.clone(),
                        ),
                    );
                    ib.finish_child(ib.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), body))
                };
                mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), inner))
            };

            // base (k=0): fun (m : Nat) (_hm : Nat.le 0 m) => @Eq.refl Nat m
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&vb);
                let (m_id, m) = bb.fresh_local(c.nat.clone());
                let hm_ty = c.le_of(c.zero.clone(), m.clone());
                let (hm_id, _hm) = bb.fresh_local(hm_ty.clone());
                let body = c.refl(m.clone());
                let lam = bb.mk_lam(hm_id, BinderInfo::Default, hm_ty, body);
                bb.finish_child(bb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // step (k=succ n'): fun (n' : Nat) (ih : motive n') => fun (m : Nat) =>
            //   @Nat.rec inner_motive izcase iscase m
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (np_id, np) = sb.fresh_local(c.nat.clone());
                let ih_ty = {
                    let mut ihb = EnvDeclBuilder::child_of(&sb);
                    let (m_id, m) = ihb.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(np.clone(), m.clone()),
                        c.eq_of(
                            c.add_of(c.sub_of(m.clone(), np.clone()), np.clone()),
                            m.clone(),
                        ),
                    );
                    ihb.finish_child(ihb.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let (m_id, m) = sb.fresh_local(c.nat.clone());

                // inner motive: fun mm =>
                //   Nat.le (succ n') mm -> @Eq Nat (add (sub mm (succ n'))(succ n')) mm
                let inner_motive = {
                    let mut imb = EnvDeclBuilder::child_of(&sb);
                    let (mm_id, mm) = imb.fresh_local(c.nat.clone());
                    let body = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(c.succ_of(np.clone()), mm.clone()),
                        c.eq_of(
                            c.add_of(
                                c.sub_of(mm.clone(), c.succ_of(np.clone())),
                                c.succ_of(np.clone()),
                            ),
                            mm.clone(),
                        ),
                    );
                    imb.finish_child(imb.mk_lam(mm_id, BinderInfo::Default, c.nat.clone(), body))
                };

                // izcase (mm=0): fun (h0 : le (succ n') 0) =>
                //   @False.elim (@Eq Nat (add (sub 0 (succ n'))(succ n')) 0)
                //     (Nat.not_succ_le_zero n' h0)
                let izcase = {
                    let mut zb = EnvDeclBuilder::child_of(&sb);
                    let h0_ty = c.le_of(c.succ_of(np.clone()), c.zero.clone());
                    let (h0_id, h0) = zb.fresh_local(h0_ty.clone());
                    let goal = c.eq_of(
                        c.add_of(
                            c.sub_of(c.zero.clone(), c.succ_of(np.clone())),
                            c.succ_of(np.clone()),
                        ),
                        c.zero.clone(),
                    );
                    let false_pf = Expr::apps(not_succ_le_zero.clone(), [np.clone(), h0]);
                    let body = c.false_elim(goal, false_pf);
                    zb.finish_child(zb.mk_lam(h0_id, BinderInfo::Default, h0_ty, body))
                };

                // iscase (mm=succ a'): fun (a' : Nat) (_iha : inner_motive a')
                //     (ha' : le (succ n')(succ a')) =>
                //   @Eq.subst Nat (fun z => @Eq Nat (add z (succ n')) (succ a'))
                //     (sub a' n') (sub (succ a')(succ n'))
                //     (Eq.symm (succ_sub_succ a' n'))
                //     (congrArg succ (ih a' (Nat.le_of_succ_le_succ n' a' ha')))
                let iscase = {
                    let mut ab = EnvDeclBuilder::child_of(&sb);
                    let (ap_id, ap) = ab.fresh_local(c.nat.clone());
                    let iha_ty = Expr::pi(
                        BinderInfo::Default,
                        c.le_of(c.succ_of(np.clone()), ap.clone()),
                        c.eq_of(
                            c.add_of(
                                c.sub_of(ap.clone(), c.succ_of(np.clone())),
                                c.succ_of(np.clone()),
                            ),
                            ap.clone(),
                        ),
                    );
                    let (iha_id, _iha) = ab.fresh_local(iha_ty.clone());
                    let ha_ty = c.le_of(c.succ_of(np.clone()), c.succ_of(ap.clone()));
                    let (ha_id, ha) = ab.fresh_local(ha_ty.clone());

                    // motive: fun z => @Eq Nat (add z (succ n')) (succ a')
                    let subst_motive = {
                        let mut lb = EnvDeclBuilder::child_of(&ab);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        let body = c.eq_of(
                            c.add_of(z.clone(), c.succ_of(np.clone())),
                            c.succ_of(ap.clone()),
                        );
                        lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                    };
                    // ih a' (le_of_succ_le_succ n' a' ha') : @Eq Nat (add (sub a' n') n') a'
                    let loss = Expr::apps(le_of_succ_le_succ.clone(), [np.clone(), ap.clone(), ha]);
                    let ih_app = Expr::apps(ih.clone(), [ap.clone(), loss]);
                    // congrArg succ : @Eq Nat (succ (add (sub a' n') n')) (succ a')
                    let cg = c.congr_succ(
                        c.add_of(c.sub_of(ap.clone(), np.clone()), np.clone()),
                        ap.clone(),
                        ih_app,
                    );
                    // succ_sub_succ a' n' : @Eq Nat (sub (succ a')(succ n')) (sub a' n')
                    let sss = Expr::apps(succ_sub_succ.clone(), [ap.clone(), np.clone()]);
                    // Eq.symm : @Eq Nat (sub a' n') (sub (succ a')(succ n'))
                    let sss_sym = c.symm(
                        c.sub_of(c.succ_of(ap.clone()), c.succ_of(np.clone())),
                        c.sub_of(ap.clone(), np.clone()),
                        sss,
                    );
                    let body = c.subst(
                        subst_motive,
                        c.sub_of(ap.clone(), np.clone()),
                        c.sub_of(c.succ_of(ap.clone()), c.succ_of(np.clone())),
                        sss_sym,
                        cg,
                    );
                    let lam = ab.mk_lam(ha_id, BinderInfo::Default, ha_ty, body);
                    let lam = ab.mk_lam(iha_id, BinderInfo::Default, iha_ty, lam);
                    ab.finish_child(ab.mk_lam(ap_id, BinderInfo::Default, c.nat.clone(), lam))
                };

                let inner_rec = c.rec0(inner_motive, izcase, iscase, m.clone());
                let lam = sb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), inner_rec);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
                sb.finish_child(sb.mk_lam(np_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // @Nat.rec.{0} motive base step n  then apply  a  then  h
            let rec = c.rec0(motive, base, step, vn.clone());
            let body = Expr::apps(rec, [va.clone(), vh.clone()]);
            let lam = vb.mk_lam(
                vh_id,
                BinderInfo::Default,
                c.le_of(vn.clone(), va.clone()),
                body,
            );
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), lam);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem modCore_zero (fuel : Nat) : ∀ (a : Nat), @Eq Nat (modCore fuel a 0) a`
    fn register_divmod_modcore_zero(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::MODCORE_ZERO);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let modcore = Nat::const_("Nat.modCore");
        let zero_sub = Nat::const_(names::ZERO_SUB);
        let modcore_of = |fuel: Expr, a: Expr, n: Expr| Expr::apps(modcore.clone(), [fuel, a, n]);

        // Type: ∀ (fuel a : Nat), @Eq Nat (modCore fuel a 0) a
        let mut b = EnvDeclBuilder::new();
        let (fuel_id, fuel) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(
            modcore_of(fuel.clone(), a.clone(), c.zero.clone()),
            a.clone(),
        );
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(fuel_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        // forall body `∀ (a : Nat), @Eq Nat (modCore F a 0) a` for fuel term F.
        let mk_forall = |bld: &EnvDeclBuilder, fuel_term: Expr| {
            let mut fb = EnvDeclBuilder::child_of(bld);
            let (fa_id, fa) = fb.fresh_local(c.nat.clone());
            let body = c.eq_of(
                modcore_of(fuel_term.clone(), fa.clone(), c.zero.clone()),
                fa.clone(),
            );
            let inner = fb.mk_pi(fa_id, BinderInfo::Default, c.nat.clone(), body);
            fb.finish_child(inner)
        };

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vfuel_id, vfuel) = vb.fresh_local(c.nat.clone());

            // motive: fun f => ∀ (a : Nat), @Eq Nat (modCore f a 0) a
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (f_id, f) = mb.fresh_local(c.nat.clone());
                let body = mk_forall(&mb, f.clone());
                mb.finish_child(mb.mk_lam(f_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // base (fuel=0): fun (a : Nat) => @Eq.refl Nat a
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&vb);
                let (a_id, a) = bb.fresh_local(c.nat.clone());
                let body = c.refl(a.clone());
                bb.finish_child(bb.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // step (fuel=succ f): fun (f : Nat) (ih : motive f) => fun (a : Nat) =>
            //   @Eq.subst Nat
            //     (fun s => @Eq Nat (@Nat.rec (fun _=>Nat)(modCore f (sub a 0) 0)(fun _ _=>a) s) a)
            //     0 (sub 0 a) (Eq.symm (zero_sub a)) (ih a)
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (f_id, f) = sb.fresh_local(c.nat.clone());
                let ih_ty = mk_forall(&sb, f.clone());
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let (a_id, a) = sb.fresh_local(c.nat.clone());

                // recz = modCore f (sub a 0) 0 ; recs = fun _ _ => a
                let recz = modcore_of(
                    f.clone(),
                    c.sub_of(a.clone(), c.zero.clone()),
                    c.zero.clone(),
                );
                let recs = {
                    let mut rb = EnvDeclBuilder::child_of(&sb);
                    let (k1_id, _k1) = rb.fresh_local(c.nat.clone());
                    let (k2_id, _k2) = rb.fresh_local(c.nat.clone());
                    let lam = rb.mk_lam(k2_id, BinderInfo::Default, c.nat.clone(), a.clone());
                    rb.finish_child(rb.mk_lam(k1_id, BinderInfo::Default, c.nat.clone(), lam))
                };
                let case_term = |s: Expr| c.nat_rec_case(recz.clone(), recs.clone(), s);

                // motive: fun s => @Eq Nat (case_term s) a
                let subst_motive = {
                    let mut lb = EnvDeclBuilder::child_of(&sb);
                    let (s_id, s) = lb.fresh_local(c.nat.clone());
                    let body = c.eq_of(case_term(s.clone()), a.clone());
                    lb.finish_child(lb.mk_lam(s_id, BinderInfo::Default, c.nat.clone(), body))
                };
                // zero_sub a : @Eq Nat (sub 0 a) 0 ; Eq.symm : @Eq Nat 0 (sub 0 a)
                let zs = Expr::app(zero_sub.clone(), a.clone());
                let zs_sym = c.symm(c.sub_of(c.zero.clone(), a.clone()), c.zero.clone(), zs);
                let ih_a = Expr::app(ih.clone(), a.clone());
                let body = c.subst(
                    subst_motive,
                    c.zero.clone(),
                    c.sub_of(c.zero.clone(), a.clone()),
                    zs_sym,
                    ih_a,
                );
                let lam = sb.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), body);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
                sb.finish_child(sb.mk_lam(f_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            let rec = c.rec0(motive, base, step, vfuel.clone());
            let lam = vb.mk_lam(vfuel_id, BinderInfo::Default, c.nat.clone(), rec);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem mod_zero (a : Nat) : @Eq Nat (mod a 0) a := modCore_zero a a`
    fn register_divmod_mod_zero(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::MOD_ZERO);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nat_mod = Nat::const_("Nat.mod");
        let modcore_zero = Nat::const_(names::MODCORE_ZERO);

        // Type: ∀ (a : Nat), @Eq Nat (mod a 0) a
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(
            Expr::apps(nat_mod.clone(), [a.clone(), c.zero.clone()]),
            a.clone(),
        );
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), concl);
        let type_ = b.finish(ty);

        // value: fun (a : Nat) => modCore_zero a a
        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let body = Expr::apps(modcore_zero.clone(), [va.clone(), va.clone()]);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), body);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem divmod_id (fuel : Nat)
    ///   : ∀ (a n : Nat), le a fuel -> lt 0 n ->
    ///       @Eq Nat (add (mul (divCore fuel a n) n) (modCore fuel a n)) a`
    ///
    /// The joint div/mod euclidean fuel induction.
    fn register_divmod_divmod_id(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string(names::DIVMOD_ID);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let divcore = Nat::const_("Nat.divCore");
        let modcore = Nat::const_("Nat.modCore");
        let le_zero = Nat::const_(names::LE_ZERO);
        let nmul_zero_left = Nat::const_(names::NMUL_ZERO_LEFT);
        let nmul_succ_left = Nat::const_(names::NMUL_SUCC_LEFT);
        let add_right_comm = Nat::const_(names::ADD_RIGHT_COMM);
        let key = Nat::const_(names::KEY);
        let sub_add_cancel = Nat::const_(names::SUB_ADD_CANCEL);
        let sub_zero_le = Nat::const_(names::SUB_ZERO_LE);
        let zero_add = Nat::const_("Nat.zero_add");

        let divcore_of = |fuel: Expr, a: Expr, n: Expr| Expr::apps(divcore.clone(), [fuel, a, n]);
        let modcore_of = |fuel: Expr, a: Expr, n: Expr| Expr::apps(modcore.clone(), [fuel, a, n]);

        // `add (mul (divCore F a n) n) (modCore F a n)`
        let euclid = |fuel: Expr, a: Expr, n: Expr| {
            c.add_of(
                c.mul_of(divcore_of(fuel.clone(), a.clone(), n.clone()), n.clone()),
                modcore_of(fuel, a, n),
            )
        };

        // Type: ∀ (fuel a n : Nat), le a fuel -> lt 0 n -> @Eq Nat (euclid fuel a n) a
        let mut b = EnvDeclBuilder::new();
        let (fuel_id, fuel) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let ha_ty = c.le_of(a.clone(), fuel.clone());
        let (ha_id, _ha) = b.fresh_local(ha_ty.clone());
        let hn_ty = c.lt_of(c.zero.clone(), n.clone());
        let (hn_id, _hn) = b.fresh_local(hn_ty.clone());
        let concl = c.eq_of(euclid(fuel.clone(), a.clone(), n.clone()), a.clone());
        let ty = b.mk_pi(hn_id, BinderInfo::Default, hn_ty, concl);
        let ty = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, ty);
        let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let ty = b.mk_pi(fuel_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        // forall body `∀ (a n : Nat), le a F -> lt 0 n -> @Eq Nat (euclid F a n) a`.
        let mk_forall = |bld: &EnvDeclBuilder, fuel_term: Expr| {
            let mut fb = EnvDeclBuilder::child_of(bld);
            let (fa_id, fa) = fb.fresh_local(c.nat.clone());
            let (fn_id, fnn) = fb.fresh_local(c.nat.clone());
            let inner = c.eq_of(
                euclid(fuel_term.clone(), fa.clone(), fnn.clone()),
                fa.clone(),
            );
            let inner = Expr::pi(
                BinderInfo::Default,
                c.lt_of(c.zero.clone(), fnn.clone()),
                inner,
            );
            let inner = Expr::pi(
                BinderInfo::Default,
                c.le_of(fa.clone(), fuel_term.clone()),
                inner,
            );
            let inner = fb.mk_pi(fn_id, BinderInfo::Default, c.nat.clone(), inner);
            let inner = fb.mk_pi(fa_id, BinderInfo::Default, c.nat.clone(), inner);
            fb.finish_child(inner)
        };

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (vfuel_id, vfuel) = vb.fresh_local(c.nat.clone());

            // outer motive: fun f => ∀ (a n : Nat), le a f -> lt 0 n -> @Eq Nat (euclid f a n) a
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (f_id, f) = mb.fresh_local(c.nat.clone());
                let body = mk_forall(&mb, f.clone());
                mb.finish_child(mb.mk_lam(f_id, BinderInfo::Default, c.nat.clone(), body))
            };

            // base (fuel=0): fun (a n : Nat) (ha : le a 0) (_hn : lt 0 n) =>
            //   @Eq.subst Nat
            //     (fun z => @Eq Nat (euclid 0 z n) z)
            //     0 a (Eq.symm (le_zero a ha)) (nmul_zero_left n)
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&vb);
                let (ba_id, ba) = bb.fresh_local(c.nat.clone());
                let (bn_id, bn) = bb.fresh_local(c.nat.clone());
                let ha_ty = c.le_of(ba.clone(), c.zero.clone());
                let (bha_id, bha) = bb.fresh_local(ha_ty.clone());
                let hn_ty = c.lt_of(c.zero.clone(), bn.clone());
                let (bhn_id, _bhn) = bb.fresh_local(hn_ty.clone());
                // motive: fun z => @Eq Nat (euclid 0 z n) z
                let subst_motive = {
                    let mut lb = EnvDeclBuilder::child_of(&bb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.eq_of(euclid(c.zero.clone(), z.clone(), bn.clone()), z.clone());
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                // le_zero a ha : @Eq Nat a 0 ; Eq.symm : @Eq Nat 0 a
                let lz = Expr::apps(le_zero.clone(), [ba.clone(), bha]);
                let lz_sym = c.symm(ba.clone(), c.zero.clone(), lz);
                // nmul_zero_left n : @Eq Nat (mul 0 n) 0  (= motive 0 by add _ 0 / divCore0/modCore0)
                let nzl = Expr::app(nmul_zero_left.clone(), bn.clone());
                let body = c.subst(subst_motive, c.zero.clone(), ba.clone(), lz_sym, nzl);
                let lam = bb.mk_lam(bhn_id, BinderInfo::Default, hn_ty, body);
                let lam = bb.mk_lam(bha_id, BinderInfo::Default, ha_ty, lam);
                let lam = bb.mk_lam(bn_id, BinderInfo::Default, c.nat.clone(), lam);
                bb.finish_child(bb.mk_lam(ba_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            // step (fuel=succ f): fun (f : Nat) (ih : motive f) =>
            //   fun (a n : Nat) (ha : le a (succ f)) (hn : lt 0 n) =>
            //     @Nat.rec inner_motive zcase scase (sub n a) (@Eq.refl Nat (sub n a))
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (f_id, f) = sb.fresh_local(c.nat.clone());
                let ih_ty = mk_forall(&sb, f.clone());
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let (a_id, a) = sb.fresh_local(c.nat.clone());
                let (n_id, n) = sb.fresh_local(c.nat.clone());
                let ha_ty = c.le_of(a.clone(), c.succ_of(f.clone()));
                let (ha_id, ha) = sb.fresh_local(ha_ty.clone());
                let hn_ty = c.lt_of(c.zero.clone(), n.clone());
                let (hn_id, hn) = sb.fresh_local(hn_ty.clone());

                // q = divCore f (sub a n) n ; r = modCore f (sub a n) n
                let q = divcore_of(f.clone(), c.sub_of(a.clone(), n.clone()), n.clone());
                let r = modcore_of(f.clone(), c.sub_of(a.clone(), n.clone()), n.clone());

                // div case-term: @Nat.rec (fun _=>Nat) (succ q) (fun _ _ => 0) s
                let div_recz = c.succ_of(q.clone());
                let div_recs = {
                    let mut rb = EnvDeclBuilder::child_of(&sb);
                    let (k1_id, _k1) = rb.fresh_local(c.nat.clone());
                    let (k2_id, _k2) = rb.fresh_local(c.nat.clone());
                    let lam = rb.mk_lam(k2_id, BinderInfo::Default, c.nat.clone(), c.zero.clone());
                    rb.finish_child(rb.mk_lam(k1_id, BinderInfo::Default, c.nat.clone(), lam))
                };
                // mod case-term: @Nat.rec (fun _=>Nat) r (fun _ _ => a) s
                let mod_recz = r.clone();
                let mod_recs = {
                    let mut rb = EnvDeclBuilder::child_of(&sb);
                    let (k1_id, _k1) = rb.fresh_local(c.nat.clone());
                    let (k2_id, _k2) = rb.fresh_local(c.nat.clone());
                    let lam = rb.mk_lam(k2_id, BinderInfo::Default, c.nat.clone(), a.clone());
                    rb.finish_child(rb.mk_lam(k1_id, BinderInfo::Default, c.nat.clone(), lam))
                };
                let div_case = |s: Expr| c.nat_rec_case(div_recz.clone(), div_recs.clone(), s);
                let mod_case = |s: Expr| c.nat_rec_case(mod_recz.clone(), mod_recs.clone(), s);

                // inner motive: fun s =>
                //   (@Eq Nat (sub n a) s) ->
                //     @Eq Nat (add (mul (div_case s) n) (mod_case s)) a
                let inner_motive = {
                    let mut imb = EnvDeclBuilder::child_of(&sb);
                    let (s_id, s) = imb.fresh_local(c.nat.clone());
                    let eq_hyp = c.eq_of(c.sub_of(n.clone(), a.clone()), s.clone());
                    let goal = c.eq_of(
                        c.add_of(
                            c.mul_of(div_case(s.clone()), n.clone()),
                            mod_case(s.clone()),
                        ),
                        a.clone(),
                    );
                    let body = Expr::pi(BinderInfo::Default, eq_hyp, goal);
                    imb.finish_child(imb.mk_lam(s_id, BinderInfo::Default, c.nat.clone(), body))
                };

                // shared sub-terms
                let qn = c.mul_of(q.clone(), n.clone()); // mul q n
                let big = c.add_of(c.add_of(qn.clone(), r.clone()), n.clone()); // add (add (mul q n) r) n
                let small = c.add_of(c.mul_of(c.succ_of(q.clone()), n.clone()), r.clone()); // add (mul (succ q) n) r

                // zcase (s=0): fun (heq : @Eq Nat (sub n a) 0) =>
                let zcase = {
                    let mut zb = EnvDeclBuilder::child_of(&sb);
                    let heq_ty = c.eq_of(c.sub_of(n.clone(), a.clone()), c.zero.clone());
                    let (heq_id, heq) = zb.fresh_local(heq_ty.clone());

                    // outer subst motive: fun w => @Eq Nat w a
                    let outer_motive = {
                        let mut lb = EnvDeclBuilder::child_of(&zb);
                        let (w_id, w) = lb.fresh_local(c.nat.clone());
                        let body = c.eq_of(w.clone(), a.clone());
                        lb.finish_child(lb.mk_lam(w_id, BinderInfo::Default, c.nat.clone(), body))
                    };

                    // h for outer subst: Eq.symm (Eq.trans cgr arc)
                    //   nmul_succ_left q n : @Eq Nat (mul (succ q) n) (add (mul q n) n)
                    let nsl = Expr::apps(nmul_succ_left.clone(), [q.clone(), n.clone()]);
                    // f_add_r = fun z => add z r
                    let f_add_r = {
                        let mut lb = EnvDeclBuilder::child_of(&zb);
                        let (z_id, z) = lb.fresh_local(c.nat.clone());
                        let body = c.add_of(z.clone(), r.clone());
                        lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                    };
                    // congrArg f_add_r (mul (succ q) n) (add (mul q n) n) nsl
                    //   : @Eq Nat (add (mul (succ q) n) r) (add (add (mul q n) n) r)
                    let cgr = c.congr_arg(
                        c.mul_of(c.succ_of(q.clone()), n.clone()),
                        c.add_of(qn.clone(), n.clone()),
                        f_add_r,
                        nsl,
                    );
                    // add_right_comm (mul q n) n r
                    //   : @Eq Nat (add (add (mul q n) n) r) (add (add (mul q n) r) n)
                    let arc =
                        Expr::apps(add_right_comm.clone(), [qn.clone(), n.clone(), r.clone()]);
                    // Eq.trans cgr arc : @Eq Nat small big
                    let tr = c.trans(
                        small.clone(),
                        c.add_of(c.add_of(qn.clone(), n.clone()), r.clone()),
                        big.clone(),
                        cgr,
                        arc,
                    );
                    // Eq.symm : @Eq Nat big small
                    let h_outer = c.symm(small.clone(), big.clone(), tr);

                    // inner subst: motive fun w => @Eq Nat (add w n) a
                    let inner_motive_subst = {
                        let mut lb = EnvDeclBuilder::child_of(&zb);
                        let (w_id, w) = lb.fresh_local(c.nat.clone());
                        let body = c.eq_of(c.add_of(w.clone(), n.clone()), a.clone());
                        lb.finish_child(lb.mk_lam(w_id, BinderInfo::Default, c.nat.clone(), body))
                    };
                    // ih (sub a n) n (key a n f ha hn) hn : @Eq Nat (add (mul q n) r) (sub a n)
                    let key_app = Expr::apps(
                        key.clone(),
                        [a.clone(), n.clone(), f.clone(), ha.clone(), hn.clone()],
                    );
                    let ih_app = Expr::apps(
                        ih.clone(),
                        [
                            c.sub_of(a.clone(), n.clone()),
                            n.clone(),
                            key_app,
                            hn.clone(),
                        ],
                    );
                    // Eq.symm ih_app : @Eq Nat (sub a n) (add (mul q n) r)
                    let ih_sym = c.symm(
                        c.add_of(qn.clone(), r.clone()),
                        c.sub_of(a.clone(), n.clone()),
                        ih_app,
                    );
                    // sub_zero_le n a heq : le n a
                    let szl = Expr::apps(sub_zero_le.clone(), [n.clone(), a.clone(), heq]);
                    // sub_add_cancel a n (sub_zero_le ..) : @Eq Nat (add (sub a n) n) a
                    let sac = Expr::apps(sub_add_cancel.clone(), [a.clone(), n.clone(), szl]);
                    // inner subst : @Eq Nat (add (add (mul q n) r) n) a = @Eq Nat big a
                    let inner = c.subst(
                        inner_motive_subst,
                        c.sub_of(a.clone(), n.clone()),
                        c.add_of(qn.clone(), r.clone()),
                        ih_sym,
                        sac,
                    );
                    // outer subst : @Eq Nat small a
                    let body = c.subst(outer_motive, big.clone(), small.clone(), h_outer, inner);
                    zb.finish_child(zb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body))
                };

                // scase (s=succ k): fun (k : Nat) (_ihk : inner_motive k)
                //     (_heq : @Eq Nat (sub n a) (succ k)) =>
                //   @Eq.subst Nat (fun w => @Eq Nat (add w a) a)
                //     0 (mul 0 n) (Eq.symm (nmul_zero_left n)) (Nat.zero_add a)
                let scase = {
                    let mut kb = EnvDeclBuilder::child_of(&sb);
                    let (k_id, k) = kb.fresh_local(c.nat.clone());
                    let ihk_ty = Expr::pi(
                        BinderInfo::Default,
                        c.eq_of(c.sub_of(n.clone(), a.clone()), k.clone()),
                        c.eq_of(
                            c.add_of(
                                c.mul_of(div_case(k.clone()), n.clone()),
                                mod_case(k.clone()),
                            ),
                            a.clone(),
                        ),
                    );
                    let (ihk_id, _ihk) = kb.fresh_local(ihk_ty.clone());
                    let heq_ty = c.eq_of(c.sub_of(n.clone(), a.clone()), c.succ_of(k.clone()));
                    let (heq_id, _heq) = kb.fresh_local(heq_ty.clone());
                    // motive: fun w => @Eq Nat (add w a) a
                    let subst_motive = {
                        let mut lb = EnvDeclBuilder::child_of(&kb);
                        let (w_id, w) = lb.fresh_local(c.nat.clone());
                        let body = c.eq_of(c.add_of(w.clone(), a.clone()), a.clone());
                        lb.finish_child(lb.mk_lam(w_id, BinderInfo::Default, c.nat.clone(), body))
                    };
                    let nzl = Expr::app(nmul_zero_left.clone(), n.clone());
                    let nzl_sym = c.symm(c.mul_of(c.zero.clone(), n.clone()), c.zero.clone(), nzl);
                    let za = Expr::app(zero_add.clone(), a.clone()); // @Eq Nat (add 0 a) a
                    let body = c.subst(
                        subst_motive,
                        c.zero.clone(),
                        c.mul_of(c.zero.clone(), n.clone()),
                        nzl_sym,
                        za,
                    );
                    let lam = kb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
                    let lam = kb.mk_lam(ihk_id, BinderInfo::Default, ihk_ty, lam);
                    kb.finish_child(kb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam))
                };

                let inner_rec = c.rec0(inner_motive, zcase, scase, c.sub_of(n.clone(), a.clone()));
                let refl_eq = c.refl(c.sub_of(n.clone(), a.clone()));
                let inner = Expr::app(inner_rec, refl_eq);

                let lam = sb.mk_lam(hn_id, BinderInfo::Default, hn_ty, inner);
                let lam = sb.mk_lam(ha_id, BinderInfo::Default, ha_ty, lam);
                let lam = sb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
                let lam = sb.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), lam);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
                sb.finish_child(sb.mk_lam(f_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            let rec = c.rec0(motive, base, step, vfuel.clone());
            let lam = vb.mk_lam(vfuel_id, BinderInfo::Default, c.nat.clone(), rec);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem Nat.div_add_mod (a n : Nat)
    ///   : @Eq Nat (add (mul (div a n) n) (mod a n)) a`  (induction on `n`).
    fn register_divmod_div_add_mod(&mut self, c: &Nat) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.div_add_mod");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nat_div = Nat::const_("Nat.div");
        let nat_mod = Nat::const_("Nat.mod");
        let le_refl = Nat::const_("Nat.le_refl");
        let zero_lt_succ = Nat::const_("Nat.zero_lt_succ");
        let zero_add = Nat::const_("Nat.zero_add");
        let mod_zero = Nat::const_(names::MOD_ZERO);
        let divmod_id = Nat::const_(names::DIVMOD_ID);

        let div_of = |a: Expr, n: Expr| Expr::apps(nat_div.clone(), [a, n]);
        let mod_of = |a: Expr, n: Expr| Expr::apps(nat_mod.clone(), [a, n]);
        // add (mul (div a n) n) (mod a n)
        let euclid = |a: Expr, n: Expr| {
            c.add_of(
                c.mul_of(div_of(a.clone(), n.clone()), n.clone()),
                mod_of(a.clone(), n.clone()),
            )
        };

        // Type: ∀ (a n : Nat), @Eq Nat (euclid a n) a
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let concl = c.eq_of(euclid(a.clone(), n.clone()), a.clone());
        let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
        let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), ty);
        let type_ = b.finish(ty);

        let value = {
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(c.nat.clone());
            let (vn_id, vn) = vb.fresh_local(c.nat.clone());

            // motive: fun nn => @Eq Nat (euclid a nn) a
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&vb);
                let (nn_id, nn) = mb.fresh_local(c.nat.clone());
                let body = c.eq_of(euclid(va.clone(), nn.clone()), va.clone());
                mb.finish_child(mb.mk_lam(nn_id, BinderInfo::Default, c.nat.clone(), body))
            };

            // base (n=0): @Eq.subst Nat
            //   (fun z => @Eq Nat (add (mul (div a 0) 0) z) a)
            //   a (mod a 0) (Eq.symm (mod_zero a)) (Nat.zero_add a)
            let base = {
                let subst_motive = {
                    let mut lb = EnvDeclBuilder::child_of(&vb);
                    let (z_id, z) = lb.fresh_local(c.nat.clone());
                    let body = c.eq_of(
                        c.add_of(
                            c.mul_of(div_of(va.clone(), c.zero.clone()), c.zero.clone()),
                            z.clone(),
                        ),
                        va.clone(),
                    );
                    lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
                };
                // mod_zero a : @Eq Nat (mod a 0) a ; Eq.symm : @Eq Nat a (mod a 0)
                let mz = Expr::app(mod_zero.clone(), va.clone());
                let mz_sym = c.symm(mod_of(va.clone(), c.zero.clone()), va.clone(), mz);
                let za = Expr::app(zero_add.clone(), va.clone());
                c.subst(
                    subst_motive,
                    va.clone(),
                    mod_of(va.clone(), c.zero.clone()),
                    mz_sym,
                    za,
                )
            };

            // step (n=succ k): fun (k : Nat) (_ihk : motive k) =>
            //   divmod_id a a (succ k) (Nat.le_refl a) (Nat.zero_lt_succ k)
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&vb);
                let (k_id, k) = sb.fresh_local(c.nat.clone());
                let ihk_ty = c.eq_of(euclid(va.clone(), k.clone()), va.clone());
                let (ihk_id, _ihk) = sb.fresh_local(ihk_ty.clone());
                let lerefl = Expr::app(le_refl.clone(), va.clone());
                let zls = Expr::app(zero_lt_succ.clone(), k.clone());
                let body = Expr::apps(
                    divmod_id.clone(),
                    [va.clone(), va.clone(), c.succ_of(k.clone()), lerefl, zls],
                );
                let lam = sb.mk_lam(ihk_id, BinderInfo::Default, ihk_ty, body);
                sb.finish_child(sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            let rec = c.rec0(motive, base, step, vn.clone());
            let lam = vb.mk_lam(vn_id, BinderInfo::Default, c.nat.clone(), rec);
            let lam = vb.mk_lam(va_id, BinderInfo::Default, c.nat.clone(), lam);
            vb.finish(lam)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ConstantKind;
    use crate::tc::TypeChecker;

    /// Build the `Nat` numeral `succ^k zero`.
    fn numeral(c: &Nat, k: u32) -> Expr {
        let mut e = c.zero.clone();
        for _ in 0..k {
            e = c.succ_of(e);
        }
        e
    }

    /// `with_prelude()` carries both headline theorems, each registered as a
    /// `Declaration::Theorem` with an EMPTY (foundational-only) axiom closure.
    #[test]
    fn nat_div_mod_headlines_proven_to_foundations() {
        let env = Environment::with_prelude();
        for short in ["Nat.div_add_mod", "Nat.mod_lt"] {
            let name = Name::from_string(short);
            let info = env
                .get_const(&name)
                .unwrap_or_else(|| panic!("{short} must be in the prelude"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{short} must be a Theorem"
            );
            assert!(info.value.is_some(), "{short} must retain its proof value");
            let deps = env
                .axiom_deps(&name)
                .unwrap_or_else(|| panic!("{short}: axiom_deps None"));
            assert!(deps.is_empty(), "{short} rests on {deps:?}");
        }
    }

    /// Every registered `Nat.divmodAux.*` helper is also axiom-free.
    #[test]
    fn nat_div_mod_helpers_axiom_free() {
        let env = Environment::with_prelude();
        for short in [
            names::LE_ZERO,
            names::SUCC_SUB_SUCC,
            names::ZERO_SUB,
            names::SUB_POS_LT,
            names::KEY,
            names::MODCORE_LT,
            names::SUB_ZERO_LE,
            names::NMUL_ZERO_LEFT,
            names::ADD_RIGHT_COMM,
            names::NMUL_SUCC_LEFT,
            names::SUB_ADD_CANCEL,
            names::MODCORE_ZERO,
            names::MOD_ZERO,
            names::DIVMOD_ID,
        ] {
            let name = Name::from_string(short);
            assert!(env.get_const(&name).is_some(), "{short} must be registered");
            let deps = env
                .axiom_deps(&name)
                .unwrap_or_else(|| panic!("{short}: axiom_deps None"));
            assert!(deps.is_empty(), "{short} rests on {deps:?}");
        }
    }

    /// A ground instance of `Nat.div_add_mod` type-checks against the explicit
    /// euclidean statement `@Eq Nat (add (mul (div 7 3) 3) (mod 7 3)) 7`.
    #[test]
    fn nat_div_add_mod_ground_instance_checks() {
        let env = Environment::with_prelude();
        let c = Nat::new();
        let n7 = numeral(&c, 7);
        let n3 = numeral(&c, 3);
        let div = Nat::const_("Nat.div");
        let nat_mod = Nat::const_("Nat.mod");
        let stmt = c.eq_of(
            c.add_of(
                c.mul_of(Expr::apps(div, [n7.clone(), n3.clone()]), n3.clone()),
                Expr::apps(nat_mod, [n7.clone(), n3.clone()]),
            ),
            n7.clone(),
        );
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Nat.div_add_mod"), vec![]),
            [n7, n3],
        );
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&proof, &stmt)
            .expect("Nat.div_add_mod 7 3 must check against the euclidean statement");
    }

    /// A ground instance of `Nat.mod_lt`: `Nat.mod_lt 7 3 (h : 0 < 3)` proves
    /// `Nat.lt (Nat.mod 7 3) 3`.
    #[test]
    fn nat_mod_lt_ground_instance_checks() {
        let env = Environment::with_prelude();
        let c = Nat::new();
        let n7 = numeral(&c, 7);
        let n3 = numeral(&c, 3);
        let nat_mod = Nat::const_("Nat.mod");
        let stmt = c.lt_of(Expr::apps(nat_mod, [n7.clone(), n3.clone()]), n3.clone());
        // 0 < 3 witness: Nat.zero_lt_succ 2
        let pos = Expr::app(Nat::const_("Nat.zero_lt_succ"), numeral(&c, 2));
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Nat.mod_lt"), vec![]),
            [n7, n3, pos],
        );
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&proof, &stmt)
            .expect("Nat.mod_lt 7 3 (0<3) must check against Nat.lt (Nat.mod 7 3) 3");
    }
}
