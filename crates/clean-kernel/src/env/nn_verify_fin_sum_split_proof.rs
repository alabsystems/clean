// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Fin.sum_split_add` — rung 2 of the Parseval
//! infrastructure ladder. THE key rung: it splits a `Fin (a+b)` sum into the
//! low block (indices `0..a`, reindexed by `Fin.castAdd`) and the high block
//! (indices `a..a+b`, reindexed by `Fin.addNat`):
//!
//! ```text
//! Fin.sum_split_add : ∀ (a b : Nat) (h : Fin (a+b) → Rat),
//!   @Eq Rat (Fin.sum (a+b) h)
//!           (Rat.add (Fin.sum a (fun i => h (Fin.castAdd a b i)))
//!                     (Fin.sum b (fun j => h (Fin.addNat  a b j))))
//! ```
//!
//! Proof: induction on `b` via `Nat.rec` with `a` fixed.
//!
//! - **Base (`b = 0`)**: `Fin.sum 0 _ ≡ Rat.zero`, `a+0 ≡ a`, and the low
//!   block reindexes `Fin a` by `Fin.castAdd a 0`, which has the same `val`
//!   as the identity. `Fin.sum_congr` folds the reindex into `Fin.sum a h`;
//!   `Rat.add_zero` drops the empty high block.
//! - **Step (`b = succ b'`)**: `a + succ b' ≡ succ (a+b')`, so `Fin.sum_succ`
//!   peels the top index `Fin.last (a+b')`. The induction hypothesis splits
//!   the remaining `Fin.sum (a+b')` block; three `Fin.sum_congr`/`congrArg`
//!   reindexings (`castSucc ∘ castAdd ≈ castAdd`, `castSucc ∘ addNat ≈
//!   addNat ∘ castSucc`, `last ≈ addNat … last`) line the pieces up with the
//!   `Fin.sum_succ`-expanded high block, and a single `Rat.add_assoc`
//!   reassociates `(P + Q) + r` into `P + (Q + r)`.
//!
//! Every index correspondence is "equal `val` ⟹ propositionally equal `Fin`",
//! discharged by `Fin.eq_of_val_eq` on an `@Eq.refl Nat`. No `sorry`, no
//! axiom: the closure routes through the constructive `Fin.sum`/`Fin.sum_succ`/
//! `Fin.sum_congr`/`Fin.eq_of_val_eq`/`Rat.add_*` family.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_fin_sum::FinSumConsts;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct C {
    base: FinSumConsts,
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    fin: Expr,
    fin_val: Expr,
    fin_cast_succ: Expr,
    fin_cast_add: Expr,
    fin_add_nat: Expr,
    fin_last: Expr,
    fin_eq_of_val: Expr,
    fin_sum_congr: Expr,
    fin_sum_succ: Expr,
    nat_rec: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    eq_nat: Expr,
    eq_rat_c: Expr,
    eq_refl_nat: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg_rr: Expr, // congrArg.{1,1} : Rat → Rat function congruence
    congr_arg_fr: Expr, // congrArg.{1,1} : Fin big → Rat function congruence
    rat_add_zero: Expr,
    rat_add_assoc: Expr,
}

impl C {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            base: FinSumConsts::new(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            fin_add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            fin_eq_of_val: Expr::const_(Name::from_string("Fin.eq_of_val_eq"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            fin_sum_succ: Expr::const_(Name::from_string("Fin.sum_succ"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            #[cfg(test)]
            eq_nat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_rat_c: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl_nat: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg_rr: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            congr_arg_fr: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            rat_add_zero: Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
            rat_add_assoc: Expr::const_(Name::from_string("Rat.add_assoc"), vec![]),
        }
    }

    fn rat(&self) -> Expr {
        self.base.rat.clone()
    }
    fn fin_n(&self, n: Expr) -> Expr {
        Expr::app(self.fin.clone(), n)
    }
    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [x, y])
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn val(&self, n: Expr, x: Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n, x])
    }
    fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.base.fin_sum.clone(), [n, f])
    }
    fn add_rat(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.base.rat_add.clone(), [x, y])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq_rat_c.clone(), [self.rat(), l, r])
    }
    fn fin_to_rat(&self, n: Expr) -> Expr {
        self.base.fin_to_rat(n)
    }
    /// `@Eq.trans Rat l m r h1 h2`.
    fn trans(&self, l: Expr, m: Expr, r: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat(), l, m, r, h1, h2])
    }
    /// `@Eq.symm Rat l r h`.
    fn symm(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat(), l, r, h])
    }
    /// `@congrArg Rat Rat l r f h` — f : Rat → Rat.
    fn congr_rat_fn(&self, l: Expr, r: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg_rr.clone(),
            [self.rat(), self.rat(), l, r, f, h],
        )
    }
    /// `@Fin.castAdd a b` / `@Fin.addNat a b` applied: index map value.
    fn cast_add(&self, a: Expr, b: Expr, i: Expr) -> Expr {
        Expr::apps(self.fin_cast_add.clone(), [a, b, i])
    }
    fn add_nat(&self, a: Expr, b: Expr, j: Expr) -> Expr {
        Expr::apps(self.fin_add_nat.clone(), [a, b, j])
    }
    fn cast_succ(&self, n: Expr, i: Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [n, i])
    }
    fn last(&self, n: Expr) -> Expr {
        Expr::app(self.fin_last.clone(), n)
    }
}

/// `fun (x : Fin k) => body(x)` where `body` is built from the bound var.
fn lam_fin<Fb>(c: &C, parent: &EnvDeclBuilder, k: Expr, body: Fb) -> Expr
where
    Fb: FnOnce(&mut EnvDeclBuilder, Expr) -> Expr,
{
    let fin_k = c.fin_n(k);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = b.fresh_local(fin_k.clone());
    let bd = body(&mut b, x);
    let lam = b.mk_lam(x_id, BinderInfo::Default, fin_k, bd);
    b.finish_child(lam)
}

/// `@Fin.sum_congr k f g pw` : `Fin.sum k f = Fin.sum k g`.
fn sum_congr(c: &C, k: Expr, f: Expr, g: Expr, pw: Expr) -> Expr {
    Expr::apps(c.fin_sum_congr.clone(), [k, f, g, pw])
}

/// Build the pointwise hypothesis `fun (x : Fin k) =>
///   @congrArg (Fin big) Rat (m1 x) (m2 x) h
///     (@Fin.eq_of_val_eq big (m1 x) (m2 x) (@Eq.refl Nat (Fin.val big (m1 x))))`
/// where `m1 x`/`m2 x` are two `Fin big` elements with DEFINITIONALLY EQUAL
/// `val`, so the `Eq.refl` discharges `val (m1 x) = val (m2 x)`. This proves
/// `(h ∘ m1) x = (h ∘ m2) x`, i.e. `h (m1 x) = h (m2 x)`.
fn reindex_pw<M1, M2>(
    c: &C,
    parent: &EnvDeclBuilder,
    k: Expr,
    big: Expr,
    h: Expr,
    m1: M1,
    m2: M2,
) -> Expr
where
    M1: Fn(&C, Expr) -> Expr,
    M2: Fn(&C, Expr) -> Expr,
{
    let fin_big = c.fin_n(big.clone());
    lam_fin(c, parent, k, |_b, x| {
        let lhs = m1(c, x.clone());
        let rhs = m2(c, x);
        // refl : @Eq Nat (val big lhs) (val big lhs)  — accepted as val lhs = val rhs by defeq
        let refl = Expr::apps(
            c.eq_refl_nat.clone(),
            [c.nat.clone(), c.val(big.clone(), lhs.clone())],
        );
        // @Fin.eq_of_val_eq {big} lhs rhs refl : @Eq (Fin big) lhs rhs
        let eqf = Expr::apps(
            c.fin_eq_of_val.clone(),
            [big.clone(), lhs.clone(), rhs.clone(), refl],
        );
        // @congrArg (Fin big) Rat lhs rhs h eqf : h lhs = h rhs
        Expr::apps(
            c.congr_arg_fr.clone(),
            [fin_big.clone(), c.rat(), lhs, rhs, h.clone(), eqf],
        )
    })
}

/// Build the conclusion body of the motive at index `b`, for a given `h`.
/// `Eq Rat (Fin.sum (a+b) h)
///         (Rat.add (Fin.sum a (fun i => h (castAdd a b i)))
///                   (Fin.sum b (fun j => h (addNat a b j))))`.
fn concl_body(c: &C, parent: &EnvDeclBuilder, a: Expr, b: Expr, h: Expr) -> Expr {
    let ab = c.add(a.clone(), b.clone());
    let lhs = c.sum(ab.clone(), h.clone());
    let low = {
        let h = h.clone();
        let a = a.clone();
        let b = b.clone();
        lam_fin(c, parent, a.clone(), move |_bd, i| {
            Expr::app(h.clone(), c.cast_add(a.clone(), b.clone(), i))
        })
    };
    let high = {
        let h = h.clone();
        let a = a.clone();
        let b = b.clone();
        lam_fin(c, parent, b.clone(), move |_bd, j| {
            Expr::app(h.clone(), c.add_nat(a.clone(), b.clone(), j))
        })
    };
    let rhs = c.add_rat(c.sum(a.clone(), low), c.sum(b.clone(), high));
    c.eq_rat(lhs, rhs)
}

/// Theorem type: `∀ (a b : Nat) (h : Fin (a+b) → Rat), <concl_body>`.
fn build_type(c: &C) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (bb_id, bb) = b.fresh_local(c.nat.clone());
    let h_ty = c.fin_to_rat(c.add(a.clone(), bb.clone()));
    let (h_id, h) = b.fresh_local(h_ty.clone());
    let concl = concl_body(c, &b, a.clone(), bb.clone(), h);
    let r = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let r = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// Motive for `Nat.rec` (induction on `b`), with `a` captured from parent:
/// `fun (b : Nat) => ∀ (h : Fin (a+b) → Rat), <concl_body a b h>`.
fn build_motive(c: &C, parent: &EnvDeclBuilder, a: Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (b_id, bb) = mb.fresh_local(c.nat.clone());
    let h_ty = c.fin_to_rat(c.add(a.clone(), bb.clone()));
    let (h_id, h) = mb.fresh_local(h_ty.clone());
    let concl = concl_body(c, &mb, a.clone(), bb.clone(), h);
    let pi = mb.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let lam = mb.mk_lam(b_id, BinderInfo::Default, c.nat.clone(), pi);
    mb.finish_child(lam)
}

/// Base case `M 0`, with `a` captured: `fun (h : Fin (a+0) → Rat) => proof`.
fn build_base(c: &C, parent: &EnvDeclBuilder, a: Expr) -> Expr {
    let mut bb = EnvDeclBuilder::child_of(parent);
    let h_ty = c.fin_to_rat(c.add(a.clone(), c.nat_zero.clone()));
    let (h_id, h) = bb.fresh_local(h_ty.clone());

    // low := fun (i : Fin a) => h (castAdd a 0 i)
    let low = {
        let h = h.clone();
        let a = a.clone();
        let zero = c.nat_zero.clone();
        lam_fin(c, &bb, a.clone(), move |_b, i| {
            Expr::app(h.clone(), c.cast_add(a.clone(), zero.clone(), i))
        })
    };
    // s_low := Fin.sum a low
    let s_low = c.sum(a.clone(), low.clone());
    // s_h := Fin.sum a h   (≡ Fin.sum (a+0) h since a+0 ≡ a)
    let s_h = c.sum(a.clone(), h.clone());

    // e1 : Fin.sum a h = Fin.sum a low
    //   via Fin.sum_congr a h low pw, pw i : h i = h (castAdd a 0 i)
    let pw = {
        let h2 = h.clone();
        let a2 = a.clone();
        reindex_pw(
            c,
            &bb,
            a.clone(),
            a.clone(), // big = a (since castAdd a 0 i : Fin (a+0) ≡ Fin a)
            h2,
            |_c, x| x,                                                    // m1 = identity
            move |cc, x| cc.cast_add(a2.clone(), cc.nat_zero.clone(), x), // m2 = castAdd a 0
        )
    };
    let e1 = sum_congr(c, a.clone(), h.clone(), low.clone(), pw);

    // e2 : Rat.add s_low Rat.zero = s_low   via Rat.add_zero s_low
    let e2 = Expr::app(c.rat_add_zero.clone(), s_low.clone());
    // symm e2 : s_low = Rat.add s_low Rat.zero
    let e2s = c.symm(
        c.add_rat(s_low.clone(), c.base.rat_zero.clone()),
        s_low.clone(),
        e2,
    );

    // proof : Fin.sum a h = Rat.add s_low Rat.zero  =  trans e1 e2s
    let proof = c.trans(
        s_h,
        s_low.clone(),
        c.add_rat(s_low, c.base.rat_zero.clone()),
        e1,
        e2s,
    );
    let lam = bb.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
    bb.finish_child(lam)
}

/// Step case `fun (b' : Nat) (ih : M b') (h : Fin (a + succ b') → Rat) => proof`,
/// with `a` captured.
fn build_step(c: &C, parent: &EnvDeclBuilder, a: Expr) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (bp_id, bp) = sb.fresh_local(c.nat.clone()); // b'
                                                     // ih : ∀ (h : Fin (a+b') → Rat), <concl_body a b' h>
    let m = c.add(a.clone(), bp.clone()); // m := a + b'
    let ih_ty = {
        let h_ty = c.fin_to_rat(m.clone());
        let (h_id, h) = sb.fresh_local(h_ty.clone());
        let concl = concl_body(c, &sb, a.clone(), bp.clone(), h);
        sb.mk_pi(h_id, BinderInfo::Default, h_ty, concl)
    };
    let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

    let sbp = c.succ(bp.clone()); // succ b'
    let a_sbp = c.add(a.clone(), sbp.clone()); // a + succ b'  ≡  succ m
    let h_ty = c.fin_to_rat(a_sbp.clone());
    let (h_id, h) = sb.fresh_local(h_ty.clone());

    // h ∘ cs m  : Fin m → Rat   (the IH summand)
    let h_cs = {
        let h = h.clone();
        let m = m.clone();
        lam_fin(c, &sb, m.clone(), move |_b, x| {
            Expr::app(h.clone(), c.cast_succ(m.clone(), x))
        })
    };

    // ── LHS expansion ──
    // step_L : Fin.sum (succ m) h
    //        = Rat.add (Fin.sum m h_cs) (h (last m))
    // built directly = @Fin.sum_succ m h  (note its summand is fun i => h (castSucc m i) ≡ h_cs)
    let h_last_m = Expr::app(h.clone(), c.last(m.clone()));
    let s_m_hcs = c.sum(m.clone(), h_cs.clone());
    let lhs = c.sum(c.succ(m.clone()), h.clone());
    let step_l = Expr::apps(c.fin_sum_succ.clone(), [m.clone(), h.clone()]);
    let lvl0 = c.add_rat(s_m_hcs.clone(), h_last_m.clone());

    // ── IH application at h_cs ──
    // ih h_cs : Fin.sum m h_cs
    //         = Rat.add (Fin.sum a (h_cs ∘ castAdd a b')) (Fin.sum b' (h_cs ∘ addNat a b'))
    let p0_fn = {
        let h_cs = h_cs.clone();
        let a = a.clone();
        let bp = bp.clone();
        lam_fin(c, &sb, a.clone(), move |_b, i| {
            Expr::app(h_cs.clone(), c.cast_add(a.clone(), bp.clone(), i))
        })
    };
    let q0_fn = {
        let h_cs = h_cs.clone();
        let a = a.clone();
        let bp = bp.clone();
        lam_fin(c, &sb, bp.clone(), move |_b, j| {
            Expr::app(h_cs.clone(), c.add_nat(a.clone(), bp.clone(), j))
        })
    };
    let p0 = c.sum(a.clone(), p0_fn.clone());
    let q0 = c.sum(bp.clone(), q0_fn.clone());
    let ih_app = Expr::app(ih.clone(), h_cs.clone());
    let ih_rhs = c.add_rat(p0.clone(), q0.clone());

    // rewrite lvl0's left factor Fin.sum m h_cs  ↦  ih_rhs
    // congrArg (fun w => Rat.add w (h (last m))) (ih h_cs)
    let add_right_lastm = {
        let last = h_last_m.clone();
        let mut bld = EnvDeclBuilder::child_of(&sb);
        let (x_id, x) = bld.fresh_local(c.rat());
        let body = c.add_rat(x, last);
        let lam = bld.mk_lam(x_id, BinderInfo::Default, c.rat(), body);
        bld.finish_child(lam)
    };
    let lvl1 = c.add_rat(ih_rhs.clone(), h_last_m.clone());
    let step_ih = c.congr_rat_fn(s_m_hcs.clone(), ih_rhs.clone(), add_right_lastm, ih_app);

    // ── target RHS pieces ──
    // P := Fin.sum a (fun i => h (castAdd a (succ b') i))
    let p_fn = {
        let h = h.clone();
        let a = a.clone();
        let sbp = sbp.clone();
        lam_fin(c, &sb, a.clone(), move |_b, i| {
            Expr::app(h.clone(), c.cast_add(a.clone(), sbp.clone(), i))
        })
    };
    let p = c.sum(a.clone(), p_fn.clone());
    // high := fun j => h (addNat a (succ b') j)  : Fin (succ b') → Rat
    let high_fn = {
        let h = h.clone();
        let a = a.clone();
        let sbp = sbp.clone();
        lam_fin(c, &sb, sbp.clone(), move |_b, j| {
            Expr::app(h.clone(), c.add_nat(a.clone(), sbp.clone(), j))
        })
    };
    // step_R : Fin.sum (succ b') high = Rat.add (Fin.sum b' (high ∘ castSucc b')) (high (last b'))
    let s_high = c.sum(sbp.clone(), high_fn.clone());
    let step_r = Expr::apps(c.fin_sum_succ.clone(), [bp.clone(), high_fn.clone()]);
    // Q := Fin.sum b' (fun j => high (castSucc b' j)) = Fin.sum b' (fun j => h (addNat a (succ b') (castSucc b' j)))
    let q_fn = {
        let high_fn = high_fn.clone();
        let bp = bp.clone();
        lam_fin(c, &sb, bp.clone(), move |_b, j| {
            Expr::app(high_fn.clone(), c.cast_succ(bp.clone(), j))
        })
    };
    let q = c.sum(bp.clone(), q_fn.clone());
    // r := high (last b') = h (addNat a (succ b') (last b'))
    let rr = Expr::app(high_fn.clone(), c.last(bp.clone()));
    let q_plus_r = c.add_rat(q.clone(), rr.clone());

    // ── congruence C1 : P0 = P (low block) ──
    // P0 summand: fun i => h_cs (castAdd a b' i) = fun i => h (castSucc m (castAdd a b' i))
    // P  summand: fun i => h (castAdd a (succ b') i)
    // big = a + succ b' = succ m
    let big = a_sbp.clone();
    let c1_pw = {
        let a2 = a.clone();
        let bp2 = bp.clone();
        let m2 = m.clone();
        let a4 = a.clone();
        let sbp2 = sbp.clone();
        reindex_pw(
            c,
            &sb,
            a.clone(),
            big.clone(),
            h.clone(),
            // m1 i = castSucc m (castAdd a b' i)
            move |cc, i| cc.cast_succ(m2.clone(), cc.cast_add(a2.clone(), bp2.clone(), i)),
            // m2 i = castAdd a (succ b') i
            move |cc, i| cc.cast_add(a4.clone(), sbp2.clone(), i),
        )
    };
    let c1 = sum_congr(c, a.clone(), p0_fn.clone(), p_fn.clone(), c1_pw);

    // ── congruence C2 : Q0 = Q ──
    // Q0 summand: fun j => h_cs (addNat a b' j) = fun j => h (castSucc m (addNat a b' j))
    // Q  summand: fun j => h (addNat a (succ b') (castSucc b' j))
    let c2_pw = {
        let a2 = a.clone();
        let bp2 = bp.clone();
        let m2 = m.clone();
        let a3 = a.clone();
        let bp3 = bp.clone();
        let sbp3 = sbp.clone();
        reindex_pw(
            c,
            &sb,
            bp.clone(),
            big.clone(),
            h.clone(),
            move |cc, j| cc.cast_succ(m2.clone(), cc.add_nat(a2.clone(), bp2.clone(), j)),
            move |cc, j| cc.add_nat(a3.clone(), sbp3.clone(), cc.cast_succ(bp3.clone(), j)),
        )
    };
    let c2 = sum_congr(c, bp.clone(), q0_fn.clone(), q_fn.clone(), c2_pw);

    // ── congruence C3 : r0 = r (last terms) ──
    // r0 = h (last m);  r = h (addNat a (succ b') (last b'))
    let last_m = c.last(m.clone());
    let an_last = c.add_nat(a.clone(), sbp.clone(), c.last(bp.clone()));
    let c3 = {
        // refl : val big (last m) = val big (last m)  (accepted = val (last m) = val (an_last) by defeq)
        let refl = Expr::apps(
            c.eq_refl_nat.clone(),
            [c.nat.clone(), c.val(big.clone(), last_m.clone())],
        );
        let eqf = Expr::apps(
            c.fin_eq_of_val.clone(),
            [big.clone(), last_m.clone(), an_last.clone(), refl],
        );
        Expr::apps(
            c.congr_arg_fr.clone(),
            [
                c.fin_n(big.clone()),
                c.rat(),
                last_m.clone(),
                an_last.clone(),
                h.clone(),
                eqf,
            ],
        )
    };

    // ── assemble the rewriting of lvl1 = Rat.add (Rat.add P0 Q0) r0
    //    into Rat.add (Rat.add P Q) r, then reassociate. ──
    // Note ih_rhs = Rat.add P0 Q0, and lvl1 = Rat.add ih_rhs r0.
    // s1 : Rat.add P0 Q0 = Rat.add P Q   (congr on both factors)
    //   via two steps: congr left (P0↦P), then congr right (Q0↦Q).
    let add_pq_right_q0 = {
        // fun w => Rat.add w Q0
        let q0 = q0.clone();
        let mut bld = EnvDeclBuilder::child_of(&sb);
        let (x_id, x) = bld.fresh_local(c.rat());
        let body = c.add_rat(x, q0);
        let lam = bld.mk_lam(x_id, BinderInfo::Default, c.rat(), body);
        bld.finish_child(lam)
    };
    let add_pq_left_p = {
        // fun w => Rat.add P w
        let p = p.clone();
        let mut bld = EnvDeclBuilder::child_of(&sb);
        let (x_id, x) = bld.fresh_local(c.rat());
        let body = c.add_rat(p, x);
        let lam = bld.mk_lam(x_id, BinderInfo::Default, c.rat(), body);
        bld.finish_child(lam)
    };
    // a1 : Rat.add P0 Q0 = Rat.add P Q0
    let a1 = c.congr_rat_fn(p0.clone(), p.clone(), add_pq_right_q0, c1);
    // a2 : Rat.add P Q0 = Rat.add P Q
    let a2 = c.congr_rat_fn(q0.clone(), q.clone(), add_pq_left_p, c2);
    // s1 : Rat.add P0 Q0 = Rat.add P Q
    let pq0 = c.add_rat(p0.clone(), q0.clone());
    let pq = c.add_rat(p.clone(), q.clone());
    let s1 = c.trans(
        pq0.clone(),
        c.add_rat(p.clone(), q0.clone()),
        pq.clone(),
        a1,
        a2,
    );

    // s2 : Rat.add (Rat.add P0 Q0) r0 = Rat.add (Rat.add P Q) r0   (congr left via s1)
    let add_r0 = {
        let r0 = h_last_m.clone();
        let mut bld = EnvDeclBuilder::child_of(&sb);
        let (x_id, x) = bld.fresh_local(c.rat());
        let body = c.add_rat(x, r0);
        let lam = bld.mk_lam(x_id, BinderInfo::Default, c.rat(), body);
        bld.finish_child(lam)
    };
    let s2 = c.congr_rat_fn(pq0.clone(), pq.clone(), add_r0, s1);

    // s3 : Rat.add (Rat.add P Q) r0 = Rat.add (Rat.add P Q) r   (congr right via c3)
    let add_pq_left = {
        let pq = pq.clone();
        let mut bld = EnvDeclBuilder::child_of(&sb);
        let (x_id, x) = bld.fresh_local(c.rat());
        let body = c.add_rat(pq, x);
        let lam = bld.mk_lam(x_id, BinderInfo::Default, c.rat(), body);
        bld.finish_child(lam)
    };
    let s3 = c.congr_rat_fn(h_last_m.clone(), rr.clone(), add_pq_left, c3);

    // s4 : Rat.add (Rat.add P Q) r = Rat.add P (Rat.add Q r)   (Rat.add_assoc P Q r)
    let s4 = Expr::apps(c.rat_add_assoc.clone(), [p.clone(), q.clone(), rr.clone()]);

    // s5 : Rat.add P (Rat.add Q r) = Rat.add P (Fin.sum (succ b') high)
    //   via congr right: Rat.add Q r = Fin.sum (succ b') high  is Eq.symm step_R
    let step_r_sym = c.symm(s_high.clone(), q_plus_r.clone(), step_r);
    let s5 = c.congr_rat_fn(
        q_plus_r.clone(),
        s_high.clone(),
        add_pq_left_p_clone(c, &sb, p.clone()),
        step_r_sym,
    );

    // ── chain everything ──
    // lhs = Fin.sum (succ m) h
    // step_l : lhs = lvl0 = Rat.add (Fin.sum m h_cs) r0
    // step_ih: lvl0 = lvl1 = Rat.add (Rat.add P0 Q0) r0
    // s2     : lvl1 = Rat.add (Rat.add P Q) r0
    // s3     : ...  = Rat.add (Rat.add P Q) r
    // s4     : ...  = Rat.add P (Rat.add Q r)
    // s5     : ...  = Rat.add P (Fin.sum (succ b') high)   = target RHS
    let t1 = c.add_rat(pq.clone(), h_last_m.clone()); // Rat.add (Rat.add P Q) r0
    let t2 = c.add_rat(pq.clone(), rr.clone()); // Rat.add (Rat.add P Q) r
    let t3 = c.add_rat(p.clone(), q_plus_r.clone()); // Rat.add P (Rat.add Q r)
    let target_rhs = c.add_rat(p.clone(), s_high.clone()); // Rat.add P (Fin.sum (succ b') high)

    let chain = c.trans(lhs.clone(), lvl0.clone(), lvl1.clone(), step_l, step_ih);
    let chain = c.trans(lhs.clone(), lvl1.clone(), t1.clone(), chain, s2);
    let chain = c.trans(lhs.clone(), t1.clone(), t2.clone(), chain, s3);
    let chain = c.trans(lhs.clone(), t2.clone(), t3.clone(), chain, s4);
    let proof = c.trans(lhs.clone(), t3.clone(), target_rhs, chain, s5);

    // wrap binders: h, ih, b'
    let lam = sb.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
    let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
    let lam = sb.mk_lam(bp_id, BinderInfo::Default, c.nat.clone(), lam);
    sb.finish_child(lam)
}

/// Helper: `fun (w : Rat) => Rat.add P w`, fresh per call.
fn add_pq_left_p_clone(c: &C, parent: &EnvDeclBuilder, p: Expr) -> Expr {
    let mut bld = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = bld.fresh_local(c.rat());
    let body = c.add_rat(p, x);
    let lam = bld.mk_lam(x_id, BinderInfo::Default, c.rat(), body);
    bld.finish_child(lam)
}

fn build_value(c: &C) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let motive = build_motive(c, &b, a.clone());
    let base = build_base(c, &b, a.clone());
    let step = build_step(c, &b, a.clone());
    // fun a => fun b => @Nat.rec.{0} motive base step b
    let (b_id, bb) = b.fresh_local(c.nat.clone());
    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, bb]);
    let lam = b.mk_lam(b_id, BinderInfo::Default, c.nat.clone(), rec_app);
    let lam = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), lam);
    b.finish(lam)
}

impl Environment {
    /// Register `Fin.sum_split_add` as a kernel-checked constructive theorem.
    pub(crate) fn register_fin_sum_split_add_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_split_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Dependencies: Fin.sum family (carrier + sum_succ + sum_congr),
        // the split-index maps, Fin.eq_of_val_eq, Rat add field lemmas, Eq.
        self.init_eq()?;
        self.init_fin_sum()?; // Fin.sum, Fin.sum_succ
        self.register_fin_split_index()?; // Fin.castAdd, Fin.addNat
        self.register_fin_dec_eq_proof()?; // Fin.eq_of_val_eq
        self.init_rat_field_inst()?; // Rat.add_zero, Rat.add_assoc
        {
            let fc = FinSumConsts::new();
            self.register_fin_sum_congr(&fc)?; // Fin.sum_congr
        }

        let c = C::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_type(&c),
            value: build_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_sum_split_add_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_split_add_theorem().expect("register");
        env.register_fin_sum_split_add_theorem()
            .expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n = Name::from_string("Fin.sum_split_add");
        let _ = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .unwrap_or_else(|e| panic!("Fin.sum_split_add should type-check: {e:?}"));
        assert_eq!(
            env.get_const(&n).expect("registered").kind,
            ConstantKind::Theorem
        );
        let deps = env.axiom_deps(&n).expect("registered");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&n),
            Some(ProofQuality::Constructive)
        ));
    }
}
