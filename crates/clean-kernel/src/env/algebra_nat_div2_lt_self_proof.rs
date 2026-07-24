// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive definition of `Nat.div2 : Nat → Nat` and proof of
//! `Nat.div2_lt_self : ∀ n : Nat, Nat.lt Nat.zero n → Nat.lt (Nat.div2 n) n`.
//!
//! This is the recursive-measure foundation for the `Nat.bitwise`
//! well-founded recursion (`Nat.land` / `Nat.lor` / `Nat.xor`, currently
//! admitted domain axioms in `axiom_audit.rs`): the WF measure for
//! `Nat.bitwise` recurses on `n` via `n / 2`, and termination needs exactly
//! `div2 n < n` for `n > 0`.
//!
//! # Encoding: a parity-carry pair fold (single-step `Nat.rec`)
//!
//! The naive two-step recursion `div2 (succ (succ n)) = succ (div2 n)` does
//! NOT hold by `rfl` for symbolic `n` (the parity discriminant is stuck —
//! the wave-7 lesson). We sidestep this by folding a PAIR
//! `(quotient, parity)` with the single-step recursor `Nat.rec`, so every
//! single step is definitional:
//!
//! ```text
//! Nat.div2Pair n : Prod Nat Nat
//!   := Nat.rec (Prod.mk 0 0) (fun _ acc => step acc) n
//!   where step (h, p) := (h + p, 1 - p)        -- p ∈ {0,1}
//!
//! Nat.div2    n := Prod.fst (Nat.div2Pair n)   -- the quotient
//! Nat.div2Par n := Prod.snd (Nat.div2Pair n)   -- the parity carry (0 or 1)
//! ```
//!
//! Because `Nat.rec` reduces by a SINGLE iota step, both
//! `Nat.div2 (succ m) ≡ Nat.div2 m + Nat.div2Par m` and
//! `Nat.div2Par (succ m) ≡ 1 - Nat.div2Par m` hold definitionally (verified
//! as `rfl` ground/symbolic checks before this module was written). No
//! stuck parity discriminant ever appears.
//!
//! # Load-bearing invariant
//!
//! `Nat.div2_add_par_le : ∀ n, Nat.le (Nat.add (Nat.div2 n) (Nat.div2Par n)) n`
//! — i.e. `div2 n + par n ≤ n` — proved by single-step induction on `n`:
//!
//! - base `n = 0`: `div2 0 + par 0 ≡ 0 + 0 ≡ 0`, witnessed `Nat.le_refl 0`.
//! - step `n = succ m`, `ih : div2 m + par m ≤ m`. The goal LHS reduces to
//!   `(div2 m + par m) + (1 - par m)`. Bound it WITHOUT any parity
//!   case-split, purely by monotonicity:
//!     `(div2 m + par m) + (1 - par m)`
//!       `≤ (div2 m + par m) + 1`        [`Nat.add_le_add_left` ∘ `Nat.sub_le 1 (par m)`]
//!       `≡ succ (div2 m + par m)`       [`x + 1 ≡ succ x` definitionally]
//!       `≤ succ m`                      [`Nat.succ_le_succ … ih`]
//!   chained with `Nat.le_trans`.
//!
//! # Main theorem
//!
//! `Nat.div2_lt_self n (h : 0 < n) : div2 n < n` by case analysis on `n`
//! (`Nat.rec` with motive `fun t => Nat.lt 0 t → Nat.lt (div2 t) t`):
//! - `n = 0`: hypothesis `Nat.lt 0 0 ≡ Nat.le 1 0` is absurd
//!   (`Nat.not_succ_le_zero 0`), discharged by `False.elim`.
//! - `n = succ m`: goal `Nat.lt (div2 (succ m)) (succ m) ≡
//!   Nat.le (succ (div2 (succ m))) (succ m)`. Since
//!   `div2 (succ m) ≡ div2 m + par m`, this is
//!   `Nat.succ_le_succ (div2 m + par m) m (Nat.div2_add_par_le m)`.
//!
//! # Axiom closure
//!
//! `Nat.div2Pair`/`Nat.div2`/`Nat.div2Par` are reducible Definitions over
//! `Nat.rec`, `Prod`, `Prod.mk`, `Prod.fst`, `Prod.snd`, `Nat.add`,
//! `Nat.sub` — none axioms. The two theorems additionally mention only
//! `Eq`-free order constructors and the constructive lemmas `Nat.le_refl`,
//! `Nat.le_trans`, `Nat.succ_le_succ`, `Nat.add_le_add_left`, `Nat.sub_le`,
//! `Nat.not_succ_le_zero`, and `False.elim`. Therefore
//! `env.axiom_deps` is empty for every declaration introduced here.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across the div2 definitions and proofs.
struct NatDiv2Consts {
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_one: Expr,
    nat_add: Expr,
    nat_sub: Expr,
    nat_rec: Expr,
    prod_type: Expr,
    prod_mk: Expr,
    prod_fst: Expr,
    prod_snd: Expr,
    div2_pair: Expr,
    div2: Expr,
    div2_par: Expr,
    nat_le: Expr,
    nat_lt: Expr,
    le_refl: Expr,
    le_trans: Expr,
    succ_le_succ: Expr,
    add_le_add_left: Expr,
    sub_le: Expr,
    not_succ_le_zero: Expr,
    false_elim: Expr,
}

impl NatDiv2Consts {
    fn new() -> Self {
        let zero = Level::zero();
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        // 1 = Nat.succ Nat.zero
        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero,
            nat_succ,
            nat_one,
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_sub: Expr::const_(Name::from_string("Nat.sub"), vec![]),
            // Nat.rec.{u}: u=1 when the motive is Type-valued (the pair fold),
            // u=0 when Prop-valued (the invariant / main theorem). We cache
            // BOTH explicitly at the use sites instead of here.
            nat_rec: Expr::const_(
                Name::from_string("Nat.rec"),
                vec![Level::succ(zero.clone())],
            ),
            // Prod : Type u → Type v → Type (max u v); here u = v = 0.
            prod_type: Expr::const_(Name::from_string("Prod"), vec![zero.clone(), zero.clone()]),
            prod_mk: Expr::const_(
                Name::from_string("Prod.mk"),
                vec![zero.clone(), zero.clone()],
            ),
            prod_fst: Expr::const_(
                Name::from_string("Prod.fst"),
                vec![zero.clone(), zero.clone()],
            ),
            prod_snd: Expr::const_(
                Name::from_string("Prod.snd"),
                vec![zero.clone(), zero.clone()],
            ),
            div2_pair: Expr::const_(Name::from_string("Nat.div2Pair"), vec![]),
            div2: Expr::const_(Name::from_string("Nat.div2"), vec![]),
            div2_par: Expr::const_(Name::from_string("Nat.div2Par"), vec![]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            nat_lt: Expr::const_(Name::from_string("Nat.lt"), vec![]),
            le_refl: Expr::const_(Name::from_string("Nat.le_refl"), vec![]),
            le_trans: Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
            succ_le_succ: Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
            add_le_add_left: Expr::const_(Name::from_string("Nat.add_le_add_left"), vec![]),
            sub_le: Expr::const_(Name::from_string("Nat.sub_le"), vec![]),
            not_succ_le_zero: Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![zero]),
        }
    }

    /// `Prod Nat Nat`.
    fn prod_nat_nat(&self) -> Expr {
        Expr::apps(
            self.prod_type.clone(),
            [self.nat_type.clone(), self.nat_type.clone()],
        )
    }

    /// `@Prod.fst Nat Nat p`.
    fn fst(&self, p: Expr) -> Expr {
        Expr::apps(
            self.prod_fst.clone(),
            [self.nat_type.clone(), self.nat_type.clone(), p],
        )
    }

    /// `@Prod.snd Nat Nat p`.
    fn snd(&self, p: Expr) -> Expr {
        Expr::apps(
            self.prod_snd.clone(),
            [self.nat_type.clone(), self.nat_type.clone(), p],
        )
    }

    /// `@Prod.mk Nat Nat a b`.
    fn mk(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.prod_mk.clone(),
            [self.nat_type.clone(), self.nat_type.clone(), a, b],
        )
    }

    /// `Nat.add x y`.
    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [x, y])
    }

    /// `Nat.sub x y`.
    fn sub(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_sub.clone(), [x, y])
    }

    /// `Nat.succ x`.
    fn succ(&self, x: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), x)
    }

    /// `Nat.div2 n`.
    fn div2(&self, n: Expr) -> Expr {
        Expr::app(self.div2.clone(), n)
    }

    /// `Nat.div2Par n`.
    fn par(&self, n: Expr) -> Expr {
        Expr::app(self.div2_par.clone(), n)
    }

    /// `Nat.le a b`.
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }

    /// `Nat.lt a b`.
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [a, b])
    }
}

/// `Nat.div2Pair : Nat → Prod Nat Nat`, a reducible Definition.
///
/// `fun n => @Nat.rec.{1} (fun _ => Prod Nat Nat)
///                        (Prod.mk 0 0)
///                        (fun _ acc => Prod.mk (acc.1 + acc.2) (1 - acc.2))
///                        n`.
fn build_div2_pair(c: &NatDiv2Consts) -> (Expr, Expr) {
    let prod = c.prod_nat_nat();
    // type: Nat → Prod Nat Nat
    let type_ = Expr::pi(BinderInfo::Default, c.nat_type.clone(), prod.clone());

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());

    // motive: fun (_ : Nat) => Prod Nat Nat
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, _t) = mb.fresh_local(c.nat_type.clone());
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), prod.clone());
        mb.finish_child(lam)
    };

    // base: Prod.mk 0 0
    let base = c.mk(c.nat_zero.clone(), c.nat_zero.clone());

    // step: fun (_ : Nat) (acc : Prod Nat Nat) =>
    //         Prod.mk (acc.1 + acc.2) (1 - acc.2)
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (k_id, _k) = sb.fresh_local(c.nat_type.clone());
        let (acc_id, acc) = sb.fresh_local(prod.clone());
        let h = c.fst(acc.clone());
        let p = c.snd(acc.clone());
        let new_h = c.add(h, p.clone());
        let new_p = c.sub(c.nat_one.clone(), p);
        let body = c.mk(new_h, new_p);
        let lam = sb.mk_lam(acc_id, BinderInfo::Default, prod.clone(), body);
        let lam = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam);
        sb.finish_child(lam)
    };

    // @Nat.rec.{1} motive base step n
    let nat_rec1 = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let rec_app = Expr::apps(nat_rec1, [motive, base, step, n]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    let value = b.finish(val);

    (type_, value)
}

/// `Nat.div2 : Nat → Nat`, reducible Definition `fun n => (div2Pair n).1`.
fn build_div2(c: &NatDiv2Consts) -> (Expr, Expr) {
    let type_ = Expr::pi(BinderInfo::Default, c.nat_type.clone(), c.nat_type.clone());
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let pair = Expr::app(c.div2_pair.clone(), n);
    let body = c.fst(pair);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
    (type_, b.finish(val))
}

/// `Nat.div2Par : Nat → Nat`, reducible Definition `fun n => (div2Pair n).2`.
fn build_div2_par(c: &NatDiv2Consts) -> (Expr, Expr) {
    let type_ = Expr::pi(BinderInfo::Default, c.nat_type.clone(), c.nat_type.clone());
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let pair = Expr::app(c.div2_pair.clone(), n);
    let body = c.snd(pair);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
    (type_, b.finish(val))
}

/// `Nat.div2_add_par_le : ∀ n, Nat.le (Nat.add (div2 n) (par n)) n`.
///
/// Proved by single-step induction on `n` via `@Nat.rec.{0}` with motive
/// `fun t => Nat.le (Nat.add (div2 t) (par t)) t`.
fn build_invariant(c: &NatDiv2Consts) -> (Expr, Expr) {
    // type: ∀ n : Nat, Nat.le (div2 n + par n) n
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat_type.clone());
        let concl = c.le(c.add(c.div2(n.clone()), c.par(n.clone())), n.clone());
        let pi = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
        b.finish(pi)
    };

    let mut vb = EnvDeclBuilder::new();
    let (n_id, n) = vb.fresh_local(c.nat_type.clone());

    // motive: fun (t : Nat) => Nat.le (div2 t + par t) t
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&vb);
        let (t_id, t) = mb.fresh_local(c.nat_type.clone());
        let body = c.le(c.add(c.div2(t.clone()), c.par(t.clone())), t.clone());
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // base: motive 0 ≡ Nat.le (0 + 0) 0 ≡ Nat.le 0 0. Witnessed Nat.le_refl 0.
    let base = Expr::app(c.le_refl.clone(), c.nat_zero.clone());

    // step: fun (m : Nat) (ih : Nat.le (div2 m + par m) m) =>
    //   Nat.le_trans
    //     (div2 (succ m) + par (succ m))     -- ≡ (div2 m + par m) + (1 - par m)
    //     (succ (div2 m + par m))            -- ≡ (div2 m + par m) + 1
    //     (succ m)
    //     (Nat.add_le_add_left (par (succ m)) 1 (Nat.sub_le 1 (par m)) (div2 m + par m))
    //     (Nat.succ_le_succ (div2 m + par m) m ih)
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (m_id, m) = sb.fresh_local(c.nat_type.clone());
        let dm_pm = c.add(c.div2(m.clone()), c.par(m.clone())); // div2 m + par m
        let ih_type = c.le(dm_pm.clone(), m.clone());
        let (ih_id, ih) = sb.fresh_local(ih_type.clone());

        let succ_m = c.succ(m.clone());
        // a := div2 (succ m) + par (succ m)   (defn = (div2 m + par m) + (1 - par m))
        let a = c.add(c.div2(succ_m.clone()), c.par(succ_m.clone()));
        // b := succ (div2 m + par m)          (defn = (div2 m + par m) + 1)
        let b_mid = c.succ(dm_pm.clone());
        // cc := succ m
        let cc = succ_m.clone();

        // left : Nat.le a b
        //   = Nat.add_le_add_left (par (succ m)) 1 (Nat.sub_le 1 (par m)) (div2 m + par m)
        //   where  par (succ m) ≡ 1 - par m,  so this has type
        //          Nat.le ((div2 m+par m) + (1 - par m)) ((div2 m+par m) + 1) ≡ Nat.le a b.
        let sub_le_proof = Expr::apps(c.sub_le.clone(), [c.nat_one.clone(), c.par(m.clone())]);
        let left = Expr::apps(
            c.add_le_add_left.clone(),
            [
                c.par(succ_m.clone()), // a' = par (succ m) ≡ 1 - par m
                c.nat_one.clone(),     // b' = 1
                sub_le_proof,          // h : Nat.le (par (succ m)) 1
                dm_pm.clone(),         // k = div2 m + par m
            ],
        );

        // right : Nat.le b cc = Nat.succ_le_succ (div2 m + par m) m ih
        let right = Expr::apps(c.succ_le_succ.clone(), [dm_pm.clone(), m.clone(), ih]);

        // Nat.le_trans a b cc left right
        let trans = Expr::apps(c.le_trans.clone(), [a, b_mid, cc, left, right]);

        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, trans);
        let lam_m = sb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_m)
    };

    // @Nat.rec.{0} motive base step n
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_app = Expr::apps(nat_rec0, [motive, base, step, n]);
    let val = vb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    (type_, vb.finish(val))
}

/// `Nat.div2_lt_self : ∀ n, Nat.lt Nat.zero n → Nat.lt (div2 n) n`.
///
/// Case analysis on `n` via `@Nat.rec.{0}` with motive
/// `fun t => Nat.lt 0 t → Nat.lt (div2 t) t`.
fn build_main(c: &NatDiv2Consts) -> (Expr, Expr) {
    // type: ∀ n : Nat, Nat.lt 0 n → Nat.lt (div2 n) n
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat_type.clone());
        let hyp = c.lt(c.nat_zero.clone(), n.clone());
        let concl = c.lt(c.div2(n.clone()), n.clone());
        let imp = {
            let (h_id, _h) = b.fresh_local(hyp.clone());
            b.mk_pi(h_id, BinderInfo::Default, hyp, concl)
        };
        let pi = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), imp);
        b.finish(pi)
    };

    let mut vb = EnvDeclBuilder::new();
    let (n_id, n) = vb.fresh_local(c.nat_type.clone());

    // motive: fun (t : Nat) => Nat.lt 0 t → Nat.lt (div2 t) t
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&vb);
        let (t_id, t) = mb.fresh_local(c.nat_type.clone());
        let hyp = c.lt(c.nat_zero.clone(), t.clone());
        let concl = c.lt(c.div2(t.clone()), t.clone());
        let imp = {
            let (h_id, _h) = mb.fresh_local(hyp.clone());
            mb.mk_pi(h_id, BinderInfo::Default, hyp, concl)
        };
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), imp);
        mb.finish_child(lam)
    };

    // base: motive 0 ≡ (Nat.lt 0 0 → Nat.lt (div2 0) 0).
    //   fun (h0 : Nat.lt 0 0) =>
    //     @False.elim.{0} (Nat.lt (div2 0) 0) (Nat.not_succ_le_zero 0 h0)
    //   (Nat.lt 0 0 ≡ Nat.le (succ 0) 0, so not_succ_le_zero 0 h0 : False.)
    let base = {
        let mut bb = EnvDeclBuilder::child_of(&vb);
        let lt_00 = c.lt(c.nat_zero.clone(), c.nat_zero.clone());
        let (h0_id, h0) = bb.fresh_local(lt_00.clone());
        let false_proof = Expr::apps(c.not_succ_le_zero.clone(), [c.nat_zero.clone(), h0]);
        let target = c.lt(c.div2(c.nat_zero.clone()), c.nat_zero.clone());
        let body = Expr::apps(c.false_elim.clone(), [target, false_proof]);
        let lam = bb.mk_lam(h0_id, BinderInfo::Default, lt_00, body);
        bb.finish_child(lam)
    };

    // step: fun (m : Nat) (_ih : motive m) =>
    //   fun (_hpos : Nat.lt 0 (succ m)) =>
    //     Nat.succ_le_succ (div2 m + par m) m (Nat.div2_add_par_le m)
    //   (goal: Nat.lt (div2 (succ m)) (succ m)
    //          ≡ Nat.le (succ (div2 (succ m))) (succ m)
    //          ≡ Nat.le (succ (div2 m + par m)) (succ m), since
    //            div2 (succ m) ≡ div2 m + par m.)
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (m_id, m) = sb.fresh_local(c.nat_type.clone());

        // ih : motive m ≡ (Nat.lt 0 m → Nat.lt (div2 m) m)
        let ih_type = {
            let mut ib = EnvDeclBuilder::child_of(&sb);
            let hyp = c.lt(c.nat_zero.clone(), m.clone());
            let concl = c.lt(c.div2(m.clone()), m.clone());
            let (hh_id, _hh) = ib.fresh_local(hyp.clone());
            let imp = ib.mk_pi(hh_id, BinderInfo::Default, hyp, concl);
            ib.finish_child(imp)
        };
        let (ih_id, _ih) = sb.fresh_local(ih_type.clone());

        let succ_m = c.succ(m.clone());
        let hpos_type = c.lt(c.nat_zero.clone(), succ_m.clone());
        let (hpos_id, _hpos) = sb.fresh_local(hpos_type.clone());

        let dm_pm = c.add(c.div2(m.clone()), c.par(m.clone()));
        let invariant_m = Expr::app(
            Expr::const_(Name::from_string("Nat.div2_add_par_le"), vec![]),
            m.clone(),
        );
        let body = Expr::apps(c.succ_le_succ.clone(), [dm_pm, m.clone(), invariant_m]);

        let lam_hpos = sb.mk_lam(hpos_id, BinderInfo::Default, hpos_type, body);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, lam_hpos);
        let lam_m = sb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_m)
    };

    // value: fun (n : Nat) => @Nat.rec.{0} motive base step n
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_app = Expr::apps(nat_rec0, [motive, base, step, n]);
    let val = vb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    (type_, vb.finish(val))
}

impl Environment {
    /// Register `Nat.div2`, its helpers, and `Nat.div2_lt_self` as
    /// kernel-checked declarations (3 reducible Definitions + 2 constructive
    /// Theorems).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` (Nat, zero, succ, add, sub, rec),
    ///           `self.init_le()` (Nat.le), `self.init_prod()` (Prod, mk,
    ///           fst, snd), `self.init_true_false()` (False, False.elim).
    /// REQUIRES: the constructive order lemmas `Nat.le_refl`,
    ///           `Nat.succ_le_succ` (`init_nat_top_level_ordering`),
    ///           `Nat.le_trans` (`register_nat_le_trans_proof`),
    ///           `Nat.add_le_add_left`, `Nat.sub_le`
    ///           (`register_nat_arith_order_proofs`),
    ///           `Nat.not_succ_le_zero`
    ///           (`register_nat_not_succ_le_zero_theorem`).
    /// ENSURES: On success, `Nat.div2` / `Nat.div2Pair` / `Nat.div2Par` are
    ///          reducible Definitions and `Nat.div2_add_par_le` /
    ///          `Nat.div2_lt_self` are `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — re-invocation is a no-op once `Nat.div2_lt_self`
    ///          is present.
    pub(crate) fn register_nat_div2_lt_self_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): Clean-native Nat bitwise cluster (div2/testBit/bitwise
        // + par helpers) — the value-bearing definitions shadow the genuine
        // v4.31 bodies whose symbolic reduction the Mathlib.Data.Nat.Bitwise
        // lemma family needs (~20-decl Data cluster), and `Bool.xor` (which
        // this web references) is import-suppressed. Suppressed together; the
        // genuine olean declarations import through the checked path.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let final_name = Name::from_string("Nat.div2_lt_self");
        if self.get_const(&final_name).is_some() {
            return Ok(());
        }

        // Dependencies (each idempotent).
        self.init_nat()?;
        self.init_le()?;
        self.init_prod()?;
        self.init_true_false()?;
        self.init_nat_top_level_ordering()?; // Nat.succ_le_succ, Nat.le_refl
        self.register_nat_le_trans_proof()?; // Nat.le_trans
        self.register_nat_arith_order_proofs()?; // Nat.add_le_add_left, Nat.sub_le
        self.register_nat_not_succ_le_zero_theorem()?; // Nat.not_succ_le_zero

        let c = NatDiv2Consts::new();

        // 1. Nat.div2Pair : Nat → Prod Nat Nat (reducible Definition).
        if self.get_const(&Name::from_string("Nat.div2Pair")).is_none() {
            let (type_, value) = build_div2_pair(&c);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.div2Pair"),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        // 2. Nat.div2 : Nat → Nat (reducible Definition).
        if self.get_const(&Name::from_string("Nat.div2")).is_none() {
            let (type_, value) = build_div2(&c);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.div2"),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        // 3. Nat.div2Par : Nat → Nat (reducible Definition).
        if self.get_const(&Name::from_string("Nat.div2Par")).is_none() {
            let (type_, value) = build_div2_par(&c);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.div2Par"),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
        }

        // 4. Nat.div2_add_par_le : ∀ n, div2 n + par n ≤ n (load-bearing invariant).
        if self
            .get_const(&Name::from_string("Nat.div2_add_par_le"))
            .is_none()
        {
            let (type_, value) = build_invariant(&c);
            // SOUNDNESS: real kernel-checked single-step induction (Nat.rec.{0}).
            // No parity case-split: the step bounds (div2 m+par m)+(1-par m) by
            // monotonicity (Nat.add_le_add_left ∘ Nat.sub_le, then
            // Nat.succ_le_succ ∘ ih) chained with Nat.le_trans. All dependencies
            // are constructive Theorems; empty axiom closure.
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.div2_add_par_le"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // 5. Nat.div2_lt_self : ∀ n, 0 < n → div2 n < n (the WF-measure lemma).
        let (type_, value) = build_main(&c);
        // SOUNDNESS: real kernel-checked case analysis (Nat.rec.{0}). Zero case
        // discharged by False.elim ∘ Nat.not_succ_le_zero (0 < 0 is absurd);
        // succ case is Nat.succ_le_succ ∘ Nat.div2_add_par_le (div2 (succ m) ≡
        // div2 m + par m definitionally). No sorry, no self-reference, empty
        // axiom closure.
        self.add_decl(Declaration::Theorem {
            name: final_name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env_with_div2() -> Environment {
        let mut env = Environment::new();
        env.register_nat_div2_lt_self_proof()
            .expect("div2 registration");
        env
    }

    #[test]
    fn test_div2_registered_kinds() {
        let env = env_with_div2();
        for (name, kind) in [
            ("Nat.div2Pair", ConstantKind::Definition),
            ("Nat.div2", ConstantKind::Definition),
            ("Nat.div2Par", ConstantKind::Definition),
            ("Nat.div2_add_par_le", ConstantKind::Theorem),
            ("Nat.div2_lt_self", ConstantKind::Theorem),
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(info.kind, kind, "{name} kind mismatch");
            assert!(info.value.is_some(), "{name} must retain its value");
        }
    }

    #[test]
    fn test_div2_idempotent() {
        let mut env = env_with_div2();
        env.register_nat_div2_lt_self_proof()
            .expect("idempotent re-registration");
    }

    #[test]
    fn test_div2_lt_self_type_checks() {
        let env = env_with_div2();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Nat.div2_lt_self"), vec![]))
            .expect("Nat.div2_lt_self should type-check");
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("Nat.div2_add_par_le"),
                vec![],
            ))
            .expect("Nat.div2_add_par_le should type-check");
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Nat.div2"), vec![]))
            .expect("Nat.div2 should type-check");
    }

    /// `Nat.div2` actually computes the floor-halving on ground inputs.
    /// Builds `@Eq.refl Nat (div2 N)` and checks it against the stated type
    /// `Eq Nat (div2 N) M`, which forces the kernel to reduce `div2 N` to `M`.
    #[test]
    fn test_div2_ground_computations() {
        let mut env = env_with_div2();
        env.init_eq().expect("init_eq");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        let div2 = Expr::const_(Name::from_string("Nat.div2"), vec![]);

        // helper: build the Nat literal N as succ^N zero
        fn nat_lit(n: u64) -> Expr {
            let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            for _ in 0..n {
                e = Expr::app(succ.clone(), e.clone());
            }
            e
        }

        for (input, expected) in [(0u64, 0u64), (1, 0), (6, 3), (7, 3), (10, 5), (11, 5)] {
            let lhs = Expr::app(div2.clone(), nat_lit(input));
            let rhs = nat_lit(expected);
            // type: Eq Nat (div2 input) expected
            let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
            let stated = Expr::apps(eq_const, [nat.clone(), lhs.clone(), rhs.clone()]);
            // proof: @Eq.refl Nat (div2 input)  — type-checks iff div2 input ≡ expected
            let proof = Expr::apps(eq_refl.clone(), [nat.clone(), lhs]);
            let inferred = tc
                .infer_type(&proof)
                .unwrap_or_else(|e| panic!("div2 {input} refl should infer: {e:?}"));
            assert!(
                tc.is_def_eq(&inferred, &stated),
                "div2 {input} should equal {expected}"
            );
        }
    }

    #[test]
    fn test_div2_axiom_deps_empty() {
        let env = env_with_div2();
        for name in [
            "Nat.div2Pair",
            "Nat.div2",
            "Nat.div2Par",
            "Nat.div2_add_par_le",
            "Nat.div2_lt_self",
        ] {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered; axiom_deps should be Some"));
            let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                domain_deps.is_empty(),
                "{name} must have empty axiom closure, got {domain_deps:?}"
            );
        }
        assert_eq!(
            env.proof_quality(&Name::from_string("Nat.div2_lt_self"))
                .expect("proof quality should compute"),
            ProofQuality::Constructive
        );
    }
}
