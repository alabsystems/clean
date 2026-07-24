// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive proofs of the integer triangle inequalities:
//!
//! - `Int.abs_add_le : ∀ a b : Int,
//!      Int.le (Int.abs (Int.add a b)) (Int.add (Int.abs a) (Int.abs b))`
//! - `Int.dist_triangle : ∀ a b c : Int,
//!      Int.le (Int.dist a c) (Int.add (Int.dist a b) (Int.dist b c))`
//!
//! `Int.dist_triangle` replaces the prior `Declaration::Axiom` registration in
//! `algebra_dist.rs::init_int_dist`; `Int.abs_add_le` is a fresh constructive
//! building block.
//!
//! # Definitions in play
//!
//! ```text
//! Int.abs i    := Int.ofNat (Int.natAbs i)              -- reducible
//! Int.natAbs (ofNat n)   = n
//! Int.natAbs (negSucc n) = Nat.succ n
//! Int.le a b   := Int.NonNeg (Int.sub b a)              -- reducible
//! Int.sub a b  := Int.add a (Int.neg b)                 -- reducible
//! Int.dist a b := Int.abs (Int.sub a b)                 -- reducible
//! Int.add (ofNat m) (ofNat n)     ≡ ofNat (Nat.add m n)
//! Int.add (ofNat m) (negSucc n)   ≡ subNatNat m (succ n)
//! Int.add (negSucc m) (ofNat n)   ≡ subNatNat n (succ m)
//! Int.add (negSucc m) (negSucc n) ≡ negSucc (succ (Nat.add m n))
//! inductive Int.NonNeg : Int → Prop where | mk (n : Nat) : NonNeg (ofNat n)
//! inductive Nat.le (n : Nat) : Nat → Prop where
//!   | refl : Nat.le n n | step {m} : Nat.le n m → Nat.le n (succ m)
//! ```
//!
//! # Proof strategy
//!
//! The heart of `Int.abs_add_le` is a *natural-number* inequality
//! `Int.natAbs (Int.add a b) ≤ Int.natAbs a + Int.natAbs b`, after which both
//! sides of the goal are `Int.ofNat _` (LHS ≡ `ofNat (natAbs (a+b))`, RHS ≡
//! `ofNat (natAbs a + natAbs b)` because `add (ofNat m) (ofNat n) ≡
//! ofNat (m+n)`), and the `≤` on `ofNat`s is exactly the `Nat.le` lifted by
//! the helper `Int.le_ofNat_of_le`.
//!
//! Four supporting lemmas, each kernel-checked and constructive:
//!
//! 1. **`Int.le_ofNat_of_le : ∀ m n, Nat.le m n → Int.le (ofNat m) (ofNat n)`**
//!    by `@Nat.le.rec` on the witness (parameter `m`, index `n`), motive
//!    `fun t _ => Int.le (ofNat m) (ofNat t)` ≡ `NonNeg (subNatNat t m)`:
//!    - refl (`t = m`): transport `@Int.NonNeg.mk 0 : NonNeg (ofNat 0)` along
//!      `Eq.symm (Int.subNatNat_self m) : ofNat 0 = subNatNat m m`.
//!    - step (`ih : NonNeg (subNatNat k m)`): `subNatNat (succ k) m =
//!      add (subNatNat k m) (ofNat 1)` by
//!      `Eq.symm (Int.add_subNatNat_ofNat_succ k m 0)` (note
//!      `Nat.add k (succ 0) ≡ succ k`); transport
//!      `Int.NonNeg.add (subNatNat k m) (ofNat 1) ih (@Int.NonNeg.mk 1)`.
//!
//!    The recursor yields `NonNeg (subNatNat n m)`; a final `@Eq.subst.{1}`
//!    along `Int.subNatNat_eq_add n m` lands on the stated goal
//!    `Int.le (ofNat m) (ofNat n) ≡ NonNeg (add (ofNat n) (neg (ofNat m)))`
//!    (defeq to `NonNeg (add (ofNat n) (negOfNat m))`).
//!
//! 2. **`Int.natAbs_subNatNat_le : ∀ m k,
//!       Nat.le (Int.natAbs (Int.subNatNat m k)) (Nat.add m k)`** by `@Nat.rec`
//!    on `k` (subNatNat recurses on its second arg):
//!    - `k = 0`: `subNatNat m 0 ≡ ofNat m`, `natAbs ≡ m`, `m + 0 ≡ m`; closes by
//!      `Nat.le.refl m`.
//!    - `k = succ j`: case-split `subNatNat m j` via `@Int.rec` (carrying
//!      `ih : natAbs (subNatNat m j) ≤ m + j`). In all cases
//!      `natAbs (subNatNat m (succ j)) ≤ succ (natAbs (subNatNat m j))`, chained
//!      with `Nat.succ_le_succ ... ih` via `Nat.le_trans`.
//!
//! 3. **`Int.natAbs_add_le : ∀ a b,
//!       Nat.le (Int.natAbs (Int.add a b)) (Nat.add (Int.natAbs a) (Int.natAbs b))`**
//!    by `@Int.rec` on `a` then `b` (4 leaves), the two mixed-sign leaves bound
//!    by `Int.natAbs_subNatNat_le`.
//!
//! 4. **`Int.abs_add_le`** = `Int.le_ofNat_of_le (natAbs (a+b))
//!    (natAbs a + natAbs b) (Int.natAbs_add_le a b)`, whose type is defeq to the
//!    goal.
//!
//! `Int.dist_triangle` then transports `Int.abs_add_le (sub a b) (sub b c)`
//! along `Int.sub_add_sub_cancel c b a : (a-b)+(b-c) = a-c` (with motive
//! `fun x => Int.le (Int.abs x) (Int.add (Int.dist a b) (Int.dist b c))`).
//!
//! # Axiom closure
//!
//! Mentions only kernel machinery / constructors / reducible Definitions and
//! the constructive Theorems `Int.subNatNat_self`, `Int.subNatNat_eq_add`,
//! `Int.add_subNatNat_ofNat_succ`, `Int.NonNeg.add`, `Nat.le_trans`,
//! `Nat.succ_le_succ`, `Nat.add_comm`, `Nat.succ_add`,
//! `Int.sub_add_sub_cancel`. None is a `Declaration::Axiom`, so each registered
//! theorem has an empty domain-axiom closure (`ProofQuality::Constructive`).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across the proof terms.
struct AbsAddLeConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_rec_0: Expr,
    nat_le: Expr,
    nat_le_refl: Expr,
    nat_le_step: Expr,
    nat_le_rec: Expr,
    nat_le_trans: Expr,
    nat_succ_le_succ: Expr,
    nat_add_comm: Expr,
    nat_succ_add: Expr,
    int_abs: Expr,
    int_nat_abs: Expr,
    int_add: Expr,
    int_sub: Expr,
    int_dist: Expr,
    int_le: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_rec_0: Expr,
    int_sub_nat_nat: Expr,
    nonneg: Expr,
    nonneg_mk: Expr,
    nonneg_add: Expr,
    sub_nat_nat_self: Expr,
    sub_nat_nat_eq_add: Expr,
    add_sub_nat_nat_ofnat_succ: Expr,
    sub_add_sub_cancel: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
}

impl AbsAddLeConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            // Prop-valued Nat.rec motive — Sort 0.
            nat_rec_0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            nat_le_refl: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            nat_le_step: Expr::const_(Name::from_string("Nat.le.step"), vec![]),
            // Nat.le : Prop with Prop motive — no level params.
            nat_le_rec: Expr::const_(Name::from_string("Nat.le.rec"), vec![]),
            nat_le_trans: Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
            nat_succ_le_succ: Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
            nat_add_comm: Expr::const_(Name::from_string("Nat.add_comm"), vec![]),
            nat_succ_add: Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
            int_abs: Expr::const_(Name::from_string("Int.abs"), vec![]),
            int_nat_abs: Expr::const_(Name::from_string("Int.natAbs"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_dist: Expr::const_(Name::from_string("Int.dist"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            // Prop-valued Int.rec motive — Sort 0.
            int_rec_0: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            nonneg_mk: Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            nonneg_add: Expr::const_(Name::from_string("Int.NonNeg.add"), vec![]),
            sub_nat_nat_self: Expr::const_(Name::from_string("Int.subNatNat_self"), vec![]),
            sub_nat_nat_eq_add: Expr::const_(Name::from_string("Int.subNatNat_eq_add"), vec![]),
            add_sub_nat_nat_ofnat_succ: Expr::const_(
                Name::from_string("Int.add_subNatNat_ofNat_succ"),
                vec![],
            ),
            sub_add_sub_cancel: Expr::const_(Name::from_string("Int.sub_add_sub_cancel"), vec![]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1]),
        }
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }
    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }
    fn nsucc(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nadd(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [x, y])
    }
    fn nat_abs(&self, x: Expr) -> Expr {
        Expr::app(self.int_nat_abs.clone(), x)
    }
    fn abs(&self, x: Expr) -> Expr {
        Expr::app(self.int_abs.clone(), x)
    }
    fn iadd(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_add.clone(), [x, y])
    }
    fn isub(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_sub.clone(), [x, y])
    }
    fn snn(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.int_sub_nat_nat.clone(), [m, n])
    }
    fn nle(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [x, y])
    }
    fn ile(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [x, y])
    }
    fn nonneg_of(&self, x: Expr) -> Expr {
        Expr::app(self.nonneg.clone(), x)
    }
    /// `@Int.NonNeg.mk n : Int.NonNeg (Int.ofNat n)`.
    fn nonneg_mk(&self, n: Expr) -> Expr {
        Expr::app(self.nonneg_mk.clone(), n)
    }
    /// `@Nat.le.refl n : Nat.le n n`.
    fn nat_le_refl_app(&self, n: Expr) -> Expr {
        Expr::app(self.nat_le_refl.clone(), n)
    }
    /// `@Nat.le.step {x} {y} h : Nat.le x (succ y)`. The two index args are
    /// implicit; supply them positionally.
    fn nat_le_step(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.nat_le_step.clone(), [x, y, h])
    }
    /// `Nat.le_trans x y z hxy hyz : Nat.le x z`.
    fn nat_le_trans(&self, x: Expr, y: Expr, z: Expr, hxy: Expr, hyz: Expr) -> Expr {
        Expr::apps(self.nat_le_trans.clone(), [x, y, z, hxy, hyz])
    }
    /// `Nat.succ_le_succ x y h : Nat.le (succ x) (succ y)`.
    fn nat_succ_le_succ(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.nat_succ_le_succ.clone(), [x, y, h])
    }
    /// `@Eq.symm.{1} Int a b h : Eq Int b a`.
    fn symm_int(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), a, b, h])
    }
    /// `fun (x : Int) => Int.NonNeg x` (transport motive).
    fn nonneg_motive(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(self.int_type.clone());
        let body = self.nonneg_of(x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, self.int_type.clone(), body);
        mb.finish_child(lam)
    }
}

// ---------------------------------------------------------------------------
// Int.le_ofNat_of_le
// ---------------------------------------------------------------------------

/// `∀ m n : Nat, Nat.le m n → Int.le (Int.ofNat m) (Int.ofNat n)`.
fn build_le_ofnat_type(c: &AbsAddLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let h_type = c.nle(m.clone(), n.clone());
    let (h_id, _h) = b.fresh_local(h_type.clone());
    let concl = c.ile(c.of_nat(m.clone()), c.of_nat(n.clone()));
    let r = b.mk_pi(h_id, BinderInfo::Default, h_type, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), r);
    let r = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), r);
    b.finish(r)
}

/// Body — induction on `h : Nat.le m n` via `@Nat.le.rec` (parameter `m`).
fn build_le_ofnat_value(c: &AbsAddLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let h_type = c.nle(m.clone(), n.clone());
    let (h_id, h) = b.fresh_local(h_type.clone());

    // motive: fun (t : Nat) (_ : Nat.le m t) => Int.NonNeg (subNatNat t m)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nat_type.clone());
        let le_mt = c.nle(m.clone(), t.clone());
        let (ht_id, _ht) = mb.fresh_local(le_mt.clone());
        let body = c.nonneg_of(c.snn(t.clone(), m.clone()));
        let lam = mb.mk_lam(ht_id, BinderInfo::Default, le_mt, body);
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), lam);
        mb.finish_child(lam)
    };

    // refl_case : NonNeg (subNatNat m m)
    //   = Eq.subst (fun x => NonNeg x) (ofNat 0) (subNatNat m m)
    //              (Eq.symm (Int.subNatNat_self m)) (NonNeg.mk 0)
    let refl_case = {
        let snn_mm = c.snn(m.clone(), m.clone());
        let int_zero = c.of_nat(c.nat_zero.clone());
        // Int.subNatNat_self m : Eq Int (subNatNat m m) (ofNat 0)
        let self_eq = Expr::app(c.sub_nat_nat_self.clone(), m.clone());
        // symm : Eq Int (ofNat 0) (subNatNat m m)
        let symm = c.symm_int(snn_mm.clone(), int_zero.clone(), self_eq);
        let mk0 = c.nonneg_mk(c.nat_zero.clone());
        Expr::apps(
            c.eq_subst.clone(),
            [
                c.int_type.clone(),
                c.nonneg_motive(&b),
                int_zero,
                snn_mm,
                symm,
                mk0,
            ],
        )
    };

    // step_case : fun {k} (_ : Nat.le m k) (ih : NonNeg (subNatNat k m)) =>
    //   NonNeg (subNatNat (succ k) m)
    let step_case = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let le_mk = c.nle(m.clone(), k.clone());
        let (hk_id, _hk) = sb.fresh_local(le_mk.clone());
        let snn_km = c.snn(k.clone(), m.clone());
        let ih_type = c.nonneg_of(snn_km.clone());
        let (ih_id, ih) = sb.fresh_local(ih_type.clone());

        let one = c.nsucc(c.nat_zero.clone()); // Nat.succ Nat.zero ≡ 1
        let int_one = c.of_nat(one.clone());
        let add_snn_one = c.iadd(snn_km.clone(), int_one.clone());
        let snn_succ_k_m = c.snn(c.nsucc(k.clone()), m.clone());

        // Int.add_subNatNat_ofNat_succ k m 0
        //   : Eq Int (add (subNatNat k m) (ofNat (succ 0)))
        //            (subNatNat (Nat.add k (succ 0)) m)
        //   RHS ≡ subNatNat (succ k) m.
        let bridge = Expr::apps(
            c.add_sub_nat_nat_ofnat_succ.clone(),
            [k.clone(), m.clone(), c.nat_zero.clone()],
        );
        // witness : NonNeg (add (subNatNat k m) (ofNat 1))
        let mk1 = c.nonneg_mk(one.clone());
        let witness = Expr::apps(
            c.nonneg_add.clone(),
            [snn_km.clone(), int_one.clone(), ih.clone(), mk1],
        );
        // Eq.subst (fun x => NonNeg x) (add (subNatNat k m) (ofNat 1))
        //          (subNatNat (succ k) m) bridge witness
        let body = Expr::apps(
            c.eq_subst.clone(),
            [
                c.int_type.clone(),
                c.nonneg_motive(&sb),
                add_snn_one,
                snn_succ_k_m,
                bridge,
                witness,
            ],
        );
        let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
        let lam = sb.mk_lam(hk_id, BinderInfo::Default, le_mk, lam);
        let lam = sb.mk_lam(k_id, BinderInfo::Implicit, c.nat_type.clone(), lam);
        sb.finish_child(lam)
    };

    // rec_app : NonNeg (subNatNat n m)
    let rec_app = Expr::apps(
        c.nat_le_rec.clone(),
        [
            m.clone(),
            motive,
            refl_case,
            step_case,
            n.clone(),
            h.clone(),
        ],
    );

    // The declared conclusion `Int.le (ofNat m) (ofNat n)` delta-reduces to
    // `NonNeg (Int.add (ofNat n) (Int.neg (ofNat m)))`, which is defeq to
    // `NonNeg (Int.add (ofNat n) (Int.negOfNat m))` — the RHS of
    // `Int.subNatNat_eq_add n m : subNatNat n m = add (ofNat n) (negOfNat m)`.
    // Transport `rec_app` along that equation to land on the goal.
    let snn_nm = c.snn(n.clone(), m.clone());
    let int_neg = Expr::const_(Name::from_string("Int.neg"), vec![]);
    // add (ofNat n) (neg (ofNat m)) — written with Int.neg so it is literally
    // the delta-reduct of `Int.sub (ofNat n) (ofNat m)` (defeq to negOfNat m).
    let target = c.iadd(c.of_nat(n.clone()), Expr::app(int_neg, c.of_nat(m.clone())));
    // Int.subNatNat_eq_add n m : Eq Int (subNatNat n m) (add (ofNat n) (negOfNat m))
    let bridge = Expr::apps(c.sub_nat_nat_eq_add.clone(), [n.clone(), m.clone()]);
    let proof = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            c.nonneg_motive(&b),
            snn_nm,
            target,
            bridge,
            rec_app,
        ],
    );

    let val = b.mk_lam(h_id, BinderInfo::Default, h_type, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), val);
    let val = b.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val);
    b.finish(val)
}

// ---------------------------------------------------------------------------
// Int.natAbs_subNatNat_le
// ---------------------------------------------------------------------------

/// `∀ m k : Nat, Nat.le (Int.natAbs (Int.subNatNat m k)) (Nat.add m k)`.
fn build_natabs_snn_type(c: &AbsAddLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let concl = c.nle(
        c.nat_abs(c.snn(m.clone(), k.clone())),
        c.nadd(m.clone(), k.clone()),
    );
    let r = b.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let r = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), r);
    b.finish(r)
}

/// Body — `subNatNat` recurses on its 2nd argument, so induct on `k` via
/// `@Nat.rec`, motive `fun t => Nat.le (natAbs (subNatNat m t)) (m + t)`.
fn build_natabs_snn_value(c: &AbsAddLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (k_id, k) = b.fresh_local(c.nat_type.clone());

    // motive: fun (t : Nat) => Nat.le (natAbs (subNatNat m t)) (m + t)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nat_type.clone());
        let body = c.nle(
            c.nat_abs(c.snn(m.clone(), t.clone())),
            c.nadd(m.clone(), t.clone()),
        );
        let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // base (t = 0): subNatNat m 0 ≡ ofNat m, natAbs ≡ m, m + 0 ≡ m.
    let base = c.nat_le_refl_app(m.clone());

    // step: fun (j : Nat) (ih : Nat.le (natAbs (subNatNat m j)) (m + j)) => ...
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = sb.fresh_local(c.nat_type.clone());
        let snn_mj = c.snn(m.clone(), j.clone());
        let ih_type = c.nle(c.nat_abs(snn_mj.clone()), c.nadd(m.clone(), j.clone()));
        let (ih_id, ih) = sb.fresh_local(ih_type.clone());

        // Lemma over d : Int : Nat.le (natAbs (snn_step d)) (succ (natAbs d)),
        // by @Int.rec on d.  snn_step (subNatNat m j) ≡ subNatNat m (succ j).
        let d_motive = {
            let mut mb = EnvDeclBuilder::child_of(&sb);
            let (d_id, d) = mb.fresh_local(c.int_type.clone());
            let lhs = c.nat_abs(snn_step(c, &mb, d.clone()));
            let rhs = c.nsucc(c.nat_abs(d.clone()));
            let body = c.nle(lhs, rhs);
            let lam = mb.mk_lam(d_id, BinderInfo::Default, c.int_type.clone(), body);
            mb.finish_child(lam)
        };
        // ofNat case (inner @Nat.rec on p)
        let of_nat_case = {
            let mut ob = EnvDeclBuilder::child_of(&sb);
            let (p_id, p) = ob.fresh_local(c.nat_type.clone());
            // inner motive: fun (t : Nat) => Nat.le (natAbs (snn_step (ofNat t))) (succ t)
            let inner_motive = {
                let mut imb = EnvDeclBuilder::child_of(&ob);
                let (t_id, t) = imb.fresh_local(c.nat_type.clone());
                let lhs = c.nat_abs(snn_step(c, &imb, c.of_nat(t.clone())));
                let rhs = c.nsucc(t.clone());
                let body = c.nle(lhs, rhs);
                let lam = imb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
                imb.finish_child(lam)
            };
            // inner base (t=0): natAbs (snn_step (ofNat 0)) ≡ natAbs (negSucc 0) ≡ 1 ≡ succ 0.
            let inner_base = c.nat_le_refl_app(c.nsucc(c.nat_zero.clone()));
            // inner step (t = succ q): natAbs (snn_step (ofNat (succ q))) ≡ q.
            //   Goal Nat.le q (succ (succ q)).
            let inner_step = {
                let mut isb = EnvDeclBuilder::child_of(&ob);
                let (q_id, q) = isb.fresh_local(c.nat_type.clone());
                let inner_ih_type = c.nle(
                    c.nat_abs(snn_step(c, &isb, c.of_nat(q.clone()))),
                    c.nsucc(q.clone()),
                );
                let (iih_id, _iih) = isb.fresh_local(inner_ih_type.clone());
                let le_q_sq = c.nat_le_step(q.clone(), q.clone(), c.nat_le_refl_app(q.clone()));
                let body = c.nat_le_step(q.clone(), c.nsucc(q.clone()), le_q_sq);
                let lam = isb.mk_lam(iih_id, BinderInfo::Default, inner_ih_type, body);
                let lam = isb.mk_lam(q_id, BinderInfo::Default, c.nat_type.clone(), lam);
                isb.finish_child(lam)
            };
            let rec_app = Expr::apps(
                c.nat_rec_0.clone(),
                [inner_motive, inner_base, inner_step, p.clone()],
            );
            let lam = ob.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
            ob.finish_child(lam)
        };
        // negSucc case: natAbs (snn_step (negSucc p)) ≡ succ (succ p) ≡ succ (natAbs (negSucc p)).
        let neg_succ_case = {
            let mut nb = EnvDeclBuilder::child_of(&sb);
            let (p_id, p) = nb.fresh_local(c.nat_type.clone());
            let refl = c.nat_le_refl_app(c.nsucc(c.nsucc(p.clone())));
            let lam = nb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), refl);
            nb.finish_child(lam)
        };

        // d_bound : Nat.le (natAbs (subNatNat m (succ j))) (succ (natAbs (subNatNat m j)))
        let d_bound = Expr::apps(
            c.int_rec_0.clone(),
            [d_motive, of_nat_case, neg_succ_case, snn_mj.clone()],
        );

        // succ_ih : Nat.le (succ (natAbs (subNatNat m j))) (succ (m + j)) ≡ (m + succ j)
        let succ_ih = c.nat_succ_le_succ(
            c.nat_abs(snn_mj.clone()),
            c.nadd(m.clone(), j.clone()),
            ih.clone(),
        );

        let lhs = c.nat_abs(c.snn(m.clone(), c.nsucc(j.clone())));
        let mid = c.nsucc(c.nat_abs(snn_mj.clone()));
        let rhs = c.nadd(m.clone(), c.nsucc(j.clone()));
        let body = c.nat_le_trans(lhs, mid, rhs, d_bound, succ_ih);

        let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
        let lam = sb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), lam);
        sb.finish_child(lam)
    };

    let rec_app = Expr::apps(c.nat_rec_0.clone(), [motive, base, step, k.clone()]);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    let val = b.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val);
    b.finish(val)
}

/// The single `Nat.rec` step of `Int.subNatNat`, applied to `e : Int`. By
/// construction (matching `data_types_arithmetic.rs`),
/// `snn_step (subNatNat m j) ≡ subNatNat m (Nat.succ j)` definitionally.
///
/// ```text
/// snn_step e :=
///   @Int.rec.{1} (fun _ => Int)
///     (fun p => @Nat.rec.{1} (fun _ => Int) (negSucc 0) (fun q _ => ofNat q) p)
///     (fun p => negSucc (succ p))
///     e
/// ```
fn snn_step(c: &AbsAddLeConsts, parent: &EnvDeclBuilder, e: Expr) -> Expr {
    let int_rec_1 = Expr::const_(
        Name::from_string("Int.rec"),
        vec![Level::succ(Level::zero())],
    );
    let nat_rec_1 = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let int_motive = Expr::lam(BinderInfo::Default, c.int_type.clone(), c.int_type.clone());
    let of_case = {
        let mut ob = EnvDeclBuilder::child_of(parent);
        let (p_id, p) = ob.fresh_local(c.nat_type.clone());
        let snn_motive = Expr::lam(BinderInfo::Default, c.nat_type.clone(), c.int_type.clone());
        let zero_case = c.neg_succ(c.nat_zero.clone());
        let succ_case = {
            let mut qb = EnvDeclBuilder::child_of(&ob);
            let (q_id, q) = qb.fresh_local(c.nat_type.clone());
            let (ih_id, _ih) = qb.fresh_local(c.int_type.clone());
            let body = c.of_nat(q.clone());
            let lam = qb.mk_lam(ih_id, BinderInfo::Default, c.int_type.clone(), body);
            let lam = qb.mk_lam(q_id, BinderInfo::Default, c.nat_type.clone(), lam);
            qb.finish_child(lam)
        };
        let rec_app = Expr::apps(
            nat_rec_1.clone(),
            [snn_motive, zero_case, succ_case, p.clone()],
        );
        let lam = ob.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
        ob.finish_child(lam)
    };
    let neg_case = {
        let mut nb = EnvDeclBuilder::child_of(parent);
        let (p_id, p) = nb.fresh_local(c.nat_type.clone());
        let body = c.neg_succ(c.nsucc(p.clone()));
        let lam = nb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), body);
        nb.finish_child(lam)
    };
    Expr::apps(int_rec_1, [int_motive, of_case, neg_case, e])
}

// ---------------------------------------------------------------------------
// Int.natAbs_add_le
// ---------------------------------------------------------------------------

/// `∀ a b : Int,
///    Nat.le (Int.natAbs (Int.add a b)) (Nat.add (Int.natAbs a) (Int.natAbs b))`.
fn build_natabs_add_le_type(c: &AbsAddLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let concl = c.nle(
        c.nat_abs(c.iadd(a.clone(), bv.clone())),
        c.nadd(c.nat_abs(a.clone()), c.nat_abs(bv.clone())),
    );
    let r = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body — `@Int.rec` on `a` then on `b`, four constructor leaves.
fn build_natabs_add_le_value(c: &AbsAddLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());

    // outer motive: fun (x : Int) => Nat.le (natAbs (add x b)) (natAbs x + natAbs b)
    let outer_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = c.nle(
            c.nat_abs(c.iadd(x.clone(), bv.clone())),
            c.nadd(c.nat_abs(x.clone()), c.nat_abs(bv.clone())),
        );
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    // ofNat-a case: fun (m : Nat) => @Int.rec (inner motive) ... b
    let of_nat_a_case = {
        let mut ob = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = ob.fresh_local(c.nat_type.clone());
        let a_on = c.of_nat(m.clone());

        let inner_motive = {
            let mut mb = EnvDeclBuilder::child_of(&ob);
            let (y_id, y) = mb.fresh_local(c.int_type.clone());
            let body = c.nle(
                c.nat_abs(c.iadd(a_on.clone(), y.clone())),
                c.nadd(c.nat_abs(a_on.clone()), c.nat_abs(y.clone())),
            );
            let lam = mb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), body);
            mb.finish_child(lam)
        };

        // ofNat/ofNat: Nat.le.refl (m + n)
        let oo = {
            let mut nb = EnvDeclBuilder::child_of(&ob);
            let (n_id, n) = nb.fresh_local(c.nat_type.clone());
            let refl = c.nat_le_refl_app(c.nadd(m.clone(), n.clone()));
            let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), refl);
            nb.finish_child(lam)
        };
        // ofNat/negSucc: bound Int.natAbs_subNatNat_le m (succ n)
        let on = {
            let mut nb = EnvDeclBuilder::child_of(&ob);
            let (n_id, n) = nb.fresh_local(c.nat_type.clone());
            let body = Expr::apps(natabs_snn_le_const(), [m.clone(), c.nsucc(n.clone())]);
            let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
            nb.finish_child(lam)
        };
        let rec_app = Expr::apps(c.int_rec_0.clone(), [inner_motive, oo, on, bv.clone()]);
        let lam = ob.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
        ob.finish_child(lam)
    };

    // negSucc-a case: fun (m : Nat) => @Int.rec (inner motive) ... b
    let neg_succ_a_case = {
        let mut ob = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = ob.fresh_local(c.nat_type.clone());
        let a_ns = c.neg_succ(m.clone());

        let inner_motive = {
            let mut mb = EnvDeclBuilder::child_of(&ob);
            let (y_id, y) = mb.fresh_local(c.int_type.clone());
            let body = c.nle(
                c.nat_abs(c.iadd(a_ns.clone(), y.clone())),
                c.nadd(c.nat_abs(a_ns.clone()), c.nat_abs(y.clone())),
            );
            let lam = mb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), body);
            mb.finish_child(lam)
        };

        // negSucc/ofNat: add (negSucc m) (ofNat n) ≡ subNatNat n (succ m).
        //   RHS ≡ succ m + n. bound: Int.natAbs_subNatNat_le n (succ m) gives
        //   Nat.le (natAbs (subNatNat n (succ m))) (n + succ m); transport RHS
        //   via Nat.add_comm n (succ m) using Eq.subst.
        let no = {
            let mut nb = EnvDeclBuilder::child_of(&ob);
            let (n_id, n) = nb.fresh_local(c.nat_type.clone());
            let bound = Expr::apps(natabs_snn_le_const(), [n.clone(), c.nsucc(m.clone())]);
            let comm = Expr::apps(c.nat_add_comm.clone(), [n.clone(), c.nsucc(m.clone())]);
            let eq_subst_nat = Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            );
            let lhs_fixed = c.nat_abs(c.snn(n.clone(), c.nsucc(m.clone())));
            let motive_w = {
                let mut wb = EnvDeclBuilder::child_of(&nb);
                let (w_id, w) = wb.fresh_local(c.nat_type.clone());
                let body = c.nle(lhs_fixed.clone(), w.clone());
                let lam = wb.mk_lam(w_id, BinderInfo::Default, c.nat_type.clone(), body);
                wb.finish_child(lam)
            };
            let body = Expr::apps(
                eq_subst_nat,
                [
                    c.nat_type.clone(),
                    motive_w,
                    c.nadd(n.clone(), c.nsucc(m.clone())),
                    c.nadd(c.nsucc(m.clone()), n.clone()),
                    comm,
                    bound,
                ],
            );
            let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
            nb.finish_child(lam)
        };
        // negSucc/negSucc: add (negSucc m) (negSucc n) ≡ negSucc (succ (m+n)),
        //   natAbs ≡ succ (succ (m+n)). RHS natAbs (negSucc m) + natAbs (negSucc n)
        //   ≡ succ m + succ n ≡ succ (Nat.add (succ m) n) (add recurses on 2nd arg).
        //   By Nat.succ_add m n : Nat.add (succ m) n = succ (m+n), the RHS equals
        //   succ (succ (m+n)) = LHS. We close with Nat.le.refl (succ (succ (m+n)))
        //   and transport the RHS via Eq.subst along (symm (succ_add m n)).
        let nn = {
            let mut nb = EnvDeclBuilder::child_of(&ob);
            let (n_id, n) = nb.fresh_local(c.nat_type.clone());
            let ssmn = c.nsucc(c.nsucc(c.nadd(m.clone(), n.clone()))); // succ (succ (m+n))
                                                                       // refl : Nat.le ssmn ssmn
            let refl = c.nat_le_refl_app(ssmn.clone());
            // Nat.succ_add m n : Eq Nat (Nat.add (succ m) n) (succ (m+n))
            let succ_add = Expr::apps(c.nat_succ_add.clone(), [m.clone(), n.clone()]);
            // symm : Eq Nat (succ (m+n)) (Nat.add (succ m) n)
            let eq_symm_nat = Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            );
            let succ_mn = c.nsucc(c.nadd(m.clone(), n.clone()));
            let add_sm_n = c.nadd(c.nsucc(m.clone()), n.clone());
            let symm = Expr::apps(
                eq_symm_nat,
                [
                    c.nat_type.clone(),
                    add_sm_n.clone(),
                    succ_mn.clone(),
                    succ_add,
                ],
            );
            // motive: fun (w : Nat) => Nat.le ssmn (succ w)
            let motive_w = {
                let mut wb = EnvDeclBuilder::child_of(&nb);
                let (w_id, w) = wb.fresh_local(c.nat_type.clone());
                let body = c.nle(ssmn.clone(), c.nsucc(w.clone()));
                let lam = wb.mk_lam(w_id, BinderInfo::Default, c.nat_type.clone(), body);
                wb.finish_child(lam)
            };
            // Eq.subst motive (succ (m+n)) (Nat.add (succ m) n) symm refl
            //   : Nat.le ssmn (succ (Nat.add (succ m) n)) ≡ Nat.le ssmn (succ m + succ n)
            let eq_subst_nat = Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            );
            let body = Expr::apps(
                eq_subst_nat,
                [c.nat_type.clone(), motive_w, succ_mn, add_sm_n, symm, refl],
            );
            let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
            nb.finish_child(lam)
        };
        let rec_app = Expr::apps(c.int_rec_0.clone(), [inner_motive, no, nn, bv.clone()]);
        let lam = ob.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
        ob.finish_child(lam)
    };

    let rec_app = Expr::apps(
        c.int_rec_0.clone(),
        [outer_motive, of_nat_a_case, neg_succ_a_case, a.clone()],
    );
    let val = b.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

/// `Int.natAbs_subNatNat_le` constant.
fn natabs_snn_le_const() -> Expr {
    Expr::const_(Name::from_string("Int.natAbs_subNatNat_le"), vec![])
}

// ---------------------------------------------------------------------------
// Int.abs_add_le
// ---------------------------------------------------------------------------

/// `∀ a b : Int,
///    Int.le (Int.abs (Int.add a b)) (Int.add (Int.abs a) (Int.abs b))`.
fn build_abs_add_le_type(c: &AbsAddLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let concl = c.ile(
        c.abs(c.iadd(a.clone(), bv.clone())),
        c.iadd(c.abs(a.clone()), c.abs(bv.clone())),
    );
    let r = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b : Int) =>
///   Int.le_ofNat_of_le (natAbs (add a b)) (natAbs a + natAbs b)
///                      (Int.natAbs_add_le a b)
/// ```
fn build_abs_add_le_value(c: &AbsAddLeConsts) -> Expr {
    let le_ofnat = Expr::const_(Name::from_string("Int.le_ofNat_of_le"), vec![]);
    let natabs_add_le = Expr::const_(Name::from_string("Int.natAbs_add_le"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());

    let x = c.nat_abs(c.iadd(a.clone(), bv.clone())); // natAbs (a+b)
    let y = c.nadd(c.nat_abs(a.clone()), c.nat_abs(bv.clone())); // natAbs a + natAbs b
    let h = Expr::apps(natabs_add_le, [a.clone(), bv.clone()]);
    let body = Expr::apps(le_ofnat, [x, y, h]);

    let val = b.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), body);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

// ---------------------------------------------------------------------------
// Int.dist_triangle
// ---------------------------------------------------------------------------

/// `∀ a b c : Int,
///    Int.le (Int.dist a c) (Int.add (Int.dist a b) (Int.dist b c))`.
fn build_dist_triangle_type(c: &AbsAddLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let (cv_id, cv) = b.fresh_local(c.int_type.clone());
    let dist = |x: Expr, y: Expr| Expr::apps(c.int_dist.clone(), [x, y]);
    let lhs = dist(a.clone(), cv.clone());
    let rhs = c.iadd(dist(a.clone(), bv.clone()), dist(bv.clone(), cv.clone()));
    let concl = c.ile(lhs, rhs);
    let r = b.mk_pi(cv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b c : Int) =>
///   @Eq.subst.{1} Int
///     (fun (x : Int) => Int.le (Int.abs x) (Int.add (Int.dist a b) (Int.dist b c)))
///     (Int.add (Int.sub a b) (Int.sub b c)) (Int.sub a c)
///     (Int.sub_add_sub_cancel c b a)
///     (Int.abs_add_le (Int.sub a b) (Int.sub b c))
/// ```
fn build_dist_triangle_value(c: &AbsAddLeConsts) -> Expr {
    let abs_add_le = Expr::const_(Name::from_string("Int.abs_add_le"), vec![]);
    let sub_add_sub_cancel = c.sub_add_sub_cancel.clone();

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let (cv_id, cv) = b.fresh_local(c.int_type.clone());

    let s1 = c.isub(a.clone(), bv.clone()); // a - b
    let s2 = c.isub(bv.clone(), cv.clone()); // b - c
    let s3 = c.isub(a.clone(), cv.clone()); // a - c
    let add_s1_s2 = c.iadd(s1.clone(), s2.clone());

    // dist a b / dist b c — keep as Int.dist so the result type literally
    // matches the stated goal RHS.
    let dist_ab = Expr::apps(c.int_dist.clone(), [a.clone(), bv.clone()]);
    let dist_bc = Expr::apps(c.int_dist.clone(), [bv.clone(), cv.clone()]);
    let rhs_fixed = c.iadd(dist_ab, dist_bc);

    // motive: fun (x : Int) => Int.le (Int.abs x) rhs_fixed
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = c.ile(c.abs(x.clone()), rhs_fixed.clone());
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    // Int.abs_add_le s1 s2 : Int.le (abs (add s1 s2)) (add (abs s1) (abs s2))
    //   ≡ motive (add s1 s2).
    let base = Expr::apps(abs_add_le, [s1.clone(), s2.clone()]);

    // Int.sub_add_sub_cancel c b a : Eq Int (add (sub a b) (sub b c)) (sub a c).
    let cancel = Expr::apps(sub_add_sub_cancel, [cv.clone(), bv.clone(), a.clone()]);

    let body = Expr::apps(
        c.eq_subst.clone(),
        [c.int_type.clone(), motive, add_s1_s2, s3, cancel, base],
    );

    let val = b.mk_lam(cv_id, BinderInfo::Default, c.int_type.clone(), body);
    let val = b.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.dist` as a reducible `Declaration::Definition`
    /// `λ a b => Int.abs (Int.sub a b)` if not already present (shared with the
    /// `Int.dist_comm` module).
    fn ensure_int_dist_def_local(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Int.dist");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = AbsAddLeConsts::new();
        let dist_type = Expr::pi(
            BinderInfo::Default,
            c.int_type.clone(),
            Expr::pi(BinderInfo::Default, c.int_type.clone(), c.int_type.clone()),
        );
        let dist_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.int_type.clone());
            let (bv_id, bv) = b.fresh_local(c.int_type.clone());
            let body = c.abs(c.isub(a.clone(), bv.clone()));
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: dist_type,
            value: dist_value,
            is_reducible: true,
        })
    }

    /// Register the integer triangle inequalities `Int.abs_add_le` and
    /// `Int.dist_triangle` (and their supporting lemmas `Int.le_ofNat_of_le`,
    /// `Int.natAbs_subNatNat_le`, `Int.natAbs_add_le`) as kernel-checked
    /// `Declaration::Theorem`s in a standalone environment.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid `Environment`.
    /// ENSURES: On success, `Int.abs_add_le` and `Int.dist_triangle` are both
    ///          `Declaration::Theorem`s with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — each target is guarded by `get_const`.
    pub(crate) fn register_int_abs_add_le(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // Dependencies.
        self.init_int_sign_abs()?; // Int.abs, Int.natAbs, Int.ofNat, Int.negSucc, Int.rec
        self.init_int_arith()?; // Int.add, Int.sub, Int.subNatNat
        self.init_int_ord()?; // Int.le, Int.NonNeg(.mk/.rec)
        self.init_nat()?; // Nat, Nat.zero, Nat.succ, Nat.add, Nat.rec
        self.init_le()?; // Nat.le, Nat.le.refl/.step/.rec
        self.init_eq()?; // Eq, Eq.refl, Eq.symm, Eq.subst
        self.ensure_int_dist_def_local()?; // Int.dist (reducible)

        // Constructive helper Theorems.
        self.register_int_sub_nat_nat_self_proof()?;
        self.register_int_sub_nat_nat_eq_add_proof()?;
        self.register_int_add_sub_nat_nat_ofnat_succ_proof()?;
        self.register_int_nonneg_add_proof()?;
        self.register_nat_arith_order_proofs()?; // Nat.le_trans, Nat.succ_le_succ
        self.register_nat_add_comm_proof()?;
        self.register_nat_succ_add_proof()?;
        self.register_int_sub_add_sub_cancel_proof()?;

        let c = AbsAddLeConsts::new();

        // Int.le_ofNat_of_le
        let name = Name::from_string("Int.le_ofNat_of_le");
        if self.get_const(&name).is_none() {
            let type_ = build_le_ofnat_type(&c);
            let value = build_le_ofnat_value(&c);
            // SOUNDNESS: Real kernel-checked proof term. `@Nat.le.rec` on the
            // witness lifts `Nat.le m n` to `Int.NonNeg (subNatNat n m)`: refl
            // transports `@Int.NonNeg.mk 0` across `Int.subNatNat_self`; step
            // transports `Int.NonNeg.add (subNatNat k m) (ofNat 1) ih (NonNeg.mk 1)`
            // across `Int.add_subNatNat_ofNat_succ k m 0`. A final `@Eq.subst.{1}`
            // along `Int.subNatNat_eq_add n m` lands on the goal `Int.le (ofNat m)
            // (ofNat n)` (defeq to `NonNeg (add (ofNat n) (neg (ofNat m)))`). No
            // `sorry`, no domain axiom.
            self.add_decl(Declaration::Theorem {
                name,
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // Int.natAbs_subNatNat_le
        let name = Name::from_string("Int.natAbs_subNatNat_le");
        if self.get_const(&name).is_none() {
            let type_ = build_natabs_snn_type(&c);
            let value = build_natabs_snn_value(&c);
            // SOUNDNESS: Real kernel-checked proof term. `@Nat.rec` on the second
            // `subNatNat` argument; the successor step case-splits `subNatNat m j`
            // via `@Int.rec` to bound `natAbs (subNatNat m (succ j))` by
            // `succ (natAbs (subNatNat m j))`, then chains with the inductive
            // hypothesis through `Nat.succ_le_succ` / `Nat.le_trans`. No `sorry`,
            // no domain axiom.
            self.add_decl(Declaration::Theorem {
                name,
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // Int.natAbs_add_le
        let name = Name::from_string("Int.natAbs_add_le");
        if self.get_const(&name).is_none() {
            let type_ = build_natabs_add_le_type(&c);
            let value = build_natabs_add_le_value(&c);
            // SOUNDNESS: Real kernel-checked proof term. `@Int.rec` on `a` then
            // `b` (4 leaves). Same-sign leaves close by `Nat.le.refl` (the
            // negSucc/negSucc leaf transports through `Nat.succ_add`); mixed-sign
            // leaves reduce `Int.add` to `Int.subNatNat` and bound `natAbs` by the
            // constructive `Int.natAbs_subNatNat_le` (commuting the bound with
            // `Nat.add_comm` in the `negSucc/ofNat` leaf). No `sorry`, no domain
            // axiom.
            self.add_decl(Declaration::Theorem {
                name,
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // Int.abs_add_le
        let name = Name::from_string("Int.abs_add_le");
        if self.get_const(&name).is_none() {
            let type_ = build_abs_add_le_type(&c);
            let value = build_abs_add_le_value(&c);
            // SOUNDNESS: Real kernel-checked proof term. Both sides of the goal
            // reduce to `Int.ofNat _` (`abs i ≡ ofNat (natAbs i)`,
            // `add (ofNat m) (ofNat n) ≡ ofNat (m+n)`), so the `Int.le` on
            // `ofNat`s is exactly `Int.le_ofNat_of_le` applied to the
            // natural-number bound `Int.natAbs_add_le a b`. No `sorry`, no domain
            // axiom.
            self.add_decl(Declaration::Theorem {
                name,
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // Int.dist_triangle
        let name = Name::from_string("Int.dist_triangle");
        if self.get_const(&name).is_none() {
            let type_ = build_dist_triangle_type(&c);
            let value = build_dist_triangle_value(&c);
            // SOUNDNESS: Real kernel-checked proof term. `Int.dist x y ≡
            // Int.abs (Int.sub x y)` (reducible), so the goal is
            // `Int.le (abs (sub a c)) (add (abs (sub a b)) (abs (sub b c)))`.
            // Transport `Int.abs_add_le (sub a b) (sub b c)` along
            // `Int.sub_add_sub_cancel c b a : (a-b)+(b-c) = a-c` via `@Eq.subst.{1}`
            // (motive `fun x => Int.le (abs x) RHS`). No `sorry`, no domain axiom.
            // Replaces the prior `Declaration::Axiom` in
            // `algebra_dist.rs::init_int_dist`.
            self.add_decl(Declaration::Theorem {
                name,
                level_params: vec![],
                type_,
                value,
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    fn registered_env() -> Environment {
        let mut env = Environment::new();
        env.register_int_abs_add_le()
            .expect("register_int_abs_add_le should succeed");
        env
    }

    fn assert_constructive_theorem(env: &Environment, name: &str) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} must be a kernel-checked Theorem, got {:?}",
            info.kind
        );
        assert!(info.value.is_some(), "{name} Theorem must retain its value");

        // Kernel re-checks the proof term against its canonical type.
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![]))
            .unwrap_or_else(|err| panic!("{name} should kernel-type-check, got {err:?}"));

        let q = env
            .proof_quality(&Name::from_string(name))
            .expect("proof_quality should be reported");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "{name} must be Constructive (empty domain-axiom closure), got {q:?}"
        );
    }

    #[test]
    fn test_int_le_ofnat_of_le_is_constructive_theorem() {
        assert_constructive_theorem(&registered_env(), "Int.le_ofNat_of_le");
    }

    #[test]
    fn test_int_natabs_subnatnat_le_is_constructive_theorem() {
        assert_constructive_theorem(&registered_env(), "Int.natAbs_subNatNat_le");
    }

    #[test]
    fn test_int_natabs_add_le_is_constructive_theorem() {
        assert_constructive_theorem(&registered_env(), "Int.natAbs_add_le");
    }

    #[test]
    fn test_int_abs_add_le_is_constructive_theorem() {
        assert_constructive_theorem(&registered_env(), "Int.abs_add_le");
    }

    #[test]
    fn test_int_dist_triangle_is_constructive_theorem() {
        assert_constructive_theorem(&registered_env(), "Int.dist_triangle");
    }

    #[test]
    fn test_register_int_abs_add_le_idempotent() {
        let mut env = Environment::new();
        env.register_int_abs_add_le().expect("first registration");
        env.register_int_abs_add_le()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.dist_triangle"))
            .expect("Int.dist_triangle should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_abs_add_le_axiom_deps_empty() {
        let env = registered_env();
        for name in ["Int.abs_add_le", "Int.dist_triangle"] {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered, axiom_deps should return Some"));
            let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                domain_deps.is_empty(),
                "{name} must have empty axiom closure, got {domain_deps:?}"
            );
        }
    }
}
