// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.abs_mul : ∀ a b : Int,
//!    Eq Int (Int.abs (Int.mul a b)) (Int.mul (Int.abs a) (Int.abs b))`.
//!
//! Replaces the prior `Declaration::Axiom` registration of `Int.abs_mul` in
//! `algebra_abs_int.rs::init_int_abs_props` with a kernel-checked
//! `Declaration::Theorem`.
//!
//! # Definitions in play
//!
//! ```text
//! Int.abs i        := Int.ofNat (Int.natAbs i)                  -- reducible
//! Int.natAbs (Int.ofNat n)   ≡ n
//! Int.natAbs (Int.negSucc n) ≡ Nat.succ n
//! Int.negOfNat (Nat.zero)    ≡ Int.ofNat Nat.zero
//! Int.negOfNat (Nat.succ k)  ≡ Int.negSucc k
//! Int.mul (ofNat m)   (ofNat n)   ≡ Int.ofNat   (Nat.mul m n)
//! Int.mul (ofNat m)   (negSucc n) ≡ Int.negOfNat (Nat.mul m (Nat.succ n))
//! Int.mul (negSucc m) (ofNat n)   ≡ Int.negOfNat (Nat.mul (Nat.succ m) n)
//! Int.mul (negSucc m) (negSucc n) ≡ Int.ofNat   (Nat.mul (Nat.succ m) (Nat.succ n))
//! ```
//!
//! Both sides of `Int.abs_mul` are `Int.ofNat _`. The right-hand side
//! `Int.mul (Int.abs a) (Int.abs b)` ≡ `Int.mul (ofNat (natAbs a)) (ofNat
//! (natAbs b))` ≡ `Int.ofNat (Nat.mul (natAbs a) (natAbs b))` (ofNat × ofNat
//! case of `Int.mul`). So the goal reduces to a `Nat`-level statement under
//! `Int.ofNat`.
//!
//! # Helper: `Int.natAbs_negOfNat`
//!
//! `Int.natAbs_negOfNat : ∀ k : Nat, Eq Nat (Int.natAbs (Int.negOfNat k)) k`,
//! proven by `@Nat.rec.{0}` on `k`:
//! - `k = Nat.zero`: `natAbs (negOfNat 0) ≡ natAbs (ofNat 0) ≡ 0`, so the goal
//!   `Eq Nat 0 0` is `@Eq.refl.{1} Nat Nat.zero`.
//! - `k = Nat.succ j`: `natAbs (negOfNat (succ j)) ≡ natAbs (negSucc j) ≡
//!   succ j`, so the goal `Eq Nat (succ j) (succ j)` is
//!   `@Eq.refl.{1} Nat (Nat.succ j)` (the inductive hypothesis is unused).
//!
//! # Proof of `Int.abs_mul`
//!
//! Outer `@Int.rec.{0}` on `a`, inner `@Int.rec.{0}` on `b`, four leaves:
//!
//! * `ofNat m`, `ofNat n`: LHS ≡ `ofNat (natAbs (ofNat (Nat.mul m n))) ≡
//!   ofNat (Nat.mul m n)`; RHS ≡ `ofNat (Nat.mul m n)`. Close by
//!   `@Eq.refl.{1} Int (ofNat (Nat.mul m n))`.
//! * `ofNat m`, `negSucc n`: LHS ≡ `ofNat (natAbs (negOfNat (Nat.mul m
//!   (succ n))))`; RHS ≡ `ofNat (Nat.mul m (succ n))`. Close by
//!   `@congrArg.{1,1} Nat Int (natAbs (negOfNat K)) K Int.ofNat
//!   (Int.natAbs_negOfNat K)` with `K := Nat.mul m (Nat.succ n)`.
//! * `negSucc m`, `ofNat n`: LHS ≡ `ofNat (natAbs (negOfNat (Nat.mul
//!   (succ m) n)))`; RHS ≡ `ofNat (Nat.mul (succ m) n)`. Close by the same
//!   `congrArg` with `K := Nat.mul (Nat.succ m) n`.
//! * `negSucc m`, `negSucc n`: LHS ≡ `ofNat (natAbs (ofNat (Nat.mul (succ m)
//!   (succ n)))) ≡ ofNat (Nat.mul (succ m) (succ n))`; RHS ≡ `ofNat (Nat.mul
//!   (succ m) (succ n))`. Close by `@Eq.refl.{1} Int (ofNat (Nat.mul (succ m)
//!   (succ n)))`.
//!
//! # Axiom closure
//!
//! Mentions only `Int`, `Int.abs`, `Int.natAbs`, `Int.mul`, `Int.ofNat`,
//! `Int.negSucc`, `Int.negOfNat`, `Int.rec`, `Nat`, `Nat.mul`, `Nat.zero`,
//! `Nat.succ`, `Nat.rec`, the constructive helper `Int.natAbs_negOfNat`, and
//! the foundational `Eq` / `Eq.refl` / `congrArg`. None is a
//! `Declaration::Axiom`, so the domain-axiom closure of each registered
//! theorem is empty (`ProofQuality::Constructive`).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across the helper and the main proof.
struct IntAbsMulConsts {
    int_type: Expr,
    nat_type: Expr,
    int_abs: Expr,
    int_nat_abs: Expr,
    int_mul: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_neg_of_nat: Expr,
    nat_mul: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_rec: Expr,
    nat_rec: Expr,
    eq_const_nat: Expr,
    eq_refl_nat: Expr,
    eq_refl_int: Expr,
    congr_arg: Expr,
    nat_abs_neg_of_nat: Expr,
}

impl IntAbsMulConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            int_abs: Expr::const_(Name::from_string("Int.abs"), vec![]),
            int_nat_abs: Expr::const_(Name::from_string("Int.natAbs"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_neg_of_nat: Expr::const_(Name::from_string("Int.negOfNat"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            // Prop-valued motives — Sort 0.
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            // Eq lives in Type 1 (Nat, Int : Type 0 = Sort 1).
            eq_const_nat: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl_nat: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_refl_int: Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
            // congrArg.{1,1} : {α β : Type} {a₁ a₂ : α} (f : α → β) → a₁ = a₂ → f a₁ = f a₂
            congr_arg: Expr::const_(
                Name::from_string("congrArg"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            ),
            nat_abs_neg_of_nat: Expr::const_(Name::from_string("Int.natAbs_negOfNat"), vec![]),
        }
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn neg_of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_of_nat.clone(), n)
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn abs(&self, x: Expr) -> Expr {
        Expr::app(self.int_abs.clone(), x)
    }

    fn nat_abs(&self, x: Expr) -> Expr {
        Expr::app(self.int_nat_abs.clone(), x)
    }

    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_mul.clone(), [x, y])
    }

    fn nat_mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [x, y])
    }

    /// `Eq Nat lhs rhs`.
    fn eq_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const_nat.clone(), [self.nat_type.clone(), lhs, rhs])
    }

    /// `Eq Int lhs rhs`.
    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const_nat.clone(), [self.int_type.clone(), lhs, rhs])
    }

    /// `@Eq.refl.{1} Int v`.
    fn refl_int(&self, v: Expr) -> Expr {
        Expr::apps(self.eq_refl_int.clone(), [self.int_type.clone(), v])
    }

    /// `@Eq.refl.{1} Nat v`.
    fn refl_nat(&self, v: Expr) -> Expr {
        Expr::apps(self.eq_refl_nat.clone(), [self.nat_type.clone(), v])
    }

    /// `@congrArg.{1,1} Nat Int (natAbs (negOfNat k)) k Int.ofNat
    ///    (Int.natAbs_negOfNat k)`
    ///   : `Eq Int (ofNat (natAbs (negOfNat k))) (ofNat k)`.
    fn congr_of_nat_natabs(&self, k: Expr) -> Expr {
        let lemma = Expr::app(self.nat_abs_neg_of_nat.clone(), k.clone());
        Expr::apps(
            self.congr_arg.clone(),
            [
                self.nat_type.clone(),
                self.int_type.clone(),
                self.nat_abs(self.neg_of_nat(k.clone())),
                k,
                self.int_of_nat.clone(),
                lemma,
            ],
        )
    }
}

// ---------------------------------------------------------------------------
// Helper: Int.natAbs_negOfNat
// ---------------------------------------------------------------------------

/// `∀ k : Nat, Eq Nat (Int.natAbs (Int.negOfNat k)) k`.
fn build_natabs_negofnat_type(c: &IntAbsMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat_type.clone());
    let concl = c.eq_nat(c.nat_abs(c.neg_of_nat(k.clone())), k.clone());
    let r = b.mk_pi(k_id, BinderInfo::Default, c.nat_type.clone(), concl);
    b.finish(r)
}

/// ```text
/// λ (k : Nat) =>
///   @Nat.rec.{0}
///     (fun (j : Nat) => Eq Nat (Int.natAbs (Int.negOfNat j)) j)
///     (@Eq.refl.{1} Nat Nat.zero)
///     (fun (j : Nat) (_ih : ...) => @Eq.refl.{1} Nat (Nat.succ j))
///     k
/// ```
fn build_natabs_negofnat_value(c: &IntAbsMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat_type.clone());

    // motive: fun (j : Nat) => Eq Nat (natAbs (negOfNat j)) j
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_nat(c.nat_abs(c.neg_of_nat(j.clone())), j.clone());
        let lam = mb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // zero case: @Eq.refl.{1} Nat Nat.zero
    //   natAbs (negOfNat 0) ≡ natAbs (ofNat 0) ≡ 0.
    let zero_case = c.refl_nat(c.nat_zero.clone());

    // succ case: fun (j : Nat) (_ih : motive j) => @Eq.refl.{1} Nat (Nat.succ j)
    //   natAbs (negOfNat (succ j)) ≡ natAbs (negSucc j) ≡ succ j.
    let succ_case = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = sb.fresh_local(c.nat_type.clone());
        let ih_type = c.eq_nat(c.nat_abs(c.neg_of_nat(j.clone())), j.clone());
        let (ih_id, _ih) = sb.fresh_local(ih_type.clone());
        let body = c.refl_nat(c.succ(j.clone()));
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
        let lam_j = sb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_j)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, zero_case, succ_case, k.clone()]);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    b.finish(val)
}

// ---------------------------------------------------------------------------
// Int.abs_mul
// ---------------------------------------------------------------------------

/// `∀ a b : Int, Eq Int (Int.abs (Int.mul a b)) (Int.mul (Int.abs a) (Int.abs b))`.
fn build_abs_mul_type(c: &IntAbsMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let lhs = c.abs(c.mul(a.clone(), bv.clone()));
    let rhs = c.mul(c.abs(a.clone()), c.abs(bv.clone()));
    let concl = c.eq_int(lhs, rhs);
    let r = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Outer motive `fun (x : Int) => Eq Int (abs (mul x b)) (mul (abs x) (abs b))`
/// for the outer `Int.rec` on `a`, with `b` a fixed parent local.
fn build_outer_motive(c: &IntAbsMulConsts, parent: &EnvDeclBuilder, bv: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = mb.fresh_local(c.int_type.clone());
    let lhs = c.abs(c.mul(x.clone(), bv.clone()));
    let rhs = c.mul(c.abs(x.clone()), c.abs(bv.clone()));
    let body = c.eq_int(lhs, rhs);
    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// Inner motive `fun (y : Int) => Eq Int (abs (mul a' y)) (mul (abs a') (abs y))`
/// for the inner `Int.rec` on `b`, with `a'` the constructor form of `a`.
fn build_inner_motive(c: &IntAbsMulConsts, parent: &EnvDeclBuilder, a_ctor: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (y_id, y) = mb.fresh_local(c.int_type.clone());
    let lhs = c.abs(c.mul(a_ctor.clone(), y.clone()));
    let rhs = c.mul(c.abs(a_ctor.clone()), c.abs(y.clone()));
    let body = c.eq_int(lhs, rhs);
    let lam = mb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// The `a = ofNat m` branch: an inner `@Int.rec.{0}` on `b`.
///
/// ```text
/// λ (m : Nat) =>
///   @Int.rec.{0} inner_motive[ofNat m]
///     (fun (n : Nat) => @Eq.refl.{1} Int (ofNat (Nat.mul m n)))
///     (fun (n : Nat) => congrArg ofNat (Int.natAbs_negOfNat (Nat.mul m (succ n))))
///     b
/// ```
fn build_ofnat_branch(c: &IntAbsMulConsts, parent: &EnvDeclBuilder, bv: &Expr) -> Expr {
    let mut ob = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = ob.fresh_local(c.nat_type.clone());
    let a_ctor = c.of_nat(m.clone());

    let inner_motive = build_inner_motive(c, &ob, &a_ctor);

    // b = ofNat n: LHS ≡ ofNat (natAbs (ofNat (Nat.mul m n))) ≡ ofNat (Nat.mul m n);
    //              RHS ≡ ofNat (Nat.mul m n). Close by refl.
    let oo = {
        let mut ib = EnvDeclBuilder::child_of(&ob);
        let (n_id, n) = ib.fresh_local(c.nat_type.clone());
        let body = c.refl_int(c.of_nat(c.nat_mul(m.clone(), n.clone())));
        let lam = ib.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
        ib.finish_child(lam)
    };

    // b = negSucc n: LHS ≡ ofNat (natAbs (negOfNat (Nat.mul m (succ n))));
    //               RHS ≡ ofNat (Nat.mul m (succ n)). Close by congrArg + lemma.
    let on = {
        let mut ib = EnvDeclBuilder::child_of(&ob);
        let (n_id, n) = ib.fresh_local(c.nat_type.clone());
        let k = c.nat_mul(m.clone(), c.succ(n.clone()));
        let body = c.congr_of_nat_natabs(k);
        let lam = ib.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
        ib.finish_child(lam)
    };

    let rec_app = Expr::apps(c.int_rec.clone(), [inner_motive, oo, on, bv.clone()]);
    let lam = ob.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    ob.finish_child(lam)
}

/// The `a = negSucc m` branch: an inner `@Int.rec.{0}` on `b`.
///
/// ```text
/// λ (m : Nat) =>
///   @Int.rec.{0} inner_motive[negSucc m]
///     (fun (n : Nat) => congrArg ofNat (Int.natAbs_negOfNat (Nat.mul (succ m) n)))
///     (fun (n : Nat) => @Eq.refl.{1} Int (ofNat (Nat.mul (succ m) (succ n))))
///     b
/// ```
fn build_negsucc_branch(c: &IntAbsMulConsts, parent: &EnvDeclBuilder, bv: &Expr) -> Expr {
    let mut nb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = nb.fresh_local(c.nat_type.clone());
    let a_ctor = c.neg_succ(m.clone());
    let succ_m = c.succ(m.clone());

    let inner_motive = build_inner_motive(c, &nb, &a_ctor);

    // b = ofNat n: LHS ≡ ofNat (natAbs (negOfNat (Nat.mul (succ m) n)));
    //             RHS ≡ ofNat (Nat.mul (succ m) n). Close by congrArg + lemma.
    let no = {
        let mut ib = EnvDeclBuilder::child_of(&nb);
        let (n_id, n) = ib.fresh_local(c.nat_type.clone());
        let k = c.nat_mul(succ_m.clone(), n.clone());
        let body = c.congr_of_nat_natabs(k);
        let lam = ib.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
        ib.finish_child(lam)
    };

    // b = negSucc n: LHS ≡ ofNat (natAbs (ofNat (Nat.mul (succ m) (succ n)))) ≡
    //               ofNat (Nat.mul (succ m) (succ n)); RHS ≡ same. Close by refl.
    let nn = {
        let mut ib = EnvDeclBuilder::child_of(&nb);
        let (n_id, n) = ib.fresh_local(c.nat_type.clone());
        let prod = c.nat_mul(succ_m.clone(), c.succ(n.clone()));
        let body = c.refl_int(c.of_nat(prod));
        let lam = ib.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
        ib.finish_child(lam)
    };

    let rec_app = Expr::apps(c.int_rec.clone(), [inner_motive, no, nn, bv.clone()]);
    let lam = nb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    nb.finish_child(lam)
}

/// Body:
/// ```text
/// λ (a b : Int) =>
///   @Int.rec.{0} outer_motive ofnat_branch negsucc_branch a
/// ```
fn build_abs_mul_value(c: &IntAbsMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());

    let outer_motive = build_outer_motive(c, &b, &bv);
    let ofnat_branch = build_ofnat_branch(c, &b, &bv);
    let negsucc_branch = build_negsucc_branch(c, &b, &bv);

    let rec_app = Expr::apps(
        c.int_rec.clone(),
        [outer_motive, ofnat_branch, negsucc_branch, a.clone()],
    );

    let val = b.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register the constructive helper
    /// `Int.natAbs_negOfNat : ∀ k : Nat, Eq Nat (Int.natAbs (Int.negOfNat k)) k`
    /// as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_sign_abs()` has registered `Int.natAbs`,
    ///           `Int.negOfNat`, `Int.ofNat`, `Int.negSucc`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Int.natAbs_negOfNat` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_natabs_negofnat_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.natAbs_negOfNat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_sign_abs()?; // Int.natAbs, Int.negOfNat, Int.ofNat, Int.negSucc
        self.init_nat()?;
        self.init_eq()?;

        let c = IntAbsMulConsts::new();
        let type_ = build_natabs_negofnat_type(&c);
        let value = build_natabs_negofnat_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. `@Nat.rec.{0}` on `k`:
        // the zero minor is `@Eq.refl.{1} Nat Nat.zero` because
        // `Int.natAbs (Int.negOfNat 0) ≡ Int.natAbs (Int.ofNat 0) ≡ 0`; the
        // succ minor is `@Eq.refl.{1} Nat (Nat.succ j)` because
        // `Int.natAbs (Int.negOfNat (Nat.succ j)) ≡ Int.natAbs (Int.negSucc j)
        // ≡ Nat.succ j` (iota on `Nat.rec`/`Int.rec` + delta on the reducible
        // `Int.negOfNat`/`Int.natAbs`). No `sorry`, no self-reference, no
        // domain-axiom dependency.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Register `Int.abs_mul` as a kernel-checked `Declaration::Theorem`.
    ///
    /// `∀ a b : Int, Eq Int (Int.abs (Int.mul a b)) (Int.mul (Int.abs a) (Int.abs b))`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_sign_abs()` has registered `Int.abs`,
    ///           `Int.natAbs`, `Int.ofNat`, `Int.negSucc`, `Int.rec`.
    /// REQUIRES: `self.init_int_arith()` has registered `Int.mul`,
    ///           `Int.negOfNat`, `Nat.mul`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `congrArg`.
    /// ENSURES: On success, `Int.abs_mul` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.abs_mul` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_abs_mul_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.abs_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_sign_abs()?; // Int.abs, Int.natAbs, Int.rec
        self.init_int_arith()?; // Int.mul, Int.negOfNat, Nat.mul, Int.ofNat, Int.negSucc
        self.init_nat()?;
        self.init_eq()?;
        // Constructive dependency.
        self.register_int_natabs_negofnat_proof()?;

        let c = IntAbsMulConsts::new();
        let type_ = build_abs_mul_type(&c);
        let value = build_abs_mul_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Both sides are
        // `Int.ofNat _`; the RHS `Int.mul (Int.abs a) (Int.abs b)` reduces to
        // `Int.ofNat (Nat.mul (Int.natAbs a) (Int.natAbs b))` (ofNat × ofNat
        // case of the reducible `Int.mul`). An outer `@Int.rec.{0}` on `a` and
        // inner `@Int.rec.{0}` on `b` split into four leaves: the
        // ofNat/ofNat and negSucc/negSucc leaves close by `@Eq.refl.{1} Int
        // (Int.ofNat (Nat.mul _ _))` (the product is `Int.ofNat _` so
        // `Int.natAbs` strips it back); the ofNat/negSucc and negSucc/ofNat
        // leaves — where `Int.mul` reduces to `Int.negOfNat K` — close by
        // `@congrArg.{1,1} Nat Int Int.ofNat (Int.natAbs_negOfNat K)`, which
        // transports `Int.natAbs (Int.negOfNat K) = K` under `Int.ofNat`. No
        // `sorry`, no self-reference, no domain-axiom dependency. Replaces the
        // prior `Declaration::Axiom` in
        // `algebra_abs_int.rs::init_int_abs_props`.
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
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    fn registered_env() -> Environment {
        let mut env = Environment::new();
        env.register_int_abs_mul_proof()
            .expect("register_int_abs_mul_proof should succeed");
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
        assert!(
            info.value.is_some(),
            "{name} Theorem must retain its proof value"
        );

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
            "{name} must be Constructive (no domain axiom in closure), got {q:?}"
        );
    }

    #[test]
    fn test_int_natabs_negofnat_is_constructive_theorem() {
        let env = registered_env();
        assert_constructive_theorem(&env, "Int.natAbs_negOfNat");
    }

    #[test]
    fn test_int_abs_mul_is_constructive_theorem() {
        let env = registered_env();
        assert_constructive_theorem(&env, "Int.abs_mul");
    }

    #[test]
    fn test_int_abs_mul_kernel_type_checks() {
        let env = registered_env();
        let info = env
            .get_const(&Name::from_string("Int.abs_mul"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let tc = TypeChecker::new(&env);
        let inferred = tc
            .infer_type(value)
            .expect("proof term must type-check in the kernel");
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "inferred type must match the declared Int.abs_mul type"
        );
    }

    #[test]
    fn test_int_abs_mul_proof_uses_int_rec() {
        use crate::expr::ExprKind;
        let env = registered_env();
        let info = env
            .get_const(&Name::from_string("Int.abs_mul"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel the two outer λ binders, then the head must be Int.rec.
        let mut body: Expr = value.clone();
        for _ in 0..2 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected outer λ, got {:?}", k),
            };
        }
        let mut head: Expr = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Int.rec",
                "Int.abs_mul proof root must be Int.rec"
            ),
            k => panic!("expected Const(Int.rec), got {:?}", k),
        }
    }

    #[test]
    fn test_int_abs_mul_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_abs_mul_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.abs_mul"))
            .expect("Int.abs_mul is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.abs_mul must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_abs_mul_idempotent() {
        let mut env = Environment::new();
        env.register_int_abs_mul_proof()
            .expect("first registration");
        env.register_int_abs_mul_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.abs_mul"))
            .expect("Int.abs_mul should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }
}
