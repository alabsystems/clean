// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.abs_neg : ∀ a : Int, Eq Int (Int.abs (Int.neg a)) (Int.abs a)`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `algebra_abs_int.rs::init_int_abs_props` with a `Declaration::Theorem`
//! whose proof term is built by an outer `@Int.rec.{0}` case-analysis on
//! `a`, with the `ofNat` branch performing an inner `@Nat.rec.{0}`
//! case-analysis on the underlying `Nat`.
//!
//! # Reducible definitions in play
//!
//! ```text
//! Int.abs i           = Int.ofNat (Int.natAbs i)      -- reducible
//! Int.natAbs (ofNat n)   = n                          -- iota on Int.rec
//! Int.natAbs (negSucc n) = Nat.succ n                 -- iota on Int.rec
//! Int.neg (ofNat n)   = Nat.rec (ofNat 0) (λ m _ => negSucc m) n
//! Int.neg (negSucc n) = ofNat (Nat.succ n)            -- reducible
//! ```
//!
//! so concretely
//!
//! ```text
//! Int.neg (ofNat 0)        = ofNat 0
//! Int.neg (ofNat (succ m)) = negSucc m
//! Int.neg (negSucc n)      = ofNat (succ n)
//! ```
//!
//! # Proof sketch
//!
//! The outer `@Int.rec.{0}` on `a` (motive
//! `λ x => Eq Int (Int.abs (Int.neg x)) (Int.abs x)`) splits into:
//!
//! - `negSucc n`: `Int.abs (Int.neg (negSucc n))` reduces via
//!   `Int.neg (negSucc n) = ofNat (succ n)` and
//!   `Int.abs (ofNat (succ n)) = ofNat (natAbs (ofNat (succ n))) = ofNat (succ n)`.
//!   The RHS `Int.abs (negSucc n) = ofNat (natAbs (negSucc n)) = ofNat (succ n)`.
//!   Both sides ≡ `ofNat (succ n)`, so the branch closes by
//!   `@Eq.refl.{1} Int (ofNat (succ n))`.
//!
//! - `ofNat n`: `Int.neg (ofNat n)` does **not** reduce without knowing
//!   whether `n` is `zero` or `succ`, so we recurse on `n` with an inner
//!   `@Nat.rec.{0}` whose motive is
//!   `λ k => Eq Int (Int.abs (Int.neg (ofNat k))) (Int.abs (ofNat k))`:
//!   - `zero`: `Int.abs (Int.neg (ofNat 0)) = Int.abs (ofNat 0) = ofNat 0`
//!     and RHS `Int.abs (ofNat 0) = ofNat 0`. Closed by
//!     `@Eq.refl.{1} Int (ofNat 0)`.
//!   - `succ m`: `Int.neg (ofNat (succ m)) = negSucc m`, then
//!     `Int.abs (negSucc m) = ofNat (succ m)`, and RHS
//!     `Int.abs (ofNat (succ m)) = ofNat (succ m)`. Closed by
//!     `@Eq.refl.{1} Int (ofNat (succ m))` (the inductive hypothesis is
//!     unused).
//!
//! The proof has the outer shape
//!
//! ```text
//! λ a : Int => @Int.rec.{0} outer_motive
//!   (λ n : Nat => @Nat.rec.{0} inner_motive
//!       (@Eq.refl.{1} Int (ofNat 0))
//!       (λ m : Nat => λ _ih => @Eq.refl.{1} Int (ofNat (succ m)))
//!       n)
//!   (λ n : Nat => @Eq.refl.{1} Int (ofNat (succ n)))
//!   a
//! ```
//!
//! against `∀ a : Int, @Eq.{1} Int (Int.abs (Int.neg a)) (Int.abs a)`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.abs`, `Int.natAbs`, `Int.neg`,
//! `Int.ofNat`, `Int.negSucc`, `Int.rec`, `Nat`, `Nat.zero`, `Nat.succ`,
//! `Nat.rec`, `Eq`, `Eq.refl` — none of which are `Declaration::Axiom`
//! (`Int.rec` / `Nat.rec` are kernel machinery; `Int.abs` / `Int.natAbs` /
//! `Int.neg` are reducible Definitions; the rest are constructors /
//! inductive machinery). Therefore `env.axiom_deps("Int.abs_neg")` is empty
//! and `env.proof_quality("Int.abs_neg") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntAbsNegConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_abs: Expr,
    int_neg: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_rec: Expr,
    nat_rec: Expr,
    eq_const: Expr,
    eq_refl: Expr,
}

impl IntAbsNegConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            int_abs: Expr::const_(Name::from_string("Int.abs"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            // Prop-valued motives — Sort 0.
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
        }
    }

    fn abs(&self, x: Expr) -> Expr {
        Expr::app(self.int_abs.clone(), x)
    }

    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    /// `Int.abs (Int.neg x)`.
    fn abs_neg(&self, x: Expr) -> Expr {
        self.abs(self.neg(x))
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn refl_int(&self, t: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int_type.clone(), t])
    }
}

/// Build `∀ a : Int, Eq Int (Int.abs (Int.neg a)) (Int.abs a)`.
fn build_type(c: &IntAbsNegConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let concl = c.eq_int(c.abs_neg(a.clone()), c.abs(a));
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(ty_raw)
}

/// Outer motive: `λ (x : Int) => Eq Int (Int.abs (Int.neg x)) (Int.abs x)`.
fn build_outer_motive(c: &IntAbsNegConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = mb.fresh_local(c.int_type.clone());
    let body = c.eq_int(c.abs_neg(x.clone()), c.abs(x));
    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// Outer `ofNat` case:
/// `λ (n : Nat) => @Nat.rec.{0} inner_motive zero_case succ_case n`.
fn build_ofnat_case(c: &IntAbsNegConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut ob = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = ob.fresh_local(c.nat_type.clone());

    // inner motive: λ (k : Nat) => Eq Int (abs (neg (ofNat k))) (abs (ofNat k))
    let inner_motive = {
        let mut mb = EnvDeclBuilder::child_of(&ob);
        let (k_id, k) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_int(c.abs_neg(c.of_nat(k.clone())), c.abs(c.of_nat(k)));
        let lam = mb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // zero case: @Eq.refl.{1} Int (ofNat 0)
    let zero_case = c.refl_int(c.of_nat(c.nat_zero.clone()));

    // succ case: λ (m : Nat) => λ (_ih : inner_motive m) =>
    //   @Eq.refl.{1} Int (ofNat (succ m))
    let succ_case = {
        let mut sb = EnvDeclBuilder::child_of(&ob);
        let (m_id, m) = sb.fresh_local(c.nat_type.clone());
        let ih_type = c.eq_int(c.abs_neg(c.of_nat(m.clone())), c.abs(c.of_nat(m.clone())));
        let (ih_id, _ih) = sb.fresh_local(ih_type.clone());
        let refl = c.refl_int(c.of_nat(c.succ(m.clone())));
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, refl);
        let lam_m = sb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_m)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [inner_motive, zero_case, succ_case, n]);
    let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    ob.finish_child(lam)
}

/// Outer `negSucc` case: `λ (n : Nat) => @Eq.refl.{1} Int (ofNat (succ n))`.
///
/// `Int.abs (Int.neg (negSucc n)) ≡ Int.abs (ofNat (succ n)) ≡ ofNat (succ n)`
/// and `Int.abs (negSucc n) ≡ ofNat (succ n)`, so the motive at `negSucc n`,
/// `Eq Int (abs (neg (negSucc n))) (abs (negSucc n))`, is closed by reflexivity
/// at `ofNat (succ n)`.
fn build_negsucc_case(c: &IntAbsNegConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut nb = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = nb.fresh_local(c.nat_type.clone());
    let refl = c.refl_int(c.of_nat(c.succ(n)));
    let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), refl);
    nb.finish_child(lam)
}

/// Body: `λ (a : Int) => @Int.rec.{0} outer_motive ofNat_case negSucc_case a`.
fn build_value(c: &IntAbsNegConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (va_id, va) = vb.fresh_local(c.int_type.clone());
    let motive = build_outer_motive(c, &vb);
    let of_nat_case = build_ofnat_case(c, &vb);
    let neg_succ_case = build_negsucc_case(c, &vb);
    let rec_app = Expr::apps(c.int_rec.clone(), [motive, of_nat_case, neg_succ_case, va]);
    let val_raw = vb.mk_lam(va_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.abs_neg` as a kernel-checked `Declaration::Theorem`.
    ///
    /// `∀ a : Int, Eq Int (Int.abs (Int.neg a)) (Int.abs a)`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_sign_abs()` has registered `Int.abs`,
    ///           `Int.natAbs`, `Int.ofNat`, `Int.negSucc`, `Int.neg`,
    ///           `Int.rec`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Int.abs_neg` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.abs_neg` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_abs_neg_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.abs_neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_sign_abs()?; // Provides Int.abs, Int.natAbs, Int.neg, Int.rec.
        self.init_nat()?;
        self.init_eq()?;

        let c = IntAbsNegConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Outer `@Int.rec.{0}`
        // case-analysis on `a`; the `negSucc` branch closes by pure
        // `@Eq.refl.{1} Int (ofNat (succ n))` and the `ofNat` branch by an
        // inner `@Nat.rec.{0}` on the underlying `Nat` (both branches pure
        // `@Eq.refl.{1}`, the inductive hypothesis unused). The kernel reduces
        // `Int.abs (Int.neg ·)` and `Int.abs ·` to the same `Int.ofNat _` on
        // each constructor by iota on `Int.rec` / `Nat.rec` + delta on the
        // reducible `Int.abs` / `Int.natAbs` / `Int.neg` definitions. No
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
    use crate::env::axiom_audit::ProofQuality;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    /// Kernel accepts the nested `Int.rec` / `Nat.rec` / `Eq.refl` proof
    /// term. Verifies the theorem is registered as a Theorem (not Axiom),
    /// retains its proof value, and idempotent re-invocation is a no-op.
    #[test]
    fn test_int_abs_neg_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_abs_neg_proof()
            .expect("first registration");
        env.register_int_abs_neg_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.abs_neg"))
            .expect("Int.abs_neg should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof term type-checks against its declared type in the kernel.
    #[test]
    fn test_int_abs_neg_kernel_type_checks() {
        let mut env = Environment::new();
        env.register_int_abs_neg_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.abs_neg"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let tc = TypeChecker::new(&env);
        let inferred = tc
            .infer_type(value)
            .expect("proof term must type-check in the kernel");
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "inferred type must match the declared Int.abs_neg type"
        );
    }

    /// The proof is not a trivial axiom reference — it is a `λ`
    /// abstraction whose root is `@Int.rec`. Guards against the
    /// axiom-wrapping masquerade.
    #[test]
    fn test_int_abs_neg_proof_uses_int_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_abs_neg_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.abs_neg"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let outer_body = match value.kind() {
            ExprKind::Lam(_, _, body) => body.clone(),
            k => panic!("expected outer λ, got {:?}", k),
        };
        let mut head = outer_body;
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Int.rec",
                "Int.abs_neg proof root must be Int.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Int.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty and the proof is classified Constructive.
    #[test]
    fn test_int_abs_neg_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_int_abs_neg_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.abs_neg"))
            .expect("Int.abs_neg is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.abs_neg must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
        let quality = env
            .proof_quality(&Name::from_string("Int.abs_neg"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.abs_neg must be Constructive, got {:?}",
            quality
        );
    }
}
