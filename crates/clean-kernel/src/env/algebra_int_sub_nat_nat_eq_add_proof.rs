// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.subNatNat_eq_add : ∀ m n : Nat,
//!     Eq Int (Int.subNatNat m n) (Int.add (Int.ofNat m) (Int.negOfNat n))`.
//!
//! This is a foundational normalization lemma that re-expresses the
//! mixed-sign `Int.subNatNat m n` (`m - n` clamped into `Int`) as the
//! `Int.add` of the positive part `Int.ofNat m` and the negative part
//! `Int.negOfNat n` (`= -n`). It is a stepping stone toward a constructive
//! `Int.left_distrib` / `Int.right_distrib`: the mixed-sign `Int.add b c`
//! branches normalize to `Int.subNatNat`, and rewriting them back into an
//! explicit `ofNat + negOfNat` sum is the bridge that lets the
//! multiplication distribute over an honest two-term `Int.add`.
//!
//! # Proof sketch
//!
//! `Int.negOfNat`, `Int.add`, `Int.subNatNat` are reducible Definitions:
//!
//! ```text
//! Int.negOfNat 0           = Int.ofNat 0
//! Int.negOfNat (succ k)    = Int.negSucc k
//!
//! Int.add (ofNat m) (ofNat n)   = Int.ofNat (Nat.add m n)
//! Int.add (ofNat m) (negSucc n) = Int.subNatNat m (Nat.succ n)
//!
//! Int.subNatNat m 0 = Int.ofNat m
//! ```
//!
//! Induct on `n` via `@Nat.rec.{0}` (motive holds `m` fixed, varies the
//! second `Nat`); the inductive hypothesis is unused (case-analysis, not
//! genuine recursion):
//!
//! Case `n = Nat.zero`. LHS `Int.subNatNat m Nat.zero ι→ Int.ofNat m`. RHS
//! `Int.add (Int.ofNat m) (Int.negOfNat Nat.zero)` reduces via
//! `Int.negOfNat Nat.zero ι→ Int.ofNat Nat.zero` then
//! `Int.add (Int.ofNat m) (Int.ofNat Nat.zero) ι→ Int.ofNat (Nat.add m Nat.zero)`.
//! So the goal is `Eq (Int.ofNat m) (Int.ofNat (Nat.add m Nat.zero))`,
//! discharged by `congrArg Int.ofNat` applied to the symmetric constructive
//! `Nat.add_zero m : Eq (Nat.add m Nat.zero) m`.
//!
//! Case `n = Nat.succ k`. LHS `Int.subNatNat m (Nat.succ k)` does NOT reduce
//! further (the `Nat.rec` underlying `Int.subNatNat` is stuck on the
//! `Int.rec` of the predecessor result). RHS
//! `Int.add (Int.ofNat m) (Int.negOfNat (Nat.succ k))` reduces via
//! `Int.negOfNat (Nat.succ k) ι→ Int.negSucc k` then
//! `Int.add (Int.ofNat m) (Int.negSucc k) ι→ Int.subNatNat m (Nat.succ k)`.
//! Both sides are definitionally `Int.subNatNat m (Nat.succ k)`, so the case
//! closes by `@Eq.refl.{1} Int (Int.subNatNat m (Nat.succ k))`.
//!
//! # Axiom closure
//!
//! The proof term mentions only kernel machinery / constructors / reducible
//! Definitions (`Int`, `Int.add`, `Int.ofNat`, `Int.negOfNat`,
//! `Int.subNatNat`, `Nat`, `Nat.zero`, `Nat.succ`, `Nat.add`, `Nat.rec`,
//! `Eq`, `Eq.refl`, `Eq.symm`, `congrArg`) and the constructive
//! `Declaration::Theorem` `Nat.add_zero` (#3551). None are
//! `Declaration::Axiom`, so `env.axiom_deps("Int.subNatNat_eq_add")` is
//! empty and the proof quality is `ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_neg_sub_nat_nat_proof.rs` (Int.neg_subNatNat).
//! - `algebra_int_sub_nat_nat_zero_right_proof.rs` (subNatNat m 0 = ofNat m).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntSubNatNatEqAddConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_rec: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_neg_of_nat: Expr,
    int_sub_nat_nat: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    nat_add_zero: Expr,
}

impl IntSubNatNatEqAddConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_of_nat: Expr::const_(Name::from_string("Int.negOfNat"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            // congrArg.{1,1}
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_add_zero: Expr::const_(Name::from_string("Nat.add_zero"), vec![]),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_of_nat.clone(), n)
    }

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn nadd(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), x), y)
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

    fn symm_nat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.nat_type.clone(), a, b, h])
    }

    /// `congrArg Nat Int x y Int.ofNat h : Eq Int (ofNat x) (ofNat y)`.
    fn congr_arg_of_nat(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [
                self.nat_type.clone(),
                self.int_type.clone(),
                x,
                y,
                self.int_of_nat.clone(),
                h,
            ],
        )
    }
}

/// Build
/// `∀ m n : Nat, Eq Int (Int.subNatNat m n) (Int.add (Int.ofNat m) (Int.negOfNat n))`.
fn build_type(c: &IntSubNatNatEqAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let lhs = c.sub_nat_nat(m.clone(), n.clone());
    let rhs = c.add(c.of_nat(m), c.neg_of_nat(n));
    let concl = c.eq_int(lhs, rhs);
    let ty_raw = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Inner motive (for fixed `m`):
/// `λ (t : Nat) => Eq Int (Int.subNatNat m t) (Int.add (Int.ofNat m) (Int.negOfNat t))`.
fn build_motive(c: &IntSubNatNatEqAddConsts, parent: &EnvDeclBuilder, m: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let lhs = c.sub_nat_nat(m.clone(), t.clone());
    let rhs = c.add(c.of_nat(m.clone()), c.neg_of_nat(t));
    let body = c.eq_int(lhs, rhs);
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam)
}

/// Body: `λ (m n : Nat) => @Nat.rec.{0} motive base step n`.
fn build_value(c: &IntSubNatNatEqAddConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (m_id, m) = vb.fresh_local(c.nat_type.clone());
    let (n_id, n) = vb.fresh_local(c.nat_type.clone());

    let motive = build_motive(c, &vb, &m);

    // Base (n = 0): goal `Eq (ofNat m) (ofNat (Nat.add m 0))`.
    // h := Nat.add_zero m : Eq (Nat.add m 0) m
    // symm h : Eq m (Nat.add m 0)
    // congrArg ofNat (symm h) : Eq (ofNat m) (ofNat (Nat.add m 0))
    let base = {
        let add_m_zero = c.nadd(m.clone(), c.nat_zero.clone());
        let h = Expr::app(c.nat_add_zero.clone(), m.clone());
        let h_symm = c.symm_nat(add_m_zero.clone(), m.clone(), h);
        c.congr_arg_of_nat(m.clone(), add_m_zero, h_symm)
    };

    // Step (n = succ k): both sides reduce to `subNatNat m (succ k)`,
    // closed by Eq.refl. The IH is unused.
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let ih_ty = {
            let lhs = c.sub_nat_nat(m.clone(), k.clone());
            let rhs = c.add(c.of_nat(m.clone()), c.neg_of_nat(k.clone()));
            c.eq_int(lhs, rhs)
        };
        let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
        let refl = c.refl_int(c.sub_nat_nat(m.clone(), c.succ(k.clone())));
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, refl);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_k)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    let val_raw = vb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    let val_raw = vb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.subNatNat_eq_add` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.negOfNat`, `Int.add`, `Int.subNatNat`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `Eq.symm`,
    ///           `congrArg`.
    /// REQUIRES: `Nat.add_zero` is registered as a constructive
    ///           `Declaration::Theorem`.
    /// ENSURES: On success, `Int.subNatNat_eq_add` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_sub_nat_nat_eq_add_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.subNatNat_eq_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_add_zero_proof()?;

        let c = IntSubNatNatEqAddConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Induction on
        // the second `Nat` argument `n` via `@Nat.rec.{0}` (case analysis;
        // the IH is unused). Base case (`n = 0`) discharged by
        // `congrArg Int.ofNat (Eq.symm (Nat.add_zero m))` because
        // `Int.subNatNat m 0 ι→ Int.ofNat m` and
        // `Int.add (Int.ofNat m) (Int.negOfNat 0) ι→ Int.ofNat (Nat.add m 0)`.
        // Step case (`n = succ k`) closed by pure
        // `@Eq.refl.{1} Int (Int.subNatNat m (Nat.succ k))` because both
        // sides reduce to that form. No `sorry`, no self-reference, no
        // domain-axiom dependency (`Nat.add_zero` is constructive #3551).
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

    #[test]
    fn test_int_sub_nat_nat_eq_add_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_eq_add_proof()
            .expect("first registration");
        env.register_int_sub_nat_nat_eq_add_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.subNatNat_eq_add"))
            .expect("Int.subNatNat_eq_add should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_sub_nat_nat_eq_add_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_eq_add_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.subNatNat_eq_add"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut body = value.clone();
        for _ in 0..2 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected outer λ, got {:?}", k),
            };
        }
        let mut head = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "Int.subNatNat_eq_add proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_int_sub_nat_nat_eq_add_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_eq_add_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.subNatNat_eq_add"))
            .expect("Int.subNatNat_eq_add is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.subNatNat_eq_add must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_sub_nat_nat_eq_add_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_eq_add_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.subNatNat_eq_add"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.subNatNat_eq_add must be Constructive, got {:?}",
            quality
        );
    }
}
