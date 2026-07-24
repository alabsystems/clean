// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.subNatNat_add_add : ∀ a b d : Nat,
//!     Eq Int (Int.subNatNat (Nat.add a d) (Nat.add b d)) (Int.subNatNat a b)`.
//!
//! Adding the same `d` to both natural-number arguments of `Int.subNatNat`
//! leaves the (clamped) difference unchanged. This is the cancellation
//! invariant that lets the multiplication-over-`subNatNat` lemmas
//! (`Int.ofNat_mul_subNatNat` / `Int.negSucc_mul_subNatNat`) reassociate the
//! scaled indices in their inductive `(succ p, succ q)` step — the bridge
//! toward a constructive `Int.left_distrib`.
//!
//! # Proof sketch
//!
//! `Nat.add` recurses on its SECOND argument:
//! `Nat.add m 0 = m`, `Nat.add m (succ k) = succ (Nat.add m k)`. So with
//! `a`, `b` held fixed, induct on `d` via `@Nat.rec.{0}`:
//!
//! - `d = Nat.zero`: `Nat.add a 0 ι→ a`, `Nat.add b 0 ι→ b`, so the goal is
//!   definitionally `Eq (subNatNat a b) (subNatNat a b)`; closes by
//!   `@Eq.refl.{1} Int (Int.subNatNat a b)`.
//! - `d = Nat.succ k`: `Nat.add a (succ k) ι→ Nat.succ (Nat.add a k)` and
//!   likewise for `b`, so the goal is definitionally
//!   `Eq (subNatNat (succ (a+k)) (succ (b+k))) (subNatNat a b)`. The first
//!   factor cancels with the constructive `Int.subNatNat_succ_succ (a+k)
//!   (b+k) : Eq (subNatNat (succ (a+k)) (succ (b+k))) (subNatNat (a+k) (b+k))`,
//!   and `ih : Eq (subNatNat (a+k) (b+k)) (subNatNat a b)` finishes via
//!   `Eq.trans`.
//!
//! # Axiom closure
//!
//! The proof mentions only kernel machinery / constructors / reducible
//! Definitions (`Int`, `Int.subNatNat`, `Nat`, `Nat.zero`, `Nat.succ`,
//! `Nat.add`, `Nat.rec`, `Eq`, `Eq.refl`, `Eq.trans`) and the constructive
//! `Declaration::Theorem` `Int.subNatNat_succ_succ` (#3604). None are
//! `Declaration::Axiom`, so `env.axiom_deps("Int.subNatNat_add_add")` is empty
//! and the proof quality is `ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_sub_nat_nat_succ_succ_proof.rs` (the cancellation step).
//! - `algebra_int_sub_nat_nat_zero_left_proof.rs` (subNatNat 0 n = negOfNat n).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntSubNatNatAddAddConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_rec: Expr,
    int_sub_nat_nat: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_trans: Expr,
    int_sub_nat_nat_succ_succ: Expr,
}

impl IntSubNatNatAddAddConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1]),
            int_sub_nat_nat_succ_succ: Expr::const_(
                Name::from_string("Int.subNatNat_succ_succ"),
                vec![],
            ),
        }
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

    /// `Eq.trans Int x y z h1 h2 : Eq Int x z`.
    fn trans_int(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), x, y, z, h1, h2],
        )
    }

    /// `Int.subNatNat_succ_succ m n : Eq (subNatNat (succ m) (succ n)) (subNatNat m n)`.
    fn snn_succ_succ(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.int_sub_nat_nat_succ_succ.clone(), [m, n])
    }
}

/// Build
/// `∀ a b d : Nat, Eq Int (Int.subNatNat (Nat.add a d) (Nat.add b d)) (Int.subNatNat a b)`.
fn build_type(c: &IntSubNatNatAddAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let (bv_id, bv) = b.fresh_local(c.nat_type.clone());
    let (d_id, d) = b.fresh_local(c.nat_type.clone());
    let lhs = c.sub_nat_nat(c.nadd(a.clone(), d.clone()), c.nadd(bv.clone(), d));
    let rhs = c.sub_nat_nat(a.clone(), bv.clone());
    let concl = c.eq_int(lhs, rhs);
    let ty_raw = b.mk_pi(d_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Motive for fixed `a`, `b`:
/// `λ (t : Nat) => Eq Int (subNatNat (a + t) (b + t)) (subNatNat a b)`.
fn build_motive(
    c: &IntSubNatNatAddAddConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let lhs = c.sub_nat_nat(c.nadd(a.clone(), t.clone()), c.nadd(bv.clone(), t));
    let rhs = c.sub_nat_nat(a.clone(), bv.clone());
    let body = c.eq_int(lhs, rhs);
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam)
}

/// Body: `λ (a b d : Nat) => @Nat.rec.{0} motive base step d`.
fn build_value(c: &IntSubNatNatAddAddConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.nat_type.clone());
    let (bv_id, bv) = vb.fresh_local(c.nat_type.clone());
    let (d_id, d) = vb.fresh_local(c.nat_type.clone());

    let motive = build_motive(c, &vb, &a, &bv);

    // Base (d = 0): `subNatNat (a+0) (b+0) ≡ subNatNat a b`. Eq.refl.
    let base = c.refl_int(c.sub_nat_nat(a.clone(), bv.clone()));

    // Step (d = succ k):
    //   goal ≡ Eq (subNatNat (succ (a+k)) (succ (b+k))) (subNatNat a b)
    //   h1 := subNatNat_succ_succ (a+k) (b+k)
    //       : Eq (subNatNat (succ (a+k)) (succ (b+k))) (subNatNat (a+k) (b+k))
    //   ih : Eq (subNatNat (a+k) (b+k)) (subNatNat a b)
    //   Eq.trans h1 ih.
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&vb);
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let a_k = c.nadd(a.clone(), k.clone());
        let b_k = c.nadd(bv.clone(), k.clone());
        let ih_ty = c.eq_int(
            c.sub_nat_nat(a_k.clone(), b_k.clone()),
            c.sub_nat_nat(a.clone(), bv.clone()),
        );
        let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

        let lhs = c.sub_nat_nat(c.succ(a_k.clone()), c.succ(b_k.clone()));
        let mid = c.sub_nat_nat(a_k.clone(), b_k.clone());
        let rhs = c.sub_nat_nat(a.clone(), bv.clone());
        let h1 = c.snn_succ_succ(a_k, b_k);
        let trans = c.trans_int(lhs, mid, rhs, h1, ih);

        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, trans);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_k)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, d]);
    let val_raw = vb.mk_lam(d_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    let val_raw = vb.mk_lam(bv_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    let val_raw = vb.mk_lam(a_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.subNatNat_add_add` as a kernel-checked
    /// `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`,
    ///           `Int.subNatNat`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `Eq.trans`.
    /// REQUIRES: `Int.subNatNat_succ_succ` is registered as a constructive
    ///           `Declaration::Theorem`.
    /// ENSURES: On success, `Int.subNatNat_add_add` is a
    ///          `Declaration::Theorem` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_sub_nat_nat_add_add_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.subNatNat_add_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_int_sub_nat_nat_succ_succ_proof()?;

        let c = IntSubNatNatAddAddConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Induction on `d`
        // via `@Nat.rec.{0}`. Base case (`d = 0`) closed by
        // `@Eq.refl.{1} Int (Int.subNatNat a b)` (both `Nat.add _ 0` arguments
        // iota-reduce). Step case (`d = succ k`) chains
        //   h1 := Int.subNatNat_succ_succ (a+k) (b+k)
        //   ih : Eq (subNatNat (a+k) (b+k)) (subNatNat a b)
        // via `Eq.trans`. No `sorry`, no self-reference, no domain-axiom
        // dependency (`Int.subNatNat_succ_succ` is itself constructive #3604).
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
    fn test_int_sub_nat_nat_add_add_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_add_add_proof()
            .expect("first registration");
        env.register_int_sub_nat_nat_add_add_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.subNatNat_add_add"))
            .expect("Int.subNatNat_add_add should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_sub_nat_nat_add_add_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_add_add_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.subNatNat_add_add"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut body = value.clone();
        for _ in 0..3 {
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
                "proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_int_sub_nat_nat_add_add_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_add_add_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.subNatNat_add_add"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.subNatNat_add_add must have empty axiom closure, got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_sub_nat_nat_add_add_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_int_sub_nat_nat_add_add_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.subNatNat_add_add"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.subNatNat_add_add must be Constructive, got {:?}",
            quality
        );
    }
}
