// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.mul_assoc : ∀ a b c : Nat,
//!     Eq (Nat.mul (Nat.mul a b) c) (Nat.mul a (Nat.mul b c))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is built by induction on the THIRD argument `c` via `Nat.rec.{0}`.
//!
//! # Proof sketch
//!
//! `Nat.mul m n := Nat.rec Nat.zero (λ _ ih => Nat.add ih m) n` recurses on
//! its SECOND argument:
//!
//! ```text
//! Nat.mul m Nat.zero      = Nat.zero
//! Nat.mul m (Nat.succ k)  = Nat.add (Nat.mul m k) m
//! ```
//!
//! Inducting on `c`:
//!
//! ```text
//! theorem Nat.mul_assoc (a b c : Nat) :
//!     Eq (Nat.mul (Nat.mul a b) c) (Nat.mul a (Nat.mul b c)) :=
//!   @Nat.rec.{0}
//!     (fun t : Nat => Eq Nat (Nat.mul (Nat.mul a b) t)
//!                            (Nat.mul a (Nat.mul b t)))           -- motive
//!     (@Eq.refl.{1} Nat Nat.zero)                                -- base
//!     (fun (k : Nat) (ih : ...) => Eq.trans c1 c2)               -- step
//!     c
//! ```
//!
//! **Base case.** `motive Nat.zero` is
//! `Eq (Nat.mul (Nat.mul a b) Nat.zero) (Nat.mul a (Nat.mul b Nat.zero))`.
//! - LHS: `Nat.mul (Nat.mul a b) Nat.zero ι→ Nat.zero`.
//! - RHS: `Nat.mul b Nat.zero ι→ Nat.zero`, then `Nat.mul a Nat.zero ι→ Nat.zero`.
//!
//! So `motive Nat.zero` defn-equals `Eq Nat.zero Nat.zero`, matched by
//! `@Eq.refl.{1} Nat Nat.zero`.
//!
//! **Step case.** Given `ih : Eq (Nat.mul (Nat.mul a b) k)
//! (Nat.mul a (Nat.mul b k))`, we need `motive (Nat.succ k)`.
//! Reductions:
//! - LHS `Nat.mul (Nat.mul a b) (Nat.succ k)` ι→
//!   `Nat.add (Nat.mul (Nat.mul a b) k) (Nat.mul a b)`.
//! - RHS `Nat.mul a (Nat.mul b (Nat.succ k))`: `Nat.mul b (Nat.succ k) ι→
//!   Nat.add (Nat.mul b k) b`, so RHS ≡ `Nat.mul a (Nat.add (Nat.mul b k) b)`
//!   (no further iota — the second argument's normal-form head is a non-constructor).
//!
//! So with `P = Nat.mul (Nat.mul a b) k`, `Q = Nat.mul a (Nat.mul b k)`
//! (`ih : Eq P Q`), `ab = Nat.mul a b`, `bk = Nat.mul b k`, the reduced target
//! is `Eq (Nat.add P ab) (Nat.mul a (Nat.add bk b))`. We witness it via two
//! `Eq.trans` steps:
//!
//! ```text
//! c1 := congrArg (λ x : Nat => Nat.add x ab) ih
//!       : Eq (Nat.add P ab) (Nat.add Q ab)
//!         where Nat.add Q ab = Nat.add (Nat.mul a bk) (Nat.mul a b)
//!
//! c2 := Eq.symm (Nat.left_distrib a bk b)
//!       : Eq (Nat.add (Nat.mul a bk) (Nat.mul a b)) (Nat.mul a (Nat.add bk b))
//! ```
//!
//! (`Nat.left_distrib a bk b : Eq (Nat.mul a (Nat.add bk b))
//! (Nat.add (Nat.mul a bk) (Nat.mul a b))`, so `Eq.symm` flips it.)
//!
//! `Eq.trans c1 c2` witnesses the reduced motive at `Nat.succ k`.
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Eq.refl`, `Eq.symm`, `Eq.trans`,
//! `congrArg`, `Nat`, `Nat.zero`, `Nat.succ`, `Nat.add`, `Nat.mul`,
//! `Nat.rec`, and `Nat.left_distrib` (constructive `Declaration::Theorem`,
//! #3604). None are `Declaration::Axiom`, so
//! `env.axiom_deps("Nat.mul_assoc")` is empty and
//! `env.proof_quality("Nat.mul_assoc") == ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_nat_left_distrib_proof.rs` (#3604, dependency — Nat.left_distrib).
//! - `algebra_nat_mul_comm_proof.rs` (#3604, same Eq.trans-chain shape).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatMulAssocConsts {
    nat_type: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    nat_zero: Expr,
    #[cfg(test)]
    nat_succ: Expr,
    nat_rec: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    nat_left_distrib: Expr,
}

impl NatMulAssocConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            #[cfg(test)]
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            // Nat.rec.{0} — Prop-valued motive.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            // congrArg.{1,1} : {α β : Type} → {a₁ a₂ : α} → (f : α → β) → Eq a₁ a₂ → Eq (f a₁) (f a₂)
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_left_distrib: Expr::const_(Name::from_string("Nat.left_distrib"), vec![]),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), x), y)
    }

    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_mul.clone(), x), y)
    }

    fn eq_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.nat_type.clone(), lhs, rhs])
    }
}

/// Build
/// `∀ a b c : Nat, Eq Nat (Nat.mul (Nat.mul a b) c) (Nat.mul a (Nat.mul b c))`.
fn build_type(c: &NatMulAssocConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let (bv_id, bv) = b.fresh_local(c.nat_type.clone());
    let (cv_id, cv) = b.fresh_local(c.nat_type.clone());
    let lhs = c.mul(c.mul(a.clone(), bv.clone()), cv.clone());
    let rhs = c.mul(a.clone(), c.mul(bv.clone(), cv));
    let concl = c.eq_nat(lhs, rhs);
    let ty_raw = b.mk_pi(cv_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Motive:
/// `λ (t : Nat) => Eq Nat (Nat.mul (Nat.mul a b) t) (Nat.mul a (Nat.mul b t))`.
fn build_motive(c: &NatMulAssocConsts, parent: &EnvDeclBuilder, va: &Expr, vb: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let m_lhs = c.mul(c.mul(va.clone(), vb.clone()), t.clone());
    let m_rhs = c.mul(va.clone(), c.mul(vb.clone(), t));
    let body = c.eq_nat(m_lhs, m_rhs);
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam)
}

/// Step case: `λ (k : Nat) (ih : motive k) => Eq.trans c1 c2`.
///
/// Let `ab = Nat.mul a b`, `bk = Nat.mul b k`, `P = Nat.mul ab k`,
/// `Q = Nat.mul a bk`. `ih : Eq P Q`.
///
/// - `c1 := congrArg (λ x => Nat.add x ab) ih
///        : Eq (Nat.add P ab) (Nat.add Q ab)`.
/// - `c2 := Eq.symm (Nat.left_distrib a bk b)
///        : Eq (Nat.add (Nat.mul a bk) (Nat.mul a b)) (Nat.mul a (Nat.add bk b))`.
///
/// `Nat.add Q ab = Nat.add (Nat.mul a bk) (Nat.mul a b)` (since `ab = Nat.mul a b`),
/// so `c2`'s LHS matches `c1`'s RHS. `Eq.trans c1 c2 : Eq (Nat.add P ab)
/// (Nat.mul a (Nat.add bk b))`, which is definitionally the reduced
/// `motive (Nat.succ k)`.
fn build_step(c: &NatMulAssocConsts, parent: &EnvDeclBuilder, va: &Expr, vb: &Expr) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = sb.fresh_local(c.nat_type.clone());

    let ab = c.mul(va.clone(), vb.clone());
    let bk = c.mul(vb.clone(), k.clone());
    let p_expr = c.mul(ab.clone(), k.clone());
    let q_expr = c.mul(va.clone(), bk.clone());

    // ih : Eq P Q
    let ih_type = c.eq_nat(p_expr.clone(), q_expr.clone());
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());

    // func c1: λ x : Nat => Nat.add x ab
    let func_c1 = {
        let mut fb = EnvDeclBuilder::child_of(&sb);
        let (x_id, x) = fb.fresh_local(c.nat_type.clone());
        let body = c.add(x, ab.clone());
        let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
        fb.finish_child(lam)
    };

    // c1 := congrArg Nat Nat P Q (λ x => Nat.add x ab) ih
    //     : Eq (Nat.add P ab) (Nat.add Q ab)
    let c1 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.nat_type.clone(),
            p_expr.clone(),
            q_expr.clone(),
            func_c1,
            ih,
        ],
    );

    // c2 := Eq.symm (Nat.left_distrib a bk b)
    // Nat.left_distrib a bk b
    //   : Eq (Nat.mul a (Nat.add bk b)) (Nat.add (Nat.mul a bk) (Nat.mul a b))
    let mul_a_bk = c.mul(va.clone(), bk.clone()); // = Q
    let mul_a_b = c.mul(va.clone(), vb.clone()); // = ab
    let mul_a_add_bk_b = c.mul(va.clone(), c.add(bk.clone(), vb.clone()));
    let add_a_bk_a_b = c.add(mul_a_bk.clone(), mul_a_b.clone());
    let left_distrib_witness = Expr::apps(
        c.nat_left_distrib.clone(),
        [va.clone(), bk.clone(), vb.clone()],
    );
    let c2 = Expr::apps(
        c.eq_symm.clone(),
        [
            c.nat_type.clone(),
            mul_a_add_bk_b.clone(),
            add_a_bk_a_b.clone(),
            left_distrib_witness,
        ],
    );

    // Eq.trans Nat (Nat.add P ab) (Nat.add Q ab) (Nat.mul a (Nat.add bk b)) c1 c2
    let add_p_ab = c.add(p_expr, ab.clone());
    let add_q_ab = c.add(q_expr, ab); // = Nat.add (Nat.mul a bk) (Nat.mul a b) = add_a_bk_a_b
    let trans = Expr::apps(
        c.eq_trans.clone(),
        [
            c.nat_type.clone(),
            add_p_ab,
            add_q_ab,
            mul_a_add_bk_b,
            c1,
            c2,
        ],
    );

    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, trans);
    let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
    sb.finish_child(lam_k)
}

/// Body: `λ (a b c : Nat) => @Nat.rec.{0} motive base step c`.
fn build_value(c: &NatMulAssocConsts) -> Expr {
    let mut vb_b = EnvDeclBuilder::new();
    let (va_id, va) = vb_b.fresh_local(c.nat_type.clone());
    let (vb_id, vb) = vb_b.fresh_local(c.nat_type.clone());
    let (vc_id, vc) = vb_b.fresh_local(c.nat_type.clone());
    let motive = build_motive(c, &vb_b, &va, &vb);
    // Base: @Eq.refl.{1} Nat Nat.zero. motive(Nat.zero) reduces both sides to
    // `Nat.zero`.
    let base = Expr::apps(c.eq_refl.clone(), [c.nat_type.clone(), c.nat_zero.clone()]);
    let step = build_step(c, &vb_b, &va, &vb);
    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, vc]);
    let val_raw = vb_b.mk_lam(vc_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    let val_raw = vb_b.mk_lam(vb_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    let val_raw = vb_b.mk_lam(va_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    vb_b.finish(val_raw)
}

impl Environment {
    /// Register `Nat.mul_assoc` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add`, `Nat.mul`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `Eq.symm`,
    ///           `Eq.trans`, `congrArg`.
    /// REQUIRES: `Nat.left_distrib` is registered as `Declaration::Theorem`
    ///           (constructive — see `register_nat_left_distrib_proof`).
    /// ENSURES: On success, `Nat.mul_assoc` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.mul_assoc` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_mul_assoc_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mul_assoc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_left_distrib_proof()?;

        let c = NatMulAssocConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Induction on the
        // third argument `c` via `Nat.rec.{0}`. Base case closed by
        // `@Eq.refl.{1} Nat Nat.zero` (motive at Nat.zero reduces both sides
        // to `Nat.zero` via iota zero-case + delta on Nat.mul). Step case
        // chains
        //   c1 := congrArg (λ x => Nat.add x (Nat.mul a b)) ih
        //   c2 := Eq.symm (Nat.left_distrib a (Nat.mul b k) b)
        // via Eq.trans. No `sorry`, no self-reference, no domain-axiom
        // dependency (`Nat.left_distrib` is itself constructive #3604).
        // Replaces the prior `Declaration::Axiom` in
        // `data_types_nat_lemmas.rs::init_nat_arith_lemmas`.
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

    /// Kernel accepts the `Nat.rec` / `congrArg` / `Eq.trans` proof term.
    /// Verifies the theorem is registered as a Theorem (not Axiom) and
    /// idempotent re-invocation is a no-op.
    #[test]
    fn test_nat_mul_assoc_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_mul_assoc_proof()
            .expect("first registration");
        env.register_nat_mul_assoc_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.mul_assoc"))
            .expect("Nat.mul_assoc should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ`
    /// abstraction. Guards against the axiom-wrapping masquerade (#3559).
    #[test]
    fn test_nat_mul_assoc_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_mul_assoc_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.mul_assoc"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.mul_assoc proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// After peeling three outer λ binders, the proof root is `@Nat.rec.{0}`.
    /// Guards against a trivial `Eq.refl` masquerade — `Nat.mul_assoc`
    /// cannot reduce without induction on the third argument.
    #[test]
    fn test_nat_mul_assoc_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_mul_assoc_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.mul_assoc"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let b1 = match value.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected λ a, got {:?}", k),
        };
        let b2 = match b1.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected λ b, got {:?}", k),
        };
        let b3 = match b2.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected λ c, got {:?}", k),
        };
        let mut head = b3.clone();
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "Nat.mul_assoc proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof). `Nat.left_distrib` is
    /// constructive (#3604), so `Nat.mul_assoc` inherits empty deps.
    #[test]
    fn test_nat_mul_assoc_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_mul_assoc_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.mul_assoc"))
            .expect("Nat.mul_assoc is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.mul_assoc must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
