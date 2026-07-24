// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.succ_mul : ∀ a b : Nat, Eq (Nat.mul (Nat.succ a) b) (Nat.add b (Nat.mul a b))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_nat_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is built by induction on the SECOND argument `b` via `Nat.rec.{0}`.
//!
//! # Proof sketch
//!
//! `Nat.mul m n := Nat.rec Nat.zero (λ _ ih => Nat.add ih m) n` — recurses
//! on the second argument.
//!
//! ```text
//! theorem Nat.succ_mul (a b : Nat) : Eq (Nat.mul (Nat.succ a) b) (Nat.add b (Nat.mul a b)) :=
//!   @Nat.rec.{0}
//!     (fun t : Nat => Eq Nat (Nat.mul (Nat.succ a) t) (Nat.add t (Nat.mul a t)))
//!     -- base: motive Nat.zero ≡ Eq Nat.zero Nat.zero (LHS and RHS both
//!     -- iota-reduce to Nat.zero).
//!     (@Eq.refl.{1} Nat Nat.zero)
//!     -- step: given ih : Eq (Nat.mul (succ a) k) (Nat.add k (Nat.mul a k)),
//!     -- witness Eq (Nat.mul (succ a) (succ k)) (Nat.add (succ k) (Nat.mul a (succ k))).
//!     -- After iota+beta reductions (see below) this reduces to
//!     -- Eq (succ (Nat.add (Nat.mul (succ a) k) a))
//!     --    (Nat.add (succ k) (Nat.add (Nat.mul a k) a))
//!     -- which we prove by Eq.trans Eq.trans over three steps:
//!     --   c1 := congrArg (λ x => succ (Nat.add x a)) ih
//!     --   c2 := congrArg Nat.succ (Nat.add_assoc k (Nat.mul a k) a)
//!     --   c3 := Eq.symm (Nat.succ_add k (Nat.add (Nat.mul a k) a))
//!     (fun (k : Nat) (ih : ...) => ...)
//!     b
//! ```
//!
//! **Base case details.**
//! - `Nat.mul (Nat.succ a) Nat.zero` iota-reduces to `Nat.zero` (zero-case
//!   of Nat.rec for Nat.mul).
//! - `Nat.add Nat.zero (Nat.mul a Nat.zero)`: `Nat.mul a Nat.zero` iota-reduces
//!   to `Nat.zero`; then `Nat.add Nat.zero Nat.zero` iota-reduces (zero-case
//!   of Nat.rec for Nat.add, which recurses on the SECOND argument) to
//!   `Nat.zero`.
//!   So motive(Nat.zero) ≡ `Eq Nat Nat.zero Nat.zero`, matched by `@Eq.refl.{1} Nat Nat.zero`.
//!
//! **Step case details.**
//! Let `am = Nat.mul a k`. After iota reductions on both sides of
//! `motive (Nat.succ k)`:
//! - LHS `Nat.mul (succ a) (succ k)`
//!     ι→ `Nat.add (Nat.mul (succ a) k) (succ a)`  (succ-case of mul's rec)
//!     ι→ `Nat.succ (Nat.add (Nat.mul (succ a) k) a)`  (succ-case of the
//!        outer add's rec — its second argument is `Nat.succ a`, headed by succ).
//! - RHS `Nat.add (succ k) (Nat.mul a (succ k))`
//!     specialising `Nat.mul a (succ k)` ι→ `Nat.add am a`, giving
//!     `Nat.add (succ k) (Nat.add am a)` — does NOT iota-reduce further
//!     because the second argument of this outer `Nat.add` is
//!     `Nat.add am a`, whose normal-form head depends on `a`.
//!
//! We witness the equality in three steps via `Eq.trans`:
//!
//! ```text
//! c1 := congrArg (λ x : Nat => Nat.succ (Nat.add x a)) ih
//!       : Eq (succ (Nat.add (Nat.mul (succ a) k) a))
//!            (succ (Nat.add (Nat.add k am) a))
//!
//! c2 := congrArg Nat.succ (Nat.add_assoc k am a)
//!       : Eq (succ (Nat.add (Nat.add k am) a))
//!            (succ (Nat.add k (Nat.add am a)))
//!
//! c3 := Eq.symm (Nat.succ_add k (Nat.add am a))
//!       : Eq (succ (Nat.add k (Nat.add am a)))
//!            (Nat.add (succ k) (Nat.add am a))
//! ```
//!
//! `Eq.trans (Eq.trans c1 c2) c3` witnesses the reduced motive.
//!
//! # Axiom closure
//!
//! Proof mentions `Eq`, `Eq.refl`, `Eq.symm`, `Eq.trans`, `congrArg`,
//! `Nat`, `Nat.zero`, `Nat.succ`, `Nat.add`, `Nat.mul`, `Nat.rec`,
//! `Nat.add_assoc` (constructive — #3551/#3604), `Nat.succ_add`
//! (constructive — #3604). None are `Declaration::Axiom`, so
//! `env.axiom_deps("Nat.succ_mul")` is empty and
//! `env.proof_quality("Nat.succ_mul") == ProofQuality::Constructive`.
//!
//! Tracks #3604 (Int cascade — precondition for `Nat.mul_comm` and then
//! `Int.mul_comm`). Sibling proofs:
//! - `algebra_nat_mul_succ_proof.rs` (companion — Nat.mul_succ).
//! - `algebra_nat_zero_mul_proof.rs` (companion — Nat.zero_mul).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct NatSuccMulConsts {
    nat_type: Expr,
    nat_mul: Expr,
    nat_add: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    nat_add_assoc: Expr,
    nat_succ_add: Expr,
}

impl NatSuccMulConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_add_assoc: Expr::const_(Name::from_string("Nat.add_assoc"), vec![]),
            nat_succ_add: Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
        }
    }
}

/// Build `∀ a b : Nat, Eq Nat (Nat.mul (Nat.succ a) b) (Nat.add b (Nat.mul a b))`.
fn build_type(c: &NatSuccMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let (bv_id, bv) = b.fresh_local(c.nat_type.clone());
    let succ_a = Expr::app(c.nat_succ.clone(), a.clone());
    let lhs = Expr::app(Expr::app(c.nat_mul.clone(), succ_a), bv.clone());
    let am = Expr::app(Expr::app(c.nat_mul.clone(), a.clone()), bv.clone());
    let rhs = Expr::app(Expr::app(c.nat_add.clone(), bv.clone()), am);
    let concl = Expr::apps(c.eq_const.clone(), [c.nat_type.clone(), lhs, rhs]);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Motive: `λ (t : Nat) => Eq Nat (Nat.mul (Nat.succ a) t) (Nat.add t (Nat.mul a t))`.
fn build_motive(c: &NatSuccMulConsts, parent: &EnvDeclBuilder, va: &Expr, v_succ_a: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let m_lhs = Expr::app(Expr::app(c.nat_mul.clone(), v_succ_a.clone()), t.clone());
    let m_am = Expr::app(Expr::app(c.nat_mul.clone(), va.clone()), t.clone());
    let m_rhs = Expr::app(Expr::app(c.nat_add.clone(), t), m_am);
    let body = Expr::apps(c.eq_const.clone(), [c.nat_type.clone(), m_lhs, m_rhs]);
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam)
}

/// Step case: `λ (k : Nat) (ih : motive k) => Eq.trans (Eq.trans c1 c2) c3`.
///
/// See module doc for the definition of `c1`, `c2`, `c3`. Concretely:
///
/// Let `am = Nat.mul a k`, `ih : Eq (Nat.mul (succ a) k) (Nat.add k am)`.
///
/// - Target (motive (succ k), reduced): `Eq (succ (Nat.add (Nat.mul (succ a) k) a))
///                                          (Nat.add (succ k) (Nat.add am a))`.
/// - `c1 : Eq (succ (Nat.add (Nat.mul (succ a) k) a)) (succ (Nat.add (Nat.add k am) a))`
///     via `congrArg (λ x => Nat.succ (Nat.add x a)) ih`.
/// - `c2 : Eq (succ (Nat.add (Nat.add k am) a)) (succ (Nat.add k (Nat.add am a)))`
///     via `congrArg Nat.succ (Nat.add_assoc k am a)`.
/// - `c3 : Eq (succ (Nat.add k (Nat.add am a))) (Nat.add (succ k) (Nat.add am a))`
///     via `Eq.symm (Nat.succ_add k (Nat.add am a))`.
fn build_step(c: &NatSuccMulConsts, parent: &EnvDeclBuilder, va: &Expr, v_succ_a: &Expr) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = sb.fresh_local(c.nat_type.clone());

    // ih type: Eq Nat (Nat.mul (succ a) k) (Nat.add k (Nat.mul a k))
    let am = Expr::app(Expr::app(c.nat_mul.clone(), va.clone()), k.clone());
    let ih_lhs = Expr::app(Expr::app(c.nat_mul.clone(), v_succ_a.clone()), k.clone());
    let ih_rhs = Expr::app(Expr::app(c.nat_add.clone(), k.clone()), am.clone());
    let ih_type = Expr::apps(
        c.eq_const.clone(),
        [c.nat_type.clone(), ih_lhs.clone(), ih_rhs.clone()],
    );
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());

    // func c1: λ x : Nat => Nat.succ (Nat.add x a)
    let func_c1 = {
        let mut fb = EnvDeclBuilder::child_of(&sb);
        let (x_id, x) = fb.fresh_local(c.nat_type.clone());
        let inner = Expr::app(Expr::app(c.nat_add.clone(), x), va.clone());
        let body = Expr::app(c.nat_succ.clone(), inner);
        let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
        fb.finish_child(lam)
    };

    // c1 := congrArg Nat Nat ih_lhs ih_rhs func_c1 ih
    //     : Eq (Nat.succ (Nat.add ih_lhs a)) (Nat.succ (Nat.add ih_rhs a))
    let c1 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.nat_type.clone(),
            ih_lhs.clone(),
            ih_rhs.clone(),
            func_c1,
            ih,
        ],
    );

    // c2: congrArg Nat.succ (Nat.add_assoc k am a)
    // Nat.add_assoc k am a : Eq (Nat.add (Nat.add k am) a) (Nat.add k (Nat.add am a))
    let add_k_am = Expr::app(Expr::app(c.nat_add.clone(), k.clone()), am.clone());
    let lhs_assoc = Expr::app(Expr::app(c.nat_add.clone(), add_k_am), va.clone());
    let add_am_a = Expr::app(Expr::app(c.nat_add.clone(), am.clone()), va.clone());
    let rhs_assoc = Expr::app(Expr::app(c.nat_add.clone(), k.clone()), add_am_a.clone());
    let assoc_witness = Expr::apps(c.nat_add_assoc.clone(), [k.clone(), am.clone(), va.clone()]);
    let c2 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.nat_type.clone(),
            lhs_assoc.clone(),
            rhs_assoc.clone(),
            c.nat_succ.clone(),
            assoc_witness,
        ],
    );

    // c3 := Eq.symm (Nat.succ_add k (Nat.add am a))
    // Nat.succ_add k X : Eq (Nat.add (succ k) X) (Nat.succ (Nat.add k X))
    // with X = Nat.add am a.
    let succ_k = Expr::app(c.nat_succ.clone(), k.clone());
    let add_succ_k_x = Expr::app(Expr::app(c.nat_add.clone(), succ_k), add_am_a.clone());
    let succ_of_add_k_x = Expr::app(c.nat_succ.clone(), rhs_assoc.clone()); // Nat.succ (Nat.add k (Nat.add am a))
    let succ_add_witness = Expr::apps(c.nat_succ_add.clone(), [k.clone(), add_am_a.clone()]);
    let c3 = Expr::apps(
        c.eq_symm.clone(),
        [
            c.nat_type.clone(),
            add_succ_k_x.clone(),
            succ_of_add_k_x.clone(),
            succ_add_witness,
        ],
    );

    // Eq.trans.{1} α x y z h1 h2 : Eq x z.
    // Let P = succ (Nat.add ih_lhs a), Q = succ (Nat.add ih_rhs a) = succ (Nat.add (Nat.add k am) a),
    //     R = succ (Nat.add k (Nat.add am a)), S = Nat.add (succ k) (Nat.add am a).
    let p_expr = Expr::app(
        c.nat_succ.clone(),
        Expr::app(Expr::app(c.nat_add.clone(), ih_lhs.clone()), va.clone()),
    );
    let q_expr = Expr::app(c.nat_succ.clone(), lhs_assoc.clone()); // = succ (Nat.add (Nat.add k am) a)
    let r_expr = succ_of_add_k_x.clone();
    let s_expr = add_succ_k_x.clone();
    // trans1 := Eq.trans p q r c1 c2 : Eq p r
    let trans1 = Expr::apps(
        c.eq_trans.clone(),
        [
            c.nat_type.clone(),
            p_expr.clone(),
            q_expr,
            r_expr.clone(),
            c1,
            c2,
        ],
    );
    // trans2 := Eq.trans p r s trans1 c3 : Eq p s
    let trans2 = Expr::apps(
        c.eq_trans.clone(),
        [c.nat_type.clone(), p_expr, r_expr, s_expr, trans1, c3],
    );

    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, trans2);
    let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
    sb.finish_child(lam_k)
}

/// Body: `λ (a b : Nat) => @Nat.rec.{0} motive base step b`.
fn build_value(c: &NatSuccMulConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (va_id, va) = vb.fresh_local(c.nat_type.clone());
    let (vb_id, vbv) = vb.fresh_local(c.nat_type.clone());
    let v_succ_a = Expr::app(c.nat_succ.clone(), va.clone());
    let motive = build_motive(c, &vb, &va, &v_succ_a);
    // Base: @Eq.refl.{1} Nat Nat.zero. motive(Nat.zero) reduces to Eq Nat.zero Nat.zero.
    let base = Expr::apps(c.eq_refl.clone(), [c.nat_type.clone(), c.nat_zero.clone()]);
    let step = build_step(c, &vb, &va, &v_succ_a);
    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, vbv]);
    let val_raw = vb.mk_lam(vb_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    let val_raw = vb.mk_lam(va_id, BinderInfo::Default, c.nat_type.clone(), val_raw);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Nat.succ_mul` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.add`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`,
    ///           `Eq.symm`, `Eq.trans`, `congrArg`.
    /// REQUIRES: `Nat.add_assoc` and `Nat.succ_add` are registered as
    ///           `Declaration::Theorem` (constructive — #3551/#3604).
    /// ENSURES: On success, `Nat.succ_mul` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_nat_succ_mul_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.succ_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        // Nat.add_assoc and Nat.succ_add are both registered via
        // `init_nat_arith_lemmas`, which register_* functions already call.
        self.register_nat_add_assoc_proof()?;
        self.register_nat_succ_add_proof()?;

        let c = NatSuccMulConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Induction on
        // `b` via `Nat.rec.{0}`. Base case `Eq.refl Nat.zero` (both sides
        // iota-reduce to Nat.zero). Step case chains
        //   c1 := congrArg (λ x => succ (add x a)) ih
        //   c2 := congrArg Nat.succ (Nat.add_assoc k (Nat.mul a k) a)
        //   c3 := Eq.symm (Nat.succ_add k (Nat.add (Nat.mul a k) a))
        // via Eq.trans to witness motive at `Nat.succ k`. Replaces the
        // prior `Declaration::Axiom` in
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

    #[test]
    fn test_nat_succ_mul_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_succ_mul_proof()
            .expect("first registration");
        env.register_nat_succ_mul_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.succ_mul"))
            .expect("Nat.succ_mul should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_nat_succ_mul_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_succ_mul_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.succ_mul"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Nat.succ_mul proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    #[test]
    fn test_nat_succ_mul_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_nat_succ_mul_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.succ_mul"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let outer_body = match value.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected outer λ, got {:?}", k),
        };
        let inner_body = match outer_body.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected inner λ, got {:?}", k),
        };
        let mut head = inner_body.clone();
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "Nat.succ_mul proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_nat_succ_mul_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_succ_mul_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.succ_mul"))
            .expect("Nat.succ_mul is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.succ_mul must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
