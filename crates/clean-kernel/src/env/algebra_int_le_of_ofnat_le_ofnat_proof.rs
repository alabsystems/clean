// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the reverse Nat-cast (Int form)
//! `Int.le_of_ofNat_le_ofNat :
//!    ∀ a b : Nat, Int.le (Int.ofNat a) (Int.ofNat b) → Nat.le a b`.
//!
//! Hand-constructed `Expr` (no tactics). This is the converse of the forward
//! cast `Int.ofNat_le_ofNat_of_le : Nat.le a b → Int.le (ofNat a) (ofNat b)`
//! (in `boolean_analysis_kkl_natbridge.rs`), and the Int-level core of the
//! reverse `Rat` cast.
//!
//! # Proof sketch
//!
//! By `@Or.rec` on `Nat.le_or_lt a b : Or (Nat.le a b) (Nat.lt b a)` with the
//! constant motive `λ _ => Nat.le a b`:
//!
//! - **inl (`h : Nat.le a b`)**: return `h` directly.
//!
//! - **inr (`h : Nat.lt b a`)** — note `Nat.lt b a ≡ Nat.le (Nat.succ b) a`:
//!   we derive `False` and apply `@False.elim`. The contradiction:
//!   * `Int.ofNat_le_ofNat_of_le (Nat.succ b) a h
//!       : Int.le (Int.ofNat (Nat.succ b)) (Int.ofNat a)` (forward cast),
//!   * chained with the hypothesis `hyp : Int.le (Int.ofNat a) (Int.ofNat b)`
//!     via `Int.le_trans (ofNat (succ b)) (ofNat a) (ofNat b)` gives
//!     `Int.le (Int.ofNat (Nat.succ b)) (Int.ofNat b)`.
//!     Now `Int.ofNat (Nat.succ b) ≡ Int.add (Int.ofNat b) (Int.ofNat 1)`
//!     (the additive `Int.ofNat` defeq the forward cast already relies on), and
//!     `Int.lt x y := Int.le (Int.add x (Int.ofNat 1)) y` (reducible), so the
//!     above term is defeq to `Int.lt (Int.ofNat b) (Int.ofNat b)`. Feeding it to
//!     `Int.lt_irrefl (Int.ofNat b) : Not (Int.lt (Int.ofNat b) (Int.ofNat b))`
//!     (`Not P := P → False`) yields `False`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Nat`, `Nat.succ`, `Nat.le`, `Nat.lt`, `Int`,
//! `Int.ofNat`, `Int.le`, `Or`, `Or.rec`, `False.elim`, and the constructive
//! `Declaration::Theorem`s `Nat.le_or_lt`, `Int.ofNat_le_ofNat_of_le`,
//! `Int.le_trans`, `Int.lt_irrefl`. None are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.le_of_ofNat_le_ofNat")` is empty and
//! `env.proof_quality("Int.le_of_ofNat_le_ofNat") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
struct IntLeOfOfNatConsts {
    nat: Expr,
    nat_succ: Expr,
    nat_le: Expr,
    #[cfg(test)]
    int: Expr,
    int_of_nat: Expr,
    int_le: Expr,
    or_const: Expr,
    or_rec: Expr,
    #[cfg(test)]
    false_const: Expr,
    false_elim: Expr,
    nat_le_or_lt: Expr,
    int_ofnat_le_ofnat_of_le: Expr,
    int_le_trans: Expr,
    int_lt_irrefl: Expr,
}

impl IntLeOfOfNatConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            #[cfg(test)]
            int: Expr::const_(Name::from_string("Int"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            or_const: Expr::const_(Name::from_string("Or"), vec![]),
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            #[cfg(test)]
            false_const: Expr::const_(Name::from_string("False"), vec![]),
            false_elim: Expr::const_(
                Name::from_string("False.elim"),
                vec![crate::level::Level::zero()],
            ),
            nat_le_or_lt: Expr::const_(Name::from_string("Nat.le_or_lt"), vec![]),
            int_ofnat_le_ofnat_of_le: Expr::const_(
                Name::from_string("Int.ofNat_le_ofNat_of_le"),
                vec![],
            ),
            int_le_trans: Expr::const_(Name::from_string("Int.le_trans"), vec![]),
            int_lt_irrefl: Expr::const_(Name::from_string("Int.lt_irrefl"), vec![]),
        }
    }

    fn succ(&self, x: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), x)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    /// Raw `Nat.le lhs rhs`.
    fn nle(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [lhs, rhs])
    }

    /// `Nat.lt lhs rhs`, written as its reducible expansion `Nat.le (succ lhs) rhs`.
    fn nlt_raw(&self, lhs: Expr, rhs: Expr) -> Expr {
        self.nle(self.succ(lhs), rhs)
    }

    /// `Int.le lhs rhs`.
    fn ile(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [lhs, rhs])
    }

    /// `Or a b`.
    fn or_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.or_const.clone(), [a, b])
    }
}

/// Build `∀ a b : Nat, Int.le (Int.ofNat a) (Int.ofNat b) → Nat.le a b`.
fn build_type(c: &IntLeOfOfNatConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (bb_id, bb) = b.fresh_local(c.nat.clone());
    let ante = c.ile(c.of_nat(a.clone()), c.of_nat(bb.clone()));
    let (h_id, _h) = b.fresh_local(ante.clone());
    let concl = c.nle(a.clone(), bb.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, ante, concl);
    let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Body: `λ (a b : Nat) (hyp : Int.le (ofNat a) (ofNat b)) =>
///          @Or.rec (Nat.le a b) (Nat.lt b a) motive inl_case inr_case
///                  (Nat.le_or_lt a b)`.
fn build_value(c: &IntLeOfOfNatConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (bb_id, bb) = b.fresh_local(c.nat.clone());
    let ante = c.ile(c.of_nat(a.clone()), c.of_nat(bb.clone()));
    let (hyp_id, hyp) = b.fresh_local(ante.clone());

    // Or summands: src_left = Nat.le a b, src_right = Nat.lt b a (≡ Nat.le (succ b) a).
    let src_left = c.nle(a.clone(), bb.clone());
    let src_right = c.nlt_raw(bb.clone(), a.clone());
    let goal = c.nle(a.clone(), bb.clone());

    // motive: λ (_ : Or (Nat.le a b) (Nat.lt b a)) => Nat.le a b
    let motive = {
        let mut om = EnvDeclBuilder::child_of(&b);
        let or_ty = c.or_of(src_left.clone(), src_right.clone());
        let (hh_id, _hh) = om.fresh_local(or_ty.clone());
        let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ty, goal.clone());
        om.finish_child(lam)
    };

    // inl: λ (h : Nat.le a b) => h
    let case_inl = {
        let mut ic = EnvDeclBuilder::child_of(&b);
        let (h_id, h) = ic.fresh_local(src_left.clone());
        let lam = ic.mk_lam(h_id, BinderInfo::Default, src_left.clone(), h);
        ic.finish_child(lam)
    };

    // inr: λ (h : Nat.lt b a) =>
    //   @False.elim (Nat.le a b)
    //     (Int.lt_irrefl (ofNat b)
    //        (Int.le_trans (ofNat (succ b)) (ofNat a) (ofNat b)
    //           (Int.ofNat_le_ofNat_of_le (succ b) a h) hyp))
    let case_inr = {
        let mut rc = EnvDeclBuilder::child_of(&b);
        let (h_id, h) = rc.fresh_local(src_right.clone());

        let of_succ_b = c.of_nat(c.succ(bb.clone()));
        let of_a = c.of_nat(a.clone());
        let of_b = c.of_nat(bb.clone());

        // fwd : Int.le (ofNat (succ b)) (ofNat a)
        //   (Int.ofNat_le_ofNat_of_le expects Nat.le (succ b) a; h : Nat.lt b a
        //    ≡ Nat.le (succ b) a by defeq).
        let fwd = Expr::apps(
            c.int_ofnat_le_ofnat_of_le.clone(),
            [c.succ(bb.clone()), a.clone(), h],
        );

        // chained : Int.le (ofNat (succ b)) (ofNat b)
        //   ≡ Int.le (Int.add (ofNat b) (ofNat 1)) (ofNat b) ≡ Int.lt (ofNat b) (ofNat b).
        let chained = Expr::apps(
            c.int_le_trans.clone(),
            [of_succ_b, of_a, of_b.clone(), fwd, hyp.clone()],
        );

        // absurd : False — Int.lt_irrefl (ofNat b) chained
        //   (Not (Int.lt (ofNat b) (ofNat b)) ≡ Int.lt (ofNat b) (ofNat b) → False).
        let absurd = Expr::apps(c.int_lt_irrefl.clone(), [of_b, chained]);

        let body = Expr::apps(c.false_elim.clone(), [goal.clone(), absurd]);
        let lam = rc.mk_lam(h_id, BinderInfo::Default, src_right.clone(), body);
        rc.finish_child(lam)
    };

    // major : Nat.le_or_lt a b : Or (Nat.le a b) (Nat.lt b a)
    let major = Expr::apps(c.nat_le_or_lt.clone(), [a.clone(), bb.clone()]);

    let or_rec_app = Expr::apps(
        c.or_rec.clone(),
        [src_left, src_right, motive, case_inl, case_inr, major],
    );

    let e = b.mk_lam(hyp_id, BinderInfo::Default, ante, or_rec_app);
    let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register `Int.le_of_ofNat_le_ofNat` as a kernel-checked
    /// `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int`, `Int.ofNat`,
    ///           `Int.le`, `Int.lt`, `Int.NonNeg`.
    /// REQUIRES: `self.init_nat()` / `init_le()` / `init_lt()` / `init_or()` /
    ///           `init_true_false()` have registered `Nat`, `Nat.succ`,
    ///           `Nat.le`, `Nat.lt`, `Or`, `Or.rec`, `False`, `False.elim`.
    /// REQUIRES: `Nat.le_or_lt`, `Int.ofNat_le_ofNat_of_le`, `Int.le_trans`,
    ///           `Int.lt_irrefl` are registered as constructive
    ///           `Declaration::Theorem`s.
    /// ENSURES: On success, `Int.le_of_ofNat_le_ofNat` is a
    ///          `Declaration::Theorem` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if already registered with any declaration kind,
    ///          this call returns `Ok(())` without modification.
    pub(crate) fn register_int_le_of_ofnat_le_ofnat_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.le_of_ofNat_le_ofNat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_or()?;
        self.init_true_false()?; // False, False.elim
        self.init_int_ord()?; // Int.le, Int.lt, Int.NonNeg

        // Constructive dependencies.
        // Nat.le_or_lt (registered transitively by this call).
        self.register_nat_mul_left_cancel_succ_proof()?;
        // `register_nat_cast_le_of_ble` also registers the Rat-level
        // `Nat.cast_le_of_ble`, which references `instLERat`; seed the Rat
        // order layer first so that lemma type-checks in a minimal env.
        self.init_rat_ord()?;
        // Int.ofNat_le_ofNat_of_le forward cast (registered alongside).
        self.register_nat_cast_le_of_ble()?;
        // Int.le_trans and Int.lt_irrefl.
        self.register_int_le_trans_proof()?;
        self.register_int_lt_irrefl_proof()?;

        let c = IntLeOfOfNatConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. `@Or.rec` on the
        // constructive `Nat.le_or_lt a b`; the `inl` branch returns the `Nat.le`
        // witness, the `inr` branch (`Nat.lt b a ≡ Nat.le (succ b) a`) derives
        // `False` via `Int.lt_irrefl (ofNat b)` applied to
        // `Int.le_trans (Int.ofNat_le_ofNat_of_le (succ b) a h) hyp`
        // — which is defeq to `Int.lt (ofNat b) (ofNat b)` because
        // `Int.ofNat (succ b) ≡ Int.add (ofNat b) (ofNat 1)` and
        // `Int.lt x y := Int.le (x+1) y` — then `@False.elim`. No `sorry`, no
        // self-reference, no domain-axiom dependency (all deps constructive).
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

    fn registered(env: &mut Environment) {
        env.register_int_le_of_ofnat_le_ofnat_proof()
            .expect("registration");
    }

    /// Kernel accepts the `Or.rec` / `Int.lt_irrefl` / `False.elim` proof term.
    /// Verifies it is a Theorem (not Axiom) and idempotent re-invocation is a
    /// no-op.
    #[test]
    fn test_int_le_of_ofnat_le_ofnat_registered_as_theorem() {
        let mut env = Environment::new();
        registered(&mut env);
        env.register_int_le_of_ofnat_le_ofnat_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.le_of_ofNat_le_ofNat"))
            .expect("Int.le_of_ofNat_le_ofNat should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// Proof root (after peeling the three outer λ binders) must be an
    /// `@Or.rec` application. Guards against an axiom-wrapping masquerade.
    #[test]
    fn test_int_le_of_ofnat_le_ofnat_proof_uses_or_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        registered(&mut env);
        let info = env
            .get_const(&Name::from_string("Int.le_of_ofNat_le_ofNat"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut body = value.clone();
        for _ in 0..3 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected λ binder, got {:?}", k),
            };
        }
        let mut head = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Or.rec",
                "Int.le_of_ofNat_le_ofNat proof root must be Or.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Or.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof).
    #[test]
    fn test_int_le_of_ofnat_le_ofnat_axiom_deps_empty() {
        let mut env = Environment::new();
        registered(&mut env);
        let deps = env
            .axiom_deps(&Name::from_string("Int.le_of_ofNat_le_ofNat"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.le_of_ofNat_le_ofNat must have empty axiom closure (constructive), got {:?}",
            domain_deps
        );
    }
}
