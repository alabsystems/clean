// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Nat.succ_inj : ∀ a b : Nat, Eq (Nat.succ a) (Nat.succ b) → Eq a b`.
//!
//! This is the constructor-injectivity helper required by the demotion of the
//! Nat/Int cancellation *laws* (`Nat.add_right_cancel`,
//! `Nat.mul_left_cancel_succ`, ...). Unlike the arithmetic identities, the
//! cancellation laws need to invert `Nat.succ`, which is precisely what
//! `Nat.noConfusion` provides.
//!
//! # Proof sketch
//!
//! `Nat.noConfusion` has the signature
//! ```text
//! Nat.noConfusion.{u} : {P : Sort u} → {a b : Nat} → Eq a b → Nat.noConfusionType P a b
//! ```
//! and for two `succ` constructors `Nat.noConfusionType` reduces (by delta+iota
//! on the generated `Nat.noConfusionType` definition) to
//! ```text
//! Nat.noConfusionType P (Nat.succ a) (Nat.succ b) ≡ (Eq a b → P) → P
//! ```
//!
//! Instantiating `P := Eq a b` and feeding the identity continuation
//! `λ (e : Eq a b) => e` yields `Eq a b`:
//!
//! ```text
//! theorem Nat.succ_inj (a b : Nat) (h : Eq (Nat.succ a) (Nat.succ b)) : Eq a b :=
//!   @Nat.noConfusion.{0} (Eq a b) (Nat.succ a) (Nat.succ b) h
//!     (fun (e : Eq a b) => e)
//! ```
//!
//! The continuation `λ e => e` is exactly the evidence extraction: the only
//! datum `noConfusionType` exposes from `succ a = succ b` is the field equality
//! `a = b`, and the identity returns it.
//!
//! # Axiom closure
//!
//! The proof mentions only `Eq`, `Nat`, `Nat.succ`, and `Nat.noConfusion`.
//! `Nat.noConfusion` is a generated *reducible definition* (built from
//! `Eq.ndrec` + `Nat.casesOn`), not a `Declaration::Axiom`, so
//! `env.axiom_deps("Nat.succ_inj")` is empty and
//! `env.proof_quality("Nat.succ_inj") == ProofQuality::Constructive`.
//!
//! Tracks #3604 (cancellation-law demotion). Consumed by
//! `algebra_nat_add_right_cancel_proof.rs` and
//! `algebra_nat_mul_left_cancel_succ_proof.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.succ_inj` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.succ`,
    ///           `Nat.noConfusion`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`.
    /// ENSURES: On success, `Nat.succ_inj` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Nat.succ_inj` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_nat_succ_inj_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.succ_inj");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // IMPORT MODE (`suppress_lossy_structure_stubs`): WITHHOLD Clean's
        // hand-rolled `Nat.succ_inj`. The shape diverges from genuine Lean 4
        // v4.8.0 / Mathlib: Clean registers
        //   `Nat.succ_inj : ∀ (a b : Nat), Eq (succ a) (succ b) → Eq a b`
        // (an EXPLICIT-binder IMPLICATION — its term actually matches the core
        // `Nat.succ.inj`), whereas genuine Mathlib `Nat.succ_inj` is the
        //   `theorem Nat.succ_inj : ∀ {a b : Nat}, (a.succ = b.succ) ↔ (a = b)`
        // IFF (defined as `Nat.succ_inj'`, axiom closure `{propext}`). The
        // `.olean` loader dedups by name (a constant already present in `env` is
        // skipped/rejected, never overwritten — see
        // `clean-olean/src/import/load.rs`), so registering Clean's wrong-shape
        // overlay FIRST shadows the genuine Iff: on import the real
        // `Nat.succ_inj` fails to register (`Duplicate declaration: Nat.succ_inj`,
        // observed on `Mathlib/Data/Nat/Defs`) and every Mathlib proof that uses
        // the Iff (`.mp`/`.mpr`/as a `simp`/rewrite lemma) then fails to
        // kernel-verify. Suppressing the overlay lets the genuine Iff import
        // through the CHECKED `add_decl` path.
        //
        // SOUNDNESS: identical to the proven Nat-arithmetic-lemma overlay gate
        // (WS17/WS19, `data_types_nat_lemmas.rs`) — suppression only ever lets
        // the genuine, fully kernel-checked Mathlib declaration import in the
        // overlay's place; nothing here touches `is_def_eq`/`check_type`/`whnf`
        // or relaxes acceptance. The NON-import lane (`try_with_prelude` /
        // `with_prelude` — `clean check`, the `decide`/`if a=b` path, and every
        // Clean-native caller: `register_nat_dec_eq_proof`, the Nat/Int
        // cancellation lemmas, `boolean_analysis_*`, the bitvec/nn-verify lanes)
        // keeps Clean's explicit-implication `Nat.succ_inj` UNCHANGED.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }

        self.init_eq()?;
        self.init_nat()?;
        // `Nat.noConfusion` may be missing in minimal environments that have not
        // run a full prelude; regenerate it from the inductive declaration.
        if self
            .get_const(&Name::from_string("Nat.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }

        let type1 = Level::succ(Level::zero());
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1]);
        // Nat.noConfusion.{0} — Prop-valued P (the conclusion `Eq a b` is in Prop).
        let nat_no_confusion =
            Expr::const_(Name::from_string("Nat.noConfusion"), vec![Level::zero()]);

        let succ = |x: Expr| Expr::app(nat_succ.clone(), x);
        let eq_nat =
            |lhs: Expr, rhs: Expr| Expr::apps(eq_const.clone(), [nat_const.clone(), lhs, rhs]);

        // ----- Type: ∀ a b : Nat, Eq (succ a) (succ b) → Eq a b -----
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_const.clone());
        let (bv_id, bv) = b.fresh_local(nat_const.clone());
        let h_type = eq_nat(succ(a.clone()), succ(bv.clone()));
        let (h_id, h) = b.fresh_local(h_type.clone());

        let type_ = {
            let concl = eq_nat(a.clone(), bv.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // ----- Value:
        // λ a b h => @Nat.noConfusion.{0} (Eq a b) (succ a) (succ b) h (λ e => e)
        // The continuation `λ (e : Eq a b) => e` extracts the field equality.
        let value = {
            let eq_ab = eq_nat(a.clone(), bv.clone());
            let cont = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (e_id, e) = cb.fresh_local(eq_ab.clone());
                let lam = cb.mk_lam(e_id, BinderInfo::Default, eq_ab.clone(), e);
                cb.finish_child(lam)
            };
            let no_conf = Expr::apps(
                nat_no_confusion,
                [eq_ab, succ(a.clone()), succ(bv.clone()), h, cont],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, no_conf);
            let e = b.mk_lam(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: Real kernel-checked proof term (#3604). Constructor
        // injectivity via `Nat.noConfusion` — for two `succ` constructors,
        // `Nat.noConfusionType (Eq a b) (succ a) (succ b)` delta+iota reduces to
        // `(Eq a b → Eq a b) → Eq a b`, and feeding the identity continuation
        // returns the field equality `Eq a b`. No `sorry`, no self-reference,
        // no domain-axiom dependency (`Nat.noConfusion` is a generated reducible
        // definition built from `Eq.ndrec` + `Nat.casesOn`).
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
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    /// Kernel accepts the `Nat.noConfusion` injectivity proof term and the
    /// declaration is registered as a Theorem (not Axiom), idempotently.
    #[test]
    fn test_nat_succ_inj_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_succ_inj_proof()
            .expect("first registration");
        env.register_nat_succ_inj_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.succ_inj"))
            .expect("Nat.succ_inj should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Nat.succ_inj"), vec![]))
            .expect("Nat.succ_inj should type-check");
    }

    /// The proof body uses `Nat.noConfusion` (constructor injectivity) — guards
    /// against a degenerate `Eq.refl` / axiom-reference masquerade.
    #[test]
    fn test_nat_succ_inj_proof_uses_no_confusion() {
        let mut env = Environment::new();
        env.register_nat_succ_inj_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Nat.succ_inj"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel three λ binders (a, b, h), then the head must be Nat.noConfusion.
        let mut cur = value.clone();
        for _ in 0..3 {
            cur = match cur.kind() {
                ExprKind::Lam(_, _, body) => (**body).clone(),
                k => panic!("expected λ binder, got {:?}", k),
            };
        }
        let mut head = cur;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.noConfusion",
                "Nat.succ_inj proof root must be Nat.noConfusion"
            ),
            k => panic!("expected Const(Nat.noConfusion, ..), got {:?}", k),
        }
    }

    /// Axiom closure is empty — `Nat.noConfusion` is a generated reducible
    /// definition, not a `Declaration::Axiom`.
    #[test]
    fn test_nat_succ_inj_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_nat_succ_inj_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Nat.succ_inj"))
            .expect("Nat.succ_inj is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Nat.succ_inj must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
        assert_eq!(
            env.proof_quality(&Name::from_string("Nat.succ_inj"))
                .expect("proof quality should compute"),
            ProofQuality::Constructive
        );
    }
}
