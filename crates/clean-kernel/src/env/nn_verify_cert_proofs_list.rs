// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! List-level composition and consistency proofs for T72b.
//!
//! Defines `listComposeTrust` via `List.rec @{1,0}` and proves that
//! its axiom profile equals the fold of pairwise `composePair`.
//! Also proves pairwise/list-level consistency.
//!
//! Split from `nn_verify_cert_proofs.rs` for the 500-line file limit.
//! Part of #3220, #3247.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::nn_verify_cert_proofs::T72Consts;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `NNVerify.listComposeTrust` via `List.rec @{1,0}`.
    ///
    /// Type: `List BlockCert → BlockCert`
    /// Value: fold via `Nat.lor`, base case `Nat.zero`.
    pub(super) fn register_list_compose_trust_grounded(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.listComposeTrust"))
            .is_some()
        {
            return Ok(());
        }
        let c = T72Consts::new();
        let fn_type = Expr::pi(
            BinderInfo::Default,
            c.list_block_cert(),
            c.block_cert.clone(),
        );
        let fn_value = build_list_compose_trust_value(&c);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.listComposeTrust"),
            level_params: vec![],
            type_: fn_type,
            value: fn_value,
            is_reducible: true,
        })
    }

    /// T72b: `axiomProfile (listComposeTrust cs) = listComposeTrust cs`.
    ///
    /// SOUNDNESS: #3592 — Branch A twin demotion. Prior proof was
    /// `fun cs => Eq.refl (listComposeTrust cs)` which type-checked only
    /// because `axiomProfile` was a reducible `Declaration::Definition`
    /// with identity body and δ-reduced the LHS `axiomProfile (listComposeTrust cs)`
    /// to `listComposeTrust cs`. Identical M1 + M2 + M4 masquerade shape
    /// as T72.a (`cert_composition_trust`, reports/audit/2026-04-20-r10-wave8-masquerade-sweep.md).
    /// Because the companion #3592 carrier demotion flips `axiomProfile`
    /// to `Declaration::Opaque`, the former δ path is closed and this
    /// theorem can no longer close by `Eq.refl`. Demoted to
    /// `Declaration::Axiom` on its original Pi type so the kernel does
    /// not silently accept a fake proof.
    pub(super) fn register_cert_list_composition_trust_grounded(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.cert_list_composition_trust"))
            .is_some()
        {
            return Ok(());
        }
        let c = T72Consts::new();
        let (theorem_type, _proof_value) = build_cert_list_composition_trust(&c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.cert_list_composition_trust"),
            level_params: vec![],
            type_: theorem_type,
        })
    }

    /// Consistency: pairwise `composePair` agrees with list-level `listComposeTrust`.
    ///
    /// States: `∀ c1 c2, axiomProfile (composePair c1 c2) =
    ///          axiomProfile (listComposeTrust [c1, c2])`.
    ///
    /// Registered as axiom because `listComposeTrust [c1, c2]` reduces to
    /// `Nat.lor c1 (Nat.lor c2 0)` while `composePair c1 c2` reduces to
    /// `Nat.lor c1 c2`. Closing the gap requires `Nat.lor n 0 = n` which
    /// is not definitionally provable for symbolic `n`.
    pub(super) fn register_cert_pairwise_list_consistent(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.cert_pairwise_list_consistent"))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_lor_zero_left()?;
        let c = T72Consts::new();
        let theorem_type = build_consistency_type(&c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.cert_pairwise_list_consistent"),
            level_params: vec![],
            type_: theorem_type,
        })
    }

    /// Register `Nat.lor_zero_left : ∀ n, Nat.lor 0 n = n` as axiom.
    ///
    /// This identity holds for concrete naturals (the native reducer handles it)
    /// but is not definitionally provable for symbolic `n`. Registered as a
    /// trusted axiom since the Rust `Nat.lor` implementation satisfies it.
    fn register_nat_lor_zero_left(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Nat.lor_zero_left"))
            .is_some()
        {
            return Ok(());
        }
        let c = T72Consts::new();
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let lhs = c.build_nat_lor(c.nat_zero.clone(), n.clone());
            let eq = c.build_eq_type(lhs, n);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), eq);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.lor_zero_left"),
            level_params: vec![],
            type_: thm_type,
        })
    }
}

// ── Helper builders ───────────────────────────────────────────────────

/// Build the `List.rec @{1,0}` value for `listComposeTrust`.
///
/// Motive: `fun _ => BlockCert` (constant function returning `Nat`).
/// Nil case: `Nat.zero`.
/// Cons case: `fun head _ acc => Nat.lor head acc`.
fn build_list_compose_trust_value(c: &T72Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (cs_id, cs) = b.fresh_local(c.list_block_cert());

    // Motive: fun (_ : List BlockCert) => BlockCert
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (m_id, _m) = ch.fresh_local(c.list_block_cert());
        let r = ch.mk_lam(
            m_id,
            BinderInfo::Default,
            c.list_block_cert(),
            c.block_cert.clone(),
        );
        ch.finish_child(r)
    };

    // Nil case: Nat.zero
    let nil_case = c.nat_zero.clone();

    // Cons case: fun (head : BlockCert) (_ : List BlockCert) (acc : BlockCert)
    //            => Nat.lor head acc
    let cons_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (head_id, head) = ch.fresh_local(c.block_cert.clone());
        let (tail_id, _tail) = ch.fresh_local(c.list_block_cert());
        let (acc_id, acc) = ch.fresh_local(c.block_cert.clone());
        let body = c.build_nat_lor(head, acc);
        let r = ch.mk_lam(acc_id, BinderInfo::Default, c.block_cert.clone(), body);
        let r = ch.mk_lam(tail_id, BinderInfo::Default, c.list_block_cert(), r);
        let r = ch.mk_lam(head_id, BinderInfo::Default, c.block_cert.clone(), r);
        ch.finish_child(r)
    };

    // List.rec @{1,0} @BlockCert motive nil_case cons_case cs
    let body = Expr::apps(
        c.list_rec_type0.clone(),
        [c.block_cert.clone(), motive, nil_case, cons_case, cs],
    );

    let r = b.mk_lam(cs_id, BinderInfo::Default, c.list_block_cert(), body);
    b.finish(r)
}

/// Build type and proof for `cert_list_composition_trust` (T72b).
///
/// Type: `∀ cs, axiomProfile (listComposeTrust cs) = listComposeTrust cs`
/// Proof: `fun cs => Eq.refl (listComposeTrust cs)` — since `axiomProfile = id`.
fn build_cert_list_composition_trust(c: &T72Consts) -> (Expr, Expr) {
    let theorem_type = {
        let mut b = EnvDeclBuilder::new();
        let (cs_id, cs) = b.fresh_local(c.list_block_cert());
        let lct = Expr::app(c.list_compose_trust.clone(), cs.clone());
        let lhs = c.build_axiom_profile_app(lct.clone());
        let eq = c.build_eq_type(lhs, lct);
        let r = b.mk_pi(cs_id, BinderInfo::Default, c.list_block_cert(), eq);
        b.finish(r)
    };
    let proof_value = {
        let mut b = EnvDeclBuilder::new();
        let (cs_id, cs) = b.fresh_local(c.list_block_cert());
        let lct = Expr::app(c.list_compose_trust.clone(), cs);
        let body = Expr::app(Expr::app(c.eq_refl.clone(), c.nat.clone()), lct);
        let r = b.mk_lam(cs_id, BinderInfo::Default, c.list_block_cert(), body);
        b.finish(r)
    };
    (theorem_type, proof_value)
}

/// Build the type for `cert_pairwise_list_consistent`.
///
/// `∀ c1 c2, axiomProfile (composePair c1 c2) =
///           axiomProfile (listComposeTrust [c1, c2])`
fn build_consistency_type(c: &T72Consts) -> Expr {
    let list_nil = Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]);
    let list_cons = Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]);

    let mut b = EnvDeclBuilder::new();
    let (c1_id, c1) = b.fresh_local(c.block_cert.clone());
    let (c2_id, c2) = b.fresh_local(c.block_cert.clone());

    // LHS: axiomProfile (composePair c1 c2)
    let lhs = c.build_axiom_profile_app(c.build_compose_pair_app(c1.clone(), c2.clone()));

    // RHS: axiomProfile (listComposeTrust [c1, c2])
    // Build [c1, c2] = cons @BlockCert c1 (cons @BlockCert c2 (nil @BlockCert))
    let nil = Expr::app(list_nil, c.block_cert.clone());
    let c2_list = Expr::app(
        Expr::app(Expr::app(list_cons.clone(), c.block_cert.clone()), c2),
        nil,
    );
    let c1c2_list = Expr::app(
        Expr::app(Expr::app(list_cons, c.block_cert.clone()), c1),
        c2_list,
    );
    let rhs = c.build_axiom_profile_app(Expr::app(c.list_compose_trust.clone(), c1c2_list));

    let eq = c.build_eq_type(lhs, rhs);
    let r = b.mk_pi(c2_id, BinderInfo::Default, c.block_cert.clone(), eq);
    let r = b.mk_pi(c1_id, BinderInfo::Default, c.block_cert.clone(), r);
    b.finish(r)
}

#[cfg(test)]
mod tests {
    use crate::env::{ConstantKind, Environment};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_cert_proofs()
            .expect("init_nn_verify_cert_proofs should succeed");
        env
    }

    #[test]
    fn test_list_compose_trust_registered() {
        let env = make_env();
        let lct = env
            .get_const(&Name::from_string("NNVerify.listComposeTrust"))
            .expect("exists");
        assert_eq!(lct.kind, ConstantKind::Definition);
        assert!(lct.value.is_some() && lct.is_reducible);
    }

    #[test]
    fn test_list_compose_trust_type_checks() {
        let env = make_env();
        let lct = env
            .get_const(&Name::from_string("NNVerify.listComposeTrust"))
            .expect("exists");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let val = lct.value.as_ref().expect("value");
        let inferred = tc.infer_type(val).expect("type-check");
        assert!(tc.is_def_eq(&inferred, &lct.type_));
    }

    #[test]
    fn test_cert_list_composition_trust_is_axiom_after_3592() {
        // Post-#3592: cert_list_composition_trust demoted from
        // Declaration::Theorem to Declaration::Axiom. Twin of
        // cert_composition_trust — the Eq.refl proof relied on
        // axiomProfile's reducible identity body, which is now Opaque.
        let env = make_env();
        let thm = env
            .get_const(&Name::from_string("NNVerify.cert_list_composition_trust"))
            .expect("exists");
        assert_eq!(thm.kind, ConstantKind::Axiom);
        assert!(thm.value.is_none(), "axiom must have no stored proof term");
    }

    #[test]
    fn test_cert_list_composition_trust_type_still_type_checks_after_3592() {
        // Post-#3592: even without a stored proof, the Pi type of
        // cert_list_composition_trust must still infer to Prop.
        let env = make_env();
        let thm = env
            .get_const(&Name::from_string("NNVerify.cert_list_composition_trust"))
            .expect("exists");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc.infer_sort(&thm.type_).expect("type should be Prop");
    }

    #[test]
    fn test_nat_lor_zero_left_registered() {
        let env = make_env();
        let ax = env
            .get_const(&Name::from_string("Nat.lor_zero_left"))
            .expect("exists");
        assert_eq!(ax.kind, ConstantKind::Axiom);
    }

    #[test]
    fn test_cert_pairwise_list_consistent_registered() {
        let env = make_env();
        let thm = env
            .get_const(&Name::from_string("NNVerify.cert_pairwise_list_consistent"))
            .expect("exists");
        assert_eq!(thm.kind, ConstantKind::Axiom);
    }

    #[test]
    fn test_cert_pairwise_list_consistent_well_typed() {
        let env = make_env();
        let thm = env
            .get_const(&Name::from_string("NNVerify.cert_pairwise_list_consistent"))
            .expect("exists");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc.infer_sort(&thm.type_).expect("type should be Prop");
    }

    #[test]
    fn test_list_level_init_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_cert_proofs().expect("first init");
        env.init_nn_verify_cert_proofs().expect("second init");
        assert!(env
            .get_const(&Name::from_string("NNVerify.listComposeTrust"))
            .is_some());
        assert!(env
            .get_const(&Name::from_string("NNVerify.cert_list_composition_trust"))
            .is_some());
        assert!(env
            .get_const(&Name::from_string("NNVerify.cert_pairwise_list_consistent"))
            .is_some());
    }
}
