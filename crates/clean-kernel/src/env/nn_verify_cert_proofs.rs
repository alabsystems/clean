// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Grounded formal proofs for NN verification certificate theorems (T72).
//!
//! Grounds `BlockCert`, `axiomProfile`, `composePair`, and
//! `CertificateEntry` as reducible definitions over `Nat` / `Nat.lor`.
//! See `nn_verify_cert_proofs_list` for list-level composition (T72b).
//!
//! Part of #3220, #3247.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constant expressions for T72 proof construction.
pub(super) struct T72Consts {
    pub(super) nat: Expr,
    pub(super) nat_zero: Expr,
    pub(super) block_cert: Expr,
    pub(super) axiom_profile: Expr,
    pub(super) compose_pair: Expr,
    pub(super) nat_lor: Expr,
    pub(super) eq_const: Expr,
    pub(super) eq_refl: Expr,
    pub(super) list: Expr,
    pub(super) list_rec_type0: Expr,
    pub(super) list_compose_trust: Expr,
}

impl T72Consts {
    pub(super) fn new() -> Self {
        let eq_u = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            block_cert: Expr::const_(Name::from_string("NNVerify.BlockCert"), vec![]),
            axiom_profile: Expr::const_(
                Name::from_string("NNVerify.BlockCert.axiomProfile"),
                vec![],
            ),
            compose_pair: Expr::const_(Name::from_string("NNVerify.composePair"), vec![]),
            nat_lor: Expr::const_(Name::from_string("Nat.lor"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![eq_u.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![eq_u]),
            list: Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            list_rec_type0: Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(Level::zero()), Level::zero()],
            ),
            list_compose_trust: Expr::const_(
                Name::from_string("NNVerify.listComposeTrust"),
                vec![],
            ),
        }
    }

    pub(super) fn build_nat_lor(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_lor.clone(), lhs), rhs)
    }

    pub(super) fn build_axiom_profile_app(&self, cert: Expr) -> Expr {
        Expr::app(self.axiom_profile.clone(), cert)
    }

    pub(super) fn build_compose_pair_app(&self, c1: Expr, c2: Expr) -> Expr {
        Expr::app(Expr::app(self.compose_pair.clone(), c1), c2)
    }

    pub(super) fn build_eq_type(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq_const.clone(), self.nat.clone()), lhs),
            rhs,
        )
    }

    pub(super) fn list_block_cert(&self) -> Expr {
        Expr::app(self.list.clone(), self.block_cert.clone())
    }
}

impl Environment {
    /// Register T72 pairwise + list-level + CertificateEntry grounding.
    ///
    /// Delegates list-level registrations to `nn_verify_cert_proofs_list`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub fn init_nn_verify_cert_proofs(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_nat()?;
        self.init_list()?;

        self.register_nat_lor_grounded()?;
        self.register_block_cert_types_grounded()?;
        self.register_certificate_entry_grounded()?;
        self.register_cert_composition_trust_grounded()?;
        // List-level and consistency (in nn_verify_cert_proofs_list.rs)
        self.register_list_compose_trust_grounded()?;
        self.register_cert_list_composition_trust_grounded()?;
        self.register_cert_pairwise_list_consistent()
    }

    fn register_nat_lor_grounded(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Nat.lor")).is_some() {
            return Ok(());
        }
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let lor_type = Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(BinderInfo::Default, nat.clone(), nat),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.lor"),
            level_params: vec![],
            type_: lor_type,
        })
    }

    fn register_block_cert_types_grounded(&mut self) -> Result<(), EnvError> {
        let c = T72Consts::new();
        let type0 = Expr::sort(Level::succ(Level::zero()));

        if self
            .get_const(&Name::from_string("NNVerify.BlockCert"))
            .is_none()
        {
            // #3592 (Branch A) — `BlockCert` stays a reducible Definition
            // aliasing `Nat`. Per R10 Finding 1 and
            // designs/2026-04-19-demasquerade-cxxx-pattern.md, the
            // T72 δ-collapse chain is closed by flipping `axiomProfile`
            // to Opaque (the argument-discarding identity carrier), not
            // by opacifying `BlockCert`. Demoting `BlockCert` to Opaque
            // would break `axiomProfile`'s own body type-check (a
            // `BlockCert` local returned where `Nat` is expected requires
            // δ-unfolding of `BlockCert = Nat`).
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNVerify.BlockCert"),
                level_params: vec![],
                type_: type0,
                value: c.nat.clone(),
                is_reducible: true,
            })?;
        }
        self.register_axiom_profile_def(&c)?;
        self.register_compose_pair_def(&c)
    }

    fn register_axiom_profile_def(&mut self, c: &T72Consts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.BlockCert.axiomProfile"))
            .is_some()
        {
            return Ok(());
        }
        let profile_type = Expr::pi(BinderInfo::Default, c.block_cert.clone(), c.nat.clone());
        let profile_value = {
            let mut b = EnvDeclBuilder::new();
            let (cert_id, cert) = b.fresh_local(c.block_cert.clone());
            let r = b.mk_lam(cert_id, BinderInfo::Default, c.block_cert.clone(), cert);
            b.finish(r)
        };
        // SOUNDNESS: #3592 — Branch A co-demotion. `axiomProfile` was a
        // reducible `Declaration::Definition` with argument-discarding
        // identity body `fun cert => cert`. Under δ-reduction the head
        // `axiomProfile (…)` collapsed to its argument, making
        // `cert_composition_trust` (`∀ c1 c2, axiomProfile (composePair c1 c2)
        // = Nat.lor (axiomProfile c1) (axiomProfile c2)`) reduce to the
        // tautology `Nat.lor c1 c2 = Nat.lor c1 c2` — rule M2 (identity
        // carrier). Flipped to `Declaration::Opaque` (same body) so the
        // δ path is closed. Genuine axiom-profile semantics (`Finset Name`
        // / bitset over axiom indices) are out of scope for kernel work.
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.BlockCert.axiomProfile"),
            level_params: vec![],
            type_: profile_type,
            value: profile_value,
        })
    }

    fn register_compose_pair_def(&mut self, c: &T72Consts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.composePair"))
            .is_some()
        {
            return Ok(());
        }
        let compose_type = Expr::pi(
            BinderInfo::Default,
            c.block_cert.clone(),
            Expr::pi(
                BinderInfo::Default,
                c.block_cert.clone(),
                c.block_cert.clone(),
            ),
        );
        let compose_value = {
            let mut b = EnvDeclBuilder::new();
            let (c1_id, c1) = b.fresh_local(c.block_cert.clone());
            let (c2_id, c2) = b.fresh_local(c.block_cert.clone());
            let body = c.build_nat_lor(c1, c2);
            let r = b.mk_lam(c2_id, BinderInfo::Default, c.block_cert.clone(), body);
            let r = b.mk_lam(c1_id, BinderInfo::Default, c.block_cert.clone(), r);
            b.finish(r)
        };
        // SOUNDNESS: #3592 — Branch A co-demotion. `composePair` was a
        // reducible `Declaration::Definition` with body
        // `fun c1 c2 => Nat.lor c1 c2`. The M1 alias chain (BlockCert → Nat,
        // axiomProfile = id, composePair = Nat.lor) let `Eq.refl` close
        // `cert_composition_trust`. Flipped to `Declaration::Opaque` (same
        // body) so `composePair c1 c2` no longer δ-unfolds to
        // `Nat.lor c1 c2`, closing the last δ-path any future masquerade
        // could ride.
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.composePair"),
            level_params: vec![],
            type_: compose_type,
            value: compose_value,
        })
    }

    /// Register `CertificateEntry` grounded to Rust `CertificateEntry`.
    fn register_certificate_entry_grounded(&mut self) -> Result<(), EnvError> {
        let c = T72Consts::new();
        let type0 = Expr::sort(Level::succ(Level::zero()));
        let cert_entry = Expr::const_(Name::from_string("NNVerify.CertificateEntry"), vec![]);

        if self
            .get_const(&Name::from_string("NNVerify.CertificateEntry"))
            .is_none()
        {
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNVerify.CertificateEntry"),
                level_params: vec![],
                type_: type0,
                value: c.block_cert.clone(),
                is_reducible: true,
            })?;
        }
        self.register_cert_entry_mk(&c, &cert_entry)?;
        self.register_cert_entry_proj(&c, &cert_entry)
    }

    fn register_cert_entry_mk(&mut self, c: &T72Consts, ce: &Expr) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.CertificateEntry.mk"))
            .is_some()
        {
            return Ok(());
        }
        let mk_type = Expr::pi(BinderInfo::Default, c.block_cert.clone(), ce.clone());
        let mk_value = {
            let mut b = EnvDeclBuilder::new();
            let (ap_id, ap) = b.fresh_local(c.block_cert.clone());
            let r = b.mk_lam(ap_id, BinderInfo::Default, c.block_cert.clone(), ap);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.CertificateEntry.mk"),
            level_params: vec![],
            type_: mk_type,
            value: mk_value,
            is_reducible: true,
        })
    }

    fn register_cert_entry_proj(&mut self, c: &T72Consts, ce: &Expr) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "NNVerify.CertificateEntry.axiom_profile",
            ))
            .is_some()
        {
            return Ok(());
        }
        let proj_type = Expr::pi(BinderInfo::Default, ce.clone(), c.block_cert.clone());
        let proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (ce_id, ce_var) = b.fresh_local(ce.clone());
            let r = b.mk_lam(ce_id, BinderInfo::Default, ce.clone(), ce_var);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.CertificateEntry.axiom_profile"),
            level_params: vec![],
            type_: proj_type,
            value: proj_value,
            is_reducible: true,
        })
    }

    fn register_cert_composition_trust_grounded(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.cert_composition_trust"))
            .is_some()
        {
            return Ok(());
        }
        let c = T72Consts::new();
        let theorem_type = {
            let mut b = EnvDeclBuilder::new();
            let (c1_id, c1) = b.fresh_local(c.block_cert.clone());
            let (c2_id, c2) = b.fresh_local(c.block_cert.clone());
            let lhs = c.build_axiom_profile_app(c.build_compose_pair_app(c1.clone(), c2.clone()));
            let rhs = c.build_nat_lor(c.build_axiom_profile_app(c1), c.build_axiom_profile_app(c2));
            let eq_expr = c.build_eq_type(lhs, rhs);
            let r = b.mk_pi(c2_id, BinderInfo::Default, c.block_cert.clone(), eq_expr);
            let r = b.mk_pi(c1_id, BinderInfo::Default, c.block_cert.clone(), r);
            b.finish(r)
        };
        // SOUNDNESS: #3592 — Branch A demotion. Proof was `Eq.refl` over
        // the reducible `axiomProfile` / `composePair` / `BlockCert`
        // alias chain (rules M1 alias-collapse + M2 identity carrier +
        // M4 Eq.refl root — see
        // designs/2026-04-19-demasquerade-cxxx-pattern.md and
        // reports/audit/2026-04-20-r10-wave8-masquerade-sweep.md Finding 1).
        // Genuine composition soundness requires real axiom-profile
        // semantics (a `Finset Name` / bitset over an indexed axiom
        // enumeration, not a raw `Nat`); out of scope for kernel work.
        // The carriers `axiomProfile` and `composePair` are flipped
        // to `Declaration::Opaque` in the same commit so this masquerade
        // cannot be reintroduced.
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.cert_composition_trust"),
            level_params: vec![],
            type_: theorem_type,
        })
    }
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
    fn test_block_cert_registered() {
        let env = make_env();
        let bc = env
            .get_const(&Name::from_string("NNVerify.BlockCert"))
            .expect("exists");
        assert_eq!(bc.kind, ConstantKind::Definition);
        assert!(bc.value.is_some() && bc.is_reducible);
    }

    #[test]
    fn test_axiom_profile_registered_after_3592() {
        // Post-#3592: axiomProfile flipped from reducible Definition to
        // Opaque (body unchanged) as Branch A co-demotion. Value is
        // retained, `is_reducible` is false, kind is Opaque.
        let env = make_env();
        let ap = env
            .get_const(&Name::from_string("NNVerify.BlockCert.axiomProfile"))
            .expect("exists");
        assert_eq!(ap.kind, ConstantKind::Opaque);
        assert!(ap.value.is_some());
        assert!(
            !ap.is_reducible,
            "axiomProfile must not be reducible post-#3592"
        );
    }

    #[test]
    fn test_compose_pair_registered_after_3592() {
        // Post-#3592: composePair flipped from reducible Definition to
        // Opaque (body unchanged) as Branch A co-demotion.
        let env = make_env();
        let cp = env
            .get_const(&Name::from_string("NNVerify.composePair"))
            .expect("exists");
        assert_eq!(cp.kind, ConstantKind::Opaque);
        assert!(cp.value.is_some());
        assert!(
            !cp.is_reducible,
            "composePair must not be reducible post-#3592"
        );
    }

    #[test]
    fn test_compose_pair_axiom_removed() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.composePair_axiomProfile"))
            .is_none());
    }

    #[test]
    fn test_cert_composition_trust_is_axiom_after_3592() {
        // Post-#3592: cert_composition_trust demoted from Declaration::Theorem
        // to Declaration::Axiom (no stored proof term) on its original Pi type.
        // The type must still type-check (infer_sort -> Prop).
        let env = make_env();
        let thm = env
            .get_const(&Name::from_string("NNVerify.cert_composition_trust"))
            .expect("exists");
        assert_eq!(thm.kind, ConstantKind::Axiom);
        assert!(thm.value.is_none(), "axiom must have no stored proof term");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_sort(&thm.type_)
            .expect("type should still be Prop");
    }

    #[test]
    fn test_certificate_entry_registered() {
        let env = make_env();
        let ce = env
            .get_const(&Name::from_string("NNVerify.CertificateEntry"))
            .expect("exists");
        assert_eq!(ce.kind, ConstantKind::Definition);
        assert!(ce.is_reducible);
    }

    #[test]
    fn test_certificate_entry_mk_type_checks() {
        let env = make_env();
        let mk = env
            .get_const(&Name::from_string("NNVerify.CertificateEntry.mk"))
            .expect("exists");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let val = mk.value.as_ref().expect("value");
        let inferred = tc.infer_type(val).expect("type-check");
        assert!(tc.is_def_eq(&inferred, &mk.type_));
    }

    #[test]
    fn test_certificate_entry_proj_type_checks() {
        let env = make_env();
        let p = env
            .get_const(&Name::from_string(
                "NNVerify.CertificateEntry.axiom_profile",
            ))
            .expect("exists");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let val = p.value.as_ref().expect("value");
        let inferred = tc.infer_type(val).expect("type-check");
        assert!(tc.is_def_eq(&inferred, &p.type_));
    }

    #[test]
    fn test_init_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_cert_proofs().expect("first init");
        env.init_nn_verify_cert_proofs().expect("second init");
    }
}
