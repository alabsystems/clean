// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Nat.not_succ_lt_zero`.
//!
//! `Nat.lt a b` reduces to `Nat.le (Nat.succ a) b`, so the theorem
//! `forall n, Nat.lt (Nat.succ n) Nat.zero -> False` is the impossible
//! lower-bound case `Nat.le (Nat.succ (Nat.succ n)) Nat.zero -> False`.
//!
//! The proof eliminates the `Nat.le` evidence with motive
//! `fun t _ => Eq Nat t Nat.zero -> False`, then applies the resulting
//! contradiction to `Eq.refl Nat.zero`. Both the refl and step minors close
//! by `Nat.noConfusion` on a hypothetical equality
//! `Eq Nat (Nat.succ k) Nat.zero`.
//!
//! This removes a checked base-case axiom on the path to `Nat.lt_irrefl`
//! (#3599). The remaining full `Nat.lt_irrefl` proof still needs a
//! constructive predecessor-inversion theorem for `Nat.le`.

use super::decl_builder::EnvDeclBuilder;
use super::order::nat_lt_tc;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

fn nat_succ_of(nat_succ: &Expr, value: Expr) -> Expr {
    Expr::app(nat_succ.clone(), value)
}

fn nat_le_of(nat_le: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(nat_le.clone(), [lhs, rhs])
}

fn nat_eq_of(eq_const: &Expr, nat_const: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(eq_const.clone(), [nat_const.clone(), lhs, rhs])
}

fn nat_succ_ne_zero_from_eq(
    nat_no_confusion: &Expr,
    false_const: &Expr,
    nat_succ: &Expr,
    nat_zero: &Expr,
    n: Expr,
    h: Expr,
) -> Expr {
    Expr::apps(
        nat_no_confusion.clone(),
        [
            false_const.clone(),
            nat_succ_of(nat_succ, n),
            nat_zero.clone(),
            h,
        ],
    )
}

impl Environment {
    /// Register `Nat.not_succ_lt_zero` as a kernel-checked theorem.
    ///
    /// The legacy declaration lives in `order_lemmas_succ.rs`; that site
    /// skips its axiom registration once this theorem is present.
    pub(crate) fn register_nat_not_succ_lt_zero_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.not_succ_lt_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_eq()?;
        self.init_nat()?;
        if self
            .get_const(&Name::from_string("Nat.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }
        self.init_lt()?;
        self.init_true_false()?;

        let type1 = Level::succ(Level::zero());
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_rec = Expr::const_(Name::from_string("Nat.le.rec"), vec![]);
        let nat_no_confusion =
            Expr::const_(Name::from_string("Nat.noConfusion"), vec![Level::zero()]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());
        let succ_n = nat_succ_of(&nat_succ, n.clone());
        let h_type = nat_lt_tc(succ_n.clone(), nat_zero.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());

        let type_ = {
            let e = b.mk_pi(
                h_id,
                BinderInfo::Default,
                h_type.clone(),
                false_const.clone(),
            );
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        let lower = nat_succ_of(&nat_succ, succ_n.clone());

        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(nat_const.clone());
            let le_lower_t = nat_le_of(&nat_le, lower.clone(), t.clone());
            let (ht_id, _ht) = mb.fresh_local(le_lower_t.clone());
            let eq_t_zero = nat_eq_of(&eq_const, &nat_const, t.clone(), nat_zero.clone());
            let (heq_id, _heq) = mb.fresh_local(eq_t_zero.clone());
            let contradiction =
                mb.mk_pi(heq_id, BinderInfo::Default, eq_t_zero, false_const.clone());
            let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_lower_t, contradiction);
            let lam_t = mb.mk_lam(t_id, BinderInfo::Default, nat_const.clone(), lam_h);
            mb.finish_child(lam_t)
        };

        let minor_refl = {
            let mut rb = EnvDeclBuilder::child_of(&b);
            let eq_lower_zero = nat_eq_of(&eq_const, &nat_const, lower.clone(), nat_zero.clone());
            let (heq_id, heq) = rb.fresh_local(eq_lower_zero.clone());
            let body = nat_succ_ne_zero_from_eq(
                &nat_no_confusion,
                &false_const,
                &nat_succ,
                &nat_zero,
                succ_n.clone(),
                heq,
            );
            let lam = rb.mk_lam(heq_id, BinderInfo::Default, eq_lower_zero, body);
            rb.finish_child(lam)
        };

        let minor_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = sb.fresh_local(nat_const.clone());
            let le_lower_t = nat_le_of(&nat_le, lower.clone(), t.clone());
            let (ht_id, _ht) = sb.fresh_local(le_lower_t.clone());
            let ih_type = {
                let eq_t_zero = nat_eq_of(&eq_const, &nat_const, t.clone(), nat_zero.clone());
                let (heq_id, _heq) = sb.fresh_local(eq_t_zero.clone());
                sb.mk_pi(heq_id, BinderInfo::Default, eq_t_zero, false_const.clone())
            };
            let (ih_id, _ih) = sb.fresh_local(ih_type.clone());
            let succ_t = nat_succ_of(&nat_succ, t.clone());
            let eq_succ_t_zero = nat_eq_of(&eq_const, &nat_const, succ_t.clone(), nat_zero.clone());
            let (heq_id, heq) = sb.fresh_local(eq_succ_t_zero.clone());
            let body = nat_succ_ne_zero_from_eq(
                &nat_no_confusion,
                &false_const,
                &nat_succ,
                &nat_zero,
                t.clone(),
                heq,
            );
            let lam_heq = sb.mk_lam(heq_id, BinderInfo::Default, eq_succ_t_zero, body);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, lam_heq);
            let lam_h = sb.mk_lam(ht_id, BinderInfo::Default, le_lower_t, lam_ih);
            let lam_t = sb.mk_lam(t_id, BinderInfo::Implicit, nat_const.clone(), lam_h);
            sb.finish_child(lam_t)
        };

        let rec_app = Expr::apps(
            nat_le_rec,
            [
                lower,
                motive,
                minor_refl,
                minor_step,
                nat_zero.clone(),
                h.clone(),
            ],
        );
        let zero_refl = Expr::apps(eq_refl, [nat_const.clone(), nat_zero.clone()]);
        let body = Expr::app(rec_app, zero_refl);

        let value = {
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const, e);
            b.finish(e)
        };

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
    use crate::tc::TypeChecker;

    #[test]
    fn test_nat_not_succ_lt_zero_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_not_succ_lt_zero_theorem()
            .expect("Nat.not_succ_lt_zero theorem registers");

        let info = env
            .get_const(&Name::from_string("Nat.not_succ_lt_zero"))
            .expect("Nat.not_succ_lt_zero should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some());

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("Nat.not_succ_lt_zero"),
                vec![],
            ))
            .expect("Nat.not_succ_lt_zero should type-check");
    }

    #[test]
    fn test_nat_not_succ_lt_zero_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.register_nat_not_succ_lt_zero_theorem()
            .expect("Nat.not_succ_lt_zero theorem registers");

        let deps = env
            .axiom_deps(&Name::from_string("Nat.not_succ_lt_zero"))
            .expect("axiom_deps should succeed");
        assert!(
            deps.is_empty(),
            "Nat.not_succ_lt_zero must have empty axiom closure, got {deps:?}"
        );
        assert_eq!(
            env.proof_quality(&Name::from_string("Nat.not_succ_lt_zero"))
                .expect("proof quality should compute"),
            ProofQuality::Constructive
        );
    }
}
