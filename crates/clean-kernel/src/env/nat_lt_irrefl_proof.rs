// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Nat.lt_irrefl`.
//!
//! `Nat.lt a a` reduces to `Nat.le (Nat.succ a) a`. The zero case closes
//! with `Nat.not_succ_le_zero`; the successor case strips one successor from
//! the `Nat.le` evidence with `Nat.le_of_succ_le_succ` and applies the
//! induction hypothesis.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

fn nat_succ(nat_succ: &Expr, value: Expr) -> Expr {
    Expr::app(nat_succ.clone(), value)
}

fn nat_lt(nat_lt: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(nat_lt.clone(), [lhs, rhs])
}

impl Environment {
    /// Register `Nat.lt_irrefl : forall a : Nat, Nat.lt a a -> False`.
    pub(crate) fn register_nat_lt_irrefl_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_irrefl");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_lt()?;
        self.init_true_false()?;
        self.register_nat_not_succ_le_zero_theorem()?;
        self.register_nat_le_of_succ_le_succ_theorem()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ_const = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_lt_const = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let not_succ_le_zero = Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]);
        let le_of_succ_le_succ = Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_const.clone());
        let lt_aa = nat_lt(&nat_lt_const, a.clone(), a.clone());
        let (h_id, _h) = b.fresh_local(lt_aa.clone());

        let type_ = {
            let e = b.mk_pi(
                h_id,
                BinderInfo::Default,
                lt_aa.clone(),
                false_const.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(nat_const.clone());
            let lt_tt = nat_lt(&nat_lt_const, t.clone(), t.clone());
            let (ht_id, _ht) = mb.fresh_local(lt_tt.clone());
            let body = mb.mk_pi(ht_id, BinderInfo::Default, lt_tt, false_const.clone());
            let lam = mb.mk_lam(t_id, BinderInfo::Default, nat_const.clone(), body);
            mb.finish_child(lam)
        };

        let base = {
            let mut bb = EnvDeclBuilder::child_of(&b);
            let lt_zero_zero = nat_lt(&nat_lt_const, nat_zero.clone(), nat_zero.clone());
            let (h0_id, h0) = bb.fresh_local(lt_zero_zero.clone());
            let body = Expr::apps(not_succ_le_zero.clone(), [nat_zero.clone(), h0]);
            let lam = bb.mk_lam(h0_id, BinderInfo::Default, lt_zero_zero, body);
            bb.finish_child(lam)
        };

        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(nat_const.clone());

            let lt_kk = nat_lt(&nat_lt_const, k.clone(), k.clone());
            let (ih_arg_id, _ih_arg) = sb.fresh_local(lt_kk.clone());
            let ih_type = sb.mk_pi(
                ih_arg_id,
                BinderInfo::Default,
                lt_kk.clone(),
                false_const.clone(),
            );
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());

            let succ_k = nat_succ(&nat_succ_const, k.clone());
            let lt_succ_succ = nat_lt(&nat_lt_const, succ_k.clone(), succ_k.clone());
            let (h_id, h) = sb.fresh_local(lt_succ_succ.clone());
            let predecessor = Expr::apps(le_of_succ_le_succ, [succ_k, k.clone(), h]);
            let body = Expr::app(ih, predecessor);

            let e = sb.mk_lam(h_id, BinderInfo::Default, lt_succ_succ, body);
            let e = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, e);
            let e = sb.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), e);
            sb.finish_child(e)
        };

        let value = {
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let body = Expr::apps(nat_rec, [motive, base, step, a]);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat_const, body);
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
    fn test_nat_lt_irrefl_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_nat_lt_irrefl_theorem()
            .expect("Nat.lt_irrefl theorem registers");

        let info = env
            .get_const(&Name::from_string("Nat.lt_irrefl"))
            .expect("Nat.lt_irrefl should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some());

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]))
            .expect("Nat.lt_irrefl should type-check");

        assert_eq!(
            env.proof_quality(&Name::from_string("Nat.lt_irrefl"))
                .expect("proof quality should compute"),
            ProofQuality::Constructive
        );
    }
}
