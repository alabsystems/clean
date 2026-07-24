// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive predecessor-inversion support for `Nat.le`.
//!
//! This module removes the `Nat.le_of_succ_le_succ` axiom by proving it from
//! the `Nat.le` recursor and constructor disjointness. The proof first adds
//! `Nat.not_succ_le_zero`, the zero-target impossibility needed by the step
//! case. Together these are the direct predecessor-inversion support needed
//! for the remaining `Nat.lt_irrefl` proof debt (#3599).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

fn nat_succ(nat_succ: &Expr, value: Expr) -> Expr {
    Expr::app(nat_succ.clone(), value)
}

fn nat_le(nat_le: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(nat_le.clone(), [lhs, rhs])
}

fn nat_eq(eq_const: &Expr, nat_const: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(eq_const.clone(), [nat_const.clone(), lhs, rhs])
}

fn p_of_t(
    nat_cases_on: &Expr,
    nat_const: &Expr,
    nat_le_const: &Expr,
    false_const: &Expr,
    n: Expr,
    t: Expr,
) -> Expr {
    let motive = Expr::lam(BinderInfo::Default, nat_const.clone(), Expr::prop());
    let succ_minor = Expr::lam(
        BinderInfo::Default,
        nat_const.clone(),
        nat_le(nat_le_const, n, Expr::bvar(0)),
    );
    // Lean-faithful casesOn order: motive, major, then minors.
    Expr::apps(
        nat_cases_on.clone(),
        [motive, t, false_const.clone(), succ_minor],
    )
}

fn succ_ne_zero_from_eq(
    nat_no_confusion: &Expr,
    false_const: &Expr,
    nat_succ_const: &Expr,
    nat_zero: &Expr,
    n: Expr,
    h: Expr,
) -> Expr {
    Expr::apps(
        nat_no_confusion.clone(),
        [
            false_const.clone(),
            nat_succ(nat_succ_const, n),
            nat_zero.clone(),
            h,
        ],
    )
}

impl Environment {
    /// Register `Nat.not_succ_le_zero : forall n, Nat.le (Nat.succ n) Nat.zero -> False`.
    pub(crate) fn register_nat_not_succ_le_zero_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.not_succ_le_zero");
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
        self.init_le()?;
        self.init_true_false()?;

        let type1 = Level::succ(Level::zero());
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ_const = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le_const = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_rec = Expr::const_(Name::from_string("Nat.le.rec"), vec![]);
        let nat_no_confusion =
            Expr::const_(Name::from_string("Nat.noConfusion"), vec![Level::zero()]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());
        let lower = nat_succ(&nat_succ_const, n.clone());
        let h_type = nat_le(&nat_le_const, lower.clone(), nat_zero.clone());
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

        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(nat_const.clone());
            let le_lower_t = nat_le(&nat_le_const, lower.clone(), t.clone());
            let (ht_id, _ht) = mb.fresh_local(le_lower_t.clone());
            let eq_t_zero = nat_eq(&eq_const, &nat_const, t.clone(), nat_zero.clone());
            let (heq_id, _heq) = mb.fresh_local(eq_t_zero.clone());
            let contradiction =
                mb.mk_pi(heq_id, BinderInfo::Default, eq_t_zero, false_const.clone());
            let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_lower_t, contradiction);
            let lam_t = mb.mk_lam(t_id, BinderInfo::Default, nat_const.clone(), lam_h);
            mb.finish_child(lam_t)
        };

        let minor_refl = {
            let mut rb = EnvDeclBuilder::child_of(&b);
            let eq_lower_zero = nat_eq(&eq_const, &nat_const, lower.clone(), nat_zero.clone());
            let (heq_id, heq) = rb.fresh_local(eq_lower_zero.clone());
            let body = succ_ne_zero_from_eq(
                &nat_no_confusion,
                &false_const,
                &nat_succ_const,
                &nat_zero,
                n.clone(),
                heq,
            );
            let lam = rb.mk_lam(heq_id, BinderInfo::Default, eq_lower_zero, body);
            rb.finish_child(lam)
        };

        let minor_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = sb.fresh_local(nat_const.clone());
            let le_lower_t = nat_le(&nat_le_const, lower.clone(), t.clone());
            let (ht_id, _ht) = sb.fresh_local(le_lower_t.clone());
            let ih_type = {
                let eq_t_zero = nat_eq(&eq_const, &nat_const, t.clone(), nat_zero.clone());
                let (heq_id, _heq) = sb.fresh_local(eq_t_zero.clone());
                sb.mk_pi(heq_id, BinderInfo::Default, eq_t_zero, false_const.clone())
            };
            let (ih_id, _ih) = sb.fresh_local(ih_type.clone());
            let succ_t = nat_succ(&nat_succ_const, t.clone());
            let eq_succ_t_zero = nat_eq(&eq_const, &nat_const, succ_t, nat_zero.clone());
            let (heq_id, heq) = sb.fresh_local(eq_succ_t_zero.clone());
            let body = succ_ne_zero_from_eq(
                &nat_no_confusion,
                &false_const,
                &nat_succ_const,
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

    /// Register `Nat.le_of_succ_le_succ` as a kernel-checked predecessor inversion theorem.
    pub(crate) fn register_nat_le_of_succ_le_succ_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_of_succ_le_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_le()?;
        self.init_true_false()?;
        self.register_nat_not_succ_le_zero_theorem()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ_const = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le_const = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        let nat_le_rec = Expr::const_(Name::from_string("Nat.le.rec"), vec![]);
        // SOUNDNESS: this proof uses Nat.casesOn at TWO different motive universes.
        // `nat_cases_on` (.{0}) is for motives returning a PROPOSITION (Nat -> Prop).
        // `nat_cases_on_type` (.{1}) is for `p_of_t`'s motive `fun n => Prop`, which
        // returns the Prop UNIVERSE and so is Nat -> Type 0. Sharing one binding was
        // ill-typed and only passed before because the nested argument check was
        // skipped (the kernel soundness hole this branch fixes).
        let nat_cases_on = Expr::const_(Name::from_string("Nat.casesOn"), vec![Level::zero()]);
        let nat_cases_on_type = Expr::const_(
            Name::from_string("Nat.casesOn"),
            vec![Level::succ(Level::zero())],
        );
        let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
        let not_succ_le_zero = Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());
        let (m_id, m) = b.fresh_local(nat_const.clone());
        let succ_n = nat_succ(&nat_succ_const, n.clone());
        let succ_m = nat_succ(&nat_succ_const, m.clone());
        let h_type = nat_le(&nat_le_const, succ_n.clone(), succ_m.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());

        let type_ = {
            let conclusion = nat_le(&nat_le_const, n.clone(), m.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), conclusion);
            let e = b.mk_pi(m_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(nat_const.clone());
            let le_sn_t = nat_le(&nat_le_const, succ_n.clone(), t.clone());
            let (ht_id, _ht) = mb.fresh_local(le_sn_t.clone());
            let body = p_of_t(
                &nat_cases_on_type,
                &nat_const,
                &nat_le_const,
                &false_const,
                n.clone(),
                t,
            );
            let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_sn_t, body);
            let lam_t = mb.mk_lam(t_id, BinderInfo::Default, nat_const.clone(), lam_h);
            mb.finish_child(lam_t)
        };

        let minor_refl = Expr::app(nat_le_refl, n.clone());

        let minor_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = sb.fresh_local(nat_const.clone());
            let le_sn_t = nat_le(&nat_le_const, succ_n.clone(), t.clone());
            let (ht_id, ht) = sb.fresh_local(le_sn_t.clone());
            let ih_type = p_of_t(
                &nat_cases_on_type,
                &nat_const,
                &nat_le_const,
                &false_const,
                n.clone(),
                t.clone(),
            );
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());

            let step_motive = {
                let mut cmb = EnvDeclBuilder::child_of(&sb);
                let (x_id, x) = cmb.fresh_local(nat_const.clone());
                let le_sn_x = nat_le(&nat_le_const, succ_n.clone(), x.clone());
                let (hx_id, _hx) = cmb.fresh_local(le_sn_x.clone());
                let px = p_of_t(
                    &nat_cases_on_type,
                    &nat_const,
                    &nat_le_const,
                    &false_const,
                    n.clone(),
                    x.clone(),
                );
                let (ihx_id, _ihx) = cmb.fresh_local(px.clone());
                let psucc_x = p_of_t(
                    &nat_cases_on_type,
                    &nat_const,
                    &nat_le_const,
                    &false_const,
                    n.clone(),
                    nat_succ(&nat_succ_const, x),
                );
                let e = cmb.mk_pi(ihx_id, BinderInfo::Default, px, psucc_x);
                let e = cmb.mk_pi(hx_id, BinderInfo::Default, le_sn_x, e);
                let e = cmb.mk_lam(x_id, BinderInfo::Default, nat_const.clone(), e);
                cmb.finish_child(e)
            };

            let zero_case = {
                let mut zb = EnvDeclBuilder::child_of(&sb);
                let le_sn_zero = nat_le(&nat_le_const, succ_n.clone(), nat_zero.clone());
                let (hz_id, hz) = zb.fresh_local(le_sn_zero.clone());
                let (ihz_id, _ihz) = zb.fresh_local(false_const.clone());
                let target = nat_le(&nat_le_const, n.clone(), nat_zero.clone());
                let contradiction = Expr::apps(not_succ_le_zero.clone(), [n.clone(), hz]);
                let body = Expr::apps(false_elim.clone(), [target, contradiction]);
                let e = zb.mk_lam(ihz_id, BinderInfo::Default, false_const.clone(), body);
                let e = zb.mk_lam(hz_id, BinderInfo::Default, le_sn_zero, e);
                zb.finish_child(e)
            };

            let succ_case = {
                let mut cb = EnvDeclBuilder::child_of(&sb);
                let (k_id, k) = cb.fresh_local(nat_const.clone());
                let succ_k = nat_succ(&nat_succ_const, k.clone());
                let le_sn_succ_k = nat_le(&nat_le_const, succ_n.clone(), succ_k.clone());
                let (hk_id, _hk) = cb.fresh_local(le_sn_succ_k.clone());
                let ihk_type = nat_le(&nat_le_const, n.clone(), k.clone());
                let (ihk_id, ihk) = cb.fresh_local(ihk_type.clone());
                let body = Expr::apps(nat_le_step.clone(), [n.clone(), k, ihk]);
                let e = cb.mk_lam(ihk_id, BinderInfo::Default, ihk_type, body);
                let e = cb.mk_lam(hk_id, BinderInfo::Default, le_sn_succ_k, e);
                let e = cb.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), e);
                cb.finish_child(e)
            };

            // Lean-faithful casesOn order: motive, major, then minors.
            let cases = Expr::apps(nat_cases_on, [step_motive, t, zero_case, succ_case]);
            let body = Expr::apps(cases, [ht, ih]);
            let e = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let e = sb.mk_lam(ht_id, BinderInfo::Default, le_sn_t, e);
            let e = sb.mk_lam(t_id, BinderInfo::Implicit, nat_const.clone(), e);
            sb.finish_child(e)
        };

        let body = Expr::apps(
            nat_le_rec,
            [succ_n, motive, minor_refl, minor_step, succ_m, h.clone()],
        );

        let value = {
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, body);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), e);
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
    fn test_nat_le_inversion_theorems_register_as_theorems() {
        let mut env = Environment::new();
        env.register_nat_le_of_succ_le_succ_theorem()
            .expect("Nat.le_of_succ_le_succ theorem registers");

        for target in ["Nat.not_succ_le_zero", "Nat.le_of_succ_le_succ"] {
            let info = env
                .get_const(&Name::from_string(target))
                .unwrap_or_else(|| panic!("{target} should be registered"));
            assert_eq!(info.kind, ConstantKind::Theorem);
            assert!(info.value.is_some());

            let tc = TypeChecker::with_mode(&env, env.mode());
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(target), vec![]))
                .unwrap_or_else(|err| panic!("{target} should type-check: {err:?}"));

            assert_eq!(
                env.proof_quality(&Name::from_string(target))
                    .expect("proof quality should compute"),
                ProofQuality::Constructive
            );
        }
    }
}
