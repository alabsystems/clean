// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive `if_pos` / `if_neg` — the two defining reduction lemmas for
//! `ite` under a *decided* (but possibly symbolic-instance) condition. Real
//! kernel-checked terms (NO `sorry`, NO axiom).
//!
//! The binder telescope MATCHES Lean 4 exactly (`Init/Core.lean:932,937`):
//!
//! ```text
//! if_pos : {c : Prop} → {h : Decidable c} → (hc : c) →
//!          {α : Sort u} → {t e : α} → @ite α c h t e = t
//! if_neg : {c : Prop} → {h : Decidable c} → (hnc : ¬c) →
//!          {α : Sort u} → {t e : α} → @ite α c h t e = e
//! ```
//!
//! Lean keeps the `Decidable` instance binder `{h}` and the `{t e}` value
//! binders *implicit*, and orders the condition's decidability + proof BEFORE
//! the value universe `{α}`. Clean's earlier shape put `{α}` second and made
//! `inst`/`t`/`e` explicit, so a genuine Mathlib `@if_pos c h hc α t e`
//! mis-slotted the `Decidable` instance into the `{α : Sort u}` position
//! ("expected Sort u, got Decidable c"). Matching Lean's telescope here lets
//! those real proofs (`ite_pos`, `min_def'`, `compare_of_injective_…`, …)
//! type-check through the unchanged kernel.
//!
//! Both dispatch on `h` via `Decidable.rec` into the `Prop` motive
//! `fun h => @ite α c h t e = t` (resp. `… = e`):
//!
//! - `if_pos`: `isTrue` minor closes by `Eq.refl t` (since `@ite α c (isTrue _)
//!   t e` ι-reduces to `t`); `isFalse h` minor is impossible given the `c`
//!   proof, discharged by `absurd hc h`.
//! - `if_neg`: dually — `isFalse` minor closes by `Eq.refl e`; `isTrue h` minor
//!   is impossible given `hnc : c → False`, discharged by `absurd h hnc`.
//!
//! These let a proof rewrite `ite` even when the `Decidable` instance is a
//! symbolic `instDecidableEqFin … j i` that cannot ι-reduce on its own (the
//! index `Nat`s are variables). Axiom closure: `ite`/`Decidable`(`.rec`)/`Eq`
//! (`.refl`)/`absurd`/`False` only — empty.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `if_pos` and `if_neg`. Idempotent; axiom-free.
    pub(crate) fn register_ite_pos_neg_lemmas(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_true_false()?;
        self.init_decidable()?;
        self.init_ite()?;

        let already = self
            .get_const(&Name::from_string("if_pos"))
            .is_some_and(|c| c.kind == super::types::ConstantKind::Theorem)
            && self
                .get_const(&Name::from_string("if_neg"))
                .is_some_and(|c| c.kind == super::types::ConstantKind::Theorem);
        if already {
            return Ok(());
        }

        let u = Name::from_string("u");
        let lu = Level::param(u.clone());
        let prop = Expr::sort(Level::zero());
        let sort_u = Expr::sort(lu.clone());

        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![Level::zero()]);
        let ite = Expr::const_(Name::from_string("ite"), vec![lu.clone()]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![lu.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![lu.clone()]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        // absurd : {a : Prop} → {b : Sort v} → a → (a → False) → b.
        // Here the conclusion `b` is the goal `@ite … = … : Prop`, so `v = 0`.
        let absurd = Expr::const_(Name::from_string("absurd"), vec![Level::zero()]);

        // @ite.{u} α c inst a b
        let mk_ite = |alpha: Expr, c: Expr, inst: Expr, a: Expr, b: Expr| {
            Expr::apps(ite.clone(), [alpha, c, inst, a, b])
        };
        // @Eq.{u} α l r
        let mk_eq = |alpha: Expr, l: Expr, r: Expr| Expr::apps(eq.clone(), [alpha, l, r]);

        // Shared type builder: `… → @ite α c inst a b = <result>`.
        // `result_is_a == true`  → if_pos statement (premise `c`).
        // `result_is_a == false` → if_neg statement (premise `c → False`).
        for result_is_a in [true, false] {
            let name = if result_is_a { "if_pos" } else { "if_neg" };
            if self
                .get_const(&Name::from_string(name))
                .is_some_and(|c| c.kind == super::types::ConstantKind::Theorem)
            {
                continue;
            }

            // Type. Lean order: {c} {inst : Decidable c} (h : c|¬c) {α} {a b : α}.
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (c_id, c) = b.fresh_local(prop.clone());
                let dec_c = Expr::app(dec.clone(), c.clone());
                let (inst_id, inst) = b.fresh_local(dec_c.clone());
                // premise: c  (if_pos)  /  c → False  (if_neg)
                let prem_ty = if result_is_a {
                    c.clone()
                } else {
                    Expr::pi(BinderInfo::Default, c.clone(), false_c.clone())
                };
                let (h_id, _h) = b.fresh_local(prem_ty.clone());
                let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());
                let (bv_id, bv) = b.fresh_local(alpha.clone());
                let lhs = mk_ite(
                    alpha.clone(),
                    c.clone(),
                    inst.clone(),
                    a.clone(),
                    bv.clone(),
                );
                let result = if result_is_a { a.clone() } else { bv.clone() };
                let concl = mk_eq(alpha.clone(), lhs, result);
                // innermost → outermost: {b} {a} {α} (h) {inst} {c}
                let r = b.mk_pi(bv_id, BinderInfo::Implicit, alpha.clone(), concl);
                let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
                let r = b.mk_pi(h_id, BinderInfo::Default, prem_ty, r);
                let r = b.mk_pi(inst_id, BinderInfo::Implicit, dec_c, r);
                let r = b.mk_pi(c_id, BinderInfo::Implicit, prop.clone(), r);
                b.finish(r)
            };

            // Value: fun {c} {inst} (h) {α} {a b} =>
            //   @Decidable.rec.{0} c
            //     (fun (w : Decidable c) => @Eq α (@ite α c w a b) result)
            //     false_minor true_minor inst
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (c_id, c) = b.fresh_local(prop.clone());
                let dec_c = Expr::app(dec.clone(), c.clone());
                let (inst_id, inst) = b.fresh_local(dec_c.clone());
                let prem_ty = if result_is_a {
                    c.clone()
                } else {
                    Expr::pi(BinderInfo::Default, c.clone(), false_c.clone())
                };
                let (h_id, h) = b.fresh_local(prem_ty.clone());
                let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());
                let (bv_id, bv) = b.fresh_local(alpha.clone());
                let result = if result_is_a { a.clone() } else { bv.clone() };

                // dmotive: fun (w : Decidable c) => @Eq α (@ite α c w a b) result
                let dmotive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (w_id, w) = d.fresh_local(dec_c.clone());
                    let ite_w = mk_ite(alpha.clone(), c.clone(), w, a.clone(), bv.clone());
                    let body = mk_eq(alpha.clone(), ite_w, result.clone());
                    d.finish_child(d.mk_lam(w_id, BinderInfo::Default, dec_c.clone(), body))
                };

                // isFalse minor: fun (hf : c → False) => <proof>
                //   if_pos: goal @ite α c (isFalse hf) a b = a ≡ b = a.
                //           absurd : @absurd c (@Eq α b a) h hf   (h : c, hf : c→False)
                //   if_neg: goal @ite α c (isFalse hf) a b = b ≡ b = b. Eq.refl b.
                let not_c = Expr::pi(BinderInfo::Default, c.clone(), false_c.clone());
                let false_minor = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (hf_id, hf) = d.fresh_local(not_c.clone());
                    let goal_ty = mk_eq(alpha.clone(), bv.clone(), result.clone());
                    let proof = if result_is_a {
                        // @absurd c (b = a) h hf
                        Expr::apps(absurd.clone(), [c.clone(), goal_ty, h.clone(), hf.clone()])
                    } else {
                        // Eq.refl: b = b
                        Expr::apps(eq_refl.clone(), [alpha.clone(), bv.clone()])
                    };
                    d.finish_child(d.mk_lam(hf_id, BinderInfo::Default, not_c.clone(), proof))
                };

                // isTrue minor: fun (ht : c) => <proof>
                //   if_pos: goal @ite α c (isTrue ht) a b = a ≡ a = a. Eq.refl a.
                //   if_neg: goal @ite α c (isTrue ht) a b = b ≡ a = b.
                //           absurd : @absurd c (a = b) ht h   (ht : c, h : c→False)
                let true_minor = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (ht_id, ht) = d.fresh_local(c.clone());
                    let goal_ty = mk_eq(alpha.clone(), a.clone(), result.clone());
                    let proof = if result_is_a {
                        // Eq.refl: a = a
                        Expr::apps(eq_refl.clone(), [alpha.clone(), a.clone()])
                    } else {
                        // @absurd c (a = b) ht h
                        Expr::apps(absurd.clone(), [c.clone(), goal_ty, ht.clone(), h.clone()])
                    };
                    d.finish_child(d.mk_lam(ht_id, BinderInfo::Default, c.clone(), proof))
                };

                // @Decidable.rec.{0} c dmotive false_minor true_minor inst
                let rec_app = Expr::apps(
                    dec_rec.clone(),
                    [c.clone(), dmotive, false_minor, true_minor, inst.clone()],
                );

                // innermost → outermost: {b} {a} {α} (h) {inst} {c}
                let r = b.mk_lam(bv_id, BinderInfo::Implicit, alpha.clone(), rec_app);
                let r = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), r);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
                let r = b.mk_lam(h_id, BinderInfo::Default, prem_ty, r);
                let r = b.mk_lam(inst_id, BinderInfo::Implicit, dec_c, r);
                let r = b.mk_lam(c_id, BinderInfo::Implicit, prop.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Theorem {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: ty,
                value,
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    #[test]
    fn test_if_pos_if_neg_type_check_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_ite_pos_neg_lemmas().expect("register");
        env.register_ite_pos_neg_lemmas().expect("idempotent");

        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["if_pos", "if_neg"] {
            let n = Name::from_string(name);
            let _ = tc
                .infer_type(&Expr::const_(
                    n.clone(),
                    vec![Level::param(Name::from_string("u"))],
                ))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
            assert_eq!(
                env.get_const(&n).expect("registered").kind,
                ConstantKind::Theorem
            );
            let deps = env.axiom_deps(&n).expect("registered");
            let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
            assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
            assert!(matches!(
                env.proof_quality(&n),
                Some(ProofQuality::Constructive)
            ));
        }
    }

    /// Verify-gate: the `if_pos`/`if_neg` binder telescope must MATCH Lean 4
    /// exactly (`Init/Core.lean:932,937`):
    /// `{c : Prop} {h : Decidable c} (hc : c | ¬c) {α : Sort u} {t e : α}`.
    /// A regression to the old shape (`{c} {α} [inst] (h) (t) (e)`) mis-slots
    /// the `Decidable` instance into the `{α : Sort u}` position, breaking every
    /// genuine Mathlib `@if_pos`/`@if_neg` consumer (ite_pos, min_def', …).
    #[test]
    fn test_if_pos_if_neg_binder_telescope_matches_lean() {
        let mut env = Environment::with_prelude();
        env.register_ite_pos_neg_lemmas().expect("register");

        for name in ["if_pos", "if_neg"] {
            let info = env.get_const(&Name::from_string(name)).expect("registered");
            // Walk the 6 leading Pi binders and assert (kind, domain head).
            let mut ty = &info.type_;
            let mut binders: Vec<(BinderInfo, String)> = Vec::new();
            for _ in 0..6 {
                let ExprKind::Pi(bi, dom, body) = ty.kind() else {
                    panic!("{name}: expected 6 Pi binders, telescope too short");
                };
                let head = match dom.kind() {
                    ExprKind::Sort(_) => "Sort".to_owned(),
                    ExprKind::App(f, _) => match f.kind() {
                        ExprKind::Const(n, _) => n.to_string(),
                        _ => "app".to_owned(),
                    },
                    ExprKind::Pi(..) => "Pi".to_owned(),
                    ExprKind::FVar(_) => "fvar".to_owned(),
                    ExprKind::BVar(_) => "bvar".to_owned(),
                    _ => "other".to_owned(),
                };
                binders.push((bi.info, head));
                ty = body;
            }

            // slot 0: {c : Prop}            — Implicit, Sort
            assert_eq!(binders[0].0, BinderInfo::Implicit, "{name} c kind");
            assert_eq!(binders[0].1, "Sort", "{name} c domain");
            // slot 1: {inst : Decidable c}  — Implicit (NOT InstImplicit), Decidable _
            assert_eq!(binders[1].0, BinderInfo::Implicit, "{name} inst kind");
            assert_eq!(binders[1].1, "Decidable", "{name} inst domain");
            // slot 2: (hc : c | ¬c)         — Default
            assert_eq!(binders[2].0, BinderInfo::Default, "{name} hc kind");
            // slot 3: {α : Sort u}          — Implicit, Sort
            assert_eq!(binders[3].0, BinderInfo::Implicit, "{name} alpha kind");
            assert_eq!(binders[3].1, "Sort", "{name} alpha domain");
            // slots 4,5: {t e : α}          — Implicit (NOT explicit)
            assert_eq!(binders[4].0, BinderInfo::Implicit, "{name} t kind");
            assert_eq!(binders[5].0, BinderInfo::Implicit, "{name} e kind");
        }
    }
}
