// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Eq inductive declaration and recursor repair (Eq.rec, Eq.casesOn, Eq.recOn).

use super::context::EqCtx;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{ConstantInfo, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{
    Constructor, InductiveDecl, InductiveType, RecursorArgOrder, RecursorRule, RecursorVal,
};
use crate::level::Level;
use crate::name::Name;

/// Register the Eq inductive type and fix the generated recursors to match
/// Lean 4's promoted-singleton-index pattern.
pub(crate) fn register(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    // Idempotent on the Eq inductive. If `Eq` is already registered (e.g. by
    // clean-verify's `Specification` foundation surface, which builds its own
    // explicit-binder `Eq` without setting the kernel `eq_init` latch), keep
    // that inductive and its recursor as-is and return — the sibling registrars
    // (`basic`/`transport`/`congruence`) still run and ADD the auxiliary lemmas
    // the foundation lacks (`congrArg`/`congrFun`/`congr`/`cast`/`Eq.ndrec`/
    // `Eq.mp`/…), type-checked against the existing `Eq`. Re-adding the inductive
    // would `DuplicateName`; overwriting the recursor could desync the
    // foundation's own `Eq` proof terms. (When `Eq` is absent — the normal kernel
    // path — we build it and fix the recursors below.)
    if env.get_const(&Name::from_string("Eq")).is_some() {
        return Ok(());
    }

    // Build Eq type: ∀ {α : Sort u}, α → α → Prop
    let eq_type = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a_var) = b.fresh_local(ctx.sort_u.clone());
        let (i1_id, _) = b.fresh_local(a_var.clone());
        let (i2_id, _) = b.fresh_local(a_var.clone());
        let r = ctx.prop.clone();
        let r = b.mk_pi(i2_id, BinderInfo::Default, a_var.clone(), r);
        let r = b.mk_pi(i1_id, BinderInfo::Default, a_var.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    // Eq.refl constructor type: ∀ {α : Sort u} {a : α}, @Eq α a a
    let refl_type = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a_var) = b.fresh_local(ctx.sort_u.clone());
        let (x_id, x_var) = b.fresh_local(a_var.clone());
        let r = Expr::app(
            Expr::app(
                Expr::app(ctx.eq_const.clone(), a_var.clone()),
                x_var.clone(),
            ),
            x_var,
        );
        let r = b.mk_pi(x_id, BinderInfo::Default, a_var.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let eq_decl = InductiveDecl {
        level_params: vec![ctx.u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("Eq"),
            type_: eq_type,
            constructors: vec![Constructor {
                name: Name::from_string("Eq.refl"),
                type_: refl_type,
            }],
        }],
    };

    env.add_inductive(eq_decl)?;

    // Fix the generated recursors: the builder doesn't implement Lean 4's
    // "fixed index" pattern where the first Eq index (a) is promoted to a
    // rec-parameter.
    let v_name = Name::from_string("v");
    let sort_v_rec = Expr::from_kind(ExprKind::Sort(Level::param(v_name.clone())));
    let rec_level_params = vec![v_name, ctx.u.clone()];

    // Placeholder binder type for RHS lambdas
    let dummy_ty = Expr::from_kind(ExprKind::Sort(Level::zero()));

    fix_eq_rec(env, ctx, &sort_v_rec, &rec_level_params, &dummy_ty)?;
    fix_eq_cases_on(env, ctx, &sort_v_rec, &rec_level_params, &dummy_ty)?;
    fix_eq_rec_on(env, ctx, &sort_v_rec, &rec_level_params, &dummy_ty)?;

    // These helpers replace both constant payloads and recursor metadata after
    // `add_inductive`. A prior FullKernelCheck stamp described the pre-repair
    // bytes and is not authority for the replacements. Re-earn it from the
    // current type/value plus mandatory release-mode metadata validation.
    //
    // R1-EQREC (2026-08-25): this re-earn is what makes the transient
    // `declaration_verification.remove` calls in the fix_* helpers sound. The
    // FullKernelCheck stamp minted here is EARNED, not asserted:
    // `validate_and_stamp_recursor` runs the recursor-metadata invariants,
    // per-rule subject-reduction checks over the repaired iota payloads, and a
    // fresh strict read-only declaration check of the exact constant payload
    // (value-bearing for Eq.casesOn/Eq.recOn, whose aux-eliminator VALUES are
    // type-checked against their types; type-only for the primitive value-less
    // Eq.rec — the same stamp semantics `add_inductive` gives every generated
    // recursor). Downstream consumers of the stamp for these names (traced
    // 2026-08-25): axiom_audit's certification walk (absent/non-Full stamps on
    // value-less kernel objects become `UnverifiedKernelObject` issues, None is
    // re-checked, never promoted), canonical-ambient-axiom and clean-verify
    // live-axiom integrity checks (kind-Axiom constants only — these three are
    // kind Definition, so out of that census), and the noConfusion
    // regeneration predicate (`.noConfusion*` names only).
    for name in ["Eq.rec", "Eq.casesOn", "Eq.recOn"] {
        env.validate_and_stamp_recursor(&Name::from_string(name))?;
    }

    Ok(())
}

/// Build the promoted-singleton RHS lambda shared by Eq.rec, casesOn, recOn.
///
/// After promotion: num_params=2, num_motives=1, num_minors=1, num_fields=0.
/// RHS: λ param₀. λ param₁. λ motive. λ minor. minor
fn promoted_singleton_rhs(dummy_ty: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (param0_id, _) = b.fresh_local(dummy_ty.clone());
    let (param1_id, _) = b.fresh_local(dummy_ty.clone());
    let (motive_id, _) = b.fresh_local(dummy_ty.clone());
    let (minor_id, minor) = b.fresh_local(dummy_ty.clone());
    let r = b.mk_lam(minor_id, BinderInfo::Default, dummy_ty.clone(), minor);
    let r = b.mk_lam(motive_id, BinderInfo::Default, dummy_ty.clone(), r);
    let r = b.mk_lam(param1_id, BinderInfo::Default, dummy_ty.clone(), r);
    let r = b.mk_lam(param0_id, BinderInfo::Default, dummy_ty.clone(), r);
    b.finish(r)
}

/// Build the common motive type: (x : α) → Eq a x → Sort v
fn eq_motive_type(
    b: &EnvDeclBuilder,
    ctx: &EqCtx,
    alpha: &Expr,
    a_var: &Expr,
    sort_v: &Expr,
) -> Expr {
    let mut c = EnvDeclBuilder::child_of(b);
    let (x_id, x_var) = c.fresh_local(alpha.clone());
    let eq_a_x = ctx.eq(alpha, a_var.clone(), x_var);
    let (h_id, _) = c.fresh_local(eq_a_x.clone());
    let r = sort_v.clone();
    let r = c.mk_pi(h_id, BinderInfo::Default, eq_a_x, r);
    let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
    c.finish_child(r)
}

fn fix_eq_rec(
    env: &mut Environment,
    ctx: &EqCtx,
    sort_v: &Expr,
    rec_level_params: &[Name],
    dummy_ty: &Expr,
) -> Result<(), EnvError> {
    // Correct Eq.rec.{v, u}:
    //   {α : Sort u} → {a : α} →
    //   {motive : (x : α) → Eq a x → Sort v} →
    //   motive a (Eq.refl a) →
    //   {b : α} → (h : Eq a b) → motive b h
    let eq_rec_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let motive_ty = eq_motive_type(&b, ctx, &alpha, &a_var, sort_v);
        let (mot_id, mot_var) = b.fresh_local(motive_ty.clone());
        let refl_a = ctx.refl(&alpha, a_var.clone());
        let minor_ty = Expr::app(Expr::app(mot_var.clone(), a_var.clone()), refl_a);
        let (minor_id, _) = b.fresh_local(minor_ty.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h_id, h_var) = b.fresh_local(eq_a_b.clone());
        let r = Expr::app(Expr::app(mot_var, bb_var), h_var);
        let r = b.mk_pi(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(minor_id, BinderInfo::Default, minor_ty, r);
        let r = b.mk_pi(mot_id, BinderInfo::Implicit, motive_ty, r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let rec_name = Name::from_string("Eq.rec");
    let rec_const_info = ConstantInfo::new(
        rec_name.clone(),
        rec_level_params.to_vec(),
        eq_rec_type.clone(),
        None,
        false,
    );
    // SOUNDNESS (R1-EQREC, 2026-08-25): TRANSIENT stamp removal, not absent
    // provenance. The `add_inductive`-minted FullKernelCheck stamp described
    // the PRE-repair payload, so it must not survive this replacement; the
    // stamp is RE-EARNED for the repaired payload by
    // `validate_and_stamp_recursor` at the end of `register()` (metadata
    // invariants + per-rule subject reduction + `check_decl_readonly_strict`).
    // If that re-check fails, `register()` errors and the absent stamp is the
    // correct conservative state — every downstream consumer treats `None` as
    // unknown, never as verified (axiom_audit certification flags it
    // `UnverifiedKernelObject` / re-checks it; nothing promotes silently).
    env.declaration_verification.remove(&rec_name);
    env.constants.insert(rec_name.clone(), rec_const_info);

    if let Some(rec_val) = env.recursors.get(&rec_name).cloned() {
        let rhs = promoted_singleton_rhs(dummy_ty);
        let fixed_rules: Vec<RecursorRule> = rec_val
            .rules
            .iter()
            .map(|rule| RecursorRule {
                num_fields: 0,
                recursive_fields: vec![],
                rhs: rhs.clone(),
                ..rule.clone()
            })
            .collect();
        let fixed_rec_val = RecursorVal {
            type_: eq_rec_type,
            num_params: 2,
            num_indices: 1,
            level_params: rec_level_params.to_vec(),
            rules: fixed_rules,
            ..rec_val
        };
        env.recursors.insert(rec_name, fixed_rec_val);
    }
    Ok(())
}

fn fix_eq_cases_on(
    env: &mut Environment,
    ctx: &EqCtx,
    sort_v: &Expr,
    rec_level_params: &[Name],
    dummy_ty: &Expr,
) -> Result<(), EnvError> {
    // Eq.casesOn.{v, u}:
    //   {α : Sort u} → {a : α} →
    //   {motive : (x : α) → Eq a x → Sort v} →
    //   {b : α} → (h : Eq a b) → motive a (Eq.refl a) → motive b h
    let eq_cases_on_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let motive_ty = eq_motive_type(&b, ctx, &alpha, &a_var, sort_v);
        let (mot_id, mot_var) = b.fresh_local(motive_ty.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h_id, h_var) = b.fresh_local(eq_a_b.clone());
        let refl_a = ctx.refl(&alpha, a_var.clone());
        let minor_ty = Expr::app(Expr::app(mot_var.clone(), a_var.clone()), refl_a);
        let (minor_id, _) = b.fresh_local(minor_ty.clone());
        let r = Expr::app(Expr::app(mot_var, bb_var), h_var);
        let r = b.mk_pi(minor_id, BinderInfo::Default, minor_ty, r);
        let r = b.mk_pi(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(mot_id, BinderInfo::Implicit, motive_ty, r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let cases_name = Name::from_string("Eq.casesOn");
    // Definitional VALUE (residual-to-zero campaign, 2026-07-03): the repair
    // previously re-inserted Eq.casesOn VALUE-LESS, clobbering the generated
    // aux-eliminator value — so a variable-scrutinee `Eq.casesOn`/`Eq.recOn`
    // could never delta-converge with the `Eq.rec` spelling
    // (`RelSeries.insertNth.proof_1`). Rebuild the Lean-parity wrapper over
    // the REPAIRED `Eq.rec` type (params α,a → motive → minor → index b →
    // major h), matching the repaired aux layout (… → index → major → minor).
    let eq_rec_ty_for_aux = env
        .get_const(&Name::from_string("Eq.rec"))
        .map(|ci| ci.type_.clone())
        .ok_or_else(|| {
            EnvError::Inductive(crate::inductive::InductiveError::InvalidType(
                "Eq.rec must be repaired before Eq.casesOn".to_string(),
            ))
        })?;
    let cases_value = env.build_aux_eliminator_value(
        &cases_name,
        &Name::from_string("Eq.rec"),
        rec_level_params,
        &eq_cases_on_type,
        &eq_rec_ty_for_aux,
        2,
        1,
        1,
        1,
        None,
    )?;
    let cases_const_info = ConstantInfo::new(
        cases_name.clone(),
        rec_level_params.to_vec(),
        eq_cases_on_type.clone(),
        Some(cases_value),
        false,
    );
    // SOUNDNESS (R1-EQREC, 2026-08-25): transient removal — re-earned by
    // `validate_and_stamp_recursor` in `register()`; see the Eq.rec note.
    env.declaration_verification.remove(&cases_name);
    env.constants.insert(cases_name.clone(), cases_const_info);

    if let Some(cases_val) = env.recursors.get(&cases_name).cloned() {
        let rhs = promoted_singleton_rhs(dummy_ty);
        let fixed_rules: Vec<RecursorRule> = cases_val
            .rules
            .iter()
            .map(|rule| RecursorRule {
                num_fields: 0,
                recursive_fields: vec![],
                rhs: rhs.clone(),
                ..rule.clone()
            })
            .collect();
        let fixed_val = RecursorVal {
            type_: eq_cases_on_type,
            num_params: 2,
            num_indices: 1,
            level_params: rec_level_params.to_vec(),
            rules: fixed_rules,
            // The repaired `Eq.casesOn` *type* built above is
            //   {α}{a}{motive}{b}(h : Eq a b)(refl : motive a rfl) → motive b h
            // i.e. the major premise `h` (and its index `b`) precede the minor
            // premise — Lean 4's `casesOn` convention. That is the
            // `MajorAfterMotive` argument order. The recursor produced by the
            // generic inductive builder defaults to `MajorAfterMinors` (correct
            // for `Eq.rec`, whose minor precedes the major), so we must override
            // it here to match the type we just installed. Without this, match
            // lowering emits `Eq.casesOn α a motive minor b h` (minor before
            // major), the kernel substitutes the minor into the index/major
            // binders, and the motive application scrambles — the symptom is a
            // spurious type mismatch with leaked index metavariables.
            arg_order: RecursorArgOrder::MajorAfterMotive,
            ..cases_val
        };
        env.recursors.insert(cases_name, fixed_val);
    }
    Ok(())
}

fn fix_eq_rec_on(
    env: &mut Environment,
    ctx: &EqCtx,
    sort_v: &Expr,
    rec_level_params: &[Name],
    dummy_ty: &Expr,
) -> Result<(), EnvError> {
    // Eq.recOn.{v, u}: same layout as casesOn for Eq
    let eq_rec_on_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let motive_ty = eq_motive_type(&b, ctx, &alpha, &a_var, sort_v);
        let (mot_id, mot_var) = b.fresh_local(motive_ty.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h_id, h_var) = b.fresh_local(eq_a_b.clone());
        let refl_a = ctx.refl(&alpha, a_var.clone());
        let minor_ty = Expr::app(Expr::app(mot_var.clone(), a_var.clone()), refl_a);
        let (minor_id, _) = b.fresh_local(minor_ty.clone());
        let r = Expr::app(Expr::app(mot_var, bb_var), h_var);
        let r = b.mk_pi(minor_id, BinderInfo::Default, minor_ty, r);
        let r = b.mk_pi(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(mot_id, BinderInfo::Implicit, motive_ty, r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let rec_on_name = Name::from_string("Eq.recOn");
    // Definitional VALUE — same rationale as Eq.casesOn above.
    let eq_rec_ty_for_aux = env
        .get_const(&Name::from_string("Eq.rec"))
        .map(|ci| ci.type_.clone())
        .ok_or_else(|| {
            EnvError::Inductive(crate::inductive::InductiveError::InvalidType(
                "Eq.rec must be repaired before Eq.recOn".to_string(),
            ))
        })?;
    let rec_on_value = env.build_aux_eliminator_value(
        &rec_on_name,
        &Name::from_string("Eq.rec"),
        rec_level_params,
        &eq_rec_on_type,
        &eq_rec_ty_for_aux,
        2,
        1,
        1,
        1,
        None,
    )?;
    let rec_on_const_info = ConstantInfo::new(
        rec_on_name.clone(),
        rec_level_params.to_vec(),
        eq_rec_on_type.clone(),
        Some(rec_on_value),
        false,
    );
    // SOUNDNESS (R1-EQREC, 2026-08-25): transient removal — re-earned by
    // `validate_and_stamp_recursor` in `register()`; see the Eq.rec note.
    env.declaration_verification.remove(&rec_on_name);
    env.constants.insert(rec_on_name.clone(), rec_on_const_info);

    if let Some(rec_on_val) = env.recursors.get(&rec_on_name).cloned() {
        let rhs = promoted_singleton_rhs(dummy_ty);
        let fixed_rules: Vec<RecursorRule> = rec_on_val
            .rules
            .iter()
            .map(|rule| RecursorRule {
                num_fields: 0,
                recursive_fields: vec![],
                rhs: rhs.clone(),
                ..rule.clone()
            })
            .collect();
        let fixed_val = RecursorVal {
            type_: eq_rec_on_type,
            num_params: 2,
            num_indices: 1,
            level_params: rec_level_params.to_vec(),
            rules: fixed_rules,
            ..rec_on_val
        };
        env.recursors.insert(rec_on_name, fixed_val);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::DeclarationVerification;

    /// R1-EQREC pin: the Eq recursor repair's transient stamp removal is
    /// re-earned — after `init_eq`, all three repaired names carry
    /// FullKernelCheck provenance (minted by `validate_and_stamp_recursor`
    /// over the REPAIRED payloads, not left over from `add_inductive`).
    #[test]
    fn test_eq_repair_reearns_full_kernel_check_stamp() {
        let mut env = Environment::new();
        env.init_eq().expect("init_eq must succeed");
        for name in ["Eq.rec", "Eq.casesOn", "Eq.recOn"] {
            assert_eq!(
                env.declaration_verification(&Name::from_string(name)),
                Some(DeclarationVerification::FullKernelCheck),
                "{name} must carry the re-earned FullKernelCheck stamp \
                 (absent/lower provenance means the R1-EQREC re-earn regressed)"
            );
        }
    }

    /// R1-EQREC adversarial pin: the stamp is EARNED by validation, not
    /// asserted. Corrupting a repaired rule payload (the iota rhs the
    /// subject-reduction check walks) makes `validate_and_stamp_recursor`
    /// refuse — so the FullKernelCheck stamp can only describe a payload that
    /// actually passed the checks.
    #[test]
    fn test_eq_rec_stamp_is_earned_not_asserted() {
        let mut env = Environment::new();
        env.init_eq().expect("init_eq must succeed");
        let rec_name = Name::from_string("Eq.rec");

        // Happy path: re-validation of the genuine repaired payload succeeds.
        env.validate_and_stamp_recursor(&rec_name)
            .expect("re-validating the genuine repaired Eq.rec must succeed");

        // Corrupt the repaired rule: claim one field where the promoted
        // singleton has zero — the symbolic rule application no longer lines
        // up and validation must refuse.
        let mut rec_val = env
            .recursors
            .get(&rec_name)
            .cloned()
            .expect("Eq.rec recursor metadata must exist");
        assert_eq!(rec_val.rules.len(), 1, "Eq has exactly one iota rule");
        rec_val.rules[0].num_fields = 1;
        env.recursors.insert(rec_name.clone(), rec_val);

        assert!(
            env.validate_and_stamp_recursor(&rec_name).is_err(),
            "a corrupted Eq.rec rule payload must refuse validation — the \
             stamp is earned by the checks, never minted by fiat"
        );
    }
}
