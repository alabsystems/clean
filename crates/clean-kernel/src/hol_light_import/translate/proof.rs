// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HOL proof-rule translation.

use super::super::{
    HolLightImportError, HolProof, HolProofObject, HolTerm, HolTermSubstitution, HolType,
    HolTypeSubstitution, HolVar, TranslatedProofObject,
};
use super::context::{
    assumption_args_in_context, root_scope, scope_args_in_context, theorem_name, Scope,
    SymbolCollector,
};
use super::proof_helpers::{
    apply_proof, apply_theorem, available_assumptions, close_pi, ensure_prop, eq_refl, expect_eq,
    instantiated_term_scope_args, instantiated_type_scope_args, match_assumption_args,
    merge_assumptions, remove_assumption, term_has_free_var, theorem_from_body,
    validate_term_substitutions, CheckedTheorem,
};
use super::term::{
    note_type_ops, substitute_term, substitute_type_in_term, substitute_type_in_type,
    support_declarations, TermTranslator,
};
use crate::{BinderInfo, CleanMode, Expr, Level, SourceSystem};

/// Apply a HOL type substitution to every term, binder type, and nested
/// substitution in a proof tree. INST_TYPE distributes over all primitive
/// inferences, so this preserves what the proof proves (up to the substitution).
fn subst_types_in_proof(proof: &HolProof, subs: &[HolTypeSubstitution]) -> HolProof {
    let sv = |v: &HolVar| HolVar::new(v.name.clone(), substitute_type_in_type(&v.ty, subs));
    match proof {
        HolProof::Refl { term } => HolProof::Refl {
            term: substitute_type_in_term(term, subs),
        },
        HolProof::Trans { left, right } => HolProof::Trans {
            left: Box::new(subst_types_in_proof(left, subs)),
            right: Box::new(subst_types_in_proof(right, subs)),
        },
        HolProof::MkComb { function, argument } => HolProof::MkComb {
            function: Box::new(subst_types_in_proof(function, subs)),
            argument: Box::new(subst_types_in_proof(argument, subs)),
        },
        HolProof::Abs { binder, proof } => HolProof::Abs {
            binder: sv(binder),
            proof: Box::new(subst_types_in_proof(proof, subs)),
        },
        HolProof::Beta {
            binder,
            body,
            argument,
        } => HolProof::Beta {
            binder: sv(binder),
            body: substitute_type_in_term(body, subs),
            argument: substitute_type_in_term(argument, subs),
        },
        HolProof::Assume { proposition } => HolProof::Assume {
            proposition: substitute_type_in_term(proposition, subs),
        },
        HolProof::EqMp { equality, proof } => HolProof::EqMp {
            equality: Box::new(subst_types_in_proof(equality, subs)),
            proof: Box::new(subst_types_in_proof(proof, subs)),
        },
        HolProof::DeductAntisym { left, right } => HolProof::DeductAntisym {
            left: Box::new(subst_types_in_proof(left, subs)),
            right: Box::new(subst_types_in_proof(right, subs)),
        },
        HolProof::Inst {
            proof,
            substitutions,
        } => HolProof::Inst {
            proof: Box::new(subst_types_in_proof(proof, subs)),
            substitutions: substitutions
                .iter()
                .map(|s| HolTermSubstitution {
                    variable: sv(&s.variable),
                    replacement: substitute_type_in_term(&s.replacement, subs),
                })
                .collect(),
        },
        HolProof::InstType {
            proof,
            substitutions,
        } => HolProof::InstType {
            proof: Box::new(subst_types_in_proof(proof, subs)),
            substitutions: substitutions
                .iter()
                .map(|s| HolTypeSubstitution {
                    variable: s.variable.clone(),
                    replacement: substitute_type_in_type(&s.replacement, subs),
                })
                .collect(),
        },
    }
}

/// Eliminate every `INST_TYPE` node by pushing its type substitution down into
/// the sub-proof. The result is `INST_TYPE`-free and well-typed under a single
/// scope, which sidesteps the scope-threading conflict where a sub-proof needs
/// its pre-substitution types while the parent needs the post-substitution ones.
fn eliminate_inst_type(proof: &HolProof) -> HolProof {
    match proof {
        HolProof::InstType {
            proof,
            substitutions,
        } => subst_types_in_proof(&eliminate_inst_type(proof), substitutions),
        HolProof::Refl { .. } | HolProof::Assume { .. } | HolProof::Beta { .. } => proof.clone(),
        HolProof::Trans { left, right } => HolProof::Trans {
            left: Box::new(eliminate_inst_type(left)),
            right: Box::new(eliminate_inst_type(right)),
        },
        HolProof::MkComb { function, argument } => HolProof::MkComb {
            function: Box::new(eliminate_inst_type(function)),
            argument: Box::new(eliminate_inst_type(argument)),
        },
        HolProof::Abs { binder, proof } => HolProof::Abs {
            binder: binder.clone(),
            proof: Box::new(eliminate_inst_type(proof)),
        },
        HolProof::EqMp { equality, proof } => HolProof::EqMp {
            equality: Box::new(eliminate_inst_type(equality)),
            proof: Box::new(eliminate_inst_type(proof)),
        },
        HolProof::DeductAntisym { left, right } => HolProof::DeductAntisym {
            left: Box::new(eliminate_inst_type(left)),
            right: Box::new(eliminate_inst_type(right)),
        },
        HolProof::Inst {
            proof,
            substitutions,
        } => HolProof::Inst {
            proof: Box::new(eliminate_inst_type(proof)),
            substitutions: substitutions.clone(),
        },
    }
}

pub(super) fn translate_proof_object(
    object: &HolProofObject,
) -> Result<TranslatedProofObject, HolLightImportError> {
    // Push all INST_TYPE substitutions into the proof leaves first, so the whole
    // tree type-checks under one consistent scope.
    let eliminated = HolProofObject {
        name: object.name.clone(),
        proof: eliminate_inst_type(&object.proof),
    };
    let object = &eliminated;
    let scope = root_scope(object)?;
    let mut symbols = SymbolCollector::default();
    for binder in scope.binders() {
        if let Some(hol_ty) = &binder.hol_ty {
            note_type_ops(&mut symbols, hol_ty);
        }
    }
    let theorem = translate_proof(&scope, &object.proof, &mut symbols)?;
    let mut translator = TermTranslator::new(&mut symbols);
    let assumptions = theorem
        .assumptions
        .iter()
        .map(|assumption| translator.translate_term(&scope, assumption))
        .collect::<Result<Vec<_>, _>>()?;
    let conclusion = translator.translate_term(&scope, &theorem.conclusion)?;
    let theorem_type = close_pi(
        &scope,
        &theorem.assumptions,
        conclusion.clone(),
        &mut translator,
    )?;
    // `translator` borrows `symbols`; let it fall out of scope here so
    // `support_declarations` can re-borrow `symbols` mutably.
    let _ = translator;
    let support_declarations = support_declarations(&mut symbols)?;
    Ok(TranslatedProofObject {
        source_name: object.name.clone(),
        theorem_name: theorem_name(&object.name),
        source_system: SourceSystem::HOLLight,
        required_mode: CleanMode::from_source_system(SourceSystem::HOLLight),
        assumptions,
        conclusion,
        theorem_type,
        proof: theorem.proof,
        support_declarations,
    })
}

fn translate_proof(
    scope: &Scope,
    proof: &HolProof,
    symbols: &mut SymbolCollector,
) -> Result<CheckedTheorem, HolLightImportError> {
    match proof {
        HolProof::Refl { term } => {
            let mut translator = TermTranslator::new(symbols);
            let ty = translator.translate_type(scope, &translator.infer_type(term)?)?;
            let term_expr = translator.translate_term(scope, term)?;
            let conclusion = HolTerm::eq(term.clone(), term.clone(), translator.infer_type(term)?);
            theorem_from_body(
                scope,
                Vec::new(),
                conclusion,
                eq_refl(ty, term_expr),
                &mut translator,
            )
        }
        HolProof::Trans { left, right } => {
            let left_thm = translate_proof(scope, left, symbols)?;
            let right_thm = translate_proof(scope, right, symbols)?;
            let mut translator = TermTranslator::new(symbols);
            let (lhs, mid) = expect_eq("TRANS", &left_thm.conclusion)?;
            let (mid_rhs, rhs) = expect_eq("TRANS", &right_thm.conclusion)?;
            if mid != mid_rhs {
                return Err(HolLightImportError::TypeMismatch {
                    expected: translator.infer_type(mid)?,
                    actual: translator.infer_type(mid_rhs)?,
                });
            }
            let assumptions = merge_assumptions(&left_thm.assumptions, &right_thm.assumptions);
            let body = {
                let scope_args = scope_args_in_context(scope, assumptions.len(), 0);
                let available = available_assumptions(
                    &assumptions,
                    &assumption_args_in_context(scope, assumptions.len(), 0),
                );
                let h_left = apply_theorem(&left_thm, &scope_args, &available)?;
                let h_right = apply_theorem(&right_thm, &scope_args, &available)?;
                let lift = assumptions.len() as u32;
                let alpha = translator
                    .translate_type(scope, &translator.infer_type(lhs)?)?
                    .lift(lift);
                let lhs_expr = translator.translate_term(scope, lhs)?.lift(lift);
                let mid_expr = translator.translate_term(scope, mid)?.lift(lift);
                let rhs_expr = translator.translate_term(scope, rhs)?.lift(lift);
                Expr::apps(
                    Expr::const_str_levels("Eq.trans", vec![Level::succ(Level::zero())]),
                    [alpha, lhs_expr, mid_expr, rhs_expr, h_left, h_right],
                )
            };
            theorem_from_body(
                scope,
                assumptions,
                HolTerm::eq(lhs.clone(), rhs.clone(), translator.infer_type(lhs)?),
                body,
                &mut translator,
            )
        }
        HolProof::MkComb { function, argument } => {
            translate_mk_comb(scope, function, argument, symbols)
        }
        HolProof::Abs { binder, proof } => translate_abs(scope, binder, proof, symbols),
        HolProof::Beta {
            binder,
            body,
            argument,
        } => translate_beta(scope, binder, body, argument, symbols),
        HolProof::Assume { proposition } => {
            let mut translator = TermTranslator::new(symbols);
            ensure_prop("ASSUME", proposition, &translator)?;
            theorem_from_body(
                scope,
                vec![proposition.clone()],
                proposition.clone(),
                Expr::bvar(0),
                &mut translator,
            )
        }
        HolProof::EqMp { equality, proof } => translate_eq_mp(scope, equality, proof, symbols),
        HolProof::DeductAntisym { left, right } => {
            translate_deduct_antisym(scope, left, right, symbols)
        }
        HolProof::Inst {
            proof,
            substitutions,
        } => translate_inst(scope, proof, substitutions, symbols),
        HolProof::InstType {
            proof,
            substitutions,
        } => translate_inst_type(scope, proof, substitutions, symbols),
    }
}

fn translate_mk_comb(
    scope: &Scope,
    function: &HolProof,
    argument: &HolProof,
    symbols: &mut SymbolCollector,
) -> Result<CheckedTheorem, HolLightImportError> {
    let fun_thm = translate_proof(scope, function, symbols)?;
    let arg_thm = translate_proof(scope, argument, symbols)?;
    let mut translator = TermTranslator::new(symbols);
    let (f1, f2) = expect_eq("MK_COMB", &fun_thm.conclusion)?;
    let (x1, x2) = expect_eq("MK_COMB", &arg_thm.conclusion)?;
    let function_ty = translator.infer_type(f1)?;
    let HolType::Fun { domain, codomain } = function_ty else {
        return Err(HolLightImportError::ExpectedFunctionType {
            ty: translator.infer_type(f1)?,
        });
    };
    let x_ty = translator.infer_type(x1)?;
    if *domain != x_ty {
        return Err(HolLightImportError::TypeMismatch {
            expected: *domain,
            actual: x_ty,
        });
    }
    let assumptions = merge_assumptions(&fun_thm.assumptions, &arg_thm.assumptions);
    let lift = assumptions.len() as u32;
    let scope_args = scope_args_in_context(scope, assumptions.len(), 0);
    let available = available_assumptions(
        &assumptions,
        &assumption_args_in_context(scope, assumptions.len(), 0),
    );
    let h_fun = apply_theorem(&fun_thm, &scope_args, &available)?;
    let h_arg = apply_theorem(&arg_thm, &scope_args, &available)?;
    let body = Expr::apps(
        Expr::const_str_levels(
            "congr",
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        ),
        [
            translator.translate_type(scope, &domain)?.lift(lift),
            translator.translate_type(scope, &codomain)?.lift(lift),
            translator.translate_term(scope, f1)?.lift(lift),
            translator.translate_term(scope, f2)?.lift(lift),
            translator.translate_term(scope, x1)?.lift(lift),
            translator.translate_term(scope, x2)?.lift(lift),
            h_fun,
            h_arg,
        ],
    );
    theorem_from_body(
        scope,
        assumptions,
        HolTerm::eq(
            HolTerm::app(f1.clone(), x1.clone()),
            HolTerm::app(f2.clone(), x2.clone()),
            *codomain,
        ),
        body,
        &mut translator,
    )
}

fn translate_abs(
    scope: &Scope,
    binder: &crate::hol_light_import::HolVar,
    proof: &HolProof,
    symbols: &mut SymbolCollector,
) -> Result<CheckedTheorem, HolLightImportError> {
    let binder_ty = {
        let mut translator = TermTranslator::new(symbols);
        translator.translate_type(scope, &binder.ty)?
    };
    let extended = scope.extend_term(binder, binder_ty.clone());
    let sub = translate_proof(&extended, proof, symbols)?;
    let mut translator = TermTranslator::new(symbols);
    let (lhs, rhs) = expect_eq("ABS", &sub.conclusion)?;
    for assumption in &sub.assumptions {
        if term_has_free_var(assumption, binder, &mut Vec::new()) {
            return Err(HolLightImportError::BinderEscapesAssumption {
                name: binder.name.clone(),
            });
        }
    }
    let assumptions = sub.assumptions.clone();
    let lift = assumptions.len() as u32;
    let scope_args = scope_args_in_context(scope, assumptions.len(), 1);
    let available = available_assumptions(
        &assumptions,
        &assumption_args_in_context(scope, assumptions.len(), 1),
    );
    let mut binder_args = scope_args;
    binder_args.push(Expr::bvar(0));
    let pointwise = apply_theorem(&sub, &binder_args, &available)?;
    let binder_ty_body = binder_ty.lift(lift);
    let lhs_lambda = translator
        .translate_term(scope, &HolTerm::abs(binder.clone(), lhs.clone()))?
        .lift(lift);
    let rhs_lambda = translator
        .translate_term(scope, &HolTerm::abs(binder.clone(), rhs.clone()))?
        .lift(lift);
    // `codomain_ty` is translated in `extended` (the abstraction binder already
    // in scope) and is placed under `funext`'s motive binder `λ(_:α). _`, which
    // re-introduces exactly that binder — so it must be lifted by `lift` (the
    // assumption count), NOT `lift + 1` (the old `+1` double-counted the motive
    // binder and produced an out-of-range de Bruijn index).
    let codomain_ty = translator
        .translate_type(&extended, &translator.infer_type(lhs)?)?
        .lift(lift);
    let beta = Expr::lam(BinderInfo::Implicit, binder_ty_body.clone(), codomain_ty);
    let body = Expr::apps(
        Expr::const_str_levels(
            "funext",
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        ),
        [
            binder_ty_body.clone(),
            beta,
            lhs_lambda,
            rhs_lambda,
            Expr::lam(BinderInfo::Default, binder_ty_body, pointwise),
        ],
    );
    theorem_from_body(
        scope,
        assumptions,
        HolTerm::eq(
            HolTerm::abs(binder.clone(), lhs.clone()),
            HolTerm::abs(binder.clone(), rhs.clone()),
            HolType::fun(binder.ty.clone(), translator.infer_type(lhs)?),
        ),
        body,
        &mut translator,
    )
}

fn translate_beta(
    scope: &Scope,
    binder: &crate::hol_light_import::HolVar,
    body: &HolTerm,
    argument: &HolTerm,
    symbols: &mut SymbolCollector,
) -> Result<CheckedTheorem, HolLightImportError> {
    let mut translator = TermTranslator::new(symbols);
    let argument_ty = translator.infer_type(argument)?;
    if argument_ty != binder.ty {
        return Err(HolLightImportError::TypeMismatch {
            expected: binder.ty.clone(),
            actual: argument_ty,
        });
    }
    let rhs = substitute_term(
        body,
        &[crate::hol_light_import::HolTermSubstitution {
            variable: binder.clone(),
            replacement: argument.clone(),
        }],
        &mut Vec::new(),
    );
    let rhs_ty = translator.infer_type(&rhs)?;
    let rhs_expr = translator.translate_term(scope, &rhs)?;
    theorem_from_body(
        scope,
        Vec::new(),
        HolTerm::eq(
            HolTerm::app(HolTerm::abs(binder.clone(), body.clone()), argument.clone()),
            rhs,
            rhs_ty.clone(),
        ),
        eq_refl(translator.translate_type(scope, &rhs_ty)?, rhs_expr),
        &mut translator,
    )
}

fn translate_eq_mp(
    scope: &Scope,
    equality: &HolProof,
    proof: &HolProof,
    symbols: &mut SymbolCollector,
) -> Result<CheckedTheorem, HolLightImportError> {
    let eq_thm = translate_proof(scope, equality, symbols)?;
    let pr_thm = translate_proof(scope, proof, symbols)?;
    let mut translator = TermTranslator::new(symbols);
    let (lhs, rhs) = expect_eq("EQ_MP", &eq_thm.conclusion)?;
    ensure_prop("EQ_MP", lhs, &translator)?;
    ensure_prop("EQ_MP", rhs, &translator)?;
    if &pr_thm.conclusion != lhs {
        return Err(HolLightImportError::ExpectedEquality { rule: "EQ_MP" });
    }
    let assumptions = merge_assumptions(&eq_thm.assumptions, &pr_thm.assumptions);
    let lift = assumptions.len() as u32;
    let scope_args = scope_args_in_context(scope, assumptions.len(), 0);
    let available = available_assumptions(
        &assumptions,
        &assumption_args_in_context(scope, assumptions.len(), 0),
    );
    let h_eq = apply_theorem(&eq_thm, &scope_args, &available)?;
    let h_pr = apply_theorem(&pr_thm, &scope_args, &available)?;
    // EQ_MP transports a *proof of the proposition* `lhs` to `rhs` along the HOL
    // equality `lhs = rhs`. In the embedding `lhs`, `rhs : bool` are clean `Prop`
    // (Sort 0), so `Eq.mp` is at universe 0 — `Eq.mp.{0} : {α β : Sort 0} → α = β
    // → α → β`, fed the level-1 `Prop`-equality `h_eq : @Eq.{1} Prop lhs rhs`.
    // (Unlike the term-level Eq rules, which are level 1 because HOL *types*
    // embed at `Type`.)
    let body = Expr::apps(
        Expr::const_str_levels("Eq.mp", vec![Level::zero()]),
        [
            translator.translate_term(scope, lhs)?.lift(lift),
            translator.translate_term(scope, rhs)?.lift(lift),
            h_eq,
            h_pr,
        ],
    );
    theorem_from_body(scope, assumptions, rhs.clone(), body, &mut translator)
}

fn translate_deduct_antisym(
    scope: &Scope,
    left: &HolProof,
    right: &HolProof,
    symbols: &mut SymbolCollector,
) -> Result<CheckedTheorem, HolLightImportError> {
    let left_thm = translate_proof(scope, left, symbols)?;
    let right_thm = translate_proof(scope, right, symbols)?;
    let mut translator = TermTranslator::new(symbols);
    ensure_prop("DEDUCT_ANTISYM_RULE", &left_thm.conclusion, &translator)?;
    ensure_prop("DEDUCT_ANTISYM_RULE", &right_thm.conclusion, &translator)?;
    let assumptions = merge_assumptions(
        &remove_assumption(
            &left_thm.assumptions,
            &right_thm.conclusion,
            "DEDUCT_ANTISYM_RULE",
        )?,
        &remove_assumption(
            &right_thm.assumptions,
            &left_thm.conclusion,
            "DEDUCT_ANTISYM_RULE",
        )?,
    );
    let lift = assumptions.len() as u32;
    let scope_args_p = scope_args_in_context(scope, assumptions.len(), 1);
    let assumption_args_p = assumption_args_in_context(scope, assumptions.len(), 1);
    let p_expr = translator
        .translate_term(scope, &left_thm.conclusion)?
        .lift(lift);
    let q_expr = translator
        .translate_term(scope, &right_thm.conclusion)?
        .lift(lift);
    let mut available_for_right = available_assumptions(&assumptions, &assumption_args_p);
    available_for_right.push((left_thm.conclusion.clone(), Expr::bvar(0)));
    let p_to_q = Expr::lam(
        BinderInfo::Default,
        p_expr.clone(),
        apply_theorem(&right_thm, &scope_args_p, &available_for_right)?,
    );
    let scope_args_q = scope_args_in_context(scope, assumptions.len(), 1);
    let assumption_args_q = assumption_args_in_context(scope, assumptions.len(), 1);
    let mut available_for_left = available_assumptions(&assumptions, &assumption_args_q);
    available_for_left.push((right_thm.conclusion.clone(), Expr::bvar(0)));
    let q_to_p = Expr::lam(
        BinderInfo::Default,
        q_expr.clone(),
        apply_theorem(&left_thm, &scope_args_q, &available_for_left)?,
    );
    // Faithful Lean `propext : {a b} → (a ↔ b) → a = b` takes a single `Iff`;
    // package the two implications via `Iff.intro p q p_to_q q_to_p`.
    let iff = Expr::apps(
        Expr::const_str("Iff.intro"),
        [p_expr.clone(), q_expr.clone(), p_to_q, q_to_p],
    );
    let body = Expr::apps(Expr::const_str("propext"), [p_expr, q_expr, iff]);
    theorem_from_body(
        scope,
        assumptions,
        HolTerm::eq(
            left_thm.conclusion.clone(),
            right_thm.conclusion.clone(),
            HolType::Bool,
        ),
        body,
        &mut translator,
    )
}

fn translate_inst(
    scope: &Scope,
    proof: &HolProof,
    substitutions: &[crate::hol_light_import::HolTermSubstitution],
    symbols: &mut SymbolCollector,
) -> Result<CheckedTheorem, HolLightImportError> {
    let sub = translate_proof(scope, proof, symbols)?;
    let mut translator = TermTranslator::new(symbols);
    validate_term_substitutions(scope, substitutions, &translator)?;
    let assumptions = sub
        .assumptions
        .iter()
        .map(|assumption| substitute_term(assumption, substitutions, &mut Vec::new()))
        .collect::<Vec<_>>();
    let conclusion = substitute_term(&sub.conclusion, substitutions, &mut Vec::new());
    let lift = assumptions.len() as u32;
    let binder_args = instantiated_term_scope_args(scope, substitutions, lift, &mut translator)?;
    let available = available_assumptions(
        &assumptions,
        &assumption_args_in_context(scope, assumptions.len(), 0),
    );
    let expected = sub
        .assumptions
        .iter()
        .map(|assumption| substitute_term(assumption, substitutions, &mut Vec::new()))
        .collect::<Vec<_>>();
    let body = apply_proof(
        &sub.proof,
        &binder_args,
        &match_assumption_args(&expected, &available)?,
    );
    theorem_from_body(scope, assumptions, conclusion, body, &mut translator)
}

fn translate_inst_type(
    scope: &Scope,
    proof: &HolProof,
    substitutions: &[crate::hol_light_import::HolTypeSubstitution],
    symbols: &mut SymbolCollector,
) -> Result<CheckedTheorem, HolLightImportError> {
    let sub = translate_proof(scope, proof, symbols)?;
    let mut translator = TermTranslator::new(symbols);
    let assumptions = sub
        .assumptions
        .iter()
        .map(|assumption| substitute_type_in_term(assumption, substitutions))
        .collect::<Vec<_>>();
    let conclusion = substitute_type_in_term(&sub.conclusion, substitutions);
    let lift = assumptions.len() as u32;
    let binder_args = instantiated_type_scope_args(scope, substitutions, lift, &mut translator)?;
    let available = available_assumptions(
        &assumptions,
        &assumption_args_in_context(scope, assumptions.len(), 0),
    );
    let expected = sub
        .assumptions
        .iter()
        .map(|assumption| substitute_type_in_term(assumption, substitutions))
        .collect::<Vec<_>>();
    let body = apply_proof(
        &sub.proof,
        &binder_args,
        &match_assumption_args(&expected, &available)?,
    );
    theorem_from_body(scope, assumptions, conclusion, body, &mut translator)
}
