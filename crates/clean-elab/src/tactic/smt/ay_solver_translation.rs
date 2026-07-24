// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Translation-sync helpers for the proof-producing SMT solver.

#[cfg(feature = "ay-smt")]
use super::ay_refutation::instantiate_exists_predicate;
#[cfg(feature = "ay-smt")]
use super::ay_solver_types::ExistsWitnessBinding;
#[cfg(feature = "ay-smt")]
use super::ay_types::smt_sort_to_lean_type;
#[cfg(feature = "ay-smt")]
use crate::tactic::smt_translate::{ExistsSkolemization, SmtLibTranslator};
#[cfg(feature = "ay-smt")]
use clean_auto::bridge::ay_contract::{AyError, AyProofBackend, AyResult, VariableMapping};
#[cfg(feature = "ay-smt")]
use clean_kernel::{name::Name, Expr, ExprKind, FVarId, Level};
#[cfg(feature = "ay-smt")]
use std::collections::HashMap;

#[cfg(feature = "ay-smt")]
pub(super) struct SyncedTranslation {
    pub(super) formula: String,
    pub(super) new_exists_skolemizations: Vec<ExistsSkolemization>,
}

#[cfg(feature = "ay-smt")]
#[derive(Debug, Clone)]
pub(super) struct ExistsShape {
    pub(super) levels: Vec<Level>,
    pub(super) binder_type: Expr,
    pub(super) predicate: Expr,
}

#[cfg(feature = "ay-smt")]
pub(super) fn translate_expr_with_sync(
    backend: &mut AyProofBackend,
    translator: &mut SmtLibTranslator,
    var_map: &mut VariableMapping,
    expr: &Expr,
) -> AyResult<SyncedTranslation> {
    let decl_count_before = translator.declarations().len();
    let var_decl_count_before = translator.var_declarations().len();
    let func_decl_count_before = translator.func_declarations().len();
    let exists_count_before = translator.exists_skolemizations().len();
    let formula = translator
        .translate_expr(expr)
        .map_err(|e| AyError::UnsupportedExpr(e.to_string()))?;

    sync_new_translator_declarations(backend, translator, decl_count_before);

    for vd in &translator.var_declarations()[var_decl_count_before..] {
        if let Some(lean_expr) = &vd.lean_expr {
            let lean_ty = smt_sort_to_lean_type(vd.sort);
            var_map.register_var(&vd.name, lean_expr.clone(), lean_ty);
        }
    }
    for decl in &translator.func_declarations()[func_decl_count_before..] {
        var_map.register_var(&decl.name, decl.lean_expr.clone(), decl.lean_ty.clone());
    }

    Ok(SyncedTranslation {
        formula,
        new_exists_skolemizations: translator.exists_skolemizations()[exists_count_before..]
            .to_vec(),
    })
}

#[cfg(feature = "ay-smt")]
pub(super) fn sync_new_translator_declarations(
    backend: &mut AyProofBackend,
    translator: &SmtLibTranslator,
    decl_count_before: usize,
) {
    for decl in &translator.declarations()[decl_count_before..] {
        backend.add_raw_declaration(decl);
    }
}

#[cfg(feature = "ay-smt")]
pub(super) fn is_literal_false_goal(prop: &Expr) -> bool {
    matches!(
        prop.strip_mdata().kind(),
        ExprKind::Const(name, _) if *name == Name::from_string("False")
    )
}

#[cfg(feature = "ay-smt")]
pub(super) fn register_exists_witness_bindings(
    var_map: &mut VariableMapping,
    exists_bindings: &mut Vec<ExistsWitnessBinding>,
    next_exists_placeholder_fvar: &mut u64,
    source_hyp_fvar: FVarId,
    source_exists_prop: &Expr,
    skolemizations: &[ExistsSkolemization],
) -> AyResult<()> {
    let mut source_exists_proof = Expr::fvar(source_hyp_fvar);
    let mut current_source_prop = source_exists_prop.clone();
    let mut translator_placeholder_bindings: HashMap<FVarId, Expr> = HashMap::new();
    for skolemization in skolemizations {
        let exists_shape = parse_exists_shape(&current_source_prop).ok_or_else(|| {
            AyError::UnsupportedExpr(format!(
                "malformed Exists witness state for {}: expected fully applied Exists, got {:?}",
                skolemization.skolem_smt_name, current_source_prop
            ))
        })?;
        let normalized_predicate = normalize_skolemized_exists_predicate(
            &skolemization.predicate,
            &translator_placeholder_bindings,
        );
        if exists_shape.binder_type != skolemization.binder_type
            || exists_shape.predicate != normalized_predicate
        {
            return Err(AyError::UnsupportedExpr(format!(
                "malformed Exists witness state for {}: source proposition no longer matches skolemization metadata: {:?}",
                skolemization.skolem_smt_name, current_source_prop
            )));
        }
        let (witness_fvar, witness_proof_fvar) =
            fresh_exists_placeholder_pair(next_exists_placeholder_fvar);
        let witness_expr = Expr::fvar(witness_fvar);
        let witness_prop = instantiate_exists_predicate(&normalized_predicate, &witness_expr);
        let witness_proof_expr = Expr::fvar(witness_proof_fvar);

        var_map.register_var(
            &skolemization.skolem_smt_name,
            witness_expr.clone(),
            exists_shape.binder_type.clone(),
        );
        var_map.register_hypothesis(
            &skolemization.skolem_smt_name,
            witness_proof_fvar,
            witness_proof_expr.clone(),
            witness_prop.clone(),
        );
        exists_bindings.push(ExistsWitnessBinding {
            skolem_smt_name: skolemization.skolem_smt_name.clone(),
            source_hyp_fvar,
            source_exists_proof: source_exists_proof.clone(),
            source_exists_levels: exists_shape.levels,
            binder_type: exists_shape.binder_type.clone(),
            predicate: normalized_predicate.clone(),
            witness_fvar,
            witness_proof_fvar,
        });
        translator_placeholder_bindings.insert(
            skolemization.translator_placeholder_fvar,
            witness_expr.clone(),
        );
        source_exists_proof = witness_proof_expr;
        current_source_prop = witness_prop;
    }
    Ok(())
}

#[cfg(feature = "ay-smt")]
pub(super) fn is_exists_hypothesis(expr: &Expr) -> bool {
    parse_exists_shape(expr).is_some()
}

#[cfg(feature = "ay-smt")]
fn normalize_skolemized_exists_predicate(
    predicate: &Expr,
    translator_placeholder_bindings: &HashMap<FVarId, Expr>,
) -> Expr {
    let mut normalized = predicate.clone();
    for (translator_fvar, solver_witness) in translator_placeholder_bindings {
        normalized = normalized.subst_fvar(*translator_fvar, solver_witness);
    }
    normalized
}

#[cfg(feature = "ay-smt")]
fn fresh_exists_placeholder_pair(next_exists_placeholder_fvar: &mut u64) -> (FVarId, FVarId) {
    let witness_id = *next_exists_placeholder_fvar;
    let witness_proof_id = witness_id
        .checked_add(1)
        .expect("exists placeholder allocator overflowed proof witness id");
    *next_exists_placeholder_fvar = witness_proof_id
        .checked_add(1)
        .expect("exists placeholder allocator overflowed next free id");

    let witness_fvar = FVarId::new(witness_id);
    let witness_proof_fvar = FVarId::new(witness_proof_id);
    assert!(
        !witness_fvar.is_sentinel(),
        "exists placeholder allocator entered sentinel range at witness {}",
        witness_fvar.as_u64()
    );
    assert!(
        !witness_proof_fvar.is_sentinel(),
        "exists placeholder allocator entered sentinel range at witness proof {}",
        witness_proof_fvar.as_u64()
    );
    (witness_fvar, witness_proof_fvar)
}

#[cfg(feature = "ay-smt")]
pub(super) fn parse_exists_shape(expr: &Expr) -> Option<ExistsShape> {
    let stripped = expr.strip_mdata();
    let args = stripped.get_app_args();
    match stripped.get_app_fn().kind() {
        ExprKind::Const(name, levels)
            if *name == Name::from_string("Exists") && args.len() == 2 =>
        {
            Some(ExistsShape {
                levels: levels.to_vec(),
                binder_type: args[0].clone(),
                predicate: args[1].clone(),
            })
        }
        _ => None,
    }
}
