// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Helpers for lifting reconstructed ay refutations into goal proofs.

#[cfg(feature = "ay-smt")]
use super::ay_solver::ExistsWitnessBinding;
use clean_kernel::{name::Name, BinderInfo, Expr, ExprKind, FVarId};

/// Wrap a proof of `False` under `¬goal` into a proof of `goal`.
///
/// ay proof reconstruction returns a refutation of the negated goal. When the
/// refutation depends on the explicit `¬goal` assumption, `negated_goal_fvar`
/// identifies the witness to abstract before applying
/// `Classical.byContradiction`.
#[cfg(feature = "ay-smt")]
pub(super) fn wrap_refutation_as_goal_proof(
    goal: &Expr,
    negated_goal: &Expr,
    refutation: Expr,
    negated_goal_fvar: Option<FVarId>,
) -> Expr {
    if matches!(goal.kind(), ExprKind::Const(name, _) if *name == Name::from_string("False"))
        && negated_goal_fvar.is_none()
    {
        return refutation;
    }

    let body = match negated_goal_fvar {
        Some(fvar_id) => refutation.abstract_fvar(fvar_id),
        None => refutation,
    };
    let proof_fun = Expr::lam(BinderInfo::Default, negated_goal.clone(), body);

    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Classical.byContradiction"), vec![]),
            goal.clone(),
        ),
        proof_fun,
    )
}

#[cfg(feature = "ay-smt")]
pub(super) fn instantiate_exists_predicate(predicate: &Expr, witness: &Expr) -> Expr {
    match predicate.strip_mdata().kind() {
        ExprKind::Lam(_, _, body) => body.instantiate(witness),
        _ => Expr::app(predicate.clone(), witness.clone()),
    }
}

#[cfg(feature = "ay-smt")]
pub(super) fn close_exists_witness_bindings(
    mut refutation: Expr,
    exists_bindings: &[ExistsWitnessBinding],
) -> Expr {
    for binding in exists_bindings.iter().rev() {
        let witness_expr = Expr::fvar(binding.witness_fvar);
        let witness_prop = instantiate_exists_predicate(&binding.predicate, &witness_expr);
        let proof_body = refutation.abstract_fvar(binding.witness_proof_fvar);
        let proof_fun = Expr::lam(BinderInfo::Default, witness_prop, proof_body);
        let witness_fun = Expr::lam(
            BinderInfo::Default,
            binding.binder_type.clone(),
            proof_fun.abstract_fvar(binding.witness_fvar),
        );

        refutation = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Exists.elim"),
                                binding.source_exists_levels.clone(),
                            ),
                            binding.binder_type.clone(),
                        ),
                        binding.predicate.clone(),
                    ),
                    Expr::const_(Name::from_string("False"), vec![]),
                ),
                binding.source_exists_proof.clone(),
            ),
            witness_fun,
        );
    }
    refutation
}
