// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked relations from an original predicate applied to typed input data to
//! the exact proposition its consumer will admit. The input is data, not a
//! replacement definition of the source predicate. No Formula vocabulary or
//! arithmetic meaning is introduced here.

use super::*;

/// A fully checked equivalence with an application of the original definition.
/// Private construction retains the same source and theorem closure admission
/// boundary as [`CheckedSourceEquation`]. It proves only the stored relation;
/// the consumer must supply its independently expected source, input data and
/// goal again when replaying. This is not an object, IR or codegen license.
#[derive(Debug, Clone)]
pub struct CheckedSourceGoalRelation {
    checked: CheckedSourceEquation,
}

impl CheckedSourceGoalRelation {
    #[must_use]
    pub fn source(&self) -> &Name {
        self.checked.source()
    }

    #[must_use]
    pub fn source_closure_digest(&self) -> &[u8; 32] {
        self.checked.source_closure_digest()
    }

    #[must_use]
    pub fn relation_closure_digest(&self) -> &[u8; 32] {
        self.checked.equation_closure_digest()
    }

    /// Exact checked relation and proof for independent original-environment
    /// replay. These bytes alone do not authenticate the source or input data.
    #[must_use]
    pub fn declaration(&self) -> &Declaration {
        self.checked.declaration()
    }
}

fn scoped(expression: &Expr, binders: u32) -> bool {
    !expression.has_fvar_quick()
        && !expression.has_expr_mvar_quick()
        && !expression.has_level_mvar_quick()
        && !expression.has_level_param_quick()
        && expression.loose_bvar_range() <= binders
}

fn judgment(
    environment: &Environment,
    source: &Name,
    parameters: &[Expr],
    arguments: &[Expr],
    actual_goal: &Expr,
) -> Result<([u8; 32], Expr, Expr), ReflectError> {
    let arity = u32::try_from(parameters.len())
        .map_err(|_| ReflectError::unsupported("source goal relation telescope exceeds u32"))?;
    if arity > 8192
        || arguments.len() > 256
        || parameters.iter().any(|ty| !scoped(ty, 0))
        || arguments.iter().any(|argument| !scoped(argument, arity))
        || !scoped(actual_goal, arity)
    {
        return Err(ReflectError::unsupported(
            "source goal relation requires a bounded closed typed telescope and scoped input/goal data",
        ));
    }
    let info = environment.get_const(source).ok_or_else(|| {
        ReflectError::unsupported("source goal relation requires the original definition")
    })?;
    if info.kind != ConstantKind::Definition
        || info.value.is_none()
        || !info.level_params.is_empty()
        || environment.declaration_verification(source)
            != Some(DeclarationVerification::FullKernelCheck)
    {
        return Err(ReflectError::unsupported(
            "source goal relation requires a fully checked monomorphic original definition",
        ));
    }
    let source_digest = environment.closure_digest(source).map_err(|error| {
        ReflectError::unsupported(format!("source goal relation source closure: {error}"))
    })?;
    let original = Expr::apps(
        Expr::const_(source.clone(), vec![]),
        arguments.iter().cloned(),
    );
    let mut statement = Expr::apps(
        Expr::const_str("Iff"),
        [original.clone(), actual_goal.clone()],
    );
    let mut conversion_proof = Expr::app(Expr::const_str("Iff.rfl"), original);
    for ty in parameters.iter().rev() {
        statement = Expr::pi(BinderInfo::Default, ty.clone(), statement);
        conversion_proof = Expr::lam(BinderInfo::Default, ty.clone(), conversion_proof);
    }
    Ok((source_digest, statement, conversion_proof))
}

/// Produce a conversion proof of the complete original-source goal relation.
///
/// `parameters` lists outermost-first closed binder types. Arguments and the
/// consumer's actual goal use de Bruijn indices under that complete telescope.
/// The kernel checks both sides as propositions and every argument against the
/// original definition's type. Failure to establish conversion is a refusal;
/// no simplified goal, sampled execution or assumed relation is substituted.
///
/// # Errors
/// Refuses unsupported/scoped input, a non-original or unchecked source, a
/// missing closure, failed exact certification or failed theorem admission.
pub fn check_source_goal_relation(
    environment: &Environment,
    source: &Name,
    parameters: &[Expr],
    arguments: &[Expr],
    actual_goal: &Expr,
    theorem_name: Name,
) -> Result<CheckedSourceGoalRelation, ReflectError> {
    let (digest, statement, proof) =
        judgment(environment, source, parameters, arguments, actual_goal)?;
    let checked = certify_equation(environment, source, digest, theorem_name, statement, proof)?;
    Ok(CheckedSourceGoalRelation { checked })
}

/// Check a supplied proof of the same independently derived complete relation.
/// This is the replay boundary and the extension point for a Lean theorem when
/// conversion alone cannot relate the original semantics to the actual goal.
/// The caller supplies expected original inputs; no proposition is recovered
/// from the proof or accepted from a retained status/digest.
///
/// # Errors
/// As [`check_source_goal_relation`], including an ill-typed or non-certifying
/// proof of the exact relation derived from the original source and inputs.
pub fn check_source_goal_relation_with_proof(
    environment: &Environment,
    source: &Name,
    parameters: &[Expr],
    arguments: &[Expr],
    actual_goal: &Expr,
    theorem_name: Name,
    proof: Expr,
) -> Result<CheckedSourceGoalRelation, ReflectError> {
    let (digest, statement, _) = judgment(environment, source, parameters, arguments, actual_goal)?;
    let checked = certify_equation(environment, source, digest, theorem_name, statement, proof)?;
    Ok(CheckedSourceGoalRelation { checked })
}

#[cfg(test)]
#[path = "goal_tests.rs"]
mod tests;
