// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original-source equations for independently typed Bool/UInt parameters.
//! Boolean elimination is a CIC proof construction, never sampled execution.
use super::*;
use crate::{ScalarDenotation, ScalarSort};

#[cfg(test)]
#[path = "scalar/export.rs"]
mod export;
#[cfg(test)]
#[path = "scalar/mixed_tests.rs"]
mod mixed_tests;
#[cfg(test)]
mod tests;

fn equality(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, lhs, rhs],
    )
}

fn judgment(source: &Name, denotation: &ScalarDenotation, parameters: &[Expr]) -> (Expr, Expr) {
    let result = denotation.result();
    let lhs = result.image(Expr::apps(
        Expr::const_(source.clone(), vec![]),
        parameters.iter().cloned(),
    ));
    let images: Vec<_> = denotation
        .parameters()
        .iter()
        .zip(parameters)
        .rev()
        .map(|(sort, parameter)| sort.image(parameter.clone()))
        .collect();
    let rhs = denotation.body().instantiate_rev(&images);
    let statement = equality(result.model_type(), lhs.clone(), rhs);
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [result.model_type(), lhs],
    );
    (statement, proof)
}

fn telescope(
    source: &Name,
    denotation: &ScalarDenotation,
    parameters: &mut Vec<Expr>,
    split: bool,
) -> (Expr, Expr) {
    let index = parameters.len();
    let Some(sort) = denotation.parameters().get(index).copied() else {
        return judgment(source, denotation, parameters);
    };
    let var = FVarId::new(index as u64);
    parameters.push(Expr::fvar(var));
    let (body, proof) = telescope(source, denotation, parameters, split);
    parameters.pop();
    let statement = Expr::pi(
        BinderInfo::Default,
        sort.source_type(),
        body.abstract_fvar(var),
    );
    let proof = if split && sort == ScalarSort::Bool {
        parameters.push(Expr::const_str("Bool.false"));
        let (_, no) = telescope(source, denotation, parameters, split);
        parameters.pop();
        parameters.push(Expr::const_str("Bool.true"));
        let (_, yes) = telescope(source, denotation, parameters, split);
        parameters.pop();
        Expr::apps(
            // The motive is a proposition, so Bool.rec is instantiated at 0.
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            [
                Expr::lam(
                    BinderInfo::Default,
                    sort.source_type(),
                    body.abstract_fvar(var),
                ),
                no,
                yes,
                Expr::fvar(var),
            ],
        )
    } else {
        proof
    };
    (
        statement,
        Expr::lam(
            BinderInfo::Default,
            sort.source_type(),
            proof.abstract_fvar(var),
        ),
    )
}

fn validate_source(
    environment: &Environment,
    source: &Name,
    denotation: &ScalarDenotation,
) -> Result<[u8; 32], ReflectError> {
    let info = environment
        .get_const(source)
        .ok_or_else(|| ReflectError::unsupported("scalar equation requires the original source"))?;
    let mut signature = denotation.result().source_type();
    for sort in denotation.parameters().iter().rev() {
        signature = Expr::arrow(sort.source_type(), signature);
    }
    if info.kind != ConstantKind::Definition
        || info.value.is_none()
        || !info.level_params.is_empty()
        || info.type_ != signature
        || environment.declaration_verification(source)
            != Some(DeclarationVerification::FullKernelCheck)
    {
        return Err(ReflectError::unsupported(
            "scalar equation requires an exactly typed fully checked monomorphic source definition",
        ));
    }
    environment
        .closure_digest(source)
        .map_err(|error| ReflectError::unsupported(format!("scalar source closure: {error}")))
}

fn conditional_boolean_proof(
    environment: &Environment,
    source: &Name,
    denotation: &ScalarDenotation,
) -> Option<Expr> {
    if denotation.result() != ScalarSort::Bool {
        return None;
    }
    let ScalarSort::UInt(width) = *denotation.parameters().first()? else {
        return None;
    };
    if denotation
        .parameters()
        .iter()
        .any(|sort| *sort != ScalarSort::UInt(width))
    {
        return None;
    }
    let params: Vec<_> = (0..denotation.parameters().len())
        .map(|i| Expr::fvar(FVarId::new(i as u64)))
        .collect();
    let images: Vec<_> = params
        .iter()
        .rev()
        .map(|value| ScalarSort::UInt(width).image(value.clone()))
        .collect();
    let rhs = denotation.body().instantiate_rev(&images);
    let mut proof = conditional::boolean_candidate(
        environment,
        width,
        &params,
        environment.get_const(source)?.value.as_ref()?,
        &rhs,
    )?;
    for i in (0..params.len()).rev() {
        proof = Expr::lam(
            BinderInfo::Default,
            ScalarSort::UInt(width).source_type(),
            proof.abstract_fvar(FVarId::new(i as u64)),
        );
    }
    Some(proof)
}

/// Check a proof against the complete original-source equation, deriving the
/// proposition from the actual typed IR denotation rather than trusting a
/// caller-supplied proposition. The normal certification audit remains required.
pub fn check_scalar_source_equation_with_proof(
    environment: &Environment,
    source: &Name,
    denotation: &ScalarDenotation,
    theorem_name: Name,
    proof: Expr,
) -> Result<CheckedSourceEquation, ReflectError> {
    let digest = validate_source(environment, source, denotation)?;
    let (statement, _) = telescope(source, denotation, &mut vec![], false);
    certify_equation(environment, source, digest, theorem_name, statement, proof)
}

/// Construct a conversion proof, then try exhaustive Boolean elimination.
/// Arithmetic identities beyond conversion still require their own proof;
/// failure is an unsupported judgment, never a substituted model theorem.
pub fn check_scalar_source_equation(
    environment: &Environment,
    source: &Name,
    denotation: &ScalarDenotation,
    theorem_name: Name,
) -> Result<CheckedSourceEquation, ReflectError> {
    let digest = validate_source(environment, source, denotation)?;
    let (statement, proof) = telescope(source, denotation, &mut vec![], false);
    if environment
        .audit_certification(&statement, &proof)
        .is_certified()
    {
        return certify_equation(environment, source, digest, theorem_name, statement, proof);
    }
    if let Some(candidate) = conditional_boolean_proof(environment, source, denotation) {
        if environment
            .audit_certification(&statement, &candidate)
            .is_certified()
        {
            return certify_equation(
                environment,
                source,
                digest,
                theorem_name,
                statement,
                candidate,
            );
        }
    }
    if denotation
        .parameters()
        .iter()
        .filter(|sort| **sort == ScalarSort::Bool)
        .count()
        > 8
    {
        return Err(ReflectError::unsupported(
            "scalar Boolean elimination exceeds 256 leaves",
        ));
    }
    let (statement, proof) = telescope(source, denotation, &mut vec![], true);
    certify_equation(environment, source, digest, theorem_name, statement, proof)
}
