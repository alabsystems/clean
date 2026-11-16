// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Kernel-checked equations from an ACTUAL source definition to a scalar
//! denotation. Unlike a comparison between two reflected Nat models, the left
//! side names the original checked definition in its original environment:
//!
//! ```text
//! forall (x0 ... : UIntW),
//!   UIntW.toNat (source x0 ...) = denotation (UIntW.toNat x0) ...
//! ```
//!
//! The proof procedure first tries conversion, then CIC arithmetic proofs
//! for wrapping subtraction, bounded bitwise composition and actual source
//! conditionals. It adds no reducer,
//! axiom or assumed bridge.
//! In particular, a legitimate equation requiring arithmetic lemmas may refuse.
//! The returned object proves exactly its stored equation. It does NOT prove
//! that the supplied denotation was derived from emitted IR, that elaboration
//! preserves Lean source semantics, or that the executable implements the IR.
//! Source/IR binding, independent source-environment replay, runtime ownership,
//! target ABI and machine-code correctness remain separate obligations. No
//! module, certificate, body gate or proof grade is modified here.

use clean_kernel::{
    BinderInfo, ConstantKind, Declaration, DeclarationVerification, Environment, Expr, FVarId,
    Level, Name,
};

use crate::{ReflectError, TvDenotation};

mod bitwise;
mod conditional;
mod scalar;
mod subtraction;
pub use scalar::{check_scalar_source_equation, check_scalar_source_equation_with_proof};

/// A source equation actually accepted by the kernel in the supplied original
/// environment. Private fields prevent constructing this from a status label.
#[derive(Debug, Clone)]
pub struct CheckedSourceEquation {
    source: Name,
    source_closure_digest: [u8; 32],
    equation_closure_digest: [u8; 32],
    declaration: Declaration,
}

impl CheckedSourceEquation {
    #[must_use]
    pub fn source(&self) -> &Name {
        &self.source
    }

    /// Identity of the source dependency closure at the actual kernel check.
    /// A changed environment must be checked again, never silently restamped.
    #[must_use]
    pub fn source_closure_digest(&self) -> &[u8; 32] {
        &self.source_closure_digest
    }

    /// Binds the complete checked theorem, including the denotation and proof
    /// dependencies that need not occur in the source's own dependency closure.
    #[must_use]
    pub fn equation_closure_digest(&self) -> &[u8; 32] {
        &self.equation_closure_digest
    }

    /// Exact proposition and proof bytes to replay with that original source
    /// environment. The declaration alone is not independent replay evidence.
    #[must_use]
    pub fn declaration(&self) -> &Declaration {
        &self.declaration
    }
}

/// Prove a universal equation about the actual monomorphic source definition,
/// with genuine UInt binders (not arbitrary unbounded Nat inputs).
///
/// The supplied denotation must be call-free and use a supported scalar width.
/// Its arity and type are enforced by the kernel on the complete proposition.
/// This bounded conversion/arithmetic procedure does not stand in for the remaining
/// source-refinement proof procedures or independently derived IR semantics.
///
/// # Errors
///
/// Refuses unsupported shape, unknown source/closure, kernel rejection, an
/// unknown axiom closure, or any non-foundational axiom dependency.
pub fn check_uint_source_equation(
    environment: &Environment,
    source: &Name,
    denotation: &TvDenotation,
    theorem_name: Name,
) -> Result<CheckedSourceEquation, ReflectError> {
    let arity = u32::try_from(denotation.arity).map_err(|_| {
        ReflectError::unsupported("source equation parameter count exceeds the bounded fragment")
    })?;
    if !matches!(denotation.width, 8 | 16 | 32 | 64)
        || !denotation.callees.is_empty()
        || arity > 64
        || denotation.body.has_fvar_quick()
        || denotation.body.has_expr_mvar_quick()
        || denotation.body.has_level_mvar_quick()
        || denotation.body.has_level_param_quick()
        || denotation.body.loose_bvar_range() > arity
    {
        return Err(ReflectError::unsupported(
            "source equation requires a closed call-free UInt8/16/32/64 denotation with at most 64 parameters",
        ));
    }
    let info = environment.get_const(source).ok_or_else(|| {
        ReflectError::unsupported("source equation requires the original source declaration")
    })?;
    if !info.level_params.is_empty() || info.value.is_none() {
        return Err(ReflectError::unsupported(
            "source equation requires a monomorphic source definition with a body",
        ));
    }
    let source_closure_digest = environment.closure_digest(source).map_err(|error| {
        ReflectError::unsupported(format!("source equation source digest: {error}"))
    })?;
    let uint = Expr::const_(
        Name::from_string(&format!("UInt{}", denotation.width)),
        vec![],
    );
    let to_nat = Expr::const_(
        Name::from_string(&format!("UInt{}.toNat", denotation.width)),
        vec![],
    );
    let params: Vec<_> = (0..denotation.arity)
        .map(|i| Expr::fvar(FVarId::new(i as u64)))
        .collect();
    let source_value = Expr::apps(Expr::const_(source.clone(), vec![]), params.iter().cloned());
    let lhs = Expr::app(to_nat.clone(), source_value);
    // instantiate_rev[0] is the INNERMOST binder. Preserve the original
    // source/IR parameter order when replacing the denotation's telescope.
    let nat_params: Vec<_> = params
        .iter()
        .rev()
        .map(|x| Expr::app(to_nat.clone(), x.clone()))
        .collect();
    let rhs = denotation.body.instantiate_rev(&nat_params);
    let mut candidates: Vec<_> = [
        subtraction::candidate(denotation.width, &params, &rhs),
        bitwise::candidate(denotation.width, &params, &rhs),
        bitwise::shifted_candidate(denotation.width, &params, &rhs),
        info.value.as_ref().and_then(|body| {
            conditional::candidate(environment, denotation.width, &params, body, &rhs)
        }),
    ]
    .into_iter()
    .flatten()
    .collect();
    let mut statement = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_str("Nat"), lhs.clone(), rhs],
    );
    let mut proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Nat"), lhs],
    );
    for i in (0..denotation.arity).rev() {
        let var = FVarId::new(i as u64);
        statement = Expr::pi(
            BinderInfo::Default,
            uint.clone(),
            statement.abstract_fvar(var),
        );
        proof = Expr::lam(BinderInfo::Default, uint.clone(), proof.abstract_fvar(var));
        for candidate in &mut candidates {
            *candidate = Expr::lam(
                BinderInfo::Default,
                uint.clone(),
                candidate.abstract_fvar(var),
            );
        }
    }
    // Use the kernel's canonical expression-rooted strict certification audit.
    // add_decl success alone is insufficient: non-certifying import paths can
    // admit structural/unchecked dependencies or park a proof as an axiom.
    // This checks the ORIGINAL judgment and its full type/value closure,
    // canonical foundation CONTENTS, staged/unsafe/partial and provenance.
    let audit = environment.audit_certification(&statement, &proof);
    if !audit.is_certified() {
        // A present but ill-typed search candidate must not suppress a later
        // valid one. Each is checked against the SAME full original judgment.
        let mut failures = Vec::new();
        let Some(candidate) = candidates.into_iter().find(|candidate| {
            let check = environment.audit_certification(&statement, candidate);
            if check.is_certified() {
                true
            } else {
                failures.push(check.issues);
                false
            }
        }) else {
            return Err(ReflectError::unsupported(format!(
                "source equation certification rejection: {:?}; proof search rejections: {failures:?}",
                audit.issues
            )));
        };
        proof = candidate;
    }
    admit_equation(
        environment,
        source,
        source_closure_digest,
        theorem_name,
        statement,
        proof,
    )
}

// Both source APIs must pass the same original-judgment audit and exact
// theorem admission checks. A successful proof search is never authority.
fn certify_equation(
    environment: &Environment,
    source: &Name,
    source_closure_digest: [u8; 32],
    theorem_name: Name,
    statement: Expr,
    proof: Expr,
) -> Result<CheckedSourceEquation, ReflectError> {
    let audit = environment.audit_certification(&statement, &proof);
    if !audit.is_certified() {
        return Err(ReflectError::unsupported(format!(
            "source equation certification rejection: {:?}",
            audit.issues
        )));
    }
    admit_equation(
        environment,
        source,
        source_closure_digest,
        theorem_name,
        statement,
        proof,
    )
}

fn admit_equation(
    environment: &Environment,
    source: &Name,
    source_closure_digest: [u8; 32],
    theorem_name: Name,
    statement: Expr,
    proof: Expr,
) -> Result<CheckedSourceEquation, ReflectError> {
    let declaration = Declaration::Theorem {
        name: theorem_name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    };
    // Never check in a fresh/model-only environment: the equation must name
    // this source's actual definition, including its actual dictionary fields.
    let mut checker = environment.clone();
    checker.add_decl(declaration.clone()).map_err(|error| {
        ReflectError::unsupported(format!("source equation kernel rejection: {error:?}"))
    })?;
    let admitted = checker
        .get_const(&theorem_name)
        .ok_or_else(|| ReflectError::unsupported("source equation theorem was not admitted"))?;
    let Declaration::Theorem { type_, value, .. } = &declaration else {
        return Err(ReflectError::unsupported(
            "source equation requires a theorem",
        ));
    };
    if admitted.kind != ConstantKind::Theorem
        || admitted.type_ != *type_
        || admitted.value.as_ref() != Some(value)
        || checker.declaration_verification(&theorem_name)
            != Some(DeclarationVerification::FullKernelCheck)
    {
        return Err(ReflectError::unsupported(
            "source equation admission did not retain the exact fully checked theorem",
        ));
    }
    let equation_closure_digest = checker.closure_digest(&theorem_name).map_err(|error| {
        ReflectError::unsupported(format!("source equation proof digest: {error}"))
    })?;
    Ok(CheckedSourceEquation {
        source: source.clone(),
        source_closure_digest,
        equation_closure_digest,
        declaration,
    })
}

#[cfg(test)]
mod tests;
