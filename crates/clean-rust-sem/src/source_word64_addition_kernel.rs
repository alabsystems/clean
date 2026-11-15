// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Independent source-model mathematics for `u64::wrapping_add` by a literal.
//!
//! The checked semantics is natural addition modulo exactly 2^64. Its universal
//! theorem preserves an arbitrary world and an empty event trace. It applies to
//! every source environment, so includes every valid u64 input without sampling
//! or a possibly uninhabited admission premise. This models only the strict
//! original-source grammar below; it authenticates no Rustc type resolution,
//! Instance, IR, native ABI, SourceNoUB, proof grade or compiler capability.

use clean_kernel::{Environment, Expr, TypeChecker};
use thiserror::Error;

mod declarations;
mod projection;
#[cfg(test)]
mod tests;

pub use projection::{project_word64_addition_source, AdditionSource};

pub const MODEL: &str = "rust-source.word64-addition-kernel.v1";

#[derive(Debug, Error)]
#[non_exhaustive]
pub enum Word64AdditionError {
    #[error("source word64 addition fragment refused: {0}")]
    Unsupported(&'static str),
    #[error("source word64 addition declaration refused: {0}")]
    Declaration(String),
    #[error("source word64 addition replay refused: {0}")]
    Replay(String),
}

/// Untrusted source syntax data; the original-source projector alone selects
/// argument0. A different index can express a different mathematical model,
/// never a different interpretation of an already supplied original source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceBody {
    pub parameter: u32,
    pub literal: u64,
}
impl SourceBody {
    pub fn reflect(&self) -> Expr {
        Expr::apps(
            declarations::c(declarations::ADD_LITERAL),
            [
                Expr::nat_lit(u64::from(self.parameter)),
                Expr::nat_lit(self.literal),
            ],
        )
    }
}

/// Checked SOURCE-MODEL mathematics only. It cannot be constructed by decoding
/// transport data and has no conversion to an executable or compiler verdict.
#[derive(Debug)]
pub struct AdditionModelProof {
    source: AdditionSource,
    claim: Expr,
    proof: Expr,
}
impl AdditionModelProof {
    pub fn source(&self) -> &AdditionSource {
        &self.source
    }
    pub fn claim(&self) -> &Expr {
        &self.claim
    }
    pub fn proof(&self) -> &Expr {
        &self.proof
    }
}

/// Fresh checked vocabulary. No imported declarations or duplicate-skip path.
pub fn source_environment() -> Result<Environment, Word64AdditionError> {
    let mut env = Environment::new();
    for initialize in [
        Environment::init_nat,
        Environment::init_eq,
        Environment::init_list,
    ] {
        initialize(&mut env).map_err(|e| Word64AdditionError::Declaration(format!("{e:?}")))?;
    }
    declarations::install(&mut env)?;
    Ok(env)
}

/// Install checked mathematical vocabulary into a canonical Nat/Eq/List
/// environment. Duplicate declarations refuse; this returns no proof or source,
/// IR, native or admission authority. A consuming checker must independently
/// bind its complete environment and check its reconstructed expected claim.
pub fn install_source_model(env: &mut Environment) -> Result<(), Word64AdditionError> {
    declarations::install(env)
}

/// Replay a retained proof against the independently reprojected ORIGINAL text.
/// A generic mathematical theorem may be reusable for equivalent spellings;
/// this private wrapper still retains the actual newly supplied source data.
pub fn replay_word64_addition_source(
    original: &str,
    proof: &Expr,
) -> Result<AdditionModelProof, Word64AdditionError> {
    let source = project_word64_addition_source(original)?;
    let claim = source.claim();
    let env = source_environment()?;
    if proof.has_fvar_quick() || proof.has_loose_bvars() {
        return Err(Word64AdditionError::Replay("open proof term".into()));
    }
    let mut checker = TypeChecker::new(&env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker
        .check_type(&claim, &Expr::sort(clean_kernel::Level::zero()))
        .map_err(|e| Word64AdditionError::Replay(format!("claim: {e:?}")))?;
    checker
        .check_type(proof, &claim)
        .map_err(|e| Word64AdditionError::Replay(format!("term: {e:?}")))?;
    if checker.heartbeat_spent() || clean_kernel::tc::declaration_budget_exhausted() {
        return Err(Word64AdditionError::Replay(
            "resource stop is not a verdict".into(),
        ));
    }
    let audit = env.audit_certification(&claim, proof);
    if !audit.is_certified() {
        return Err(Word64AdditionError::Replay(format!(
            "certification audit: {audit:?}"
        )));
    }
    for name in audit.dependencies {
        for closure in [
            env.axiom_deps(&name),
            env.foundational_axiom_deps(&name),
            env.trust_marker_deps(&name),
        ] {
            if !closure
                .ok_or_else(|| Word64AdditionError::Replay("missing dependency closure".into()))?
                .is_empty()
            {
                return Err(Word64AdditionError::Replay(format!(
                    "unexpected axiom/marker: {name:?}"
                )));
            }
        }
    }
    Ok(AdditionModelProof {
        source,
        claim,
        proof: proof.clone(),
    })
}
