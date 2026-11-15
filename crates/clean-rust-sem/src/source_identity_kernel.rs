// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Kernel mathematics for a closed, effect-free Rust source-body fragment.
//!
//! The source syntax is defined independently of Trust-IR. Its only leaves are
//! source variables; wrappers, empty blocks and explicit returns cannot execute
//! a continuation or create effects. The universal adequacy theorem preserves an
//! arbitrary world and an explicitly empty event trace. It holds for every Nat
//! value, hence for every u64 bit pattern, without sampling or a NoUB assumption.
//!
//! This is a source MODEL theorem. The syntax projection and Rust front
//! end remain trusted, and no actual TCX, Instance, FnAbi, SSA or output module is
//! authenticated here. In particular this module has no IR dependency, compiler
//! admission, SourceNoUB, physical ABI or proof-grade constructor. The separate
//! source-to-IR theorem still requires the exact subject and logical Rust-entry
//! interpretation described in `designs/2026-11-06-source-identity-kernel.md`.

use clean_kernel::{Environment, Expr, Name, TypeChecker};
use thiserror::Error;

mod declarations;
mod projection;
#[cfg(test)]
mod tests;

pub use projection::{project_identity_source, IdentitySource};

/// Version of this source-only semantic contract, not a compiler capability.
pub const MODEL: &str = "rust-source.identity-kernel.v1";

/// Closed vocabulary; these values are untrusted source data, never evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SourceBody {
    Variable(u32),
    Wrapper(Box<SourceBody>),
    Block(Box<SourceBody>),
    Return(Box<SourceBody>),
}

#[derive(Debug, Error)]
#[non_exhaustive]
pub enum SourceIdentityError {
    #[error("source identity fragment refused: {0}")]
    Unsupported(&'static str),
    #[error("source identity kernel declaration refused: {0}")]
    Declaration(String),
    #[error("source identity proof replay refused: {0}")]
    Replay(String),
}

/// Retained checked SOURCE-MODEL mathematics only. No runtime/IR authority.
#[derive(Debug)]
pub struct SourceModelProof {
    source: IdentitySource,
    claim: Expr,
    proof: Expr,
}
impl SourceModelProof {
    pub fn source(&self) -> &IdentitySource {
        &self.source
    }
    pub fn claim(&self) -> &Expr {
        &self.claim
    }
    pub fn proof(&self) -> &Expr {
        &self.proof
    }
}

impl SourceBody {
    /// Candidate closed kernel syntax. No declaration or proof is imported.
    pub fn reflect(&self) -> Result<Expr, SourceIdentityError> {
        fn go(body: &SourceBody, depth: usize) -> Result<Expr, SourceIdentityError> {
            if depth >= 128 {
                return Err(SourceIdentityError::Unsupported("source depth"));
            }
            let (name, child) = match body {
                SourceBody::Variable(index) => {
                    return Ok(Expr::app(
                        declarations::c(declarations::VAR),
                        Expr::nat_lit(u64::from(*index)),
                    ))
                }
                SourceBody::Wrapper(body) => (declarations::WRAPPER, body),
                SourceBody::Block(body) => (declarations::BLOCK, body),
                SourceBody::Return(body) => (declarations::RETURN, body),
            };
            Ok(Expr::app(declarations::c(name), go(child, depth + 1)?))
        }
        go(self, 0)
    }
}

/// A new checked semantic environment, with no supplied context or declaration
/// reuse. Duplicate or ill-typed semantic declarations cannot be skipped.
pub fn source_environment() -> Result<Environment, SourceIdentityError> {
    let mut env = Environment::new();
    for initialize in [
        Environment::init_nat,
        Environment::init_eq,
        Environment::init_list,
    ] {
        initialize(&mut env).map_err(|e| SourceIdentityError::Declaration(format!("{e:?}")))?;
    }
    declarations::install(&mut env)?;
    Ok(env)
}

/// Install the exact checked source-model definitions in a caller-owned semantic
/// environment with Nat, Eq and List already installed. Duplicate declarations
/// refuse. This installs vocabulary only; the caller must independently check
/// its own closed claim and audit the complete dependency closure. Canonical
/// standalone replay above still constructs its own environment from scratch.
pub fn install_source_model(env: &mut Environment) -> Result<(), SourceIdentityError> {
    declarations::install(env)
}

/// Reconstruct the expected source claim from the caller's original source text,
/// then replay a retained term in a freshly constructed canonical environment.
/// The supplied term cannot choose its own source, result, world or context.
pub fn replay_identity_source(
    original_source: &str,
    proof: &Expr,
) -> Result<SourceModelProof, SourceIdentityError> {
    let source = project_identity_source(original_source)?;
    let claim = source.claim()?;
    let env = source_environment()?;
    if proof.has_fvar_quick() || proof.has_loose_bvars() {
        return Err(SourceIdentityError::Replay("open proof term".into()));
    }
    let mut checker = TypeChecker::new(&env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker
        .check_type(&claim, &Expr::sort(clean_kernel::Level::zero()))
        .map_err(|e| SourceIdentityError::Replay(format!("claim: {e:?}")))?;
    checker
        .check_type(proof, &claim)
        .map_err(|e| SourceIdentityError::Replay(format!("term: {e:?}")))?;
    if checker.heartbeat_spent() || clean_kernel::tc::declaration_budget_exhausted() {
        return Err(SourceIdentityError::Replay(
            "resource stop is not a verdict".into(),
        ));
    }
    let audit = env.audit_certification(&claim, proof);
    if !audit.is_certified() {
        return Err(SourceIdentityError::Replay(format!(
            "certification audit: {audit:?}"
        )));
    }
    for name in &audit.dependencies {
        for closure in [
            env.axiom_deps(name),
            env.foundational_axiom_deps(name),
            env.trust_marker_deps(name),
        ] {
            if !closure
                .ok_or_else(|| SourceIdentityError::Replay("missing dependency closure".into()))?
                .is_empty()
            {
                return Err(SourceIdentityError::Replay(format!(
                    "unexpected axiom/marker: {name:?}"
                )));
            }
        }
    }
    Ok(SourceModelProof {
        source,
        claim,
        proof: proof.clone(),
    })
}
