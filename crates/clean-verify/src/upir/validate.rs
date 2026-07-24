// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural validation for UPIR terms.

use super::syntax::{
    SourceLoc, UpirExpr, UpirForeignExpr, UpirLevel, UpirMatchArm, UpirName, UpirPattern,
    UpirProjection, UpirProof, UpirSort,
};
use std::collections::HashSet;

/// Structural validation errors for UPIR.
#[derive(Debug, thiserror::Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum UpirValidationError {
    #[error("empty {kind}")]
    EmptyName { kind: &'static str },
    #[error("qualified name contains an empty segment")]
    EmptyNameSegment,
    #[error("duplicate universe parameter `{0}`")]
    DuplicateUniverseParam(String),
    #[error("unbound universe parameter `{0}`")]
    UnboundUniverseParam(String),
    #[error("unbound de Bruijn variable #{index} at depth {depth}")]
    UnboundVar { index: u32, depth: usize },
    #[error("projection index must be greater than zero")]
    ProjectionIndexZero,
    #[error("pattern binder `{0}` is duplicated in the same branch")]
    DuplicatePatternBinder(String),
    #[error("holes are not allowed in validated proofs")]
    HoleNotAllowed(u64),
    #[error("{kind} cannot be empty")]
    EmptyPayload { kind: &'static str },
}

pub(crate) fn validate_proof(proof: &UpirProof) -> Result<(), UpirValidationError> {
    proof.name.validate()?;

    let mut seen = HashSet::new();
    for param in &proof.universe_params {
        validate_universe_param_name(param)?;
        if !seen.insert(param.clone()) {
            return Err(UpirValidationError::DuplicateUniverseParam(param.clone()));
        }
    }

    if let Some(statement) = &proof.statement {
        validate_expr(statement, &proof.universe_params)?;
    }
    validate_expr(&proof.proof, &proof.universe_params)
}

pub(crate) fn validate_expr(
    expr: &UpirExpr,
    universe_params: &[String],
) -> Result<(), UpirValidationError> {
    validate_expr_with_depth(expr, universe_params, 0)
}

fn validate_expr_with_depth(
    expr: &UpirExpr,
    universe_params: &[String],
    depth: usize,
) -> Result<(), UpirValidationError> {
    match expr {
        UpirExpr::Var(index) => {
            if usize::try_from(*index).expect("u32 always fits in usize") >= depth {
                return Err(UpirValidationError::UnboundVar {
                    index: *index,
                    depth,
                });
            }
        }
        UpirExpr::Sort(sort) => validate_sort(sort, universe_params)?,
        UpirExpr::Const {
            name, universes, ..
        } => {
            validate_name(name)?;
            for level in universes {
                validate_level(level, universe_params)?;
            }
        }
        UpirExpr::App(func, arg) => {
            validate_expr_with_depth(func, universe_params, depth)?;
            validate_expr_with_depth(arg, universe_params, depth)?;
        }
        UpirExpr::Lambda {
            binder,
            domain,
            body,
        }
        | UpirExpr::Pi {
            binder,
            domain,
            body,
        } => {
            validate_binder_name(binder.name.as_deref())?;
            validate_expr_with_depth(domain, universe_params, depth)?;
            validate_expr_with_depth(body, universe_params, depth + 1)?;
        }
        UpirExpr::Let {
            binder,
            type_,
            value,
            body,
        } => {
            validate_binder_name(binder.name.as_deref())?;
            validate_expr_with_depth(type_, universe_params, depth)?;
            validate_expr_with_depth(value, universe_params, depth)?;
            validate_expr_with_depth(body, universe_params, depth + 1)?;
        }
        UpirExpr::Match {
            scrutinee,
            motive,
            arms,
            ..
        } => {
            validate_expr_with_depth(scrutinee, universe_params, depth)?;
            if let Some(motive) = motive {
                validate_expr_with_depth(motive, universe_params, depth + 1)?;
            }
            if arms.is_empty() {
                return Err(UpirValidationError::EmptyPayload { kind: "match arms" });
            }
            for arm in arms {
                validate_arm(arm, universe_params, depth)?;
            }
        }
        UpirExpr::Proj { expr, projection } => {
            validate_expr_with_depth(expr, universe_params, depth)?;
            match projection {
                UpirProjection::Index(0) => return Err(UpirValidationError::ProjectionIndexZero),
                UpirProjection::Index(_) => {}
                UpirProjection::Field(field) if field.is_empty() => {
                    return Err(UpirValidationError::EmptyName {
                        kind: "projection field",
                    });
                }
                UpirProjection::Field(_) => {}
            }
        }
        UpirExpr::Annot { expr, type_ } => {
            validate_expr_with_depth(expr, universe_params, depth)?;
            validate_expr_with_depth(type_, universe_params, depth)?;
        }
        UpirExpr::Literal(_) => {}
        UpirExpr::SourceLoc { expr, loc } => {
            validate_source_loc(loc)?;
            validate_expr_with_depth(expr, universe_params, depth)?;
        }
        UpirExpr::Hole { id, .. } => return Err(UpirValidationError::HoleNotAllowed(*id)),
        UpirExpr::Foreign(foreign) => validate_foreign(foreign)?,
    }

    Ok(())
}

fn validate_binder_name(name: Option<&str>) -> Result<(), UpirValidationError> {
    if matches!(name, Some("")) {
        return Err(UpirValidationError::EmptyName {
            kind: "binder name",
        });
    }
    Ok(())
}

fn validate_universe_param_name(name: &str) -> Result<(), UpirValidationError> {
    if name.is_empty() {
        return Err(UpirValidationError::EmptyName {
            kind: "universe parameter",
        });
    }
    Ok(())
}

fn validate_name(name: &UpirName) -> Result<(), UpirValidationError> {
    name.validate()
}

fn validate_level(
    level: &UpirLevel,
    universe_params: &[String],
) -> Result<(), UpirValidationError> {
    match level {
        UpirLevel::Zero => {}
        UpirLevel::Succ(inner) => validate_level(inner, universe_params)?,
        UpirLevel::Max(lhs, rhs) | UpirLevel::IMax(lhs, rhs) => {
            validate_level(lhs, universe_params)?;
            validate_level(rhs, universe_params)?;
        }
        UpirLevel::Param(name) => {
            validate_universe_param_name(name)?;
            if !universe_params.iter().any(|param| param == name) {
                return Err(UpirValidationError::UnboundUniverseParam(name.clone()));
            }
        }
    }
    Ok(())
}

fn validate_sort(sort: &UpirSort, universe_params: &[String]) -> Result<(), UpirValidationError> {
    match sort {
        UpirSort::Prop => Ok(()),
        UpirSort::Type(level) => validate_level(level, universe_params),
        UpirSort::Foreign { descriptor, .. } => {
            if descriptor.is_empty() {
                Err(UpirValidationError::EmptyPayload {
                    kind: "foreign sort descriptor",
                })
            } else {
                Ok(())
            }
        }
    }
}

fn validate_arm(
    arm: &UpirMatchArm,
    universe_params: &[String],
    depth: usize,
) -> Result<(), UpirValidationError> {
    validate_pattern(&arm.pattern)?;
    let mut names = Vec::new();
    arm.pattern.bound_names(&mut names);
    let mut seen = HashSet::new();
    for name in names.iter().filter_map(Clone::clone) {
        if !seen.insert(name.clone()) {
            return Err(UpirValidationError::DuplicatePatternBinder(name));
        }
    }
    validate_expr_with_depth(&arm.body, universe_params, depth + names.len())
}

fn validate_pattern(pattern: &UpirPattern) -> Result<(), UpirValidationError> {
    match pattern {
        UpirPattern::Wildcard | UpirPattern::Literal(_) => {}
        UpirPattern::Var(name) => {
            validate_binder_name(name.as_deref())?;
        }
        UpirPattern::Ctor { name, args } => {
            validate_name(name)?;
            for arg in args {
                validate_pattern(arg)?;
            }
        }
    }
    Ok(())
}

fn validate_source_loc(loc: &SourceLoc) -> Result<(), UpirValidationError> {
    if loc.file.is_empty() {
        return Err(UpirValidationError::EmptyName {
            kind: "source location file",
        });
    }
    Ok(())
}

fn validate_foreign(foreign: &UpirForeignExpr) -> Result<(), UpirValidationError> {
    match foreign {
        UpirForeignExpr::CoqSet | UpirForeignExpr::CoqSProp | UpirForeignExpr::AgdaInterval => {}
        UpirForeignExpr::HolType { repr } | UpirForeignExpr::MizarTerm { repr } => {
            if repr.is_empty() {
                return Err(UpirValidationError::EmptyPayload {
                    kind: "foreign representation",
                });
            }
        }
        UpirForeignExpr::HolConst { name, type_args } => {
            validate_name(name)?;
            if type_args.iter().any(String::is_empty) {
                return Err(UpirValidationError::EmptyPayload {
                    kind: "HOL type argument",
                });
            }
        }
        UpirForeignExpr::MetamathExpr { symbols } => {
            if symbols.is_empty() || symbols.iter().any(String::is_empty) {
                return Err(UpirValidationError::EmptyPayload {
                    kind: "Metamath symbol list",
                });
            }
        }
    }
    Ok(())
}
