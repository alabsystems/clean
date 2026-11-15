// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Compiler-only constant replacement at the owning body's source cutoff.
use crate::error::CompilerError;
use crate::implemented_by::CodeMeaning;
use clean_kernel::env::csimp::Rule;
use clean_kernel::{Environment, Name};
use std::collections::HashSet;

pub(crate) fn runtime_name(
    env: &Environment,
    rules: &[Rule],
    name: &Name,
    meaning: CodeMeaning,
) -> Result<Name, CompilerError> {
    if meaning == CodeMeaning::KernelValue {
        return Ok(name.clone());
    }
    validate_metadata(env)?;
    let current = replacement_name(env, rules, name)?;
    // Lean's ToLCNF csimp conversion precedes LCNF's implementedBy pass.
    crate::implemented_by::runtime_const_name_for(env, &current, meaning)
}

/// Resolve source-body dependency names at that body's compilation point.
/// Native dependency discovery and actual lowering must select the same symbols.
/// Kernel-value extraction preserves the names of logical dependencies.
pub fn resolve_dependencies(
    env: &Environment,
    owner: &Name,
    names: Vec<Name>,
    meaning: CodeMeaning,
) -> Result<Vec<Name>, CompilerError> {
    if meaning == CodeMeaning::KernelValue {
        return Ok(names);
    }
    validate_metadata(env)?;
    let rules = clean_kernel::env::csimp::rules_for(env, Some(owner));
    names
        .into_iter()
        .map(|name| replacement_name(env, &rules, &name))
        .collect()
}

/// Resolve a source reference through the same CSimp conversion as LCNF
/// lowering, before its later implementedBy pass. Named bodies use their source cutoff;
/// unnamed expressions use the current visible rules. Logical values and
/// kernel dependency closures are never rewritten by this query.
pub fn resolve_csimp_reference(
    env: &Environment,
    owner: Option<&Name>,
    name: &Name,
) -> Result<Name, CompilerError> {
    validate_metadata(env)?;
    let rules = clean_kernel::env::csimp::rules_for(env, owner);
    replacement_name(env, &rules, name)
}

fn replacement_name(env: &Environment, rules: &[Rule], name: &Name) -> Result<Name, CompilerError> {
    let mut current = name.clone();
    let mut seen = HashSet::new();
    while let Some(rule) = rules.iter().rev().find(|r| r.from == current) {
        let Some(theorem) = env.get_const(&rule.theorem) else {
            return Err(CompilerError::UnknownConstant(rule.theorem.clone()));
        };
        if clean_kernel::env::csimp::constant_replacement(&theorem.type_)
            != Some((rule.from.clone(), rule.to.clone()))
        {
            return Err(CompilerError::InvalidExpr(format!(
                "invalid imported csimp rule {}",
                rule.theorem
            )));
        }
        if !seen.insert(current.clone()) {
            return Err(CompilerError::InvalidExpr(format!(
                "csimp replacement cycle at {current}"
            )));
        }
        if env.get_const(&rule.to).is_none() {
            return Err(CompilerError::UnknownConstant(rule.to.clone()));
        }
        current = rule.to.clone();
    }
    Ok(current)
}

pub(crate) fn validate_metadata(env: &Environment) -> Result<(), CompilerError> {
    if clean_kernel::env::csimp::has_invalid_metadata(env) {
        return Err(CompilerError::InvalidExpr(
            "malformed or conflicting csimp compilation metadata".into(),
        ));
    }
    Ok(())
}
