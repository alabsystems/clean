// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::tla_core::ast::{self as core_ast, BoundPattern, ModuleTarget};
use crate::tla_core::Spanned;
use crate::TlaError;

pub(super) fn bound_name(bound: &core_ast::BoundVar, context: &str) -> Result<String, TlaError> {
    match &bound.pattern {
        None => Ok(bound.name.node.clone()),
        Some(BoundPattern::Var(name)) => Ok(name.node.clone()),
        Some(BoundPattern::Tuple(_)) => Err(TlaError::UnsupportedCoreAst(format!(
            "{context} tuple patterns cannot map to clean-tla"
        ))),
    }
}

pub(super) fn single_named_domain<'a>(
    bounds: &'a [core_ast::BoundVar],
    context: &str,
) -> Result<(String, &'a Spanned<core_ast::Expr>), TlaError> {
    if bounds.len() != 1 {
        return Err(TlaError::UnsupportedCoreAst(format!(
            "{context} with {} binders cannot map to clean-tla",
            bounds.len()
        )));
    }
    let bound = &bounds[0];
    let name = bound_name(bound, context)?;
    let domain = bound.domain.as_deref().ok_or_else(|| {
        TlaError::UnsupportedCoreAst(format!(
            "{context} without an explicit domain cannot map to clean-tla"
        ))
    })?;
    Ok((name, domain))
}

pub(super) fn callee_name(callee: &Spanned<core_ast::Expr>) -> Option<String> {
    match &callee.node {
        core_ast::Expr::Ident(name, _) | core_ast::Expr::OpRef(name) => Some(name.clone()),
        core_ast::Expr::ModuleRef(target, name, _) => {
            Some(format!("{}!{}", module_target_name(target), name))
        }
        _ => None,
    }
}

pub(super) fn module_target_name(target: &ModuleTarget) -> String {
    match target {
        ModuleTarget::Named(name) | ModuleTarget::Parameterized(name, _) => name.clone(),
        ModuleTarget::Chained(base) => format!("{:?}", base.node),
    }
}
