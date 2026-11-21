// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lean's compiler-only macro expansion, after source-point CSimp replacement.
//! This returns a temporary term; it never changes a logical declaration.

use crate::CompilerError;
use clean_kernel::{Environment, Expr, ExprKind, Name};

/// One genuinely attributed helper expanded at a source compilation point.
pub struct SourceMacroExpansion {
    /// The replacement helper whose body was expanded.
    pub name: Name,
    /// Universe-instantiated body, beta-applied to the original arguments.
    pub body: Expr,
}

/// Expand an attributed helper using the owning body's actual CSimp cutoff.
/// Ordinary inlining and implementedBy are later compiler phases, not licenses
/// to discard an otherwise unavailable source dependency here.
pub fn expand_source_macro_inline(
    env: &Environment,
    owner: Option<&Name>,
    expression: &Expr,
) -> Result<Option<SourceMacroExpansion>, CompilerError> {
    let ExprKind::Const(name, levels) = expression.get_app_fn().kind() else {
        return Ok(None);
    };
    let name = crate::csimp::resolve_csimp_reference(env, owner, name)?;
    if clean_kernel::env::csimp::inline_mode_at(env, owner, &name)
        != Some(clean_kernel::env::csimp::InlineMode::MacroInline)
    {
        return Ok(None);
    }
    let info = env
        .get_const(&name)
        .ok_or_else(|| CompilerError::UnknownConstant(name.clone()))?;
    if info.kind != clean_kernel::ConstantKind::Definition {
        return Err(CompilerError::InvalidExpr(format!(
            "macro_inline declaration {name} is not a definition"
        )));
    }
    if info.level_params.len() != levels.len() {
        return Err(CompilerError::InvalidExpr(format!(
            "macro_inline universe arity mismatch for {name}"
        )));
    }
    let value = info.value.as_ref().ok_or_else(|| {
        CompilerError::InvalidExpr(format!("macro_inline declaration {name} has no body"))
    })?;
    let mut body = value.instantiate_level_params_direct(&info.level_params, levels);
    for argument in expression.get_app_args() {
        while let ExprKind::MData(_, inner) = body.kind() {
            body = inner.as_ref().clone();
        }
        body = match body.kind() {
            ExprKind::Lam(_, _, inner) => inner.instantiate(argument),
            _ => Expr::app(body, argument.clone()),
        };
    }
    Ok(Some(SourceMacroExpansion { name, body }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Declaration;

    #[test]
    fn externally_marked_opaque_body_is_not_a_macro_definition() {
        let mut env = Environment::with_prelude();
        let name = Name::from_string("hidden");
        env.add_decl(Declaration::Opaque {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::const_str("Nat"),
            value: Expr::nat_lit(0),
        })
        .expect("valid logical opaque declaration");
        env.register_macro_inline(name.clone());
        let result = expand_source_macro_inline(&env, None, &Expr::const_str("hidden"));
        assert!(matches!(result, Err(CompilerError::InvalidExpr(message))
            if message.contains("not a definition")));
        assert_eq!(
            env.get_const(&name).expect("logical value remains").value,
            Some(Expr::nat_lit(0))
        );
    }
}
