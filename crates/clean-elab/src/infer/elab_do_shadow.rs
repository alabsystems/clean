// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Mutable-name checks on the do element actually being elaborated.
use crate::ElabError;
use clean_parser::{DoElem, SurfaceName, SurfacePattern};

fn check_name(name: &SurfaceName, active: &[SurfaceName]) -> Result<(), ElabError> {
    if !name.is_unescaped_component("_") && active.contains(name) {
        return Err(ElabError::MutableVariableShadowing {
            name: name.to_string(),
        });
    }
    Ok(())
}

fn check_pattern(pattern: &SurfacePattern, active: &[SurfaceName]) -> Result<(), ElabError> {
    let mut names = Vec::new();
    pattern.collect_var_names(&mut names);
    for name in names {
        check_name(&name, active)?;
    }
    Ok(())
}

/// Enforce Lean4.35's mutable-name restriction at declaration positions.
/// Only inspect this element's declarations. Visiting the whole sequence would
/// incorrectly reject dead code after return; visiting terms would incorrectly
/// reject nested lambdas and independent nested do blocks. Decidable-if proof
/// witnesses are term binders and are intentionally allowed to shadow.
pub(super) fn check_do_head_shadowing(
    elem: &DoElem,
    active: &[SurfaceName],
) -> Result<(), ElabError> {
    match elem {
        DoElem::Bind(_, binder, _)
        | DoElem::Let(_, binder, _)
        | DoElem::Have(_, binder, _)
        | DoElem::LetMut(_, binder, _)
        | DoElem::For(_, binder, _, _) => check_name(&binder.name, active)?,
        DoElem::LetRec(_, declarations) => {
            for (binder, _) in declarations {
                check_name(&binder.name, active)?;
            }
        }
        DoElem::IfLet(_, pattern, ..)
        | DoElem::LetElse(_, pattern, ..)
        | DoElem::LetExpr(_, pattern, ..) => check_pattern(pattern, active)?,
        DoElem::Match(_, _, arms) => {
            for arm in arms {
                for pattern in &arm.patterns {
                    check_pattern(pattern, active)?;
                }
            }
        }
        DoElem::TryCatch(_, _, catches, _) => {
            for catch in catches {
                check_name(&catch.binder, active)?;
            }
        }
        _ => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::super::ElabCtx;
    use clean_kernel::Environment;
    use clean_parser::{parse_expr, SurfaceName};

    #[test]
    fn mutable_scope_restores_after_nested_success_and_failure() {
        let env = Environment::with_prelude();
        let mut ctx = ElabCtx::new(&env);
        let outer = vec![SurfaceName::generated_path("outer")];
        ctx.do_active_mut_vars = outer.clone();
        let bad = parse_expr("(do { let mut x := 1; have x : Nat := 2; pure x } : Id Nat)")
            .expect("fixture parses");
        let err = ctx.elaborate(&bad).expect_err("shadowing is rejected");
        assert!(err.to_string().contains("cannot be shadowed"));
        assert_eq!(ctx.do_active_mut_vars, outer);
        let good =
            parse_expr("(do { let outer := 2; pure outer } : Id Nat)").expect("fixture parses");
        let term = ctx
            .elaborate(&good)
            .expect("independent do can shadow outer names");
        assert!(!ctx.metas.instantiate(&term).has_fvar_quick());
        assert_eq!(ctx.do_active_mut_vars, outer);
    }
}
