// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retry a type's arrow domain only when field notation is blocked on an
//! unassigned receiver type. The codomain can supply that missing type.

use super::{ElabCtx, ElabError, Expr, SurfaceExpr};

impl ElabCtx<'_> {
    pub(super) fn elab_arrow(
        &mut self,
        from: &SurfaceExpr,
        to: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        let watch = self.begin_field_notation_watch();
        let domain = self.with_local_scope_rollback(|ctx| ctx.elaborate_type_observing(from));
        let stuck = self.end_field_notation_watch(watch);
        match domain {
            Ok(from_expr) => {
                let to_expr = self.elaborate_type_observing(to)?;
                self.finish_arrow(from_expr, to_expr)
            }
            Err(original) if stuck => self
                .lean_order_attempt(|ctx| {
                    let to_expr = ctx.elaborate_type_observing(to)?;
                    let from_expr = ctx.elaborate_type_observing(from)?;
                    ctx.finish_arrow(from_expr, to_expr)
                })
                .map_err(|_| original),
            Err(error) => Err(error),
        }
    }

    fn finish_arrow(&mut self, from_expr: Expr, to_expr: Expr) -> Result<Expr, ElabError> {
        let (from_expr, _) = self.ensure_type_coerced(from_expr)?;
        let (to_expr, _) = self.ensure_type_coerced(to_expr)?;
        Ok(Expr::arrow(from_expr, to_expr))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Environment;
    use clean_parser::SurfaceName;

    #[test]
    fn successful_temporary_scope_retains_auto_implicit_metadata() {
        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);
        let name = SurfaceName::generated_path("inferred");
        let inferred = ctx
            .with_temporary_local_scope(
                |ctx| Ok(ctx.add_auto_implicit(name.clone(), Expr::type_())),
            )
            .expect("successful temporary work");
        // Successful work already propagates declaration metadata. Only a
        // failed attempt should discard the auto-implicits it introduced.
        assert_eq!(ctx.has_auto_implicit(&name), Some(inferred));
        assert_eq!(ctx.auto_implicit_count(), 1);
    }

    #[test]
    fn failed_arrow_scope_restores_auto_implicit_packet_and_lookup() {
        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);
        let outer = SurfaceName::generated_path("outer");
        let inner = SurfaceName::generated_path("inner");
        let outer_id = ctx.add_auto_implicit(outer.clone(), Expr::type_());
        let result: Result<(), ElabError> = ctx.with_local_scope_rollback(|ctx| {
            ctx.add_auto_implicit(inner.clone(), Expr::type_());
            Err(ElabError::CannotInfer)
        });
        assert!(result.is_err());
        assert_eq!(ctx.auto_implicit_count(), 1);
        assert_eq!(ctx.has_auto_implicit(&outer), Some(outer_id));
        assert_eq!(ctx.has_auto_implicit(&inner), None);
    }
}
