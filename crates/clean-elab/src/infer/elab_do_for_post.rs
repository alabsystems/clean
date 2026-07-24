// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Post-loop unwrapping for do-notation for-loops (#1818 Phase 4C).
//!
//! After `ForIn.forIn` returns `m beta`, the post-loop processing:
//! 1. Binds the result to a local `__do_post`
//! 2. Destructures the accumulator into individual mutable variable locals
//! 3. Case-splits the `Option rho` component via `Option.rec` for early return
//!
//! This module handles step (1)-(3) so that the compound for-loop case
//! (`for x in xs do body; rest`) correctly threads state and propagates
//! early returns after the loop completes.
//!
//! Reference: ~/lean4-ref/src/Lean/Elab/Do/BuiltinDo/For.lean:172-190

use super::elab_do_prod;
use super::*;

impl<'a> ElabCtx<'a> {
    /// Post-loop processing: bind ForIn result, destructure accumulator,
    /// and case-split Option for early return tunneling.
    ///
    /// Generates:
    /// ```text
    /// Bind.bind forIn (fun (__do_post : beta) =>
    ///   let a := proj_a(__do_post)        -- mutable var extraction
    ///   let b := proj_b(__do_post)        -- mutable var extraction
    ///   [Option.rec rho motive            -- case-split if returns_early
    ///     (rest)                           --   none: continue do-block
    ///     (fun r => Pure.pure r)           --   some: propagate return
    ///     (proj_ret(__do_post))])           --   Option value
    /// ```
    ///
    /// Reference: Lean 4 BuiltinDo/For.lean:172-190
    pub(super) fn elab_do_for_post_loop(
        &mut self,
        for_in_expr: Expr,
        beta: &Expr,
        mut_var_info: &[(String, FVarId, Expr)],
        return_type: &Option<Expr>,
        rest: Option<&[DoElem]>,
    ) -> Result<Expr, ElabError> {
        let has_reassigns = !mut_var_info.is_empty();
        let returns_early = return_type.is_some();

        // Push post-loop accumulator binding.
        let fvar_post = self.push_local("__do_post".to_string(), beta.clone());

        // Destructure accumulator into mutable variable shadow locals.
        let shadow_vars = if has_reassigns {
            let base_expr = if returns_early {
                // Prod.snd (Option rho) MutVarProduct __do_post
                let ret_ty = return_type
                    .as_ref()
                    .expect("invariant: returns_early implies return_type is Some");
                let ret_level = elab_do_prod::type_universe(self, ret_ty)?;
                let option_ty = Expr::app(
                    Expr::const_(Name::from_string("Option"), vec![ret_level]),
                    ret_ty.clone(),
                );
                let mut_sigma = elab_do_prod::build_sigma_type(
                    self,
                    &mut_var_info
                        .iter()
                        .map(|(n, _, ty)| (n.clone(), ty.clone()))
                        .collect::<Vec<_>>(),
                )?;
                elab_do_prod::project_prod(
                    self,
                    &option_ty,
                    &mut_sigma,
                    Expr::fvar(fvar_post),
                    false,
                )?
            } else {
                Expr::fvar(fvar_post)
            };
            self.destructure_acc_from_expr(base_expr, mut_var_info)?
        } else {
            vec![]
        };

        // Elaborate the rest of a compound block with shadow locals in scope.
        // A terminal loop still needs an explicit continuation: the raw
        // accumulator is an internal tunneling representation and must not
        // escape as the result of the do-block.
        let rest_expr = match rest {
            Some(rest) => self.elab_do_elems(rest)?,
            None => self.build_terminal_for_result()?,
        };

        // Build the result expression.
        let mut result = if returns_early {
            self.build_option_case_split(
                return_type
                    .as_ref()
                    .expect("invariant: returns_early implies return_type is Some"),
                fvar_post,
                has_reassigns,
                mut_var_info,
                rest_expr,
            )?
        } else {
            rest_expr
        };

        // Fix #3419: Instantiate metas before abstracting FVars.
        // rest_expr was elaborated with shadow locals and fvar_post in scope.
        result = self.metas.instantiate(&result);

        // Pop shadow locals wrapping in let-bindings.
        for (shadow_name, shadow_fvar, shadow_ty, proj_expr) in shadow_vars.iter().rev() {
            let abs = result.abstract_fvar(*shadow_fvar);
            result = Expr::let_named(
                Name::from_string(shadow_name),
                shadow_ty.clone(),
                proj_expr.clone(),
                abs,
                false,
            );
            self.pop_local();
        }

        // Abstract over post-loop accumulator.
        let cont_body = result.abstract_fvar(fvar_post);
        self.pop_local();
        let cont_lam = Expr::lam(BinderInfo::Default, beta.clone(), cont_body);

        // forIn >>= (fun __do_post : beta => ...)
        Ok(self.mk_bind_app(for_in_expr, cont_lam))
    }

    /// Build the normal-fallthrough result of a terminal `for` statement.
    ///
    /// Lean's statement result is `Unit`.  If the surrounding do-block has an
    /// expected inner result, authenticate that it is definitionally the same
    /// type now; otherwise a terminal loop could hide a `m Unit`/`m alpha`
    /// mismatch until a distant kernel-registration failure.
    fn build_terminal_for_result(&mut self) -> Result<Expr, ElabError> {
        let unit_ty = Expr::const_(Name::from_string("Unit"), vec![]);
        if let Some(expected) = self.expected_do_result_alpha() {
            if !self.try_unify(&unit_ty, &expected) && !self.is_def_eq(&unit_ty, &expected) {
                return Err(ElabError::TypeMismatch {
                    expected: format!("{expected:?}"),
                    actual: format!("{unit_ty:?}"),
                });
            }
        }
        let unit = Expr::const_(Name::from_string("Unit.unit"), vec![]);
        let result = self.mk_pure_app_at(unit_ty, unit);
        if let Some(expected) = self.current_expected_type.clone() {
            self.enforce_expr_type(&result, &expected)?;
        }
        Ok(result)
    }

    /// Build the Option.rec case-split for early return tunneling post-loop.
    ///
    /// Produces: `@Option.rec rho motive rest_expr (fun r => pure r) option_val`
    /// where option_val is extracted from the accumulator.
    fn build_option_case_split(
        &mut self,
        ret_ty: &Expr,
        fvar_post: FVarId,
        has_reassigns: bool,
        mut_var_info: &[(String, FVarId, Expr)],
        rest_expr: Expr,
    ) -> Result<Expr, ElabError> {
        // Extract the Option component from the accumulator.
        let option_val = if has_reassigns {
            // Prod.fst (Option rho) MutVarProduct __do_post
            let ret_level = elab_do_prod::type_universe(self, ret_ty)?;
            let option_ty = Expr::app(
                Expr::const_(Name::from_string("Option"), vec![ret_level]),
                ret_ty.clone(),
            );
            let mut_sigma = elab_do_prod::build_sigma_type(
                self,
                &mut_var_info
                    .iter()
                    .map(|(n, _, ty)| (n.clone(), ty.clone()))
                    .collect::<Vec<_>>(),
            )?;
            elab_do_prod::project_prod(self, &option_ty, &mut_sigma, Expr::fvar(fvar_post), true)?
        } else {
            // beta = Option rho, so the post value IS the Option.
            Expr::fvar(fvar_post)
        };

        // The eliminator's motive is exactly the type of the normal
        // continuation.  Inferring it from `rest_expr` makes both branches and
        // both universe arguments check against one authenticated judgment.
        let result_ty = self.infer_type(&rest_expr)?;

        // Build some_case: fun (r : rho) => Pure.pure r
        let fvar_r = self.push_local("__do_ret_val".to_string(), ret_ty.clone());
        let pure_r = self.mk_pure_app_at(ret_ty.clone(), Expr::fvar(fvar_r));
        self.enforce_expr_type(&pure_r, &result_ty)?;
        let some_body = pure_r.abstract_fvar(fvar_r);
        self.pop_local();
        let some_case = Expr::lam(BinderInfo::Default, ret_ty.clone(), some_body);

        // Build motive: fun (_ : Option rho) => m_result_ty
        let ret_level = elab_do_prod::type_universe(self, ret_ty)?;
        let option_rho_ty = Expr::app(
            Expr::const_(Name::from_string("Option"), vec![ret_level.clone()]),
            ret_ty.clone(),
        );
        let fvar_motive = self.push_local("_".to_string(), option_rho_ty.clone());
        let motive_body = result_ty.abstract_fvar(fvar_motive);
        self.pop_local();
        let motive = Expr::lam(BinderInfo::Default, option_rho_ty, motive_body);

        // Option.rec.{u1, u2} : {alpha : Type u2} ->
        //   {motive : Option alpha -> Sort u1} ->
        //   motive none -> ((val : alpha) -> motive (some val)) ->
        //   (t : Option alpha) -> motive t
        let rec_u1 = self.infer_sort(&result_ty)?;
        let rec_u2 = ret_level;
        let option_rec = Expr::const_(Name::from_string("Option.rec"), vec![rec_u1, rec_u2]);

        // @Option.rec u1 u2 rho motive none_case some_case option_val
        let e = Expr::app(option_rec, ret_ty.clone());
        let e = Expr::app(e, motive);
        let e = Expr::app(e, rest_expr); // none -> continue with rest
        let e = Expr::app(e, some_case); // some r -> pure r
        Ok(Expr::app(e, option_val)) // the Option rho value
    }
}
