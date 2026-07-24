// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definition body elaboration: binder processing for def/theorem/axiom declarations.

use crate::stack_safe;
use crate::ElabError;
use clean_kernel::{BinderInfo, Expr};
use clean_parser::{QAntiquotContent, SurfaceBinder, SurfaceExpr, SurfacePattern};

use super::{convert_binder_info, ElabCtx};

impl<'a> ElabCtx<'a> {
    fn binder_contains_retry_sensitive_surface(binder: &SurfaceBinder) -> bool {
        binder
            .ty
            .as_ref()
            .is_some_and(|ty| Self::contains_retry_sensitive_surface(ty))
            || binder
                .default
                .as_ref()
                .is_some_and(|value| Self::contains_retry_sensitive_surface(value))
    }

    fn pattern_contains_retry_sensitive_surface(pattern: &SurfacePattern) -> bool {
        match pattern {
            SurfacePattern::Var(_)
            | SurfacePattern::Wildcard
            | SurfacePattern::Ellipsis
            | SurfacePattern::Lit(_) => false,
            SurfacePattern::Inaccessible(expr) => Self::contains_retry_sensitive_surface(expr),
            SurfacePattern::Ctor(_, args) => args
                .iter()
                .any(Self::pattern_contains_retry_sensitive_surface),
            SurfacePattern::NumeralAdd(inner, _) | SurfacePattern::As(_, inner) => {
                Self::pattern_contains_retry_sensitive_surface(inner)
            }
            SurfacePattern::Or(lhs, rhs) => {
                Self::pattern_contains_retry_sensitive_surface(lhs)
                    || Self::pattern_contains_retry_sensitive_surface(rhs)
            }
            SurfacePattern::QPattern(expr) => Self::contains_retry_sensitive_surface(expr),
        }
    }

    pub(super) fn contains_retry_sensitive_surface(expr: &SurfaceExpr) -> bool {
        match expr {
            SurfaceExpr::Ident(_, name) => name == "sorry",
            SurfaceExpr::SyntheticSorry(_)
            | SurfaceExpr::ByTactic(..)
            | SurfaceExpr::CalcBlock(..)
            | SurfaceExpr::Do(..) => true,
            SurfaceExpr::Universe(_, _)
            | SurfaceExpr::Lit(_, _)
            | SurfaceExpr::Hole(_)
            | SurfaceExpr::NamedHole(_, _)
            | SurfaceExpr::SyntaxQuote(_, _) => false,
            SurfaceExpr::App(_, func, args) => {
                Self::contains_retry_sensitive_surface(func)
                    || args.iter().any(|a| Self::contains_retry_sensitive_surface(&a.expr))
            }
            SurfaceExpr::Lambda(_, binders, body)
            | SurfaceExpr::PatternMatchLambda(_, binders, body)
            | SurfaceExpr::Pi(_, binders, body) => {
                binders
                    .iter()
                    .any(Self::binder_contains_retry_sensitive_surface)
                    || Self::contains_retry_sensitive_surface(body)
            }
            SurfaceExpr::Arrow(_, from, to) | SurfaceExpr::Ascription(_, from, to) => {
                Self::contains_retry_sensitive_surface(from)
                    || Self::contains_retry_sensitive_surface(to)
            }
            SurfaceExpr::Let(_, binder, val, body) | SurfaceExpr::LetRec(_, binder, val, body) => {
                Self::binder_contains_retry_sensitive_surface(binder)
                    || Self::contains_retry_sensitive_surface(val)
                    || Self::contains_retry_sensitive_surface(body)
            }
            SurfaceExpr::LetPattern(_, pattern, scrutinee, fallback, body) => {
                Self::pattern_contains_retry_sensitive_surface(pattern)
                    || Self::contains_retry_sensitive_surface(scrutinee)
                    || Self::contains_retry_sensitive_surface(fallback)
                    || Self::contains_retry_sensitive_surface(body)
            }
            SurfaceExpr::Paren(_, inner)
            | SurfaceExpr::OutParam(_, inner)
            | SurfaceExpr::SemiOutParam(_, inner)
            | SurfaceExpr::Proj(_, inner, _)
            | SurfaceExpr::UniverseInst(_, inner, _)
            | SurfaceExpr::NamedArg(_, _, inner)
            | SurfaceExpr::Explicit(_, inner)
            | SurfaceExpr::LiftMethod(_, inner) => Self::contains_retry_sensitive_surface(inner),
            SurfaceExpr::If(_, cond, then_br, else_br) => {
                Self::contains_retry_sensitive_surface(cond)
                    || Self::contains_retry_sensitive_surface(then_br)
                    || Self::contains_retry_sensitive_surface(else_br)
            }
            SurfaceExpr::IfLet(_, pattern, scrutinee, then_br, else_br) => {
                Self::pattern_contains_retry_sensitive_surface(pattern)
                    || Self::contains_retry_sensitive_surface(scrutinee)
                    || Self::contains_retry_sensitive_surface(then_br)
                    || Self::contains_retry_sensitive_surface(else_br)
            }
            SurfaceExpr::IfDecidable(_, _, prop, then_br, else_br) => {
                Self::contains_retry_sensitive_surface(prop)
                    || Self::contains_retry_sensitive_surface(then_br)
                    || Self::contains_retry_sensitive_surface(else_br)
            }
            // A `match` is ALWAYS retry-sensitive: the `surface → syntax →
            // expand → surface` macro roundtrip mangles a nested match (it loses
            // the match's scoped gensym bookkeeping, leaking bogus binder idents
            // and an unresolved motive FVar — see the `Match`/`PatternMatchLambda`
            // bypasses in `infer/mod.rs::elaborate`). So an enclosing `App` /
            // `Ascription` / `Paren` carrying a match — e.g. `Eq (match e with …) x`
            // for a `theorem : (match …) = v` — must be routed AROUND
            // whole-expression expansion to `elab_app`/`elab_ascription`, which
            // re-elaborate the match through its own (bypassed) dispatch intact.
            // Same rationale as `ByTactic`/`Do`/`CalcBlock` above; the recursive
            // scrutinee/arm check it replaces was strictly weaker (it missed a
            // match whose mangling is intrinsic, not from a nested by/do block).
            SurfaceExpr::Match(..) => true,
            SurfaceExpr::QQuotation { inner, type_annot, .. } => {
                Self::contains_retry_sensitive_surface(inner)
                    || type_annot.as_ref().is_some_and(|ty| Self::contains_retry_sensitive_surface(ty))
            }
            SurfaceExpr::QAntiquot { content, .. } => match content {
                QAntiquotContent::Simple(_) | QAntiquotContent::Splice { .. } => false,
                QAntiquotContent::Expr(expr) => Self::contains_retry_sensitive_surface(expr),
                QAntiquotContent::Typed { ty, .. } => Self::contains_retry_sensitive_surface(ty),
            },
            SurfaceExpr::StructLit {
                struct_type,
                base,
                fields,
                ..
            } => {
                struct_type
                    .as_ref()
                    .is_some_and(|ty| Self::contains_retry_sensitive_surface(ty))
                    || base
                        .as_ref()
                        .is_some_and(|expr| Self::contains_retry_sensitive_surface(expr))
                    || fields
                        .iter()
                        .any(|field| Self::contains_retry_sensitive_surface(&field.val))
            }
            SurfaceExpr::InterpolatedStr { parts, .. } => parts.iter().any(|part| {
                matches!(part, clean_parser::InterpolationPart::Expr(e) if Self::contains_retry_sensitive_surface(e))
            }),
            // `open X in <term>`: the retry-sensitivity lives in the sub-term.
            SurfaceExpr::OpenIn { body, .. } => Self::contains_retry_sensitive_surface(body),
        }
    }

    fn try_elab_def_value_without_expected(
        &mut self,
        val: &SurfaceExpr,
        ty_expr: &Expr,
    ) -> Result<Option<Expr>, ElabError> {
        // A `match` body must see its expected type so the recursor motive is
        // built from the declared return type, not from the first arm's
        // inferred type. Without the expected type, a first arm that is a
        // decidable `Prop` (used where the declared return is `Bool`) would
        // fix the motive to `Prop`, and the whole-match `decide` coercion the
        // speculative no-expected lane would then apply is the wrong reading
        // (it must be per-arm). Defer such bodies to the expected-type lane.
        // (Track PP)
        if matches!(val, SurfaceExpr::Match(..)) {
            return Ok(None);
        }
        let saved_expected = self.current_expected_type.clone();
        self.metas.push_scope();
        self.current_expected_type = None;

        let result: Result<Expr, ElabError> = (|| {
            let val_expr = self.with_term_body_scope(|this| this.elaborate(val))?;
            let val_expr = self.apply_implicit_to_expected_type(&val_expr, ty_expr)?;
            // Apply (not merely check) any coercion — e.g. a Prop used where a
            // Bool is expected becomes `@decide p inst`. Keeping the original
            // term here would drop the coercion and fail the kernel check.
            let val_expr = self.coerce_to_expected_type(&val_expr, ty_expr)?;
            let val_expr = self.metas.instantiate(&val_expr);
            let val_expr = self.metas.instantiate_levels(&val_expr);
            // Reject a speculative term that still carries unsolved expression
            // metavariables after full instantiation. Such metavars would be
            // emitted to the kernel as free variables (an FVar leak) and fail the
            // kernel check with a spurious mismatch. This is exactly what happens
            // for a dependent / GADT `match` lowered *without* its expected type:
            // the motive degrades to the constant first-arm type and the omitted
            // index is left as an unconstrained metavar (e.g. `Eq.refl ?a` in
            // `symm`). Returning the leak here makes the caller fall back to the
            // expected-type-driven lane, which synthesizes the index-refining
            // motive. A genuinely ground speculative term (the common case, e.g.
            // `T.eval … := match … | T.t => Int`) is unaffected.
            if val_expr.has_expr_mvar_quick() {
                return Err(ElabError::CannotInfer);
            }
            Ok(val_expr)
        })();

        self.current_expected_type = saved_expected;
        match result {
            Ok(expr) => {
                self.metas.commit();
                Ok(Some(expr))
            }
            Err(_) => {
                self.metas.pop_scope();
                Ok(None)
            }
        }
    }

    /// B14 — reject a definition/theorem body that is well-typed against its
    /// declared type ONLY by delta-unfolding an `@[irreducible]` definition.
    ///
    /// Lean elaborates `rfl`/value bodies with `isDefEq` at `.default`
    /// transparency, where an `@[irreducible]` def does NOT unfold, so
    /// `theorem : f = v := rfl` through an irreducible `f` is a LOUD elaboration
    /// error — the proof term is never handed to the kernel. Clean's elaborator
    /// is lenient (it defers final checking to the kernel), and the kernel's
    /// `add_decl` re-check is transparency-blind (Lean-faithful: it unfolds
    /// everything), so without this gate such a body silently kernel-certifies.
    ///
    /// Precise, STRICTLY-NARROWING discriminator: run the COMPLETE kernel def-eq
    /// at two transparencies whose ONLY difference is the reducibility gate, and
    /// reject exactly when honor=true (blocks `@[irreducible]`) FAILS while
    /// honor=false (blind) SUCCEEDS — i.e. the sole route to well-typedness is an
    /// irreducible unfold. Every other outcome is unchanged:
    /// - def-eq already holds at honor=true → accept (ordinary `Regular`/
    ///   `@[reducible]` defs unfold at `.default`, so they are untouched);
    /// - not def-eq at either transparency → stay lenient, the kernel re-check
    ///   decides (never a new reject here).
    ///
    /// Skipped when either side still carries an unsolved metavariable (a leaked
    /// metavar would make the ground kernel def-eq unreliable — fail open).
    fn reject_body_defeq_only_via_irreducible(
        &self,
        val: &Expr,
        ty: &Expr,
    ) -> Result<(), ElabError> {
        let Ok(val_ty) = self.infer_type(val) else {
            return Ok(());
        };
        let val_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&val_ty));
        let ty = self.metas.instantiate_levels(&self.metas.instantiate(ty));
        if val_ty.has_expr_mvar_quick() || ty.has_expr_mvar_quick() {
            return Ok(());
        }
        let ctx = self.build_local_ctx();
        // honor=true: elaboration `.default` transparency — `@[irreducible]`
        // stays folded (matches MetaM `canUnfold`).
        let honor_ok = {
            let tc = clean_kernel::TypeChecker::with_context(self.env, ctx.clone());
            tc.set_honor_reducibility(true);
            tc.is_def_eq(&val_ty, &ty)
        };
        if honor_ok {
            return Ok(());
        }
        // honor=false: transparency-blind, complete — mirrors the kernel
        // `add_decl` re-check that would otherwise silently accept the body.
        let blind_ok =
            clean_kernel::TypeChecker::with_context(self.env, ctx).is_def_eq(&val_ty, &ty);
        if blind_ok {
            return Err(ElabError::TypeMismatch {
                expected: format!("{ty:?}"),
                actual: format!("{val_ty:?}"),
            });
        }
        Ok(())
    }

    /// Elaborate a definition body with binders.
    ///
    /// Processes binders recursively, building Pi types for the type signature
    /// and Lambda abstractions for the value. Returns (type, value) pair.
    pub(super) fn elab_def_body(
        &mut self,
        binders: &[SurfaceBinder],
        ty: Option<&SurfaceExpr>,
        val: &SurfaceExpr,
    ) -> Result<(Expr, Expr), ElabError> {
        stack_safe(|| {
            use clean_parser::SurfaceLit;

            if binders.is_empty() {
                let ty_expr = if let Some(ty) = ty {
                    // Signature position: the result type may auto-bind
                    // implicits (Lean header elaboration).
                    self.elaborate(ty)?
                } else {
                    // No ascribed type: the type is INFERRED from the value,
                    // but the value is still a term-body position — unknown
                    // idents there are loud, never auto-bound (B03).
                    let val_expr = self.with_term_body_scope(|this| this.elaborate(val))?;
                    self.infer_type(&val_expr)?
                };

                // Set expected type for bidirectional type checking (#172)
                // This enables anonymous constructor syntax ⟨...⟩ to determine
                // the target structure from the type annotation.
                let prev_expected = self.current_expected_type.take();
                let val_expr = if ty.is_some() {
                    match val {
                        // When we have `def foo : UInt8 := 1`, elaborate the literal
                        // directly to the expected type using the type's constructor.
                        SurfaceExpr::Lit(_, SurfaceLit::Nat(n)) => self
                            .elab_nat_literal_with_expected(
                                &clean_kernel::BigNat::from_u64(*n),
                                &ty_expr,
                            ),
                        SurfaceExpr::Lit(_, SurfaceLit::BigNat(n)) => {
                            self.elab_nat_literal_with_expected(n, &ty_expr)
                        }
                        _ => {
                            // Explicit/synthetic `sorry` and tactic-style proofs
                            // record global trust counters during elaboration.
                            // A failed speculative pass would leak that debt into
                            // the successful retry, so elaborate these surfaces once.
                            if Self::contains_retry_sensitive_surface(val) {
                                let expected_ty = self
                                    .metas
                                    .instantiate_levels(&self.metas.instantiate(&ty_expr));
                                self.current_expected_type = Some(expected_ty.clone());
                                let result = self.with_term_body_scope(|this| this.elaborate(val));
                                self.current_expected_type = prev_expected.clone();
                                let val_expr = result?;
                                self.apply_implicit_to_expected_type(&val_expr, &expected_ty)?
                            } else {
                                // Avoid pushing the full declaration type into every body
                                // expression up front. Application-valued bodies like
                                // `PEmpty.rec (fun _ => Nat)` and `id` should elaborate
                                // from their own type first, then be checked against the
                                // declaration type. If that lane fails, retry with the
                                // old expected-type-driven elaboration for forms that need it
                                // (`sorry`, anonymous constructors, untyped lambdas, ...).
                                if let Some(expr) =
                                    self.try_elab_def_value_without_expected(val, &ty_expr)?
                                {
                                    expr
                                } else {
                                    self.current_expected_type = Some(ty_expr.clone());
                                    let result =
                                        self.with_term_body_scope(|this| this.elaborate(val));
                                    self.current_expected_type = prev_expected.clone();
                                    let val_expr = result?;
                                    self.apply_implicit_to_expected_type(&val_expr, &ty_expr)?
                                }
                            }
                        }
                    }
                } else {
                    self.with_term_body_scope(|this| this.elaborate(val))?
                };

                self.current_expected_type = prev_expected;

                // Fix #171: Unify value type with expected type to solve level constraints.
                // Universe params like u_0 are created during elaboration but need to be
                // unified with concrete levels from the expected type.
                // Example: `def foo : Type → Prop := Nonempty` needs u_0 = 1
                //
                // This unifier already runs at elaboration `.default` transparency
                // (honor_reducibility on), so its verdict doubles as a cheap B14
                // pre-filter below: when it SUCCEEDS the body's type is def-eq to
                // the declared type WITHOUT unfolding any `@[irreducible]` def, so
                // the (expensive) precise gate can be skipped entirely — the
                // common case.
                let mut level_unify_ok = true;
                if let Ok(val_ty) = self.infer_type(&val_expr) {
                    let ctx = self.build_local_ctx();
                    let mut unifier =
                        crate::unify::Unifier::with_env(&mut self.metas, self.env, ctx);
                    level_unify_ok = matches!(
                        unifier.unify(&val_ty, &ty_expr),
                        crate::unify::UnifyResult::Success
                    );
                }

                // B14: a body well-typed against its declared type ONLY by
                // delta-unfolding an `@[irreducible]` def is a LOUD elaboration
                // error in Lean (elaboration `isDefEq` runs at `.default`
                // transparency). Reject it here so it never reaches the
                // transparency-blind kernel re-check (the `p04` silent-wrong).
                // Only run the precise (2× kernel def-eq) discriminator when the
                // `.default`-transparency unifier above could NOT equate the two
                // types — otherwise def-eq already holds without any irreducible
                // unfold and there is nothing to reject.
                if !level_unify_ok {
                    self.reject_body_defeq_only_via_irreducible(&val_expr, &ty_expr)?;
                    // B18: `Term.ensureHasType` at the def-/theorem-body boundary.
                    // The `.default`-transparency unifier above could not equate
                    // the body's type with the declared type. If the kernel's own
                    // transparency-blind def-eq ALSO cannot, the body is genuinely
                    // ill-typed: fail LOUD here so it is never registered and no
                    // downstream path can launder it into a `sorryAx`, instead of
                    // shipping it to the kernel as a `KernelCheckFailed`. Strictly
                    // relocation-only — when the kernel WOULD accept (def-eq holds
                    // blind), this is a no-op and the term reaches the kernel
                    // unchanged, so no body the kernel accepts is newly rejected.
                    self.reject_body_type_mismatch(&val_expr, &ty_expr)?;
                }

                return Ok((ty_expr, val_expr));
            }

            // Process first binder
            let binder = &binders[0];
            let binder_ty = if let Some(ty) = &binder.ty {
                let elaborated = self.elaborate(ty)?;
                let instantiated = self.metas.instantiate(&elaborated);
                self.metas.instantiate_levels(&instantiated)
            } else {
                // Lean 4 elaborates omitted binder annotations as holes checked
                // against an expected `Sort ?u`, not a fixed `Type`. Mirror that
                // here so declaration headers such as
                // `def h {α β} {f : α → β} : ...`
                // can solve their binder universes from later constraints.
                let binder_sort = Expr::sort(self.fresh_universe_param());
                self.fresh_meta(binder_sort)
            };

            let bi = convert_binder_info(binder.info);
            let fvar = self.push_local(binder.name.clone(), binder_ty.clone());

            // For instance-implicit binders, register as local instance for nested resolution
            let is_inst_implicit = bi == BinderInfo::InstImplicit;
            if is_inst_implicit {
                self.push_local_instance(fvar, binder_ty.clone());
            }

            // Recursively process remaining binders
            let (inner_ty, inner_val) = self.elab_def_body(&binders[1..], ty, val)?;

            // Pop local instance before popping local
            if is_inst_implicit {
                self.pop_local_instance();
            }
            self.pop_local();

            // Fix #443: Instantiate metas BEFORE abstracting FVars
            // If a meta is assigned to an expression containing the FVar (e.g., `?m := Proj(C, 0, FVar(x))`),
            // we must substitute the meta first so the FVar is visible for abstraction.
            // Otherwise, abstract_fvar won't find the FVar (it's hidden inside the uninstantiated meta),
            // and after later instantiation, the FVar remains unabstracted.
            let ty_inst = self.metas.instantiate(&inner_ty);
            let ty_abs = self.metas.instantiate_levels(&ty_inst.abstract_fvar(fvar));
            let val_inst = self.metas.instantiate(&inner_val);
            let val_abs = self.metas.instantiate_levels(&val_inst.abstract_fvar(fvar));

            Ok((
                Expr::pi(bi, binder_ty.clone(), ty_abs),
                Expr::lam(bi, binder_ty, val_abs),
            ))
        })
    }

    /// Elaborate an axiom type with binders.
    ///
    /// Builds a Pi type from binders, wrapping the body type.
    /// Used for axiom and opaque declarations.
    pub(super) fn elab_axiom_type(
        &mut self,
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        // Collect all binders' fvars and types first, then build Pi from outside in
        self.elab_axiom_type_with_fvars(binders, ty, &[])
    }

    /// Helper that tracks outer fvars for proper abstraction
    fn elab_axiom_type_with_fvars(
        &mut self,
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        outer_fvars: &[(clean_kernel::FVarId, Expr, BinderInfo)],
    ) -> Result<Expr, ElabError> {
        stack_safe(|| {
            if binders.is_empty() {
                let mut result = self.elaborate(ty)?;
                // Abstract fvars outermost-first (Track KK). `abstract_fvar`
                // replaces its target with BVar(0) and shifts existing loose
                // BVars up by one, so abstracting the OUTERMOST binder first and
                // the innermost last lands the outermost at the highest BVar
                // index and the innermost at BVar(0) — matching the nesting
                // `Pi outer, … Pi inner, body`. `outer_fvars` is in push order
                // (outermost binder first), so we iterate it forward.
                //
                // The prior `.rev()` reversed this: for a two-binder axiom such
                // as `(m n : Nat) : Nat.land m n = Nat.land n m` it abstracted
                // `n` then `m`, giving `m = BVar 0` (inner) and `n = BVar 1`
                // (outer) — i.e. the binders, hence every body reference to them,
                // were swapped. Applying the axiom to `m n` then inferred the
                // type with the arguments transposed (`Nat.land n m = …`), which
                // surfaced downstream as a spurious "fvar mismatch" in `exact`
                // (TrustIr `Basic.lean` `Int.land_comm` and its `nat_*_comm`
                // helpers). Single-binder declarations are unaffected (`rev` of a
                // one-element slice is identity).
                for (fvar, _, _) in outer_fvars.iter() {
                    result = result.abstract_fvar(*fvar);
                }
                return Ok(result);
            }

            let binder = &binders[0];
            let mut binder_ty = if let Some(t) = &binder.ty {
                let elaborated = self.elaborate(t)?;
                let instantiated = self.metas.instantiate(&elaborated);
                self.metas.instantiate_levels(&instantiated)
            } else {
                return Err(ElabError::CannotInfer);
            };

            let bi = convert_binder_info(binder.info);
            let fvar = self.push_local(binder.name.clone(), binder_ty.clone());

            // For instance-implicit binders, register as local instance for nested resolution
            let is_inst_implicit = bi == BinderInfo::InstImplicit;
            if is_inst_implicit {
                self.push_local_instance(fvar, binder_ty.clone());
            }

            // Recurse with this fvar added to the list
            let mut new_outer_fvars = outer_fvars.to_vec();
            new_outer_fvars.push((fvar, binder_ty.clone(), bi));
            let inner_ty = self.elab_axiom_type_with_fvars(&binders[1..], ty, &new_outer_fvars)?;

            // Pop local instance before popping local
            if is_inst_implicit {
                self.pop_local_instance();
            }
            self.pop_local();

            // Abstract this binder's type over the outer fvars, outermost-first
            // (Track KK) — same de Bruijn convention as the body abstraction
            // above. For a dependent domain `T(b₀, …, bₖ₋₁)` sitting under the k
            // preceding binders, the outermost preceding binder must land at the
            // highest BVar index and the nearest at BVar(0); `outer_fvars` is in
            // push (outermost-first) order, so iterate it forward.
            for (outer_fvar, _, _) in outer_fvars.iter() {
                binder_ty = binder_ty.abstract_fvar(*outer_fvar);
            }

            Ok(Expr::pi(bi, binder_ty, inner_ty))
        })
    }
}
