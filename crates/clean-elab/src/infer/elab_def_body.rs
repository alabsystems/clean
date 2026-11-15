// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definition body elaboration: binder processing for def/theorem/axiom declarations.

use crate::stack_safe;
use crate::unify::MetaState;
use crate::ElabError;
use clean_kernel::{BinderInfo, Expr};
use clean_parser::{QAntiquotContent, SurfaceBinder, SurfaceExpr, SurfacePattern};

use super::{convert_binder_info, ElabCtx, RecursiveParam};

#[cfg(test)]
#[path = "elab_def_body_meta_tests.rs"]
mod meta_tests;

struct DefinitionHeaderLocals {
    fvars: Vec<clean_kernel::FVarId>,
    /// Autos discovered while elaborating the semantically marked section
    /// prefix belong to that captured prefix, including implicit carriers
    /// introduced by a section variable's own type.
    section_auto_count: usize,
}

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
            SurfacePattern::StructInst { fields, ty, .. } => {
                fields
                    .iter()
                    .any(|(_, pat)| Self::pattern_contains_retry_sensitive_surface(pat))
                    || ty
                        .as_ref()
                        .is_some_and(|ty| Self::contains_retry_sensitive_surface(ty))
            }
        }
    }

    pub(super) fn contains_retry_sensitive_surface(expr: &SurfaceExpr) -> bool {
        match expr {
            SurfaceExpr::Ident(_, name) => name.is_unescaped_component("sorry"),
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
            SurfaceExpr::Let(_, binder, val, body)
            | SurfaceExpr::Have(_, binder, val, body)
            | SurfaceExpr::LetRec(_, binder, val, body) => {
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
            // The `surface → syntax → expand → surface` roundtrip has no
            // faithful `openIn` node (`to_syntax` keeps only the body), so an
            // `open X in e` NESTED in an argument came back as the bare
            // identifier `openIn` (`Function.extend_const`'s `funext fun _ ↦
            // open scoped Classical in ite_id _`, measured 2026-09-12). Like a
            // `by` block, it must reach its own bypass intact.
            SurfaceExpr::OpenIn { .. } => true,
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
        let term_info_mark = self.term_contexts.len();
        // The postponed open-carrier instance goals this lane queues name ITS
        // metavariables. A failed lane pops their scope, which also rolls the
        // id counter back (`MetaState::pop_scope` replays `NextId`), so the
        // expected-type lane re-mints those ids for different metavariables;
        // a queued goal left behind then pinned its carrier into whichever
        // one reused the id — `def f : Nat → Nat := fun x => x * x` lost its
        // `HMul` instance to `Nat` and the kernel refused the term (integ/r5,
        // 2026-10-16: lane X's real G46 scan made this lane fail for every
        // term with a postponed instance). Roll the queue back with the metas.
        let saved_postponed = self.postponed_open_carrier_instances.clone();
        let saved_postponed_do_pure = self.do_pure_obligations.clone();
        self.metas.push_scope();
        self.current_expected_type = None;

        let result: Result<Expr, ElabError> = (|| {
            let val_expr = self.with_term_body_scope(|this| this.elaborate(val))?;
            let val_expr =
                self.apply_implicit_to_expected_type_for_surface(val, &val_expr, ty_expr)?;
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
            //
            // A REAL scan (G46, ledger (116)): elaborator metas are bit-63
            // FVars, which the kernel's `has_expr_mvar_quick` flag never sees,
            // so until 2026-10-08 this guard was vacuous and a speculative term
            // with an open `?m` was committed.
            if MetaState::expr_has_meta(&val_expr) {
                return Err(ElabError::CannotInfer);
            }
            Ok(val_expr)
        })();

        self.current_expected_type = saved_expected;
        match result {
            Ok(expr) => {
                self.metas.commit();
                self.commit_checked_body_info(term_info_mark, val.span(), &expr, ty_expr);
                Ok(Some(expr))
            }
            Err(_) => {
                self.metas.pop_scope();
                self.postponed_open_carrier_instances = saved_postponed;
                self.do_pure_obligations = saved_postponed_do_pure;
                self.term_contexts.truncate(term_info_mark);
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
    /// A side that still carries an unsolved metavariable is checked with the
    /// metavariable opaque (G46: the skip this once claimed was vacuous).
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
        // NO metavariable skip (G46, ledger (116)). This gate used to "skip"
        // a type that still carried a metavariable, through
        // `has_expr_mvar_quick` — constant false for elaborator metas (bit-63
        // FVars), so the skip never fired and the gate has always run on such
        // types, the metas opaque to both def-eq runs. A REAL skip would open
        // this Lean-fidelity refusal exactly where a later assignment could
        // still make the body kernel-acceptable, so the fail-closed behavior
        // the gate was measured with is kept and stated instead.
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
                expected: crate::error_render::term(&ty),
                actual: crate::error_render::term(&val_ty),
            });
        }
        Ok(())
    }

    /// An ascribed declaration must finish its header before its value runs.
    /// Without an ascription, value inference may solve binder types, but any
    /// still unresolved binder type is an error rather than a new parameter.
    pub(super) fn check_declaration_header(
        &mut self,
        parameters: &[clean_kernel::FVarId],
        result: Option<&Expr>,
    ) -> Result<(), ElabError> {
        self.retry_postponed_open_carrier_instances();
        let mut types = Vec::with_capacity(parameters.len() + 1);
        for parameter in parameters {
            let (_, _, ty) = self
                .locals
                .iter()
                .find(|(_, id, _)| id == parameter)
                .ok_or_else(|| {
                    ElabError::InternalInvariant("declaration header lost its parameter".into())
                })?;
            types.push(self.metas.instantiate(ty));
        }
        if let Some(result) = result {
            types.push(self.metas.instantiate(result));
        }
        if types
            .iter()
            .all(|ty| self.collect_meta_fvars(ty).is_empty())
        {
            return Ok(());
        }
        Err(ElabError::Unsupported {
            feature: "Failed to infer declaration header: unresolved parameter types and header holes must be resolved before the body is processed".into(),
        })
    }

    pub(super) fn check_declaration_default(
        &mut self,
        ty: &Expr,
        value: &SurfaceExpr,
    ) -> Result<(), ElabError> {
        // `(x : T := by tac)` is Lean's `binderTactic`, not `binderDefault`:
        // `expandBinderModifier` (Lean/Elab/Binders.lean) turns it into
        // `autoParam T stx` and only quotes the tactic, which runs at each
        // call site that omits the argument, never in the header. The parser
        // keeps parentheses, so `:= (by tac)` (a `binderDefault` whose term
        // Lean DOES elaborate against `T`) still takes the check below.
        if matches!(value, SurfaceExpr::ByTactic(..)) {
            return Ok(());
        }
        let value = self.elaborate_with_expected_type(value, Some(ty.clone()))?;
        let actual = self.infer_type(&value)?;
        let context = self.build_local_ctx();
        let mut unifier = crate::unify::Unifier::with_env(&mut self.metas, self.env, context);
        if matches!(
            unifier.unify(&actual, ty),
            crate::unify::UnifyResult::Success
        ) {
            Ok(())
        } else {
            Err(ElabError::TypeMismatch {
                expected: crate::error_render::term(ty),
                actual: crate::error_render::term(&actual),
            })
        }
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
        self.elab_def_body_record_sections(binders, ty, val, None, None)
    }

    pub(super) fn elab_decl_body(
        &mut self,
        binders: &[SurfaceBinder],
        ty: Option<&SurfaceExpr>,
        val: &SurfaceExpr,
    ) -> Result<(Expr, Expr, Vec<clean_kernel::FVarId>), ElabError> {
        let mut sections = Vec::new();
        let mut header_binders = Vec::new();
        let (ty, val) = self.elab_def_body_record_sections(
            binders,
            ty,
            val,
            Some(&mut sections),
            Some(&mut header_binders),
        )?;
        Ok((ty, val, sections))
    }

    fn elab_def_body_record_sections(
        &mut self,
        binders: &[SurfaceBinder],
        ty: Option<&SurfaceExpr>,
        val: &SurfaceExpr,
        mut section_fvars: Option<&mut Vec<clean_kernel::FVarId>>,
        mut header_binders: Option<&mut Vec<clean_kernel::FVarId>>,
    ) -> Result<(Expr, Expr), ElabError> {
        // Keep the explicit-binder push/pop stack unchanged. Only the complete
        // declaration header/body boundary adds its auto-implicit packet; the
        // original vector is restored even if header/body elaboration fails.
        let saved_recursive_parameters = if binders.is_empty() && !self.in_term_body {
            self.recursive_def_ctx
                .as_ref()
                .map(|ctx| ctx.parameters.clone())
        } else {
            None
        };
        let result = stack_safe(|| {
            use clean_parser::SurfaceLit;

            if binders.is_empty() {
                // Structural-recursion sites this body's lowering records are
                // checked once the body is elaborated (`recursion_site`).
                let rec_site_mark = self.structural_rec_site_mark();
                let ty_expr = if let Some(ty) = ty {
                    // Signature position: the result type may auto-bind
                    // implicits (Lean header elaboration). It is a type
                    // position, so `theorem t : b := …` with `b : Bool` states
                    // `b = true` (G34, `elab_type_position`).
                    if let Some(prepared) = self.single_theorem_prepared_result_type() {
                        prepared
                    } else {
                        let ty_expr = self.elaborate_single_theorem_header_annotation(ty)?;
                        self.coerce_type_position(ty_expr)
                    }
                } else if header_binders.is_some() {
                    // Lean's inferred header has a result-type metavariable.
                    // Elaborate the body once against it, so the ordinary term
                    // finalizer inserts implicit arguments and solves its type.
                    let sort = Expr::sort(self.fresh_universe_param());
                    self.fresh_meta(sort)
                } else {
                    if saved_recursive_parameters.is_some() {
                        self.capture_recursive_auto_implicit_parameters()?;
                    }
                    let val_expr = self.with_term_body_scope(|this| this.elaborate(val))?;
                    self.infer_type(&val_expr)?
                };

                if saved_recursive_parameters.is_some() {
                    self.capture_recursive_auto_implicit_parameters()?;
                }
                self.sync_single_theorem_result_type(&ty_expr)?;
                if ty.is_some() {
                    if let Some(parameters) = header_binders.as_deref() {
                        self.check_declaration_header(parameters, Some(&ty_expr))?;
                    }
                }

                // Written types request implicit-lambda introduction. Inferred
                // headers carry a fresh result metavariable, so the shared term
                // finalizer resolves the body instead. Aliases preserve the
                // target telescope directly in their own declaration path.
                let wrap_implicit_lambda = ty.is_some();
                let val_expr = self.elab_def_value_maybe_implicit_lambda(
                    val,
                    &ty_expr,
                    wrap_implicit_lambda,
                    |this, ty_expr| {
                        // Set expected type for bidirectional type checking (#172)
                        // This enables anonymous constructor syntax ⟨...⟩ to determine
                        // the target structure from the type annotation.
                        let prev_expected = this.current_expected_type.take();
                        let val_expr = if ty.is_some() {
                            match val {
                                // When we have `def foo : UInt8 := 1`, elaborate the literal
                                // directly to the expected type using the type's constructor.
                                SurfaceExpr::Lit(_, SurfaceLit::Nat(n)) => this
                                    .elab_nat_literal_with_expected(
                                        &clean_kernel::BigNat::from_u64(*n),
                                        &ty_expr,
                                    ),
                                SurfaceExpr::Lit(_, SurfaceLit::BigNat(n)) => {
                                    this.elab_nat_literal_with_expected(n, &ty_expr)
                                }
                                _ => {
                                    // Explicit/synthetic `sorry` and tactic-style proofs
                                    // record global trust counters during elaboration.
                                    // A failed speculative pass would leak that debt into
                                    // the successful retry, so elaborate these surfaces once.
                                    if Self::contains_retry_sensitive_surface(val) {
                                        let expected_ty = this
                                            .metas
                                            .instantiate_levels(&this.metas.instantiate(&ty_expr));
                                        this.current_expected_type = Some(expected_ty.clone());
                                        let result =
                                            this.with_term_body_scope(|this| this.elaborate(val));
                                        this.current_expected_type = prev_expected.clone();
                                        let val_expr = result?;
                                        this.apply_implicit_to_expected_type_for_surface(
                                            val,
                                            &val_expr,
                                            &expected_ty,
                                        )?
                                    } else {
                                        // Avoid pushing the full declaration type into every body
                                        // expression up front. Application-valued bodies like
                                        // `PEmpty.rec (fun _ => Nat)` and `id` should elaborate
                                        // from their own type first, then be checked against the
                                        // declaration type. If that lane fails, retry with the
                                        // old expected-type-driven elaboration for forms that need it
                                        // (`sorry`, anonymous constructors, untyped lambdas, ...).
                                        if let Some(expr) =
                                            this.try_elab_def_value_without_expected(val, &ty_expr)?
                                        {
                                            expr
                                        } else {
                                            this.current_expected_type = Some(ty_expr.clone());
                                            let result = this
                                                .with_term_body_scope(|this| this.elaborate(val));
                                            this.current_expected_type = prev_expected.clone();
                                            let val_expr = result?;
                                            this.apply_implicit_to_expected_type_for_surface(
                                                val, &val_expr, &ty_expr,
                                            )?
                                        }
                                    }
                                }
                            }
                        } else if header_binders.is_some() {
                            this.with_term_body_scope(|ctx| {
                                ctx.elaborate_with_expected_type(val, Some(ty_expr.clone()))
                            })?
                        } else {
                            this.with_term_body_scope(|this| this.elaborate(val))?
                        };

                        this.current_expected_type = prev_expected;
                        Ok(val_expr)
                    },
                )?;

                // Every structural `.rec` the body's lowering emitted must be
                // the value of the whole body, or its induction hypotheses
                // would not stand for this definition (`recursion_site`).
                self.check_structural_recursion_sites(&val_expr, rec_site_mark)?;

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
                // Close any postponed `?x =?= max ?x ?y` (Lean's `solveSelfMax`)
                // BEFORE the value's type is unified with the stated type:
                // that comparison is level-exact, and a self-max equation left
                // open by the instance search made `Sort (?x+1)` against
                // `Sort (max ?x ?y + 1)` fail here and surface as a kernel
                // mismatch (measured 2026-09-11 on `example`s over a `Type*`
                // carrier taking the `Pi` instance path).
                self.resolve_self_max_level_equations();
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
                    // B18 + B07 (2026-09-20): gate on the term the KERNEL WILL SEE.
                    // Since 2026-09-28 that is the elaborated term itself:
                    // `Bind.bind`/`Pure.pure` are Lean's class projections
                    // carrying their instance, so the kernel unfolds them here
                    // exactly as it will in `add_decl`. (Until then they were
                    // instance-less AXIOMS — which proved `False` — rewritten
                    // into `Proj` form by a post-pass this gate had to run first,
                    // or `theorem t : (do let x <- some 1; pure (x+1) : Option
                    // Nat) = some 2 := rfl` was rejected here.)
                    let gate_val = val_expr.clone();
                    let gate_ty = ty_expr.clone();
                    self.reject_body_defeq_only_via_irreducible(&gate_val, &gate_ty)?;
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
                    self.reject_body_type_mismatch(&gate_val, &gate_ty)?;
                }

                if ty.is_none() {
                    if let Some(parameters) = header_binders.as_deref() {
                        self.check_declaration_header(parameters, None)?;
                    }
                }
                return Ok((ty_expr, val_expr));
            }

            // Process first binder
            let binder = &binders[0];
            let prepared = self.single_theorem_prepared_binder()?;
            let binder_ty = if let Some((_, ty)) = &prepared {
                ty.clone()
            } else if let Some(ty) = &binder.ty {
                let elaborated = self.elaborate_single_theorem_header_annotation(ty)?;
                // An EARLIER untyped binder used HERE as a type is where its own
                // type gets solved (`{alpha}` then `(x : alpha)`). See
                // `ElabCtx::solve_binder_type_from_use`.
                self.solve_binder_type_from_use(&elaborated);
                // A type position: `(h : o != none)` binds `h : (o != none) =
                // true` (G34, `elab_type_position`).
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

            let binder_ty = self.coerce_type_position(binder_ty);
            if header_binders.is_some() {
                if let Some(default) = &binder.default {
                    self.check_declaration_default(&binder_ty, default)?;
                }
            }
            self.check_instance_binder_annotation(binder.info, &binder_ty)?;

            let bi = convert_binder_info(binder.info);
            let fvar = if let Some((fvar, _)) = prepared {
                self.push_local_with_fvar(binder.name.clone(), fvar, binder_ty.clone());
                fvar
            } else {
                self.push_local(binder.name.clone(), binder_ty.clone())
            };
            if binder.name.is_section_variable() {
                if let Some(sections) = section_fvars.as_mut() {
                    sections.push(fvar);
                }
            }
            self.note_local_forall_binder_names(fvar, binder.ty.as_deref(), &binder_ty);
            self.capture_binder_info(binder, fvar);
            self.note_let_rec_binder(fvar, bi);
            let single_theorem_header =
                self.note_single_theorem_header_binder(&binder.name, fvar, &binder_ty)?;
            if let Some(ctx) = &mut self.recursive_def_ctx {
                ctx.parameters.push(RecursiveParam {
                    name: binder.name.clone(),
                    binder_info: bi,
                    captured_section: binder.name.is_section_variable(),
                    fvar,
                    type_: binder_ty.clone(),
                });
            }

            // Any local whose type is a class is a local instance (Lean's rule;
            // see `binder_is_local_instance`), not only the `[…]` spelling.
            let is_inst_implicit = self.binder_is_local_instance(bi, &binder_ty);
            if is_inst_implicit {
                self.push_local_instance(fvar, binder_ty.clone());
            }

            // Recursively process remaining binders
            if let Some(parameters) = header_binders.as_mut() {
                parameters.push(fvar);
            }
            let inner = self.elab_def_body_record_sections(
                &binders[1..],
                ty,
                val,
                section_fvars,
                header_binders.as_deref_mut(),
            );
            if let Some(parameters) = header_binders.as_mut() {
                parameters.pop();
            }
            self.restore_single_theorem_header_binder(single_theorem_header);
            if let Some(ctx) = &mut self.recursive_def_ctx {
                ctx.parameters.pop();
            }

            // Pop local instance before popping local
            if is_inst_implicit {
                self.pop_local_instance();
            }
            // A later header binder may have introduced an auto-implicit
            // above this binder. Remove the binder we own, retaining that
            // packet for declaration finalization.
            self.locals.retain(|(_, id, _)| *id != fvar);
            let (inner_ty, inner_val) = inner?;

            // Fix #443: Instantiate metas BEFORE abstracting FVars
            // If a meta is assigned to an expression containing the FVar (e.g., `?m := Proj(C, 0, FVar(x))`),
            // we must substitute the meta first so the FVar is visible for abstraction.
            // Otherwise, abstract_fvar won't find the FVar (it's hidden inside the uninstantiated meta),
            // and after later instantiation, the FVar remains unabstracted.
            let ty_inst = self.metas.instantiate(&inner_ty);
            let ty_abs = self.metas.instantiate_levels(&ty_inst.abstract_fvar(fvar));
            let val_inst = self.metas.instantiate(&inner_val);
            let val_abs = self.metas.instantiate_levels(&val_inst.abstract_fvar(fvar));

            // NOT instantiated here, deliberately. An untyped binder's domain
            // IS a metavariable (`?α`) that a later use in this telescope may
            // have just solved, so instantiating it looks necessary — but every
            // caller of `elab_def_body` already runs `metas.instantiate` +
            // `instantiate_levels` over the WHOLE returned pair
            // (`elab_decl_value.rs`, both the def and the theorem site), which
            // reaches this domain through the Pi. Adding it here was measured
            // to be unobservable: mutation `M5-def-body-domain-not-instantiated`
            // deletes it and all nine tests of
            // `infer::tests::untyped_binder_type_from_use` still pass.
            Ok((
                Expr::pi(bi, binder_ty.clone(), ty_abs),
                Expr::lam(bi, binder_ty, val_abs),
            ))
        });
        if let (Some(parameters), Some(ctx)) =
            (saved_recursive_parameters, self.recursive_def_ctx.as_mut())
        {
            ctx.parameters = parameters;
        }
        // Declaration boundary: the last place a postponed
        // heterogeneous-operator instance goal can still be grounded, and the
        // only one that catches an ASCRIBED declaration. Measured while
        // landing the postponement:
        // `def rAdd2 : Nat → Nat → Nat := fun a b => a + b` reached the
        // fail-closed residual guard carrying a fully GROUND
        // `HAdd Nat Nat Nat` goal and an unfilled instance metavariable — the
        // ascription grounds the lambda's binder types by unifying with the
        // elaborated value's type, which happens AFTER the body's own
        // application has finished and drained. The nested frames run this
        // while their binder locals are still pushed (the recursive call
        // returns before `pop_local`), so a goal needing a local `[Add α]`
        // binder is resolvable here too. One `is_empty` test per frame when
        // nothing was postponed.
        self.retry_postponed_open_carrier_instances();
        result
    }

    pub(super) fn elab_decl_type(
        &mut self,
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
    ) -> Result<(Expr, Vec<clean_kernel::FVarId>), ElabError> {
        let mut sections = Vec::new();
        let ty = self.elab_axiom_type_with_fvars(binders, ty, &[], None, Some(&mut sections))?;
        Ok((ty, sections))
    }

    /// Elaborate a value declaration's header before its body, preserving the
    /// untyped-binder inference and type-position coercion of `elab_def_body`.
    pub(super) fn elab_def_header(
        &mut self,
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
    ) -> Result<(Expr, Vec<clean_kernel::FVarId>, usize), ElabError> {
        let mut header = DefinitionHeaderLocals {
            fvars: Vec::with_capacity(binders.len()),
            section_auto_count: 0,
        };
        let ty = self.elab_axiom_type_with_fvars(binders, ty, &[], Some(&mut header), None)?;
        self.check_declaration_header(&[], Some(&ty))?;
        Ok((ty, header.fvars, header.section_auto_count))
    }

    /// Helper that tracks outer fvars for proper abstraction
    fn elab_axiom_type_with_fvars(
        &mut self,
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        outer_fvars: &[(clean_kernel::FVarId, Expr, BinderInfo)],
        mut header_locals: Option<&mut DefinitionHeaderLocals>,
        mut section_fvars: Option<&mut Vec<clean_kernel::FVarId>>,
    ) -> Result<Expr, ElabError> {
        stack_safe(|| {
            let definition_header = header_locals.is_some();
            if binders.is_empty() {
                let mut result = self.elaborate_type_observing(ty)?;
                if definition_header {
                    result = self.coerce_type_position(result);
                }
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
            let binder_ty = if let Some(t) = &binder.ty {
                let elaborated = self.elaborate_type_observing(t)?;
                if definition_header {
                    self.solve_binder_type_from_use(&elaborated);
                }
                let instantiated = self.metas.instantiate(&elaborated);
                self.metas.instantiate_levels(&instantiated)
            } else if definition_header {
                let binder_sort = Expr::sort(self.fresh_universe_param());
                self.fresh_meta(binder_sort)
            } else {
                return Err(ElabError::CannotInfer);
            };

            let mut binder_ty = self.coerce_type_position(binder_ty);
            if definition_header {
                if let Some(default) = &binder.default {
                    self.check_declaration_default(&binder_ty, default)?;
                }
            }
            self.check_instance_binder_annotation(binder.info, &binder_ty)?;

            let bi = convert_binder_info(binder.info);
            let fvar = self.push_local(binder.name.clone(), binder_ty.clone());
            if binder.name.is_section_variable() {
                if let Some(sections) = section_fvars.as_mut() {
                    sections.push(fvar);
                }
            }
            if let Some(header) = header_locals.as_mut() {
                header.fvars.push(fvar);
                if binder.name.is_section_variable() {
                    header.section_auto_count = self.auto_implicit_count();
                }
            }
            self.note_local_forall_binder_names(fvar, binder.ty.as_deref(), &binder_ty);
            self.capture_binder_info(binder, fvar);

            // Any local whose type is a class is a local instance (Lean's rule;
            // see `binder_is_local_instance`), not only the `[…]` spelling.
            let is_inst_implicit = self.binder_is_local_instance(bi, &binder_ty);
            if is_inst_implicit {
                self.push_local_instance(fvar, binder_ty.clone());
            }

            // Recurse with this fvar added to the list
            let mut new_outer_fvars = outer_fvars.to_vec();
            new_outer_fvars.push((fvar, binder_ty.clone(), bi));
            let inner_ty = self.elab_axiom_type_with_fvars(
                &binders[1..],
                ty,
                &new_outer_fvars,
                header_locals,
                section_fvars,
            )?;

            // Pop local instance before popping local
            if is_inst_implicit {
                self.pop_local_instance();
            }
            self.locals.retain(|(_, id, _)| *id != fvar);

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
