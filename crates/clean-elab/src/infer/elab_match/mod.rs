// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Match and if-let elaboration.
//!
//! Extracted from `infer/mod.rs`. Contains methods for elaborating match expressions,
//! if-let expressions, and supporting utilities like casesOn/rec construction,
//! constructor pattern handling, and recursive arm elaboration.
//! Sub-modules split per #307.

mod alias_patterns;
mod ctor_order;
mod helpers;
mod if_let;
mod match_arms;
mod nested_ctor;
mod rec_arm;

use super::*;
use crate::tactic::bvar_ops::lift_bvars;
pub(in crate::infer) use alias_patterns::{
    expand_do_or_match_arms, expand_or_match_arms, prepend_do_alias_binding,
    wrap_alias_surface_body,
};

pub(in crate::infer) type ExtraParamBinding = (FVarId, BinderInfo, Expr);

/// Authenticated metadata for a match eliminator application.
///
/// Native `casesOn` constants are also registered recursors, so their
/// `arg_order` and global motive/minor counts come from the same packet.  Lean
/// imports `casesOn` as a plain definition, however; in that shape the wrapper
/// has the `MajorAfterMotive` layout while the member's primitive `.rec`
/// remains the authority for global motive/minor metadata (including restored
/// nested companions exposed as `.rec_1`, `.rec_2`, ...).
pub(in crate::infer) struct MatchEliminatorMetadata {
    pub major_after_motive: bool,
    pub recursor: clean_kernel::RecursorVal,
}

pub(in crate::infer) struct NestedPatternFieldPlan {
    pub fvar: FVarId,
    pub ty: Expr,
    pub plan: NestedPatternPlan,
}

pub(in crate::infer) enum NestedPatternPlan {
    None,
    Alias {
        alias_fvar: FVarId,
        alias_ty: Expr,
        alias_expr: Expr,
        inner: Box<NestedPatternPlan>,
    },
    CasesOn {
        field_expr: Expr,
        field_ty: Expr,
        target_ctor_name: String,
        target_fields: Vec<NestedPatternFieldPlan>,
    },
}

fn ensure_nat_pattern_scrutinee(
    context: &str,
    type_name: &str,
    pattern_kind: &str,
) -> Result<(), ElabError> {
    if type_name == "Nat" {
        Ok(())
    } else {
        Err(ElabError::NotImplemented(format!(
            "{context}: {pattern_kind} patterns are only supported for Nat scrutinees, got {type_name}"
        )))
    }
}

pub(in crate::infer) fn ensure_supported_literal_pattern(
    context: &str,
    type_name: &str,
    lit: &SurfaceLit,
) -> Result<(), ElabError> {
    ensure_nat_pattern_scrutinee(context, type_name, "literal")?;
    match lit {
        SurfaceLit::Nat(_) => Ok(()),
        _ => Err(ElabError::NotImplemented(format!(
            "{context}: only Nat literal patterns are currently supported, got {lit:?}"
        ))),
    }
}

impl<'a> ElabCtx<'a> {
    /// Resolve the application layout and the authoritative recursor packet for
    /// a match eliminator.  Missing metadata is an error: `all_names` describes
    /// only public inductive members after nested restore and therefore cannot
    /// reconstruct erased helper motives or minors.
    pub(in crate::infer) fn match_eliminator_metadata(
        &self,
        type_name: &str,
        eliminator_name: &Name,
        is_cases_on: bool,
    ) -> Result<MatchEliminatorMetadata, ElabError> {
        if let Some(rec) = self.env.get_recursor(eliminator_name) {
            if rec.inductive_name != Name::from_string(type_name) {
                return Err(ElabError::InternalInvariant(format!(
                    "recursor metadata `{eliminator_name}` identifies inductive `{}` instead of match scrutinee `{type_name}`",
                    rec.inductive_name
                )));
            }
            self.authenticate_recursor_cached(eliminator_name)?;
            let ind_info = self.authenticate_inductive_metadata(&rec.inductive_name)?;
            self.recursor_minor_rules(ind_info, rec)?;
            return Ok(MatchEliminatorMetadata {
                major_after_motive: rec.arg_order
                    == clean_kernel::RecursorArgOrder::MajorAfterMotive,
                recursor: rec.clone(),
            });
        }

        if !is_cases_on {
            return Err(ElabError::InternalInvariant(format!(
                "recursive match selected `{eliminator_name}` without recursor metadata"
            )));
        }

        // In an imported environment `T.casesOn` is a definition whose value
        // reorders `T.rec` arguments.  Its wrapper layout is fixed by Lean, but
        // all arity/rule information must still come from the genuine `.rec`.
        let rec_name = Name::from_string(&format!("{type_name}.rec"));
        let recursor = self
            .env
            .get_recursor(&rec_name)
            .ok_or_else(|| ElabError::TypeMismatch {
                expected: format!(
                    "recursor metadata `{rec_name}` for imported eliminator `{eliminator_name}`"
                ),
                actual: "missing".to_string(),
            })?
            .clone();
        if recursor.inductive_name != Name::from_string(type_name) {
            return Err(ElabError::InternalInvariant(format!(
                "recursor metadata `{rec_name}` identifies inductive `{}` instead of imported cases family `{type_name}`",
                recursor.inductive_name
            )));
        }
        self.authenticate_recursor_cached(&rec_name)?;
        let ind_info = self.authenticate_inductive_metadata(&recursor.inductive_name)?;
        let minor_rules = self.recursor_minor_rules(ind_info, &recursor)?;
        self.authenticate_imported_cases_on_cached(eliminator_name, &rec_name, &minor_rules)?;
        Ok(MatchEliminatorMetadata {
            major_after_motive: true,
            recursor,
        })
    }

    /// Lower a `String`/`Char`-scrutinee `match` into a nested surface
    /// `if scrutinee == lit then body else …` cascade.
    ///
    /// Returns `None` (so the caller keeps its prior behavior) unless every arm
    /// is either a `String`/`Char` literal pattern or a trailing catch-all
    /// (`Wildcard`, or a `Var` binder that is NOT a constructor name). A
    /// trailing catch-all is required so the cascade is total — without it
    /// there is no sound `else` to emit. Each literal arm becomes
    /// `if BEq.beq scrutinee <lit> then <body> else <rest>`; the catch-all arm
    /// supplies the innermost `else`. The produced surface tree is elaborated +
    /// kernel-checked by the standard path, so this is a sound desugaring.
    fn build_literal_match_cascade(
        scrutinee_surface: &SurfaceExpr,
        arms: &[clean_parser::SurfaceMatchArm],
    ) -> Option<SurfaceExpr> {
        use clean_parser::Span;

        if arms.is_empty() {
            return None;
        }

        // Split into leading literal arms + one trailing catch-all.
        let (lit_arms, default_arm) = arms.split_at(arms.len() - 1);
        let default_arm = &default_arm[0];

        // The trailing arm must be a genuine catch-all. A `Var` whose name looks
        // like a qualified constructor (`T.ctor`) is rejected — but String/Char
        // have no such constructors at play here, so a bare `Var`/`Wildcard` is
        // a binder. We bind the catch-all variable via a surface `let` so its
        // body can still refer to it (it equals the scrutinee).
        let default_body: SurfaceExpr = match &default_arm.pattern {
            SurfacePattern::Wildcard => default_arm.body.clone(),
            SurfacePattern::Var(name) if !name.contains('.') => SurfaceExpr::let_expr(
                name.clone(),
                scrutinee_surface.clone(),
                default_arm.body.clone(),
            ),
            _ => return None,
        };

        // Every leading arm must be a BEq-comparable literal pattern: String,
        // Char, or a numeric literal (`Int`/`UInt*` scrutinees). `BEq.beq` keys
        // the comparison off the scrutinee's type, so the numeric literal
        // elaborates at that type.
        for arm in lit_arms {
            match &arm.pattern {
                SurfacePattern::Lit(
                    SurfaceLit::String(_)
                    | SurfaceLit::Char(_)
                    | SurfaceLit::Nat(_)
                    | SurfaceLit::BigNat(_),
                ) => {}
                _ => return None,
            }
        }

        // Build the cascade bottom-up: start from the catch-all body, then wrap
        // each literal arm (in reverse) as `if scrutinee == lit then body else acc`.
        let mut acc = default_body;
        for arm in lit_arms.iter().rev() {
            let lit = match &arm.pattern {
                SurfacePattern::Lit(
                    l @ (SurfaceLit::String(_)
                    | SurfaceLit::Char(_)
                    | SurfaceLit::Nat(_)
                    | SurfaceLit::BigNat(_)),
                ) => l.clone(),
                _ => return None,
            };
            // cond := BEq.beq scrutinee <lit>   (a `Bool`, eliminated via Bool.rec)
            let cond = SurfaceExpr::App(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(Span::dummy(), "BEq.beq".to_string())),
                vec![
                    SurfaceArg::positional(scrutinee_surface.clone()),
                    SurfaceArg::positional(SurfaceExpr::Lit(Span::dummy(), lit)),
                ],
            );
            acc = SurfaceExpr::If(
                Span::dummy(),
                Box::new(cond),
                Box::new(arm.body.clone()),
                Box::new(acc),
            );
        }
        Some(acc)
    }
}

/// Desugar a non-zero Nat literal to nested constructor patterns (#796).
///
/// `Nat(0)` stays as `Lit(Nat(0))`; `Nat(k)` becomes `Ctor("Nat.succ", [Nat(k-1)])`.
/// Fully recursive: `Nat(2)` → `Ctor("Nat.succ", [Ctor("Nat.succ", [Lit(Nat(0))])])`.
pub(in crate::infer) fn desugar_nonzero_nat_lit(k: u64) -> SurfacePattern {
    if k == 0 {
        SurfacePattern::Lit(SurfaceLit::Nat(0))
    } else {
        SurfacePattern::Ctor("Nat.succ".to_string(), vec![desugar_nonzero_nat_lit(k - 1)])
    }
}

/// Desugar a Nat numeral-add pattern to nested `Nat.succ` constructor patterns.
///
/// `n + 1` becomes `Ctor("Nat.succ", [Var("n")])`.
/// `n + 2` becomes `Ctor("Nat.succ", [Ctor("Nat.succ", [Var("n")])])`.
pub(in crate::infer) fn desugar_nat_numeral_add_pattern(
    inner_pat: &SurfacePattern,
    k: u64,
) -> SurfacePattern {
    if k == 0 {
        inner_pat.clone()
    } else {
        SurfacePattern::Ctor(
            "Nat.succ".to_string(),
            vec![desugar_nat_numeral_add_pattern(inner_pat, k - 1)],
        )
    }
}

/// Normalize nested Nat numeral-add patterns into constructor form.
///
/// This is used before nested-constructor planning so the shared nested-ctor
/// infrastructure only has to reason about constructors, literals, and binders.
pub(in crate::infer) fn normalize_nested_nat_numeral_add_pattern(
    pat: &SurfacePattern,
) -> SurfacePattern {
    match pat {
        SurfacePattern::NumeralAdd(inner_pat, k) => {
            let normalized_inner = normalize_nested_nat_numeral_add_pattern(inner_pat);
            desugar_nat_numeral_add_pattern(&normalized_inner, *k)
        }
        SurfacePattern::Ctor(ctor_name, sub_pats) => SurfacePattern::Ctor(
            ctor_name.clone(),
            sub_pats
                .iter()
                .map(normalize_nested_nat_numeral_add_pattern)
                .collect(),
        ),
        _ => pat.clone(),
    }
}

pub(in crate::infer) fn numeral_add_pattern_binder_name(
    context: &str,
    type_name: &str,
    inner_pat: &SurfacePattern,
    k: u64,
) -> Result<String, ElabError> {
    ensure_nat_pattern_scrutinee(context, type_name, "numeral-add")?;
    match inner_pat {
        SurfacePattern::Var(name) => Ok(name.clone()),
        SurfacePattern::Wildcard => Ok("_".to_string()),
        _ => Err(ElabError::NotImplemented(format!(
            "{context}: unsupported inner pattern for `n + {k}`: {inner_pat:?}"
        ))),
    }
}

pub(in crate::infer) fn ensure_ctor_pattern_arity(
    context: &str,
    full_ctor: &str,
    expected_fields: Option<usize>,
    actual_fields: usize,
) -> Result<(), ElabError> {
    if let Some(expected) = expected_fields {
        if actual_fields != expected {
            return Err(ElabError::ConstructorPatternArityMismatch {
                context: context.to_string(),
                ctor_name: full_ctor.to_string(),
                expected,
                actual: actual_fields,
            });
        }
    }
    Ok(())
}

/// Arity gate for a constructor pattern that ends in a `..` ellipsis: the
/// leading user-written patterns may fill *fewer* than (but never more than) the
/// constructor's `max_fields` positions; the ellipsis supplies the wildcards for
/// the rest. Writing more leading patterns than fields is still a genuine arity
/// error. The reported `expected` is the maximum the slot can hold.
pub(in crate::infer) fn ensure_ctor_pattern_arity_at_most(
    context: &str,
    full_ctor: &str,
    max_fields: usize,
    actual_fields: usize,
) -> Result<(), ElabError> {
    if actual_fields > max_fields {
        return Err(ElabError::ConstructorPatternArityMismatch {
            context: context.to_string(),
            ctor_name: full_ctor.to_string(),
            expected: max_fields,
            actual: actual_fields,
        });
    }
    Ok(())
}

fn bind_extra_params<F>(
    mut body: Expr,
    extra_params: &[ExtraParamBinding],
    mut mk_binder: F,
) -> Expr
where
    F: FnMut(BinderInfo, Expr, Expr) -> Expr,
{
    for (fvar, binder_info, ty) in extra_params.iter().rev() {
        body = body.abstract_fvar(*fvar);
        body = mk_binder(*binder_info, ty.clone(), body);
    }
    body
}

/// Wrap an expression with extra param lambdas for varying-parameter support (#1386).
///
/// Abstracts over the extra param fvars (innermost to outermost) and wraps in
/// lambda binders. This converts a body of type `ResultType` to a body of type
/// `P1_ty → P2_ty → ... → ResultType`.
pub(in crate::infer) fn wrap_with_extra_params(
    body: Expr,
    extra_params: &[ExtraParamBinding],
) -> Expr {
    bind_extra_params(body, extra_params, Expr::lam)
}

pub(in crate::infer) fn generalize_with_extra_params(
    body: Expr,
    extra_params: &[ExtraParamBinding],
) -> Expr {
    bind_extra_params(body, extra_params, Expr::pi)
}

/// Extract the *applied* domain type of every one of a (possibly nested/mutual)
/// recursor's motives, in order: `[Primary, Aux…]` (length `num_motives`).
///
/// Post-B0-B5 the nested container aux (e.g. `List Value`) is the REAL `List` and
/// is **erased** from the primary inductive's `all_names` on restore — yet the
/// recursor stays multi-motive. So the recursor type is the authoritative source:
/// `T.rec.{u} : (m₀ : T → Sort u) (m₁ : Aux₁ → Sort u) … (minors…) (major : T) → …`,
/// and each `Auxᵢ` is the domain of `mᵢ`'s type.
///
/// `rec_type` must already be positioned at the motive telescope — the caller
/// (`block_motive_domains`) instantiates the recursor's leading parameter binders
/// with the scrutinee's type arguments first, so each `Auxᵢ` here is a closed term
/// even for a parametric primary (e.g. `Rose α`). Returns fewer than `num_motives`
/// entries (caller rejects the result) if the telescope is malformed.
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(in crate::infer) fn motive_domains_from_rec_type(
    rec_type: &Expr,
    num_motives: usize,
) -> Vec<Expr> {
    let mut cursor = rec_type;
    let mut domains = Vec::with_capacity(num_motives);
    for _ in 0..num_motives {
        let ExprKind::Pi(_, motive_ty, body) = cursor.kind() else {
            break;
        };
        // `motive_ty` is `Domᵢ → … → Sort u`; its head Pi domain is `Domᵢ`.
        let ExprKind::Pi(_, dom, _) = motive_ty.kind() else {
            break;
        };
        domains.push(dom.as_ref().clone());
        cursor = body;
    }
    domains
}

impl<'a> ElabCtx<'a> {
    /// Lower a single catch-all arm — `match [h :] e with | x => body` (or
    /// `| _ => body` with a hypothesis) — as a let-binding:
    ///
    /// ```text
    /// let x := e; [let h : e = x := Eq.refl e;] body
    /// ```
    ///
    /// This is Lean's pattern-variable equation for the annotated
    /// discriminant: the pattern IS the variable, so `h : e = x`. Because
    /// `x := e` is a zeta-transparent let, the kernel accepts `Eq.refl e`
    /// against the annotation `e = x` — no axiom, no sorry, re-checked on
    /// registration.
    fn lower_single_catchall_match_arm(
        &mut self,
        discr_hyp: Option<&str>,
        pattern_var: Option<&str>,
        body: &SurfaceExpr,
        scrutinee_ty: &Expr,
        scrutinee_expr: &Expr,
    ) -> Result<Expr, ElabError> {
        // `x✝` mirrors Lean's inaccessible pattern variable for `| _ =>`.
        let var_name = pattern_var.unwrap_or("x✝");
        let fvar = self.push_local(var_name.to_string(), scrutinee_ty.clone());
        let hyp_binding = match discr_hyp {
            Some(h) => {
                let u = self.infer_sort(scrutinee_ty)?;
                let eq_ty = Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![u.clone()]),
                    [
                        scrutinee_ty.clone(),
                        scrutinee_expr.clone(),
                        Expr::fvar(fvar),
                    ],
                );
                let refl = Expr::apps(
                    Expr::const_(Name::from_string("Eq.refl"), vec![u]),
                    [scrutinee_ty.clone(), scrutinee_expr.clone()],
                );
                let h_fvar = self.push_local(h.to_string(), eq_ty.clone());
                Some((h.to_string(), h_fvar, eq_ty, refl))
            }
            None => None,
        };
        let body_expr =
            self.elaborate_with_expected_type(body, self.current_expected_type.clone())?;
        let mut inner = body_expr;
        if let Some((h_name, h_fvar, eq_ty, refl)) = hyp_binding {
            self.pop_local();
            inner = Expr::let_named(
                Name::from_string(&h_name),
                eq_ty,
                refl,
                inner.abstract_fvar(h_fvar),
                false,
            );
        }
        self.pop_local();
        let inner = inner.abstract_fvar(fvar);
        let non_dep = pattern_var.is_none() && discr_hyp.is_none();
        Ok(Expr::let_named(
            Name::from_string(var_name),
            scrutinee_ty.clone(),
            scrutinee_expr.clone(),
            inner,
            non_dep,
        ))
    }

    /// Elaborate a match expression.
    ///
    /// match e with | pat1 => body1 | pat2 => body2 | ...
    /// Desugars to: T.casesOn (motive) e alt1 alt2 ...
    ///
    /// For simple cases with variable/wildcard patterns, we use let bindings.
    /// For constructor patterns, we build casesOn applications.
    /// For q-patterns (Qq Phase 3), we use unification-based matching.
    ///
    /// `discr_hyp` is Lean's annotated discriminant (`match h : e with`);
    /// see [`Self::elab_match_with_scrutinee_hyp`].
    pub(in crate::infer) fn elab_match(
        &mut self,
        discr_hyp: Option<&str>,
        scrutinee: &SurfaceExpr,
        arms: &[clean_parser::SurfaceMatchArm],
    ) -> Result<Expr, ElabError> {
        // Elaborate the scrutinee with the match's expected (result) type CLEARED.
        // A scrutinee's type is independent of the match's result type, so leaking
        // the expected result type into scrutinee elaboration corrupts inference:
        // for `(match (10, 20) with | (a, b) => a) = 10`, the LHS match's expected
        // type is a fresh metavar `?m` (Eq's `α`, pinned later by the RHS `10`).
        // Elaborating the scrutinee `Prod.mk 10 20` under `?m` unifies the
        // parameterized ctor's result `Prod ?α ?β` with `?m`, wrongly assigning
        // `?m := Prod Nat Nat` — so `branch_ty` becomes `Prod Nat Nat` (the
        // scrutinee type) and each arm body (`a : Nat`) is rejected against it. A
        // monomorphic scrutinee (`Box.mk 5 : Box`) does not exhibit this because its
        // concrete result never flows into `?m`. Clearing here is the Lean-faithful
        // order (elaborate the discriminant on its own, then the result type drives
        // the arms); it is restored immediately for `branch_ty`/arm elaboration.
        let saved_scrutinee_expected = self.current_expected_type.take();
        let scrutinee_expr = self.elaborate(scrutinee)?;
        let scrutinee_ty = self.infer_type(&scrutinee_expr)?;
        self.current_expected_type = saved_scrutinee_expected;
        if arms.is_empty() {
            // `nomatch e` / arm-less `match e with`: the scrutinee must be an
            // uninhabited (zero-constructor) type, discharged by its recursor
            // with zero minor premises. See [`Self::elab_empty_match`].
            return self.elab_empty_match(scrutinee_expr, scrutinee_ty);
        }
        self.elab_match_with_scrutinee_hyp(
            discr_hyp,
            scrutinee_expr,
            scrutinee_ty,
            Some(scrutinee),
            arms,
        )
    }

    /// Elaborate an **empty match** — Lean's `nomatch e` sugar, or a
    /// `match e with` that lists no arms. The scrutinee's type must be an
    /// *uninhabited* inductive with **zero constructors and no indices**
    /// (`False`, `Empty`, `PEmpty α`, or a user `inductive T` written with no
    /// `|` arms; type parameters are allowed). There are no branches to
    /// elaborate: the eliminator is the inductive's own recursor applied with
    /// **zero minor premises** —
    ///
    /// ```text
    /// @T.rec.{u, …} params… (fun _ : T => C) e   :   C
    /// ```
    ///
    /// where `C` is the expected result type (for `False` this is exactly the
    /// term `False.elim` expands to). The emitted term is ordinary kernel
    /// syntax, re-checked on registration — it can only narrow, never widen, the
    /// trusted surface.
    ///
    /// FAILS LOUD (never silently accepts) when the scrutinee type is not a
    /// zero-constructor inductive (a real, arm-bearing match is required), when
    /// it carries indices (`Fin 0` and friends are empty only *at an index* and
    /// need `noConfusion` index refutation — out of scope here), or when no
    /// expected type is in scope (the constant motive would be unconstrained).
    pub(in crate::infer) fn elab_empty_match(
        &mut self,
        scrutinee_expr: Expr,
        scrutinee_ty: Expr,
    ) -> Result<Expr, ElabError> {
        let scrutinee_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&scrutinee_ty));
        let scrutinee_ty_whnf = self.whnf(&scrutinee_ty);

        // Equation-empty case: `nomatch (h : @Eq T a b)` with `a`, `b` DISTINCT
        // constructors — the equation is absurd and is refuted by `T`'s
        // `noConfusion` (see [`Self::elab_empty_match_eq`]). Intercept before the
        // zero-constructor path below: `Eq` itself has a constructor (`Eq.refl`),
        // so that path would otherwise reject a genuinely-refutable equation.
        if let ExprKind::Const(head_name, _) = scrutinee_ty_whnf.get_app_fn().kind() {
            if *head_name == Name::from_string("Eq") && scrutinee_ty_whnf.get_app_num_args() == 3 {
                return self.elab_empty_match_eq(&scrutinee_ty_whnf, scrutinee_expr);
            }
        }

        let type_name = self.get_type_name(&scrutinee_ty_whnf)?;

        let ind = self
            .env
            .get_inductive(&Name::from_string(&type_name))
            .ok_or_else(|| {
                ElabError::NotImplemented(format!(
                    "empty match: `{type_name}` is not an inductive type"
                ))
            })?;

        // A zero-minor recursor only discharges a type that is uninhabited *by
        // construction* (no constructors). A type WITH constructors demands real
        // arms — refuse loudly rather than silently accept an ill-formed match.
        if !ind.constructor_names.is_empty() {
            return Err(ElabError::NotImplemented(format!(
                "empty match on `{type_name}`, which has {} constructor(s); \
                 a match with arms is required",
                ind.constructor_names.len()
            )));
        }
        // Index-empty types (`Fin 0`) do have constructors and are empty only at
        // a specific index; discharging them needs `noConfusion` on the index,
        // not a zero-minor recursor. Out of scope — fail loud.
        if ind.num_indices != 0 {
            return Err(ElabError::NotImplemented(format!(
                "empty match on indexed type `{type_name}` \
                 (needs noConfusion index refutation, unsupported)"
            )));
        }

        // No arms means the result type cannot be inferred — it must come from
        // the expected type in scope.
        let expected = self.current_expected_type.clone().ok_or_else(|| {
            ElabError::NotImplemented(
                "empty match requires a known expected (result) type".to_string(),
            )
        })?;
        let expected = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&expected));

        // motive := fun (_ : T) => C  — constant / non-dependent (the empty type
        // has no inhabitant for C to depend on). Locals are fvars, so C needs no
        // de Bruijn lift when placed under the fresh binder.
        let motive = Expr::lam(
            BinderInfo::Default,
            scrutinee_ty_whnf.clone(),
            expected.clone(),
        );

        let rec_name = Name::from_string(&format!("{type_name}.rec"));
        let levels = self.eliminator_levels(&rec_name, &scrutinee_ty_whnf, &expected)?;
        let mut elim = Expr::const_(rec_name, levels);
        // params… then the motive; zero minors (zero constructors); zero indices;
        // finally the major (the scrutinee).
        elim = self.apply_eliminator_params(elim, &scrutinee_ty_whnf, &type_name)?;
        elim = Expr::app(elim, motive);
        elim = Expr::app(elim, scrutinee_expr);
        Ok(elim)
    }

    /// Equation-empty `nomatch (h : @Eq T a b)`: when `a` and `b` are DISTINCT
    /// constructors the equation is absurd, and is discharged by `T`'s
    /// auto-generated `noConfusion`:
    ///
    /// ```text
    /// @T.noConfusion.{u, …} C a b h : C
    /// ```
    ///
    /// `T.noConfusionType C a b` ι-reduces to `C` **exactly when** `a` and `b`
    /// have different constructor heads; for the same constructor (or a genuine
    /// `n = n`) it reduces to a function type `(… = … → C) → C`, which is *not*
    /// `C`. The def-eq gate below — and the kernel re-check on registration —
    /// therefore REJECT any non-refutable equation. Distinctness is enforced by
    /// typing, never bypassed; the emitted term is ordinary kernel syntax.
    ///
    /// Handles both a MONOMORPHIC `T` (`Nat`, `Bool`, a user enum — via the
    /// classic homogeneous noConfusion `@T.noConfusion C a b h`) and a
    /// PARAMETRIC `T` (`List α`, `Option α`, a user `Pair α` — via the v4.30
    /// heterogeneous noConfusion, threading the type parameters plus an `Eq.refl`
    /// per parameter and a `heq_of_eq`-lifted `HEq` for the values). A missing
    /// `T.noConfusion`, a universe-arity mismatch, an absent expected type, a
    /// non-inductive equation type, and any build the refutation gate cannot
    /// type-check (e.g. a dependent parameter needing `HEq` in a param slot) all
    /// fail LOUD — never a silently-accepted or unchecked term.
    fn elab_empty_match_eq(
        &mut self,
        eq_ty_whnf: &Expr,
        scrutinee_expr: Expr,
    ) -> Result<Expr, ElabError> {
        // `@Eq T a b` — exactly three args (the caller checked the arity).
        // `get_app_args_iter` yields *reverse* spine order (`b, a, T`); reverse
        // to source order `[T, a, b]`.
        let mut args: Vec<Expr> = eq_ty_whnf.get_app_args_iter().cloned().collect();
        args.reverse();
        let (t, a, b) = (&args[0], &args[1], &args[2]);

        // `T` must be an inductive constant, possibly applied to type parameters.
        let t_whnf = self.whnf(t);
        let ExprKind::Const(tname, tlevels) = t_whnf.get_app_fn().kind() else {
            return Err(ElabError::NotImplemented(
                "nomatch: the equation's type is not an inductive constant".to_string(),
            ));
        };
        let num_params = t_whnf.get_app_num_args();

        let nc_name = Name::from_string(&format!("{tname}.noConfusion"));
        let nc_arity = self
            .env
            .get_const(&nc_name)
            .ok_or_else(|| {
                ElabError::NotImplemented(format!(
                    "nomatch: `{nc_name}` is unavailable — equation refutation \
                     needs the type's noConfusion"
                ))
            })?
            .level_params
            .len();

        let expected = self.current_expected_type.clone().ok_or_else(|| {
            ElabError::NotImplemented(
                "nomatch on an equation requires a known expected (result) type".to_string(),
            )
        })?;
        let expected = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&expected));

        // noConfusion levels = [motive/result universe, …T's universe params].
        let motive_level = self.motive_universe_level(&expected)?;
        let mut levels = Vec::with_capacity(tlevels.len() + 1);
        levels.push(motive_level);
        levels.extend(tlevels.iter().cloned());
        if levels.len() != nc_arity {
            return Err(ElabError::NotImplemented(format!(
                "nomatch: `{nc_name}` expects {nc_arity} universe param(s), built {} \
                 (unsupported equation type)",
                levels.len()
            )));
        }
        let nc = Expr::const_(nc_name, levels);

        let term = if num_params == 0 {
            // MONOMORPHIC `T` (Nat, Bool, a user enum) — the classic *homogeneous*
            // noConfusion: `@T.noConfusion.{u} C a b h`.
            Expr::apps(nc, [expected.clone(), a.clone(), b.clone(), scrutinee_expr])
        } else {
            // PARAMETRIC `T` (`List α`, `Option α`, a user `Pair α`) — the
            // generated noConfusion is the v4.30 *heterogeneous* form, which
            // threads BOTH sides' type parameters and takes a parameter equality
            // per parameter followed by a `HEq` for the values:
            //   @T.noConfusion.{u,…} C p… a p… b (h_p : p = p)… (h_t : HEq a b)
            // For a *homogeneous* equation `a b : T p…` the two parameter sets
            // coincide, so each `h_p` is `Eq.refl` and `h_t` is `heq_of_eq h`.
            // Operand universe levels are read off via `infer_sort`. A wrong build
            // — e.g. a *dependent* parameter whose slot wants `HEq`, not `Eq` — is
            // caught by the `is_def_eq` gate below and the kernel re-check, so it
            // fails LOUD rather than producing an ill-typed term (never bypassed).
            let params = self.extract_type_args(&t_whnf, num_params as u32);

            // Per-parameter reflexivity proof `@Eq.refl.{lvl} A p : @Eq A p p`.
            let mut refls = Vec::with_capacity(params.len());
            for p in &params {
                let p_ty = self.infer_type(p)?;
                let p_lvl = self.infer_sort(&p_ty)?;
                refls.push(Expr::apps(
                    Expr::const_(Name::from_string("Eq.refl"), vec![p_lvl]),
                    [p_ty, p.clone()],
                ));
            }

            // `@heq_of_eq.{m} (T p…) a b h : HEq a b` — lift the homogeneous `Eq`.
            let val_ty = self.infer_type(a)?;
            let val_lvl = self.infer_sort(&val_ty)?;
            let heq = Expr::apps(
                Expr::const_(Name::from_string("heq_of_eq"), vec![val_lvl]),
                [val_ty, a.clone(), b.clone(), scrutinee_expr],
            );

            // Assemble in the hetero binder order: C, p…, a, p…, b, refl…, h_t.
            let mut app_args = Vec::with_capacity(2 * params.len() + refls.len() + 3);
            app_args.push(expected.clone());
            app_args.extend(params.iter().cloned());
            app_args.push(a.clone());
            app_args.extend(params.iter().cloned());
            app_args.push(b.clone());
            app_args.extend(refls);
            app_args.push(heq);
            Expr::apps(nc, app_args)
        };

        // Distinctness gate: for distinct ctors `noConfusionType C a b` reduces
        // to `C`; otherwise it reduces to a function type, so this rejects LOUD.
        // (The kernel re-checks the same term on registration.)
        let inferred = self.infer_type(&term)?;
        if !self.is_def_eq(&inferred, &expected) {
            return Err(ElabError::NotImplemented(
                "nomatch: the equation is not between distinct constructors — its \
                 noConfusion does not refute it"
                    .to_string(),
            ));
        }
        Ok(term)
    }

    /// Plain-match entry point (no annotated discriminant). Kept as the
    /// callers' interface for the parser-generated shapes (pattern lambdas,
    /// if-let, …), which never carry a discriminant hypothesis.
    pub(in crate::infer) fn elab_match_with_scrutinee(
        &mut self,
        scrutinee_expr: Expr,
        scrutinee_ty: Expr,
        scrutinee_surface: Option<&SurfaceExpr>,
        arms: &[clean_parser::SurfaceMatchArm],
    ) -> Result<Expr, ElabError> {
        self.elab_match_with_scrutinee_hyp(
            None,
            scrutinee_expr,
            scrutinee_ty,
            scrutinee_surface,
            arms,
        )
    }

    /// Lower a match, optionally with Lean's annotated discriminant
    /// (`match h : e with …`, `Lean/Parser/Term.lean:275 matchDiscr` /
    /// `Lean/Elab/Match.lean:67 Discr`): each branch with pattern `pᵢ` binds
    /// `h : e = pᵢ` (the per-branch pattern instance).
    ///
    /// Lowering for the hypothesis form: the motive is wrapped with the
    /// equation binder —
    ///   `T.casesOn (motive := fun x => e = x → C) e
    ///      (fun fields… (h : e = ctorᵢ fields…) => bodyᵢ) … (Eq.refl e)`
    /// — so the equality hypothesis is exactly the casesOn-refined per-branch
    /// equation, and the final application to `rfl` discharges the wrapper.
    /// Every produced term is ordinary kernel syntax, re-checked on
    /// registration. Unsupported sub-shapes fail LOUD with
    /// [`ElabError::MatchDiscrHypUnsupported`]; the hypothesis is never
    /// silently dropped.
    pub(in crate::infer) fn elab_match_with_scrutinee_hyp(
        &mut self,
        discr_hyp: Option<&str>,
        scrutinee_expr: Expr,
        scrutinee_ty: Expr,
        scrutinee_surface: Option<&SurfaceExpr>,
        arms: &[clean_parser::SurfaceMatchArm],
    ) -> Result<Expr, ElabError> {
        self.with_temporary_local_scope(|this| {
            this.elab_match_with_scrutinee_hyp_inner(
                discr_hyp,
                scrutinee_expr,
                scrutinee_ty,
                scrutinee_surface,
                arms,
            )
        })
    }

    fn elab_match_with_scrutinee_hyp_inner(
        &mut self,
        discr_hyp: Option<&str>,
        scrutinee_expr: Expr,
        scrutinee_ty: Expr,
        scrutinee_surface: Option<&SurfaceExpr>,
        arms: &[clean_parser::SurfaceMatchArm],
    ) -> Result<Expr, ElabError> {
        if arms.is_empty() {
            return self.elab_empty_match(scrutinee_expr, scrutinee_ty);
        }

        // Resolve solved metavars and canonicalize levels before motive/arm elaboration (#2727).
        let scrutinee_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&scrutinee_ty));

        // Check if any arm uses q-patterns - these need special handling
        // Part of #16: Qq quotation support - Phase 3
        if self.has_q_patterns(arms) {
            if let Some(h) = discr_hyp {
                return Err(ElabError::MatchDiscrHypUnsupported {
                    hyp: h.to_string(),
                    shape: "q-pattern (Qq quotation) match arms".to_string(),
                });
            }
            return self.elaborate_q_match(&scrutinee_expr, &scrutinee_ty, arms);
        }

        // Pre-expand Or-pattern arms: `| p1 | p2 => body` becomes two arms
        // with the same body. This must happen before casesOn construction.
        let expanded_arms = expand_or_match_arms(arms);
        let arms = &expanded_arms;

        // Check for simple single-arm cases first
        if arms.len() == 1 {
            let rewritten_simple_arm = match &arms[0].pattern {
                SurfacePattern::As(name, inner_pat)
                    if matches!(
                        inner_pat.as_ref(),
                        SurfacePattern::Var(_) | SurfacePattern::Wildcard
                    ) =>
                {
                    let (pattern, alias_value) = self.rewrite_as_pattern_inner(
                        "match arm pattern",
                        &scrutinee_ty,
                        inner_pat,
                    )?;
                    Some(clean_parser::SurfaceMatchArm {
                        span: arms[0].span,
                        pattern,
                        body: wrap_alias_surface_body(name, alias_value, &arms[0].body),
                    })
                }
                _ => None,
            };
            let arm = rewritten_simple_arm.as_ref().unwrap_or(&arms[0]);
            // A single-arm `Var` pattern is normally a catch-all binder
            // (`let x := e in body`). But the parser also produces `Var("T.ctor")`
            // for a *nullary constructor* written without parentheses
            // (e.g. `| Eq.refl =>` or `| Option.none =>`). Such an arm must NOT
            // be lowered as a let-binding — it is a genuine constructor match
            // whose minor premise refines the motive (the dependent-elimination
            // / GADT case, e.g. `symm` where `Eq.refl` forces `b ≡ a`). Detect
            // this and fall through to the casesOn/rec path below.
            let single_var_is_nullary_ctor = matches!(&arm.pattern, SurfacePattern::Var(name)
                if self
                    .get_type_name(&scrutinee_ty)
                    .ok()
                    .and_then(|tn| self.resolve_ctor_name(name, &tn))
                    .is_some());
            match &arm.pattern {
                SurfacePattern::Var(name) if !single_var_is_nullary_ctor => {
                    // match e with | x => body  ==  let x := e in body
                    //
                    // With an annotated discriminant (`match h : e with | x =>
                    // body`, Lean matchDiscr) additionally bind the pattern-
                    // variable equation `h : e = x`. Since `x := e` is a
                    // zeta-transparent let, `Eq.refl e : e = e` proves it —
                    // the kernel re-checks the annotation `e = x` against the
                    // value's type `e = e` through the let binding.
                    return self.lower_single_catchall_match_arm(
                        discr_hyp,
                        Some(name),
                        &arm.body,
                        &scrutinee_ty,
                        &scrutinee_expr,
                    );
                }
                SurfacePattern::Inaccessible(inaccessible_expr) => {
                    if let Some(h) = discr_hyp {
                        return Err(ElabError::MatchDiscrHypUnsupported {
                            hyp: h.to_string(),
                            shape: "single inaccessible-pattern arm".to_string(),
                        });
                    }
                    let pattern_expr = self.elaborate_with_expected_type(
                        inaccessible_expr,
                        Some(scrutinee_ty.clone()),
                    )?;
                    if !self.is_def_eq(&pattern_expr, &scrutinee_expr) {
                        return Err(ElabError::TypeMismatch {
                            expected: format!(
                                "inaccessible pattern definitionally equal to {scrutinee_expr:?}"
                            ),
                            actual: format!("{pattern_expr:?}"),
                        });
                    }
                    let body_expr = self.elaborate_with_expected_type(
                        &arm.body,
                        self.current_expected_type.clone(),
                    )?;
                    let n = Name::from_string("_");
                    return Ok(Expr::let_named(
                        n,
                        scrutinee_ty,
                        scrutinee_expr,
                        body_expr,
                        true,
                    ));
                }
                SurfacePattern::Wildcard => {
                    if discr_hyp.is_some() {
                        // `match h : e with | _ => body` — Lean binds
                        // `h : e = x✝` for an inaccessible pattern variable;
                        // lower through the same let-encoding as the named
                        // catch-all (the binder name is cosmetic).
                        return self.lower_single_catchall_match_arm(
                            discr_hyp,
                            None,
                            &arm.body,
                            &scrutinee_ty,
                            &scrutinee_expr,
                        );
                    }
                    // match e with | _ => body  ==  let _ := e in body
                    let body_expr = self.elaborate_with_expected_type(
                        &arm.body,
                        self.current_expected_type.clone(),
                    )?;
                    let n = Name::from_string("_");
                    return Ok(Expr::let_named(
                        n,
                        scrutinee_ty,
                        scrutinee_expr,
                        body_expr,
                        true,
                    ));
                }
                _ => {}
            }
        }

        // For multiple arms or constructor patterns, build casesOn/rec
        let type_name = self.get_type_name(&scrutinee_ty)?;

        // Annotated discriminant: rewrite every arm body into a hypothesis
        // lambda `fun h => body`. The binder is deliberately UNANNOTATED — its
        // domain is pinned per-branch by the Eq-wrapped dependent motive set
        // below (`elab_lambda` takes an unannotated binder's domain from the
        // expected Pi), so each branch sees `h : e = <its own pattern
        // instance>` exactly as in Lean. Wrapping happens AFTER or-pattern
        // expansion, so `| p₁ | p₂ => body` gets a per-alternative equation.
        let hyp_wrapped_arms: Vec<clean_parser::SurfaceMatchArm>;
        let arms: &[clean_parser::SurfaceMatchArm] = match discr_hyp {
            Some(h) => {
                hyp_wrapped_arms = arms
                    .iter()
                    .map(|arm| clean_parser::SurfaceMatchArm {
                        span: arm.span,
                        pattern: arm.pattern.clone(),
                        body: SurfaceExpr::Lambda(
                            arm.span,
                            vec![SurfaceBinder::new(
                                h.to_string(),
                                None,
                                SurfaceBinderInfo::Explicit,
                            )],
                            Box::new(arm.body.clone()),
                        ),
                    })
                    .collect();
                &hyp_wrapped_arms
            }
            None => arms,
        };

        // Literal-pattern lowering (Track DD). Non-inductive literal types —
        // `String`, `Char`, and the numeric types (`Int`, `UInt*`, …) whose
        // literals are NOT constructors — cannot be dispatched by the casesOn/rec
        // path below. Lean 4 compiles `match s with | "a" => … | _ => …` (and the
        // numeric analogue) to a `BEq.beq`/`ite` guard cascade. We mirror that by
        // rewriting the match into a nested surface `if scrutinee == lit then body
        // else …` and elaborating it through the proven `elab_if` path (a `Bool`
        // `==` condition reduces via `Bool.rec`, no `Decidable` instance needed).
        // Pure surface desugaring: every produced term is elaborated and
        // kernel-checked by the existing machinery, so soundness is unchanged.
        // `Nat` is EXCLUDED — it is an inductive (`zero`/`succ`) handled by the
        // casesOn/`Nat.rec` path (incl. `n+k` patterns). `build_literal_match_cascade`
        // returns `None` (falls through) whenever the scrutinee is unavailable or
        // the arms are not a literal-pattern + trailing catch-all shape, so
        // genuine inductive matches are unaffected.
        if type_name != "Nat" && !arms.is_empty() {
            if let Some(h) = discr_hyp {
                // The BEq/ite cascade lowering has no per-branch equation to
                // offer — refuse loud rather than bind `h` to the wrong thing.
                return Err(ElabError::MatchDiscrHypUnsupported {
                    hyp: h.to_string(),
                    shape: format!("literal-pattern match on `{type_name}`"),
                });
            }
            if let Some(scrutinee_surface) = scrutinee_surface {
                if let Some(cascade) = Self::build_literal_match_cascade(scrutinee_surface, arms) {
                    return self.elaborate_with_expected_type(
                        &cascade,
                        self.current_expected_type.clone(),
                    );
                }
            }
        }

        // Check if this match is on the decreasing argument of a recursive def (#381)
        // If so, use T.rec instead of T.casesOn to get the inductive hypothesis
        let use_rec =
            scrutinee_surface.is_some_and(|scrutinee| self.is_match_on_decreasing_arg(scrutinee));
        if use_rec {
            if let Some(h) = discr_hyp {
                // `T.rec` folds induction hypotheses and extra params into the
                // motive through a separate mechanism; combining that with the
                // equation-wrapped motive is descoped — fail loud.
                return Err(ElabError::MatchDiscrHypUnsupported {
                    hyp: h.to_string(),
                    shape: "match on the decreasing argument of a recursive definition".to_string(),
                });
            }
        }

        // Dependent-motive detection. When the match runs under an expected type
        // that *depends on the scrutinee* — e.g. `def f (b : T) : Choose b :=
        // match b with …` where `Choose b` reduces differently per constructor —
        // the motive is NOT the constant `fun _ : T => R`. It must be the
        // dependent `fun (x : T) => R[scrutinee := x]`, so the kernel accepts each
        // minor premise `mᵢ : R[scrutinee := ctorᵢ]` (which differ per branch).
        //
        // We detect this when the scrutinee elaborated to a bare local `FVar` that
        // genuinely occurs in the (instantiated) expected type. Abstracting that
        // fvar yields the motive body `R[scrutinee := BVar(0)]`; if abstraction
        // leaves the type unchanged the expected type is constant in the scrutinee
        // and we keep the existing constant-motive path (byte-for-byte unchanged).
        //
        // Restricted to `casesOn` (not `use_rec`): recursive defs fold extra
        // params into the motive via a separate mechanism, and combining a
        // value-dependent motive with induction hypotheses is a distinct case.
        let saved_dependent_motive = self.match_dependent_motive.take();
        let saved_dependent_motive_indices =
            std::mem::replace(&mut self.match_dependent_motive_indices, 0);
        let saved_index_discriminating_punit = self.match_index_discriminating_punit.take();
        if !use_rec {
            if let ExprKind::FVar(scrutinee_fvar) = scrutinee_expr.kind() {
                if let Some(expected) = self.current_expected_type.clone() {
                    let expected = self
                        .metas
                        .instantiate_levels(&self.metas.instantiate(&expected));
                    let motive_body = expected.abstract_fvar(*scrutinee_fvar);
                    if motive_body != expected {
                        self.match_dependent_motive = Some(motive_body);
                    }
                }
            }
        }

        // Lower the rest of the match with the (possibly dependent) motive in
        // scope, restoring the saved motive on every exit so nested/sibling
        // matches never observe a stale motive.
        let lowered = (|| {
            // Collect extra param info for varying-parameter support (#1386).
            // When the recursive function has params after the decreasing arg (e.g.,
            // `lift_at (e : KExpr) (cutoff : Nat) (amount : Nat)`), we fold them into
            // the motive so IHs can express results with different param values.
            let extra_param_info: Vec<ExtraParamBinding> = if use_rec {
                if let Some(ref ctx) = self.recursive_def_ctx {
                    ctx.extra_params
                        .iter()
                        .filter_map(|param| {
                            self.lookup_local(&param.name)
                                .map(|(fvar, ty)| (fvar, param.binder_info, ty.clone()))
                        })
                        .collect()
                } else {
                    vec![]
                }
            } else {
                vec![]
            };

            let eliminator_name = if use_rec {
                Name::from_string(&format!("{type_name}.rec"))
            } else {
                Name::from_string(&format!("{type_name}.casesOn"))
            };
            // Annotated discriminant: resolve the ground expected type C up
            // front — the equation-wrapped motive and the shared branch type
            // both derive from it. The first-arm fallback is unusable here
            // (arm bodies now reference `h`, which only the motive binds), so
            // an unknown or metavariable-carrying expected type fails loud.
            let hyp_expected: Option<Expr> = match discr_hyp {
                Some(h) => {
                    let expected = self.current_expected_type.clone().and_then(|expected| {
                        let expected = self
                            .metas
                            .instantiate_levels(&self.metas.instantiate(&expected));
                        if self.has_metavars(&expected) {
                            None
                        } else {
                            Some(expected)
                        }
                    });
                    match expected {
                        Some(expected) => Some(expected),
                        None => {
                            return Err(ElabError::MatchDiscrHypUnsupported {
                                hyp: h.to_string(),
                                shape: "requires a known (metavariable-free) expected type; \
                                        annotate the surrounding definition's return type"
                                    .to_string(),
                            })
                        }
                    }
                }
                None => None,
            };
            // Branch (result) type for the constant motive `fun _ : T => branch_ty`.
            //
            // Normally inferred from the first arm's body type. But when the match
            // runs under a known, scrutinee-independent expected type (e.g. a
            // `def f … : Prop := match …`), prefer that expected type: it lets each
            // arm body be elaborated *against* it, so a sort coercion (Bool → Prop
            // via `instCoeSortBoolProp`, or Prop → Bool via `decide`) is inserted
            // per-arm instead of the motive being pinned to the first arm's raw
            // type and later arms rejected. We only do this in the non-dependent
            // constant-motive case (`match_dependent_motive` unset) and only when
            // the expected type is ground (no unassigned metavars), so inference-
            // driven matches keep their existing first-arm behavior unchanged.
            let branch_ty = {
                // With an annotated discriminant the ground expected type is
                // mandatory (resolved above) and IS the branch result type C,
                // even when the motive is scrutinee-dependent.
                let scrutinee_is_indexed = self
                    .env
                    .get_inductive(&Name::from_string(&type_name))
                    .is_some_and(|ind| ind.num_indices > 0);
                let from_expected = if let Some(c) = &hyp_expected {
                    Some(c.clone())
                } else if self.match_dependent_motive.is_none() {
                    self.current_expected_type.clone().and_then(|expected| {
                        let expected = self
                            .metas
                            .instantiate_levels(&self.metas.instantiate(&expected));
                        if self.has_metavars(&expected) {
                            None
                        } else {
                            Some(expected)
                        }
                    })
                } else if !scrutinee_is_indexed {
                    // Non-indexed dependent motive (proof-by-match, value-dependent
                    // return). The raw expected type is the motive applied at the
                    // scrutinee, so it shares the SAME sort as every per-arm
                    // specialization — a valid `branch_ty` for eliminator-level
                    // computation (#B09). Crucially we must NOT re-derive it by
                    // elaborating arm 0's body against the *unspecialized* expected
                    // type: a proof body such as `Or.inl rfl` propagates that wrong
                    // type inward (`rfl` forced to `n = 0`, not `0 = 0`) and fails.
                    // Each arm re-derives its own `arm_branch_ty` from the motive.
                    // Indexed families never take this branch — the scrutinee-value
                    // dependent-motive detection only fires on value dependence;
                    // index-dependent returns install their motive later, after
                    // `branch_ty` is fixed.
                    self.current_expected_type.clone().map(|expected| {
                        self.metas
                            .instantiate_levels(&self.metas.instantiate(&expected))
                    })
                } else {
                    None
                };
                match from_expected {
                    Some(expected) => expected,
                    None => self.infer_first_arm_branch_ty(&arms[0], &scrutinee_ty, &type_name)?,
                }
            };
            let branch_ty = self.stabilize_open_constant_match_motive(
                arms,
                &scrutinee_ty,
                &type_name,
                branch_ty,
            )?;
            // Create eliminator with motive + inductive universe levels (#422).
            let elim_levels =
                self.eliminator_levels(&eliminator_name, &scrutinee_ty, &branch_ty)?;

            // Index count and scrutinee decomposition for indexed inductives (#796).
            // Return a proper error if the inductive is not registered (#422 safety).
            let ind_info = self
                .env
                .get_inductive(&Name::from_string(&type_name))
                .cloned()
                .ok_or_else(|| {
                    ElabError::NotImplemented(format!(
                        "match: type `{type_name}` is not a registered inductive type"
                    ))
                })?;

            // Effective param/index split for the *eliminator we are applying*.
            //
            // For most inductives this equals the inductive's own
            // `num_params`/`num_indices`. But some eliminators *promote* a
            // leading index into a recursor parameter — Lean's `Eq` is the
            // canonical case: the inductive `Eq : {α} → α → α → Prop` has
            // `num_params=1, num_indices=2`, yet `Eq.casesOn`/`Eq.rec` are
            // registered with `num_params=2, num_indices=1` (the first index
            // `a` is fixed/promoted, leaving a single varying index `b` plus
            // the proof as the major premise). When a *native* recursor is
            // registered (`get_recursor` is `Some`), its `num_params`/
            // `num_indices` is the authoritative arity contract for the
            // application we build, so we use it. Imported `.casesOn`
            // (recursor absent) keeps the inductive's split, byte-for-byte.
            let (elim_num_params, elim_num_indices) = match self.env.get_recursor(&eliminator_name)
            {
                Some(rec) => (rec.num_params as usize, rec.num_indices as usize),
                None => (ind_info.num_params as usize, ind_info.num_indices as usize),
            };
            let num_indices = elim_num_indices;
            let num_params = elim_num_params;
            if let Some(h) = discr_hyp {
                if num_indices > 0 {
                    // Indexed families need index-generalized motives; wiring
                    // the equation binder through that path is descoped — loud.
                    return Err(ElabError::MatchDiscrHypUnsupported {
                        hyp: h.to_string(),
                        shape: format!("match on the indexed inductive family `{type_name}`"),
                    });
                }
            }

            let eliminator = self.apply_eliminator_params_count(
                Expr::const_(eliminator_name.clone(), elim_levels),
                &scrutinee_ty,
                elim_num_params as u32,
            )?;
            // Extract index arguments and scrutinee type decomposition for indexed inductives.
            let (index_args, scrutinee_decomp): (Vec<Expr>, Option<(Expr, Vec<Expr>)>) =
                if num_indices > 0 {
                    let scrutinee_whnf = self.whnf(&scrutinee_ty);
                    let mut all_args = Vec::new();
                    let mut head = &scrutinee_whnf;
                    while let ExprKind::App(func, arg) = head.kind() {
                        all_args.push(arg.as_ref().clone());
                        head = func;
                    }
                    all_args.reverse();
                    let head = head.clone();
                    let idx = if all_args.len() > num_params {
                        all_args[num_params..].to_vec()
                    } else {
                        vec![]
                    };
                    (idx, Some((head, all_args)))
                } else {
                    (vec![], None)
                };

            // Annotated discriminant (`match h : e with`): wrap the motive
            // body with the equation binder —
            //   `fun (x : T) => (h : e = x) → C`
            // (`C` abstracted over the scrutinee when it already was). Under
            // the motive's `x` binder the equation domain refers to `x` as
            // `BVar(0)`; crossing the new Pi binder lifts `C`'s loose bvars by
            // one (same shape as `elab_subst::mk_subst_motive`). Each casesOn
            // minor for `ctorᵢ fields…` then has expected type
            // `e = ctorᵢ fields… → C` — the per-branch pattern-instance
            // equation — and `hyp_refl` (`@Eq.refl T e`) discharges the
            // wrapper at the end. Note `Pi (h : Eq …) C : sort C` (the domain
            // is a `Prop`, so `imax` collapses), so `eliminator_levels`
            // computed from the unwrapped `branch_ty` stays correct.
            let mut hyp_refl: Option<Expr> = None;
            if let (Some(_), Some(c)) = (discr_hyp, &hyp_expected) {
                let base = match self.match_dependent_motive.take() {
                    Some(dep_body) => dep_body,
                    None => c.clone(),
                };
                let u = self.infer_sort(&scrutinee_ty)?;
                let eq_ty = Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![u.clone()]),
                    [scrutinee_ty.clone(), scrutinee_expr.clone(), Expr::bvar(0)],
                );
                let dep_body = Expr::pi(BinderInfo::Default, eq_ty, lift_bvars(&base, 1));
                self.match_dependent_motive = Some(dep_body);
                hyp_refl = Some(Expr::apps(
                    Expr::const_(Name::from_string("Eq.refl"), vec![u]),
                    [scrutinee_ty.clone(), scrutinee_expr.clone()],
                ));
            }

            // Build motive: (fun _ : T => ResultType)
            // When extra params exist (#1386), generalize to:
            //   (fun _ : T => P1_ty → P2_ty → ... → ResultType)
            // so IHs become functions that take the extra params.
            //
            // For indexed inductives (#796), the motive takes index parameters
            // before the major premise:
            //   (fun (idx₀ : I₀) ... (idxₙ : Iₙ) (x : T idx₀ ... idxₙ) => R)
            let motive = if num_indices > 0 && index_args.len() == num_indices {
                // Dependent-return over the index: when the match's expected type
                // varies with the index (e.g. `match v : IVec n with … : IVec n`),
                // the motive body must be `R[indices := idx][scrutinee := major]`,
                // generalized over BOTH the index and the scrutinee — not the
                // constant first-arm `branch_ty`. We detect this only when the
                // scrutinee is a bare `FVar` and every index is a distinct `FVar`
                // (the variable-index dependent-elimination case); otherwise we
                // fall back to the constant motive, byte-for-byte unchanged.
                //
                // `match_dependent_motive` (+ `_indices`) is set so each arm
                // recovers its own `motive idx(ctorᵢ)… (ctorᵢ fields…)` expected
                // type in `arm_branch_ty`. `extra_param_info` is empty here (only
                // populated for `use_rec`, which never sets a dependent motive).
                let indexed_dep_body = if !use_rec {
                    self.current_expected_type.clone().and_then(|expected| {
                        self.build_indexed_dependent_motive_body(
                            &expected,
                            &index_args,
                            &scrutinee_expr,
                        )
                    })
                } else {
                    None
                };
                if let Some(ref dep_body) = indexed_dep_body {
                    self.match_dependent_motive = Some(dep_body.clone());
                    self.match_dependent_motive_indices = num_indices;
                }
                // Index-discriminating motive (GADT omitted-impossible branch):
                // when the match is NOT index-dependent (the expected type does
                // not vary with the index — e.g. `Vec.head : Vec α (succ n) → α`)
                // but it legitimately omits an index-impossible constructor, the
                // constant `fun (idx)(major) => branch_ty` motive would force the
                // omitted branch's minor to inhabit `branch_ty` (impossible when
                // `branch_ty` is a bare `α`). Instead build a motive that returns
                // `branch_ty` at the scrutinee's index head and `PUnit.{u}` at
                // every other head, so the omitted minor is `PUnit.unit.{u}` — a
                // sound, sorry-free discharge. This also handles *non-variable*
                // indices (`succ k`) for free, since the discriminator reduces on
                // the index value structurally.
                //
                // Engage ONLY when the constant-motive path genuinely cannot fill
                // the omitted minor — i.e. `branch_ty` has no closed inhabitant
                // (`try_default_value_of_type` is `None`, as for a bare type
                // variable `α`). When a default exists (e.g. `branch_ty = Nat`,
                // the GExpr GADT case) the existing constant-motive + default-value
                // discharge stays byte-for-byte unchanged, so envs without `PUnit`
                // are unaffected.
                let needs_discriminator = !use_rec
                    && indexed_dep_body.is_none()
                    && num_indices == 1
                    && self
                        .env
                        .get_inductive(&Name::from_string("PUnit"))
                        .is_some()
                    && self.try_default_value_of_type(&branch_ty)?.is_none()
                    && self.match_omits_index_impossible_ctor(arms, &type_name, &scrutinee_ty);
                let discriminating_body = if needs_discriminator {
                    self.build_index_discriminating_motive_body(
                        &scrutinee_ty,
                        &type_name,
                        &branch_ty,
                    )?
                } else {
                    None
                };
                if let Some((_, ref u)) = discriminating_body {
                    self.match_index_discriminating_punit = Some(u.clone());
                }
                let motive_body = match (indexed_dep_body, discriminating_body) {
                    (Some(dep_body), _) => dep_body,
                    (None, Some((disc_body, _))) => disc_body,
                    (None, None) => {
                        generalize_with_extra_params(branch_ty.clone(), &extra_param_info)
                    }
                };

                // Build the major-premise domain type with BVars for indices.
                // At depth num_indices (inside all index lambdas), BVar(i) for i in
                // 0..num_indices references the (num_indices-1-i)-th index lambda.
                let (head_expr, all_args) = scrutinee_decomp.as_ref().ok_or_else(|| {
                    ElabError::InternalInvariant(
                        "indexed match motive lost its scrutinee type decomposition".into(),
                    )
                })?;
                let mut motive_major_ty = head_expr.clone();
                for param in &all_args[..num_params] {
                    motive_major_ty = Expr::app(motive_major_ty, param.clone());
                }
                // Replace index args with BVars
                for i in 0..num_indices {
                    let bvar_idx = (num_indices - 1 - i) as u32;
                    motive_major_ty = Expr::app(motive_major_ty, Expr::bvar(bvar_idx));
                }

                let mut m = Expr::lam(BinderInfo::Default, motive_major_ty, motive_body);
                // Outer lambdas for each index, from innermost to outermost
                for idx_arg in index_args.iter().rev() {
                    let idx_ty = self.infer_type(idx_arg)?;
                    m = Expr::lam(BinderInfo::Default, idx_ty, m);
                }

                m
            } else if let Some(dep_body) = self.match_dependent_motive.clone() {
                // Dependent motive: `fun (x : T) => R[scrutinee := x]`. `dep_body`
                // already has the scrutinee fvar abstracted to `BVar(0)`, so it slots
                // directly under the binder. `extra_param_info` is empty here (only
                // populated for `use_rec`, which never sets a dependent motive).
                Expr::lam(BinderInfo::Default, scrutinee_ty.clone(), dep_body)
            } else {
                let motive_body =
                    generalize_with_extra_params(branch_ty.clone(), &extra_param_info);
                Expr::lam(BinderInfo::Default, scrutinee_ty.clone(), motive_body)
            };

            // Build: eliminator motive (casesOn or rec)
            // Lean-faithful casesOn order: motive, (indices,) major, then minors.
            // `T.casesOn` uses the `MajorAfterMotive` layout
            //   motive(s) → indices → major → minors
            // both natively (the kernel now generates it with
            // `RecursorArgOrder::MajorAfterMotive`) and when imported from `.olean`
            // (a definitional constant unfolding to `T.rec motive minors… major`).
            // `T.rec` keeps the recursor layout `MajorAfterMinors`:
            //   motive(s) → minors → indices → major (#386, #796).
            // The scrutinee must sit in the slot the eliminator's type actually
            // expects, or `whnf` selects the wrong branch (#bug: match misorders
            // casesOn minors).
            //
            // Discriminator: a registered recursor's declared `arg_order` is
            // authoritative (so a recursor still declaring `MajorAfterMinors` keeps
            // the major-last path); an *imported* `.casesOn` is registered only as a
            // plain constant, in which case it follows Lean's `MajorAfterMotive`
            // convention. Primitive `.rec` packets normally declare
            // `MajorAfterMinors`; if an authenticated packet declares otherwise,
            // its metadata remains authoritative here too.
            let eliminator_metadata =
                self.match_eliminator_metadata(&type_name, &eliminator_name, !use_rec)?;
            let major_after_motive = eliminator_metadata.major_after_motive;

            // For nested inductives (#3396), the eliminator is a mutual recursor with
            // motives and minors for auxiliary types (e.g., Value._List). We must supply
            // extra motives and minors for these auxiliary types, even though the user's
            // match only targets the primary type.  The authenticated recursor count is
            // essential here: restore erases helper types from `all_names`, while the
            // eliminator still carries their motive slots.
            let num_motives = eliminator_metadata.recursor.num_motives as usize;
            if num_motives == 0 {
                return Err(ElabError::InternalInvariant(format!(
                    "match eliminator `{eliminator_name}` declares no motives"
                )));
            }
            let selected_motive_idx =
                self.selected_motive_index(&ind_info, num_motives, "plain mutual-inductive match")?;

            // Supply every remaining motive from the eliminator's authoritative
            // telescope.  Nested-inductive restore intentionally erases helper
            // constants such as `Value._List`; the corresponding motive domain
            // is restored to the real container type (`List Value`) inside the
            // recursor signature.  Reading that signature handles both restored
            // nested blocks and ordinary mutual inductives without fabricating
            // names or depending on `InductiveVal::all_names` retaining erased
            // implementation details.
            let motive_body = generalize_with_extra_params(branch_ty.clone(), &extra_param_info);
            // A primary major can never select an auxiliary member's motive or
            // minors. Give those unreachable slots their own genuinely
            // inhabited result type when canonical PUnit is available. This is
            // stronger than requiring `motive_body` itself to have a closed
            // value and avoids manufacturing proof evidence for dead slots.
            // Recursive nested folds have a separate telescope-driven builder
            // that constructs every auxiliary minor against branch-typed
            // motives (including real IHs). Keep those motives aligned; this
            // PUnit substitution is for the casesOn/dead-aux path repaired here.
            let aux_punit = if num_motives > 1 && !use_rec {
                self.punit_dummy_at_result_sort(&motive_body)?
            } else {
                None
            };
            let aux_motive_body = aux_punit
                .as_ref()
                .map(|(punit, _)| punit.clone())
                .unwrap_or_else(|| motive_body.clone());
            let aux_punit_unit = aux_punit.map(|(_, unit)| unit);
            let mut result = eliminator;
            for motive_idx in 0..num_motives {
                if motive_idx == selected_motive_idx {
                    result = Expr::app(result, motive.clone());
                } else {
                    let result_ty = self.infer_type(&result)?;
                    let result_ty = self.whnf(&result_ty);
                    let ExprKind::Pi(_, expected_motive, _) = result_ty.kind() else {
                        return Err(ElabError::TypeMismatch {
                            expected: format!("mutual-inductive motive slot {motive_idx}"),
                            actual: format!("{result_ty:?}"),
                        });
                    };
                    let aux_motive =
                        self.constant_over_telescope(expected_motive, aux_motive_body.clone());
                    result = Expr::app(result, aux_motive);
                }
            }

            // For the `MajorAfterMotive` layout (casesOn, native and imported), the
            // indices and the major premise (scrutinee) precede the minor premises:
            // motive(s) → indices → major → minors. Emit them here, before the minor
            // alternatives below.
            if major_after_motive {
                for idx_arg in &index_args {
                    result = Expr::app(result, idx_arg.clone());
                }
                result = Expr::app(result, scrutinee_expr.clone());
            }

            // Add case alternatives (minor premises)
            // For now, we handle arms in order, treating each as a constructor case
            // When using rec, we also need to add IH lambdas for recursive fields
            //
            // Set expected type for arm body elaboration (#469)
            // This allows nested recursor calls (e.g., Nat.rec inside MicroExpr match)
            // to properly unify their result types with the expected branch type.
            let saved_expected = self.current_expected_type.clone();
            self.set_expected_type(Some(branch_ty.clone()));

            // Set by the `use_rec` telescope path when it has already emitted a
            // minor for every constructor in a nested mutual block, so the
            // separate aux-minor supply below is not run a second time.
            let mut nested_minors_already_supplied = false;
            let mut primary_alts: Vec<Expr> = Vec::new();
            let mut applied_primary_minor_names: Vec<Option<Name>> = Vec::new();

            if !use_rec {
                if let Some(ordered_alts) = self.try_build_ctor_ordered_match_alts(
                    arms,
                    &type_name,
                    &scrutinee_ty,
                    &branch_ty,
                    &extra_param_info,
                )? {
                    for (index, alt) in ordered_alts.into_iter().enumerate() {
                        primary_alts.push(alt);
                        applied_primary_minor_names
                            .push(ind_info.constructor_names.get(index).cloned());
                    }
                } else {
                    for (arm_idx, arm) in arms.iter().enumerate() {
                        let alt = self.elaborate_match_arm(
                            arm,
                            arm_idx,
                            &type_name,
                            &scrutinee_ty,
                            &branch_ty,
                            &extra_param_info,
                            use_rec,
                        )?;
                        primary_alts.push(alt);
                        applied_primary_minor_names.push(
                            self.top_level_ctor_target_name(&type_name, &arm.pattern)
                                .map(|name| Name::from_string(&name)),
                        );
                    }
                }
            } else {
                // Recursor (`T.rec`) minor premises must appear in constructor
                // *declaration* order and cover every constructor — but the
                // surface arms may be reordered and/or end in a wildcard
                // catch-all (TrustIr `Ty.bitWidth`, Track R). Build them in
                // declaration order with wildcard expansion and IH binders;
                // fall back to the legacy source-order loop for arm shapes the
                // ordered builder declines to handle.
                if let Some(ordered_alts) = self.try_build_ctor_ordered_rec_alts(
                    arms,
                    &type_name,
                    &scrutinee_ty,
                    &branch_ty,
                    &extra_param_info,
                )? {
                    // For a nested inductive the ordered builder runs the
                    // telescope path, which already emits minors for EVERY
                    // constructor in the mutual block (primary + auxiliary).
                    // Suppress the separate aux-minor supply below so they are
                    // not double-applied.
                    if num_motives > 1 {
                        nested_minors_already_supplied = true;
                    }
                    for alt in ordered_alts {
                        result = Expr::app(result, alt);
                    }
                } else {
                    for (arm_idx, arm) in arms.iter().enumerate() {
                        let alt = self.elaborate_match_arm(
                            arm,
                            arm_idx,
                            &type_name,
                            &scrutinee_ty,
                            &branch_ty,
                            &extra_param_info,
                            use_rec,
                        )?;
                        primary_alts.push(alt);
                        applied_primary_minor_names.push(
                            self.top_level_ctor_target_name(&type_name, &arm.pattern)
                                .map(|name| Name::from_string(&name)),
                        );
                    }
                }
            }

            // Supply minor premises for auxiliary types' constructors (#3396, #3420).
            // For nested inductives, the eliminator expects minors for ALL constructors
            // in the mutual block, not just the primary type's constructors. Since the
            // scrutinee has the primary type, aux minors are dead code — but they
            // still require genuine, kernel-checkable inhabitants. Prefer the
            // PUnit dummy selected with the aux motives above. In environments
            // without canonical PUnit, retain the branch-typed aux motive and
            // require a real wildcard body or nullary constructor; otherwise fail.
            // Skipped when the telescope path already supplied every minor.
            if num_motives > 1 && !nested_minors_already_supplied {
                let minor_rules =
                    self.recursor_minor_rules(&ind_info, &eliminator_metadata.recursor)?;
                let primary_range = self.validate_primary_minor_boundary(
                    &ind_info,
                    &minor_rules,
                    &applied_primary_minor_names,
                    "plain multi-motive match",
                )?;
                if primary_alts.len() != primary_range.len() {
                    return Err(ElabError::InternalInvariant(format!(
                        "plain multi-motive match compiled {} primary alternatives for authenticated range {primary_range:?}",
                        primary_alts.len()
                    )));
                }

                let default_branch_value: Option<Expr> = if aux_punit_unit.is_none() {
                    // Wildcard/variable arms act as catch-all for aux ctors. A
                    // real catch-all body that fails to elaborate is an error,
                    // not permission to silently substitute a different default.
                    let wildcard_body = arms
                        .iter()
                        .rev()
                        .find(|arm| {
                            matches!(
                                &arm.pattern,
                                SurfacePattern::Wildcard | SurfacePattern::Var(_)
                            )
                        })
                        .map(|arm| {
                            self.elaborate_with_expected_type(&arm.body, Some(branch_ty.clone()))
                        })
                        .transpose()?;
                    match wildcard_body {
                        some @ Some(_) => some,
                        None => self.try_default_value_of_type(&branch_ty)?,
                    }
                } else {
                    None
                };

                // Emit the complete global minor order. Sibling/restored-helper
                // rules may precede or follow the selected member's authenticated
                // slice; only that slice consumes the compiled source arms.
                for (rule_idx, rule) in minor_rules.iter().enumerate() {
                    if primary_range.contains(&rule_idx) {
                        let alt = primary_alts[rule_idx - primary_range.start].clone();
                        result = Expr::app(result, alt);
                        continue;
                    }
                    let minor_body = if let Some(ref unit) = aux_punit_unit {
                        unit.clone()
                    } else if let Some(ref db) = default_branch_value {
                        wrap_with_extra_params(db.clone(), &extra_param_info)
                    } else {
                        return Err(ElabError::NotImplemented(format!(
                            "cannot construct a sound auxiliary minor for `{}` while matching \
                             `{type_name}`; add a wildcard arm or use an inhabited result type",
                            rule.constructor_name
                        )));
                    };
                    let result_ty = self.infer_type(&result)?;
                    let result_ty = self.whnf(&result_ty);
                    let ExprKind::Pi(_, expected_minor, _) = result_ty.kind() else {
                        return Err(ElabError::TypeMismatch {
                            expected: format!("minor premise for {}", rule.constructor_name),
                            actual: format!("{result_ty:?}"),
                        });
                    };
                    let binder_count = rule.num_fields as usize
                        + if use_rec {
                            rule.recursive_fields.iter().filter(|&&r| r).count()
                        } else {
                            0
                        };
                    let Some(alt) = self.constant_over_telescope_prefix(
                        expected_minor,
                        binder_count,
                        minor_body,
                    ) else {
                        return Err(ElabError::TypeMismatch {
                            expected: format!(
                                "{} binders for {} minor",
                                binder_count, rule.constructor_name
                            ),
                            actual: format!("{expected_minor:?}"),
                        });
                    };
                    result = Expr::app(result, alt);
                }
            } else if !nested_minors_already_supplied {
                for alt in primary_alts {
                    result = Expr::app(result, alt);
                }
            }

            self.set_expected_type(saved_expected);
            // For the `MajorAfterMinors` layout (`.rec`, or any recursor still
            // declaring it), the indices and major premise come AFTER the minors
            // (#796): motive → minors → indices → major. For the `MajorAfterMotive`
            // layout (casesOn) they were already emitted before the minors above, so
            // skip them here.
            if !major_after_motive {
                for idx_arg in &index_args {
                    result = Expr::app(result, idx_arg.clone());
                }
                result = Expr::app(result, scrutinee_expr);
            }
            // Apply extra params to recover final ResultType (#1386).
            for (fvar, _, _) in &extra_param_info {
                result = Expr::app(result, Expr::fvar(*fvar));
            }

            // Annotated discriminant: discharge the equation binder at the
            // scrutinee itself — `motive e ≡ (e = e) → C`, applied to
            // `@Eq.refl T e` to recover `C`.
            if let Some(refl) = hyp_refl {
                result = Expr::app(result, refl);
            }

            Ok(result)
        })();
        self.match_dependent_motive = saved_dependent_motive;
        self.match_dependent_motive_indices = saved_dependent_motive_indices;
        self.match_index_discriminating_punit = saved_index_discriminating_punit;
        lowered
    }
}
