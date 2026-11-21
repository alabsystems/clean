// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core elaboration helpers for identifiers, universes, and binder forms.

use super::let_rec_lift::{helper_own_params, helper_site_span, HelperRecursion, HelperSite};
use super::*;
use crate::agent_diagnostics::nearest_string_candidates;
use crate::namespace::TemplateGlobal;
use crate::stack_safe;
use clean_kernel::sorry::{create_sorry_term_with_kind_at_level, SorryKind};
use clean_kernel::ConstantKind;

#[derive(Clone, Copy)]
enum TermLocalKind {
    Let,
    Have,
}

/// Bare prelude exports and the qualified constants they alias (see
/// `resolve_ident_target`).
const PRELUDE_ALIASES: &[(&str, &str)] = &[
    // Monad typeclass methods (#3435).
    ("pure", "Pure.pure"),
    ("bind", "Bind.bind"),
    ("map", "Functor.map"),
    ("seq", "Seq.seq"),
    ("seqLeft", "SeqLeft.seqLeft"),
    ("seqRight", "SeqRight.seqRight"),
    // MonadExcept methods, exported by `Init/Prelude.lean` via
    // `export MonadExcept (throw tryCatch)`. Without this, a bare
    // `throw e` falls through to auto-implicit and is bound as a fresh
    // free variable typed `Sort u` — the elaborator then applies the
    // error argument to a non-function `Sort(u_0)` ("Too many
    // arguments: function type Sort(...)"). Aliasing to the registered
    // `MonadExcept.throw` axiom resolves it to the real polymorphic op.
    ("throw", "MonadExcept.throw"),
    ("tryCatch", "MonadExcept.tryCatch"),
    // Indexing and collection-literal heads, exported by Lean via
    // `export GetElem (getElem)` / `export GetElem? (getElem? getElem!)`
    // (Init/GetElem.lean:79/112) and `export Insert (insert)` /
    // `export Singleton (singleton)` (Init/Core.lean:593/602). The
    // parser emits these bare names for `xs[i]`-family subscripts and
    // `{a, b, c}` collection literals (Brick P1); like the entries
    // above, the alias fires only when the target constant is
    // registered, so it is a no-op in environments without the classes.
    ("getElem", "GetElem.getElem"),
    ("getElem?", "GetElem?.getElem?"),
    ("getElem!", "GetElem?.getElem!"),
    ("insert", "Insert.insert"),
    ("singleton", "Singleton.singleton"),
    // Inductive-type constructors exported by `Init/Prelude.lean`
    // (#3527). Matching Lean 4's `export Option (some none)` etc.
    ("some", "Option.some"),
    ("none", "Option.none"),
    ("inl", "Sum.inl"),
    ("inr", "Sum.inr"),
    // `export Bool (false true)` (Init/Prelude.lean). Clean's native
    // prelude ships root-level reducible `true`/`false` defs, so this
    // alias only fires in environments without them — e.g. a real-Lean
    // `.olean` import, where a bare `false` otherwise fell through to
    // auto-implicit and silently GENERALIZED the statement over an
    // arbitrary Bool (`(r == 0) = false` became `∀ b, (r == 0) = b`,
    // fail-closed but wrong — trust-ir bridge division-guard
    // statements).
    ("true", "Bool.true"),
    ("false", "Bool.false"),
];

/// Lean 4.8.0 core constants that Clean's prelude does not declare but whose
/// applied forms an elaborator recognizer supplies (`infer/mod.rs`). For
/// dotted-identifier resolution they count as existing globals, as they do in
/// Lean: `And.elim` with a `where`-bound `And` in scope names this global
/// ([`ElabCtx::resolve_dotted_ident`]).
const RECOGNIZER_SUPPLIED_CORE_GLOBALS: &[&str] = &["And.elim", "Iff.elim", "Or.elim", "Not.elim"];

/// Heads a recognizer supplies that Lean 4.8.0 core LACKS (measured: `#check
/// @Function.uncurry` is `unknown identifier`; `Sum.elim` is field notation
/// on the type `Sum`). They are Clean extensions: a recognizer may supply one
/// only where the written name denotes NOTHING else — no local, no value its
/// first component could be a field of, and no user constant of that name.
const CLEAN_EXTENSION_HEADS: &[&str] = &["Function.curry", "Function.uncurry", "Sum.elim"];

/// What a written dotted identifier `base.field` denotes, by Lean's rules
/// (see [`ElabCtx::resolve_dotted_ident`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DottedIdent {
    /// The whole identifier names this global constant.
    Global(Name),
    /// A projection (field access or dot-call) on the innermost local
    /// `base`, or on the global `base` names (or on nothing: unknown).
    Field,
    /// A projection on an ORDINARY local `base` that an innermost
    /// `where`/`let rec` auxiliary declaration of the same spelling shadows
    /// for plain references (Lean skips the auxiliary declaration here
    /// because a global `base.field` exists). Clean's projection path would
    /// read the auxiliary declaration, so this shape is refused.
    FieldOfShadowedLocal(FVarId),
    /// A projection chain on the GLOBAL `receiver`: Lean skipped a
    /// `where`/`let rec` auxiliary declaration of the leading spelling (a
    /// global of some spelling exists) and no ordinary local of it is in
    /// scope, so the longest prefix naming a global is the receiver and
    /// `fields` (in order) are projected from it.
    FieldOfGlobal {
        receiver: Name,
        fields: Vec<SurfaceName>,
    },
    /// The whole spelling is this Lean core constant, which Clean's prelude
    /// neither declares nor supplies: refused, never read as something else.
    CoreUnavailable(Name),
    /// As [`Self::FieldOfGlobal`], but the receiver Lean would take is a
    /// global Clean supplies only as a builtin (not a constant it can
    /// reference here): refused rather than read from the auxiliary
    /// declaration.
    UnsupportedGlobalReceiver,
}

/// What a dotted spelling names as a global ([`ElabCtx::dotted_global`]).
#[derive(Debug, Clone, PartialEq, Eq)]
enum DottedGlobal {
    /// This global constant.
    Found(Name),
    /// A Lean core constant Clean's prelude lacks.
    CoreUnavailable(Name),
}

/// What an identifier denotes (see [`ElabCtx::resolve_ident_target`]).
#[derive(Debug, Clone)]
pub(crate) enum IdentTarget {
    /// A leading-dot constructor selector, resolved against the expected type.
    RelativeConstructor,
    /// A metaprogram value binding (an already-elaborated term).
    MetaValue(Expr),
    /// A local binder: parameter, `let`, `fun`, pattern variable, ….
    Local(FVarId),
    /// A global constant, inductive, constructor, recursor or alias target.
    Global(Name),
    /// `_root_.x` naming no global.
    RootEscapeUnknown,
    /// The bare prelude combinator `id` (absent from Clean's prelude).
    BuiltinId,
    /// The bare prelude combinator `cond` (absent from Clean's prelude).
    BuiltinCond,
    /// A bare root export Clean registers under its qualified name
    /// (`not` IS `Bool.not`).
    Redirect(&'static str),
    /// Nothing: auto-bound implicit in a header, otherwise unknown.
    Unresolved,
    /// More than one distinct root-stage candidate: Lean's "ambiguous,
    /// possible interpretations". Clean elaborates no overloads, so this is
    /// refused, never resolved to one of them.
    Ambiguous(Vec<Name>),
}

impl<'a> ElabCtx<'a> {
    /// `inferInstance` synthesizes an instance of the contextual expected type.
    /// A missing expected type or instance is a hard elaboration error; no
    /// placeholder term is fabricated.
    pub(in crate::infer) fn elab_infer_instance(&mut self) -> Result<Expr, ElabError> {
        let expected =
            self.current_expected_type
                .clone()
                .ok_or_else(|| ElabError::Unsupported {
                    feature:
                        "`inferInstance` without a known expected type (use `inferInstanceAs T`)"
                            .to_string(),
                })?;
        let expected = self.metas.instantiate(&expected);
        self.resolve_instance(&expected)
            .ok_or_else(|| ElabError::FailedToSynthesizeInstance {
                goal: crate::error_render::term(&expected),
                detail: self.instance_failure_detail(&expected),
            })
    }

    /// Classify a conditional guard after elaboration.
    ///
    /// Lean conditionals accept either `Bool` (through the Bool-to-Prop lane) or
    /// a term whose type is exactly `Prop`. Treating every non-Bool expression
    /// as a proposition defers an ill-typed `ite` to a distant kernel failure
    /// and can even ask instance synthesis for nonsense such as
    /// `Decidable (Type)`. Reject that category error at the elaboration
    /// boundary. Returns `true` for Bool and `false` for Prop.
    ///
    /// A condition whose type is still an unassigned metavariable — `if h : _
    /// then … else …`, whose hole is fixed only by the branches (`dif_pos h`
    /// against `dite P A B = A h`: Mathlib's `dite_eq_or_eq`/`ite_eq_or_eq`,
    /// measured 2026-09-12) — is a `Prop`: Lean elaborates the condition of
    /// `ite`/`dite` against `Prop`, so the hole becomes `?c : Prop`.
    pub(in crate::infer) fn condition_is_bool(
        &mut self,
        condition: &Expr,
    ) -> Result<bool, ElabError> {
        let condition_ty = self.infer_type(condition)?;
        let condition_ty = self.whnf(&self.metas.instantiate(&condition_ty));
        if let ExprKind::FVar(id) = condition_ty.kind() {
            if MetaState::from_fvar(*id).is_some() && self.try_unify(&condition_ty, &Expr::prop()) {
                return Ok(false);
            }
        }
        match condition_ty.kind() {
            ExprKind::Const(name, _) if *name == Name::from_string("Bool") => Ok(true),
            ExprKind::Sort(level) if level.normalize() == Level::Zero => Ok(false),
            _ => Err(ElabError::TypeMismatch {
                expected: "conditional guard of type Bool or Prop".to_string(),
                actual: format!("{condition_ty}"),
            }),
        }
    }

    pub(in crate::infer) fn resolve_decidable(&mut self, prop: &Expr) -> Result<Expr, ElabError> {
        let decidable_ty = Expr::app(
            Expr::const_(Name::from_string("Decidable"), vec![]),
            prop.clone(),
        );
        if let Some(inst) = self.resolve_instance(&decidable_ty) {
            return Ok(inst);
        }
        // Inside a postponing `let` scope a goal that still mentions a
        // metavariable waits, as Lean's instance argument of `ite` does:
        // `let k := 5; (if k = 5 then Tag.tag k else 0) + Tag.tag (k : Int)`
        // decides `k = 5` at `Int` (210). It is queued like any stuck goal;
        // one nothing grounds fails closed at the declaration.
        let goal = self.metas.instantiate(&decidable_ty);
        if self.postponing_let_depth > 0 && self.has_metavars(&goal) {
            let meta = self.fresh_meta(goal.clone());
            self.record_postponed_stuck_instance(&meta, &goal);
            return Ok(meta);
        }
        Err(ElabError::FailedToSynthesize {
            class_name: Name::from_string("Decidable"),
            goal: crate::error_render::term(&decidable_ty),
        })
    }

    fn sorry_goal_type(&mut self) -> Expr {
        self.current_expected_type
            .as_ref()
            .map(|ty| {
                let ty = self.metas.instantiate(ty);
                self.metas.instantiate_levels(&ty)
            })
            .unwrap_or_else(|| self.fresh_meta(Expr::type_()))
    }

    fn elab_sorry_with_kind(&mut self, kind: SorryKind) -> Result<Expr, ElabError> {
        let goal_ty = self.sorry_goal_type();
        // The elaborator may know local context and unresolved level assignments.
        // A failed sort inference is an elaboration error; fabricating universe
        // zero would change the judgment carried by the explicit trust marker.
        let goal_level = self.infer_sort(&goal_ty)?;
        Ok(create_sorry_term_with_kind_at_level(
            self.env, &goal_ty, kind, goal_level,
        ))
    }

    pub(super) fn elab_explicit_sorry(&mut self) -> Result<Expr, ElabError> {
        self.elab_sorry_with_kind(SorryKind::Explicit)
    }
    pub(super) fn elab_synthetic_sorry(&mut self) -> Result<Expr, ElabError> {
        self.elab_sorry_with_kind(SorryKind::Synthetic)
    }

    fn resolve_expected_ctor_ident(&mut self, ctor_suffix: &SurfaceName) -> Option<Expr> {
        let mut expected_ty = self.current_expected_type.clone()?;
        // Lean's `resolveDotName` reads the head constant of the expected type
        // BEFORE unfolding anything, and unfolds one definition at a time only
        // when `<head>.<name>` does not exist. The loop below started from a
        // full `whnf`, so an expected type headed by a DEFINITION —
        // `Function.Injective (Pi.map f)` for `.piMap fun _ ↦ hg` — was
        // unfolded into its `∀ a b, …` body and its domain, and
        // `Function.Injective.piMap` was never tried (`Injective.piMap`,
        // `Surjective.piMap`, `Bijective.piMap`, `Injective.comp_left` in
        // `Mathlib/Logic/Function/Basic.lean`, measured 2026-09-11).
        {
            let head_ty = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&expected_ty));
            if let ExprKind::Const(head, _) = head_ty.get_app_fn().kind() {
                let candidate = crate::namespace::append_names(head, ctor_suffix.name());
                if let Some(info) = self.env.get_const(&candidate) {
                    let levels: Vec<_> = info
                        .level_params
                        .iter()
                        .map(|_| self.fresh_universe_param())
                        .collect();
                    return Some(Expr::const_(candidate, levels));
                }
            }
        }
        // A function-typed expected type names its constructor through its
        // RESULT — Lean's `resolveDotName` runs `withForallBody`, so
        // `(.intro _) : p False → ∃ h, p h` is `Exists.intro`
        // (`h.elim (.intro _) (.intro _)`, `Prop.exists_iff` in
        // `Mathlib/Logic/Basic.lean`, measured 2026-09-11). The domain is kept
        // as the legacy fallback below.
        {
            let mut result_ty = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&expected_ty));
            let mut peeled = false;
            loop {
                let whnf = self.whnf(&result_ty);
                let ExprKind::Pi(_, domain, codomain) = whnf.kind() else {
                    break;
                };
                let placeholder = self.fresh_meta(domain.as_ref().clone());
                result_ty = codomain.instantiate(&placeholder);
                peeled = true;
            }
            if peeled {
                if let ExprKind::Const(head, _) = self.whnf(&result_ty).get_app_fn().kind() {
                    let candidate = crate::namespace::append_names(head, ctor_suffix.name());
                    if let Some(info) = self.env.get_const(&candidate) {
                        let levels: Vec<_> = info
                            .level_params
                            .iter()
                            .map(|_| self.fresh_universe_param())
                            .collect();
                        return Some(Expr::const_(candidate, levels));
                    }
                }
            }
        }
        loop {
            let expected_ty_whnf = self.whnf(
                &self
                    .metas
                    .instantiate_levels(&self.metas.instantiate(&expected_ty)),
            );
            if let ExprKind::Pi(_, domain, _) = expected_ty_whnf.kind() {
                expected_ty = domain.as_ref().clone();
                continue;
            }
            let mut head = &expected_ty_whnf;
            while let ExprKind::App(function, _) = head.kind() {
                head = function;
            }
            let ExprKind::Const(family, _) = head.kind() else {
                return None;
            };
            let ctor_name = crate::namespace::append_names(family, ctor_suffix.name());
            let levels: Vec<_> = self
                .env
                .get_const(&ctor_name)?
                .level_params
                .iter()
                .map(|_| self.fresh_universe_param())
                .collect();
            return Some(Expr::const_(ctor_name, levels));
        }
    }

    pub(super) fn elab_let(
        &mut self,
        binder: &SurfaceBinder,
        val: &SurfaceExpr,
        body: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        self.elab_let_binding(binder, val, body, false, TermLocalKind::Let)
    }

    pub(super) fn elab_have(
        &mut self,
        binder: &SurfaceBinder,
        val: &SurfaceExpr,
        body: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        self.elab_let_binding(binder, val, body, false, TermLocalKind::Have)
    }

    /// [`Self::elab_let`], with `aux_decl` set when the binding is a
    /// non-recursive `where`/`let rec` lowered to a plain `let`: the local is
    /// then recorded as an auxiliary declaration for the body
    /// ([`Self::resolve_dotted_ident`]).
    fn elab_let_binding(
        &mut self,
        binder: &SurfaceBinder,
        val: &SurfaceExpr,
        body: &SurfaceExpr,
        aux_decl: bool,
        kind: TermLocalKind,
    ) -> Result<Expr, ElabError> {
        // An unannotated numeral (`let k := 5`) has type `?α` in Lean, with
        // `OfNat ?α 5` pending until the body pins `?α` or defaulting makes it
        // `Nat` at the end. Clean's literal defaults to `Nat` at once, so a
        // body that pins `k` otherwise (`Tag.tag (k : Int)`) changed meaning:
        // with `Tag Nat`/`Tag Int` instances, `let k := 5; Tag.tag (k : Int)
        // + Tag.tag k` read `k : Nat` and was accepted as 110 (Lean 4.8.0:
        // `k : Int`, 210). So the value is first POSTPONED past the body (the
        // G36 path below), in a transaction; if that fails, the eager order
        // stands as before.
        // With a user `@[default_instance]` in the file the value is not
        // postponed whole: the default must be able to settle it before the
        // numeral's own `Nat` default (`NumeralsWait` below). Nor is it inside
        // an enclosing postponing `let` scope, whose numerals all wait for its
        // drain (`let k := (let j := 5; j + 0); Tag.tag (k : Int)` has `j :
        // Int`; resuming `5` at the inner `let`'s end would make it `Nat`).
        if binder.ty.is_none()
            && !aux_decl
            && Self::let_value_is_bare_numeral(val)
            && self.default_instances.is_empty()
            && self.postponing_let_depth == 0
        {
            if let Some(term) = self.lean_order_let_attempt(|this| {
                this.elab_let_binding_ordered(
                    binder,
                    val,
                    body,
                    aux_decl,
                    kind,
                    LetValueOrder::AfterBody,
                )
            })? {
                return Ok(term);
            }
        }
        // Any other value with a numeral in it (`id 5`, `(5, 0)`, `[5]`, `k +
        // 1`, `(5 : _)`, `let k : _ := 5`): the value is elaborated first, as
        // in Lean, but a numeral whose carrier is open waits for the body
        // (`elab_let_postpone.rs`, `LetValueOrder::NumeralsWait`). Inside an
        // enclosing such `let` this one joins it (no second transaction);
        // otherwise it is a transaction, and the eager order stands if it
        // fails.
        if !aux_decl && self.let_value_may_wait(binder, val) {
            if self.postponing_let_depth > 0 {
                return self.elab_let_binding_ordered(
                    binder,
                    val,
                    body,
                    aux_decl,
                    kind,
                    LetValueOrder::NumeralsWait,
                );
            }
            if let Some(term) = self.lean_order_let_attempt(|this| {
                this.elab_let_binding_ordered(
                    binder,
                    val,
                    body,
                    aux_decl,
                    kind,
                    LetValueOrder::NumeralsWait,
                )
            })? {
                return Ok(term);
            }
        }
        self.elab_let_binding_ordered(binder, val, body, aux_decl, kind, LetValueOrder::Eager)
    }

    /// A numeral expression: natural-number literals, parenthesized or
    /// combined by the arithmetic operators (`5`, `(5)`, `5 + 0`, `-2 * 3`),
    /// whose type Lean leaves open until the body or defaulting fixes it.
    pub(super) fn let_value_is_bare_numeral(val: &SurfaceExpr) -> bool {
        match val {
            SurfaceExpr::Lit(_, SurfaceLit::Nat(_) | SurfaceLit::BigNat(_)) => true,
            SurfaceExpr::Paren(_, inner) => Self::let_value_is_bare_numeral(inner),
            SurfaceExpr::App(_, func, args) => {
                matches!(
                    func.as_ref(),
                    SurfaceExpr::Ident(_, op) if matches!(
                        op.to_string().as_str(),
                        "HAdd.hAdd" | "HSub.hSub" | "HMul.hMul" | "HDiv.hDiv" | "HMod.hMod"
                            | "Neg.neg"
                    )
                ) && !args.is_empty()
                    && args
                        .iter()
                        .all(|arg| arg.name.is_none() && Self::let_value_is_bare_numeral(&arg.expr))
            }
            _ => false,
        }
    }

    /// [`Self::elab_let_binding`] with the value elaborated before the body
    /// (`LetValueOrder::Eager`), after it (`AfterBody`, see there), or first
    /// with its open numerals waiting for the body (`NumeralsWait`).
    fn elab_let_binding_ordered(
        &mut self,
        binder: &SurfaceBinder,
        val: &SurfaceExpr,
        body: &SurfaceExpr,
        aux_decl: bool,
        kind: TermLocalKind,
        order: LetValueOrder,
    ) -> Result<Expr, ElabError> {
        if order == LetValueOrder::Eager {
            return self.elab_let_binding_ordered_inner(binder, val, body, aux_decl, kind, order);
        }
        self.with_postponing_let_scope(|this| {
            this.elab_let_binding_ordered_inner(binder, val, body, aux_decl, kind, order)
        })
    }

    fn elab_let_binding_ordered_inner(
        &mut self,
        binder: &SurfaceBinder,
        val: &SurfaceExpr,
        body: &SurfaceExpr,
        aux_decl: bool,
        kind: TermLocalKind,
        order: LetValueOrder,
    ) -> Result<Expr, ElabError> {
        let postpone_value = order == LetValueOrder::AfterBody;
        let numerals_wait = order == LetValueOrder::NumeralsWait;
        // The surrounding expected type belongs to the *body* of the `let`, not
        // its bound value: in `let x := v; body : T`, it is `body` that has
        // type `T`, while `v` has the binder's own (annotated or inferred)
        // type. Carrying the body's expected type into the value elaboration
        // leaks the wrong target — e.g. `Except E α` from the enclosing match —
        // and elaborating the value mutates `current_expected_type` so that the
        // body (often the `match` itself) is then elaborated with a stale/wrong
        // expected type. That breaks anonymous-constructor (`.ok`/`.error`) dot
        // resolution inside the match arms ("cannot unify ... Const vs App").
        // Clear it for the value; restore it for the body. (Track KL)
        let body_expected = self.current_expected_type.clone();

        // A `where` / `let rec` helper lifts to the auxiliary declaration
        // `<decl>.<name>` (`let_rec_lift`); its value elaborates under that
        // name so a helper nested in it lifts to `<decl>.<name>.<inner>`.
        let aux_name = if aux_decl {
            self.let_rec_aux_name(&binder.name)
        } else {
            None
        };

        // Elaborate type and value, avoiding double elaboration when type is inferred.
        // G36: an unannotated value that failed for want of an expected type
        // (a leading-dot constructor) is POSTPONED past the body
        // (`elab_let_postpone.rs`); `postponed` then holds its eager error.
        let mut postponed: Option<ElabError> = None;
        let (ty, val_expr) = self.with_let_rec_decl_name(aux_name.as_ref(), |this| {
            if let Some(ty) = &binder.ty {
                // Explicit type annotation provided: the value is elaborated
                // against its own annotated type, not the body's expected type.
                let ty_expr = this.elaborate_type_observing(ty)?;
                let val_expr = if numerals_wait {
                    this.elab_value_with_waiting_numerals(val, Some(ty_expr.clone()))?
                } else {
                    this.elaborate_with_expected_type(val, Some(ty_expr.clone()))?
                };
                this.check_annotated_value_in_scope(&val_expr, &ty_expr)?;
                Ok::<_, ElabError>((ty_expr, val_expr))
            } else if numerals_wait {
                let val_expr = this.elab_value_with_waiting_numerals(val, None)?;
                let ty = this.infer_type(&val_expr)?;
                Ok((ty, val_expr))
            } else if postpone_value {
                postponed = Some(ElabError::CannotInfer);
                Ok(this.postponed_let_value_placeholder())
            } else {
                // Infer type from value - elaborate once and reuse. No expected
                // type applies to an unannotated `let` value.
                match this.elaborate_with_expected_type(val, None) {
                    Ok(val_expr) => {
                        let ty = this.infer_type(&val_expr)?;
                        Ok((ty, val_expr))
                    }
                    Err(err) if !aux_decl && Self::let_value_postponable(val) => {
                        postponed = Some(err);
                        Ok(this.postponed_let_value_placeholder())
                    }
                    Err(err) => Err(err),
                }
            }
        })?;
        let lifted = match aux_name.as_ref() {
            Some(aux) => self.let_rec_lifted_value(
                HelperSite {
                    aux,
                    span: helper_site_span(binder, val),
                    recursion: HelperRecursion::NonRecursive,
                    own_params: helper_own_params(binder, val),
                },
                &ty,
                &val_expr,
            )?,
            None => None,
        };

        // Push local, elaborate body with the let's expected type restored, then
        // abstract.
        let fvar = self.fresh_fvar();
        let stored_value = match kind {
            TermLocalKind::Let => val_expr.clone(),
            TermLocalKind::Have => crate::tactic::have_value(val_expr.clone()),
        };
        self.push_local_let_with_fvar(binder.name.clone(), fvar, ty.clone(), stored_value);
        if let (Some(aux), Some(lifted)) = (&aux_name, &lifted) {
            self.push_let_rec_use(fvar, aux, &ty, lifted);
        }
        self.note_local_forall_binder_names(fvar, binder.ty.as_deref(), &ty);
        self.capture_binder_info(binder, fvar);
        // A class-typed `let`/`have` local — `letI _ : LE α := ⟨…⟩`, `haveI :
        // Fact p := ⟨hp⟩` — is a local instance for the body, as every local
        // is in Lean (`withNewFVar` → `withNewLocalInstance`, Lean/Meta/Basic).
        // Only binders were, so `Preorder.lift`'s `letI _instLE : LE α := …;
        // Function.Injective.preorder f .rfl .rfl` failed "failed to
        // synthesize instance LE α" (measured 2026-09-12).
        let is_inst = self.binder_is_local_instance(BinderInfo::Default, &ty);
        if is_inst {
            self.push_local_instance(fvar, ty.clone());
        }
        if aux_decl {
            self.aux_decl_locals.insert(fvar);
        }
        let numeral_open = postpone_value && binder.ty.is_none();
        if numeral_open {
            self.open_numeral_let_types.push(ty.clone());
        }
        let body_result = self.elaborate_with_expected_type(body, body_expected);
        if numeral_open {
            self.open_numeral_let_types.pop();
        }
        self.aux_decl_locals.remove(&fvar);
        self.pop_let_rec_use(fvar);
        if is_inst {
            self.pop_local_instance();
        }
        // The body's error is propagated only after its lexical binder has
        // been removed, just like its instance and recursion bookkeeping.
        // Work counters and fresh identifiers remain cumulative.
        self.pop_local();
        let body_expr = match body_result {
            Ok(body_expr) => body_expr,
            // A postponed value's own error is what this `let` reported
            // before postponement existed: keep reporting it.
            Err(err) => return Err(postponed.unwrap_or(err)),
        };
        let (ty, val_expr) = match postponed {
            // The body has pinned the binder type; elaborate the value now,
            // outside the binder, against it.
            Some(original) => self.resume_postponed_let_value(val, &ty, &val_expr, original)?,
            None => (ty, val_expr),
        };
        // SOUNDNESS: instantiate assigned metavars/levels in the body before
        // abstracting `fvar` so any assignment mentioning a local is substituted
        // rather than left as a loose fvar in the closed `let`. TCB-neutral —
        // no-op absent assignments, and the kernel re-checks the result.
        let body_expr = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&body_expr));
        let body_abs = body_expr.abstract_fvar(fvar);
        // A lifted helper binds its auxiliary's closed form under the
        // auxiliary's name, for `finish_let_rec_lifts` to register; the term
        // is the same value, beta-expanded, so it checks exactly as before.
        let (name, value) = match (aux_name, lifted) {
            (Some(aux), Some(lifted)) => (aux, lifted),
            _ => (binder.name.name().clone(), val_expr),
        };
        Ok(Expr::let_named(
            name,
            ty,
            value,
            body_abs,
            matches!(kind, TermLocalKind::Have),
        ))
    }

    /// Elaborate `let rec f : T := v in e`.
    ///
    /// Three-way dispatch, mirroring Lean's `where`/`let rec` semantics
    /// (`where` desugars to a leading `let rec` group —
    /// `Lean/Elab/Binders.lean:472-476 expandWhereDecls`; the group is
    /// elaborated by `Lean/Elab/LetRec.lean:140 elabLetRec` and each decl is
    /// lifted to a top-level auxiliary definition,
    /// `Lean/Elab/LetRec.lean:110 registerLetRecsToLift`):
    ///
    /// 1. **Non-recursive** (`v` never mentions `f`, shadowing-aware): a plain
    ///    `let f : T := v in e`. Lean lifts a non-self-referential `let rec`
    ///    decl to a plain auxiliary definition — no fixpoint is involved — so
    ///    a plain `let` binding of the independently elaborated value is
    ///    exactly its semantics. This is the common `where` helper shape
    ///    (audit d04).
    ///
    /// 2. **Structurally recursive**: lift `f` to a real self-contained
    ///    recursive *value* `V : T` through the existing structural-recursion
    ///    machinery (the same path that lowers top-level recursive `def`s via
    ///    `<Inductive>.rec`), and bind it with an ordinary non-recursive
    ///    `let f : T := V in e`. The kernel re-checks `V`.
    ///
    ///    `V` may legitimately reference outer locals (e.g. a `let rec go`
    ///    inside `def Memory.readBytes (mem) := …` that reads `mem`, or a
    ///    `where` helper reading the parent's binders — Lean's `where` decls
    ///    likewise see the parent's binders because the generated `let rec`
    ///    sits inside them, `Lean/Elab/MutualDef.lean:332-397`): those locals
    ///    remain in scope while `V` is elaborated, so they stay bound by the
    ///    enclosing binder. No explicit capture-lifting is required because
    ///    `let f := V in e` keeps `V` in the same local context.
    ///
    /// 3. **Recursive but not structurally liftable** (no decreasing
    ///    parameter, zero-parameter self-reference, …): FAIL LOUD with
    ///    [`ElabError::WhereLetRecUnsupported`]. The pre-2026-07 fallback
    ///    bound `f` to a synthetic `sorry` and let the enclosing declaration
    ///    register axiom-tainted (audit d04's "registers-anyway" trap); that
    ///    fallback is eliminated.
    pub(super) fn elab_let_rec(
        &mut self,
        binder: &SurfaceBinder,
        val: &SurfaceExpr,
        body: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        self.with_eager_numerals(|this| this.elab_let_rec_inner(binder, val, body))
    }

    fn elab_let_rec_inner(
        &mut self,
        binder: &SurfaceBinder,
        val: &SurfaceExpr,
        body: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        // Recursive or not, this is a `let rec` header to Lean, whose
        // elaboration settles every pending numeral by defaulting (see
        // `let_rec_settled_open_numerals`).
        let open_numeral = self.open_numeral_let_types.iter().any(|ty| {
            let ty = self.metas.instantiate(ty);
            instance::bare_unassigned_meta(&self.metas, &ty).is_some()
        }) || self.postponed_numeral_still_open();
        if open_numeral {
            self.let_rec_settled_open_numerals += 1;
        }
        // Non-recursive binding: exactly a plain `let`. Two complementary,
        // shadowing-aware detectors decide "does `v` mention `f`":
        //  - the structural-recursion call detector (finds APPLIED self-calls
        //    anywhere, including match arms and do-blocks), and
        //  - the free-ident collector (finds BARE, non-applied self-mentions
        //    such as `let rec c : Nat := c`).
        // The second is essential: a bare self-mention routed to the plain
        // `let` path would leave `f` unresolved in the value, where decl-mode
        // auto-implicit insertion silently captures it as an extra implicit
        // binder — registering a declaration whose signature differs from the
        // one written. Both detectors must clear the value before it is
        // treated as non-recursive.
        let mentions_self = structural::detect_recursion_with_params(&binder.name, val, &[])
            .is_recursive
            || crate::where_desugar_ext::collect_free_idents(val).contains(&binder.name);
        if !mentions_self {
            return self.elab_let_binding(binder, val, body, true, TermLocalKind::Let);
        }

        // Recursive binding: lift to a real recursive value, or fail loud.
        if let Some(result) = self.try_elab_let_rec_lifted(binder, val, body)? {
            return Ok(result);
        }
        Err(ElabError::WhereLetRecUnsupported {
            name: binder.name.to_string(),
            shape: self.describe_unliftable_let_rec(binder, val),
        })
    }

    /// True iff every detected self-call passes the parameter at `pos`
    /// through unchanged — i.e. the "decreasing" argument never actually
    /// decreases. Shared by the lift gate and the loud-error description.
    fn all_calls_pass_param_unchanged(
        calls: &[structural::RecursiveCall],
        param_names: &[SurfaceName],
        pos: usize,
    ) -> bool {
        param_names.get(pos).is_some_and(|param| {
            calls.iter().all(|call| {
                matches!(call.args.get(pos),
                         Some(structural::RecursiveArg::Var(name)) if name == param)
            })
        })
    }

    /// Describe why a *recursive* `let rec`/`where` binding could not be
    /// lifted through the structural-recursion machinery. Used only to build
    /// the loud [`ElabError::WhereLetRecUnsupported`] message.
    fn describe_unliftable_let_rec(&self, binder: &SurfaceBinder, val: &SurfaceExpr) -> String {
        let mut params: Vec<SurfaceName> = Vec::new();
        let mut inner = val;
        while let SurfaceExpr::Lambda(_, bs, b) = inner {
            params.extend(bs.iter().map(|p| p.name.clone()));
            inner = b;
        }
        if params.is_empty() {
            return "self-recursive with no parameters (a value-level fixpoint has no \
                    terminating interpretation)"
                .to_string();
        }
        let info = structural::detect_recursion_with_params(&binder.name, inner, &params);
        // Mirrors the lift gate below (B97): a name-equality "unchanged"
        // verdict is discounted when a whole-body-match arm rebinds the
        // parameter, so shapes that ATTEMPTED the lift and failed for another
        // reason fall to the generic description instead.
        let no_descent = info.decreasing_arg.is_none()
            || info.decreasing_arg.is_some_and(|pos| {
                Self::all_calls_pass_param_unchanged(&info.calls, &params, pos)
                    && !structural::whole_body_match_rebinds_param(inner, &params, pos)
            });
        if info.is_recursive && no_descent {
            return "recursive, but no structurally decreasing parameter was found \
                    (well-founded recursion is not supported for `where`/`let rec` \
                    local definitions)"
                .to_string();
        }
        "recursive, but not liftable through the structural-recursion machinery".to_string()
    }

    /// Record the termination hints of a declaration's `where` helpers for
    /// the `let rec` lift. A helper without hints records nothing.
    pub(super) fn register_where_termination(
        &mut self,
        where_decls: &[clean_parser::WhereLocalDef],
    ) {
        self.where_termination.clear();
        for def in where_decls {
            if def.termination.termination_by.is_some() || def.termination.decreasing_by.is_some() {
                self.where_termination.push((
                    def.span,
                    def.name.name().clone(),
                    def.termination.clone(),
                    def.binders.len(),
                ));
            }
        }
    }

    /// The termination hints recorded for the `where` helper this `let rec`
    /// binder came from (matched by span and name), or none.
    pub(super) fn where_termination_for(
        &self,
        binder: &SurfaceBinder,
    ) -> clean_parser::TerminationHints {
        self.where_termination
            .iter()
            .find(|(span, name, _, _)| *span == binder.span && name == binder.name.name())
            .map(|(_, _, hints, _)| hints.clone())
            .unwrap_or_default()
    }

    /// Attempt the structural-recursion lift for `let rec f := v in e`.
    ///
    /// Returns `Ok(Some(term))` on success, `Ok(None)` when the binding is not
    /// a liftable structurally recursive function (the caller then FAILS LOUD
    /// with [`ElabError::WhereLetRecUnsupported`] — there is no `sorry`
    /// fallback), and `Err` for genuine type errors discovered while
    /// elaborating the lifted value or the body.
    fn try_elab_let_rec_lifted(
        &mut self,
        binder: &SurfaceBinder,
        val: &SurfaceExpr,
        body: &SurfaceExpr,
    ) -> Result<Option<Expr>, ElabError> {
        let func_name = binder.name.clone();

        // 1. Recover the helper's (parameters, ascribed return type, body). Two
        //    encodings reach here:
        //
        //    (a) EQUATION form (`where go : Nat → Nat | 0 => 0 | k+1 => go k`):
        //        `build_let_rec` emits `Ascription(PatternMatchLambda([_x],
        //        match _x with …), τ)` with the full `τ = params → ret` on the
        //        binder. The `_x` scrutinee parameter is hidden from the plain
        //        lambda peel below, so reuse the top-level equation-def
        //        normalization — unwrap the return-type ascription, then peel one
        //        domain off `τ` to lift `_x` into a real binder — routing the
        //        helper through the IDENTICAL structural-recursion lowering a
        //        top-level equation `def` uses.
        //
        //    (b) PLAIN lambda (`let rec f (p₁ …) : R := body`, encoded as
        //        `Lambda([p₁ …], (body : R))`): peel the leading lambda binders.
        let eq_val = match val {
            SurfaceExpr::Ascription(_, boxed, _) => boxed.as_ref(),
            other => other,
        };
        for arm in elab_decl_value::whole_body_match_arms(eq_val) {
            self.check_pattern_linear(&arm.pattern)?;
        }
        let (helper_binders, ret_ty, helper_body): (
            Vec<SurfaceBinder>,
            Option<SurfaceExpr>,
            SurfaceExpr,
        ) = if let Some((lifted, ret, body)) = elab_decl_value::normalize_equation_def(
            self.env,
            &self.pattern_idents(eq_val),
            &binder.name,
            &[],
            binder.ty.as_deref(),
            eq_val,
        )? {
            (lifted, ret, body)
        } else {
            let mut binders: Vec<SurfaceBinder> = Vec::new();
            let mut inner = val;
            while let SurfaceExpr::Lambda(_, bs, b) = inner {
                binders.extend(bs.iter().cloned());
                inner = b;
            }
            // No parameters → not a function we can lift via structural recursion.
            if binders.is_empty() {
                return Ok(None);
            }
            match inner {
                SurfaceExpr::Ascription(_, b, r) => (binders, Some((**r).clone()), (**b).clone()),
                other => (binders, binder.ty.as_deref().cloned(), other.clone()),
            }
        };
        let helper_body = &helper_body;

        // 2. Detect structural recursion on `func_name` over the helper's
        //    parameters. Only lift when a decreasing argument is found; any
        //    other shape (well-founded, non-recursive, mutual) defers to the
        //    conservative fallback so we never fabricate an ill-formed term.
        let param_names: Vec<SurfaceName> = helper_binders.iter().map(|b| b.name.clone()).collect();
        let recursion_info =
            structural::detect_recursion_with_params(&func_name, helper_body, &param_names);
        if !recursion_info.is_recursive {
            return Ok(None);
        }
        // A `where` helper's own `termination_by <measure>` (K5 probe b2)
        // routes it to the same well-founded lowering a top-level `def`
        // with that hint gets (`setup_recursion`), so the structural gates
        // below do not apply to it: no structurally decreasing parameter is
        // expected.
        let mut termination = self.where_termination_for(binder);
        let written_count = self
            .where_termination
            .iter()
            .find(|(span, name, _, _)| *span == binder.span && name == binder.name.name())
            .map(|(_, _, _, count)| *count)
            .unwrap_or(helper_binders.len());
        if let Some(tb) = termination.termination_by.as_mut() {
            let written_binders =
                helper_binders
                    .get(..written_count)
                    .ok_or_else(|| ElabError::Unsupported {
                        feature: "where helper lost written parameters during normalization".into(),
                    })?;
            if let Some(index) =
                Self::structural_hint_index(tb, written_binders, helper_binders.len())
                    .map_err(|feature| ElabError::Unsupported { feature })?
            {
                tb.kind =
                    clean_parser::TerminationKind::Structural(helper_binders[index].name.clone());
                tb.params.clear();
                tb.measure = None;
            }
        }
        let well_founded = termination
            .termination_by
            .as_ref()
            .is_some_and(|tb| tb.well_founded_measure().is_some());
        if recursion_info.decreasing_arg.is_none() && !well_founded {
            return Ok(None);
        }
        // `find_decreasing_arg` falls back to "last variable position" when no
        // position is provably smaller. For a local helper, reject the lift
        // when EVERY self-call passes the chosen parameter through UNCHANGED
        // (`g m` with param `m`): that is not structural descent, and running
        // the `.rec` lowering on it only produces a downstream unification
        // error. Bailing here routes the shape to the caller's typed loud
        // `WhereLetRecUnsupported` ("no structurally decreasing parameter").
        //
        // B97 exception (shadowed rebind): when the whole body is
        // `match <param> with …` and some arm REBINDS the parameter's name
        // (`let rec go (k : Nat) := match k with | 0 => 0 | k + 1 => go k`),
        // the name-equality check above is unreliable — the call's `k` is the
        // rebound, one-step-smaller pattern component, exactly the shape the
        // shared B89 whole-body-match-scrutinee preference selected `dec_pos`
        // for. Proceed with the lift: the `.rec` lowering substitutes IHs
        // solely for genuinely smaller components, so a call that really
        // passes the OUTER parameter unchanged still fails loud downstream
        // (and the kernel re-checks the lowered value regardless).
        if let (false, Some(dec_pos)) = (well_founded, recursion_info.decreasing_arg) {
            if Self::all_calls_pass_param_unchanged(&recursion_info.calls, &param_names, dec_pos)
                && !structural::whole_body_match_rebinds_param(helper_body, &param_names, dec_pos)
            {
                return Ok(None);
            }
        }

        // 3. Run the helper through the structural-recursion lowering exactly
        //    like a top-level recursive `def`.
        //
        //    The namespace prefix is INTENTIONALLY KEPT in scope (this code used
        //    to `std::mem::take` it). The helper's binder/return types and body
        //    may mention namespace-scoped constants — inside `namespace TrustIr`,
        //    a helper param `cur : Addr` refers to `TrustIr.Addr`. Clearing the
        //    prefix broke that resolution: the bare `Addr` then fell through to
        //    auto-implicit and was bound as a fresh free variable typed `Sort u`,
        //    leaking an `UnknownFVar` / `FVar vs Const` mismatch into the lowered
        //    recursor term (Track F — `Memory.readBytes` and every imported-type
        //    extra param). The prefix was originally cleared only so
        //    `setup_recursion` would record the *unqualified* self-call name; we
        //    now restore that unqualified name explicitly after setup (below)
        //    instead, decoupling it from type resolution.
        let saved_ctx = self.recursive_def_ctx.take();

        // The helper lifts to `<decl>.<name>` (`let_rec_lift`); its value
        // elaborates under that name so a nested helper lifts beneath it.
        let aux_name = self.let_rec_aux_name(&func_name);
        // Every local bound from here on belongs to the helper; one bound
        // before (a sibling `where` helper of the same name above all) is
        // shadowed by the helper's own name (`outer_locals_floor`).
        let outer_locals_floor = self.next_fvar;
        let lowered: Result<(Expr, Expr), ElabError> =
            self.with_let_rec_decl_name(aux_name.as_ref(), |this| {
                // `setup_recursion` returns `Some` only for the explicit
                // `termination_by <measure>` well-founded path: the helper's
                // value is then the `WellFounded.fix` lowering, elaborated
                // in the enclosing context so a captured outer variable
                // (`limit` in `go i := … go (i + 1) … termination_by limit
                // - i`) stays a free variable of the value, exactly like a
                // structural helper's. For structural recursion it installs
                // `recursive_def_ctx` and returns `None`.
                if let Some(pair) = this.setup_recursion(
                    &func_name,
                    &helper_binders,
                    ret_ty.as_ref(),
                    helper_body,
                    &termination,
                )? {
                    return Ok(pair);
                }
                // `setup_recursion` qualifies the recorded `func_name` with the
                // active namespace prefix (`TrustIr.go`). But a `let rec` helper's
                // self-calls are written *unqualified* (`go …`), and
                // `RecursiveDefContext::matches_call_name` only matches a bare
                // candidate against the *exact* recorded name (its suffix rule
                // requires the qualified side to be the candidate). Force the
                // recorded name back to the bare helper name so call-site IH
                // substitution recognizes `go …` — while the namespace prefix stays
                // in scope so the helper's binder/return types still resolve their
                // namespace-scoped constants (`Addr` → `TrustIr.Addr`).
                if let Some(ref mut ctx) = this.recursive_def_ctx {
                    ctx.func_name = func_name.clone();
                    ctx.outer_locals_floor = Some(outer_locals_floor);
                }
                this.elab_def_body(&helper_binders, ret_ty.as_ref(), helper_body)
            });

        // Always restore the recursion context, even on error.
        self.recursive_def_ctx = saved_ctx;

        let (helper_ty, helper_val) = match lowered {
            Ok(pair) => pair,
            // A `CannotInfer` here is our own bail-out signal for the WF path;
            // treat it as "not liftable" rather than a hard error so the
            // fallback can run. Other errors are genuine and propagate.
            Err(ElabError::CannotInfer) => return Ok(None),
            Err(e) => return Err(e),
        };

        // Instantiate metavariables/levels so the bound value is closed.
        let helper_ty = self.metas.instantiate(&helper_ty);
        let helper_ty = self.metas.instantiate_levels(&helper_ty);
        let helper_val = self.metas.instantiate(&helper_val);
        let helper_val = self.metas.instantiate_levels(&helper_val);

        // 4. Bind the lifted value with a plain non-recursive `let`, with `f`
        //    in scope for the body. Self-references in the body resolve to `f`
        //    (the bound local), whose value is the closed recursive term.
        let lifted = match aux_name.as_ref() {
            Some(aux) => self.let_rec_lifted_value(
                HelperSite {
                    aux,
                    span: helper_site_span(binder, val),
                    recursion: HelperRecursion::Recursive,
                    own_params: helper_own_params(binder, val),
                },
                &helper_ty,
                &helper_val,
            )?,
            None => None,
        };
        let fvar = self.push_local(func_name.clone(), helper_ty.clone());
        if let (Some(aux), Some(lifted)) = (&aux_name, &lifted) {
            self.push_let_rec_use(fvar, aux, &helper_ty, lifted);
        }
        self.aux_decl_locals.insert(fvar);
        let body_expr = self.elaborate(body);
        self.aux_decl_locals.remove(&fvar);
        self.pop_let_rec_use(fvar);
        let body_expr = body_expr?;
        self.pop_local();
        // SOUNDNESS: instantiate assigned metavars/levels in the body before
        // abstracting `fvar` so no loose fvar leaks into the closed `let rec`
        // body. TCB-neutral — the kernel re-checks the lifted value and body.
        let body_expr = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&body_expr));
        let body_abs = body_expr.abstract_fvar(fvar);

        // A lifted helper binds its auxiliary's closed form under the
        // auxiliary's name (see `elab_let_binding`).
        let (name, value) = match (aux_name, lifted) {
            (Some(aux), Some(lifted)) => (aux, lifted),
            _ => (func_name.name().clone(), helper_val),
        };
        Ok(Some(Expr::let_named(
            name, helper_ty, value, body_abs, false,
        )))
    }

    /// Returns `true` iff `ty` is a proposition (`ty : Prop`, i.e. `Sort 0`).
    ///
    /// Used by [`elab_ascription`] to decide whether to preserve the ascribed
    /// type as written (proof ascriptions) or fall back to the inner term's
    /// inferred type (data/coercion ascriptions). A failure to infer the sort
    /// (e.g. unresolved metavariables) conservatively returns `false`, leaving
    /// the legacy behavior intact.
    fn ascription_is_prop(&self, ty: &Expr) -> bool {
        match self.infer_type(ty) {
            Ok(sort) => matches!(self.whnf(&sort).kind(), ExprKind::Sort(l) if l.is_zero()),
            Err(_) => false,
        }
    }

    pub(super) fn elab_ascription(
        &mut self,
        expr: &SurfaceExpr,
        ty: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        let ty_expr = self.elaborate_type_observing(ty)?;
        // A WRITTEN ascribed type with no metavariable is the expected type
        // Lean hands `expr` (`elabTermEnsuringType e T`), whatever the context
        // holds; a bare `x.casesOn` may then be elaborated as an eliminator
        // against it (`elab_dot_elim.rs`). A type completed from the context
        // below is not: Lean elaborates `expr` against the metavariable.
        let written_ground = (!self.has_metavars(&ty_expr)).then(|| ty_expr.clone());
        // An ascribed type that still carries metavariables — `(e : _)`, and
        // in particular `‹_›`, which parses as `(by assumption : _)` — takes
        // them from the expected type FIRST, so the inner term (a tactic
        // block above all) sees the type the context demands instead of a
        // bare hole. Lean reaches the same state by postponing the block until
        // `ensureHasType` has unified the ascription with the expected type;
        // measured on `theorem t {p : Prop} (hp : p) : p := ‹_›`, whose
        // `assumption` ran against the unassigned hole and found nothing
        // (2026-09-11). A failed unification leaves no assignment behind and
        // the ordinary post-check below still decides.
        let ty_expr = if self.has_metavars(&ty_expr) {
            if let Some(expected) = self.current_expected_type.clone() {
                let ty_inst = self.metas.instantiate(&ty_expr);
                let expected_inst = self.metas.instantiate(&expected);
                self.metas.push_scope();
                if self.try_unify(&ty_inst, &expected_inst) {
                    self.metas.commit();
                } else {
                    self.metas.pop_scope();
                }
            }
            self.metas.instantiate(&ty_expr)
        } else {
            ty_expr
        };
        let saved_dot = self.dot_elim.arm_expected(expr, written_ground.as_ref());
        let expr_val = self.elaborate_with_expected_type(expr, Some(ty_expr.clone()));
        self.dot_elim.restore_expected(saved_dot);
        let expr_val = expr_val?;

        // Infer the actual type of the expression
        let actual_ty = self.infer_type(&expr_val)?;

        // Unify the actual type with the expected type
        let ctx = self.build_local_ctx();
        let ur = Unifier::with_env(&mut self.metas, self.env, ctx).unify(&actual_ty, &ty_expr);
        match ur {
            UnifyResult::Success => {
                // Apply level instantiation - unification may solve level constraints
                let result = self.metas.instantiate(&expr_val);
                let result = self.metas.instantiate_levels(&result);

                // Preserve the ascribed type AS WRITTEN for proof ascriptions.
                //
                // For `show A = B from rfl` (and any `show T from e` where `T` is
                // a Prop), the inner proof's *inferred* type can differ
                // syntactically from the written `T`: a `rfl : @Eq α a a` carries
                // a single side, and inferring the inner term re-derives both
                // sides from that one expression, losing the surface forms `A`
                // and `B` (e.g. `Nat.land m n` δ-unfolds to its `Nat.rec` body).
                //
                // `rw [show A = B from rfl]` then searches the goal for the
                // *unfolded* `from` side, which does not occur (the goal still
                // holds the folded `Nat.land m n`), and fails `RewriteNoMatch`.
                //
                // Wrap the proof in an applied identity lambda
                // `(fun (h : T) => h) e`. Its inferred type is exactly the
                // ascribed `T` (App inference instantiates the lambda's
                // codomain, which is `T` verbatim — see tc/infer.rs App arm), so
                // downstream `match_equality` recovers `A`/`B` as written. The
                // kernel re-checks the beta-redex: it still requires `e : T` by
                // definitional equality, so soundness is unchanged (the redex
                // β-reduces back to `e`).
                //
                // Restricted to Prop-valued ascriptions whose written type
                // differs *syntactically* from the inner proof's inferred type.
                // When the inner term already infers to exactly the ascribed type
                // (e.g. `exact (f hP : Q)` where `f hP : Q`), wrapping would only
                // bloat the term and break callers that pattern-match the bare
                // proof — so we leave it untouched in that case.
                let ty_inst = self.metas.instantiate(&ty_expr);
                let ty_inst = self.metas.instantiate_levels(&ty_inst);
                let actual_inst = self.metas.instantiate(&actual_ty);
                let actual_inst = self.metas.instantiate_levels(&actual_inst);
                if ty_inst != actual_inst && self.ascription_is_prop(&ty_inst) {
                    let id_lam = Expr::lam(BinderInfo::Default, ty_inst.clone(), Expr::bvar(0));
                    return Ok(Expr::app(id_lam, result));
                }
                Ok(result)
            }
            UnifyResult::Failure(_msg) => {
                // Before returning TypeMismatch, try type coercion (#796).
                // Lean 4 inserts Coe instances when ascription types don't directly unify.
                if let Some(coerced) = self.try_coerce(&expr_val, &actual_ty, &ty_expr) {
                    let result = self.metas.instantiate(&coerced);
                    return Ok(self.metas.instantiate_levels(&result));
                }
                Err(ElabError::TypeMismatch {
                    expected: format!("{ty_expr}"),
                    actual: format!("{actual_ty} ({_msg})"),
                })
            }
            UnifyResult::Stuck => {
                // Stuck means unification could not determine correctness
                // (e.g., unsolved metavariables). Treat as error for soundness.
                Err(ElabError::CannotInfer)
            }
        }
    }

    /// Desugar `if c then a else b` → `@ite α c inst a b`.
    /// Both branches elaborate against one shared result type (#2786).
    pub(super) fn elab_if(
        &mut self,
        cond: &SurfaceExpr,
        then_br: &SurfaceExpr,
        else_br: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        // Capture the expected type *before* elaborating the condition: the
        // expected type belongs to the branches (`then`/`else`), not to the
        // condition. Elaborating the condition (`b == 0`, …) can mutate
        // `current_expected_type` as a side effect, which would otherwise strand
        // the branches without their expected type — breaking anonymous
        // constructor (`.ok`/`.error`) resolution when the `if` sits inside a
        // match arm. Elaborate the condition with the expected type cleared.
        // (Track KL)
        let branch_expected = self.current_expected_type.clone();
        let cond_expr = self.elaborate_with_expected_type(cond, None)?;
        let (result_ty, then_expr, else_expr) = if let Some(expected) = branch_expected {
            let t = self.elaborate_with_expected_type(then_br, Some(expected.clone()))?;
            let e = self.elaborate_with_expected_type(else_br, Some(expected.clone()))?;
            (expected, t, e)
        } else {
            let t = self.elaborate(then_br)?;
            let raw = self.infer_type(&t)?;
            let raw = self.metas.instantiate_levels(&self.metas.instantiate(&raw));
            // Insert any LEADING IMPLICIT args on the then-branch so its inferred
            // type is concrete before it becomes the else-branch's expected type.
            // Without this, a bare polymorphic `none : {α} → Option α` leaves the
            // branch type a function type, and an `else some 0 : Option Int` then
            // mismatches it. `insert_implicit_args` only fills leading implicit /
            // instance binders (explicit function types like `A → B` are left
            // untouched), so this is a no-op for genuinely function-valued branches.
            // Nothing is applied to the branch, so `⦃x⦄` stays a binder.
            //
            // The else-branch gets the FOLDED then-type: `insert_implicit_args`
            // returns the whnf of the remaining type, which unfolds an
            // abbreviated monad (`StateT σ m α` is a Pi underneath), and a
            // `pure ()`/`throw e` else-branch cannot pin its monad against a
            // bare Pi (G31, ledger (101)). When nothing was inserted the
            // then-type is the inferred `raw` itself; otherwise the type is
            // re-inferred from the applied term, as Lean's `finalize` does.
            let before = t.clone();
            let (t, unfolded) = self.insert_implicit_args(t, &raw, ArgsFollow::No);
            // Gated (r4 review): a folded type headed by a semireducible
            // `def` that no instance keys on keeps the unfolded type until
            // G47 lands (`elab_folded_type`), or `def M := StateT …` with a
            // `pure ()` else-branch would be ACCEPTED where Lean fails to
            // synthesize `Pure M`.
            let folded = if t == before {
                raw
            } else {
                self.infer_type(&t).unwrap_or_else(|_| unfolded.clone())
            };
            let folded = self.later_branch_type(folded, unfolded);
            let ty = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&folded));
            let e = self.elaborate_with_expected_type(else_br, Some(ty.clone()))?;
            (ty, t, e)
        };
        let result_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&result_ty));
        let level = self.infer_sort(&result_ty)?;
        // A `Bool` condition takes the Lean-faithful Bool→Prop lane (see
        // `mk_bool_if`); a genuine `Prop` condition takes the `ite` path below.
        let cond_is_bool = self.condition_is_bool(&cond_expr)?;
        if cond_is_bool {
            return Ok(self.mk_bool_if(&level, &result_ty, cond_expr, then_expr, else_expr));
        }
        let ite = Expr::const_(Name::from_string("ite"), vec![level]);
        let decidable_inst = self.resolve_decidable(&cond_expr)?;
        Ok(Expr::apps(
            ite,
            [result_ty, cond_expr, decidable_inst, then_expr, else_expr],
        ))
    }

    /// Lower `if (c : Bool) then t else e` the way Lean 4 does: the condition
    /// is coerced to the Prop `c = true` and the whole expression becomes
    /// `@ite.{u} α (c = true) inst t e` with `inst : Decidable (c = true)`
    /// from instance synthesis (`instDecidableEqBool c true` in a Lean-core
    /// environment, via the decEq bridge). Producing the SAME term shape real
    /// Lean produces is what lets clean-elaborated statements unify
    /// definitionally against `.olean`-imported encodings of the same source —
    /// the trust-ir Lean↔Clean bridge's Bool-guarded division arms (blocker
    /// B2) hinge on it.
    ///
    /// When the environment carries no `Decidable (c = true)` instance at all
    /// (bare kernel environments without a decidable-equality-of-Bool leaf),
    /// fall back to the definitional `Bool.rec` elimination — honest and
    /// self-contained, but a shape real Lean never emits (Lean core always has
    /// the instance). No `sorry` is ever synthesized on this path.
    pub(in crate::infer) fn mk_bool_if(
        &mut self,
        level: &Level,
        result_ty: &Expr,
        cond_expr: Expr,
        then_expr: Expr,
        else_expr: Expr,
    ) -> Expr {
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let prop = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [
                bool_ty.clone(),
                cond_expr.clone(),
                Expr::const_(Name::from_string("Bool.true"), vec![]),
            ],
        );
        let decidable_goal = Expr::app(
            Expr::const_(Name::from_string("Decidable"), vec![]),
            prop.clone(),
        );
        if let Some(inst) = self.resolve_instance(&decidable_goal) {
            let ite = Expr::const_(Name::from_string("ite"), vec![level.clone()]);
            return Expr::apps(ite, [result_ty.clone(), prop, inst, then_expr, else_expr]);
        }
        // Fallback: `@Bool.rec.{u} (fun _ : Bool => α) e t c` — Bool.rec's
        // false-case is the else-branch and its true-case the then-branch.
        // Non-dependent motive; lift result_ty's loose bound variables past
        // the new binder.
        let motive = Expr::lam(BinderInfo::Default, bool_ty, result_ty.lift(1));
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![level.clone()]);
        Expr::apps(bool_rec, [motive, else_expr, then_expr, cond_expr])
    }

    pub(super) fn elab_syntax_quote(&mut self, content: &str) -> Result<Expr, ElabError> {
        // ``` ``foo ```: Lean's `doubleQuotedName` resolves `foo` to the ONE
        // declaration it names in this scope (`realizeGlobalConstNoOverload`)
        // and quotes THAT name, refusing an unknown or ambiguous one. The lexer
        // keeps the second backtick as the content's first character.
        if let Some(written) = content.strip_prefix(clean_parser::lexer::DOUBLE_QUOTED_NAME_PREFIX)
        {
            let resolved = self.resolve_double_quoted_name(written)?;
            return self.elab_syntax_quote(&resolved);
        }
        // `` `foo.bar ``: a NAME literal, `Lean.Name.str (Lean.Name.str
        // Lean.Name.anonymous "foo") "bar"` -- Lean's `quote` of the name. It
        // used to go through `parse_quotation` -> `syntax_to_surface`, which
        // turns a quoted identifier back into the IDENTIFIER, so `` `foo ``
        // elaborated to the declaration `foo` itself: with `import Lean`,
        // ``s.contains `foo`` read "expected Lean.Name, got Nat" (upstream
        // tests/elab/2077.lean). Built only where `Lean.Name` exists; without
        // it (Clean's own prelude has none) the long-standing path below runs.
        if let Some(literal) = self.name_literal(content) {
            return Ok(literal);
        }
        let quoted = parse_quotation(&format!("`{content}"))
            .map_err(|e| ElabError::MacroError(e.to_string()))?;
        let surface = syntax_to_surface(&quoted.syntax).ok_or_else(|| {
            ElabError::MacroError("could not convert syntax quotation to surface expression".into())
        })?;
        self.elaborate(&surface)
    }

    /// The `Lean.Name` term a simple quote `` `content `` denotes, or `None`
    /// when `content` is not a plain name (a `(…)`/`[…]`/`{…}` syntax
    /// quotation) or the environment has no `Lean.Name` constructors.
    fn name_literal(&self, content: &str) -> Option<Expr> {
        if content.is_empty() || content.starts_with(['(', '[', '{']) {
            return None;
        }
        let ctor = |name: &str| {
            let name = Name::from_string(name);
            self.env
                .get_const(&name)
                .is_some()
                .then(|| Expr::const_(name, vec![]))
        };
        let (anonymous, str_ctor, num_ctor) = (
            ctor("Lean.Name.anonymous")?,
            ctor("Lean.Name.str")?,
            ctor("Lean.Name.num")?,
        );
        let surface = clean_parser::parse_name(content).ok()?;
        fn quote(name: &Name, anonymous: &Expr, str_ctor: &Expr, num_ctor: &Expr) -> Expr {
            match name.inner() {
                clean_kernel::name::NameInner::Anon => anonymous.clone(),
                clean_kernel::name::NameInner::Str(pre, s) => Expr::app(
                    Expr::app(str_ctor.clone(), quote(pre, anonymous, str_ctor, num_ctor)),
                    Expr::str_lit(s.as_ref()),
                ),
                clean_kernel::name::NameInner::Num(pre, n) => Expr::app(
                    Expr::app(num_ctor.clone(), quote(pre, anonymous, str_ctor, num_ctor)),
                    Expr::nat_lit(*n),
                ),
            }
        }
        Some(quote(surface.name(), &anonymous, &str_ctor, &num_ctor))
    }

    /// The declaration a double-quoted name literal ``` ``written ``` denotes,
    /// spelled for a single-backtick quote. Lean's `doubleQuotedName`
    /// elaborator: `realizeGlobalConstNoOverload`, so an unknown name is
    /// `unknown constant` and an ambiguous one `ambiguous identifier`.
    fn resolve_double_quoted_name(&self, written: &str) -> Result<String, ElabError> {
        let name = clean_parser::parse_name(written).map_err(|e| {
            ElabError::MacroError(format!("invalid double-quoted name ``{written}: {e}"))
        })?;
        match crate::name_resolution::resolve_global_const_no_overload(
            &name,
            &self.namespace_state,
            self.env,
            &self.foreign_private_decls,
        ) {
            Ok(resolved) => Ok(resolved.to_string()),
            Err(crate::name_resolution::GlobalConstResolution::Unknown) => Err(
                ElabError::UnknownIdent(format!("unknown constant '{written}' in ``{written}")),
            ),
            Err(crate::name_resolution::GlobalConstResolution::Ambiguous(candidates)) => {
                Err(ElabError::UnknownIdent(format!(
                    "ambiguous identifier '{written}' in ``{written}, possible interpretations: [{}]",
                    candidates
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                )))
            }
        }
    }

    pub(super) fn elab_explicit(&mut self, inner: &SurfaceExpr) -> Result<Expr, ElabError> {
        // Explicit application: @f (#1231)
        // This disables implicit argument insertion for the inner expression.
        // Set explicit_mode = true so insert_implicit_args returns early.
        let prev_explicit_mode = self.explicit_mode;
        self.explicit_mode = true;
        let result = self.elaborate(inner);
        self.explicit_mode = prev_explicit_mode;
        result
    }

    pub(super) fn elab_if_decidable(
        &mut self,
        witness_name: &SurfaceName,
        prop: &SurfaceExpr,
        then_br: &SurfaceExpr,
        else_br: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        // The condition and both branches are fallible after taking the outer
        // expected type and after introducing branch witnesses. A temporary
        // transaction commits successful metavariable work used by the result,
        // while restoring the exact expected/local state on every exit.
        self.with_temporary_local_scope(|this| {
            this.elab_if_decidable_inner(witness_name, prop, then_br, else_br)
        })
    }

    fn elab_if_decidable_inner(
        &mut self,
        witness_name: &SurfaceName,
        prop: &SurfaceExpr,
        then_br: &SurfaceExpr,
        else_br: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        if std::env::var_os("CLEAN_UNIFY_TRACE").is_some() {
            eprintln!("dite-builder: entered witness={witness_name}");
        }
        // if h : p then t else e
        // Desugars to: dite p (fun h : p => t) (fun h : ¬p => e)
        //
        // dite (Decidable If-Then-Else) has type:
        // dite : {α : Sort u} → (p : Prop) → [Decidable p] →
        //        (p → α) → (¬p → α) → α
        //
        // `dite`'s result type `α` is FIXED (it does not depend on the decision),
        // so BOTH branch bodies must inhabit the same `α` — the surrounding
        // expected type when one is known (#B09). Take it as the branches'
        // expected type and CLEAR it while elaborating the condition: `p`'s type
        // is `Prop`, never the branch result type, and letting the outer result
        // type leak into `elaborate(prop)` mis-checks the condition (the
        // def-body expected-type lane otherwise fails `n = 0` against
        // `n = 0 ∨ ¬ n = 0`). This mirrors `elab_if`, which likewise elaborates
        // its condition with the expected type cleared and propagates it into the
        // branches. A polymorphic proof/value body such as `Or.inl h` (`h : p`)
        // or `.ok x` needs that expected type to resolve its metavariables, and
        // the hypothesis binder is in scope so `h` is usable in that body.
        // Without it `dite` is unusable whenever `h` is actually consumed
        // (Init/Prelude.lean `dite`).
        let outer_expected = self.current_expected_type.take();
        let branch_expected = outer_expected.as_ref().map(|expected| {
            self.metas
                .instantiate_levels(&self.metas.instantiate(expected))
        });
        let prop_expr = self.elaborate(prop)?;
        if self.condition_is_bool(&prop_expr)? {
            return Err(ElabError::TypeMismatch {
                expected: "dependent-if condition of type Prop".to_string(),
                actual: "Bool".to_string(),
            });
        }

        // Create the then branch: (fun h : p => t), body checked against α.
        let then_fvar = self.push_local(witness_name.clone(), prop_expr.clone());
        let then_result = self.elaborate_with_expected_type(then_br, branch_expected.clone());
        if std::env::var_os("CLEAN_UNIFY_TRACE").is_some() {
            eprintln!("dite-then: ok={}", then_result.is_ok());
        }
        let then_expr = match then_result {
            Ok(e) => e,
            Err(err) => {
                self.pop_local();
                return Err(err);
            }
        };
        self.pop_local();

        // `α` is the shared result type of BOTH branches: the known expected
        // type, else the then-branch's inferred type. Using it as the else
        // branch's expected type (below) cross-resolves the branches'
        // metavariables — `Or.inl h`'s right disjunct is pinned by `Or.inr h`'s
        // type and vice versa — so a `dite` in an INFERENCE position (`def f :=
        // if h : c then Or.inl h else Or.inr h`) leaves no dangling metavariable
        // that would otherwise leak to the kernel as a free variable. Mirrors
        // `elab_if`, which feeds the then-branch type to the else branch.
        let alpha = match &branch_expected {
            Some(expected) => expected.clone(),
            None => {
                let alpha = self.infer_type(&then_expr)?;
                let alpha = self.metas.instantiate(&alpha);
                self.metas.instantiate_levels(&alpha)
            }
        };
        // SOUNDNESS: instantiate assigned metavars/levels in the branch body
        // before abstracting its hypothesis fvar. A branch such as `Or.inl h`
        // solves metavars that mention `then_fvar`; abstracting first would
        // leave a loose fvar in the closed `(fun h => …)`, rejected by the
        // kernel. Instantiating only substitutes decided values (no-op when
        // none) and is TCB-neutral — the kernel re-checks the declaration.
        let then_body = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&then_expr));
        let then_lambda = Expr::lam(
            BinderInfo::Default,
            prop_expr.clone(),
            then_body.abstract_fvar(then_fvar),
        );

        // Create the else branch: (fun h : ¬p => e), body checked against α.
        // `¬p` with the `Not` head, as `dite`'s `e : ¬c → α` and Lean's
        // elaborator state it: simp reads a negation off that head only.
        let not_prop = Expr::app(
            Expr::const_(Name::from_string("Not"), vec![]),
            prop_expr.clone(),
        );
        let else_fvar = self.push_local(witness_name.clone(), not_prop.clone());
        let else_result = self.elaborate_with_expected_type(else_br, Some(alpha.clone()));
        if std::env::var_os("CLEAN_UNIFY_TRACE").is_some() {
            eprintln!("dite-else: ok={} alpha={alpha:?}", else_result.is_ok());
        }
        let else_expr = match else_result {
            Ok(e) => e,
            Err(err) => {
                self.pop_local();
                return Err(err);
            }
        };
        self.pop_local();
        // SOUNDNESS: as with the then-branch, instantiate assigned
        // metavars/levels in the else body before abstracting its fvar so no
        // loose fvar leaks into the closed `(fun h : ¬p => …)`. TCB-neutral.
        let else_body = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&else_expr));
        let else_lambda = Expr::lam(
            BinderInfo::Default,
            not_prop,
            else_body.abstract_fvar(else_fvar),
        );

        // Build: dite p then_lambda else_lambda
        // Note: The Decidable instance is resolved implicitly by type class resolution
        // dite : {α : Sort u} → (p : Prop) → [Decidable p] → (p → α) → (¬p → α) → α
        //
        // Re-instantiate `α` (and hence the branch lambdas at emit time) so any
        // metavariable the else-branch elaboration just solved is reflected.
        let alpha = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&alpha));
        // `alpha` must itself inhabit a sort. Propagate a malformed inferred
        // branch type instead of silently manufacturing `Type 1`.
        let level = self.infer_sort(&alpha)?;
        let dite = Expr::const_(Name::from_string("dite"), vec![level]);
        let decidable_inst = self.resolve_decidable(&prop_expr)?;
        let result = Expr::apps(
            dite,
            [alpha, prop_expr, decidable_inst, then_lambda, else_lambda],
        );
        Ok(result)
    }

    /// Check if a constant is accessible from the current namespace context.
    ///
    /// - `private` declarations are module-local, as in Lean 4.8.0: another
    ///   module's are never accessible, and this module's are accessible
    ///   everywhere in it (`private def S.g` is `S.g` and `(s : S).g` at the
    ///   top level too). Without a `FileContext` the module is unknown, and a
    ///   private declaration is accessible only within its declaring
    ///   namespace (the constant's namespace prefix must match or be a parent
    ///   of the current `namespace_prefix`).
    /// - `protected` and `public` declarations are always accessible.
    pub(super) fn is_const_accessible(&self, name: &Name) -> bool {
        if !self.env.is_private(name) {
            return true;
        }
        // Another module's `private` declaration: Lean's private names are
        // module-local, so no namespace makes it accessible here.
        if self.foreign_private_decls.contains(name) {
            return false;
        }
        if self.private_module_known {
            return true;
        }
        let const_ns = crate::namespace::parent_name(name);
        if const_ns.is_anon() {
            self.namespace_prefix.is_anonymous()
        } else {
            crate::namespace::name_has_prefix(self.namespace_prefix.name(), &const_ns)
        }
    }

    /// Lean's PRIVATE STEP (`Lean/ResolveName.lean:100-111, 121-132,
    /// 174-178`): when `candidate` itself names nothing, this module's private
    /// declaration whose user-facing name is `candidate`
    /// (`_private.<main module>.0.<candidate>`), if it exists. Only the
    /// CURRENT module's prefix is ever built, so another module's private
    /// declaration is unreachable by construction (G21). `None` without a
    /// named module.
    pub(crate) fn private_candidate(&self, candidate: &Name) -> Option<Name> {
        let private = self.namespace_state.private_name(candidate)?;
        let declared = self.env.get_const(&private).is_some()
            || self.env.get_inductive(&private).is_some()
            || self.env.get_constructor(&private).is_some()
            || self.env.get_recursor(&private).is_some();
        (declared && self.is_const_accessible(&private)).then_some(private)
    }

    /// How `#check` / `#print` render private names here: Lean's
    /// `pp.privateNames`, read like every other option (local
    /// `set_option … in` first, then the file's).
    pub(crate) fn private_names_rendering(&self) -> crate::private_names::PrivateNames {
        crate::private_names::PrivateNames::from_option(self.get_option("pp.privateNames"))
    }

    /// Lean's `findMethod?` / `resolveQualifiedName` private step as a
    /// rewrite: `name` when the environment declares it, otherwise this
    /// module's private `name` when that exists, otherwise `name` unchanged
    /// (so the caller's own lookup fails as before). One helper for every
    /// `<head>.<field>` probe (G21).
    pub(crate) fn with_private_step(&self, name: Name) -> Name {
        if self.env.get_const(&name).is_some()
            || self.env.get_inductive(&name).is_some()
            || self.env.get_constructor(&name).is_some()
            || self.env.get_recursor(&name).is_some()
        {
            return name;
        }
        self.private_candidate(&name).unwrap_or(name)
    }

    /// The constant `name` denotes, seeing through a PRELUDE alias definition
    /// (`def true := Bool.true`, a value that is exactly another constant at
    /// its own universe parameters): two resolution candidates that denote
    /// the same constant are one interpretation, not an ambiguity, and Clean's
    /// native prelude ships such root-level aliases where Lean has `export`
    /// aliases of the one constant. Only the prelude's own
    /// ([`clean_kernel::Environment::is_prelude_alias`]): any other definition
    /// is a constant of its own to Lean, however its value reads — `def w :=
    /// N.w` and `N.w` with `open N` are "ambiguous, possible
    /// interpretations" (measured on Lean 4.8.0, round-25 `dedup_abbrev`,
    /// `dedup_diffns`, and `dedup_mynat`, where `w : MyNat := N.w` was merged
    /// with `N.w : Nat` and a false sum credited). Bounded, so a cycle cannot
    /// loop.
    fn canonical_constant(&self, name: &Name) -> Name {
        let mut current = name.clone();
        for _ in 0..8 {
            if !self.env.is_prelude_alias(&current) {
                break;
            }
            let Some(info) = self.env.get_const(&current) else {
                break;
            };
            if info.kind != ConstantKind::Definition {
                break;
            }
            let Some(value) = info.value.as_ref() else {
                break;
            };
            let ExprKind::Const(target, levels) = value.kind() else {
                break;
            };
            let own_params = levels.len() == info.level_params.len()
                && levels
                    .iter()
                    .zip(&info.level_params)
                    .all(|(level, param)| matches!(level, Level::Param(p) if p == param));
            if !own_params || target == &current {
                break;
            }
            current = target.clone();
        }
        current
    }

    /// What the identifier `name` denotes here, decided WITHOUT side effects.
    ///
    /// This is THE name-resolution order of the elaborator (`elab_ident` builds
    /// its term from it), exposed so that a recognizer of a well-known global
    /// head (`ite`, `not`, `flip`, `Eq`, `inferInstance`, …) can ask whether
    /// the head it matched by spelling actually RESOLVES to that global
    /// ([`Self::head_denotes_global`]). Matching the spelling alone rewrote a
    /// user's call of a LOCAL bound under that name into the global's meaning:
    /// `def g0 (ite : Bool → Nat → Nat → Nat) : Nat := ite true 1 2` computed
    /// `if true then 1 else 2`, and `g0 (fun _ _ c => c) = 1` was accepted by
    /// `rfl` (measured 2026-09-26; Lean 4.8.0: `2`). Keeping one resolution
    /// function for both is what stops the two from ever disagreeing.
    pub(in crate::infer) fn resolve_ident_target(&self, name: &SurfaceName) -> IdentTarget {
        self.resolve_ident_target_in(name, true)
    }

    /// [`Self::resolve_ident_target`] with the LOCAL stages (locals and
    /// metaprogram value bindings) skipped: what `name` denotes as a global,
    /// Lean's `resolveGlobalName` step of `resolveName`.
    pub(in crate::infer) fn resolve_global_ident_target(&self, name: &SurfaceName) -> IdentTarget {
        self.resolve_ident_target_in(name, false)
    }

    /// The declaration-time resolution of a notation template's free
    /// reference `name` (`crate::namespace::TemplateResolution`), when its
    /// template was declared in this file.
    pub(in crate::infer) fn template_resolution(
        &self,
        name: &SurfaceName,
    ) -> Option<&crate::namespace::TemplateResolution> {
        let site = name.template_origin()?.site?;
        self.namespace_state.template_resolution(site, name.name())
    }

    /// Pre-resolve, at a `notation` declaration, every spelling a use of its
    /// template resolves as a global (Lean's quotation pre-resolution; see
    /// `crate::namespace::TemplateResolution`), and record the result under
    /// the declaration's `site` for every later use to read.
    ///
    /// # Errors
    ///
    /// A template the hygiene walk refuses (`clean_parser::TemplateRefusal`):
    /// the notation declaration is refused.
    pub(in crate::infer) fn record_template_resolutions(
        &mut self,
        site: clean_parser::TemplateSiteId,
        pattern: &[clean_parser::NotationItem],
        expansion: &SurfaceExpr,
    ) -> Result<(), ElabError> {
        let operands: Vec<SurfaceName> = pattern
            .iter()
            .filter_map(|item| match item {
                clean_parser::NotationItem::Variable(v) => Some(v.clone()),
                clean_parser::NotationItem::Literal(_) => None,
            })
            .collect();
        self.record_template_site_resolutions(site, &operands, expansion)
    }

    /// [`Self::record_template_resolutions`] for a template over `operands`
    /// (none for a `macro`, whose operands are antiquotations).
    pub(in crate::infer) fn record_template_site_resolutions(
        &mut self,
        site: clean_parser::TemplateSiteId,
        operands: &[SurfaceName],
        expansion: &SurfaceExpr,
    ) -> Result<(), ElabError> {
        let spellings = clean_parser::template_free_reference_spellings(
            expansion,
            operands,
            self.namespace_prefix.name(),
        )
        .map_err(|refusal| {
            ElabError::MacroError(format!("notation template refused: {}", refusal.reason()))
        })?;
        self.record_template_site_spellings(site, spellings);
        Ok(())
    }

    /// Record, under the template declaration `site`, what each of
    /// `spellings` resolves to as a global here (see
    /// [`Self::record_template_resolutions`]).
    pub(in crate::infer) fn record_template_site_spellings(
        &mut self,
        site: clean_parser::TemplateSiteId,
        spellings: Vec<SurfaceName>,
    ) {
        let resolutions = self.template_spelling_resolutions(spellings);
        self.namespace_state.record_template_site(site, resolutions);
    }

    /// Make again, against this context's environment, the resolution this
    /// context records for the template declared at `site`, under
    /// `declared_under`: the namespace state where the template was declared,
    /// with the `open`s and `export`s in force there replayed against this
    /// environment. The new resolution replaces the recorded one; with no
    /// record there is nothing to make again.
    ///
    /// `crate::module_batch` needs it. Its plan applies a template's
    /// declaration in authored order, before any declaration of the batch
    /// exists and under none of its `open`s (each declaration replays those
    /// against the complete header index), so the record the declaration made
    /// is not what the template names: inside `namespace N`, after `def
    /// Satisfies …`, `notation:50 M " ⊨ " F:50 => Satisfies M F` recorded
    /// nothing for `Satisfies`, and every use of `⊨` was an unknown
    /// identifier (Trust 0.11.0's island lane, 2026-10-18; Lean 4.8.0
    /// pre-resolves it to `N.Satisfies`). Made again here, a template's free
    /// name resolves against the environment the declaration using it is
    /// elaborated in, as that declaration's own names do, but from where the
    /// template was declared: its namespace (each spelling's
    /// `TemplateOrigin`) and its `open`s, never the use's.
    pub(crate) fn re_resolve_template_site(
        &mut self,
        site: clean_parser::TemplateSiteId,
        declared_under: crate::namespace::NamespaceState,
    ) {
        let Some(recorded) = self.namespace_state.template_site(site) else {
            return;
        };
        let spellings: Vec<SurfaceName> = recorded
            .values()
            .map(|resolution| resolution.spelling.clone())
            .collect();
        // The declaration resolved under the namespace its spellings carry
        // (`scoped[NS]` makes it `NS`, not the namespace written around it).
        let declared_in = spellings
            .iter()
            .find_map(SurfaceName::template_origin)
            .map_or_else(
                || SurfaceName::from_name(declared_under.current_namespace().clone()),
                |origin| SurfaceName::from_name(origin.namespace.clone()),
            );
        let own_state = std::mem::replace(&mut self.namespace_state, declared_under);
        let own_prefix = std::mem::replace(&mut self.namespace_prefix, declared_in);
        let own_decl_site = self.decl_site_namespace.take();
        let resolutions = self.template_spelling_resolutions(spellings);
        self.decl_site_namespace = own_decl_site;
        self.namespace_state = own_state;
        self.namespace_prefix = own_prefix;
        self.namespace_state
            .replace_template_site(site, resolutions);
    }

    /// What each of `spellings` resolves to as a global here, by spelling
    /// (see [`Self::record_template_resolutions`]).
    fn template_spelling_resolutions(
        &self,
        spellings: Vec<SurfaceName>,
    ) -> HashMap<Name, crate::namespace::TemplateResolution> {
        let mut resolutions = HashMap::new();
        for spelling in spellings {
            // `spelling` carries no site, so this is resolved afresh here.
            let ident = match self.resolve_global_ident_target(&spelling) {
                IdentTarget::Global(global) => TemplateGlobal::Global(global),
                IdentTarget::BuiltinId => TemplateGlobal::BuiltinId,
                IdentTarget::BuiltinCond => TemplateGlobal::BuiltinCond,
                IdentTarget::Redirect(target) => TemplateGlobal::Redirect(target),
                IdentTarget::Ambiguous(candidates) => TemplateGlobal::Ambiguous(candidates),
                IdentTarget::RelativeConstructor
                | IdentTarget::MetaValue(_)
                | IdentTarget::Local(_)
                | IdentTarget::RootEscapeUnknown
                | IdentTarget::Unresolved => TemplateGlobal::Unresolved,
            };
            let resolution = crate::namespace::TemplateResolution {
                ident,
                chain: self.resolve_qualified_chain(&spelling),
                is_value: self.ident_resolves_to_value(&spelling),
                is_type_former: self.ident_resolves_to_type_former(&spelling),
                spelling,
            };
            resolutions.insert(resolution.spelling.name().clone(), resolution);
        }
        resolutions
    }

    /// Pre-resolve, at a `macro`/`macro_rules` declaration `site`, the free
    /// names of the expansion template `expansion` (see
    /// [`Self::record_template_resolutions`]).
    pub(in crate::infer) fn record_macro_template(
        &mut self,
        site: clean_parser::TemplateSiteId,
        expansion: &SurfaceExpr,
    ) -> Result<(), ElabError> {
        let spellings = crate::macro_integration::macro_template_spellings(
            expansion,
            self.namespace_prefix.name(),
        )
        .map_err(|error| ElabError::MacroError(error.to_string()))?;
        self.record_template_site_spellings(site, spellings);
        Ok(())
    }

    /// Whether a template declared here carries its expansions' macro scope:
    /// `false` under `set_option hygiene false`, where Lean's quotation adds
    /// no scope and pre-resolves nothing (`Lean/Elab/Quotation.lean`).
    pub(in crate::infer) fn templates_hygienic(&self) -> bool {
        !matches!(self.get_option("hygiene"), Some(Some(value)) if value == "false")
    }

    /// Whether the namespace-relative or `open`ed candidate `candidate` for
    /// the WRITTEN spelling `written` is visible: Lean's
    /// `resolveQualifiedName` (`Lean/ResolveName.lean`) passes over a
    /// `protected` declaration only when the written name is ATOMIC. So
    /// inside `namespace P`, `w` with a `protected def P.w` names the root
    /// `w` (Clean took `P.w`: `P.t = 1` was accepted, Lean 4.8.0: `5`), while
    /// under `open M` the dotted `Zed.x` does reach a `protected def
    /// M.Zed.x` (Clean refused it and read a field of a root `Zed`; both
    /// measured 2026-09-26).
    pub(in crate::infer) fn namespace_candidate_visible(
        &self,
        candidate: &Name,
        written: &SurfaceName,
    ) -> bool {
        !written.parent().is_anonymous() || !self.env.is_protected(candidate)
    }

    /// Whether Clean resolves the root spelling `full` as a Lean core global
    /// IN THIS ENVIRONMENT although no constant of that name is declared: a
    /// redirect or alias to a differently named constant that exists, the
    /// `cond` fallback over the prelude's `Bool`, or a core `T.elim` a
    /// recognizer supplies for the prelude's `T`. An environment without
    /// those (a bare kernel environment, like a Lean file with `prelude`)
    /// models none of them; so is `id`, whose fallback exists only where no
    /// `id` constant does. (In an environment built by the prelude every core
    /// name is refused anyway: `check_not_declared_in_lean_core`.)
    pub(in crate::infer) fn models_lean_core_global(&self, full: &Name) -> bool {
        if RECOGNIZER_SUPPLIED_CORE_GLOBALS
            .iter()
            .any(|name| Name::from_string(name) == *full)
        {
            let owner = SurfaceName::from_name(full.clone()).parent().into_name();
            return self.env.get_inductive(&owner).is_some();
        }
        match self.resolve_global_ident_target(&SurfaceName::global_constant(full.clone())) {
            IdentTarget::BuiltinCond => {
                self.env.get_inductive(&Name::from_string("Bool")).is_some()
            }
            IdentTarget::Redirect(_) => true,
            IdentTarget::Global(resolved) => resolved != *full,
            _ => false,
        }
    }

    /// Whether `name` denotes a global (constant, alias, prelude fallback or
    /// redirect) ignoring every local — Lean's `resolveGlobalName` returning
    /// a candidate with an empty field list.
    pub(in crate::infer) fn name_denotes_global(&self, name: &SurfaceName) -> bool {
        matches!(
            self.resolve_global_ident_target(name),
            IdentTarget::Global(_)
                | IdentTarget::BuiltinId
                | IdentTarget::BuiltinCond
                | IdentTarget::Redirect(_)
        )
    }

    fn resolve_ident_target_in(&self, name: &SurfaceName, consult_locals: bool) -> IdentTarget {
        // A leading-dot selector is syntax, not a local binding of the same Name.
        if name.is_relative_constructor() {
            return IdentTarget::RelativeConstructor;
        }
        // A reference spelled as a Lean 4.8.0 keyword (`nomatch`, `nofun`,
        // …; `SurfaceName::is_lean_keyword`) is that keyword in Lean, never a
        // name: it denotes no local, no constant and no alias, whatever this
        // file binds or declares with an escaped `«nomatch»`. Only Clean's
        // recognizer of the keyword (`nomatch e`, which asks
        // `head_denotes_global` and so accepts an unresolved head) gives it a
        // meaning; anywhere else it is an unknown identifier.
        if name.is_lean_keyword() {
            return IdentTarget::Unresolved;
        }
        // A template pattern variable, or a template reference to one
        // (`clean_parser::TemplateScope`), is the local its pattern bound —
        // or, when that pattern named a constructor where the template was
        // declared (Lean's `CollectPatternVars.processId`), that constructor.
        // It is never any other global: a pattern that bound a variable but
        // whose local this lookup cannot see is refused, not resolved to a
        // global of the same spelling.
        if name.template_scope().is_some() {
            if consult_locals {
                if let Some((fvar, _)) = self.lookup_local(name) {
                    return IdentTarget::Local(fvar);
                }
            }
            let written = name.clone().without_template_scope();
            return match self.resolve_ident_target_in(&written, false) {
                IdentTarget::Global(global) if self.names_pattern_constructor(&global) => {
                    IdentTarget::Global(global)
                }
                _ => IdentTarget::Unresolved,
            };
        }
        // Metaprogram value channel: a name bound to an already-elaborated kernel
        // `Expr` (e.g. `let t := inferType e`) splices that stored term directly,
        // bypassing the surface round-trip. The value was kernel-checked when it
        // was produced and is checked again wherever this body is used, so this
        // adds no trust surface (see `meta_query`).
        if consult_locals && !name.is_global_reference() && name.template_origin().is_none() {
            if let Some(value) = self.meta_value_bindings.get(name) {
                return IdentTarget::MetaValue(value.clone());
            }
        }

        // A notation's reference to a global constant (`SurfaceName::
        // global_path`: `and` for `&&`, `Eq` for `=`, `Prod` for `×`, …) is
        // the root constant, as Lean's pre-resolved quotation identifiers
        // are: neither a local (`lookup_local` refuses it) nor a same-named
        // member of the current namespace may capture it. Only if no root
        // constant exists does it fall through to the ROOT-level stages below
        // (export aliases, the prelude aliases and fallbacks) — never to a
        // local, a namespace member or an opened alias.
        if name.is_global_reference() {
            // A spelling that Lean exports as an ALIAS (`getElem!` is
            // `GetElem?.getElem!`, `insert` is `Insert.insert`, …) was
            // pre-resolved to the alias target where the notation was
            // declared, in Lean core: a user's own root constant of that
            // spelling, which Lean allows, does not capture it. Resolving the
            // root constant first made `[a, b][1]!` call a user `def getElem!`
            // (measured 2026-09-26; Lean 4.8.0 indexes the list).
            if let Some((_, target)) = PRELUDE_ALIASES
                .iter()
                .find(|(alias, _)| name.component_text() == Some(*alias))
            {
                let target_name = Name::from_string(target);
                if self.env.get_const(&target_name).is_some()
                    && self.is_const_accessible(&target_name)
                {
                    return IdentTarget::Global(target_name);
                }
            }
            let global = name.name().clone();
            if self.env.get_const(&global).is_some() && self.is_const_accessible(&global) {
                return IdentTarget::Global(global);
            }
            if self.env.get_inductive(&global).is_some()
                || self.env.get_constructor(&global).is_some()
                || self.env.get_recursor(&global).is_some()
            {
                return IdentTarget::Global(global);
            }
        }

        // Explicit root-namespace escape: `_root_.Bool` forces resolution at the
        // top level, bypassing the current namespace prefix and auto-implicit
        // binding. Strip the marker and resolve the remainder as a global
        // constant / inductive / constructor (TrustIr `Ty.isSigned : Ty →
        // _root_.Bool`, Track R). If the stripped name is not a known global we
        // fall through so the normal UnknownIdent diagnostics still fire.
        let root_name = name.qualify_under(&SurfaceName::default());
        if root_name.name() != name.name() {
            let global = root_name.into_name();
            if self.env.get_const(&global).is_some() && self.is_const_accessible(&global) {
                return IdentTarget::Global(global);
            }
            if self.env.get_inductive(&global).is_some()
                || self.env.get_constructor(&global).is_some()
                || self.env.get_recursor(&global).is_some()
            {
                return IdentTarget::Global(global);
            }
            // Lean's `resolveExact` also takes `_root_` to this module's
            // private declaration ("We also allow `_root` when accessing
            // private declarations").
            if let Some(private) = self.private_candidate(&global) {
                return IdentTarget::Global(private);
            }
            return IdentTarget::RootEscapeUnknown;
        }

        // First check locals (including any existing auto-implicits)
        if consult_locals {
            if let Some((fvar, _ty)) = self.lookup_local(name) {
                return IdentTarget::Local(fvar);
            }
        }

        // A notation template's free reference denotes what it resolved to
        // where the template was DECLARED (`TemplateResolution`), whatever
        // the namespace, `open`s and later declarations at the use site.
        if let Some(resolution) = self.template_resolution(name) {
            return match &resolution.ident {
                TemplateGlobal::Global(global) => IdentTarget::Global(global.clone()),
                TemplateGlobal::BuiltinId => IdentTarget::BuiltinId,
                TemplateGlobal::BuiltinCond => IdentTarget::BuiltinCond,
                TemplateGlobal::Redirect(target) => IdentTarget::Redirect(target),
                TemplateGlobal::Unresolved => IdentTarget::Unresolved,
                TemplateGlobal::Ambiguous(candidates) => IdentTarget::Ambiguous(candidates.clone()),
            };
        }

        // Global resolution order mirrors Lean's `resolveGlobalName`
        // (`Lean/ResolveName.lean`): candidates from the CURRENT NAMESPACE
        // OUTWARD win first (`resolveUsingNamespace` walks `Foo.Bar.name`,
        // then `Foo.name`), and only when that walk finds nothing are the
        // root-level exact name, aliases, and `open` decls consulted
        // (`resolveGlobalNameCore`'s anonymous-namespace stage). The previous
        // order checked the ROOT constant first, so inside `namespace Bar` a
        // bare `w` resolved to the root `w` instead of `Bar.w` — a silently
        // WRONG value the kernel then certified (gap sweep B03,
        // namespaces_scoping/p21).
        //
        // 1. Current-namespace-outward walk (#3410 + B03 reorder). Inside
        //    `namespace Foo.Bar`, try `Foo.Bar.name`, then `Foo.name`.
        //
        //    ONE candidate is deliberately passed over here: a DERIVED
        //    inherited-field projection (`crate::name_resolution::
        //    is_generated_inherited_projection`). Lean 4 declares no such
        //    constant — it composes `P.f (C.toP self)` on the fly per use site
        //    — so it must not join this candidate set and shadow the root /
        //    exported name the author wrote. It is remembered in `deferred` and
        //    used only if NOTHING else resolves, which keeps every name that
        //    resolves today resolving (Lean would report `unknown identifier`
        //    there instead; accepting more is safe — the kernel re-checks).
        let mut deferred_inherited_projection: Option<Name> = None;
        // A notation's global reference is pre-resolved at the ROOT (see the
        // `is_global_reference` stage above): no namespace member and no
        // opened alias of the same spelling may capture it (stages 1, 2, 2b).
        // Falling through to them made `!a` inside `namespace N` with a
        // `N.not` in scope call `N.not`, and `bif` call a `N.cond`, because
        // Clean's root `not`/`cond` are fallbacks below, not constants
        // (measured 2026-09-26; Lean 4.8.0 calls the root ones).
        // A user template's free reference resolves from the namespace the
        // template was DECLARED in (Lean pre-resolves it there), not the one
        // it is used in.
        let namespace_prefix = self.term_lookup_namespace(name);
        if !namespace_prefix.is_anonymous() && !name.is_global_reference() {
            let mut prefix = namespace_prefix;
            loop {
                let qualified_name = prefix.append(name).into_name();
                // Lean's `resolveQualifiedName` at this prefix: the
                // declaration `prefix.name` AND the aliases named
                // `prefix.name` (an `export` made inside this namespace, by
                // this file — `NamespaceState`, every target it still has —
                // or by another module — the environment's table) are ONE
                // candidate set; more than one distinct constant is ambiguous
                // (measured on Lean 4.8.0: with `def A.x := 2` and `namespace
                // A; export N.M (x); end A`, `x` inside `A` is "ambiguous").
                // An atomic spelling passes over a `protected` candidate
                // (`namespace_candidate_visible`).
                let mut aliased: Vec<Name> = Vec::new();
                for target in self
                    .namespace_state
                    .resolve_all(&qualified_name)
                    .into_iter()
                    .chain(self.env.export_alias_targets(&qualified_name))
                {
                    if self.is_const_accessible(target)
                        && self.namespace_candidate_visible(target, name)
                        && !aliased.contains(target)
                    {
                        aliased.push(target.clone());
                    }
                }
                let mut declared = false;
                if self.is_const_accessible(&qualified_name)
                    && self.namespace_candidate_visible(&qualified_name, name)
                {
                    if self.env.get_const(&qualified_name).is_some() {
                        if crate::name_resolution::is_generated_inherited_projection(
                            self.env,
                            &qualified_name,
                        ) {
                            if deferred_inherited_projection.is_none() {
                                deferred_inherited_projection = Some(qualified_name.clone());
                            }
                        } else {
                            declared = true;
                        }
                    } else if self.env.get_inductive(&qualified_name).is_some()
                        || self.env.get_constructor(&qualified_name).is_some()
                        || self.env.get_recursor(&qualified_name).is_some()
                    {
                        // Namespace-relative inductives/constructors/recursors
                        // may not carry a plain constant entry (mirrors the
                        // `_root_.` branch above).
                        declared = true;
                    }
                }
                // Lean's `resolveQualifiedName`: no `prefix.name` declared,
                // so this module's private `prefix.name` is the candidate.
                let mut declared_name = qualified_name.clone();
                if !declared && deferred_inherited_projection.as_ref() != Some(&qualified_name) {
                    if let Some(private) = self.private_candidate(&qualified_name) {
                        if self.namespace_candidate_visible(&private, name) {
                            declared = true;
                            declared_name = private;
                        }
                    }
                }
                if declared {
                    aliased.retain(|target| target != &declared_name);
                }
                match (declared, aliased.len()) {
                    (true, 0) => return IdentTarget::Global(declared_name),
                    (false, 1) => return IdentTarget::Global(aliased.remove(0)),
                    (false, 0) => {}
                    (declared, _) => {
                        if declared {
                            aliased.insert(0, declared_name);
                        }
                        return IdentTarget::Ambiguous(aliased);
                    }
                }
                // Walk up: "Foo.Bar" -> "Foo", then stop
                prefix = prefix.parent();
                if prefix.is_anonymous() {
                    break;
                }
            }
        }

        // Lean's `resolveExact`: a DOTTED name that exists as written wins
        // before the root stage's aliases and `open`s (measured on Lean
        // 4.8.0: `def K.x := 3` with `namespace K; export N.M (x); end K`
        // gives `K.x = 3`).
        if !name.parent().is_anonymous() {
            let exact = name.name().clone();
            if self.is_const_accessible(&exact) && self.env.get_const(&exact).is_some() {
                return IdentTarget::Global(exact);
            }
            if self.env.get_const(&exact).is_none() {
                if let Some(private) = self.private_candidate(&exact) {
                    return IdentTarget::Global(private);
                }
            }
        }

        // 2-3. The ROOT stage (Lean's `resolveGlobalName` once the namespace
        //      walk found nothing): the `open` declarations (the frozen alias
        //      table, every target a short name still has — explicit `open
        //      Foo (x)`, renaming, and simple opens — and the LIVE walk of the
        //      simple opens, with the aliases named `<ns>.<name>` of each
        //      opened namespace), the imported `export` aliases (every
        //      target) and the root-level exact constant are ONE candidate
        //      set. More than one DISTINCT candidate (after
        //      `canonical_constant`) is Lean's "ambiguous, possible
        //      interpretations" (measured on Lean 4.8.0: `def w := 2`, `N.w :=
        //      3`, `open N`, `w = 3` is ambiguous; so is `open A B` with `A.x`
        //      and `B.x`; round-25 `export_ns`: `namespace K; export N (x); end
        //      K`, a root `x`, `open K`: `x` is ambiguous); Clean does not
        //      elaborate overloads, so it refuses rather than pick one
        //      ([`IdentTarget::Ambiguous`]). Clean used to return the first hit
        //      (alias, then open walk, then root), crediting `w = 3`.
        //
        //      The live walk exists because `process_single_open`
        //      materializes the alias table at `open` time, so a declaration
        //      added to the namespace LATER in the file is missing from it
        //      (Mathlib `Function.swap₂`); it applies the alias loop's
        //      admission filter (hidden suffixes; `protected` members for an
        //      atomic spelling, `namespace_candidate_visible`). A notation's
        //      global reference (`is_global_reference`) is resolved at the
        //      root: no alias or opened member may capture it. Imported
        //      `export` aliases (`Lean.aliasExtension`) make Lean core's
        //      `export Decidable (isTrue isFalse decide)` short names
        //      resolvable at the root.
        {
            let mut candidates: Vec<Name> = Vec::new();
            let push = |ctx: &Self, candidate: Name, candidates: &mut Vec<Name>| {
                let canonical = ctx.canonical_constant(&candidate);
                if !candidates
                    .iter()
                    .any(|c| ctx.canonical_constant(c) == canonical)
                {
                    candidates.push(candidate);
                }
            };
            if !name.is_global_reference() {
                let aliased: Vec<Name> = self
                    .namespace_state
                    .resolve_all(name.name())
                    .into_iter()
                    .cloned()
                    .collect();
                for qualified in aliased {
                    if self.is_const_accessible(&qualified) {
                        push(self, qualified, &mut candidates);
                    }
                }
                for (open_ns, hidden) in self.namespace_state.open_namespaces_with_hidden() {
                    let candidate = crate::namespace::append_names(open_ns, name.name());
                    if hidden.iter().any(|h| h == name.name()) {
                        continue;
                    }
                    if self.env.get_const(&candidate).is_some()
                        && self.namespace_candidate_visible(&candidate, name)
                        && self.is_const_accessible(&candidate)
                    {
                        push(self, candidate.clone(), &mut candidates);
                    } else if self.env.get_const(&candidate).is_none() {
                        // `resolveQualifiedName`'s private step at `open_ns`.
                        if let Some(private) = self.private_candidate(&candidate) {
                            if self.namespace_candidate_visible(&private, name) {
                                push(self, private, &mut candidates);
                            }
                        }
                    }
                    let mut aliased: Vec<Name> = self
                        .namespace_state
                        .resolve_all(&candidate)
                        .into_iter()
                        .cloned()
                        .collect();
                    aliased.extend(
                        self.env
                            .export_alias_targets(&candidate)
                            .into_iter()
                            .cloned(),
                    );
                    for target in aliased {
                        if self.is_const_accessible(&target)
                            && self.namespace_candidate_visible(&target, name)
                        {
                            push(self, target, &mut candidates);
                        }
                    }
                }
                // `open Foo (Bar)` then `Bar.a`: an explicit open whose short
                // name is a proper prefix of the written one (Lean's
                // `resolveOpenDecls`, `id.replacePrefix openedId resolvedId`).
                for candidate in self
                    .namespace_state
                    .explicit_open_prefix_targets(name.name())
                {
                    if self.is_known_accessible_global(&candidate) {
                        push(self, candidate, &mut candidates);
                    }
                }
            }
            // A notation's global reference is not captured by an `export`
            // alias either — this file's own `export MX (not)` included,
            // which the environment's alias table now holds — any more than
            // by an `open`: Lean resolved it where the notation was declared
            // (`!b` is the core `not`, `∅` the core `EmptyCollection`).
            if !name.is_global_reference() {
                let alias_key = name.name().clone();
                let alias_targets: Vec<Name> = self
                    .env
                    .export_alias_targets(&alias_key)
                    .into_iter()
                    .cloned()
                    .collect();
                for target in alias_targets {
                    if self.is_const_accessible(&target)
                        && self.namespace_candidate_visible(&target, name)
                    {
                        push(self, target, &mut candidates);
                    }
                }
            }
            let const_name = name.name().clone();
            // `resolveGlobalName`'s root stage takes this module's private
            // `name` beside the public one.
            if let Some(private) = self.private_candidate(&const_name) {
                push(self, private, &mut candidates);
            }
            if self.env.get_const(&const_name).is_some() && self.is_const_accessible(&const_name) {
                push(self, const_name, &mut candidates);
            }
            if candidates.len() > 1 {
                return IdentTarget::Ambiguous(candidates);
            }
            if let Some(only) = candidates.pop() {
                return IdentTarget::Global(only);
            }
        }

        // Monad typeclass alias fallback (#3435) and prelude-export fallback (#3527).
        //
        // Lean 4 supplies bare `pure`/`bind`/... through `open Pure`/`open Bind`
        // which the Monad typeclass does implicitly. It additionally exports
        // inductive-type constructors via `export Option (some none)`,
        // `export Sum (inl inr)`, etc. in `Init/Prelude.lean`, so users write
        // `some x` rather than `Option.some x`.
        //
        // Our elaborator has no open-prelude step, so a bare `pure`, `some`,
        // etc. otherwise falls through to auto-implicit and gets bound as a
        // fresh free variable whose type inherits the expected type. That
        // silently shadows the real constant and produces errors such as
        // `UnknownFVar(FVarId(N))` (the auto-implicit fvar references a binder
        // that is no longer in scope by the time the term is re-checked) or
        // type mismatches where an auto-implicit domain unifies with an
        // unrelated value type (see #3435).
        //
        // The fix is to treat these names as aliases for their underlying
        // constants when (a) the identifier is not found as any other
        // constant / local and (b) the target constant actually exists.
        // We only handle identifiers with clear typeclass / prelude ownership
        // to avoid accidentally shadowing user-defined names.
        for (alias, target) in PRELUDE_ALIASES {
            if name.component_text() == Some(*alias) {
                let target_name = Name::from_string(target);
                if self.env.get_const(&target_name).is_some()
                    && self.is_const_accessible(&target_name)
                {
                    return IdentTarget::Global(target_name);
                }
            }
        }

        // Core combinator `id`, absent from clean's prelude (elaborator Brick E1).
        //
        // Lean's `Init/Prelude.lean` defines `@[reducible] def id {α : Sort u}
        // (a : α) : α := a` and exports it at the root. Clean's prelude never
        // registers it, so a bare `id` reached here (no local, no constant, no
        // alias) otherwise falls through to auto-implicit and is bound as a fresh
        // free variable typed `Sort u`; applying an explicit argument to a
        // `Sort u`-typed head then fails `TooManyArguments { func_type:
        // "Sort(u)" }` — the standalone `id 5` gap, and every `id $ x` / `id <| x`
        // / `x |> id` reduction (all of which desugar to `App(id, [x])`).
        //
        // Resolve it here to the definitional identity lambda `fun {α : Sort u}
        // (a : α) => a`. Placing the check AFTER local / constant / namespace /
        // alias resolution means a user-defined `id` (the integration-test
        // `def id (A : Type) (x : A) := x`) or a binder named `id` still wins;
        // this only fires when `id` is otherwise unresolved. The application
        // elaborator then inserts the leading implicit `{α}` as a metavariable
        // through the ordinary `insert_implicit_args` path (identical to how the
        // registered `HAdd.hAdd`/`id zero` heads flow), applies the explicit
        // argument, and the kernel re-checks the resulting β-redex — so this adds
        // no trust and no new constant: `(fun a => a) x` reduces to `x`.
        if name.component_text() == Some("id") {
            return IdentTarget::BuiltinId;
        }

        // Core combinator `cond`, absent from clean's prelude (like `id` above).
        //
        // Lean's `Init/Prelude.lean` defines `@[macro_inline] def cond {α : Sort u}
        // (c : Bool) (x y : α) : α := match c with | true => x | false => y`, exported
        // at the root. Clean never registers it, so a bare `cond` reaching here (no
        // local, no constant, no alias) otherwise falls through to auto-implicit and
        // is bound as a fresh free variable, then `cond true 1 0` fails
        // `TooManyArguments`/`UnknownIdent`.
        //
        // Resolve it to the definitional term
        //   fun {α : Sort u} (c : Bool) (x y : α) => @Bool.rec.{u} (fun _ => α) y x c
        // `Bool.rec`'s minors are in constructor order (false, then true), so the
        // false-case is `y` (`cond false x y = y`) and the true-case is `x`
        // (`cond true x y = x`); the recursor's ι-rules give exactly those two
        // computation rules, which the kernel re-checks (the `cond_true`/`cond_false`
        // `rfl` tests). Placed AFTER local / constant / alias resolution, so a
        // user-defined `cond` — or a future prelude registration — still wins; this
        // only fires when `cond` is otherwise unresolved, and `add_decl` re-checks
        // the resulting β/ι-redex, so it adds no trust and no new constant.
        if name.component_text() == Some("cond") {
            return IdentTarget::BuiltinCond;
        }

        // Bare `default`, absent from clean's prelude as a root export. Lean's
        // `Init/Prelude.lean` defines `@[reducible] def default {α} [Inhabited α]
        // : α := Inhabited.default`, exported at the root — i.e. `default` IS
        // `@Inhabited.default`. Clean registers `Inhabited.default` but not the
        // bare alias, so a correctly-`deriving Inhabited` structure is unusable:
        // `(default : T)` reaches here unresolved and is auto-bound as a fresh
        // free variable (`UnknownIdent "default"` / a leaked fvar in `(default :
        // T).field`). Resolve it to the registered `Inhabited.default` by
        // delegating to the ordinary constant path — the leading `{α}` implicit
        // (from the expected type) and the `[Inhabited α]` instance are then
        // inserted/synthesized exactly as for an explicit `Inhabited.default`
        // (verified to reduce: `(Inhabited.default : S).field = <field default>`).
        // Placed AFTER local / constant / alias resolution, so a user-defined
        // `default` still wins; only fires when `default` is otherwise unresolved,
        // and adds no new constant or trust (it names the registered projection).
        if name.component_text() == Some("default")
            && self
                .env
                .get_const(&Name::from_string("Inhabited.default"))
                .is_some()
        {
            return IdentTarget::Redirect("Inhabited.default");
        }

        // Bare `not`, a root export in Lean's `Init/Prelude.lean` (`def not :
        // Bool → Bool | true => false | false => true`) — `not` IS `Bool.not`.
        // Clean registers `Bool.not` but not the bare alias, so `not b` reached
        // here unresolved and was auto-bound as a fresh free variable
        // (`UnknownIdent "not"`, or `TooManyArguments` once applied). Resolve it
        // to the registered `Bool.not` — a plain `Bool → Bool` function whose
        // application reduces by rfl. Placed AFTER local / constant / alias
        // resolution, so a user-defined `not` still wins; only fires when `not`
        // is otherwise unresolved, and adds no new constant or trust (it names
        // the registered function). Same shape as the `default`/`cond` aliases.
        if name.component_text() == Some("not")
            && self.env.get_const(&Name::from_string("Bool.not")).is_some()
        {
            return IdentTarget::Redirect("Bool.not");
        }

        // Bare `xor`, a root export in Lean's `Init/Prelude.lean` (`def xor :
        // Bool → Bool → Bool`) — `xor` IS `Bool.xor`. Same shape as `not`
        // above: clean registers `Bool.xor` but not the bare alias, so `xor a b`
        // reached here unresolved. Resolve it to `Bool.xor` (a plain
        // `Bool → Bool → Bool` whose application reduces by rfl). Placed after
        // local / constant / alias resolution, so a user-defined `xor` wins.
        if name.component_text() == Some("xor")
            && self.env.get_const(&Name::from_string("Bool.xor")).is_some()
        {
            return IdentTarget::Redirect("Bool.xor");
        }

        // Bare `compare`, a root export in Lean's `Init/Data/Ord` (`export Ord
        // (compare)`) — `compare` IS `@Ord.compare : {α} → [Ord α] → α → α →
        // Ordering`. Clean registers the `Ord.compare` projection (reducible,
        // unfolds through the `Ord` instance) but not the bare alias, so
        // `compare a b` reached here unresolved and was auto-bound as a fresh
        // free variable, then over-applied (`TooManyArguments`). Resolve it to
        // `Ord.compare`; the elaborator then inserts + synthesizes the implicit
        // `{α}` and instance `[Ord α]` (e.g. `instOrdNat`) exactly as for an
        // explicit `Ord.compare a b` — verified to reduce: `compare (2:Nat) 7`
        // ≡ `Ordering.lt`. Placed AFTER local / constant / alias resolution, so
        // a user-defined `compare` still wins; adds no new constant or trust.
        // Same shape as the `default` / `not` / `xor` aliases (and mirrors the
        // registered `min`/`max` := `Min.min`/`Max.max` surface aliases).
        if name.component_text() == Some("compare")
            && self
                .env
                .get_const(&Name::from_string("Ord.compare"))
                .is_some()
        {
            return IdentTarget::Redirect("Ord.compare");
        }

        // Bare `hash`, a root export in Lean's `Init/Prelude.lean` (`export
        // Hashable (hash)`) — `hash` IS `@Hashable.hash : {α} → [Hashable α]
        // → α → Nat` (Nat-valued in Clean's prelude; Lean's is UInt64 — a
        // pre-existing kernel divergence, see `data_typeclasses_hashable`).
        // Same shape as the `compare` alias above: resolve to `Hashable.hash`
        // and let the elaborator insert + synthesize the implicit `{α}` and
        // `[Hashable α]` instance (prelude `instHashableNat` / a derived
        // instance). Placed AFTER local / constant / alias resolution, so a
        // user-defined `hash` still wins; adds no new constant or trust.
        if name.component_text() == Some("hash")
            && self
                .env
                .get_const(&Name::from_string("Hashable.hash"))
                .is_some()
        {
            return IdentTarget::Redirect("Hashable.hash");
        }

        // Last resort BEFORE auto-implicit: the derived inherited-field
        // projection the namespace walk passed over. Reached only when the
        // root/exported name it would have shadowed does not exist, so this
        // can only ever ACCEPT what already resolved before this change.
        if let Some(qualified_name) = deferred_inherited_projection {
            if self.env.get_const(&qualified_name).is_some() {
                return IdentTarget::Global(qualified_name);
            }
        }

        IdentTarget::Unresolved
    }

    /// Whether the surface head `name`, spelled as the global `global`
    /// (`"ite"`, `"not"`, `"Eq"`, …), RESOLVES here to that global's meaning.
    ///
    /// A recognizer that rewrites a well-known global head (`ite c t e` to
    /// `elab_if`, `not b` to `Bool.not`, `(flip g) a b` to `g b a`, …) may
    /// fire only when this holds. It is false whenever the spelling denotes
    /// something else at this point: a local (parameter, `let`, `fun`,
    /// pattern variable), a metaprogram value, or a DIFFERENT constant (a
    /// namespace member or an opened alias of the same spelling). A
    /// compiler-authored [`SurfaceName::global_path`] head never resolves to
    /// a local, so it passes whenever it names the global. The spelling's
    /// own prelude fallbacks (`not` ↦ `Bool.not`, `id`, `cond`) and a
    /// spelling that resolves to nothing (a global Clean's prelude lacks,
    /// such as `Function.comp`, which the recognizer itself supplies) keep
    /// the global meaning.
    pub(in crate::infer) fn head_denotes_global(&self, name: &SurfaceName, global: &str) -> bool {
        self.head_denotes_global_name(name, SurfaceName::generated_path(global).name())
    }

    /// [`Self::head_denotes_global`] for a global given as a kernel `Name`.
    pub(in crate::infer) fn head_denotes_global_name(
        &self,
        name: &SurfaceName,
        global: &Name,
    ) -> bool {
        if name.name() != global || name.is_relative_constructor() {
            return false;
        }
        // A Clean extension head (`Function.uncurry`) that the USER declared
        // is the user's constant, never the recognizer's meaning.
        if Self::is_clean_extension_head(global) && self.env.get_const(global).is_some() {
            return false;
        }
        match self.resolve_ident_target(name) {
            IdentTarget::Global(resolved) => {
                &resolved == global
                    || PRELUDE_ALIASES.iter().any(|(alias, target)| {
                        name.component_text() == Some(*alias)
                            && resolved == Name::from_string(target)
                    })
            }
            IdentTarget::BuiltinId
            | IdentTarget::BuiltinCond
            | IdentTarget::Redirect(_)
            | IdentTarget::Unresolved => true,
            IdentTarget::RelativeConstructor
            | IdentTarget::MetaValue(_)
            | IdentTarget::Local(_)
            | IdentTarget::RootEscapeUnknown
            | IdentTarget::Ambiguous(_) => false,
        }
    }

    /// Elaborate the parser's `outParam e` / `semiOutParam e` wrapper
    /// (`marker` is the head's spelling) as an ordinary application, retaining
    /// the global marker for class metadata and honoring local shadowing.
    pub(in crate::infer) fn elab_out_param_marker(
        &mut self,
        span: clean_parser::Span,
        marker: &str,
        inner: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        let head = SurfaceName::component(marker, false);
        // Preserve the reducible marker in the registered telescope. Erasing
        // it here loses class output metadata and makes dependent-parameter
        // validation impossible. Ordinary application also honors shadowing.
        let applied = SurfaceExpr::App(
            span,
            Box::new(SurfaceExpr::Ident(span, head)),
            vec![SurfaceArg::positional(inner.clone())],
        );
        self.elaborate(&applied)
    }

    fn is_clean_extension_head(global: &Name) -> bool {
        CLEAN_EXTENSION_HEADS
            .iter()
            .any(|head| Name::from_string(head) == *global)
    }

    /// Lean's resolution of the WRITTEN dotted identifier `base.field` (the
    /// parser splits it into `Proj(Ident(base), field)`, or a chain of such
    /// projections when `base` is itself dotted; a parenthesized
    /// `(base).field` is a projection of a term and never reaches here).
    ///
    /// Lean elaborates the identifier as one name (`resolveName`,
    /// `Lean/Elab/Term.lean`):
    /// 1. `resolveLocalName` walks the name from its full spelling down to
    ///    its leading component, setting `globalDeclFound` as soon as the
    ///    spelling at hand (the full one, or any shorter prefix INCLUDING the
    ///    leading component alone) resolves as a global. At the leading
    ///    component a local makes the identifier a projection of that local
    ///    — but a `where`/`let rec` AUXILIARY declaration is skipped once
    ///    `globalDeclFound` holds (`skipAuxDecl`), and an ordinary local of
    ///    that spelling further out is then the receiver.
    /// 2. Otherwise `resolveGlobalName` tries the FULL name first
    ///    (namespace-outward, exact, `open`s, `export` aliases) and only then
    ///    shorter prefixes with the rest as projections — so a global
    ///    `base.field` wins over a field of a global VALUE `base` (a
    ///    namespace member included).
    ///
    /// Clean used to skip the auxiliary declaration only when the FULL
    /// spelling was a global, so with a global `def Foo : S := ⟨5⟩` and
    /// `where Foo : S := ⟨9⟩`, `Foo.x` read the auxiliary declaration
    /// (`q1 = 9` accepted; Lean 4.8.0: 5), and `true.toNat` under `where true
    /// : Bool := false` read `false`. It also resolved the full spelling
    /// without the live `open` walk, so under `open M` a `M.Zed.x` lost to a
    /// field of a root value `Zed` (measured 2026-09-26).
    ///
    /// A global "exists" here when Clean resolves the spelling as a global
    /// ([`Self::name_denotes_global`], [`Self::resolve_qualified_chain`]) or
    /// when it is a Lean core constant a recognizer supplies
    /// ([`RECOGNIZER_SUPPLIED_CORE_GLOBALS`]).
    pub(in crate::infer) fn resolve_dotted_ident(
        &self,
        base: &SurfaceName,
        field: &SurfaceName,
    ) -> DottedIdent {
        if base.is_relative_constructor()
            || field.is_relative_constructor()
            || base.is_anonymous()
            || field.is_anonymous()
        {
            return DottedIdent::Field;
        }
        // The spellings `resolveLocalName` visits, longest first:
        // `A.b.c`, `A.b`, `A`.
        let full = base.append(field);
        let mut prefixes = vec![full.clone()];
        loop {
            let parent = prefixes[prefixes.len() - 1].parent();
            if parent.is_anonymous() {
                break;
            }
            prefixes.push(parent);
        }
        let leading = prefixes[prefixes.len() - 1].clone();
        if !leading.is_global_reference() && self.meta_value_bindings.contains_key(&leading) {
            return DottedIdent::Field;
        }
        let full_global = self.dotted_global(&full);
        let Some((innermost, _)) = self.lookup_local(&leading) else {
            return match full_global {
                Some(DottedGlobal::Found(name)) => DottedIdent::Global(name),
                Some(DottedGlobal::CoreUnavailable(name)) => DottedIdent::CoreUnavailable(name),
                None => DottedIdent::Field,
            };
        };
        if !self.local_is_aux_decl(innermost) {
            return DottedIdent::Field;
        }
        let global_found = full_global.is_some()
            || prefixes[1..].iter().any(|prefix| {
                self.dotted_global(prefix).is_some() || self.name_denotes_global(prefix)
            });
        if !global_found {
            // No global of any of these spellings: the auxiliary declaration
            // is the receiver.
            return DottedIdent::Field;
        }
        if let Some((ordinary, _)) = self.lookup_local_skipping_aux(&leading) {
            return DottedIdent::FieldOfShadowedLocal(ordinary);
        }
        match full_global {
            Some(DottedGlobal::Found(name)) => return DottedIdent::Global(name),
            Some(DottedGlobal::CoreUnavailable(name)) => return DottedIdent::CoreUnavailable(name),
            None => {}
        }
        // The longest global prefix is the receiver; the rest are fields.
        for (depth, prefix) in prefixes.iter().enumerate().skip(1) {
            let receiver = match self.dotted_global(prefix) {
                Some(DottedGlobal::Found(name)) => Some(name),
                Some(DottedGlobal::CoreUnavailable(name)) => {
                    return DottedIdent::CoreUnavailable(name);
                }
                None => match self.resolve_global_ident_target(prefix) {
                    IdentTarget::Global(name) => Some(name),
                    _ if self.name_denotes_global(prefix) => {
                        return DottedIdent::UnsupportedGlobalReceiver;
                    }
                    _ => None,
                },
            };
            if let Some(receiver) = receiver {
                let fields = prefixes[..depth]
                    .iter()
                    .rev()
                    .map(SurfaceName::last_component)
                    .collect();
                return DottedIdent::FieldOfGlobal { receiver, fields };
            }
        }
        DottedIdent::UnsupportedGlobalReceiver
    }

    /// What the (possibly dotted) `spelling` names as a GLOBAL, in Lean's
    /// `resolveGlobalName` order for a non-atomic name
    /// (`Lean/ResolveName.lean`): namespace-outward candidates first, then
    /// the EXACT root declaration, which for a dotted name wins alone
    /// (`resolveExact`), and only then `open` declarations and aliases. So
    /// `open M in Iff.elim …` with a user `M.Iff.elim` still names Lean core's
    /// `Iff.elim` (Lean 4.8.0 refuses the application), and `Function.comp`
    /// names the root one. A Lean core constant that Clean's prelude neither
    /// declares nor supplies through a recognizer is reported as such rather
    /// than silently replaced by an opened one.
    fn dotted_global(&self, spelling: &SurfaceName) -> Option<DottedGlobal> {
        // An atomic spelling has no `resolveExact` stage (Lean combines its
        // root declaration with the `open`s); it keeps the identifier
        // resolver's order.
        if spelling.parent().is_anonymous()
            || spelling.template_origin().is_some()
            || spelling.is_global_reference()
            || spelling.qualify_under(&SurfaceName::default()).name() != spelling.name()
        {
            return self
                .resolve_qualified_chain(spelling)
                .or_else(|| match self.resolve_global_ident_target(spelling) {
                    IdentTarget::Global(name) => Some(name),
                    _ => None,
                })
                .map(DottedGlobal::Found);
        }
        // 1. The current namespace outward (with the aliases declared in
        //    those namespaces).
        let mut prefix = self.term_lookup_namespace(spelling);
        while !prefix.is_anonymous() {
            let qualified = prefix.append(spelling).into_name();
            let declared = self.with_private_step(qualified.clone());
            if self.is_known_accessible_global(&declared) {
                return Some(DottedGlobal::Found(declared));
            }
            if let Some(target) = self.namespace_state.resolve(&qualified) {
                if self.is_known_accessible_global(target) {
                    return Some(DottedGlobal::Found(target.clone()));
                }
            }
            prefix = prefix.parent();
        }
        // 2. The exact root declaration (or this module's private one).
        let root = self.with_private_step(spelling.name().clone());
        if self.is_known_accessible_global(&root) {
            return Some(DottedGlobal::Found(root));
        }
        if RECOGNIZER_SUPPLIED_CORE_GLOBALS
            .iter()
            .any(|name| Name::from_string(name) == root)
        {
            return Some(DottedGlobal::Found(root));
        }
        // 3. `open` declarations, aliases and imported `export`s — reached
        //    only when no root declaration exists. Where Lean's root one is a
        //    core constant Clean lacks, an opened one would silently stand in
        //    for it: refused instead.
        let opened = self.resolve_qualified_chain(spelling).or_else(|| {
            match self.resolve_global_ident_target(spelling) {
                IdentTarget::Global(name) => Some(name),
                _ => None,
            }
        })?;
        if crate::lean_core_names::is_lean_init_constant(&root) {
            return Some(DottedGlobal::CoreUnavailable(root));
        }
        Some(DottedGlobal::Found(opened))
    }

    /// [`Self::head_denotes_global`] for an application head that may be
    /// written dotted: `Function.comp` parses as the projection
    /// `Function .comp`, which is resolved as ONE identifier by Lean's rules
    /// ([`Self::resolve_dotted_ident`]): a field of an ordinary local
    /// `Function`, but the global `Function.comp` even when a `where`/`let
    /// rec`-bound `Function` or a namespace member `N.Function` is in scope.
    pub(in crate::infer) fn func_denotes_global(&self, func: &SurfaceExpr, global: &str) -> bool {
        self.func_denotes_global_name(func, SurfaceName::generated_path(global).name())
    }

    /// [`Self::func_denotes_global`] for a global given as a kernel `Name`.
    pub(in crate::infer) fn func_denotes_global_name(
        &self,
        func: &SurfaceExpr,
        global: &Name,
    ) -> bool {
        match Self::unwrap_surface_parens(func) {
            SurfaceExpr::Ident(_, name) => self.head_denotes_global_name(name, global),
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => match base.as_ref() {
                SurfaceExpr::Ident(_, namespace) => {
                    let written = namespace.append(field);
                    if written.name() != global {
                        return false;
                    }
                    // A local spelled with the whole dotted name is that local.
                    if self.lookup_local(&written).is_some() {
                        return false;
                    }
                    match self.resolve_dotted_ident(namespace, field) {
                        DottedIdent::Global(resolved) => {
                            &resolved == global && !Self::is_clean_extension_head(global)
                        }
                        // Lean core's constant, which the recognizer for
                        // `global` is Clean's supply of.
                        DottedIdent::CoreUnavailable(resolved) => {
                            &resolved == global && !Self::is_clean_extension_head(global)
                        }
                        DottedIdent::FieldOfShadowedLocal(_)
                        | DottedIdent::FieldOfGlobal { .. }
                        | DottedIdent::UnsupportedGlobalReceiver => false,
                        // Nothing named `base.field` exists. Only a Clean
                        // extension head may then be supplied, and only when
                        // `base` is no value it could be a field of.
                        DottedIdent::Field => {
                            Self::is_clean_extension_head(global)
                                && self.lookup_local(namespace).is_none()
                                && (!self.ident_resolves_to_value(namespace)
                                    || self.ident_resolves_to_type_former(namespace))
                        }
                    }
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// Lean's overload resolution for an identifier with several distinct
    /// root-stage candidates ([`IdentTarget::Ambiguous`]): the term `build`
    /// makes of the identifier is elaborated once per candidate — each
    /// attempt with the head naming exactly that global
    /// ([`SurfaceName::global_constant`]) and rolled back, whatever its
    /// outcome — and when exactly ONE candidate elaborates, the term is
    /// elaborated with it. Measured on Lean 4.8.0: `export MX (outParam)`
    /// with `def MX.outParam (n : Nat) : Nat`, `outParam a + 1` is
    /// `MX.outParam` (the core `outParam : Sort u → Sort u` does not
    /// elaborate there), while two candidates of one type (`_root_.k` and
    /// `A.k : Nat` under `open A`) stay "ambiguous, possible
    /// interpretations". Nothing is credited that the chosen candidate's own
    /// elaboration and the kernel do not check.
    pub(in crate::infer) fn elab_overloaded(
        &mut self,
        span: clean_parser::Span,
        candidates: &[Name],
        build: impl Fn(SurfaceExpr) -> SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        let head = |candidate: &Name| {
            SurfaceExpr::Ident(span, SurfaceName::global_constant(candidate.clone()))
        };
        let mut elaborating: Vec<&Name> = Vec::new();
        for candidate in candidates {
            let attempt = build(head(candidate));
            let mut succeeded = false;
            // Always rolled back: the probe only asks whether it elaborates.
            let _ = self.with_local_scope_rollback(|ctx| {
                // Only whether it elaborates matters; the term is discarded.
                let _ = ctx.elaborate(&attempt)?;
                succeeded = true;
                Err::<(), _>(ElabError::InternalInvariant("overload probe".to_string()))
            });
            if succeeded {
                elaborating.push(candidate);
            }
        }
        match elaborating.as_slice() {
            [only] => {
                let chosen = build(head(only));
                self.elaborate(&chosen)
            }
            _ => Err(ElabError::UnknownIdent(format!(
                "ambiguous, possible interpretations: {}",
                candidates
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ))),
        }
    }

    pub(super) fn elab_ident(&mut self, name: &SurfaceName) -> Result<Expr, ElabError> {
        match self.resolve_ident_target(name) {
            IdentTarget::RelativeConstructor => {
                return self
                    .resolve_expected_ctor_ident(name)
                    .ok_or_else(|| self.unknown_ident_error(name));
            }
            IdentTarget::MetaValue(value) => return Ok(value),
            IdentTarget::Local(fvar) => {
                return Ok(self
                    .single_theorem_captured_reference(fvar)
                    .unwrap_or_else(|| Expr::fvar(fvar)));
            }
            IdentTarget::Global(global) => return Ok(self.mk_const(&global)),
            IdentTarget::RootEscapeUnknown => return Err(self.unknown_ident_error(name)),
            IdentTarget::Ambiguous(candidates) => {
                let span = clean_parser::Span::dummy();
                return self.elab_overloaded(span, &candidates, |head| head);
            }
            IdentTarget::BuiltinId => {
                // fun {α : Sort u} (a : α) => a
                //   outer binder α : Sort u   (Implicit)
                //   inner binder a : α        (α is de Bruijn index 0 under the outer binder)
                //   body a                    (a is de Bruijn index 0 under the inner binder)
                let sort_u = Expr::sort(self.fresh_universe_param());
                let inner = Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0));
                return Ok(Expr::lam(BinderInfo::Implicit, sort_u, inner));
            }
            IdentTarget::BuiltinCond => {
                // de Bruijn in the innermost body scope {α, c, x, y}: y=0, x=1, c=2, α=3.
                let u = self.fresh_universe_param();
                let sort_u = Expr::sort(u.clone());
                let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
                let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![u]);
                // motive `fun (_ : Bool) => α`; under its extra binder α is bvar 4.
                let motive = Expr::lam(BinderInfo::Default, bool_c.clone(), Expr::bvar(4));
                // @Bool.rec motive (false=y) (true=x) (major=c)
                let core = Expr::apps(
                    bool_rec,
                    [motive, Expr::bvar(0), Expr::bvar(1), Expr::bvar(2)],
                );
                let lam_y = Expr::lam(BinderInfo::Default, Expr::bvar(2), core); // (y : α)
                let lam_x = Expr::lam(BinderInfo::Default, Expr::bvar(1), lam_y); // (x : α)
                let lam_c = Expr::lam(BinderInfo::Default, bool_c, lam_x); // (c : Bool)
                return Ok(Expr::lam(BinderInfo::Implicit, sort_u, lam_c)); // {α : Sort u}
            }
            // The redirect names the ROOT constant the bare export aliases
            // (`not` IS `Bool.not`), never a local or a namespace member that
            // happens to share the qualified spelling.
            IdentTarget::Redirect(target) => {
                return self.elab_ident(&SurfaceName::global_path(target));
            }
            IdentTarget::Unresolved => {}
        }

        // Auto-implicit handling (#164)
        // Respect `set_option autoImplicit false` at file or section scope.
        //
        // SIGNATURE-ONLY (gap sweep B03): Lean's auto-bound implicits apply
        // exclusively to declaration *headers* — binder types and the result
        // type (`Lean/Elab/MutualDef.lean` `elabHeaders` under
        // `withAutoBoundImplicit`; validity rules in `Lean/Elab/Binders.lean` /
        // `isValidAutoBoundImplicitName`). An unknown identifier in a VALUE
        // position (`in_term_body`) is a loud `unknown identifier` — a typo'd
        // ident in a def body must never be silently generalized into an
        // implicit binder (namespaces_scoping/p20, p23).
        let auto_implicit_enabled = match self.get_option("autoImplicit") {
            Some(Some(v)) => v != "false",
            _ => true, // default: enabled
        };
        let relaxed_auto_implicit = match self.get_option("relaxedAutoImplicit") {
            Some(Some(v)) => v != "false",
            _ => true, // default: enabled
        };
        // A Lean keyword is no name, so it cannot be auto-bound either.
        if auto_implicit_enabled
            && self.in_decl_context
            && !self.in_term_body
            && !name.is_lean_keyword()
            && Self::is_valid_auto_implicit_name(name, relaxed_auto_implicit)
        {
            if let Some(fvar) = self.has_auto_implicit(name) {
                return Ok(Expr::fvar(fvar));
            }

            // Reuse the expected type when available so constructor-local names
            // like `x`, `y`, `z`, `t`, or `c` become term binders. Fall back to
            // `Sort u` so header-level parameters like `α` still auto-bind.
            let ty = self
                .current_expected_type
                .as_ref()
                .map(|ty| {
                    let ty = self.metas.instantiate(ty);
                    self.metas.instantiate_levels(&ty)
                })
                .unwrap_or_else(|| Expr::sort(self.fresh_universe_param()));

            // Add the auto-implicit
            let fvar = self.add_auto_implicit(name.clone(), ty);
            return Ok(Expr::fvar(fvar));
        }

        Err(self.unknown_ident_error(name))
    }

    pub(super) fn unknown_ident_error(&self, name: &SurfaceName) -> ElabError {
        // Protected-name diagnostic (B13, namespaces_scoping/p16): a simple
        // `open Foo` deliberately does NOT alias `protected def Foo.x` (Lean
        // skips protected names in `OpenDecl.simple` resolution), so a bare
        // `x` afterwards is unknown — but the actionable fix is the qualified
        // name, not a fuzzy-match list. Point at it directly.
        for ns in self.namespace_state.open_namespaces() {
            let qualified = crate::namespace::append_names(ns, name.name());
            if self.env.is_protected(&qualified) && self.env.get_const(&qualified).is_some() {
                return ElabError::ProtectedIdent {
                    name: name.to_string(),
                    qualified: qualified.to_string(),
                    namespace_: ns.to_string(),
                };
            }
        }
        // A SELF-REFERENCE is not a typo (Trust ruling v7/D3: a refusal must
        // carry the fix, with options). `def gcd (a b : Nat) : Nat := … gcd b
        // (a % b)` used to die here as `UnknownIdentWithSuggestions` offering
        // `Quotient.ind` — the nearest theorem name to `gcd` — which is a
        // name-distance answer to a question nobody asked: `gcd` is the name
        // being DEFINED, so the real report is that its recursion is outside
        // the fragment Clean lowers, plus the ways across that boundary.
        //
        // This runs only where resolution has ALREADY failed, so it is a
        // choice of MESSAGE and nothing else — fail-closed behaviour is
        // byte-identical, and the two admitting recursion shapes never reach
        // this function at all (they resolve the self-call to an induction
        // hypothesis or a `WellFounded.fix` argument long before).
        if let Some(subject) = &self.self_reference {
            if self.ident_names_current_decl(name, &subject.written) {
                return ElabError::RecursionOutsideFragment {
                    name: name.to_string(),
                    decl: subject.written.to_string(),
                    params: subject.params,
                    detail: self.recursive_call_miss.clone().unwrap_or_else(|| {
                        "no parameter receives a structurally smaller variable in every \
                         recursive call, so no structural recursion was set up, and no \
                         `termination_by` measure was given"
                            .to_string()
                    }),
                };
            }
        }

        // The adjacent case, one level out: the identifier names a declaration
        // in the SAME header-first batch whose own signature never reached the
        // index, so there was nothing to forward-resolve against. That is a
        // report about the sibling, and nearest-theorem names are noise.
        // Exact canonical match first, short name second, so a qualified
        // sibling is never mistaken for a differently-namespaced one.
        let written = name.qualify_under(&SurfaceName::default());
        let sibling = self
            .unstaged_siblings
            .iter()
            .find(|candidate| &candidate.name == written.name())
            .or_else(|| {
                self.unstaged_siblings.iter().find(|candidate| {
                    let last = match candidate.name.inner() {
                        clean_kernel::name::NameInner::Str(_, text) => {
                            Name::anon().str(text.as_ref())
                        }
                        clean_kernel::name::NameInner::Num(_, number) => Name::anon().num(*number),
                        clean_kernel::name::NameInner::Anon => Name::anon(),
                    };
                    &last == written.name()
                })
            });
        if let Some(sibling) = sibling {
            return ElabError::SameBatchHeaderUnavailable {
                name: name.to_string(),
                sibling: sibling.name.to_string(),
                reason: sibling.reason,
            };
        }

        // Lazy Mathverse resolution (`crate::mathverse_lazy`). Placed AFTER
        // every diagnostic about a name this file or environment owns — the
        // protected-name pointer (a resident declaration always wins over a
        // library one), the self-reference report (the declaration being
        // DEFINED must never be satisfied by a library constant of the same
        // name, which would then collide at registration) and the same-batch
        // sibling report (likewise the file's own declaration) — and BEFORE
        // the ordinary unknown-identifier error, which it replaces only while
        // a corpus is armed and the library offers the name.
        if let Some(request) = self.mathverse_lazy_request(written.name()) {
            return request;
        }

        // The nearest-theorem scan is DEFERRED to where the error is reported
        // (`ElabError::with_ident_suggestions`): most of these errors are
        // raised on speculative paths that catch them, and the scan over every
        // accessible theorem was 4-15% of `Mathlib/Logic/Basic.lean`'s
        // elaboration (performance audit 2026-09-24).
        #[cfg(test)]
        DEFERRED_IDENT_ERRORS.with(|minted| minted.set(minted.get() + 1));
        ElabError::UnknownIdentDeferred {
            name: name.to_string(),
            namespace_prefix: self.namespace_prefix.name().clone(),
            fallback: None,
        }
    }

    /// Is `written`, as it appears at a failed use site, the name of the
    /// declaration currently being elaborated?
    ///
    /// Both the bare spelling and the namespace-qualified one count: inside
    /// `namespace Ty`, `def bitWidth` is `Ty.bitWidth`, and a body may write
    /// either. `_root_.` prefixes are stripped on both sides, mirroring
    /// [`super::structural`]'s own recursion-name normalization.
    fn ident_names_current_decl(&self, written: &SurfaceName, decl: &SurfaceName) -> bool {
        let written = written.qualify_under(&SurfaceName::default());
        let decl = decl.qualify_under(&SurfaceName::default());
        written == decl || written == self.qualify_name(&decl)
    }

    /// Ask the decl driver to install `name` from the Mathverse Library — a
    /// REQUEST, not a diagnosis. Returns `None` in every case where the
    /// ordinary error must stand.
    ///
    /// Three conditions, cheapest first:
    ///
    /// 1. a corpus is ARMED for this file (`import Mathverse.<Corpus>`), which
    ///    is one hash probe on an option map. A file that never wrote such an
    ///    import returns here, so no library lookup happens and the resulting
    ///    error is byte-identical to before;
    /// 2. `name` is NOT already resident — this is what makes lazy retry
    ///    terminate: a granted request ends with the name resident, so it can
    ///    never be requested twice;
    /// 3. the installed library offers `name` (one hash probe, ~5ns on a miss).
    ///
    /// Condition 3 is deliberately corpus-BLIND: a name the library has under
    /// the wrong corpus still produces a request so the loader can report the
    /// provenance mismatch, rather than letting it present as a typo.
    ///
    /// `name` is the canonical written name (`_root_.` already stripped); the
    /// library is keyed by its plain dotted spelling.
    ///
    /// `&self` — `ElabCtx` cannot install anything; see [`crate::mathverse_lazy`].
    pub(super) fn mathverse_lazy_request(&self, name: &Name) -> Option<ElabError> {
        if !self.mathverse_armed() || name.is_anon() || self.name_is_resident(name) {
            return None;
        }
        let name = name.to_string();
        crate::mathverse_lazy::library_offers(&name)
            .then_some(ElabError::MathverseNameAvailable { name })
    }

    /// Did this file write a corpus-level `import Mathverse.<Corpus>`?
    ///
    /// One hash probe, no allocation. Every lazy-resolution path asks this
    /// FIRST so a disarmed file pays nothing beyond it — in particular it must
    /// be answered before any dotted name is reassembled.
    pub(super) fn mathverse_armed(&self) -> bool {
        self.get_option(crate::mathverse_lazy::MATHVERSE_ARMED_OPTION)
            .is_some_and(Option::is_some)
    }

    /// Is `name` already installed in the environment under any declaration
    /// kind? Ignores accessibility on purpose: a private-but-present constant
    /// is still installed, and re-loading it would not help.
    fn name_is_resident(&self, name: &Name) -> bool {
        self.env.get_const(name).is_some()
            || self.env.get_inductive(name).is_some()
            || self.env.get_constructor(name).is_some()
            || self.env.get_recursor(name).is_some()
    }

    pub(super) fn elab_universe(&mut self, univ: &UniverseExpr) -> Result<Expr, ElabError> {
        let level = match univ {
            UniverseExpr::Prop => Level::zero(),
            UniverseExpr::Type => Level::succ(Level::zero()),
            UniverseExpr::TypeLevel(level_expr) => {
                let l = self.elab_level(level_expr)?;
                Level::succ(l)
            }
            // Type* (Mathlib syntax): a fresh RIGID universe parameter + 1
            // (`ElabCtx::fresh_star_universe_param`, Mathlib's
            // `TypeStar.lean` `mkFreshLevelParam`) — never a metavariable.
            // Under the strict `--prelude lean4-core` lane, `Type*` is
            // Mathlib-only (Lean core rejects it at parse time), so mirror the
            // B07 strict-monad gate and reject it LOUDLY here rather than
            // silently accepting with fresh-universe semantics
            // (GAP_SWEEP_2026-07-09 universes/p09). `Type _` (a level hole) is
            // the core-compatible spelling and is unaffected — it parses to
            // `TypeLevel(Param("_"))`, not `TypeImplicit`.
            UniverseExpr::TypeImplicit if self.env.lean4_core_strict_monads() => {
                return Err(ElabError::Lean4CoreOnlySyntax {
                    syntax: "Type*",
                    hint: "use `Type _` (a universe hole) or an explicit `Type u`",
                });
            }
            UniverseExpr::TypeImplicit => Level::succ(self.fresh_star_universe_param()),
            UniverseExpr::Sort(level_expr) => self.elab_level(level_expr)?,
            // Sort without explicit level: create a fresh universe parameter
            UniverseExpr::SortImplicit => self.fresh_universe_param(),
            // `Sort*` (Mathlib): a fresh RIGID universe parameter, the `Sort`
            // analogue of `Type*`. Gated LOUDLY under `--prelude lean4-core`
            // exactly like `Type*` above (`Sort*` is Mathlib-only; core rejects
            // it at parse time). `Sort _` (a level hole) is the core-compatible
            // spelling and is unaffected.
            UniverseExpr::SortStar if self.env.lean4_core_strict_monads() => {
                return Err(ElabError::Lean4CoreOnlySyntax {
                    syntax: "Sort*",
                    hint: "use `Sort _` (a universe hole) or an explicit `Sort u`",
                });
            }
            UniverseExpr::SortStar => self.fresh_star_universe_param(),
        };
        Ok(Expr::sort(level))
    }

    pub(super) fn elab_level(&mut self, level: &LevelExpr) -> Result<Level, ElabError> {
        stack_safe(|| match level {
            LevelExpr::Lit(n) => {
                let mut l = Level::zero();
                for _ in 0..*n {
                    l = Level::succ(l);
                }
                Ok(l)
            }
            LevelExpr::Param(name) => {
                // A level HOLE `_` (from `Type _` / `Sort _`) is not a named
                // parameter — it is a universe metavariable to be solved during
                // elaboration (Lean's `levelMVarToParam`). Mint a fresh one so
                // each `_` is independent and stays assignable (NOT rigid).
                if name.is_unescaped_component("_") {
                    return Ok(self.fresh_universe_param());
                }
                // THE MINT NAMESPACE IS RESERVED (2026-08-26b). Universe
                // metavariables are spelled `?u_N`, and `?` is not
                // `is_ident_start`, so `Sort ?u_0` has no production in the
                // level grammar. Guillemets are the one door that does not go
                // through the lexer's identifier rules — measured on the
                // release binary at `2ce2cf2c1`, `def gq (γ : Sort «my?weird»)
                // (y : γ) : γ := y` reports `1 passed, 0 failed` — so a
                // written `«?u_0»` would otherwise walk straight back into the
                // namespace this reservation exists to keep empty. Refusing it
                // here is what turns "a user cannot write a mint name" from a
                // lexer accident into a checked property, and it is the reason
                // `crate::level_role`'s `Minted` arm is now unreachable from a
                // WRITTEN name rather than merely unlikely. See
                // `crate::level_mint::MINT_PREFIX`.
                if name
                    .component_text()
                    .is_some_and(crate::level_mint::is_reserved_level_name)
                {
                    return Err(ElabError::ReservedUniverseName {
                        detail: format!(
                            "`{name}` is not a universe parameter name: the `?` space is \
                             reserved for universe METAVARIABLES the elaborator mints \
                             (`{}0`, `{}1`, …), so that a level hole and a level a \
                             declaration writes can never be the same level. The level \
                             grammar has no production for such a name — a quoted \
                             identifier (`«…»`) is the only way to write one. Use an \
                             ordinary universe name (`u`, `v`, `u_0`, …) — or `_` if you \
                             meant a hole.",
                            crate::level_mint::MINT_PREFIX,
                            crate::level_mint::MINT_PREFIX,
                        ),
                    });
                }
                // Check if it's a known universe parameter; if not, auto-add it.
                // This matches Lean 4's auto-bound implicit universe behavior:
                // `class Foo (X : Type u)` without explicit `universe u` declaration
                // will implicitly declare `u` as a universe parameter.
                //
                // RIGID, like a declared one. An auto-bound universe NAME is a
                // genuine parameter of the declaration; Lean does not
                // distinguish `def f (α : Type u)` from
                // `universe u; def f (α : Type u)`. Registering it only in
                // `universe_params` and not in the rigid set left it ASSIGNABLE,
                // so `add_level_constraint`'s rigid refusal never fired for it
                // and `def badAuto : Sort u := Nat` silently solved `u := 1` and
                // registered monomorphic with empty `level_params` — while the
                // declared twin `def bad.{u} : Sort u := Nat` was correctly
                // rejected. Measured 2026-08-14; probes p29/p30.
                //
                // Level holes (`Type _`) are NOT affected: they return above via
                // `fresh_universe_param` and must stay solvable.
                //
                // U2 stage-3 deferral 1 (2026-08-26): the test used to be
                // `!self.universe_params.contains(name)`, and that vector is
                // the UNION of the rigid names and the MINTED ones —
                // `fresh_universe_param` pushes its mints there so the next
                // mint skips them. So a user-written universe name colliding
                // with a name this declaration had already minted read as
                // "already a parameter", never reached the rigid set, and
                // stayed solvable: `def badAutoCollide (β : Sort _) : Sort u_0
                // := Nat` was ACCEPTED and monomorphized to `Sort 1` with zero
                // surviving level params, while the identical declaration
                // spelled `Sort w` was correctly rejected. That is p30's
                // silent-monomorphization class reached through the mint-name
                // door. Asking for the total ROLE instead of the union's
                // membership is the whole fix; a `Minted` name the user also
                // WROTE is a genuine parameter and is promoted to rigid, which
                // resolves the name clash in the loud-refusal direction.
                // Fixtures: universes/p47_..._MUST_FAIL (the defect), p48 (its
                // precision companion, which must keep passing), and p49 (the
                // MEASURED COST — a shape Lean accepts that this now refuses,
                // pinned rather than left unstated). See `crate::level_role`.
                //
                // GATED BY LEAN'S AUTO-BOUND RULE (2026-11-12). An undeclared
                // name auto-binds only while `autoImplicit` is on and the name
                // passes `isValidAutoBoundLevelName` (`Lean/Elab/Level.lean`
                // `elabLevel`); otherwise Lean says `unknown universe level`.
                // Binding it unconditionally accepted
                // `set_option autoImplicit false in def g2 {α : Type u} …` and,
                // under `relaxedAutoImplicit false`, `{α : Type β}` — both
                // rejected by Lean (`tests/elab_fail/autoBoundImplicits2`).
                let role = self.level_param_role(name.name());
                if role == crate::level_role::LevelParamRole::Foreign {
                    let (auto_implicit, relaxed) = self.auto_implicit_options();
                    if !auto_implicit || !Self::is_valid_auto_bound_level_name(name, relaxed) {
                        return Err(ElabError::UnknownUniverseLevel {
                            name: name.to_string(),
                        });
                    }
                }
                if role.is_assignable() {
                    if !self.universe_params.contains(name) {
                        self.universe_params.push(name.clone());
                    }
                    self.metas.add_rigid_level_param(name.name().clone());
                }
                Ok(Level::param(name.name().clone()))
            }
            LevelExpr::Succ(inner) => {
                let l = self.elab_level(inner)?;
                Ok(Level::succ(l))
            }
            LevelExpr::Max(l1, l2) => {
                let l1 = self.elab_level(l1)?;
                let l2 = self.elab_level(l2)?;
                Ok(Level::max(l1, l2))
            }
            LevelExpr::IMax(l1, l2) => {
                let l1 = self.elab_level(l1)?;
                let l2 = self.elab_level(l2)?;
                Ok(Level::imax(l1, l2))
            }
            LevelExpr::Antiquot(name) => {
                // Level antiquotation: $u inside q(Type $u) or q(Sort $u)
                // Look up the level variable from the enclosing scope.
                // For now, treat it as a level parameter (will be resolved during
                // antiquotation processing in q-quotations).
                //
                // In a full implementation, we'd check if `name` is bound to a
                // Level value in scope. For Phase 4, we treat it as a level param
                // that will be substituted.
                //
                // The reserved-namespace guard runs here too (2026-08-26b).
                // This arm builds a `Level::Param` straight from a written
                // identifier, so `$«?u_0»` is the SECOND way into the mint
                // namespace and it does not pass through the `Param` arm above.
                // Two lines is the whole cost of making the reservation total
                // over the level grammar rather than total over one of its
                // productions; see `crate::level_mint::MINT_PREFIX`.
                if name
                    .component_text()
                    .is_some_and(crate::level_mint::is_reserved_level_name)
                {
                    return Err(ElabError::ReservedUniverseName {
                        detail: format!(
                            "`{name}` is not a universe parameter name: the `?` space is \
                             reserved for universe METAVARIABLES the elaborator mints \
                             (`{}0`, `{}1`, …). A level antiquotation names a level \
                             variable in the quotation's scope, and no such variable can \
                             be spelled in this space.",
                            crate::level_mint::MINT_PREFIX,
                            crate::level_mint::MINT_PREFIX,
                        ),
                    });
                }
                Ok(Level::param(name.name().clone()))
            }
        })
    }

    pub(super) fn elab_lambda(
        &mut self,
        binders: &[SurfaceBinder],
        body: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        stack_safe(|| {
            if binders.is_empty() {
                // Base case: elaborate the lambda body against the codomain
                // expected type the enclosing binder set in
                // `current_expected_type` (line ~741). Routing through
                // `elaborate_with_expected_type` (rather than the bare
                // `elaborate`) runs `apply_implicit_to_expected_type` on the
                // body, so a polymorphic head like `none : {α} → Option α`
                // gets its implicit `{α}` inserted and unified against the
                // expected codomain (`Option Value`). Without this, the body
                // keeps its leading implicit Pi (`{α} → Option α`), the lambda
                // is typed `Nat → ({α} → Option α)`, and the kernel rejects it
                // with the leaked universe param ("Too many arguments: function
                // type Sort(...)"). An open expected function type propagates a
                // fresh codomain below. The lower-level untyped elaboration API
                // keeps lowering the body; declaration callers always finalize
                // against their written type or fresh inferred result type.
                let expected = self.current_expected_type.clone();
                // `@fun x => body`: the `@` governs the BINDERS only — Lean's
                // `elabFunBinders` skips implicit-lambda insertion for them
                // (`blockImplicitLambda`) — and the body is an ordinary term
                // that inserts its own implicit arguments. `elab_explicit`'s
                // flag used to leak into the body, so `@fun _ x => x.val`
                // elaborated `x.val` without `Fin.val`'s implicit `{n}`.
                let saved_explicit = std::mem::replace(&mut self.explicit_mode, false);
                let result = match expected {
                    Some(_) => self.elaborate_with_expected_type(body, expected),
                    None => self.elaborate(body),
                };
                self.explicit_mode = saved_explicit;
                return result;
            }

            let binder = &binders[0];
            let prev_expected = self.current_expected_type.clone();
            let expected_pi = prev_expected.as_ref().and_then(|expected_ty| {
                let expected_ty = self.metas.instantiate(expected_ty);
                let expected_ty = self.metas.instantiate_levels(&expected_ty);
                let expected_ty = self.whnf(&expected_ty);
                match expected_ty.kind() {
                    ExprKind::Pi(bi, domain, codomain) => {
                        Some((*bi, domain.as_ref().clone(), codomain.as_ref().clone()))
                    }
                    _ => None,
                }
            });

            // Implicit-lambda insertion is NOT decided here.
            //
            // It used to be, once per surface binder: whenever the expected
            // binder was implicit / instance-implicit and the surface binder
            // was explicit, a synthetic `✝implicit` was bound and the SAME
            // surface binder list was retried against the codomain. Lean
            // decides it ONCE for the whole term, before the `fun` is entered
            // (`useImplicitLambda`, `Term/TermElabM.lean`:1711, dispatched at
            // :1806), and `elabFunBinders` → `propagateExpectedType`
            // (`Elab/Binders.lean`:410, the arm `| .forallE _ d b _ =>` at
            // :416) then peels exactly one `forallE` per user binder and
            // IGNORES its binder info. So an explicit surface binder
            // legitimately binds an implicit expected binder, which is why
            // Lean accepts `⟨fun h ↦ …, fun h a ↦ by rw [h]⟩` against
            // `(∀ {a}, a = b ↔ a = c) ↔ b = c`
            // (`Mathlib/Logic/Basic.lean` `eq_iff_eq_cancel_left`/`_right`,
            // where the per-binder rule left the `by` block facing a fresh
            // unassigned metavariable) and REJECTS
            // `fun n x => x : Nat → {α : Type} → α → α`, which the per-binder
            // rule silently ACCEPTED. Both measured against the pinned
            // v4.30.0-rc2 binary.
            //
            // The term-level decision lives in `infer::elab_implicit_lambda`
            // and is taken at the two entries that arm an expected type: the
            // chokepoint `elaborate_with_expected_type`, and the `Lambda`
            // bypass in `elaborate` for definition bodies.

            let ty = if let Some(ty) = &binder.ty {
                let elaborated = self.elaborate_type_observing(ty)?;
                // `{alpha}` … `fun (x : alpha) => …`: the lambda DOMAIN is
                // where `alpha`'s own type is solved. See
                // `ElabCtx::solve_binder_type_from_use`.
                self.solve_binder_type_from_use(&elaborated);
                // A type position: `fun (h : b) => …` with `b : Bool` binds
                // `h : b = true` (G34, `elab_type_position`).
                let elaborated = self.coerce_type_position(elaborated);
                // Lean's `elabFunBinderViews` (`Lean/Elab/Binders.lean`):
                // with an expected `∀ x : d, _`, each binder's elaborated type
                // is unified with `d` (`discard <| isDefEq type d`) BEFORE the
                // body, so `fun (foo : _) => foo.x` against `S → Nat` sees
                // `foo : S` there. Left unsolved, the receiver's type was a
                // bare metavariable when `foo.x` was elaborated. A failed
                // unification is rolled back and ignored, as in Lean.
                if let Some((_, domain, _)) = expected_pi.as_ref() {
                    self.metas.push_scope();
                    let unified = {
                        let ctx = self.build_local_ctx();
                        let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                        matches!(unifier.unify(&elaborated, domain), UnifyResult::Success)
                    };
                    if unified {
                        self.metas.commit();
                    } else {
                        self.metas.pop_scope();
                    }
                }
                elaborated
            } else if let Some((_, domain, _)) = expected_pi.as_ref() {
                domain.clone()
            } else if !self.pinned_lambda_binder_types.is_empty() {
                // A β-redex head retried with the binder types its first
                // attempt settled (`elab_beta_redex.rs`).
                self.pinned_lambda_binder_types.remove(0)
            } else {
                // Lean: a missing binder type is a hole (`expandBinderType` →
                // `mkHole`, `Lean/Elab/Binders.lean`), elaborated by
                // `elabFunBinderViews` → `elabType`, which mints a fresh LEVEL
                // metavariable and a natural `?T : Sort ?u`
                // (`Lean/Elab/Term/TermElabM.lean` `elabType`) — the same
                // repair `elab_hole` got for `_` in 75ce06eaa. This minted
                // `?T : Type`, i.e. `Sort 1`, and `unify_meta`'s Sort arm then
                // enforced it: `?T := α` with `α : Sort u` asked `u := 1`.
                // Measured: `f ∘ g = …` (desugared to `fun x => f (g x)`) and
                // `(fun x => f x) = f` on the left of `=`, where no Pi is
                // expected, died `cannot assign rigid universe parameter
                // u := 1` over a declared universe (`Function.comp_update`,
                // `update_comp_eq_of_injective`, `Involutive.comp_self`), and
                // over `Sort*` the solution was silently ACCEPTED — the
                // declaration monomorphized to `Type 0` and only a later use
                // at `Prop` failed.
                let binder_sort = Expr::sort(self.fresh_universe_param());
                self.fresh_natural_meta(binder_sort)
            };

            if binder.name.is_header_binder() {
                self.check_instance_binder_annotation(binder.info, &ty)?;
            }

            let bi = convert_binder_info(binder.info);
            let fvar = self.push_local(binder.name.clone(), ty.clone());
            self.note_local_forall_binder_names(fvar, binder.ty.as_deref(), &ty);
            self.capture_binder_info(binder, fvar);
            // A `let rec` under this binder that captures it keeps its info.
            self.note_let_rec_binder(fvar, bi);

            // Any local whose type is a class is a local instance (Lean's rule;
            // see `binder_is_local_instance`), not only the `[…]` spelling.
            let is_inst_implicit = self.binder_is_local_instance(bi, &ty);
            if is_inst_implicit {
                self.push_local_instance(fvar, ty.clone());
            }

            let open_expected = prev_expected.as_ref().is_some_and(|expected| {
                matches!(self.metas.instantiate(expected).kind(), ExprKind::FVar(id) if MetaState::from_fvar(*id).is_some())
            });
            self.current_expected_type = expected_pi.map(|(_, _, codomain)| {
                let codomain = codomain.instantiate(&Expr::fvar(fvar));
                let codomain = self.metas.instantiate(&codomain);
                self.metas.instantiate_levels(&codomain)
            });
            if self.current_expected_type.is_none() && open_expected {
                // A declaration's inferred result is initially a bare type meta.
                // Preserve that expected-type boundary through every lambda
                // binder, so the body finalizer inserts its own implicits.
                let sort = Expr::sort(self.fresh_universe_param());
                self.current_expected_type = Some(self.fresh_meta(sort));
            }
            let inner_result = self.elab_lambda(&binders[1..], body);
            self.current_expected_type = prev_expected;

            if is_inst_implicit {
                self.pop_local_instance();
            }
            self.pop_local();
            let inner = inner_result?;

            // SOUNDNESS: instantiate assigned metavars/levels in the domain and
            // body before abstracting the binder fvar. If a metavar in `ty` or
            // `inner` was assigned during elaboration — and the assignment
            // mentions `fvar` or another local — abstracting first would leave a
            // loose fvar / uninstantiated metavar in the closed lambda, which the
            // kernel rejects ("contains free variables" / a Pi domain that leaked
            // an FVar). Instantiating only substitutes already-decided values, so
            // it is a no-op when nothing was assigned and produces the correct
            // closed term otherwise. TCB-neutral: no kernel code is touched and
            // `add_decl` still re-checks the result.
            let ty = self.metas.instantiate_levels(&self.metas.instantiate(&ty));
            let inner = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&inner));

            // NOTE: a bare-metavariable body (`fun x => ?_`) records its
            // dependence on the binder only in the METAVARIABLE'S TYPE, which
            // `abstract_fvar` cannot reach, so the lambda's INFERRED type keeps
            // the binder's fvar free. That is the open class pinned in
            // `tests_refine_hole_under_lambda`; making the dependence explicit
            // in the term here was measured and REVERTED (see that file).
            // Abstract the fvar to a bvar
            let inner_abs = inner.abstract_fvar(fvar);
            Ok(Expr::lam(bi, ty, inner_abs))
        })
    }

    pub(super) fn elab_pi(
        &mut self,
        binders: &[SurfaceBinder],
        body: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        stack_safe(|| {
            if binders.is_empty() {
                // The Pi body is a type position (`elabType`): a `Bool` body
                // is coerced to `b = true` (G34, `elab_type_position`).
                let body = self.elaborate_type_observing(body)?;
                return Ok(self.coerce_type_position(body));
            }

            let binder = &binders[0];
            let ty = if let Some(ty) = &binder.ty {
                let elaborated = self.elaborate_type_observing(ty)?;
                // `{alpha}` … `(f : forall x : alpha, T)`: the Pi DOMAIN is
                // where `alpha`'s own type is solved. See
                // `ElabCtx::solve_binder_type_from_use`.
                self.solve_binder_type_from_use(&elaborated);
                // A type position: `(h : b)` with `b : Bool` binds `h : b = true`.
                self.coerce_type_position(elaborated)
            } else {
                // Lean 4: unannotated Pi binders get fresh NATURAL metavars
                // (`Sort ?u`, `elabType`), whose context `ctxApprox` may narrow.
                let binder_sort = Expr::sort(self.fresh_universe_param());
                self.fresh_natural_meta(binder_sort)
            };

            self.check_instance_binder_annotation(binder.info, &ty)?;

            let bi = convert_binder_info(binder.info);
            let fvar = self.push_local(binder.name.clone(), ty.clone());
            self.note_local_forall_binder_names(fvar, binder.ty.as_deref(), &ty);
            self.capture_binder_info(binder, fvar);

            // Any local whose type is a class is a local instance (Lean's rule;
            // see `binder_is_local_instance`), not only the `[…]` spelling.
            let is_inst_implicit = self.binder_is_local_instance(bi, &ty);
            if is_inst_implicit {
                self.push_local_instance(fvar, ty.clone());
            }

            let inner = self.elab_pi(&binders[1..], body)?;

            if is_inst_implicit {
                self.pop_local_instance();
            }
            self.pop_local();

            // SOUNDNESS: instantiate assigned metavars/levels in the domain and
            // body before abstracting the binder fvar. An unannotated Pi binder
            // gets `ty = fresh_meta(...)`; if that domain (or a nested dependent
            // domain) is later assigned to a term mentioning `fvar`, abstracting
            // first leaks a loose fvar and the kernel sees `Pi(…, FVar(0), …)`
            // where it expected a `Sort`. Instantiating substitutes only
            // already-decided values, so it is a no-op absent assignments and
            // yields the correct closed term otherwise. TCB-neutral: the kernel
            // re-checks the declaration.
            let ty = self.metas.instantiate_levels(&self.metas.instantiate(&ty));
            let inner = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&inner));

            // Abstract the fvar to a bvar
            let inner_abs = inner.abstract_fvar(fvar);
            Ok(Expr::pi(bi, ty, inner_abs))
        })
    }
}

/// Whether the constant `name` is visible from inside `namespace_prefix` by
/// the NAMESPACE rule alone: a private constant only from its own namespace
/// (or below it). The deferred nearest-theorem scan uses it, because it runs
/// when an error is REPORTED, after the elaborator is gone.
/// `ElabCtx::is_const_accessible` — which decides what elaborates — adds
/// Lean 4.8.0's module-local privacy (another module's `private` is never
/// accessible; this module's is accessible everywhere in it), which needs the
/// elaborator's own record of foreign private declarations. So a suggestion
/// can at most name another module's `private` declaration that sits in the
/// current namespace: error text only, never a verdict.
pub(crate) fn const_accessible_from(
    env: &Environment,
    namespace_prefix: &Name,
    name: &Name,
) -> bool {
    if !env.is_private(name) {
        return true;
    }
    let const_ns = crate::namespace::parent_name(name);
    if const_ns.is_anon() {
        namespace_prefix.is_anon()
    } else {
        crate::namespace::name_has_prefix(namespace_prefix, &const_ns)
    }
}

/// The `limit` accessible theorem names nearest `name`, for an unknown
/// identifier written inside `namespace_prefix` — the "did you mean" list.
/// A scan of every constant in `env`, so it runs only for a REPORTED error
/// (`ElabError::with_ident_suggestions`).
pub(crate) fn nearest_theorem_names(
    env: &Environment,
    namespace_prefix: &Name,
    name: &str,
    limit: usize,
) -> Vec<String> {
    #[cfg(test)]
    NEAREST_THEOREM_SCANS.with(|scans| scans.set(scans.get() + 1));
    let theorem_names: Vec<String> = env
        .constants()
        .filter(|info| info.kind == ConstantKind::Theorem)
        // A mangled private name (`_private.M.0.helper`, G21) is never a
        // spelling to suggest: a sibling's is unreachable, and this module's
        // own is reached by its user-facing name, which was just missed.
        .filter(|info| !crate::private_names::is_private_name(&info.name))
        .filter(|info| const_accessible_from(env, namespace_prefix, &info.name))
        .map(|info| info.name.to_string())
        .collect();
    nearest_string_candidates(name, theorem_names.iter().map(String::as_str), limit)
}

#[cfg(test)]
thread_local! {
    /// How many nearest-theorem scans this thread has run: the observable the
    /// deferral tests pin (a speculative unknown identifier must cost none).
    static NEAREST_THEOREM_SCANS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// How many deferred unknown-identifier errors this thread has minted: the
    /// witness that a speculative miss really happened in a test that asserts
    /// it cost no scan.
    static DEFERRED_IDENT_ERRORS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Test-only: the number of deferred unknown-identifier errors minted on this
/// thread.
#[cfg(test)]
pub(crate) fn deferred_ident_error_count() -> usize {
    DEFERRED_IDENT_ERRORS.with(std::cell::Cell::get)
}

/// Test-only: the number of [`nearest_theorem_names`] scans on this thread.
#[cfg(test)]
pub(crate) fn nearest_theorem_scan_count() -> usize {
    NEAREST_THEOREM_SCANS.with(std::cell::Cell::get)
}
