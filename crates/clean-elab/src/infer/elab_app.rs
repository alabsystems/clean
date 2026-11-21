// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Application elaboration, implicit argument insertion, and anonymous constructors.
//!
//! Extracted from `infer/mod.rs`. Contains the core application elaboration loop,
//! implicit argument insertion, and anonymous constructor elaboration.
//!
//! Support methods (bidirectional checking, named args, coercion) are in
//! `elab_app_support.rs` (#307).

use super::*;

struct RecursorApplication<'a> {
    name: Name,
    recursor: clean_kernel::RecursorVal,
    major_first: bool,
    args: &'a [SurfaceArg],
}
/// Type arguments of a desugared heterogeneous operator application.
struct HeteroBinopSlots {
    alpha: Expr,
    beta: Expr,
    gamma: Expr,
    /// Arithmetic `binop%` joins all three carrier slots.
    homogeneous: bool,
    /// A shift's actual dictionary slot. Its default bridge must resolve its
    /// homogeneous-class premise before it can join the amount to the carrier.
    shift_instance: Option<Expr>,
}

/// Whether explicit arguments remain to be elaborated after a run of implicit
/// argument insertion — the one fact Lean's `processStrictImplicitArg`
/// (`Lean/Elab/App.lean:767-774`) consults:
/// `if (← hasArgsToProcess) then addImplicitArg argName else finalize`.
///
/// A `{x}` or `[x]` binder is always filled; a strict-implicit `⦃x⦄` binder
/// only while an argument follows, even when `normalizeFunType`'s
/// `whnfForall` exposed it by unfolding a definition. Measured 2026-09-12 on
/// `Mathlib/Logic/Function/Basic.lean` and `Mathlib/Data/Subtype.lean`: with
/// `Function.Injective f := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂`, every
/// application or identifier whose type unfolds to it (`I.of_comp_right hg`,
/// `coe_injective`, `not_involutive.injective`, …) came back as
/// `f ?a₁ = f ?a₂ → ?a₁ = ?a₂` and failed against `Injective f`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::infer) enum ArgsFollow {
    /// An explicit argument is still to come: `⦃x⦄` is filled like `{x}`.
    Yes,
    /// No explicit argument remains: insertion stops at the first `⦃x⦄`.
    No,
}

impl ArgsFollow {
    /// `Yes` iff `remaining` explicit arguments are still to be elaborated.
    pub(in crate::infer) fn from_remaining(remaining: usize) -> Self {
        if remaining > 0 {
            Self::Yes
        } else {
            Self::No
        }
    }
}

impl<'a> ElabCtx<'a> {
    /// Static dispatch labels are selected only after structural identity agrees.
    fn canonical_application_head(name: &SurfaceName) -> Option<&'static str> {
        if name.is_relative_constructor() {
            return None;
        }
        [
            "HMod.hMod",
            "HAdd.hAdd",
            "HSub.hSub",
            "HMul.hMul",
            "HDiv.hDiv",
            "HAnd.hAnd",
            "HOr.hOr",
            "HXor.hXor",
            "HAppend.hAppend",
            "HPow.hPow",
            "HShiftLeft.hShiftLeft",
            "HShiftRight.hShiftRight",
            "List.cons",
            "Array.mk",
            "some",
            "Option.some",
            "Prod.mk",
        ]
        .into_iter()
        .find(|label| name == &SurfaceName::generated_path(label))
    }

    /// True iff `e` (parens unwrapped) is a *bare* structure literal
    /// `{ f := v, … }` — neither an explicit `: T` annotation nor a `with` base.
    /// This is the form that can only elaborate once an expected structure type
    /// is known from context.
    fn is_bare_struct_lit(e: &SurfaceExpr) -> bool {
        matches!(
            Self::unwrap_surface_parens(e),
            SurfaceExpr::StructLit {
                struct_type: None,
                base: None,
                ..
            }
        )
    }

    /// Elaborate a homogeneous equality `a = b` / `a ≠ b` whose ONE operand is a
    /// bare structure literal, taking the structure type from the OTHER operand.
    ///
    /// Lean's `binop%` elaboration (`Elab/Extra.lean`) elaborates the operands
    /// that carry a type first, fixes the shared operand type, then elaborates
    /// the type-directed leaves (structure instances, `Elab/StructInst.lean`)
    /// against it. Clean's generic application path elaborates operands
    /// left-to-right, so a struct literal on the LHS (`{ x := 1 } = s`) is
    /// elaborated before `s` can supply its type and fails "struct literal
    /// requires type annotation or expected type" (the RHS form `s = { x := 1 }`
    /// already works because operand-0 pins the shared type first).
    ///
    /// Here we detect that shape, elaborate the type-carrying operand first to
    /// fix the shared type `T`, elaborate the struct literal against `T`, and
    /// build `@Eq/@Ne T lhs rhs` with the operands in their ORIGINAL order. Only
    /// fires when exactly one side is a bare struct literal — `{…} = {…}` (no
    /// operand can supply the type) and the all-concrete case both fall through
    /// to the generic path unchanged. The kernel re-checks the result, so a
    /// wrong type simply fails to type-check.
    fn try_elab_eq_struct_lit_reorder(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Option<Expr>, ElabError> {
        if self.explicit_mode || args.len() != 2 || args.iter().any(|a| a.name.is_some()) {
            return Ok(None);
        }
        let SurfaceExpr::Ident(_, head) = Self::unwrap_surface_parens(func) else {
            return Ok(None);
        };
        // Only the GLOBAL `Eq`/`Ne` (the `=`/`≠` desugaring, or a user-written
        // head that resolves to it): a local bound as `Eq` is the user's own
        // relation, and rebuilding its application as `@Eq T lhs rhs` proved
        // `r (fun _ _ => False)` for `def r (Eq : P → P → Prop) : Prop := Eq
        // {x := 1} (P.mk 1)` (Lean 4.8.0: `False`).
        if !self.head_denotes_global(head, "Eq") && !self.head_denotes_global(head, "Ne") {
            return Ok(None);
        }
        let lhs_is_lit = Self::is_bare_struct_lit(&args[0].expr);
        let rhs_is_lit = Self::is_bare_struct_lit(&args[1].expr);
        // Fire ONLY when exactly one side is a type-directed struct literal.
        if lhs_is_lit == rhs_is_lit {
            return Ok(None);
        }
        // Require a `<head>` const with exactly one universe parameter so the
        // level we synthesize below matches its signature; otherwise decline.
        match self.env.get_const(head.name()) {
            Some(c) if c.level_params.len() == 1 => {}
            _ => return Ok(None),
        }

        // Elaborate the type-carrying operand with NO expected type (the
        // equation's own expected type is `Prop`, which is not the operand
        // type), then read off the shared operand type `T`.
        let typed_idx = usize::from(lhs_is_lit);
        let lit_idx = 1 - typed_idx;
        let typed_val = self.elaborate_with_expected_type(&args[typed_idx].expr, None)?;
        let ty = self.infer_type(&typed_val)?;
        let ty = self.metas.instantiate_levels(&self.metas.instantiate(&ty));
        // A still-open operand type cannot drive the struct literal — bail to the
        // generic path (which errors loudly) rather than guess.
        if self.has_metavars(&ty) {
            return Ok(None);
        }
        let lit_val = self.elaborate_with_expected_type(&args[lit_idx].expr, Some(ty.clone()))?;

        let sort_level = self.infer_sort(&ty)?;
        let (lhs, rhs) = if lhs_is_lit {
            (lit_val, typed_val)
        } else {
            (typed_val, lit_val)
        };
        Ok(Some(Expr::apps(
            Expr::const_(head.name().clone(), vec![sort_level]),
            [ty, lhs, rhs],
        )))
    }

    /// Resolve the ASCII `!` prefix over a `Bool` operand to `Bool.not`.
    ///
    /// The lexer maps both ASCII `!` and `¬` to a single `TokenKind::Not`
    /// (`lexer.rs`), and the parser desugars that prefix uniformly to the
    /// PROPOSITIONAL `Not` (`Not p := p → False`, `logic_true_false.rs`). For a
    /// genuine `Prop` that is correct; but Lean's `!` is the BOOLEAN negation
    /// `Bool.not : Bool → Bool`. When the operand elaborates to a `Bool` (e.g.
    /// `!(xs.contains y)`), the propositional `Not` is ill-typed and only limps
    /// through via a `Bool → Prop` coercion — which then leaves an unsolved
    /// element-type metavariable when the result feeds a `++`/`HAppend` (the
    /// `setUnion`-style `xs ++ ys.filter (fun y => !(…))`), so the elaborated
    /// term escapes with a free variable and the kernel rejects it
    /// ("contains free variables").
    ///
    /// This helper short-circuits that: if the single operand of a `Not`
    /// application elaborates (under a throw-away metavar scope) to a `Bool`,
    /// re-emit it as `@Bool.not operand`, matching Lean's `!`. Otherwise it
    /// declines (`Ok(None)`) and the operand is re-elaborated on the normal
    /// propositional-`Not` path, so genuine `¬p` over a `Prop` is unaffected.
    /// Soundness: `Bool.not` is a total, axiom-free `Bool.rec` definition; the
    /// kernel still type-checks the resulting application.
    fn try_elab_bool_not_app(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Option<Expr>, ElabError> {
        if args.len() != 1 || args[0].name.is_some() {
            return Ok(None);
        }
        let SurfaceExpr::Ident(_, name) = Self::unwrap_surface_parens(func) else {
            return Ok(None);
        };
        // `!x` reaches here as `not x` and `¬x` as `Not x` (the parser tells
        // the two spellings apart; Lean: `notation "!" b => not b`,
        // `notation "¬" p => Not p`). `¬b` over a `Bool` is `Not (b = true)`
        // — the ordinary coercion path below — and becomes `Bool.not` only
        // where a `Bool` is EXPECTED (Lean coerces the proposition back with
        // `decide`; the two agree propositionally). Rewriting every `¬b` into
        // `Bool.not b` had made `¬(a == b)` a Bool-valued statement, so
        // `fun h => …` against it had no binder type (`not_beq_of_ne`,
        // measured 2026-09-12).
        // Only a head that RESOLVES to the global `not`/`Not`: a local bound
        // under either spelling is an ordinary function of the user's, and
        // rewriting its call to `Bool.not` computed `def r (not : Bool → Bool)
        // (b : Bool) := not b` as negation (`r (fun b => b) true = false` was
        // accepted; Lean 4.8.0: `true`).
        let bang = self.head_denotes_global(name, "not");
        if !bang && !self.head_denotes_global(name, "Not") {
            return Ok(None);
        }
        if !bang && !self.expected_type_is_bool() {
            return Ok(None);
        }
        // `Bool.not` must exist (it does under `with_prelude`); decline cleanly
        // on a sparser env so behavior is never worse than the status quo.
        if self.env.get_const(&Name::from_string("Bool.not")).is_none() {
            return Ok(None);
        }

        // Probe the operand under a throw-away metavar scope so a decline leaves
        // no metavariable residue for the propositional-`Not` re-elaboration.
        self.metas.push_scope();
        let operand = match self.elaborate(&args[0].expr) {
            Ok(e) => e,
            Err(_) => {
                self.metas.pop_scope();
                return Ok(None);
            }
        };
        let operand_ty = match self.infer_type(&operand) {
            Ok(t) => self.whnf(&self.metas.instantiate(&t)),
            Err(_) => {
                self.metas.pop_scope();
                return Ok(None);
            }
        };
        let is_bool = matches!(
            operand_ty.get_app_fn().kind(),
            ExprKind::Const(n, _) if n == &Name::from_string("Bool")
        );
        let is_prop = matches!(operand_ty.kind(), ExprKind::Sort(l) if l.is_zero());
        let bool_not = Expr::const_(Name::from_string("Bool.not"), vec![]);
        if is_bool {
            self.metas.commit();
            return Ok(Some(Expr::app(bool_not, operand)));
        }
        if bang && is_prop {
            // `!p` over a proposition is `!decide p` (Lean's Prop → Bool
            // coercion); a proposition with no `Decidable` instance is an
            // error, as in Lean.
            self.metas.commit();
            let inst = self.resolve_decidable(&operand)?;
            let decided = Expr::apps(
                Expr::const_(Name::from_string("Decidable.decide"), vec![]),
                [operand, inst],
            );
            return Ok(Some(Expr::app(bool_not, decided)));
        }
        // Neither a `Bool` nor (for `!`) a proposition: elaborate the
        // application as written, so any mismatch is reported there.
        self.metas.pop_scope();
        Ok(None)
    }

    /// Whether the expected type, as it stands, is `Bool`.
    fn expected_type_is_bool(&self) -> bool {
        self.current_expected_type.as_ref().is_some_and(|ty| {
            let ty = self.whnf(&self.metas.instantiate(ty));
            matches!(
                ty.get_app_fn().kind(),
                ExprKind::Const(n, _) if n == &Name::from_string("Bool")
            )
        })
    }

    /// Recover the inductive type of a leading-dot constructor `.suffix` from
    /// the constructor name alone, when no usable expected type is available.
    ///
    /// Scans every registered inductive's constructor list (the constructor
    /// table is keyed by full name, so we walk inductives to keep the answer
    /// inductive-scoped) for a constructor whose last name component equals
    /// `suffix`. Returns `Some(inductive_name)` only when exactly ONE inductive
    /// owns a matching constructor; an ambiguous suffix returns `None`, so the
    /// caller hard-fails rather than guessing. This is a *resolution* helper
    /// only — the chosen constructor's actual type is still checked by the
    /// kernel, so an over-eager match cannot weaken soundness.
    fn resolve_leading_dot_inductive_by_suffix(&self, suffix: &SurfaceName) -> Option<Name> {
        let mut found: Option<Name> = None;
        for ind in self.env.inductives() {
            let owns = ind
                .constructor_names
                .iter()
                .any(|ctor| SurfaceName::from_name(ctor.clone()).last_component() == *suffix);
            if owns {
                if found.is_some() {
                    // Ambiguous: more than one inductive has a `.suffix`
                    // constructor. Refuse to guess.
                    return None;
                }
                found = Some(ind.name.clone());
            }
        }
        found
    }

    pub(in crate::infer) fn elab_leading_dot_ctor_with_expected_type(
        &mut self,
        name: &SurfaceName,
        expected_ty: &Expr,
    ) -> Result<Expr, ElabError> {
        if !name.is_relative_constructor() {
            return Err(ElabError::UnknownIdent(name.to_string()));
        }
        let ctor_suffix = SurfaceName::from_name(name.name().clone());

        let expected_ty = self.metas.instantiate(expected_ty);
        let expected_ty = self.metas.instantiate_levels(&expected_ty);
        // Lean's `resolveDotName`: the head constant of the expected type is
        // tried BEFORE any unfolding, for any constant (`Function.Injective.piMap`
        // for `.piMap fun _ ↦ hg : Injective (g ∘ ·)`), and the expected type
        // of an APPLICATION headed by `.name` is the application's own — the
        // `∀`-bodied definition `Function.Injective` used to be unfolded first
        // and the theorem never found (`Injective.comp_left`,
        // `Surjective.comp_left`, `Bijective.piMap` in
        // `Mathlib/Logic/Function/Basic.lean`, measured 2026-09-11).
        if let ExprKind::Const(head, _) = expected_ty.get_app_fn().kind() {
            let candidate = crate::namespace::append_names(head, ctor_suffix.name());
            if let Some(info) = self.env.get_const(&candidate) {
                let levels: Vec<Level> = info
                    .level_params
                    .iter()
                    .map(|_| self.fresh_universe_param())
                    .collect();
                return Ok(Expr::const_(candidate, levels));
            }
        }
        // A FUNCTION-typed expected type names the constructor through its
        // result — Lean's `resolveDotName` runs `withForallBody` — and the
        // constructor's return type is unified with that result below:
        // `(.intro _) : p False → ∃ h, p h` is `Exists.intro` with the
        // predicate solved from `∃ h, p h` (`h.elim (.intro _) (.intro _)`,
        // `Prop.exists_iff` in `Mathlib/Logic/Basic.lean`, measured
        // 2026-09-11; the suffix scan found `.intro` ambiguous).
        let expected_whnf = {
            let mut result_ty = self.whnf(&expected_ty);
            loop {
                let ExprKind::Pi(_, domain, codomain) = result_ty.kind() else {
                    break result_ty;
                };
                let placeholder = self.fresh_meta(domain.as_ref().clone());
                result_ty = self.whnf(&codomain.instantiate(&placeholder));
            }
        };

        let ind_name = match expected_whnf.get_app_fn().kind() {
            ExprKind::Const(name, _) => name.clone(),
            // No usable expected type (the head reduces to a metavariable or
            // some non-`Const` shape — e.g. `throw (.ub msg)` where the error
            // type `ε` is pinned only by a later `MonadExcept` instance, or a
            // `match (.ctor …) with` scrutinee with no motive-supplied type).
            // Recover the inductive purely from the constructor *suffix*: scan
            // every registered inductive's constructor list for one whose last
            // component matches, and if exactly one inductive owns such a
            // constructor, use it. The constructor's own return type is unified
            // back into the (still-open) expected type below, so a wrong guess
            // cannot leak past the kernel re-check. Only an unambiguous suffix
            // is accepted — ambiguity falls through to `UnknownIdent`. (trk-gh)
            _ => self
                .resolve_leading_dot_inductive_by_suffix(&ctor_suffix)
                .ok_or_else(|| ElabError::UnknownIdent(name.to_string()))?,
        };

        // Resolve the constructor name and its type info.
        let (ctor_name, ctor_levels) = if let Some(ind) = self.env.get_inductive(&ind_name) {
            // Registered inductive (e.g., Option, List, Bool, Nat, user-defined, etc.)
            if let Some(ctor) = ind
                .constructor_names
                .iter()
                .find(|ctor| {
                    SurfaceName::from_name((*ctor).clone()).last_component() == ctor_suffix
                })
                .cloned()
            {
                let levels = match expected_whnf.get_app_fn().kind() {
                    ExprKind::Const(_, levels) if !levels.is_empty() => levels.to_vec(),
                    // Either a `Const` head with no explicit levels, or a non-`Const`
                    // head (suffix-recovered inductive, where the expected type was a
                    // metavariable). In both cases the universe levels are unknown up
                    // front, so allocate fresh universe params and let return-type
                    // unification below pin them. (trk-gh extends the latter arm.)
                    _ => ind
                        .level_params
                        .iter()
                        .map(|_| self.fresh_universe_param())
                        .collect(),
                };
                (ctor, levels)
            } else {
                // `.suffix` names no constructor of the expected inductive. Widen
                // to the accessible namespace constant `Ind.suffix`, mirroring
                // the unregistered-type arm below — Lean's generalized field
                // notation resolves non-constructor members too (`.symm h`
                // under an expected `Eq` type is the THEOREM `Eq.symm`).
                // Suffixes with no namespace constant stay UnknownIdent, which
                // is why `.rfl` under an expected `Eq` type correctly fails:
                // Lean has no `Eq.rfl` (see `tests/leading_dot_theorem.rs`).
                // Universe
                // params are minted fresh from the CONSTANT's own arity — a
                // member's level count need not match the inductive's — and
                // pinned by return-type unification below. A suffix-recovered
                // `ind_name` (meta-headed expected type) cannot reach this arm:
                // recovery only returns an inductive that owns the constructor,
                // so that path stays constructor-only and fail-closed.
                let ctor = crate::namespace::append_names(&ind_name, ctor_suffix.name());
                let info = self
                    .env
                    .get_const(&ctor)
                    .filter(|_| self.is_const_accessible(&ctor))
                    .ok_or_else(|| ElabError::UnknownIdent(name.to_string()))?;
                let levels: Vec<_> = info
                    .level_params
                    .iter()
                    .map(|_| self.fresh_universe_param())
                    .collect();
                (ctor, levels)
            }
        } else {
            // Fallback: type is not a registered inductive (e.g., Except is declared
            // as an axiom with its constructors as separate axiom constants). Look up
            // `TypeName.ctor_suffix` directly as a constant in the environment.
            let ctor = crate::namespace::append_names(&ind_name, ctor_suffix.name());
            let info = self
                .env
                .get_const(&ctor)
                .ok_or_else(|| ElabError::UnknownIdent(name.to_string()))?;
            let levels: Vec<_> = info
                .level_params
                .iter()
                .map(|_| self.fresh_universe_param())
                .collect();
            (ctor, levels)
        };

        // Build the constructor constant and insert implicit arguments using
        // return-type unification. This is more precise than apply_implicit_to_expected_type:
        // we fill implicit Pi binders with metavariables, extract the return type
        // (after all binders, including explicit ones), unify the return type with
        // the expected type to solve the metas, then return the constructor applied
        // to only the implicit args (leaving explicit args for the caller). (#3421)
        let ctor_expr = Expr::const_(ctor_name, ctor_levels);
        let ctor_ty = self.infer_type(&ctor_expr)?;
        let ctor_ty_whnf = self.whnf(&ctor_ty);

        // Collect implicit args and find the return type
        let mut result = ctor_expr;
        let mut ty = ctor_ty_whnf;
        loop {
            match ty.kind() {
                ExprKind::Pi(bi, arg_ty, body_ty) if Self::is_implicit_binder(*bi) => {
                    let arg_ty_inst = self.metas.instantiate(arg_ty);
                    let meta = self.fresh_meta(arg_ty_inst);
                    result = Expr::app(result, meta.clone());
                    ty = self.whnf(&self.metas.instantiate(&body_ty.instantiate(&meta)));
                }
                _ => break,
            }
        }

        // `ty` is now the type after all implicit binders have been filled.
        // Extract the return type by stripping all remaining (explicit) Pi binders.
        let mut return_ty = ty.clone();
        while let ExprKind::Pi(_, _, body) = return_ty.kind() {
            // Use a fresh meta for the explicit arg to get the body type
            let fresh = self.fresh_meta(Expr::type_());
            return_ty = self.whnf(&body.instantiate(&fresh));
        }

        // Unify the return type with the expected type to solve implicit metas.
        // E.g., for Option.some: return_ty = Option ?α, expected = Option Nat → ?α = Nat.
        {
            let ctx = self.build_local_ctx();
            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
            let _ = unifier.unify(&return_ty, &expected_whnf);
        }

        // Instantiate the result to replace solved metas.
        let result = self.metas.instantiate(&result);
        Ok(self.metas.instantiate_levels(&result))
    }

    /// Elaborate an anonymous constructor application `⟨v1, v2, ...⟩`.
    ///
    /// Parser transforms `⟨v1, v2, ...⟩` to `App(Ident("anonymousCtor"), [v1, v2, ...])`.
    /// This method uses the expected type (from declaration context) to determine which
    /// structure/inductive constructor to use, then applies arguments to that constructor.
    ///
    /// Algorithm (based on Lean 4's `elabAnonymousCtor`):
    /// 1. Get expected type from context
    /// 2. Reduce expected type to WHNF and extract head constant
    /// 3. Verify it's a single-constructor inductive
    /// 4. Build constructor application with universe levels and type args
    /// 5. Elaborate and apply explicit arguments
    pub(in crate::infer) fn elab_anonymous_ctor(
        &mut self,
        args: &[SurfaceArg],
    ) -> Result<Expr, ElabError> {
        self.elab_anonymous_ctor_at(args, false)
    }

    /// `elab_anonymous_ctor`, told whether it is already INSIDE Lean's
    /// implicit-lambda loop.
    ///
    /// The distinction is Lean's own and is not cosmetic. `useImplicitLambda`
    /// (`Lean/Elab/Term/TermElabM.lean:1711-1720`) decides whether to ENTER the
    /// loop and refuses unless the leading binder is `{…}` or `[…]` — a leading
    /// `⦃y⦄` is not enough, and pinned lean v4.30.0-rc2 really does reject
    /// `def g : ∀ ⦃y : Nat⦄, Pair := ⟨1, 2⟩` with "the expected type
    /// `⦃y : Nat⦄ → Pair` is not an inductive type". Once inside,
    /// `elabImplicitLambda`'s loop (:1774-1788) peels every binder that is not
    /// EXPLICIT, strict-implicit included, so
    /// `def g : ∀ {x : Nat} ⦃y : Nat⦄, Pair := ⟨1, 2⟩` elaborates to
    /// `fun {x} ⦃y⦄ => …` (measured with `#print` at the same pin).
    fn elab_anonymous_ctor_at(
        &mut self,
        args: &[SurfaceArg],
        in_implicit_lambda: bool,
    ) -> Result<Expr, ElabError> {
        // 1. Get expected type from context
        let expected_ty = self
            .current_expected_type
            .clone()
            .ok_or(ElabError::AnonymousCtorNoExpectedType)?;

        // 1b. IMPLICIT LAMBDA (Lean's `useImplicitLambda` /
        //     `elabImplicitLambda`, `Lean/Elab/Term/TermElabM.lean:1711-1790`,
        //     wired into `elabTermAux` at :1806-1808). When a term's expected
        //     type is `{a : α} → β` or `[a : α] → β`, Lean introduces one fvar
        //     per non-explicit leading binder, elaborates the term at the
        //     residual type, and `mkLambdaFVars` them back — BEFORE the
        //     per-form elaborator runs. `⟨…⟩` is not on the blocker list
        //     (`blockImplicitLambda`, :1684-1688), so
        //     `⟨fun hr ↦ …, fun h' ↦ …⟩` against `∀ {a b}, r a b ↔ f a = b`
        //     really faces `Iff` and not the `∀` (`forall_existsUnique_iff`,
        //     `Mathlib/Logic/Function/Basic.lean`).
        //
        //     Clean's only implicit-lambda insertion lives in `elab_lambda`
        //     (Lean's *other* mechanism, `elabFunBinders`) and so never covers
        //     a non-`fun` surface form. This is the same increment for the one
        //     form that needs it; it cannot double-insert with `elab_lambda`
        //     because a `⟨…⟩` is not a lambda, and Lean's blocked forms (`_`,
        //     `by …`, `@f`, an ascription) never reach this function.
        //
        //     A leading STRICT-implicit `{{a}}` does not OPEN the loop, exactly
        //     as in Lean (`useImplicitLambda`, TermElabM.lean:1719 —
        //     `unless c.isImplicit || c.isInstImplicit do return .no`), but once
        //     the loop is open every non-EXPLICIT binder is peeled
        //     (`elabImplicitLambda`'s loop, :1780 — `if c.isExplicit then …
        //     else peel`), strict implicits included. Both halves are measured
        //     against pinned lean v4.30.0-rc2: `∀ ⦃y⦄, Pair := ⟨1,2⟩` is
        //     REJECTED, `∀ {x} ⦃y⦄, Pair := ⟨1,2⟩` prints `fun {x} ⦃y⦄ => …`.
        //
        //     `@`-explicit mode is NOT a blocker here. Lean's
        //     `blockImplicitLambda` reads the TERM's own syntax (`isExplicit
        //     stx`), and a `⟨…⟩` is never `@`-marked; the enclosing application
        //     being `@f` says nothing about its arguments, which Lean
        //     elaborates with implicit lambdas enabled. Measured: `@h Nat 0
        //     ⟨1, 2⟩` elaborates to `h 0 fun {x} => { a := 1, b := 2 }`.
        let expected_whnf_for_lambda = self.whnf(&expected_ty);
        if let ExprKind::Pi(binder, domain, codomain) = expected_whnf_for_lambda.kind() {
            let opens_or_continues = match binder.info {
                BinderInfo::Implicit | BinderInfo::InstImplicit => true,
                BinderInfo::StrictImplicit => in_implicit_lambda,
                BinderInfo::Default => false,
            };
            if opens_or_continues {
                let binder = *binder;
                let domain = domain.as_ref().clone();
                let codomain = codomain.as_ref().clone();
                // The synthetic binder carries the inaccessible dagger, so no
                // source identifier inside the constructor's fields can resolve
                // to it (capture-freedom, as in `elab_lambda`).
                let fvar = self.push_local(
                    SurfaceName::from_name(Name::anon().str("✝implicit")),
                    domain.clone(),
                );
                let is_inst = self.binder_is_local_instance(binder.info, &domain);
                if is_inst {
                    self.push_local_instance(fvar, domain.clone());
                }
                let residual = {
                    let codomain = codomain.instantiate(&Expr::fvar(fvar));
                    let codomain = self.metas.instantiate(&codomain);
                    self.metas.instantiate_levels(&codomain)
                };
                let prev_expected = self.current_expected_type.replace(residual);
                let inner = self.elab_anonymous_ctor_at(args, true);
                self.current_expected_type = prev_expected;
                if is_inst {
                    self.pop_local_instance();
                }
                self.pop_local();
                let inner = inner?;
                let inner = self
                    .metas
                    .instantiate_levels(&self.metas.instantiate(&inner));
                let domain = self
                    .metas
                    .instantiate_levels(&self.metas.instantiate(&domain));
                return Ok(Expr::lam(binder, domain, inner.abstract_fvar(fvar)));
            }
        }

        // 2. Reduce to WHNF and extract head constant
        let expected_whnf = expected_whnf_for_lambda;
        let _type_args: Vec<Expr> = expected_whnf.get_app_args().into_iter().cloned().collect();

        let struct_name = match expected_whnf.get_app_fn().kind() {
            ExprKind::Const(name, _) => name.clone(),
            // Name the whole expected type, not the bare head kind: the head
            // alone is what the reader already knows is wrong, and rendering
            // an `ExprKind` was a Debug dump of it.
            _ => {
                return Err(ElabError::AnonymousCtorNotInductive(
                    crate::error_render::term(&expected_whnf),
                ));
            }
        };

        // 3. Verify it's a single-constructor inductive
        // Clone the small inductive metadata so we can call `&mut self` methods
        // (e.g. `add_level_constraint`) later without holding a `&self.env` borrow.
        let ind = self
            .env
            .get_inductive(&struct_name)
            .ok_or_else(|| ElabError::AnonymousCtorNotInductive(format!("{struct_name}")))?
            .clone();

        if ind.constructor_names.len() != 1 {
            return Err(ElabError::AnonymousCtorNotSingleCtor(
                struct_name.clone(),
                ind.constructor_names.len(),
            ));
        }

        let ctor_name = ind.constructor_names[0].clone();
        let ctor_name = &ctor_name;
        // Another module's private structure (G21 B3): Lean refuses `⟨...⟩`
        // from an importer.
        self.check_imported_private_ctor(
            &struct_name,
            ctor_name,
            imported_private_access::CtorNotation::Anonymous,
        )?;

        // 4. Build constructor application with universe levels
        // Extract levels from expected type's head constant, or use fresh levels
        let levels: Vec<Level> = match expected_whnf.get_app_fn().kind() {
            ExprKind::Const(_, lvls) => lvls.to_vec(),
            _ => ind
                .level_params
                .iter()
                .map(|p| Level::param(p.clone()))
                .collect(),
        };

        // Get constructor type and insert implicit arguments as metavariables (#173)
        // This handles polymorphic types like Prod.mk : {α : Type u} → {β : Type v} → α → β → Prod α β
        let ctor_info = self
            .env
            .get_const(ctor_name)
            .ok_or_else(|| ElabError::UnknownIdent(ctor_name.to_string()))?;
        let ctor_type = ctor_info.type_.clone();

        // Substitute universe parameters with concrete levels from expected type (#173 fix)
        // Without this, implicit arg types retain abstract levels (Type u) instead of
        // concrete ones (Type 0), causing TypeMismatch during verification.
        // Guard: reject level count mismatch to prevent silent zip truncation (#1277)
        if ind.level_params.len() != levels.len() {
            return Err(ElabError::TypeMismatch {
                expected: format!(
                    "{} universe levels for {}",
                    ind.level_params.len(),
                    struct_name
                ),
                actual: format!("{} universe levels supplied", levels.len()),
            });
        }
        let level_subst: Vec<(Name, Level)> = ind
            .level_params
            .iter()
            .cloned()
            .zip(levels.iter().cloned())
            .collect();
        let ctor_type = ctor_type.instantiate_level_params(&level_subst);

        let expected_args: Vec<Expr> = expected_whnf.get_app_args().into_iter().cloned().collect();
        if expected_args.len() < ind.num_params as usize {
            return Err(ElabError::TypeMismatch {
                expected: format!(
                    "{} constructor parameters for {}",
                    ind.num_params, struct_name
                ),
                actual: format!("{} parameters supplied", expected_args.len()),
            });
        }

        // Solve abstract universe-level *parameters* carried by the expected type.
        //
        // When the expected type is `Exists.{u_1} Nat pred` (the goal of an
        // `∃ m, …` proof), `u_1` is a free `Level::Param`, NOT a metavariable —
        // it was never constrained during goal elaboration. The proof term we
        // build inherits that `u_1`. `try_unify(result_ty, expected_ty)` below
        // cannot fix it because BOTH sides carry the SAME `u_1`, so the unifier
        // sees a reflexive (already-equal) level and commits nothing. The kernel
        // later rejects the term: `Exists.intro.{u_1}` requires `α : Sort u_1`,
        // but `α = Nat : Sort 1`, so `u_1` ≠ `Succ Zero` → TypeMismatch.
        //
        // Mirror the `existsi` universe-level fix (existential.rs): commit the
        // level parameter to the *concrete* universe of the inductive's type
        // parameter. For each inductive parameter binder whose declared type is
        // `Sort (Param p)`, infer the universe of the corresponding expected
        // type-argument (`infer_type(Nat) = Sort 1`) and record `p := that
        // level` in the level union-find. `instantiate_levels` (already applied
        // to the returned term) then realizes the solved `p` before the kernel
        // re-check.
        //
        // SOUNDNESS: `add_level_constraint` is conflict-checked — it refuses to
        // overwrite an existing concrete assignment with a different level, so a
        // genuinely-polymorphic or already-pinned level is never silently
        // changed. This only *solves* an otherwise-unconstrained parameter; the
        // assembled proof is still kernel-rechecked by `add_decl`, so a wrong
        // commitment fails downstream rather than slipping through.
        {
            // Walk the inductive's parameter telescope, instantiating its OWN
            // level params with `levels` (the concrete/expected levels) so the
            // domain Sort we inspect carries the SAME level head (`u_1`) that the
            // built term uses — not the inductive's abstract `u`.
            let mut telescope = ind.type_.clone().instantiate_level_params(&level_subst);
            for type_arg in expected_args.iter().take(ind.num_params as usize) {
                let telescope_whnf = self.whnf(&telescope);
                let ExprKind::Pi(_, dom, body) = telescope_whnf.kind() else {
                    break;
                };
                let body = body.clone();
                // Is this parameter a type whose universe is a free Param? (e.g.
                // `α : Sort u_1` for `Exists`). If so, solve `u_1` from the actual
                // type-argument's universe (`Nat : Sort 1`).
                if let ExprKind::Sort(Level::Param(p)) = self.whnf(dom).kind() {
                    let p = p.clone();
                    if let Ok(arg_ty) = self.infer_type(type_arg) {
                        if let ExprKind::Sort(concrete) = self.whnf(&arg_ty).kind() {
                            // Best-effort: ignore conflicts (a real conflict means
                            // the level was already pinned to the correct value).
                            let _ = self.metas.add_level_constraint(p, concrete.clone());
                        }
                    }
                }
                telescope = body.instantiate(type_arg);
            }
        }

        let mut result = Expr::const_(ctor_name.clone(), levels);
        let mut result_ty = ctor_type;

        for arg in expected_args.iter().take(ind.num_params as usize) {
            result_ty = self.whnf(&result_ty);
            let body_ty = match result_ty.kind() {
                ExprKind::Pi(_, _, body_ty) => body_ty.instantiate(arg),
                _ => {
                    return Err(ElabError::TypeMismatch {
                        expected: format!(
                            "constructor telescope for {} with {} parameters",
                            struct_name, ind.num_params
                        ),
                        actual: format!("{result_ty}"),
                    })
                }
            };
            result = Expr::app(result, arg.clone());
            result_ty = self.metas.instantiate(&body_ty);
        }

        // `⟨a, …⟩` is Lean's `C.mk a …` (`elabAnonymousCtor`): its arguments
        // are what follows the constructor's leading implicits.
        let (result, result_ty) =
            self.insert_implicit_args(result, &result_ty, ArgsFollow::from_remaining(args.len()));

        // N-ary flattening (Lean 4 `elabAnonymousCtor`, BuiltinNotation.lean):
        // when the constructor has M explicit fields but N > M arguments are
        // supplied, the first M-1 arguments fill the first M-1 fields and the
        // REMAINING arguments (indices M-1..N) are grouped into a single nested
        // `⟨…⟩` for the LAST field, recursively. So `⟨ha, hb, hc⟩` against the
        // right-associated `a ∧ (b ∧ c)` (And has 2 fields) becomes
        // `⟨ha, ⟨hb, hc⟩⟩`, and `⟨ha, hb, hc, hd⟩` against `a ∧ (b ∧ (c ∧ d))`
        // becomes `⟨ha, ⟨hb, ⟨hc, hd⟩⟩⟩` once the recursion fires on the nested
        // anonymous constructor's own elaboration.
        //
        // This is the EXACT analog of the `rcases`/`rintro` flattening rule
        // (`tactic/pattern/rintro.rs::destruct_hypothesis`), but on the
        // term-elaboration side for the anonymous constructor `⟨…⟩` value.
        //
        // SOUNDNESS: this only regroups surface arguments before the existing
        // per-field elaboration loop runs — every grouped argument is still
        // elaborated against its field's expected type and kernel-rechecked by
        // `add_decl`. If the last field is NOT itself a single-constructor
        // inductive, the nested `⟨…⟩` re-enters `elab_anonymous_ctor` and fails
        // there (`AnonymousCtorNotInductive`), so an over-long flat tuple can
        // never silently typecheck. Too-FEW arguments are unaffected (no
        // regrouping happens) and still fail in the loop below as before.
        let num_fields = Self::count_explicit_binders(&result_ty);

        // Subobject flattening for `extends` targets (Lean's subobject layout):
        // when the constructor embeds parent structures as subobject fields
        // (`B.mk : A → Nat → B`), a flat `⟨1, 2⟩` distributes across the
        // flattened leaf fields and wraps each subobject field's share in a
        // nested `⟨…⟩`, so it builds `B.mk (A.mk 1) 2`. Runs before the trailing
        // n-ary flatten and only when the target has recorded parent subobjects,
        // so non-`extends` structures (And/Exists/Prod/…) are untouched.
        let subobject_grouped: Option<Vec<SurfaceArg>> =
            self.flatten_anon_ctor_subobjects(&struct_name, num_fields, args);

        // Lean's own rule FIRST. `elabAnonymousCtor` has no subobject
        // flattening: when the argument count equals the constructor's explicit
        // field count it emits `ctor args` as written
        // (`Lean/Elab/BuiltinNotation.lean:43-100`), so `⟨⟨a⟩, h⟩ : Unique α`
        // is `Unique.mk ⟨a⟩ h`. The subobject regrouping above also fires on
        // that count whenever every parent contributes ONE leaf, and wrapped
        // the already-nested `⟨a⟩` a second time: `⟨⟨a⟩, h⟩ : Unique α` died
        // "Anonymous constructor ⟨⟩ expected inductive type, got α"
        // (`unique_iff_existsUnique`, `unique_subtype_iff_existsUnique`, Mathlib
        // `Logic/Unique.lean`), and `⟨⟨1⟩, 2⟩ : B` for `B extends A` was
        // refused. The as-written reading is tried in a transaction; when it
        // fails, every side effect is rolled back and the regrouped reading —
        // the flat spelling Clean has always accepted — runs as before, so
        // this only ADDS the reading Lean has.
        if subobject_grouped.is_some() && args.len() == num_fields {
            let as_written = self.with_local_scope_rollback(|this| {
                this.apply_anonymous_ctor_args(
                    result.clone(),
                    result_ty.clone(),
                    args,
                    &expected_ty,
                )
            });
            if let Ok(term) = as_written {
                return Ok(term);
            }
        }

        // N-ary flattening (Lean 4 `elabAnonymousCtor`, BuiltinNotation.lean):
        // when the constructor has M explicit fields but N > M arguments are
        // supplied, the first M-1 arguments fill the first M-1 fields and the
        // REMAINING arguments (indices M-1..N) are grouped into a single nested
        // `⟨…⟩` for the LAST field, recursively. So `⟨ha, hb, hc⟩` against the
        // right-associated `a ∧ (b ∧ c)` (And has 2 fields) becomes
        // `⟨ha, ⟨hb, hc⟩⟩`, and `⟨ha, hb, hc, hd⟩` against `a ∧ (b ∧ (c ∧ d))`
        // becomes `⟨ha, ⟨hb, ⟨hc, hd⟩⟩⟩` once the recursion fires on the nested
        // anonymous constructor's own elaboration.
        //
        // This is the EXACT analog of the `rcases`/`rintro` flattening rule
        // (`tactic/pattern/rintro.rs::destruct_hypothesis`), but on the
        // term-elaboration side for the anonymous constructor `⟨…⟩` value.
        //
        // SOUNDNESS: this only regroups surface arguments before the existing
        // per-field elaboration loop runs — every grouped argument is still
        // elaborated against its field's expected type and kernel-rechecked by
        // `add_decl`. If the last field is NOT itself a single-constructor
        // inductive, the nested `⟨…⟩` re-enters `elab_anonymous_ctor` and fails
        // there (`AnonymousCtorNotInductive`), so an over-long flat tuple can
        // never silently typecheck. Too-FEW arguments are unaffected (no
        // regrouping happens) and still fail in the loop below as before.
        let grouped_args: Vec<SurfaceArg>;
        let args: &[SurfaceArg] = if let Some(g) = subobject_grouped.as_ref() {
            g.as_slice()
        } else if num_fields >= 1 && args.len() > num_fields {
            // Span covering the grouped trailing arguments, used for the synthetic
            // nested anonymous-constructor node.
            let group_span = args[num_fields - 1].span.merge(args[args.len() - 1].span);
            let nested = SurfaceExpr::App(
                group_span,
                Box::new(SurfaceExpr::Ident(
                    group_span,
                    clean_parser::anonymous_constructor_head(),
                )),
                args[num_fields - 1..].to_vec(),
            );
            grouped_args = args[..num_fields - 1]
                .iter()
                .cloned()
                .chain(std::iter::once(SurfaceArg::positional(nested)))
                .collect();
            &grouped_args
        } else {
            args
        };

        // 5. Elaborate and apply explicit arguments with expected type context (#173 fix)
        self.apply_anonymous_ctor_args(result, result_ty, args, &expected_ty)
    }

    /// Apply an anonymous constructor's explicit `args` to `result` (the
    /// constructor already applied to its parameters and leading implicits,
    /// of type `result_ty`), then unify the result type with `expected_ty`.
    ///
    /// Each argument is elaborated against its field's type, which lets
    /// unification solve the implicit type parameters (`α := Nat` when
    /// elaborating `42` in `⟨42, true⟩`).
    fn apply_anonymous_ctor_args(
        &mut self,
        mut result: Expr,
        mut result_ty: Expr,
        args: &[SurfaceArg],
        expected_ty: &Expr,
    ) -> Result<Expr, ElabError> {
        for arg in args {
            // Get expected arg type from result_ty (which is a Pi type)
            result_ty = self.whnf(&result_ty);
            let expected_arg_ty = match result_ty.kind() {
                // Beta-reduce the Pi domain so the per-component expected type is
                // already reduced (matches Lean's App.lean arg-type computation).
                // For a dependent constructor like Exists.intro, the domain of a
                // later field is the predicate applied to an earlier elaborated
                // field (e.g. `(fun n => n > 0) 1`); beta-reducing it here yields
                // `1 > 0` for both term and tactic components, while keeping the
                // `GT.gt`/`LE.le` typeclass head intact (full WHNF would unfold
                // it to `Nat.le`, which head-matching tactics do not recognize).
                ExprKind::Pi(_, arg_ty, _) => Some(crate::tactic::simp::beta_reduce(
                    &self.metas.instantiate(arg_ty),
                )),
                _ => None,
            };

            // Set expected type for elaboration to enable bidirectional checking
            let arg_expr =
                self.elaborate_arg_with_expected_type(&arg.expr, expected_arg_ty.clone())?;

            if let Some(exp_ty) = expected_arg_ty.as_ref() {
                self.enforce_expr_type(&arg_expr, exp_ty)?;
            }

            result = Expr::app(result, arg_expr.clone());

            // Update result_ty by substituting through pi
            if let ExprKind::Pi(_, _, body_ty) = result_ty.kind() {
                result_ty = body_ty.instantiate(&arg_expr);
            }
        }

        // Unify result type with expected type to solve any remaining metavariables
        let result_ty = self.metas.instantiate(&result_ty);
        if !self.try_unify(&result_ty, expected_ty) {
            return Err(ElabError::TypeMismatch {
                expected: format!("{expected_ty}"),
                actual: format!("{result_ty}"),
            });
        }

        let result = self.metas.instantiate(&result);
        Ok(self.metas.instantiate_levels(&result))
    }

    /// Distribute a flat anonymous-constructor argument list across the
    /// flattened leaf fields of an `extends` target, wrapping each parent
    /// subobject field's share in a nested `⟨…⟩`. Returns the regrouped `n`
    /// arguments (one per explicit constructor field), or `None` when the
    /// target has no recorded parent subobjects or the argument count does not
    /// match the flattened leaf count (so the caller falls through to the
    /// ordinary/trailing behavior).
    ///
    /// Mirrors Lean's subobject constructor: `⟨1, 2⟩ : B` for `B extends A`
    /// (with `B.mk : A → Nat → B`) rebuilds `B.mk ⟨1⟩ 2 = B.mk (A.mk 1) 2`.
    /// Only the exact flattened-leaf match is handled, so ambiguous shapes fall
    /// through rather than silently regrouping.
    fn flatten_anon_ctor_subobjects(
        &self,
        struct_name: &Name,
        num_fields: usize,
        args: &[SurfaceArg],
    ) -> Option<Vec<SurfaceArg>> {
        let parents = self.env.get_structure_parents(struct_name)?;
        if parents.is_empty() {
            return None;
        }
        let field_names = self.env.get_structure_field_names(struct_name)?;
        if field_names.len() != num_fields {
            return None;
        }

        // Per explicit field: (leaf-arity, is-subobject-parent?).
        let per_field: Vec<(usize, bool)> = field_names
            .iter()
            .map(|f| match parents.iter().find(|(sf, _)| sf == f) {
                Some((_, parent)) => (self.flattened_leaf_arity(parent, 0), true),
                None => (1, false),
            })
            .collect();

        let total: usize = per_field.iter().map(|(count, _)| count).sum();
        if total != args.len() {
            return None;
        }

        let mut out: Vec<SurfaceArg> = Vec::with_capacity(num_fields);
        let mut idx = 0;
        for (count, is_subobject) in per_field {
            let slice = &args[idx..idx + count];
            idx += count;
            if is_subobject {
                // Wrap the subobject field's share in a nested anonymous ctor;
                // its own elaboration recurses (flattening any grandparents).
                let span = if slice.is_empty() {
                    clean_parser::Span::dummy()
                } else {
                    slice[0].span.merge(slice[slice.len() - 1].span)
                };
                let nested = SurfaceExpr::App(
                    span,
                    Box::new(SurfaceExpr::Ident(
                        span,
                        clean_parser::anonymous_constructor_head(),
                    )),
                    slice.to_vec(),
                );
                out.push(SurfaceArg::positional(nested));
            } else {
                out.push(slice[0].clone());
            }
        }
        Some(out)
    }

    /// The number of flattened leaf fields of a structure `s` — its own
    /// non-subobject fields plus, recursively, the leaf fields of each parent
    /// subobject. A leaf (non-`extends`) structure's leaf count equals its
    /// constructor field count. `depth` guards against pathological metadata.
    fn flattened_leaf_arity(&self, s: &Name, depth: usize) -> usize {
        if depth > 64 {
            return 1;
        }
        let Some(fields) = self.env.get_structure_field_names(s) else {
            return 1;
        };
        let parents = self.env.get_structure_parents(s);
        let mut total = 0;
        for f in fields {
            match parents.and_then(|ps| ps.iter().find(|(sf, _)| sf == f)) {
                Some((_, parent)) => total += self.flattened_leaf_arity(parent, depth + 1),
                None => total += 1,
            }
        }
        total
    }

    /// Solve still-abstract universe-level *parameters* on the head constant of
    /// an assembled application from its now-concrete type arguments.
    ///
    /// When a polymorphic constant is elaborated, its universe-level parameters
    /// are instantiated with fresh `Level::Param`s (`fresh_universe_param`), NOT
    /// proper metavariables. Ordinary expression unification solves the value
    /// metavars (`?α := Nat`) but can leave such a level param unconstrained when
    /// the type argument was elided — e.g. `∃ m, n = m + 1` desugars to
    /// `Exists.{u_1} ?α (fun m => …)`; `?α` is solved to `Nat` from the predicate
    /// domain, yet `u_1` (the universe of `α : Sort u_1`) never gets pinned. The
    /// kernel then rejects the term: `Exists.{u_1}` needs `Nat : Sort u_1`, but
    /// `Nat : Sort 1`.
    ///
    /// Mirrors the `existsi` universe fix: walk the head constant's declared type
    /// telescope alongside the supplied arguments; for each binder whose domain is
    /// `Sort (Param p)`, infer the universe of the corresponding (now-concrete)
    /// argument and record `p := that level` in the level union-find. A later
    /// `instantiate_levels` realizes it.
    ///
    /// SOUNDNESS: `add_level_constraint` is conflict-checked, so a level already
    /// pinned to a different concrete value is never overwritten; this only
    /// *solves* an otherwise-free parameter. The term is still kernel-rechecked.
    /// Best-effort: any failure (unknown const, non-`Sort` binder, infer error)
    /// is silently skipped, leaving the term exactly as before.
    pub(in crate::infer) fn solve_head_const_levels(&mut self, app: &Expr) {
        let head = app.get_app_fn();
        let ExprKind::Const(name, levels) = head.kind() else {
            return;
        };
        // Nothing to solve unless at least one level is a bare param.
        if !levels.iter().any(|l| matches!(l, Level::Param(_))) {
            return;
        }
        let Some(const_info) = self.env.get_const(name) else {
            return;
        };
        // Instantiate the constant's declared type with the term's ACTUAL levels
        // so the domain `Sort`s we inspect carry the same level head (`u_1`) that
        // the assembled term uses — not the constant's own abstract param (`u`).
        if const_info.level_params.len() != levels.len() {
            return;
        }
        let level_subst: Vec<(Name, Level)> = const_info
            .level_params
            .iter()
            .cloned()
            .zip(levels.iter().cloned())
            .collect();
        let mut telescope = const_info
            .type_
            .clone()
            .instantiate_level_params(&level_subst);
        let args: Vec<Expr> = app.get_app_args().into_iter().cloned().collect();
        for arg in &args {
            let telescope_whnf = self.whnf(&telescope);
            let ExprKind::Pi(_, dom, body) = telescope_whnf.kind() else {
                break;
            };
            let body = body.clone();
            if let ExprKind::Sort(Level::Param(p)) = self.whnf(dom).kind() {
                let p = p.clone();
                if let Ok(arg_ty) = self.infer_type(arg) {
                    if let ExprKind::Sort(concrete) = self.whnf(&arg_ty).kind() {
                        let _ = self.metas.add_level_constraint(p, concrete.clone());
                    }
                }
            }
            telescope = body.instantiate(arg);
        }
    }

    /// Insert implicit arguments for a function application.
    /// Returns the function with all implicit arguments applied, and the remaining function type.
    ///
    /// For InstImplicit binders `[inst : T]`, this attempts instance resolution.
    /// If resolution fails, falls back to creating a metavariable (which may be
    /// resolved later by unification).
    ///
    /// When `explicit_mode` is true (#1231), no implicit arguments are inserted.
    /// This implements the semantics of the @ marker: `@f` requires all arguments
    /// (including implicit ones) to be provided explicitly.
    ///
    /// `follow` says whether explicit arguments remain after this run: a
    /// strict-implicit `⦃x⦄` binder is filled only when one does (see
    /// [`ArgsFollow`]). When the run stops at a `⦃x⦄` binder, the returned type
    /// is the FOLDED remaining type (`Function.Injective f`, not its unfolded
    /// `∀ ⦃a₁ a₂⦄, …`), as Lean's `finalize` re-infers the type instead of
    /// reusing the `whnfForall`-unfolded `fType` (`Lean/Elab/App.lean`: "it
    /// may have been unfolded").
    pub(in crate::infer) fn insert_implicit_args(
        &mut self,
        func: Expr,
        func_type: &Expr,
        follow: ArgsFollow,
    ) -> (Expr, Expr) {
        // In explicit mode, don't insert implicit arguments (#1231)
        if self.explicit_mode {
            return (func, func_type.clone());
        }

        let mut result = func;
        let mut folded = self.metas.instantiate(func_type);
        let mut ty = self.whnf(&folded);

        loop {
            match ty.kind() {
                ExprKind::Pi(bi, _, _) if Self::stops_at_strict_implicit(*bi, follow) => {
                    return (result, folded);
                }
                ExprKind::Pi(bi, arg_ty, body_ty) if Self::is_implicit_binder(*bi) => {
                    let arg_ty_inst = self.metas.instantiate(arg_ty);

                    // For InstImplicit, try instance resolution first. An
                    // unresolved instance remains a metavariable so later
                    // unification can pin its carrier; never manufacture
                    // evidence for a ground `Decidable` goal.
                    let arg = if bi.info == BinderInfo::InstImplicit {
                        if let Some(inst) = self.resolve_instance(&arg_ty_inst) {
                            inst
                        } else {
                            // Fall back to metavariable if no instance found.
                            // A heterogeneous-operator goal that `resolve_instance`
                            // POSTPONED (every type argument still open) is recorded
                            // so the enclosing application can retry it once a
                            // sibling argument grounds the carrier; every other
                            // unresolved goal is recorded by nobody and keeps the
                            // pre-existing leak-then-fail-closed path.
                            let meta = self.fresh_meta(arg_ty_inst.clone());
                            if self.instance_search_stuck {
                                // Lean's "typeclass instance problem is stuck"
                                // (`Pure ?m`, `Monad ?m`, … with the monad still
                                // open — `instance::is_monad_family_class`):
                                // QUEUE it for the declaration-boundary drain
                                // rather than leaking an unassigned slot. Until
                                // 2026-09-28 such goals never arose; the monad
                                // operations were instance-less axioms.
                                self.record_postponed_stuck_instance(&meta, &arg_ty_inst);
                            } else {
                                self.record_postponed_open_carrier_instance(&meta, &arg_ty_inst);
                            }
                            meta
                        }
                    } else {
                        // For regular implicit/strict implicit, use a NATURAL
                        // metavariable — Lean's `mkFreshExprMVar` for an
                        // implicit argument (`Lean/Elab/App.lean`
                        // `addImplicitArg`), whose context `ctxApprox` may
                        // narrow (`unify::meta_id::MetaKind`).
                        self.fresh_natural_meta(arg_ty_inst)
                    };

                    result = Expr::app(result, arg.clone());
                    // Instantiate the body type with the argument
                    folded = self.metas.instantiate(&body_ty.instantiate(&arg));
                    ty = self.whnf(&folded);
                }
                _ => break,
            }
        }

        (result, ty)
    }

    /// Like [`Self::insert_implicit_args`], but does *not* resolve
    /// instance-implicit binders eagerly. Each `[inst : C ?α]` binder is filled
    /// with a fresh metavariable and recorded; the caller is expected to unify
    /// the returned result type with the expected type first (pinning carrier
    /// metavariables such as `?α`) and then resolve the recorded instance
    /// metavariables via [`Self::resolve_deferred_instances`].
    ///
    /// This mirrors Lean 4's postponement of typeclass resolution until the
    /// surrounding type information is available. Resolving instances eagerly
    /// against an unconstrained carrier metavariable would pick whichever
    /// registered instance happens to come first (e.g. the first `Pick`
    /// instance) instead of the one the expected type demands — a real bug for
    /// methods whose carrier is determined by their result type.
    ///
    /// Returns `(applied_expr, remaining_type, pending_instances)` where each
    /// pending entry is `(instance_metavar, instance_goal_type)`.
    ///
    /// `follow` is [`Self::insert_implicit_args`]'s strict-implicit stop rule,
    /// with the same folded-type result when the run stops at a `⦃x⦄` binder.
    pub(in crate::infer) fn insert_implicit_args_deferring_instances(
        &mut self,
        func: Expr,
        func_type: &Expr,
        follow: ArgsFollow,
    ) -> (Expr, Expr, Vec<(Expr, Expr)>) {
        if self.explicit_mode {
            return (func, func_type.clone(), Vec::new());
        }

        let mut result = func;
        let mut folded = self.metas.instantiate(func_type);
        let mut ty = self.whnf(&folded);
        let mut pending = Vec::new();

        loop {
            match ty.kind() {
                ExprKind::Pi(bi, _, _) if Self::stops_at_strict_implicit(*bi, follow) => {
                    return (result, folded, pending);
                }
                ExprKind::Pi(bi, arg_ty, body_ty) if Self::is_implicit_binder(*bi) => {
                    let arg_ty_inst = self.metas.instantiate(arg_ty);

                    // An instance slot stays OPAQUE: it is recorded in
                    // `pending` and assigned later by
                    // `resolve_deferred_instances`. Every other implicit is a
                    // NATURAL metavariable (see `insert_implicit_args`).
                    let arg = if bi.info == BinderInfo::InstImplicit {
                        let arg = self.fresh_meta(arg_ty_inst.clone());
                        pending.push((arg.clone(), arg_ty_inst));
                        arg
                    } else {
                        self.fresh_natural_meta(arg_ty_inst)
                    };

                    result = Expr::app(result, arg.clone());
                    folded = self.metas.instantiate(&body_ty.instantiate(&arg));
                    ty = self.whnf(&folded);
                }
                _ => break,
            }
        }

        (result, ty, pending)
    }

    /// Resolve a set of deferred instance metavariables produced by
    /// [`Self::insert_implicit_args_deferring_instances`].
    ///
    /// Each goal type is re-instantiated (so carrier metavariables pinned by a
    /// prior unification with the expected type are reflected) before being
    /// resolved. On success the instance metavariable is assigned the resolved
    /// instance expression. Unresolved goals return `false`; callers either
    /// retry after more unification or report a typed synthesis failure.
    ///
    /// Returns `true` iff every deferred instance was resolved and assigned. On
    /// `false` the caller should fall back to eager insertion so behavior is
    /// never worse than before.
    pub(in crate::infer) fn resolve_deferred_instances(
        &mut self,
        pending: &[(Expr, Expr)],
    ) -> bool {
        for (meta_arg, goal_ty) in pending {
            let goal_ty = self.whnf(&self.metas.instantiate(goal_ty));

            let resolved = if let Some(inst) = self.resolve_instance(&goal_ty) {
                inst
            } else {
                return false;
            };

            let ExprKind::FVar(fvar) = meta_arg.kind() else {
                return false;
            };
            let Some(meta_id) = MetaState::from_fvar(*fvar) else {
                return false;
            };
            if !self.metas.assign(meta_id, resolved) {
                return false;
            }
        }
        true
    }

    /// [`Self::resolve_deferred_instances`], except that a goal the search
    /// reports STUCK — `ElabCtx::instance_search_stuck`, Lean's "typeclass
    /// instance problem is stuck" — is QUEUED for the drain instead of
    /// failing the caller.
    ///
    /// Lean's order is `Lean/Elab/App.lean:496-502`: `finalize` unifies the
    /// application's type with the expected type and only THEN runs
    /// `synthesizeAppInstMVars`, so `Preorder ?α` is `Preorder α` before
    /// synthesis ever runs. Clean's caller has just unified an OPEN expected
    /// metavariable with the inserted type, which is the same moment — the
    /// carrier is still open here and the enclosing term is what pins it.
    ///
    /// An ABSENT instance still fails the caller, so the speculative path
    /// rolls back exactly as it did: only the stuck verdict is new.
    pub(in crate::infer) fn resolve_deferred_instances_postponing_stuck(
        &mut self,
        pending: &[(Expr, Expr)],
    ) -> bool {
        let mut stuck: Vec<(Expr, Expr)> = Vec::new();
        for (meta_arg, goal_ty) in pending {
            let goal_ty = self.whnf(&self.metas.instantiate(goal_ty));
            match self.resolve_instance(&goal_ty) {
                Some(inst) => {
                    let ExprKind::FVar(fvar) = meta_arg.kind() else {
                        return false;
                    };
                    let Some(meta_id) = MetaState::from_fvar(*fvar) else {
                        return false;
                    };
                    if !self.metas.assign(meta_id, inst) {
                        return false;
                    }
                }
                None => {
                    if !self.instance_search_stuck {
                        return false;
                    }
                    stuck.push((meta_arg.clone(), goal_ty));
                }
            }
        }
        for (meta_arg, goal_ty) in stuck {
            self.record_postponed_stuck_instance(&meta_arg, &goal_ty);
        }
        true
    }

    /// Queue an instance goal the search reported STUCK, for
    /// [`Self::retry_postponed_open_carrier_instances`].
    ///
    /// Distinct from [`Self::record_postponed_open_carrier_instance`], which
    /// is Lean's default-instance collapse for the heterogeneous-operator
    /// classes and PINS slots when it drains. Nothing is pinned here: the goal
    /// is simply re-resolved once the surrounding term has grounded it, and a
    /// goal that never grounds leaves its metavariable unassigned for the
    /// fail-closed residual guard in `elab_decl_value` to report — which is
    /// what Lean does with a synthetic instance metavariable nothing solves.
    ///
    /// Refuses a goal with no metavariable left: nothing could ever change its
    /// answer, so queueing it would only defer a failure the caller should
    /// report where it happened.
    pub(in crate::infer) fn record_postponed_stuck_instance(
        &mut self,
        meta_arg: &Expr,
        goal_ty: &Expr,
    ) {
        let ExprKind::FVar(fvar) = meta_arg.kind() else {
            return;
        };
        if MetaState::from_fvar(*fvar).is_none() {
            return;
        }
        let goal = self.metas.instantiate(goal_ty);
        if crate::instances::extract_class_app(&goal).is_none() || !self.has_metavars(&goal) {
            return;
        }
        self.postponed_open_carrier_instances
            .push((meta_arg.clone(), goal));
    }

    /// An explicit `_` at an instance-implicit binder whose synthesis failed.
    ///
    /// Lean elaborates that `_` as a SYNTHETIC instance metavariable, not a
    /// user hole (`Lean/Elab/App.lean`, `addInstMVar`), so an unsatisfiable
    /// goal is reported as "failed to synthesize". Until 2026-09-29 Clean made
    /// it an ordinary hole: the fail-closed residual guard exempts user holes
    /// (their goal is agent feedback), so `Empty.elim (@Inhabited.default
    /// Empty _)` reached the kernel and was refused only as "contains free
    /// variables". A GROUND goal can never become satisfiable, so it fails
    /// here; a goal that still mentions a metavariable is queued like any
    /// stuck instance goal and, if nothing ever solves it, is named by the
    /// residual guard at declaration close as the instance goal it is.
    fn explicit_inst_hole_unsynthesized(&mut self, goal_ty: &Expr) -> Result<Expr, ElabError> {
        let goal = self.metas.instantiate(goal_ty);
        if !self.has_metavars(&goal) {
            return Err(ElabError::FailedToSynthesizeInstance {
                goal: format!("{goal}"),
                detail: self.instance_failure_detail(&goal),
            });
        }
        let meta = self.fresh_meta(goal.clone());
        self.record_postponed_stuck_instance(&meta, &goal);
        Ok(meta)
    }

    /// Record an instance metavariable whose goal `resolve_instance`
    /// POSTPONED: a heterogeneous operator goal every one of whose type
    /// arguments is still an open metavariable (Lean's own refusal — see
    /// `instance::is_hetero_binop_default_instance_class` for the measured
    /// message). A no-op for every other unresolved goal, so the pre-existing
    /// leak-then-fail-closed paths are untouched.
    pub(in crate::infer) fn record_postponed_open_carrier_instance(
        &mut self,
        meta_arg: &Expr,
        goal_ty: &Expr,
    ) {
        let ExprKind::FVar(fvar) = meta_arg.kind() else {
            return;
        };
        if MetaState::from_fvar(*fvar).is_none() {
            return;
        }
        let goal = self.metas.instantiate(goal_ty);
        let Some((class_name, args)) = crate::instances::extract_class_app(&goal) else {
            return;
        };
        if args.is_empty()
            || !(instance::is_hetero_binop_default_instance_class(&class_name)
                || class_name == Name::from_string("DecidableEq"))
        {
            return;
        }
        // The doc above says "every one of whose type arguments is still an
        // open metavariable", and until now only the CLASS was checked. The
        // real postpone condition in `resolve_instance` is the `all(bare
        // unassigned meta)` test at `instance.rs`'s phase-1 exit, and a goal
        // that fails it was a genuine resolution FAILURE, never a postponement.
        //
        // Queueing such a goal was not merely cosmetic. The drain performs
        // Lean's default-instance collapse on whatever it holds: it takes the
        // first metavariable-free linked argument as the carrier and pins every
        // still-open linked slot onto it, in the GLOBAL `MetaState` with no
        // enclosing scope — so when resolution then fails anyway, that
        // speculative assignment is never rolled back. For `def bad (a b :
        // Widget) := a % b` the partially-determined `HMod Widget Widget ?γ`
        // was queued, `?γ` was pinned to `Widget`, and the declaration-close
        // diagnostic then reported a fully GROUND goal and dropped its "the
        // goal is NOT fully determined" paragraph — the honest half of the
        // message, and the half that tells the user to ascribe the result type.
        //
        // The all-open shapes the drain exists for are untouched: `(· + ·)` and
        // `fun a b => a + b` are elaborated with every slot open, so they still
        // record and still drain.
        if !args.iter().all(|a| {
            instance::bare_unassigned_meta(&self.metas, &self.metas.instantiate(a)).is_some()
        }) {
            return;
        }
        self.postponed_open_carrier_instances
            .push((meta_arg.clone(), goal));
    }

    /// Is `goal` a heterogeneous-operator instance goal (`HAdd α β γ`, …,
    /// [`instance::is_hetero_binop_default_instance_class`]) whose INPUT
    /// arguments are all metavariable-free — every argument but the last, the
    /// result slot `γ`, which Lean declares `outParam`?
    ///
    /// Such a goal is DETERMINED: Lean's `synthesizeInstMVarCore` replaces an
    /// `outParam` by a fresh metavariable before searching, so an open `γ`
    /// never makes the problem postponable, and a failed search is reported
    /// ("failed to synthesize `HAdd (Fin 4) Nat ?m`") where it happens. Nothing
    /// a later unification can do to `γ` makes an instance exist for inputs
    /// that already have none — the only thing a later assignment of `γ` could
    /// do is what it did here: let a sibling numeral default `γ` to `Nat`, after
    /// which the carrier-first pass read `Nat` off the failed operator and
    /// re-elaborated the `Fin` leaf through the `Fin → Nat` coercion.
    ///
    /// Only the operator classes, whose `outParam` position is fixed by Lean's
    /// declarations (`class HAdd (α : Type u) (β : Type v) (γ : outParam (Type
    /// w))`, and likewise for every class in that list), are judged here; any
    /// other goal keeps the metavariable-free test.
    pub(in crate::infer) fn hetero_binop_goal_is_determined(&self, goal: &Expr) -> bool {
        let goal = self.metas.instantiate(goal);
        let Some((class_name, args)) = crate::instances::extract_class_app(&goal) else {
            return false;
        };
        if !instance::is_hetero_binop_default_instance_class(&class_name) {
            return false;
        }
        let Some((_out_param, inputs)) = args.split_last() else {
            return false;
        };
        !inputs.is_empty()
            && inputs
                .iter()
                .all(|a| !self.has_metavars(&self.metas.instantiate(a)))
    }

    /// Re-resolve the postponed heterogeneous-operator instance goals whose
    /// carrier a sibling argument has since grounded.
    ///
    /// This is the second half of Lean's rule. Lean postpones
    /// `HAdd ?b ?a ?g`; its `@[default_instance] instHAdd [Add α] : HAdd α α α`
    /// (priority `default`) then collapses the three slots onto whichever one
    /// the rest of the term determined, and only the low-priority
    /// `@[default_instance 100] instOfNatNat` defaults what is still open. So
    /// `List.foldl (· + ·) (0 : Int) [1, 2, 3]` is `Int` and
    /// `List.foldl (· + ·) 0 [1, 2, 3]` is `Nat` — both measured on the pinned
    /// v4.30.0-rc2. [`Self::pin_open_type_slots`] is that collapse: it assigns
    /// only OPEN slots and only from a metavariable-free carrier, so it can
    /// neither reshape a slot the term already pinned nor invent one.
    ///
    /// A goal that is still ungrounded stays queued. A goal that never grounds
    /// leaves its metavariable unassigned and the declaration fails closed,
    /// which is what Lean's "typeclass instance problem is stuck" is.
    pub(in crate::infer) fn retry_postponed_open_carrier_instances(&mut self) {
        if self.postponed_open_carrier_instances.is_empty() {
            return;
        }
        let queue = std::mem::take(&mut self.postponed_open_carrier_instances);
        let mut still_open: Vec<(Expr, Expr)> = Vec::with_capacity(queue.len());
        for (meta_arg, goal_ty) in queue {
            // Solved already — by unification with the surrounding term, or by
            // an earlier drain. Nothing to do and nothing to re-queue.
            let meta_id = match self.metas.instantiate(&meta_arg).kind() {
                ExprKind::FVar(fvar) => MetaState::from_fvar(*fvar),
                _ => None,
            };
            let Some(meta_id) = meta_id else {
                continue;
            };
            if self.metas.is_assigned(meta_id) {
                continue;
            }

            let goal = self.metas.instantiate(&goal_ty);
            let Some((class_name, args)) = crate::instances::extract_class_app(&goal) else {
                continue;
            };
            // A rolled-back elaboration can leave an entry behind whose
            // metavariable id was re-minted for another metavariable
            // (`MetaState::pop_scope` restores the id counter). Only a
            // metavariable whose own type is still a goal of this class is
            // the one recorded; anything else is dropped, never assigned.
            let owns_goal = self.metas.get(meta_id).is_some_and(|var| {
                crate::instances::extract_class_app(&self.metas.instantiate(&var.ty))
                    .is_some_and(|(owned_class, _)| owned_class == class_name)
            });
            if !owns_goal {
                continue;
            }
            // The bridge instance links all three arguments for `+ - * / %`
            // and the bitwise ops; power and shift keep their own exponent /
            // shift-amount slot (index 1) free.
            // The slot collapse belongs to the heterogeneous-operator bridge
            // (`instHAdd : [Add α] → HAdd α α α` identifies the three slots).
            // An input-only class has ONE input and nothing to collapse onto
            // it: its goal is simply re-resolved once the surrounding term has
            // grounded the carrier.
            if instance::is_hetero_binop_default_instance_class(&class_name) {
                let linked: Vec<usize> = if instance::hetero_binop_links_all_arguments(&class_name)
                {
                    (0..args.len()).collect()
                } else {
                    (0..args.len()).filter(|i| *i != 1).collect()
                };
                let carrier = linked
                    .iter()
                    .map(|i| self.metas.instantiate(&args[*i]))
                    .find(|a| !self.has_metavars(a));
                if let Some(carrier) = carrier {
                    let targets: Vec<&Expr> = linked.iter().map(|i| &args[*i]).collect();
                    self.pin_open_type_slots(&targets, &carrier);
                }
            }

            let goal = self.whnf(&self.metas.instantiate(&goal));
            match self.resolve_instance(&goal) {
                Some(inst) => {
                    if !self.metas.assign(meta_id, inst) {
                        still_open.push((meta_arg, goal));
                    }
                }
                None => still_open.push((meta_arg, goal)),
            }
        }
        self.postponed_open_carrier_instances = still_open;
    }

    /// Elaborate a function application with implicit argument insertion.
    ///
    /// For a function `f : {A : Type} → (x : A) → A` and call `f 42`:
    /// 1. Elaborate `f` to get its type
    /// 2. Insert metavariables for implicit arguments (A becomes ?m)
    /// 3. Elaborate explicit arguments and unify types
    ///
    /// Special handling for numeric literals:
    /// - When a Nat literal is first argument to a polymorphic function
    /// - And a later argument has type Real
    /// - We coerce the literal via Real.ofNat
    ///
    /// # Contract
    ///
    /// ENSURES: Result has all solved metavariables instantiated
    /// ENSURES: Result has all solved level constraints substituted (instantiate_levels applied)
    /// Recognise a desugared heterogeneous arithmetic binop application
    /// (`@HOp.hOp ?α ?β ?γ ?inst`, produced by the parser for `a % b`, `a + b`,
    /// `a ^ b`, ...) and return its type-parameter metavar slots, emulating
    /// Lean's homogeneous `@[default_instance]` (e.g. `instHMod : HMod α α α`).
    ///
    /// Returns `HeteroBinopSlots { alpha, beta, gamma, homogeneous }` where each
    /// field is the `Expr` occupying that type-parameter position and
    /// `homogeneous` is true for the ops whose `β` collapses onto `α` (`% + - *
    /// / ` and bitwise); power / shift ops leave `β` (exponent / shift amount,
    /// usually `Nat`) free. `γ` (the result, an `outParam`) always equals `α`.
    ///
    /// Keyed off the surface head identifier, so it only fires for the operator
    /// desugarings, never for a hand-written `HMod.hMod` with explicit args.
    fn hetero_binop_homogenize_slots(
        &self,
        func: &SurfaceExpr,
        result: &Expr,
    ) -> Option<HeteroBinopSlots> {
        let head = match Self::unwrap_surface_parens(func) {
            SurfaceExpr::Ident(_, name) => Self::canonical_application_head(name)?,
            _ => return None,
        };
        let homogeneous = match head {
            "HMod.hMod" | "HAdd.hAdd" | "HSub.hSub" | "HMul.hMul" | "HDiv.hDiv" | "HAnd.hAnd"
            | "HOr.hOr" | "HXor.hXor" => true,
            // `++` (`HAppend.hAppend`) is homogeneous for List/String/Array — its
            // default `instHAppend : Append α → HAppend α α α` forces α=β=γ. Wiring
            // it in lets an empty-list literal `[]` (whose element-type metavar has
            // no operand to pin it) inherit the concrete carrier from its sibling
            // operand (`[] ++ xs` / `xs ++ []`), mirroring Lean's bidirectional
            // `[]` elaboration. Pure ELAB: only assigns open slots; the kernel
            // re-checks, so a wrong inference fails closed (TypeMismatch /
            // ContainsFreeVar).
            "HAppend.hAppend" => true,
            "HPow.hPow" | "HShiftLeft.hShiftLeft" | "HShiftRight.hShiftRight" => false,
            _ => return None,
        };
        // `@HOp.hOp α β γ inst` — the 1st/2nd/3rd application args are α/β/γ.
        let args = result.get_app_args();
        if args.len() < 3 {
            return None;
        }
        Some(HeteroBinopSlots {
            alpha: (*args[0]).clone(),
            beta: (*args[1]).clone(),
            gamma: (*args[2]).clone(),
            homogeneous,
            shift_instance: if matches!(head, "HShiftLeft.hShiftLeft" | "HShiftRight.hShiftRight") {
                args.get(3).map(|arg| (**arg).clone())
            } else {
                None
            },
        })
    }

    /// Unify the given still-open type-param slots with a concrete carrier
    /// `carrier`. Only *assigns* open metavariable slots — it never reshapes a
    /// type the operands already pinned, and the kernel re-checks the
    /// instantiated term, so this cannot weaken the kernel check. A rigid
    /// mismatch (a deliberately heterogeneous user instance) fails the
    /// speculative unify harmlessly and leaves the slot untouched.
    ///
    /// Used both by the `binop%` homogenization passes (α/β/γ of a desugared
    /// `@HOp.hOp`) and by the head-agnostic carrier-first pass
    /// [`Self::pin_open_slots_from_carrier_operand`], which pins the shared
    /// type parameter of an ordinary polymorphic application (`LT.lt`, `Eq`,
    /// `BEq.beq`, a user `{α} → α → α → …`).
    fn pin_open_type_slots(&mut self, slots: &[&Expr], carrier: &Expr) {
        let carrier = self.whnf(&self.metas.instantiate(carrier));
        // Only propagate a concrete carrier; a flex type would just pin our
        // metas to another metavar with no benefit.
        if self.has_metavars(&carrier) {
            return;
        }
        for slot in slots {
            let slot_inst = self.metas.instantiate(slot);
            if self.has_metavars(&slot_inst) {
                let ctx = self.build_local_ctx();
                let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                let _ = unifier.unify(&slot_inst, &carrier);
            }
        }
    }

    /// Is `e` a *bare* numeric literal — a numeral with no ascription, no
    /// operator around it, nothing but parentheses?
    ///
    /// A bare numeral is the canonical CARRIER-FREE argument: it carries no
    /// type of its own and must READ the type of the slot it lands in (Lean
    /// elaborates it through `OfNat α n`, Clean through
    /// `elab_nat_literal_with_expected`). Everything else — an ascription
    /// `(10 : Nat)`, a variable, an application — carries or determines a type
    /// and is therefore a usable carrier.
    ///
    /// Deliberately NON-recursive, unlike
    /// [`Self::surface_contains_bare_nat_literal`]: `f 10` determines its own
    /// type from `f`, so it is a carrier even though it contains a numeral.
    fn arg_is_bare_numeral(e: &SurfaceExpr) -> bool {
        matches!(
            Self::unwrap_surface_parens(e),
            SurfaceExpr::Lit(_, SurfaceLit::Nat(_) | SurfaceLit::BigNat(_))
        )
    }

    /// Read the explicit-argument domains of `func_ty`'s binder telescope.
    ///
    /// Pure read: creates no metavariables and assigns nothing. Stops early —
    /// returning a SHORT vector, which the caller must tolerate — at the first
    /// binder that is not `Default` (positional alignment with the surface
    /// arguments would no longer hold) and after the first DEPENDENT binder (a
    /// later domain that mentions an earlier argument cannot be read before
    /// that argument has a value).
    fn leading_explicit_arg_domains(&mut self, func_ty: &Expr, n: usize) -> Vec<Expr> {
        let mut cur = self.whnf(&self.metas.instantiate(func_ty));
        let mut doms = Vec::with_capacity(n);
        for _ in 0..n {
            let ExprKind::Pi(bi, dom, body) = cur.kind() else {
                break;
            };
            if bi.info != BinderInfo::Default {
                break;
            }
            doms.push(self.metas.instantiate(dom));
            let body = body.as_ref().clone();
            if body.has_loose_bvar(0) {
                break;
            }
            cur = self.whnf(&body);
        }
        doms
    }

    /// Carrier-first ordering: pin an argument slot that a CARRIER-FREE operand
    /// would otherwise have to guess, using a sibling operand that names the
    /// type.
    ///
    /// ## The defect this repairs
    ///
    /// Clean's argument loop is strictly left-to-right. A bare numeral in a
    /// slot whose type is still an open metavariable is therefore COMMITTED —
    /// by the `@[default_instance]` `Nat` pin at the literal seam
    /// (`infer/coercion.rs`, step 0) — before the sibling operand that actually
    /// names the carrier has been looked at. For `10 < a` with `a : UInt64`
    /// that pins `?α := Nat` and the second operand then mismatches
    /// ("expected Nat, got UInt64"), while the mirror image `a < 10` elaborates
    /// fine because operand 0 pins the carrier first. Real Lean has no such
    /// asymmetry: `binop%` (`Elab/Extra.lean`) elaborates the operands that
    /// CARRY a type first, fixes the shared type, and only then elaborates the
    /// type-directed leaves against it — and a numeral at a metavariable type
    /// is postponed, not defaulted.
    ///
    /// This is that ordering, in lookahead form. Two narrow instances of the
    /// same idea already exist — [`Self::try_elab_eq_struct_lit_reorder`] (a
    /// struct literal under `Eq`/`Ne`) and the `[]`-operand pre-pass in
    /// `elab_app_inner` (a homogeneous `HOp` binop) — but neither covers a
    /// numeral, and neither is head-agnostic.
    ///
    /// ## What links two slots
    ///
    /// Nothing about the operator is hard-coded. Two argument positions share a
    /// carrier when either
    ///
    ///   * their domains are literally the SAME unassigned metavariable — the
    ///     shape of every homogeneous polymorphic head (`LT.lt`/`LE.le`/`Eq`/
    ///     `BEq.beq : {α} → α → α → …`, and any user function of that shape); or
    ///   * a homogeneous arithmetic `binop%` joins its carrier slots; or
    ///   * a shift's actual default dictionary resolves before the numeral's
    ///     lower-priority Nat default. Its generic bridge joins the slots only
    ///     when its `ShiftLeft`/`ShiftRight` premise resolves. The selected
    ///     dictionary and universe constraints are retained. `HPow` keeps its
    ///     independent exponent type.
    ///
    /// Only a BARE NUMERAL reaches this pass, so a shift whose amount is a
    /// typed operand (`a <<< (n : Nat)`) is untouched and still fails closed
    /// when no heterogeneous instance exists — the shift's `homogeneous` flag
    /// stays false everywhere else for exactly that reason.
    ///
    /// ## Why this cannot launder a genuine mismatch
    ///
    /// ELAB-only, and strictly weaker than what the operand loop already does:
    /// it assigns an OPEN metavariable from the type of an operand the loop
    /// would have elaborated anyway, one position later
    /// ([`Self::pin_open_type_slots`] refuses a non-ground carrier and refuses
    /// to reshape an already-pinned slot). It fires only when some argument is
    /// a bare numeral — an argument with no type of its own — so a genuinely
    /// heterogeneous comparison of two typed operands (`a < b` with `a : Nat`,
    /// `b : UInt64`) never reaches it and still fails closed, as does an
    /// ascribed literal (`(10 : Nat) < a`), which is a carrier and not a leaf.
    /// The assembled term is kernel-re-checked on registration.
    fn pin_open_slots_from_carrier_operand(
        &mut self,
        func_ty: &Expr,
        args: &[SurfaceArg],
        hetero_slots: Option<&HeteroBinopSlots>,
    ) {
        // Only a carrier-free leaf can be committed to the wrong type by the
        // left-to-right order; without one there is nothing to repair.
        if !args.iter().any(|a| Self::arg_is_bare_numeral(&a.expr)) {
            return;
        }
        let doms = self.leading_explicit_arg_domains(func_ty, args.len());
        if doms.len() < 2 {
            return;
        }
        // A slot is "open" when its domain is a bare, still-unassigned
        // metavariable. `instantiate` has already been applied, so a surviving
        // meta-tagged `FVar` is by construction unassigned (same invariant the
        // literal seam relies on).
        let open_slot_fvar = |d: &Expr| match d.kind() {
            ExprKind::FVar(id) if MetaState::from_fvar(*id).is_some() => Some(*id),
            _ => None,
        };
        let homogeneous_binop =
            hetero_slots.is_some_and(|s| s.homogeneous || s.shift_instance.is_some());

        for (lit_idx, dom) in doms.iter().enumerate() {
            if !Self::arg_is_bare_numeral(&args[lit_idx].expr) {
                continue;
            }
            let Some(lit_fvar) = open_slot_fvar(dom) else {
                continue;
            };
            // A sibling that (a) can name a type at all and (b) shares this
            // slot's carrier. Excluded from (a): every other type-DIRECTED leaf
            // — another numeral, `[]`, a leading-dot constructor, a bare
            // structure literal — which reads its slot rather than naming it;
            // and an unascribed `by`/`calc` block, whose goal IS the open slot
            // (running its tactic script speculatively to learn a type it does
            // not have would be both wrong and expensive).
            let carrier_idx = doms.iter().enumerate().position(|(j, dom_j)| {
                j != lit_idx
                    && !Self::arg_is_bare_numeral(&args[j].expr)
                    && !Self::arg_needs_result_type_pinned(&args[j].expr)
                    && !Self::is_bare_struct_lit(&args[j].expr)
                    && !Self::arg_contains_unascribed_by_block(&args[j].expr)
                    // Linked either by the `binop%` default instance (the two
                    // operands of a homogeneous `@HOp.hOp ?α ?β ?γ`, whose
                    // slots are DISTINCT metavariables) or, head-agnostically,
                    // by being literally the same open metavariable.
                    && ((homogeneous_binop && args.len() == 2)
                        || open_slot_fvar(dom_j) == Some(lit_fvar))
            });
            let Some(carrier_idx) = carrier_idx else {
                continue;
            };
            // Speculatively elaborate the carrier operand for its TYPE only.
            // The term is discarded — the operand loop re-elaborates it
            // normally — and the scope is popped so a failed attempt leaves no
            // assignments behind.
            //
            // Elaborated the way the ARGUMENT LOOP will elaborate it — against
            // this slot's own (still open) domain — not bare. A bare
            // `self.elaborate` stops at the head for anything whose leading
            // binders are implicit or instance-implicit: a class projection
            // `C.lo : [self : C] → Nat` infers as that PI, and pinning the
            // shared slot to a `Pi(InstImplicit …)` breaks `C.lo = 3`
            // (measured: `class_extends_instance_e2e::
            // b24_multilevel_grandparent_field_flattens`). Passing the slot as
            // the expected type routes through
            // `apply_implicit_to_expected_type`, exactly as the loop does, so
            // the projection is applied and its type reads `Nat`.
            self.metas.push_scope();
            let carrier_type = self
                .elaborate_arg_with_expected_type(
                    &args[carrier_idx].expr,
                    Some(doms[carrier_idx].clone()),
                )
                .ok()
                .and_then(|e| self.infer_type(&e).ok())
                .map(|t| self.whnf(&self.metas.instantiate(&t)));
            self.metas.pop_scope();
            let Some(carrier_type) = carrier_type else {
                continue;
            };
            if self.has_metavars(&carrier_type) {
                continue;
            }
            // Belt and braces for the same failure mode: a type whose leading
            // binder is implicit / instance-implicit is an UNAPPLIED head, not
            // the type this operand will have in its slot. Decline rather than
            // pin it.
            if matches!(carrier_type.kind(), ExprKind::Pi(bi, _, _) if bi.info != BinderInfo::Default)
            {
                continue;
            }
            match hetero_slots {
                Some(slots) if slots.homogeneous => {
                    let targets = [&slots.alpha, &slots.beta, &slots.gamma];
                    self.pin_open_type_slots(&targets, &carrier_type);
                }
                Some(slots) if slots.shift_instance.is_some() => {
                    self.pin_open_type_slots(&[&slots.alpha, &slots.gamma], &carrier_type);
                    if let Some(instance) = &slots.shift_instance {
                        self.resolve_shift_numeral_instance(instance);
                    }
                }
                // An ordinary polymorphic head: pin the one shared slot. Every
                // other position whose domain IS that metavariable follows by
                // instantiation.
                _ => self.pin_open_type_slots(&[dom], &carrier_type),
            }
            return;
        }
    }

    /// Apply a real shift default before a numeral's lower-priority Nat
    /// default. Keep the selected dictionary and its universe constraints on
    /// success. A failed search restores the complete metavariable world,
    /// local/cached state and defaulting counters before the numeral proceeds.
    fn resolve_shift_numeral_instance(&mut self, instance: &Expr) {
        let instance = self.metas.instantiate(instance);
        let Some(meta) = instance::bare_unassigned_meta(&self.metas, &instance) else {
            return;
        };
        let Some(goal) = self.metas.get(meta).map(|var| var.ty.clone()) else {
            return;
        };
        let saved_metas = self.metas.clone();
        let saved_scope = self.local_scope_snapshot();
        let saved_steps = self.instance_search_steps;
        let saved_stuck = self.instance_search_stuck;
        let saved_failures = self.failed_local_subgoals.clone();
        let saved_answers = self.user_default_instance_answers;
        let saved_deferred = self.deferred_user_default_goals;
        let saved_postponed = self.postponed_open_carrier_instances.clone();
        let saved_postponed_do_pure = self.do_pure_obligations.clone();
        let accepted = self
            .resolve_instance(&goal)
            .is_some_and(|value| self.metas.assign(meta, value));
        if !accepted {
            self.metas = saved_metas;
            self.restore_local_scope(saved_scope, true);
            self.instance_search_steps = saved_steps;
            self.instance_search_stuck = saved_stuck;
            self.failed_local_subgoals = saved_failures;
            self.user_default_instance_answers = saved_answers;
            self.deferred_user_default_goals = saved_deferred;
            self.postponed_open_carrier_instances = saved_postponed;
            self.do_pure_obligations = saved_postponed_do_pure;
        } else {
            self.tc_caches.replace(TcCaches::default());
        }
    }

    /// Pre-operand pass: if an expected result type is present, collapse the
    /// homogeneous slots onto it. Drives `t_c`/`t_d`-style bodies where the
    /// result type is the only carrier (`2 ^ width : Int`) and the inner
    /// operand of a nested binop once its outer op has pinned the expected type.
    fn homogenize_hetero_binop_from_expected(&mut self, slots: &HeteroBinopSlots) {
        let Some(expected) = self.current_expected_type.clone() else {
            return;
        };
        let expected = self.whnf(&self.metas.instantiate(&expected));
        // α and γ (result) always collapse onto the carrier; β only for the
        // homogeneous ops (power / shift keep an independent exponent type).
        let mut targets: Vec<&Expr> = vec![&slots.alpha, &slots.gamma];
        if slots.homogeneous {
            targets.push(&slots.beta);
        }
        self.pin_open_type_slots(&targets, &expected);
    }

    /// B104: retry a failed binop% application with the homogeneous slot
    /// pinning suppressed — Lean's try-homogeneous-then-heterogeneous
    /// `binop%` behavior. The caller pops its speculative meta scope first,
    /// so the failed homogeneous attempt leaves no assignments; the retry
    /// then elaborates each operand at its own type and synthesizes the
    /// `[HOp ?α ?β ?γ]` goal directly against the concrete operand types
    /// (the open result slot `?γ` is solved by unifying with the registered
    /// instance — the outParam direction).
    ///
    /// Bounded: the flag is one-shot (consumed at `elab_app_inner` entry) and
    /// the retry recognizes NO slots, so its own failure exits cannot re-enter
    /// this fallback. Only invoked from error exits, so any elaboration that
    /// previously succeeded is untouched.
    ///
    /// SOUNDNESS: ELAB-only. The fallback builds an ordinary fully-applied
    /// operator term that is kernel-rechecked on `add_decl`; a wrong instance
    /// or type inference fails closed (TypeMismatch / free-variable
    /// rejection). No unchecked registration.
    fn elab_app_binop_hetero_fallback(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Expr, ElabError> {
        self.suppress_binop_homogenize = true;
        let result = self.elab_app_inner(func, args);
        // One-shot: `elab_app_inner` entry already consumed the flag; keep
        // this reset as a defensive invariant.
        self.suppress_binop_homogenize = false;
        result
    }

    /// Does this argument expression *require* the application's result type to
    /// be pinned before it can elaborate? Two type-directed literals do:
    ///
    ///   * a leading-dot constructor (`.ctor` / `.ctor args`) — resolves its
    ///     head against the expected type;
    ///   * an empty-list literal `[]` (the bare ident `List.nil`) — has no
    ///     operand to pin its element type / universe.
    ///
    /// The check recurses through `Prod.mk` tuple spines so that a nested tuple
    /// component carrying an empty list — `(x, ([], [])) : A × (List B × List C)`
    /// desugars to `Prod.mk x (Prod.mk [] [])`, whose outer second arg is itself
    /// a `Prod.mk` application — still triggers the outer pre-arg unification
    /// that pins the nested component types.
    fn arg_needs_result_type_pinned(e: &SurfaceExpr) -> bool {
        let mut e = e;
        while let SurfaceExpr::Paren(_, inner) = e {
            e = inner;
        }
        match e {
            SurfaceExpr::Ident(_, n) => {
                n.is_relative_constructor() || n == &SurfaceName::generated_path("List.nil")
            }
            SurfaceExpr::App(_, head, app_args) => {
                let mut h = head.as_ref();
                while let SurfaceExpr::Paren(_, inner) = h {
                    h = inner;
                }
                match h {
                    SurfaceExpr::Ident(_, n) if n.is_relative_constructor() => true,
                    // Recurse into a tuple spine: `Prod.mk a b` — if any
                    // component itself needs the result type pinned, so does the
                    // enclosing application.
                    SurfaceExpr::Ident(_, n) if n == &SurfaceName::generated_path("Prod.mk") => {
                        app_args
                            .iter()
                            .any(|a| Self::arg_needs_result_type_pinned(&a.expr))
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// Is some remaining argument a *bare numeric literal* (`0`, `8`) landing in
    /// a function-parameter slot whose type is still an **open metavariable**?
    ///
    /// Such a literal carries no type information, so without the slot pinned it
    /// defaults eagerly to `Nat` and pins the slot to `Nat`. When the slot is a
    /// polymorphic element type (`α`) and the application's result type is
    /// constrained by an expected type (`List.replicate 8 0 : List UInt8`), the
    /// pre-arg expected-result unification should fire first to pin `α := UInt8`
    /// so the literal resolves against the right element type.
    ///
    /// The open-metavar guard is what keeps this from disturbing arithmetic:
    /// literals in concrete `Nat`/`Int` slots (`a % (2 ^ width)`) have a
    /// *concrete* parameter type after instantiation, not a metavar, so they do
    /// not trigger the pre-arg pass. `func_ty` is the already-instantiated
    /// function type with leading implicits inserted as metas; its Pi spine is
    /// walked in lockstep with `args`, generating fresh metas for non-literal
    /// slots exactly as the pre-arg unification loop does. This is a read-only
    /// predicate — it consumes a temporary `metas` scope so no assignment leaks.
    /// A hetero-binop head (`HAdd.hAdd`, `HSub.hSub`, …). The pre-arg
    /// expected-result pin must NOT fire for these: their operand/result slots
    /// are handled by `binop%`-style homogenization (which deliberately drives
    /// arithmetic coercion, e.g. `(2:Nat) - (5:Nat) : Int`), and pinning the
    /// carrier early here would change that established behavior.
    pub(super) fn is_hetero_binop_head(func: &SurfaceExpr) -> bool {
        matches!(
            Self::unwrap_surface_parens(func),
            SurfaceExpr::Ident(_, name) if matches!(
                Self::canonical_application_head(name).unwrap_or(""),
                "HMod.hMod" | "HAdd.hAdd" | "HSub.hSub" | "HMul.hMul" | "HDiv.hDiv"
                    | "HAnd.hAnd" | "HOr.hOr" | "HXor.hXor" | "HAppend.hAppend"
                    | "HPow.hPow" | "HShiftLeft.hShiftLeft" | "HShiftRight.hShiftRight"
            )
        )
    }

    /// An argument that carries a *concrete, already-determined* type — an
    /// ascription `(e : T)` or a bare variable/constant `Ident` (NOT a leading-dot
    /// constructor, which resolves from the expected type). Such an arg, if it
    /// lands in an OPEN type-param slot, would pin that slot to its own type
    /// (`Nat`) before the expected result type is consulted — so `Prod.mk (3:Nat)
    /// (4:Nat) : Int × Int` / `some (n:Nat) : Option Int` yield `Prod/Option Nat`
    /// and the element coercion to `Int` is lost.
    fn arg_is_typed_value(e: &SurfaceExpr) -> bool {
        let mut e = e;
        while let SurfaceExpr::Paren(_, inner) = e {
            e = inner;
        }
        match e {
            SurfaceExpr::Ascription(..) => true,
            SurfaceExpr::Ident(_, n) => {
                !n.is_relative_constructor() && n != &SurfaceName::generated_path("List.nil")
            }
            // Recurse into container/constructor spines so a nested typed-value
            // element still triggers the pre-arg pin at each enclosing level:
            // `#[(1:Nat), …]` is `Array.mk (List.cons (1:Nat) …)` and `some (some
            // (n:Nat))` wraps its ascribed element in an `App`. Without this the
            // enclosing container's element type never pins from the expected
            // result (`Array Int` / `Option (Option Int)`), so the inner value is
            // not coerced. Mirrors `arg_needs_result_type_pinned`'s Prod.mk-spine
            // recursion; restricted to the standard container heads.
            SurfaceExpr::App(_, head, app_args) => {
                let mut h = head.as_ref();
                while let SurfaceExpr::Paren(_, inner) = h {
                    h = inner;
                }
                matches!(h, SurfaceExpr::Ident(_, n) if matches!(
                    Self::canonical_application_head(n).unwrap_or(""),
                    "List.cons" | "Array.mk" | "some" | "Option.some" | "Prod.mk"
                )) && app_args.iter().any(|a| Self::arg_is_typed_value(&a.expr))
            }
            _ => false,
        }
    }

    /// Does some argument carry a concrete type ([`Self::arg_is_typed_value`])
    /// and land in an OPEN metavariable type-param slot whose application result
    /// is safe to pin from the expected type? If so the pre-arg expected-result
    /// unification should fire first, pinning that slot so the arg then coerces
    /// to it (the brick-46 chokepoint inserts the `Coe`).
    ///
    /// The result-shape guard is essential for higher-order proof combinators.
    /// `congrArg (fun z => ...) ih` also has a typed identifier in an open slot,
    /// but its result contains an applied/repeated function metavariable. Eagerly
    /// matching that result against a reducible expected equality can leave
    /// premature assignments that later manifest as unrelated rigid-head
    /// mismatches. This path therefore shares
    /// [`Self::result_metavars_first_order_linear`]'s completeness guard and
    /// requires the Pi walk to reach the actual result. Constructor/container
    /// results such as `Prod ?a ?b`, `Option ?a`, and `List ?a` remain eligible.
    ///
    /// Mirrors `bare_nat_literal_in_open_slot`'s spine walk; caller additionally
    /// gates on the head not being a hetero-binop.
    fn typed_value_arg_in_open_slot(&mut self, func_ty: &Expr, args: &[SurfaceArg]) -> bool {
        if self.current_expected_type.is_none() {
            return false;
        }
        self.metas.push_scope();
        let mut cur = self.whnf(&self.metas.instantiate(func_ty));
        let mut found = false;
        let mut walked_all = true;
        for arg in args {
            let ExprKind::Pi(_, dom, body) = cur.kind() else {
                walked_all = false;
                break;
            };
            let dom_inst = self.whnf(&self.metas.instantiate(dom));
            // The slot needs pinning if it CONTAINS an open metavar — not only when
            // its head is one. A container slot `List ?α` / `Option ?α` (head a
            // concrete `List`/`Option`) still has an open element the ground
            // expected result can pin, so `Array.mk (…) : Array Int` and `some (…)
            // : Option Int` propagate `Int` inward. Arithmetic is unaffected: its
            // operand slots are *bare* metavars, for which `has_metavars` and
            // head-is-metavar coincide (and this helper is binop-excluded anyway).
            if Self::arg_is_typed_value(&arg.expr) && self.has_metavars(&dom_inst) {
                found = true;
            }
            let meta = self.fresh_meta(dom_inst);
            cur = self.whnf(&self.metas.instantiate(&body.instantiate(&meta)));
        }
        let result_is_safe = walked_all
            && !matches!(cur.kind(), ExprKind::Pi(_, _, _))
            && self.has_metavars(&cur)
            && Self::result_metavars_first_order_linear(&cur);
        self.metas.pop_scope();
        found && result_is_safe
    }

    /// Is `e` a *flex application* `?p w₁ … wₙ` (n ≥ 1) — an application whose
    /// spine head is an UNASSIGNED metavariable?
    ///
    /// Narrower than [`Self::contains_flex_application`], which reports a flex
    /// application anywhere inside `e` (including under binders). Here we ask
    /// only about the head of `e` itself, because that is exactly the slot shape
    /// [`Self::rigid_arg_in_flex_slot`] cannot solve argument-first.
    fn is_flex_application(metas: &MetaState, e: &Expr) -> bool {
        matches!(e.kind(), ExprKind::App(_, _))
            && matches!(e.get_app_fn().kind(),
                ExprKind::FVar(id) if MetaState::from_fvar(*id)
                    .is_some_and(|m| metas.get_assignment(m).is_none()))
    }

    /// An argument whose type is *self-determined*: it is fixed by the argument
    /// itself (its head constant / local, or an ascription), not read off the
    /// expected type. A leading-dot constructor, a hole, a bare literal, a
    /// lambda and `[]` are all expected-type-driven and therefore excluded.
    ///
    /// Deliberately head-shaped and not recursive: we only need to know that
    /// elaborating this argument will produce a type of its own for the slot to
    /// be checked against.
    fn arg_type_is_self_determined(e: &SurfaceExpr) -> bool {
        fn head_ident_is_rigid(e: &SurfaceExpr) -> bool {
            let mut e = e;
            while let SurfaceExpr::Paren(_, inner) = e {
                e = inner;
            }
            matches!(e, SurfaceExpr::Ident(_, n) if !n.is_relative_constructor() && n != &SurfaceName::generated_path("List.nil"))
        }
        let mut e = e;
        while let SurfaceExpr::Paren(_, inner) = e {
            e = inner;
        }
        match e {
            SurfaceExpr::Ascription(..) => true,
            SurfaceExpr::Ident(..) => head_ident_is_rigid(e),
            SurfaceExpr::App(_, head, _) => head_ident_is_rigid(head),
            _ => false,
        }
    }

    /// A self-determined argument ([`Self::arg_type_is_self_determined`]) landing
    /// in a slot whose domain is a FLEX APPLICATION `?p w₁ … wₙ`
    /// ([`Self::is_flex_application`]) — the one slot shape that can never be
    /// solved argument-first, so the expected result type must pin it FIRST.
    ///
    /// WHY THIS SHAPE IS UNSOLVABLE FROM THE ARGUMENT. `Exists.intro : {α} →
    /// {p : α → Prop} → (w : α) → p w → Exists p`, applied as
    /// `Exists.intro (Nat.succ x) (inner1 x)` against an expected `CP (Nat.succ x)`
    /// where `def CP (y : Nat) : Prop := ∃ a b, a + b = y`. The expected type is
    /// a `def` application, so its head is `CP`, not `Exists` — nothing pins `?p`
    /// before the arguments run. The second argument is then checked against
    /// `?p (Nat.succ x)`, and because the witness is a COMPOUND term that
    /// constraint is not a Miller pattern: `try_pattern_unify` declines and the
    /// structural `App`/`App` rule pairs the two spines POSITIONALLY, assigning
    /// `?p := @Exists Nat` and then failing `Nat.succ x` against the predicate
    /// lambda ("different shape: Discriminant(5) vs Discriminant(4)"). The
    /// printed "expected `Exists Nat (Nat.succ x)`" is that poisoned assignment.
    /// Lean pins the slot from the expected type before any argument is
    /// elaborated (`propagateExpectedType`, `Elab/App.lean`).
    ///
    /// WHY IT IS SAFE TO FIRE HERE, AND ONLY HERE. Two independent narrowings:
    ///
    ///   * The slot's head must be an unsolved metavariable *applied to
    ///     something*. A bare open slot (`?α`) is already handled by
    ///     [`Self::typed_value_arg_in_open_slot`]; a rigid slot needs no pin.
    ///   * The walked result type must be reached, still carry metavariables and
    ///     be FIRST-ORDER LINEAR ([`Self::result_metavars_first_order_linear`]),
    ///     the shared completeness guard that keeps `congrArg`-style
    ///     higher-order results (`@Eq ?β (?f a₁) (?f a₂)`) and forced results
    ///     (`@Eq ?α ?a ?a`) out — those must stay argument-driven.
    ///
    /// The block this gates is speculative (it only assigns still-open metas)
    /// and every elaborated declaration is re-checked by the kernel, so a wrong
    /// pin can only produce a spurious rejection, never an unsound accept.
    fn rigid_arg_in_flex_slot(&mut self, func_ty: &Expr, args: &[SurfaceArg]) -> bool {
        if self.current_expected_type.is_none() {
            return false;
        }
        self.metas.push_scope();
        let mut cur = self.whnf(&self.metas.instantiate(func_ty));
        let mut found = false;
        let mut walked_all = true;
        for arg in args {
            let ExprKind::Pi(_, dom, body) = cur.kind() else {
                walked_all = false;
                break;
            };
            let dom_inst = self.whnf(&self.metas.instantiate(dom));
            if Self::arg_type_is_self_determined(&arg.expr)
                && Self::is_flex_application(&self.metas, &dom_inst)
            {
                found = true;
            }
            let meta = self.fresh_meta(dom_inst);
            cur = self.whnf(&self.metas.instantiate(&body.instantiate(&meta)));
        }
        let result_is_safe = walked_all
            && !matches!(cur.kind(), ExprKind::Pi(_, _, _))
            && self.has_metavars(&cur)
            && Self::result_metavars_first_order_linear(&cur);
        self.metas.pop_scope();
        found && result_is_safe
    }

    fn bare_nat_literal_in_open_slot(&mut self, func_ty: &Expr, args: &[SurfaceArg]) -> bool {
        // Only meaningful when an expected result type is available to drive the
        // pin; without one the pre-arg unification block is a no-op anyway.
        if self.current_expected_type.is_none() {
            return false;
        }
        self.metas.push_scope();
        let mut cur = self.whnf(&self.metas.instantiate(func_ty));
        let mut found = false;
        for arg in args {
            let ExprKind::Pi(_, dom, body) = cur.kind() else {
                break;
            };
            let dom_inst = self.whnf(&self.metas.instantiate(dom));
            // A bare numeric literal, OR an application transitively containing
            // one, whose slot head is an unsolved metavar FVar. The nested case
            // covers a polymorphic wrapper: `some (List.replicate 8 0)` has the
            // inner `List.replicate 8 0` (an application carrying a bare `0`) in
            // `Option.some`'s open `α` slot. Pinning that slot from the expected
            // `Option (List UInt8)` flows `List UInt8` into the inner
            // application, which then pins `List.replicate`'s element type.
            // Slot needs pinning if it CONTAINS an open metavar (not only when its
            // head is one), so a bare literal inside a container slot `List ?α`
            // pins the element type from the expected result — `#[1, 2] : Array
            // Int` (`Array.mk (List.cons 1 …)`) flows `Int` into the list. A binop
            // operand slot is a *bare* metavar (head-is-metavar), unchanged.
            if Self::surface_contains_bare_nat_literal(&arg.expr) && self.has_metavars(&dom_inst) {
                found = true;
                break;
            }
            // Advance the spine with a fresh meta for this slot (mirrors the
            // pre-arg unification walk), so later slots see solved earlier metas.
            let meta = self.fresh_meta(dom_inst);
            cur = self.whnf(&self.metas.instantiate(&body.instantiate(&meta)));
        }
        self.metas.pop_scope();
        found
    }

    /// Is the current expected type a bare, still-UNASSIGNED metavariable?
    ///
    /// The pre-arg unification block exists to push a *known* expected result
    /// inward so open argument slots get pinned before the arguments elaborate.
    /// A bare unsolved metavariable is precisely the case that carries nothing
    /// to push: unifying the walked result against it cannot pin anything, it
    /// merely ASSIGNS the expected metavariable to a half-open result shape
    /// whose remaining slot metas came from this speculative walk.
    ///
    /// That premature assignment is actively harmful under `Eq`, whose `α` is
    /// still open while its left operand elaborates. `Quotient.mk s 3 = Quot.mk
    /// r 3` pins `?α := Quot Nat (Setoid.r Nat ?m)` with `?m` unsolved, and the
    /// right operand's honest `Quot Nat trivRel` can no longer match it — the
    /// witness being that even two *syntactically identical* operands fail,
    /// which no defeq question could explain. Binding the literal to a name
    /// (`def n3 : Nat := 3`) sidesteps it only because the named constant does
    /// not trip `bare_nat_literal_in_open_slot` in the first place.
    ///
    /// Skipping here restores the ordinary path: the arguments elaborate on
    /// their own and the expected metavariable is solved from the finished
    /// result afterwards, as it is for every application that never requested
    /// pre-arg unification.
    pub(super) fn expected_is_unassigned_meta(&self) -> bool {
        let Some(expected) = self.current_expected_type.as_ref() else {
            return false;
        };
        let inst = self.metas.instantiate(expected);
        matches!(inst.kind(),
            ExprKind::FVar(id) if MetaState::from_fvar(*id)
                .is_some_and(|m| self.metas.get_assignment(m).is_none()))
    }

    /// Does `e` transitively contain a bare `by`/`calc` block whose result type
    /// is an argument slot — i.e. a `by`-block that is NOT ascribed and so takes
    /// its goal from the surrounding elaboration (B25)?
    ///
    /// `some (by exact 2)`, `Prod.mk (by exact 1) (by exact 2)`, and
    /// `some (some (by exact 2))` all match (the by-block sits, possibly nested
    /// through applications/parens, in a polymorphic argument slot). An ascribed
    /// block `(by tac : T)` does NOT match: its type is fixed by the ascription,
    /// so it never needs the slot pinned first.
    fn arg_contains_unascribed_by_block(e: &SurfaceExpr) -> bool {
        match e {
            SurfaceExpr::ByTactic(..) | SurfaceExpr::CalcBlock(..) => true,
            SurfaceExpr::Paren(_, inner) | SurfaceExpr::Explicit(_, inner) => {
                Self::arg_contains_unascribed_by_block(inner)
            }
            // `(by tac : _)` — the shape `‹_›` expands to — pins nothing: the
            // hole is a fresh metavariable the slot has to solve.
            SurfaceExpr::Ascription(_, inner, ty)
                if matches!(ty.as_ref(), SurfaceExpr::Hole(_)) =>
            {
                Self::arg_contains_unascribed_by_block(inner)
            }
            // A leading-dot identifier reads its constructor off the slot type
            // (`deferrable_leading_dot`): pin the result type first.
            SurfaceExpr::Ident(_, name) if name.is_relative_constructor() => true,
            SurfaceExpr::App(_, func, app_args) => {
                Self::arg_contains_unascribed_by_block(func)
                    || app_args
                        .iter()
                        .any(|a| Self::arg_contains_unascribed_by_block(&a.expr))
            }
            // An ascription pins the block's type; the slot need not be solved
            // first. Every other shape (identifiers, literals, holes, …) carries
            // no metavar-driven by-block.
            _ => false,
        }
    }

    /// Is `e` itself a `by` block whose goal is the argument slot — bare, in
    /// parentheses, or ascribed to a hole (`‹_›` parses as
    /// `(by assumption : _)`)? Such an argument is DEFERRED by the argument
    /// loop when its slot type still carries metavariables: the slot is
    /// filled with a placeholder and the block runs once the remaining
    /// arguments have pinned the type (Lean's postponed
    /// `SyntheticMVarKind.tactic`). A block ascribed to a real type fixes its
    /// own goal and is never deferred; a `calc` block is not a tactic block.
    fn deferrable_by_block(e: &SurfaceExpr) -> bool {
        match e {
            SurfaceExpr::ByTactic(..) => true,
            SurfaceExpr::Paren(_, inner) => Self::deferrable_by_block(inner),
            SurfaceExpr::Ascription(_, inner, ty)
                if matches!(ty.as_ref(), SurfaceExpr::Hole(_)) =>
            {
                Self::deferrable_by_block(inner)
            }
            _ => false,
        }
    }

    /// The parser's exact `heq ▸ value` desugaring, without an authored
    /// ascription. Lean's `elabSubst` starts with `tryPostponeIfHasMVars?`:
    /// resume against the solved slot instead of choosing an inferred motive
    /// while a later argument can still determine a cast endpoint.
    fn deferrable_subst(&self, e: &SurfaceExpr) -> bool {
        match e {
            SurfaceExpr::Paren(_, inner) => self.deferrable_subst(inner),
            SurfaceExpr::App(_, head, args)
                if args.len() == 2 && args.iter().all(|arg| arg.name.is_none()) =>
            {
                matches!(head.as_ref(), SurfaceExpr::Ident(_, name)
                    if self.head_denotes_global(name, "Eq.rec"))
            }
            _ => false,
        }
    }

    /// Is `e` a leading-dot identifier (`.intro`, possibly applied:
    /// `.intro _`) — an argument whose meaning comes entirely from its slot
    /// type? Lean postpones its elaboration until the expected type is known
    /// (`elabDotIdent` throws `postpone` on a metavariable), so it is
    /// deferred exactly like a `by` block (`h.elim (.intro _) (.intro _)`,
    /// `Prop.exists_iff` in `Mathlib/Logic/Basic.lean`, measured 2026-09-11).
    fn deferrable_leading_dot(e: &SurfaceExpr) -> bool {
        match e {
            SurfaceExpr::Ident(_, name) => name.is_relative_constructor(),
            SurfaceExpr::Paren(_, inner) => Self::deferrable_leading_dot(inner),
            SurfaceExpr::App(_, func, _) => Self::deferrable_leading_dot(func),
            _ => false,
        }
    }

    /// Is the head of `ty`, after metavariable instantiation, itself an
    /// unassigned metavariable? This is Lean's `expectedType.getAppFn.isMVar`
    /// (`Lean/Elab/BuiltinNotation.lean:54`) — the condition under which
    /// `elabAnonymousCtor` has nothing to read and postpones.
    fn expected_type_head_is_meta(&self, ty: &Expr) -> bool {
        let ty = self.metas.instantiate(ty);
        matches!(ty.get_app_fn().kind(),
            ExprKind::FVar(fvar) if MetaState::from_fvar(*fvar).is_some())
    }

    /// An open predicate applied to callback parameters can be determined
    /// by a later proof argument. Inspect the domain before the eager
    /// callback has an opportunity to solve that predicate from its body.
    fn has_open_callback_premise(&self, slot: &Expr) -> bool {
        let mut telescope = slot;
        while let ExprKind::Pi(_, domain, body) = telescope.kind() {
            if domain.is_app() && self.expected_type_head_is_meta(domain) {
                return true;
            }
            telescope = body;
        }
        false
    }

    /// Is `e` an anonymous constructor `⟨…⟩` (possibly parenthesized)?
    ///
    /// `⟨…⟩` reads its constructor off the slot type and can say nothing at all
    /// without one, so Lean postpones it exactly like a `by` block or a
    /// leading-dot name: `elabAnonymousCtor` opens with
    /// `tryPostponeIfNoneOrMVar expectedType?`
    /// (`Lean/Elab/BuiltinNotation.lean:46`) and only throws
    /// `throwExpTypeUnknown` at :54 once the type is still a metavariable after
    /// the postponement. `Function.sometimes_eq := dif_pos ⟨a⟩` is the row:
    /// `dif_pos`'s `{c : Prop}` is open at the moment `⟨a⟩` is reached, and it
    /// is the application's RESULT type that pins it.
    ///
    /// An ASCRIBED anonymous constructor (`(⟨a, b⟩ : T)`) pins its own type and
    /// is deliberately absent here, as it is from `deferrable_by_block`.
    fn deferrable_anonymous_ctor(e: &SurfaceExpr) -> bool {
        match e {
            SurfaceExpr::Paren(_, inner) => Self::deferrable_anonymous_ctor(inner),
            SurfaceExpr::App(_, func, _) => matches!(
                func.as_ref(),
                SurfaceExpr::Ident(_, n) if n.is_unescaped_component("anonymousCtor")
            ),
            _ => false,
        }
    }

    /// Is some remaining argument an unascribed `by`/`calc` block (possibly
    /// nested through applications/parens) landing in an argument slot whose
    /// type is still an **open metavariable** (B25 — by-block postponement)?
    ///
    /// A `by`-block argument elaborates its tactic script against the slot type
    /// as the goal. When that slot is an unsolved metavariable — `Option.some`'s
    /// `?α` in `some (by exact 2) : Option Nat` — running the tactic *now* hands
    /// the block a metavariable goal (a leaked meta-encoded FVar), so `exact`/
    /// `rfl` fail or produce an uncertifiable term. This predicate triggers the
    /// pre-arg expected-result unification below, which unifies the
    /// application's return type (`Option ?α`) against the expected type
    /// (`Option Nat`) FIRST, pinning `?α := Nat` so the tactic sees a concrete
    /// goal — the same effect as Lean's `synthesizeSyntheticMVars` postponement
    /// of `SyntheticMVarKind.tactic` (Elab/Term.lean). When no slot can be
    /// pinned this way (nothing constrains the return type), the by-block still
    /// runs against a metavar goal and fails LOUDLY downstream (UnsolvedGoals /
    /// CannotInfer) — never a silently-wrong term.
    ///
    /// Read-only: walks the Pi spine under a throwaway `metas` scope generating
    /// fresh per-slot metas exactly like the pre-arg unification loop, so no
    /// assignment leaks. The actual pin happens in the speculative block below
    /// and is kernel-re-checked, so soundness is unchanged.
    fn by_block_arg_in_open_slot(&mut self, func_ty: &Expr, args: &[SurfaceArg]) -> bool {
        // Without an expected result type there is nothing to drive the pin, so
        // the pre-arg unification block is a no-op anyway.
        if self.current_expected_type.is_none() {
            return false;
        }
        self.metas.push_scope();
        let mut cur = self.whnf(&self.metas.instantiate(func_ty));
        let mut found = false;
        for arg in args {
            let ExprKind::Pi(_, dom, body) = cur.kind() else {
                break;
            };
            let dom_inst = self.whnf(&self.metas.instantiate(dom));
            if Self::arg_contains_unascribed_by_block(&arg.expr) && self.has_metavars(&dom_inst) {
                found = true;
                break;
            }
            // Advance the spine with a fresh meta for this slot (mirrors the
            // pre-arg unification walk), so later slots see solved earlier metas.
            let meta = self.fresh_meta(dom_inst);
            cur = self.whnf(&self.metas.instantiate(&body.instantiate(&meta)));
        }
        self.metas.pop_scope();
        found
    }

    /// Lambda-argument analog of [`Self::by_block_arg_in_open_slot`] — Lean's
    /// `propagateExpectedType` for postponable `fun` arguments. An
    /// UN-annotated lambda in a slot whose domain still carries metavariables
    /// cannot elaborate its body (the binder's type IS the open meta, so
    /// `h.symm ▸ …` and dot-notation inside die on "cannot extract type name
    /// from opaque type variable"); firing the pre-arg unification block pins
    /// the application's result against the expected type first, so the
    /// lambda sees a concrete domain. Restricted to lambdas carrying at least
    /// one UN-annotated binder: `fun (x : T) => …` supplies its own domain and
    /// needs no pin (narrowness mirrors the 33-codata-test lesson recorded on
    /// the ctor gate below).
    fn lambda_arg_in_open_slot(&mut self, func_ty: &Expr, args: &[SurfaceArg]) -> bool {
        if self.current_expected_type.is_none() {
            return false;
        }
        fn is_unascribed_lambda(e: &SurfaceExpr) -> bool {
            match e {
                SurfaceExpr::Paren(_, inner) => is_unascribed_lambda(inner),
                SurfaceExpr::Lambda(_, binders, _) => binders.iter().any(|b| b.ty.is_none()),
                SurfaceExpr::PatternMatchLambda(..) => true,
                _ => false,
            }
        }
        // RESULT-SHAPE GUARD, shared with `typed_value_arg_in_open_slot`.
        //
        // This helper is one of several `||` routes into the SAME pre-arg
        // expected-result unification block. The element-coercion route already
        // learned that higher-order proof combinators must not take it:
        // `congrArg (fun c => Bool.or (satLit a l) c) ih` has an un-annotated
        // lambda in an open slot, so the shape test below matches, but
        // `congrArg`'s result contains an APPLIED function metavariable.
        // Matching that against a reducible expected equality leaves premature
        // assignments that resurface as an unrelated rigid-head mismatch
        // (`List.rec` vs `Bool.rec` —
        // `test_typed_value_pin_preserves_congr_arg_over_reducible_list_rec`).
        //
        // Adding this route without the guard reopened exactly that hole. Reuse
        // the established predicate rather than a new heuristic: first-order,
        // linear result metavariables only, and the Pi walk must reach the real
        // result. Constructor/container results (`Option ?a`, `List ?a`) stay
        // eligible, so the un-annotated-lambda case this route exists to serve
        // is untouched.
        self.metas.push_scope();
        let mut cur = self.whnf(&self.metas.instantiate(func_ty));
        let mut found = false;
        let mut walked_all = true;
        for arg in args {
            let ExprKind::Pi(_, dom, body) = cur.kind() else {
                walked_all = false;
                break;
            };
            let dom_inst = self.whnf(&self.metas.instantiate(dom));
            if is_unascribed_lambda(&arg.expr) && self.has_metavars(&dom_inst) {
                found = true;
            }
            let meta = self.fresh_meta(dom_inst);
            cur = self.whnf(&self.metas.instantiate(&body.instantiate(&meta)));
        }
        let result_is_safe = walked_all
            && !matches!(cur.kind(), ExprKind::Pi(_, _, _))
            && self.has_metavars(&cur)
            && Self::result_metavars_first_order_linear(&cur);
        self.metas.pop_scope();
        found && result_is_safe
    }

    /// NARROW re-try of the flex-application-slot gate (see the failed broad
    /// attempt recorded below).
    ///
    /// Fires ONLY for a CONSTRUCTOR head whose own inductive is *syntactically*
    /// the head constant of the expected type — `Equivalence.mk … : Equivalence
    /// ?r` against expected `Equivalence trivRel` — AND only when some remaining
    /// slot type is a flex application (a metavariable in application-HEAD
    /// position, e.g. the `refl` field `∀ x : ?α, ?r x x`). Such a slot can never
    /// be solved argument-first: matching against `?r x x` is a Miller-pattern
    /// problem the unifier rejects as a rigid shape clash, so Lean's
    /// `propagateExpectedType` (App.lean:414) pins the result type first.
    ///
    /// WHY SO NARROW. A previous attempt gated on the flex-slot shape ALONE and
    /// broke 33 codata tests. Widening this predicate is not merely widening a
    /// test: it makes the pre-arg-unify BLOCK run on shapes it never ran on, and
    /// that block ASSIGNS metavariables. Codata's generated M-type machinery is
    /// built from `isigmaStep A B t X i`, whose slots (`(b : B i a) → X (t i a
    /// b)`) are flex applications by construction, so the broad form matched the
    /// whole encoding and pre-pinning wrecked it. The expected type is compared
    /// WITHOUT whnf precisely so that a generated `Sigma.mk` against an expected
    /// `isigmaStep …` (head `isigmaStep`, not `Sigma`) does NOT match.
    fn ctor_flex_slot_needs_expected(
        &mut self,
        func: &SurfaceExpr,
        func_ty: &Expr,
        args: &[SurfaceArg],
    ) -> bool {
        let Some(expected) = self.current_expected_type.clone() else {
            return false;
        };
        // Head must be a constructor, and the expected type's head constant must
        // be that constructor's own inductive — compared UN-whnf'd (see above).
        let Some(ctor_name) = self.surface_head_const_name(func) else {
            return false;
        };
        let Some(ind_name) = self
            .env
            .get_constructor(&ctor_name)
            .map(|c| c.inductive_name.clone())
        else {
            return false;
        };
        let expected_inst = self.metas.instantiate(&expected);
        let ExprKind::Const(exp_head, _) = expected_inst.get_app_fn().kind() else {
            return false;
        };
        if *exp_head != ind_name {
            return false;
        }
        self.metas.push_scope();
        let mut cur = self.whnf(&self.metas.instantiate(func_ty));
        let mut found = false;
        for _ in args {
            let ExprKind::Pi(_, dom, body) = cur.kind() else {
                break;
            };
            let dom_inst = self.whnf(&self.metas.instantiate(dom));
            if Self::contains_flex_application(&self.metas, &dom_inst) {
                found = true;
                break;
            }
            let meta = self.fresh_meta(dom_inst);
            cur = self.whnf(&self.metas.instantiate(&body.instantiate(&meta)));
        }
        self.metas.pop_scope();
        found
    }

    /// Is there an application whose HEAD is an unassigned metavariable anywhere
    /// in `e` (under binders)? See [`Self::ctor_flex_slot_needs_expected`].
    fn contains_flex_application(metas: &MetaState, e: &Expr) -> bool {
        match e.kind() {
            ExprKind::App(f, a) => {
                let mut head = f.as_ref();
                while let ExprKind::App(g, _) = head.kind() {
                    head = g.as_ref();
                }
                let head_is_meta = matches!(head.kind(),
                    ExprKind::FVar(id) if MetaState::from_fvar(*id)
                        .is_some_and(|m| metas.get_assignment(m).is_none()));
                head_is_meta
                    || Self::contains_flex_application(metas, f)
                    || Self::contains_flex_application(metas, a)
            }
            ExprKind::Pi(_, d, b) | ExprKind::Lam(_, d, b) => {
                Self::contains_flex_application(metas, d)
                    || Self::contains_flex_application(metas, b)
            }
            _ => false,
        }
    }

    /// The head constant name of a surface application head, if it is a plain
    /// (possibly dotted) identifier naming an environment constant.
    fn surface_head_const_name(&self, func: &SurfaceExpr) -> Option<Name> {
        let mut cur = func;
        loop {
            match cur {
                SurfaceExpr::Ident(_, n) => {
                    let name = n.name().clone();
                    return self.env.get_constructor(&name).map(|_| name);
                }
                // `Equivalence.mk` reaches the elaborator as PROJECTION-POSTFIX
                // (`Proj(Ident("Equivalence"), Named("mk"))`), not as a dotted
                // identifier — the same parse shape the codata command has to
                // accept for `C.mk`. Without this arm the gate never fires.
                SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                    let SurfaceExpr::Ident(_, ns) = base.as_ref() else {
                        return None;
                    };
                    let name = ns.append(field).into_name();
                    return self.env.get_constructor(&name).map(|_| name);
                }
                SurfaceExpr::Explicit(_, inner) | SurfaceExpr::Paren(_, inner) => cur = inner,
                _ => return None,
            }
        }
    }

    /// General result-only-implicit propagation gate (mirrors Lean's
    /// `propagateExpectedType`, App.lean:414).
    ///
    /// Fires when a result-type implicit metavariable would otherwise leak
    /// because no argument pins it: e.g. `Or.inl rfl : x = x ∨ False`. `Or.inl`
    /// has type `{a b : Prop} → a → Or a b`; after inserting the leading
    /// implicits as metas, the explicit arg `rfl` is elaborated against `?a` —
    /// but `rfl` does not itself pin `?a`, and `?b` only appears in the result
    /// `Or ?a ?b`. The post-hoc final unify (`apply_implicit_to_expected_type`)
    /// runs too late and against an already-mis-assigned `?a`. Unifying the
    /// application's result type against the expected type *before* the args are
    /// elaborated pins `?a`/`?b` up front, so `rfl` resolves correctly.
    ///
    /// Conditions (all required):
    ///   (a) an expected type is in scope;
    ///   (b) the expected type, in WHNF, is NOT a `Sort` (Lean explicitly skips
    ///       propagating `Prop`/`Sort` into argument positions — App.lean:444 —
    ///       because it over-pins argument-position metavariables);
    ///   (c) walking the remaining-arg Pi spine leaves a result type that still
    ///       contains unsolved metavariables (so there is something to pin).
    ///
    /// Read-only: runs entirely under a throwaway `metas` scope, so no
    /// assignment leaks. The actual pin happens in the speculative block below
    /// (and is itself kernel-re-checked), so soundness is unchanged.
    fn result_only_implicit_needs_expected(&mut self, func_ty: &Expr, args: &[SurfaceArg]) -> bool {
        let Some(expected) = self.current_expected_type.clone() else {
            return false;
        };
        // Guard (b): never propagate a Sort/Prop expected type into arg slots.
        let expected_whnf = self.whnf(&self.metas.instantiate(&expected));
        if matches!(expected_whnf.kind(), ExprKind::Sort(_)) {
            return false;
        }
        self.metas.push_scope();
        let mut cur = self.whnf(&self.metas.instantiate(func_ty));
        let mut walked_all = true;
        let mut domains: Vec<Expr> = Vec::new();
        let mut arg_slot_metas: std::collections::HashSet<MetaId> =
            std::collections::HashSet::new();
        for _ in 0..args.len() {
            let ExprKind::Pi(_, dom, body) = cur.kind() else {
                walked_all = false;
                break;
            };
            let dom_inst = self.metas.instantiate(dom);
            domains.push(dom_inst.clone());
            let meta = self.fresh_meta(dom_inst);
            // Record the fresh per-ARGUMENT metavar so it is NOT mistaken for a
            // result-only implicit below: it is pinned by the actual argument, and
            // for a result that depends on the arg (`pe_nil m : Eq (pe m []) …`)
            // it leaks into `cur` even though `m`'s domain is metavar-free.
            if let ExprKind::FVar(id) = meta.kind() {
                if let Some(mid) = MetaState::from_fvar(*id) {
                    arg_slot_metas.insert(mid);
                }
            }
            cur = self.whnf(&self.metas.instantiate(&body.instantiate(&meta)));
        }
        // Regression guard (merge re-verify, 2026-06-28): pre-arg result-type
        // unification is only completeness-safe when each unsolved metavar in the
        // result type can be pinned by a SINGLE FIRST-ORDER match against the
        // expected type — the `Or.inl rfl : x = x ∨ False` shape (`Or ?a ?b`:
        // distinct metavars as direct args of the head). When a metavar instead
        // occurs in APPLICATION-HEAD position (`congrArg`'s `@Eq ?β (?f a₁)
        // (?f a₂)`) or MORE THAN ONCE (`rfl`'s `@Eq ?α ?a ?a`), eagerly unifying
        // result-vs-expected does premature higher-order / forced unification that
        // mis-assigns the metavar, so otherwise-valid proofs — chained
        // `Eq.trans (congrArg …) …`, `rfl`/`decide` on a reducible goal — fail to
        // elaborate (they elaborated correctly before this gate existed). Skipping
        // propagation for those terms restores the pre-gate behavior while keeping
        // the `Or`/`And`/`Iff` result-only-implicit cases this gate was added for.
        // ELAB-only and kernel-re-checked, so soundness is unchanged either way.
        // A `cur` that is still a `Pi` means the walk did NOT reach the true
        // result type — there are auto-inserted implicit/instance binders pending
        // beyond the surface args (e.g. `decide p`'s `[Decidable p] → Bool`: the
        // `[Decidable p]` instance arg is not a surface arg, so the metavar `?p`
        // in its domain is a SLOT metavar, not a result-only implicit). Firing
        // here would unify a function type against the (non-`Pi`) expected type
        // and spuriously fail ("Const vs Pi"). Require the result to be reached.
        let ret_is_pi = matches!(cur.kind(), ExprKind::Pi(_, _, _));
        // Genuinely RESULT-ONLY implicit: a metavar that appears in the result
        // type but in NONE of the argument domains — the actual
        // `propagateExpectedType` precondition. `Eq.symm`/`Eq.trans`/`Eq.mp` have
        // every result metavar ALSO occurring in an argument's type, so they are
        // arg-driven (the inner proof determines the equality sides) and must NOT
        // be pre-pinned from the expected type: pre-pinning forces the
        // un-normalized goal sides onto the inner proof and breaks reducible-term
        // chains (`parEvalV`/`Int.add`/`Bool.xor` → `List.rec`/`…`). `Or.inl rfl`'s
        // `?b` genuinely occurs only in the result, so it stays eligible.
        let mut dom_metas = std::collections::HashSet::new();
        for d in &domains {
            Self::collect_metavars(d, &mut dom_metas);
        }
        let mut cur_metas = std::collections::HashSet::new();
        Self::collect_metavars(&cur, &mut cur_metas);
        // A genuine result-only implicit is a metavar in the result that is
        // NEITHER pinned by an argument's domain NOR a fresh per-argument slot
        // metavar (the latter is pinned by the actual argument value).
        let has_result_only_meta = cur_metas
            .iter()
            .any(|m| !dom_metas.contains(m) && !arg_slot_metas.contains(m));
        let ret_has_metas = walked_all
            && !ret_is_pi
            && has_result_only_meta
            && self.has_metavars(&cur)
            && Self::result_metavars_first_order_linear(&cur);
        self.metas.pop_scope();
        ret_has_metas
    }

    /// Collect the unsolved metavariables (as [`crate::unify::MetaId`]s) occurring
    /// anywhere in `e`. Used by [`Self::result_only_implicit_needs_expected`] to
    /// detect genuinely result-only implicits.
    fn collect_metavars(e: &Expr, out: &mut std::collections::HashSet<MetaId>) {
        match e.kind() {
            ExprKind::FVar(id) => {
                if let Some(mid) = MetaState::from_fvar(*id) {
                    out.insert(mid);
                }
            }
            ExprKind::App(f, a) => {
                Self::collect_metavars(f, out);
                Self::collect_metavars(a, out);
            }
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                Self::collect_metavars(t, out);
                Self::collect_metavars(b, out);
            }
            ExprKind::Let(_, t, v, b, _) => {
                Self::collect_metavars(t, out);
                Self::collect_metavars(v, out);
                Self::collect_metavars(b, out);
            }
            ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => Self::collect_metavars(x, out),
            _ => {}
        }
    }

    /// Helper for [`Self::result_only_implicit_needs_expected`] and
    /// [`Self::typed_value_arg_in_open_slot`]: `true` iff every unsolved
    /// metavariable in `e` occurs AT MOST ONCE and NEVER in application-head
    /// position — i.e. unifying `e` against an expected type would yield only
    /// first-order pattern constraints (`Or ?a ?b`), never higher-order
    /// (`@Eq ?β (?f a₁) (?f a₂)`) or forced (`@Eq ?α ?a ?a`) ones.
    fn result_metavars_first_order_linear(e: &Expr) -> bool {
        fn walk(e: &Expr, seen: &mut std::collections::HashSet<MetaId>, bad: &mut bool) {
            if *bad {
                return;
            }
            // Higher-order (applied) metavar: any application whose spine head is
            // an unsolved metavar FVar.
            if matches!(e.kind(), ExprKind::App(_, _)) {
                if let ExprKind::FVar(id) = e.get_app_fn().kind() {
                    if MetaState::from_fvar(*id).is_some() {
                        *bad = true;
                        return;
                    }
                }
            }
            match e.kind() {
                ExprKind::FVar(id) => {
                    if let Some(mid) = MetaState::from_fvar(*id) {
                        // A repeated metavar would force `?m =?= lhs` AND
                        // `?m =?= rhs`, equating two result-type subterms early.
                        if !seen.insert(mid) {
                            *bad = true;
                        }
                    }
                }
                ExprKind::App(f, a) => {
                    walk(f, seen, bad);
                    walk(a, seen, bad);
                }
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    walk(t, seen, bad);
                    walk(b, seen, bad);
                }
                ExprKind::Let(_, t, v, b, _) => {
                    walk(t, seen, bad);
                    walk(v, seen, bad);
                    walk(b, seen, bad);
                }
                ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => walk(x, seen, bad),
                _ => {}
            }
        }
        let mut seen = std::collections::HashSet::new();
        let mut bad = false;
        walk(e, &mut seen, &mut bad);
        !bad
    }

    /// Does this surface expression contain a *bare numeric literal* (`0`, `8`)
    /// that would default to `Nat` for want of a type — either directly, or as
    /// an operand of a nested application spine?
    ///
    /// Direct: the expression itself is `Nat(_)` (parentheses unwrapped).
    /// Nested: an application `f a₀ … aₙ` where some operand recursively
    /// contains such a literal — covers the polymorphic-wrapper case
    /// `some (List.replicate 8 0)`, where pinning the wrapper's slot from the
    /// expected type flows the element type into the inner application.
    ///
    /// An *annotated* literal (`(0 : UInt8)`) is an `Ascription`, not a `Lit`,
    /// so it is correctly excluded — its type is already fixed. The recursion is
    /// only consulted when the enclosing parameter slot is an open metavariable
    /// (see [`bare_nat_literal_in_open_slot`]), so it cannot perturb
    /// concrete-typed arithmetic slots.
    fn surface_contains_bare_nat_literal(e: &SurfaceExpr) -> bool {
        let mut e = e;
        while let SurfaceExpr::Paren(_, inner) = e {
            e = inner;
        }
        match e {
            SurfaceExpr::Lit(_, SurfaceLit::Nat(_)) => true,
            SurfaceExpr::App(_, head, app_args) => {
                Self::surface_contains_bare_nat_literal(head)
                    || app_args
                        .iter()
                        .any(|a| Self::surface_contains_bare_nat_literal(&a.expr))
            }
            // `if c then t else e` (e.g. `[if b then 1 else 0] : List UInt8`):
            // each branch is checked against the element type, so a bare literal
            // in a branch needs the slot pinned just like a direct literal. The
            // condition is ignored — it has its own `Bool`/`Decidable` type.
            SurfaceExpr::If(_, _, t, f) => {
                Self::surface_contains_bare_nat_literal(t)
                    || Self::surface_contains_bare_nat_literal(f)
            }
            _ => false,
        }
    }

    /// The candidates of an ambiguous application head, if it is one. Kept
    /// out of line: `elab_app` is on the recursion path of every nested
    /// application, and the resolver's frame must not be added to each level
    /// (`codata_cmd_tests::test_codata_stream_encoding_survives_small_thread_stack`).
    #[inline(never)]
    fn ambiguous_head(&self, name: &SurfaceName) -> Option<Vec<Name>> {
        match self.resolve_ident_target(name) {
            elab_core::IdentTarget::Ambiguous(candidates) => Some(candidates),
            _ => None,
        }
    }

    /// [`Self::elab_overloaded`] for an application headed by an ambiguous
    /// identifier (out of line for the same reason as [`Self::ambiguous_head`]).
    #[inline(never)]
    fn elab_overloaded_app(
        &mut self,
        span: clean_parser::Span,
        candidates: &[Name],
        args: &[SurfaceArg],
    ) -> Result<Expr, ElabError> {
        let args = args.to_vec();
        self.elab_overloaded(span, candidates, move |head| {
            SurfaceExpr::App(span, Box::new(head), args.clone())
        })
    }

    pub(in crate::infer) fn elab_app(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Expr, ElabError> {
        // Handle @explicit marker: @f x y parses as App(Explicit(f), [x, y]) (#1255)
        // The @ marker should suppress implicit argument insertion for the entire
        // application, not just the function resolution. Unwrap Explicit and set
        // explicit_mode for the duration of this elab_app call.
        if let SurfaceExpr::Explicit(_, inner) = func {
            let prev = self.explicit_mode;
            self.explicit_mode = true;
            let result = self.elab_app_inner(inner, args);
            self.explicit_mode = prev;
            return result;
        }
        // `@f.{u v} x`: the parser nests the `@` marker INSIDE the
        // universe-instance node — `App(UniverseInst(Explicit(f), levels), x)`
        // — so the direct-`Explicit` unwrap above misses it. Unwrap it here so
        // the head stays `UniverseInst(f, levels)` (explicit levels preserved)
        // AND `explicit_mode` is on for the whole application, letting `x` fill
        // `f`'s leading explicit binder rather than an inserted implicit
        // metavar. Without this, `Nat` was routed into id's *value* slot,
        // pinning `{α : Sort n} := Sort 1` and inverting the level check
        // (GAP_SWEEP universes/p39: `@id.{1} Nat` must accept, `@id.{2} Nat`
        // must reject).
        if let SurfaceExpr::UniverseInst(span, base, levels) = func {
            if let SurfaceExpr::Explicit(_, inner) = base.as_ref() {
                let rebuilt_head = SurfaceExpr::UniverseInst(
                    *span,
                    Box::new(inner.as_ref().clone()),
                    levels.clone(),
                );
                let prev = self.explicit_mode;
                self.explicit_mode = true;
                let result = self.elab_app_inner(&rebuilt_head, args);
                self.explicit_mode = prev;
                return result;
            }
        }
        // An ambiguous head is resolved by the application it heads (Lean's
        // overload resolution, `ElabCtx::elab_overloaded`).
        if let SurfaceExpr::Ident(span, name) = func {
            if let Some(candidates) = self.ambiguous_head(name) {
                return self.elab_overloaded_app(*span, &candidates, args);
            }
        }
        // Lean's result-is-outParam defaulting (`elab_let_postpone.rs`).
        let open_before = self.open_waiting_carriers();
        let saved_floor = self.settle_floor;
        let saved_bne = self.bne_beq_head;
        if let Some(head) = Self::bne_desugaring_beq_head(func, args) {
            self.bne_beq_head = Some(head);
        } else if Self::is_lean_binrel_notation_head(func)
            && !matches!(func, SurfaceExpr::Ident(span, _) if Some(*span) == self.bne_beq_head)
        {
            self.settle_floor = Some(self.metas.postponed_numeral_count());
        }
        // An operator tree's root plans which leaves a later leaf's
        // defaulting settles (`elab_binop_leaf.rs`).
        let plan = self.binop_tree_plan(func, args);
        let term = match plan {
            Some(plan) if plan.refuse => Err(ElabError::Unsupported {
                feature: "an operator tree whose operand Lean elaborates alone (a later operand \
                          applies the numerals' default instances) is written exactly as one it \
                          does not"
                    .to_owned(),
            }),
            Some(plan) => {
                self.binop_tree_plans.push(plan);
                let term = self.elab_app_inner(func, args);
                self.binop_tree_plans.pop();
                term
            }
            None => self.elab_app_inner(func, args),
        };
        self.settle_floor = saved_floor;
        self.bne_beq_head = saved_bne;
        let term = term?;
        self.settle_at_open_out_param_result(func, args, &term, &open_before)?;
        Ok(term)
    }

    /// Return the registered eliminator's ordering, preserving genuine imported
    /// recOn/casesOn definitions whose primitive metadata lives under rec.
    fn elaboration_recursor(
        &self,
        applied_name: &Name,
    ) -> Option<(clean_kernel::RecursorVal, bool)> {
        if let Some(rec) = self.env.get_recursor(applied_name) {
            let major_first = rec.arg_order == clean_kernel::RecursorArgOrder::MajorAfterMotive;
            return Some((rec.clone(), major_first));
        }
        let clean_kernel::name::NameInner::Str(parent, suffix) = applied_name.inner() else {
            return None;
        };
        if suffix.as_ref() != "recOn" && suffix.as_ref() != "casesOn" {
            return None;
        }
        self.env.get_const(applied_name)?;
        let primitive = parent.as_ref().clone().str("rec");
        let rec = self.env.get_recursor(&primitive)?.clone();
        // For empty auxiliaries casesOn and recOn have the same canonical
        // wrapper. Other imported definitions keep their ordinary application
        // path until their distinct minor telescopes are authenticated.
        if rec.num_indices != 0 || rec.num_motives != 1 || rec.num_minors != 0 {
            return None;
        }
        self.authenticate_imported_cases_on_cached(applied_name, &primitive, &[])
            .ok()?;
        Some((rec, true))
    }

    /// Read the motive slot from the actual applied declaration, including an
    /// imported auxiliary's own annotations. Parameter bodies need not be
    /// instantiated just to inspect this binder's metadata.
    fn elaboration_motive_info(&self, name: &Name, num_params: u32) -> Option<BinderInfo> {
        let mut ty = &self.env.get_const(name)?.type_;
        for _ in 0..num_params {
            let ExprKind::Pi(_, _, body) = ty.kind() else {
                return None;
            };
            ty = body;
        }
        let ExprKind::Pi(binder, _, _) = ty.kind() else {
            return None;
        };
        Some(binder.info)
    }

    /// Construct the same expected-type motive for ordinary eliminator calls
    /// and a completed empty-eliminator field access. Every resulting term
    /// still follows the existing full declaration/kernel registration path.
    fn recursor_head_from_expected_type(
        &mut self,
        name: &Name,
        inductive_name: &Name,
        major: &Expr,
        major_type: &Expr,
        expected: &Expr,
    ) -> Result<Expr, ElabError> {
        let expected = self
            .metas
            .instantiate_levels(&self.metas.instantiate(expected));
        let major_type = self.whnf(major_type);
        // Lean's mkMotive abstracts the discriminant even when it is an
        // application, rather than silently making that motive constant.
        let body = self.abstract_eliminator_motive(&expected, major);
        let motive = Expr::lam(BinderInfo::Default, major_type.clone(), body);
        let levels = self.eliminator_levels(name, &major_type, &expected)?;
        let head = Expr::const_(name.clone(), levels);
        let head = self.apply_eliminator_params(
            head,
            &major_type,
            &SurfaceName::from_name(inductive_name.clone()),
        )?;
        Ok(Expr::app(head, motive))
    }

    /// Classify the same declared application for speculative definition
    /// dispatch and for actual expected-type eliminator elaboration.
    fn recursor_application<'b>(
        &self,
        func: &SurfaceExpr,
        args: &'b [SurfaceArg],
    ) -> Option<RecursorApplication<'b>> {
        if self.explicit_mode || args.iter().any(|arg| arg.name.is_some()) {
            return None;
        }
        let full_name = Self::func_qualified_name(func)?;
        let applied_name = full_name.name().clone();
        let (rec, major_first) = self.elaboration_recursor(&applied_name)?;
        if !self.func_denotes_global_name(func, &applied_name)
            || rec.num_indices != 0
            || rec.num_motives != 1
        {
            return None;
        }
        let args = match self.elaboration_motive_info(&applied_name, rec.num_params) {
            Some(BinderInfo::Default) => {
                let (motive, rest) = args.split_first()?;
                if !matches!(
                    Self::unwrap_surface_parens(&motive.expr),
                    SurfaceExpr::Hole(_)
                ) {
                    return None;
                }
                rest
            }
            Some(BinderInfo::Implicit | BinderInfo::StrictImplicit) => args,
            _ => return None,
        };
        (args.len() == rec.num_minors as usize + 1).then_some(RecursorApplication {
            name: applied_name,
            recursor: rec,
            major_first,
            args,
        })
    }

    /// Expected-type eliminator elaboration for one-motive, non-indexed calls.
    /// An explicit motive receives ordinary positional arguments as declared;
    /// only a syntactic hole invokes inference (Lean App.lean elabAsElim?).
    fn try_elab_recursor_as_elim(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Option<Expr>, ElabError> {
        let Some(application) = self.recursor_application(func, args) else {
            return Ok(None);
        };
        let RecursorApplication {
            name: applied_name,
            recursor: rec,
            major_first,
            args,
        } = application;
        let Some(expected) = self.current_expected_type.clone() else {
            return Ok(None);
        };
        let major_index = if major_first { 0 } else { args.len() - 1 };
        // The major is checked against its own declared domain, never the
        // result type of the whole eliminator application.
        let declaration = self.env.get_const(&applied_name).cloned().ok_or_else(|| {
            ElabError::InternalInvariant(format!("missing eliminator `{applied_name}`"))
        })?;
        let level_subst: Vec<_> = declaration
            .level_params
            .iter()
            .map(|name| (name.clone(), self.fresh_universe_param()))
            .collect();
        let mut telescope = declaration.type_.instantiate_level_params(&level_subst);
        let preceding =
            rec.num_params + rec.num_motives + if major_first { 0 } else { rec.num_minors };
        for _ in 0..preceding {
            let ExprKind::Pi(_, domain, body) = telescope.kind() else {
                return Ok(None);
            };
            telescope = body.instantiate(&self.fresh_meta(domain.as_ref().clone()));
        }
        let ExprKind::Pi(_, major_domain, _) = telescope.kind() else {
            return Ok(None);
        };
        let major = self.elaborate_arg_with_expected_type(
            &args[major_index].expr,
            Some(major_domain.as_ref().clone()),
        )?;
        let major_type = self.whnf(
            &self
                .metas
                .instantiate_levels(&self.metas.instantiate(&self.infer_type(&major)?)),
        );
        if !matches!(major_type.get_app_fn().kind(), ExprKind::Const(n, _) if *n == rec.inductive_name)
        {
            return Ok(None);
        }
        let mut result = self.recursor_head_from_expected_type(
            &applied_name,
            &rec.inductive_name,
            &major,
            &major_type,
            &expected,
        )?;
        let mut result_type = self.whnf(&self.infer_type(&result)?);
        for (index, arg) in args.iter().enumerate() {
            let ExprKind::Pi(_, domain, body) = result_type.kind() else {
                return Ok(None);
            };
            let domain = self.metas.instantiate(domain);
            let body = body.clone();
            let value = if index == major_index {
                major.clone()
            } else {
                self.elaborate_arg_with_expected_type(&arg.expr, Some(domain.clone()))?
            };
            self.enforce_expr_type(&value, &domain)?;
            let value = self.metas.instantiate(&value);
            result_type = self.whnf(&self.metas.instantiate(&body.instantiate(&value)));
            result = Expr::app(result, value);
        }
        Ok(Some(result))
    }

    pub(super) fn elab_app_inner(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Expr, ElabError> {
        // B104: consume the one-shot heterogeneous-fallback flag FIRST, before
        // any nested elaboration can observe it — only THIS application (the
        // retried binop) skips homogeneous slot pinning; operands and other
        // sub-elaborations behave exactly as on the first attempt.
        let suppress_binop_homogenize = std::mem::take(&mut self.suppress_binop_homogenize);
        // G28: argument indices whose un-annotated lambda this application
        // postpones (`elab_app_postpone_lambda.rs`); one-shot, so nested
        // applications never see the retry's set.
        let deferred_lambda_args = self.take_deferred_lambda_args();
        // Anonymous ctor `⟨val⟩` (#172) + `pure x` in do-block (#3435).
        if matches!(func, SurfaceExpr::Ident(_, n) if clean_parser::is_anonymous_constructor_head(n))
        {
            return self.elab_anonymous_ctor(args);
        }
        // `(e :)`: `e` with no expected type (Lean's type-less
        // `typeAscription`, `Lean/Elab/BuiltinNotation.lean:433-435`).
        if matches!(
            func,
            SurfaceExpr::Ident(_, n) if clean_parser::is_type_ascription_without_type(n)
        ) {
            return self.elab_ascription_without_type(args);
        }
        // Bare `ite` application re-route (ite STEP 2 PART A).
        //
        // The plain-`if` surface macro (`ifThenElse $c $t $e`) rewrites at the
        // syntax level into `App(Ident("ite"), [c, t, e])` BEFORE the
        // syntax→surface step, so the from_syntax `ifThenElse` handler never
        // sees an `if_then_else` node and the `SurfaceExpr::If` elab bypass is
        // skipped. The macro template drops the `{α : Sort u}` and
        // `[Decidable c]` slots that `ite` requires, so this app reaches
        // elab_app as a bare 3-explicit-arg constant application. Generic
        // implicit insertion then mis-aligns the branch positions when `α` is
        // unconstrained (the Eq-LHS case), producing a spurious TypeMismatch.
        //
        // Re-route a bare `ite c t e` (exactly 3 positional args, non-explicit
        // mode) back through `elab_if`, which already synthesizes the shared
        // branch result type (→ α), computes the level, resolves the
        // `[Decidable c]` instance, and routes Bool conditions through
        // `Bool.rec` — exactly the desugaring the surface `if` would have used.
        //
        // SOUNDNESS: this reroute is ELAB-only. It produces an ordinary kernel
        // `ite`/`Bool.rec` term (identical to what `elab_if` builds for the
        // equivalent surface `if`), which is re-checked by the kernel via
        // `add_decl` when the declaration is added. If the reroute were ever
        // wrong (e.g. a user constant named `ite` with a different 3-arg
        // signature), the resulting term simply fails the kernel re-check and
        // `clean check` errors — it cannot fabricate a false `proved`. No
        // `add_decl_unchecked`/`add_decl_structural`, no new axioms. The guard
        // is conservative — exactly 3 positional args and non-explicit mode —
        // so `@ite …`, partial applications, and named-arg calls are untouched.
        if !self.explicit_mode {
            if let SurfaceExpr::Ident(_, n) = func {
                // Only the GLOBAL `ite`: a local named `ite` is the user's own
                // function (`def g (ite : Bool → Nat → Nat → Nat) := ite true 1
                // 2` proved `g (fun _ _ c => c) = 1`; Lean 4.8.0: `2`).
                if self.head_denotes_global(n, "ite")
                    && args.len() == 3
                    && args.iter().all(|a| a.name.is_none())
                {
                    return self.elab_if(&args[0].expr, &args[1].expr, &args[2].expr);
                }
                // `▸` subst re-route (Brick E2). The parser desugars
                // `heq ▸ h` to `App(Ident("Eq.rec"), [heq, h])`
                // (`grammar/expr_operators.rs::subst_expr`) — an equation-FIRST
                // shape a plain application can never elaborate (`@Eq.rec`
                // takes the minor premise before the equation, and the motive
                // must be inferred from the expected type). Route the exact
                // desugar shape to the Lean-faithful `elabSubst` port in
                // `elab_subst.rs`. A hand-written `Eq.rec …` in source parses
                // with a projection head (dotted names are not single idents),
                // so it cannot reach this arm; `@Eq.rec …` is explicit mode.
                // When the first operand's type is not an equality the arm
                // yields `None` and we fall through to the generic application
                // path, which fails loudly (fail-closed either way).
                //
                // SOUNDNESS: ELAB-only. The arm builds an ordinary kernel
                // `@Eq.rec` application that is re-checked by the kernel on
                // registration — it cannot fabricate a false `proved`. The
                // orientation of the inferred motive is value-relevant for
                // computational casts, which is why the arm replicates Lean's
                // rhs-first-then-lhs-with-symm search exactly (see the module
                // docs and `tests/brick_e2_subst_e2e.rs`).
                if self.head_denotes_global(n, "Eq.rec")
                    && args.len() == 2
                    && args.iter().all(|a| a.name.is_none())
                {
                    if let Some(subst) = self.try_elab_subst(&args[0].expr, &args[1].expr)? {
                        return Ok(subst);
                    }
                }
            }
        }
        if let Some(p) = self.try_short_circuit_do_pure(func, args)? {
            return Ok(p);
        }
        if let Some(bool_not) = self.try_elab_bool_not_app(func, args)? {
            return Ok(bool_not);
        }
        if let Some(eq) = self.try_elab_eq_struct_lit_reorder(func, args)? {
            return Ok(eq);
        }
        if let Some(elim) = self.try_elab_recursor_as_elim(func, args)? {
            return Ok(elim);
        }
        if let Some(result) = self.try_elab_recursive_call(func, args)? {
            return Ok(result);
        }
        if let Some(result) = self.try_elab_recursive_dot_call(func, args)? {
            return Ok(result);
        }

        let mut dot_head = if args.iter().any(|a| a.name.is_some() && !a.is_ellipsis()) {
            DotHeadCapture::Named(None)
        } else {
            DotHeadCapture::Positional {
                generated_binders: 0,
            }
        };
        let mut receiver_source = None;
        let func_expr = match Self::unwrap_surface_parens(func) {
            SurfaceExpr::Proj(_, base, field @ Projection::Named(_))
                if matches!(dot_head, DotHeadCapture::Named(_)) =>
            {
                receiver_source = Some(base.as_ref());
                let saved_route = self.dot_elim.arm_app_head(func, args);
                let saved_expected = self.current_expected_type.take();
                let head = self.elab_proj(base, field, Some(&mut dot_head));
                self.current_expected_type = saved_expected;
                self.dot_elim.restore_app_head(saved_route);
                head?
            }
            SurfaceExpr::Ident(_, name)
                if matches!(func, SurfaceExpr::Ident(..)) && name.is_relative_constructor() =>
            {
                // A leading-dot constructor in application *head* position
                // (`.ctor arg …`). Prefer the expected type when one is in
                // scope; otherwise hand `elab_leading_dot_ctor_with_expected_type`
                // a fresh metavariable so its suffix-recovery fallback can find
                // the inductive from the constructor name alone (e.g. a
                // `match (.ctor …) with` scrutinee, where no motive type is
                // propagated). Recovery still returns `UnknownIdent` for an
                // ambiguous/unknown suffix, so the no-expected-type error
                // surface is preserved for the genuinely unresolvable cases.
                let expected_ty = self
                    .current_expected_type
                    .clone()
                    .unwrap_or_else(|| self.fresh_meta(Expr::type_()));
                self.elab_leading_dot_ctor_with_expected_type(name, &expected_ty)?
            }
            // The whole application's result is not the function head's
            // expected type. In particular a dot recursor with supplied
            // motive arguments must retain those slots for this argument loop.
            // Parenthesizing the field itself elaborates it as a standalone
            // function. Its lambda is then the authored application's head.
            SurfaceExpr::Proj(_, _, Projection::Named(_))
                if matches!(func, SurfaceExpr::Proj(..)) =>
            {
                self.elaborate_app_head_without_expected(func, args, Some(&mut dot_head))?
            }
            _ => self.elaborate_app_head_without_expected(func, args, None)?,
        };

        let (dot_receiver, mut generated_binders) = match dot_head {
            DotHeadCapture::Named(receiver) => (receiver, 0),
            DotHeadCapture::Positional { generated_binders } => (None, generated_binders),
        };
        // Consume only lambdas introduced to put the receiver after earlier
        // explicit arguments. Lean emits the ordinary method call for supplied
        // arguments, and a partial application keeps its remaining binders.
        let mut apply_arg = |function: Expr, argument: Expr| {
            if generated_binders > 0 {
                if let ExprKind::Lam(_, _, body) = function.kind() {
                    generated_binders -= 1;
                    return body.instantiate(&argument);
                }
            }
            Expr::app(function, argument)
        };

        // Expand a trailing `..` (Lean `Term.ellipsis`) into the explicit
        // holes it abbreviates, BEFORE named-argument resolution — the marker
        // carries a reserved `name`, so `resolve_named_args` would otherwise
        // report it as an unknown parameter. `..` needs the elaborated head's
        // arity, which is why it happens here and not in the parser.
        let ellipsis_args;
        let args = if dot_receiver.is_none() && args.iter().any(SurfaceArg::is_ellipsis) {
            ellipsis_args = self.expand_app_ellipsis(&func_expr, args)?;
            &ellipsis_args[..]
        } else {
            args
        };

        // Resolve named arguments (#1230): if any arg has a name, reorder
        // args to match parameter positions before the main elaboration loop.
        let has_named_args = args.iter().any(|a| a.name.is_some());
        let resolved_args;
        let (args, positioned_prefix, receiver_slot) = if has_named_args {
            resolved_args = self.resolve_named_args(
                &func_expr,
                args,
                dot_receiver.as_ref().zip(receiver_source),
            )?;
            (&resolved_args.0[..], resolved_args.1, resolved_args.2)
        } else {
            (args, 0, None)
        };

        // Try to infer the function's type to know about implicit arguments
        // If we can't infer it (e.g., function is a metavariable), fall back to simple elaboration
        let func_type_result = self.infer_type(&func_expr);

        if let Ok(func_type) = func_type_result {
            let remaining_args = args;
            // Only @ or named-slot resolution can authorize positional filling
            // of implicit binders. Argument count never changes their meaning.
            let mut leading_pending: Vec<(Expr, Expr)> = Vec::new();
            let (mut result, mut current_type) = if positioned_prefix == 0 {
                let (result, ty, pending) = self.insert_implicit_args_deferring_instances(
                    func_expr.clone(),
                    &func_type,
                    ArgsFollow::from_remaining(remaining_args.len()),
                );
                leading_pending = pending;
                (result, ty)
            } else {
                (func_expr.clone(), func_type.clone())
            };

            // Push scope so we can retry with Nat literals coerced to Real
            // without keeping earlier Nat constraints.
            self.metas.push_scope();

            // Homogeneous-default propagation for heterogeneous arithmetic binops
            // (`a % b`, `a + b`, `a ^ b`, ...). These desugar to
            // `@HMod.hMod ?α ?β ?γ ?inst a b` etc., where `?α ?β ?γ` were just
            // inserted as unconstrained metavariables. Lean resolves the operand
            // types with a `binop%` elaborator + `@[default_instance] instHMod :
            // HMod α α α` that makes the operation homogeneous; clean's naive
            // left-to-right loop instead elaborates the second operand against the
            // still-unconstrained `?β`, so `2 ^ width` in `val % (2 ^ width)`
            // defaults to `Nat`, pins `?β := Nat`, and then `HMod Int Nat Int` has
            // no instance — the instance metavar leaks to the kernel as a free
            // variable. We record the type-param slots up front and, after the
            // FIRST operand pins `?α`, collapse the homogeneous slots onto it so
            // the second operand inherits the right type — independent of whether
            // an expected result type is present (the body is elaborated once
            // without an expected type, so a result-type-driven fix alone would
            // miss `val % (2 ^ width)`).
            // B104 heterogeneous fallback: on the one-shot retry the slots are
            // left UNRECOGNIZED, so no pass pins `?β`/`?γ` — each operand
            // elaborates at its own type and the deferred `[HAdd ?α ?β ?γ]`
            // goal is synthesized directly against the (now concrete) operand
            // types, with the still-open result slot `?γ` solved by unifying
            // against the registered instance (Lean's outParam direction).
            let hetero_binop_slots = if suppress_binop_homogenize {
                None
            } else {
                self.hetero_binop_homogenize_slots(func, &result)
            };
            if let Some(slots) = &hetero_binop_slots {
                // Expected-result-type pass first (handles `2 ^ width : Int` and
                // the inner operand of a nested binop once the outer op pinned
                // the expected type).
                self.homogenize_hetero_binop_from_expected(slots);

                // Homogeneous binops (`+ - * / % ++` …) have `α = β = γ`. When one
                // operand is a value-less polymorphic literal (`[]`, which carries
                // no value to pin its element type) and the *other* carries a
                // concrete type, the literal must be elaborated against the
                // sibling's type — but the operand loop processes operands
                // left-to-right, so `[] ++ xs` would elaborate `[]` first against
                // an open slot and leak a free element-type/universe variable to
                // the kernel. Pre-pass: speculatively elaborate the *non-literal*
                // operand(s) first to pin the shared slot, so the literal then
                // elaborates against the concrete carrier. Order-independent — it
                // also covers `xs ++ []`. Pure ELAB: only assigns open slots; the
                // operands are re-elaborated normally in the loop and the kernel
                // re-checks the assembled term, so a wrong inference fails closed.
                if slots.homogeneous && remaining_args.len() == 2 {
                    let literal_idx = remaining_args
                        .iter()
                        .position(|a| Self::arg_needs_result_type_pinned(&a.expr));
                    if let Some(lit_idx) = literal_idx {
                        let carrier_idx = 1 - lit_idx;
                        // Only the *other* operand is a usable carrier (not itself a
                        // value-less literal).
                        if !Self::arg_needs_result_type_pinned(&remaining_args[carrier_idx].expr) {
                            // Speculatively elaborate the carrier operand to learn
                            // its concrete type, then pin the shared slot. We do
                            // NOT keep the elaborated term — the main loop
                            // re-elaborates it normally; we only want its type.
                            self.metas.push_scope();
                            let carrier_type = self
                                .elaborate(&remaining_args[carrier_idx].expr)
                                .ok()
                                .and_then(|e| self.infer_type(&e).ok())
                                .map(|t| self.whnf(&self.metas.instantiate(&t)));
                            // Drop any side metavars created during the speculative
                            // elaboration; keep only slot assignments by re-pinning
                            // against the committed parent scope.
                            self.metas.pop_scope();
                            if let Some(carrier_type) = carrier_type {
                                if !self.has_metavars(&carrier_type) {
                                    let targets = [&slots.alpha, &slots.beta, &slots.gamma];
                                    self.pin_open_type_slots(&targets, &carrier_type);
                                }
                            }
                        }
                    }
                }
            }

            // Carrier-first ordering for a bare NUMERAL operand (head-agnostic).
            //
            // The block above only fires for a recognised homogeneous `HOp`
            // binop and only for the two value-less container literals. A bare
            // numeral is the same kind of leaf — it carries no type and must
            // read the slot it lands in — but it appears under ANY polymorphic
            // head (`LT.lt`, `Eq`, `BEq.beq`, a user `{α} → α → α → …`) as well
            // as under the arithmetic binops, and it does not fail loudly: the
            // literal seam DEFAULTS it to `Nat`, which then rigidly mismatches
            // the sibling operand ("expected Nat, got UInt64"). See
            // `pin_open_slots_from_carrier_operand` for the full rationale.
            //
            // Suppressed on the B104 heterogeneous retry, which deliberately
            // elaborates each operand at its own type.
            if !self.explicit_mode && !suppress_binop_homogenize {
                // Lean propagates the expected type before the first explicit
                // argument (`propagateExpectedType`), so a slot the expected
                // type pins is not open for a sibling to pin: `min (1 - 7) 9 :
                // Int` has `α := Int` and is `-6` in Lean 4.8.0; pinning `α`
                // from the carrier `1 - 7` first made it `Nat` (`0`), and `min
                // (1 - 7) 9 = 0` was accepted at `Int`. The argument loop
                // below propagates again; a second unification of the same
                // pair changes nothing.
                if !has_named_args
                    && !Self::is_hetero_binop_head(func)
                    && !self.result_is_out_param_of_local_instance(&func_type)
                    && remaining_args
                        .iter()
                        .any(|a| Self::arg_is_bare_numeral(&a.expr))
                {
                    let _ = self.propagate_expected_type(&current_type, remaining_args);
                }
                self.pin_open_slots_from_carrier_operand(
                    &current_type,
                    remaining_args,
                    hetero_binop_slots.as_ref(),
                );
            }

            // Pre-arg expected-result unification — narrowly gated.
            //
            // Fires when (a) an expected type is in scope and (b) some remaining
            // argument is one of two type-directed literals that REQUIRE a
            // concrete expected type up front:
            //
            //   1. a *leading-dot constructor* (`.ctor` / `.ctor args`, possibly
            //      parenthesised). The dot-ctor head resolves against its
            //      expected type, and inside a polymorphic wrapper that type is
            //      still an open metavariable (`some (.frame x) : Option Value` ⇒
            //      `Option.some`'s arg type is `?α`). Speculatively unifying the
            //      application's return type with the expected type pins
            //      `?α := Value` so `.frame` resolves.
            //
            //   2. an *empty-list literal* `[]` (parsed as the bare ident
            //      `List.nil`). `List.nil : {α : Type u} → List α` carries no
            //      operand to pin its element type, so when it lands in a
            //      polymorphic argument slot whose type is still an open
            //      metavariable — most importantly a tuple component
            //      (`(x, []) : A × List B` desugars to `Prod.mk x []` where
            //      `Prod.mk`'s second arg type is the unconstrained `?β`) — the
            //      element type *and its universe* `u` leak to the kernel as
            //      free variables ("Sort(Succ(Succ(u_N)))"). Unifying the
            //      application's return type with the expected `Prod A (List B)`
            //      pins `?β := List B`, which then drives `List.nil`'s element
            //      type. A non-empty `[a, …]` is unaffected: it desugars to
            //      `List.cons a …`, whose first operand already pins the element
            //      type.
            //
            // The gate keeps every other application path byte-identical (the
            // earlier unconditional version regressed Basic.lean / ValueMap by
            // over-pinning arithmetic/literal metas). Speculative: only open
            // metas are assigned and the kernel re-checks the final term.
            // A bare numeric literal (`0`, `8`) carries no type information and,
            // when it lands in an argument slot whose type is still an open
            // type-parameter metavariable (`α`), defaults eagerly to `Nat` and
            // pins that slot to `Nat`. For `List.replicate 8 0 : List UInt8`
            // (trust-ir `Semantics/Memory.lean` `encodeValue`'s axiomatized
            // `some (List.replicate 8 0)` placeholder), the element-type slot `α`
            // would thus be pinned to `Nat` instead of the expected `UInt8`,
            // producing a `List Nat` vs `List UInt8` mismatch. The pre-arg
            // expected-result unification below pins `α := UInt8` from the
            // expected type *before* the literal is elaborated, so the literal
            // resolves against the right element type via OfNat.
            //
            // Guard: only fire for a literal whose parameter slot is an *open
            // metavariable* — i.e. a polymorphic element slot, never a concrete
            // arithmetic slot (`Nat`/`Int`). This keeps Basic.lean's arithmetic
            // (`a % (2 ^ width)` etc.) byte-identical: those literals land in
            // concrete numeric slots, so the guard skips them. Speculative +
            // kernel-re-checked, so soundness is unchanged.
            let needs_pre_arg_unify = remaining_args
                .iter()
                .any(|a| Self::arg_needs_result_type_pinned(&a.expr))
                || self.bare_nat_literal_in_open_slot(&current_type, remaining_args)
                || self.by_block_arg_in_open_slot(&current_type, remaining_args)
                || self.lambda_arg_in_open_slot(&current_type, remaining_args)
                || self.result_only_implicit_needs_expected(&current_type, remaining_args)
                // Element coercion (gap A): a concrete-typed arg (`(3:Nat)`, a
                // variable) in an open type-param slot needs the slot pinned from
                // the expected result FIRST, so the arg then coerces to it. Only
                // for NON-hetero-binop heads — arithmetic keeps its `binop%`
                // homogenization path untouched.
                || (!Self::is_hetero_binop_head(func)
                    && self.typed_value_arg_in_open_slot(&current_type, remaining_args))
                // Constructor whose own inductive heads the expected type, with a
                // flex-application slot the argument can never pin (Lean pins it
                // via propagateExpectedType). Deliberately narrow — see the
                // helper's doc for the 33-codata-test regression that a broader
                // form caused.
                || self.ctor_flex_slot_needs_expected(func, &current_type, remaining_args)
                // The row above only fires when the expected type is SYNTACTICALLY
                // headed by the constructor's own inductive. Behind a `def`
                // (`CP (Nat.succ x)` for `def CP y : Prop := ∃ a b, a + b = y`) the
                // head is the definition, so nothing pinned `?p` and the argument
                // check faced the non-pattern `?p (Nat.succ x)`. Fire on the SLOT
                // shape instead of the head name, under the same first-order-linear
                // result guard. See the helper's doc.
                || self.rigid_arg_in_flex_slot(&current_type, remaining_args);
            // An expected type that is itself an unsolved metavariable has
            // nothing to push inward; firing the block would only pin it to a
            // half-open result. See `expected_is_unassigned_meta`. A literal
            // `Prop` is never pushed inward either — Lean's
            // `propagateExpectedType` skips it (`Prop` is used as a "Bool"),
            // and this block used to pin `List.head! s`'s carrier to `Prop` in
            // `(List.head! s : Prop)` with `s : List Bool` (measured
            // 2026-09-12; Lean accepts it).
            if needs_pre_arg_unify
                && !self.expected_is_unassigned_meta()
                && !self.expected_is_literal_prop()
                // This earlier heuristic must honor the same instance-owned
                // result boundary as ordinary expected-type propagation.
                && (self.explicit_mode
                    || !self.result_is_out_param_of_local_instance(&func_type))
            {
                if let Some(expected) = self.current_expected_type.clone() {
                    let mut ret_ty = self.whnf(&self.metas.instantiate(&current_type));
                    let mut ok = true;
                    for _ in 0..remaining_args.len() {
                        match ret_ty.kind() {
                            ExprKind::Pi(_, dom, body) => {
                                let dom_inst = self.metas.instantiate(dom);
                                let meta = self.fresh_meta(dom_inst);
                                ret_ty =
                                    self.whnf(&self.metas.instantiate(&body.instantiate(&meta)));
                            }
                            _ => {
                                ok = false;
                                break;
                            }
                        }
                    }
                    if ok {
                        // Try the *unreduced* expected type first so a monadic
                        // abbreviation in the expected result (`pure (.ctor …) :
                        // Sem StepRes` ⇒ expected `App(Sem, StepRes)`) keeps its
                        // surface `App(m, α)` spine. WHNF-ing it here would δ-unfold
                        // `Sem StepRes` into `MState → Except SErr (StepRes × MState)`
                        // (a Pi), so the flex application `?m ?α` we are unifying
                        // against (the wrapper's return type) would face a Pi and
                        // fail to pin `?α := StepRes` — the dot-ctor then cannot
                        // resolve (`Unknown identifier: .Continue`). Unifying against
                        // the App form solves `?m := Sem`, `?α := StepRes`
                        // structurally. Only fall back to the WHNF form if metas
                        // remain. Speculative + kernel-re-checked, so soundness is
                        // unchanged.
                        let expected_inst = self.metas.instantiate(&expected);
                        // Nested-inductive aux-mirror expected type (Track FF).
                        // A list literal `[.int …, .bool …]` whose element type is
                        // ambiguous (`.int` is owned by both `Value` and `Constant`)
                        // can only resolve once its `List ?α` element metavar is
                        // pinned. When this list lands in a constructor field of a
                        // *nested* inductive (`Value.aggregate : List Value → Value`),
                        // the kernel has rewritten the field type to the aux mirror
                        // `Value._List`, so the expected type the pre-arg pass would
                        // unify against is `Const(Value._List)` — a different head
                        // from the wrapper's `List ?α` return type, leaving `?α`
                        // open and `.int` unresolvable. Recover the *real* container
                        // type `List Value` from the aux mirror's `toContainer`
                        // codomain and unify against THAT instead, so `?α := Value`.
                        // The list value is still coerced back to the aux mirror by
                        // the existing Step 1c container→aux coercion and re-checked
                        // by the kernel, so soundness is unchanged. No-op for any
                        // expected type that is not an aux mirror.
                        let expected_inst = {
                            let expected_whnf = self.whnf(&expected_inst);
                            match self.aux_mirror_container_type(&expected_whnf) {
                                Some(container) => container,
                                None => expected_inst,
                            }
                        };
                        if self.has_metavars(&ret_ty) || self.has_metavars(&expected_inst) {
                            {
                                let ctx = self.build_local_ctx();
                                let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                                // Skip the eager leading WHNF: it would δ-unfold the
                                // monadic abbreviation in `expected_inst`
                                // (`App(Sem, StepRes)` → `Pi(…)`) and leave the flex
                                // `App(?m, ?α)` facing a Pi, so `?α` would never be
                                // pinned. `unify_no_initial_whnf` lets the structural
                                // App rule pair `?m := Sem`, `?α := StepRes`.
                                let _ = unifier.unify_no_initial_whnf(&ret_ty, &expected_inst);
                            }
                            // Fall back to the reduced form only if the App-form
                            // unification left the return type's metas unsolved.
                            let ret_ty_now = self.metas.instantiate(&ret_ty);
                            if self.has_metavars(&ret_ty_now) {
                                let expected_whnf = self.whnf(&expected_inst);
                                let ctx = self.build_local_ctx();
                                let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                                let _ = unifier.unify(&ret_ty_now, &expected_whnf);
                            }
                        }
                    }
                }
            }

            // GetElem `xs[i]` proof slot (Brick 4): the parser desugars
            // `xs[i]` to `getElem xs i _` — explicit args `[xs, i, hole]`
            // with the hole standing for Lean's `(by get_elem_tactic)` block
            // (`Init/GetElem.lean:82`). Identify the slot up front; the arg
            // loop below (a) resolves the deferred `[GetElem …]` instance
            // EARLY — right before the proof slot, once `xs`/`i` have pinned
            // `coll`/`idx` — so the `valid` out-param is concrete both for
            // the tactic goal and for unifying an explicit `xs[i]'h` proof
            // (a flex `?valid xs i` head otherwise invites a wrong
            // higher-order solution), and (b) discharges a syntactic hole in
            // that slot with the `get_elem_tactic` analog (elab_getelem.rs)
            // — never leaving it as a leakable metavariable. Skipped in
            // `@`-explicit mode, exactly like Lean's `@getElem` (no `by`
            // block there either).
            let getelem_proof_slot = if self.explicit_mode || remaining_args.len() != 3 {
                None
            } else {
                Self::getelem_valid_proof_slot(&result)
            };

            // Track Nat literals and their positions for potential coercion
            let mut nat_literal_indices: Vec<usize> = Vec::new();
            let mut elaborated_args: Vec<Expr> = Vec::new();
            // `by` blocks whose slot type still carried metavariables when
            // their turn came: (placeholder meta, the block, the slot type).
            // Run after the remaining arguments — see `deferrable_by_block`.
            let mut deferred_by_blocks: Vec<(Expr, SurfaceExpr, Expr)> = Vec::new();
            // Lean's `propagateExpected` flag (see `propagate_expected_type`).
            // Not armed for a heterogeneous arithmetic head (Clean's `binop%`
            // stand-in), nor when the result is an
            // `outParam` of the head's own instance binder (Lean's
            // `addImplicitArg` disarms it there; off under `@`, as in Lean).
            let mut propagate_expected = !Self::is_hetero_binop_head(func)
                && (self.explicit_mode || !self.result_is_out_param_of_local_instance(&func_type));
            // Process each explicit argument
            for (idx, arg) in remaining_args.iter().enumerate() {
                // Check the current type to see if we need more implicit args
                current_type = self.whnf(&current_type);

                // Brick 4 (a): pin the GetElem out-params before the proof
                // slot is elaborated. On failure, leave the pending list for
                // the ordinary post-loop path (fail-closed, unchanged).
                if getelem_proof_slot == Some(idx)
                    && !leading_pending.is_empty()
                    && self.resolve_deferred_instances(&leading_pending)
                {
                    leading_pending.clear();
                }

                // Lean's `processExplicitArg` propagates the expected type
                // before elaborating each explicit argument until it succeeds.
                if propagate_expected {
                    propagate_expected = self.propagate_expected_type_with_named_prefix(
                        &current_type,
                        &remaining_args[idx..],
                        positioned_prefix.saturating_sub(idx),
                    );
                }

                // Extract binder info and types to avoid borrow issues
                let type_info = match current_type.kind() {
                    ExprKind::Pi(bi, arg_ty, body_ty) => {
                        Some((*bi, arg_ty.as_ref().clone(), body_ty.as_ref().clone()))
                    }
                    _ => None,
                };

                if let Some((bi, expected_arg_ty, _body_ty)) = type_info {
                    let local_arg_ty = expected_arg_ty;

                    // Elaborate the actual argument with expected type context so
                    // bare polymorphic constants can consume their implicit args.
                    let expected_arg_ty = self.metas.instantiate(&local_arg_ty);
                    // Brick 4 (b): a syntactic hole in the GetElem proof slot
                    // is Lean's `(by get_elem_tactic)` — discharge it with
                    // the real tactic chain. Only when the obligation is
                    // ground (instance resolution pinned `valid`); otherwise
                    // fall through to the ordinary hole → metavariable path,
                    // whose leak is caught fail-closed by the kernel.
                    let getelem_hole_goal = if getelem_proof_slot == Some(idx)
                        && matches!(Self::unwrap_surface_parens(&arg.expr), SurfaceExpr::Hole(_))
                        && !self.has_metavars(&expected_arg_ty)
                    {
                        Some(expected_arg_ty.clone())
                    } else {
                        None
                    };
                    // An explicit `_` handed to an INSTANCE-IMPLICIT binder
                    // (`@default (∀ i, β i) _`, `@Inhabited.default α _`) is
                    // synthesized by typeclass resolution, as Lean does for a
                    // hole in that position; it used to become a plain
                    // metavariable nothing ever solved, so a `rfl` about
                    // `@default _ _` reached the kernel with the instance
                    // unassigned (`Pi.default_def`, `Pi.default_apply` in
                    // `Mathlib/Logic/Unique.lean`, measured 2026-09-11). A
                    // failed synthesis is Lean's "failed to synthesize" when
                    // the goal is ground, and a queued instance goal when it
                    // is not (`explicit_inst_hole_unsynthesized`).
                    let inst_hole = getelem_hole_goal.is_none()
                        && bi.info == BinderInfo::InstImplicit
                        && matches!(Self::unwrap_surface_parens(&arg.expr), SurfaceExpr::Hole(_));
                    let synthesized_inst = if inst_hole {
                        self.resolve_instance(&expected_arg_ty)
                    } else {
                        None
                    };
                    // Lean postpones a `by` block until the rest of the
                    // application has been elaborated (`SyntheticMVarKind.tactic`
                    // in `synthesizeSyntheticMVars`): the block's goal is the
                    // slot type, and running it while that type still carries
                    // metavariables hands the tactic a goal it cannot read
                    // (`Nonempty.elim ‹_› (congr_fun …)` — `‹_›`'s goal is
                    // `Nonempty ?α`, pinned only by the SECOND argument;
                    // `Mathlib/Logic/Function/Basic.lean`, measured
                    // 2026-09-11). Stand a metavariable in the slot now and run
                    // the block after the loop against the instantiated type.
                    // An `⟨…⟩` is postponed on a NARROWER condition than a
                    // `by` block: Lean's `tryPostponeIfNoneOrMVar` +
                    // `expectedType.getAppFn.isMVar`
                    // (`Lean/Elab/BuiltinNotation.lean:46,54`) ask whether the
                    // expected type's HEAD is a metavariable, not whether the
                    // type mentions one anywhere. `f ⟨a, b⟩` at a slot typed
                    // `?α × Nat` therefore keeps elaborating eagerly — its head
                    // is `Prod`, and the fields are what pin `?α`.
                    let defer_by_block = getelem_hole_goal.is_none()
                        && !inst_hole
                        && ((Self::deferrable_by_block(&arg.expr)
                            || Self::deferrable_leading_dot(&arg.expr)
                            || self.deferrable_subst(&arg.expr))
                            && self.has_metavars(&expected_arg_ty)
                            || Self::deferrable_anonymous_ctor(&arg.expr)
                                && self.expected_type_head_is_meta(&expected_arg_ty));
                    // G28: an un-annotated lambda whose slot type is still
                    // open. A retry of this application postpones it (like a
                    // `by` block); otherwise it is elaborated eagerly as ever,
                    // watched for field notation on a meta-typed receiver —
                    // Lean's `tryPostponeIfMVar` (`elab_app_postpone_lambda.rs`).
                    let lambda_in_open_slot = getelem_hole_goal.is_none()
                        && !inst_hole
                        && !defer_by_block
                        && Self::is_unascribed_lambda_arg(&arg.expr)
                        && self.has_metavars(&expected_arg_ty);
                    let defer_lambda = lambda_in_open_slot && deferred_lambda_args.contains(&idx);
                    let open_callback_premise = lambda_in_open_slot
                        && !defer_lambda
                        && idx + 1 < args.len()
                        && self.has_open_callback_premise(&expected_arg_ty);
                    let mut lambda_stuck_on_meta = false;
                    let arg_expr = match (
                        dot_receiver.as_ref().filter(|_| receiver_slot == Some(idx)),
                        getelem_hole_goal,
                        synthesized_inst,
                    ) {
                        (Some(receiver), _, _) => Ok(receiver.term.clone()),
                        (None, Some(goal), _) => self.discharge_getelem_valid_hole(&goal),
                        (None, None, Some(inst)) => Ok(inst),
                        (None, None, None) if inst_hole => {
                            self.explicit_inst_hole_unsynthesized(&expected_arg_ty)
                        }
                        (None, None, None) if defer_by_block || defer_lambda => {
                            let placeholder = self.fresh_meta(expected_arg_ty.clone());
                            deferred_by_blocks.push((
                                placeholder.clone(),
                                arg.expr.clone(),
                                expected_arg_ty.clone(),
                            ));
                            Ok(placeholder)
                        }
                        (None, None, None) if lambda_in_open_slot => {
                            let watch = self.begin_field_notation_watch();
                            let r = self.elaborate_arg_with_expected_type(
                                &arg.expr,
                                Some(expected_arg_ty.clone()),
                            );
                            lambda_stuck_on_meta = self.end_field_notation_watch(watch);
                            r
                        }
                        // Lean's `binop%` elaborates a compound leaf with no
                        // expected type and coerces it into the tree's type
                        // (`elab_binop_leaf.rs`); the slot's type would reach
                        // inside it otherwise.
                        (None, None, None)
                            if (hetero_binop_slots.as_ref().is_some_and(|s| s.homogeneous)
                                || Self::is_neg_head(func))
                                && (self.binop_leaf_forced_alone(&arg.expr)
                                    || self
                                        .binop_leaf_settles_alone(&arg.expr, &expected_arg_ty)) =>
                        {
                            self.elaborate_arg_with_expected_type(&arg.expr, None)
                        }
                        (None, None, None) => self.elaborate_arg_with_expected_type(
                            &arg.expr,
                            Some(expected_arg_ty.clone()),
                        ),
                    };
                    let arg_expr = match arg_expr {
                        Ok(e) => e,
                        Err(e) => {
                            self.metas.pop_scope();
                            // A nested application can have committed a more specific
                            // predicate than the callback's later evidence allows.
                            // Retry only a failed eager attempt, after rollback.
                            let conflicting_premise = open_callback_premise
                                && matches!(e, ElabError::TypeMismatch { .. });
                            if (lambda_stuck_on_meta || conflicting_premise)
                                && self.lambda_retry_allowed()
                            {
                                let mut defer = deferred_lambda_args.clone();
                                defer.push(idx);
                                return self.elab_app_retry_deferring_lambdas(func, args, defer, e);
                            }
                            // B104: the operand was elaborated AGAINST the
                            // pinned homogeneous slot type and mismatched
                            // inside its own elaboration (e.g. a nested binop
                            // whose result type is rigid). Same fallback as
                            // the unify site below: retry once unpinned.
                            if matches!(e, ElabError::TypeMismatch { .. })
                                && hetero_binop_slots.as_ref().is_some_and(|s| s.homogeneous)
                            {
                                return self.elab_app_binop_hetero_fallback(func, args);
                            }
                            return Err(e);
                        }
                    };

                    // Track if this is a Nat literal for potential coercion. Check
                    // the SURFACE arg too: a bare numeral often elaborates to
                    // `@OfNat.ofNat Nat n …` (not a raw `Lit(Nat)`), which
                    // `is_nat_literal` does not recognise — yet it is exactly the
                    // literal that can pin a shared carrier metavar to `Nat` and
                    // later need Int re-coercion.
                    if Self::is_nat_literal(&arg_expr)
                        || matches!(&arg.expr, SurfaceExpr::Lit(_, SurfaceLit::Nat(_)))
                    {
                        nat_literal_indices.push(idx);
                    }
                    elaborated_args.push(arg_expr.clone());

                    let arg_type = match self.infer_type(&arg_expr) {
                        Ok(t) => t,
                        Err(e) => {
                            self.metas.pop_scope();
                            return Err(e);
                        }
                    };
                    let arg_type = self.metas.instantiate(&arg_type);
                    // A slot that is still a BARE metavariable takes the
                    // argument's type AS WRITTEN, the way Lean's `?α =?= VM`
                    // assigns `VM`: whnf would unfold a `def` alias (`VM :=
                    // Nat → Option Nat`) into the assignment, and field
                    // notation on a later binder of that type (G28, `acc.set`)
                    // or instance search at `.instances` transparency (G47)
                    // could no longer see the alias.
                    let folded_assigned = self.assign_bare_slot_folded(&arg_type, &expected_arg_ty);
                    let arg_type = self.whnf(&arg_type);
                    let expected_arg_ty = self.whnf(&expected_arg_ty);

                    let unify_result = if folded_assigned {
                        UnifyResult::Success
                    } else {
                        let ctx = self.build_local_ctx();
                        let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                        unifier.unify(&arg_type, &expected_arg_ty)
                    };
                    let mut final_arg = match unify_result {
                        UnifyResult::Success => arg_expr.clone(),
                        // The unifier is structural and incomplete: it splits
                        // `Box1.mk v =?= f n` into `Box1.mk =?= f` and fails,
                        // where Lean's `ensureHasType` (isDefEq, lazy delta and
                        // structure eta) accepts. Once `propagate_expected_type`
                        // has pinned this slot, a def-eq the outer check used to
                        // settle is met here instead (`iVis_inj_k`, bisected to
                        // e03668c7d). As `enforce_expr_type` does, the
                        // elaborator's def-eq decides before coercion or
                        // refusal: the kernel's checker at elaboration
                        // transparency (`@[irreducible]` stays folded, B14),
                        // with universe METAVARIABLES solved through the level
                        // callback and a rigid `.{u}` never assigned
                        // (`make_tc`). Unlike Lean's isDefEq, the failed
                        // unifier attempt's partial assignments are not rolled
                        // back first; the def-eq is decided under them.
                        UnifyResult::Failure(_) if self.is_def_eq(&arg_type, &expected_arg_ty) => {
                            arg_expr.clone()
                        }
                        UnifyResult::Failure(msg) => {
                            // Try Nat → Real coercion if applicable
                            if let Some(coerced) =
                                self.try_coerce(&arg_expr, &arg_type, &expected_arg_ty)
                            {
                                coerced
                            } else {
                                // Special case for Real: an earlier Nat literal
                                // solved a shared carrier metavar to `Nat`, but
                                // this later argument is `Real`. As in the Int
                                // lane below, `local_arg_ty` may already be the
                                // concrete `Nat`: the first operand's solution
                                // was instantiated into the function type. The
                                // literal history and rigid Real argument are
                                // the discriminating evidence; requiring a
                                // surviving metavar here incorrectly disabled
                                // the retry for `LT.lt 0 x` with `x : Real`.
                                if self.is_nat_type(&expected_arg_ty)
                                    && self.is_real_type(&arg_type)
                                    && !nat_literal_indices.is_empty()
                                    && self
                                        .env
                                        .get_const(&Name::from_string("Real.ofNat"))
                                        .is_some()
                                {
                                    // Retry with Nat literals coerced to Real
                                    self.metas.pop_scope();
                                    return self.elab_app_with_real_coercion(func, args);
                                }
                                // Symmetric case for Int: an earlier Nat literal
                                // (e.g. operand-0 of `0 ≤ a`) solved a shared type
                                // metavar to `Nat`, but this later argument is
                                // `Int`. Retry with the literals coerced via
                                // `Int.ofNat`. NB: unlike the Real path we do NOT
                                // require `has_metavars(local_arg_ty)`. For a
                                // homogeneous binop (`LE.le`/`Eq : α → α → …`)
                                // operand-0's literal solves `?α := Nat`, which is
                                // instantiated INTO the function type, so this
                                // operand's `local_arg_ty` is already concrete `Nat`
                                // (no metavar) — exactly the case to recover.
                                if self.is_nat_type(&expected_arg_ty)
                                    && self.is_int_type(&arg_type)
                                    && !nat_literal_indices.is_empty()
                                    && self
                                        .env
                                        .get_const(&Name::from_string("Int.ofNat"))
                                        .is_some()
                                {
                                    self.metas.pop_scope();
                                    return self.elab_app_with_int_coercion(func, args);
                                }
                                // B104: binop% heterogeneous fallback. The
                                // homogeneous pin collapsed `?β`/`?γ` onto an
                                // earlier carrier and THIS operand's type is
                                // rigidly different — the shape of a genuinely
                                // heterogeneous user instance (`HAdd Sec Min
                                // Sec`). Lean's binop% TRIES homogeneous first
                                // and falls back to genuine heterogeneous
                                // elaboration on failure. Retry the whole
                                // application ONCE with slot pinning
                                // suppressed (one-shot flag, consumed at
                                // `elab_app_inner` entry, so nested binops
                                // still homogenize). The pushed scope is
                                // popped first, so the failed attempt leaves
                                // no meta assignments. Only fires where
                                // elaboration already FAILED — successful
                                // homogeneous paths are byte-identical.
                                if hetero_binop_slots.as_ref().is_some_and(|s| s.homogeneous) {
                                    self.metas.pop_scope();
                                    return self.elab_app_binop_hetero_fallback(func, args);
                                }
                                // Pop scope before returning error
                                self.metas.pop_scope();
                                return Err(ElabError::TypeMismatch {
                                    expected: format!("{expected_arg_ty}"),
                                    actual: msg,
                                });
                            }
                        }
                        UnifyResult::Stuck => {
                            // An eager lambda's hypothesis can have a type headed by
                            // an unsolved predicate. A later argument of its enclosing
                            // application may still determine that predicate.
                            self.note_unassigned_expected_type(&arg_type);
                            self.note_unassigned_expected_type(&expected_arg_ty);
                            // Pop scope before returning error
                            self.metas.pop_scope();
                            return Err(ElabError::CannotInfer);
                        }
                    };

                    // After the FIRST operand of a recognised *homogeneous*
                    // hetero binop pins its concrete type, collapse the still-open
                    // `?β` and `?γ` slots onto it so the SECOND operand elaborates
                    // against the right expected type instead of an unconstrained
                    // metavar that would default to `Nat`. This is what makes
                    // `val % (2 ^ width)` work when the body is first elaborated
                    // without an expected type: `val : Int` pins the carrier.
                    // Power / shift ops are excluded — their first operand (the
                    // base) is often a bare literal that defaults to `Nat`, so the
                    // expected-result-type pass above is the only safe driver.
                    if idx == 0 {
                        if let Some(slots) = &hetero_binop_slots {
                            if slots.homogeneous {
                                let targets = [&slots.beta, &slots.gamma];
                                self.pin_open_type_slots(&targets, &arg_type);
                            }
                        }
                    }

                    // Symmetric back-collapse after the SECOND operand: when the
                    // FIRST operand was a value-less polymorphic literal (`[]`,
                    // whose element-type metavar stayed open) and the SECOND operand
                    // (`xs : List Nat`) carries the only concrete carrier, pin the
                    // still-open `?α`/`?γ` slots onto operand-1's type. `?α` was
                    // unified with operand-0's `List ?α'`, so pinning `?α := List Nat`
                    // retroactively solves the literal's `?α' := Nat`. This covers the
                    // `[] ++ xs` direction (carrier on the right); the idx==0 step
                    // above covers `xs ++ []` (carrier on the left). Only the
                    // homogeneous arm fires, and `pin_open_type_slots` only assigns
                    // open slots from a metavar-free carrier, so this is a no-op when
                    // operand-0 already pinned the slots.
                    if idx == 1 {
                        if let Some(slots) = &hetero_binop_slots {
                            if slots.homogeneous {
                                let targets = [&slots.alpha, &slots.gamma];
                                self.pin_open_type_slots(&targets, &arg_type);
                            }
                        }
                    }

                    let next_body = match current_type.kind() {
                        ExprKind::Pi(_, _, body) => Some(body.as_ref().clone()),
                        _ => None,
                    };

                    if let Some(body) = &next_body {
                        let next_type =
                            self.whnf(&self.metas.instantiate(&body.instantiate(&final_arg)));
                        let expected_is_sort =
                            matches!(self.whnf(&expected_arg_ty).kind(), ExprKind::Sort(_));
                        if expected_is_sort
                            && matches!(next_type.kind(), ExprKind::Pi(bi, _, _) if bi.info == BinderInfo::InstImplicit)
                        {
                            // INSTANCE transparency, not default.
                            //
                            // This normalisation exists so a Sort-valued
                            // argument feeding an instance-implicit parameter is
                            // in a form instance search can match — correct for
                            // `@[reducible]` aliases. At DEFAULT transparency it
                            // also flattens wrapper `def`s: `def M := Nat` became
                            // `Nat` here, so the goal `Sz M` was already `Sz Nat`
                            // before resolution ran, two distinct wrappers
                            // collapsed onto one instance, and the LAST-registered
                            // one won. Measured: `Sz.size M = 1` selected the
                            // `Sz F` instance and evaluated to 2.
                            //
                            // Reducing at instance transparency keeps
                            // `@[reducible]` aliases transparent while leaving a
                            // plain `def` folded, which is what Lean does and
                            // what Mathlib's OrderDual/Multiplicative idiom
                            // depends on.
                            final_arg = self.whnf_instances(&self.metas.instantiate(&final_arg));
                        }
                    }

                    // Update the type for the next iteration before consuming final_arg
                    // Need to get fresh body_ty since we may have consumed it
                    current_type = if let Some(body) = next_body {
                        self.metas.instantiate(&body.instantiate(&final_arg))
                    } else {
                        current_type.clone() // Already not a Pi, just keep it
                    };

                    // Build the application (consuming final_arg)
                    result = apply_arg(result, final_arg);

                    // Lean's default-instance pass, in argument order: a
                    // heterogeneous-operator goal postponed inside an EARLIER
                    // argument (`(· + ·)`, whose binder types were open when
                    // its body elaborated) is retried now that THIS argument
                    // may have grounded the carrier —
                    // `List.foldl (· + ·) 0 [1, 2, 3]` grounds it at the `0`,
                    // before the list literal is reached. One `is_empty` test
                    // whenever nothing was postponed, which is every
                    // application that does not pass an unannotated arithmetic
                    // function.
                    self.retry_postponed_open_carrier_instances();

                    // A named-slot prefix is already positioned, including
                    // holes for omitted implicit slots. Its remaining suffix is
                    // ordinary positional application and inserts implicits.
                    let remaining_user_args = remaining_args.len() - idx - 1;
                    if idx + 1 >= positioned_prefix {
                        let (new_result, new_type) = self.insert_implicit_args(
                            result,
                            &current_type,
                            ArgsFollow::from_remaining(remaining_user_args),
                        );
                        result = new_result;
                        current_type = new_type;
                    }
                } else {
                    // Function type is exhausted (not a Pi) but arguments remain.
                    // Return an error instead of silently applying (#1720).
                    //
                    // `over_applied_head_error` NAMES the head when auto-implicit
                    // swallowed it in a signature position (the third mask,
                    // frontier recon §2.6); every other head keeps the untouched
                    // `TooManyArguments` message. Same failure, same span, same
                    // verdict either way.
                    self.metas.pop_scope();
                    let err = self.over_applied_head_error(
                        &result,
                        &current_type,
                        remaining_args.len() - idx,
                    );
                    return Err(err);
                }
            }

            // Default-argument (`optParam`) insertion at the end of the
            // application: once the user's positional arguments are consumed,
            // every leading explicit `optParam α default` binder receives its
            // default, and the implicit binders between such defaults are
            // filled as after any argument. This is Lean's
            // `processExplicitArg` with no argument left (`Lean/Elab/App.lean`):
            // `match (← read).explicit, argType.getOptParamDefault?, …` takes
            // the default arm whenever `explicit` is false, WITH OR WITHOUT an
            // expected type. It keys off the raw `optParam` parameter type, so it
            // fires for imported declarations with no clean-side metadata.
            //
            // Until 2026-10-07 the default was supplied only when an expected
            // type was present and the defaulted type unified with it. Both
            // halves diverged from Lean, measured on the pinned v4.30.0-rc2
            // binary: with no expected type, `ext.getState env |>.field` saw a
            // receiver typed `optParam … → S` instead of `S` and refused the
            // field (upstream tests/elab/2077.lean); and against an expected
            // function type the partial application was ACCEPTED where Lean
            // fills the default and reports the mismatch (`def h : Nat → Nat :=
            // addTwo 1` is a type error in Lean).
            //
            // `@f a` supplies NO default: Lean takes the default arm only at
            // `explicit = false`, and the pinned binary prints `@withOpt 1 :
            // optParam Nat 5 → Nat` and refuses `def t : Nat := @withOpt 1`.
            // The `autoParam` twin is the same arm.
            if !self.explicit_mode {
                loop {
                    let current_type_now = self.whnf(&self.metas.instantiate(&current_type));
                    let leads_with_opt_param = matches!(
                        current_type_now.kind(),
                        ExprKind::Pi(bi, arg_ty, _)
                            if !Self::is_implicit_binder(*bi)
                                && Self::opt_param_default(&self.metas.instantiate(arg_ty)).is_some()
                    );
                    if !leads_with_opt_param {
                        break;
                    }
                    let (defaulted, defaulted_ty) =
                        self.insert_opt_param_defaults(result, &current_type_now);
                    let (filled, filled_ty) =
                        self.insert_implicit_args(defaulted, &defaulted_ty, ArgsFollow::No);
                    result = filled;
                    current_type = filled_ty;
                }
            }

            // Resolve any leading instance-implicit binders that were deferred
            // above. By now the explicit arguments have pinned the carrier
            // metavariables (e.g. `?α := UInt8` from the `a b : α` operands of
            // `LE.le`), so each `[inst : C ?α]` goal is ground and resolves to the
            // correct registered instance (`instLEUInt8`, not `instLENat`). If a
            // goal is still unresolvable (carrier never pinned), fall back to
            // eager resolution so behavior is never worse than before.
            if !leading_pending.is_empty() && !self.resolve_deferred_instances(&leading_pending) {
                for (meta_arg, goal_ty) in &leading_pending {
                    let goal_ty = self.whnf(&self.metas.instantiate(goal_ty));
                    let resolved = self.resolve_instance(&goal_ty);
                    // POSTPONED rather than absent: a heterogeneous-operator
                    // goal with every type argument still open. Record it so
                    // the enclosing application retries it once a sibling
                    // argument grounds the carrier. The goal still carries
                    // metavariables, so the loud GROUND-goal exit below does
                    // not fire and the pre-existing leak-then-fail-closed path
                    // is what catches it if nothing ever grounds it.
                    if resolved.is_none() {
                        if self.instance_search_stuck {
                            // Lean's stuck verdict: the surrounding term may
                            // still ground the carrier (`Lean/Elab/App.lean`
                            // synthesizes AFTER the expected-type unification).
                            self.record_postponed_stuck_instance(meta_arg, &goal_ty);
                        }
                        self.record_postponed_open_carrier_instance(meta_arg, &goal_ty);
                    }
                    if let (Some(resolved), ExprKind::FVar(fvar)) = (&resolved, meta_arg.kind()) {
                        if let Some(meta_id) = MetaState::from_fvar(*fvar) {
                            let _ = self.metas.assign(meta_id, resolved.clone());
                        }
                    }
                    // GROUND goal with no instance: fail LOUDLY (B06). The goal
                    // has no metavariables left, so no later unification can
                    // make it synthesizable — before this check the unassigned
                    // instance metavariable leaked into the declaration and
                    // surfaced as the kernel's opaque "Declaration contains
                    // free variables" rejection (sweep row
                    // classes_instances/p17). Lean: "failed to synthesize".
                    //
                    // A heterogeneous-operator goal whose INPUTS are ground and
                    // whose only open slot is the `outParam` result is ground
                    // for this purpose too (`hetero_binop_goal_is_determined`):
                    // leaving it postponed is what let `(3 : Fin 4) + 1`, read
                    // at `HAdd (Fin 4) Nat ?γ` by the B104 retry, have `?γ`
                    // solved to `Nat` by a sibling numeral and the `Fin` leaf
                    // coerced — accepting `(if True then (3 : Fin 4) + 1 else
                    // 0) ≠ 0`, which is false in Lean.
                    //
                    // Goals that still carry metavariables in an input keep the
                    // legacy leak-then-fail-closed path: an enclosing
                    // elaboration context may yet pin them and assign the meta.
                    if resolved.is_none()
                        && (!self.has_metavars(&goal_ty)
                            || (!self.instance_search_stuck
                                && self.hetero_binop_goal_is_determined(&goal_ty)))
                    {
                        let still_unassigned = matches!(
                            self.metas.instantiate(meta_arg).kind(),
                            ExprKind::FVar(fvar) if MetaState::from_fvar(*fvar).is_some()
                        );
                        if still_unassigned {
                            // Restore the metavariable scope pushed before the
                            // argument loop, exactly like the loop's other
                            // error exits.
                            self.metas.pop_scope();
                            // B104: the homogeneous pin can make the instance
                            // goal itself unsatisfiable (`HAdd Sec Sec Sec`
                            // when the user registered `HAdd Sec Sec Min`).
                            // Retry once unpinned so the goal keeps its open
                            // result slot and unifies against the genuinely
                            // heterogeneous registered instance.
                            if hetero_binop_slots.as_ref().is_some_and(|s| s.homogeneous) {
                                return self.elab_app_binop_hetero_fallback(func, args);
                            }
                            // A determined operator goal still has its open
                            // `outParam`: name it `?N`, not by its raw fvar id.
                            let goal = if self.has_metavars(&goal_ty) {
                                self.render_instance_goal(&goal_ty)
                            } else {
                                format!("{goal_ty}")
                            };
                            return Err(ElabError::FailedToSynthesizeInstance {
                                goal,
                                detail: self.instance_failure_detail(&goal_ty),
                            });
                        }
                    }
                }
            }

            // Impose the expected RESULT type before resuming anything that
            // was postponed, which is where Lean does it: a postponed
            // elaborator is resumed in `synthesizeSyntheticMVars`, run after
            // the enclosing term's `ensureHasType`, so by then the application
            // type and the expected type have met. `propagate_expected_type`
            // cannot stand in for it — it declines whenever the result type
            // mentions an explicit argument (`body.has_loose_bvars()`), which
            // is exactly `mydif_pos : {c} -> c -> (t e : Nat) -> MyDite c t e =
            // t`, the `Function.sometimes_eq` shape. Without this the drain
            // re-runs `⟨a⟩` against the same open `?c` and reports the very
            // error the deferral exists to avoid.
            //
            // SPECULATIVE and scoped: on failure nothing is assigned and the
            // behaviour is exactly what it was, so this can only turn an error
            // into a success. Gated on there being something deferred, so an
            // application that postponed nothing is untouched.
            if !deferred_by_blocks.is_empty() {
                if let Some(expected) = self.current_expected_type.clone() {
                    let actual = self.metas.instantiate(&current_type);
                    let expected = self.metas.instantiate(&expected);
                    self.metas.push_scope();
                    if self.try_unify(&actual, &expected) {
                        self.metas.commit();
                    } else {
                        self.metas.pop_scope();
                    }
                }
            }

            // Run the `by` blocks deferred in the loop, each against its slot
            // type as the other arguments (and the expected result type) have
            // now pinned it. A block whose slot is STILL open runs against the
            // open metavariable and fails loudly inside the tactic, exactly as
            // it did before the deferral — never a silently-wrong term.
            for (placeholder, block, slot_ty) in deferred_by_blocks {
                let goal_ty = self.metas.instantiate(&slot_ty);
                let proof =
                    match self.elaborate_arg_with_expected_type(&block, Some(goal_ty.clone())) {
                        Ok(p) => p,
                        Err(e) => {
                            self.metas.pop_scope();
                            return Err(e);
                        }
                    };
                // A `by` block's tactic guarantees its goal type; a postponed
                // lambda (G28) elaborated against the slot does not — its
                // body's type is whatever it is. Unify it with the slot, as
                // the eager path does, so an ill-typed argument is refused
                // HERE ("type mismatch", as Lean says) rather than reaching
                // the kernel.
                if Self::is_unascribed_lambda_arg(&block) || self.deferrable_subst(&block) {
                    let lam_ty = match self.infer_type(&proof) {
                        Ok(t) => self.metas.instantiate(&t),
                        Err(e) => {
                            self.metas.pop_scope();
                            return Err(e);
                        }
                    };
                    let slot = self.metas.instantiate(&goal_ty);
                    if !self.try_unify(&lam_ty, &slot) {
                        self.metas.pop_scope();
                        return Err(ElabError::TypeMismatch {
                            expected: format!("{slot}"),
                            actual: format!("{lam_ty}"),
                        });
                    }
                }
                let assigned = match placeholder.kind() {
                    ExprKind::FVar(fvar) => MetaState::from_fvar(*fvar)
                        .is_some_and(|meta_id| self.metas.assign(meta_id, proof.clone())),
                    _ => false,
                };
                // The placeholder may already have been solved by a later
                // unification (e.g. against a sibling argument); the block's
                // proof must then agree with that solution.
                if !assigned {
                    let current = self.metas.instantiate(&placeholder);
                    if !self.try_unify(&current, &proof) {
                        self.metas.pop_scope();
                        return Err(ElabError::TypeMismatch {
                            expected: format!("{current}"),
                            actual: format!("{proof}"),
                        });
                    }
                }
            }
            // Last chance for a postponed heterogeneous-operator goal:
            // every argument of this application has been elaborated, so
            // anything they were going to ground is grounded.
            self.retry_postponed_open_carrier_instances();

            // Commit scope - elaboration succeeded
            self.metas.commit();
            let result = self.metas.instantiate(&result);
            // Solve any still-abstract universe-level *parameters* on the head
            // constant from its now-concrete type arguments (#existsi-class).
            self.solve_head_const_levels(&result);
            Ok(self.metas.instantiate_levels(&result))
        } else {
            // Fallback: simple elaboration without implicit insertion
            let mut result = func_expr;
            for arg in args {
                let arg_expr = self.elaborate(&arg.expr)?;
                result = apply_arg(result, arg_expr);
            }
            let result = self.metas.instantiate(&result);
            Ok(self.metas.instantiate_levels(&result))
        }
    }
}
