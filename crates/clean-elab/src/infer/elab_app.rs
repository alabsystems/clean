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
/// Type-parameter metavar slots of a desugared heterogeneous arithmetic binop
/// `@HOp.hOp ?α ?β ?γ ?inst`. See `hetero_binop_homogenize_slots`.
struct HeteroBinopSlots {
    alpha: Expr,
    beta: Expr,
    gamma: Expr,
    /// True for ops whose `β` collapses onto `α` (`% + - * /` + bitwise);
    /// false for power / shift (independent exponent / shift-amount type).
    homogeneous: bool,
}

impl<'a> ElabCtx<'a> {
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
        if args.len() != 2 || args.iter().any(|a| a.name.is_some()) {
            return Ok(None);
        }
        let SurfaceExpr::Ident(_, head) = Self::unwrap_surface_parens(func) else {
            return Ok(None);
        };
        let head = head.as_str();
        if head != "Eq" && head != "Ne" {
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
        match self.env.get_const(&Name::from_string(head)) {
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
            Expr::const_(Name::from_string(head), vec![sort_level]),
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
        if name != "Not" {
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
        if !is_bool {
            self.metas.pop_scope();
            return Ok(None);
        }
        self.metas.commit();
        Ok(Some(Expr::app(
            Expr::const_(Name::from_string("Bool.not"), vec![]),
            operand,
        )))
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
    fn resolve_leading_dot_inductive_by_suffix(&self, suffix: &str) -> Option<Name> {
        let mut found: Option<Name> = None;
        for ind in self.env.inductives() {
            let owns = ind
                .constructor_names
                .iter()
                .any(|ctor| ctor.last_component().as_deref() == Some(suffix));
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
        name: &str,
        expected_ty: &Expr,
    ) -> Result<Expr, ElabError> {
        let Some(ctor_suffix) = name.strip_prefix('.') else {
            return Err(ElabError::UnknownIdent(name.to_string()));
        };

        let expected_ty = self.metas.instantiate(expected_ty);
        let expected_ty = self.metas.instantiate_levels(&expected_ty);
        let expected_whnf = self.whnf(&expected_ty);

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
                .resolve_leading_dot_inductive_by_suffix(ctor_suffix)
                .ok_or_else(|| ElabError::UnknownIdent(name.to_string()))?,
        };

        // Resolve the constructor name and its type info.
        let (ctor_name, ctor_levels) = if let Some(ind) = self.env.get_inductive(&ind_name) {
            // Registered inductive (e.g., Option, List, Bool, Nat, user-defined, etc.)
            let ctor = ind
                .constructor_names
                .iter()
                .find(|ctor| ctor.last_component().as_deref() == Some(ctor_suffix))
                .cloned()
                .ok_or_else(|| ElabError::UnknownIdent(name.to_string()))?;
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
            // Fallback: type is not a registered inductive (e.g., Except is declared
            // as an axiom with its constructors as separate axiom constants). Look up
            // `TypeName.ctor_suffix` directly as a constant in the environment.
            let ctor = Name::append(&ind_name, ctor_suffix);
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
        // 1. Get expected type from context
        let expected_ty = self
            .current_expected_type
            .clone()
            .ok_or(ElabError::AnonymousCtorNoExpectedType)?;

        // 2. Reduce to WHNF and extract head constant
        let expected_whnf = self.whnf(&expected_ty);
        let _type_args: Vec<Expr> = expected_whnf.get_app_args().into_iter().cloned().collect();

        let struct_name = match expected_whnf.get_app_fn().kind() {
            ExprKind::Const(name, _) => name.clone(),
            other => {
                return Err(ElabError::AnonymousCtorNotInductive(format!("{other:?}")));
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
                        actual: format!("{result_ty:?}"),
                    })
                }
            };
            result = Expr::app(result, arg.clone());
            result_ty = self.metas.instantiate(&body_ty);
        }

        let (mut result, mut result_ty) = self.insert_implicit_args(result, &result_ty);

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
                Box::new(SurfaceExpr::Ident(group_span, "anonymousCtor".to_string())),
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
        // Setting expected type for each arg allows unification to solve metavariables
        // for implicit type parameters (e.g., α := Nat when elaborating 42 in ⟨42, true⟩)
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
        if !self.try_unify(&result_ty, &expected_ty) {
            return Err(ElabError::TypeMismatch {
                expected: format!("{expected_ty:?}"),
                actual: format!("{result_ty:?}"),
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
                    Box::new(SurfaceExpr::Ident(span, "anonymousCtor".to_string())),
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
    pub(in crate::infer) fn insert_implicit_args(
        &mut self,
        func: Expr,
        func_type: &Expr,
    ) -> (Expr, Expr) {
        // In explicit mode, don't insert implicit arguments (#1231)
        if self.explicit_mode {
            return (func, func_type.clone());
        }

        let mut result = func;
        let mut ty = self.whnf(func_type);

        loop {
            match ty.kind() {
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
                            // Fall back to metavariable if no instance found
                            self.fresh_meta(arg_ty_inst)
                        }
                    } else {
                        // For regular implicit/strict implicit, use metavariable
                        self.fresh_meta(arg_ty_inst)
                    };

                    result = Expr::app(result, arg.clone());
                    // Instantiate the body type with the argument
                    ty = self.whnf(&self.metas.instantiate(&body_ty.instantiate(&arg)));
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
    pub(in crate::infer) fn insert_implicit_args_deferring_instances(
        &mut self,
        func: Expr,
        func_type: &Expr,
    ) -> (Expr, Expr, Vec<(Expr, Expr)>) {
        if self.explicit_mode {
            return (func, func_type.clone(), Vec::new());
        }

        let mut result = func;
        let mut ty = self.whnf(func_type);
        let mut pending = Vec::new();

        loop {
            match ty.kind() {
                ExprKind::Pi(bi, arg_ty, body_ty) if Self::is_implicit_binder(*bi) => {
                    let arg_ty_inst = self.metas.instantiate(arg_ty);

                    let arg = self.fresh_meta(arg_ty_inst.clone());
                    if bi.info == BinderInfo::InstImplicit {
                        pending.push((arg.clone(), arg_ty_inst));
                    }

                    result = Expr::app(result, arg.clone());
                    ty = self.whnf(&self.metas.instantiate(&body_ty.instantiate(&arg)));
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
            SurfaceExpr::Ident(_, name) => name.as_str(),
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
        })
    }

    /// Unify the given still-open type-param slots with a concrete carrier
    /// `carrier`. Only *assigns* open metavariable slots — it never reshapes a
    /// type the operands already pinned, and the kernel re-checks the
    /// instantiated term, so this cannot weaken the kernel check. A rigid
    /// mismatch (a deliberately heterogeneous user instance) fails the
    /// speculative unify harmlessly and leaves the slot untouched.
    fn pin_hetero_binop_slots(&mut self, slots: &[&Expr], carrier: &Expr) {
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
        self.pin_hetero_binop_slots(&targets, &expected);
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
            SurfaceExpr::Ident(_, n) => n.starts_with('.') || n == "List.nil",
            SurfaceExpr::App(_, head, app_args) => {
                let mut h = head.as_ref();
                while let SurfaceExpr::Paren(_, inner) = h {
                    h = inner;
                }
                match h {
                    SurfaceExpr::Ident(_, n) if n.starts_with('.') => true,
                    // Recurse into a tuple spine: `Prod.mk a b` — if any
                    // component itself needs the result type pinned, so does the
                    // enclosing application.
                    SurfaceExpr::Ident(_, n) if n == "Prod.mk" => app_args
                        .iter()
                        .any(|a| Self::arg_needs_result_type_pinned(&a.expr)),
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
    fn is_hetero_binop_head(func: &SurfaceExpr) -> bool {
        matches!(
            Self::unwrap_surface_parens(func),
            SurfaceExpr::Ident(_, name) if matches!(
                name.as_str(),
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
            SurfaceExpr::Ident(_, n) => !n.starts_with('.') && n != "List.nil",
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
                    n.as_str(),
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
    fn expected_is_unassigned_meta(&self) -> bool {
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
                    let name = Name::from_string(n);
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
                    let name = Name::from_string(&format!("{ns}.{field}"));
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
        self.elab_app_inner(func, args)
    }

    /// Eliminator-style elaboration (`elabAsElim`) for a recursor applied with
    /// its `{motive}` left IMPLICIT: `Nat.rec 0 (fun _ ih => ih + 1) n`, or the
    /// `.recOn` form `Nat.recOn n 0 (fun _ ih => ih + 1)` (which applies the
    /// major FIRST). The generic path inserts a metavariable for the motive, then
    /// checks the first minor (`0`) against `?motive Nat.zero` — a higher-order
    /// constraint the unifier cannot solve, so it fails. Lean's `elabAsElim`
    /// instead synthesizes the motive from the expected type.
    ///
    /// This is the tractable slice: a NON-DEPENDENT motive for a recursor with
    /// **no indices and one motive** — `Nat.rec`, `Bool.rec`, a user enum's
    /// `.rec`, and PARAMETRIC types (`List.rec`, `Option.rec`, a user `Pair α`;
    /// the inductive parameters precede the motive and are recovered from the
    /// major's type). With expected result type `C` and major premise of type
    /// `T`, the motive is `fun (_ : T) => C`; the recursor is then applied to the
    /// parameters, the motive, and the user's minors + major exactly as a written
    /// `@T.rec params… (fun _ => C) …`.
    ///
    /// Returns `None` (falls through to the generic path) whenever the shape is
    /// outside this slice: explicit mode, a non-recursor head, an indexed or
    /// mutual recursor, a supplied motive (arg count ≠ minors+major),
    /// named args, or no expected type. SOUNDNESS: the emitted term is an
    /// ordinary `@T.rec …` application, kernel-re-checked on registration — a
    /// wrong motive makes the minors mismatch and fails LOUD; it can never
    /// fabricate an ill-typed term.
    fn try_elab_recursor_as_elim(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Option<Expr>, ElabError> {
        if self.explicit_mode {
            return Ok(None);
        }
        let Some(full_name) = Self::func_qualified_name(func) else {
            return Ok(None);
        };
        // Accept both `<T>.rec` (motive · minors · major) and `<T>.recOn`
        // (motive · MAJOR · minors — the major is applied FIRST). The
        // `RecursorVal` lives under `.rec`; `recOn` reuses the same
        // universe/parameter/minor structure, only reordering the major.
        let (recursor_name, is_recon) = if let Some(base) = full_name.strip_suffix(".recOn") {
            (format!("{base}.rec"), true)
        } else if full_name.ends_with(".rec") {
            (full_name.clone(), false)
        } else {
            return Ok(None);
        };
        let recursor_name = Name::from_string(&recursor_name);
        let Some(rec_val) = self.env.get_recursor(&recursor_name).cloned() else {
            return Ok(None);
        };
        // The constant actually applied (`.rec` or `.recOn`).
        let applied_name = Name::from_string(&full_name);
        // Slice: no indices, exactly one motive (parameters ARE allowed —
        // `List.rec`, `Option.rec`, a user `Pair α` — they precede the motive
        // and are recovered from the major's type by `apply_eliminator_params`).
        if rec_val.num_indices != 0 || rec_val.num_motives != 1 {
            return Ok(None);
        }
        // The motive is UNSUPPLIED iff the args are exactly the minors + major.
        let expected_arg_count = rec_val.num_minors as usize + 1;
        if args.len() != expected_arg_count || args.iter().any(|a| a.name.is_some()) {
            return Ok(None);
        }
        let Some(expected) = self.current_expected_type.clone() else {
            return Ok(None);
        };
        let expected = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&expected));

        // The major premise gives the motive's domain `T`. It is the LAST arg
        // for `.rec`, the FIRST arg for `.recOn`.
        let major_idx = if is_recon { 0 } else { args.len() - 1 };
        let major_expr = self.elaborate(&args[major_idx].expr)?;
        let t = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&self.infer_type(&major_expr)?));
        // Guard: `T`'s head must be this recursor's inductive (a mis-typed major
        // should defer to the generic path's loud error, not this reroute).
        let t_whnf = self.whnf(&t);
        match t_whnf.get_app_fn().kind() {
            ExprKind::Const(n, _) if *n == rec_val.inductive_name => {}
            _ => return Ok(None),
        }

        // Motive := `fun (x : T) => C[major := x]`. When the major premise is a
        // local variable (fvar) that the expected type `C` mentions, abstract it
        // so the motive is DEPENDENT — `0 + n = n` inducts with motive
        // `fun k => 0 + k = k`, which the constant `fun _ => C` cannot express
        // (`0 + n` is not def-eq `n` for a variable `n`, so the base minor fails).
        // When `C` does not mention the major, `abstract_fvar` leaves it
        // unchanged, giving the non-dependent `fun _ => C`. A non-fvar major
        // (`Nat.rec … (f x)`) cannot be cleanly abstracted here, so it stays
        // non-dependent (and defers loudly if `C` actually depends on it). `T` is
        // the FULLY-APPLIED major type, so the motive domain is correct for a
        // parametric recursor.
        let motive_body = match major_expr.kind() {
            ExprKind::FVar(id) => expected.abstract_fvar(*id),
            _ => expected.clone(),
        };
        let motive = Expr::lam(BinderInfo::Default, t_whnf.clone(), motive_body);
        let levels = self.eliminator_levels(&recursor_name, &t_whnf, &expected)?;
        let type_name = rec_val.inductive_name.to_string();
        // `@Rec.{levels} params… motive` — the inductive parameters (recovered
        // from the major's type `T`) precede the motive.
        let mut head = Expr::const_(applied_name, levels);
        head = self.apply_eliminator_params(head, &t_whnf, &type_name)?;
        head = Expr::app(head, motive);

        // Apply the user's minors + major against the recursor's Pi telescope,
        // elaborating each against its expected (motive-instantiated) domain.
        let mut result = head;
        let mut result_ty = self.whnf(&self.infer_type(&result)?);
        for (i, arg) in args.iter().enumerate() {
            let ExprKind::Pi(_, dom, cod) = result_ty.kind() else {
                // Telescope shorter than the arg list — not our shape.
                return Ok(None);
            };
            let dom = self.metas.instantiate(dom);
            let cod = cod.clone();
            let is_major = i == major_idx;
            let arg_expr = if is_major {
                major_expr.clone()
            } else {
                self.elaborate_arg_with_expected_type(&arg.expr, Some(dom.clone()))?
            };
            self.enforce_expr_type(&arg_expr, &dom)?;
            let arg_expr = self.metas.instantiate(&arg_expr);
            result_ty = self.whnf(&self.metas.instantiate(&cod.instantiate(&arg_expr)));
            result = Expr::app(result, arg_expr);
        }
        Ok(Some(result))
    }

    fn elab_app_inner(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Expr, ElabError> {
        // B104: consume the one-shot heterogeneous-fallback flag FIRST, before
        // any nested elaboration can observe it — only THIS application (the
        // retried binop) skips homogeneous slot pinning; operands and other
        // sub-elaborations behave exactly as on the first attempt.
        let suppress_binop_homogenize = std::mem::take(&mut self.suppress_binop_homogenize);
        // Anonymous ctor `⟨val⟩` (#172) + `pure x` in do-block (#3435).
        if matches!(func, SurfaceExpr::Ident(_, n) if n == "anonymousCtor") {
            return self.elab_anonymous_ctor(args);
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
                if n == "ite" && args.len() == 3 && args.iter().all(|a| a.name.is_none()) {
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
                if n == "Eq.rec" && args.len() == 2 && args.iter().all(|a| a.name.is_none()) {
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
        // Check for recursive call that should be replaced with IH (#381)
        // If we're calling the recursive function with a pattern variable that has an IH,
        // replace the call with the corresponding IH.
        if let Some(ref ctx) = self.recursive_def_ctx.clone() {
            // Unwrap parentheses to get the actual function name
            let func_name = Self::unwrap_surface_parens(func);

            // Check if this is a recursive call - handles both:
            // - Simple idents: `add p m` (func_name = "add")
            // - Qualified names: `Nat.add p m` (func_name = Proj("Nat", "add") => "Nat.add")
            // Fix for #522: qualified recursive calls like Nat.add should be recognized
            let is_recursive_call = match func_name {
                SurfaceExpr::Ident(_, name) => {
                    // A self-call spelled with the full qualified path or a
                    // namespace-relative dotted prefix is matched by
                    // `matches_call_name`. A *bare* free-function application head
                    // (a dot-free Ident, e.g. `maskBitsAux rest …` inside
                    // `namespace TrustIr.VectorDialect` defining
                    // `…VectorDialect.maskBitsAux`) is the standard in-namespace
                    // self-reference: it has no method receiver to qualify it, so
                    // recognize it by matching the bare name against the enclosing
                    // def's SHORT name. Scoped to dot-free Idents so a genuinely
                    // qualified call to a different function is unaffected, and the
                    // IH only actually substitutes when the decreasing argument is
                    // a bound recursive pattern var (`ih_map`), keeping the rewrite
                    // conservative.
                    ctx.matches_call_name(name) || (!name.contains('.') && name == ctx.short_name())
                }
                SurfaceExpr::Proj(_, base, proj) => {
                    // Try to collect qualified name like "Nat.add" from Proj("Nat", "add"),
                    // tolerating an enclosing-namespace prefix (Track R).
                    Self::try_collect_qualified_name(base, proj)
                        .is_some_and(|qname| ctx.matches_call_name(&qname))
                }
                _ => false,
            };

            // B01: this fast path consumes `args` positionally; a named arg
            // must instead flow to the standard path where it binds by binder
            // name (or fails loudly) — never silently by position.
            if is_recursive_call && !args.is_empty() && args.iter().all(|a| a.name.is_none()) {
                // Check if the argument at the decreasing position is a pattern var with IH
                if let Some(dec_arg) = args.get(ctx.decreasing_arg_pos) {
                    let arg_inner = Self::unwrap_surface_parens(&dec_arg.expr);
                    if let SurfaceExpr::Ident(_, arg_name) = arg_inner {
                        if let Some(&ih_fvar) = ctx.ih_map.get(arg_name) {
                            // Found a recursive call with a pattern var that has IH.
                            let mut result = Expr::fvar(ih_fvar);
                            // Apply extra (varying) arguments from the recursive call (#1386).
                            // With generalized motive, IH has type P1 → P2 → ... → ResultType.
                            // Explicit extra params come from the recursive call's surface args,
                            // while implicit params must be replayed from the current local
                            // context because they are omitted from surface applications.
                            let mut next_explicit_pos = ctx.decreasing_arg_pos + 1;
                            for extra_param in &ctx.extra_params {
                                // Expected type for this extra-param argument: the
                                // domain of the IH's (partially applied) Pi type.
                                // Elaborating the surface arg *with* this expected
                                // type lets type-directed literals resolve — most
                                // importantly an empty-list `[]` passed at a
                                // recursive call site (`f insts []`), whose element
                                // type would otherwise be left a polymorphic
                                // metavariable and fail the kernel re-check.
                                let expected_dom = self
                                    .infer_type(&result)
                                    .ok()
                                    .map(|t| self.whnf(&t))
                                    .and_then(|t| match t.kind() {
                                        ExprKind::Pi(_, dom, _) => Some(dom.as_ref().clone()),
                                        _ => None,
                                    });
                                let arg_expr = match extra_param.binder_info {
                                    BinderInfo::Default => {
                                        let arg = args.get(next_explicit_pos);
                                        if arg.is_some() {
                                            next_explicit_pos += 1;
                                        }
                                        arg.map(|arg| match &expected_dom {
                                            Some(dom) => self.elaborate_with_expected_type(
                                                &arg.expr,
                                                Some(dom.clone()),
                                            ),
                                            None => self.elaborate(&arg.expr),
                                        })
                                        .transpose()?
                                    }
                                    BinderInfo::Implicit
                                    | BinderInfo::StrictImplicit
                                    | BinderInfo::InstImplicit => self
                                        .lookup_local(&extra_param.name)
                                        .map(|(fvar, _)| Expr::fvar(fvar)),
                                };
                                if let Some(arg_expr) = arg_expr {
                                    result = Expr::app(result, arg_expr);
                                }
                            }
                            return Ok(result);
                        }
                    }
                }
            }
        }

        // Elaborate the function
        let func_expr = match func {
            SurfaceExpr::Ident(_, name) if name.starts_with('.') => {
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
            _ => self.elaborate(func)?,
        };

        // Resolve named arguments (#1230): if any arg has a name, reorder
        // args to match parameter positions before the main elaboration loop.
        let has_named_args = args.iter().any(|a| a.name.is_some());
        let resolved_args;
        let args = if has_named_args {
            resolved_args = self.resolve_named_args(&func_expr, args)?;
            &resolved_args[..]
        } else {
            args
        };

        // Try to infer the function's type to know about implicit arguments
        // If we can't infer it (e.g., function is a metavariable), fall back to simple elaboration
        let func_type_result = self.infer_type(&func_expr);

        if let Ok(func_type) = func_type_result {
            let (pre_applied_result, pre_applied_type, consumed_implicit_args) =
                self.try_consume_leading_implicit_args(func_expr.clone(), func_type.clone(), args)?;
            let remaining_args = &args[consumed_implicit_args..];

            // Decide whether to insert implicit args with metavariables.
            // If user provided more args than explicit binders, the extra args fill implicit slots.
            // Example: Ring : {α : Type u} → Type u has 0 explicit binders.
            //          Ring R provides 1 arg for 0 explicit binders, so R fills the implicit.
            // Example: id : {A : Type} → A → A has 1 explicit binder.
            //          id zero provides 1 arg for 1 explicit binder, so we insert meta for A.
            let num_explicit_binders = Self::count_explicit_binders(&pre_applied_type);
            // Leading instance-implicit binders whose carrier is pinned only by a
            // later *explicit* argument (e.g. `[inst : LE ?α]` in
            // `LE.le {α} [inst] (a b : α)`) must NOT be resolved eagerly: with an
            // unconstrained `?α`, `resolve_instance` would unify against whichever
            // `LE` instance is registered first (`instLENat`, pinning `?α := Nat`)
            // and then the `UInt8` operand mismatches. Defer them so the explicit
            // args pin `?α` first, then resolve after the arg loop. This mirrors
            // Lean 4's postponement of typeclass resolution (and the deferred path
            // already used in `apply_implicit_to_expected_type`).
            let mut leading_pending: Vec<(Expr, Expr)> = Vec::new();
            let (mut result, mut current_type) = if remaining_args.len() <= num_explicit_binders {
                // User args can be consumed by explicit binders, insert implicits as metas
                let (r, t, pending) = self.insert_implicit_args_deferring_instances(
                    pre_applied_result,
                    &pre_applied_type,
                );
                leading_pending = pending;
                (r, t)
            } else {
                // User provided more args than explicit binders, so some args fill implicits
                // Don't insert leading implicits - let args fill them directly
                (pre_applied_result, pre_applied_type)
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
                                    self.pin_hetero_binop_slots(&targets, &carrier_type);
                                }
                            }
                        }
                    }
                }
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
                || self.ctor_flex_slot_needs_expected(func, &current_type, remaining_args);
            // An expected type that is itself an unsolved metavariable has
            // nothing to push inward; firing the block would only pin it to a
            // half-open result. See `expected_is_unassigned_meta`.
            if needs_pre_arg_unify && !self.expected_is_unassigned_meta() {
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

                // Skip leading IMPLICIT binders that this explicit argument is not
                // meant to fill. The "more args than explicit binders" branch above
                // deliberately did NOT pre-insert leading implicits, so an explicit
                // argument can arrive while `current_type` still leads with an
                // implicit binder. That is correct when the user really does supply
                // a value for an implicit slot (`@`-style or `Ring R`), but WRONG
                // when a declaration carries an implicit binder Lean treats as
                // explicit — most importantly `Eq.refl`, whose value parameter
                // `(a : α)` is stored here as `{a : α}` (Implicit). Without this
                // skip, `Eq.refl n` matches `n` against the FIRST implicit
                // `{α : Sort u}`, yielding `Nat` vs `Sort u` and leaving the
                // universe `u` unsolved.
                //
                // We only skip an implicit binder when the explicit argument does
                // NOT fit its domain: speculatively elaborate the arg against the
                // implicit domain in a throwaway scope; if it fails to type-check
                // there, insert the implicit as a metavariable and advance to the
                // next binder. A binder the argument *does* fit is left for the
                // ordinary path (preserving `@`/`Ring R`-style explicit-fills-
                // implicit behaviour). SOUNDNESS: this only inserts metavariables
                // for skipped implicit binders (later solved by unification) and
                // the assembled term is kernel-rechecked; a wrong skip cannot
                // accept an ill-typed term.
                // Never skip in explicit mode (`@f`): the user has asked to
                // supply every argument positionally, including implicit ones,
                // so an explicit argument is meant for the leading implicit slot
                // (`@id zero` deliberately fills `{A : Type}` and must mismatch).
                while !self.explicit_mode {
                    let ExprKind::Pi(bi, dom, body) = current_type.kind() else {
                        break;
                    };
                    if !Self::is_implicit_binder(*bi) {
                        break;
                    }
                    let dom = dom.as_ref().clone();
                    let body = body.as_ref().clone();
                    let dom_inst = self.metas.instantiate(&dom);
                    // Does the explicit argument fit this implicit domain? Try in a
                    // speculative scope so a failed attempt leaves no assignments.
                    self.metas.push_scope();
                    let fits = self
                        .elaborate_arg_with_expected_type(&arg.expr, Some(dom_inst.clone()))
                        .map(|e| {
                            self.infer_type(&e)
                                .map(|t| {
                                    let t = self.whnf(&self.metas.instantiate(&t));
                                    let d = self.whnf(&self.metas.instantiate(&dom_inst));
                                    self.try_unify(&t, &d)
                                })
                                .unwrap_or(false)
                        })
                        .unwrap_or(false);
                    self.metas.pop_scope();
                    if fits {
                        break;
                    }
                    // The argument is not for this implicit binder — insert a
                    // metavariable for it and look at the next binder.
                    let meta = self.fresh_meta(dom_inst);
                    result = Expr::app(result, meta.clone());
                    current_type = self.whnf(&self.metas.instantiate(&body.instantiate(&meta)));
                }

                // Extract binder info and types to avoid borrow issues
                let type_info = match current_type.kind() {
                    ExprKind::Pi(bi, arg_ty, body_ty) => {
                        Some((*bi, arg_ty.as_ref().clone(), body_ty.as_ref().clone()))
                    }
                    _ => None,
                };

                if let Some((_bi, expected_arg_ty, _body_ty)) = type_info {
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
                    let arg_expr = match getelem_hole_goal {
                        Some(goal) => self.discharge_getelem_valid_hole(&goal),
                        None => self.elaborate_arg_with_expected_type(
                            &arg.expr,
                            Some(expected_arg_ty.clone()),
                        ),
                    };
                    let arg_expr = match arg_expr {
                        Ok(e) => e,
                        Err(e) => {
                            self.metas.pop_scope();
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
                    let arg_type = self.whnf(&arg_type);
                    let expected_arg_ty = self.whnf(&expected_arg_ty);

                    let ctx = self.build_local_ctx();
                    let unify_result = {
                        let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                        unifier.unify(&arg_type, &expected_arg_ty)
                    };
                    let mut final_arg = match unify_result {
                        UnifyResult::Success => arg_expr.clone(),
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
                                    expected: format!("{expected_arg_ty:?}"),
                                    actual: msg,
                                });
                            }
                        }
                        UnifyResult::Stuck => {
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
                                self.pin_hetero_binop_slots(&targets, &arg_type);
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
                    // homogeneous arm fires, and `pin_hetero_binop_slots` only assigns
                    // open slots from a metavar-free carrier, so this is a no-op when
                    // operand-0 already pinned the slots.
                    if idx == 1 {
                        if let Some(slots) = &hetero_binop_slots {
                            if slots.homogeneous {
                                let targets = [&slots.alpha, &slots.gamma];
                                self.pin_hetero_binop_slots(&targets, &arg_type);
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
                    result = Expr::app(result, final_arg);

                    // Insert any trailing implicit arguments before the next explicit arg
                    // BUT only if remaining user args fit in remaining explicit binders.
                    // This prevents over-inserting implicits when user args should fill them.
                    let remaining_user_args = remaining_args.len() - idx - 1;
                    let remaining_explicits = Self::count_explicit_binders(&current_type);
                    if remaining_user_args <= remaining_explicits {
                        let (new_result, new_type) =
                            self.insert_implicit_args(result, &current_type);
                        result = new_result;
                        current_type = new_type;
                    }
                } else {
                    // Function type is exhausted (not a Pi) but arguments remain.
                    // Return an error instead of silently applying (#1720).
                    self.metas.pop_scope();
                    return Err(ElabError::TooManyArguments {
                        func_type: format!("{current_type:?}"),
                        remaining_args: remaining_args.len() - idx,
                    });
                }
            }

            // Default-argument (`optParam`) insertion at the end of the
            // application: if the user supplied all positional arguments but the
            // function type still begins with explicit `optParam α default`
            // parameters, supply the defaults — but only when an expected type is
            // present and is reached by doing so. This matches Lean 4's default
            // insertion in `elabApp` while leaving genuine partial applications
            // (a function value passed on without an expected result type) alone.
            // It keys off the raw `optParam` parameter type, so it fires for
            // imported declarations with no clean-side default metadata.
            if let Some(expected) = self.current_expected_type.clone() {
                let current_type_now = self.whnf(&self.metas.instantiate(&current_type));
                let leads_with_opt_param = matches!(
                    current_type_now.kind(),
                    ExprKind::Pi(bi, arg_ty, _)
                        if !Self::is_implicit_binder(*bi)
                            && Self::opt_param_default(&self.metas.instantiate(arg_ty)).is_some()
                );
                if leads_with_opt_param {
                    let (defaulted, defaulted_ty) =
                        self.insert_opt_param_defaults(result.clone(), &current_type_now);
                    let defaulted_ty_whnf = self.whnf(&self.metas.instantiate(&defaulted_ty));
                    let expected_whnf = self.whnf(&self.metas.instantiate(&expected));
                    let matched = {
                        let ctx = self.build_local_ctx();
                        let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                        matches!(
                            unifier.unify(&defaulted_ty_whnf, &expected_whnf),
                            UnifyResult::Success
                        )
                    };
                    if matched {
                        result = defaulted;
                    }
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
                    // Goals that still carry metavariables keep the legacy
                    // leak-then-fail-closed path: an enclosing elaboration
                    // context may yet pin them and assign the meta.
                    if resolved.is_none() && !self.has_metavars(&goal_ty) {
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
                            return Err(ElabError::FailedToSynthesizeInstance {
                                goal: format!("{goal_ty}"),
                            });
                        }
                    }
                }
            }

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
                result = Expr::app(result, arg_expr);
            }
            let result = self.metas.instantiate(&result);
            Ok(self.metas.instantiate_levels(&result))
        }
    }
}
