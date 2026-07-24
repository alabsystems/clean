// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic elaboration: bridge from parsed `SurfaceTactic` AST to the
//! `ProofState`-based tactic framework.
//!
//! When the parser encounters `by tac1; tac2; ...`, it produces a
//! `SurfaceExpr::ByTactic(span, Vec<SurfaceTactic>)`. The elaborator
//! calls `elab_by_tactic` which:
//! 1. Creates a `ProofState` with the expected type as the goal
//! 2. Evaluates each `SurfaceTactic` against the proof state
//! 3. Extracts the closed proof term on success

use super::ElabCtx;
use crate::tactic::registry::{
    ElaboratedRefine, RefinePendingGoal, RefinePendingLocal, TacticEval,
};
use crate::tactic::{self, ProofState, TacticError};
use crate::unify::{MetaId, MetaState};
use crate::ElabError;
use clean_kernel::{Expr, ExprFolder, ExprVisitor, FVarId};
use clean_parser::{SurfaceExpr, SurfaceTactic, TacticArgPattern};
use std::collections::{HashMap, HashSet};

/// Implement `TacticEval` for `ElabCtx` so compound tactic handlers can
/// recursively evaluate sub-tactics and elaborate expressions without a
/// direct dependency on `ElabCtx`.
/// Phase 3D Waves 5-6 (#2440).
impl<'a> TacticEval for ElabCtx<'a> {
    fn eval(&mut self, ps: &mut ProofState, tac: &SurfaceTactic) -> Result<(), TacticError> {
        self.eval_tactic(ps, tac)
            .map_err(TacticError::from_elab_error)
    }

    fn eval_seq(&mut self, ps: &mut ProofState, tacs: &[SurfaceTactic]) -> Result<(), TacticError> {
        self.eval_tactic_seq(ps, tacs)
            .map_err(TacticError::from_elab_error)
    }

    fn elaborate(&mut self, expr: &SurfaceExpr) -> Result<Expr, TacticError> {
        ElabCtx::elaborate(self, expr).map_err(TacticError::from_elab_error)
    }

    fn elaborate_expected(
        &mut self,
        expr: &SurfaceExpr,
        expected: &Expr,
    ) -> Result<Expr, TacticError> {
        ElabCtx::elaborate_with_expected_type(self, expr, Some(expected.clone()))
            .map_err(TacticError::from_elab_error)
    }

    fn infer_type(&mut self, expr: &Expr) -> Result<Expr, TacticError> {
        ElabCtx::infer_type(self, expr).map_err(TacticError::from_elab_error)
    }

    fn elaborate_refine(
        &mut self,
        ps: &ProofState,
        expr: &SurfaceExpr,
    ) -> Result<ElaboratedRefine, TacticError> {
        let goal = ps.current_goal().ok_or(TacticError::NoGoals)?.clone();
        self.elaborate_refine_term(&goal, expr)
            .map_err(TacticError::from_elab_error)
    }

    fn metas(&self) -> &MetaState {
        &self.metas
    }

    /// Phase 8: bind `name` to a kernel `Expr` in the value channel so a later
    /// body position referencing `name` splices the stored term via
    /// `elab_ident` (the B78 `meta_value_bindings` mechanism).
    fn set_value_binding(&mut self, name: &str, value: Expr) {
        self.meta_value_bindings.insert(name.to_owned(), value);
    }

    /// Phase 8: remove a value-channel binding (paired with
    /// `set_value_binding`) so a goal-query value does not leak past the body.
    fn clear_value_binding(&mut self, name: &str) {
        self.meta_value_bindings.remove(name);
    }
}

#[derive(Default)]
struct PendingRefineMetaCollector {
    existing: HashSet<MetaId>,
    pending_metas: Vec<MetaId>,
    seen: HashSet<MetaId>,
}

impl ExprVisitor for PendingRefineMetaCollector {
    type Result = ();

    fn combine(&self, _a: (), _b: ()) {}

    fn visit_fvar(&mut self, id: FVarId) {
        let Some(meta_id) = MetaState::from_fvar(id) else {
            return;
        };
        if self.existing.contains(&meta_id) || !self.seen.insert(meta_id) {
            return;
        }
        self.pending_metas.push(meta_id);
    }
}

/// Rewrites meta-encoded FVars through `mapping`, recording any meta-FVar with
/// no mapping entry in `unmapped` (left untouched in the output).
struct MetaFVarRemapper<'a> {
    mapping: &'a HashMap<MetaId, MetaId>,
    unmapped: Vec<MetaId>,
}

impl ExprFolder for MetaFVarRemapper<'_> {
    fn fold_fvar(&mut self, id: FVarId) -> Expr {
        if let Some(meta_id) = MetaState::from_fvar(id) {
            if let Some(mapped) = self.mapping.get(&meta_id) {
                return Expr::fvar(MetaState::to_fvar(*mapped));
            }
            self.unmapped.push(meta_id);
        }
        Expr::fvar(id)
    }
}

/// B102: re-mint residual UNSOLVED elaborator metavariables inside an `apply`
/// term argument as ProofState metavariables.
///
/// `apply Nat.le_trans hab` elaborates its term argument with the ELABORATOR's
/// `MetaState`: trailing implicit args the partial application does not
/// determine (the `?k` of `b ≤ ?k → a ≤ ?k`) stay unsolved there. The
/// `ProofState` owns a SEPARATE `MetaState` with an overlapping id space, so a
/// leaked elaborator meta is (fail-closed) an `UnknownFVar` for the tactic
/// type-checker before `apply` even sees the goal. Translate each residual
/// meta into a fresh ProofState meta — registered with its (instantiated,
/// translated) type and scoped to the current goal's locals — so `apply`'s
/// unifier can solve it against the goal target (`?k := c`).
///
/// Soundness: this only re-labels unknowns; no assignment is invented. The
/// re-minted metas are either solved by unification or stay open and fail the
/// final `verify_tactic_proof` re-check loudly, and the closing proof still
/// passes `close_goal`'s strict type-check plus the kernel `add_decl`
/// re-verification.
fn adopt_residual_elab_metas(
    ps: &mut ProofState,
    elab_metas: &MetaState,
    term: &Expr,
) -> Result<Expr, TacticError> {
    let term = elab_metas.instantiate_levels(&elab_metas.instantiate(term));

    let mut collector = PendingRefineMetaCollector::default();
    collector.visit_expr(&term);
    if collector.pending_metas.is_empty() {
        return Ok(term);
    }

    // Mint in first-occurrence order; a residual meta's TYPE may reference
    // earlier residual metas, which the growing mapping resolves. A type that
    // references a meta we have not (yet) minted fails loud rather than
    // leaking a foreign id into the ProofState.
    let mut mapping: HashMap<MetaId, MetaId> = HashMap::new();
    for meta_id in &collector.pending_metas {
        let meta = elab_metas
            .get(*meta_id)
            .ok_or_else(|| TacticError::ElaborationFailed {
                detail: format!("apply: term references unknown elaborator meta {meta_id:?}"),
            })?;
        let ty = elab_metas.instantiate_levels(&elab_metas.instantiate(&meta.ty));
        let mut ty_remapper = MetaFVarRemapper {
            mapping: &mapping,
            unmapped: Vec::new(),
        };
        let ty = ty_remapper.fold_expr(&ty);
        if !ty_remapper.unmapped.is_empty() {
            return Err(TacticError::ElaborationFailed {
                detail: format!(
                    "apply: residual elaborator meta {meta_id:?} has a type mentioning \
                     untranslated metas {:?}",
                    ty_remapper.unmapped
                ),
            });
        }
        let ps_id = ps.fresh_meta(ty);
        ps.invalidate_tc_cache();
        mapping.insert(*meta_id, ps_id);
    }

    let mut remapper = MetaFVarRemapper {
        mapping: &mapping,
        unmapped: Vec::new(),
    };
    let translated = remapper.fold_expr(&term);
    if remapper.unmapped.is_empty() {
        Ok(translated)
    } else {
        Err(TacticError::ElaborationFailed {
            detail: format!(
                "apply: term retains untranslated elaborator metas {:?}",
                remapper.unmapped
            ),
        })
    }
}

impl<'a> ElabCtx<'a> {
    /// Elaborate a `by tactic_seq` expression.
    ///
    /// The expected type must be known (from a type annotation or the declaration
    /// type). If no expected type is available, we create a metavariable.
    pub(crate) fn elab_by_tactic(&mut self, tactics: &[SurfaceTactic]) -> Result<Expr, ElabError> {
        let target = self
            .current_expected_type
            .clone()
            .unwrap_or_else(|| self.fresh_meta(Expr::type_()));

        // Instantiate metavars and beta-reduce the expected type before it
        // becomes the tactic goal. Inside an anonymous constructor, a later
        // field's expected type is the constructor's dependent Pi domain applied
        // to earlier elaborated fields — e.g. for `⟨1, by omega⟩ : ∃ n, n > 0`
        // the raw expected type is the redex `(fun n => n > 0) 1`, not `1 > 0`.
        // Handing the redex to the tactic makes head-matching tactics (omega,
        // decide, rfl) fail to recognize the goal.
        //
        // We beta-reduce (not full WHNF): beta removes the `(fun n => …) 1`
        // redex to yield `1 > 0` while keeping the `GT.gt`/`LE.le` typeclass
        // head that omega/decide pattern-match on. Full WHNF would unfold the
        // typeclass projection all the way to `Nat.le …`, which those tactics
        // do not recognize. Beta preserves the type by beta-defeq (the reduced
        // goal is definitionally equal to the original), and `verify_tactic_proof`
        // re-checks the produced proof against the original target, so this can
        // only let currently-failing-but-valid proofs through, never an unsound
        // one. Mirrors Lean's `getMainTarget` (instantiateMVars before the
        // tactic block sees the goal).
        let target = crate::tactic::simp::beta_reduce(&self.metas.instantiate(&target));

        let elab_locals: Vec<_> = self
            .locals
            .iter()
            .map(|(name, fvar, ty)| tactic::LocalDecl {
                fvar: *fvar,
                name: name.clone(),
                ty: ty.clone(),
                value: None,
            })
            .collect();
        let mut ps = ProofState::with_instances_and_elab_context(
            self.env.clone(),
            target.clone(),
            self.instances.clone(),
            elab_locals,
        );

        // Thread the opened-namespace context so name-based tactics resolve
        // unqualified extra-lemma names through opened namespaces. After
        // `open Nat`, `simp [add_zero]` must reach `Nat.add_zero`, mirroring
        // the term elaborator's `resolve_identifier` order. Without this the
        // simp lemma lookup only tries the literal name and fails.
        ps.set_namespace_state(self.namespace_state.clone());

        // Populate ProofState with elaborator-scope FVars (#2212).
        // When a theorem has parameters (e.g., `theorem t (A : Prop) (a : A) : A`),
        // the elaborator creates FVars for those parameters. The ProofState
        // TypeChecker needs these to type-check proof terms that reference them
        // (e.g., `exact a` resolves to FVar(1) from the elaborator).
        // `with_instances_and_elab_context` also seeds Goal.local_ctx so tactic
        // hypothesis lookup (rw, conv, etc.) sees theorem parameters.

        for tac in tactics {
            self.eval_tactic(&mut ps, tac)?;
        }

        match ps.closed_proof() {
            Some(proof) => {
                // Realize any universe-level *parameters* solved during tactic
                // elaboration (e.g. `Exists.{u_1}` → `Exists.{1}`, committed by
                // `elab_anonymous_ctor`/`existsi` into the ElabCtx level union-find)
                // before the strict kernel re-check. The assembled `cases`/
                // `induction` proof carries the goal's motive, which still mentions
                // the abstract `u_1`; without this the motive's `Sort u_1` fails the
                // kernel's `Nat : Sort u_1` check against the concrete `Sort 1`.
                // `instantiate_levels` is a no-op when no level was solved.
                let proof = self.metas.instantiate_levels(&proof);
                let target = self.metas.instantiate_levels(&target);
                self.verify_tactic_proof(&proof, &target)?;
                Ok(proof)
            }
            None => {
                let goals = ps.goals();
                let n_goals = goals.len();
                if n_goals > 0 {
                    // #2203: Structural sorry auto-fill eliminated. When tactics
                    // leave goals unfinished, return an error instead of silently
                    // filling with sorry. Explicit `sorry` tactic (user intent)
                    // still works — it closes the goal via close_goal at eval time.
                    // #1801: Include remaining goal types in the error (like Lean 4).
                    let mut detail = String::new();
                    for goal in goals.iter().take(5) {
                        for decl in &goal.local_ctx {
                            detail.push_str(&format!("\n{} : {:?}", decl.name, decl.ty));
                        }
                        detail.push_str(&format!("\n⊢ {:?}", goal.target));
                    }
                    if n_goals > 5 {
                        detail.push_str(&format!("\n... and {} more goal(s)", n_goals - 5));
                    }
                    Err(TacticError::UnsolvedGoals {
                        count: n_goals,
                        detail,
                    }
                    .into())
                } else {
                    Err(TacticError::ProofNotProduced.into())
                }
            }
        }
    }

    /// Post-hoc type check: verify the assembled proof term is well-typed
    /// and matches the expected target type. Part of #2154, #2201.
    ///
    /// This catches soundness bugs in goal-transforming tactics (have,
    /// suffices, cases, induction, generalize, congr, etc.) whose proof
    /// terms contain metavariable sub-goals that cannot be individually
    /// type-checked at `close_goal` time. At this point all metas are
    /// resolved, so the full proof can be verified.
    ///
    /// Phase 2 (hard error): returns `Err(ElabError::ProofTypeMismatch)`
    /// on type mismatch, rejecting ill-typed proofs at the elaboration
    /// boundary. This is the single enforcement point that catches all
    /// bypass pathways (close_goal_unchecked, metas.assign). Runtime is
    /// O(n) in proof size (infer_type + is_def_eq), not O(1).
    ///
    /// Note: Both `infer_type` and `is_def_eq` on `ElabCtx` delegate to
    /// the kernel `TypeChecker` after fully instantiating metavariables.
    /// They do not assign elaborator-level metas — this check is purely
    /// observational (side-effect-free except for TC cache warming).
    fn verify_tactic_proof(&self, proof: &Expr, target: &Expr) -> Result<(), ElabError> {
        // Strict (infer_only=false) inference so the assembled proof is held to
        // the same standard as Environment::add_decl: App-argument types and
        // Lam/Pi domain sorts are validated, rejecting ill-typed terms (e.g. a
        // mis-applied Eq.trans) that the lenient infer_type would accept. #38.
        match self.infer_type_full(proof) {
            Ok(proof_ty) => {
                if !self.is_def_eq(&proof_ty, target) {
                    let target_inst = self.metas.instantiate(target);
                    return Err(ElabError::ProofTypeMismatch {
                        expected: format!("{target_inst:?}"),
                        actual: format!("{proof_ty:?}"),
                    });
                }
                Ok(())
            }
            Err(e) => {
                let target_inst = self.metas.instantiate(target);
                Err(ElabError::ProofTypeMismatch {
                    expected: format!("{target_inst:?}"),
                    actual: format!("ill-typed: {e}"),
                })
            }
        }
    }

    fn elaborate_refine_term(
        &mut self,
        goal: &tactic::Goal,
        expr: &SurfaceExpr,
    ) -> Result<ElaboratedRefine, ElabError> {
        let existing: HashSet<_> = self.metas.iter().map(|(id, _)| id).collect();
        let saved_expected = self.current_expected_type.clone();
        let expected = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&goal.target));
        self.current_expected_type = Some(expected.clone());
        let term = self.elaborate(expr);
        self.current_expected_type = saved_expected;
        let term = term?;

        // Post-elaboration: unify the elaborated term's type with the goal
        // target to resolve type metas created by SurfaceExpr::Hole (#2184).
        // Hole creates ty_meta (type=Type) + value_meta (type=ty_meta_fvar);
        // without this unification, ty_meta remains unsolved and
        // remap_elab_metas rejects the residual. elab_app does this internally
        // for args inside applications, but standalone holes need it here.
        if let Ok(inferred_ty) = self.infer_type(&term) {
            self.try_unify(&inferred_ty, &expected);
        }

        let term = self.metas.instantiate(&term);
        let term = self.metas.instantiate_levels(&term);

        let mut collector = PendingRefineMetaCollector {
            existing,
            ..PendingRefineMetaCollector::default()
        };
        collector.visit_expr(&term);

        let goal_fvars: HashSet<_> = goal.local_ctx.iter().map(|decl| decl.fvar).collect();
        let pending_goals = collector
            .pending_metas
            .into_iter()
            .map(|meta_id| {
                let meta = self.metas.get(meta_id).ok_or(ElabError::CannotInfer)?;
                let locals = meta
                    .locals
                    .iter()
                    .filter(|(_, fvar, _)| !goal_fvars.contains(fvar))
                    .map(|(name, fvar, ty)| RefinePendingLocal {
                        name: name.clone(),
                        fvar: *fvar,
                        ty: ty.clone(),
                    })
                    .collect();
                // A `?name` synthetic hole recorded its name against this meta;
                // carry it into the pending goal so the refine bridge tags the
                // tactic goal, letting `case name => …` select it. Anonymous
                // holes have no entry, so their goals stay untagged.
                let tag = self.hole_names.get(&meta_id).cloned();
                Ok(RefinePendingGoal {
                    meta_id,
                    locals,
                    tag,
                })
            })
            .collect::<Result<Vec<_>, ElabError>>()?;

        Ok(ElaboratedRefine {
            term,
            pending_goals,
        })
    }

    /// Elaborate the term argument of `exact <term>` against the current goal
    /// target as the expected type, fully solving the term's implicit
    /// arguments and universe levels before it reaches the `exact` handler.
    ///
    /// The plain `self.elaborate(arg)` path only sets `current_expected_type`
    /// as a side-channel; for a universe-polymorphic term whose arguments are
    /// ALL implicit — e.g. `@rfl.{u} {α : Sort u} {a : α} : a = a`, or
    /// `Eq.refl n` whose `Sort` universe `?u` is still abstract — there is no
    /// explicit operand to drive unification, so `?u`/`?α`/`?a` are left
    /// unsolved. The assembled term then carries a `Sort (Param u)`-flavoured
    /// type that fails the def-eq check against the goal `n = n`.
    ///
    /// This routes the argument through `elaborate_with_expected_type`, which
    /// invokes `apply_implicit_to_expected_type` to insert the implicit
    /// arguments and unify the term's result type with the expected goal
    /// target — pinning the value metavariables AND the universe levels
    /// exactly as the `rfl`/`existsi`/head-const level fixes do. A
    /// post-elaboration unify + level commit then instantiates every solved
    /// metavariable and level back into the term, so the `exact` handler
    /// receives a closed, fully-instantiated proof.
    ///
    /// SOUNDNESS: this only SOLVES metavariables/levels against the expected
    /// type; it never fabricates a proof. The returned term's type is still
    /// def-eq checked against the goal by the `exact` handler, and the whole
    /// proof is re-checked by `verify_tactic_proof`/`add_decl`. A term whose
    /// type genuinely does not match the goal still errors (the expected-type
    /// unify simply fails to solve the metas, and the downstream check
    /// rejects it). No over-acceptance is possible.
    fn elaborate_exact_term(
        &mut self,
        goal: &tactic::Goal,
        arg: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        let expected = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&goal.target));
        let term = self.elaborate_with_expected_type(arg, Some(expected.clone()))?;

        // Post-elaboration: unify the elaborated term's type with the goal
        // target so any value metavars / universe levels still left abstract
        // (the universe of `α` in `@rfl`/`Eq.refl`) are solved by unifying the
        // term's type with the expected proposition. Best-effort: a genuine
        // mismatch leaves the term unchanged and is rejected downstream.
        if let Ok(inferred_ty) = self.infer_type(&term) {
            self.try_unify(&inferred_ty, &expected);
        }
        self.commit_pending_level_assigns();

        // Solve any still-abstract universe-level PARAMETERS on the term's head
        // constant from its now-concrete type arguments — the same fix the
        // application elaborator and `existsi` apply. After the expected-type
        // unify above pins `?α := Nat`, the universe `u` of `α : Sort u` in
        // `@Eq.refl.{u} α a` is no longer a metavariable but a free
        // `Level::Param`; the type-level unify cannot reach it, so walk the
        // head telescope and constrain `u` from `Nat : Sort 1`.
        let term = self.metas.instantiate(&term);
        self.solve_head_const_levels(&term);
        self.commit_pending_level_assigns();

        let term = self.metas.instantiate(&term);
        Ok(self.metas.instantiate_levels(&term))
    }

    /// Evaluate a single `SurfaceTactic` against the proof state.
    ///
    /// Pushes the current goal's local context into ElabCtx before
    /// dispatching, so ALL tactic sub-methods that call `self.elaborate()`
    /// can resolve tactic-introduced hypotheses. This is the ProofState →
    /// ElabCtx bridge (#2212). Locals are popped after dispatch (even on
    /// error).
    pub(super) fn eval_tactic(
        &mut self,
        ps: &mut ProofState,
        tac: &SurfaceTactic,
    ) -> Result<(), ElabError> {
        // Push tactic-local declarations into ElabCtx for name resolution.
        // Without this, `intro h; exact h` (or `have`, `change`, `calc`,
        // etc.) would resolve `h` as auto-implicit instead of the FVar
        // introduced by the tactic.
        let locals_before = self.locals.len();
        if let Some(goal) = ps.current_goal() {
            // #2529: Deduplicate by FVarId — after the bridge fix, theorem
            // parameters appear in both ElabCtx.locals and goal.local_ctx.
            // Pushing duplicates would create identical entries that confuse
            // name resolution.
            let existing: HashSet<FVarId> = self.locals.iter().map(|(_, fvar, _)| *fvar).collect();
            for decl in &goal.local_ctx {
                if !existing.contains(&decl.fvar) {
                    // Carry the let-value through the bridge so `let`-introduced
                    // locals stay body-visible (zeta-reducible) when a later
                    // tactic elaborates a term that mentions them (e.g.
                    // `have h : x = v := rfl`). Opaque hypotheses (`have`,
                    // `intro`) have `value == None` and bridge as rigid locals.
                    match &decl.value {
                        Some(value) => self.push_local_let_with_fvar(
                            decl.name.clone(),
                            decl.fvar,
                            decl.ty.clone(),
                            value.clone(),
                        ),
                        None => {
                            self.push_local_with_fvar(decl.name.clone(), decl.fvar, decl.ty.clone())
                        }
                    }
                }
            }
        }

        let result = match tac {
            SurfaceTactic::Term(..) => self.eval_term_tactic(ps, tac),

            // Compound tactics: registry-only dispatch (Phase 3D Waves 3-6).
            // 23 compound variants have registered handlers in
            // builtins_compound.rs (Wave 5), builtins_phase3d_elab.rs (Wave 6),
            // builtins_phase3d_conv.rs (Wave 4), builtins_phase3d_rewrite.rs
            // (Wave 3), and builtins_phase3d_intro.rs (Wave 4).
            SurfaceTactic::Cases(..)
            | SurfaceTactic::Induction { .. }
            | SurfaceTactic::Rw(..)
            | SurfaceTactic::Simp { .. }
            | SurfaceTactic::SimpRw(..)
            | SurfaceTactic::Simpa { .. }
            | SurfaceTactic::Have(..)
            | SurfaceTactic::Let(..)
            | SurfaceTactic::Suffices(..)
            | SurfaceTactic::Obtain { .. }
            | SurfaceTactic::RCases { .. }
            | SurfaceTactic::RIntro { .. }
            | SurfaceTactic::Case(..)
            | SurfaceTactic::Match(..)
            | SurfaceTactic::AllGoals(..)
            | SurfaceTactic::AnyGoals(..)
            | SurfaceTactic::Try(..)
            | SurfaceTactic::First(..)
            | SurfaceTactic::Repeat(..)
            | SurfaceTactic::SeqFocus(..)
            | SurfaceTactic::Paren(..)
            | SurfaceTactic::FocusBlock(..)
            | SurfaceTactic::Focus(..)
            | SurfaceTactic::Conv(..)
            | SurfaceTactic::ConvArg(..)
            | SurfaceTactic::ConvEnter(..) => {
                let name = compound_tactic_name(tac).unwrap_or("unknown");
                let handler = self
                    .tactic_registry
                    .get_compound(name)
                    .map(|e| e.handler.clone())
                    .ok_or_else(|| ElabError::from(TacticError::UnknownTactic(name.into())))?;
                (handler)(self, ps, tac).map_err(ElabError::from)
            }

            // Calc remains hardcoded (specialized SurfaceCalcStep parsing, deferred).
            SurfaceTactic::Calc(..) => self.eval_context_terminal_tactic(ps, tac),

            // Named tactics dispatched via TacticRegistry (#1894).
            //
            // User-defined `elab ... : tactic => <body>` tactics register a
            // compound handler (substitute call-site args into the body tactic
            // AST, then delegate). Prefer it over the simple handler so the
            // executable body actually runs. Soundness: the compound handler
            // only delegates back to this same evaluator.
            SurfaceTactic::Named { name, .. }
                if self.tactic_registry.get_compound(name).is_some() =>
            {
                let handler = self
                    .tactic_registry
                    .get_compound(name)
                    .map(|e| e.handler.clone())
                    .ok_or_else(|| ElabError::from(TacticError::UnknownTactic(name.clone())))?;
                (handler)(self, ps, tac).map_err(ElabError::from)
            }

            SurfaceTactic::Named { name, args, .. } => {
                if name == "refine" {
                    let arg = args.first().ok_or_else(|| {
                        ElabError::from(TacticError::MissingArgument {
                            tactic: "refine".into(),
                            expected: "an argument".into(),
                        })
                    })?;
                    let goal = ps
                        .current_goal()
                        .cloned()
                        .ok_or_else(|| ElabError::from(TacticError::NoGoals))?;
                    let refined = self.elaborate_refine_term(&goal, arg)?;
                    tactic::term_close::refine_elaborated_from_pending(
                        ps,
                        refined.term,
                        &self.metas,
                        &refined.pending_goals,
                    )
                    .map_err(ElabError::from)
                } else {
                    let entry = self.tactic_registry.get(name).cloned();
                    if let Some(entry) = entry {
                        // `wlog h p` (B104): the ExprList grammar parses the
                        // space-separated form as ONE application expr `h p` —
                        // but slot 0 is a binder NAME for a hypothesis not yet
                        // in scope (exactly like `by_cases h : p`). Split the
                        // application back into [name, assumption] so the name
                        // takes the binder-name pass-through below and only the
                        // assumption elaborates as a term. The comma form
                        // `wlog h, p` already arrives split.
                        let wlog_split: Option<Vec<SurfaceExpr>> =
                            if name == "wlog" && args.len() == 1 {
                                match &args[0] {
                                    SurfaceExpr::App(span, head, rest)
                                        if matches!(head.as_ref(), SurfaceExpr::Ident(_, _))
                                            && !rest.is_empty()
                                            && rest.iter().all(|a| a.name.is_none()) =>
                                    {
                                        let assumption = if rest.len() == 1 {
                                            rest[0].expr.clone()
                                        } else {
                                            SurfaceExpr::App(
                                                *span,
                                                Box::new(rest[0].expr.clone()),
                                                rest[1..].to_vec(),
                                            )
                                        };
                                        Some(vec![head.as_ref().clone(), assumption])
                                    }
                                    _ => None,
                                }
                            } else {
                                None
                            };
                        let args: &[SurfaceExpr] = wlog_split.as_deref().unwrap_or(args);
                        // For ident-list patterns, Ident args are bare names (not
                        // bound variables) — convert directly to Expr::Const without
                        // elaboration. Other args still get elaborated normally.
                        let is_ident_pattern = matches!(
                            entry.pattern,
                            TacticArgPattern::IdentList | TacticArgPattern::NonemptyIdentList
                        );
                        // Goal-closing term tactics (`exact`) must elaborate their
                        // term argument against the CURRENT goal target as expected
                        // type — exactly as `refine` does via `elaborate_refine_term`.
                        // Otherwise `self.elaborate` below reads a stale
                        // `current_expected_type` (the original `by`-block target,
                        // which still carries the pre-`cases` scrutinee FVar and any
                        // unsolved universe metavars). Inside a `cases`/`induction`
                        // branch this makes `exact Or.inr ⟨k, rfl⟩` unify against the
                        // wrong disjunct / leave a `Sort ?u` level meta unsolved for a
                        // goal like `Nat.succ k = 0 ∨ ∃ m, Nat.succ k = m + 1`.
                        //
                        // For `exact` we additionally route the single term argument
                        // through `elaborate_exact_term`, which uses
                        // `elaborate_with_expected_type` +
                        // `apply_implicit_to_expected_type` to INSERT implicit
                        // arguments and SOLVE the term's universe levels from the
                        // expected goal target. Merely setting `current_expected_type`
                        // is not enough for a fully-implicit polymorphic term like
                        // `rfl`/`Eq.refl n`/`id hp`: a bare ident has no operand to
                        // drive unification, so `self.elaborate` leaves `?u`/`?α`/`?a`
                        // unsolved and the assembled term fails the def-eq check.
                        //
                        // Soundness: this only refines the EXPECTED type fed to the
                        // bidirectional elaborator and SOLVES (never fabricates)
                        // metavars/levels; the resulting term is still def-eq checked
                        // against the goal by the `exact` handler and the whole proof
                        // is re-checked by `verify_tactic_proof`/`add_decl`, so a
                        // mismatched expected can only let a valid-but-currently-failing
                        // proof through, never an unsound one.
                        let saved_expected = self.current_expected_type.clone();
                        // For `exact`, capture the goal once so the term arg can be
                        // elaborated against it via `elaborate_exact_term`.
                        let exact_goal = if name == "exact" {
                            ps.current_goal().cloned()
                        } else {
                            None
                        };
                        let restore_expected = if name == "exact" {
                            if let Some(goal) = &exact_goal {
                                let expected = self
                                    .metas
                                    .instantiate_levels(&self.metas.instantiate(&goal.target));
                                self.current_expected_type = Some(expected);
                            }
                            true
                        } else {
                            false
                        };
                        // Some `ExprList` compound tactics carry a *binder name*
                        // in a fixed argument slot (e.g. `by_cases h : p` names a
                        // NEW hypothesis `h`; `generalize e : x` names a new var
                        // `x`). Such a slot must NOT be elaborated as a term:
                        // the name is not yet in scope, so the elaborator would
                        // bind it as a fresh auto-implicit fvar that is absent
                        // from the goal's local context, and `expr_to_hyp_name`
                        // would then raise `HypothesisNotFound`. Pass these
                        // slots through as bare `Const`s exactly like the
                        // ident-list pass-through below. Soundness: the handler
                        // only reads the const's name via `expr_to_hyp_name`; the
                        // resulting case-split / generalize proof term is still
                        // kernel-rechecked by `verify_tactic_proof`/`add_decl`.
                        let binder_name_slot = |idx: usize| -> bool {
                            match name.as_str() {
                                "by_cases" => idx == 0,
                                // `wlog h p` names a NEW hypothesis `h` (B104),
                                // exactly like `by_cases h : p`.
                                "wlog" => idx == 0,
                                // `generalize (h :)? e = x`: slot 1 is the new
                                // variable `x`; the optional slot 2 is the
                                // hypothesis name `h` (the `h : e = x` form).
                                // Neither is in scope yet, so both pass through
                                // as bare `Const`s (read back via
                                // `expr_to_hyp_name`) rather than being
                                // elaborated as terms.
                                "generalize" => idx == 1 || idx == 2,
                                _ => false,
                            }
                        };
                        let elaborated: Result<Vec<Expr>, ElabError> =
                            if matches!(entry.pattern, TacticArgPattern::Nullary) {
                                Ok(Vec::new())
                            } else {
                                args.iter()
                                    .enumerate()
                                    .map(|(idx, a)| {
                                        if binder_name_slot(idx) {
                                            if let SurfaceExpr::Ident(_, ident_name) = a {
                                                return Ok(Expr::const_str(ident_name));
                                            }
                                        }
                                        // An `_` in a NAME position (ident-list tactic
                                        // like `intro _`, or a binder-name slot) is an
                                        // ANONYMOUS binder name, NOT a term hole. Parsed
                                        // as `SurfaceExpr::Hole`, it must pass through as
                                        // the bare name `"_"` (read back by
                                        // `expr_to_hyp_name`) — elaborating it as a term
                                        // mints a stray value metavar that never gets
                                        // solved and leaks a meta-encoded FVar into the
                                        // assembled proof (fail-closed `UnknownFVar`).
                                        // Soundness: only supplies a binder NAME; the
                                        // resulting proof is kernel-rechecked by
                                        // `verify_tactic_proof`/`add_decl`.
                                        if (is_ident_pattern || binder_name_slot(idx))
                                            && matches!(a, SurfaceExpr::Hole(_))
                                        {
                                            return Ok(Expr::const_str("_"));
                                        }
                                        // `exact <term>`: drive the term's elaboration
                                        // with the goal target so implicit args and
                                        // universe levels of a polymorphic term (`rfl`,
                                        // `Eq.refl n`, `id hp`) are solved by
                                        // unification before the handler runs.
                                        if let Some(goal) = &exact_goal {
                                            return self.elaborate_exact_term(goal, a);
                                        }
                                        if is_ident_pattern {
                                            if let SurfaceExpr::Ident(_, ident_name) = a {
                                                // Try namespace-qualified name first when
                                                // inside a namespace block and the bare name
                                                // is not a known constant. This allows
                                                // `unfold land` to find `Int.land` inside
                                                // `namespace Int`. Part of #3396.
                                                if !self.namespace_prefix.is_empty() {
                                                    let bare =
                                                        clean_kernel::Name::from_string(ident_name);
                                                    if self.env.get_const(&bare).is_none() {
                                                        let qualified =
                                                            self.qualify_name(ident_name);
                                                        let qname = clean_kernel::Name::from_string(
                                                            &qualified,
                                                        );
                                                        if self.env.get_const(&qname).is_some() {
                                                            return Ok(Expr::const_str(&qualified));
                                                        }
                                                    }
                                                }
                                                return Ok(Expr::const_str(ident_name));
                                            }
                                        }
                                        self.elaborate(a)
                                    })
                                    .collect::<Result<Vec<_>, ElabError>>()
                            };
                        // Restore the saved expected type before running the handler,
                        // regardless of whether arg elaboration succeeded.
                        if restore_expected {
                            self.current_expected_type = saved_expected;
                        }
                        let elaborated = elaborated?;
                        // `apply <lemma> <arg>`: a partially-applied lemma leaves
                        // trailing implicit args as UNSOLVED elaborator metas; hand
                        // them to the ProofState as its own metas so `apply` can
                        // solve them against the goal (B102, see
                        // `adopt_residual_elab_metas`).
                        let elaborated = if name == "apply" {
                            elaborated
                                .into_iter()
                                .map(|e| {
                                    adopt_residual_elab_metas(ps, &self.metas, &e)
                                        .map_err(ElabError::from)
                                })
                                .collect::<Result<Vec<_>, ElabError>>()?
                        } else {
                            elaborated
                        };
                        (entry.handler)(ps, &elaborated).map_err(ElabError::from)
                    } else {
                        Err(TacticError::UnknownTactic(name.clone()).into())
                    }
                }
            }
        };

        // Pop tactic locals (even on error). Clear any let-value side-channel
        // entries for the popped fvars in lock-step so a `let`-local's value
        // cannot leak into a later, unrelated tactic's term elaboration.
        for (_, fvar, _) in self.locals.drain(locals_before..) {
            self.local_let_values.remove(&fvar);
        }

        // After each successful tactic, remove goals whose metavariables
        // are already assigned (transitively solved). Matches Lean 4's
        // getUnsolvedGoals behavior. Part of #1803.
        if result.is_ok() {
            ps.prune_solved_goals();
        }

        result
    }

    /// Evaluate term-mode tactic (bare expression in tactic position).
    ///
    /// Goal locals are already pushed by `eval_tactic` (#2212).
    /// Named term-arg tactics (exact, apply, refine, trans) migrated to
    /// TacticRegistry (#2430 Phase 3C Wave 2).
    fn eval_term_tactic(
        &mut self,
        ps: &mut ProofState,
        tac: &SurfaceTactic,
    ) -> Result<(), ElabError> {
        match tac {
            // A tactic-mode `do`-block at a proof site (`by do …`) parses as
            // `Term(Do(elems))`. Run it as a sequenced tactic script via the
            // shared user-tactic do-block executor — NOT as a monadic term
            // (`elaborate` on a `SurfaceExpr::Do` would try to find a `Monad`
            // instance for the tactic world and fail). Goal closure flows
            // through the executor's kernel-checked `eval_seq`/`exact`/`refine`
            // paths; this only sequences statements.
            SurfaceTactic::Term(_, expr) if matches!(expr.as_ref(), SurfaceExpr::Do(..)) => {
                super::user_tactic::run_tactic_do_block(self, ps, std::slice::from_ref(tac))
                    .map_err(ElabError::from)
            }
            SurfaceTactic::Term(_, expr) => {
                // Elaborate a bare-term tactic against the CURRENT goal's target as
                // expected type. Without this, `self.elaborate` reads a stale
                // `current_expected_type` (the original `by`-block target carrying
                // the pre-tactic scrutinee FVar and unsolved universe metavars),
                // which breaks bidirectional terms (`Or.inr ⟨k, rfl⟩`, anonymous
                // constructors) inside a `cases`/`induction` branch. This mirrors
                // the named-`exact` arm below and `refine`'s `elaborate_refine_term`.
                //
                // Soundness: only the EXPECTED type fed to the elaborator changes;
                // the term is still def-eq checked by `tactic::exact` and the whole
                // proof re-checked by `verify_tactic_proof`/`add_decl`.
                let saved_expected = self.current_expected_type.clone();
                if let Some(goal) = ps.current_goal() {
                    let expected = self
                        .metas
                        .instantiate_levels(&self.metas.instantiate(&goal.target));
                    self.current_expected_type = Some(expected);
                }
                let term = self.elaborate(expr);
                self.current_expected_type = saved_expected;
                let term = term?;
                tactic::exact(ps, term).map_err(ElabError::from)
            }
            _ => unreachable!("eval_term_tactic called with non-Term SurfaceTactic"),
        }
    }

    /// Evaluate calc tactic (remaining hardcoded — specialized SurfaceCalcStep
    /// parsing deferred to future migration wave).
    ///
    /// Conv, ConvArg, ConvEnter migrated to registry (Phase 3D Wave 4, #2440).
    fn eval_context_terminal_tactic(
        &mut self,
        ps: &mut ProofState,
        tac: &SurfaceTactic,
    ) -> Result<(), ElabError> {
        match tac {
            SurfaceTactic::Calc(_, steps) => {
                let proof = self.elab_calc(steps)?;
                tactic::exact(ps, proof).map_err(ElabError::from)
            }
            _ => unreachable!("eval_context_terminal_tactic called with non-Calc SurfaceTactic"),
        }
    }
}

/// Map a compound `SurfaceTactic` variant to its registry name.
///
/// Returns `None` for non-compound variants (Term, Named, Calc).
fn compound_tactic_name(tac: &SurfaceTactic) -> Option<&'static str> {
    match tac {
        SurfaceTactic::Paren(..) => Some("paren"),
        SurfaceTactic::Try(..) => Some("try"),
        SurfaceTactic::Focus(..) => Some("focus"),
        SurfaceTactic::FocusBlock(..) => Some("focus_block"),
        SurfaceTactic::Repeat(..) => Some("repeat"),
        SurfaceTactic::AllGoals(..) => Some("all_goals"),
        SurfaceTactic::AnyGoals(..) => Some("any_goals"),
        SurfaceTactic::First(..) => Some("first"),
        SurfaceTactic::SeqFocus(..) => Some("seq_focus"),
        SurfaceTactic::Case(..) => Some("case"),
        SurfaceTactic::Have(..) => Some("have"),
        SurfaceTactic::Let(..) => Some("let"),
        SurfaceTactic::Suffices(..) => Some("suffices"),
        SurfaceTactic::Obtain { .. } => Some("obtain"),
        SurfaceTactic::RCases { .. } => Some("rcases"),
        SurfaceTactic::RIntro { .. } => Some("rintro"),
        SurfaceTactic::Match(..) => Some("match"),
        SurfaceTactic::Conv(..) => Some("conv"),
        SurfaceTactic::ConvArg(..) => Some("conv_arg"),
        SurfaceTactic::ConvEnter(..) => Some("conv_enter"),
        // Wave 3D.3: rewrite/simp
        SurfaceTactic::Rw(..) => Some("rw"),
        SurfaceTactic::Simp { .. } => Some("simp"),
        SurfaceTactic::SimpRw(..) => Some("simp_rw"),
        SurfaceTactic::Simpa { .. } => Some("simpa"),
        // Wave 3D.4: cases/induction
        SurfaceTactic::Cases(..) => Some("cases"),
        SurfaceTactic::Induction { .. } => Some("induction"),
        _ => None,
    }
}
