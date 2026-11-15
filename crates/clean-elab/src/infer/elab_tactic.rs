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

use super::elab_core::IdentTarget;
use super::tactic_trace::{names_tactic, render_chain};
use super::ElabCtx;
use crate::tactic::registry::{
    ElaboratedRefine, RefinePendingGoal, RefinePendingLocal, TacticEval,
};
use crate::tactic::{self, ProofState, TacticError};
use crate::unify::{MetaId, MetaState};
use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprFolder, ExprKind, ExprVisitor, FVarId};
use clean_parser::{SurfaceExpr, SurfaceName, SurfaceTactic, TacticArgPattern};
use std::collections::{HashMap, HashSet};

/// Implement `TacticEval` for `ElabCtx` so compound tactic handlers can
/// recursively evaluate sub-tactics and elaborate expressions without a
/// direct dependency on `ElabCtx`.
/// Phase 3D Waves 5-6 (#2440).
impl<'a> TacticEval for ElabCtx<'a> {
    fn source_world(&self) -> Option<clean_kernel::LeanWorld> {
        self.source_world
    }

    fn note_tactic(&mut self, tac: &SurfaceTactic) {
        self.tactic_trace.note(tac);
    }

    fn note_local_forall_binder_names(
        &mut self,
        fvar: FVarId,
        surface_ty: &SurfaceExpr,
        ty: &Expr,
    ) {
        ElabCtx::note_local_forall_binder_names(self, fvar, Some(surface_ty), ty);
    }

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

    fn elaborate_no_expected(&mut self, expr: &SurfaceExpr) -> Result<Expr, TacticError> {
        // `elaborate_with_expected_type(expr, None)` is the only spelling that
        // saves, CLEARS and restores `current_expected_type` — the same one
        // `BridgedTermTarget::Open` already uses below.
        ElabCtx::elaborate_with_expected_type(self, expr, None)
            .map_err(TacticError::from_elab_error)
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
        // In the CURRENT goal's context, as `elaborate_open` below: a compound
        // tactic may have extended it since it started — the tactic `match h :
        // e` generalizes `e` to a fresh local and then refines a `match` on
        // that local ("Unknown identifier" for it otherwise). Bridging is
        // deduplicated by FVarId, so a plain `refine` sees exactly what it saw.
        let locals_before = self.locals.len();
        let local_instances_before = self.local_instances.len();
        // Consumed declaration binders are hidden (lane C), bridged locals the
        // goal renamed take its names (lane B, G66): undo the renames on the
        // vector they index, then restore the hidden binders' snapshot.
        let hidden = self.hide_consumed_binders(ps, &goal);
        let renamed = self.push_goal_locals(&goal);
        let result = self.elaborate_bridged_term(&goal, expr, BridgedTermTarget::Goal);
        self.restore_bridged_names(renamed);
        match hidden {
            Some(hidden) => self.restore_hidden_binders(hidden),
            None => self.locals.truncate(locals_before),
        }
        while self.local_instances.len() > local_instances_before {
            self.pop_local_instance();
        }
        result.map_err(TacticError::from_elab_error)
    }

    fn elaborate_open(
        &mut self,
        ps: &ProofState,
        expr: &SurfaceExpr,
    ) -> Result<ElaboratedRefine, TacticError> {
        let goal = ps.current_goal().ok_or(TacticError::NoGoals)?.clone();
        // The term is elaborated in the CURRENT goal's context, which a
        // tactic may have extended since it started (Lean's `g.withContext`):
        // a typed rcases pattern `⟨x, hx : p x⟩` elaborates `p x` after the
        // destructure bound `x`, and `eval_tactic_inner` only bridged the
        // locals that existed when `obtain` began ("Unknown identifier: x").
        let locals_before = self.locals.len();
        let local_instances_before = self.local_instances.len();
        // Consumed declaration binders are hidden (lane C), bridged locals the
        // goal renamed take its names (lane B, G66): undo the renames on the
        // vector they index, then restore the hidden binders' snapshot.
        let hidden = self.hide_consumed_binders(ps, &goal);
        let renamed = self.push_goal_locals(&goal);
        let result = self.elaborate_bridged_term(&goal, expr, BridgedTermTarget::Open);
        self.restore_bridged_names(renamed);
        match hidden {
            Some(hidden) => self.restore_hidden_binders(hidden),
            None => self.locals.truncate(locals_before),
        }
        while self.local_instances.len() > local_instances_before {
            self.pop_local_instance();
        }
        result.map_err(TacticError::from_elab_error)
    }

    fn metas(&self) -> &MetaState {
        &self.metas
    }

    /// Phase 8: bind `name` to a kernel `Expr` in the value channel so a later
    /// body position referencing `name` splices the stored term via
    /// `elab_ident` (the B78 `meta_value_bindings` mechanism).
    fn set_value_binding(&mut self, name: &SurfaceName, value: Expr) {
        self.meta_value_bindings.insert(name.to_owned(), value);
    }

    /// Phase 8: remove a value-channel binding (paired with
    /// `set_value_binding`) so a goal-query value does not leak past the body.
    fn clear_value_binding(&mut self, name: &SurfaceName) {
        self.meta_value_bindings.remove(name);
    }
}

/// What a bridged term is elaborated against — see
/// [`ElabCtx::elaborate_bridged_term`].
#[derive(Debug, Clone, Copy)]
enum BridgedTermTarget {
    /// Against the goal target (`refine`).
    Goal,
    /// With no expected type (a `rw` rule).
    Open,
}

/// Whether `e` mentions a metavariable-encoded free variable (after the
/// caller's instantiation: an UNASSIGNED elaborator metavariable).
fn contains_unassigned_meta_fvar(e: &Expr) -> bool {
    let mut collector = PendingRefineMetaCollector::default();
    collector.visit_expr(e);
    !collector.pending_metas.is_empty()
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
    let mut mapping: HashMap<MetaId, MetaId> = HashMap::new();
    adopt_residual_elab_metas_into(ps, elab_metas, term, &mut mapping, "apply")
}

/// [`adopt_residual_elab_metas`] over a CALLER-OWNED mapping: metas already
/// mapped are reused, new residual metas are minted and recorded, so several
/// terms (a goal target and its locals' types) can be translated
/// consistently and the caller can translate solutions BACK through the
/// inverse mapping afterwards (the `by`-block bridge does).
fn adopt_residual_elab_metas_into(
    ps: &mut ProofState,
    elab_metas: &MetaState,
    term: &Expr,
    mapping: &mut HashMap<MetaId, MetaId>,
    who: &str,
) -> Result<Expr, TacticError> {
    let term = elab_metas.instantiate_levels(&elab_metas.instantiate(term));

    let mut collector = PendingRefineMetaCollector {
        existing: mapping.keys().copied().collect(),
        ..PendingRefineMetaCollector::default()
    };
    collector.visit_expr(&term);
    if collector.pending_metas.is_empty() && mapping.is_empty() {
        return Ok(term);
    }

    // Mint each residual meta AFTER the metas its own TYPE mentions (a
    // dependency-first walk with a cycle guard), so a type that names a meta
    // occurring later in the term — or not in the term at all — is
    // translated rather than refused. A first-occurrence-order mint used to
    // fail loud here on exactly that shape ("residual elaborator meta ?m5
    // has a type mentioning untranslated metas", `Involutive.leftInverse_iff`,
    // `factorsThrough_iff` in `Mathlib/Logic/Function/Basic.lean`, measured
    // 2026-09-11).
    for meta_id in &collector.pending_metas {
        let mut in_progress = HashSet::new();
        adopt_one_residual_meta(ps, elab_metas, *meta_id, mapping, &mut in_progress, who)?;
    }

    let mut remapper = MetaFVarRemapper {
        mapping,
        unmapped: Vec::new(),
    };
    let translated = remapper.fold_expr(&term);
    if remapper.unmapped.is_empty() {
        Ok(translated)
    } else {
        Err(TacticError::ElaborationFailed {
            detail: format!(
                "{who}: term retains untranslated elaborator metas {}",
                crate::error_render::opaque(remapper.unmapped.as_slice())
            ),
        })
    }
}

/// Mint the ProofState twin of one residual elaborator meta, minting the
/// metas its type mentions first. `in_progress` breaks a (malformed) cycle.
fn adopt_one_residual_meta(
    ps: &mut ProofState,
    elab_metas: &MetaState,
    meta_id: MetaId,
    mapping: &mut HashMap<MetaId, MetaId>,
    in_progress: &mut HashSet<MetaId>,
    who: &str,
) -> Result<(), TacticError> {
    if mapping.contains_key(&meta_id) {
        return Ok(());
    }
    if !in_progress.insert(meta_id) {
        return Err(TacticError::ElaborationFailed {
            detail: format!(
                "{who}: residual elaborator meta ?m{} has a type mentioning itself",
                meta_id.0
            ),
        });
    }
    let meta = elab_metas
        .get(meta_id)
        .ok_or_else(|| TacticError::ElaborationFailed {
            detail: format!(
                "{who}: term references unknown elaborator meta ?m{}",
                meta_id.0
            ),
        })?;
    let ty = elab_metas.instantiate_levels(&elab_metas.instantiate(&meta.ty));
    let mut deps = PendingRefineMetaCollector {
        existing: mapping.keys().copied().collect(),
        ..PendingRefineMetaCollector::default()
    };
    deps.visit_expr(&ty);
    for dep in deps.pending_metas {
        adopt_one_residual_meta(ps, elab_metas, dep, mapping, in_progress, who)?;
    }
    let mut ty_remapper = MetaFVarRemapper {
        mapping,
        unmapped: Vec::new(),
    };
    let ty = ty_remapper.fold_expr(&ty);
    if !ty_remapper.unmapped.is_empty() {
        return Err(TacticError::ElaborationFailed {
            detail: format!(
                "{who}: residual elaborator meta ?m{} has a type mentioning \
                 untranslated metas {}",
                meta_id.0,
                crate::error_render::opaque(ty_remapper.unmapped.as_slice())
            ),
        });
    }
    let ps_id = ps.fresh_meta(ty);
    ps.invalidate_tc_cache();
    mapping.insert(meta_id, ps_id);
    in_progress.remove(&meta_id);
    Ok(())
}

impl<'a> ElabCtx<'a> {
    /// Elaborate a `by tactic_seq` expression.
    ///
    /// The expected type must be known (from a type annotation or the declaration
    /// type). If no expected type is available, we create a metavariable.
    ///
    /// Wraps [`Self::elab_by_tactic_inner`] with the failure-**attribution**
    /// boundary: on the way out, an error that does not already name the
    /// tactic responsible is tagged with that tactic's source spelling, its
    /// nesting chain and its source span. See `infer::tactic_trace`.
    pub(crate) fn elab_by_tactic(&mut self, tactics: &[SurfaceTactic]) -> Result<Expr, ElabError> {
        self.elab_by_tactic_at(None, tactics)
    }

    pub(super) fn elab_by_tactic_at(
        &mut self,
        span: Option<clean_parser::Span>,
        tactics: &[SurfaceTactic],
    ) -> Result<Expr, ElabError> {
        let block = self.tactic_goal_capture.as_ref().and_then(|capture| {
            capture.start_block(span.filter(|s| s.start < s.end).map(|s| {
                tactic::TacticPostSnapshotRange {
                    start: s.start,
                    end: s.end,
                }
            }))
        });
        let saved = std::mem::replace(&mut self.tactic_goal_block, block);
        let result = self.elab_by_tactic_traced(tactics);
        self.tactic_goal_block = saved;
        result
    }

    fn elab_by_tactic_traced(&mut self, tactics: &[SurfaceTactic]) -> Result<Expr, ElabError> {
        self.with_eager_numerals(|this| this.elab_by_tactic_attributed(tactics))
    }

    fn elab_by_tactic_attributed(&mut self, tactics: &[SurfaceTactic]) -> Result<Expr, ElabError> {
        // FAIL-CLOSED: a `by` block with no tactics never comes from a
        // well-formed source file — `by` followed by nothing is a parse error
        // in Lean, and Clean's recovery path yields `SyntheticSorry`, not an
        // empty block. The one producer of an empty script is the lossy
        // `surface → syntax → expand → surface` roundtrip, whose
        // `surface_to_syntax` discards a `ByTactic`'s children
        // (`macro_integration/to_syntax.rs`). Running zero tactics leaves the
        // goal open and is reported as `unsolved goals` on a correctly
        // instantiated goal — indistinguishable from a script that ran and
        // failed, which is the entire cost of that class: `by sorry`, `by skip`
        // and `by unknown_tactic_xyz` all produce the identical message in the
        // dropped shape. Refusing loudly turns a silent loss into a named one.
        if tactics.is_empty() {
            return Err(ElabError::InternalInvariant(
                "a `by` block reached elaboration with an empty tactic script: its tactics were \
                 discarded before they could run (the `surface → syntax → surface` roundtrip \
                 drops `ByTactic` children), so the goal was never attempted"
                    .to_string(),
            ));
        }
        let saved = self.tactic_trace.enter_block();
        let result = self
            .elab_by_tactic_inner(tactics)
            .map_err(|err| self.attribute_tactic_failure(err));
        self.tactic_trace.leave_block(saved);
        result
    }

    /// Name the tactic responsible for `err`, unless the diagnostic already
    /// does.
    ///
    /// The "already does" test is the same word-boundary predicate the census
    /// grades with, applied to the same rendering the census grades: the
    /// Debug form (`{err:?}`). Since 2026-08-27 `clean check` prints the
    /// Display form (`crates/clean-cli/src/cmd_core.rs`, "THE SINGLE
    /// RENDERING SITE"); Debug carries every payload field Display can show,
    /// so a diagnostic that names its tactic in Display names it here too, and
    /// the predicate and the census gate keep grading one string. So an error
    /// carrying
    /// `tactic: "simp"` is returned untouched, and one carrying nothing is
    /// wrapped. Nothing is invented: the chain contains only tactics that
    /// really dispatched.
    fn attribute_tactic_failure(&self, err: ElabError) -> ElabError {
        if matches!(err, ElabError::InTactic { .. }) {
            // A nested `by` block already attributed this; re-wrapping would
            // bury the innermost (more precise) chain.
            return err;
        }
        let chain = self.tactic_trace.attribution_chain();
        let Some(innermost) = chain.last() else {
            // No tactic ever dispatched — e.g. an empty `by` block. There is
            // nothing to attribute to, and inventing one would be a fiction.
            return err;
        };
        let rendered = format!("{err:?}");
        if names_tactic(&rendered, &innermost.name) {
            return err;
        }
        ElabError::InTactic {
            tactic: innermost.name.clone(),
            chain: render_chain(chain),
            span_start: innermost.span.start,
            span_end: innermost.span.end,
            source: Box::new(err),
        }
    }

    fn elab_by_tactic_inner(&mut self, tactics: &[SurfaceTactic]) -> Result<Expr, ElabError> {
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
        // U2 stage 1a (entry): resolve SOLVED universe levels through the
        // ElabCtx metas before anything crosses the bridge. `instantiate`
        // substitutes expression metas only, so without `instantiate_levels`
        // the goal and the locals could carry a param the ElabCtx has already
        // solved (e.g. `u_0 := 1` from header elaboration) into a ProofState
        // that has no access to that solution — and, with the seeded rigid
        // set below, could not even re-derive it. Genuinely-unsolved params
        // (declared `.{u}`, still-abstract `Sort*` mints) pass through
        // unchanged, exactly as before.
        let target = tactic::simp::beta_reduce(
            &self
                .metas
                .instantiate_levels(&self.metas.instantiate(&target)),
        );

        // The locals cross the bridge under the SAME two-step instantiation the
        // target just had, and for the same reason. This used to run
        // `instantiate_levels` alone — the level half of the U2 stage-1a note
        // above — so a local whose TYPE is an EXPRESSION metavariable the
        // ElabCtx has already solved arrived at the ProofState still spelled as
        // the raw metavariable. An untyped binder is exactly that shape: in
        // `theorem id_tac {alpha} (x : alpha) : x = x := by rfl` the local
        // `alpha` has type `?α`, `?α := Sort ?v` is solved by the `(x : alpha)`
        // use before the block opens, and the block nevertheless received
        // `alpha : ?α`. The assembled proof then failed its kernel re-check
        // with `TypeMismatch { expected: Sort(?u_1), inferred: FVar(2^63) }` —
        // `2^63` being a metavariable wearing its fvar encoding. The TERM
        // spelling of the same theorem (`:= rfl`) never crossed this bridge and
        // always passed, which is what makes the gap a bridge gap and not an
        // elaboration one. `instantiate` substitutes only already-decided
        // values, so this is a no-op for every local that was already ground.
        let elab_locals: Vec<_> = self
            .locals
            .iter()
            .map(|(name, fvar, ty)| tactic::LocalDecl {
                binder_info: self.locals.binder_info(*fvar),
                fvar: *fvar,
                name: name.clone(),
                ty: self.metas.instantiate_levels(&self.metas.instantiate(ty)),
                value: self.locals.let_value(*fvar).map(|value| {
                    self.metas
                        .instantiate_levels(&self.metas.instantiate(value))
                }),
            })
            .collect();
        let mut ps = ProofState::with_instances_and_elab_context(
            self.env.clone(),
            target.clone(),
            self.instances.clone(),
            elab_locals.clone(),
        );
        // A `set_option tactic.customEliminators … in` the elaborator scoped
        // to this declaration lives in `local_options`, which the cloned
        // environment does not carry; `induction` reads the option from the
        // proof's environment.
        let custom_eliminators = tactic::custom_eliminator::CUSTOM_ELIMINATORS_OPTION;
        if let Some(value) = self.local_options.get(custom_eliminators) {
            ps.env
                .set_option(custom_eliminators.to_string(), value.clone());
        }

        // The ProofState owns a SEPARATE metavariable state, so an ENCLOSING
        // elaborator metavariable still open in the goal or a local's type —
        // `Nonempty ?α` faced by a `‹_›` deferred until the application around
        // it had been elaborated (`Function.surjective_comp_left_iff`,
        // measured 2026-09-11) — used to cross as a foreign id the tactic
        // checker could not type and no tactic could assign. Adopt each as a
        // ProofState metavariable (the `apply` bridge's translation), rewrite
        // the goal and the locals to the adopted ids, and hand the solutions
        // the block finds BACK through the inverse mapping below — Lean's
        // single `MetavarContext` in two steps. Universe levels stay as they
        // were (see the rigid seeding below).
        let mut bridge_mapping: HashMap<MetaId, MetaId> = HashMap::new();
        if contains_unassigned_meta_fvar(&target)
            || elab_locals.iter().any(|d| {
                contains_unassigned_meta_fvar(&d.ty)
                    || d.value.as_ref().is_some_and(contains_unassigned_meta_fvar)
            })
        {
            let translated_target = adopt_residual_elab_metas_into(
                &mut ps,
                &self.metas,
                &target,
                &mut bridge_mapping,
                "by",
            )
            .map_err(ElabError::from)?;
            let mut translated_locals = Vec::with_capacity(elab_locals.len());
            for decl in &elab_locals {
                let ty = adopt_residual_elab_metas_into(
                    &mut ps,
                    &self.metas,
                    &decl.ty,
                    &mut bridge_mapping,
                    "by",
                )
                .map_err(ElabError::from)?;
                let value = decl
                    .value
                    .as_ref()
                    .map(|value| {
                        adopt_residual_elab_metas_into(
                            &mut ps,
                            &self.metas,
                            value,
                            &mut bridge_mapping,
                            "by",
                        )
                    })
                    .transpose()
                    .map_err(ElabError::from)?;
                translated_locals.push(tactic::LocalDecl {
                    ty,
                    value,
                    ..decl.clone()
                });
            }
            // The new root must capture the translated local types too.
            // Scope snapshots prefer elab_locals over duplicate goal FVars;
            // leaving the old locals here captures foreign elaborator meta
            // IDs instead of their adopted ProofState identities.
            // Re-root the state on the translated goal; the original root
            // metavariable stays unassigned and unreferenced.
            // Install the translated enclosing scope before capturing the new
            // root: scope_snapshot gives enclosing locals precedence over the
            // visible goal context. Capturing first would retain foreign meta
            // IDs in local types and make the immutable scope disagree with
            // the translated goal as soon as a tactic tried to close it.
            ps.elab_locals = translated_locals.clone();
            let root = ps.fresh_meta_in_context(translated_target.clone(), &translated_locals);
            ps.root_meta_id = root;
            ps.goals.clear();
            ps.goals.push_front(tactic::Goal {
                meta_id: root,
                target: translated_target,
                local_ctx: translated_locals.clone(),
                tag: None,
                case_binders: Vec::new(),
            });
            ps.invalidate_tc_cache();
        }

        // Lean's auxiliary declarations (`LocalDecl.isAuxDecl`: a `mutual`
        // block's members while their bodies elaborate, a `let rec` /
        // `where` helper) are in the local context, but every tactic that
        // ENUMERATES hypotheses skips them — `assumption`, `simp_all`,
        // `simp [*]`, `contradiction`, omega's and linarith's collection,
        // `exact?`, `aesop` (brick B6 of
        // `designs/2026-10-08-mutual-nested-recursion.md`). They stay in the
        // proof state's scope, so a term that names one (`exact sibling x h`,
        // `simp [sibling]`) still elaborates — names resolve through this
        // elaborator's locals — and its proof still closes; they leave only
        // the goal's visible context, which is what those tactics read.
        if !self.aux_decl_locals.is_empty() {
            for goal in ps.goals.iter_mut() {
                goal.local_ctx
                    .retain(|decl| !self.aux_decl_locals.contains(&decl.fvar));
            }
        }

        // Thread the opened-namespace context so name-based tactics resolve
        // unqualified extra-lemma names through opened namespaces. After
        // `open Nat`, `simp [add_zero]` must reach `Nat.add_zero`, mirroring
        // the term elaborator's `resolve_identifier` order. Without this the
        // simp lemma lookup only tries the literal name and fails.
        ps.set_namespace_state(self.namespace_state.clone());
        ps.set_instance_visibility(self.instance_visibility());

        // U2 stage 1a — level identity across the ElabCtx↔ProofState bridge.
        // The ProofState must not re-mint a `u_N` name this declaration
        // already uses, and EVERY enclosing-declaration level name is rigid
        // inside the tactic block — declared `.{u}` because it is genuinely
        // fixed, and still-unsolved ElabCtx mints because the bridge has no
        // sound way to hand a tactic-side solution of them back (simp's
        // env-lemma path records constraints under lemmas' OWN declared
        // param names, so a write-back could silently monomorphize or
        // weaken the statement — the p30/p37 class; stage 3's mint registry
        // makes names UNIQUE, it does not make them provenance-carrying, so
        // this refusal is still the right posture). A tactic unification
        // that genuinely needs to solve an enclosing level therefore refuses
        // LOUDLY, never silently. See `ProofState::seed_universe_world`.
        // U2 stage 3 (2026-08-25): the counter is SHARED, not copied. Stage
        // 1a handed over a `u64` snapshot, which left both authorities
        // starting at the same value for the whole block — and a single
        // tactic STEP mints on both sides (its term arguments through this
        // ElabCtx, its lemma instances on the ProofState), so the first
        // mid-block mint on each side was the same string. Measured at HEAD
        // before the fix: `rw [pid_eq]` then `have hn := pid_eq 0` in one
        // block minted `u_3` on the ProofState and `u_3` on the ElabCtx —
        // two different levels, one name. One handle, one monotone counter,
        // no window.
        let mut tactic_rigid = self.metas.rigid_level_params_snapshot();
        for name in &self.universe_params {
            tactic_rigid.insert(name.name().clone());
        }
        // The level MINTS an adopted metavariable's goal mentions (`?u_1` in
        // `Nonempty.{?u_1} ?α`) are the levels the block must be free to solve
        // together with it — a declared `.{u}` stays rigid. Their solutions
        // are handed back below under the same guard as the expression
        // metavariables (only in terms of levels the elaborator knew at
        // entry), which is what makes solving them sound here where a
        // general write-back was not (see `seed_universe_world`).
        let entry_level_names: HashSet<Name> = tactic_rigid.clone();
        let mut bridge_levels: Vec<Name> = Vec::new();
        if !bridge_mapping.is_empty() {
            let mut names = Vec::new();
            if let Some(goal) = ps.current_goal() {
                crate::level_params::collect_level_params_from_expr(&goal.target, &mut names);
                for decl in &goal.local_ctx {
                    crate::level_params::collect_level_params_from_expr(&decl.ty, &mut names);
                }
            }
            // An adopted expression meta can hide its universe in its TYPE,
            // even when the visible goal and local type are just meta FVars.
            for ps_id in bridge_mapping.values() {
                if let Some(meta) = ps.metas.get(*ps_id) {
                    let ty = ps.metas.instantiate_levels(&ps.metas.instantiate(&meta.ty));
                    crate::level_params::collect_level_params_from_expr(&ty, &mut names);
                }
            }
            for name in names {
                if crate::level_mint::is_reserved_level_name(&name.to_string())
                    && !self.metas.is_rigid_level_param(&name)
                    && tactic_rigid.remove(&name)
                    && !bridge_levels.contains(&name)
                {
                    bridge_levels.push(name);
                }
            }
        }
        ps.seed_universe_world(
            self.universe_params.clone(),
            self.level_mint.clone(),
            tactic_rigid,
        );
        debug_assert!(
            ps.level_mint.shares_counter_with(&self.level_mint),
            "U2 stage 3: the bridge must hand the ProofState this ElabCtx's mint handle"
        );

        // Populate ProofState with elaborator-scope FVars (#2212).
        // When a theorem has parameters (e.g., `theorem t (A : Prop) (a : A) : A`),
        // the elaborator creates FVars for those parameters. The ProofState
        // TypeChecker needs these to type-check proof terms that reference them
        // (e.g., `exact a` resolves to FVar(1) from the elaborator).
        // `with_instances_and_elab_context` also seeds Goal.local_ctx so tactic
        // hypothesis lookup (rw, conv, etc.) sees theorem parameters.

        if let (Some(capture), Some(block), Some(first)) = (
            self.tactic_goal_capture.as_ref(),
            self.tactic_goal_block,
            tactics.first(),
        ) {
            if let Some(range) = block
                .range
                .filter(|range| range.start < first.span().start && first.span().start <= range.end)
            {
                capture.record(
                    block,
                    tactic::TacticGoalObservationKind::ByPrefix,
                    false,
                    tactic::TacticPostSnapshotRange {
                        start: range.start,
                        end: first.span().start,
                    },
                    Box::new(ps.clone()),
                    None,
                );
            }
        }
        // The two sides of the bridge must agree on which enclosing levels
        // are fixed. Otherwise term elaboration may rename an enclosing ?u
        // onto a fresh function level ?v, while ProofState still holds ?u as
        // rigid. Even a valid `cases h : pick xs i` then has incompatible
        // universes in its scrutinee and its original local context.
        let elaborator_rigid = self.metas.rigid_level_params_snapshot();
        let temporary_rigid: Vec<Name> = ps
            .metas
            .rigid_level_params_snapshot()
            .difference(&elaborator_rigid)
            .cloned()
            .collect();
        for name in &temporary_rigid {
            self.metas.add_rigid_level_param(name.clone());
        }
        let classical_saved = self.classical_tactic_scope;
        let run = tactics.iter().try_for_each(|tac| {
            self.enter_classical_if_opener(&mut ps, tac);
            self.eval_tactic(&mut ps, tac)
        });
        self.leave_classical_scope(&mut ps, classical_saved);
        // Restore on success and failure, removing only our temporary names.
        // Rigidity introduced by nested elaboration must survive this scope.
        if !temporary_rigid.is_empty() {
            let mut rigid = self.metas.rigid_level_params_snapshot();
            for name in temporary_rigid {
                rigid.remove(&name);
            }
            self.metas.restore_rigid_level_params(rigid);
        }
        run?;

        // Hand back the solutions the block found for the ENCLOSING
        // elaborator metavariables it adopted (see `bridge_mapping` above) —
        // levels first, since assigning `?α := α` checks `Sort ?u_1` against
        // `Sort u`. A solution that mentions a tactic-minted metavariable or
        // level cannot cross back and is left where it is — the proof below
        // then fails its re-check loudly, exactly as before.
        for name in &bridge_levels {
            let level = clean_kernel::Level::param(name.clone());
            let solution = ps.metas.instantiate_level(&level);
            if solution == level {
                continue;
            }
            let mut mentioned = Vec::new();
            solution.collect_params(&mut mentioned);
            if mentioned.iter().all(|p| entry_level_names.contains(p)) {
                let _ = self.metas.add_level_constraint(name.clone(), solution);
            }
        }
        let inverse: HashMap<MetaId, MetaId> =
            bridge_mapping.iter().map(|(e, p)| (*p, *e)).collect();
        for (elab_id, ps_id) in &bridge_mapping {
            let Some(value) = ps.metas.get(*ps_id).and_then(|m| m.assignment.clone()) else {
                continue;
            };
            let value = ps.metas.instantiate_levels(&ps.metas.instantiate(&value));
            let mut back = MetaFVarRemapper {
                mapping: &inverse,
                unmapped: Vec::new(),
            };
            let value = back.fold_expr(&value);
            if back.unmapped.is_empty() {
                let _ = self.metas.assign(*elab_id, value);
            }
        }

        match ps.closed_proof() {
            Some(proof) => {
                // Adopted metavariables the block left OPEN still wear their
                // ProofState ids in the proof; spell them as the elaborator's
                // own again so the checks below (and any later unification)
                // see one metavariable, not a stranger.
                let proof = if inverse.is_empty() {
                    proof
                } else {
                    let mut back = MetaFVarRemapper {
                        mapping: &inverse,
                        unmapped: Vec::new(),
                    };
                    back.fold_expr(&proof)
                };
                // U2 stage 1 exit path (§1.3 item 5 of the plan): realize the
                // levels the TACTIC side solved before the ElabCtx ever looks
                // at the proof. Level solutions recorded only in `ps.metas`
                // (e.g. a rewrite lemma's fresh param unified with the goal's
                // level) are invisible to `self.metas`, so without this the
                // returned proof still carries raw tactic-minted params and
                // `verify_tactic_proof` / the decl-close kernel re-check
                // correctly reject it — the measured sub-class A face.
                let proof = ps.metas.instantiate_levels(&proof);
                // U2 stage 3: no counter copy-back is needed or possible —
                // the ProofState minted from THIS ElabCtx's counter, so its
                // ids are already spent here. (Stage 1a raised `next_universe`
                // to `max(self, ps)` at this point; with one shared counter
                // that assignment is the identity.) The NAMES still have to
                // be merged: `finalize_level_params` generalizes over
                // `self.universe_params`, and a param the tactic minted and
                // left abstract in the proof must appear there.
                for name in &ps.universe_params {
                    if !self.universe_params.contains(name) {
                        self.universe_params.push(name.clone());
                    }
                }
                // Deliberately NO write-back of tactic-side level solutions
                // into the ElabCtx: every enclosing name is rigid inside the
                // block (above), so `ps.metas` can only have solved
                // TACTIC-MINTED params, and those are fully realized into the
                // proof by the `instantiate_levels` call just before this.
                // (A general flush was drafted and rejected: simp's
                // env-lemma path records constraints under lemmas' own
                // declared param names, and importing those into the
                // declaration's world could silently monomorphize or weaken
                // the statement — the p30/p37 class.)
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
                    // Private constants by their user-facing names, as
                    // Lean 4.8.0 prints an unsolved goal (G21).
                    let shown = crate::private_names::user_facing_expr;
                    for goal in goals.iter().take(5) {
                        for decl in &goal.local_ctx {
                            detail.push_str(&format!("\n{} : {}", decl.name, shown(&decl.ty)));
                        }
                        detail.push_str(&format!("\n⊢ {}", shown(&goal.target)));
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
                        expected: format!("{target_inst}"),
                        actual: format!("{proof_ty}"),
                    });
                }
                Ok(())
            }
            Err(e) => {
                let target_inst = self.metas.instantiate(target);
                Err(ElabError::ProofTypeMismatch {
                    expected: format!("{target_inst}"),
                    actual: format!("ill-typed: {e}"),
                })
            }
        }
    }

    /// Elaborate a term for the tactic bridge, reporting the metavariables
    /// its elaboration left open (`pending_goals`, with the locals each one
    /// captured beyond the goal's context — binders the term itself opened,
    /// never an enclosing local the goal no longer holds) so the proof state can import
    /// them. `Goal` elaborates against the goal target — `refine` — and
    /// `Open` with no expected type — a `rw` rule, whose type is an equation
    /// the goal has nothing to say about.
    fn elaborate_bridged_term(
        &mut self,
        goal: &tactic::Goal,
        expr: &SurfaceExpr,
        target: BridgedTermTarget,
    ) -> Result<ElaboratedRefine, ElabError> {
        let existing: HashSet<_> = self.metas.iter().map(|(id, _)| id).collect();
        // The ElabCtx locals the term was elaborated UNDER (as opposed to
        // binders its own elaboration opened, which a pending metavariable
        // legitimately captures).
        let enclosing: HashSet<FVarId> = self.locals.iter().map(|(_, fvar, _)| *fvar).collect();
        let term = match target {
            BridgedTermTarget::Goal => {
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
                term
            }
            BridgedTermTarget::Open => self.elaborate_with_expected_type(expr, None)?,
        };

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
                // An enclosing local the goal does not hold is not the term's
                // own: either an outer elaborator local, which the final proof
                // binds anyway, or a hypothesis a tactic consumed since the
                // block began (`rcases h with ⟨f, hf : a = _⟩` removes `h`,
                // then elaborates `a = _`; `cases h` on `h : .ok (a, s) = .ok
                // (ids, s')` clears `h` and substitutes `ids` and `s'`). Lean
                // elaborates the term in the goal's own context, so its holes
                // never see one. Capturing one minted a fresh tactic fvar for
                // it: an OPEN term's finished proof was refused
                // ("ProofNotProduced"), and `refine ⟨?_, ?_⟩`'s holes revived
                // the consumed locals under fresh ids outside the goal's
                // creation scope ("assignment violates its creation scope",
                // `Sem.bindFreshPair_ok` in trust-ir's `Semantics/Monad.lean`).
                let locals = meta
                    .locals
                    .iter()
                    .filter(|(_, fvar, _)| !goal_fvars.contains(fvar))
                    .filter(|(_, fvar, _)| !enclosing.contains(fvar))
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

    /// Push `goal`'s locals that ElabCtx does not hold yet, so a term
    /// elaborated for a tactic resolves the goal's hypotheses by name. The
    /// caller truncates `self.locals` and pops `self.local_instances` back
    /// afterwards.
    fn push_goal_locals(&mut self, goal: &tactic::Goal) -> Vec<(usize, SurfaceName)> {
        // #2529: Deduplicate — after the bridge fix, theorem parameters
        // appear in both ElabCtx.locals and goal.local_ctx. Pushing
        // duplicates would create identical entries that confuse name
        // resolution.
        //
        // A local already bridged under ANOTHER name is renamed in place for
        // this tactic (gap G66), and the caller restores the old name with
        // [`Self::restore_bridged_names`]: a compound tactic (`·`, `case`,
        // `next`) bridges its goal's locals once for its whole block, so a
        // local the block then renames (`rename_i x`, `case succ m =>`
        // naming a field, an older local a new one shadows) was visible to
        // the block's terms under its old name only ("Unknown identifier:
        // m"). Bridging it a second time is not an option: the kernel local
        // context refuses a duplicate free variable.
        let existing: HashMap<FVarId, usize> = self
            .locals
            .iter()
            .enumerate()
            .map(|(index, (_, fvar, _))| (*fvar, index))
            .collect();
        let existing_instances: HashSet<FVarId> =
            self.local_instances.iter().map(|(fvar, _)| *fvar).collect();
        let mut renamed = Vec::new();
        for decl in &goal.local_ctx {
            if let Some(&index) = existing.get(&decl.fvar) {
                if self.locals[index].0 != decl.name {
                    if let Some(old) = self.locals.rename(index, decl.name.clone()) {
                        renamed.push((index, old));
                    }
                }
                continue;
            }
            // A class-typed local a TACTIC introduced (`have : Inhabited α
            // := …`, `intro inst`, `inhabit α`) is a local instance, as
            // Lean's `withNewLocalInstances` makes every introduced local
            // whose type is a class (`Lean/Meta/Tactic/Intro.lean`);
            // declaration binders already were (class (4)). Measured
            // 2026-09-12: `have : Inhabited α := …; exact ⟨default⟩`
            // failed to synthesize `Inhabited α`.
            if !existing_instances.contains(&decl.fvar)
                && self.binder_is_local_instance(BinderInfo::Default, &decl.ty)
            {
                self.push_local_instance(decl.fvar, decl.ty.clone());
            }
            // Retain raw values in both directions of the bridge. ElabCtx's
            // full and demand-driven reduction views hide marked have proofs;
            // scope snapshots and nested tactic blocks must still keep them.
            match decl.value.as_ref() {
                Some(value) => self.push_local_let_with_fvar(
                    decl.name.clone(),
                    decl.fvar,
                    decl.ty.clone(),
                    value.clone(),
                ),
                None => self.push_local_with_fvar(decl.name.clone(), decl.fvar, decl.ty.clone()),
            }
            self.locals.set_binder_info(decl.fvar, decl.binder_info);
            // Retain the existing conservative let-rec lifting policy.
            self.note_let_rec_unknown_binder(decl.fvar);
        }
        renamed
    }

    /// Undo [`Self::push_goal_locals`]' in-place renames, innermost first; the
    /// renamed entries precede every local it pushed, so this may run before
    /// or after the caller truncates those.
    fn restore_bridged_names(&mut self, renamed: Vec<(usize, SurfaceName)>) {
        for (index, old) in renamed.into_iter().rev() {
            self.locals.rename(index, old);
        }
    }

    /// `infer_instance` is Lean's `exact inferInstance` (`Init/Tactics.lean`:
    /// ``macro "infer_instance" : tactic => `(tactic| exact inferInstance)``):
    /// elaborate the term `inferInstance` against the goal — the real
    /// resolver, with its sub-goals, local instances, telescopes and
    /// alias-goal opening — and close the goal with it.
    ///
    /// The bare tactic handler (`tactic::pattern::infer_instance`) never
    /// called the resolver: it took the goal's head as the class, scanned
    /// only binder-free instances of that exact head, and finally GUESSED
    /// constant names (`inst{Class}`), returned bare with no universe levels
    /// or arguments. So `Classical.decPred := by infer_instance`
    /// (`Mathlib/Logic/Basic.lean`, `DecidablePred p` under `namespace
    /// Classical`) failed where `by exact inferInstance` reached further, and
    /// `Classical.dec` died on `Level count mismatch for instDecidable`.
    ///
    /// `None` when the resolver finds no instance: the caller then runs the
    /// bare handler's synthesizers as a FALLBACK (they cover prelude
    /// environments with no registered `Decidable True`/`Inhabited Nat`
    /// instance; the kernel re-checks what they build). Once the term is
    /// elaborated its `exact` verdict is final — a failed `exact` may have
    /// touched the proof state, so it is reported, never retried.
    fn infer_instance_via_resolver(
        &mut self,
        ps: &mut ProofState,
        span: clean_parser::Span,
    ) -> Option<Result<(), ElabError>> {
        let goal = ps.current_goal().cloned()?;
        let saved_expected = self.current_expected_type.clone();
        // A failed elaboration must not leave its metavariable writes behind
        // for the fallback (or the rest of the declaration) to trip over.
        self.metas.push_scope();
        let term = self.elaborate_exact_term(
            &goal,
            &SurfaceExpr::Ident(span, SurfaceName::global_path("inferInstance")),
        );
        self.current_expected_type = saved_expected;
        let Ok(term) = term else {
            self.metas.pop_scope();
            return None;
        };
        self.metas.commit();
        Some(tactic::exact(ps, term).map_err(ElabError::from))
    }

    /// The `Nonempty α` proof `inhabit α` needs, from the REAL resolver.
    ///
    /// Mathlib's `evalInhabit` (`Mathlib/Tactic/Inhabit.lean`) is
    /// `let nonempty_e_pf ← synthInstance (Nonempty e)` followed by
    /// `nonempty_to_inhabited` / `nonempty_prop_to_inhabited`, so a GLOBAL
    /// `instance : Nonempty Foo`, a parametric instance and a local
    /// `[Nonempty α]` binder all answer it. The bare handler
    /// (`tactic::inhabit`) has no resolver and scanned the goal's locals only,
    /// so `inhabit Foo` with the instance registered globally failed `no
    /// instance in scope`. The search runs here — the goal's locals and local
    /// instances are already bridged into this context by
    /// [`Self::eval_tactic_inner`] — and the proof is handed to the handler,
    /// which re-checks its type before using it.
    ///
    /// `None` when the search finds nothing or leaves a metavariable open: the
    /// handler then falls back to its local scan and fails closed.
    fn synthesize_inhabit_witness(&mut self, alpha: &Expr) -> Option<Expr> {
        let alpha = self.metas.instantiate(alpha);
        let sort = self.infer_type(&alpha).ok()?;
        let sort = self.whnf(&sort);
        let ExprKind::Sort(level) = sort.kind() else {
            return None;
        };
        let nonempty = Expr::app(
            Expr::const_(Name::anon().str("Nonempty"), vec![level.clone()]),
            alpha,
        );
        // A failed or open search must not leave its metavariable writes
        // behind for the handler's fallback.
        self.metas.push_scope();
        let witness = self.resolve_instance(&nonempty).map(|found| {
            let found = self.metas.instantiate(&found);
            self.metas.instantiate_levels(&found)
        });
        match witness {
            Some(found) if !self.has_metavars(&found) => {
                self.metas.commit();
                Some(found)
            }
            _ => {
                self.metas.pop_scope();
                None
            }
        }
    }

    /// Evaluate a single `SurfaceTactic` against the proof state, recording it
    /// on the attribution trace.
    ///
    /// The trace push/pop lives here rather than inside
    /// [`Self::eval_tactic_inner`] because that function returns early through
    /// `?` in several arms; wrapping it is the only way the stack is
    /// guaranteed to unwind on every path.
    pub(super) fn eval_tactic(
        &mut self,
        ps: &mut ProofState,
        tac: &SurfaceTactic,
    ) -> Result<(), ElabError> {
        let head_span = tac.span();
        let capture = self
            .tactic_goal_capture
            .clone()
            .zip(self.tactic_goal_block)
            .filter(|_| head_span.start < head_span.end);
        // Named tactic spans identify their head for attribution. Observation
        // alone covers the actual parsed arguments, including nested terms.
        let span = if capture.is_some() || self.term_info_capture.is_some() {
            let end = match tac {
                SurfaceTactic::Named { args, .. } => args
                    .iter()
                    .map(observation_term_end)
                    .fold(head_span.end, usize::max),
                SurfaceTactic::Term(_, term) => head_span.end.max(observation_term_end(term)),
                _ => head_span.end,
            };
            clean_parser::Span {
                start: head_span.start,
                end,
            }
        } else {
            head_span
        };
        let before = capture.as_ref().map(|_| Box::new(ps.clone()));
        let intro_before = self.intro_info_before(ps, tac);
        let info_frame = self.begin_tactic_info(span);
        let depth = self.tactic_trace.depth();
        let entered = self.tactic_trace.enter(tac);
        let result = self.eval_tactic_inner(ps, tac);
        if result.is_ok() {
            self.capture_intro_binders(ps, tac, intro_before.as_ref());
        }
        self.end_tactic_info(info_frame, result.is_err());
        if entered {
            self.tactic_trace.leave(depth, result.is_err());
        }
        if let (Some((capture, block)), Some(before)) = (capture, before) {
            capture.record(
                block,
                tactic::TacticGoalObservationKind::Tactic,
                matches!(
                    tac,
                    SurfaceTactic::Rw(..) | SurfaceTactic::Rewrite(..) | SurfaceTactic::Rwa(..)
                ),
                tactic::TacticPostSnapshotRange {
                    start: span.start,
                    end: span.end,
                },
                before,
                result.is_ok().then(|| Box::new(ps.clone())),
            );
        }
        result
    }

    /// [`Self::eval_tactic_inner_body`] with the declaration binders the
    /// current goal no longer holds hidden from every term the tactic
    /// elaborates (`elab_tactic_consumed`). The binders are restored whatever
    /// the body returns, including its early `?` exits.
    fn eval_tactic_inner(
        &mut self,
        ps: &mut ProofState,
        tac: &SurfaceTactic,
    ) -> Result<(), ElabError> {
        let hidden = match ps.current_goal().cloned() {
            Some(goal) => self.hide_consumed_binders(ps, &goal),
            None => None,
        };
        let result = self.eval_tactic_inner_body(ps, tac);
        if let Some(hidden) = hidden {
            self.restore_hidden_binders(hidden);
        }
        result
    }

    /// The dispatch body of [`Self::eval_tactic`] (under [`Self::eval_tactic_inner`]).
    ///
    /// Pushes the current goal's local context into ElabCtx before
    /// dispatching, so ALL tactic sub-methods that call `self.elaborate()`
    /// can resolve tactic-introduced hypotheses. This is the ProofState →
    /// ElabCtx bridge (#2212). Locals are popped after dispatch (even on
    /// error).
    fn eval_tactic_inner_body(
        &mut self,
        ps: &mut ProofState,
        tac: &SurfaceTactic,
    ) -> Result<(), ElabError> {
        // Push tactic-local declarations into ElabCtx for name resolution.
        // Without this, `intro h; exact h` (or `have`, `change`, `calc`,
        // etc.) would resolve `h` as auto-implicit instead of the FVar
        // introduced by the tactic.
        let locals_before = self.locals.len();
        let local_instances_before = self.local_instances.len();
        let renamed = match ps.current_goal() {
            Some(goal) => {
                let goal = goal.clone();
                self.push_goal_locals(&goal)
            }
            None => Vec::new(),
        };

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
            | SurfaceTactic::Rewrite(..)
            | SurfaceTactic::Rwa(..)
            | SurfaceTactic::Simp { .. }
            | SurfaceTactic::SimpRw(..)
            | SurfaceTactic::Simpa { .. }
            | SurfaceTactic::Have(..)
            | SurfaceTactic::Let(..)
            | SurfaceTactic::Suffices(..)
            | SurfaceTactic::Replace(..)
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
                    .ok_or_else(|| ElabError::from(self.tactic_registry.unknown_tactic(name)))?;
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

            SurfaceTactic::Named { span, name, args } => {
                let via_resolver = if name == "infer_instance" && args.is_empty() {
                    self.infer_instance_via_resolver(ps, *span)
                } else {
                    None
                };
                if let Some(result) = via_resolver {
                    result
                } else if name == "refine" {
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
                    let refined =
                        self.elaborate_bridged_term(&goal, arg, BridgedTermTarget::Goal)?;
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
                        // `BracketedParamList` joins the ident patterns: a
                        // `grind [foo]` parameter is a lemma NAME, not a term
                        // to elaborate against the goal — elaborating one
                        // would insert implicit arguments and mint metas that
                        // nothing solves, and the tactic only ever reads the
                        // name back.
                        let is_ident_pattern = matches!(
                            entry.pattern,
                            TacticArgPattern::IdentList
                                | TacticArgPattern::NonemptyIdentList
                                | TacticArgPattern::BracketedParamList
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
                                // `generalize (h :)? e = x (at loc)?`: slot 1 is
                                // the new variable `x`; the optional slot 2 is
                                // the hypothesis name `h` (the `h : e = x`
                                // form, `_` when a location follows without
                                // one). Neither is in scope yet, so both pass
                                // through as bare `Const`s (read back via
                                // `expr_to_hyp_name`) rather than being
                                // elaborated as terms. The location slots
                                // after them name hypotheses (or `⊢` / `*`),
                                // read back by name exactly as the
                                // location-taking tactics read theirs.
                                "generalize" => idx >= 1,
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
                                                return Ok(tactic::registry::encode_name_argument(
                                                    ident_name,
                                                ));
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
                                            return Ok(tactic::registry::encode_name_argument(
                                                &SurfaceName::generated_path("_"),
                                            ));
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
                                                // A notation or macro template's
                                                // FREE name (not a section
                                                // variable) denotes what it named
                                                // where the template was declared
                                                // (Lean's `kh✝`): that global, or
                                                // nothing — never a use-site
                                                // hypothesis, which its marks keep
                                                // it from matching.
                                                if let Some(origin) = ident_name
                                                    .template_origin_arc()
                                                    .filter(|origin| !origin.section_variable)
                                                    .filter(|_| {
                                                        ident_name.template_scope().is_none()
                                                    })
                                                {
                                                    let resolved = match self
                                                        .resolve_global_ident_target(ident_name)
                                                    {
                                                        IdentTarget::Global(global) => {
                                                            SurfaceName::from_name(global)
                                                        }
                                                        _ => SurfaceName::unspellable(
                                                            "_unresolved_template_name",
                                                            0,
                                                        ),
                                                    };
                                                    return Ok(
                                                        tactic::registry::encode_name_argument(
                                                            &resolved.with_template_origin(
                                                                std::sync::Arc::clone(origin),
                                                            ),
                                                        ),
                                                    );
                                                }
                                                // Try namespace-qualified name first when
                                                // inside a namespace block and the bare name
                                                // is not a known constant. This allows
                                                // `unfold land` to find `Int.land` inside
                                                // `namespace Int`. Part of #3396.
                                                if !self.namespace_prefix.is_anonymous() {
                                                    let bare = ident_name.name().clone();
                                                    if self.env.get_const(&bare).is_none() {
                                                        let qualified =
                                                            self.qualify_name(ident_name);
                                                        let qname = qualified.name().clone();
                                                        if self.env.get_const(&qname).is_some() {
                                                            return Ok(
                                                            tactic::registry::encode_name_argument(
                                                                &qualified,
                                                            ),
                                                        );
                                                        }
                                                    }
                                                }
                                                return Ok(tactic::registry::encode_name_argument(
                                                    ident_name,
                                                ));
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
                        } else if name == "inhabit" && elaborated.len() == 1 {
                            // `inhabit α`: Mathlib's `synthInstance (Nonempty
                            // α)`, run through the real resolver.
                            let mut elaborated = elaborated;
                            if let Some(witness) = self.synthesize_inhabit_witness(&elaborated[0]) {
                                elaborated.push(witness);
                            }
                            elaborated
                        } else {
                            elaborated
                        };
                        (entry.handler)(ps, &elaborated).map_err(ElabError::from)
                    } else if let Some(expansion) = args
                        .is_empty()
                        .then(|| self.imported_tactic_macro(name))
                        .flatten()
                    {
                        // An imported zero-argument `macro "kw" : tactic` —
                        // class (11): `compareOfLessAndEq_rfl`, the autoParam
                        // of every `LinearOrder` instance (`imported_tactic_macro`).
                        self.eval_imported_tactic_macro(ps, name, &expansion)
                    } else {
                        Err(self.tactic_registry.unknown_tactic(name).into())
                    }
                }
            }
        };

        // Pop tactic locals (even on error). `LocalBindings::truncate` drops
        // the let-value side-channel entries for the popped fvars in
        // lock-step so a `let`-local's value cannot leak into a later,
        // unrelated tactic's term elaboration.
        self.locals.truncate(locals_before);
        self.restore_bridged_names(renamed);
        while self.local_instances.len() > local_instances_before {
            self.pop_local_instance();
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

/// Application nodes retain their function's attribution span. Observation
/// ranges also include their actual parsed arguments, without changing spans
/// used by elaboration or constructing any proof-state context from syntax.
fn observation_term_end(expr: &SurfaceExpr) -> usize {
    let mut end = expr.span().end;
    let mut pending = vec![expr];
    while let Some(term) = pending.pop() {
        end = end.max(term.span().end);
        if let SurfaceExpr::App(_, head, args) = term {
            pending.push(head);
            pending.extend(args.iter().map(|arg| &arg.expr));
        }
    }
    end
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
        SurfaceTactic::Replace(..) => Some("replace"),
        SurfaceTactic::Obtain { .. } => Some("obtain"),
        SurfaceTactic::RCases { .. } => Some("rcases"),
        SurfaceTactic::RIntro { .. } => Some("rintro"),
        SurfaceTactic::Match(..) => Some("match"),
        SurfaceTactic::Conv(..) => Some("conv"),
        SurfaceTactic::ConvArg(..) => Some("conv_arg"),
        SurfaceTactic::ConvEnter(..) => Some("conv_enter"),
        // Wave 3D.3: rewrite/simp
        SurfaceTactic::Rw(..) => Some("rw"),
        SurfaceTactic::Rewrite(..) => Some("rewrite"),
        SurfaceTactic::Rwa(..) => Some("rwa"),
        SurfaceTactic::Simp { all: true, .. } => Some("simp_all"),
        SurfaceTactic::Simp { all: false, .. } => Some("simp"),
        SurfaceTactic::SimpRw(..) => Some("simp_rw"),
        SurfaceTactic::Simpa { .. } => Some("simpa"),
        // Wave 3D.4: cases/induction
        SurfaceTactic::Cases(..) => Some("cases"),
        SurfaceTactic::Induction { .. } => Some("induction"),
        _ => None,
    }
}
