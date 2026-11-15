// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic registry for extensible tactic dispatch.
//!
//! Provides [`TacticRegistry`] for registering tactic elaborators by name,
//! enabling programmatic registration of new tactics without modifying the
//! hardcoded `SurfaceTactic` enum or `eval_tactic` dispatch.
//!
//! # Architecture
//!
//! The registry stores [`TacticEntry`] values keyed by tactic name. Each entry
//! includes an argument pattern (for parser-level argument parsing) and a
//! handler function that receives the proof state and elaborated arguments.
//!
//! The elaboration of raw `SurfaceExpr` arguments into kernel `Expr` values
//! is handled by the dispatch site in `eval_tactic`, not by the handler itself.
//! This keeps handlers simple and avoids lifetime entanglement with `ElabCtx`.

use std::collections::HashMap;
use std::sync::Arc;

use super::{ProofState, TacticError};
use crate::unify::{MetaId, MetaState};
use clean_kernel::Expr;
use clean_kernel::FVarId;
use clean_parser::{SurfaceExpr, SurfaceName, SurfaceTactic};

mod name_argument;
pub use name_argument::{decode_name_argument, encode_name_argument};

// Re-export TacticArgPattern from the parser crate where it is canonically defined.
// The parser owns this type because it controls how arguments are parsed.
pub use clean_parser::TacticArgPattern;
pub use clean_parser::TacticPatterns;

/// Extra local visible to a pending refine goal that was created by elaboration.
#[derive(Debug, Clone)]
pub struct RefinePendingLocal {
    pub name: SurfaceName,
    pub fvar: FVarId,
    pub ty: Expr,
}

/// Pending goal produced while elaborating a refine term.
#[derive(Debug, Clone)]
pub struct RefinePendingGoal {
    pub meta_id: MetaId,
    pub locals: Vec<RefinePendingLocal>,
    /// Name of the `?name` synthetic hole this goal came from, if any. Threaded
    /// into the tactic goal's `tag` by the refine bridge so `case name => …` can
    /// select it. `None` for anonymous holes (`_`, `?`, `?_`).
    pub tag: Option<SurfaceName>,
}

/// Result of elaborating a refine expression against the current goal.
#[derive(Debug, Clone)]
pub struct ElaboratedRefine {
    pub term: Expr,
    pub pending_goals: Vec<RefinePendingGoal>,
}

/// A registered tactic handler.
///
/// Takes a mutable proof state and pre-elaborated arguments. The dispatch
/// site in `eval_tactic` elaborates raw `SurfaceExpr` arguments into `Expr`
/// before calling the handler.
pub type TacticHandler =
    Arc<dyn Fn(&mut ProofState, &[Expr]) -> Result<(), TacticError> + Send + Sync>;

/// A value produced by running a value-yielding tactic, read out of the proof
/// state *after* the tactic ran its normal kernel-checked effect.
///
/// # Metaprogramming Phase 7
///
/// The tactic monad does not return values (`eval`/`eval_seq` return
/// `Result<(), TacticError>`). A `do`-block bind `let x <- tac` therefore needs a
/// principled way to recover what `tac` produced. [`TacticEval::eval_returning`]
/// runs the tactic and then *reads* the produced value out of the (already
/// mutated, kernel-checked) [`ProofState`] — it never fabricates a value or a
/// goal-closing effect.
///
/// The value is carried as a [`SurfaceExpr`] so the existing
/// substitute-and-delegate user-tactic pipeline can thread it into later
/// statements (`exact x`) exactly like any other binding. Only values that are
/// representable as surface syntax are produced here; tactics whose result has
/// no surface representation (a raw goal/target term) yield `None` and the
/// caller defers honestly.
#[derive(Debug, Clone)]
pub enum BoundValue {
    /// A hypothesis the tactic introduced into the local context, identified by
    /// its actual (post-`intro`) name. Threaded as the `Ident` that names it, so
    /// a later `exact x` resolves the same hypothesis.
    Hyp {
        name: SurfaceName,
        ident: SurfaceExpr,
    },
}

impl BoundValue {
    /// The surface expression this value substitutes into later `do` statements.
    #[must_use]
    pub(crate) fn as_surface(&self) -> &SurfaceExpr {
        match self {
            BoundValue::Hyp { ident, .. } => ident,
        }
    }

    /// The name the value is known by (e.g. the introduced hypothesis name for
    /// [`BoundValue::Hyp`]).
    #[must_use]
    pub fn name(&self) -> &SurfaceName {
        match self {
            BoundValue::Hyp { name, .. } => name,
        }
    }
}

/// Callback trait for compound tactic handlers that need recursive tactic
/// evaluation and expression elaboration. Provided by the dispatch site
/// (`ElabCtx::eval_tactic`) at call time, avoiding a direct dependency on
/// `ElabCtx` (which would create a circular dependency with the registry).
///
/// Phase 3D Wave 5 (#2440): `eval`/`eval_seq` enable compound tactics
/// (AllGoals, Try, etc.) to recursively evaluate sub-tactic sequences.
/// Phase 3D Wave 6 (#2440): `elaborate`/`infer_type` enable expression-
/// dependent compound tactics (Have, Let, Suffices, Match) to elaborate
/// surface expressions and infer types without direct `ElabCtx` access.
pub trait TacticEval {
    /// The file's explicit source world, if one was selected. Without one,
    /// world-sensitive tactics consult the proof environment before the oracle.
    fn source_world(&self) -> Option<clean_kernel::LeanWorld> {
        None
    }

    /// Evaluate a single tactic against the proof state.
    /// REQUIRES: `ps` is the proof state currently being elaborated for `tac`.
    /// REQUIRES: `tac` is a well-formed parser-produced tactic node.
    /// ENSURES: On Ok, all state changes from elaborating `tac` are reflected in `ps`.
    fn eval(&mut self, ps: &mut ProofState, tac: &SurfaceTactic) -> Result<(), TacticError>;

    /// Record that `tac` ran, without dispatching it.
    ///
    /// Failure **attribution** (`crates/clean-elab/src/infer/tactic_trace.rs`)
    /// is derived from the dispatch stack maintained by [`Self::eval`], so a
    /// handler that services a tactic *itself* instead of delegating would
    /// leave that tactic out of the chain and the resulting diagnostic would
    /// name its parent. `run_conv_body`'s conv-mode `congr` interception is
    /// the one such site; it calls this so the chain still reads
    /// ``` `conv` > `congr` ```.
    ///
    /// Diagnostic only: the default implementation is a no-op, and no
    /// evaluator's proof-producing behaviour depends on it.
    fn note_tactic(&mut self, _tac: &SurfaceTactic) {}

    /// Record the binder names of a hypothesis a tactic introduced with a `∀`
    /// type written in place (`have h : ∀ {n m : Nat}, … := …`), so a later
    /// `h (n := a)` can bind by name: kernel terms keep no binder names, and
    /// Lean reads them off the local's type (`Lean/Elab/App.lean:803-815`).
    ///
    /// Names only select argument positions in a term the kernel re-checks;
    /// the default implementation records nothing, which leaves such a call
    /// the loud refusal it was.
    fn note_local_forall_binder_names(
        &mut self,
        _fvar: FVarId,
        _surface_ty: &SurfaceExpr,
        _ty: &Expr,
    ) {
    }

    /// Evaluate a sequence of tactics against the proof state.
    /// REQUIRES: each entry in `tacs` is well-formed tactic syntax for the current goal context.
    /// ENSURES: On Ok, `tacs` have been evaluated left-to-right against `ps`.
    fn eval_seq(&mut self, ps: &mut ProofState, tacs: &[SurfaceTactic]) -> Result<(), TacticError>;

    /// Elaborate a surface expression into a kernel expression.
    /// Phase 3D Wave 6: needed by Have, Let, Suffices, Match handlers.
    /// REQUIRES: `expr` is valid surface syntax for the active elaboration context.
    /// ENSURES: On Ok, the returned `Expr` is usable by tactic handlers in the same context.
    fn elaborate(&mut self, expr: &SurfaceExpr) -> Result<Expr, TacticError>;

    /// Elaborate a surface expression with NO expected type at all.
    ///
    /// [`TacticEval::elaborate`] leaves whatever expected type the enclosing
    /// TERM elaboration armed in place, because it is a bare
    /// `ElabCtx::elaborate`. That is right for a tactic argument the goal
    /// should type, and wrong for one Lean deliberately elaborates blind: a
    /// `cases`/`induction` target (`Lean/Elab/Tactic/Induction.lean`:895
    /// `elabTerm view.term none` and :1040 `elabTerm stx none`) and the value
    /// of an un-ascribed `have h := e`. Under a pattern lambda whose binder
    /// domain is `Subtype p`, `cases Subsingleton.elim x y` had
    /// `Subsingleton.elim`'s implicit carrier fixed to `Subtype p` before its
    /// explicit `x : α` was checked — `Mathlib/Logic/Basic.lean`'s
    /// `instance [Subsingleton α] (p) : Subsingleton (Subtype p)`.
    ///
    /// The default implementation falls back to [`TacticEval::elaborate`], so
    /// an evaluator without an expected-type channel (a unit-test stub) is
    /// unchanged rather than silently pretending to have cleared one.
    ///
    /// # Soundness
    ///
    /// Removing a hint can only make elaboration less determined, never more
    /// permissive: every term produced here is still typed by `infer_type` and
    /// re-checked by the kernel.
    fn elaborate_no_expected(&mut self, expr: &SurfaceExpr) -> Result<Expr, TacticError> {
        self.elaborate(expr)
    }

    /// Elaborate a surface expression against a known expected type.
    ///
    /// Threads `expected` as the elaboration goal so a polymorphic proof term —
    /// most importantly `rfl`, whose principal type `@Eq.refl ?α ?a` fixes
    /// nothing on its own — is solved against the ascribed type. This mirrors
    /// Lean's `have h : T := e`, which elaborates `e` with expected type `T`
    /// (`Lean.Elab.Term` `elabHaveCore` → `elabTermEnsuringType`), rather than
    /// bare `have h := e` (inferred). Without it, `have h : n + 0 = n := rfl`
    /// leaves `rfl`'s sides as unconstrained metavariables and the unifier
    /// reports a shape mismatch even for a closed, true equation.
    ///
    /// The default implementation ignores `expected` and falls back to
    /// [`TacticEval::elaborate`]; the real dispatch site (`ElabCtx`) overrides
    /// it to route through the elaborator's expected-type channel. An evaluator
    /// without that channel (a unit-test stub) therefore stays honest — it
    /// elaborates without the hint rather than fabricating one.
    ///
    /// # Soundness
    ///
    /// This only *seeds* the elaboration goal; it closes nothing and fabricates
    /// nothing. Every `have` branch still routes the elaborated term through the
    /// kernel-checked `have_`, which re-checks that the term has the recorded
    /// type, so a term whose type does not actually match `expected` still
    /// surfaces as a `TacticError`, never a silent over-accept.
    fn elaborate_expected(
        &mut self,
        expr: &SurfaceExpr,
        expected: &Expr,
    ) -> Result<Expr, TacticError> {
        let _ = expected;
        self.elaborate(expr)
    }

    /// Infer the type of a kernel expression.
    /// Phase 3D Wave 6: needed by Let handler (type inference fallback).
    /// REQUIRES: `expr` is well-formed in the current elaboration context.
    /// ENSURES: On Ok, the returned expression is the inferred type of `expr`.
    fn infer_type(&mut self, expr: &Expr) -> Result<Expr, TacticError>;

    /// Elaborate a `refine` expression against the current goal.
    /// ENSURES: On Ok, `term` is the elaborated proof term and `pending_goals`
    /// lists the resulting subgoals in the order the tactic framework should
    /// expose them.
    fn elaborate_refine(
        &mut self,
        ps: &ProofState,
        expr: &SurfaceExpr,
    ) -> Result<ElaboratedRefine, TacticError>;

    /// Elaborate a term with NO expected type — a rewrite rule (`rw [e]`) —
    /// reporting the metavariables its elaboration left open exactly as
    /// [`TacticEval::elaborate_refine`] does, so the caller can import them
    /// into the proof state (`import_open_term`) and solve them against the
    /// goal. The default is a plain [`TacticEval::elaborate`] with nothing
    /// pending, for an evaluator that has no elaborator metavariable state.
    fn elaborate_open(
        &mut self,
        ps: &ProofState,
        expr: &SurfaceExpr,
    ) -> Result<ElaboratedRefine, TacticError> {
        let _ = ps;
        Ok(ElaboratedRefine {
            term: self.elaborate(expr)?,
            pending_goals: Vec::new(),
        })
    }

    /// Get the elaborator metavariable state backing refined proof terms.
    /// ENSURES: Returned metas contain the pending metavariables referenced by
    /// results from `elaborate_refine` and `elaborate_open`.
    fn metas(&self) -> &MetaState;

    /// Metaprogramming Phase 8: bind `name` to an already-elaborated kernel
    /// `Expr` value in the elaborator's *value channel*, so a later body
    /// position referencing `name` splices the stored term directly (the B78
    /// `meta_value_bindings` mechanism, consulted first by `elab_ident`).
    ///
    /// Used by the tactic do-block executor to make a goal-query value (e.g.
    /// `let g := getMainTarget`, which reads `ps.current_goal().target`)
    /// available to a later statement (`exact g`). The value carried here is a
    /// kernel `Expr` with no surface form, so it cannot flow through the
    /// surface-substitution path.
    ///
    /// The default implementation is a no-op: an evaluator without a value
    /// channel (e.g. a unit-test stub) simply ignores the binding, and the
    /// later reference then fails to resolve honestly rather than splicing a
    /// fabricated term.
    ///
    /// # Soundness
    ///
    /// This only *names* a term the query already read out of the live proof
    /// state; it closes no goal and fabricates nothing. The bound value is
    /// kernel-checked wherever the referencing statement flows through the
    /// normal pipeline (e.g. `exact g` type-checks `g` against the goal). The
    /// caller is responsible for clearing the binding (see
    /// [`TacticEval::clear_value_binding`]) so it never leaks past the body.
    fn set_value_binding(&mut self, name: &SurfaceName, value: Expr) {
        let _ = (name, value);
    }

    /// Metaprogramming Phase 8: remove a value-channel binding previously set by
    /// [`TacticEval::set_value_binding`]. The executor calls this for every name
    /// it introduced once the do-block finishes (on success *and* failure) so a
    /// goal-query value never leaks into a later, unrelated elaboration.
    ///
    /// The default implementation is a no-op (paired with the no-op
    /// `set_value_binding`).
    fn clear_value_binding(&mut self, name: &SurfaceName) {
        let _ = name;
    }

    /// Metaprogramming Phase 7: run a *value-yielding* tactic, then read the
    /// value it produced out of the proof state.
    ///
    /// This is the principled generalization of the `do`-block `let x <- intro`
    /// bind: rather than threading a chosen name *into* the emitted tactic call,
    /// the tactic is run normally (via [`TacticEval::eval`]) and the resulting
    /// value is *read back* from the (already mutated, kernel-checked)
    /// `ProofState`. The default implementation handles the value-yielding
    /// tactics whose result has a surface representation:
    ///
    /// * `intro` / `intros` (single binder) — yields the introduced hypothesis
    ///   ([`BoundValue::Hyp`]), read as the newly-added local declaration.
    ///
    /// Returns `Ok(None)` for any tactic that produces no surface-representable
    /// value (the caller then defers the bind honestly — it never fabricates a
    /// binding). The `eval`/`eval_seq` signatures are unchanged; this is a
    /// purely additive read-after-effect path.
    ///
    /// # Soundness
    ///
    /// The value is observed *after* the tactic ran its normal effect: `intro`'s
    /// hypothesis exists in the local context only because `intro` already
    /// closed the original goal with the kernel-checked `λ`-proof. No goal is
    /// closed here and no value is invented; this only names state the tactic
    /// itself produced.
    ///
    /// REQUIRES: `ps` is the proof state currently being elaborated for `tac`.
    /// ENSURES: On `Ok(Some(v))`, `tac` ran successfully and `v` names a value
    /// genuinely present in `ps` after the run.
    /// ENSURES: On `Ok(None)`, `tac` ran successfully but produced no
    /// surface-representable value.
    fn eval_returning(
        &mut self,
        ps: &mut ProofState,
        tac: &SurfaceTactic,
    ) -> Result<Option<BoundValue>, TacticError> {
        // Snapshot identities: a newly introduced local may repeat a user name.
        let before: Vec<FVarId> = ps
            .current_goal()
            .map(|g| g.local_ctx.iter().map(|d| d.fvar).collect())
            .unwrap_or_default();

        // Run the tactic through the normal kernel-checked path.
        self.eval(ps, tac)?;

        // Only `intro`-style tactics yield a surface-representable value: the
        // single hypothesis they newly added to the local context.
        let yields_hyp = matches!(
            tac,
            SurfaceTactic::Named { name, .. } if name == "intro" || name == "intros"
        );
        if !yields_hyp {
            return Ok(None);
        }

        let Some(goal) = ps.current_goal() else {
            // The tactic closed every goal: there is no live local context to
            // read a hypothesis name from. Defer honestly.
            return Ok(None);
        };
        // The introduced hypothesis is the unique local not present before.
        let introduced = goal
            .local_ctx
            .iter()
            .rev()
            .find(|d| !before.contains(&d.fvar))
            .map(|d| d.name.clone());
        match introduced {
            Some(name) => Ok(Some(BoundValue::Hyp {
                ident: SurfaceExpr::Ident(clean_parser::Span::dummy(), name.clone()),
                name,
            })),
            // No new local (e.g. `intros` over a non-Pi goal would have errored
            // already; defensively treat "nothing added" as no value).
            None => Ok(None),
        }
    }
}

/// Handler for compound tactics that contain sub-tactic sequences.
///
/// Unlike `TacticHandler`, compound handlers receive the raw `SurfaceTactic`
/// variant (to extract sub-tactic data) and a `TacticEval` callback (to
/// recursively evaluate sub-tactics). This avoids storing `ElabCtx` in the
/// registry, which would create lifetime/circular-dependency issues.
pub type CompoundTacticHandler = Arc<
    dyn Fn(&mut dyn TacticEval, &mut ProofState, &SurfaceTactic) -> Result<(), TacticError>
        + Send
        + Sync,
>;

/// A registered compound tactic entry.
#[derive(Clone)]
pub struct CompoundTacticEntry {
    pub name: String,
    pub handler: CompoundTacticHandler,
}

/// A registered tactic entry.
#[derive(Clone)]
pub struct TacticEntry {
    pub name: String,
    pub pattern: TacticArgPattern,
    pub handler: TacticHandler,
}

/// Registry for tactic elaborators, keyed by tactic name.
///
/// Tactics registered here are dispatched via `SurfaceTactic::Named` in
/// `eval_tactic`. Built-in (hardcoded) tactics continue to use their
/// dedicated `SurfaceTactic` variants and are unaffected by the registry.
///
/// The registry supports two handler types:
/// - **Simple** (`TacticEntry`): receives pre-elaborated `Expr` args.
///   Used by `SurfaceTactic::Named` dispatch.
/// - **Compound** (`CompoundTacticEntry`): receives raw `SurfaceTactic` +
///   `TacticEval` callback. Used by dedicated variants (AllGoals, Try, etc.)
///   that contain sub-tactic sequences. Phase 3D Wave 5 (#2440).
#[derive(Clone, Default)]
pub struct TacticRegistry {
    entries: HashMap<String, TacticEntry>,
    compound: HashMap<String, CompoundTacticEntry>,
}

impl TacticRegistry {
    /// ENSURES: returned registry contains no simple or compound tactic entries.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a tactic elaborator for the given name.
    /// Overwrites any previous registration for the same name.
    /// REQUIRES: `entry.name` is the lookup key callers will use for this tactic.
    /// ENSURES: `get(&entry.name)` returns the newly registered entry.
    /// ENSURES: Any previous simple entry with the same name is replaced; compound entries are unchanged.
    pub fn register(&mut self, entry: TacticEntry) {
        self.entries.insert(entry.name.clone(), entry);
    }

    /// Register a compound tactic handler by name.
    ///
    /// Compound handlers are dispatched for dedicated `SurfaceTactic` variants
    /// (AllGoals, Try, etc.) that contain sub-tactic sequences. The dispatch
    /// site maps the variant to a name and looks it up here.
    /// REQUIRES: `entry.name` matches the dispatch name for the dedicated compound variant.
    /// ENSURES: `get_compound(&entry.name)` returns the newly registered handler.
    /// ENSURES: Any previous compound entry with the same name is replaced; simple entries are unchanged.
    pub(crate) fn register_compound(&mut self, entry: CompoundTacticEntry) {
        self.compound.insert(entry.name.clone(), entry);
    }

    /// Look up a tactic by name.
    /// ENSURES: Returns `Some` iff a simple tactic entry is registered under `name`.
    pub fn get(&self, name: &str) -> Option<&TacticEntry> {
        self.entries.get(name)
    }

    /// Look up a compound tactic handler by name.
    /// ENSURES: Returns `Some` iff a compound tactic entry is registered under `name`.
    pub(crate) fn get_compound(&self, name: &str) -> Option<&CompoundTacticEntry> {
        self.compound.get(name)
    }

    /// Check if a name is a registered tactic (for keyword detection).
    /// ENSURES: Returns `true` exactly when `get(name)` would return `Some(_)`.
    pub fn is_registered(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }

    /// Build the error for a tactic name that is not registered, suggesting the
    /// closest registered names when there are any.
    ///
    /// Searches BOTH maps. `names()` deliberately excludes compound-only names
    /// because it feeds the parser's keyword list; a user who mistypes `conv`
    /// or `calc` still deserves the suggestion, so this does not reuse it.
    ///
    /// Everything here was already in scope at every site that minted the bare
    /// error, and no site called any of it: a user who typed `inhabit` was told
    /// `unknown tactic 'inhabit'` and nothing more.
    #[must_use]
    pub(crate) fn unknown_tactic(&self, name: &str) -> TacticError {
        let all: Vec<&str> = self
            .entries
            .keys()
            .chain(self.compound.keys())
            .map(String::as_str)
            .collect();
        let suggestions = crate::agent_diagnostics::nearest_string_candidates(name, all, 3);
        if suggestions.is_empty() {
            // No near miss. Three alphabetically-first tactic names would be
            // noise dressed as help.
            TacticError::UnknownTactic(name.to_string())
        } else {
            TacticError::UnknownTacticWithSuggestions {
                name: name.to_string(),
                suggestions,
            }
        }
    }

    /// All registered tactic names (for parser keyword list).
    /// ENSURES: Iterator yields every simple tactic name exactly once and excludes compound-only names.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.entries.keys().map(|s| s.as_str())
    }

    /// Number of registered tactics (simple + compound).
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len() + self.compound.len()
    }

    #[must_use]
    /// ENSURES: Returns `true` iff both the simple and compound tables are empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty() && self.compound.is_empty()
    }

    /// Extract the tactic argument patterns for passing to the parser.
    ///
    /// Returns a [`TacticPatterns`] map (name → pattern) suitable for use
    /// with `parse_file_with_tactics` and related APIs.
    #[must_use]
    /// ENSURES: Result contains one `(name, pattern)` pair for every simple tactic entry.
    /// ENSURES: Compound tactic entries are excluded because they are not parser-dispatched by `Named`.
    pub fn tactic_patterns(&self) -> TacticPatterns {
        self.entries
            .iter()
            .map(|(name, entry)| (name.clone(), entry.pattern.clone()))
            .collect()
    }
}
