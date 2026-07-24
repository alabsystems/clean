// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Execution bridge for user-defined `elab ... : tactic => <body>` tactics.
//!
//! # Phase 1 (Option B — substitute-and-delegate)
//!
//! A tactic-category elaborator whose body parses as a flat `by` tactic block
//! (`SurfaceExpr::ByTactic` of simple `Named`/`Term` tactics) is run by:
//!
//! 1. binding each pattern variable (e.g. `e` in `elab "myexact" e:term`) to the
//!    corresponding call-site argument syntax,
//! 2. substituting those bindings into the body tactic AST (every occurrence of
//!    the bound variable's identifier is replaced by the call-site argument
//!    expression), and
//! 3. evaluating the substituted body via the existing tactic evaluator
//!    (`TacticEval::eval_seq`) against the current proof state.
//!
//! # Phase 2 (do-notation tactic bodies)
//!
//! A tactic body written as a `do` block — which the parser wraps as
//! `ByTactic([Term(Do([DoElem..]))])` — is interpreted by lowering the
//! tractable `DoElem` subset to the *same* flat `SurfaceTactic` sequence Phase 1
//! delegates, then reusing the Phase 1 evaluation path. The supported subset is:
//!
//! - **Action statements** (`DoElem::Expr`) whose payload is a tactic call:
//!   `do exact e`, `do intro h; exact h`, `do rfl`. The action expression is an
//!   `App(Ident(name), args)` (or a bare `Ident(name)` for nullary tactics),
//!   which lowers to `SurfaceTactic::Named { name, args }` — exactly the shape
//!   the Phase 1 flat-sequence form produces.
//! - **Pure value let** (`DoElem::Let`): `do let x := <expr>; ...`. Binds `x` to
//!   the (substituted) right-hand expression for the remainder of the block.
//!   This is a pure substitution extension — no tactic effect is emitted.
//! - **`intro`/`intros` value bind** (`DoElem::Bind`): `do let h <- intro; ...`.
//!   `intro` already takes the introduced hypothesis name as an *argument*, so
//!   the bind threads the bound name into the emitted call (`intro h`) and into
//!   the substitution map so later actions (`exact h`) reference the same
//!   hypothesis. This is the only cleanly-threadable value bind, because the
//!   tactic monad does not (yet) return values (`eval`/`eval_seq` return
//!   `Result<(), TacticError>`); every other `Bind` shape is deferred.
//!
//! # Phase 7 (value-yielding tactic binds)
//!
//! Phase 2's `intro` bind *threads* the bound name forward by emitting `intro h`
//! — it chooses the name rather than reading what the tactic produced. Phase 7
//! generalizes this into the principled value path
//! [`TacticEval::eval_returning`]: a `do`-block containing a value bind
//! (`let x <- tac`) is interpreted *statefully* against the live proof state
//! ([`LoweredBody::DoExec`]). Each statement runs in order; a value bind runs
//! `tac` through the normal kernel-checked evaluator and then *reads* the value
//! the tactic produced out of the (already mutated) `ProofState`
//! ([`BoundValue`]), binding it into the substitution map for later statements.
//!
//! Currently `intro`/`intros` are the value-yielding tactics: their value is the
//! hypothesis they introduced, read back as the local declaration `tac` added
//! (so `let h <- intro; exact h` binds `h` to the *actual* introduced name). A
//! bind whose tactic yields no surface-representable value is deferred honestly
//! (the bind cannot be threaded, so the whole body falls back to the
//! honest-error handler — never a fabricated binding).
//!
//! Soundness is unchanged: `eval_returning` reads state the tactic itself
//! produced *after* its normal kernel-checked effect; it closes no goal and
//! invents no value.
//!
//! # Soundness
//!
//! Every supported shape only *delegates* to the existing tactic evaluator. A
//! user tactic — flat or `do`-notation — can therefore do nothing a hand-written
//! `by` block of the same tactics could not: goals close exclusively through the
//! normal kernel-checked tactic effects (`exact`, `apply`, `close_goal`, ...). No
//! goal is ever marked solved without the kernel-checked effect, so no new trust
//! surface is added. A `do` body that should not close a goal still fails — the
//! lowering never fabricates an effect.
//!
//! # Deferred (still honest-error)
//!
//! Body shapes outside the lowerable subset keep the honest-error simple handler
//! the caller registers: control-flow do statements (`if`/`for`/`try`/`match`/
//! `while`/`repeat`/`unless`/reassignment), value binds whose result cannot be
//! threaded without a value-returning tactic monad, `do`-blocks ending in a
//! binding, bodies that elaborate brand-new expressions at tactic runtime, and
//! non-tactic (`term`/`command`) elaborators.

use crate::tactic::term_close::refine_elaborated_from_pending;
use crate::tactic::{
    BoundValue, CompoundTacticEntry, CompoundTacticHandler, ProofState, TacticError, TacticEval,
};
use clean_kernel::{ExprKind, Name};
use clean_parser::{DoElem, InterpolationPart, SurfaceArg, SurfaceExpr, SurfaceLit, SurfaceTactic};
use std::sync::Arc;

/// A name binding used during substitution: a bound identifier mapped to the
/// surface expression that should replace it. Owned so that sequential
/// `do`-block bindings (`let x := ...`) can extend the map as the block is
/// lowered.
type Binding = (String, SurfaceExpr);

/// Decide whether a parsed tactic-block body is one the bridge can execute via
/// substitute-and-delegate.
///
/// Accepts:
/// - a flat sequence of simple existing-tactic invocations (`Named`/`Term`),
///   the Phase 1 form (e.g. `exact e`, `intro h; exact h`, `rfl`); and
/// - a single `do`-notation body (`[Term(Do(elems))]`) whose statements all lie
///   in the lowerable subset (see [module docs](self)).
///
/// Returns `false` (deferred) for empty bodies and for `do`-blocks containing a
/// control-flow / non-threadable statement, so the caller keeps the honest-error
/// handler rather than mis-running them.
pub(super) fn is_executable_tactic_body(tactics: &[SurfaceTactic]) -> bool {
    if let Some(elems) = as_do_block(tactics) {
        // Phase 7: a do-block with a value bind (`let x <- tac`) is run by the
        // stateful executor; otherwise the Phase 2/3 lowering applies.
        return do_block_is_exec_interpretable(elems)
            || do_block_to_tactics(elems, &mut Vec::new()).is_some();
    }
    !tactics.is_empty() && tactics.iter().all(is_executable_tactic)
}

fn is_executable_tactic(tac: &SurfaceTactic) -> bool {
    match tac {
        SurfaceTactic::Named { .. } => true,
        // A term-mode tactic is executable unless its payload is a `do` monad
        // (which is handled by the dedicated do-block path, not here).
        SurfaceTactic::Term(_, expr) => !matches!(expr.as_ref(), SurfaceExpr::Do(..)),
        // All other (compound) tactic shapes are conservatively deferred: we only
        // substitute into the simple term/ident-argument forms.
        _ => false,
    }
}

/// If `tactics` is exactly a single `do`-notation body (the parser wraps a
/// tactic-category `do` block as `ByTactic([Term(Do(elems))])`), return its
/// statement sequence. Returns `None` for any other shape.
fn as_do_block(tactics: &[SurfaceTactic]) -> Option<&[DoElem]> {
    match tactics {
        [SurfaceTactic::Term(_, expr)] => match expr.as_ref() {
            SurfaceExpr::Do(_, elems) => Some(elems),
            _ => None,
        },
        _ => None,
    }
}

/// Lower a `do`-block statement sequence to the flat `SurfaceTactic` sequence
/// the Phase 1 evaluator delegates, applying `bindings` (pattern vars +
/// previously-bound `do` vars) and extending them as pure/value lets are seen.
///
/// Returns `None` if any statement is outside the lowerable subset (the caller
/// then defers the whole body to the honest-error handler), guaranteeing we
/// never partially run a `do` block we cannot fully interpret.
fn do_block_to_tactics(
    elems: &[DoElem],
    bindings: &mut Vec<Binding>,
) -> Option<Vec<SurfaceTactic>> {
    if elems.is_empty() {
        return None;
    }
    let mut out = Vec::with_capacity(elems.len());
    for elem in elems {
        match elem {
            // Action statement: `exact e`, `intro h`, `rfl`, ... parsed as an
            // expression. Lower to the tactic call it denotes.
            DoElem::Expr(_, expr) => {
                let tac = action_expr_to_tactic(expr, bindings)?;
                out.push(tac);
            }
            // Pure value let: `let x := <expr>`. No tactic effect — extend the
            // substitution map so later actions can reference `x`.
            DoElem::Let(_, binder, val) => {
                let replacement = substitute_in_expr(val, bindings);
                upsert_binding(bindings, &binder.name, replacement);
            }
            // A value bind (`let x <- tac`) is NOT lowered to a flat sequence:
            // Phase 7 runs it statefully via the executor (`run_do_exec`), which
            // reads the tactic's produced value out of the proof state. Bail here
            // so the caller routes the block to the `DoExec` path instead.
            DoElem::Bind(..) => return None,
            // Everything else (control flow, mutation, ...) is deferred: bail so
            // the caller keeps the honest-error handler.
            _ => return None,
        }
    }
    if out.is_empty() {
        // A block of only pure lets has no tactic effect — not executable.
        return None;
    }
    Some(out)
}

// ===========================================================================
// Phase 3: runtime sub-expression elaboration
// ===========================================================================
//
// Phases 1-2 run a user-tactic body purely by *substituting* call-site argument
// syntax into the body's tactic AST and delegating to `TacticEval::eval_seq`.
// The body can therefore only *reuse* the pre-bound argument syntax; it cannot
// build a NEW expression and elaborate it at tactic runtime.
//
// Phase 3 adds the minimal runtime-elaboration case: a do-block of the shape
//
//     do let x := <build-expr>; ...; exact <final-expr>
//
// where `<build-expr>` is *elaborated at tactic runtime* into a kernel `Expr`
// (against the current goal's local context), bound to `x` as a runtime VALUE
// (a kernel term, not syntax), and the terminal `exact <final-expr>` closes the
// goal using that elaborated term.
//
// This is possible because the compound-handler dispatch in `eval_tactic`
// passes the live `ElabCtx` as the `&mut dyn TacticEval` callback, which already
// exposes `elaborate_refine` (elaborate a surface expression against the current
// goal) and `metas`. The handler therefore holds BOTH the elaboration context
// (via `eval`) and the proof state (`ps`) — the Phase 3 inflection — without any
// ownership refactor: the two are distinct `&mut` parameters at the call site.
//
// # Soundness
//
// The terminal close goes exclusively through the kernel-checked `refine`
// bridge (`elaborate_refine` + `refine_elaborated_from_pending`) — the SAME path
// the built-in `refine`/`exact` use. The elaborated term is type-checked against
// the goal target during elaboration, and `close_goal` type-checks it again
// before acceptance. No goal is closed without the kernel-checked effect, and a
// term that does not fit the goal fails honestly (it cannot fabricate a proof).

/// A user-tactic body lowered to an execution plan.
enum LoweredBody {
    /// Phase 1/2: substitute and delegate the whole body to `eval_seq`.
    Delegate(Vec<SurfaceTactic>),
    /// Phase 3: run `prefix` via `eval_seq`, then elaborate `close` at runtime
    /// against the current goal and close it through the kernel-checked refine
    /// bridge. `prefix` is empty for `do exact <build-expr>`.
    RuntimeElabClose {
        prefix: Vec<SurfaceTactic>,
        close: SurfaceExpr,
    },
    /// Phase 7: interpret a `do`-block statement-by-statement against the live
    /// proof state, recovering value-yielding tactic results via
    /// [`TacticEval::eval_returning`]. Carries the raw `do` statements and the
    /// seed bindings (call-site args). Used when the block contains a value bind
    /// `let x <- tac` whose result must be read out of the proof state.
    DoExec {
        elems: Vec<DoElem>,
        seed: Vec<Binding>,
    },
    /// A terminal `throwError "msg"` body (the bare, non-`do` form, e.g.
    /// `elab "boom" : tactic => throwError "msg"`). Raises the user's custom error
    /// as a typed [`TacticError::UserThrowError`]: it closes no goal and
    /// fabricates nothing — it only makes elaboration FAIL with the message.
    ThrowError { message: String },
}

/// The goal-closing keywords whose single argument is elaborated against the
/// current goal: a terminal `exact`/`refine` is what the runtime path drives.
fn is_runtime_close_keyword(name: &str) -> bool {
    name == "exact" || name == "refine"
}

/// Tactics that take a SINGLE term argument. When such a tactic appears in a
/// `do`-block action parsed as a multi-arg application (`exact f x` →
/// `App(exact, [f, x])`), the trailing args belong to the term, not to the
/// tactic, so they must be folded back into one applied term.
fn is_term_arg_close_keyword(name: &str) -> bool {
    matches!(name, "exact" | "apply" | "refine" | "show")
}

/// Detect the Phase 3 runtime-elaboration shape in a do-block and build its
/// plan, fully applying `bindings` (call-site args; extended by value lets).
///
/// Recognized: zero or more *pure value lets* (`let x := <expr>`) followed by a
/// single terminal `exact <expr>` / `refine <expr>` action. The terminal
/// expression — with all bindings substituted — becomes the `close` expression
/// elaborated at runtime. Any other statement shape returns `None` (the caller
/// then falls back to the Phase 1/2 delegate lowering).
///
/// Only fires when at least one value let participates, because a bare
/// `do exact e` is already handled identically by the delegate path; the value
/// let is what makes runtime elaboration the meaningful interpretation (the let
/// RHS is elaborated once, as a term, rather than re-substituted as syntax).
fn runtime_elab_close_plan(elems: &[DoElem], bindings: &mut Vec<Binding>) -> Option<SurfaceExpr> {
    if elems.len() < 2 {
        return None;
    }
    let mut saw_value_let = false;
    let (last, prefix) = elems.split_last()?;
    for elem in prefix {
        match elem {
            DoElem::Let(_, binder, val) => {
                let replacement = substitute_in_expr(val, bindings);
                upsert_binding(bindings, &binder.name, replacement);
                saw_value_let = true;
            }
            // Any non-pure-let prefix statement disqualifies the runtime shape;
            // defer to the delegate path which can sequence tactic effects.
            _ => return None,
        }
    }
    if !saw_value_let {
        return None;
    }
    let DoElem::Expr(_, expr) = last else {
        return None;
    };
    let (name, args) = close_action_head(expr)?;
    if !is_runtime_close_keyword(&name) || args.len() != 1 {
        return None;
    }
    Some(substitute_in_expr(&args[0], bindings))
}

/// Extract `(keyword, args)` from a terminal action expression (`exact e`,
/// `refine e`), descending through parentheses. Returns `None` for any other
/// shape or for actions headed by a metaprogramming-monad op.
fn close_action_head(expr: &SurfaceExpr) -> Option<(String, Vec<SurfaceExpr>)> {
    match expr {
        SurfaceExpr::App(_, func, args) => {
            let SurfaceExpr::Ident(_, name) = func.as_ref() else {
                return None;
            };
            if is_metaprogramming_monad_op(name) {
                return None;
            }
            Some((name.clone(), args.iter().map(|a| a.expr.clone()).collect()))
        }
        SurfaceExpr::Paren(_, inner) => close_action_head(inner),
        _ => None,
    }
}

/// Run a `RuntimeElabClose` plan: evaluate the prefix tactics, then elaborate
/// the `close` expression against the current goal at runtime and close the goal
/// through the kernel-checked refine bridge.
///
/// # Soundness
///
/// `elaborate_refine` type-checks the elaborated term against the goal target;
/// `refine_elaborated_from_pending` closes the goal via `close_goal`, which
/// type-checks again. A term that does not fit the goal fails — no fabrication.
fn run_runtime_elab_close(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    prefix: &[SurfaceTactic],
    close: &SurfaceExpr,
) -> Result<(), TacticError> {
    if !prefix.is_empty() {
        eval.eval_seq(ps, prefix)?;
    }
    // Elaborate the close expression against the current goal at tactic runtime.
    let refined = eval.elaborate_refine(ps, close)?;
    // Close the goal through the same kernel-checked bridge `refine`/`exact` use.
    refine_elaborated_from_pending(ps, refined.term, eval.metas(), &refined.pending_goals)
}

// ===========================================================================
// Phase 7: stateful do-block execution with value-yielding tactic binds
// ===========================================================================
//
// Phase 2 lowers a `do`-block to a flat tactic sequence and delegates it to
// `eval_seq`. That model cannot recover a *value* a tactic produced — it only
// threads syntax forward (the `intro h` name special-case). Phase 7 interprets
// a `do`-block STATEFULLY against the live proof state so a value bind
// `let x <- tac` can run `tac` and read its result out of the state via
// `eval_returning`, binding `x` for later statements.
//
// The executor fires only when the block contains a value bind; every other
// `do`-block keeps its Phase 2/3 lowering unchanged. Each statement runs in
// order against the SAME `ps` the surrounding `by` block uses:
//
//   * action (`exact e`, `rfl`, ...)  -> `eval` the lowered tactic call;
//   * pure let (`let x := e`)          -> extend the substitution map, no effect;
//   * value bind (`let x <- tac`)      -> `eval_returning(tac)`; on `Some(v)` bind
//                                          `x -> v.as_surface()`, on `None` ERROR
//                                          (the bind is not threadable — honest).
//
// # Soundness
//
// The executor adds no goal-closing path: actions and value binds run through
// the same kernel-checked `eval` the delegate path uses, and a value is only
// *read* from state the tactic already produced. A bind whose tactic yields no
// value fails honestly rather than fabricating a binding.

/// Whether a `do`-block can be run by the Phase 7 stateful executor.
///
/// Requires at least one *executor-only* statement — a value bind (`let x <-
/// tac`) or a goal-query let (`let g := getMainTarget`) — otherwise the Phase
/// 2/3 lowering is the right interpretation. Every statement must lie in the
/// executable subset: action call, pure value let, goal-query let, or a value
/// bind whose tactic is recognized as value-yielding (`intro`/`intros` with no
/// explicit name argument). Any other statement (control flow,
/// metaprogramming-monad op, non-value-yielding bind) disqualifies the block.
///
/// A goal-query let (`let g := getMainTarget`) requires the stateful executor
/// because its value is a kernel `Expr` read from the live proof state — it has
/// no surface form, so it cannot flow through the Phase 2/3 surface-substitution
/// path.
fn do_block_is_exec_interpretable(elems: &[DoElem]) -> bool {
    let mut needs_executor = false;
    for elem in elems {
        match elem {
            DoElem::Expr(_, expr) => {
                // A supported `throwError "msg"` is a first-class executor op: it
                // raises the user's custom error. Route the block to the executor.
                // A `throwError s!"…{x}…"` interpolation is routed by *shape* (the
                // call-site binding environment that resolves `{x}` does not exist
                // at classification time); the executor renders it against the live
                // bindings and surfaces an honest error if a hole is unresolvable.
                if as_throw_error_message(expr).is_some()
                    || is_throw_error_interpolation_shape(expr)
                {
                    needs_executor = true;
                    continue;
                }
                // Otherwise an action must lower to a tactic call (this rejects
                // genuinely-unsupported monad ops such as `logInfo`, so a block
                // containing one still defers to the honest-error handler).
                if action_expr_to_tactic(expr, &[]).is_none() {
                    return false;
                }
            }
            // A computed `if <cond> then <...> else <...>` whose branches are
            // themselves exec-runnable is run by the executor (B83): the condition
            // is decided at metaprogram time and the chosen branch runs (so
            // `if c then throwError "bad" else exact h` fires the error iff `c` is
            // true). Requires the executor for the metaprogram-time decide.
            DoElem::If(_, _, then_elems, else_elems) => {
                if !do_branch_is_exec_runnable(then_elems) {
                    return false;
                }
                if !else_elems
                    .as_ref()
                    .is_none_or(|elems| do_branch_is_exec_runnable(elems))
                {
                    return false;
                }
                needs_executor = true;
            }
            DoElem::Let(_, _, val) => {
                // A goal-query let routes the block to the executor (its value
                // is a kernel Expr with no surface form). A plain pure let is
                // fine in either path.
                if is_get_main_target_query(val) {
                    needs_executor = true;
                }
            }
            DoElem::Bind(_, _, val) => {
                if !is_value_yielding_bind_tac(val) {
                    return false;
                }
                needs_executor = true;
            }
            _ => return false,
        }
    }
    needs_executor
}

/// Whether a computed-`if` *branch* (a statement sequence) can be run by the
/// executor. Unlike [`do_block_is_exec_interpretable`], a branch does NOT need a
/// dedicated executor-only statement: an ordinary action sequence (e.g. a single
/// `exact h`) is a valid branch. Every statement must still be supported — a
/// tactic action, a supported `throwError "msg"`, a pure / goal-query let, a
/// value-yielding bind, or a nested exec-runnable `if` — so a branch containing a
/// genuinely-unsupported monad op (`logInfo`) disqualifies the whole block.
fn do_branch_is_exec_runnable(elems: &[DoElem]) -> bool {
    !elems.is_empty()
        && elems.iter().all(|elem| match elem {
            DoElem::Expr(_, expr) => {
                as_throw_error_message(expr).is_some()
                    || is_throw_error_interpolation_shape(expr)
                    || action_expr_to_tactic(expr, &[]).is_some()
            }
            DoElem::If(_, _, then_elems, else_elems) => {
                do_branch_is_exec_runnable(then_elems)
                    && else_elems
                        .as_ref()
                        .is_none_or(|elems| do_branch_is_exec_runnable(elems))
            }
            DoElem::Let(..) => true,
            DoElem::Bind(_, _, val) => is_value_yielding_bind_tac(val),
            _ => false,
        })
}

/// The query-head identifiers that read the current goal's target as a kernel
/// `Expr` value. `getMainTarget` is the Lean spelling; `getMainGoalTarget` and
/// the dotted `Expr.goalTarget` alias name the same read.
const GET_MAIN_TARGET_HEADS: &[&str] = &["getMainTarget", "getMainGoalTarget", "Expr.goalTarget"];

/// Whether `expr` is the `getMainTarget` goal-query (a bare head identifier with
/// no arguments). Recognized spellings are listed in [`GET_MAIN_TARGET_HEADS`].
///
/// The query takes no arguments — it reads the *current goal's* target — so any
/// application form (`getMainTarget x`) is rejected and falls through to the
/// ordinary surface-substitution path.
fn is_get_main_target_query(expr: &SurfaceExpr) -> bool {
    match expr {
        SurfaceExpr::Ident(_, name) => GET_MAIN_TARGET_HEADS.contains(&name.as_str()),
        SurfaceExpr::Proj(_, base, clean_parser::Projection::Named(field)) => {
            matches!(base.as_ref(), SurfaceExpr::Ident(_, b)
                if GET_MAIN_TARGET_HEADS.contains(&format!("{b}.{field}").as_str()))
        }
        SurfaceExpr::Paren(_, inner) => is_get_main_target_query(inner),
        _ => false,
    }
}

/// Whether the tactic bound by `let x <- tac` yields a surface-representable
/// value the executor can recover via `eval_returning`.
///
/// Currently `intro`/`intros` with no explicit name argument: the bound name
/// receives the hypothesis the tactic introduces. (`let h <- intro x` names the
/// hypothesis explicitly and is deferred, matching the Phase 2 boundary.)
fn is_value_yielding_bind_tac(val: &SurfaceExpr) -> bool {
    match action_expr_to_tactic(val, &[]) {
        Some(SurfaceTactic::Named { name, args, .. }) => {
            (name == "intro" || name == "intros") && args.is_empty()
        }
        _ => false,
    }
}

/// Run a Phase 7/8 `DoExec` plan: interpret `elems` statement-by-statement
/// against the live proof state, seeded with the call-site argument `bindings`.
///
/// Phase 8 adds the goal-query let (`let g := getMainTarget`): the current
/// goal's target is read as a kernel `Expr` and bound into the elaborator's
/// value channel (via [`TacticEval::set_value_binding`]) so a later statement
/// referencing `g` (e.g. `exact g`) splices that stored term. Every value-channel
/// name introduced here is cleared once the block finishes — on success *and*
/// failure — so a goal-query value never leaks into a later elaboration.
///
/// # Soundness
///
/// Actions and value binds run through the kernel-checked `eval`; a value bind
/// reads its result from state the tactic produced (`eval_returning`). A
/// goal-query let only *names* the target the current goal already carries —
/// it closes no goal and fabricates nothing; the named term is kernel-checked
/// wherever the referencing statement flows (e.g. `exact g`). A bind that yields
/// no value errors honestly. The executor closes no goal itself.
fn run_do_exec(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    elems: &[DoElem],
    bindings: Vec<Binding>,
) -> Result<(), TacticError> {
    let mut value_channel_names: Vec<String> = Vec::new();
    let result = run_do_exec_inner(eval, ps, elems, bindings, &mut value_channel_names);
    // Always unbind every value-channel name this block introduced, on success
    // or failure, so a goal-query value never leaks into a later elaboration.
    for name in &value_channel_names {
        eval.clear_value_binding(name);
    }
    result
}

/// Inner driver for [`run_do_exec`]; records value-channel names it introduces in
/// `value_channel_names` for the caller to clear unconditionally.
fn run_do_exec_inner(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    elems: &[DoElem],
    mut bindings: Vec<Binding>,
    value_channel_names: &mut Vec<String>,
) -> Result<(), TacticError> {
    for elem in elems {
        match elem {
            DoElem::Expr(_, expr) => {
                // A supported `throwError "msg"` action raises the user's custom
                // error as a typed diagnostic: it closes no goal and fabricates
                // nothing — it only makes elaboration FAIL with the user's message.
                // The message may interpolate already-bound values (`s!"got {x}"`),
                // resolved here against the live `bindings`.
                if let Some(message) = as_throw_error_message_in(expr, &bindings) {
                    return Err(TacticError::UserThrowError { message });
                }
                // A `throwError` interpolation whose holes could NOT be resolved to
                // concrete values surfaces an honest error rather than fabricating a
                // message or silently dispatching `throwError` as a tactic.
                if is_throw_error_interpolation_shape(expr) {
                    return Err(TacticError::ElaborationFailed {
                        detail: "throwError interpolation references a value that is not bound to \
                                 a concrete renderable term"
                            .to_owned(),
                    });
                }
                let tac = action_expr_to_tactic(expr, &bindings).ok_or_else(|| {
                    TacticError::ElaborationFailed {
                        detail: "unsupported do-block action in value-bind tactic body".to_owned(),
                    }
                })?;
                eval.eval(ps, &tac)?;
            }
            // Computed `if <cond> then <...> else <...>`: decide the condition at
            // metaprogram time and run only the chosen branch. The condition is
            // elaborated + kernel-checked and weak-head-reduced; only a concrete
            // `Bool.true`/`Bool.false` decides a branch (anything else errors
            // honestly rather than guessing). This is a metaprogram-time choice of
            // which statements to run, not an object-level case split.
            DoElem::If(_, cond, then_elems, else_elems) => {
                let branch = match decide_meta_bool(eval, ps, cond, &bindings)? {
                    true => then_elems.as_slice(),
                    false => match else_elems {
                        Some(elems) => elems.as_slice(),
                        // A decided-false `if` with no `else` branch is a no-op.
                        None => continue,
                    },
                };
                run_do_exec_inner(eval, ps, branch, bindings.clone(), value_channel_names)?;
            }
            DoElem::Let(_, binder, val) if is_get_main_target_query(val) => {
                // Goal query: read the current goal's target (a kernel Expr) and
                // bind it into the value channel so a later `exact g` splices it.
                // This only names a term the goal already carries — no fabrication.
                let target = ps
                    .current_goal()
                    .ok_or(TacticError::NoGoals)?
                    .target
                    .clone();
                eval.set_value_binding(&binder.name, target);
                value_channel_names.push(binder.name.clone());
            }
            DoElem::Let(_, binder, val) => {
                let replacement = substitute_in_expr(val, &bindings);
                upsert_binding(&mut bindings, &binder.name, replacement);
            }
            DoElem::Bind(_, binder, val) => {
                let tac = action_expr_to_tactic(val, &bindings).ok_or_else(|| {
                    TacticError::ElaborationFailed {
                        detail: "unsupported value bind in do-block tactic body".to_owned(),
                    }
                })?;
                // Run the tactic and read the value it produced out of the proof
                // state. A tactic that yields no surface value cannot be threaded.
                match eval.eval_returning(ps, &tac)? {
                    Some(value) => {
                        upsert_binding(&mut bindings, &binder.name, value.as_surface().clone());
                    }
                    None => {
                        return Err(TacticError::ElaborationFailed {
                            detail: format!(
                                "tactic bound to `{}` produced no value to bind",
                                binder.name
                            ),
                        });
                    }
                }
            }
            // The classifier (`do_block_is_exec_interpretable`) rejects any other
            // statement before registration, so this is defensive.
            _ => {
                return Err(TacticError::ElaborationFailed {
                    detail: "unsupported statement in value-bind do-block tactic body".to_owned(),
                });
            }
        }
    }
    Ok(())
}

/// The `Bool.true` / `Bool.false` constructor names a decided condition reduces
/// to (matching the term-elaborator computed-`if` path in `meta_control_flow`).
const BOOL_TRUE: &str = "Bool.true";
const BOOL_FALSE: &str = "Bool.false";

/// Decide a computed-`if` condition at metaprogram time: substitute the active
/// bindings into `cond`, elaborate + kernel-check it, weak-head-reduce the result
/// in the current goal context, and classify it as a concrete `Bool` constructor.
///
/// Returns `Ok(true)` for `Bool.true`, `Ok(false)` for `Bool.false`. A condition
/// that does NOT reduce to a concrete `Bool` (stuck / symbolic / non-`Bool`) is
/// not a decided metaprogram-time value, so it errors honestly rather than
/// guessing a branch.
///
/// # Soundness
///
/// The condition is elaborated and kernel-checked by the normal pipeline and
/// reduced by the kernel weak-head reducer (meaning-preserving). Only a concrete
/// `Bool` constructor decides a branch; this is a metaprogram-time choice of which
/// statements to run, not an object-level case split — no goal is closed and
/// nothing is fabricated.
fn decide_meta_bool(
    eval: &mut dyn TacticEval,
    ps: &ProofState,
    cond: &SurfaceExpr,
    bindings: &[Binding],
) -> Result<bool, TacticError> {
    let substituted = substitute_in_expr(cond, bindings);
    let cond_expr = eval.elaborate(&substituted)?;
    let goal = ps.current_goal().ok_or(TacticError::NoGoals)?;
    let reduced = ps.whnf(goal, &cond_expr);
    let ExprKind::Const(name, _) = reduced.kind() else {
        return Err(TacticError::ElaborationFailed {
            detail: "computed `if` condition did not reduce to a concrete Bool".to_owned(),
        });
    };
    if *name == Name::from_string(BOOL_TRUE) {
        Ok(true)
    } else if *name == Name::from_string(BOOL_FALSE) {
        Ok(false)
    } else {
        Err(TacticError::ElaborationFailed {
            detail: "computed `if` condition did not reduce to a concrete Bool".to_owned(),
        })
    }
}

/// Metaprogramming-monad operations that are NOT tactics. A `do`-block action
/// headed by one of these (`logInfo msg`, `trace`, lift ops, ...) operates in the
/// elaboration/tactic *monad* — logging, tracing, lifting — rather than
/// transforming the proof state. We cannot interpret the monad, so a `do`-block
/// containing any of these (other than a supported `throwError`) is deferred to
/// the honest-error handler. Treating them as tactic calls would mis-dispatch
/// (e.g. run a non-existent `logInfo` tactic) or silently no-op an effect.
///
/// `throwError` / `throwErrorAt` / `throw` remain listed here so they are NEVER
/// dispatched as tactic calls; a supported string-message `throwError` is instead
/// recognized *before* this check (via [`as_throw_error_message`]) and turned into
/// a real typed [`TacticError::UserThrowError`]. A `throwError` whose message is
/// not a literal string (f-string / `MessageData`) still falls through to the
/// honest-error handler, which surfaces its static message.
fn is_metaprogramming_monad_op(name: &str) -> bool {
    matches!(
        name,
        "throwError"
            | "throwErrorAt"
            | "throw"
            | "logInfo"
            | "logWarning"
            | "logError"
            | "logInfoAt"
            | "trace"
            | "dbg_trace"
            | "dbgTrace"
            | "pure"
            | "return"
            | "liftMetaTactic"
            | "liftMetaM"
            | "liftTermElabM"
            | "withMainContext"
            | "getMainGoal"
            | "getMainTarget"
    )
}

/// The metaprogramming-monad ops that raise a custom error from a string message
/// — `throwError "msg"`, the positional `throwErrorAt _ "msg"`, and the bare
/// `throw "msg"`. These are a FIRST-CLASS supported op: a do-body action (or
/// computed-`if` branch) of this shape produces a real typed error carrying the
/// message rather than deferring. The message may be a plain string literal (B87)
/// or a string-interpolation (`s!"…"` / `m!"…"` / `f!"…"`, B89) whose embedded
/// `{expr}` holes all resolve to concrete already-bound values.
fn is_throw_error_op(name: &str) -> bool {
    matches!(name, "throwError" | "throwErrorAt" | "throw")
}

/// Whether `expr` is *any* `throwError`-family call (`throwError …` /
/// `throwErrorAt …` / `throw …`), regardless of whether its message is a
/// renderable literal/interpolation. Descends through parentheses.
///
/// `pub(crate)` so the macro-expansion path can distinguish "a `throwError`
/// whose message is not renderable here" (which must DEFER honestly, because the
/// message depends on runtime-matched syntax) from "not a `throwError` at all"
/// (which is a different defer reason). Pairs with [`as_throw_error_message_in`],
/// which returns the rendered message only when fully resolvable.
pub(crate) fn is_throw_error_call(expr: &SurfaceExpr) -> bool {
    match expr {
        SurfaceExpr::App(_, func, _) => {
            matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if is_throw_error_op(name))
        }
        SurfaceExpr::Paren(_, inner) => is_throw_error_call(inner),
        _ => false,
    }
}

/// Cap on how many binding-indirection hops [`render_metavalue`] follows when an
/// embedded interpolation hole resolves to another bound identifier. A bound name
/// can point at another bound name (`let a := b`); the cap stops a pathological
/// binding cycle from looping forever — once exhausted the value is treated as
/// unresolvable and the whole interpolation declines (never fabricates).
const MAX_METAVALUE_HOPS: usize = 64;

/// Render an already-bound metaprogram value (the expression `expr` denotes,
/// after the active `bindings` are taken into account) to the faithful text its
/// Lean `toString` / pretty form would print, or `None` if it is not a concrete
/// renderable value at this point.
///
/// Only forms whose surface spelling has an unambiguous, fabrication-free textual
/// rendering are accepted:
/// - a string literal renders as its raw contents (Lean `toString` on a `String`
///   is the string itself);
/// - a `Nat` / `Float` / `Char` literal renders as its source text;
/// - a bare identifier is resolved through `bindings` and rendered recursively
///   (so `s!"{x}"` with `x := 7` renders `7`); an *unbound* identifier — or one
///   bound to a value that is itself unrenderable — declines (`None`);
/// - parentheses are transparent.
///
/// Anything else (an application, a stuck/symbolic term, an unsupported literal)
/// declines so the caller defers honestly rather than guessing a value.
fn render_metavalue(expr: &SurfaceExpr, bindings: &[Binding], fuel: usize) -> Option<String> {
    match expr {
        SurfaceExpr::Lit(_, SurfaceLit::String(s)) => Some(s.clone()),
        SurfaceExpr::Lit(_, SurfaceLit::Nat(n)) => Some(n.to_string()),
        SurfaceExpr::Lit(_, SurfaceLit::Float(text)) => Some(text.clone()),
        SurfaceExpr::Lit(_, SurfaceLit::Char(c)) => Some(c.to_string()),
        SurfaceExpr::Paren(_, inner) => render_metavalue(inner, bindings, fuel),
        SurfaceExpr::Ident(_, name) => {
            let fuel = fuel.checked_sub(1)?;
            // Resolve through the binding environment. An identifier with no
            // binding is NOT a concrete value here — decline rather than render
            // the bare name (which would fabricate a value the metaprogram never
            // produced). A binding that maps the name to itself is also stuck.
            let (_, value) = bindings.iter().find(|(bound, _)| bound == name)?;
            if matches!(value, SurfaceExpr::Ident(_, v) if v == name) {
                return None;
            }
            render_metavalue(value, bindings, fuel)
        }
        _ => None,
    }
}

/// Render an interpolated-string message (`s!"…"` / `m!"…"` / `f!"…"`) to its
/// final text by concatenating the literal chunks with the rendered values of the
/// embedded `{expr}` holes, resolving holes through `bindings`.
///
/// Returns `None` (declining the whole interpolation) if ANY embedded hole cannot
/// be faithfully rendered to a concrete string at this point — the message text is
/// then honestly deferred rather than partially fabricated. The interpolation
/// *kind* (`s!`/`m!`/`f!`) does not change the rendered text: all three format the
/// same value text for an error message.
fn render_interpolation(parts: &[InterpolationPart], bindings: &[Binding]) -> Option<String> {
    let mut out = String::new();
    for part in parts {
        match part {
            InterpolationPart::Literal(text) => out.push_str(text),
            InterpolationPart::Expr(expr) => {
                out.push_str(&render_metavalue(expr, bindings, MAX_METAVALUE_HOPS)?);
            }
            // A future `InterpolationPart` variant is not a value we know how to
            // render faithfully — decline so the message defers honestly.
            _ => return None,
        }
    }
    Some(out)
}

/// Whether `expr` is a `throwError`-family call whose trailing positional message
/// argument is a string interpolation (`s!"…"` / `m!"…"` / `f!"…"`), regardless of
/// whether the embedded holes are resolvable yet.
///
/// Used by the do-block classifier (which runs at registration time, before the
/// call-site binding environment exists) to route such a `throwError` to the
/// stateful executor. The executor then resolves the interpolation against the
/// live bindings via [`as_throw_error_message_in`]; an unresolvable hole surfaces
/// an honest error there rather than fabricating a value.
fn is_throw_error_interpolation_shape(expr: &SurfaceExpr) -> bool {
    match expr {
        SurfaceExpr::App(_, func, args) => {
            let SurfaceExpr::Ident(_, name) = func.as_ref() else {
                return false;
            };
            if !is_throw_error_op(name) {
                return false;
            }
            match args.last() {
                Some(last) if last.name.is_none() => {
                    matches!(&last.expr, SurfaceExpr::InterpolatedStr { .. })
                }
                _ => false,
            }
        }
        SurfaceExpr::Paren(_, inner) => is_throw_error_interpolation_shape(inner),
        _ => false,
    }
}

/// Literal-only form of [`as_throw_error_message_in`]: recognizes a `throwError`
/// whose message is a plain string literal (or an interpolation with no unresolved
/// holes). Used for the static deny-list pre-check where no binding environment is
/// available. Equivalent to `as_throw_error_message_in(expr, &[])`.
///
/// Shared with the term-elaborator path (`user_term`/`meta_control_flow`) so a
/// `throwError "msg"` body or computed-`if` branch is recognized identically in
/// both term and tactic positions.
pub(super) fn as_throw_error_message(expr: &SurfaceExpr) -> Option<String> {
    as_throw_error_message_in(expr, &[])
}

/// If `expr` is a supported `throwError`-family call whose trailing positional
/// message argument is a string literal or a *fully resolvable* string
/// interpolation, return the final message text rendered against `bindings`.
///
/// `throwErrorAt` in Lean takes a leading position argument before the message
/// (`throwErrorAt stx "msg"`); we accept the trailing argument as the message and
/// ignore the position. A literal message yields its contents verbatim (the B87
/// path, unchanged). An interpolated message (`s!"got {x}"`) is rendered by
/// concatenating its literal chunks with the rendered values of its embedded
/// holes resolved through `bindings`; if any hole is unresolvable (stuck /
/// symbolic / unbound / unsupported) the whole message declines (`None`) so the
/// caller defers honestly rather than guessing. Any other message shape (a bare
/// identifier, a `MessageData` builder, …) also declines. Descends through
/// parentheses.
///
/// `pub(crate)` so the macro-expansion path
/// ([`crate::macro_integration::computed_body`]) reuses the *same*
/// `throwError`/`s!"…"` recognition + interpolation rendering to surface a
/// `throwError` raised inside a computed `macro_rules` body as a real macro
/// diagnostic (B87/B89 machinery, shared rather than duplicated).
pub(crate) fn as_throw_error_message_in(
    expr: &SurfaceExpr,
    bindings: &[Binding],
) -> Option<String> {
    match expr {
        SurfaceExpr::App(_, func, args) => {
            let SurfaceExpr::Ident(_, name) = func.as_ref() else {
                return None;
            };
            if !is_throw_error_op(name) {
                return None;
            }
            // The message is the final positional argument (so `throwError "m"`
            // and `throwErrorAt stx "m"` both name the trailing message). A named
            // argument is not the positional message form, so defer.
            let last = args.last()?;
            if last.name.is_some() {
                return None;
            }
            match &last.expr {
                SurfaceExpr::Lit(_, SurfaceLit::String(message)) => Some(message.clone()),
                SurfaceExpr::InterpolatedStr { parts, .. } => render_interpolation(parts, bindings),
                _ => None,
            }
        }
        SurfaceExpr::Paren(_, inner) => as_throw_error_message_in(inner, bindings),
        _ => None,
    }
}

/// If `tac` is a supported terminal `throwError "msg"` tactic, return its message
/// rendered against `bindings`. A bare tactic-position `throwError "msg"` parses
/// as a `Named { "throwError", ["msg"] }` call; the term-position spelling is a
/// `Term(throwError "msg")`. Both yield the message (a literal, or a fully
/// resolvable interpolation); any unresolvable interpolation, non-string message,
/// or non-throw head returns `None`.
fn tactic_throw_error_message_in(tac: &SurfaceTactic, bindings: &[Binding]) -> Option<String> {
    match tac {
        SurfaceTactic::Named { name, args, .. } if is_throw_error_op(name) => match args.last()? {
            SurfaceExpr::Lit(_, SurfaceLit::String(message)) => Some(message.clone()),
            SurfaceExpr::InterpolatedStr { parts, .. } => render_interpolation(parts, bindings),
            _ => None,
        },
        SurfaceTactic::Term(_, expr) => as_throw_error_message_in(expr, bindings),
        _ => None,
    }
}

/// Lower a `do`-block action expression to the tactic call it denotes.
///
/// `App(Ident(name), args)` -> `Named { name, args }` (substituted); a bare
/// `Ident(name)` -> nullary `Named { name }`. Returns `None` (deferring the
/// whole block) for any other expression shape and for actions headed by a
/// metaprogramming-monad operation (see [`is_metaprogramming_monad_op`]).
fn action_expr_to_tactic(expr: &SurfaceExpr, bindings: &[Binding]) -> Option<SurfaceTactic> {
    match expr {
        SurfaceExpr::App(span, func, args) => {
            let SurfaceExpr::Ident(_, name) = func.as_ref() else {
                return None;
            };
            if is_metaprogramming_monad_op(name) {
                return None;
            }
            let lowered_args: Vec<SurfaceExpr> = args
                .iter()
                .map(|a| substitute_in_expr(&a.expr, bindings))
                .collect();
            // Goal-closing keywords (`exact`/`apply`/`refine`/`show`) take a
            // SINGLE term argument. In term position `exact f x` parses as
            // `App(exact, [f, x])`, so the trailing args (`x`) belong to the
            // term `(f x)`, not as separate tactic arguments. Fold them back
            // into one applied term, mirroring how `by exact f x` parses (the
            // tactic dispatcher gives `exact` the full `f x` application).
            let folded_args = if is_term_arg_close_keyword(name) && lowered_args.len() > 1 {
                let mut it = lowered_args.into_iter();
                let head = it.next().expect("len > 1 guarantees a head");
                let rest: Vec<SurfaceArg> = it.map(SurfaceArg::positional).collect();
                let applied = SurfaceExpr::App(*span, Box::new(head), rest);
                vec![applied]
            } else {
                lowered_args
            };
            Some(SurfaceTactic::Named {
                span: *span,
                name: name.clone(),
                args: folded_args,
            })
        }
        SurfaceExpr::Ident(span, name) => {
            if is_metaprogramming_monad_op(name) {
                return None;
            }
            Some(SurfaceTactic::Named {
                span: *span,
                name: name.clone(),
                args: Vec::new(),
            })
        }
        // Parenthesized action: descend.
        SurfaceExpr::Paren(_, inner) => action_expr_to_tactic(inner, bindings),
        _ => None,
    }
}

/// Insert or replace a binding for `name` with `replacement`.
///
/// A later `do` binding shadows an earlier same-named one (matching block
/// scoping), so replace in place when present.
fn upsert_binding(bindings: &mut Vec<Binding>, name: &str, replacement: SurfaceExpr) {
    if let Some(slot) = bindings.iter_mut().find(|(n, _)| n == name) {
        slot.1 = replacement;
    } else {
        bindings.push((name.to_owned(), replacement));
    }
}

// ===========================================================================
// Phase 6: variadic (trailing-repetition) user tactics
// ===========================================================================
//
// A user tactic declared with a single TRAILING repetition variable —
//
//     elab "intros2" xs:ident* : tactic => intro xs
//     elab "exactFirst" x:term ys:term,* : tactic => exact x   -- (fixed + rep)
//
// is VARIADIC: the call site supplies any number of trailing arguments
// (`intros2 a b c`). The repetition variable `xs` binds the entire variadic
// tail as a LIST `[a, b, c]`, and the body is EXPANDED before delegation:
//
//   * a body tactic that MENTIONS the repetition var is replicated once per
//     list element, with the repetition var replaced by that single element
//     (so `intro xs` over `[a, b, c]` expands to `intro a; intro b; intro c`);
//   * a body tactic that does NOT mention the repetition var is emitted once,
//     unchanged (after the usual fixed-prefix substitution).
//
// The expanded flat sequence is then handed to the SAME `eval.eval_seq`
// delegation path Phase 1 uses — so soundness is unchanged: a variadic user
// tactic can do nothing a hand-written `by` block of the expanded tactics could
// not. Goals close exclusively through the normal kernel-checked tactic effects;
// the expansion only chooses WHICH (and how many) delegated tactics run.
//
// # Expansion semantics (precise)
//
// Given fixed prefix bindings `f_1..f_k` (k = number of non-repetition bound
// vars) bound 1:1 to the first k call-site args, and the repetition var `xs`
// bound to the remaining args `[e_1..e_n]`:
//
//   For each body tactic `t` (in order):
//     if `t` references `xs`:
//        emit  subst(t, {f_i}, xs := e_1),
//              subst(t, {f_i}, xs := e_2), ...,
//              subst(t, {f_i}, xs := e_n)      -- n copies (n may be 0)
//     else:
//        emit  subst(t, {f_i})                 -- one copy
//
// `n == 0` (zero variadic args) is legal: repetition-mentioning tactics expand
// to nothing, non-mentioning tactics still run once. A `do`-notation variadic
// body is DEFERRED (see [`build_variadic_tactic_handler`]): the per-element
// replication of `do` statements needs more design than the flat case.

/// Execute a lowered user-tactic body against the proof state.
///
/// Shared by the user-tactic compound handler and the proof-site `by do …`
/// dispatch ([`run_tactic_do_block`]). Every branch routes through a
/// kernel-checked path: `eval_seq` (Phase 1/2), `run_runtime_elab_close`
/// (Phase 3), `run_do_exec` (Phase 7/8), or an honest `UserThrowError`.
fn run_lowered_body(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    lowered: LoweredBody,
) -> Result<(), TacticError> {
    match lowered {
        LoweredBody::Delegate(tactics) => eval.eval_seq(ps, &tactics),
        LoweredBody::RuntimeElabClose { prefix, close } => {
            run_runtime_elab_close(eval, ps, &prefix, &close)
        }
        LoweredBody::DoExec { elems, seed } => run_do_exec(eval, ps, &elems, seed),
        LoweredBody::ThrowError { message } => Err(TacticError::UserThrowError { message }),
    }
}

/// Run a tactic-mode `do`-block at a proof site (`by do …`).
///
/// `body` is the parsed tactic sequence wrapping the `do` block — the parser
/// emits a `by do …` proof as `ByTactic([Term(Do(elems))])`, so this is invoked
/// with that single `Term(Do(..))` tactic. Reuses the exact same `lower_body`
/// machinery the user-defined `elab … : tactic => do …` bodies use, with no
/// call-site argument bindings (a proof-site `do` has no bound parameters).
///
/// # Soundness
///
/// Goal closure flows entirely through the kernel-checked paths in
/// [`run_lowered_body`]; this entry only sequences statements and never closes a
/// goal itself.
pub(super) fn run_tactic_do_block(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    body: &[SurfaceTactic],
) -> Result<(), TacticError> {
    let mut bindings: Vec<Binding> = Vec::new();
    let lowered =
        lower_body(body, &mut bindings).ok_or_else(|| TacticError::ElaborationFailed {
            detail: "unsupported `do`-block in tactic position".to_string(),
        })?;
    run_lowered_body(eval, ps, lowered)
}

/// Build a compound tactic handler that runs a user-defined tactic body by
/// substituting the call-site arguments for the pattern-bound variables and
/// delegating to the existing tactic evaluator.
///
/// `name` is the user tactic keyword (used only for diagnostics).
/// `bound_names` are the pattern variable names in declaration order.
/// `body` is the parsed tactic sequence (from `SurfaceExpr::ByTactic`): either a
/// flat Phase 1 sequence or a single `do`-notation body.
pub(super) fn build_user_tactic_handler(
    name: String,
    bound_names: Vec<String>,
    body: Vec<SurfaceTactic>,
) -> CompoundTacticEntry {
    let entry_name = name.clone();
    let handler: CompoundTacticHandler = Arc::new(move |eval, ps, tac| {
        let args = call_site_args(tac).ok_or_else(|| TacticError::ElaborationFailed {
            detail: format!("user tactic `{name}` invoked with unexpected syntax"),
        })?;
        if args.len() != bound_names.len() {
            return Err(TacticError::MissingArgument {
                tactic: name.clone(),
                expected: format!(
                    "{} argument(s) ({}), received {}",
                    bound_names.len(),
                    bound_names.join(", "),
                    args.len()
                ),
            });
        }
        // Seed the substitution map with the call-site argument bindings.
        let mut bindings: Vec<Binding> = bound_names
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();

        let lowered =
            lower_body(&body, &mut bindings).ok_or_else(|| TacticError::ElaborationFailed {
                detail: format!("unsupported body for user tactic `{name}`"),
            })?;
        run_lowered_body(eval, ps, lowered)
    });
    CompoundTacticEntry {
        name: entry_name,
        handler,
    }
}

/// Build a compound tactic handler for a VARIADIC user tactic — one declared
/// with a single trailing repetition variable (`elab "kw" .. xs:CAT* : tactic`).
///
/// `name` is the user tactic keyword (diagnostics + dispatch).
/// `fixed_names` are the leading non-repetition bound vars (1:1 with the first
/// `fixed_names.len()` call-site args; may be empty).
/// `rep_name` is the repetition variable (binds the remaining args as a list).
/// `body` is the parsed flat tactic sequence (from `SurfaceExpr::ByTactic`).
///
/// At least `fixed_names.len()` call-site args are required (the fixed prefix);
/// every additional arg is a repetition element. The body is expanded per
/// [the module's Phase 6 semantics](self) and the resulting flat sequence is
/// delegated to `eval.eval_seq` — the SAME kernel-checked path Phase 1 uses.
///
/// A `do`-notation variadic body is deferred (honest error): per-element
/// replication of `do` statements is out of Phase 6 scope.
pub(super) fn build_variadic_tactic_handler(
    name: String,
    fixed_names: Vec<String>,
    rep_name: String,
    body: Vec<SurfaceTactic>,
) -> CompoundTacticEntry {
    let entry_name = name.clone();
    let handler: CompoundTacticHandler = Arc::new(move |eval, ps, tac| {
        let args = call_site_args(tac).ok_or_else(|| TacticError::ElaborationFailed {
            detail: format!("user tactic `{name}` invoked with unexpected syntax"),
        })?;
        if args.len() < fixed_names.len() {
            return Err(TacticError::MissingArgument {
                tactic: name.clone(),
                expected: format!(
                    "at least {} argument(s) ({}{}), received {}",
                    fixed_names.len(),
                    fixed_names.join(", "),
                    if fixed_names.is_empty() {
                        format!("{rep_name}*")
                    } else {
                        format!(", {rep_name}*")
                    },
                    args.len()
                ),
            });
        }

        // Bind the fixed prefix 1:1; the remaining args form the repetition list.
        let (fixed_args, rep_args) = args.split_at(fixed_names.len());
        let fixed_bindings: Vec<Binding> = fixed_names
            .iter()
            .cloned()
            .zip(fixed_args.iter().cloned())
            .collect();

        // A variadic `do`-notation body is not expanded (deferred): only a flat
        // tactic sequence is replicated per repetition element.
        if as_do_block(&body).is_some() {
            return Err(TacticError::ElaborationFailed {
                detail: format!(
                    "user tactic `{name}` uses a do-notation body with a repetition \
                     argument, which is not yet supported (Phase 6 supports flat \
                     tactic-sequence variadic bodies)"
                ),
            });
        }

        let expanded = expand_variadic_body(&body, &fixed_bindings, &rep_name, rep_args);
        eval.eval_seq(ps, &expanded)
    });
    CompoundTacticEntry {
        name: entry_name,
        handler,
    }
}

/// Expand a flat variadic tactic body per the Phase 6 semantics (see module
/// docs): a body tactic that references `rep_name` is replicated once per
/// `rep_args` element (with `rep_name` bound to that element); a body tactic
/// that does not reference `rep_name` is emitted once with only the fixed
/// bindings applied.
///
/// Returns the fully-substituted flat sequence ready for `eval_seq`.
fn expand_variadic_body(
    body: &[SurfaceTactic],
    fixed_bindings: &[Binding],
    rep_name: &str,
    rep_args: &[SurfaceExpr],
) -> Vec<SurfaceTactic> {
    let mut out = Vec::with_capacity(body.len().saturating_mul(rep_args.len().max(1)));
    for tac in body {
        if tactic_mentions(tac, rep_name) {
            // Replicate once per repetition element, binding `rep_name` to it.
            for element in rep_args {
                let mut bindings = fixed_bindings.to_vec();
                upsert_binding(&mut bindings, rep_name, element.clone());
                out.push(substitute_in_tactic(tac, &bindings));
            }
        } else {
            // No repetition reference: emit once with only the fixed bindings.
            out.push(substitute_in_tactic(tac, fixed_bindings));
        }
    }
    out
}

/// Whether a tactic node textually references the identifier `name` anywhere in
/// its `SurfaceExpr` payloads. Used to decide whether a body tactic participates
/// in per-element repetition expansion.
fn tactic_mentions(tac: &SurfaceTactic, name: &str) -> bool {
    match tac {
        SurfaceTactic::Named { args, .. } => args.iter().any(|a| expr_mentions(a, name)),
        SurfaceTactic::Term(_, expr) => expr_mentions(expr, name),
        // Other tactic shapes are passed through unchanged by substitution, so
        // they cannot meaningfully reference the repetition var for expansion.
        _ => false,
    }
}

/// Whether a surface expression references the identifier `name`, descending
/// through the same shapes [`substitute_in_expr`] rewrites (so "mentions" and
/// "substitutes" stay consistent).
fn expr_mentions(expr: &SurfaceExpr, name: &str) -> bool {
    match expr {
        SurfaceExpr::Ident(_, n) => n == name,
        SurfaceExpr::App(_, func, args) => {
            expr_mentions(func, name) || args.iter().any(|a| expr_mentions(&a.expr, name))
        }
        SurfaceExpr::Paren(_, inner) | SurfaceExpr::Explicit(_, inner) => {
            expr_mentions(inner, name)
        }
        SurfaceExpr::Ascription(_, inner, ty) => {
            expr_mentions(inner, name) || expr_mentions(ty, name)
        }
        // Leaf / unsupported shapes: substitution leaves them unchanged, so they
        // do not participate in expansion.
        _ => false,
    }
}

/// Lower the (already pattern-bound) body to an execution plan.
///
/// For a do-block, prefers in order:
/// 1. Phase 7 [`LoweredBody::DoExec`] when the block contains a value bind
///    (`let x <- tac`) — interpreted statefully so the bind reads the tactic's
///    value out of the proof state;
/// 2. Phase 3 [`LoweredBody::RuntimeElabClose`] for `do let x := <expr>; exact
///    <expr>` (runtime sub-expression elaboration);
/// 3. Phase 2 [`LoweredBody::Delegate`] flat-sequence lowering.
///
/// A flat (non-`do`) body always lowers via the Phase 1 substitute-and-delegate
/// path. `bindings` is seeded with the call-site argument bindings; the runtime
/// plan is tried on a clone first so a partial match never leaves `bindings`
/// mutated for the fallback path.
fn lower_body(body: &[SurfaceTactic], bindings: &mut Vec<Binding>) -> Option<LoweredBody> {
    if let Some(elems) = as_do_block(body) {
        // Phase 7: a value bind is run statefully by the executor, seeded with
        // the current call-site bindings.
        if do_block_is_exec_interpretable(elems) {
            return Some(LoweredBody::DoExec {
                elems: elems.to_vec(),
                seed: bindings.clone(),
            });
        }
        // Try the runtime-elaboration shape on a scratch copy of the bindings so
        // a partial match never leaves `bindings` mutated for the fallback path.
        let mut scratch = bindings.clone();
        if let Some(close) = runtime_elab_close_plan(elems, &mut scratch) {
            *bindings = scratch;
            return Some(LoweredBody::RuntimeElabClose {
                prefix: Vec::new(),
                close,
            });
        }
        // Phase 2: lower the do-block to a flat delegated sequence.
        return do_block_to_tactics(elems, bindings).map(LoweredBody::Delegate);
    }
    // A bare (non-`do`) terminal `throwError "msg"` body raises the user's custom
    // error rather than mis-dispatching `throwError` as a non-existent tactic. In
    // tactic position the parser produces a `Named { "throwError", ["msg"] }` call
    // (a `Term(throwError "msg")` is the term-position spelling); recognize both.
    // The message may interpolate already-bound call-site values (`s!"got {x}"`),
    // rendered here against `bindings`; an unresolvable interpolation declines so
    // the body defers to the honest-error handler rather than fabricating text.
    if let [single] = body {
        if let Some(message) = tactic_throw_error_message_in(single, bindings) {
            return Some(LoweredBody::ThrowError { message });
        }
    }
    // Phase 1: flat tactic sequence — substitute and delegate.
    Some(LoweredBody::Delegate(
        body.iter()
            .map(|t| substitute_in_tactic(t, bindings))
            .collect(),
    ))
}

/// Extract the call-site argument expressions from the invoked tactic node.
///
/// User tactics are dispatched through `SurfaceTactic::Named`, so the arguments
/// are the `args` of that variant. Returns `None` for any other shape.
fn call_site_args(tac: &SurfaceTactic) -> Option<&[SurfaceExpr]> {
    match tac {
        SurfaceTactic::Named { args, .. } => Some(args),
        _ => None,
    }
}

/// Substitute the pattern bindings into a single tactic node.
///
/// Only the `SurfaceExpr` payloads carried by the tactic are rewritten; the
/// tactic structure itself is preserved. Bound variables appear inside those
/// expression payloads as bare identifiers (e.g. `exact e` carries `e` as an
/// argument expression), so replacing matching identifiers is sufficient for
/// the supported shapes (term/ident-argument tactics and flat sequences).
fn substitute_in_tactic(tac: &SurfaceTactic, bindings: &[Binding]) -> SurfaceTactic {
    match tac {
        SurfaceTactic::Named { span, name, args } => SurfaceTactic::Named {
            span: *span,
            name: name.clone(),
            args: args
                .iter()
                .map(|a| substitute_in_expr(a, bindings))
                .collect(),
        },
        SurfaceTactic::Term(span, expr) => {
            SurfaceTactic::Term(*span, Box::new(substitute_in_expr(expr, bindings)))
        }
        // Other tactic shapes are passed through unchanged. They are still
        // evaluated by the delegated evaluator; only the explicit substitution
        // of bound variables into the simple term/ident argument tactics is
        // performed here.
        other => other.clone(),
    }
}

/// Recursively substitute pattern bindings inside a surface expression.
///
/// Replaces every `SurfaceExpr::Ident(_, name)` whose `name` matches a bound
/// variable with the call-site argument expression, descending through the
/// expression shapes that appear in simple tactic arguments.
fn substitute_in_expr(expr: &SurfaceExpr, bindings: &[Binding]) -> SurfaceExpr {
    match expr {
        SurfaceExpr::Ident(_, name) => bindings
            .iter()
            .find(|(bound, _)| bound == name)
            .map_or_else(|| expr.clone(), |(_, replacement)| replacement.clone()),
        SurfaceExpr::App(span, func, args) => SurfaceExpr::App(
            *span,
            Box::new(substitute_in_expr(func, bindings)),
            args.iter()
                .map(|a| SurfaceArg {
                    span: a.span,
                    expr: substitute_in_expr(&a.expr, bindings),
                    name: a.name.clone(),
                })
                .collect(),
        ),
        SurfaceExpr::Paren(span, inner) => {
            SurfaceExpr::Paren(*span, Box::new(substitute_in_expr(inner, bindings)))
        }
        SurfaceExpr::Ascription(span, inner, ty) => SurfaceExpr::Ascription(
            *span,
            Box::new(substitute_in_expr(inner, bindings)),
            Box::new(substitute_in_expr(ty, bindings)),
        ),
        SurfaceExpr::Explicit(span, inner) => {
            SurfaceExpr::Explicit(*span, Box::new(substitute_in_expr(inner, bindings)))
        }
        // Leaf / unsupported shapes are returned unchanged: any bound variable
        // nested inside them is left for the evaluator to resolve (which fails
        // honestly if it cannot), never fabricating a success.
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_parser::{InterpolatedStringKind, Span, SurfaceBinder};

    fn ident(name: &str) -> SurfaceExpr {
        SurfaceExpr::Ident(Span::dummy(), name.to_owned())
    }

    fn named(name: &str, args: Vec<SurfaceExpr>) -> SurfaceTactic {
        SurfaceTactic::Named {
            span: Span::dummy(),
            name: name.to_owned(),
            args,
        }
    }

    fn app(head: &str, args: Vec<SurfaceExpr>) -> SurfaceExpr {
        SurfaceExpr::App(
            Span::dummy(),
            Box::new(ident(head)),
            args.into_iter().map(SurfaceArg::positional).collect(),
        )
    }

    fn do_body(elems: Vec<DoElem>) -> Vec<SurfaceTactic> {
        vec![SurfaceTactic::Term(
            Span::dummy(),
            Box::new(SurfaceExpr::Do(Span::dummy(), elems)),
        )]
    }

    fn binder(name: &str) -> SurfaceBinder {
        SurfaceBinder::new(name, None, clean_parser::SurfaceBinderInfo::Explicit)
    }

    #[test]
    fn test_substitute_in_expr_replaces_bound_ident() {
        let bindings = vec![("e".to_owned(), ident("h"))];
        let out = substitute_in_expr(&ident("e"), &bindings);
        assert!(
            matches!(&out, SurfaceExpr::Ident(_, n) if n == "h"),
            "bound `e` should become call-site `h`, got {out:?}"
        );
    }

    #[test]
    fn test_substitute_in_expr_leaves_unbound_ident() {
        let bindings = vec![("e".to_owned(), ident("h"))];
        let out = substitute_in_expr(&ident("other"), &bindings);
        assert!(
            matches!(&out, SurfaceExpr::Ident(_, n) if n == "other"),
            "unbound `other` should be unchanged, got {out:?}"
        );
    }

    #[test]
    fn test_substitute_in_tactic_rewrites_named_args() {
        let bindings = vec![("e".to_owned(), ident("h"))];
        let tac = named("exact", vec![ident("e")]);
        let out = substitute_in_tactic(&tac, &bindings);
        match out {
            SurfaceTactic::Named { name, args, .. } => {
                assert_eq!(name, "exact");
                assert_eq!(args.len(), 1);
                assert!(
                    matches!(&args[0], SurfaceExpr::Ident(_, n) if n == "h"),
                    "exact arg should be substituted to `h`, got {:?}",
                    args[0]
                );
            }
            other => panic!("expected Named, got {other:?}"),
        }
    }

    #[test]
    fn test_is_executable_tactic_body_accepts_named_sequence() {
        let body = vec![
            named("intro", vec![ident("h")]),
            named("exact", vec![ident("h")]),
        ];
        assert!(
            is_executable_tactic_body(&body),
            "flat Named sequence should be executable"
        );
    }

    #[test]
    fn test_is_executable_tactic_body_rejects_empty() {
        assert!(
            !is_executable_tactic_body(&[]),
            "an empty body has nothing to run and is not executable"
        );
    }

    #[test]
    fn test_substitute_in_expr_descends_into_application() {
        let bindings = vec![("e".to_owned(), ident("h"))];
        // f e  -> f h
        let out = substitute_in_expr(&app("f", vec![ident("e")]), &bindings);
        match out {
            SurfaceExpr::App(_, _, args) => {
                assert!(
                    matches!(&args[0].expr, SurfaceExpr::Ident(_, n) if n == "h"),
                    "nested arg should be substituted, got {:?}",
                    args[0].expr
                );
            }
            other => panic!("expected App, got {other:?}"),
        }
    }

    // ---- Phase 2: do-block lowering ---------------------------------------

    #[test]
    fn test_do_block_accepts_action_call() {
        // do exact e
        let body = do_body(vec![DoElem::Expr(
            Span::dummy(),
            Box::new(app("exact", vec![ident("e")])),
        )]);
        assert!(
            is_executable_tactic_body(&body),
            "`do exact e` action body should be executable"
        );
    }

    #[test]
    fn test_do_block_accepts_nullary_action() {
        // do rfl
        let body = do_body(vec![DoElem::Expr(Span::dummy(), Box::new(ident("rfl")))]);
        assert!(
            is_executable_tactic_body(&body),
            "`do rfl` nullary action body should be executable"
        );
    }

    #[test]
    fn test_do_block_lowers_action_to_named() {
        let elems = vec![DoElem::Expr(
            Span::dummy(),
            Box::new(app("intro", vec![ident("h")])),
        )];
        let tacs =
            do_block_to_tactics(&elems, &mut Vec::new()).expect("action lowers to a tactic seq");
        assert_eq!(tacs.len(), 1);
        match &tacs[0] {
            SurfaceTactic::Named { name, args, .. } => {
                assert_eq!(name, "intro");
                assert!(matches!(&args[0], SurfaceExpr::Ident(_, n) if n == "h"));
            }
            other => panic!("expected Named intro, got {other:?}"),
        }
    }

    #[test]
    fn test_do_block_pure_let_extends_substitution_and_emits_no_effect() {
        // do let x := hP; exact x   ==>   [exact hP]
        let elems = vec![
            DoElem::Let(Span::dummy(), binder("x"), Box::new(ident("hP"))),
            DoElem::Expr(Span::dummy(), Box::new(app("exact", vec![ident("x")]))),
        ];
        let tacs = do_block_to_tactics(&elems, &mut Vec::new())
            .expect("pure-let + action lowers to a tactic seq");
        // Only one effect (the `exact`); the let emits no tactic.
        assert_eq!(tacs.len(), 1, "pure let must not emit a tactic effect");
        match &tacs[0] {
            SurfaceTactic::Named { name, args, .. } => {
                assert_eq!(name, "exact");
                assert!(
                    matches!(&args[0], SurfaceExpr::Ident(_, n) if n == "hP"),
                    "`x` should be substituted to `hP`, got {:?}",
                    args[0]
                );
            }
            other => panic!("expected Named exact, got {other:?}"),
        }
    }

    #[test]
    fn test_do_block_intro_value_bind_routes_to_exec() {
        // Phase 7: `do let h <- intro; exact h` is no longer lowered to a flat
        // sequence by `do_block_to_tactics` (which now defers all binds); it is
        // classified as executor-interpretable and lowers to `DoExec`.
        let elems = vec![
            DoElem::Bind(Span::dummy(), binder("h"), Box::new(ident("intro"))),
            DoElem::Expr(Span::dummy(), Box::new(app("exact", vec![ident("h")]))),
        ];
        assert!(
            do_block_to_tactics(&elems, &mut Vec::new()).is_none(),
            "a value bind must no longer lower to a flat delegated sequence"
        );
        assert!(
            do_block_is_exec_interpretable(&elems),
            "intro value-bind do-block must be executor-interpretable"
        );
        // And `lower_body` routes it to the stateful `DoExec` plan.
        let body = do_body(elems);
        let mut bindings = Vec::new();
        match lower_body(&body, &mut bindings) {
            Some(LoweredBody::DoExec { elems, .. }) => {
                assert_eq!(elems.len(), 2, "DoExec carries the raw do statements");
            }
            other => panic!(
                "expected DoExec plan, got {}",
                match other {
                    Some(LoweredBody::Delegate(_)) => "Delegate",
                    Some(LoweredBody::RuntimeElabClose { .. }) => "RuntimeElabClose",
                    None => "None",
                    _ => "other",
                }
            ),
        }
    }

    #[test]
    fn test_is_value_yielding_bind_tac_accepts_nullary_intro() {
        assert!(
            is_value_yielding_bind_tac(&ident("intro")),
            "`intro` (no name arg) is value-yielding"
        );
        assert!(
            is_value_yielding_bind_tac(&ident("intros")),
            "`intros` (no name arg) is value-yielding"
        );
        assert!(
            !is_value_yielding_bind_tac(&app("intro", vec![ident("x")])),
            "`intro x` names the hypothesis explicitly and is not the value path"
        );
        assert!(
            !is_value_yielding_bind_tac(&ident("foo")),
            "a non-intro tactic yields no surface value"
        );
    }

    #[test]
    fn test_do_block_defers_non_intro_value_bind() {
        // do let h <- foo; exact h  — `foo` is not threadable, defer.
        let body = do_body(vec![
            DoElem::Bind(Span::dummy(), binder("h"), Box::new(ident("foo"))),
            DoElem::Expr(Span::dummy(), Box::new(app("exact", vec![ident("h")]))),
        ]);
        assert!(
            !is_executable_tactic_body(&body),
            "a non-intro value bind must be deferred (not executable)"
        );
    }

    #[test]
    fn test_do_block_defers_throw_error_monad_op() {
        // do logInfo "foo"; throwError "error"  — `logInfo` is a genuinely
        // unsupported monad op, so the whole body must defer (the honest-error
        // handler then surfaces the static `throwError` message). Note the
        // message arg here is a bare identifier, not a string literal.
        let body = do_body(vec![
            DoElem::Expr(Span::dummy(), Box::new(app("logInfo", vec![ident("foo")]))),
            DoElem::Expr(
                Span::dummy(),
                Box::new(app("throwError", vec![ident("error")])),
            ),
        ]);
        assert!(
            !is_executable_tactic_body(&body),
            "a do block containing an unsupported `logInfo` must be deferred"
        );
    }

    // ---- throwError: first-class custom errors ----------------------------

    fn str_lit(s: &str) -> SurfaceExpr {
        SurfaceExpr::Lit(Span::dummy(), SurfaceLit::String(s.to_owned()))
    }

    #[test]
    fn test_as_throw_error_message_extracts_string() {
        let call = app("throwError", vec![str_lit("custom message")]);
        assert_eq!(
            as_throw_error_message(&call).as_deref(),
            Some("custom message"),
            "`throwError \"custom message\"` must yield the literal message"
        );
    }

    #[test]
    fn test_as_throw_error_message_accepts_aliases_and_trailing_message() {
        // `throw "m"` (bare) and `throwErrorAt stx "m"` (position then message).
        assert_eq!(
            as_throw_error_message(&app("throw", vec![str_lit("m")])).as_deref(),
            Some("m")
        );
        assert_eq!(
            as_throw_error_message(&app("throwErrorAt", vec![ident("stx"), str_lit("m")]))
                .as_deref(),
            Some("m"),
            "throwErrorAt's trailing literal-string argument is the message"
        );
    }

    #[test]
    fn test_as_throw_error_message_rejects_non_literal_and_non_throw() {
        // A non-literal message (an identifier / interpolation) is deferred.
        assert!(
            as_throw_error_message(&app("throwError", vec![ident("msg")])).is_none(),
            "a non-string-literal message must not be recognized (deferred to static path)"
        );
        // A non-throw head is not a throwError.
        assert!(
            as_throw_error_message(&app("exact", vec![str_lit("m")])).is_none(),
            "`exact` is not a throwError op"
        );
    }

    #[test]
    fn test_do_block_terminal_throw_error_is_executor_interpretable() {
        // do throwError "custom message"  — a supported throwError body IS
        // executable (it raises the real typed error).
        let elems = vec![DoElem::Expr(
            Span::dummy(),
            Box::new(app("throwError", vec![str_lit("custom message")])),
        )];
        assert!(
            do_block_is_exec_interpretable(&elems),
            "a terminal `throwError \"msg\"` body must be executor-interpretable"
        );
        let body = do_body(elems);
        assert!(
            is_executable_tactic_body(&body),
            "a terminal `throwError \"msg\"` body must be executable"
        );
    }

    #[test]
    fn test_do_block_computed_if_throw_error_is_executor_interpretable() {
        // do if true then throwError "bad" else exact hP
        let elems = vec![DoElem::If(
            Span::dummy(),
            Box::new(ident("true")),
            vec![DoElem::Expr(
                Span::dummy(),
                Box::new(app("throwError", vec![str_lit("bad")])),
            )],
            Some(vec![DoElem::Expr(
                Span::dummy(),
                Box::new(app("exact", vec![ident("hP")])),
            )]),
        )];
        assert!(
            do_block_is_exec_interpretable(&elems),
            "a computed-if with a throwError branch must be executor-interpretable"
        );
    }

    #[test]
    fn test_tactic_throw_error_message_recognizes_named_and_term_forms() {
        // Bare tactic-position `throwError "m"` parses as a Named call.
        let named_throw = named("throwError", vec![str_lit("m")]);
        assert_eq!(
            tactic_throw_error_message_in(&named_throw, &[]).as_deref(),
            Some("m"),
            "a bare `throwError` Named tactic call must yield the message"
        );
        // Term-position spelling wraps the App.
        let term_throw = SurfaceTactic::Term(
            Span::dummy(),
            Box::new(app("throwError", vec![str_lit("m")])),
        );
        assert_eq!(
            tactic_throw_error_message_in(&term_throw, &[]).as_deref(),
            Some("m")
        );
        // A non-throw tactic is not a throwError.
        assert!(
            tactic_throw_error_message_in(&named("exact", vec![ident("hP")]), &[]).is_none(),
            "`exact hP` is not a throwError tactic"
        );
        // A non-literal message defers.
        assert!(
            tactic_throw_error_message_in(&named("throwError", vec![ident("msg")]), &[]).is_none(),
            "a non-string-literal message must not be recognized"
        );
    }

    /// Build a `SurfaceExpr::InterpolatedStr` from already-parsed parts.
    fn interp(kind: InterpolatedStringKind, parts: Vec<InterpolationPart>) -> SurfaceExpr {
        SurfaceExpr::InterpolatedStr {
            span: Span::dummy(),
            kind,
            parts,
        }
    }

    fn nat_lit(n: u64) -> SurfaceExpr {
        SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(n))
    }

    #[test]
    fn test_render_interpolation_concats_literals_and_bound_values() {
        // `s!"got {x}!"` with `x := 7` renders `got 7!`.
        let parts = vec![
            InterpolationPart::Literal("got ".to_owned()),
            InterpolationPart::Expr(ident("x")),
            InterpolationPart::Literal("!".to_owned()),
        ];
        let bindings: Vec<Binding> = vec![("x".to_owned(), nat_lit(7))];
        assert_eq!(
            render_interpolation(&parts, &bindings).as_deref(),
            Some("got 7!"),
            "a bound Nat value must render faithfully into the message"
        );
    }

    #[test]
    fn test_render_interpolation_unbound_hole_declines() {
        // `s!"got {x}"` with no binding for `x` declines (defers honestly).
        let parts = vec![
            InterpolationPart::Literal("got ".to_owned()),
            InterpolationPart::Expr(ident("x")),
        ];
        assert!(
            render_interpolation(&parts, &[]).is_none(),
            "an unbound interpolation hole must decline rather than fabricate a value"
        );
    }

    #[test]
    fn test_render_interpolation_application_hole_declines() {
        // A `{f x}` hole (an application) has no faithful textual rendering here.
        let parts = vec![InterpolationPart::Expr(app("f", vec![ident("x")]))];
        let bindings: Vec<Binding> = vec![("x".to_owned(), nat_lit(1))];
        assert!(
            render_interpolation(&parts, &bindings).is_none(),
            "an application hole must decline rather than guess a rendering"
        );
    }

    #[test]
    fn test_as_throw_error_message_in_renders_interpolation() {
        // `throwError s!"got {x}"` with `x := 3` yields `got 3`.
        let msg = interp(
            InterpolatedStringKind::String,
            vec![
                InterpolationPart::Literal("got ".to_owned()),
                InterpolationPart::Expr(ident("x")),
            ],
        );
        let call = app("throwError", vec![msg]);
        let bindings: Vec<Binding> = vec![("x".to_owned(), nat_lit(3))];
        assert_eq!(
            as_throw_error_message_in(&call, &bindings).as_deref(),
            Some("got 3"),
            "a fully-resolved interpolation message must render against the bindings"
        );
        // With no binding the same call declines (defers).
        assert!(
            as_throw_error_message_in(&call, &[]).is_none(),
            "an unresolved interpolation message must decline"
        );
    }

    #[test]
    fn test_as_throw_error_message_in_message_kinds_all_render() {
        // s!/m!/f! all render the same message text for an error.
        for kind in [
            InterpolatedStringKind::String,
            InterpolatedStringKind::MessageData,
            InterpolatedStringKind::Format,
        ] {
            let msg = interp(
                kind,
                vec![
                    InterpolationPart::Literal("v=".to_owned()),
                    InterpolationPart::Expr(str_lit("ok")),
                ],
            );
            let call = app("throwError", vec![msg]);
            assert_eq!(
                as_throw_error_message_in(&call, &[]).as_deref(),
                Some("v=ok"),
                "every interpolation kind must render the same error text"
            );
        }
    }

    #[test]
    fn test_is_throw_error_interpolation_shape_recognizes_and_rejects() {
        let interp_call = app(
            "throwError",
            vec![interp(
                InterpolatedStringKind::String,
                vec![InterpolationPart::Expr(ident("x"))],
            )],
        );
        assert!(
            is_throw_error_interpolation_shape(&interp_call),
            "a throwError applied to an interpolation must be recognized by shape"
        );
        // A literal-message throwError is NOT an interpolation shape (the literal
        // path handles it).
        assert!(
            !is_throw_error_interpolation_shape(&app("throwError", vec![str_lit("m")])),
            "a literal-message throwError is not an interpolation shape"
        );
        // A non-throw head is not recognized.
        assert!(
            !is_throw_error_interpolation_shape(&app(
                "exact",
                vec![interp(InterpolatedStringKind::String, vec![])]
            )),
            "an interpolation passed to a non-throw op is not a throwError shape"
        );
    }

    #[test]
    fn test_b87_literal_path_unchanged_through_env_aware_variant() {
        // The plain-literal B87 path is unchanged: a literal message renders to
        // itself regardless of bindings.
        let call = app("throwError", vec![str_lit("custom message")]);
        assert_eq!(
            as_throw_error_message(&call).as_deref(),
            Some("custom message"),
            "the B87 literal path must be unchanged"
        );
        assert_eq!(
            as_throw_error_message_in(&call, &[("x".to_owned(), nat_lit(9))]).as_deref(),
            Some("custom message"),
            "bindings must not affect a plain-literal message"
        );
    }

    #[test]
    fn test_lower_body_picks_throw_error_for_bare_named_throw() {
        // A flat body `[Named { throwError, ["m"] }]` lowers to the ThrowError plan.
        let body = vec![named("throwError", vec![str_lit("boom")])];
        let mut bindings = Vec::new();
        match lower_body(&body, &mut bindings) {
            Some(LoweredBody::ThrowError { message }) => assert_eq!(message, "boom"),
            other => panic!(
                "expected ThrowError plan, got {}",
                match other {
                    Some(LoweredBody::Delegate(_)) => "Delegate",
                    Some(LoweredBody::RuntimeElabClose { .. }) => "RuntimeElabClose",
                    Some(LoweredBody::DoExec { .. }) => "DoExec",
                    None => "None",
                    _ => "other",
                }
            ),
        }
    }

    #[test]
    fn test_do_block_computed_if_with_unsupported_branch_defers() {
        // do if true then logInfo "x" else exact hP  — `logInfo` in a branch is
        // genuinely unsupported, so the whole block must defer.
        let elems = vec![DoElem::If(
            Span::dummy(),
            Box::new(ident("true")),
            vec![DoElem::Expr(
                Span::dummy(),
                Box::new(app("logInfo", vec![str_lit("x")])),
            )],
            Some(vec![DoElem::Expr(
                Span::dummy(),
                Box::new(app("exact", vec![ident("hP")])),
            )]),
        )];
        assert!(
            !do_block_is_exec_interpretable(&elems),
            "a computed-if branch with an unsupported op must defer the whole block"
        );
    }

    #[test]
    fn test_do_block_defers_control_flow() {
        // do for x in xs do skip  — control flow, deferred.
        let body = do_body(vec![DoElem::For(
            Span::dummy(),
            binder("x"),
            Box::new(ident("xs")),
            vec![DoElem::Expr(Span::dummy(), Box::new(ident("skip")))],
        )]);
        assert!(
            !is_executable_tactic_body(&body),
            "a do `for` loop body must be deferred (not executable)"
        );
    }

    #[test]
    fn test_do_block_defers_empty() {
        let body = do_body(vec![]);
        assert!(
            !is_executable_tactic_body(&body),
            "an empty do block has nothing to run and is not executable"
        );
    }

    // ---- Phase 3: runtime sub-expression elaboration ---------------------

    #[test]
    fn test_runtime_elab_close_plan_detects_let_then_exact() {
        // do let x := f e; exact x   ==> runtime-elaborate `f e`, close.
        let elems = vec![
            DoElem::Let(
                Span::dummy(),
                binder("x"),
                Box::new(app("f", vec![ident("e")])),
            ),
            DoElem::Expr(Span::dummy(), Box::new(app("exact", vec![ident("x")]))),
        ];
        // Seed `e -> hP` (call-site arg binding).
        let mut bindings = vec![("e".to_owned(), ident("hP"))];
        let close = runtime_elab_close_plan(&elems, &mut bindings)
            .expect("let-then-exact should yield a runtime close expression");
        // `x` resolves to `f hP` (the let RHS with `e` substituted to `hP`).
        match close {
            SurfaceExpr::App(_, func, args) => {
                assert!(matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "f"));
                assert!(
                    matches!(&args[0].expr, SurfaceExpr::Ident(_, n) if n == "hP"),
                    "argument should be substituted to `hP`, got {:?}",
                    args[0].expr
                );
            }
            other => panic!("expected App(f, hP), got {other:?}"),
        }
    }

    #[test]
    fn test_runtime_elab_close_plan_rejects_bare_exact() {
        // do exact e  — no value let, so the delegate path handles it (no runtime).
        let elems = vec![
            DoElem::Expr(Span::dummy(), Box::new(app("exact", vec![ident("e")]))),
            DoElem::Expr(Span::dummy(), Box::new(ident("rfl"))),
        ];
        let mut bindings = Vec::new();
        assert!(
            runtime_elab_close_plan(&elems, &mut bindings).is_none(),
            "a do-block with no value let must not take the runtime path"
        );
    }

    #[test]
    fn test_runtime_elab_close_plan_rejects_non_close_terminal() {
        // do let x := e; intro x  — terminal is not exact/refine, defer.
        let elems = vec![
            DoElem::Let(Span::dummy(), binder("x"), Box::new(ident("e"))),
            DoElem::Expr(Span::dummy(), Box::new(app("intro", vec![ident("x")]))),
        ];
        let mut bindings = Vec::new();
        assert!(
            runtime_elab_close_plan(&elems, &mut bindings).is_none(),
            "a non-exact/refine terminal must not take the runtime path"
        );
    }

    #[test]
    fn test_lower_body_picks_runtime_path_for_let_then_exact() {
        let body = do_body(vec![
            DoElem::Let(
                Span::dummy(),
                binder("x"),
                Box::new(app("f", vec![ident("e")])),
            ),
            DoElem::Expr(Span::dummy(), Box::new(app("exact", vec![ident("x")]))),
        ]);
        let mut bindings = vec![("e".to_owned(), ident("hP"))];
        match lower_body(&body, &mut bindings) {
            Some(LoweredBody::RuntimeElabClose { prefix, close }) => {
                assert!(prefix.is_empty(), "value-let plan has no tactic prefix");
                assert!(matches!(close, SurfaceExpr::App(..)), "close is `f hP`");
            }
            other => panic!(
                "expected RuntimeElabClose plan, got a different lowering: {}",
                match other {
                    Some(LoweredBody::Delegate(_)) => "Delegate",
                    None => "None",
                    _ => "other",
                }
            ),
        }
    }

    #[test]
    fn test_lower_body_keeps_delegate_for_plain_sequence() {
        // A flat sequence stays on the delegate path.
        let body = vec![
            named("intro", vec![ident("h")]),
            named("exact", vec![ident("h")]),
        ];
        let mut bindings = Vec::new();
        assert!(
            matches!(
                lower_body(&body, &mut bindings),
                Some(LoweredBody::Delegate(_))
            ),
            "a flat tactic sequence must lower to the delegate path"
        );
    }

    #[test]
    fn test_do_block_defers_pure_let_only() {
        // do let x := hP   — no tactic effect, not executable.
        let body = do_body(vec![DoElem::Let(
            Span::dummy(),
            binder("x"),
            Box::new(ident("hP")),
        )]);
        assert!(
            !is_executable_tactic_body(&body),
            "a do block of only pure lets has no effect and is not executable"
        );
    }

    // ----- Phase 6: variadic expansion -----

    fn tactic_name(tac: &SurfaceTactic) -> &str {
        match tac {
            SurfaceTactic::Named { name, .. } => name,
            _ => "<not-named>",
        }
    }

    fn tactic_single_arg_ident(tac: &SurfaceTactic) -> &str {
        match tac {
            SurfaceTactic::Named { args, .. } => match args.first() {
                Some(SurfaceExpr::Ident(_, n)) => n,
                _ => "<not-ident-arg>",
            },
            _ => "<not-named>",
        }
    }

    #[test]
    fn test_expr_mentions_detects_bound_var() {
        assert!(expr_mentions(&ident("xs"), "xs"));
        assert!(!expr_mentions(&ident("ys"), "xs"));
        // Nested under an application.
        assert!(expr_mentions(
            &app("f", vec![ident("a"), ident("xs")]),
            "xs"
        ));
        assert!(!expr_mentions(
            &app("f", vec![ident("a"), ident("b")]),
            "xs"
        ));
    }

    #[test]
    fn test_expand_variadic_body_replicates_rep_tactic_per_element() {
        // Body: `intro xs` — one repetition-mentioning tactic.
        let body = vec![named("intro", vec![ident("xs")])];
        let rep_args = vec![ident("a"), ident("b"), ident("c")];
        let out = expand_variadic_body(&body, &[], "xs", &rep_args);
        assert_eq!(out.len(), 3, "should expand to one `intro` per element");
        assert_eq!(tactic_single_arg_ident(&out[0]), "a");
        assert_eq!(tactic_single_arg_ident(&out[1]), "b");
        assert_eq!(tactic_single_arg_ident(&out[2]), "c");
    }

    #[test]
    fn test_expand_variadic_body_emits_non_rep_tactic_once() {
        // Body: `intro xs; exact hP` — `exact hP` does not mention `xs`.
        let body = vec![
            named("intro", vec![ident("xs")]),
            named("exact", vec![ident("hP")]),
        ];
        let rep_args = vec![ident("a"), ident("b")];
        let out = expand_variadic_body(&body, &[], "xs", &rep_args);
        // 2 expanded `intro` + 1 `exact` = 3 tactics.
        assert_eq!(out.len(), 3);
        assert_eq!(tactic_name(&out[0]), "intro");
        assert_eq!(tactic_single_arg_ident(&out[0]), "a");
        assert_eq!(tactic_single_arg_ident(&out[1]), "b");
        assert_eq!(tactic_name(&out[2]), "exact");
        assert_eq!(tactic_single_arg_ident(&out[2]), "hP");
    }

    #[test]
    fn test_expand_variadic_body_zero_args_drops_rep_keeps_non_rep() {
        // Zero repetition elements: `intro xs` expands to nothing; `exact hP`
        // still runs once.
        let body = vec![
            named("intro", vec![ident("xs")]),
            named("exact", vec![ident("hP")]),
        ];
        let out = expand_variadic_body(&body, &[], "xs", &[]);
        assert_eq!(out.len(), 1, "only the non-repetition tactic survives");
        assert_eq!(tactic_name(&out[0]), "exact");
        assert_eq!(tactic_single_arg_ident(&out[0]), "hP");
    }

    #[test]
    fn test_expand_variadic_body_applies_fixed_prefix_bindings() {
        // Fixed prefix `x -> hP`; body `exact x; intro xs`. The non-rep `exact x`
        // gets the fixed binding; the rep `intro xs` is replicated.
        let body = vec![
            named("exact", vec![ident("x")]),
            named("intro", vec![ident("xs")]),
        ];
        let fixed = vec![("x".to_owned(), ident("hP"))];
        let rep_args = vec![ident("a")];
        let out = expand_variadic_body(&body, &fixed, "xs", &rep_args);
        assert_eq!(out.len(), 2);
        assert_eq!(tactic_name(&out[0]), "exact");
        assert_eq!(
            tactic_single_arg_ident(&out[0]),
            "hP",
            "fixed-prefix binding `x -> hP` should apply to non-rep tactic"
        );
        assert_eq!(tactic_name(&out[1]), "intro");
        assert_eq!(tactic_single_arg_ident(&out[1]), "a");
    }
}
