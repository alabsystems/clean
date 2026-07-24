// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Supporting types for tactic and do-block AST nodes.
//!
//! Split from `surface_tactic.rs` to maintain the 500-line file limit.
//! Contains `SurfaceCalcStep`, `SurfaceCalcJustification`, `TacticMatchArm`,
//! `DoElem`, and `DoMatchArm`.

use crate::surface::{Span, SurfaceBinder, SurfaceExpr, SurfacePattern};
use crate::surface_tactic::SurfaceTactic;

/// A step in a `calc` proof block
#[derive(Debug, Clone)]
pub struct SurfaceCalcStep {
    pub span: Span,
    /// The relation expression (e.g., `a = b`, `a ≤ b`)
    pub rel: SurfaceExpr,
    /// The justification (proof of this step)
    pub proof: SurfaceCalcJustification,
}

/// Justification for a calc step
#[derive(Debug, Clone)]
pub enum SurfaceCalcJustification {
    /// Explicit proof term: `_ = b := proof_term`
    Term(SurfaceExpr),
    /// Tactic proof: `_ = b := by tac_seq`
    Tactic(Vec<SurfaceTactic>),
}

/// A match arm in tactic mode: `| pat => tac_seq`
///
/// Each arm has a pattern and a tactic sequence body (unlike expression-mode
/// match arms which have expression bodies).
#[derive(Debug, Clone)]
pub struct TacticMatchArm {
    pub span: Span,
    pub pattern: SurfacePattern,
    pub tactics: Vec<SurfaceTactic>,
}

/// Element of a `do` block (monadic notation)
///
/// Each element represents one statement in a do-block. During elaboration,
/// these are desugared to chains of `Bind.bind` and `Pure.pure` calls.
#[derive(Debug, Clone)]
pub enum DoElem {
    /// Monadic bind: `let x <- e` or `x <- e`
    /// Desugars to: `Bind.bind e (fun x => rest)`
    Bind(Span, SurfaceBinder, Box<SurfaceExpr>),

    /// Let binding: `let x := e` (pure, not monadic)
    /// Desugars to: `let x := e in rest`
    Let(Span, SurfaceBinder, Box<SurfaceExpr>),

    /// Mutable let: `let mut x := e`
    /// For now, treated as a regular let (mutable variable lifting deferred)
    LetMut(Span, SurfaceBinder, Box<SurfaceExpr>),

    /// Recursive let binding: `let rec f (args) := e` or mutual recursion
    /// `let rec f (args) := e and g (args) := e`.
    /// Each element is a (binder, value) pair. Mutual recursion uses multiple entries.
    /// Desugars to recursive local declaration(s) whose scope is the remaining do-block.
    LetRec(Span, Vec<(SurfaceBinder, Box<SurfaceExpr>)>),

    /// Return: `return e`
    /// Desugars to: `Pure.pure e`
    Return(Span, Box<SurfaceExpr>),

    /// Expression statement: `e` (the last expression, or a sequenced action)
    /// If not last: desugars to `Bind.bind e (fun _ => rest)`
    /// If last: this is the final expression of the do block
    Expr(Span, Box<SurfaceExpr>),

    /// Conditional: `if cond then doSeq else doSeq`
    /// Branches contain nested do-element sequences.
    /// Desugars to: `if cond then (desugar thenBranch) else (desugar elseBranch)`
    If(Span, Box<SurfaceExpr>, Vec<DoElem>, Option<Vec<DoElem>>),

    /// If-let: `if let pat := scrutinee then doSeq else doSeq`
    /// Pattern-matching conditional in do blocks.
    /// Desugars to a match on the scrutinee with the pattern as one arm.
    IfLet(
        Span,
        SurfacePattern,
        Box<SurfaceExpr>,
        Vec<DoElem>,
        Option<Vec<DoElem>>,
    ),

    /// Decidable if: `if h : prop then doSeq else doSeq`
    /// Conditional with a proof witness binding.
    /// Desugars to: `dite prop (fun h => thenBranch) (fun h => elseBranch)`
    IfDecidable(
        Span,
        String,
        Box<SurfaceExpr>,
        Vec<DoElem>,
        Option<Vec<DoElem>>,
    ),

    /// Monadic for loop: `for x in xs do doSeq`
    /// Desugars to: `ForIn.forIn xs () (fun x _ => do body; Pure.pure (ForInStep.yield ()))`
    For(Span, SurfaceBinder, Box<SurfaceExpr>, Vec<DoElem>),

    /// Match in do block: `match discrs with | pat => doSeq ...`
    /// Each arm body is a do-element sequence.
    Match(Span, Vec<SurfaceExpr>, Vec<DoMatchArm>),

    /// Try/catch/finally: `try doSeq catch e => doSeq finally doSeq`
    ///
    /// Desugars to compositions of `MonadExcept.tryCatch` / `tryCatchThe` (for
    /// catch clauses) and `tryFinally` (for the finally clause). Multiple catch
    /// clauses are folded left: each wraps the previous body.
    ///
    /// Reference: Lean 4 `doTry` in `src/Lean/Parser/Do.lean:201-202`
    TryCatch(
        Span,
        /// The try body (do-element sequence)
        Vec<DoElem>,
        /// Zero or more catch clauses
        Vec<DoCatchClause>,
        /// Optional finally clause (do-element sequence)
        Option<Vec<DoElem>>,
    ),

    /// Refutable monadic bind: `let pat <- e | fallback`
    ///
    /// Desugars in two steps:
    /// 1. `let __x <- e` (plain monadic bind)
    /// 2. `match __x with | pat => rest | _ => fallback`
    ///
    /// Reference: Lean 4 `doPatDecl` in `src/Lean/Parser/Do.lean:88-90`
    LetElse(
        Span,
        /// The pattern to match against (e.g., `.some x`)
        SurfacePattern,
        /// The monadic action whose result is matched
        Box<SurfaceExpr>,
        /// The fallback do-sequence for non-matching patterns
        Vec<DoElem>,
    ),

    /// Refutable expression destructuring: `let_expr pat := e | fallback`
    /// or `let_expr pat <- e | fallback`
    ///
    /// The success path continues with the remaining do-elements; the fallback
    /// path evaluates the explicit fallback do-sequence.
    LetExpr(
        Span,
        SurfacePattern,
        Box<SurfaceExpr>,
        DoLetExprKind,
        Vec<DoElem>,
    ),

    /// Infinite loop: `repeat body`
    ///
    /// Desugars to `for _ in Lean.Loop.mk do body`, matching Lean 4's
    /// expansion of `doRepeat` through `ForIn` on `Lean.Loop`.
    ///
    /// Reference: Lean 4 `doRepeat` in `src/Lean/Parser/Do.lean`
    Repeat(Span, Vec<DoElem>),

    /// Conditional loop: `while cond do body`
    ///
    /// Desugars to a `ForIn` loop on `Lean.Loop` with a condition check
    /// that produces `ForInStep.done` when the condition is false.
    ///
    /// Reference: Lean 4 `doWhile` in `src/Lean/Parser/Do.lean`
    While(Span, Box<SurfaceExpr>, Vec<DoElem>),

    /// Debug trace: `dbg_trace msg`
    ///
    /// Desugars to `dbgTrace msg (fun () => rest)`.
    ///
    /// Reference: Lean 4 `doDbgTrace` in `src/Lean/Parser/Do.lean`
    DbgTrace(Span, Box<SurfaceExpr>),

    /// Break out of a for/repeat/while loop: `break`
    ///
    /// Sets `ControlInfo.breaks = true`. Elaboration uses `BreakT.break`
    /// (= `OptionT` failure at the break layer of the control stack).
    ///
    /// Reference: Lean 4 `doBreak` in `src/Lean/Parser/Do.lean`
    Break(Span),

    /// Continue to next iteration of a for/repeat/while loop: `continue`
    ///
    /// Sets `ControlInfo.continues = true`. Elaboration uses `ContinueT.continue`
    /// (= `OptionT` failure at the continue layer of the control stack).
    ///
    /// Reference: Lean 4 `doContinue` in `src/Lean/Parser/Do.lean`
    Continue(Span),

    /// Mutable variable reassignment: `x := new_val`
    ///
    /// Only valid when `x` was introduced by `let mut x := ...`.
    /// Sets `ControlInfo.reassigns += {x}`. Elaboration uses `StateT.set`
    /// with the updated state tuple.
    ///
    /// Reference: Lean 4 `doReassign` in `src/Lean/Parser/Do.lean:91-92`
    Reassign(Span, String, Box<SurfaceExpr>),

    /// Pattern reassignment: `(a, b) := expr`
    ///
    /// Destructures `expr` and reassigns each pattern variable.
    /// All pattern variables must be mutable (introduced by `let mut`).
    /// Sets `ControlInfo.reassigns += {vars in pattern}`.
    ///
    /// Desugared during elaboration to a let binding + individual reassigns
    /// using `Prod.fst`/`Prod.snd` projections.
    ///
    /// Reference: Lean 4 `doReassign` with `letPatDecl` in `src/Lean/Parser/Do.lean:104-105`
    PatternReassign(Span, SurfacePattern, Box<SurfaceExpr>),
}

/// Source form for `let_expr` destructuring in do-notation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DoLetExprKind {
    /// `let_expr pat := expr | fallback`
    Pure,
    /// `let_expr pat <- expr | fallback`
    Bind,
}

/// A match arm within a do block, where the body is a do-element sequence.
#[derive(Debug, Clone)]
pub struct DoMatchArm {
    pub span: Span,
    pub patterns: Vec<SurfacePattern>,
    pub body: Vec<DoElem>,
}

/// A catch clause in a try/catch block.
///
/// Supports two forms:
/// - `catch e => doSeq` — untyped, desugars to `MonadExcept.tryCatch`
/// - `catch e : ExcType => doSeq` — typed, desugars to `tryCatchThe ExcType`
///
/// Pattern-match catch (`catch | pat => doSeq`) is first rewritten to
/// `catch __x => match __x with | pat => doSeq` (matching Lean 4).
#[derive(Debug, Clone)]
pub struct DoCatchClause {
    pub span: Span,
    /// The exception binder name
    pub binder: String,
    /// Optional exception type annotation (if present, uses `tryCatchThe`)
    pub exc_type: Option<Box<SurfaceExpr>>,
    /// The handler body (do-element sequence)
    pub body: Vec<DoElem>,
}

impl DoElem {
    pub fn span(&self) -> Span {
        match self {
            DoElem::Bind(s, _, _)
            | DoElem::Let(s, _, _)
            | DoElem::LetMut(s, _, _)
            | DoElem::LetRec(s, _)
            | DoElem::Return(s, _)
            | DoElem::Expr(s, _)
            | DoElem::If(s, _, _, _)
            | DoElem::IfLet(s, _, _, _, _)
            | DoElem::IfDecidable(s, _, _, _, _)
            | DoElem::For(s, _, _, _)
            | DoElem::Match(s, _, _)
            | DoElem::TryCatch(s, _, _, _)
            | DoElem::LetElse(s, _, _, _)
            | DoElem::LetExpr(s, _, _, _, _)
            | DoElem::Repeat(s, _)
            | DoElem::While(s, _, _)
            | DoElem::DbgTrace(s, _)
            | DoElem::Break(s)
            | DoElem::Continue(s)
            | DoElem::Reassign(s, _, _)
            | DoElem::PatternReassign(s, _, _) => *s,
        }
    }
}
