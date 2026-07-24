// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic surface syntax types
//!
//! AST types for tactics, calc blocks, and do-notation parsed from Lean 4 source.
//! These are used by [`SurfaceExpr::ByTactic`], [`SurfaceExpr::CalcBlock`],
//! and [`SurfaceExpr::Do`] variants in the surface syntax.

use crate::surface::{Span, SurfaceExpr};
use crate::surface_tactic_types::{SurfaceCalcStep, TacticMatchArm};

/// A rewrite rule in `rw [rule1, rule2, ...]` syntax
#[derive(Debug, Clone)]
pub struct SurfaceRwRule {
    pub span: Span,
    /// Whether to rewrite right-to-left (← prefix)
    pub reverse: bool,
    /// The rewrite lemma/term
    pub term: SurfaceExpr,
}

/// Location specifier for tactics like `simp at h` or `rw [...] at *`
#[derive(Debug, Clone)]
pub enum SurfaceTacticLocation {
    /// Apply at specific hypotheses: `at h1 h2`
    Hyps(Vec<String>),
    /// Apply at specific hypotheses and the goal: `at h1 h2 ⊢` / `at h1 h2 |-`
    HypsAndGoal(Vec<String>),
    /// Apply at the goal (default, no `at` clause)
    Goal,
    /// Apply everywhere: `at *`
    Wildcard,
}

/// Argument in `enter [args]` conv navigation tactic.
/// Each arg is either a numeric index (navigate to i-th argument)
/// or a name (introduce variable and enter binder body).
#[derive(Debug, Clone)]
pub enum ConvEnterArg {
    /// Numeric index: `enter [1, 2]` navigates to arguments
    Index(i64),
    /// Named variable: `enter [x]` introduces x and enters binder
    Name(String),
}

/// A single `case` arm in `cases`/`induction` with-blocks:
/// `| constructor_name args => tactic_seq`
#[derive(Debug, Clone)]
pub struct SurfaceInductionAlt {
    pub span: Span,
    /// Constructor/case name
    pub name: String,
    /// Bound variable names for this case
    pub args: Vec<String>,
    /// Tactics for this case
    pub tactics: Vec<SurfaceTactic>,
}

/// Surface syntax for a single tactic
///
/// Represents parsed tactic syntax before elaboration. Each variant
/// corresponds to a Lean 4 tactic form. Simple tactics (nullary, term-arg,
/// ident-list, etc.) are dispatched via the `Named` variant through the
/// `TacticRegistry`. Compound tactics with sub-tactic sequences or complex
/// argument types retain dedicated variants for parser fidelity.
#[derive(Debug, Clone)]
pub enum SurfaceTactic {
    /// `cases e with | alt1 => ... | alt2 => ...`
    Cases(Span, Box<SurfaceExpr>, Vec<SurfaceInductionAlt>),

    /// `induction e (using r)? (generalizing x y …)? with | alt1 => … | alt2 => …`
    ///
    /// - `target` is the major premise (the hypothesis to induct on).
    /// - `using_recursor` is the optional `using <term>` recursor override
    ///   (`None` = the type's default `.rec`). Parsed as a full term so
    ///   qualified names like `Nat.rec` are captured intact.
    /// - `generalizing` is the optional `generalizing x y …` ident list: those
    ///   hypotheses are reverted into the goal before running the recursor and
    ///   re-introduced in each case, so each induction hypothesis is quantified
    ///   over them (`∀ x y, …`) rather than fixed.
    Induction {
        span: Span,
        target: Box<SurfaceExpr>,
        using_recursor: Option<Box<SurfaceExpr>>,
        generalizing: Vec<String>,
        alts: Vec<SurfaceInductionAlt>,
    },

    /// `rw [rule1, ← rule2] (at loc)?` - rewrite with given rules
    Rw(Span, Vec<SurfaceRwRule>, SurfaceTacticLocation),

    /// `simp` or `simp only [lemma1, lemma2]` with optional location
    Simp {
        span: Span,
        only: bool,
        lemmas: Vec<SurfaceExpr>,
        location: SurfaceTacticLocation,
    },

    /// `have h : T := proof`, `have : T := proof`, or `have h := proof`
    /// (tactic-mode have). The type annotation is `None` when omitted
    /// (`have h := term`), in which case the elaborator infers the hypothesis
    /// type from the elaborated proof term. The destructuring form
    /// (`have ⟨a, b⟩ := e`) is desugared to [`Self::Obtain`] at parse time, so
    /// it never reaches this variant.
    Have(
        Span,
        Option<String>,
        Option<Box<SurfaceExpr>>,
        Box<SurfaceTactic>,
    ),

    /// `let h : T := val` (tactic-mode let)
    Let(Span, String, Option<Box<SurfaceExpr>>, Box<SurfaceExpr>),

    /// `suffices h : T by tac_seq` or `suffices h : T from proof`
    Suffices(Span, Option<String>, Box<SurfaceExpr>, Vec<SurfaceTactic>),

    /// `case name (binders)* => tacs` - focus on a named case.
    ///
    /// The second field is the case tag; the third is the optional list of
    /// `binderIdent`s that rename the case's most-recently-introduced
    /// inaccessible hypotheses (Lean: `case tag x₁ … xₙ => tac`). An empty
    /// binder list is the plain `case tag => tac` form.
    Case(Span, String, Vec<String>, Vec<SurfaceTactic>),

    /// `all_goals tacs` - apply to all goals
    AllGoals(Span, Vec<SurfaceTactic>),

    /// `any_goals tacs` - apply to any goal that succeeds
    AnyGoals(Span, Vec<SurfaceTactic>),

    /// `try tacticSeq` - try a tactic sequence, succeed even if it fails
    Try(Span, Vec<SurfaceTactic>),

    /// `first | tac1 | tac2 | ...` - try tactics in order
    First(Span, Vec<Vec<SurfaceTactic>>),

    /// `repeat tacticSeq` - repeat a tactic sequence until it fails
    Repeat(Span, Vec<SurfaceTactic>),

    /// `tac1 <;> tac2` - apply tac2 to all goals produced by tac1
    SeqFocus(Span, Box<SurfaceTactic>, Box<SurfaceTactic>),

    /// `(tac1; tac2; ...)` - parenthesized tactic sequence (plain grouping)
    Paren(Span, Vec<SurfaceTactic>),

    /// `{ tac1; tac2 }` or `· tac1; tac2` - focus on first goal and require closure
    ///
    /// In Lean 4, braced blocks (`tacticSeqBracketed`) and cdot focus (`evalTacticCDot`)
    /// both use `closeUsingOrAdmit` which wraps `focusAndDone`: focus on goal 0,
    /// run tactics, then check zero unsolved goals remain.
    FocusBlock(Span, Vec<SurfaceTactic>),

    /// `focus tac` - focus on first goal without requiring closure
    ///
    /// Unlike `FocusBlock`, the explicit `focus` keyword does NOT check that the
    /// focused goal is closed after running the tactic.
    Focus(Span, Vec<SurfaceTactic>),

    /// `conv => tacs` - enter conversion mode
    Conv(Span, SurfaceTacticLocation, Vec<SurfaceTactic>),

    /// `arg i` - conv navigation: focus on i-th argument (negative = from end)
    ConvArg(Span, i64),

    /// `enter [args]` - conv navigation: compact path into subexpression
    ConvEnter(Span, Vec<ConvEnterArg>),

    /// `simp_rw [rules] (at loc)?` - simp with rewriting
    SimpRw(Span, Vec<SurfaceRwRule>, SurfaceTacticLocation),

    /// `calc` block inside tactic mode
    Calc(Span, Vec<SurfaceCalcStep>),

    /// `match discrs with | pat => tac_seq | ...` in tactic mode
    ///
    /// Like expression-mode match, but arm bodies are tactic sequences.
    /// Reference: Lean 4 `Lean.Parser.Tactic.match` in Tactic.lean
    Match(Span, Vec<SurfaceExpr>, Vec<TacticMatchArm>),

    /// `simpa` or `simpa only [lemmas] using h` - simp then close with `h`
    /// (or `assumption` when no `using` term is given).
    Simpa {
        span: Span,
        only: bool,
        lemmas: Vec<SurfaceExpr>,
        /// The optional `using <term>` proof term. When present, `simpa`
        /// simplifies both the goal and `term`'s type and closes the goal with
        /// the simplified term; when absent, it falls back to `assumption`.
        using_term: Option<SurfaceExpr>,
    },

    /// `obtain ⟨a, b⟩ := e` or `obtain pat : T := e` — destructure a term.
    ///
    /// Equivalent to `have h : T := e; rcases h with pat`. The `pattern` is the
    /// canonical anonymous-constructor pattern text (e.g. `⟨a, b⟩`, `⟨⟨a, b⟩, c⟩`,
    /// or a single name `h`) consumed by the elaborator's recursive-intro pattern
    /// engine. `ty` is the optional `: T` ascription; `term` is the RHS scrutinee.
    Obtain {
        span: Span,
        pattern: String,
        ty: Option<Box<SurfaceExpr>>,
        term: Box<SurfaceExpr>,
    },

    /// `rcases h with ⟨hp, hq⟩` — destructure an EXISTING hypothesis in place.
    ///
    /// Unlike [`Self::Obtain`], the scrutinee `term` is an already-introduced
    /// hypothesis (resolved to its binder name in the elaborator); there is no
    /// `have`/copy step. The `pattern` is the canonical anonymous-constructor
    /// pattern text (e.g. `⟨a, b⟩`, `⟨a, ⟨b, c⟩⟩`, or a single name) consumed by
    /// the same recursive-intro pattern engine that backs `obtain`. The `with`
    /// keyword separates the scrutinee from the pattern.
    RCases {
        span: Span,
        term: Box<SurfaceExpr>,
        pattern: String,
    },

    /// `rintro ⟨hp, hq⟩ h _` — recursive intro with destructuring patterns.
    ///
    /// `rintro pat₁ pat₂ …` is exactly `intro <fresh> ; rcases <fresh> with patᵢ`
    /// for each pattern in order. Each `pattern` is the canonical
    /// anonymous-constructor pattern text (`⟨a, b⟩`, `⟨a, ⟨b, c⟩⟩`, a single name,
    /// or `_`) consumed by the SAME recursive-intro pattern engine that backs
    /// `obtain`/`rcases` (`destruct_named_hypothesis`).
    ///
    /// Capturing the pattern as source text (rather than parsing `⟨…⟩` as a
    /// term-mode anonymous-constructor expression and feeding it to the registry
    /// dispatcher) is what keeps the introduced hypothesis re-resolved BY NAME in
    /// the current goal before destructuring, avoiding the stale-FVar dangling
    /// reference that the term-elaboration path produced.
    RIntro { span: Span, patterns: Vec<String> },

    /// A named tactic not in the hardcoded enum — dispatched via TacticRegistry.
    /// Captures the tactic name and its raw arguments as surface expressions.
    Named {
        span: Span,
        name: String,
        args: Vec<SurfaceExpr>,
    },

    /// An expression used as a tactic (term-mode proof)
    /// This handles `exact`-like usage without the keyword
    Term(Span, Box<SurfaceExpr>),
}

impl SurfaceTactic {
    /// Get the source span of this tactic.
    /// All variants store a Span as the first field (or `span:` for struct variants).
    #[must_use]
    #[rustfmt::skip]
    pub fn span(&self) -> Span {
        match self {
            SurfaceTactic::Cases(s, _, _)
            | SurfaceTactic::Rw(s, _, _)
            | SurfaceTactic::Induction { span: s, .. }
            | SurfaceTactic::Simp { span: s, .. }
            | SurfaceTactic::Have(s, _, _, _) | SurfaceTactic::Let(s, _, _, _)
            | SurfaceTactic::Suffices(s, _, _, _)
            | SurfaceTactic::Case(s, _, _, _) | SurfaceTactic::AllGoals(s, _)
            | SurfaceTactic::AnyGoals(s, _) | SurfaceTactic::Try(s, _)
            | SurfaceTactic::First(s, _) | SurfaceTactic::Repeat(s, _)
            | SurfaceTactic::SeqFocus(s, _, _) | SurfaceTactic::Paren(s, _)
            | SurfaceTactic::FocusBlock(s, _) | SurfaceTactic::Focus(s, _)
            | SurfaceTactic::Conv(s, _, _) | SurfaceTactic::ConvArg(s, _)
            | SurfaceTactic::ConvEnter(s, _)
            | SurfaceTactic::SimpRw(s, _, _) | SurfaceTactic::Calc(s, _)
            | SurfaceTactic::Match(s, _, _)
            | SurfaceTactic::Simpa { span: s, .. }
            | SurfaceTactic::Obtain { span: s, .. }
            | SurfaceTactic::RCases { span: s, .. }
            | SurfaceTactic::RIntro { span: s, .. }
            | SurfaceTactic::Named { span: s, .. }
            | SurfaceTactic::Term(s, _) => *s,
        }
    }
}
