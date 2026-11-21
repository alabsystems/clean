// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic surface syntax types
//!
//! AST types for tactics, calc blocks, and do-notation parsed from Lean 4 source.
//! These are used by [`SurfaceExpr::ByTactic`], [`SurfaceExpr::CalcBlock`],
//! and [`SurfaceExpr::Do`] variants in the surface syntax.

use crate::surface::{Span, SurfaceExpr, SurfaceName, SurfacePattern};
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

/// One element of a `simp`/`simp only`/`simpa` lemma list — Lean's `simpArg`.
///
/// Lean's grammar is `simpLemma := (simpPre <|> simpPost)? "← "? term` and
/// `simpErase := "-" ident` (`Lean/Elab/Tactic/Simp.lean`), so a list element
/// carries up to two modifiers besides its term (a phase and `←`, or `-`
/// alone). The direction and the erasure used to be eaten and thrown away by
/// `Parser::parse_simp_lemmas`, which made `simp [← h]` run `h` FORWARD and
/// `simp [-h]` *add* `h` where Lean removes it — a silent inversion of the
/// request, not merely a dropped feature.
#[derive(Debug, Clone)]
pub struct SurfaceSimpArg {
    pub span: Span,
    /// `↓ lemma` / `↑ lemma`: the traversal phase the rule is added to
    /// (Lean's `simpPre` / `simpPost`); `None` when the element has neither.
    pub phase: Option<SimpPhase>,
    /// `← lemma`: use the equation right-to-left (Lean's `inv`).
    pub reverse: bool,
    /// `- lemma`: REMOVE the lemma from the simp set (Lean's `simpErase`).
    pub erase: bool,
    /// The lemma term. Lean elaborates this as an arbitrary term when it does
    /// not resolve as an identifier, so it is a [`SurfaceExpr`], not a name.
    pub term: SurfaceExpr,
}

/// The traversal phase a simp-list element names: Lean's `simpPre` (`↓`, the
/// rule fires before simp visits the subterms) or `simpPost` (`↑`, after).
/// It says WHEN a rule fires, never which rule it is or its direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimpPhase {
    /// `↓` — Lean's `simpPre`.
    Pre,
    /// `↑` — Lean's `simpPost`.
    Post,
}

/// Location specifier for tactics like `simp at h` or `rw [...] at *`
#[derive(Debug, Clone)]
pub enum SurfaceTacticLocation {
    /// Apply at specific hypotheses: `at h1 h2`
    Hyps(Vec<SurfaceName>),
    /// Apply at specific hypotheses and the goal: `at h1 h2 ⊢` / `at h1 h2 |-`
    HypsAndGoal(Vec<SurfaceName>),
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
    Name(SurfaceName),
}

/// A single `case` arm in `cases`/`induction` with-blocks:
/// `| constructor_name args => tactic_seq`
#[derive(Debug, Clone)]
pub struct SurfaceInductionAlt {
    pub span: Span,
    /// Whether `@` requests names for implicit constructor fields too.
    pub explicit: bool,
    /// Constructor/case name
    pub name: SurfaceName,
    /// Bound variable names for this case
    pub args: Vec<SurfaceName>,
    /// Tactics for this case
    pub tactics: Vec<SurfaceTactic>,
}

/// One `casesTarget` of `rcases` (`Init/RCases.lean`): `e`, or `h : e`,
/// which generalizes `e` and records `h : e = <pattern instance>` in every
/// goal the pattern produces.
#[derive(Debug, Clone)]
pub struct SurfaceRCasesTarget {
    /// The `h` of `h : e`.
    pub eq_name: Option<SurfaceName>,
    /// The scrutinee `e`.
    pub term: SurfaceExpr,
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
    /// Introduce an argument using a constructor pattern whose locals scope over later tactics.
    IntroPattern(Span, SurfacePattern),

    /// `cases (h :)? e with | alt1 => ... | alt2 => ...`
    ///
    /// The second field is the optional `h :` of Lean's `casesTarget`
    /// (`atomic(ident " : ")? term`, `Init/Tactics.lean`): when present the
    /// target is generalized with the equation `h : e = cᵢ fields` recorded
    /// in every branch.
    Cases(
        Span,
        Option<SurfaceName>,
        Box<SurfaceExpr>,
        Vec<SurfaceInductionAlt>,
    ),

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
        generalizing: Vec<SurfaceName>,
        alts: Vec<SurfaceInductionAlt>,
    },

    /// `rw [rule1, ← rule2] (at loc)?` - rewrite with given rules, then
    /// Lean's `try (with_reducible rfl)` on the main goal (Lean's `rw` macro
    /// over `rewrite`, `Init/Tactics.lean`).
    Rw(Span, Vec<SurfaceRwRule>, SurfaceTacticLocation),

    /// `rewrite [rule1, ← rule2] (at loc)?` - the rewrite alone, with no
    /// closing `rfl` at any location (Lean's `rewriteSeq`).
    Rewrite(Span, Vec<SurfaceRwRule>, SurfaceTacticLocation),

    /// `rwa [rules] (at h)?` — focus the main goal, rewrite, and close it.
    Rwa(Span, Vec<SurfaceRwRule>, SurfaceTacticLocation),

    /// `simp` with optional location, or `simp_all`, with ordered arguments.
    Simp {
        span: Span,
        /// Simplify the whole context using cross-hypothesis rewriting.
        all: bool,
        only: bool,
        lemmas: Vec<SurfaceSimpArg>,
        location: SurfaceTacticLocation,
        /// The lemma list contained Lean's `*` element (`simp [*]`,
        /// `simp only [*]`, `simp [foo, *]`): every local hypothesis is also
        /// used as a rewrite rule. `*` is not a term, so it is carried here
        /// rather than in `lemmas`.
        use_hypotheses: bool,
    },

    /// `have h : T := proof`, `have : T := proof`, or `have h := proof`
    /// (tactic-mode have). The type annotation is `None` when omitted
    /// (`have h := term`), in which case the elaborator infers the hypothesis
    /// type from the elaborated proof term. The destructuring form
    /// (`have ⟨a, b⟩ := e`) is desugared to [`Self::Obtain`] at parse time, so
    /// it never reaches this variant.
    Have(
        Span,
        Option<SurfaceName>,
        Option<Box<SurfaceExpr>>,
        Box<SurfaceTactic>,
    ),

    /// `let h : T := val` (tactic-mode let)
    Let(
        Span,
        SurfaceName,
        Option<Box<SurfaceExpr>>,
        Box<SurfaceExpr>,
    ),

    /// `letI h : T := val` introduces a local whose value is inlined in the proof.
    LetI(
        Span,
        SurfaceName,
        Option<Box<SurfaceExpr>>,
        Box<SurfaceExpr>,
    ),

    /// `replace h : T := proof` (Lean's `replace letDecl`): the wrapped
    /// declaration (a [`Self::Have`]) runs, then the older hypothesis of the
    /// same name is cleared when nothing depends on it.
    Replace(Span, Box<SurfaceTactic>),

    /// `suffices h : T by tac_seq` or `suffices h : T from proof`
    Suffices(
        Span,
        Option<SurfaceName>,
        Box<SurfaceExpr>,
        Vec<SurfaceTactic>,
    ),

    /// `case name (binders)* => tacs` - focus on a named case.
    ///
    /// The second field is the case tag; the third is the optional list of
    /// `binderIdent`s that rename the case's most-recently-introduced
    /// inaccessible hypotheses (Lean: `case tag x₁ … xₙ => tac`). An empty
    /// binder list is the plain `case tag => tac` form.
    Case(Span, SurfaceName, Vec<SurfaceName>, Vec<SurfaceTactic>),

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

    /// `repeat' tacticSeq` - repeat independently on each goal and its children.
    RepeatAll(Span, Vec<SurfaceTactic>),

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

    /// `match (h :)? discrs with | pat => tac_seq | ...` in tactic mode
    ///
    /// Like expression-mode match, but arm bodies are tactic sequences.
    /// Reference: Lean 4 `Lean.Parser.Tactic.match` in Tactic.lean. The
    /// second field is the `h :` of an annotated single discriminant
    /// (`matchDiscr`), bound as `h : e = pat` in every arm exactly as the
    /// term-mode [`SurfaceExpr::Match`] binds it.
    Match(
        Span,
        Option<SurfaceName>,
        Vec<SurfaceExpr>,
        Vec<TacticMatchArm>,
    ),

    /// `simpa` or `simpa only [lemmas] using h` - simp then close with `h`
    /// (or `assumption` when no `using` term is given).
    Simpa {
        span: Span,
        only: bool,
        lemmas: Vec<SurfaceSimpArg>,
        /// The lemma list contained Lean's `*` element (`simpa [*] using h`).
        /// `simpa` shares `simp`'s `mkSimpContext`, so `[*]` means the same
        /// thing there; the parser used to bind this to `_use_hypotheses` and
        /// throw it away, which made `simpa [*]` a strictly weaker `simpa`.
        use_hypotheses: bool,
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
    /// `term` is `None` for `obtain pat : T` (no `:= e`), which leaves `⊢ T`
    /// as a new first goal and destructures the assumed `T` (Lean's
    /// `obtainNone`); the parser accepts that form only with a type.
    Obtain {
        span: Span,
        pattern: String,
        ty: Option<Box<SurfaceExpr>>,
        term: Option<Box<SurfaceExpr>>,
        /// The types of the typed sub-patterns (`⟨x, hx : p x⟩`), referred to
        /// in `pattern` as `hx : #k`.
        pattern_types: Vec<SurfaceExpr>,
        /// What each identifier of `pattern` binds, as written → as bound,
        /// when a notation or macro template's expansion renamed it apart
        /// (`crate::instantiate_notation_template`); empty otherwise, and
        /// every identifier binds itself.
        pattern_binders: Vec<(SurfaceName, SurfaceName)>,
    },

    /// `rcases h with ⟨hp, hq⟩` — destructure a hypothesis (or a term).
    ///
    /// Lean 4.8: `"rcases" casesTarget,* (" with " rcasesPatLo)?`
    /// (`Init/RCases.lean`). Each target is `e` or `h : e`
    /// ([`SurfaceRCasesTarget`]); with several targets the pattern's tuple
    /// components go to the targets in order. The `pattern` is the canonical
    /// pattern text (e.g. `⟨a, b⟩`, `⟨a, ⟨b, c⟩⟩`, or a single name) consumed by
    /// the same recursive-intro pattern engine that backs `obtain`. The `with`
    /// keyword separates the targets from the pattern.
    RCases {
        span: Span,
        /// At least one target, in source order.
        targets: Vec<SurfaceRCasesTarget>,
        pattern: String,
        /// The types of the typed sub-patterns, as for [`Self::Obtain`].
        pattern_types: Vec<SurfaceExpr>,
        /// As for [`Self::Obtain`].
        pattern_binders: Vec<(SurfaceName, SurfaceName)>,
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
    RIntro {
        span: Span,
        patterns: Vec<String>,
        /// The types of the typed sub-patterns, as for [`Self::Obtain`].
        pattern_types: Vec<SurfaceExpr>,
        /// As for [`Self::Obtain`].
        pattern_binders: Vec<(SurfaceName, SurfaceName)>,
    },

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
            SurfaceTactic::Cases(s, _, _, _)
            | SurfaceTactic::Rw(s, _, _) | SurfaceTactic::Rewrite(s, _, _)
            | SurfaceTactic::Rwa(s, _, _)
            | SurfaceTactic::Induction { span: s, .. }
            | SurfaceTactic::Simp { span: s, .. }
            | SurfaceTactic::Have(s, _, _, _) | SurfaceTactic::Let(s, _, _, _)
            | SurfaceTactic::LetI(s, _, _, _)
            | SurfaceTactic::Suffices(s, _, _, _) | SurfaceTactic::Replace(s, _)
            | SurfaceTactic::Case(s, _, _, _) | SurfaceTactic::AllGoals(s, _)
            | SurfaceTactic::AnyGoals(s, _) | SurfaceTactic::Try(s, _)
            | SurfaceTactic::First(s, _) | SurfaceTactic::Repeat(s, _) | SurfaceTactic::RepeatAll(s, _)
            | SurfaceTactic::SeqFocus(s, _, _) | SurfaceTactic::Paren(s, _)
            | SurfaceTactic::FocusBlock(s, _) | SurfaceTactic::Focus(s, _)
            | SurfaceTactic::Conv(s, _, _) | SurfaceTactic::ConvArg(s, _)
            | SurfaceTactic::ConvEnter(s, _)
            | SurfaceTactic::SimpRw(s, _, _) | SurfaceTactic::Calc(s, _)
            | SurfaceTactic::IntroPattern(s, _)
            | SurfaceTactic::Match(s, _, _, _)
            | SurfaceTactic::Simpa { span: s, .. }
            | SurfaceTactic::Obtain { span: s, .. }
            | SurfaceTactic::RCases { span: s, .. }
            | SurfaceTactic::RIntro { span: s, .. }
            | SurfaceTactic::Named { span: s, .. }
            | SurfaceTactic::Term(s, _) => *s,
        }
    }
}
