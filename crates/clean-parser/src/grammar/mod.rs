// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursive descent parser for Lean 4 syntax
//!
//! Parses tokens into a surface syntax AST.

use crate::lexer::{Lexer, Token, TokenKind};
use crate::surface::{DocComment, Span, SurfaceDecl, SurfaceExpr};
use crate::tactic_patterns::{TacticArgPattern, TacticPatterns};
use crate::{LocatedParseError, ParseError, ParseReport, ParserRecoveryDiagnostic};

#[derive(Debug, Clone)]
pub(super) struct IndentContext {
    pub(super) construct: String,
    pub(super) line: usize,
    pub(super) column: u32,
    pub(super) byte: usize,
}

#[derive(Debug, Clone)]
pub(super) struct PendingRecoveryDiagnostic {
    pub(super) code: String,
    pub(super) construct: String,
    pub(super) block_start: Option<crate::ParseSourceLocation>,
    pub(super) recovery_start: crate::ParseSourceLocation,
    pub(super) expected_indent: Option<u32>,
    pub(super) actual_indent: Option<u32>,
    pub(super) message: String,
    /// Tactic token whose grammar failed (T0 measurement integrity); see
    /// [`crate::ParserRecoveryDiagnostic::tactic`].
    pub(super) tactic: Option<String>,
}

/// Display symbol for a binary operator token that has NO rule in the
/// hand-written precedence chain and would therefore silently truncate an
/// expression if left unconsumed at the top level. Returns `None` for every
/// other token (separators, delimiters, atoms) so the base parser stays lenient
/// about ordinary trailing input. See [`Parser::reject_truncating_operator`].
fn unhandled_binary_operator_symbol(kind: &TokenKind) -> Option<&'static str> {
    match kind {
        // `>>` — HAndThen.hAndThen (`seq_expr` handles it; this is a defensive
        // fallback for a `>>` left stranded by an associativity conflict).
        TokenKind::Seq => Some(">>"),
        // `$` — low-precedence application. `seq_expr`/`pipe_expr` consume the
        // real operator; a stranded `$` (e.g. the no-whitespace `f $x`
        // pseudo-antiquotation in plain term position) is rejected here.
        TokenKind::Dollar => Some("$"),
        // `$>` / `<$` — Functor.mapConst siblings of the handled `<$>`.
        TokenKind::DollarArrow => Some("$>"),
        TokenKind::LeftDollar => Some("<$"),
        // `×'` (anonymous PSigma) only exists with a typed binder-group left
        // (`(x : T) ×' b`, handled in `prod_expr`); anywhere else it is a gap.
        TokenKind::TimesPrime => Some("×'"),
        // `<;>` is a TACTIC sequencing combinator, not a term operator; Lean
        // rejects it in term position. Without this, `parse_expr` would return
        // just the left tactic-name expression and silently drop the rest.
        TokenKind::SeqFocusOp => Some("<;>"),
        _ => None,
    }
}

// Types used only in tests (imported via super::*)
#[cfg(test)]
use crate::surface::{
    ConvEnterArg, DoElem, DoLetExprKind, NotationKind, Projection, QAntiquotContent,
    QQuotationKind, SurfaceBinderInfo, SurfaceCalcJustification, SurfaceLit, SurfacePattern,
    SurfaceTactic, SurfaceTacticLocation, TerminationKind, UniverseExpr,
};

/// Parser state
///
/// Recursive descent parser for Lean 4 syntax. The parser consumes tokens
/// produced by the lexer and builds a surface syntax AST.
pub struct Parser {
    /// Optional syntactic observations. Ordinary parser entry points leave
    /// this absent; an observation error never becomes a parse error.
    origins: Option<crate::origins::OriginBuilder>,
    tokens: Vec<Token>,
    pos: usize,
    /// Declaration visibility inherited from a module header or section.
    default_visibility: crate::Visibility,
    default_exposure: Option<bool>,
    /// Lean declaration doc comments (`/-- ... -/`) captured by the lexer while
    /// skipping trivia, in source order. The token stream is unchanged; these
    /// are associated with the declarations that follow them by
    /// [`Parser::parse_file_with_docs`]. Empty for inputs without doc comments.
    doc_comments: Vec<DocComment>,
    /// Module docs (`/-! ... -/`) the lexer skipped, in source order: the file
    /// header ends at one (`decl::header`).
    module_docs: Vec<Span>,
    stop_app_at_newline_lparen: bool,
    stop_app_at_newline_outer_indent: bool,
    /// When true, `atom_expr` treats `do` as an identifier instead of a keyword.
    /// Used by `parse_do_for` to prevent the collection expression from consuming
    /// the `do` keyword that delimits the loop body.
    forbid_do: bool,
    /// When true, `catch` and `finally` identifiers are not considered atom starts.
    /// Used by `parse_do_try` to prevent the try body expression parser from
    /// consuming `catch`/`finally` as function application arguments on single-line
    /// `do try expr catch e => expr` forms. See #2969.
    stop_at_catch_finally: bool,
    /// Column of the command keyword whose binder list is being parsed, when
    /// that list may NOT run past the start of the next source line.
    ///
    /// LANE FAILOPEN (2026-08-25). `variable`'s binder list accepts a run of
    /// bare names (`variable α β`), and that run has no line discipline, so a
    /// following COMMAND line the parser does not recognise was silently
    /// absorbed as more binders. In Mathlib `Logic/Function/Basic.lean`:
    ///
    /// ```text
    /// variable {α : Sort u} {f : α → α} (h : Involutive f)
    ///
    /// include h
    /// ```
    ///
    /// parsed as FOUR section variables — `f`, `h`, and then untyped `include`
    /// and `h`. The second, untyped `h` SHADOWED the real `(h : Involutive f)`,
    /// so every declaration in `namespace Involutive` elaborated against a
    /// meta FVar and died. Measured: `omit h` and even `frobnicate h` behaved
    /// identically, so this was never about `include` — any unrecognised
    /// `<ident> <ident>` line minted untyped section variables.
    ///
    /// Lean 4's own `variable` takes `many1 bracketedBinder` and rejects bare
    /// names outright, so refusing to START a bare-name run on a new line at or
    /// left of the keyword's own column is strictly MORE permissive than Lean:
    /// it can only accept inputs Lean accepts, never reject one.
    ///
    /// Consumed by [`Parser::binders`] with `take()`, so it applies to exactly
    /// one binder list and never leaks into a nested binder parse (a binder
    /// TYPE containing `∀ a b, …` must stay unaffected).
    binder_run_line_barrier: Option<u32>,
    /// When true, identifiers followed by `:=` (or binders then `:=`) are not
    /// considered atom starts. Used by `parse_where_local_defs` to prevent the
    /// expression parser for one where-clause body from consuming the next
    /// where-clause definition's name as a function argument.
    in_where_block: bool,
    /// When true, a `by` tactic block is not consumed as an application
    /// argument. Used by `show_body` so that `show t by tac` parses the type
    /// `t` and leaves `by` for the `show` parser to dispatch into a tactic
    /// block, matching Lean 4's `Term.show` precedence (the `by` term has lower
    /// precedence than an application argument). Without this, `show True by
    /// trivial` would parse the type as the application `True (by trivial)`.
    stop_app_at_by: bool,
    /// When true, `Type` does NOT consume a following token as its universe
    /// level — it parses as the bare sort.
    ///
    /// Lean parses an application ARGUMENT at max precedence, where `Type` is
    /// atomic: `@Eq.rec Type Y motive rfl Z h` passes `Type` and `Y` as two
    /// separate arguments, and `Type u` in argument position must be written
    /// `(Type u)`. Without this, `Type` greedily swallowed the NEXT ARGUMENT as
    /// a universe level, so that call parsed as `@Eq.rec (Type Y) motive rfl Z h`
    /// — one argument short, with the term variable `Y` reinterpreted as a
    /// universe parameter. The measured symptom was `Sort(Succ(Param(Y)))`
    /// appearing in the expected type, then `CannotInfer` (and 17 cascading
    /// failures in `data/graduation/clean-mtype/proof/MType.lean`).
    ///
    /// Cleared on entry to `atom_expr`, so it applies only to the immediate
    /// argument atom and never leaks into a nested parse: `f (Type u) x` still
    /// reads the level inside the parentheses.
    type_atomic_in_arg: bool,
    /// When true, the `generalizing` and `using` identifiers are not consumed as
    /// application arguments. Used by `parse_tactic_cases_induction` so the
    /// major premise `e` in `induction e using r generalizing x with …` stops at
    /// the `using` / `generalizing` clause keywords instead of greedily parsing
    /// `e using r generalizing x` as a function application. Both are ordinary
    /// identifier tokens to the lexer, so without this the target parse absorbs
    /// them (and `r`/`x`) as arguments, yielding `TacticFailed(UnknownIdent)`.
    stop_app_at_generalizing_using: bool,
    /// When true, identifiers immediately followed by `:=` are not considered
    /// atom starts. Used by `struct_field_value_expr` so that full-expression
    /// parsing of a struct-literal field value stops at the next field's name
    /// rather than consuming it as an application argument. Without this, the
    /// comma-less Lean 4 style `{ x := 1 y := 2 }` would parse the value of `x`
    /// as `1 y` (application) and then fail to find `}`. See #3517.
    in_struct_field: bool,
    /// When true, an identifier immediately followed by `:=` is not a
    /// constructor-argument start in PATTERN position. Set by
    /// [`Parser::struct_instance_pattern`] while it parses a field's value, so
    /// the comma-less Lean 4 layout `{ a := x` / newline / `b := y }` stops the
    /// value of `a` at `x` instead of reading `x b` as a constructor
    /// application. The pattern twin of `in_struct_field`; real Mathlib writes
    /// exactly that layout (`Mathlib/Order/Basic.lean:455-459`).
    in_struct_pattern_field: bool,
    /// When true, identifiers immediately followed by `:=` are not considered
    /// atom starts. Used by `instance_field_value_expr` so that full-expression
    /// parsing of an instance `where`-field value stops at the next field's
    /// name rather than consuming it as an application argument. This matters
    /// when the value is a `fun .. => body` lambda: the lambda body is parsed
    /// via the general `expr` grammar (not the boundary-aware
    /// `instance_field_*_expr` helpers), so without this flag
    /// `render := fun _ => Nat.succ Nat.zero` followed by `tag := 3` parses the
    /// body as `fun _ => Nat.succ Nat.zero tag` and drops the `tag` field.
    /// Mirrors `in_struct_field` for `{ x := 1 y := 2 }`. See B53.
    in_instance_field: bool,
    /// When true, the application/operator spine of a structure or class field
    /// TYPE stops at the next field — a newline-leading identifier immediately
    /// followed by `:`. Set by `field_type_expr`, which parses field types with
    /// the full operator grammar (so dependent fields like `h : n = n` and
    /// `property : 0 < val` parse) rather than the old app+arrow-only
    /// sub-grammar. The newline requirement keeps a same-line `(f x : T)`
    /// ascription / `(x y : T)` binder group inside the type intact (those are
    /// never a field boundary), mirroring Lean's layout-sensitive
    /// `structExplicitBinder` grouping in `src/Lean/Elab/Structure.lean`. See
    /// brick B11.
    in_field_type: bool,
    /// Delimiter nesting inside the CURRENT field type. `> 0` while the parse
    /// is inside any `(…)`/`⟨…⟩`/`{…}`/`[…]` opened within a structure field's
    /// type. The same-line next-field boundary (see `expr_app.rs`) fires only
    /// at depth 0, so `x : Nat y : Nat` on one line splits into two fields
    /// while a parenthesized `(f x : T)` ascription inside a field type stays
    /// intact.
    field_delim_depth: u32,
    /// Stack of block-opening reference columns for indentation-sensitive parsing.
    /// Each entry is the column of the **first child element** in the block (not the keyword).
    /// Matches Lean 4's `withPosition` + `sepBy1Indent` pattern.
    indent_stack: Vec<u32>,
    /// Metadata parallel to `indent_stack`, used only for recovery diagnostics.
    indent_context_stack: Vec<IndentContext>,
    /// Lean's `withoutPosition`: `Some(depth)` while the parse is inside a
    /// bracketed term group (`(…)`, `⟨…⟩`, `{…}`, `[…]`, `#[…]`, `‹…›`) opened
    /// when `indent_stack` had `depth` frames, and no indentation frame has
    /// been pushed since. Lean clears the saved position inside every one of
    /// those groups (`Lean/Parser/Term.lean:183,187,201,210,345`,
    /// `Init/Data/Array/Basic.lean:29`), so neither `checkColGt` (application
    /// arguments) nor `checkColGe` (tactic sequences) can cut a bracketed term
    /// at an enclosing block's column. A block opened INSIDE the group (a
    /// `by`, a bullet) pushes a frame, which re-establishes a position — so
    /// the suppression is keyed on the frame count rather than being a plain
    /// flag. Read through [`Parser::position_suppressed`].
    position_suppressed_at: Option<usize>,
    /// The types written in the rcases pattern being parsed (`⟨f, rfl : r =
    /// _⟩`), in order; the pattern text refers to the `k`-th as `p : #k`.
    /// Taken by the `rcases`/`obtain`/`rintro` parsers into their tactic node.
    rcases_pattern_types: Vec<SurfaceExpr>,
    /// Parser recovery diagnostics accumulated by non-breaking report APIs.
    recovery_diagnostics: Vec<ParserRecoveryDiagnostic>,
    /// Indentation diagnostics waiting for the skip/resume location.
    pending_recovery_diagnostics: Vec<PendingRecoveryDiagnostic>,
    /// Outer-to-inner chain of tactic tokens whose parse is still in progress.
    ///
    /// Measurement integrity (T0, `docs/plans/TACTICS_TO_100_2026-07-29.md`
    /// §RC-Q): when a tactic's argument grammar fails, `by_body` recovers the
    /// whole block to a `SyntheticSorry` and the *only* thing the user ever saw
    /// was `declaration uses synthetic sorry` — with nothing naming the tactic
    /// that failed to parse. `Parser::tactic` pushes on entry and pops on
    /// success, so on failure this holds the full nesting chain, outermost
    /// first. Purely diagnostic: it never changes what parses.
    tactic_chain: Vec<String>,
    /// Whole source text, kept so a diagnostic can quote a token's exact
    /// spelling (`module`, `:=`, `·`) instead of a `TokenKind` debug name.
    /// Diagnostics only.
    source: String,
    /// Tactic argument patterns for registry-known tactics.
    /// When present, `parse_ident_tactic`'s `Named` fallback uses these patterns
    /// for argument-aware parsing instead of generic expression-list parsing.
    tactic_patterns: Option<TacticPatterns>,
    /// Current expression nesting depth. Incremented on each `expr()` call,
    /// decremented on return. Prevents stack overflow on deeply nested input
    /// like `[[[[...` or `((((...)`. See #2556.
    expr_depth: u32,
    /// User-declared fixed-arity operators (`infixl`/`infixr`/`prefix`/`postfix`)
    /// registered while parsing a file, so later expressions can use them.
    /// Empty for single-shot `parse_expr`/`parse_decl` and whenever a file
    /// declares no operators — in which case `custom_op_expr` is a transparent
    /// pass-through to `app_expr`.
    custom_operators: Vec<custom_notation::CustomOperator>,
    /// User-declared CLOSED multi-hole `notation` patterns (leading + trailing
    /// literal, e.g. `notation:max "⟪" a ", " b "⟫" => …`). Registered and
    /// consumed alongside `custom_operators`; see `custom_notation.rs`.
    custom_mixfixes: Vec<custom_notation::CustomMixfix>,
    /// The Lean precedence of the operand slot currently being parsed — the
    /// context a user-declared operator must bind at least as tightly as to be
    /// consumed. Set by every builtin right-operand parse in the operator
    /// chain (`with_custom_min_prec`), reset to `CUSTOM_PREC_FLOOR` at each
    /// full-expression entry (`expr()`), and only read when the file declared
    /// custom notation. See `custom_notation.rs` (B100).
    custom_min_prec: u32,
    /// Which Lean precedence level the current full-expression slot opens.
    ///
    /// `↔` is `infix:20` — LOOSER than `→` (`infixr:25`) — so a `↔` met inside
    /// an arrow CODOMAIN belongs to an enclosing `↔`, not to the codomain:
    /// `a → b ↔ c` is `(a → b) ↔ c`. The hand-written precedence chain reaches
    /// `arrow_expr` BELOW `iff_expr`, so without this marker the codomain's
    /// full-precedence re-entry swallows that `↔`. Set to
    /// `ArrowCodomain` only by [`Parser::arrow_codomain_expr`] and reset to
    /// `Term` by every other full-expression entry ([`Parser::expr`]) — so a
    /// parenthesized, quantifier-body or lambda-body codomain
    /// (`a → (b ↔ c)`, `a → ∀ x, p x ↔ q x`) still consumes its own `↔`.
    expr_slot: expr_operators::ExprSlot,
    /// Guards harvested from PARENTHESIZED bounded quantifier binders
    /// (`∀ (x ∈ s), p`, `∃ (n > 0), p`) while `explicit_binders` parses them.
    /// Lean desugars `∀ (x ∈ s), p` to `∀ x, x ∈ s → p` (and `∃ (x ∈ s), p`
    /// to `∃ x, x ∈ s ∧ p`) — the guard must survive the binder parse so the
    /// enclosing quantifier can wrap the body. Previously the guard was parsed
    /// and DISCARDED, silently dropping the hypothesis. Each entry is the
    /// desugared guard proposition (`Membership.mem s x`, `GT.gt n 0`, …),
    /// already referencing the bound name; the enclosing quantifier drains
    /// this via [`Parser::quant_binders`]. Non-quantifier callers of
    /// `binders()` clear it, so a stale guard can never leak between binders.
    pending_binder_guards: Vec<SurfaceExpr>,
    /// Namespace-path stack for scoped custom notation: each entry is the
    /// FULL dotted path at that nesting depth (`namespace A.B` inside
    /// `namespace X` pushes `"X.A.B"`). A `scoped infixl` is tagged with the
    /// top of this stack and consulted only while its namespace is active
    /// (current, an ancestor of the current path, or opened). See
    /// `custom_notation.rs`.
    notation_ns_stack: Vec<crate::SurfaceName>,
    /// Scoped-notation namespaces activated at parse time by simple `open X`
    /// / `open scoped X` commands. Bounded by the enclosing namespace /
    /// section block (saved and truncated by the block parsers) and by an
    /// `open … in`'s body.
    open_scoped_notation_ns: Vec<crate::SurfaceName>,
    /// Names of the section `variable`s in scope (bounded by the enclosing
    /// namespace / section block, like [`Self::notation_ns_stack`]). A
    /// notation or macro template records which of its free references name
    /// one (`surface::template_hygiene`).
    section_variable_names: Vec<crate::SurfaceName>,
    /// `set_option hygiene false` is in force: a `notation` declared now is
    /// expanded without macro scopes (`crate::instantiate_unhygienic_notation_template`).
    /// Scoped like Lean's options: `… in` for one command, otherwise to the
    /// end of the enclosing section or namespace.
    hygiene_off: bool,
    /// The source positions of the `·` operands of notation templates hoisted
    /// to placeholders (`expr_app::cdot::hoist_operand`) that no parentheses
    /// have bound yet: the parentheses around each bind it
    /// (`expr_app::cdot::desugar`), wherever the template put it — or nowhere.
    hoisted_operand_cdots: Vec<usize>,
    /// Token index where the command being parsed began: the first token
    /// `decl()` saw, before any attribute or modifier. The module-system
    /// refusals read the modifier prefix between it and the command keyword
    /// (`decl::module_spelling`).
    command_start: usize,
    /// The explicit shared source-world decision; Oracle by default.
    lean_world: clean_kernel::LeanWorld,
    // Synthetic future tags exist only in the legacy grammar-model tests.
    // Production always reads the known world's explicit feature decision.
    #[cfg(test)]
    variable_visibility_override: Option<bool>,
    /// The header `file()` read (plan item `formats-module-spelling-refusals`).
    file_header: crate::FileHeader,
    /// A whole-file refusal raised inside a `namespace`/`section` body, whose
    /// block parser recovers from every other error: the blocks stop, and
    /// `file()` or the `parse_decl` entry points (`with_latched_refusal`)
    /// return it.
    file_refusal: Option<ParseError>,
    /// Whether the file header recovered an import whose module name does not
    /// parse (`decl::header`). Lean's header parser stops at its first error
    /// and pinned Lean reads no command after it, so that error is the file's
    /// first: from there no later error refuses the whole file, and each is
    /// recovered like any other.
    header_recovered: bool,
}

impl Parser {
    /// Create a new parser for the given input string.
    ///
    /// # ENSURES
    /// - `pos == 0` (parser starts at beginning)
    /// - `tokens` contains at least one token (EOF if input is empty)
    #[must_use]
    pub fn new(input: &str) -> Self {
        Self::build(input, None)
    }

    /// Create a parser with tactic argument patterns for pattern-aware parsing.
    ///
    /// When patterns are provided, the `Named` tactic fallback uses them to
    /// choose the correct argument parser (nullary, term, ident list, etc.)
    /// instead of the generic comma-separated expression list.
    #[must_use]
    pub(crate) fn new_with_tactics(input: &str, patterns: &TacticPatterns) -> Self {
        Self::build(input, Some(patterns.clone()))
    }

    /// Register every notation of `seed` before any of `self`'s input is
    /// parsed, so a file may use notation its imports declare.
    ///
    /// Each entry goes through the same registration path a file-local
    /// `notation` command takes, carrying its own declaring namespace (see
    /// [`crate::notation_seed`]). Seeding an empty seed is a no-op and leaves
    /// the custom-notation layers as transparent pass-throughs.
    pub(crate) fn seed_notation(&mut self, seed: &crate::notation_seed::NotationSeed) {
        for entry in seed.entries() {
            self.register_custom_operator_ns(
                entry.kind,
                entry.precedence,
                &entry.pattern,
                entry.expansion.clone(),
                entry.scope_ns.clone(),
                // The harvester reads no `set_option hygiene false`: an
                // imported template it records is hygienic.
                true,
            );
        }
    }

    /// Shared constructor backing [`Parser::new`] and [`Parser::new_with_tactics`];
    /// holds the single canonical field initializer so the two entry points
    /// cannot drift.
    fn build(input: &str, tactic_patterns: Option<TacticPatterns>) -> Self {
        let (tokens, doc_comments, module_docs) = Lexer::tokenize_with_all_docs(input);
        Self {
            origins: None,
            tokens,
            doc_comments,
            module_docs,
            pos: 0,
            default_visibility: crate::Visibility::Public,
            default_exposure: None,
            stop_app_at_newline_lparen: false,
            stop_app_at_newline_outer_indent: false,
            forbid_do: false,
            stop_at_catch_finally: false,
            binder_run_line_barrier: None,
            stop_app_at_by: false,
            type_atomic_in_arg: false,
            stop_app_at_generalizing_using: false,
            in_where_block: false,
            in_struct_field: false,
            in_struct_pattern_field: false,
            in_instance_field: false,
            in_field_type: false,
            field_delim_depth: 0,
            indent_stack: Vec::new(),
            indent_context_stack: Vec::new(),
            position_suppressed_at: None,
            rcases_pattern_types: Vec::new(),
            recovery_diagnostics: Vec::new(),
            pending_recovery_diagnostics: Vec::new(),
            tactic_chain: Vec::new(),
            source: input.to_owned(),
            tactic_patterns,
            expr_depth: 0,
            custom_operators: Vec::new(),
            custom_mixfixes: Vec::new(),
            custom_min_prec: custom_notation::CUSTOM_PREC_FLOOR,
            expr_slot: expr_operators::ExprSlot::Term,
            pending_binder_guards: Vec::new(),
            notation_ns_stack: Vec::new(),
            open_scoped_notation_ns: Vec::new(),
            section_variable_names: Vec::new(),
            hygiene_off: false,
            hoisted_operand_cdots: Vec::new(),
            command_start: 0,
            lean_world: clean_kernel::LeanWorld::ORACLE,
            #[cfg(test)]
            variable_visibility_override: None,
            file_header: crate::FileHeader::default(),
            file_refusal: None,
            header_recovered: false,
        }
    }

    /// Simulate release-order grammar boundaries in the legacy model tests.
    /// Unregistered tags here are never production source-world decisions.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn at_lean_world(mut self, world: &'static str) -> Self {
        self.variable_visibility_override = Some(crate::parse_world::world_at_least(
            world,
            crate::parse_world::VARIABLE_VISIBILITY_SINCE,
        ));
        self
    }

    /// Select a known source world. The default constructor remains at the
    /// oracle; an unknown release cannot be represented by this API.
    #[must_use]
    pub fn with_lean_world(mut self, world: clean_kernel::lean_world::LeanWorld) -> Self {
        self.lean_world = world;
        #[cfg(test)]
        {
            self.variable_visibility_override = None;
        }
        self
    }

    fn variable_visibility(&self) -> bool {
        #[cfg(test)]
        if let Some(visible) = self.variable_visibility_override {
            return visible;
        }
        self.lean_world.variable_visibility()
    }

    pub(crate) fn parse_file_in_world(
        input: &str,
        world: clean_kernel::lean_world::LeanWorld,
    ) -> Result<Vec<SurfaceDecl>, ParseError> {
        Self::new(input).with_lean_world(world).file()
    }

    /// Look up a tactic argument pattern by name.
    pub(crate) fn tactic_pattern(&self, name: &str) -> Option<&TacticArgPattern> {
        self.tactic_patterns.as_ref().and_then(|p| p.get(name))
    }
}

/// Associate captured doc comments with the declarations they precede.
///
/// A `/-- ... -/` doc comment attaches to the first declaration that begins at
/// or after the comment's end. The returned [`DocComment`]s carry the span of
/// the **declaration** they attach to (so callers can match on `decl.span()`),
/// and the original comment text. When several doc comments precede the same
/// declaration, the last one wins in this association helper. Raw comments with
/// no following declaration are dropped here; file parsing rejects an orphan
/// declaration doc comment before association.
///
/// Both inputs are in source order, so a single forward scan suffices.
fn associate_docs(decls: &[SurfaceDecl], raw_docs: Vec<DocComment>) -> Vec<DocComment> {
    let mut result = Vec::new();
    let mut decl_idx = 0usize;
    for doc in raw_docs {
        // Advance to the first declaration that begins at or after this doc's
        // end. Declarations before the doc cannot own it.
        while decl_idx < decls.len() && decls[decl_idx].span().start < doc.span.end {
            decl_idx += 1;
        }
        let Some(decl) = decls.get(decl_idx) else {
            // No following declaration: this doc is trailing; drop it.
            break;
        };
        let decl_span = decl.span();
        // A later doc preceding the same declaration overrides an earlier one.
        if let Some(last) = result.last_mut() {
            let last: &mut DocComment = last;
            if last.span == decl_span {
                last.text = doc.text;
                continue;
            }
        }
        result.push(DocComment::new(decl_span, doc.text));
    }
    result
}

mod custom_notation;
pub(crate) use custom_notation::hygienic_expansion;
mod decl;
mod entry_points;
mod expr;
mod expr_app;
mod expr_binders;
mod expr_do;
mod expr_do_compat;
mod expr_do_try;
mod expr_exists_kw;
mod expr_lambda_let;
mod expr_match;
mod expr_mul;
mod expr_operators;
mod helpers;
mod macros;
mod qq;
mod tactic;
mod tactic_extra;
mod tactic_have;
mod tactic_rcases;
mod tactic_sub;
mod tactic_sub_alternatives;
mod tactic_sub_rw_simp;
mod tokens;

#[cfg(test)]
mod class_attribute_scope_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_cmp_arrow;
#[cfg(test)]
mod tests_do;
#[cfg(test)]
mod tests_do_try;
#[cfg(test)]
mod tests_error_recovery;
#[cfg(test)]
mod tests_exact;
#[cfg(test)]
mod tests_interpolation;
#[cfg(test)]
mod tests_name_strategy;
#[cfg(test)]
mod tests_tactic;
#[cfg(test)]
mod tests_tactic_alt_syntax;
#[cfg(test)]
mod tests_tactic_calc_do;
#[cfg(test)]
mod tests_tactic_dispatch;
#[cfg(test)]
mod tests_tactic_generalize;
#[cfg(test)]
mod tests_tactic_rcases;
#[cfg(test)]
mod tests_tactic_seq_conv;
#[cfg(test)]
mod tests_tactic_silence;
#[cfg(test)]
mod tests_tactic_targets;
#[cfg(test)]
mod tests_term_alt_syntax;
#[cfg(test)]
mod tests_termination;
#[cfg(test)]
mod tests_variable_in;
#[cfg(test)]
mod tests_where;
