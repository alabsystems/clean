// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic-failure **attribution**: which tactic raised the diagnostic.
//!
//! ## The defect class this closes
//!
//! Brick T0 of `docs/plans/TACTICS_TO_100_2026-07-29.md` closed the *silent*
//! class — a construct that dispatched nothing and produced no diagnostic at
//! all. What survived is narrower: a tactic fails **loudly** but the message
//! does not say **which tactic** failed.
//!
//! `unsolved goals: tactic block has 1 unsolved goal(s) …` is the canonical
//! case. It is emitted once, at the end of the whole `by` block, and names no
//! tactic — so a reader cannot tell whether `omega` ran and gave up or was
//! never reached. `TypeMismatch`, `UnknownIdentWithSuggestions`,
//! `TooManyArguments` and friends have the same shape: they are *term*-level
//! diagnostics that escape through a tactic's argument elaboration carrying no
//! tactic context. Measured on `origin/main` at 2026-08-09, **88 of 373**
//! census probes (`data/silent_tactic_census.json`) failed this way.
//!
//! ## What is recorded
//!
//! `ElabCtx::eval_tactic` maintains a stack of the tactics currently being
//! dispatched — outermost first — so a failure inside `conv => lhs` is
//! attributed to the chain `conv > lhs`, not just to `conv`. Every nested
//! dispatch (combinators, `conv` bodies, `cases` alternatives, a `by` block
//! inside a `have`) funnels through that one method, so the stack is complete
//! by construction.
//!
//! Two snapshots are kept:
//!
//! * `last_chain` — the deepest chain reached by the most recent dispatch.
//!   This is what attributes `UnsolvedGoals`, which is raised by the *block*
//!   after every tactic has already returned successfully.
//! * `failing_chain` — the chain in effect when the innermost failure was
//!   raised. Set on the first (deepest) unwind and cleared whenever a tactic
//!   subsequently succeeds, so a failure that `try`/`first` recovered from
//!   cannot be blamed for a later, unrelated diagnostic.
//!
//! ## What is deliberately NOT changed
//!
//! Attribution is added at the `by`-block boundary and **only when the
//! underlying diagnostic does not already name the dispatching tactic**
//! (`names_tactic`). Errors that already carry a `tactic:` field —
//! `NoProgress { tactic }`, `RewriteNoMatch { tactic }`,
//! `UnknownTactic(name)`, … — are returned byte-identical to before. No goal
//! closes that did not close before, and no goal fails that did not fail
//! before: this changes the *message*, never the verdict.

use clean_parser::{Span, SurfaceExpr, SurfaceTactic};

/// One frame of the tactic nesting chain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TacticFrame {
    /// The tactic's **source spelling** (`arg`, not the registry key
    /// `conv_arg`) — the token a reader sees in the file.
    pub(crate) name: String,
    /// Source byte range of the tactic.
    pub(crate) span: Span,
}

/// Per-`by`-block attribution state held by `ElabCtx`.
#[derive(Debug, Clone, Default)]
pub(crate) struct TacticTrace {
    /// Tactics currently being dispatched, outermost first.
    stack: Vec<TacticFrame>,
    /// Deepest chain reached by the most recent dispatch.
    last_chain: Vec<TacticFrame>,
    /// Chain in effect when the innermost failure was raised.
    failing_chain: Option<Vec<TacticFrame>>,
}

impl TacticTrace {
    /// Current nesting depth (used to restore the stack after a dispatch that
    /// returned early through `?`).
    pub(crate) fn depth(&self) -> usize {
        self.stack.len()
    }

    /// Enter `tac`, recording it as the most recent dispatch.
    ///
    /// Returns `false` for a tactic with no source spelling worth naming (a
    /// bare term in tactic position), in which case no frame was pushed.
    pub(crate) fn enter(&mut self, tac: &SurfaceTactic) -> bool {
        let Some(frame) = frame_of(tac) else {
            return false;
        };
        self.stack.push(frame);
        self.last_chain.clone_from(&self.stack);
        true
    }

    /// Record that `tac` ran without going through `enter`/`leave`.
    ///
    /// Used by the one dispatch site that handles a tactic itself instead of
    /// delegating to the evaluator: the conv body's `congr` interception
    /// (`tactic::builtins_phase3d_conv::run_conv_body`).
    pub(crate) fn note(&mut self, tac: &SurfaceTactic) {
        if let Some(frame) = frame_of(tac) {
            let mut chain = self.stack.clone();
            chain.push(frame);
            self.last_chain = chain;
        }
    }

    /// Leave a dispatch that started at `depth`, recording its outcome.
    pub(crate) fn leave(&mut self, depth: usize, failed: bool) {
        if failed {
            if self.failing_chain.is_none() {
                self.failing_chain = Some(self.stack.clone());
            }
        } else {
            // A tactic that SUCCEEDED clears any failure recovered beneath it
            // (`try rfl`, a losing `first` branch). Without this a later,
            // unrelated `unsolved goals` would be blamed on the recovered
            // branch.
            self.failing_chain = None;
        }
        self.stack.truncate(depth);
    }

    /// The chain to attribute a block-level failure to: the failing chain when
    /// a tactic raised, otherwise the last chain that ran (which is what
    /// `UnsolvedGoals` needs, since no tactic raised at all).
    pub(crate) fn attribution_chain(&self) -> &[TacticFrame] {
        match &self.failing_chain {
            Some(chain) if !chain.is_empty() => chain,
            _ => &self.last_chain,
        }
    }

    /// Take the state aside for a nested `by` block, leaving a fresh one.
    ///
    /// The dispatch *stack* is retained: a `by` block inside a `have` is still
    /// nested inside `have`, and its chain should say so.
    pub(crate) fn enter_block(&mut self) -> (Vec<TacticFrame>, Option<Vec<TacticFrame>>) {
        let last = std::mem::take(&mut self.last_chain);
        let failing = self.failing_chain.take();
        self.last_chain.clone_from(&self.stack);
        (last, failing)
    }

    /// Restore the state saved by [`Self::enter_block`].
    pub(crate) fn leave_block(&mut self, saved: (Vec<TacticFrame>, Option<Vec<TacticFrame>>)) {
        self.last_chain = saved.0;
        self.failing_chain = saved.1;
    }
}

/// The tactic's source spelling and span, or `None` for a bare term.
fn frame_of(tac: &SurfaceTactic) -> Option<TacticFrame> {
    Some(TacticFrame {
        name: source_name(tac)?.to_owned(),
        span: tac.span(),
    })
}

/// A tactic's **source spelling**.
///
/// Deliberately not `compound_tactic_name`, which returns the *registry* key:
/// `arg 1` and `enter [1]` register as `conv_arg`/`conv_enter` but a reader
/// only ever sees `arg` and `enter`, and the census denominator is keyed on
/// the token as written.
fn source_name(tac: &SurfaceTactic) -> Option<&str> {
    Some(match tac {
        SurfaceTactic::Named { name, .. } => name.as_str(),
        SurfaceTactic::Cases(..) => "cases",
        SurfaceTactic::Induction { .. } => "induction",
        SurfaceTactic::Rw(..) => "rw",
        SurfaceTactic::Rewrite(..) => "rewrite",
        SurfaceTactic::Rwa(..) => "rwa",
        SurfaceTactic::Simp { all: true, .. } => "simp_all",
        SurfaceTactic::Simp { all: false, .. } => "simp",
        SurfaceTactic::SimpRw(..) => "simp_rw",
        SurfaceTactic::Simpa { .. } => "simpa",
        SurfaceTactic::Have(..) => "have",
        SurfaceTactic::Let(..) => "let",
        SurfaceTactic::Suffices(..) => "suffices",
        SurfaceTactic::Replace(..) => "replace",
        SurfaceTactic::Obtain { .. } => "obtain",
        SurfaceTactic::RCases { .. } => "rcases",
        SurfaceTactic::RIntro { .. } => "rintro",
        SurfaceTactic::Case(..) => "case",
        SurfaceTactic::Match(..) => "match",
        SurfaceTactic::Calc(..) => "calc",
        SurfaceTactic::AllGoals(..) => "all_goals",
        SurfaceTactic::AnyGoals(..) => "any_goals",
        SurfaceTactic::Try(..) => "try",
        SurfaceTactic::First(..) => "first",
        SurfaceTactic::Repeat(..) => "repeat",
        SurfaceTactic::SeqFocus(..) => "<;>",
        SurfaceTactic::Paren(..) => "(...)",
        SurfaceTactic::FocusBlock(..) => "·",
        SurfaceTactic::Focus(..) => "focus",
        SurfaceTactic::Conv(..) => "conv",
        SurfaceTactic::ConvArg(..) => "arg",
        SurfaceTactic::ConvEnter(..) => "enter",
        // A term in tactic position: Lean's tactic-mode `if`/`match`/`do` all
        // parse into this variant, and the leading keyword IS the construct the
        // user wrote, so it is honest to name it. A *bare* proof term names no
        // tactic — calling it `exact` would be a fiction, since the user did
        // not write `exact`.
        SurfaceTactic::Term(_, expr) => match expr.as_ref() {
            SurfaceExpr::If(..) | SurfaceExpr::IfLet(..) | SurfaceExpr::IfDecidable(..) => "if",
            SurfaceExpr::Match(..) => "match",
            SurfaceExpr::Do(..) => "do",
            _ => return None,
        },
    })
}

/// Render a chain outermost → innermost, e.g. ``` `conv` > `lhs` ```.
pub(crate) fn render_chain(chain: &[TacticFrame]) -> String {
    chain
        .iter()
        .map(|frame| format!("`{}`", frame.name))
        .collect::<Vec<_>>()
        .join(" > ")
}

/// Does `haystack` already name `token` as a standalone word?
///
/// The word-boundary test is load-bearing in both directions: `simp` must not
/// be credited by a message that only contains `simp_all`, and `rw` must not
/// be credited by `rewrite`. Tactic spellings carry `?`, `!` and `'`, so those
/// count as part of the word. Mirrors the census grader in
/// `crates/clean-elab/tests/silent_tactic_census.rs` so the gate and the
/// production predicate cannot drift apart.
pub(crate) fn names_tactic(haystack: &str, token: &str) -> bool {
    /// Characters that always continue an identifier.
    fn ident_char(c: char) -> bool {
        c.is_alphanumeric() || c == '_'
    }
    /// Characters a tactic spelling may END with (`rw?`, `simp!`, `let'`).
    fn suffix_char(c: char) -> bool {
        matches!(c, '?' | '!' | '\'')
    }
    if token.is_empty() {
        return false;
    }
    // A trailing suffix character continues the word only when the token does
    // NOT already carry one: `simp` must not be credited by `simp?`, but `rw?`
    // *must* be credited by `unknown tactic 'rw?'`, where the next character is
    // the closing quote. Treating `'` as a word character in both roles made
    // that second case false — caught by this module's own boundary test.
    let token_has_suffix = token.chars().next_back().is_some_and(suffix_char);
    let mut from = 0usize;
    while let Some(rel) = haystack[from..].find(token) {
        let start = from + rel;
        let end = start + token.len();
        let before_ok = haystack[..start]
            .chars()
            .next_back()
            .is_none_or(|c| !ident_char(c));
        let after_ok = haystack[end..]
            .chars()
            .next()
            .is_none_or(|c| !ident_char(c) && (token_has_suffix || !suffix_char(c)));
        if before_ok && after_ok {
            return true;
        }
        from = end.max(start + 1);
        if from >= haystack.len() {
            break;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    fn named(name: &str) -> SurfaceTactic {
        SurfaceTactic::Named {
            span: Span::new(3, 3 + name.len()),
            name: name.to_owned(),
            args: Vec::new(),
        }
    }

    #[test]
    fn test_names_tactic_requires_word_boundaries() {
        assert!(names_tactic("NoProgress { tactic: \"simp\" }", "simp"));
        assert!(
            !names_tactic("NoProgress { tactic: \"simp_all\" }", "simp"),
            "`simp_all` must not be credited as naming `simp`"
        );
        assert!(
            !names_tactic("RewriteNoMatch { tactic: \"rewrite\" }", "rw"),
            "`rewrite` must not be credited as naming `rw`"
        );
        assert!(
            !names_tactic("unknown tactic 'rw?'", "rw"),
            "`rw?` is a different tactic from `rw` and must not credit it"
        );
        // Both renderings of the same diagnostic: `{err:?}` (what the census
        // and the attribution predicate grade) quotes with `"`, `{err}` (what
        // `clean check` prints) with `'`. A token that ENDS in a suffix
        // character must be found in both.
        assert!(names_tactic("UnknownTactic(\"rw?\")", "rw?"));
        assert!(names_tactic("unknown tactic 'rw?'", "rw?"));
        assert!(names_tactic("unknown tactic 'let''", "let'"));
    }

    #[test]
    fn test_conv_navigation_uses_source_spelling_not_registry_key() {
        assert_eq!(
            source_name(&SurfaceTactic::ConvArg(Span::dummy(), 1)),
            Some("arg")
        );
        assert_eq!(
            source_name(&SurfaceTactic::ConvEnter(Span::dummy(), Vec::new())),
            Some("enter")
        );
    }

    #[test]
    fn test_trace_records_the_deepest_chain_that_ran() {
        let mut trace = TacticTrace::default();
        let conv = SurfaceTactic::Conv(
            Span::new(0, 4),
            clean_parser::SurfaceTacticLocation::Goal,
            Vec::new(),
        );
        let outer = trace.depth();
        assert!(trace.enter(&conv));
        let inner_depth = trace.depth();
        assert!(trace.enter(&named("lhs")));
        trace.leave(inner_depth, false);
        trace.leave(outer, false);
        assert_eq!(render_chain(trace.attribution_chain()), "`conv` > `lhs`");
    }

    #[test]
    fn test_a_recovered_failure_does_not_blame_a_later_diagnostic() {
        let mut trace = TacticTrace::default();
        // `rfl` fails …
        let d = trace.depth();
        assert!(trace.enter(&named("rfl")));
        trace.leave(d, true);
        assert_eq!(render_chain(trace.attribution_chain()), "`rfl`");
        // … and `try` swallows it, so the failure must stop being attributed.
        let d = trace.depth();
        assert!(trace.enter(&named("try")));
        trace.leave(d, false);
        assert_eq!(render_chain(trace.attribution_chain()), "`try`");
    }

    #[test]
    fn test_bare_term_pushes_no_frame() {
        let mut trace = TacticTrace::default();
        let term = SurfaceTactic::Term(
            Span::dummy(),
            Box::new(SurfaceExpr::Ident(
                Span::dummy(),
                clean_parser::SurfaceName::generated_path("h"),
            )),
        );
        assert!(!trace.enter(&term));
        assert_eq!(trace.depth(), 0);
    }
}
