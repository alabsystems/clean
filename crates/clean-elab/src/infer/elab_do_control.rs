// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ControlInfo pre-pass for do-notation.
//!
//! Before elaboration, walks the do-block AST to determine which control
//! effects are present (break, continue, early return, mutable reassignment).
//! This information is used by Phase 4 (ControlStack) to wrap the base monad
//! in the appropriate transformer stack.
//!
//! This is a purely syntactic pass — no type information needed.
//!
//! Reference: ~/lean4-ref/src/Lean/Elab/Do/InferControlInfo.lean

use clean_parser::DoElem;
use std::collections::HashSet;

/// Control flow effects detected in a do-block before elaboration.
///
/// Mirrors Lean 4's `ControlInfo` (InferControlInfo.lean:20-34).
/// Computed by a pre-pass over the do-block AST before elaboration.
///
/// Combinators:
/// - `sequence(a, b)`: for `a; b` — if `a` has no exits, `b` is dead code
/// - `alternative(a, b)`: for `if .. then a else b` — both may be taken
pub(crate) struct ControlInfo {
    /// A `break` statement was found in the block.
    pub(crate) breaks: bool,
    /// A `continue` statement was found in the block.
    pub(crate) continues: bool,
    /// A `return` in non-terminal position was found.
    pub(crate) returns_early: bool,
    /// Number of paths that reach the end of the block normally (not via break/continue/return).
    /// 0 means all paths exit via control flow (dead code after this block).
    pub(crate) num_regular_exits: usize,
    /// Names of mutable variables that are reassigned in this block.
    pub(crate) reassigns: HashSet<String>,
}

impl ControlInfo {
    /// Default: no control flow effects, 1 regular exit.
    pub(crate) fn pure() -> Self {
        Self {
            breaks: false,
            continues: false,
            returns_early: false,
            num_regular_exits: 1,
            reassigns: HashSet::new(),
        }
    }

    /// No exits (dead code after break/continue/return).
    fn no_exit() -> Self {
        Self {
            breaks: false,
            continues: false,
            returns_early: false,
            num_regular_exits: 0,
            reassigns: HashSet::new(),
        }
    }

    /// Pure element that records a single mutable variable name.
    fn with_reassign(name: String) -> Self {
        let mut info = Self::pure();
        info.reassigns.insert(name);
        info
    }

    /// Combine two sequential elements: `a; b`.
    /// If `a` has no regular exits, `b` is dead code.
    pub(crate) fn sequence(a: Self, b: Self) -> Self {
        if a.num_regular_exits == 0 {
            return a;
        }
        Self {
            breaks: a.breaks || b.breaks,
            continues: a.continues || b.continues,
            returns_early: a.returns_early || b.returns_early,
            num_regular_exits: b.num_regular_exits,
            reassigns: a.reassigns.union(&b.reassigns).cloned().collect(),
        }
    }

    /// Combine two alternative branches: `if .. then a else b`.
    /// Both branches may be taken, so merge effects and add exit counts.
    pub(crate) fn alternative(a: Self, b: Self) -> Self {
        Self {
            breaks: a.breaks || b.breaks,
            continues: a.continues || b.continues,
            returns_early: a.returns_early || b.returns_early,
            num_regular_exits: a.num_regular_exits + b.num_regular_exits,
            reassigns: a.reassigns.union(&b.reassigns).cloned().collect(),
        }
    }

    /// Returns true if any control flow effects are present that require
    /// a transformer stack (break, continue, early return, or mutable reassignment).
    pub(crate) fn needs_control_stack(&self) -> bool {
        self.breaks || self.continues || self.returns_early || !self.reassigns.is_empty()
    }
}

/// Infer control info for a single DoElem.
/// This is a SYNTACTIC pass — no type information needed.
pub(crate) fn infer_control_info_elem(elem: &DoElem) -> ControlInfo {
    crate::stack_safe(|| match elem {
        DoElem::Break(_) => ControlInfo {
            breaks: true,
            num_regular_exits: 0,
            ..ControlInfo::pure()
        },
        DoElem::Continue(_) => ControlInfo {
            continues: true,
            num_regular_exits: 0,
            ..ControlInfo::pure()
        },
        DoElem::Return(_, _) => ControlInfo {
            returns_early: true,
            num_regular_exits: 0,
            ..ControlInfo::pure()
        },
        DoElem::Expr(_, _)
        | DoElem::Bind(_, _, _)
        | DoElem::Let(_, _, _)
        | DoElem::LetRec(_, _)
        | DoElem::DbgTrace(_, _) => ControlInfo::pure(),
        // LetMut is pure — only Reassign adds to reassigns (InferControlInfo.lean:97)
        DoElem::LetMut(_, _, _) => ControlInfo::pure(),
        DoElem::Reassign(_, name, _) => ControlInfo::with_reassign(name.clone()),
        DoElem::PatternReassign(_, pat, _) => {
            let mut names = Vec::new();
            pat.collect_var_names(&mut names);
            ControlInfo {
                reassigns: names.into_iter().collect(),
                ..ControlInfo::pure()
            }
        }
        DoElem::If(_, _, t, e)
        | DoElem::IfLet(_, _, _, t, e)
        | DoElem::IfDecidable(_, _, _, t, e) => infer_branch_info(t, e),
        DoElem::Match(_, _, arms) => arms
            .iter()
            .map(|arm| infer_control_info_seq(&arm.body))
            .reduce(ControlInfo::alternative)
            .unwrap_or_else(ControlInfo::pure),
        DoElem::For(_, _, _, body) | DoElem::Repeat(_, body) | DoElem::While(_, _, body) => {
            infer_loop_info(body)
        }
        DoElem::TryCatch(_, try_body, catches, finally_body) => {
            infer_try_catch_info(try_body, catches, finally_body)
        }
        DoElem::LetElse(_, _, _, fallback) => {
            let fallback_info = infer_control_info_seq(fallback);
            ControlInfo::alternative(ControlInfo::pure(), fallback_info)
        }
        DoElem::LetExpr(_, _, _, _, fallback) => {
            let fallback_info = infer_control_info_seq(fallback);
            ControlInfo::alternative(ControlInfo::pure(), fallback_info)
        }
    })
}

/// Infer control info for an if/if-let/if-decidable branch.
fn infer_branch_info(then_elems: &[DoElem], else_elems: &Option<Vec<DoElem>>) -> ControlInfo {
    let then_info = infer_control_info_seq(then_elems);
    let else_info = else_elems
        .as_ref()
        .map(|e| infer_control_info_seq(e))
        .unwrap_or_else(ControlInfo::pure);
    ControlInfo::alternative(then_info, else_info)
}

/// Infer control info for a loop body (for, repeat, while).
///
/// Per Lean 4 InferControlInfo.lean:131-137: for loop handler strips
/// breaks/continues (they are consumed by the loop), keeps reassigns+earlyReturn.
fn infer_loop_info(body: &[DoElem]) -> ControlInfo {
    let body_info = infer_control_info_seq(body);
    ControlInfo {
        breaks: false,
        continues: false,
        returns_early: body_info.returns_early,
        num_regular_exits: 1,
        reassigns: body_info.reassigns,
    }
}

/// Infer control info for try/catch/finally.
fn infer_try_catch_info(
    try_body: &[DoElem],
    catches: &[clean_parser::DoCatchClause],
    finally_body: &Option<Vec<DoElem>>,
) -> ControlInfo {
    let try_info = infer_control_info_seq(try_body);
    let catch_combined = catches
        .iter()
        .map(|c| infer_control_info_seq(&c.body))
        .fold(try_info, ControlInfo::alternative);
    match finally_body {
        Some(fin) => ControlInfo::sequence(catch_combined, infer_control_info_seq(fin)),
        None => catch_combined,
    }
}

/// Infer control info for a sequence of DoElems.
pub(crate) fn infer_control_info_seq(elems: &[DoElem]) -> ControlInfo {
    if elems.is_empty() {
        // Empty sequence: 1 regular exit, no effects
        let mut info = ControlInfo::no_exit();
        info.num_regular_exits = 1;
        return info;
    }
    let mut info = infer_control_info_elem(&elems[0]);
    for elem in &elems[1..] {
        if info.num_regular_exits == 0 {
            break; // dead code
        }
        info = ControlInfo::sequence(info, infer_control_info_elem(elem));
    }
    info
}

fn seq_contains_return_for_outer_continuation(elems: &[DoElem]) -> bool {
    elems
        .iter()
        .any(elem_contains_return_for_outer_continuation)
}

fn elem_contains_return_for_outer_continuation(elem: &DoElem) -> bool {
    crate::stack_safe(|| match elem {
        DoElem::Return(_, _) => true,
        DoElem::If(_, _, then_branch, else_branch)
        | DoElem::IfLet(_, _, _, then_branch, else_branch)
        | DoElem::IfDecidable(_, _, _, then_branch, else_branch) => {
            seq_contains_return_for_outer_continuation(then_branch)
                || else_branch
                    .as_ref()
                    .is_some_and(|branch| seq_contains_return_for_outer_continuation(branch))
        }
        DoElem::Match(_, _, arms) => arms
            .iter()
            .any(|arm| seq_contains_return_for_outer_continuation(&arm.body)),
        DoElem::TryCatch(_, try_body, catches, finally_body) => {
            seq_contains_return_for_outer_continuation(try_body)
                || catches
                    .iter()
                    .any(|catch| seq_contains_return_for_outer_continuation(&catch.body))
                || finally_body
                    .as_ref()
                    .is_some_and(|body| seq_contains_return_for_outer_continuation(body))
        }
        DoElem::LetElse(_, _, _, fallback) | DoElem::LetExpr(_, _, _, _, fallback) => {
            seq_contains_return_for_outer_continuation(fallback)
        }
        // Loop-local returns propagate through the loop accumulator instead of
        // the outer EarlyReturn control stack.
        DoElem::For(_, _, _, _) | DoElem::Repeat(_, _) | DoElem::While(_, _, _) => false,
        DoElem::Break(_)
        | DoElem::Continue(_)
        | DoElem::Expr(_, _)
        | DoElem::Bind(_, _, _)
        | DoElem::Let(_, _, _)
        | DoElem::LetRec(_, _)
        | DoElem::LetMut(_, _, _)
        | DoElem::Reassign(_, _, _)
        | DoElem::PatternReassign(_, _, _)
        | DoElem::DbgTrace(_, _) => false,
    })
}

/// Check if any Return element in the expanded sequence is followed by more elements.
///
/// Only such returns trigger `elab_do_early_return` via the `[Return, rest @ ..]`
/// dispatch pattern in `elab_do_elems`. Returns at the end of the sequence are
/// terminal and handled by `elab_pure` instead.
pub(crate) fn has_top_level_non_terminal_return(elems: &[DoElem]) -> bool {
    for (i, elem) in elems.iter().enumerate() {
        if i < elems.len() - 1 && elem_contains_return_for_outer_continuation(elem) {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_parser::{Span, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr};

    fn dummy_span() -> Span {
        Span::new(0, 0)
    }

    fn dummy_expr() -> Box<SurfaceExpr> {
        Box::new(SurfaceExpr::Ident(dummy_span(), "x".to_string()))
    }

    fn dummy_binder(name: &str) -> SurfaceBinder {
        SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit)
    }

    #[test]
    fn test_pure_elem_has_one_exit() {
        let info = infer_control_info_elem(&DoElem::Expr(dummy_span(), dummy_expr()));
        assert_eq!(info.num_regular_exits, 1);
        assert!(!info.breaks);
        assert!(!info.continues);
        assert!(!info.returns_early);
        assert!(info.reassigns.is_empty());
    }

    #[test]
    fn test_break_has_zero_exits() {
        let info = infer_control_info_elem(&DoElem::Break(dummy_span()));
        assert_eq!(info.num_regular_exits, 0);
        assert!(info.breaks);
        assert!(!info.continues);
    }

    #[test]
    fn test_continue_has_zero_exits() {
        let info = infer_control_info_elem(&DoElem::Continue(dummy_span()));
        assert_eq!(info.num_regular_exits, 0);
        assert!(info.continues);
        assert!(!info.breaks);
    }

    #[test]
    fn test_return_has_zero_exits_and_early_return() {
        let info = infer_control_info_elem(&DoElem::Return(dummy_span(), dummy_expr()));
        assert_eq!(info.num_regular_exits, 0);
        assert!(info.returns_early);
    }

    #[test]
    fn test_reassign_records_name() {
        let info = infer_control_info_elem(&DoElem::Reassign(
            dummy_span(),
            "x".to_string(),
            dummy_expr(),
        ));
        assert_eq!(info.num_regular_exits, 1);
        assert!(info.reassigns.contains("x"));
    }

    #[test]
    fn test_let_mut_is_pure() {
        // LetMut declaration does NOT add to reassigns (Lean 4 InferControlInfo.lean:97).
        // Only Reassign (the reassignment syntax `x := new_val`) adds to reassigns.
        let info = infer_control_info_elem(&DoElem::LetMut(
            dummy_span(),
            dummy_binder("y"),
            dummy_expr(),
        ));
        assert!(info.reassigns.is_empty());
        assert_eq!(info.num_regular_exits, 1);
        assert!(!info.needs_control_stack());
    }

    #[test]
    fn test_sequence_dead_code_after_break() {
        let elems = vec![
            DoElem::Break(dummy_span()),
            DoElem::Expr(dummy_span(), dummy_expr()),
        ];
        let info = infer_control_info_seq(&elems);
        assert_eq!(info.num_regular_exits, 0);
        assert!(info.breaks);
    }

    #[test]
    fn test_if_alternative_merges() {
        let then_branch = vec![DoElem::Break(dummy_span())];
        let else_branch = vec![DoElem::Continue(dummy_span())];
        let info = infer_control_info_elem(&DoElem::If(
            dummy_span(),
            dummy_expr(),
            then_branch,
            Some(else_branch),
        ));
        assert!(info.breaks);
        assert!(info.continues);
        // Both branches exit via control flow — 0 regular exits
        assert_eq!(info.num_regular_exits, 0);
    }

    #[test]
    fn test_for_loop_consumes_break_continue() {
        let body = vec![DoElem::Break(dummy_span())];
        let info = infer_control_info_elem(&DoElem::For(
            dummy_span(),
            dummy_binder("_"),
            dummy_expr(),
            body,
        ));
        // For loop consumes break/continue
        assert!(!info.breaks);
        assert!(!info.continues);
        assert_eq!(info.num_regular_exits, 1);
    }

    #[test]
    fn test_for_loop_propagates_early_return() {
        let body = vec![DoElem::Return(dummy_span(), dummy_expr())];
        let info = infer_control_info_elem(&DoElem::For(
            dummy_span(),
            dummy_binder("_"),
            dummy_expr(),
            body,
        ));
        assert!(info.returns_early);
        assert_eq!(info.num_regular_exits, 1);
    }

    #[test]
    fn test_needs_control_stack() {
        let pure_info = ControlInfo::pure();
        assert!(!pure_info.needs_control_stack());

        let break_info = infer_control_info_elem(&DoElem::Break(dummy_span()));
        assert!(break_info.needs_control_stack());

        let reassign_info = infer_control_info_elem(&DoElem::Reassign(
            dummy_span(),
            "x".to_string(),
            dummy_expr(),
        ));
        assert!(reassign_info.needs_control_stack());
    }

    #[test]
    fn test_empty_seq() {
        let info = infer_control_info_seq(&[]);
        assert_eq!(info.num_regular_exits, 1);
        assert!(!info.needs_control_stack());
    }

    #[test]
    fn test_try_catch_alternative() {
        let try_body = vec![DoElem::Expr(dummy_span(), dummy_expr())];
        let catch_body = vec![DoElem::Return(dummy_span(), dummy_expr())];
        let catch_clause = clean_parser::DoCatchClause {
            span: dummy_span(),
            binder: "e".to_string(),
            exc_type: None,
            body: catch_body,
        };
        let info = infer_control_info_elem(&DoElem::TryCatch(
            dummy_span(),
            try_body,
            vec![catch_clause],
            None,
        ));
        assert!(info.returns_early);
        // try: 1 exit, catch: 0 exits → alternative = 1 exit
        assert_eq!(info.num_regular_exits, 1);
    }

    #[test]
    fn test_has_top_level_non_terminal_return_detects_if_let_branch_return_before_rest() {
        let elems = vec![
            DoElem::IfLet(
                dummy_span(),
                clean_parser::SurfacePattern::Wildcard,
                dummy_expr(),
                vec![DoElem::Return(dummy_span(), dummy_expr())],
                Some(vec![DoElem::Expr(dummy_span(), dummy_expr())]),
            ),
            DoElem::Expr(dummy_span(), dummy_expr()),
        ];
        assert!(
            has_top_level_non_terminal_return(&elems),
            "if-let branch return before later elements should keep EarlyReturn active"
        );
    }

    fn wildcard_arm(body: Vec<DoElem>) -> clean_parser::DoMatchArm {
        clean_parser::DoMatchArm {
            span: dummy_span(),
            patterns: vec![clean_parser::SurfacePattern::Wildcard],
            body,
        }
    }

    #[test]
    fn test_has_top_level_non_terminal_return_ignores_terminal_match_branch_returns() {
        let ret = || vec![DoElem::Return(dummy_span(), dummy_expr())];
        let elems = vec![DoElem::Match(
            dummy_span(),
            vec![*dummy_expr()],
            vec![wildcard_arm(ret()), wildcard_arm(ret())],
        )];
        assert!(
            !has_top_level_non_terminal_return(&elems),
            "terminal match branch returns should still avoid EarlyReturn wrapping"
        );
    }
}
