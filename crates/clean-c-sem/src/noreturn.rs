// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `_Noreturn` function specifier checking (C11 6.7.4).
//!
//! A function declared with the `_Noreturn` specifier (or the
//! `<stdnoreturn.h>` `noreturn` convenience macro) promises never to return
//! to its caller. If such a function *can* return — either by executing a
//! reachable `return` statement or by falling off the end of its body — the
//! behavior is undefined (C11 6.7.4p2):
//!
//! > If a function is declared with a `_Noreturn` function specifier and
//! > eventually returns to its caller [...] the behavior is undefined.
//!
//! This module statically detects the *clear* cases of such UB. The analysis
//! is deliberately **sound against false positives**: a function that this
//! module flags can genuinely return. A genuinely-diverging `_Noreturn`
//! function (one that always ends the program, jumps away, or loops forever)
//! is never flagged.
//!
//! ## Soundness model
//!
//! For each statement we compute, conservatively, whether control may:
//!
//! - *fall through* — reach the end of the statement and continue, and
//! - *return* — execute a `return` statement that hands control to the caller.
//!
//! A `_Noreturn` function is flagged iff its body may fall through (reach the
//! closing brace) or may return. To avoid flagging diverging functions, any
//! construct we cannot analyze precisely (e.g. `goto`, `switch`, inline `asm`)
//! is treated as *not* falling through and *not* returning — an
//! under-approximation that yields false negatives (missed bugs) rather than
//! false positives. Calls to known diverging functions (`abort`, `exit`,
//! `_Exit`, `quick_exit`, `longjmp`, `__builtin_unreachable`,
//! `__builtin_trap`) and to other `_Noreturn` functions in the same
//! translation unit are recognized as terminating control flow.

use crate::expr::CExpr;
use crate::stmt::{CStmt, FuncDef};
use crate::ub::UBKind;
use std::collections::HashSet;

/// Standard-library and builtin functions that never return to their caller.
///
/// These mirror the `_Noreturn` declarations in the C standard library
/// (`<stdlib.h>`, `<setjmp.h>`) plus common compiler builtins. A call to any
/// of these terminates the current control-flow path.
const DIVERGING_BUILTINS: &[&str] = &[
    "abort",
    "exit",
    "_Exit",
    "quick_exit",
    "longjmp",
    "_longjmp",
    "siglongjmp",
    "__builtin_unreachable",
    "__builtin_trap",
    "__builtin_abort",
    "thrd_exit",
    "pthread_exit",
];

/// Conservative completion behavior of a statement.
///
/// Both flags are *may* approximations: `true` means the behavior is possible,
/// `false` means it is provably impossible (or, for unanalyzable constructs,
/// conservatively assumed impossible so we never over-report).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Completion {
    /// Control may reach the end of the statement and continue past it.
    may_fall_through: bool,
    /// Control may execute a `return` that hands control back to the caller.
    may_return: bool,
}

impl Completion {
    /// A statement that completes normally and contains no `return`.
    const FALL_THROUGH: Self = Self {
        may_fall_through: true,
        may_return: false,
    };

    /// A statement that diverts/terminates control: neither falls through nor
    /// returns to the caller (e.g. a diverging call, `break`, `goto`).
    const DIVERTS: Self = Self {
        may_fall_through: false,
        may_return: false,
    };

    /// A `return` statement: returns to the caller, never falls through.
    const RETURNS: Self = Self {
        may_fall_through: false,
        may_return: true,
    };
}

/// Check every function in a translation unit for `_Noreturn` violations.
///
/// `funcs` is the full set of function definitions in the translation unit;
/// any `_Noreturn` function among them is treated as a diverging callee when
/// analyzing the others. Returns one [`UBKind::NoreturnReturns`] per offending
/// function (in declaration order).
#[must_use]
pub fn check_translation_unit(funcs: &[FuncDef]) -> Vec<UBKind> {
    let noreturn_callees: HashSet<&str> = funcs
        .iter()
        .filter(|f| f.is_noreturn)
        .map(|f| f.name.as_str())
        .collect();

    funcs
        .iter()
        .filter_map(|f| check_func_with_callees(f, &noreturn_callees))
        .collect()
}

/// Check a single function for a `_Noreturn` violation.
///
/// Returns `Some(UBKind::NoreturnReturns)` if the function is declared
/// `_Noreturn` yet may return to its caller; `None` if the function is not
/// `_Noreturn` or provably diverges. Other `_Noreturn` functions in the same
/// translation unit are not known to this single-function entry point; use
/// [`check_translation_unit`] when cross-function divergence matters.
#[must_use]
pub fn check_func(func: &FuncDef) -> Option<UBKind> {
    check_func_with_callees(func, &HashSet::new())
}

fn check_func_with_callees(func: &FuncDef, noreturn_callees: &HashSet<&str>) -> Option<UBKind> {
    if !func.is_noreturn {
        return None;
    }
    let completion = analyze(&func.body, noreturn_callees);
    if completion.may_fall_through || completion.may_return {
        Some(UBKind::NoreturnReturns(func.name.clone()))
    } else {
        None
    }
}

/// Determine whether `expr`, when evaluated as a full expression, terminates
/// the current control-flow path (i.e. is a call to a diverging function).
fn expr_diverges(expr: &CExpr, noreturn_callees: &HashSet<&str>) -> bool {
    if let CExpr::Call { func, .. } = expr {
        if let CExpr::Var(name) = func.as_ref() {
            return DIVERGING_BUILTINS.contains(&name.as_str())
                || noreturn_callees.contains(name.as_str());
        }
    }
    false
}

/// Is `expr` a compile-time-nonzero integer constant (e.g. the `1` in
/// `while (1)`)? Used to recognize syntactically-infinite loops.
fn is_nonzero_constant(expr: &CExpr) -> bool {
    match expr {
        CExpr::IntLit(v) => *v != 0,
        CExpr::UIntLit(v) => *v != 0,
        CExpr::CharLit(c) => *c != 0,
        _ => false,
    }
}

/// Conservative check for a `break` that could exit *this* loop.
///
/// `break` statements inside nested loops/switches target the inner construct,
/// so they are not counted. A `break` anywhere else that is reachable can exit
/// the loop; we over-approximate "has a break" (treat the loop as escapable)
/// to stay sound against false positives — i.e. we would rather *not* flag a
/// loop that might exit than wrongly flag a diverging one.
fn has_loop_break(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Break => true,
        // A nested loop or switch captures its own `break`.
        CStmt::While { .. } | CStmt::DoWhile { .. } | CStmt::For { .. } | CStmt::Switch { .. } => {
            false
        }
        CStmt::Block(stmts) => stmts.iter().any(has_loop_break),
        CStmt::If {
            then_stmt,
            else_stmt,
            ..
        } => has_loop_break(then_stmt) || else_stmt.as_ref().is_some_and(|s| has_loop_break(s)),
        CStmt::Case { stmt, .. } | CStmt::Label { stmt, .. } => has_loop_break(stmt),
        _ => false,
    }
}

/// Compute the conservative [`Completion`] of `stmt`.
fn analyze(stmt: &CStmt, noreturn_callees: &HashSet<&str>) -> Completion {
    match stmt {
        // Statements with no control effect: complete normally.
        CStmt::Empty
        | CStmt::Decl(_)
        | CStmt::DeclList(_)
        | CStmt::Assert(_)
        | CStmt::Assume(_)
        | CStmt::StaticAssert { .. } => Completion::FALL_THROUGH,

        // An expression statement falls through unless it is a diverging call.
        CStmt::Expr(e) => {
            if expr_diverges(e, noreturn_callees) {
                Completion::DIVERTS
            } else {
                Completion::FALL_THROUGH
            }
        }

        CStmt::Return(_) => Completion::RETURNS,

        // `break`/`continue`/`goto` divert control away from the normal
        // sequential successor; they never return to the caller.
        CStmt::Break | CStmt::Continue | CStmt::Goto(_) => Completion::DIVERTS,

        // Unanalyzable constructs: assume they do not fall through and do not
        // return (sound under-approximation — never over-reports).
        CStmt::Asm(_) | CStmt::FuncDef(_) => Completion::DIVERTS,

        CStmt::Block(stmts) => analyze_block(stmts, noreturn_callees),

        CStmt::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            let then_c = analyze(then_stmt, noreturn_callees);
            match else_stmt {
                Some(else_s) => {
                    let else_c = analyze(else_s, noreturn_callees);
                    Completion {
                        may_fall_through: then_c.may_fall_through || else_c.may_fall_through,
                        may_return: then_c.may_return || else_c.may_return,
                    }
                }
                // No `else`: the condition can be false, so control can skip
                // the `then` branch and fall through.
                None => Completion {
                    may_fall_through: true,
                    may_return: then_c.may_return,
                },
            }
        }

        CStmt::While { cond, body } => {
            let body_c = analyze(body, noreturn_callees);
            let infinite = is_nonzero_constant(cond) && !has_loop_break(body);
            Completion {
                may_fall_through: !infinite,
                may_return: body_c.may_return,
            }
        }

        CStmt::DoWhile { body, cond } => {
            let body_c = analyze(body, noreturn_callees);
            let infinite = is_nonzero_constant(cond) && !has_loop_break(body);
            Completion {
                may_fall_through: !infinite,
                may_return: body_c.may_return,
            }
        }

        CStmt::For { cond, body, .. } => {
            let body_c = analyze(body, noreturn_callees);
            // A `for` with no condition (`for(;;)`) or a nonzero-constant
            // condition loops forever unless the body can `break`.
            let cond_always_true = cond.as_ref().is_none_or(is_nonzero_constant);
            let infinite = cond_always_true && !has_loop_break(body);
            Completion {
                may_fall_through: !infinite,
                may_return: body_c.may_return,
            }
        }

        // A label simply names its inner statement.
        CStmt::Label { stmt, .. } | CStmt::Case { stmt, .. } => analyze(stmt, noreturn_callees),

        // `switch` fall-through, `default`, and case ordering make precise
        // analysis involved; conservatively report only the `return`s we can
        // see and never claim the switch itself falls through.
        CStmt::Switch { body, .. } => {
            let body_c = analyze(body, noreturn_callees);
            Completion {
                may_fall_through: false,
                may_return: body_c.may_return,
            }
        }
    }
}

/// Analyze a statement sequence with reachability tracking: a statement is
/// only reachable if every preceding statement may fall through.
fn analyze_block(stmts: &[CStmt], noreturn_callees: &HashSet<&str>) -> Completion {
    let mut reachable = true;
    let mut may_return = false;

    for stmt in stmts {
        if !reachable {
            // Unreachable code cannot make the function return; ignore it.
            // (Labels can be reached via `goto`, but we conservatively do not
            // model that, keeping the analysis sound against false positives.)
            break;
        }
        let c = analyze(stmt, noreturn_callees);
        may_return = may_return || c.may_return;
        reachable = c.may_fall_through;
    }

    Completion {
        // An empty block, or a block whose last reachable statement falls
        // through, completes normally.
        may_fall_through: reachable,
        may_return,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::CExpr;
    use crate::stmt::{CStmt, FuncDef};
    use crate::types::CType;

    fn call(name: &str) -> CStmt {
        CStmt::Expr(CExpr::call(CExpr::var(name), vec![]))
    }

    fn noreturn_fn(name: &str, body: CStmt) -> FuncDef {
        FuncDef::new(name, CType::Void, vec![], body).with_noreturn(true)
    }

    #[test]
    fn test_check_func_abort_only_passes() {
        // _Noreturn void f(void) { abort(); }
        let f = noreturn_fn("f", CStmt::Block(vec![call("abort")]));
        assert_eq!(
            check_func(&f),
            None,
            "a _Noreturn function whose body always aborts must not be flagged"
        );
    }

    #[test]
    fn test_check_func_falls_off_end_flagged() {
        // _Noreturn void g(void) { }
        let g = noreturn_fn("g", CStmt::Block(vec![]));
        assert_eq!(
            check_func(&g),
            Some(UBKind::NoreturnReturns("g".to_string())),
            "a _Noreturn function that falls off the end must be flagged"
        );
    }

    #[test]
    fn test_check_func_reachable_return_flagged() {
        // _Noreturn void h(int x) { if (x) return; abort(); }
        let h = FuncDef::new(
            "h",
            CType::Void,
            vec![crate::stmt::FuncParam::new("x", CType::int())],
            CStmt::Block(vec![
                CStmt::if_stmt(CExpr::var("x"), CStmt::Return(None)),
                call("abort"),
            ]),
        )
        .with_noreturn(true);
        assert_eq!(
            check_func(&h),
            Some(UBKind::NoreturnReturns("h".to_string())),
            "a _Noreturn function with a reachable return must be flagged"
        );
    }

    #[test]
    fn test_check_func_non_noreturn_unaffected() {
        // void g(void) { }  -- not _Noreturn, so never flagged.
        let g = FuncDef::new("g", CType::Void, vec![], CStmt::Block(vec![]));
        assert_eq!(
            check_func(&g),
            None,
            "a function without _Noreturn is never subject to the check"
        );
    }

    #[test]
    fn test_check_func_exit_passes() {
        // _Noreturn void f(void) { exit(1); }
        let f = noreturn_fn(
            "f",
            CStmt::Block(vec![CStmt::Expr(CExpr::call(
                CExpr::var("exit"),
                vec![CExpr::int(1)],
            ))]),
        );
        assert_eq!(check_func(&f), None, "exit() diverges; must not be flagged");
    }

    #[test]
    fn test_check_func_return_after_abort_passes() {
        // _Noreturn void f(void) { abort(); return; }
        // The trailing return is unreachable, so the function still diverges.
        let f = noreturn_fn("f", CStmt::Block(vec![call("abort"), CStmt::Return(None)]));
        assert_eq!(
            check_func(&f),
            None,
            "a return after an unconditional abort is unreachable and must not flag"
        );
    }

    #[test]
    fn test_check_func_infinite_loop_passes() {
        // _Noreturn void f(void) { while (1) {} }
        let f = noreturn_fn(
            "f",
            CStmt::Block(vec![CStmt::while_loop(CExpr::int(1), CStmt::Block(vec![]))]),
        );
        assert_eq!(
            check_func(&f),
            None,
            "an infinite while loop never returns; must not be flagged"
        );
    }

    #[test]
    fn test_check_func_for_no_cond_loop_passes() {
        // _Noreturn void f(void) { for(;;) {} }
        let f = noreturn_fn(
            "f",
            CStmt::Block(vec![CStmt::for_loop(
                None,
                None,
                None,
                CStmt::Block(vec![]),
            )]),
        );
        assert_eq!(
            check_func(&f),
            None,
            "an unconditional for loop never returns; must not be flagged"
        );
    }

    #[test]
    fn test_check_func_infinite_loop_with_break_flagged() {
        // _Noreturn void f(void) { while (1) { break; } }
        // The break exits the loop, so control falls off the end.
        let f = noreturn_fn(
            "f",
            CStmt::Block(vec![CStmt::while_loop(
                CExpr::int(1),
                CStmt::Block(vec![CStmt::Break]),
            )]),
        );
        assert_eq!(
            check_func(&f),
            Some(UBKind::NoreturnReturns("f".to_string())),
            "an infinite loop with a break exits and falls off the end; must be flagged"
        );
    }

    #[test]
    fn test_check_func_both_if_branches_diverge_passes() {
        // _Noreturn void f(int x) { if (x) abort(); else exit(1); }
        let f = FuncDef::new(
            "f",
            CType::Void,
            vec![crate::stmt::FuncParam::new("x", CType::int())],
            CStmt::Block(vec![CStmt::if_else(
                CExpr::var("x"),
                call("abort"),
                CStmt::Expr(CExpr::call(CExpr::var("exit"), vec![CExpr::int(1)])),
            )]),
        )
        .with_noreturn(true);
        assert_eq!(
            check_func(&f),
            None,
            "both branches diverge, so the function never returns"
        );
    }

    #[test]
    fn test_check_func_if_without_else_flagged() {
        // _Noreturn void f(int x) { if (x) abort(); }
        // The false path skips the abort and falls off the end.
        let f = FuncDef::new(
            "f",
            CType::Void,
            vec![crate::stmt::FuncParam::new("x", CType::int())],
            CStmt::Block(vec![CStmt::if_stmt(CExpr::var("x"), call("abort"))]),
        )
        .with_noreturn(true);
        assert_eq!(
            check_func(&f),
            Some(UBKind::NoreturnReturns("f".to_string())),
            "the else-less if can fall through; the function can return"
        );
    }

    #[test]
    fn test_check_translation_unit_noreturn_callee_passes() {
        // _Noreturn void die(void) { abort(); }
        // _Noreturn void f(void) { die(); }
        let die = noreturn_fn("die", CStmt::Block(vec![call("abort")]));
        let f = noreturn_fn("f", CStmt::Block(vec![call("die")]));
        let reports = check_translation_unit(&[die, f]);
        assert!(
            reports.is_empty(),
            "calling another _Noreturn function diverges; got {reports:?}"
        );
    }

    #[test]
    fn test_check_translation_unit_unknown_callee_flagged() {
        // _Noreturn void f(void) { do_work(); }   // do_work returns normally
        let f = noreturn_fn("f", CStmt::Block(vec![call("do_work")]));
        let reports = check_translation_unit(&[f]);
        assert_eq!(
            reports,
            vec![UBKind::NoreturnReturns("f".to_string())],
            "a call to an ordinary function falls through and can return"
        );
    }

    #[test]
    fn test_check_func_return_in_loop_flagged() {
        // _Noreturn void f(void) { while (1) { return; } }
        let f = noreturn_fn(
            "f",
            CStmt::Block(vec![CStmt::while_loop(
                CExpr::int(1),
                CStmt::Block(vec![CStmt::Return(None)]),
            )]),
        );
        assert_eq!(
            check_func(&f),
            Some(UBKind::NoreturnReturns("f".to_string())),
            "a return inside the loop hands control to the caller; must be flagged"
        );
    }
}
