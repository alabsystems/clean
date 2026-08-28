//! The conservative statement-completion walker.
//!
//! `analyze` maps one [`CStmt`] to its [`Completion`]; `analyze_block` folds a
//! statement sequence with reachability tracking. The `_Noreturn` entry points,
//! the `Completion` lattice and the diverging-call predicates stay in the
//! parent module — this file is only the recursive walk over statement shapes.

use super::*;

/// Compute the conservative [`Completion`] of `stmt`.
pub(super) fn analyze(stmt: &CStmt, noreturn_callees: &HashSet<&str>) -> Completion {
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
