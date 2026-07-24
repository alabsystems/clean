// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! If-let chains for Rust semantics.
//!
//! Rust's if-let chains (RFC 2497, stabilized in Rust 1.87) allow multiple
//! `let` patterns and boolean conditions to be combined with `&&`:
//!
//! ```text
//! if let Some(x) = a && x > 0 && let Ok(y) = b {
//!     // both patterns matched and condition held
//! }
//! ```
//!
//! This module provides a standalone desugaring that converts if-let chains
//! into the nested `Match` / `If` expressions already handled by the
//! evaluator. The desugaring is pure (no evaluator state required) and
//! mirrors the strategy used in `source/desugar.rs` for simple `if let`.
//!
//! ## Desugaring strategy
//!
//! Each clause in the chain is lowered right-to-left into nested expressions:
//!
//! - **Pattern clause** (`let Pat = scrutinee`): becomes a `match` with
//!   two arms -- one matching the pattern (continuing to the inner body)
//!   and a wildcard arm (executing the else branch).
//! - **Boolean clause** (`condition`): becomes an `if` expression that
//!   guards the inner body.
//!
//! For example:
//!
//! ```text
//! if let Some(x) = a && x > 0 && let Ok(y) = b { body } else { fallback }
//! ```
//!
//! desugars to:
//!
//! ```text
//! match a {
//!     Some(x) => if x > 0 {
//!         match b {
//!             Ok(y) => body,
//!             _     => fallback,
//!         }
//!     } else { fallback },
//!     _ => fallback,
//! }
//! ```

use crate::expr::{Expr, MatchArm, Pattern};
use crate::values::Value;

/// A single clause inside an if-let chain.
///
/// Clauses are evaluated left-to-right. A pattern clause introduces bindings
/// visible to all subsequent clauses and the then-branch. A boolean clause
/// acts as an early-exit guard.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum IfLetClause {
    /// Pattern-matching clause: `let pattern = scrutinee`.
    Pattern {
        /// The irrefutable or refutable pattern to match.
        pattern: Pattern,
        /// The expression whose value is matched against `pattern`.
        scrutinee: Expr,
    },

    /// Boolean guard clause: an expression that must evaluate to `true`.
    Bool(Expr),
}

/// An if-let chain: a sequence of [`IfLetClause`]s with a then-branch
/// and an optional else-branch.
///
/// Mirrors the surface syntax:
/// ```text
/// if <clause_0> && <clause_1> && ... { then } else { else_ }
/// ```
#[derive(Debug, Clone)]
pub struct IfLetChain {
    /// Clauses evaluated left-to-right. Must be non-empty.
    pub clauses: Vec<IfLetClause>,
    /// Body executed when all clauses succeed.
    pub then_branch: Box<Expr>,
    /// Body executed when any clause fails (defaults to `()` if absent).
    pub else_branch: Option<Box<Expr>>,
}

/// Desugar an [`IfLetChain`] into core `Expr` nodes.
///
/// The returned expression uses only `Match` and `If` nodes so the
/// evaluator does not need special-case support for if-let chains.
///
/// # Panics
///
/// Panics if `chain.clauses` is empty.
#[must_use]
pub fn desugar_if_let_chain(chain: &IfLetChain) -> Expr {
    assert!(
        !chain.clauses.is_empty(),
        "if-let chain must have at least one clause"
    );
    let fallback = chain
        .else_branch
        .as_deref()
        .cloned()
        .unwrap_or(Expr::Literal(Value::Unit));
    desugar_clauses(&chain.clauses, &chain.then_branch, &fallback)
}

/// Convenience wrapper: desugar a single `if let pattern = scrutinee { then } else { else_ }`.
///
/// Equivalent to an [`IfLetChain`] with one [`IfLetClause::Pattern`].
#[must_use]
pub fn desugar_simple_if_let(
    pattern: &Pattern,
    scrutinee: &Expr,
    then_branch: &Expr,
    else_branch: &Expr,
) -> Expr {
    Expr::Match {
        scrutinee: Box::new(scrutinee.clone()),
        arms: vec![
            MatchArm {
                pattern: pattern.clone(),
                guard: None,
                body: then_branch.clone(),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                guard: None,
                body: else_branch.clone(),
            },
        ],
    }
}

// --- private helpers -------------------------------------------------------

/// Recursively desugar a slice of clauses into nested `Match` / `If` nodes.
///
/// `body` is the expression to evaluate once all clauses have succeeded.
/// `fallback` is the expression used when any clause fails.
fn desugar_clauses(clauses: &[IfLetClause], body: &Expr, fallback: &Expr) -> Expr {
    match clauses {
        [] => body.clone(),
        [clause, rest @ ..] => {
            let inner = desugar_clauses(rest, body, fallback);
            match clause {
                IfLetClause::Pattern { pattern, scrutinee } => Expr::Match {
                    scrutinee: Box::new(scrutinee.clone()),
                    arms: vec![
                        MatchArm {
                            pattern: pattern.clone(),
                            guard: None,
                            body: inner,
                        },
                        MatchArm {
                            pattern: Pattern::Wildcard,
                            guard: None,
                            body: fallback.clone(),
                        },
                    ],
                },
                IfLetClause::Bool(cond) => Expr::If {
                    condition: Box::new(cond.clone()),
                    then_branch: Box::new(inner),
                    else_branch: Some(Box::new(fallback.clone())),
                },
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{EnumPatternPayload, Pattern};
    use crate::values::{BinOp, Value};

    // -- helpers ----------------------------------------------------------

    fn some_pattern(binding: &str) -> Pattern {
        Pattern::EnumVariant {
            enum_name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: EnumPatternPayload::Tuple(vec![Pattern::Binding {
                name: binding.to_string(),
                mutable: false,
                subpattern: None,
            }]),
        }
    }

    fn ok_pattern(binding: &str) -> Pattern {
        Pattern::EnumVariant {
            enum_name: "Result".to_string(),
            variant: "Ok".to_string(),
            payload: EnumPatternPayload::Tuple(vec![Pattern::Binding {
                name: binding.to_string(),
                mutable: false,
                subpattern: None,
            }]),
        }
    }

    fn var(name: &str) -> Expr {
        Expr::Var {
            name: name.to_string(),
            local_idx: 0,
        }
    }

    fn lit_u32(n: u32) -> Expr {
        Expr::Literal(Value::u32(n))
    }

    fn lit_bool(b: bool) -> Expr {
        Expr::Literal(Value::Bool(b))
    }

    fn gt_zero(name: &str) -> Expr {
        Expr::BinOp {
            op: BinOp::Gt,
            left: Box::new(var(name)),
            right: Box::new(lit_u32(0)),
        }
    }

    // -- desugar_simple_if_let --------------------------------------------

    #[test]
    fn test_simple_if_let_produces_match_with_two_arms() {
        let pat = some_pattern("x");
        let scrutinee = var("opt");
        let then_br = var("x");
        let else_br = lit_u32(0);

        let result = desugar_simple_if_let(&pat, &scrutinee, &then_br, &else_br);
        let Expr::Match { arms, .. } = &result else {
            panic!("expected Match, got {result:?}");
        };
        assert_eq!(arms.len(), 2, "should have pattern arm + wildcard arm");
        assert!(
            matches!(&arms[1].pattern, Pattern::Wildcard),
            "second arm should be wildcard"
        );
    }

    #[test]
    fn test_simple_if_let_scrutinee_preserved() {
        let pat = Pattern::Wildcard;
        let scrutinee = lit_u32(42);
        let result = desugar_simple_if_let(&pat, &scrutinee, &lit_bool(true), &lit_bool(false));
        let Expr::Match { scrutinee: s, .. } = &result else {
            panic!("expected Match");
        };
        assert!(
            matches!(s.as_ref(), Expr::Literal(Value::Uint { value: 42, .. })),
            "scrutinee should be the literal 42"
        );
    }

    // -- desugar_if_let_chain: single pattern clause ----------------------

    #[test]
    fn test_chain_single_pattern_equivalent_to_simple() {
        let chain = IfLetChain {
            clauses: vec![IfLetClause::Pattern {
                pattern: some_pattern("x"),
                scrutinee: var("opt"),
            }],
            then_branch: Box::new(var("x")),
            else_branch: Some(Box::new(lit_u32(0))),
        };
        let result = desugar_if_let_chain(&chain);
        assert!(matches!(result, Expr::Match { .. }));
    }

    // -- desugar_if_let_chain: single bool clause -------------------------

    #[test]
    fn test_chain_single_bool_produces_if() {
        let chain = IfLetChain {
            clauses: vec![IfLetClause::Bool(gt_zero("n"))],
            then_branch: Box::new(lit_u32(1)),
            else_branch: Some(Box::new(lit_u32(0))),
        };
        let result = desugar_if_let_chain(&chain);
        assert!(
            matches!(result, Expr::If { .. }),
            "single bool clause should desugar to If, got {result:?}"
        );
    }

    // -- desugar_if_let_chain: multiple clauses ---------------------------

    #[test]
    fn test_chain_two_patterns_nested_matches() {
        // if let Some(x) = a && let Ok(y) = b { body } else { fallback }
        let chain = IfLetChain {
            clauses: vec![
                IfLetClause::Pattern {
                    pattern: some_pattern("x"),
                    scrutinee: var("a"),
                },
                IfLetClause::Pattern {
                    pattern: ok_pattern("y"),
                    scrutinee: var("b"),
                },
            ],
            then_branch: Box::new(var("y")),
            else_branch: Some(Box::new(lit_u32(0))),
        };
        let result = desugar_if_let_chain(&chain);

        // outer: match a { Some(x) => <inner>, _ => 0 }
        let Expr::Match { arms, .. } = &result else {
            panic!("expected outer Match");
        };
        assert_eq!(arms.len(), 2);

        // inner: match b { Ok(y) => y, _ => 0 }
        let Expr::Match {
            arms: inner_arms, ..
        } = &arms[0].body
        else {
            panic!("expected inner Match in pattern arm");
        };
        assert_eq!(inner_arms.len(), 2);
    }

    #[test]
    fn test_chain_mixed_pattern_then_bool() {
        // if let Some(x) = opt && x > 0 { body } else { fallback }
        let chain = IfLetChain {
            clauses: vec![
                IfLetClause::Pattern {
                    pattern: some_pattern("x"),
                    scrutinee: var("opt"),
                },
                IfLetClause::Bool(gt_zero("x")),
            ],
            then_branch: Box::new(var("x")),
            else_branch: Some(Box::new(lit_u32(0))),
        };
        let result = desugar_if_let_chain(&chain);

        // outer: Match
        let Expr::Match { arms, .. } = &result else {
            panic!("expected outer Match");
        };
        // inner of pattern arm: If
        assert!(
            matches!(&arms[0].body, Expr::If { .. }),
            "bool clause should produce If inside pattern match arm"
        );
    }

    #[test]
    fn test_chain_mixed_bool_then_pattern() {
        // if x > 0 && let Some(y) = opt { body } else { fallback }
        let chain = IfLetChain {
            clauses: vec![
                IfLetClause::Bool(gt_zero("x")),
                IfLetClause::Pattern {
                    pattern: some_pattern("y"),
                    scrutinee: var("opt"),
                },
            ],
            then_branch: Box::new(var("y")),
            else_branch: Some(Box::new(lit_u32(0))),
        };
        let result = desugar_if_let_chain(&chain);

        // outer: If
        let Expr::If {
            then_branch: inner, ..
        } = &result
        else {
            panic!("expected outer If");
        };
        // inner: Match
        assert!(
            matches!(inner.as_ref(), Expr::Match { .. }),
            "pattern clause should produce Match inside If then-branch"
        );
    }

    // -- else branch defaulting -------------------------------------------

    #[test]
    fn test_chain_no_else_defaults_to_unit() {
        let chain = IfLetChain {
            clauses: vec![IfLetClause::Bool(lit_bool(true))],
            then_branch: Box::new(lit_u32(1)),
            else_branch: None,
        };
        let result = desugar_if_let_chain(&chain);
        let Expr::If { else_branch, .. } = &result else {
            panic!("expected If");
        };
        let Some(eb) = else_branch else {
            panic!("else branch should be present");
        };
        assert!(
            matches!(eb.as_ref(), Expr::Literal(Value::Unit)),
            "absent else should default to Unit, got {eb:?}"
        );
    }

    // -- three-clause chain -----------------------------------------------

    #[test]
    fn test_chain_three_clauses_nesting_depth() {
        // if let Some(x) = a && x > 0 && let Ok(y) = b { y } else { 0 }
        let chain = IfLetChain {
            clauses: vec![
                IfLetClause::Pattern {
                    pattern: some_pattern("x"),
                    scrutinee: var("a"),
                },
                IfLetClause::Bool(gt_zero("x")),
                IfLetClause::Pattern {
                    pattern: ok_pattern("y"),
                    scrutinee: var("b"),
                },
            ],
            then_branch: Box::new(var("y")),
            else_branch: Some(Box::new(lit_u32(0))),
        };
        let result = desugar_if_let_chain(&chain);

        // L0: Match (Some(x) = a)
        let Expr::Match { arms, .. } = &result else {
            panic!("L0: expected Match");
        };
        // L1: If (x > 0)
        let Expr::If {
            then_branch: l2, ..
        } = &arms[0].body
        else {
            panic!("L1: expected If inside first match arm");
        };
        // L2: Match (Ok(y) = b)
        assert!(
            matches!(l2.as_ref(), Expr::Match { .. }),
            "L2: expected Match inside If then-branch"
        );
    }

    // -- panic on empty ---------------------------------------------------

    #[test]
    #[should_panic(expected = "if-let chain must have at least one clause")]
    fn test_chain_empty_clauses_panics() {
        let chain = IfLetChain {
            clauses: vec![],
            then_branch: Box::new(lit_u32(1)),
            else_branch: None,
        };
        let _ = desugar_if_let_chain(&chain);
    }

    // -- wildcard-only pattern passes through -----------------------------

    #[test]
    fn test_chain_wildcard_pattern_always_matches() {
        let chain = IfLetChain {
            clauses: vec![IfLetClause::Pattern {
                pattern: Pattern::Wildcard,
                scrutinee: lit_u32(99),
            }],
            then_branch: Box::new(lit_bool(true)),
            else_branch: Some(Box::new(lit_bool(false))),
        };
        let result = desugar_if_let_chain(&chain);
        let Expr::Match { arms, .. } = &result else {
            panic!("expected Match");
        };
        assert!(matches!(&arms[0].pattern, Pattern::Wildcard));
    }
}
