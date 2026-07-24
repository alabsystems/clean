// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! While-let loop desugaring and termination analysis for Rust semantics.
//!
//! Rust's `while let` loops are syntactic sugar:
//!
//! ```text
//! while let Pat = scrutinee { body }
//! ```
//!
//! desugars to:
//!
//! ```text
//! loop { match scrutinee { Pat => body, _ => break } }
//! ```
//!
//! This module provides:
//! - [`WhileLetPattern`]: Classification of common while-let pattern forms
//! - [`desugar_while_let`]: Transforms while-let into loop+match core form
//! - [`analyze_while_let_termination`]: Static termination reasoning

use crate::expr::{Expr, MatchArm, Pattern};

/// Classification of patterns used in `while let` loops.
///
/// While any refutable pattern is valid, most real-world usage falls into
/// a small number of categories that we can reason about for termination.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum WhileLetPattern {
    /// `while let Some(x) = expr` — iterating over `Option`-producing sources.
    Some {
        /// Name bound inside `Some(binding)`.
        binding: String,
    },

    /// `while let Ok(x) = expr` — consuming fallible operations until error.
    Ok {
        /// Name bound inside `Ok(binding)`.
        binding: String,
    },

    /// `while let Variant(x) = expr` — arbitrary enum variant match.
    CustomVariant {
        /// Enum type name (e.g., `"MyEnum"`).
        enum_name: String,
        /// Variant being matched (e.g., `"Continue"`).
        variant: String,
        /// Binding names extracted from the payload.
        bindings: Vec<String>,
    },

    /// A nested or compound pattern (e.g., `Some(Ok(x))`).
    Nested {
        /// Outer pattern layer.
        outer: Box<WhileLetPattern>,
        /// Inner pattern layer.
        inner: Box<WhileLetPattern>,
    },

    /// Any pattern that does not match one of the known forms.
    Other,
}

/// Result of static termination analysis on a while-let loop.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TerminationResult {
    /// The loop provably terminates (e.g., scrutinee is a constant `None`).
    Terminates,

    /// The loop provably does not terminate (scrutinee always matches).
    Diverges,

    /// Termination depends on runtime behavior — cannot determine statically.
    Unknown,
}

/// Classify a [`Pattern`] into a [`WhileLetPattern`] for analysis.
///
/// Recognises `Some(x)`, `Ok(x)`, nested combinations, and arbitrary
/// enum variant patterns. Falls back to [`WhileLetPattern::Other`] for
/// patterns that do not fit a known category.
#[must_use]
pub fn classify_pattern(pattern: &Pattern) -> WhileLetPattern {
    match pattern {
        Pattern::EnumVariant {
            enum_name,
            variant,
            payload,
        } => {
            let bindings = extract_payload_bindings(payload);

            // Recognise Option::Some
            if (enum_name == "Option" || enum_name.is_empty()) && variant == "Some" {
                if let [single] = bindings.as_slice() {
                    // Check for nested pattern inside Some(...)
                    if let Some(inner) = extract_inner_enum_pattern(payload) {
                        let inner_classified = classify_pattern(&inner);
                        if inner_classified != WhileLetPattern::Other {
                            return WhileLetPattern::Nested {
                                outer: Box::new(WhileLetPattern::Some {
                                    binding: single.clone(),
                                }),
                                inner: Box::new(inner_classified),
                            };
                        }
                    }
                    return WhileLetPattern::Some {
                        binding: single.clone(),
                    };
                }
            }

            // Recognise Result::Ok
            if (enum_name == "Result" || enum_name.is_empty()) && variant == "Ok" {
                if let [single] = bindings.as_slice() {
                    return WhileLetPattern::Ok {
                        binding: single.clone(),
                    };
                }
            }

            WhileLetPattern::CustomVariant {
                enum_name: enum_name.clone(),
                variant: variant.clone(),
                bindings,
            }
        }
        _ => WhileLetPattern::Other,
    }
}

/// Desugar a `while let` expression into the core `loop { match ... }` form.
///
/// The desugaring follows the Rust Reference specification:
///
/// ```text
/// while let PAT = SCRUTINEE { BODY }
///   =>
/// loop {
///   match SCRUTINEE {
///     PAT [if GUARD] => BODY,
///     _              => break,
///   }
/// }
/// ```
///
/// If a loop label is provided it is attached to the outer `loop`.
#[must_use]
pub fn desugar_while_let(
    pattern: Pattern,
    scrutinee: Expr,
    body: Expr,
    guard: Option<Expr>,
    label: Option<String>,
) -> Expr {
    Expr::Loop {
        label,
        body: Box::new(Expr::Match {
            scrutinee: Box::new(scrutinee),
            arms: vec![
                MatchArm {
                    pattern,
                    guard,
                    body,
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::Break {
                        label: None,
                        value: None,
                    },
                },
            ],
        }),
    }
}

/// Analyse whether a `while let` loop is statically known to terminate.
///
/// This performs conservative reasoning:
/// - A literal `None` scrutinee never matches `Some(x)` — terminates immediately.
/// - A literal `Some(v)` scrutinee always matches — diverges.
/// - Everything else is [`TerminationResult::Unknown`].
#[must_use]
pub fn analyze_while_let_termination(
    pattern: &WhileLetPattern,
    scrutinee: &Expr,
) -> TerminationResult {
    match (pattern, scrutinee) {
        // while let Some(_) = None  =>  terminates on first iteration
        (
            WhileLetPattern::Some { .. },
            Expr::EnumVariant {
                enum_name, variant, ..
            },
        ) if (enum_name == "Option" || enum_name.is_empty()) && variant == "None" => {
            TerminationResult::Terminates
        }

        // while let Some(_) = Some(v)  =>  always matches, diverges
        (
            WhileLetPattern::Some { .. },
            Expr::EnumVariant {
                enum_name, variant, ..
            },
        ) if (enum_name == "Option" || enum_name.is_empty()) && variant == "Some" => {
            TerminationResult::Diverges
        }

        // while let Ok(_) = Err(e)  =>  terminates on first iteration
        (
            WhileLetPattern::Ok { .. },
            Expr::EnumVariant {
                enum_name, variant, ..
            },
        ) if (enum_name == "Result" || enum_name.is_empty()) && variant == "Err" => {
            TerminationResult::Terminates
        }

        // while let Ok(_) = Ok(v)  =>  always matches, diverges
        (
            WhileLetPattern::Ok { .. },
            Expr::EnumVariant {
                enum_name, variant, ..
            },
        ) if (enum_name == "Result" || enum_name.is_empty()) && variant == "Ok" => {
            TerminationResult::Diverges
        }

        // Custom variant matching a different variant of the same enum
        (
            WhileLetPattern::CustomVariant {
                enum_name: pat_enum,
                variant: pat_var,
                ..
            },
            Expr::EnumVariant {
                enum_name: scr_enum,
                variant: scr_var,
                ..
            },
        ) if pat_enum == scr_enum && pat_var != scr_var => TerminationResult::Terminates,

        // Custom variant matching the same variant  =>  diverges
        (
            WhileLetPattern::CustomVariant {
                enum_name: pat_enum,
                variant: pat_var,
                ..
            },
            Expr::EnumVariant {
                enum_name: scr_enum,
                variant: scr_var,
                ..
            },
        ) if pat_enum == scr_enum && pat_var == scr_var => TerminationResult::Diverges,

        // Nested: outer terminates => whole thing terminates
        (WhileLetPattern::Nested { outer, .. }, scrutinee) => {
            let outer_result = analyze_while_let_termination(outer, scrutinee);
            if outer_result == TerminationResult::Terminates {
                return TerminationResult::Terminates;
            }
            TerminationResult::Unknown
        }

        _ => TerminationResult::Unknown,
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Extract top-level binding names from an enum pattern payload.
fn extract_payload_bindings(payload: &crate::expr::EnumPatternPayload) -> Vec<String> {
    use crate::expr::EnumPatternPayload;
    match payload {
        EnumPatternPayload::Unit => Vec::new(),
        EnumPatternPayload::Tuple(patterns) => patterns
            .iter()
            .filter_map(|p| match p {
                Pattern::Binding { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect(),
        EnumPatternPayload::Struct(fields) => fields
            .iter()
            .filter_map(|(_, p)| match p {
                Pattern::Binding { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect(),
    }
}

/// If the enum pattern payload contains exactly one tuple element that is
/// itself an enum variant pattern, return it for nested classification.
fn extract_inner_enum_pattern(payload: &crate::expr::EnumPatternPayload) -> Option<Pattern> {
    use crate::expr::EnumPatternPayload;
    match payload {
        EnumPatternPayload::Tuple(patterns) if patterns.len() == 1 => {
            let inner = &patterns[0];
            // Unwrap binding-with-subpattern to reach the inner enum pattern
            match inner {
                Pattern::EnumVariant { .. } => Some(inner.clone()),
                Pattern::Binding {
                    subpattern: Some(sub),
                    ..
                } => {
                    if matches!(sub.as_ref(), Pattern::EnumVariant { .. }) {
                        Some(sub.as_ref().clone())
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "while_let_tests.rs"]
mod tests;
