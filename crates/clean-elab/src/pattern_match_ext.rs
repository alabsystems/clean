// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended pattern match elaboration.
//!
//! Compiles complex pattern matching syntax (nested patterns, or-patterns,
//! as-patterns, guard clauses, literal patterns) into kernel case expressions.
//! This module operates on a high-level `Pattern` AST that is lowered to
//! `clean_kernel::Expr` via `compile_patterns`.
//!
//! Reference: Lean 4 `Lean.Elab.Match` (C++ src/library/compiler/match.cpp).

use crate::error::ElabError;
use clean_kernel::expr::BinderInfo;
use clean_kernel::{Expr, Name};

// ---------------------------------------------------------------------------
// Pattern types
// ---------------------------------------------------------------------------

/// A high-level pattern node before compilation to kernel expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum Pattern {
    /// Constructor pattern: `Ctor arg1 arg2 ...`
    Ctor { name: Name, args: Vec<Pattern> },
    /// Variable binding: `x`
    Var(Name),
    /// Wildcard: `_`
    Wildcard,
    /// Literal pattern: `0`, `42`, `"hello"`, `'a'`
    Literal(LitPattern),
    /// Or-pattern: `p1 | p2 | ...`  (Lean 4 extension)
    Or(Vec<Pattern>),
    /// As-pattern: `x@p`  — binds `x` to the scrutinee while matching `p`
    As { name: Name, pattern: Box<Pattern> },
    /// Inaccessible (dot) pattern: `.expr` — used in dependent matching
    Inaccessible(Expr),
}

/// Literal values that can appear in patterns.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum LitPattern {
    Nat(u64),
    Int(i64),
    String(String),
    Char(char),
}

// ---------------------------------------------------------------------------
// Match arm & configuration
// ---------------------------------------------------------------------------

/// A single arm of a `match` expression before compilation.
#[derive(Debug, Clone)]
pub(crate) struct MatchArm {
    /// Patterns to match (one per scrutinee in multi-discriminant match).
    pub patterns: Vec<Pattern>,
    /// Optional guard expression (`if cond`).
    pub guard: Option<Expr>,
    /// Right-hand side body expression.
    pub body: Expr,
}

/// Configuration for match elaboration passes.
#[derive(Debug, Clone)]
pub(crate) struct MatchElabConfig {
    /// Whether to check exhaustiveness and report missing patterns.
    pub check_exhaustive: bool,
    /// Whether to detect and report redundant arms.
    pub check_redundant: bool,
    /// Maximum pattern nesting depth before bailing out.
    pub max_depth: usize,
}

impl Default for MatchElabConfig {
    fn default() -> Self {
        Self {
            check_exhaustive: true,
            check_redundant: true,
            max_depth: 20,
        }
    }
}

/// Result of elaborating a match expression.
#[derive(Debug, Clone)]
pub(crate) struct MatchElabResult {
    /// The compiled kernel expression.
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    pub compiled: Expr,
    /// Warnings emitted during compilation.
    pub warnings: Vec<MatchWarning>,
    /// Number of arms after expansion (or-patterns may increase this).
    pub arms_count: usize,
}

/// Warnings produced during match elaboration.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum MatchWarning {
    /// The match is not exhaustive; `missing` lists uncovered patterns.
    NonExhaustive { missing: Vec<Pattern> },
    /// Arm at `arm_index` (0-based, post-expansion) is redundant.
    Redundant { arm_index: usize },
    /// Multiple arms have overlapping guard conditions.
    OverlappingGuards,
}

// ---------------------------------------------------------------------------
// Well-formedness & depth
// ---------------------------------------------------------------------------

/// Validate that a pattern is structurally well-formed.
///
/// Checks:
/// - Or-patterns must have >=2 alternatives.
/// - Constructor args are recursively well-formed.
/// - As-patterns wrap a well-formed inner pattern.
/// - Nesting depth does not exceed a reasonable bound (1000).
pub(crate) fn check_pattern_well_formed(pattern: &Pattern) -> Result<(), ElabError> {
    check_well_formed_inner(pattern, 0)
}

fn check_well_formed_inner(pattern: &Pattern, depth: usize) -> Result<(), ElabError> {
    if depth > 1000 {
        return Err(ElabError::NotImplemented(
            "pattern nesting depth exceeds 1000".to_string(),
        ));
    }
    match pattern {
        Pattern::Wildcard | Pattern::Var(_) | Pattern::Literal(_) | Pattern::Inaccessible(_) => {
            Ok(())
        }
        Pattern::Ctor { args, .. } => {
            for arg in args {
                check_well_formed_inner(arg, depth + 1)?;
            }
            Ok(())
        }
        Pattern::Or(alts) => {
            if alts.len() < 2 {
                return Err(ElabError::NotImplemented(
                    "or-pattern must have at least 2 alternatives".to_string(),
                ));
            }
            for alt in alts {
                check_well_formed_inner(alt, depth + 1)?;
            }
            Ok(())
        }
        Pattern::As { pattern: inner, .. } => check_well_formed_inner(inner, depth + 1),
    }
}

/// Compute the maximum nesting depth of a pattern tree.
///
/// - Leaf patterns (`Var`, `Wildcard`, `Literal`, `Inaccessible`) have depth 0.
/// - Composite patterns (`Ctor`, `Or`, `As`) have depth = 1 + max child depth.
pub(crate) fn pattern_depth(pattern: &Pattern) -> usize {
    match pattern {
        Pattern::Wildcard | Pattern::Var(_) | Pattern::Literal(_) | Pattern::Inaccessible(_) => 0,
        Pattern::Ctor { args, .. } => {
            let max_child = args.iter().map(pattern_depth).max().unwrap_or(0);
            1 + max_child
        }
        Pattern::Or(alts) => {
            let max_child = alts.iter().map(pattern_depth).max().unwrap_or(0);
            1 + max_child
        }
        Pattern::As { pattern: inner, .. } => 1 + pattern_depth(inner),
    }
}

// ---------------------------------------------------------------------------
// Or-pattern expansion
// ---------------------------------------------------------------------------

/// Expand or-patterns in a match arm into multiple arms.
///
/// Given an arm with patterns `[A, B | C, D]`, produces two arms:
///   - `[A, B, D]` → same guard & body
///   - `[A, C, D]` → same guard & body (cloned)
///
/// Arms without or-patterns are returned unchanged (as a singleton vec).
pub(crate) fn expand_or_patterns(arm: &MatchArm) -> Vec<MatchArm> {
    // Find the first pattern position that contains an Or.
    let or_idx = arm
        .patterns
        .iter()
        .position(|p| matches!(p, Pattern::Or(_)));

    let Some(idx) = or_idx else {
        return vec![arm.clone()];
    };

    let Pattern::Or(alts) = &arm.patterns[idx] else {
        return vec![arm.clone()];
    };

    let mut result = Vec::with_capacity(alts.len());
    for alt in alts {
        let mut new_patterns = arm.patterns.clone();
        new_patterns[idx] = alt.clone();
        let new_arm = MatchArm {
            patterns: new_patterns,
            guard: arm.guard.clone(),
            body: arm.body.clone(),
        };
        // Recursively expand in case there are more or-patterns.
        result.extend(expand_or_patterns(&new_arm));
    }
    result
}

// ---------------------------------------------------------------------------
// As-pattern binding extraction
// ---------------------------------------------------------------------------

/// Extract as-pattern bindings from a match arm.
///
/// Returns the arm with `As` nodes replaced by their inner pattern, plus a
/// list of `(name, scrutinee_placeholder)` bindings that need to be let-bound
/// around the arm body. The placeholder is `Expr::const_str("_")` since the
/// actual scrutinee is only known at compile time.
pub(crate) fn bind_as_patterns(arm: &MatchArm) -> (MatchArm, Vec<(Name, Expr)>) {
    let mut bindings = Vec::new();
    let new_patterns = arm
        .patterns
        .iter()
        .map(|p| strip_as(p, &mut bindings))
        .collect();
    let new_arm = MatchArm {
        patterns: new_patterns,
        guard: arm.guard.clone(),
        body: arm.body.clone(),
    };
    (new_arm, bindings)
}

fn strip_as(pattern: &Pattern, bindings: &mut Vec<(Name, Expr)>) -> Pattern {
    match pattern {
        Pattern::As {
            name,
            pattern: inner,
        } => {
            bindings.push((name.clone(), Expr::const_str("_")));
            strip_as(inner, bindings)
        }
        Pattern::Ctor { name, args } => Pattern::Ctor {
            name: name.clone(),
            args: args.iter().map(|a| strip_as(a, bindings)).collect(),
        },
        Pattern::Or(alts) => Pattern::Or(alts.iter().map(|a| strip_as(a, bindings)).collect()),
        other => other.clone(),
    }
}

// ---------------------------------------------------------------------------
// Pattern compilation
// ---------------------------------------------------------------------------

/// Compile a list of match arms against a scrutinee into nested case/let
/// expressions.
///
/// This is a simplified compilation that:
/// 1. Expands or-patterns into flat arms.
/// 2. Extracts as-pattern bindings.
/// 3. Wraps each arm body with let-bindings for as-patterns.
/// 4. Builds a chain of if-then-else for literal patterns, or a casesOn
///    spine for constructor patterns.
///
/// For constructor patterns, each arm is lowered to a `casesOn` application
/// where the constructor branch invokes the arm body. Variable and wildcard
/// patterns act as catch-all default branches.
pub(crate) fn compile_patterns(scrutinee: &Expr, arms: &[MatchArm]) -> Expr {
    if arms.is_empty() {
        return Expr::const_str("sorryAx");
    }

    let expanded: Vec<MatchArm> = arms.iter().flat_map(expand_or_patterns).collect();
    let mut result: Option<Expr> = None;

    // Build from last arm to first so the default falls through.
    for arm in expanded.iter().rev() {
        let (cleaned, as_bindings) = bind_as_patterns(arm);
        let body = prepare_arm_body(scrutinee, &cleaned, &as_bindings, &result);
        let compiled_arm = compile_first_pattern(scrutinee, &cleaned, body, &result);
        result = Some(compiled_arm);
    }

    result.unwrap_or_else(|| Expr::const_str("sorryAx"))
}

/// Prepare the arm body: wrap with as-pattern let-bindings and guard ite.
fn prepare_arm_body(
    scrutinee: &Expr,
    arm: &MatchArm,
    as_bindings: &[(Name, Expr)],
    fallback: &Option<Expr>,
) -> Expr {
    let mut body = arm.body.clone();

    // Wrap body with let-bindings for as-pattern names.
    for (name, _placeholder) in as_bindings.iter().rev() {
        body = Expr::let_named(
            name.clone(),
            Expr::const_str("_"),
            scrutinee.clone(),
            body,
            false,
        );
    }

    // Apply guard: if guard then body else <fallback>
    if let Some(guard_expr) = &arm.guard {
        let fb = fallback
            .clone()
            .unwrap_or_else(|| Expr::const_str("sorryAx"));
        body = build_ite(guard_expr.clone(), body, fb);
    }

    body
}

/// Lower the first pattern position of a cleaned arm into a kernel Expr.
fn compile_first_pattern(
    scrutinee: &Expr,
    arm: &MatchArm,
    body: Expr,
    fallback: &Option<Expr>,
) -> Expr {
    match arm.patterns.first() {
        Some(Pattern::Ctor { name, args }) => {
            let cases_on = Name::from_string(&format!("{}.casesOn", name));
            let ctor_branch = args.iter().rev().fold(body, |acc, _| {
                Expr::lam(BinderInfo::Default, Expr::const_str("_"), acc)
            });
            // Degenerate placeholder lowering (no motive/levels, single
            // branch). Scrutinee-before-branch matches the Lean-faithful
            // casesOn order: motive, (indices,) major, then minors.
            Expr::apps(
                Expr::const_(cases_on, Vec::<clean_kernel::Level>::new()),
                [scrutinee.clone(), ctor_branch],
            )
        }
        Some(Pattern::Literal(lit)) => {
            let lit_expr = lit_to_expr(lit);
            let fb = fallback
                .clone()
                .unwrap_or_else(|| Expr::const_str("sorryAx"));
            let cond = Expr::apps(Expr::const_str("BEq.beq"), [scrutinee.clone(), lit_expr]);
            build_ite(cond, body, fb)
        }
        // Catch-all: Var, Wildcard, Inaccessible, or residual Or/As.
        _ => body,
    }
}

/// Build `@ite _ cond (fun _ => then_) (fun _ => else_)`.
fn build_ite(cond: Expr, then_: Expr, else_: Expr) -> Expr {
    Expr::apps(
        Expr::const_str("ite"),
        [
            Expr::const_str("_"),
            cond,
            Expr::lam(BinderInfo::Default, Expr::const_str("_"), then_),
            Expr::lam(BinderInfo::Default, Expr::const_str("_"), else_),
        ],
    )
}

fn lit_to_expr(lit: &LitPattern) -> Expr {
    match lit {
        LitPattern::Nat(n) => Expr::nat_lit(*n),
        LitPattern::Int(n) => {
            if *n >= 0 {
                Expr::apps(Expr::const_str("Int.ofNat"), [Expr::nat_lit(*n as u64)])
            } else {
                Expr::apps(
                    Expr::const_str("Int.negSucc"),
                    [Expr::nat_lit((-n - 1) as u64)],
                )
            }
        }
        LitPattern::String(s) => Expr::str_lit(s),
        LitPattern::Char(c) => {
            Expr::apps(Expr::const_str("Char.ofNat"), [Expr::nat_lit(*c as u64)])
        }
    }
}

// ---------------------------------------------------------------------------
// Top-level entry point
// ---------------------------------------------------------------------------

/// Elaborate a match expression from high-level patterns to a kernel `Expr`.
///
/// This is the main entry point for extended pattern match compilation.
/// It validates patterns, checks depth limits, compiles to case expressions,
/// and optionally checks exhaustiveness/redundancy (emitting warnings).
pub(crate) fn elaborate_match(
    scrutinee: &Expr,
    arms: &[MatchArm],
    config: &MatchElabConfig,
) -> Result<MatchElabResult, ElabError> {
    // Validate all patterns.
    for arm in arms {
        for pat in &arm.patterns {
            check_pattern_well_formed(pat)?;
        }
    }

    // Check depth limit.
    for arm in arms {
        for pat in &arm.patterns {
            if pattern_depth(pat) > config.max_depth {
                return Err(ElabError::NotImplemented(format!(
                    "pattern depth {} exceeds maximum {}",
                    pattern_depth(pat),
                    config.max_depth
                )));
            }
        }
    }

    // Expand or-patterns to count final arms.
    let expanded: Vec<MatchArm> = arms.iter().flat_map(expand_or_patterns).collect();
    let arms_count = expanded.len();

    // Compile.
    let compiled = compile_patterns(scrutinee, arms);

    // Collect warnings.
    let mut warnings = Vec::new();

    if config.check_exhaustive {
        // Heuristic: if no wildcard or var pattern in any arm's first position,
        // and we have constructor patterns, warn about potential non-exhaustiveness.
        let has_catch_all = expanded.iter().any(|arm| {
            arm.patterns
                .first()
                .is_some_and(|p| matches!(p, Pattern::Var(_) | Pattern::Wildcard))
        });
        if !has_catch_all && !expanded.is_empty() {
            let all_ctor = expanded.iter().all(|arm| {
                arm.patterns
                    .first()
                    .is_some_and(|p| matches!(p, Pattern::Ctor { .. } | Pattern::Literal(_)))
            });
            if all_ctor {
                warnings.push(MatchWarning::NonExhaustive {
                    missing: vec![Pattern::Wildcard],
                });
            }
        }
    }

    if config.check_redundant {
        // Simple heuristic: if a catch-all arm is not the last, subsequent arms
        // are redundant.
        let mut seen_catch_all = false;
        for (i, arm) in expanded.iter().enumerate() {
            if seen_catch_all {
                warnings.push(MatchWarning::Redundant { arm_index: i });
            }
            if arm
                .patterns
                .first()
                .is_some_and(|p| matches!(p, Pattern::Var(_) | Pattern::Wildcard))
                && arm.guard.is_none()
            {
                seen_catch_all = true;
            }
        }
    }

    // Check for overlapping guards (heuristic: multiple guarded arms with same
    // first-position pattern shape).
    if config.check_redundant {
        let guarded_count = expanded.iter().filter(|a| a.guard.is_some()).count();
        if guarded_count >= 2 {
            warnings.push(MatchWarning::OverlappingGuards);
        }
    }

    Ok(MatchElabResult {
        compiled,
        warnings,
        arms_count,
    })
}
