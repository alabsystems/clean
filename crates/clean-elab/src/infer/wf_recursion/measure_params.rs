// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which PARAMETERS does a `termination_by` measure mention?
//!
//! This answers one question for [`super::super::elab_decl_value`]'s ROUTING
//! decision: the user wrote `termination_by <measure>`, and the structural
//! auto-detector independently guessed a decreasing argument. When the two
//! name different parameters, the DECLARATION wins and the definition is
//! routed to the well-founded lowering (the R3 rule).
//!
//! R3 implemented that rule for a measure spelled as a BARE parameter
//! identifier only (`termination_by b`). Measured at pin `99e2128ef`, any
//! other spelling — `termination_by b + 0`, `termination_by b.toNat`,
//! `termination_by xs.length` — fell through the `SurfaceExpr::Ident` match
//! arm, so the measure was never consulted, routing stayed structural, and the
//! self-call died `RecursionOutsideFragment`: the SAME failure R3 diagnosed and
//! fixed, surviving one spelling change. That is unfinished work, not a
//! soundness boundary, and this module finishes it.
//!
//! # Why this walker refuses to look inside binders
//!
//! A "which names occur free here" question is only well posed once shadowing
//! is accounted for: in `termination_by (fun b => b) b` the two `b`s are
//! different variables. Rather than carry a scope stack — and be silently
//! wrong the first time a variant is added to [`SurfaceExpr`] — this walker
//! descends ONLY through nodes that bind nothing, and returns [`None`] the
//! moment it meets anything else. With no binders on the path, a syntactic
//! occurrence IS a free occurrence, so the answer is exact rather than
//! approximate.
//!
//! [`None`] means "I cannot answer", and every caller must read it as
//! *leave routing exactly as it was* — which is the pre-existing behaviour for
//! every measure that is not a bare identifier. So the fragment boundary here
//! can only ADMIT shapes that were previously refused; it can never redirect
//! one that already worked. Widening the walker later (a scope-aware version
//! that handles `fun`/`let`/`match` measures) is a strictly additive change.
//!
//! **This is a routing decision and carries no proof authority.** It selects
//! which lowering is ATTEMPTED. The well-founded lowering then re-derives the
//! recursion parameter itself from the ELABORATED measure
//! (`elab_wf_recursion_core`'s phase 2b, which uses `contains_fvar` on real
//! `FVar`s and is immune to every spelling question above), requires the
//! measure to be `Nat`-valued, and discharges a genuine decreasing obligation
//! per call site or refuses. A wrong answer here costs a diagnostic, never a
//! verdict.

use clean_parser::SurfaceExpr;

/// The positions of the parameters mentioned by `measure`, ascending and
/// deduplicated.
///
/// Returns `None` when `measure` is not a plain binder-free expression — see
/// the module docs. `Some(vec![])` is a real answer ("mentions no parameter");
/// the well-founded lowering has its own, better-worded refusal for that case,
/// so routing leaves it alone.
pub(crate) fn mentioned_params(
    measure: &SurfaceExpr,
    param_names: &[String],
) -> Option<Vec<usize>> {
    let mut found = Vec::new();
    walk(measure, param_names, &mut found)?;
    found.sort_unstable();
    found.dedup();
    Some(found)
}

/// The position of the single parameter `measure` mentions, or `None` when it
/// mentions zero, several, or could not be analysed.
///
/// "Exactly one" is deliberately the same rule the well-founded lowering
/// applies to the elaborated measure in phase 2b, so routing and lowering agree
/// on what a one-parameter measure is instead of drifting apart.
pub(crate) fn sole_mentioned_param(measure: &SurfaceExpr, param_names: &[String]) -> Option<usize> {
    match mentioned_params(measure, param_names)?.as_slice() {
        [only] => Some(*only),
        _ => None,
    }
}

/// Descend through binder-free nodes, recording parameter occurrences.
///
/// `None` propagates: one unanalysable node anywhere makes the whole answer
/// unavailable, which is the fail-closed direction (routing is left untouched).
fn walk(expr: &SurfaceExpr, param_names: &[String], found: &mut Vec<usize>) -> Option<()> {
    match expr {
        SurfaceExpr::Ident(_, name) => {
            if let Some(pos) = param_names.iter().position(|p| p == name) {
                found.push(pos);
            }
            Some(())
        }

        // Inert leaves: no identifier, nothing to bind.
        SurfaceExpr::Lit(..) | SurfaceExpr::Hole(_) | SurfaceExpr::Universe(..) => Some(()),

        // Binder-free structural nodes.
        SurfaceExpr::App(_, f, args) => {
            walk(f, param_names, found)?;
            for arg in args {
                walk(&arg.expr, param_names, found)?;
            }
            Some(())
        }
        SurfaceExpr::Proj(_, e, _)
        | SurfaceExpr::Paren(_, e)
        | SurfaceExpr::Explicit(_, e)
        | SurfaceExpr::NamedArg(_, _, e)
        | SurfaceExpr::UniverseInst(_, e, _)
        | SurfaceExpr::OutParam(_, e)
        | SurfaceExpr::SemiOutParam(_, e) => walk(e, param_names, found),
        SurfaceExpr::Ascription(_, a, b) | SurfaceExpr::Arrow(_, a, b) => {
            walk(a, param_names, found)?;
            walk(b, param_names, found)
        }
        SurfaceExpr::If(_, c, t, e) => {
            walk(c, param_names, found)?;
            walk(t, param_names, found)?;
            walk(e, param_names, found)
        }

        // Everything else BINDS a name (`Lambda`, `Pi`, `Let`, `LetRec`,
        // `LetPattern`, `PatternMatchLambda`, `Match`, `IfLet`,
        // `IfDecidable`, `Do`, `OpenIn`, …) or is not a plain measure
        // expression (`ByTactic`, `CalcBlock`, quotations, `StructLit`,
        // interpolated strings, `SyntheticSorry`, …). Refuse to answer.
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_parser::parse_file;

    /// Parse `termination_by <measure>` off a one-declaration source and hand
    /// back the measure with the declaration's parameter names.
    fn measure_of(source: &str) -> (SurfaceExpr, Vec<String>) {
        let decls = parse_file(source).expect("fixture should parse");
        let clean_parser::SurfaceDecl::Def {
            binders,
            termination,
            ..
        } = &decls[0]
        else {
            panic!("fixture must be a `def`")
        };
        let measure = termination
            .termination_by
            .as_ref()
            .and_then(|tb| tb.measure.clone())
            .expect("fixture must carry a `termination_by` measure");
        (*measure, binders.iter().map(|b| b.name.clone()).collect())
    }

    fn sole(source: &str) -> Option<usize> {
        let (measure, params) = measure_of(source);
        sole_mentioned_param(&measure, &params)
    }

    const HEAD: &str = "def f (a b : Nat) : Nat := a\ntermination_by ";

    #[test]
    fn test_bare_identifier_names_its_parameter() {
        // The R3 case, unchanged: this is the shape that already routed.
        assert_eq!(sole(&format!("{HEAD}b")), Some(1));
        assert_eq!(sole(&format!("{HEAD}a")), Some(0));
    }

    #[test]
    fn test_compound_measure_over_one_parameter_is_resolved() {
        // The R5 case. `b + 0` is `App(HAdd.hAdd, [b, 0])`; before this module
        // it fell through the `Ident` arm and the measure was never consulted.
        assert_eq!(sole(&format!("{HEAD}b + 0")), Some(1));
        assert_eq!(sole(&format!("{HEAD}(b)")), Some(1));
        assert_eq!(sole(&format!("{HEAD}Nat.succ b")), Some(1));
    }

    #[test]
    fn test_projection_measure_is_resolved() {
        // `b.toNat` is `Proj(Ident(b), Named("toNat"))` — the shape the UInt64
        // carrier lane needs before it can even reach the decrease question.
        let (measure, params) =
            measure_of("def f (a b : UInt64) : Nat := 0\ntermination_by b.toNat");
        assert_eq!(sole_mentioned_param(&measure, &params), Some(1));
    }

    #[test]
    fn test_a_measure_over_two_parameters_has_no_sole_parameter() {
        // Must stay `None`: a lexicographic/packed measure is NOT lowered, and
        // routing must not claim one of the two parameters.
        assert_eq!(sole(&format!("{HEAD}b - a")), None);
        // …and it is a real answer naming BOTH, not a refusal to analyse.
        let (measure, params) = measure_of(&format!("{HEAD}b - a"));
        assert_eq!(mentioned_params(&measure, &params), Some(vec![0, 1]));
    }

    #[test]
    fn test_a_measure_mentioning_no_parameter_has_no_sole_parameter() {
        assert_eq!(sole(&format!("{HEAD}5")), None);
        assert_eq!(sole(&format!("{HEAD}Nat.zero")), None);
        // …and it is a real answer, not a refusal to analyse.
        let (measure, params) = measure_of(&format!("{HEAD}5"));
        assert_eq!(mentioned_params(&measure, &params), Some(vec![]));
    }

    #[test]
    fn test_a_binder_bearing_measure_refuses_to_answer() {
        // THE SHADOWING GUARD. `(fun b => b) b`'s inner `b` is a different
        // variable; rather than resolve it, the walker declines, and routing
        // is left exactly as it was.
        let (measure, params) = measure_of(&format!("{HEAD}(fun b => b) b"));
        assert_eq!(mentioned_params(&measure, &params), None);
        assert_eq!(sole_mentioned_param(&measure, &params), None);
    }

    #[test]
    fn test_a_repeated_parameter_is_counted_once() {
        assert_eq!(sole(&format!("{HEAD}b + b")), Some(1));
    }
}
