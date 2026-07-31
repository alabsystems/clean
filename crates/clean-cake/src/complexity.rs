// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Within-node complexity + best-proof selection.
//!
//! A fact-node holds multiple *lineage items* (derivations of the same fact —
//! "how you combine the deps is different theory"). This module ranks them.
//!
//! - [`ProofComplexity`] — a derivation's **within-node** cost: proof-term size + depth +
//!   distinct lemmas in its closure. Least-complex is the canonical derivation of a fact.
//! - [`better`] / [`best`] — the **best-proof** order over `(goodness, complexity)`:
//!   lexicographic by soundness **floor** (bedrock ceiling beats axiom-/sorry-tainted),
//!   then goodness **`g_mass`** (richer/cleaner derivation), then **least complexity**
//!   (compactness tie-break). This makes the canonical proof "the least-complex among the
//!   soundest", and keeps the corpus compact: one canonical proof per fact, the rest
//!   retained out of line at their bottleneck (see the design doc §6).

use clean_kernel::expr::ExprKind;
use clean_kernel::{Environment, Expr, Name};

use crate::goodness::{closure_goodness, Goodness};

/// A derivation's within-node complexity. Lower is simpler (and preferred).
///
/// `term_size`/`term_depth` are a **structural-size heuristic over the core
/// lambda-calculus fragment** (App/Lam/Pi/Let/Proj/MData) used only as the lexicographic
/// **tie-break** in [`better`] (after floor and `g_mass`); they do not descend the non-core
/// `Squash`/`Cubical*`/`ZFC*` variants, so they may under-count a proof that uses those
/// modes (which do not occur in the targeted Mathlib corpus). `distinct_lemmas` is exact —
/// it reuses [`Goodness::closure_size`], which walks the kernel's exhaustive
/// `collect_constants`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProofComplexity {
    /// Heuristic node count of the proof term over the core fragment. `0` for an axiom.
    pub term_size: usize,
    /// Heuristic maximum nesting depth over the core fragment. `0` for an axiom.
    pub term_depth: usize,
    /// Distinct constants in the dependency closure (exact; = [`Goodness::closure_size`]).
    pub distinct_lemmas: usize,
}

/// Node count and maximum nesting depth in a single iterative pass (deep terms
/// must not overflow the stack). Fused from the former separate `term_size` /
/// `term_depth` walks: it visits the identical node set and returns the same
/// `(size, depth)` pair, so every downstream score is byte-identical.
fn term_size_depth(e: &Expr) -> (usize, usize) {
    let mut n = 0usize;
    let mut max = 0usize;
    let mut stack: Vec<(&Expr, usize)> = vec![(e, 1)];
    while let Some((cur, d)) = stack.pop() {
        n += 1;
        if d > max {
            max = d;
        }
        match cur.kind() {
            ExprKind::App(f, a) => {
                stack.push((f, d + 1));
                stack.push((a, d + 1));
            }
            ExprKind::Lam(_, ty, b) | ExprKind::Pi(_, ty, b) => {
                stack.push((ty, d + 1));
                stack.push((b, d + 1));
            }
            ExprKind::Let(_, ty, v, b, _) => {
                stack.push((ty, d + 1));
                stack.push((v, d + 1));
                stack.push((b, d + 1));
            }
            ExprKind::Proj(_, _, s) => stack.push((s, d + 1)),
            ExprKind::MData(_, inner) => stack.push((inner, d + 1)),
            _ => {}
        }
    }
    (n, max)
}

/// Compute the [`ProofComplexity`] of `name`'s derivation in `env`. `None` if absent.
#[must_use]
pub fn proof_complexity(env: &Environment, name: &Name) -> Option<ProofComplexity> {
    let info = env.get_const(name)?;
    let (term_size, term_depth) = match info.value.as_ref() {
        Some(v) => term_size_depth(v),
        None => (0, 0),
    };
    let distinct_lemmas = closure_goodness(env, name)
        .map(|g| g.closure_size)
        .unwrap_or(0);
    Some(ProofComplexity {
        term_size,
        term_depth,
        distinct_lemmas,
    })
}

/// One lineage item's combined score: cross-node goodness + within-node complexity.
// Best-proof selection awaiting its pipeline caller; kept alive by tests.
// The expects fire when a caller lands.
#[cfg_attr(not(test), expect(dead_code))]
#[derive(Debug, Clone)]
pub(crate) struct ProofRecord {
    /// Cross-node goodness (`G` mass + `F` floor) of the derivation's closure.
    pub goodness: Goodness,
    /// Within-node complexity of the derivation.
    pub complexity: ProofComplexity,
}

/// The best-proof order: returns `Greater` when `a` is the *better* proof. Lexicographic:
/// 1. soundness **floor** (higher = better: `Foundational` > `AxiomDependent` > `Unsound`),
/// 2. goodness **`g_mass`** (higher = better),
/// 3. **complexity** (lower `term_size`, then `term_depth`, then `distinct_lemmas` = better).
#[cfg_attr(not(test), expect(dead_code))]
#[must_use]
pub(crate) fn better(a: &ProofRecord, b: &ProofRecord) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    a.goodness
        .floor
        .cmp(&b.goodness.floor)
        .then_with(|| {
            a.goodness
                .g_mass
                .partial_cmp(&b.goodness.g_mass)
                .unwrap_or(Ordering::Equal)
        })
        // lower complexity is better ⇒ reverse the comparison
        .then_with(|| b.complexity.term_size.cmp(&a.complexity.term_size))
        .then_with(|| b.complexity.term_depth.cmp(&a.complexity.term_depth))
        .then_with(|| {
            b.complexity
                .distinct_lemmas
                .cmp(&a.complexity.distinct_lemmas)
        })
}

/// The canonical (best) proof among lineage items of one fact, or `None` if empty.
#[cfg_attr(not(test), expect(dead_code))]
#[must_use]
pub(crate) fn best(candidates: &[ProofRecord]) -> Option<&ProofRecord> {
    candidates.iter().max_by(|a, b| better(a, b))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::goodness::FloorLevel;
    use clean_kernel::{Declaration, Level};

    fn name(s: &str) -> Name {
        Name::from_string(s)
    }

    fn rec(floor: FloorLevel, g_mass: f64, size: usize) -> ProofRecord {
        ProofRecord {
            goodness: Goodness {
                g_mass,
                floor,
                closure_size: size,
                domain_axioms: vec![],
                trust_markers: vec![],
            },
            complexity: ProofComplexity {
                term_size: size,
                term_depth: 1,
                distinct_lemmas: size,
            },
        }
    }

    #[test]
    fn test_floor_dominates_goodness_and_complexity() {
        // A sound-but-bigger proof beats an unsound-but-tiny one: floor first.
        let sound_big = rec(FloorLevel::Foundational, 1.0, 1000);
        let unsound_tiny = rec(FloorLevel::Unsound, 999.0, 1);
        assert_eq!(
            better(&sound_big, &unsound_tiny),
            std::cmp::Ordering::Greater
        );
        assert_eq!(
            best(&[unsound_tiny, sound_big]).unwrap().goodness.floor,
            FloorLevel::Foundational
        );
    }

    #[test]
    fn test_least_complex_wins_at_equal_floor_and_goodness() {
        let simple = rec(FloorLevel::Foundational, 5.0, 10);
        let complex = rec(FloorLevel::Foundational, 5.0, 99);
        assert_eq!(better(&simple, &complex), std::cmp::Ordering::Greater);
        let chosen = best(std::slice::from_ref(&simple)); // single
        assert!(chosen.is_some());
        // among both, the simpler (smaller closure/term) is canonical
        let pool = vec![complex.clone(), simple.clone()];
        assert_eq!(best(&pool).unwrap().complexity.term_size, 10);
    }

    #[test]
    fn test_higher_goodness_wins_at_equal_floor() {
        let richer = rec(FloorLevel::Foundational, 10.0, 50);
        let leaner = rec(FloorLevel::Foundational, 2.0, 50);
        assert_eq!(better(&richer, &leaner), std::cmp::Ordering::Greater);
    }

    #[test]
    fn test_proof_complexity_counts_term_and_axiom_is_zero() {
        let mut env = Environment::default();
        // An axiom has no proof term → size/depth 0, but closure_size ≥ 1 (itself).
        env.add_decl(Declaration::Axiom {
            name: name("Ax"),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        })
        .expect("add Ax");
        let c = proof_complexity(&env, &name("Ax")).expect("present");
        assert_eq!(c.term_size, 0, "axiom has no proof term");
        assert!(c.distinct_lemmas >= 1, "closure includes itself");
        assert!(proof_complexity(&env, &name("Missing")).is_none());
    }
}
