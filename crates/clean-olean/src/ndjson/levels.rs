// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What the kernel's level constructors may do to a level as written, and
//! which of their rewrites keep an export from being accepted (decision R125).
//!
//! The front door builds every level with the kernel's constructors, as the
//! `.olean` loader did when this was decided, so that a declaration read alike
//! through either front door (the native-fold digests are taken over
//! `.olean`-loaded terms). Since R150 the `.olean` loader builds a stored
//! level node for node instead (`import/convert_expr.rs`, `convert_level`);
//! the reader does that only where asked (`tables.rs`,
//! `LevelBuild::AsWritten`: the fenced-entry check and the writer's round
//! trip), and the front door has not been moved. Those
//! constructors simplify: `max u u` is built as `u`, `imax u (v+1)` as
//! `max u (v+1)`, `max 0 0` as `0`. Lean's kernel holds the level as
//! written and compares two levels by its own normalization
//! (`level.cpp` `is_equivalent`: equal, or equal after `normalize`), and reads
//! a few properties off the level as written (`is_zero`, `is_prop`, which
//! universe parameters it names). The reader marks every rewrite Lean could
//! tell from the level as written ([`LevelProblem`]), and every declaration
//! whose stored data mentions such a level ([`LevelTaint`]); an export with a
//! marked declaration is never accepted (`replay.rs`), while a refusal Clean
//! finds in it is still reported (a refusal is never an accept):
//!
//! - a `max`/`imax` record built as `zero` (an `il` record is never Lean's
//!   `zero`; read as `zero` it turns a sort into `Prop`, and drops any
//!   parameter written in it from the undeclared-parameter check);
//! - a rewrite of a level that mentions `imax`: Lean's `normalize` rewrites an
//!   `imax` into a `max` without flattening or sorting it, and does not push an
//!   outer `succ` through it, so it does not identify `succ (imax u (v+1))`
//!   with `max (u+1) (v+2)` though the constructors build one as the other
//!   (measured with the pinned kernel);
//! - and, as a safety net, a rewrite of an `imax`-free level whose normal form
//!   differs.
//!
//! An `imax`-free level is a `max` of parameters and numerals under `succ`s,
//! and Lean's `normalize` maps it to the set of its parameters at their
//! largest offsets, with the largest numeral unless some parameter's offset
//! reaches it ([`NormalForm`]). Two such levels with one normal form are
//! equivalent to Lean in every context it compares them in, instantiated or
//! not: instantiating a parameter shifts every argument it expands to by the
//! same offset, so the larger offset still wins and the numeral is still
//! subsumed. What the constructors do to them -- drop a duplicate, a zero, a
//! smaller offset of one parameter, a numeral some parameter reaches -- is
//! exactly that, so those rewrites are kept in definitions. In an inductive
//! block every rewrite marks the block (`records.rs`): Lean compares the
//! block's constructors and recursors structurally.
//!
//! Cost: the constructors normalize, and normalization is cubic in the
//! composite arguments (`imax`, or `succ` over `max`/`imax`) of a flattened
//! `max`. A `max`/`imax` record may give its `max` at most
//! [`MAX_LEVEL_COMPOSITE_ARGS`]; with the tree budget that bounds every
//! record's cost (review N5). A record's operands can still flatten to more
//! (a `succ` over a `max` is one counted argument and many normalized ones),
//! so the export's total estimated work is bounded too
//! ([`MAX_LEVEL_WORK`]). Those bounds decline at read time.

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

use clean_kernel::level::Level;
use clean_kernel::name::Name;

/// The most composite arguments (`imax`, or a `succ` of a `max`/`imax`) a
/// level record's flattened `max` may have. Lean's own levels have at most 2
/// (the Round 2026-09 archive, v4.30.0-rc2's `Init.Prelude`); a constructor
/// call costs about `10·k³` hash visits in them, and a debug build took over
/// 100 s for 20,000 records at 16.
pub(crate) const MAX_LEVEL_COMPOSITE_ARGS: u64 = 8;

/// The most level-normalization work one export's level records may cost, in
/// the reader's estimate ([`level_record_work`]: a normalizing record costs
/// its tree size times `(c + 1)³`, `c` the `imax` nodes in its operands' trees,
/// an upper bound on the kernel's subsumption passes, which are cubic in the
/// composite arguments a normalization flattens, `succ`-wrapped and nested ones
/// included). Lean's own exports cost little: v4.30.0-rc2's and 4.29.1's whole
/// `Init.Prelude` about 2,000; 10,000 records at the 8-argument cap about
/// 2.4e8. A record built over the budget declines the export
/// (`level-work-budget`), so a 290 KB export whose records each cost tens of
/// millions of steps (review round 3) stops after about ten of them.
pub(crate) const MAX_LEVEL_WORK: u64 = 500_000_000;

/// One `max`/`imax` record's work estimate. The constructors normalize only
/// for a `max`, or an `imax` whose right operand is surely not zero (which they
/// build as a `max`): then its tree size times `(c + 1)³`, `c` the `imax`
/// nodes in its operands (every composite argument a normalization can
/// flatten has one at its base); otherwise they compare and rebuild, linear in
/// the size.
pub(crate) fn level_record_work(size: u64, imax_nodes: u64, normalizes: bool) -> u64 {
    if !normalizes {
        return size;
    }
    let c = imax_nodes.saturating_add(1);
    size.saturating_mul(c.saturating_mul(c).saturating_mul(c))
}

/// Whether `level` is surely not zero, as the kernel's `Level::imax` asks
/// before it builds an `imax` as a `max` (structural: a `succ`, a `max` with
/// such an operand, an `imax` with such a right operand).
pub(crate) fn surely_nonzero(level: &Level) -> bool {
    match level {
        Level::Succ(_) => true,
        Level::Max(a, b) => surely_nonzero(a) || surely_nonzero(b),
        Level::IMax(_, b) => surely_nonzero(b),
        Level::Zero | Level::Param(_) => false,
    }
}

/// An `imax`-free level as Lean's `normalize` reads it: each parameter at its
/// largest offset, and the largest numeral.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NormalForm {
    params: BTreeMap<Name, u64>,
    numeral: Option<u64>,
}

impl NormalForm {
    fn zero() -> Self {
        Self {
            params: BTreeMap::new(),
            numeral: Some(0),
        }
    }

    fn param(name: &Name) -> Self {
        Self {
            params: BTreeMap::from([(name.clone(), 0)]),
            numeral: None,
        }
    }

    fn succ(&self) -> Self {
        Self {
            params: self
                .params
                .iter()
                .map(|(p, k)| (p.clone(), k.saturating_add(1)))
                .collect(),
            numeral: self.numeral.map(|k| k.saturating_add(1)),
        }
    }

    fn max(&self, other: &Self) -> Self {
        let mut params = self.params.clone();
        for (p, k) in &other.params {
            let at = params.entry(p.clone()).or_insert(*k);
            *at = (*at).max(*k);
        }
        let numeral = match (self.numeral, other.numeral) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (a, b) => a.or(b),
        };
        Self { params, numeral }
    }

    /// The form `normalize` returns: the numeral is dropped when some
    /// parameter's offset reaches it (`level.cpp`: "an explicit universe k is
    /// subsumed by succ^k(l)").
    fn normalized(&self) -> (&BTreeMap<Name, u64>, Option<u64>) {
        let reached = |k: u64| self.params.values().any(|&o| o >= k);
        (
            &self.params,
            self.numeral
                .filter(|&k| self.params.is_empty() || !reached(k)),
        )
    }

    fn equivalent(&self, other: &Self) -> bool {
        self.normalized() == other.normalized()
    }
}

/// A level as written, as far as the decline rules read it.
#[derive(Clone, Debug)]
pub(crate) enum Written {
    /// It mentions `imax`.
    Imax,
    /// It does not: its normal form.
    Form(Arc<NormalForm>),
}

impl Written {
    pub(crate) fn zero() -> Self {
        Written::Form(Arc::new(NormalForm::zero()))
    }

    pub(crate) fn param(name: &Name) -> Self {
        Written::Form(Arc::new(NormalForm::param(name)))
    }

    pub(crate) fn succ(&self) -> Self {
        match self {
            Written::Imax => Written::Imax,
            Written::Form(f) => Written::Form(Arc::new(f.succ())),
        }
    }

    pub(crate) fn max(&self, other: &Self) -> Self {
        match (self, other) {
            (Written::Form(a), Written::Form(b)) => Written::Form(Arc::new(a.max(b))),
            _ => Written::Imax,
        }
    }
}

/// `level`'s normal form, or `None` when it has an `imax`.
fn built_form(level: &Level) -> Option<NormalForm> {
    Some(match level {
        Level::Zero => NormalForm::zero(),
        Level::Param(name) => NormalForm::param(name),
        Level::Succ(inner) => built_form(inner)?.succ(),
        Level::Max(a, b) => built_form(a)?.max(&built_form(b)?),
        Level::IMax(..) => return None,
    })
}

/// Why Lean could tell a level written as `written` from the one the
/// constructors built, or `None` when it cannot.
pub(crate) fn rewrite_problem(written: &Written, built: &Level) -> Option<&'static str> {
    match written {
        Written::Imax => Some(
            "the level mentions `imax`, and Lean's normalization does not identify an `imax` \
             with the `max` the kernel's constructors rewrite it to in every context",
        ),
        Written::Form(form) => match built_form(built) {
            Some(built) if built.equivalent(form) => None,
            _ => Some("the built level's normal form is not the written one's"),
        },
    }
}

/// A level record Lean could tell from the level the constructors built.
#[derive(Clone, Debug)]
pub(crate) enum LevelProblem {
    /// A `max`/`imax` record built as `zero`.
    ToZero {
        /// The level index.
        index: u64,
        /// `Level.max` or `Level.imax`.
        record: &'static str,
    },
    /// A rewrite Lean's normalization does not make.
    LeanVisible {
        /// The level index.
        index: u64,
        /// The record as written (its kind and operand indices).
        written: String,
        /// The level as built.
        built: String,
        /// Why Lean may tell the two apart.
        why: &'static str,
    },
}

impl LevelProblem {
    /// A stable name for the rule, for reports and tests.
    pub(crate) fn rule(&self) -> &'static str {
        match self {
            LevelProblem::ToZero { .. } => "level-rewritten-to-zero",
            LevelProblem::LeanVisible { .. } => "level-rewrite-lean-visible",
        }
    }
}

impl fmt::Display for LevelProblem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LevelProblem::ToZero { index, record } => write!(
                f,
                "level {index} ({record}) is not `zero` as written, but the kernel's level \
                 constructors build it as `zero`; Lean reads it as written (no proposition's \
                 sort, naming every parameter written in it)"
            ),
            LevelProblem::LeanVisible {
                index,
                written,
                built,
                why,
            } => write!(
                f,
                "level {index} is written as {written} and built as {built}; {why}"
            ),
        }
    }
}

/// Why a declaration's stored data keeps the export from being accepted.
#[derive(Clone, Debug)]
pub(crate) struct LevelTaint {
    /// The declaration (a block member), rendered unambiguously as written.
    pub(crate) member: String,
    /// Which of its expressions: `type`, `value`, `inductive type's type`,
    /// `constructor type`, `recursor type` or `recursor rule's right-hand
    /// side`.
    pub(crate) path: &'static str,
    /// A level Lean could tell from the built one, or `None` for a block over
    /// a rewritten level.
    pub(crate) problem: Option<LevelProblem>,
}

impl LevelTaint {
    /// A stable name for the rule, for reports and tests.
    pub(crate) fn rule(&self) -> &'static str {
        self.problem
            .as_ref()
            .map_or("level-rewritten-in-block", LevelProblem::rule)
    }
}

impl fmt::Display for LevelTaint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            member,
            path,
            problem,
        } = self;
        match problem {
            Some(problem) => write!(
                f,
                "the {path} of `{member}` mentions a level Lean reads otherwise: {problem}"
            )?,
            None => write!(
                f,
                "the {path} of `{member}` mentions a level the kernel's constructors built \
                 otherwise than written; Lean compares an inductive block's constructors and \
                 recursors with the ones it generates from the block as written"
            )?,
        }
        write!(f, " [{}]", self.rule())
    }
}

/// The composite arguments of `level`'s flattened top-level `max`.
pub(crate) fn composite_args(level: &Level) -> u64 {
    match level {
        Level::Max(a, b) => composite_args(a).saturating_add(composite_args(b)),
        other => {
            let mut base = other;
            while let Level::Succ(inner) = base {
                base = &**inner;
            }
            u64::from(matches!(base, Level::Max(..) | Level::IMax(..)))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(name: &str) -> Level {
        Level::param(Name::from_string(name))
    }

    fn written_of(f: impl Fn(&Written, &Written) -> Written) -> Written {
        f(
            &Written::param(&Name::from_string("u")),
            &Written::param(&Name::from_string("v")),
        )
    }

    #[test]
    fn test_levels_numeral_reached_by_a_parameter_is_subsumed() {
        // `max 1 (u+1)` is written; `u+1` is built: one normal form.
        let written = Written::zero()
            .succ()
            .max(&Written::param(&Name::from_string("u")).succ());
        assert_eq!(rewrite_problem(&written, &Level::succ(p("u"))), None);
        // `max 2 (u+1)` is not `u+1`.
        let written = Written::zero()
            .succ()
            .succ()
            .max(&Written::param(&Name::from_string("u")).succ());
        assert!(rewrite_problem(&written, &Level::succ(p("u"))).is_some());
    }

    #[test]
    fn test_levels_duplicates_and_offsets_share_a_normal_form() {
        let written = written_of(|u, v| u.max(&u.max(v)));
        let built = Level::max(p("u"), p("v"));
        assert_eq!(rewrite_problem(&written, &built), None);
        let written = written_of(|u, _| u.succ().max(u));
        assert_eq!(rewrite_problem(&written, &Level::succ(p("u"))), None);
        // A different parameter set is a different level.
        let written = written_of(|u, v| u.max(v));
        assert!(rewrite_problem(&written, &p("u")).is_some());
    }

    #[test]
    fn test_levels_any_imax_is_lean_visible() {
        assert!(rewrite_problem(&Written::Imax, &Level::max(p("u"), p("v"))).is_some());
        assert!(
            rewrite_problem(&written_of(|u, _| u.clone()), &Level::imax(p("u"), p("v"))).is_some()
        );
    }

    #[test]
    fn test_levels_work_is_charged_only_where_the_constructors_normalize() {
        assert_eq!(level_record_work(10, 3, false), 10);
        assert_eq!(level_record_work(10, 3, true), 640);
        assert!(surely_nonzero(&Level::succ(p("u"))));
        assert!(surely_nonzero(&Level::max(p("u"), Level::succ(p("v")))));
        assert!(!surely_nonzero(&Level::imax(p("u"), p("v"))));
        assert!(!surely_nonzero(&p("u")));
    }

    #[test]
    fn test_levels_composite_arguments_are_counted_on_the_top_max() {
        let spine = Level::max(
            Level::imax(p("a"), p("b")),
            Level::max(p("c"), Level::succ(Level::imax(p("d"), p("e")))),
        );
        assert_eq!(composite_args(&spine), 2);
        assert_eq!(composite_args(&p("c")), 0);
    }
}
