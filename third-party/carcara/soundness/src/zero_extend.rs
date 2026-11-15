// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! An audit of how Carcara's parser reads `zero_extend` under Clean's Alethe dialect
//! (`Config::clean_dialect()`, third-party/carcara/DOWNSTREAM.md § Dialect).
//!
//! The dialect builds `((_ zero_extend k) t)` as its SMT-LIB definition while it parses: `t` for
//! `k = 0`, otherwise `(concat Z t)` with `Z` the all-zero constant of width `k`. Every rule then
//! sees only the definition, so a wrong reading is invisible to rule checking and to the battery's
//! evaluator, which judge the parsed terms: the refutation would simply be about another problem.
//! This audit compares the parsed term with the definition built here from the numerals as
//! written, and evaluates it on closed operands, over the width class where a `u32` cast of a width
//! would hide (fix 35). A mismatch is reported as an unsound acceptance of the pseudo-rule
//! `parser:zero_extend`, since every rule reads that term.

use crate::eval::Evaluator;
use crate::model::{Model, Vocab};
use crate::oracle::{Cex, Instance};
use crate::run::{Example, RuleStats};
use crate::value::{Env, V};
use carcara::ast::pool::{PrimitivePool, TermPool};
use carcara::ast::{Constant, Operator, Rc, Sort, Term};
use carcara::parser;
use rug::Integer;
use std::rc::Rc as StdRc;

pub const RULE: &str = "parser:zero_extend";

/// Operand widths: the literal audit's, the `2^32` class among them.
const WIDTHS: [usize; 15] = [
    1,
    2,
    3,
    8,
    31,
    32,
    33,
    63,
    64,
    65,
    (1 << 32) - 1,
    1 << 32,
    (1 << 32) + 1,
    (1 << 33) + 1,
    (1 << 40) + 3,
];

/// Extension amounts.
const EXTRAS: [usize; 9] = [0, 1, 7, 8, 24, 52, 64, 1 << 32, (1 << 33) + 1];

/// The right side of `(assert (= c <operand extended by k>))`, parsed under the dialect, and the
/// pool it lives in.
fn parse_extension(w: usize, k: usize, operand: &str) -> Result<(Rc<Term>, PrimitivePool), String> {
    let problem = format!(
        "(declare-const d (_ BitVec {w}))\n(declare-const c (_ BitVec {wk}))\n\
         (assert (= c ((_ zero_extend {k}) {operand})))\n",
        wk = w + k,
    );
    let (problem, _, _, pool) =
        parser::parse_instance(&problem, "", None, parser::Config::clean_dialect())
            .map_err(|e| format!("parse error: {}", e))?;
    let premise = problem.premises.iter().next().ok_or("no premise")?;
    match premise.as_ref() {
        Term::Op(Operator::Equals, args) if args.len() == 2 => Ok((args[1].clone(), pool)),
        other => Err(format!("premise parsed as {}", other)),
    }
}

/// Why the parsed `((_ zero_extend k) d)` is not its definition, built here from `w` and `k`.
fn structural_mismatch(w: usize, k: usize) -> Option<String> {
    let (parsed, mut pool) = match parse_extension(w, k, "d") {
        Ok(parsed) => parsed,
        Err(why) => return Some(why),
    };
    let sort = pool.add_sort(Sort::BitVec(w));
    let d = pool.add(Term::new_var("d", sort));
    let definition = if k == 0 {
        d
    } else {
        let zero = pool.add(Term::Const(Constant::BitVec(Integer::new(), k)));
        pool.add(Term::Op(Operator::BvConcat, vec![zero, d]))
    };
    if parsed != definition {
        return Some(format!("parsed as {}, but it is {}", parsed, definition));
    }
    let width = pool.sort(&parsed);
    (*width != Sort::BitVec(w + k)).then(|| format!("sort {}, not (_ BitVec {})", width, w + k))
}

/// What the audit concluded about one reading.
enum Verdict {
    /// The reading is the definition.
    Right,
    /// The reading is not the definition, and why.
    Wrong(String),
    /// The evaluator could not judge the reading (it reached a value it does not model). Such a
    /// reading is counted as accepted and not exercised, the battery's meaning for a step no model
    /// judged, and `zero_extend_is_parsed_as_its_definition` (tests/battery.rs) requires that
    /// there are none.
    Unjudged,
}

impl From<Option<String>> for Verdict {
    fn from(why: Option<String>) -> Self {
        why.map_or(Verdict::Right, Verdict::Wrong)
    }
}

/// Whether the parsed `((_ zero_extend k) (_ bvN w))` evaluates to `N` at width `w + k`.
fn semantic_verdict(w: usize, k: usize, n: u32) -> Verdict {
    let (parsed, mut pool) = match parse_extension(w, k, &format!("(_ bv{} {})", n, w)) {
        Ok(parsed) => parsed,
        Err(why) => return Verdict::Wrong(why),
    };
    let mut model = Model::new(0, StdRc::new(Vocab::default()));
    let mut evaluator = Evaluator::new(&mut model, &mut pool, 1_000_000);
    match evaluator.eval(&parsed, &Env::new()) {
        Ok(V::Bv(value, width)) if value == n && width == w + k => Verdict::Right,
        Ok(V::Bv(value, width)) => Verdict::Wrong(format!(
            "evaluates to (_ bv{} {}), not (_ bv{} {})",
            value,
            width,
            n,
            w + k
        )),
        Ok(other) => Verdict::Wrong(format!("evaluates to the non-bit-vector {:?}", other)),
        Err(_) => Verdict::Unjudged,
    }
}

pub fn audit(max_examples: usize) -> RuleStats {
    let mut stats = RuleStats::default();
    let report = |stats: &mut RuleStats, case: String, verdict: Verdict| {
        stats.accepted += 1;
        let why = match verdict {
            Verdict::Unjudged => return,
            Verdict::Right => {
                stats.exercised += 1;
                return;
            }
            Verdict::Wrong(why) => why,
        };
        stats.exercised += 1;
        stats.counterexamples += 1;
        if stats.examples.len() < max_examples {
            stats.examples.push(Example {
                source: "zero_extend::audit".to_owned(),
                instance: Instance { defs: String::new(), proof: case },
                cex: Cex {
                    step: "zero_extend".to_owned(),
                    rule: RULE.to_owned(),
                    global: false,
                    model: why,
                },
            });
        }
    };
    for &w in &WIDTHS {
        for &k in &EXTRAS {
            let case = format!("((_ zero_extend {}) d) with d : (_ BitVec {})", k, w);
            report(&mut stats, case, structural_mismatch(w, k).into());
            for n in [0u32, 1, 5] {
                if u64::from(32 - n.leading_zeros()) > w as u64 {
                    continue;
                }
                let case = format!("((_ zero_extend {}) (_ bv{} {}))", k, n, w);
                report(&mut stats, case, semantic_verdict(w, k, n));
            }
        }
    }
    stats
}
