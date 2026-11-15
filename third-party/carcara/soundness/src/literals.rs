// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! An audit of how Carcara's parser reads `(_ bv<n> <w>)` literals.
//!
//! The battery's evaluator judges the terms Carcara's parser produced, so it cannot see a literal
//! the parser already read wrongly: `(_ bv5 4294967298)` parsed as the term `(_ bv1 4294967298)`
//! makes `refl` prove `(= (_ bv5 4294967298) (_ bv1 4294967298))`, and to the evaluator both sides
//! are the same value. This audit compares the parsed literal with `n mod 2^w`, computed here from
//! the numerals as written, and reports a mismatch as an unsound acceptance of the pseudo-rule
//! `parser:bv_literal` — every rule reads that term.

use crate::oracle::{Cex, Instance};
use crate::run::{Example, RuleStats};
use carcara::ast::{Constant, Operator, Term};
use carcara::parser;
use rug::Integer;

pub const RULE: &str = "parser:bv_literal";

/// `n mod 2^w`: `n` itself when it is below `2^w`, otherwise a remainder by a power of two no wider
/// than `n`.
fn expected(n: &Integer, w: u64) -> Integer {
    if u64::from(n.significant_bits()) <= w {
        n.clone()
    } else {
        let m = Integer::from(1) << u32::try_from(w).expect("w is below n's bit count");
        n.clone() % m
    }
}

fn parse_literal(n: &Integer, w: u64) -> Result<(Integer, u64), String> {
    let problem = format!(
        "(declare-const c (_ BitVec {w}))\n(assert (= c (_ bv{n} {w})))\n",
        n = n,
        w = w
    );
    let (problem, _, _, _) =
        parser::parse_instance(problem.as_str(), "", None, parser::Config::new())
            .map_err(|e| format!("parse error: {}", e))?;
    let t = problem.premises.iter().next().ok_or("no premise")?;
    match t.as_ref() {
        Term::Op(Operator::Equals, args) if args.len() == 2 => match args[1].as_ref() {
            Term::Const(Constant::BitVec(v, width)) => Ok((v.clone(), *width as u64)),
            other => Err(format!("literal parsed as {}", other)),
        },
        other => Err(format!("premise parsed as {}", other)),
    }
}

pub fn audit(max_examples: usize) -> RuleStats {
    let widths: [u64; 17] = [
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
        (1 << 32) + 2,
        (1 << 32) + 5,
        (1 << 33) + 1,
        (1 << 40) + 3,
    ];
    let numerals: Vec<Integer> = vec![
        Integer::from(0),
        Integer::from(1),
        Integer::from(2),
        Integer::from(5),
        Integer::from(7),
        Integer::from(255),
        (Integer::from(1) << 32) + 5,
        (Integer::from(1) << 64) + 9,
        Integer::from(3) * (Integer::from(1) << 40) + 17,
        (Integer::from(1) << 100) - 1,
    ];
    let mut stats = RuleStats::default();
    for &w in &widths {
        for n in &numerals {
            let want = expected(n, w);
            // A literal the parser refuses (it bounds the numeral) is not read at all, so it
            // cannot be read wrongly
            let Ok((v, width)) = parse_literal(n, w) else {
                continue;
            };
            stats.accepted += 1;
            stats.exercised += 1;
            let wrong = (v != want || width != w).then(|| {
                format!(
                    "parsed as (_ bv{} {}), but it denotes (_ bv{} {})",
                    v, width, want, w
                )
            });
            if let Some(why) = wrong {
                stats.counterexamples += 1;
                if stats.examples.len() < max_examples {
                    stats.examples.push(Example {
                        source: "literals::audit".to_owned(),
                        instance: Instance {
                            defs: String::new(),
                            proof: format!("(_ bv{} {})", n, w),
                        },
                        cex: Cex {
                            step: "literal".to_owned(),
                            rule: RULE.to_owned(),
                            global: false,
                            model: why,
                        },
                    });
                }
            }
        }
    }
    stats
}

#[cfg(test)]
mod tests {
    #[test]
    fn literals_denote_n_mod_2_to_the_w() {
        let stats = super::audit(5);
        assert!(stats.accepted >= 130, "{} literals parsed", stats.accepted);
        assert_eq!(stats.counterexamples, 0, "{:?}", stats.examples);
    }
}
