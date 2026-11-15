// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The vendored parser refuses a bit-vector whose result width it cannot
//! represent (`third-party/carcara/DOWNSTREAM.md`, "Also hardened").
//!
//! Widths are `usize`, and `TermPool::compute_sort` adds and multiplies them
//! unchecked; it cannot return an error. Measured on pinned Carcara 9a352ee
//! (release build): `((_ sign_extend 18446744073709551615) #b11)`, the same
//! `zero_extend`, and `(concat (_ bv0 18446744073709551615) #b11)` each
//! sort-checked as `(_ BitVec 1)`, and `((_ repeat 9223372036854775809) #b11)`
//! panicked. The parser now checks every width it computes before the pool
//! sees the term, under every configuration.

use carcara::{
    ast::{
        pool::{PrimitivePool, TermPool},
        Rc, Sort, Term,
    },
    parser::{Config, Parser},
    CarcaraResult,
};
use std::panic::{catch_unwind, AssertUnwindSafe};

/// `(term, sort)` of `input` after `declarations`, or the parse error; a panic
/// is returned as the outer `Err`.
fn parse(
    declarations: &str,
    input: &str,
    config: Config,
) -> std::thread::Result<CarcaraResult<(Rc<Term>, Rc<Sort>)>> {
    catch_unwind(AssertUnwindSafe(|| {
        let mut pool = PrimitivePool::new();
        let term = {
            let mut parser = Parser::new(&mut pool, config, declarations)?;
            parser.parse_problem()?;
            parser.reset(input)?;
            parser.parse_term()?
        };
        let sort = pool.sort(&term);
        Ok((term, sort))
    }))
}

fn configs() -> [Config; 2] {
    [Config::new(), Config::clean_dialect()]
}

/// A bit-vector whose width is only known symbolically: `Sort::ParamBitVec`.
const PARAMETRIC: &str = "(declare-const n Int)(declare-const y (_ BitVec n))";

#[test]
fn result_widths_that_do_not_fit_are_parse_errors() {
    let max = usize::MAX;
    // `2 * (max / 2 + 2)` exceeds `max` by 2.
    let half = max / 2 + 2;
    let overflowing = [
        ("", format!("(concat (_ bv0 {max}) #b11)")),
        ("", format!("((_ sign_extend {max}) #b11)")),
        ("", format!("((_ zero_extend {max}) #b11)")),
        ("", format!("((_ repeat {half}) #b11)")),
        // `extract` computes `i - j + 1`; with `i < j` that underflows, and
        // with `i = max, j = 0` it overflows, when the operand's width is not
        // known to refuse it first.
        (PARAMETRIC, "((_ extract 0 1) y)".to_owned()),
        (PARAMETRIC, format!("((_ extract {max} 0) y)")),
    ];
    for config in configs() {
        for (declarations, input) in &overflowing {
            match parse(declarations, input, config) {
                Ok(Err(_)) => {}
                Ok(Ok((_, sort))) => {
                    panic!("{input} under {config:?} was accepted with sort {sort}")
                }
                Err(_) => panic!("{input} under {config:?} panicked the parser"),
            }
        }
    }
}

#[test]
fn wide_result_widths_that_fit_keep_their_exact_width() {
    let wide = [1usize << 32, (1usize << 33) + 1];
    for config in configs() {
        for k in wide {
            for (input, width) in [
                (format!("(concat (_ bv0 {k}) #b11)"), k + 2),
                (format!("((_ sign_extend {k}) #b11)"), k + 2),
                (format!("((_ zero_extend {k}) #b11)"), k + 2),
                (format!("((_ repeat {k}) #b1)"), k),
            ] {
                let parsed = parse("", &input, config);
                let Ok(Ok((_, sort))) = parsed else {
                    panic!("{input} under {config:?} did not parse");
                };
                assert_eq!(*sort, Sort::BitVec(width), "{input} under {config:?}");
            }
        }
        let parsed = parse(PARAMETRIC, "((_ extract 1 1) y)", config);
        let Ok(Ok((_, sort))) = parsed else {
            panic!("an extract with i >= j over a parametric width did not parse");
        };
        assert_eq!(*sort, Sort::BitVec(1));
    }
}
