// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[path = "tests_core.rs"]
mod tests_core;
#[path = "tests_deductions.rs"]
mod tests_deductions;
#[path = "tests_performance.rs"]
mod tests_performance;
#[path = "tests_rational.rs"]
mod tests_rational;
#[path = "tests_reset.rs"]
mod tests_reset;
#[path = "tests_simplex_audit.rs"]
mod tests_simplex_audit;
#[path = "tests_simplex_core.rs"]
mod tests_simplex_core;
#[path = "tests_simplex_rational.rs"]
mod tests_simplex_rational;
#[path = "tests_trait_coverage.rs"]
mod tests_trait_coverage;

use super::types::*;
use super::*;
use crate::cdcl::Var;
use crate::theories::rational::{DeltaRational, Rational};
use std::collections::HashMap;

fn make_lit(idx: u32, pos: bool) -> Lit {
    let var = Var::new(idx);
    if pos {
        Lit::pos(var)
    } else {
        Lit::neg(var)
    }
}

fn level_bound(value: Rational, reason: Lit, level: u32) -> Bound {
    Bound::new(DeltaRational::from_rational(value), reason, level)
}

fn insert_bound(
    bounds: &mut HashMap<ArithVar, Bound>,
    var: ArithVar,
    value: Rational,
    reason: Lit,
    level: u32,
) {
    bounds.insert(var, level_bound(value, reason, level));
}

fn set_zero_assignments(arith: &mut ArithmeticTheory, vars: &[ArithVar]) {
    for &var in vars {
        arith
            .assignment
            .insert(var, DeltaRational::from_rational(Rational::ZERO));
    }
}
