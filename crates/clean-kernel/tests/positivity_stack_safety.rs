// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::inductive::check_positivity;
use clean_kernel::{Expr, Name};

fn deep_pi_chain(depth: usize, tail: Expr) -> Expr {
    let mut expr = tail;
    for _ in 0..depth {
        expr = Expr::arrow(Expr::prop(), expr);
    }
    expr
}

#[test]
fn test_positivity_handles_20k_constructor_chain_without_stack_overflow() {
    let ind = Name::from_string("T");
    let ctor_type = deep_pi_chain(20_000, Expr::const_(ind.clone(), vec![]));

    check_positivity(&ind, &ctor_type, 0, &[&ind])
        .expect("20k constructor Pi chain should stay stack safe");
}

#[test]
fn test_positivity_handles_20k_domain_tree_without_stack_overflow() {
    let ind = Name::from_string("T");
    let deep_domain = deep_pi_chain(20_000, Expr::prop());
    let ctor_type = Expr::arrow(deep_domain, Expr::const_(ind.clone(), vec![]));

    check_positivity(&ind, &ctor_type, 0, &[&ind])
        .expect("20k nested domain should stay stack safe");
}
