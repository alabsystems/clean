// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semantic soundness of the Lean kernel level algebra (`lean_kernel.rs`,
//! DECISIONS R150) against the ground truth `soundness_harness::eval`, over
//! every raw `Level` the harness enumerates (its `max`/`imax` nodes are built
//! raw, never through a collapsing constructor).
//!
//! The pinned-Lean verdict table (`lean_kernel_tests.rs`) fixes what the port
//! ANSWERS on chosen pairs; this fixes that no answer is FALSE on any pair in
//! the domain: `lean_normalize` and `lean_mk_max` / `lean_mk_imax` preserve the
//! value at every assignment, `lean_is_equivalent` and `lean_is_geq` accept
//! only pairs that hold at every assignment, and `lean_instantiate_with`
//! builds a level whose value is the substituted one.

use super::soundness_harness::{all_assignments, enumerate, eval, genuine_equal};
use super::{Level, SliceLookup};
use crate::name::Name;
use std::collections::HashMap;

fn params(names: &[&str]) -> Vec<Name> {
    names.iter().map(|n| Name::from_string(n)).collect()
}

/// `eval(a) >= eval(b)` at every assignment.
fn genuine_geq(a: &Level, b: &Level, assignments: &[Vec<(Name, u64)>]) -> bool {
    assignments.iter().all(|asn| eval(a, asn) >= eval(b, asn))
}

fn imax_value(a: u64, b: u64) -> u64 {
    if b == 0 {
        0
    } else {
        a.max(b)
    }
}

/// `lean_normalize` keeps the value of every level of depth 3 over two
/// parameters, so its equivalence (`nf(a) == nf(b)`) is sound; checked on
/// every accepted pair directly too.
#[test]
fn test_lean_normalize_and_is_equivalent_are_sound_depth3_2params() {
    let ps = params(&["u", "v"]);
    let asns = all_assignments(&ps, 4);
    let levels = enumerate(3, &ps, None);
    // 1,175 levels, measured 2026-10-20.
    assert!(levels.len() > 1_000, "domain: {} levels", levels.len());
    let mut classes: HashMap<Level, Vec<&Level>> = HashMap::new();
    for l in &levels {
        let nf = l.lean_normalize();
        assert!(
            genuine_equal(&nf, l, &asns),
            "lean_normalize changed the value of `{l}`: `{nf}`"
        );
        classes.entry(nf).or_default().push(l);
    }
    let mut accepted = 0usize;
    for members in classes.values() {
        for a in members {
            for b in members {
                assert!(
                    Level::lean_is_equivalent(a, b),
                    "same normal form, not equivalent: `{a}` vs `{b}`"
                );
                assert!(
                    genuine_equal(a, b, &asns),
                    "lean_is_equivalent accepts a false equality: `{a}` = `{b}`"
                );
                accepted += 1;
            }
        }
    }
    assert!(
        accepted > levels.len(),
        "nontrivial classes: {accepted} pairs"
    );
}

/// The same over three parameters, capped at the first 4,000 levels the
/// harness enumerates.
#[test]
fn test_lean_normalize_is_sound_depth3_3params_capped() {
    let ps = params(&["u", "v", "w"]);
    let asns = all_assignments(&ps, 4);
    for l in enumerate(3, &ps, Some(4_000)) {
        let nf = l.lean_normalize();
        assert!(
            genuine_equal(&nf, &l, &asns),
            "lean_normalize changed the value of `{l}`: `{nf}`"
        );
    }
}

/// `lean_is_geq` accepts only pairs with `eval(a) >= eval(b)` at every
/// assignment, and `lean_mk_max` / `lean_mk_imax` build `max` / `imax` of
/// their arguments' values, over every ordered pair of the first 700 levels.
#[test]
fn test_lean_is_geq_and_mk_max_imax_are_sound_on_every_pair() {
    let ps = params(&["u", "v"]);
    let asns = all_assignments(&ps, 4);
    let levels = enumerate(3, &ps, Some(700));
    let mut geq_accepted = 0usize;
    for a in &levels {
        for b in &levels {
            if Level::lean_is_geq(a, b) {
                assert!(
                    genuine_geq(a, b, &asns),
                    "lean_is_geq accepts a false bound: `{a}` >= `{b}`"
                );
                geq_accepted += 1;
            }
            let m = Level::lean_mk_max(a.clone(), b.clone());
            let im = Level::lean_mk_imax(a.clone(), b.clone());
            for asn in &asns {
                let (va, vb) = (eval(a, asn), eval(b, asn));
                assert_eq!(eval(&m, asn), va.max(vb), "mk_max `{a}` `{b}` = `{m}`");
                assert_eq!(
                    eval(&im, asn),
                    imax_value(va, vb),
                    "mk_imax `{a}` `{b}` = `{im}`"
                );
            }
        }
    }
    assert!(
        geq_accepted > levels.len(),
        "nontrivial: {geq_accepted} pairs"
    );
}

/// `lean_instantiate_with` at `u := s, v := t` builds a level whose value at
/// every assignment is the input's value at the substituted assignment,
/// whether or not it reports a sharing hazard (the hazard is about which
/// SPELLING Lean keeps, never the value).
#[test]
fn test_lean_instantiate_preserves_value_under_substitution() {
    let ps = params(&["u", "v"]);
    let asns = all_assignments(&ps, 4);
    let levels = enumerate(3, &ps, Some(1_500));
    let u = Level::Param(Name::from_string("u"));
    let v = Level::Param(Name::from_string("v"));
    let substitutions = [
        vec![v.clone(), u.clone()],
        vec![u.clone(), Level::lean_imax_core(u.clone(), v.clone())],
        vec![Level::Zero, Level::succ(v.clone())],
        vec![Level::lean_max_core(u.clone(), v.clone()), Level::Zero],
        vec![u.clone(), v.clone()],
    ];
    let mut hazards = 0usize;
    for subst in &substitutions {
        let lookup = SliceLookup {
            params: &ps,
            levels: subst,
        };
        for l in &levels {
            let mut hazard = false;
            let out = l.lean_instantiate_with(&lookup, &mut hazard);
            hazards += usize::from(hazard);
            let built = out.level.unwrap_or_else(|| l.clone());
            for asn in &asns {
                let substituted: Vec<(Name, u64)> = ps
                    .iter()
                    .zip(subst)
                    .map(|(p, s)| (p.clone(), eval(s, asn)))
                    .collect();
                assert_eq!(
                    eval(&built, asn),
                    eval(l, &substituted),
                    "instantiate `{l}` at {subst:?} built `{built}`"
                );
            }
        }
    }
    // The identity substitution is where a sharing hazard can arise.
    assert!(hazards > 0, "the domain reaches the sharing hazard");
}
