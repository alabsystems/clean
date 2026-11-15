// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's kernel level algebra (`lean_kernel.rs`) against pinned Lean
//! v4.30.0-rc2's own verdicts (`fixtures/lean_kernel_verdicts_v4.30.0-rc2.tsv`,
//! minted by `fixtures/KernelLevelVerdicts.lean`; see `fixtures/README.md`).

use super::{LeanInstantiated, SliceLookup};
use crate::env::{Environment, KernelTheory};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

const VERDICTS: &str = include_str!("fixtures/lean_kernel_verdicts_v4.30.0-rc2.tsv");

/// One fixture row: `a<TAB>b<TAB>ACCEPT|REJECT`.
struct Row {
    lhs: Level,
    rhs: Level,
    lean_accepts: bool,
    text: String,
}

fn parse_level(chars: &[u8], pos: &mut usize) -> Level {
    let head = chars[*pos];
    *pos += 1;
    match head {
        b'Z' => Level::zero(),
        b'P' => {
            *pos += 1; // '('
            let start = *pos;
            while chars[*pos] != b')' {
                *pos += 1;
            }
            let name = std::str::from_utf8(&chars[start..*pos]).expect("utf8 parameter name");
            *pos += 1; // ')'
            Level::param(Name::from_string(name))
        }
        b'S' => {
            *pos += 1;
            let inner = parse_level(chars, pos);
            *pos += 1;
            Level::succ(inner)
        }
        b'M' | b'I' => {
            *pos += 1;
            let a = parse_level(chars, pos);
            *pos += 1; // ','
            let b = parse_level(chars, pos);
            *pos += 1; // ')'
            if head == b'M' {
                Level::lean_max_core(a, b)
            } else {
                Level::lean_imax_core(a, b)
            }
        }
        other => panic!("bad level head {}", other as char),
    }
}

fn parse(text: &str) -> Level {
    let mut pos = 0;
    let level = parse_level(text.as_bytes(), &mut pos);
    assert_eq!(pos, text.len(), "trailing input in {text}");
    level
}

fn rows() -> Vec<Row> {
    let mut lines = VERDICTS.lines();
    assert_eq!(
        lines.next(),
        Some("# lean 4.30.0-rc2"),
        "the fixture must name the pinned Lean that minted it"
    );
    let rows: Vec<Row> = lines
        .map(|line| {
            let cols: Vec<&str> = line.split('\t').collect();
            assert_eq!(cols.len(), 3, "malformed fixture row {line}");
            let lean_accepts = match cols[2] {
                "ACCEPT" => true,
                "REJECT" => false,
                other => panic!("bad verdict {other} in {line}"),
            };
            Row {
                lhs: parse(cols[0]),
                rhs: parse(cols[1]),
                lean_accepts,
                text: line.to_owned(),
            }
        })
        .collect();
    assert_eq!(
        rows.len(),
        2009,
        "fixture row count (see fixtures/README.md)"
    );
    rows
}

fn p(name: &str) -> Level {
    Level::param(Name::from_string(name))
}

fn one() -> Level {
    Level::succ(Level::zero())
}

fn checker_verdicts(theory: KernelTheory, rows: &[Row]) -> Vec<String> {
    let env = Environment::for_lean_replay();
    let mut tc = TypeChecker::new(&env);
    tc.set_kernel_theory(theory);
    rows.iter()
        .filter(|row| tc.levels_eq(&row.lhs, &row.rhs) != row.lean_accepts)
        .map(|row| row.text.clone())
        .collect()
}

#[test]
fn test_lean_kernel_matches_pinned_lean_verdict_table() {
    let rows = rows();
    let wrong: Vec<&str> = rows
        .iter()
        .filter(|row| Level::lean_is_equivalent(&row.lhs, &row.rhs) != row.lean_accepts)
        .map(|row| row.text.as_str())
        .collect();
    assert!(
        wrong.is_empty(),
        "{} of {} rows disagree with pinned Lean v4.30.0-rc2, e.g. {:?}",
        wrong.len(),
        rows.len(),
        &wrong[..wrong.len().min(8)]
    );
    // Both verdicts occur, so the table can fail in both directions.
    assert!(rows.iter().any(|row| row.lean_accepts));
    assert!(rows.iter().any(|row| !row.lean_accepts));
}

/// The plan's exit test: under `KernelTheory::Lean` the checker's level
/// comparison is pinned Lean's on every fixture row, so the soundness
/// harness's own completeness targets (t1, t2) are refused, as pinned Lean
/// refuses them ("declaration type mismatch", 2026-10-17).
#[test]
fn lean_profile_level_def_eq_matches_pinned_normalizer() {
    let env = Environment::for_lean_replay();
    let mut tc = TypeChecker::new(&env);
    tc.set_kernel_theory(KernelTheory::Lean);
    let (lhs, rhs) = crate::level::soundness_harness::completeness_target_pair();
    assert!(
        !tc.levels_eq(&lhs, &rhs),
        "completeness_target_pair (t1) {lhs} vs {rhs}: pinned Lean refuses it"
    );
    let (lhs, rhs) = crate::level::soundness_harness::reverse_rec_on_target_pair();
    assert!(
        !tc.levels_eq(&lhs, &rhs),
        "reverse_rec_on_target_pair (t2) {lhs} vs {rhs}: pinned Lean refuses it"
    );
    let rows = rows();
    let wrong = checker_verdicts(KernelTheory::Lean, &rows);
    assert!(
        wrong.is_empty(),
        "{} of {} rows: KernelTheory::Lean disagrees with pinned Lean, e.g. {:?}",
        wrong.len(),
        rows.len(),
        &wrong[..wrong.len().min(8)]
    );
}

#[test]
fn lean_reference_profile_uses_the_same_level_rules() {
    let rows = rows();
    let wrong = checker_verdicts(KernelTheory::LeanReference, &rows);
    assert!(
        wrong.is_empty(),
        "{} rows: KernelTheory::LeanReference disagrees with pinned Lean, e.g. {:?}",
        wrong.len(),
        &wrong[..wrong.len().min(8)]
    );
}

/// The scoped R2 exception (DECISIONS R150): `Extended` keeps Clean's superset.
/// It accepts every pair pinned Lean accepts, the harness targets, and pairs
/// pinned Lean refuses.
#[test]
fn extended_profile_keeps_clean_superset_on_the_harness_pairs() {
    let env = Environment::for_lean_replay();
    let tc = TypeChecker::new(&env);
    assert_eq!(tc.kernel_theory(), KernelTheory::Extended);
    let (lhs, rhs) = crate::level::soundness_harness::completeness_target_pair();
    assert!(tc.levels_eq(&lhs, &rhs), "t1 stays accepted under Extended");
    let (lhs, rhs) = crate::level::soundness_harness::reverse_rec_on_target_pair();
    assert!(tc.levels_eq(&lhs, &rhs), "t2 stays accepted under Extended");
    let rows = rows();
    let refused_accepts: Vec<&str> = rows
        .iter()
        .filter(|row| row.lean_accepts && !tc.levels_eq(&row.lhs, &row.rhs))
        .map(|row| row.text.as_str())
        .collect();
    assert!(
        refused_accepts.is_empty(),
        "Extended refuses pairs pinned Lean accepts: {refused_accepts:?}"
    );
    let superset = rows
        .iter()
        .filter(|row| !row.lean_accepts && tc.levels_eq(&row.lhs, &row.rhs))
        .count();
    assert!(
        superset > 0,
        "Extended accepts no pair pinned Lean refuses; the R150 exception is gone"
    );
}

#[test]
fn lean_mk_max_follows_level_cpp_branch_order() {
    let (u, v) = (p("u"), p("v"));
    let two = Level::succ(one());
    // 1. both explicit: the larger offset.
    assert_eq!(Level::lean_mk_max(one(), two.clone()), two);
    // 2. equal.
    assert_eq!(Level::lean_mk_max(u.clone(), u.clone()), u);
    // 3. zero on either side.
    assert_eq!(Level::lean_mk_max(Level::zero(), u.clone()), u);
    assert_eq!(Level::lean_mk_max(u.clone(), Level::zero()), u);
    // 4./5. one side is a `max` holding the other.
    let max_uv = Level::lean_max_core(u.clone(), v.clone());
    assert_eq!(Level::lean_mk_max(u.clone(), max_uv.clone()), max_uv);
    assert_eq!(Level::lean_mk_max(max_uv.clone(), v.clone()), max_uv);
    // 6. same base: the larger offset.
    let u2 = Level::succ(Level::succ(u.clone()));
    assert_eq!(Level::lean_mk_max(Level::succ(u.clone()), u2.clone()), u2);
    // 7. otherwise a raw node: `max 1 (v+1)` keeps both (Clean's `Level::max`
    // returns `v+1`).
    let v1 = Level::succ(v.clone());
    let raw = Level::lean_mk_max(one(), v1.clone());
    assert_eq!(raw, Level::lean_max_core(one(), v1.clone()));
    assert_eq!(Level::max(one(), v1.clone()), v1);
}

#[test]
fn lean_mk_imax_follows_level_cpp_branch_order() {
    let (u, w) = (p("u"), p("w"));
    let w1 = Level::succ(w);
    // `imax u (w+1)` is `mk_max u (w+1)`.
    assert_eq!(
        Level::lean_mk_imax(u.clone(), w1.clone()),
        Level::lean_max_core(u.clone(), w1)
    );
    assert_eq!(Level::lean_mk_imax(u.clone(), Level::zero()), Level::zero());
    assert_eq!(Level::lean_mk_imax(Level::zero(), u.clone()), u);
    assert_eq!(Level::lean_mk_imax(one(), u.clone()), u);
    assert_eq!(Level::lean_mk_imax(u.clone(), u.clone()), u);
    let v = p("v");
    assert_eq!(
        Level::lean_mk_imax(u.clone(), v.clone()),
        Level::lean_imax_core(u, v)
    );
}

#[test]
fn lean_normalize_does_not_reflatten_imax() {
    let u1 = Level::succ(p("u"));
    let raw = Level::lean_imax_core(one(), u1.clone());
    // `mk_imax 1 (u+1)` is `mk_max 1 (u+1)`, a raw `max`, and stays one.
    assert_eq!(
        raw.lean_normalize(),
        Level::lean_max_core(one(), u1.clone())
    );
    // A measured REJECT row; Clean's #1436 re-flattening accepts it.
    assert!(!Level::lean_is_equivalent(&u1, &raw));
    assert!(Level::is_def_eq(&u1, &raw));
}

#[test]
fn lean_is_geq_is_weaker_than_clean_on_raw_imax() {
    let (u, v) = (p("u"), p("v"));
    let u1 = Level::succ(u.clone());
    let lhs = Level::lean_imax_core(Level::lean_imax_core(one(), u1.clone()), v.clone());
    let rhs = Level::lean_imax_core(u1.clone(), v.clone());
    assert!(!Level::lean_is_geq(&lhs, &rhs));
    assert!(Level::is_geq(&lhs, &rhs));
    assert!(Level::lean_is_geq(&Level::lean_max_core(u.clone(), v), &u));
    assert!(Level::lean_is_geq(&u1, &one()));
    assert!(!Level::lean_is_geq(&one(), &u1));
}

fn lean_instantiate(level: &Level, params: &[Name], levels: &[Level]) -> (LeanInstantiated, bool) {
    let mut hazard = false;
    let lookup = SliceLookup { params, levels };
    let out = level.lean_instantiate_with(&lookup, &mut hazard);
    (out, hazard)
}

#[test]
fn lean_instantiate_rebuilds_only_substituted_nodes() {
    let (u, v, w) = (p("u"), p("v"), p("w"));
    let names = |ns: &[&str]| ns.iter().map(|n| Name::from_string(n)).collect::<Vec<_>>();

    // `max 1 (u+1)` with `u := w`: Lean keeps `max 1 (w+1)`; Clean's
    // substitution collapses it to `w+1`.
    let l = Level::lean_max_core(one(), Level::succ(u.clone()));
    let (out, hazard) = lean_instantiate(&l, &names(&["u"]), std::slice::from_ref(&w));
    assert!(!hazard);
    assert_eq!(
        out.level,
        Some(Level::lean_max_core(one(), Level::succ(w.clone())))
    );
    assert_eq!(
        l.substitute_slice(&names(&["u"]), std::slice::from_ref(&w)),
        Level::succ(w.clone())
    );

    // t5: `max (max u v) w` with `w := imax u v` is `max (max u v) (imax u v)`
    // under Lean, `max u v` under Clean.
    let k = Level::lean_max_core(Level::lean_max_core(u.clone(), v.clone()), w.clone());
    let imax_uv = Level::lean_imax_core(u.clone(), v.clone());
    let subst = [u.clone(), v.clone(), imax_uv.clone()];
    let (out, hazard) = lean_instantiate(&k, &names(&["u", "v", "w"]), &subst);
    assert!(!hazard, "max u v rebuilds to itself: no sharing dependence");
    assert_eq!(
        out.level,
        Some(Level::lean_max_core(
            Level::lean_max_core(u.clone(), v.clone()),
            imax_uv
        ))
    );
    assert_eq!(
        k.substitute_slice(&names(&["u", "v", "w"]), &subst),
        Level::lean_max_core(u.clone(), v.clone())
    );

    // No substituted parameter: kept, untouched.
    let (out, hazard) = lean_instantiate(&k, &names(&["x"]), std::slice::from_ref(&w));
    assert!(out.level.is_none() && !out.touched && !hazard);

    // An identity renaming of a node `mk_max` rebuilds to itself: kept, no hazard.
    let (out, hazard) = lean_instantiate(&k, &names(&["u", "v"]), &[u.clone(), v.clone()]);
    assert!(out.level.is_none() && out.touched && !hazard);

    // An identity renaming of `imax v (u+1)`, which `mk_imax` rebuilds to
    // `max v (u+1)`: Lean keeps it when the objects are shared and rebuilds it
    // when they are not (critic B1), so the instantiation is a hazard.
    let cs = Level::lean_imax_core(v.clone(), Level::succ(u.clone()));
    let (out, hazard) = lean_instantiate(&cs, &names(&["u", "v"]), &[u.clone(), v.clone()]);
    assert!(out.level.is_none() && hazard);
    // The same node with a parameter that really changes is rebuilt, which is
    // Lean's answer whatever the sharing: no hazard.
    let (out, hazard) = lean_instantiate(&cs, &names(&["u"]), std::slice::from_ref(&w));
    assert!(!hazard);
    assert_eq!(out.level, Some(Level::lean_max_core(v, Level::succ(w))));
    // A parameter-free non-canonical node is never rebuilt (level.cpp:304).
    let ground = Level::lean_imax_core(one(), Level::succ(one()));
    let (out, hazard) = lean_instantiate(&ground, &names(&["u"]), std::slice::from_ref(&u));
    assert!(out.level.is_none() && !out.touched && !hazard);
}
