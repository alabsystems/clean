// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The second half of `level_as_written.rs`: the residue validation cannot see
//! (a form built by instantiation), and the checks against Lean's kernel
//! verdicts and the port of Lean's level algebra (`super::lean`).

use super::*;

// --- the residue: a form built by instantiation, which validation cannot see ---

/// `succ (imax w r)` over `u, v, w` (indices 0, 1, 2), with `r` written
/// `max v u` (`swapped`) or `max u v`.
fn succ_imax_w(swapped: bool) -> RawLevel {
    let (a, b) = if swapped { (1, 0) } else { (0, 1) };
    raw_succ(raw_imax(
        RawLevel::Param(2),
        raw_max(RawLevel::Param(a), RawLevel::Param(b)),
    ))
}

/// `[u, v, max u v]`, the levels the residue instantiates at.
fn at_w_max_u_v() -> Vec<RawLevel> {
    vec![
        RawLevel::Param(0),
        RawLevel::Param(1),
        raw_max(RawLevel::Param(0), RawLevel::Param(1)),
    ]
}

fn succ_max_u_v() -> RawLevel {
    raw_succ(raw_max(RawLevel::Param(0), RawLevel::Param(1)))
}

/// `B.{u,v,w} : Sort (succ_imax_w + 1) := Sort succ_imax_w`; does ck0 find
/// `Sort (succ (max u v))` and `B.{u, v, max u v}` def-eq? Lean's kernel
/// unfolds `B` with `instantiate`, which keeps `imax (max u v) (max v u)`
/// when `r` is written `max v u`; its `normalize` then finds the two sides
/// equal and keeps `succ (max u v)`, not `max (u+1) (v+1)`.
fn instantiated_def_eq(swapped: bool) -> bool {
    let b = n("B");
    let env0 = MinimalEnv::new();
    let valid = |env: &MinimalEnv, raw: &RawExpr, arity| {
        Term::validate(env, raw, 0, arity).expect("the term validates")
    };
    let ty = valid(&env0, &RawExpr::Sort(raw_succ(succ_imax_w(swapped))), 3);
    let body = valid(&env0, &RawExpr::Sort(succ_imax_w(swapped)), 3);
    let env = env0.with_def(b.clone(), 3, ty, body, Transparency::Transparent);
    let lhs = valid(&env, &RawExpr::Sort(succ_max_u_v()), 2);
    let rhs = valid(&env, &RawExpr::Const(b, at_w_max_u_v()), 2);
    is_def_eq(&env, &lhs, &rhs, &mut Budget::default_budget()).expect("within budget")
}

/// Lean's kernel refuses `t : Sort (succ (max u v)) → B.{u, v, max u v}`
/// with `r` written `max v u` ("declaration type mismatch") and admits it
/// with `max u v`; ck0 finds the sorts equal either way.
#[test]
fn test_instantiated_def_eq_with_swapped_max_is_equal_where_lean_refuses_it() {
    assert!(
        instantiated_def_eq(true),
        "ck0 finds them equal, Lean does not"
    );
    assert!(
        instantiated_def_eq(false),
        "the control, which Lean admits too"
    );
}

/// `G.{u,v,w} : Sort succ_imax_w`, an axiom, and
/// `I.{u,v} : Sort (succ (max u v))` with `I.mk : G.{u, v, max u v} → I`.
fn instantiated_universe_check(swapped: bool) -> Result<(), clean_ck0::AdmitError> {
    let g = n("G");
    let env0 = MinimalEnv::new();
    let g_ty = Term::validate(&env0, &RawExpr::Sort(succ_imax_w(swapped)), 0, 3)
        .expect("G's type validates");
    let mut env = env0.with_const_typed(g.clone(), 3, g_ty);
    let own = env.clone().with_const(n("I"), 2);
    let valid = |raw: &RawExpr| Term::validate(&own, raw, 0, 2).expect("the decl validates");
    let decl = InductiveDecl {
        name: n("I"),
        num_level_params: 2,
        num_params: 0,
        type_: valid(&RawExpr::Sort(succ_max_u_v())),
        constructors: vec![Constructor {
            name: n("I.mk"),
            type_: valid(&RawExpr::Pi(
                BinderInfo::Default,
                Box::new(RawExpr::Const(g, at_w_max_u_v())),
                Box::new(RawExpr::Const(
                    n("I"),
                    vec![RawLevel::Param(0), RawLevel::Param(1)],
                )),
            )),
        }],
    };
    add_inductive(&mut env, decl)
}

/// Lean's kernel refuses `I` with `r` written `max v u` ("universe level of
/// type_of(arg #1) of 'G1.I.mk' is too big") and admits it with `max u v`;
/// ck0 admits it either way.
#[test]
fn test_instantiated_universe_check_with_swapped_max_admits_where_lean_refuses_it() {
    instantiated_universe_check(true).expect("ck0 admits it, Lean does not");
    instantiated_universe_check(false).expect("the control, which Lean admits too");
}

const LEAN_VERDICTS: &str =
    include_str!("../fixtures/level_gap/lean_kernel_verdicts_v4.30.0-rc2.txt");

/// The recorded verdicts are the ones the tests here and R174's
/// universe-check tests state.
#[test]
fn test_lean_kernel_verdicts_are_the_ones_pinned() {
    let mut lines = LEAN_VERDICTS.lines();
    assert_eq!(lines.next(), Some("# lean 4.30.0-rc2"));
    let verdicts: Vec<(&str, &str)> = lines
        .map(|l| {
            let (tag, verdict) = l.split_once('\t').expect("a tab-separated row");
            (tag, verdict.split(' ').next().unwrap_or_default())
        })
        .collect();
    let expected = [
        ("S imax u v + 1, field alpha -> beta", "REJECT"),
        ("S max u v + 1, field alpha -> beta", "ACCEPT"),
        ("T imax u (v+1) + 1, field Sort (v+1)", "REJECT"),
        ("T imax u (v+1) + 1, field Sort (imax u v)", "ACCEPT"),
        (
            "def : Sort (imax u (v+1) + 2) := Sort (max u (v+1) + 1)",
            "REJECT",
        ),
        (
            "def : Sort (max u (v+1) + 2) := Sort (max u (v+1) + 1)",
            "ACCEPT",
        ),
        ("P Sort (imax u 0), field Type", "REJECT"),
        ("P Prop, field Type", "ACCEPT"),
        ("proof irrelevance at Sort 0", "ACCEPT"),
        ("proof irrelevance at Sort (max 0 0)", "REJECT"),
        ("proof irrelevance at Sort (imax 0 0)", "REJECT"),
        ("def-eq at w := max u v, rhs max v u", "REJECT"),
        ("def-eq at w := max u v, rhs max u v", "ACCEPT"),
        ("universe check at w := max u v, rhs max v u", "REJECT"),
        ("universe check at w := max u v, rhs max u v", "ACCEPT"),
        ("C universe check, a = 0", "REJECT"),
        ("C universe check, a = 1", "REJECT"),
        ("C universe check, a = max u v", "REJECT"),
        ("C universe check, a = max v u", "REJECT"),
        ("C universe check, control succ (max u v)", "ACCEPT"),
        ("C def-eq, a = 0", "REJECT"),
        ("C def-eq, a = 1", "REJECT"),
        ("C def-eq, a = max u v", "REJECT"),
        ("C def-eq, a = max v u", "REJECT"),
        ("C def-eq, control succ (succ (max u v))", "ACCEPT"),
        ("C typed sort, universe check, a = 0", "REJECT"),
        ("C typed sort, universe check, a = 1", "REJECT"),
        ("C typed sort, universe check, a = max u v", "REJECT"),
        ("C typed sort, universe check, a = max v u", "REJECT"),
        ("C typed sort, universe check, control max u v", "ACCEPT"),
        ("C typed sort, def-eq, a = 0", "REJECT"),
        ("C typed sort, def-eq, a = 1", "REJECT"),
        ("C typed sort, def-eq, a = max u v", "REJECT"),
        ("C typed sort, def-eq, a = max v u", "REJECT"),
        ("C typed sort, def-eq, control max u v", "ACCEPT"),
    ];
    assert_eq!(verdicts, expected);
}

/// The recorded verdict of the row tagged `tag`.
fn lean_accepts(tag: &str) -> bool {
    let row = LEAN_VERDICTS
        .lines()
        .find_map(|l| l.strip_prefix(tag)?.strip_prefix('\t'))
        .unwrap_or_else(|| panic!("no row tagged {tag}"));
    row.starts_with("ACCEPT")
}

/// The port decides as Lean's kernel on the rows it can state as one
/// comparison: the third form's order and equality checks, and the residue's
/// through its `instantiate`. `I (α : Sort u) : Sort r` checks `r >= u`; a
/// `def : Sort t := Sort (max (u+1) (v+1))` compares `t` with
/// `succ (max (u+1) (v+1))`; with no `succ` written, a field `Sort l` of an
/// `I : Sort (succ (max u v))` checks `succ (max u v) >= succ l`, and a
/// `def : Sort (succ (max u v)) := Sort l` compares the two; the residue
/// compares `succ (max u v)` with `succ (imax w r)` instantiated at
/// `w := max u v`.
#[test]
fn test_lean_port_decides_the_level_gap_rows_as_lean() {
    let lv = lean::from_raw;
    let u = lv(&RawLevel::Param(0));
    let def_value_type = lv(&raw_succ(raw_max(
        raw_succ(RawLevel::Param(0)),
        raw_succ(RawLevel::Param(1)),
    )));
    let mut forms: Vec<(String, RawLevel)> = c_form_lhs()
        .into_iter()
        .map(|(a, lhs)| (format!("a = {a}"), succ_imax_max_u_v(lhs)))
        .collect();
    forms.push(("control succ (max u v)".to_string(), succ_max_u_v()));
    for (case, r) in &forms {
        let tag = format!("C universe check, {case}");
        assert_eq!(lean::is_geq(&lv(r), &u), lean_accepts(&tag), "{tag}");
        let tag = if case.starts_with("control") {
            "C def-eq, control succ (succ (max u v))".to_string()
        } else {
            format!("C def-eq, {case}")
        };
        let t = lv(&raw_succ(r.clone()));
        assert_eq!(
            lean::is_equivalent(&t, &def_value_type),
            lean_accepts(&tag),
            "{tag}"
        );
    }
    let result = lv(&succ_max_u_v());
    let mut typed: Vec<(String, RawLevel)> = c_form_lhs()
        .into_iter()
        .map(|(a, lhs)| (format!("a = {a}"), imax_max_u_v(lhs)))
        .collect();
    typed.push((
        "control max u v".to_string(),
        raw_max(RawLevel::Param(0), RawLevel::Param(1)),
    ));
    for (case, l) in &typed {
        let kernel_succ = lv(&raw_succ(l.clone()));
        let tag = format!("C typed sort, universe check, {case}");
        assert_eq!(
            lean::is_geq(&result, &kernel_succ),
            lean_accepts(&tag),
            "{tag}"
        );
        let tag = format!("C typed sort, def-eq, {case}");
        assert_eq!(
            lean::is_equivalent(&result, &kernel_succ),
            lean_accepts(&tag),
            "{tag}"
        );
    }
    let sub: Vec<_> = at_w_max_u_v().iter().map(lv).collect();
    for (swapped, rhs) in [(true, "max v u"), (false, "max u v")] {
        let field = lean::instantiate(&lv(&succ_imax_w(swapped)), &sub);
        let tag = format!("def-eq at w := max u v, rhs {rhs}");
        assert_eq!(
            lean::is_equivalent(&result, &field),
            lean_accepts(&tag),
            "{tag}"
        );
        let tag = format!("universe check at w := max u v, rhs {rhs}");
        assert_eq!(lean::is_geq(&result, &field), lean_accepts(&tag), "{tag}");
    }
}

// --- R150's 2,009 pairs of equal levels and Lean's kernel verdicts ---

const R150: &str =
    include_str!("../../../clean-kernel/src/level/fixtures/lean_kernel_verdicts_v4.30.0-rc2.tsv");

fn r150_rows() -> Vec<(RawLevel, RawLevel, bool)> {
    let mut lines = R150.lines();
    assert_eq!(lines.next(), Some("# lean 4.30.0-rc2"));
    lines
        .map(|l| {
            let mut cols = l.split('\t');
            let (a, b, verdict) = (cols.next(), cols.next(), cols.next());
            let (Some(a), Some(b), Some(verdict)) = (a, b, verdict) else {
                panic!("a three-column row: {l}");
            };
            (lean::parse(a), lean::parse(b), verdict == "ACCEPT")
        })
        .collect()
}

/// The port decides as Lean's kernel on every recorded row.
#[test]
fn test_lean_port_decides_every_r150_row_as_lean() {
    let rows = r150_rows();
    assert_eq!(rows.len(), 2009);
    for (a, b, accept) in &rows {
        assert_eq!(
            lean::is_equivalent(&lean::from_raw(a), &lean::from_raw(b)),
            *accept,
            "{a:?} = {b:?}"
        );
    }
}

/// Through ck0: a row is refused by name when either side holds one of the
/// three forms (1,250 an `imax` whose right side is never zero, 269 a zero
/// form, 3 another `imax` that reduces to a `max`), and ck0's equality is
/// Lean's kernel's on all the rest (442 equal, 45 not). Before R177 ck0 found
/// 546 of the 654 pairs Lean refuses equal.
#[test]
fn test_r150_rows_through_ck0_are_refused_by_name_or_decided_as_lean() {
    let mut never_zero = 0;
    let mut zero_form = 0;
    let mut to_max = 0;
    let mut equal = 0;
    let mut unequal = 0;
    for (a, b, accept) in r150_rows() {
        let (ta, tb) = match (sort(a, 3), sort(b, 3)) {
            (Ok(ta), Ok(tb)) => (ta, tb),
            (Err(e), _) | (_, Err(e)) => {
                match e {
                    ValidateError::LevelAsWritten {
                        form: WrittenLevel::IMaxOfNeverZero,
                    } => never_zero += 1,
                    ValidateError::LevelAsWritten {
                        form: WrittenLevel::ZeroOnceCanonical,
                    } => zero_form += 1,
                    ValidateError::LevelAsWritten {
                        form: WrittenLevel::IMaxReducingToMax,
                    } => to_max += 1,
                    other => panic!("refused otherwise: {other}"),
                }
                continue;
            }
        };
        let ck0 = is_def_eq(&MinimalEnv::new(), &ta, &tb, &mut Budget::default_budget())
            .expect("within budget");
        assert_eq!(ck0, accept, "{ta:?} = {tb:?}");
        if ck0 {
            equal += 1;
        } else {
            unequal += 1;
        }
    }
    assert_eq!(
        (never_zero, zero_form, to_max, equal, unequal),
        (1250, 269, 3, 442, 45)
    );
}

// --- random levels ---

fn arb_level() -> impl Strategy<Value = RawLevel> {
    let leaf = prop_oneof![
        Just(RawLevel::Zero),
        Just(raw_succ(RawLevel::Zero)),
        (0u32..3).prop_map(RawLevel::Param),
    ];
    leaf.prop_recursive(4, 24, 2, |inner| {
        prop_oneof![
            inner.clone().prop_map(raw_succ),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| raw_max(a, b)),
            (inner.clone(), inner).prop_map(|(a, b)| raw_imax(a, b)),
        ]
    })
}

/// A random level free of the three forms, by the port's reading of them.
fn arb_admitted_level() -> impl Strategy<Value = RawLevel> {
    arb_level().prop_filter("free of the three forms", |l| {
        lean::first_form(&lean::from_raw(l)).is_none()
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4000))]

    /// Validation refuses a level exactly when it holds one of the three
    /// forms, naming the first a walk meets, children first.
    #[test]
    fn prop_validation_refuses_exactly_the_three_forms(l in arb_level()) {
        let form = match lean::first_form(&lean::from_raw(&l)) {
            None => None,
            Some('A') => Some(WrittenLevel::IMaxOfNeverZero),
            Some('B') => Some(WrittenLevel::ZeroOnceCanonical),
            Some('C') => Some(WrittenLevel::IMaxReducingToMax),
            Some(other) => panic!("the port names no form {other}"),
        };
        match (sort(l.clone(), 3), form) {
            (Ok(_), None) => {}
            (Err(ValidateError::LevelAsWritten { form: got }), Some(want)) => {
                prop_assert_eq!(got, want);
            }
            (got, want) => prop_assert!(false, "{l:?}: {got:?}, expected {want:?}"),
        }
    }

    /// On levels free of the three forms, validation admits both, and ck0's
    /// equality, order and `Prop` test are the port's on the levels as
    /// written, and with the `succ` Lean's kernel adds typing `Sort a` on one
    /// side.
    #[test]
    fn prop_admitted_levels_are_decided_as_lean(a in arb_admitted_level(), b in arb_admitted_level()) {
        let admitted = |l: &RawLevel| {
            sort(l.clone(), 3).unwrap_or_else(|e| panic!("{l:?} is free of the forms, refused: {e}"))
        };
        let (ta, tb) = (admitted(&a), admitted(&b));
        let (la, lb) = (lean::from_raw(&a), lean::from_raw(&b));
        let eq = is_def_eq(&MinimalEnv::new(), &ta, &tb, &mut Budget::default_budget())
            .expect("within budget");
        prop_assert_eq!(eq, lean::is_equivalent(&la, &lb), "{:?} = {:?}", a, b);
        prop_assert_eq!(
            Level::is_geq(&level_of(&ta), &level_of(&tb)),
            lean::is_geq(&la, &lb),
            "{:?} >= {:?}", a, b
        );
        prop_assert_eq!(level_of(&ta).is_zero(), a == RawLevel::Zero);
        let (sa, lsa) = (Level::succ(level_of(&ta)), lean::succ(la));
        prop_assert_eq!(sa == level_of(&tb), lean::is_equivalent(&lsa, &lb), "succ {:?} = {:?}", a, b);
        prop_assert_eq!(
            Level::is_geq(&sa, &level_of(&tb)),
            lean::is_geq(&lsa, &lb),
            "succ {:?} >= {:?}", a, b
        );
        prop_assert_eq!(
            Level::is_geq(&level_of(&tb), &sa),
            lean::is_geq(&lb, &lsa),
            "{:?} >= succ {:?}", b, a
        );
    }
}
