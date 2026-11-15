// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compiler-introduced binders that source code could spell, and the nested
//! `n + k` plan: false theorems measured 2026-09-25 against Lean 4.8.0, and
//! their fixes.
//!
//! * SPELLABLE INTERNAL BINDERS. Every desugaring that wraps user-written
//!   code in a binder of its own named that binder with an ordinary
//!   identifier: `_x` (`fun | …`, equation definitions), `_x_arg<n>` (a lifted
//!   equation column), `_x_dep<n>`, `_dx<n>` (destructuring `fun`), `_tpl`
//!   (tuple `let`), `__cdot_<n>` (`·` sections), `_comp_x` (`∘`), `_cov_*`
//!   (course-of-values recursion), `__reassign_tmp` (do-block pattern
//!   reassignment), `__do_lift_<n>` (`(← e)`), and more. A body naming a
//!   GLOBAL of that spelling read the binder instead, and a pattern variable
//!   of that spelling captured the binder: with `def _x_arg1 := 77`, `| 0, y
//!   => y | n+1, _ => _x_arg1` proved `e1 1 5 = 5` (Lean: 77). The binders
//!   are now `SurfaceName::unspellable` — a numeric last component, which no
//!   identifier token produces.
//! * NESTED `n + k`. The nested-pattern plan read every `n + k` below a
//!   constructor as `n + 1`, so in a recursive definition `(z+2) :: y`
//!   matched `1 :: y` and `h1 [1] = 1` was provable (Lean: 0), and `(z+0) ::
//!   y` did not match `0 :: y`.
//!
//! Every expected value was measured with Lean 4.8.0 (`#eval`); every WRONG
//! value is the one the previous Clean computed (its own reduct, not `truth +
//! 1`) and is refused by `rfl` and by `decide`.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn register(env: &mut Environment, source: &str) -> Result<(), String> {
    fn failures(result: &ElabResult) -> Result<(), String> {
        match result {
            ElabResult::Multiple(results) => {
                for result in results {
                    failures(result)?;
                }
                Ok(())
            }
            ElabResult::Failed { name, error, .. } => Err(format!("{name}: {error}")),
            _ => Ok(()),
        }
    }
    let mut context = FileContext::new();
    for decl in parse_file(source).map_err(|error| format!("parse error: {error}"))? {
        let processed = preprocess_decl_with_context(&decl, &mut context);
        let result = elaborate_decl_and_register(env, &processed)
            .map_err(|error| format!("elaborate/kernel-check error: {error}"))?;
        failures(&result)?;
    }
    Ok(())
}

/// `call = expected` must register axiom-free; `call = wrong` must be refused
/// by `rfl` and by `decide`, and leave nothing registered.
fn computation(env: &mut Environment, tag: &str, call: &str, expected: u64, wrong: Option<u64>) {
    let good = format!("correct_{tag}");
    register(env, &format!("theorem {good} : {call} = {expected} := rfl"))
        .unwrap_or_else(|error| panic!("{call} = {expected} must hold: {error}"));
    let deps = env
        .axiom_deps(&Name::from_string(&good))
        .expect("registered theorem");
    assert!(
        deps.is_empty(),
        "{call}: computation depends on axioms: {deps:?}"
    );
    let Some(wrong) = wrong else { return };
    assert_ne!(
        expected, wrong,
        "{tag}: a check needs a genuinely wrong value"
    );
    for (kind, proof) in [("rfl", "rfl"), ("decide", "by decide")] {
        let bad = format!("incorrect_{tag}_{kind}");
        let error = register(env, &format!("theorem {bad} : {call} = {wrong} := {proof}"))
            .expect_err(&format!(
                "FALSE theorem accepted: {call} = {wrong} := {proof}"
            ));
        assert!(
            !error.contains("parse error"),
            "negative must parse: {error}"
        );
        assert!(
            env.get_const(&Name::from_string(&bad)).is_none(),
            "false theorem registered: {call} = {wrong}"
        );
    }
}

fn run(env: &mut Environment, prefix: &str, cases: &[(&str, u64, Option<u64>)]) {
    for (id, (call, expected, wrong)) in cases.iter().enumerate() {
        computation(env, &format!("{prefix}{id}"), call, *expected, *wrong);
    }
}

#[test]
fn equation_binders_do_not_capture_globals_or_pattern_variables() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def _x_arg1 : Nat := 77
def _x_arg2 : Nat := 33
def _x : Nat := 55
def e1 : Nat → Nat → Nat
  | 0, y => y
  | n+1, _ => _x_arg1
def e2 : Nat → Nat → Nat
  | 0, _ => _x_arg1
  | n+1, _ => e2 n 3
def e3 : Nat → Nat → Nat
  | 0, _ => _x
  | n+1, _ => e3 n 3
def e4 : Nat → Nat → Nat
  | 0, _x_arg1 => _x_arg1
  | n+1, _ => _x_arg1
def e5 : Nat → Nat → Nat
  | 0, y => y
  | n+1, _ => e5 n 3 + _x_arg1
def e6 : Nat → Nat → Nat → Nat
  | 0, 0, z => z
  | _, _, _ => _x_arg2
def e7 : List Nat → Nat → Nat
  | [], y => y
  | _ :: t, _ => e7 t 1 + _x_arg1
def e8 : Nat → Nat := fun
  | 0 => _x
  | n+1 => n
"#,
    )
    .expect("definitions elaborate");
    run(
        &mut env,
        "eq",
        &[
            // The regression of 6dc48c14c (base and 29de4ae8b refused `= 5`).
            ("e1 1 5", 77, Some(5)),
            ("e1 0 5", 5, None),
            ("e2 1 5", 77, Some(3)),
            ("e3 1 5", 55, Some(0)),
            ("e4 1 5", 77, Some(5)),
            ("e4 0 5", 5, None),
            ("e5 1 5", 80, Some(8)),
            ("e6 1 1 5", 33, Some(5)),
            ("e6 0 0 5", 5, None),
            ("e7 [4] 9", 78, Some(2)),
            ("e8 0", 55, Some(0)),
            ("e8 3", 2, None),
        ],
    );
    // The universally quantified form the verifier proved on 6dc48c14c.
    let error = register(
        &mut env,
        "theorem e1_general_false : ∀ n m : Nat, e1 (n+1) m = m := fun _ _ => rfl",
    )
    .expect_err("FALSE theorem accepted: ∀ n m, e1 (n+1) m = m");
    assert!(!error.contains("parse error"), "{error}");
}

#[test]
fn tuple_let_destructuring_fun_sections_and_composition_read_globals() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def _tpl : Nat × Nat := (7, 7)
def _dx0 : Nat := 40
def __cdot_0 : Nat := 65
def __cdot_1 : Nat := 70
def _comp_x : Nat := 30
def t3 (p : Nat × Nat) : Nat := let (a, b) := p; _tpl.2 + a
def d1 : Nat × Nat → Nat := fun (a, b) => a + _dx0
def d2 : Nat → Nat × Nat → Nat := fun _dx0 (a, b) => _dx0 + a
def c1 : Nat := (· + __cdot_0) 1
def c2 : Nat := (· + · + __cdot_1) 1 2
def k1 : Nat → Nat := (fun y => y + _comp_x) ∘ (fun z => z)
"#,
    )
    .expect("definitions elaborate");
    run(
        &mut env,
        "tpl",
        &[
            ("(let (_tpl, y) := ((5, 6), 2); y)", 2, Some(6)),
            ("(let (x, y) := (1, 2); _tpl.1 + x)", 8, Some(2)),
            ("t3 (1, 2)", 8, Some(3)),
            ("d1 (1, 2)", 41, None),
            ("d2 10 (1, 2)", 11, None),
            ("c1", 66, Some(2)),
            ("c2", 73, Some(5)),
            ("k1 1", 31, Some(2)),
        ],
    );
}

#[test]
fn do_block_and_course_of_values_temporaries_read_globals() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def __reassign_tmp : Nat × Nat := (9, 9)
def __do_lift_0 : Nat := 24
def _cov_a : Nat := 25
def _cov_b : Nat := 26
def _cov_k : Nat := 27
def r1 : Id Nat := do
  let mut a := 0
  let mut b := 0
  (a, b) := (1, 2)
  return a + __reassign_tmp.1
def p4 : Id Nat := do
  let x := (← pure 5) + __do_lift_0
  return x
def p5 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => p5 n + p5 (n+1) + _cov_a + _cov_b + _cov_k
"#,
    )
    .expect("definitions elaborate");
    run(
        &mut env,
        "do",
        &[
            ("r1.run", 10, Some(2)),
            ("p4.run", 29, Some(10)),
            // The previous Clean computed 2 here (its self-call rewrite read
            // the globals as its own accumulators); `= 2` is refused.
            ("p5 2", 79, Some(2)),
            ("p5 3", 158, None),
        ],
    );
}

#[test]
fn nested_numeral_add_under_a_constructor_keeps_its_offset() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def h1 : List Nat → Nat
  | (z+2) :: y => 1 + h1 y
  | _ => 0
def h5 : List Nat → Nat → Nat
  | (z+2) :: y, _ => 1 + h5 y 0
  | _, _ => 0
def h6 (l : List Nat) : Nat := match l with
  | (z+2) :: y => z + h6 y
  | _ => 0
def h9 : List Nat → Nat
  | (z+3) :: y => z + h9 y
  | _ => 100
def p8 : List Nat → Nat
  | (z+0) :: y => z + p8 y
  | _ => 100
"#,
    )
    .expect("definitions elaborate");
    run(
        &mut env,
        "nk",
        &[
            ("h1 [1]", 0, Some(1)),
            ("h1 [2, 3, 0]", 2, None),
            ("h5 [1] 0", 0, Some(1)),
            ("h6 [1]", 0, Some(1)),
            ("h6 [5, 3, 1, 9]", 4, None),
            ("h9 [3, 2]", 100, Some(0)),
            ("h9 [4, 5, 1]", 103, None),
            ("p8 [3, 4]", 107, Some(105)),
        ],
    );
    let error = register(
        &mut env,
        "theorem h1_general_false : ∀ y : List Nat, h1 (0 :: y) = 1 + h1 y := fun _ => rfl",
    )
    .expect_err("FALSE theorem accepted: h1 (0 :: y) = 1 + h1 y");
    assert!(!error.contains("parse error"), "{error}");
}

/// Battery: every spelling a desugaring used for a binder of its own is a
/// global read in a body, across the equation, `fun |`, `match`, tuple-`let`,
/// destructuring-`fun`, section, composition, do-block and course-of-values
/// forms. Each call's value is closed-form in the global's value `G` (checked
/// against Lean 4.8.0 for every spelling), so no evaluator is needed; a binder
/// capturing the global's name makes the call compute something else and the
/// `= <expected>` theorem fail.
#[test]
fn battery_every_internal_spelling_is_an_ordinary_global() {
    const SPELLINGS: &[&str] = &[
        "_x",
        "_x_arg0",
        "_x_arg1",
        "_x_arg2",
        "_x_dep0",
        "_dx0",
        "_dx1",
        "_tpl",
        "__cdot_0",
        "__cdot_1",
        "_comp_x",
        "_flip_a",
        "_curry_a",
        "_uncurry_p",
        "__or_elim_x",
        "__sum_elim_x",
        "_cov_a",
        "_cov_b",
        "_cov_k",
        "_cov_n",
        "__letpat_scrutinee",
        "__reassign_tmp",
        "__do_lift_0",
        "_pv",
        "_nested_fallback",
        "_match_ctor_field_0",
        "_field_0",
        "_wf_hyp0",
    ];
    const G: u64 = 1000;
    let mut checked = 0usize;
    for (si, s) in SPELLINGS.iter().enumerate() {
        let mut env = Environment::with_prelude();
        // `(source, call, expected)`.
        let defs: Vec<(String, String, u64)> = vec![
            (format!("def b0 : Nat → Nat → Nat\n  | 0, y => y\n  | n+1, _ => {s}\n"), "b0 1 5".into(), G),
            (format!("def b1 : Nat → Nat → Nat\n  | 0, _ => {s}\n  | n+1, _ => b1 n 3\n"), "b1 2 5".into(), G),
            (format!("def b2 : Nat → Nat → Nat → Nat\n  | 0, 0, z => z\n  | _, _, _ => {s}\n"), "b2 1 1 5".into(), G),
            (format!("def b3 : List Nat → Nat → Nat\n  | [], y => y\n  | _ :: t, _ => b3 t 1 + {s}\n"), "b3 [4] 9".into(), G + 1),
            (format!("def b4 : Nat → Nat := fun\n  | 0 => {s}\n  | n+1 => n\n"), "b4 0".into(), G),
            (format!("def b5 (a b : Nat) : Nat := match a, b with\n  | 0, y => y\n  | _, _ => {s}\n"), "b5 1 5".into(), G),
            (format!("def b6 (p : Nat × Nat) : Nat := let (a, c) := p; {s} + a\n"), "b6 (1, 2)".into(), G + 1),
            (format!("def b7 : Nat × Nat → Nat := fun (a, c) => a + {s}\n"), "b7 (1, 2)".into(), G + 1),
            (format!("def b8 : Nat := (· + {s}) 1\n"), "b8".into(), G + 1),
            (format!("def b9 : Nat → Nat := (fun y => y + {s}) ∘ (fun z => z)\n"), "b9 1".into(), G + 1),
            (format!("def b10 : List Nat → Nat\n  | (z+2) :: y => z + {s}\n  | _ => 7\n"), "b10 [3]".into(), G + 1),
            (format!("def b11 : Id Nat := do\n  let mut a := 0\n  let mut c := 0\n  (a, c) := (1, 2)\n  return a + {s}\n"), "b11.run".into(), G + 1),
            (format!("def b12 : Id Nat := do\n  let x := (← pure 5) + {s}\n  return x\n"), "b12.run".into(), G + 5),
            (format!("def b13 : Nat → Nat\n  | 0 => 0\n  | 1 => 1\n  | n+2 => b13 n + b13 (n+1) + {s}\n"), "b13 2".into(), G + 1),
        ];
        register(&mut env, &format!("def {s} : Nat := {G}\n"))
            .unwrap_or_else(|error| panic!("global {s}: {error}"));
        for (di, (source, call, expected)) in defs.iter().enumerate() {
            register(&mut env, source).unwrap_or_else(|error| panic!("{s}:\n{source}\n{error}"));
            let tag = format!("s{si}_d{di}");
            let good = format!("correct_{tag}");
            register(
                &mut env,
                &format!("theorem {good} : {call} = {expected} := rfl"),
            )
            .unwrap_or_else(|error| {
                panic!("global `{s}` not read: {call} = {expected}:\n{source}\n{error}")
            });
            checked += 1;
        }
    }
    assert_eq!(checked, SPELLINGS.len() * 14, "no case may be skipped");
}
