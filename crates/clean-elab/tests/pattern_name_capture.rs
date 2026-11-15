// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Name capture in the equation / `match x, y` lowering, and non-linear
//! `let` / `if let` / do-block patterns: false theorems measured 2026-09-25
//! against Lean 4.8.0, and their fixes.
//!
//! * DEFERRED ROW BINDINGS. The pattern-matrix compiler re-bound a row's
//!   variable (`let x := <scrutinee>`) around the row body while it was
//!   still building the tree, so a later column's binding wrapped OUTSIDE an
//!   earlier one and captured the scrutinee name it read: `match a, b with |
//!   x, a+1 => v2 x a + x` became `let a := b._f0; let x := a; …`, and `v2 4
//!   1 = 100` was provable (Lean: 104). The bindings are now recorded per row
//!   and emitted all at once at the leaf, through unspellable temporaries when
//!   some variable is spelled like some source.
//! * FIELD BINDERS. A constructor field bound directly under a row's variable
//!   name was in scope for every row the arm keeps — also rows that bind
//!   nothing there, whose bodies meant a parameter or a global of that name:
//!   `| c+1, 0 => … | _, _ => c` returned the field.
//! * LIFTED BINDERS. An equation column that some arm names and another arm
//!   leaves `_` was lifted under the arm's variable name, shadowing a global
//!   in the `_` arm: `def y := 7; | 0, y => y | n+1, _ => y` gave `k 1 5 = 5`.
//! * NON-LINEAR `let (x, x)`, `let (x, _, x)`, `if let some (x, x)` and
//!   do-block `let (x, x)` / `match` kept one of the bindings (Lean refuses
//!   them all).
//!
//! Every value below was measured with Lean 4.8.0 (`#eval`). Where the
//! previous Clean computed a wrong value, the WRONG value of the computation
//! is exactly that one (Clean's own reduct, not `truth + 1`), and each is
//! refused by `rfl` and by `decide`. The generated battery at the end decides
//! truth with a first-match evaluator written here.

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

/// `call = expected` must register axiom-free; `call = wrong` must be refused.
fn computation(env: &mut Environment, tag: &str, call: &str, expected: u64, wrong: u64) {
    assert_ne!(
        expected, wrong,
        "{tag}: a check needs a genuinely wrong value"
    );
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
    refused(env, tag, call, wrong);
}

/// `call = wrong` must be refused, by `rfl` and by `decide`, and leave nothing
/// registered.
fn refused(env: &mut Environment, tag: &str, call: &str, wrong: u64) {
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

fn run(env: &mut Environment, prefix: &str, cases: &[(&str, u64, u64)]) {
    for (id, (call, expected, wrong)) in cases.iter().enumerate() {
        computation(env, &format!("{prefix}{id}"), call, *expected, *wrong);
    }
}

/// A declaration that must be refused, with `needle` in the error; nothing
/// named `name` may be registered.
fn refused_decl(env: &mut Environment, name: &str, source: &str, needle: &str) {
    let error = register(env, source).expect_err(&format!("must be refused:\n{source}"));
    assert!(
        error.contains(needle),
        "{name}: refused for the wrong reason (want `{needle}`): {error}"
    );
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "{name} was registered although refused"
    );
}

#[test]
fn a_later_column_binding_does_not_capture_an_earlier_columns_scrutinee() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def v2 (a b : Nat) : Nat := match a, b with
  | x, a+1 => v2 x a + x
  | _, _ => 100
def v5 (a b : Nat) : Nat := match b, a with
  | a+1, b => v5 b a + b
  | _, _ => 100
def p (a b : Nat) : Nat :=
  match a, b with
  | a, 2 => a
  | b, a+1 => p b a + b
  | _, _ => 100
def p2 (a b : Nat) : Nat :=
  match a, b with
  | b, a+1 => p2 b a + b
  | _, _ => 100
def gg (a b : Nat) : Nat :=
  match a, b with
  | a, 2 => a
  | b, a+1 => gg b a + b
  | _, _ => b
def v7 (n a : Nat) : Nat := match a, n with
  | n, a+1 => v7 a (n * 2) + n
  | _, _ => 100
"#,
    )
    .unwrap();
    run(
        &mut env,
        "swap",
        &[
            // Previous Clean: 100, 101, 103, 103 (Lean: 104, 108, 121, 100).
            ("v2 4 1", 104, 100),
            ("v2 4 2", 108, 101),
            ("v2 7 3", 121, 103),
            ("v2 0 3", 100, 103),
            ("v5 4 1", 104, 100),
            // `p` was refused before 0ffcbd885 and accepted with `100` by it.
            ("p 4 1", 104, 100),
            ("p 2 4", 6, 7),
            ("p2 4 1", 104, 100),
            ("gg 4 1", 4, 0),
            ("gg 2 4", 6, 7),
            ("v7 2 3", 109, 100),
        ],
    );
}

#[test]
fn a_field_binder_is_not_in_scope_for_rows_that_do_not_bind_it() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def g (a b c : Nat) : Nat := match a, b with
  | c+1, 0 => g c 0 7 + 1
  | _, _ => c
def cc : Nat := 50
def h : Nat → Nat → Nat
  | cc+1, 0 => h cc 0 + 1
  | _, _ => cc
"#,
    )
    .unwrap();
    run(
        &mut env,
        "field",
        &[
            // Previous Clean: `2` for `g 3 1 5` and `h 3 1` (the field of `3`).
            ("g 3 1 5", 5, 2),
            ("g 3 0 5", 10, 11),
            ("h 3 1", 50, 2),
            ("h 3 0", 53, 5),
        ],
    );
}

#[test]
fn a_lifted_column_binder_does_not_shadow_a_global_in_a_wildcard_arm() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def y : Nat := 7
def k : Nat → Nat → Nat
  | 0, y => y
  | n+1, _ => y
def k2 : Nat → Nat → Nat
  | 0, y => y
  | n+1, _ => k2 n 3 + y
def k3 : Nat → Nat → Nat → Nat
  | 0, y, _ => y
  | n+1, _, acc => k3 n acc (acc + 1) + y
"#,
    )
    .unwrap();
    run(
        &mut env,
        "lift",
        &[
            // Previous Clean: `5` and `8`.
            ("k 1 5", 7, 5),
            ("k 0 5", 5, 7),
            ("k2 1 5", 10, 8),
            ("k2 0 5", 5, 7),
            ("k3 2 9 4", 19, 9),
        ],
    );
}

#[test]
fn lowering_keeps_structural_recursion_through_the_row_bindings() {
    // Capability controls: rows that bind a recursion field or a fixed
    // column under their own names still lower structurally.
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def zipSum : List Nat → List Nat → Nat
  | x :: xs, y :: ys => x + y + zipSum xs ys
  | _, _ => 0
def addAll : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, n => x + n + addAll xs n
def acc3 : List Nat → Nat → Nat → Nat
  | [], _, acc => acc
  | x :: xs, n, acc => acc3 xs n (acc + x * n)
def sw (a b : Nat) : Nat :=
  match a, b with
  | b, a+1 => sw (b + 1) a + b
  | _, _ => 100
"#,
    )
    .unwrap();
    run(
        &mut env,
        "cap",
        &[
            ("zipSum [1, 2, 3] [10, 20]", 33, 0),
            ("addAll [1, 2] 5", 13, 0),
            ("acc3 [1, 2, 3] 2 0", 12, 0),
            ("sw 4 2", 109, 100),
        ],
    );
}

#[test]
fn non_linear_let_if_let_and_do_patterns_are_refused() {
    let mut env = Environment::with_prelude();
    const NONLINEAR: &str = "occurred more than once";
    // Each was accepted, with one binding silently kept; Lean 4.8.0 refuses
    // every one ("variable `x` occurred more than once").
    for (name, source) in [
        (
            "k1",
            "theorem k1 : (let (x, x) := ((1 : Nat), (2 : Nat)); x) = 2 := rfl",
        ),
        ("n7", "def n7 (p : Nat × Nat) : Nat := let (x, x) := p; x"),
        (
            "k4",
            "def k4 (p : Nat × Nat × Nat) : Nat := let (x, _, x) := p; x",
        ),
        (
            "k5",
            "def k5 (p : Option (Nat × Nat)) : Nat := if let some (x, x) := p then x else 0",
        ),
        (
            "k6",
            "def k6 (p : Nat × Nat) : Nat := Id.run do\n  let (x, x) := p\n  return x",
        ),
        (
            "m3",
            "def m3 (p : Nat × Nat) : Id Nat := do\n  let (x, x) ← pure p\n  return x",
        ),
        (
            "m4",
            "def m4 (p : Nat × Nat) : Nat := Id.run do\n  match p with\n  | (x, x) => return x",
        ),
    ] {
        refused_decl(&mut env, name, source, NONLINEAR);
    }
    // Linear spellings of the same shapes are unaffected.
    register(
        &mut env,
        r#"
def l1 (p : Nat × Nat) : Nat := let (x, y) := p; x * 10 + y
def l2 (p : Nat × Nat × Nat) : Nat := let (x, _, z) := p; x * 10 + z
def l3 (p : Option (Nat × Nat)) : Nat := if let some (x, y) := p then x * 10 + y else 0
def l4 (p : Nat × Nat) : Nat := Id.run do
  let (x, y) := p
  return x * 10 + y
def l5 (p : Nat × Nat) : Nat := let (_, _) := p; 3
"#,
    )
    .unwrap();
    run(
        &mut env,
        "lin",
        &[
            ("l1 (1, 2)", 12, 21),
            ("l2 (1, 2, 3)", 13, 12),
            ("l3 (some (1, 2))", 12, 0),
            ("l4 (1, 2)", 12, 21),
            ("l5 (1, 2)", 3, 0),
        ],
    );
}

/// Deterministic generator (no external crates).
struct Lcg(u64);
impl Lcg {
    fn next(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) % n
    }
    fn pick<'a>(&mut self, xs: &[&'a str]) -> &'a str {
        xs[self.next(xs.len() as u64) as usize]
    }
}

/// Names shared by parameters, pattern variables and globals.
const POOL: &[&str] = &["a", "b", "c", "x", "y", "g"];
const PARAMS: &[&str] = &["a", "b", "c"];
const G: u64 = 50;

#[derive(Clone)]
enum Pat {
    Var(&'static str),
    Wild,
    Lit(u64),
    Succ(&'static str),
}

struct Row {
    pats: Vec<Pat>,
    /// Summands: a name (resolved in the row's scope) or a constant.
    terms: Vec<Result<&'static str, u64>>,
    /// Self-call arguments, by parameter position: a name or a constant.
    call: Option<Vec<Result<&'static str, u64>>>,
}

fn bind(p: &Pat, value: u64) -> Option<Option<(&'static str, u64)>> {
    match p {
        Pat::Var(n) => Some(Some((n, value))),
        Pat::Wild => Some(None),
        Pat::Lit(k) => (value == *k).then_some(None),
        Pat::Succ(n) => (value >= 1).then(|| Some((*n, value - 1))),
    }
}

/// First-match evaluation with Lean's scoping: a row's variables shadow the
/// parameters (match form) and the global `g`; nothing else is in scope.
fn eval(
    rows: &[Row],
    cols: &[usize],
    match_form: bool,
    args: &[u64],
    fuel: &mut u32,
) -> Option<u64> {
    *fuel = fuel.checked_sub(1)?;
    for row in rows {
        let mut scope: Vec<(&str, u64)> = vec![("g", G)];
        if match_form {
            scope.extend(PARAMS.iter().copied().zip(args.iter().copied()));
        }
        let mut ok = true;
        let mut binds = Vec::new();
        for (p, &col) in row.pats.iter().zip(cols) {
            match bind(p, args[col]) {
                None => {
                    ok = false;
                    break;
                }
                Some(Some(b)) => binds.push(b),
                Some(None) => {}
            }
        }
        if !ok {
            continue;
        }
        scope.extend(binds);
        let lookup = |n: &str| scope.iter().rev().find(|(m, _)| *m == n).map(|(_, v)| *v);
        let val = |t: &Result<&str, u64>| match t {
            Ok(n) => lookup(n),
            Err(k) => Some(*k),
        };
        let mut sum = 0;
        for t in &row.terms {
            sum += val(t)?;
        }
        if let Some(call) = &row.call {
            let vals: Option<Vec<u64>> = call.iter().map(val).collect();
            sum += eval(rows, cols, match_form, &vals?, fuel)?;
        }
        return Some(sum);
    }
    None
}

fn pat_src(p: &Pat) -> String {
    match p {
        Pat::Var(n) => n.to_string(),
        Pat::Wild => "_".into(),
        Pat::Lit(k) => k.to_string(),
        Pat::Succ(n) => format!("{n}+1"),
    }
}

fn term_src(t: &Result<&str, u64>) -> String {
    match t {
        Ok(n) => n.to_string(),
        Err(k) => k.to_string(),
    }
}

/// Recursive and non-recursive definitions, in `match` form over parameters
/// `a b c` (columns in any order) and in equation form, whose pattern
/// variables, parameters, the global `g` and the self-call arguments share
/// one pool of names. A definition may be refused (loudly), but every
/// accepted one must compute the evaluator's value on every probe — so its
/// value is Lean's, and any other stated value is false.
#[test]
fn generated_name_collision_battery_agrees_with_lean_scoping() {
    let mut env = Environment::with_prelude();
    register(&mut env, &format!("def g : Nat := {G}")).unwrap();
    let mut rng = Lcg(0x5eed_2026_0926);
    let (mut accepted_defs, mut checked) = (0usize, 0usize);
    let mut def_id = 0;
    // `PATTERN_BATTERY_DUMP=<file>` writes every accepted definition and its
    // probes as `#eval`s, to re-check the evaluator against Lean 4.8.0.
    let mut dump = format!("def g : Nat := {G}\n");
    while def_id < 200 {
        let match_form = rng.next(3) != 0;
        let ncols = 2 + rng.next(2) as usize;
        // Column i scrutinizes argument cols[i].
        let cols: Vec<usize> = if match_form {
            let mut all = vec![0, 1, 2];
            let mut out = Vec::new();
            for _ in 0..ncols {
                out.push(all.remove(rng.next(all.len() as u64) as usize));
            }
            out
        } else {
            (0..ncols).collect()
        };
        let arity = if match_form { 3 } else { ncols };
        let recursive_row = if rng.next(10) < 7 {
            Some(rng.next(2) as usize)
        } else {
            None
        };
        let nrows = 1 + rng.next(2) as usize;
        let mut rows = Vec::new();
        for r in 0..nrows {
            let dec = (recursive_row == Some(r)).then(|| rng.next(ncols as u64) as usize);
            let mut pats = Vec::new();
            let mut bound: Vec<&str> = Vec::new();
            for col in 0..ncols {
                let fresh = |rng: &mut Lcg, bound: &[&str]| -> Option<&'static str> {
                    let n = rng.pick(POOL);
                    (!bound.contains(&n)).then_some(n)
                };
                let p = if Some(col) == dec {
                    match fresh(&mut rng, &bound) {
                        Some(n) => Pat::Succ(n),
                        None => Pat::Succ("x"),
                    }
                } else {
                    match rng.next(4) {
                        0 => fresh(&mut rng, &bound).map_or(Pat::Wild, Pat::Succ),
                        1 => fresh(&mut rng, &bound).map_or(Pat::Wild, Pat::Var),
                        2 => Pat::Wild,
                        _ => Pat::Lit(rng.next(3)),
                    }
                };
                if let Pat::Var(n) | Pat::Succ(n) = p {
                    bound.push(n);
                }
                pats.push(p);
            }
            let linear = bound
                .iter()
                .enumerate()
                .all(|(i, n)| !bound[..i].contains(n));
            if !linear || pats.iter().all(|p| matches!(p, Pat::Wild | Pat::Var(_))) {
                pats[0] = Pat::Lit(rng.next(3));
            }
            let mut visible: Vec<&'static str> = vec!["g"];
            if match_form {
                visible.extend(PARAMS);
            }
            for p in &pats {
                if let Pat::Var(n) | Pat::Succ(n) = p {
                    visible.push(n);
                }
            }
            let mut terms = vec![Ok(rng.pick(&visible))];
            terms.push(Err(rng.next(10)));
            let call = dec.and_then(|d| {
                let Pat::Succ(field) = pats[d] else {
                    return None;
                };
                Some(
                    (0..arity)
                        .map(|pos| {
                            if pos == cols[d] {
                                Ok(field)
                            } else if rng.next(4) == 0 {
                                Err(rng.next(3))
                            } else {
                                Ok(rng.pick(&visible))
                            }
                        })
                        .collect(),
                )
            });
            rows.push(Row { pats, terms, call });
        }
        rows.push(Row {
            pats: vec![Pat::Wild; ncols],
            terms: vec![Err(100 + rng.next(10))],
            call: None,
        });
        // A repeated variable after the rewrite above, or an unreachable row,
        // makes Lean refuse the definition: skip those shapes.
        let nonlinear = rows.iter().any(|r| {
            let names: Vec<&str> = r
                .pats
                .iter()
                .filter_map(|p| match p {
                    Pat::Var(n) | Pat::Succ(n) => Some(*n),
                    _ => None,
                })
                .collect();
            names
                .iter()
                .enumerate()
                .any(|(i, n)| names[..i].contains(n))
        });
        let mut reached = vec![false; rows.len()];
        for v in 0..6u64.pow(ncols as u32) {
            let vals: Vec<u64> = (0..ncols).map(|i| v / 6u64.pow(i as u32) % 6).collect();
            if let Some(r) = rows.iter().position(|row| {
                row.pats
                    .iter()
                    .zip(&vals)
                    .all(|(p, &x)| bind(p, x).is_some())
            }) {
                reached[r] = true;
            }
        }
        if nonlinear || reached.contains(&false) {
            continue;
        }
        let name = format!("nc{def_id}");
        def_id += 1;
        let mut src = if match_form {
            let scruts: Vec<&str> = cols.iter().map(|&c| PARAMS[c]).collect();
            format!(
                "def {name} (a b c : Nat) : Nat :=\n  match {} with\n",
                scruts.join(", ")
            )
        } else {
            format!("def {name} : {}Nat\n", "Nat → ".repeat(ncols))
        };
        for row in &rows {
            let pats: Vec<String> = row.pats.iter().map(pat_src).collect();
            let mut body: Vec<String> = row.terms.iter().map(term_src).collect();
            if let Some(call) = &row.call {
                let args: Vec<String> = call.iter().map(term_src).collect();
                body.push(format!("{name} {}", args.join(" ")));
            }
            src.push_str(&format!(
                "  | {} => {}\n",
                pats.join(", "),
                body.join(" + ")
            ));
        }
        if register(&mut env, &src).is_err() {
            assert!(env.get_const(&Name::from_string(&name)).is_none(), "{src}");
            continue;
        }
        accepted_defs += 1;
        dump.push_str(&src);
        for probe in 0..4 {
            let args: Vec<u64> = (0..arity).map(|_| rng.next(5)).collect();
            let mut fuel = 10_000;
            let truth = eval(&rows, &cols, match_form, &args, &mut fuel)
                .unwrap_or_else(|| panic!("evaluator ran out of fuel:\n{src}"));
            let call = format!(
                "{name} {}",
                args.iter()
                    .map(u64::to_string)
                    .collect::<Vec<_>>()
                    .join(" ")
            );
            dump.push_str(&format!("#eval (\"{call}\", {call}, {truth})\n"));
            let good = format!("correct_{name}_{probe}");
            register(
                &mut env,
                &format!("theorem {good} : {call} = {truth} := rfl"),
            )
            .unwrap_or_else(|error| panic!("{src}\n{call} = {truth} must hold: {error}"));
            let bad = format!("incorrect_{name}_{probe}");
            register(
                &mut env,
                &format!("theorem {bad} : {call} = {} := rfl", truth + 1),
            )
            .expect_err(&format!(
                "{src}\nFALSE theorem accepted: {call} = {}",
                truth + 1
            ));
            checked += 1;
        }
    }
    // SELF-SKIP OK: opt-in PATTERN_BATTERY_DUMP env var only writes a diagnostic dump; every battery assertion and the non-vacuity floor run unconditionally.
    if let Ok(path) = std::env::var("PATTERN_BATTERY_DUMP") {
        std::fs::write(path, dump).expect("write the battery dump");
    }
    eprintln!("name-collision battery: {accepted_defs} definitions accepted, {checked} probes");
    // Non-vacuity: most definitions lower, so the checks above have teeth.
    assert!(
        accepted_defs >= 120 && checked >= 480,
        "battery too small to mean anything: {accepted_defs} definitions / {checked} probes"
    );
}
