// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-registered computation checks for multi-argument equation defs.
//!
//! Each definition below is lowered by the multi-argument equation normalizer
//! (`elab_decl_value.rs`: `normalize_equation_def_multiarg` and its pattern
//! matrix). Before 2026-09-24 that lowering let `rfl` prove FALSE equations
//! that Lean 4.8.0 refuses, in four measured shapes:
//!
//! * a bare constructor ident (`none`) in a column whose domain is an
//!   application (`Option Nat`) was lifted as a BINDER, dropping the test;
//! * the same with a type abbreviation domain (`abbrev ON := Option Nat`);
//! * a bare constructor ident NESTED under a constructor (`some none`) was bound
//!   as a variable by the field-decomposition rule;
//! * a Nat literal beside `Nat.succ` (or an expanded `n + k`) and one
//!   constructor under two spellings (`some` / `Option.some`) were treated as
//!   disjoint heads, making a later arm unreachable.
//!
//! Every check registers the TRUE computation (must succeed, axiom-free) and
//! the FALSE one (must be refused, with nothing registered). The generated
//! battery at the end decides truth with an evaluator written here, not with
//! Clean.

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
    let bad = format!("incorrect_{tag}");
    let error = register(env, &format!("theorem {bad} : {call} = {wrong} := rfl"))
        .expect_err(&format!("FALSE theorem accepted: {call} = {wrong}"));
    assert!(
        !error.contains("parse error"),
        "negative must parse: {error}"
    );
    assert!(
        env.get_const(&Name::from_string(&bad)).is_none(),
        "false theorem registered: {call} = {wrong}"
    );
}

fn run(env: &mut Environment, prefix: &str, cases: &[(&str, u64, u64)]) {
    for (id, (call, expected, wrong)) in cases.iter().enumerate() {
        computation(env, &format!("{prefix}{id}"), call, *expected, *wrong);
    }
}

#[test]
fn bare_constructor_in_an_application_domain_is_a_test_not_a_binder() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def someNone : Option Nat → Option Nat → Nat
  | some _, none => 0
  | _, _ => 1
def noneSome : Option Nat → Option Nat → Nat
  | none, some _ => 0
  | _, _ => 1
def noneZero : Option (Option Nat) → Nat → Nat
  | none, 0 => 0
  | _, _ => 1
"#,
    )
    .unwrap();
    run(
        &mut env,
        "app",
        &[
            // The original false theorem: `someNone (some 5) (some 2) = 0`.
            ("someNone (some 5) (some 2)", 1, 0),
            ("someNone (some 5) none", 0, 1),
            ("someNone none none", 1, 0),
            ("noneSome (some 4) (some 5)", 1, 0),
            ("noneSome none (some 5)", 0, 1),
            ("noneSome none none", 1, 0),
            ("noneZero (some (some 4)) 0", 1, 0),
            ("noneZero none 0", 0, 1),
            ("noneZero none 3", 1, 0),
        ],
    );
}

#[test]
fn bare_constructor_under_an_abbreviation_domain_is_not_a_binder() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
abbrev ON := Option Nat
def aliased : ON → ON → Nat
  | some _, none => 0
  | _, _ => 1
"#,
    )
    .unwrap();
    run(
        &mut env,
        "alias",
        &[
            ("aliased (some 5) (some 2)", 1, 0),
            ("aliased (some 5) none", 0, 1),
            ("aliased none none", 1, 0),
        ],
    );
}

#[test]
fn nested_bare_constructor_is_not_a_field_binder() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def nestedNone : Option (Option Nat) → Nat → Nat
  | some _, 5 => 0
  | some none, 2 => 1
  | _, _ => 2
def nestedTrue : Option Bool → Bool → Nat
  | some true, false => 0
  | _, _ => 1
"#,
    )
    .unwrap();
    run(
        &mut env,
        "nested",
        &[
            ("nestedNone (some (some 1)) 5", 0, 2),
            ("nestedNone (some (some 1)) 2", 2, 1),
            ("nestedNone (some none) 2", 1, 2),
            ("nestedNone none 5", 2, 0),
            ("nestedTrue (some false) false", 1, 0),
            ("nestedTrue (some true) false", 0, 1),
        ],
    );
}

/// The recursive lowering has no general path to fall back to, so an unsettled
/// bare constructor is promoted to a constructor pattern there. Before
/// 2026-09-24 `recNested 1 (some (some 3)) = 0` was provable.
#[test]
fn recursive_defs_resolve_nested_and_abbreviated_constructors() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
abbrev ON := Option Nat
def recNested (k : Nat) (x : Option (Option Nat)) : Nat :=
  match k, x with
  | 0, some none => 0
  | 0, _ => 1
  | n + 1, y => recNested n y
def recAliased : Nat → ON → ON → Nat
  | 0, some _, none => 0
  | 0, _, _ => 1
  | n + 1, a, b => recAliased n a b
def recEqnNested : Nat → Option (Option Nat) → Nat
  | 0, some Option.none => 0
  | 0, some (some 4) => 1
  | 0, _ => 2
  | n + 1, y => recEqnNested n y
"#,
    )
    .unwrap();
    run(
        &mut env,
        "rec",
        &[
            ("recNested 1 (some (some 3))", 1, 0),
            ("recNested 1 (some none)", 0, 1),
            ("recNested 0 none", 1, 0),
            ("recAliased 2 (some 5) (some 2)", 1, 0),
            ("recAliased 2 (some 5) none", 0, 1),
            ("recEqnNested 3 (some (some 3))", 2, 0),
            ("recEqnNested 3 (some none)", 0, 2),
            ("recEqnNested 3 (some (some 4))", 1, 2),
        ],
    );
}

#[test]
fn literal_beside_succ_and_respelled_constructor_heads_overlap_correctly() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def litAfterSucc : Option Nat → Nat → Nat
  | some (Nat.succ (Nat.succ _)), 0 => 0
  | some 1, 0 => 1
  | _, _ => 2
def litBeforeSucc : Nat → Nat → Nat
  | 3, 1 => 0
  | Nat.succ _, 0 => 1
  | _, _ => 2
def respelled : Option Nat → Nat → Nat
  | some 5, 0 => 0
  | Option.some 6, 0 => 1
  | _, _ => 2
def recAdd : Nat → Option Nat → Nat
  | 0, some (x + 2) => x
  | 0, some 1 => 100
  | 0, _ => 200
  | fuel + 1, r => recAdd fuel r
def recBigLit : Nat → Option Nat → Nat
  | 0, some 300 => 0
  | 0, some (Nat.succ 7) => 1
  | 0, _ => 2
  | fuel + 1, r => recBigLit fuel r
"#,
    )
    .unwrap();
    run(
        &mut env,
        "overlap",
        &[
            ("litAfterSucc (some 1) 0", 1, 2),
            ("litAfterSucc (some 7) 0", 0, 2),
            ("litAfterSucc (some 0) 0", 2, 1),
            ("litBeforeSucc 3 0", 1, 2),
            ("litBeforeSucc 3 1", 0, 1),
            ("litBeforeSucc 0 0", 2, 1),
            ("respelled (some 6) 0", 1, 2),
            ("respelled (some 5) 0", 0, 1),
            ("recAdd 2 (some 1)", 100, 200),
            ("recAdd 1 (some 9)", 7, 200),
            ("recAdd 0 (some 0)", 200, 100),
            // A literal far above any succ tower in its column: unfolded one
            // layer, not refused and not expanded 300 deep.
            ("recBigLit 1 (some 300)", 0, 1),
            ("recBigLit 1 (some 8)", 1, 0),
            ("recBigLit 1 (some 7)", 2, 1),
            // `Nat.succ 7` is exactly 8, not "at least 8".
            ("recBigLit 1 (some 299)", 2, 1),
            ("recBigLit 1 (some 9)", 2, 1),
        ],
    );
}

// ---------------------------------------------------------------- battery

/// Column-0 pattern over `Option Nat`.
#[derive(Clone, Copy)]
enum P0 {
    Wild,
    None(&'static str),
    Some(&'static str, P1),
}

/// Pattern over `Nat`.
#[derive(Clone, Copy)]
enum P1 {
    Wild,
    Lit(u64),
    /// `Nat.succ` applied `k` times around a wildcard.
    Succ(u64),
    /// `x + k`.
    Add(u64),
}

/// `var` names the `n + k` binder. Each column gets its own: a pattern that
/// binds one name twice is non-linear, which Lean refuses (and so, since
/// 2026-09-25, does Clean) — this battery used to emit `some (x + 2), (x + 2)`.
fn p1_src(p: P1, var: &str) -> String {
    match p {
        P1::Wild => "_".into(),
        P1::Lit(k) => k.to_string(),
        P1::Succ(k) => {
            let mut s = "_".to_string();
            for _ in 0..k {
                s = format!("(Nat.succ {s})");
            }
            s
        }
        P1::Add(k) => format!("({var} + {k})"),
    }
}

fn p1_matches(p: P1, v: u64) -> bool {
    match p {
        P1::Wild => true,
        P1::Lit(k) => v == k,
        P1::Succ(k) | P1::Add(k) => v >= k,
    }
}

fn p0_src(p: P0) -> String {
    match p {
        P0::Wild => "_".into(),
        P0::None(spelling) => spelling.into(),
        P0::Some(spelling, inner) => format!("{spelling} {}", p1_src(inner, "x")),
    }
}

fn p0_matches(p: P0, v: Option<u64>) -> bool {
    match (p, v) {
        (P0::Wild, _) | (P0::None(_), None) => true,
        (P0::Some(_, inner), Some(x)) => p1_matches(inner, x),
        _ => false,
    }
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
}

fn gen_p1(rng: &mut Lcg) -> P1 {
    match rng.next(4) {
        0 => P1::Wild,
        1 => P1::Lit(rng.next(4)),
        2 => P1::Succ(1 + rng.next(2)),
        _ => P1::Add(1 + rng.next(2)),
    }
}

fn gen_p0(rng: &mut Lcg) -> P0 {
    const SOME: [&str; 3] = ["some", "Option.some", ".some"];
    const NONE: [&str; 2] = ["none", "Option.none"];
    match rng.next(5) {
        0 => P0::Wild,
        1 => P0::None(NONE[rng.next(2) as usize]),
        _ => P0::Some(SOME[rng.next(3) as usize], gen_p1(rng)),
    }
}

/// Whether some row of `arms` followed by the catch-all `_, _` is the first
/// match for no value. The generator's literals are below 4 and its offsets at
/// most 2, so `0..=4` stands for every `Nat` (each larger value matches
/// exactly the patterns 4 does) and the check is exact.
fn has_unreachable_row(arms: &[(P0, P1)]) -> bool {
    let nats = 0..=4u64;
    let options = std::iter::once(None).chain(nats.clone().map(Some));
    let mut reached = vec![false; arms.len() + 1];
    for v0 in options {
        for v1 in nats.clone() {
            let first = arms
                .iter()
                .position(|(a, b)| p0_matches(*a, v0) && p1_matches(*b, v1))
                .unwrap_or(arms.len());
            reached[first] = true;
        }
    }
    reached.contains(&false)
}

/// The equation source of a generated definition: `arms`, the catch-all, and
/// for the recursive form a fuel column and the recursive row.
fn generated_source(name: &str, arms: &[(P0, P1)], recursive: bool) -> String {
    let last = arms.len();
    let mut src = if recursive {
        format!("def {name} : Nat → Option Nat → Nat → Nat\n")
    } else {
        format!("def {name} : Option Nat → Nat → Nat\n")
    };
    let lead = if recursive { "0, " } else { "" };
    for (i, (a, b)) in arms.iter().enumerate() {
        src.push_str(&format!(
            "  | {lead}{}, {} => {i}\n",
            p0_src(*a),
            p1_src(*b, "y")
        ));
    }
    src.push_str(&format!("  | {lead}_, _ => {last}\n"));
    if recursive {
        src.push_str(&format!("  | fuel + 1, r, s => {name} fuel r s\n"));
    }
    src
}

/// Random multi-argument equation defs over `Option Nat → Nat → Nat`, both a
/// plain and a recursive (fuel-prefixed, extended-lowering) form, checked on
/// every input in a small domain against first-match semantics.
///
/// Only definitions Lean 4.8.0 accepts are measured: one with a row no value
/// reaches is "redundant alternative" there and has no value semantics to
/// compare. Each such candidate is still elaborated, and Clean's verdict is
/// checked, never skipped:
///
/// * refused: only as a redundant alternative, with nothing registered;
/// * accepted: only as ledger class (89) — a plain definition with at most
///   one STRUCTURAL column (a column some row matches on), which lowers
///   through a single-column match that builds no decision tree. Its value is
///   then checked on every input against first-match semantics, so that
///   lowering's meaning stays pinned. A recursive candidate (its fuel column
///   is structural) or one with two structural columns goes through the
///   equation matrix, which must refuse it (`2cd5d8d5c`).
///
/// At least one candidate must be refused as redundant, or the reason check
/// is vacuous.
#[test]
fn generated_two_column_battery_agrees_with_first_match_semantics() {
    let mut env = Environment::with_prelude();
    let mut rng = Lcg(0x5eed_2026_0924);
    let domain0: [Option<u64>; 5] = [None, Some(0), Some(1), Some(2), Some(5)];
    let domain1: [u64; 4] = [0, 1, 2, 5];
    let mut checked = 0usize;
    let mut redundant_candidates = 0usize;
    let mut refused_redundant = 0usize;
    for def_id in 0..24 {
        let recursive = def_id % 2 == 1;
        let arms: Vec<(P0, P1)> = loop {
            let arms: Vec<(P0, P1)> = (0..2 + rng.next(2))
                .map(|_| (gen_p0(&mut rng), gen_p1(&mut rng)))
                .collect();
            if !has_unreachable_row(&arms) {
                break arms;
            }
            let name = format!("redundant{redundant_candidates}");
            redundant_candidates += 1;
            let src = generated_source(&name, &arms, recursive);
            match register(&mut env, &src) {
                Err(error) => {
                    assert!(
                        error.contains("redundant alternative"),
                        "a definition with an unreachable row is refused only as Lean \
                         refuses it:\n{src}\n{error}"
                    );
                    assert!(
                        env.get_const(&Name::from_string(&name)).is_none(),
                        "refused yet registered:\n{src}"
                    );
                    refused_redundant += 1;
                }
                Ok(()) => {
                    assert!(
                        !recursive && structural_columns(&arms) <= 1,
                        "Lean refuses this (\"redundant alternative\") and it is not a \
                         ledger class (89) shape, so Clean must refuse it too:\n{src}"
                    );
                    class_89_first_match_values(&mut env, &name, &arms);
                }
            }
        };
        let last = arms.len() as u64;
        let name = format!("gen{def_id}");
        let src = generated_source(&name, &arms, recursive);
        register(&mut env, &src).unwrap_or_else(|error| panic!("{src}\n{error}"));
        // Four inputs per def, spread over the domain.
        for probe in 0..4 {
            let v0 = domain0[rng.next(domain0.len() as u64) as usize];
            let v1 = domain1[rng.next(domain1.len() as u64) as usize];
            let truth = arms
                .iter()
                .position(|(a, b)| p0_matches(*a, v0) && p1_matches(*b, v1))
                .map_or(last, |i| i as u64);
            let wrong = (truth + 1 + rng.next(last)) % (last + 1);
            let v0_src = match v0 {
                None => "(none : Option Nat)".to_string(),
                Some(x) => format!("(some {x})"),
            };
            let fuel = if recursive { "2 " } else { "" };
            let call = format!("{name} {fuel}{v0_src} {v1}");
            computation(&mut env, &format!("g{def_id}_{probe}"), &call, truth, wrong);
            checked += 1;
        }
    }
    assert_eq!(checked, 96, "the battery must not silently shrink");
    assert!(
        refused_redundant > 0,
        "no candidate with an unreachable row was refused as redundant \
         ({redundant_candidates} generated); the reason check above is vacuous"
    );
}

/// Columns some arm matches on (a constructor, literal or `n + k` pattern),
/// over the plain two-column form.
fn structural_columns(arms: &[(P0, P1)]) -> usize {
    usize::from(arms.iter().any(|(a, _)| !matches!(a, P0::Wild)))
        + usize::from(arms.iter().any(|(_, b)| !matches!(b, P1::Wild)))
}

/// An ACCEPTED candidate (ledger class (89)): Lean refuses it, but the
/// lowering Clean gives it must still be first-match, so every input of the
/// exact domain `has_unreachable_row` uses is checked, TRUE and FALSE.
fn class_89_first_match_values(env: &mut Environment, name: &str, arms: &[(P0, P1)]) {
    let last = arms.len() as u64;
    let options = std::iter::once(None).chain((0..=4u64).map(Some));
    for (i, v0) in options.enumerate() {
        for v1 in 0..=4u64 {
            let truth = arms
                .iter()
                .position(|(a, b)| p0_matches(*a, v0) && p1_matches(*b, v1))
                .map_or(last, |row| row as u64);
            let v0_src = match v0 {
                None => "(none : Option Nat)".to_string(),
                Some(x) => format!("(some {x})"),
            };
            let call = format!("{name} {v0_src} {v1}");
            let wrong = (truth + 1) % (last + 1);
            computation(env, &format!("{name}_{i}_{v1}"), &call, truth, wrong);
        }
    }
}

/// Ledger class (197). A constructor-application head whose short name
/// several inductives own (`succ`: `Nat.succ` and this file's `Tm.succ`) is
/// read by ordinary name resolution, as Lean reads it: inside `namespace Tm`
/// it is `Tm.succ`. The head canonicalization used to consult the environment
/// alone, found two `succ`s, and dropped any matrix with a column holding
/// `succ` by itself — here the second column under the `succ` arm. `same`
/// then died "`same` is the name being defined", and `bothSucc` (not
/// recursive) was left to a lowering the native path could not compile.
#[test]
fn a_head_several_inductives_own_resolves_through_the_namespace() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
inductive Tm where
  | lit : Nat → Tm
  | succ : Tm → Tm
namespace Tm
def same : Tm → Tm → Nat
  | lit m, lit n => m + n
  | succ a, succ b => same a b + 100
  | _, _ => 7
def bothSucc : Tm → Tm → Nat
  | succ _, succ _ => 1
  | _, _ => 0
def underSucc : Tm → Tm → Nat
  | succ (succ _), succ (lit n) => n
  | _, _ => 9
end Tm
"#,
    )
    .unwrap();
    run(
        &mut env,
        "shared",
        &[
            (
                "Tm.same (Tm.succ (Tm.succ (Tm.lit 1))) (Tm.succ (Tm.succ (Tm.lit 2)))",
                203,
                7,
            ),
            ("Tm.same (Tm.succ (Tm.lit 1)) (Tm.lit 1)", 7, 102),
            ("Tm.same (Tm.lit 4) (Tm.lit 5)", 9, 7),
            (
                "Tm.bothSucc (Tm.succ (Tm.lit 1)) (Tm.succ (Tm.lit 2))",
                1,
                0,
            ),
            ("Tm.bothSucc (Tm.succ (Tm.lit 1)) (Tm.lit 2)", 0, 1),
            ("Tm.bothSucc (Tm.lit 1) (Tm.succ (Tm.lit 2))", 0, 1),
            (
                "Tm.underSucc (Tm.succ (Tm.succ (Tm.lit 1))) (Tm.succ (Tm.lit 5))",
                5,
                9,
            ),
            (
                "Tm.underSucc (Tm.succ (Tm.lit 1)) (Tm.succ (Tm.lit 5))",
                9,
                5,
            ),
        ],
    );
}

/// NEGATIVE CONTROL for class (197): the namespace reading is the only one
/// taken. Inside `namespace Tm`, `succ n` over a `Nat` column is `Tm.succ n`
/// to Lean, which rejects the definition (v4.30.0-rc2: "Type mismatch:
/// n.succ has type Tm but is expected to have type Nat"). Reading the head by
/// the column's type instead would accept it as `Nat.succ`.
#[test]
fn the_namespace_reading_of_a_shared_head_is_refused_over_another_type() {
    let mut env = Environment::with_prelude();
    let error = register(
        &mut env,
        r#"
inductive Tm where
  | lit : Nat → Tm
  | succ : Tm → Tm
namespace Tm
def bad : Nat → Nat → Nat
  | succ n, succ _ => n
  | _, _ => 0
end Tm
"#,
    )
    .expect_err("Lean rejects `succ n` over Nat inside `namespace Tm`");
    assert!(
        error.contains("Tm.succ"),
        "the refusal must name the constructor the head resolved to: {error}"
    );
    assert!(
        env.get_const(&Name::from_string("Tm.bad")).is_none(),
        "a definition Lean rejects was registered"
    );
}
