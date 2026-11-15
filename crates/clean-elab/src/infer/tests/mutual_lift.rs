// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Gap G23 / ledger class (92): a `mutual` block of definitions or theorems
//! recursing over a NESTED inductive, lifted onto the family's shared
//! recursor (`infer/mutual_lift/`, design
//! `designs/2026-10-08-mutual-nested-recursion.md`), through the production
//! entry `elaborate_decl_and_register`.
//!
//! Every fixture is a whole Lean file under `tests/fixtures/mutual_nested/`
//! whose pinned Lean verdicts — v4.8.0, trust-ir's toolchain, and v4.30.0-rc2,
//! the reference of docs/DECISIONS.md R2 — `scripts/mutual_nested_verdicts.py`
//! re-derived into `verdicts.json`. Clean agrees with v4.30.0-rc2 on every
//! fixture. Against v4.8.0 it widens on purpose: its structural members reduce
//! on open terms where Lean 4.8's well-founded ones do not (Lean >= 4.12
//! compiles these blocks structurally too; recorded in docs/DECISIONS.md).
//! Every widening carries a false twin all three refuse.

use super::*;
use clean_kernel::env::Environment;

const VERDICTS: &str = include_str!("../../../../../tests/fixtures/mutual_nested/verdicts.json");

macro_rules! fixture {
    ($name:literal) => {
        (
            $name,
            include_str!(concat!(
                "../../../../../tests/fixtures/mutual_nested/",
                $name
            )),
        )
    };
}
pub(super) use fixture;

/// The pinned verdict of `fixture` under `version` (`lean_4_8_0`,
/// `lean_4_30_0_rc2`): `true` when accepted.
pub(super) fn lean_verdict(fixture: &str, version: &str) -> bool {
    let verdicts: serde_json::Value = serde_json::from_str(VERDICTS).expect("verdicts.json parses");
    match verdicts["fixtures"][fixture][version].as_str() {
        Some("accepted") => true,
        Some("refused") => false,
        other => panic!("no pinned {version} verdict for {fixture}: {other:?}"),
    }
}

/// Both pinned Leans give the same verdict, returned.
pub(super) fn lean_accepts(fixture: &str) -> bool {
    let old = lean_verdict(fixture, "lean_4_8_0");
    assert_eq!(
        old,
        lean_verdict(fixture, "lean_4_30_0_rc2"),
        "{fixture}: the pinned Leans disagree; use `widening`"
    );
    old
}

/// A recorded widening: Lean 4.8.0 refuses, Lean 4.30.0-rc2 accepts.
pub(super) fn assert_widening(fixture: &str) {
    assert!(
        !lean_verdict(fixture, "lean_4_8_0"),
        "{fixture}: Lean 4.8.0 refuses it"
    );
    assert!(
        lean_verdict(fixture, "lean_4_30_0_rc2"),
        "{fixture}: Lean 4.30.0-rc2 accepts it"
    );
}

/// Register every declaration of `src` in order; the per-declaration outcomes.
pub(super) fn run_file(env: &mut Environment, src: &str) -> Vec<Result<(), String>> {
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    let decls = clean_parser::parse_file_with_tactics(src, &patterns).expect("fixture parses");
    decls
        .iter()
        .map(|decl| {
            crate::elaborate_decl_and_register(env, decl)
                .map_err(|err| format!("{err}"))
                .and_then(|result| {
                    let mut leaves = Vec::new();
                    result.leaf_decls(&mut leaves);
                    match leaves.iter().find_map(|leaf| match leaf {
                        ElabResult::Failed { error, .. } => Some(error.to_string()),
                        _ => None,
                    }) {
                        Some(error) => Err(error),
                        None => Ok(()),
                    }
                })
        })
        .collect()
}

pub(super) fn fresh() -> Environment {
    Environment::with_prelude()
}

pub(super) fn registered(env: &Environment, name: &str) -> bool {
    env.get_const(&Name::from_string(name)).is_some()
}

/// Every declaration of the fixture registered.
pub(super) fn accepts_all(env: &mut Environment, fixture: (&str, &str)) {
    let outcomes = run_file(env, fixture.1);
    for (i, outcome) in outcomes.iter().enumerate() {
        if let Err(err) = outcome {
            panic!("{}: declaration {i} must register: {err}", fixture.0);
        }
    }
}

/// Everything but the LAST declaration registered; the last is refused.
pub(super) fn refuses_last(env: &mut Environment, fixture: (&str, &str), last: &str) -> String {
    let outcomes = run_file(env, fixture.1);
    let (tail, init) = outcomes.split_last().expect("fixture has declarations");
    for (i, outcome) in init.iter().enumerate() {
        if let Err(err) = outcome {
            panic!("{}: declaration {i} must register: {err}", fixture.0);
        }
    }
    let err = match tail {
        Ok(()) => panic!("{}: the false claim `{last}` must be refused", fixture.0),
        Err(err) => err.clone(),
    };
    assert!(
        !registered(env, last),
        "a refused `{last}` must not be registered"
    );
    err
}

/// The value of `name` and the constants it mentions.
pub(super) fn value_constants(env: &Environment, name: &str) -> std::collections::HashSet<Name> {
    env.get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .unwrap_or_else(|| panic!("`{name}` has a value"))
        .collect_constants()
}

/// The lifted value names its family recursor and none of its block's
/// members, and its axiom census is exactly the union of what it uses.
pub(super) fn assert_lifted(env: &mut Environment, block: &[&str], recursor_prefix: &str) {
    for member in block {
        let consts = value_constants(env, member);
        for other in block {
            assert!(
                !consts.contains(&Name::from_string(other)),
                "`{member}`'s value must not name the block member `{other}`"
            );
        }
        assert!(
            consts
                .iter()
                .any(|c| c.to_string().starts_with(recursor_prefix)),
            "`{member}` must be a `{recursor_prefix}*` application: {consts:?}"
        );
        let own = crate::print_axioms::collect_axioms(env, &Name::from_string(member))
            .expect("census of a lifted member");
        let mut used: Vec<Name> = Vec::new();
        for c in &consts {
            for axiom in crate::print_axioms::collect_axioms(env, c).expect("census") {
                if !used.contains(&axiom) {
                    used.push(axiom);
                }
            }
        }
        for axiom in &own {
            assert!(
                used.contains(axiom),
                "lifting `{member}` added the axiom `{axiom}`"
            );
        }
        let entry = env
            .get_ext_state_or_init::<crate::MutualLiftState>(crate::mutual_lift_idx())
            .and_then(|state| state.get(&Name::from_string(member)).cloned())
            .unwrap_or_else(|| panic!("`{member}` has a registry entry"));
        assert!(entry.recursor.to_string().starts_with(recursor_prefix));
        assert_eq!(entry.block.len(), block.len());
    }
}

/// Refused by the lift, naming the call, and nothing of the block registered.
pub(super) fn refused_by_lift(
    env: &mut Environment,
    fixture: (&str, &str),
    block: &[&str],
    callee: &str,
) {
    assert!(
        !lean_accepts(fixture.0),
        "{} is a Lean-refused control",
        fixture.0
    );
    let outcomes = run_file(env, fixture.1);
    let err = outcomes
        .iter()
        .find_map(|o| o.as_ref().err())
        .unwrap_or_else(|| panic!("{} must be refused", fixture.0))
        .clone();
    assert!(
        err.contains("mutual structural recursion") && err.contains("cannot be lowered"),
        "{}: refused by the lift, not by the kernel: {err}",
        fixture.0
    );
    assert!(
        err.contains(callee),
        "{}: the message names `{callee}`: {err}",
        fixture.0
    );
    assert!(!err.contains("Unknown constant"), "{err}");
    for member in block {
        assert!(
            !registered(env, member),
            "`{member}` must not be registered"
        );
    }
}

#[test]
fn test_mutual_lift_nested_beq_repro_decide_accepted() {
    let fixture = fixture!("repro.lean");
    assert!(lean_accepts(fixture.0));
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    assert!(registered(&env, "t1"));
    assert_lifted(&mut env, &["P.beq", "P.listBeq"], "P.rec");
}

#[test]
fn test_mutual_lift_nested_beq_repro_twin_refused() {
    let fixture = fixture!("repro_twin.lean");
    assert!(!lean_accepts(fixture.0));
    let mut env = fresh();
    let err = refuses_last(&mut env, fixture, "t1_twin");
    assert!(
        err.contains("decide"),
        "refused by `decide` evaluating false: {err}"
    );
}

#[test]
fn test_mutual_lift_nested_decide_two_levels() {
    let fixture = fixture!("decide_nested.lean");
    assert!(lean_accepts(fixture.0));
    accepts_all(&mut fresh(), fixture);
    let twin = fixture!("decide_nested_twin.lean");
    assert!(!lean_accepts(twin.0));
    refuses_last(&mut fresh(), twin, "d2f");
}

/// Widening (docs/DECISIONS.md): Lean 4.8 refuses `w1` only because its
/// well-founded members do not reduce on open terms; Lean 4.30 accepts it.
#[test]
fn test_mutual_lift_open_rfl_widening_with_false_twin() {
    let fixture = fixture!("rfl_open_widening.lean");
    assert_widening(fixture.0);
    accepts_all(&mut fresh(), fixture);
    let twin = fixture!("rfl_open_widening_twin.lean");
    assert!(!lean_accepts(twin.0));
    refuses_last(&mut fresh(), twin, "w1f");
}

/// Block 10: the major premise is `c`, the parameter the source matches, not
/// `ty` (also structural).
#[test]
fn test_mutual_lift_major_is_matched_second_parameter() {
    let fixture = fixture!("width_ambiguous.lean");
    assert!(lean_accepts(fixture.0));
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    assert_lifted(
        &mut env,
        &["constWidthAmbiguous", "constFieldsAmbiguous"],
        "C.rec",
    );
    let state = env
        .get_ext_state_or_init::<crate::MutualLiftState>(crate::mutual_lift_idx())
        .expect("registry");
    let width = state
        .get(&Name::from_string("constWidthAmbiguous"))
        .expect("entry");
    assert_eq!(width.major_param, 1, "recursion on `c`");
    assert_eq!(width.rest_params, vec![0]);
    let fields = state
        .get(&Name::from_string("constFieldsAmbiguous"))
        .expect("entry");
    assert_eq!(fields.major_param, 1, "recursion on the `List C` column");
    let twin = fixture!("width_ambiguous_twin.lean");
    assert!(!lean_accepts(twin.0));
    refuses_last(&mut fresh(), twin, "a3_twin");
}

/// Blocks 4-6: fixed parameters `σ η`, calls under `Option.bind` lambdas,
/// members with different codomains.
#[test]
fn test_mutual_lift_template_slice_fixed_params() {
    let fixture = fixture!("template_slice.lean");
    assert!(lean_accepts(fixture.0));
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    assert_lifted(&mut env, &["substTy", "substTys"], "TemplateTy.rec");
    assert_lifted(&mut env, &["embed", "embeds"], "Ty.rec");
    assert_lifted(&mut env, &["refsOk", "refsOks"], "TemplateTy.rec");
    let state = env
        .get_ext_state_or_init::<crate::MutualLiftState>(crate::mutual_lift_idx())
        .expect("registry");
    for member in ["substTy", "substTys", "refsOk", "refsOks"] {
        let entry = state.get(&Name::from_string(member)).expect("entry");
        assert_eq!(entry.fixed_arity, 2, "`{member}` keeps `σ η` fixed");
        assert_eq!(entry.major_param, 2);
    }
    for (twin, last) in [
        (fixture!("template_slice_twin.lean"), "ok1_twin"),
        (fixture!("template_slice_subst_twin.lean"), "sub1_twin"),
    ] {
        assert!(!lean_accepts(twin.0));
        refuses_last(&mut fresh(), twin, last);
    }
}

/// Non-recursive blocks register in dependency order.
#[test]
fn test_mutual_lift_nonrecursive_blocks_dependency_order() {
    let fixture = fixture!("nonrec_order.lean");
    assert!(lean_accepts(fixture.0));
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    for name in ["twoA", "twoB", "useLater", "later", "useLater_eq"] {
        assert!(registered(&env, name), "`{name}` registered");
    }
    let twin = fixture!("nonrec_order_twin.lean");
    assert!(!lean_accepts(twin.0));
    refuses_last(&mut fresh(), twin, "useLater_eq");
}

/// Mutual theorems by term arms (sibling calls inside a `by` block):
/// accepted as a widening; its non-structural twin refused by the lift.
#[test]
fn test_mutual_lift_theorem_arms_widening_and_nonstructural_twin() {
    let fixture = fixture!("theorem_arms_widening.lean");
    assert_widening(fixture.0);
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    assert_lifted(&mut env, &["P.beq_refl", "P.listBeq_refl"], "P.rec");
    // `P.listBeq_refl xs.reverse` does not even have the arm's type: Lean
    // 4.8.0 and 4.30.0-rc2 refuse it with a type mismatch, and so does Clean,
    // before the lift.
    let twin = fixture!("theorem_arms_nonstruct.lean");
    assert!(!lean_accepts(twin.0));
    let mut env = fresh();
    let outcomes = run_file(&mut env, twin.1);
    let err = outcomes
        .iter()
        .find_map(|o| o.as_ref().err())
        .expect("the non-structural theorem block is refused")
        .clone();
    assert!(
        err.contains("Match arm") && err.contains("List.reverse"),
        "{err}"
    );
    for member in ["P.beq_refl", "P.listBeq_refl"] {
        assert!(
            !registered(&env, member),
            "`{member}` must not be registered"
        );
    }
}

#[test]
fn test_mutual_lift_refuses_non_subterm_argument() {
    refused_by_lift(
        &mut fresh(),
        fixture!("neg_nonstruct.lean"),
        &["P.f", "P.g"],
        "P.g",
    );
}

#[test]
fn test_mutual_lift_refuses_rebuilt_major_premise() {
    refused_by_lift(
        &mut fresh(),
        fixture!("neg_cycle.lean"),
        &["P.f", "P.g"],
        "P.f",
    );
}

/// lean4 `tests/elab_fail/mutwftypemismatch.lean`: Lean refuses a `mutual`
/// block whose `termination_by` measures have different types, which the
/// structural lift alone would accept (`infer/elab_mutual_measures.rs`).
#[test]
fn test_mutual_measures_of_different_types_are_refused() {
    const NAT_AND_PROP: &str = "
mutual
def foo : Nat → Nat
 | 0   => 1
 | n+1 => bar n
termination_by n => n

def bar : Nat → Nat
 | 0   => 1
 | n+1 => foo n
termination_by n => n > 2
end
";
    const NAT_AND_FIN: &str = "
mutual
def foo (fixed : Nat) : Nat → Nat
 | 0   => 1
 | n+1 => bar fixed n
termination_by n => n

def bar (fixed : Nat) : Nat → Nat
 | 0   => 1
 | n+1 => foo fixed n
termination_by n => (⟨n, sorry⟩ : Fin fixed)
end
";
    for (src, block, other_ty) in [(NAT_AND_PROP, "Ex1", "Prop"), (NAT_AND_FIN, "Ex2", "Fin")] {
        let mut env = fresh();
        let outcomes = run_file(&mut env, src);
        let err = outcomes
            .iter()
            .find_map(|outcome| outcome.as_ref().err())
            .unwrap_or_else(|| panic!("{block}: the block must be refused"));
        assert!(
            err.contains("must have the same return type") && err.contains(other_ty),
            "{block}: refused for the wrong reason: {err}"
        );
        for member in ["foo", "bar"] {
            assert!(
                !registered(&env, member),
                "{block}: `{member}` must not be registered"
            );
        }
    }
}

/// Measures of one type (lean4 `tests/elab/955.lean`'s shape, which Lean
/// accepts) leave the block to the structural lift.
#[test]
fn test_mutual_measures_of_one_type_are_lowered() {
    let mut env = fresh();
    let src = "
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  termination_by n => n

  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
  termination_by n => n
end
";
    for outcome in run_file(&mut env, src) {
        if let Err(err) = outcome {
            panic!("measures of one type must not be refused: {err}");
        }
    }
    assert!(registered(&env, "isEven") && registered(&env, "isOdd"));
}
