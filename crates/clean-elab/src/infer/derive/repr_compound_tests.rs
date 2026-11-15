// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `deriving Repr` / `deriving BEq` over fields of compound type (`Option`,
//! `List`, products), through the production elaborate-and-register entry over
//! the default prelude — the shapes of trust-ir's `TrustIr/Basic.lean`
//! (`FieldDef.offset : Option Nat`, `EnumDef.discriminants : List (Option
//! Int)`), `Semantics/Eval.lean` (`BasicBlock.params : List (ValueId × Ty)`)
//! and `Pred.lean` (`x == some k` at `Option (Nat × Int)`), filed as G02 in
//! `docs/issues/2026-09-19-trust-ir-semantics-elaborator-gaps.md`.
//!
//! Every acceptance below has a negative control that pinned Lean 4.8.0
//! refuses (measured 2026-09-30 with the toolchain binary as oracle): a field
//! whose component has no `Repr`, a false `==` equation, and a `repr` equation
//! between two values Lean renders differently.

use clean_kernel::name::Name;
use clean_kernel::Environment;

use crate::ElabError;

fn run_source(source: &str) -> (Environment, Vec<Result<crate::ElabResult, ElabError>>) {
    let mut env = Environment::with_prelude();
    let mut file = crate::FileContext::new();
    let declarations = clean_parser::parse_file(source).expect("test source parses");
    let results = declarations
        .iter()
        .map(|decl| {
            let decl = crate::preprocess_decl_with_context(decl, &mut file);
            crate::elaborate_decl_and_register_with_context(&mut env, &decl, &mut file)
        })
        .collect();
    (env, results)
}

const FIELD_DEF: &str =
    "structure FieldDef where\n  name : String\n  offset : Option Nat\n  deriving BEq, Repr\n";

/// Every declaration accepted with no failed leaf: a failed `deriving` class
/// is reported as a failed leaf beside its declared type
/// (`infer::deriving_log`), so `is_ok()` alone would read it as derived.
fn assert_all_ok(results: &[Result<crate::ElabResult, ElabError>]) {
    for (index, result) in results.iter().enumerate() {
        let Ok(result) = result else {
            panic!("declaration {index} refused: {result:?}");
        };
        let mut leaves = Vec::new();
        result.leaf_decls(&mut leaves);
        assert!(
            !leaves
                .iter()
                .any(|leaf| matches!(leaf, crate::ElabResult::Failed { .. })),
            "declaration {index} has a failed leaf: {result:?}"
        );
    }
}

/// The text of the one failed `deriving` class beside a declared type.
fn failed_class_text(result: &Result<crate::ElabResult, ElabError>) -> String {
    let Ok(crate::ElabResult::Multiple(leaves)) = result else {
        panic!("expected the declared type plus its failed class, got {result:?}");
    };
    match leaves.as_slice() {
        [declared, crate::ElabResult::Failed { error, .. }]
            if !matches!(declared, crate::ElabResult::Failed { .. })
                && matches!(**error, ElabError::DerivingHandlerFailed { .. }) =>
        {
            error.to_string()
        }
        _ => panic!("expected the declared type plus its failed class, got {leaves:?}"),
    }
}

#[test]
fn test_derive_repr_option_field_structure_registers_instance() {
    let source = format!(
        "{FIELD_DEF}structure StructDef where\n  name : String\n  fields : List FieldDef\n  size : Option Nat\n  deriving Repr\n"
    );
    let (env, results) = run_source(&source);
    assert_eq!(results.len(), 2);
    assert_all_ok(&results);
    for target in ["FieldDef", "StructDef"] {
        let instance = crate::derive::builtin_instance_name(&Name::from_string(target), "Repr");
        assert!(
            env.get_const(&instance).is_some(),
            "{target}: `{instance}` must be registered"
        );
    }
    assert!(env.get_const(&Name::from_string("StructDef")).is_some());
}

#[test]
fn test_derive_repr_nested_compound_fields_registers_instance() {
    let source = "structure EnumDef where\n  discriminants : List (Option Int) := []\n  tagRepr : Option Bool := none\n  deriving Repr\n\
                  structure BasicBlock where\n  params : List (Nat × Int)\n  bodyResultDests : List (List Nat) := []\n  deriving Repr\n\
                  structure Machine where\n  globals : List (Nat × Nat × Bool)\n  deriving Repr\n";
    let (_env, results) = run_source(source);
    assert_eq!(results.len(), 3);
    assert_all_ok(&results);
}

#[test]
fn test_derive_repr_compound_field_without_repr_component_is_refused() {
    // Lean 4.8: `failed to synthesize instance Repr (Option (Nat → Nat))` and
    // `… Repr (List (Nat × (Nat → Nat)))`. The compound instances are
    // conditional on their components; they must not make these derivable.
    for (source, field) in [
        (
            "structure BadOpt where\n  f : Option (Nat → Nat)\n  deriving Repr\n",
            "f",
        ),
        (
            "structure BadProd where\n  g : List (Nat × (Nat → Nat))\n  deriving Repr\n",
            "g",
        ),
    ] {
        let (_env, results) = run_source(source);
        assert_eq!(results.len(), 1);
        // The structure is declared (Lean adds it first); the clause fails.
        let text = failed_class_text(&results[0]);
        assert!(
            text.contains(&format!("cannot synthesize Repr for field `{field}`")),
            "{text}"
        );
    }
}

#[test]
fn test_derive_repr_parametric_structure_option_field_registers_instance() {
    let source =
        "structure Box (α : Type) where\n  x : Option α\n  xs : List (α × Nat)\n  deriving Repr\n";
    let (_env, results) = run_source(source);
    assert_eq!(results.len(), 1);
    assert_all_ok(&results);
}

#[test]
fn test_repr_distinct_values_rfl_equation_is_refused() {
    // Each `name` theorem is Lean-false (`type mismatch` under pinned Lean
    // 4.8) and was ACCEPTED while the stub renderings were constants. Each has
    // a positive twin, `lhs = lhs := rfl`, that Lean accepts: the same
    // statement elaborates and checks, so the refusal is the rendering's
    // inequality and not an unrelated failure of the statement.
    let refused = [
        (
            "bad_opt",
            "",
            "repr (some (1 : Nat))",
            "repr (some (2 : Nat))",
        ),
        (
            "bad_prod",
            "",
            "repr ((1 : Nat), (2 : Nat))",
            "repr ((1 : Nat), (3 : Nat))",
        ),
        ("bad_nat", "", "repr (1 : Nat)", "repr (2 : Nat)"),
        ("bad_list", "", "repr [(1 : Nat)]", "repr ([] : List Nat)"),
        (
            "bad_struct",
            "",
            "repr ({ name := \"a\", offset := some 1 } : FieldDef)",
            "repr ({ name := \"a\", offset := some 2 } : FieldDef)",
        ),
        (
            "bad_box",
            "structure Box (α : Type) where\n  x : Option α\n  deriving Repr\n",
            "repr (Box.mk (some (1 : Nat)))",
            "repr (Box.mk (some (2 : Nat)))",
        ),
    ];
    for (name, decls, lhs, rhs) in refused {
        let twin = format!("{name}_twin");
        let source = format!("{FIELD_DEF}{decls}theorem {twin} : {lhs} = {lhs} := rfl\n");
        let (env, results) = run_source(&source);
        assert_all_ok(&results);
        assert!(
            env.get_const(&Name::from_string(&twin)).is_some(),
            "{twin} must register"
        );

        let theorem = format!("theorem {name} : {lhs} = {rhs} := rfl");
        let source = format!("{FIELD_DEF}{decls}{theorem}\n");
        let (env, results) = run_source(&source);
        let last = results.last().expect("the theorem was parsed");
        assert!(last.is_err(), "Lean-false equation accepted: {theorem}");
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} registered"
        );
        // Everything before the theorem still registers: the refusal is the
        // theorem's own, not a cascade.
        assert_all_ok(&results[..results.len() - 1]);
    }
}

#[test]
fn test_beq_prod_and_option_prod_resolve_and_compute() {
    let source = "def membersContainKey (items : List (Option (Nat × Int))) (k : Nat × Int) : Bool :=\n  items.any (fun c => c == some k)\n\
                  theorem beq_pair_true : (((1 : Nat), (2 : Int)) == ((1 : Nat), (2 : Int))) = true := rfl\n\
                  theorem beq_opt_pair_false : (some ((1 : Nat), (2 : Int)) == some ((1 : Nat), (3 : Int))) = false := rfl\n";
    let (env, results) = run_source(source);
    assert_eq!(results.len(), 3);
    assert_all_ok(&results);
    assert!(env
        .get_const(&Name::from_string("beq_opt_pair_false"))
        .is_some());
}

#[test]
fn test_beq_prod_false_equation_is_refused() {
    // Lean 4.8 refuses `((1, 2) == (1, 3)) = true := rfl`.
    for theorem in [
        "theorem bad_snd : (((1 : Nat), (2 : Int)) == ((1 : Nat), (3 : Int))) = true := rfl",
        "theorem bad_fst : (((0 : Nat), (3 : Int)) == ((1 : Nat), (3 : Int))) = true := rfl",
    ] {
        let (_env, results) = run_source(theorem);
        assert_eq!(results.len(), 1);
        assert!(
            results[0].is_err(),
            "Lean-false equation accepted: {theorem}"
        );
    }
    // The positive twins: the same comparisons ARE `false` (Lean 4.8 accepts
    // both), so the refusals above are the values, not the statements.
    let source = "theorem ok_snd : (((1 : Nat), (2 : Int)) == ((1 : Nat), (3 : Int))) = false := rfl\n\
                  theorem ok_fst : (((0 : Nat), (3 : Int)) == ((1 : Nat), (3 : Int))) = false := rfl\n";
    let (env, results) = run_source(source);
    assert_eq!(results.len(), 2);
    assert_all_ok(&results);
    assert!(env.get_const(&Name::from_string("ok_fst")).is_some());
}

// ---------------------------------------------------------------------------
// OPEN, ledger class (90) — pinned so each fails loudly the day it closes.
// ---------------------------------------------------------------------------

#[test]
fn test_derive_repr_inductive_ctor_with_fields_renders_opaquely() {
    // A constructor with fields renders through the opaque renderer, so two
    // argument lists are two renderings (Lean 4.8: `type mismatch`); the
    // constructor-name text used to make them equal.
    let source = "inductive N where\n  | mk (n : Nat)\n  | z\n  deriving Repr\n\
                  theorem n_collapse : repr (N.mk 1) = repr (N.mk 2) := rfl\n\
                  theorem n_twin : repr (N.mk 1) = repr (N.mk 1) := rfl\n";
    let (env, results) = run_source(source);
    assert_eq!(results.len(), 3);
    assert!(results[0].is_ok(), "{:?}", results[0]);
    assert!(results[1].is_err(), "Lean-false equation accepted");
    assert!(env.get_const(&Name::from_string("n_collapse")).is_none());
    // The positive twin (Lean 4.8 accepts it): the statement itself checks.
    assert!(results[2].is_ok(), "{:?}", results[2]);
    assert!(env.get_const(&Name::from_string("n_twin")).is_some());
}

#[test]
fn test_derive_repr_inductive_nonlean_acceptances_open_class_90() {
    // ACCEPTED WITH A NON-LEAN MEANING, both: the inductive `Repr` derive
    // resolves no field's `Repr` (Lean 4.8: `failed to synthesize instance
    // Repr (Nat → Nat)` for `T`), and a nullary constructor renders as bare
    // text where Lean's is `Format.group (Format.nest 2 "E.a")` (Lean 4.8:
    // `type mismatch` for `e_text`). When either flips, re-file class (90).
    let source = "inductive T where\n  | mk (f : Nat → Nat)\n  deriving Repr\n\
                  inductive E where\n  | a\n  | b\n  deriving Repr\n\
                  theorem e_text : repr E.a = \"E.a\" := rfl\n";
    let (env, results) = run_source(source);
    assert_eq!(results.len(), 3);
    assert_all_ok(&results);
    assert!(env.get_const(&Name::from_string("e_text")).is_some());
}
