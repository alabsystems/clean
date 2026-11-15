// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End to end: a zero-argument tactic macro that reaches the environment the
//! way an olean-imported one does — a `ParserDescr` constant for its syntax
//! kind plus a `_aux_…___macroRules_<kind>_1` rule whose value builds the
//! expansion with `Lean.Syntax.node*` — runs as the tactic it expands to
//! (class (11), `compareOfLessAndEq_rfl`). The `Lean.*` syntax vocabulary is
//! registered as IMPORTED constants — straight into the kernel environment,
//! the way the `.olean` importer registers Lean's own declarations — because
//! the built-in prelude has none of it and every one of these names is a
//! Lean 4.8.0 `Init.Prelude` constant, which a source file may not declare
//! (Lean: "already declared"; `crate::lean_core_names`). The shapes are those
//! the pinned v4.30.0-rc2 prints for Mathlib's macro.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use clean_parser::parse_file;

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

const VOCABULARY: &str = "axiom Lean.Name : Type\n\
    axiom Lean.Name.mkStr1 : String → Lean.Name\n\
    axiom Lean.Name.mkStr4 : String → String → String → String → Lean.Name\n\
    axiom Lean.SourceInfo : Type\n\
    axiom Lean.SourceInfo.none : Lean.SourceInfo\n\
    axiom Lean.Syntax : Type\n\
    axiom Lean.Syntax.atom : Lean.SourceInfo → String → Lean.Syntax\n\
    axiom Lean.Syntax.node1 : Lean.SourceInfo → Lean.Name → Lean.Syntax → Lean.Syntax\n\
    axiom Lean.Syntax.isOfKind : Lean.Syntax → Lean.Name → Bool\n\
    axiom Lean.ParserDescr : Type\n\
    axiom Lean.ParserDescr.node : Lean.Name → Nat → Lean.ParserDescr → Lean.ParserDescr\n\
    axiom Lean.ParserDescr.nonReservedSymbol : String → Bool → Lean.ParserDescr\n\
    axiom Lean.ParserDescr.binary : Lean.Name → Lean.ParserDescr → Lean.ParserDescr → Lean.ParserDescr\n";

/// Register each `axiom <name> : <A> → … → <R>` line of [`VOCABULARY`] as an
/// imported constant (`Type` is `Sort 1`, every other type a constant).
fn import_vocabulary(env: &mut Environment) {
    for line in VOCABULARY.lines() {
        let (name, ty) = line
            .strip_prefix("axiom ")
            .and_then(|rest| rest.split_once(" : "))
            .unwrap_or_else(|| panic!("vocabulary line {line:?}"));
        let parts: Vec<Expr> = ty
            .split(" → ")
            .map(|part| match part {
                "Type" => Expr::sort(Level::succ(Level::zero())),
                constant => Expr::const_(Name::from_string(constant), vec![]),
            })
            .collect();
        let ty = parts
            .into_iter()
            .rev()
            .reduce(|codomain, domain| Expr::pi(BinderInfo::Default, domain, codomain))
            .expect("a type");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
        .unwrap_or_else(|e| panic!("import {name}: {e:?}"));
    }
}

fn rule(kind: &str, rhs: &str) -> String {
    format!(
        "def _aux_T___macroRules_{kind}_1 : Lean.Syntax → Lean.Syntax := fun x =>\n\
         \x20 if Lean.Syntax.isOfKind x (Lean.Name.mkStr1 \"{kind}\") = true then {rhs} else x\n"
    )
}

const RFL_RHS: &str = "Lean.Syntax.node1 Lean.SourceInfo.none \
    (Lean.Name.mkStr4 \"Lean\" \"Parser\" \"Tactic\" \"tacticRfl\") \
    (Lean.Syntax.atom Lean.SourceInfo.none \"rfl\")";

#[test]
fn test_imported_zero_arg_tactic_macro_runs_its_expansion() {
    let mut env = Environment::with_prelude();
    import_vocabulary(&mut env);
    let src = format!(
        "def tacticMy_rfl : Lean.ParserDescr := Lean.ParserDescr.node\n\
         \x20 (Lean.Name.mkStr1 \"tacticMy_rfl\") 1024 (Lean.ParserDescr.nonReservedSymbol \"my_rfl\" false)\n\
         {}\
         theorem usesMacro : (2 : Nat) = 2 := by my_rfl\n",
        rule("tacticMy_rfl", RFL_RHS)
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("the imported macro must expand to `rfl` and close the goal: {e}");
    }
}

#[test]
fn test_imported_tactic_macro_with_an_argument_stays_unknown() {
    let mut env = Environment::with_prelude();
    import_vocabulary(&mut env);
    // The kind's syntax is `my_rfl` FOLLOWED by something: not a single atom,
    // so there is an antiquotation this decoder must not guess at.
    let src = format!(
        "def tacticMy_rfl : Lean.ParserDescr := Lean.ParserDescr.node\n\
         \x20 (Lean.Name.mkStr1 \"tacticMy_rfl\") 1024\n\
         \x20 (Lean.ParserDescr.binary (Lean.Name.mkStr1 \"andthen\")\n\
         \x20   (Lean.ParserDescr.nonReservedSymbol \"my_rfl\" false)\n\
         \x20   (Lean.ParserDescr.nonReservedSymbol \"x\" false))\n\
         {}\
         theorem usesMacro : (2 : Nat) = 2 := by my_rfl\n",
        rule("tacticMy_rfl", RFL_RHS)
    );
    let err = elab(&mut env, &src).expect("a macro with arguments must stay unknown");
    assert!(err.contains("my_rfl"), "got: {err}");
}

#[test]
fn test_imported_tactic_macro_expansion_is_still_checked() {
    let mut env = Environment::with_prelude();
    import_vocabulary(&mut env);
    // The expansion is `rfl`, which cannot prove `2 = 3`: the macro only
    // routes to the ordinary kernel-checked tactic.
    let src = format!(
        "def tacticMy_rfl : Lean.ParserDescr := Lean.ParserDescr.node\n\
         \x20 (Lean.Name.mkStr1 \"tacticMy_rfl\") 1024 (Lean.ParserDescr.nonReservedSymbol \"my_rfl\" false)\n\
         {}\
         theorem wrong : (2 : Nat) = 3 := by my_rfl\n",
        rule("tacticMy_rfl", RFL_RHS)
    );
    assert!(
        elab(&mut env, &src).is_some(),
        "an expansion that does not prove the goal must fail"
    );
}
