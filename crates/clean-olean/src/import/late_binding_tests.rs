// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The late-binding judgement over the pinned toolchain's own output: the
//! fixture family `implemented_by_late` (`tests/fixtures/lean/v4.30.0-rc2/`)
//! and `ImplByLib` (`implemented_by_import`), loaded through the production
//! loader, and the order record it leaves. What the programs print is pinned
//! by clean-native's `compile_implemented_by_import_tests`.

use std::collections::BTreeMap;
use std::path::PathBuf;

use clean_kernel::env::Environment;
use clean_kernel::name::Name;

use super::*;
use crate::load_module_with_deps;
use crate::test_support::compiled_fixture_dir;

/// The pinned toolchain's library; these tests fail closed without it.
fn pinned_lean_lib() -> PathBuf {
    crate::pinned_lean_lib_path().expect("the pinned Lean toolchain's library is required")
}

fn n(s: &str) -> Name {
    Name::from_string(s)
}

/// The order record after loading `module` of fixture `family` over the
/// pinned `Init.Prelude`: referrer -> (rebound, via).
fn record_after(family: &str, module: &str) -> BTreeMap<String, (String, String)> {
    let fixture = compiled_fixture_dir(family);
    let mut env = Environment::with_prelude();
    load_module_with_deps(&mut env, module, &[fixture, pinned_lean_lib()])
        .unwrap_or_else(|e| panic!("load {module}: {e}"));
    env.compiled_before_record()
        .into_iter()
        .flatten()
        .map(|(referrer, why)| {
            (
                referrer.to_string(),
                (why.rebound.to_string(), why.via.to_string()),
            )
        })
        .collect()
}

fn row(referrer: &str, rebound: &str, via: &str) -> (String, (String, String)) {
    (referrer.to_owned(), (rebound.to_owned(), via.to_owned()))
}

/// `attribute [implemented_by lateFast] lateSlow` after `lateCaller`: the
/// caller and `lateSlow`'s own code are recorded, and so is `lateAfter`,
/// added after the command: a `.olean` does not say which constants came
/// before it, so every own referrer is recorded (every root is refused
/// either way).
#[test]
fn test_late_binding_plain_records_every_own_referrer_and_the_declaration() {
    assert_eq!(
        record_after("implemented_by_late", "LateLib"),
        BTreeMap::from([
            row("lateAfter", "lateSlow", "lateSlow"),
            row("lateCaller", "lateSlow", "lateSlow"),
            row("lateSlow", "lateSlow", "lateSlow"),
        ])
    );
}

/// `@[inline]` with a late binding: the same rows (Lean copies the body).
#[test]
fn test_late_binding_inline_records_the_earlier_caller_and_the_declaration() {
    assert_eq!(
        record_after("implemented_by_late", "LateInline"),
        BTreeMap::from([
            row("inlineCaller", "inlineSlow", "inlineSlow"),
            row("inlineSlow", "inlineSlow", "inlineSlow"),
        ])
    );
}

/// `@[macro_inline]`: the binding is not registered, so nothing is late and
/// every reference compiles the body Lean expands.
#[test]
fn test_late_binding_macro_inline_registers_no_binding() {
    let fixture = compiled_fixture_dir("implemented_by_late");
    let mut env = Environment::with_prelude();
    load_module_with_deps(&mut env, "LateMacro", &[fixture, pinned_lean_lib()])
        .expect("load LateMacro");
    assert!(!env.has_implemented_by(&n("macroSlow")));
    assert!(env.compiled_before_record().is_none());
}

/// A recursive declaration bound on itself has IR whose recursion runs the
/// implementation, so it was compiled after the binding, and a late binding
/// of a `@[noinline]` declaration nothing in the module reaches leaves no
/// code of its body to run: nothing recorded.
#[test]
fn test_late_binding_recursive_and_unreached_noinline_are_not_late() {
    assert!(record_after("implemented_by_late", "LateOk").is_empty());
}

/// A binding written on its declaration inside a macro (`LateHyg`): the
/// declaration's name is hygienic and ends in a number, like the `TypeName`
/// instance `Std.Http.Body.inst._@.Std.Internal.Http.Data.Body.Stream.<hash>.
/// _hygCtx._hyg.18` pinned `Std` derives, and Lean compiled no IR for it
/// because the binding came first: nothing recorded. Judging a name that
/// ends in a number as compiled structurally judged such a binding late, and
/// `clean run` refused every program that imports `Std` (the import sample,
/// 2026-10-21).
#[test]
fn test_late_binding_hygienic_on_declaration_binding_is_not_late() {
    assert!(record_after("implemented_by_late", "LateHyg").is_empty());
}

/// A constructor bound by the command form (`LateCtor`): Lean compiles a
/// constructor structurally and never runs the binding (`ctorUse 1` prints
/// `1`), so the binding is late, and the constructor and the own constants
/// that build it are recorded (every root is refused). Registering it as an
/// on-declaration binding crashed the importer (`clean run` exit 139).
#[test]
fn test_late_binding_constructor_binding_records_the_constructor() {
    let record = record_after("implemented_by_late", "LateCtor");
    for (referrer, rebound) in [
        ("P.mk", "P.mk"),
        ("pf", "P.mk"),
        ("ctorUse", "P.mk"),
        ("T.leaf", "T.leaf"),
        ("tf", "T.leaf"),
        ("tUse", "T.leaf"),
    ] {
        assert_eq!(
            record.get(referrer).map(|(rebound, _)| rebound.as_str()),
            Some(rebound),
            "`{referrer}` is recorded for `{rebound}`: {record:?}"
        );
    }
}

/// An axiom bound on its declaration (`LateAx`): Lean runs the
/// implementation where the axiom is called (`axCaller 1` prints `20`), so
/// nothing is recorded. Pinned `Lean.Attributes`' public part holds its
/// `@[implemented_by] opaque mkAttributeImplOfConstant` as such an axiom, and
/// judging an axiom as compiled structurally refused every program that
/// imports `Lean`.
#[test]
fn test_late_binding_axiom_bound_on_declaration_is_not_late() {
    assert!(record_after("implemented_by_late", "LateAx").is_empty());
}

/// Every binding of `ImplByLib` is on its declaration: no record. The module
/// has no inline attribute, so Lean writes no `inlineAttrs` table for it
/// (`CompilerNames::of`), and `Init.Prelude`'s computed-field binding
/// `Lean.Name.casesOn` → `Lean.Name.casesOn._override` is not late
/// (`computed_field_override`); either misjudged recorded rows here.
#[test]
fn test_late_binding_on_declaration_bindings_record_nothing() {
    assert!(record_after("implemented_by_import", "ImplByLib").is_empty());
}

#[test]
fn test_has_prefix_follows_name_components() {
    assert!(has_prefix(&n("t._at_.f.spec_0._redArg"), &n("t")));
    assert!(has_prefix(&n("t"), &n("t")));
    assert!(!has_prefix(&n("tt"), &n("t")));
    assert!(!has_prefix(&n("f._at_.t.spec_0"), &n("t")));
}

#[test]
fn test_compiler_names_unknown_answers_nothing() {
    assert_eq!(CompilerNames::unknown().macro_inline(&n("d")), None);
}

fn table(name: &str, rows: Option<Vec<(Name, u64)>>) -> TypedExtension {
    TypedExtension {
        extension_name: Name::interned(name),
        source_rows: None,
        entries: Vec::new(),
        undecoded_entries: 0,
        compiler_names: rows,
    }
}

/// A table the part does not hold has no rows (pinned Lean writes none for an
/// extension with nothing to export); one it holds whose rows did not read
/// answers nothing.
#[test]
fn test_compiler_names_absent_table_is_empty_and_unread_table_is_unknown() {
    let d = n("d");
    let absent = CompilerNames::of(&[]);
    assert_eq!(absent.macro_inline(&d), Some(false));
    assert!(absent.ir.is_some_and(|ir| ir.is_empty()));
    assert_eq!(
        CompilerNames::of(&[table(INLINE_ATTRS_EXT, None)]).macro_inline(&d),
        None
    );
    assert!(CompilerNames::of(&[table(DECL_MAP_EXT, None)]).ir.is_none());
    let read = CompilerNames::of(&[table(
        INLINE_ATTRS_EXT,
        Some(vec![(d.clone(), MACRO_INLINE)]),
    )]);
    assert_eq!(read.macro_inline(&d), Some(true));
    assert_eq!(read.macro_inline(&n("e")), Some(false));
}
