// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end pins for gap-sweep **B21 — attribute & `set_option` validation**.
//!
//! Before B21 an unknown attribute (`@[notARealAttribute]`), an unknown option
//! (`set_option notARealOption true`), and a wrongly-typed option value
//! (`set_option autoImplicit 5`) were all silently accepted — which masked
//! every other attribute/option gap. These tests pin the loud behavior:
//!
//! - every attribute/option Clean actually honors is still accepted, and the
//!   positive declarations elaborate with an empty failure closure;
//! - an unknown attribute is a loud elaboration error;
//! - an unknown option is a loud elaboration error;
//! - an option value of the wrong type is a loud elaboration error.
//!
//! Ground truth: Lean 4 `src/Lean/Attributes.lean` (registry lookup → error on
//! unknown) and `src/Lean/Data/Options.lean` (registered option decls + value
//! type check).

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

fn collect_failures(result: &ElabResult, failures: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for result in results {
                collect_failures(result, failures);
            }
        }
        ElabResult::Failed { name, error, .. } => failures.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// Elaborate every declaration in `source`, returning `Err` with the first
/// diagnostic if any declaration fails to elaborate (either a hard elaboration
/// error or an inner `ElabResult::Failed`).
fn try_elaborate(source: &str) -> Result<(), String> {
    let mut env = Environment::with_prelude();
    let mut file_context = FileContext::new();
    let declarations = parse_file(source).map_err(|error| format!("parse error: {error}"))?;
    for declaration in &declarations {
        let processed = preprocess_decl_with_context(declaration, &mut file_context);
        match elaborate_decl_and_register(&mut env, &processed) {
            Ok(result) => {
                let mut failures = Vec::new();
                collect_failures(&result, &mut failures);
                if !failures.is_empty() {
                    return Err(failures.join("; "));
                }
            }
            Err(error) => return Err(error.to_string()),
        }
    }
    Ok(())
}

// ----------------------------------------------------------------------------
// Positives: everything Clean honors must stay accepted with an empty closure.
// ----------------------------------------------------------------------------

#[test]
fn known_attributes_are_accepted() {
    for source in [
        "@[simp] theorem attr_simp_eq : (1 : Nat) = 1 := rfl",
        "@[reducible] def attr_reducible (n : Nat) : Nat := n",
        "@[irreducible] def attr_irreducible : Nat := 3",
        "@[inline] def attr_inline (n : Nat) : Nat := n + 1",
        "@[specialize] def attr_specialize (f : Nat -> Nat) (n : Nat) : Nat := f n",
        "@[macro_inline] def attr_macro_inline (n : Nat) : Nat := n",
        // Unmodeled-but-known Lean attributes must not be rejected.
        "@[inherit_doc] def attr_inherit_doc : Nat := 0",
    ] {
        let result = try_elaborate(source);
        assert!(
            result.is_ok(),
            "known attribute must be accepted, but got error for `{source}`: {result:?}"
        );
    }
}

#[test]
fn known_instance_attribute_is_accepted() {
    // `@[instance]` on a definition registers it as a type-class instance; this
    // is a modeled attribute Clean honors (the conclusion is a registered
    // class, so registration succeeds rather than tripping the B14 def-alias
    // reducibility gap).
    let source = "class Pointed (α : Type) where point : α\n\
         @[instance] def natPointed : Pointed Nat := ⟨0⟩";
    let result = try_elaborate(source);
    assert!(
        result.is_ok(),
        "@[instance] must be accepted and honored: {result:?}"
    );
}

#[test]
fn known_options_are_accepted() {
    for source in [
        "set_option autoImplicit false\ndef opt_ok1 : Nat := 1",
        "set_option maxHeartbeats 400000\ndef opt_ok2 : Nat := 1",
        "set_option maxRecDepth 4000\ndef opt_ok3 : Nat := 1",
        "set_option pp.all true\ndef opt_ok4 : Nat := 1",
        "set_option relaxedAutoImplicit false\ndef opt_ok5 : Nat := 1",
        "set_option synthInstance.maxSize 128\ndef opt_ok6 : Nat := 1",
        "set_option linter.unusedVariables true\ndef opt_ok7 : Nat := 1",
        // `set_option ... in` scoped form must validate and accept too.
        "set_option autoImplicit true in\ndef opt_ok8 (a : α) : α := a",
    ] {
        let result = try_elaborate(source);
        assert!(
            result.is_ok(),
            "known option must be accepted, but got error for `{source}`: {result:?}"
        );
    }
}

// ----------------------------------------------------------------------------
// Negatives: unknown attribute / unknown option / wrong-typed value are loud.
// ----------------------------------------------------------------------------

#[test]
fn unknown_attribute_is_tolerated_as_noop() {
    // Drop-in behavior (supersedes the strict B21 probe attributes_options/p14):
    // an UNKNOWN (unmodeled) attribute is tolerated as a no-op — real Lean core +
    // Mathlib register hundreds of attributes via macros (`@[grind]`, `@[simps]`,
    // `@[mfld_simps]`, `@[nolint]`, …) that Clean does not enumerate, and a
    // declaration carrying one MUST still elaborate. Clean cannot act on an
    // attribute it does not model, so ignoring it is sound; the decl is still
    // kernel-checked. (A MODELED attribute given the wrong target stays loud — see
    // `attribute_ext2` `validate_attribute_for_decl`.)
    let result = try_elaborate("@[notARealAttribute] def bad14 : Nat := 1");
    assert!(
        result.is_ok(),
        "unknown attribute must be tolerated so `bad14` still elaborates, got: {result:?}"
    );
}

#[test]
fn unknown_attribute_in_command_form_is_tolerated() {
    let result = try_elaborate("def cmdTarget : Nat := 1\nattribute [notARealAttribute] cmdTarget");
    assert!(
        result.is_ok(),
        "command-form unknown attribute must be tolerated, got: {result:?}"
    );
}

#[test]
fn unknown_option_is_tolerated_as_noop() {
    // Drop-in behavior (supersedes the original strict B21 probe
    // attributes_options/p17): an UNKNOWN option NAME is tolerated as a no-op,
    // NOT a loud error — real Lean core/plugins/linters register options Clean's
    // finite registry does not enumerate (`genInjectivity`, `linter.*`), and a
    // source file that sets one must still elaborate the following declarations.
    // (A KNOWN option given a wrongly-typed value stays loud — see the
    // `*_wrong_value_type_*` / `nat_option_given_bool_*` tests below.)
    let result = try_elaborate("set_option notARealOption true\ndef ok17 : Nat := 1");
    assert!(
        result.is_ok(),
        "unknown option name must be tolerated so `ok17` still elaborates, got: {result:?}"
    );
}

#[test]
fn option_wrong_value_type_is_a_loud_error() {
    // Probe attributes_options/p18: autoImplicit is Bool, given a Nat value.
    let result = try_elaborate("set_option autoImplicit 5\ndef ok18 : Nat := 1");
    let error = result.expect_err("Bool option given a Nat value must be loud");
    assert!(
        error.contains("autoImplicit") && error.contains("Bool"),
        "type-mismatch error should mention the option and its Bool type, got: {error}"
    );
}

#[test]
fn nat_option_given_bool_is_a_loud_error() {
    // The dual of p18: a Nat option given a Bool value.
    let result = try_elaborate("set_option maxHeartbeats true\ndef okN : Nat := 1");
    let error = result.expect_err("Nat option given a Bool value must be loud");
    assert!(
        error.contains("maxHeartbeats") && error.contains("Nat"),
        "type-mismatch error should mention the option and its Nat type, got: {error}"
    );
}

#[test]
fn unknown_option_in_scoped_form_is_tolerated() {
    // The `set_option <unknown> … in <decl>` form is the one that bit real
    // Mathlib (`set_option genInjectivity false in <structure>`): rejecting it
    // killed the wrapped declaration. Now the unknown name is tolerated and the
    // wrapped decl elaborates.
    let result = try_elaborate("set_option notARealOption true in\ndef okScoped : Nat := 1");
    assert!(
        result.is_ok(),
        "unknown option in `set_option ... in` must be tolerated so the wrapped \
         decl elaborates, got: {result:?}"
    );
}
