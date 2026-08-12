// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Import adopts Lean's serialized instance priority** — the structural
//! retirement of the guessed-priority defect class.
//!
//! Clean seeds a hand-rolled prelude whose instance priorities are GUESSED, then
//! imports a real Lean environment on top. Import is first-registered-wins, so a
//! wrong guess used to be frozen in place forever, and instance priority decides
//! which candidate `synthInstance` reaches first — the shape of every elaborated
//! term. Three separate one-off fixes preceded these tests:
//!
//! - `8d80c9d98` `instOfNatNat` guessed 100, Lean serializes **1000**. The guess
//!   came from reading `@[default_instance 100]` off Lean's SOURCE — a
//!   *different table* (literal-type defaulting, not candidate ordering). The
//!   `instance` itself is unannotated, hence Lean's default 1000.
//! - `066a1173f` `instLTNat` guessed 100, Lean serializes **1000**; it ranked
//!   30th of 43 `LT` candidates, below every imported instance.
//! - `28e7834a1` the B101 hetero bridges (priority 50) were seeded BEFORE the
//!   import they were documented to defer to.
//!
//! # Decoy discipline
//!
//! **Every decoy here is an `Axiom`-kind constant with NO value** — the shape a
//! constant actually has after `.olean` import. That is deliberate and
//! load-bearing: a `@[reducible]` definition decoy (which is what Clean's own
//! prelude instances are) can be delta-reduced away, so a test built on one
//! passes with *and* without the fix and diagnoses nothing. For the same reason
//! the decoy is pre-registered at the WRONG priority: a decoy already carrying
//! Lean's value would pass under first-registered-wins too.
//!
//! These tests need no Lean toolchain: the `InstanceEntry` is synthesized
//! directly, so they gate on every machine. The real-toolchain end of the same
//! claim is `crates/clean-olean/tests/prelude_instance_priority_census.rs`
//! (`import_adopts_lean_priority_for_hand_registered_instances`).

use super::load_parsed_module;
use crate::module::{
    ParsedAttrKind, ParsedExtension, ParsedExtensionEntry, ParsedInstanceEntry, ParsedModule,
};
use clean_kernel::env::{Environment, KernelClassInfo, KernelInstanceInfo};
use clean_kernel::name::Name;
use clean_kernel::{Declaration, Expr};

/// The persisted name of Lean 4's typeclass-instance extension.
const INSTANCE_EXT: &str = "Lean.Meta.instanceExtension";

/// Lean's default priority for an unannotated `instance`.
const LEAN_DEFAULT: u64 = 1000;

/// Clean's fabricated `DEFAULT_INSTANCE_PRIORITY`, i.e. the wrong guess.
const CLEAN_GUESS: u32 = 100;

/// Build an environment holding a class `TestCls` and two **`Axiom`-kind,
/// value-less** instance constants of it, both hand-registered at the guessed
/// priority. `held` is the one the synthetic `.olean` will disagree with;
/// `rival` is the control — Lean never mentions it, so nothing may touch it.
fn env_with_axiom_decoys() -> Environment {
    let mut env = Environment::new();
    let class = Name::from_string("TestCls");

    env.add_decl(Declaration::Axiom {
        name: class.clone(),
        level_params: vec![],
        type_: Expr::sort(clean_kernel::Level::zero()),
    })
    .expect("class constant");
    env.register_class(KernelClassInfo {
        name: class.clone(),
        num_params: 0,
        out_params: Vec::new(),
        semi_out_params: Vec::new(),
    });

    for name in ["testInstHeld", "testInstRival"] {
        // AXIOM, NO VALUE — the imported shape. Not a `@[reducible]` def.
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_str("TestCls"),
        })
        .unwrap_or_else(|e| panic!("axiom decoy {name}: {e}"));
        env.register_instance(KernelInstanceInfo {
            name: Name::from_string(name),
            class_name: class.clone(),
            priority: CLEAN_GUESS,
            type_: None,
            value: None,
        });
    }
    env
}

/// A module carrying nothing but one `Lean.Meta.instanceExtension` entry.
fn module_with_instance_entry(instance_name: &str, priority: u64) -> ParsedModule {
    ParsedModule {
        const_names: Vec::new(),
        constants: Vec::new(),
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: vec![ParsedExtension {
            extension_name: INSTANCE_EXT.to_owned(),
            entries: vec![ParsedExtensionEntry::Instance(ParsedInstanceEntry {
                instance_name: instance_name.to_owned(),
                priority,
                attr_kind: ParsedAttrKind::Global,
                scope_ns: None,
                synth_order: Vec::new(),
            })],
            undecoded_entries: 0,
        }],
        clean_payload: None,
    }
}

fn priority_of(env: &Environment, name: &str) -> Option<u32> {
    let target = Name::from_string(name);
    env.instances()
        .find(|i| i.name == target)
        .map(|i| i.priority)
}

/// The defect, reproduced end to end: a hand-registered instance at the guessed
/// 100 must come out at the 1000 the `.olean` serializes.
///
/// RED before the fix — `register_real_instance_entries` used to `continue` on
/// `env.is_instance(&name)`, keeping 100.
#[test]
fn test_import_adopts_serialized_priority_over_guessed_registration() {
    let mut env = env_with_axiom_decoys();
    assert_eq!(priority_of(&env, "testInstHeld"), Some(CLEAN_GUESS));

    let module = module_with_instance_entry("testInstHeld", LEAN_DEFAULT);
    load_parsed_module(&mut env, &module, Some("TestMod".to_owned()))
        .expect("synthetic module loads");

    assert_eq!(
        priority_of(&env, "testInstHeld"),
        Some(1000),
        "import must ADOPT the priority Lean serialized, not keep Clean's guess"
    );
}

/// Adoption also LOWERS. Lean serializes 500 for `instBEqOfDecidableEq`, so a
/// raise-only path would leave a 1000 guess wrong in the other direction.
#[test]
fn test_import_adopts_lower_serialized_priority() {
    let mut env = Environment::new();
    let class = Name::from_string("TestCls");
    env.add_decl(Declaration::Axiom {
        name: class.clone(),
        level_params: vec![],
        type_: Expr::sort(clean_kernel::Level::zero()),
    })
    .expect("class constant");
    env.register_class(KernelClassInfo {
        name: class.clone(),
        num_params: 0,
        out_params: Vec::new(),
        semi_out_params: Vec::new(),
    });
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testInstTooHigh"),
        level_params: vec![],
        type_: Expr::const_str("TestCls"),
    })
    .expect("axiom decoy");
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("testInstTooHigh"),
        class_name: class,
        priority: 1000,
        type_: None,
        value: None,
    });

    let module = module_with_instance_entry("testInstTooHigh", 500);
    load_parsed_module(&mut env, &module, Some("TestMod".to_owned()))
        .expect("synthetic module loads");

    assert_eq!(
        priority_of(&env, "testInstTooHigh"),
        Some(500),
        "adoption must be exact, not raise-only"
    );
}

/// CONTROL: a hand-registered instance the `.olean` never mentions is left
/// exactly as Clean registered it. Without this the test above would also pass
/// if adoption blindly rewrote every instance to 1000.
#[test]
fn test_import_leaves_instances_lean_never_registers_untouched() {
    let mut env = env_with_axiom_decoys();

    let module = module_with_instance_entry("testInstHeld", LEAN_DEFAULT);
    load_parsed_module(&mut env, &module, Some("TestMod".to_owned()))
        .expect("synthetic module loads");

    assert_eq!(
        priority_of(&env, "testInstRival"),
        Some(CLEAN_GUESS),
        "an instance absent from the `.olean` has nothing contradicting it and must keep \
         Clean's value"
    );
}

/// CONTROL: adoption must not duplicate the entry, and the adopted instance must
/// actually OUTRANK its equal-guess rival afterwards — priority that does not
/// reorder the candidate list would be cosmetic.
#[test]
fn test_adopted_priority_reorders_the_candidate_list_without_duplicating() {
    let mut env = env_with_axiom_decoys();
    let class = Name::from_string("TestCls");

    // Both decoys sit in one tier; `register_instance` is most-recent-first, so
    // the rival (registered second) leads before the import.
    let before: Vec<String> = env
        .get_class_instances(&class)
        .iter()
        .map(|i| i.name.to_string())
        .collect();
    assert_eq!(
        before,
        vec!["testInstRival".to_owned(), "testInstHeld".to_owned()],
        "pre-import candidate order"
    );

    let module = module_with_instance_entry("testInstHeld", LEAN_DEFAULT);
    load_parsed_module(&mut env, &module, Some("TestMod".to_owned()))
        .expect("synthetic module loads");

    let after: Vec<String> = env
        .get_class_instances(&class)
        .iter()
        .map(|i| i.name.to_string())
        .collect();
    assert_eq!(
        after,
        vec!["testInstHeld".to_owned(), "testInstRival".to_owned()],
        "the adopted 1000 must move the instance AHEAD of the 100 rival"
    );
    assert_eq!(
        env.get_class_instances(&class).len(),
        2,
        "adoption re-seats the existing entry; it must never add a second one"
    );
}

/// Adoption is idempotent across the repeated/overlapping loads that real
/// imports do (base `.olean` + `.olean.private` re-list the same entries).
#[test]
fn test_import_priority_adoption_is_idempotent() {
    let mut env = env_with_axiom_decoys();
    let module = module_with_instance_entry("testInstHeld", LEAN_DEFAULT);
    for _ in 0..3 {
        load_parsed_module(&mut env, &module, Some("TestMod".to_owned()))
            .expect("synthetic module loads");
    }
    assert_eq!(priority_of(&env, "testInstHeld"), Some(1000));
    assert_eq!(
        env.get_class_instances(&Name::from_string("TestCls")).len(),
        2,
        "repeated loads must not accumulate duplicate instance entries"
    );
}

/// Never fabricate: an `InstanceEntry` naming a constant this environment does
/// not have registers nothing at all.
#[test]
fn test_import_does_not_fabricate_an_instance_for_an_absent_constant() {
    let mut env = env_with_axiom_decoys();
    let before = env.num_instances();

    let module = module_with_instance_entry("testInstNeverDeclared", LEAN_DEFAULT);
    load_parsed_module(&mut env, &module, Some("TestMod".to_owned()))
        .expect("synthetic module loads");

    assert_eq!(
        env.num_instances(),
        before,
        "an entry whose constant is absent must be skipped, not fabricated"
    );
    assert_eq!(priority_of(&env, "testInstNeverDeclared"), None);
}
