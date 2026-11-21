// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Which default priority does an UNANNOTATED instance get, and by which
//! code path?**
//!
//! Lean 4 ground truth: an attribute with no explicit priority gets `default`,
//! which is **1000** — `src/Init/Meta/Defs.lean` `evalOptPrio | none => 1000`,
//! reached for `@[instance]` via `getAttrParamOptPrio`
//! (`src/Lean/Attributes.lean`) → `addInstance`
//! (`src/Lean/Meta/Instances.lean`). Lean's keyword ladder
//! (`src/Init/Notation.lean`) is `low` = 100 < `mid` = 500 < `default` = 1000
//! < `high` = 10000.
//!
//! # Why a bare-vs-`low` pair is the discriminator
//!
//! Asserting "the bare instance beats an explicit 2000" (as
//! `instprio_attr_numeric_prio` does) passes whether the bare default is 100
//! or 1000, so it cannot see this defect. The discriminating control is a bare
//! instance against an explicit **`low` (100)** one registered **afterwards**:
//!
//!  * bare = 1000  →  priority dominates  →  the BARE instance wins;
//!  * bare = 100   →  ties with `low`, and the most-recent-first tie-break
//!                    hands the win to the LATER `low` instance.
//!
//! The two arms therefore select different *values*, so the outcome is read
//! off a computed `Nat` and not off any definitional identity: `rfl` here is
//! discharging `3 = 3` only once instance synthesis has already committed to
//! an instance, and the decoy in the opposite direction must stay red.
//!
//! Each lane additionally asserts the **recorded** priority in the class's
//! candidate list, so a pass cannot be produced by a resolution accident.
//!
//! # Path coverage
//!
//! Both surfaces that can produce an unannotated instance are covered:
//!
//!  * `attribute [instance] foo` / `@[instance] def foo` — parser
//!    `grammar/expr_binders.rs` `Attribute::InstancePriority` → `ElabCtx`
//!    `collected_instance_attrs` → `clean-elab/src/lib.rs` `instance_attrs`
//!    loop.
//!  * `instance foo : C T := …` — `SurfaceDecl::Instance { priority: None }`
//!    → `infer/elab_instance.rs` → `instances::DEFAULT_PRIORITY`.
//!
//! A third surface, `command_elab_registry::register_instance_handler`,
//! defaults to the KERNEL constant (100) and stamps `class_name` with the
//! declaration name. It is **not** on either dispatch path — see
//! `instance_attr_handler_is_not_on_the_dispatch_path` below, which pins that
//! the class registered for a `@[instance]` target is the real class and never
//! the declaration name (the signature that handler would leave behind).

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_olean::load_module_with_deps;
use std::path::PathBuf;

// ----------------------------------------------------------------------------
// Fixtures
// ----------------------------------------------------------------------------

/// `attribute [instance]` surface. `probeAttrBare` is registered FIRST and
/// unannotated; `probeAttrLow` is registered SECOND at Lean's `low` (100).
/// Lean picks `probeAttrBare` (1000 > 100), yielding 3.
const ATTR_SURFACE: &str = "class ProbeAttrC (α : Type) where\n  \
     n : Nat\n\
     @[reducible] def probeAttrBare : ProbeAttrC Nat := ⟨3⟩\n\
     @[reducible] def probeAttrLow : ProbeAttrC Nat := ⟨4⟩\n\
     attribute [instance] probeAttrBare\n\
     attribute [instance 100] probeAttrLow\n\
     def probeAttrN : Nat := ProbeAttrC.n (α := Nat)\n\
     theorem probeAttrN_eq : probeAttrN = 3 := rfl";

/// DECOY for [`ATTR_SURFACE`]: the same file claiming the LATER `low`
/// instance won. Must stay red — if it ever passes, the bare default sank to
/// 100 and tied.
const ATTR_SURFACE_DECOY: &str = "class ProbeAttrDC (α : Type) where\n  \
     n : Nat\n\
     @[reducible] def probeAttrDBare : ProbeAttrDC Nat := ⟨3⟩\n\
     @[reducible] def probeAttrDLow : ProbeAttrDC Nat := ⟨4⟩\n\
     attribute [instance] probeAttrDBare\n\
     attribute [instance 100] probeAttrDLow\n\
     def probeAttrDN : Nat := ProbeAttrDC.n (α := Nat)\n\
     theorem probeAttrDN_eq : probeAttrDN = 4 := rfl";

/// `instance` DECLARATION surface, same discriminator via `(priority := low)`.
const DECL_SURFACE: &str = "class ProbeDeclC (α : Type) where\n  \
     n : Nat\n\
     instance probeDeclBare : ProbeDeclC Nat := ⟨3⟩\n\
     instance (priority := low) probeDeclLow : ProbeDeclC Nat := ⟨4⟩\n\
     def probeDeclN : Nat := ProbeDeclC.n (α := Nat)\n\
     theorem probeDeclN_eq : probeDeclN = 3 := rfl";

/// DECOY for [`DECL_SURFACE`].
const DECL_SURFACE_DECOY: &str = "class ProbeDeclDC (α : Type) where\n  \
     n : Nat\n\
     instance probeDeclDBare : ProbeDeclDC Nat := ⟨3⟩\n\
     instance (priority := low) probeDeclDLow : ProbeDeclDC Nat := ⟨4⟩\n\
     def probeDeclDN : Nat := ProbeDeclDC.n (α := Nat)\n\
     theorem probeDeclDN_eq : probeDeclDN = 4 := rfl";

/// `(priority := mid)`. Lean's `mid` is **500** — strictly between `low` and
/// `default` (lean4 `src/Init/Notation.lean`: "This is lower than `default`,
/// and higher than `low`"). Clean mapped `mid` to 1000, collapsing it onto
/// `default`, so the LATER `mid` instance tied and won the recency tie-break.
const MID_SURFACE: &str = "class ProbeMidC (α : Type) where\n  \
     n : Nat\n\
     instance probeMidDefault : ProbeMidC Nat := ⟨3⟩\n\
     instance (priority := mid) probeMidMid : ProbeMidC Nat := ⟨5⟩\n\
     def probeMidN : Nat := ProbeMidC.n (α := Nat)\n\
     theorem probeMidN_eq : probeMidN = 3 := rfl";

/// DECOY for [`MID_SURFACE`]: claims the later `mid` instance won. This is
/// exactly what the pre-fix mapping produced, so it must stay red.
const MID_SURFACE_DECOY: &str = "class ProbeMidDC (α : Type) where\n  \
     n : Nat\n\
     instance probeMidDDefault : ProbeMidDC Nat := ⟨3⟩\n\
     instance (priority := mid) probeMidDMid : ProbeMidDC Nat := ⟨5⟩\n\
     def probeMidDN : Nat := ProbeMidDC.n (α := Nat)\n\
     theorem probeMidDN_eq : probeMidDN = 5 := rfl";

/// All four priority keywords in one file, for the ordering assertion.
const KEYWORD_SURFACE: &str = "class ProbeKwC (α : Type) where\n  \
     n : Nat\n\
     @[reducible] def probeKwLow : ProbeKwC Nat := ⟨1⟩\n\
     @[reducible] def probeKwMid : ProbeKwC Nat := ⟨2⟩\n\
     @[reducible] def probeKwDefault : ProbeKwC Nat := ⟨3⟩\n\
     @[reducible] def probeKwHigh : ProbeKwC Nat := ⟨4⟩\n\
     instance (priority := low) probeKwLowI : ProbeKwC Nat := ⟨1⟩\n\
     instance (priority := mid) probeKwMidI : ProbeKwC Nat := ⟨2⟩\n\
     instance (priority := default) probeKwDefaultI : ProbeKwC Nat := ⟨3⟩\n\
     instance (priority := high) probeKwHighI : ProbeKwC Nat := ⟨4⟩";

// ----------------------------------------------------------------------------
// Harness
// ----------------------------------------------------------------------------

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

/// Elaborate `source` into `env`, returning the first diagnostic if any
/// declaration fails.
fn elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_context = FileContext::new();
    let declarations =
        clean_parser::parse_file(source).map_err(|error| format!("parse error: {error}"))?;
    for declaration in &declarations {
        let processed = preprocess_decl_with_context(declaration, &mut file_context);
        match elaborate_decl_and_register(env, &processed) {
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

/// Priority recorded for `instance` inside `class`'s candidate list.
fn recorded_priority(env: &Environment, class: &str, instance: &str) -> Option<u32> {
    let target = Name::from_string(instance);
    env.get_class_instances(&Name::from_string(class))
        .iter()
        .find(|i| i.name == target)
        .map(|i| i.priority)
}

fn pinned_lib_path() -> PathBuf {
    clean_olean::require_pinned_lean_lib_path()
        .expect("real import probe requires the exact repository-pinned Lean standard library")
}

/// A prelude environment with a real `import Init` on top.
fn imported_env() -> Environment {
    let lib = pinned_lib_path();
    let mut env = Environment::with_prelude();
    load_module_with_deps(&mut env, "Init", &[lib])
        .unwrap_or_else(|e| panic!("importing Init must succeed: {e}"));
    env
}

// ----------------------------------------------------------------------------
// Lane 1 — builtin prelude (fast)
// ----------------------------------------------------------------------------

#[test]
fn attribute_instance_without_priority_is_lean_default_1000() {
    let mut env = Environment::with_prelude();
    elaborate_into(&mut env, ATTR_SURFACE).expect(
        "the bare `attribute [instance]` target must win over a later `low` (100) one: \
         Lean's unannotated attribute priority is `default` = 1000",
    );
    assert_eq!(
        recorded_priority(&env, "ProbeAttrC", "probeAttrBare"),
        Some(1000),
        "`attribute [instance] foo` with no priority must record Lean's `default` (1000)"
    );
    assert_eq!(
        recorded_priority(&env, "ProbeAttrC", "probeAttrLow"),
        Some(100),
        "`attribute [instance 100] foo` must record exactly 100 (control)"
    );
}

#[test]
fn attribute_instance_decoy_stays_red() {
    let mut env = Environment::with_prelude();
    assert!(
        elaborate_into(&mut env, ATTR_SURFACE_DECOY).is_err(),
        "DECOY: the later `low` (100) instance must NOT win against a bare (1000) one. \
         A pass here means the bare default sank to 100 and the recency tie-break took over."
    );
}

#[test]
fn instance_declaration_without_priority_is_lean_default_1000() {
    let mut env = Environment::with_prelude();
    elaborate_into(&mut env, DECL_SURFACE).expect(
        "an unannotated `instance` DECLARATION must win over a later \
         `(priority := low)` one",
    );
    assert_eq!(
        recorded_priority(&env, "ProbeDeclC", "probeDeclBare"),
        Some(1000),
        "an unannotated `instance` declaration must record Lean's `default` (1000)"
    );
    assert_eq!(
        recorded_priority(&env, "ProbeDeclC", "probeDeclLow"),
        Some(100),
        "`(priority := low)` must record exactly 100 (control)"
    );
}

#[test]
fn instance_declaration_decoy_stays_red() {
    let mut env = Environment::with_prelude();
    assert!(
        elaborate_into(&mut env, DECL_SURFACE_DECOY).is_err(),
        "DECOY: the later `(priority := low)` instance must NOT win against a bare one"
    );
}

/// `(priority := mid)` is Lean's 500, so it LOSES to an unannotated instance.
///
/// Pre-fix `mid` mapped to 1000: it tied with `default`, and the
/// most-recent-first tie-break handed the win to the later `mid` instance.
#[test]
fn priority_keyword_mid_is_500_and_loses_to_default() {
    let mut env = Environment::with_prelude();
    elaborate_into(&mut env, MID_SURFACE).expect(
        "`(priority := mid)` is 500 in Lean and must LOSE to an unannotated \
         (1000) instance, even when declared later",
    );
    assert_eq!(
        recorded_priority(&env, "ProbeMidC", "probeMidMid"),
        Some(500),
        "Lean's `mid` is 500 (src/Init/Notation.lean), not 1000"
    );
    assert_eq!(
        recorded_priority(&env, "ProbeMidC", "probeMidDefault"),
        Some(1000),
        "the unannotated instance is Lean's `default` = 1000 (control)"
    );
}

#[test]
fn priority_keyword_mid_decoy_stays_red() {
    let mut env = Environment::with_prelude();
    assert!(
        elaborate_into(&mut env, MID_SURFACE_DECOY).is_err(),
        "DECOY: a later `(priority := mid)` instance must NOT beat an \
         unannotated one. A pass here means `mid` collapsed onto `default`."
    );
}

/// Lean's documented invariant `low < mid < default < high`, with the exact
/// values from `src/Init/Notation.lean`.
#[test]
fn priority_keywords_match_lean_notation_values() {
    let mut env = Environment::with_prelude();
    elaborate_into(&mut env, KEYWORD_SURFACE).expect("keyword fixture must elaborate");
    let got = |inst: &str| recorded_priority(&env, "ProbeKwC", inst);
    assert_eq!(got("probeKwLowI"), Some(100), "Lean `low` = 100");
    assert_eq!(got("probeKwMidI"), Some(500), "Lean `mid` = 500");
    assert_eq!(got("probeKwDefaultI"), Some(1000), "Lean `default` = 1000");
    assert_eq!(got("probeKwHighI"), Some(10000), "Lean `high` = 10000");
    assert!(
        got("probeKwLowI") < got("probeKwMidI")
            && got("probeKwMidI") < got("probeKwDefaultI")
            && got("probeKwDefaultI") < got("probeKwHighI"),
        "Lean documents `low < mid < default` (< high); got \
         low={:?} mid={:?} default={:?} high={:?}",
        got("probeKwLowI"),
        got("probeKwMidI"),
        got("probeKwDefaultI"),
        got("probeKwHighI")
    );
}

/// The `@[instance]` target is registered under its **real class**, read off
/// the type's conclusion — never under the declaration name.
///
/// `command_elab_registry::register_instance_handler` stamps
/// `class_name: ctx.decl_name`, so were it on the dispatch path the candidate
/// list for `ProbeKeyC` would be empty and a bucket keyed by
/// `probeKeyBare` would exist instead. Both halves are asserted.
#[test]
fn instance_attr_handler_is_not_on_the_dispatch_path() {
    let source = "class ProbeKeyC (α : Type) where\n  \
         n : Nat\n\
         @[reducible] def probeKeyBare : ProbeKeyC Nat := ⟨7⟩\n\
         attribute [instance] probeKeyBare";
    let mut env = Environment::with_prelude();
    elaborate_into(&mut env, source).expect("fixture must elaborate");

    let under_class = env.get_class_instances(&Name::from_string("ProbeKeyC"));
    assert!(
        under_class
            .iter()
            .any(|i| i.name == Name::from_string("probeKeyBare")),
        "the instance must be keyed by its real class `ProbeKeyC`; found only: {:?}",
        under_class.iter().map(|i| &i.name).collect::<Vec<_>>()
    );
    assert!(
        env.get_class_instances(&Name::from_string("probeKeyBare"))
            .is_empty(),
        "no bucket may be keyed by the DECLARATION name — that is the \
         `class_name: ctx.decl_name` placeholder signature of \
         `command_elab_registry::register_instance_handler`, which must not be \
         on the dispatch path"
    );
}

// ----------------------------------------------------------------------------
// Lane 2 — real `import Init` (the configuration that actually competes)
// ----------------------------------------------------------------------------

/// Same discriminators, but with Lean's real `.olean` instances in the
/// environment — the configuration where Clean's numbers actually compete with
/// the ~3,000 imported ones rather than only with each other.
///
/// Batched into ONE import and ONE environment: the import dominates the
/// runtime, and each fixture uses distinct class and declaration names so they
/// cannot interfere. Every positive fixture ends in a `theorem … := rfl` that
/// only elaborates once synthesis has committed to the expected instance, so a
/// clean run IS the "which one does synthesis pick" observation; the recorded
/// priorities are asserted alongside so a pass cannot come from a resolution
/// accident.
///
/// The four opposite-direction decoys are deliberately left on the fast
/// prelude lane above: an `Environment` clone per decoy costs minutes here and
/// buys nothing the prelude lane does not already discriminate.
#[test]
fn unannotated_instances_are_1000_under_real_import_init() {
    let mut env = imported_env();
    eprintln!("import Init: {} constants in scope", env.num_constants());

    elaborate_into(&mut env, ATTR_SURFACE).expect(
        "under real `import Init`, the bare `attribute [instance]` target must \
         still win over a later `low` (100) one",
    );
    elaborate_into(&mut env, DECL_SURFACE).expect(
        "under real `import Init`, an unannotated `instance` declaration must \
         still win over a later `(priority := low)` one",
    );
    elaborate_into(&mut env, MID_SURFACE).expect(
        "under real `import Init`, `(priority := mid)` (500) must still LOSE to \
         an unannotated (1000) instance declared earlier",
    );

    for (class, instance, want) in [
        ("ProbeAttrC", "probeAttrBare", 1000),
        ("ProbeAttrC", "probeAttrLow", 100),
        ("ProbeDeclC", "probeDeclBare", 1000),
        ("ProbeDeclC", "probeDeclLow", 100),
        ("ProbeMidC", "probeMidDefault", 1000),
        ("ProbeMidC", "probeMidMid", 500),
    ] {
        assert_eq!(
            recorded_priority(&env, class, instance),
            Some(want),
            "under real `import Init`, `{instance}` must record priority {want}"
        );
    }
}
