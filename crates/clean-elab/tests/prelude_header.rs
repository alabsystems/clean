// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
use clean_elab::module_driver::{module_environment_for_header_in_world, EnvironmentSetup};
use clean_elab::{elaborate_decl_and_register_with_context, FileContext};
use clean_kernel::{Environment, LeanWorld, Name};
use clean_parser::{parse_file_with_diagnostics, SurfaceDecl};

fn bare(source: &str) -> (Environment, Vec<SurfaceDecl>) {
    let parsed = parse_file_with_diagnostics(source).expect("parse header fixture");
    assert!(parsed.header.is_prelude);
    let decision = clean_olean::source_world_for_file(
        std::path::Path::new("/tmp/clean-prelude-header-test.lean"),
        Some(LeanWorld::ORACLE),
    )
    .expect("select pinned source world");
    let (env, base) = module_environment_for_header_in_world(
        EnvironmentSetup::default(),
        &decision,
        &parsed.header,
    )
    .expect("construct bare module");
    assert_eq!(env.num_constants(), 0);
    let base = base.environment();
    if parsed.header.imports.is_empty() {
        assert_eq!(base.num_constants(), 0);
    } else {
        assert!(base.is_canonical_foundational_axiom(&Name::from_string("propext")));
        assert!(
            base.get_const(&Name::from_string("Nat")).is_none(),
            "native prelude declarations must not shadow genuine imports"
        );
        assert!(base.is_canonical_foundational_axiom(&Name::from_string("Classical.choice")));
        base.check_foundation_premises(&Name::from_string("Classical.choice"))
            .expect("choice uses the canonical Nonempty family");
        for name in [
            "OfNat",
            "OfNat.ofNat",
            "sorry",
            "trustedArith",
            "Classical.em",
        ] {
            assert!(
                base.get_const(&Name::from_string(name)).is_none(),
                "unexpected {name}"
            );
        }
    }
    (env, parsed.decls)
}

#[test]
fn prelude_accepts_primitive_sorts_without_installing_session_support() {
    let (mut env, decls) = bare("prelude\naxiom A : Sort 1\naxiom a : A\n");
    let mut context = FileContext::new();
    for decl in decls {
        elaborate_decl_and_register_with_context(&mut env, &decl, &mut context)
            .expect("primitive declarations need no implicit Init");
    }
    assert!(env.get_const(&Name::from_string("A")).is_some());
    assert!(env.get_const(&Name::from_string("a")).is_some());
    for name in ["Nat", "PProd", "Bool", "Quot", "IO", "ULift", "instHAdd"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "unexpected {name}"
        );
    }
}

#[test]
fn prelude_without_import_cannot_use_nat() {
    let (mut env, decls) = bare("prelude\ndef leak : Nat := 0\n");
    let mut context = FileContext::new();
    elaborate_decl_and_register_with_context(&mut env, &decls[0], &mut context)
        .expect("header accepted in bare environment");
    assert!(elaborate_decl_and_register_with_context(&mut env, &decls[1], &mut context).is_err());
    assert!(env.get_const(&Name::from_string("leak")).is_none());
    assert!(env.get_const(&Name::from_string("Nat")).is_none());
}

#[test]
fn prelude_marker_refuses_a_preseeded_environment_without_mutating_it() {
    let decls = parse_file_with_diagnostics("prelude\n")
        .expect("header")
        .decls;
    let mut env = Environment::with_prelude();
    let before = env.num_constants();
    let mut context = FileContext::new();
    assert!(elaborate_decl_and_register_with_context(&mut env, &decls[0], &mut context).is_err());
    assert_eq!(env.num_constants(), before);
}

#[test]
fn prelude_cannot_gain_numerals_by_declaring_a_constant_named_nat() {
    let (mut env, decls) = bare("prelude\naxiom Nat : Sort 1\ndef leak : Nat := 0\n");
    let mut context = FileContext::new();
    for decl in &decls[..2] {
        elaborate_decl_and_register_with_context(&mut env, decl, &mut context)
            .expect("header and explicit type axiom");
    }
    assert!(elaborate_decl_and_register_with_context(&mut env, &decls[2], &mut context).is_err());
    assert!(env.get_const(&Name::from_string("leak")).is_none());
}

#[test]
fn prelude_import_base_contains_only_rechecked_logical_foundations() {
    let (env, _) = bare("prelude\nimport Init.Prelude\n");
    assert_eq!(env.num_constants(), 0);
}

#[test]
fn imported_option_coercions_use_the_visible_instance() {
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned SDK");
    let mut env = Environment::new();
    clean_olean::load_module_with_deps(&mut env, "Init.Prelude", std::slice::from_ref(&lib))
        .unwrap();
    let mut context = FileContext::new();
    let check = |env: &mut Environment, context: &mut FileContext, source: &str| {
        for decl in clean_parser::parse_file(source).unwrap() {
            let decl = clean_elab::preprocess_decl_with_context(&decl, context);
            let result = elaborate_decl_and_register_with_context(env, &decl, context)
                .map_err(|e| e.to_string())?;
            if let Some(message) = result.source_error_message() {
                return Err(message);
            }
            let mut leaves = Vec::new();
            result.checked_leaves(&mut leaves);
            for leaf in leaves {
                if let clean_elab::ElabResult::Failed { error, .. } = leaf {
                    return Err(error.to_string());
                }
            }
        }
        Ok::<_, String>(())
    };
    let implicit = "def wrap (n : Nat) : Option Nat := n\n";
    let mut local = Environment::default();
    let mut local_context = FileContext::new();
    check(
        &mut local,
        &mut local_context,
        "inductive Option (α : Type) where\n  | none : Option α\n  | some : α → Option α\naxiom X : Type\n",
    )
    .unwrap();
    assert!(check(
        &mut local,
        &mut local_context,
        "noncomputable def invented (x : X) : Option X := x\n",
    )
    .is_err());
    assert!(check(&mut env, &mut context, implicit).is_err());
    check(
        &mut env,
        &mut context,
        "def explicit (n : Nat) : Option Nat := Option.some n\n",
    )
    .unwrap();

    clean_olean::load_module_with_deps(&mut env, "Init.Data.Option.Coe", &[lib]).unwrap();
    check(&mut env, &mut context, implicit).unwrap();
    check(
        &mut env,
        &mut context,
        "def poly.{u} {α : Type u} (x : α) : Option α := x\n",
    )
    .unwrap();
    let mut used = std::collections::HashSet::new();
    env.get_const(&Name::interned("wrap"))
        .unwrap()
        .value
        .as_ref()
        .unwrap()
        .used_constants_dag(
            clean_kernel::expr::UsedConstants::WithProjectionStructures,
            &mut used,
        );
    assert!(used.contains(&Name::interned("optionCoe")), "{used:?}");
    check(
        &mut env,
        &mut context,
        "example (n : Nat) : Eq (wrap n) (Option.some n) := Eq.refl _\n",
    )
    .unwrap();
    let erased = check(
        &mut env,
        &mut context,
        "section\nattribute [-instance] optionCoe\ndef erased (n : Nat) : Option Nat := n\nend\n",
    )
    .unwrap_err();
    assert!(erased.contains("Option"), "{erased}");
    assert!(env.get_const(&Name::interned("erased")).is_none());
    check(
        &mut env,
        &mut context,
        r#"
section
local instance (priority := 2000) skip : Coe Nat (Option Nat) where
  coe _ := Option.none
def fromLocal (n : Nat) : Option Nat := n
example (n : Nat) : Eq (fromLocal n) Option.none := Eq.refl _
end
def afterScope (n : Nat) : Option Nat := n
example (n : Nat) : Eq (afterScope n) (Option.some n) := Eq.refl _
"#,
    )
    .unwrap();
}
