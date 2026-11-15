// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A source choice reaches the real parser, genuine Init and ordinary
//! elaboration/registration. No handwritten recent-world prelude is used.

use clean_elab::module_driver::{
    module_environment_with_import_base_in_world, module_file_context_in_world,
    parse_module_in_world, EnvironmentSetup,
};
use clean_elab::{elaborate_decl_and_register_with_context, preprocess_decl_with_context};
use clean_kernel::lean_world::LeanWorld;
use clean_kernel::{BinderInfo, Environment, Expr, Name, TypeChecker};
use std::path::Path;

fn check_source(
    env: &mut Environment,
    choice: &clean_olean::SourceWorldDecision,
    source: &str,
) -> Result<(), String> {
    let path = Path::new("SelectedWorld.lean");
    let report = parse_module_in_world(path, source, choice)
        .1
        .map_err(|error| error.to_string())?;
    assert!(report.diagnostics.is_empty());
    let mut context = module_file_context_in_world(path, choice);
    assert_eq!(context.lean_world().unwrap(), choice.world());
    for decl in report.decls {
        let decl = preprocess_decl_with_context(&decl, &mut context);
        elaborate_decl_and_register_with_context(env, &decl, &mut context)
            .map_err(|error| error.to_string())?;
    }
    Ok(())
}

fn recent_world(world: LeanWorld) {
    std::thread::Builder::new().stack_size(128 << 20).spawn(move || {
        let choice = clean_olean::source_world_for_file(Path::new("SelectedWorld.lean"), Some(world)).unwrap();
        let (initial, import_base) = module_environment_with_import_base_in_world(EnvironmentSetup::default(), &choice).unwrap();
        assert_eq!(clean_olean::environment_world(&initial), Some(world.tag()));
        assert_eq!(clean_olean::environment_world(&import_base), Some(world.tag()));
        assert!(import_base.get_const(&Name::from_string("Nat")).is_none(), "Init must not be trusted as the kernel base");
        assert!(import_base.get_const(&Name::from_string("Decidable")).is_none());
        let mut import_gate = clean_olean::ImportedConeGate::new(&import_base);
        // Actual recent Init carries the Bool structure, never the oracle's
        // two-constructor Decidable. This detects a handwritten oracle fallback.
        let decidable = initial.get_inductive(&Name::from_string("Decidable")).unwrap();
        assert_eq!(decidable.constructor_names, vec![Name::from_string("Decidable.intro")]);
        // Both official worlds place this theorem in Init.Data.UInt.Bitwise,
        // not Init.Prelude. A genuine Prelude-only fallback must fail here.
        let full_init_witness = Name::from_string("UInt16.not_neg_one");
        assert!(initial.get_const(&full_init_witness).is_some(), "full Init must include UInt.Bitwise");
        assert!(import_base.get_const(&full_init_witness).is_none());

        for source in [
            "variable (x : Nat)\npublic def plainVariable : Nat := x\n",
            "private variable (x : Nat)\npublic def publicUsesPrivate : Nat := x\n",
            "public variable (x : Nat)\npublic def publicUsesPublic : Nat := x\n",
            "module\nprivate variable (x : Nat)\npublic def modulePrivate : Nat := x\n",
            "section\nprivate variable (x : Nat)\npublic def fromSection : Nat := x\nend\n",
            "private variable (x : Nat) in\npublic def localVariable : Nat := x\n",
            "private variable (x : Nat)\nvariable {x}\npublic def rebound : Nat := x\n",
        ] {
            let mut env = initial.clone();
            let result = check_source(&mut env, &choice, source);
            if world != LeanWorld::Lean436Rc2 && source.contains(" variable") {
                assert!(result.is_err(), "{world}: {source}");
                continue;
            }
            result.unwrap_or_else(|error| panic!("{world}: {source}: {error}"));
            // Public results have the native signature `(x : Nat) -> Nat`
            // (implicit after rebinding) and the identity body. Type-check the
            // actual stored value and require an empty axiom closure.
            let mut checked = 0;
            for name in ["plainVariable", "publicUsesPrivate", "publicUsesPublic", "modulePrivate", "fromSection", "localVariable", "rebound"] {
                let name = Name::from_string(name);
                if let Some(decl) = env.get_const(&name) {
                    checked += 1;
                    TypeChecker::new(&env).check_type(decl.value.as_ref().unwrap(), &decl.type_).unwrap();
                    let binder = if name == Name::from_string("rebound") { BinderInfo::Implicit } else { BinderInfo::Default };
                    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
                    assert_eq!(decl.type_, Expr::pi(binder, nat.clone(), nat.clone()));
                    assert_eq!(decl.value.as_ref().unwrap(), &Expr::lam(binder, nat, Expr::bvar(0)));
                    assert!(env.axiom_deps(&name).unwrap().is_empty());
                    let verdict = import_gate.check(&env, &std::collections::BTreeSet::from([name.clone()]));
                    assert!(verdict.passed(false), "{world}: {}", verdict.refusal_summary(false));
                }
            }
            assert_eq!(checked, 1, "one actual declaration must be checked: {source}");
        }
        if world == LeanWorld::Lean436Rc2 {
            for source in [
                "private variable (x : Nat)\npublic def bad : Bool := x\n",
                "section\nprivate variable (x : Nat)\npublic def fromSection : Nat := x\nend\nset_option autoImplicit false\ndef outside : Nat := x\n",
                "public variable (x : Nat) in\npublic def localVariable : Nat := x\nset_option autoImplicit false\ndef outside : Nat := x\n",
            ] {
                let mut env = initial.clone();
                assert!(check_source(&mut env, &choice, source).is_err(), "must refuse: {source}");
                assert!(env.get_const(&Name::from_string("bad")).is_none());
                assert!(env.get_const(&Name::from_string("outside")).is_none());
            }
        }
    }).unwrap().join().unwrap();
}

#[test]
fn selected_world_435_uses_genuine_init_and_keeps_old_variable_refusal() {
    recent_world(LeanWorld::Lean435);
}

#[test]
fn selected_world_436rc2_preserves_actual_variable_scope_and_public_signatures() {
    recent_world(LeanWorld::Lean436Rc2);
}

#[test]
fn visible_variable_ast_cannot_bypass_the_default_world_at_public_elaboration_entries() {
    let decl =
        clean_parser::parse_file_in_world("private variable (x : Nat)", LeanWorld::Lean436Rc2)
            .unwrap()
            .pop()
            .unwrap();
    let mut env = Environment::with_prelude();
    assert!(matches!(
        clean_elab::elaborate_decl(&env, &decl),
        Err(clean_elab::ElabError::SourceWorld(_))
    ));
    assert!(matches!(
        clean_elab::elaborate_decl_and_register(&mut env, &decl),
        Err(clean_elab::ElabError::SourceWorld(_))
    ));
}

#[test]
fn refused_project_world_refuses_its_imports_not_an_ordinary_declaration() {
    let project = tempfile::TempDir::new().unwrap();
    let path = project.path().join("RefusedWorld.lean");
    let source = "def refusedWorldDeclaration : Nat := 1\n";
    std::fs::write(
        project.path().join("lean-toolchain"),
        "leanprover/lean4:v4.99.0\n",
    )
    .unwrap();
    std::fs::write(&path, source).unwrap();
    let mut context = clean_elab::module_driver::module_file_context(&path);
    // R111 (restored 2026-11-13): the unknown v4.99.0 world refuses the run's
    // imports, naming itself; no Lean module resolves in it or in another.
    let refusal = context
        .effective_import_search_paths()
        .expect_err("unknown project world refuses every Lean import");
    assert!(refusal.to_string().contains("v4.99.0"), "{refusal}");
    // Its source language is the Oracle's and takes no feature decision of
    // the refused release: pinned v4.30.0-rc2 and v4.35.0 reject
    // `private variable` ("unexpected token 'variable'").
    let world = context
        .lean_world()
        .expect("a refused world parses in the Oracle's language");
    assert_eq!(world, LeanWorld::ORACLE);
    assert!(clean_parser::parse_file_in_world("private variable (x : Nat)\n", world).is_err());
    // An import-free ordinary declaration reaches the public declaration
    // entry in that language and registers, as every pinned Lean accepts it.
    let mut env = Environment::with_prelude();
    let decl = clean_parser::parse_file(source).unwrap().pop().unwrap();
    let decl = preprocess_decl_with_context(&decl, &mut context);
    let result = elaborate_decl_and_register_with_context(&mut env, &decl, &mut context);
    assert!(
        result.is_ok(),
        "the refused project world refuses imports, not the file: {result:?}"
    );
    assert!(env
        .get_const(&Name::from_string("refusedWorldDeclaration"))
        .is_some());
    assert!(
        context.effective_import_search_paths().is_err(),
        "registration must not clear the import refusal"
    );
}
