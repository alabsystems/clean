// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression: the B101 homogeneous→heterogeneous bridge seed must not run
//! while an `import` declaration is being elaborated.
//!
//! ## The bug
//!
//! `elaborate_decl_and_register_inner` (`clean-elab/src/lib.rs`) calls
//! `hetero_bridge_seed::seed_hetero_bridges` once per declaration, at the very
//! top — and an `import` IS one of the declarations it handles, further down the
//! same function. So the seed ran BEFORE the import it was supposed to defer to.
//!
//! The seed installs `instHAdd`/`instHSub`/`instHMul` at
//! `BRIDGE_INSTANCE_PRIORITY` (50), chosen deliberately to sit below the
//! prelude's fused monomorphic `instHAddNat`/`instHSubNat`/`instHMulNat` (100).
//! Both of the `.olean` import's repair paths are first-writer-wins — the
//! constant is dropped as a name collision, and `register_real_instance_entries`
//! (`clean-olean/src/import/load_register.rs`) skips any name already in the
//! instance registry — so Lean's decoded priority (1000, `instHSub` is an
//! unannotated `instance` at `Init/Prelude.lean:1667`) was discarded every time.
//!
//! Measured under real `import Init` (93,252 constants), the resolver's ordered
//! candidate list for the ground goal `HSub Nat Nat Nat` was:
//!
//! ```text
//! String.instHSubRawSlice@1000  String.instHSubRawChar@1000  String.instHSubRaw@1000
//! instHSubNat@100  instHSubUInt64@100 … instHSubInt@100  instHSub@50
//! ```
//!
//! so `a - b` elaborated to `HSub.hSub … instHSubNat a b` where Lean produces
//! `HSub.hSub … (instHSub Nat instSubNat) a b`. `HDiv`/`HMod` have no bridge in
//! `BRIDGES`, so Lean's `instHDiv@1000` won there — and `/` and `%` were the
//! only Nat operators whose notation matched their own imported lemmas.
//!
//! ## Why it mattered
//!
//! `simp only [Nat.sub_sub]`, `simp only [Nat.sub_add_cancel]` and
//! `simp only [Nat.add_sub_cancel']` all failed under `import Init` while the
//! byte-identical goals written with Lean's stack spelled out
//! (`@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) …`) passed. The matcher
//! was never the problem; the elaborated instance surface was.
//!
//! ## What this test pins
//!
//! Hermetically, with no `.olean` anywhere: elaborating an `import` declaration
//! must leave the bridge constants alone, and the very next ordinary
//! declaration must still install them (the seed is idempotent and
//! self-healing, so a file whose imports do not supply the bridges is not left
//! without them).
//!
//! A test that only checked "the bridges exist after elaborating a file" would
//! pass either way — the seed runs on every declaration. The load-bearing
//! assertion is the one taken BETWEEN the import and the next declaration.

use clean_elab::{elaborate_decl_and_register_with_context, FileContext};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

/// The three constants `hetero_bridge_seed::BRIDGES` installs.
const BRIDGE_CONSTS: [&str; 3] = ["instHAdd", "instHSub", "instHMul"];

fn bridges_present(env: &Environment) -> Vec<&'static str> {
    BRIDGE_CONSTS
        .into_iter()
        .filter(|c| env.get_const(&Name::from_string(c)).is_some())
        .collect()
}

/// CORE REGRESSION: an `import` declaration must not trigger the seed.
///
/// The module named here does not exist, so the import is a no-op on the
/// environment — which is exactly what makes the assertion clean: anything the
/// bridge constants gain across this declaration came from the seed, not from
/// the import.
#[test]
fn test_import_declaration_does_not_seed_the_hetero_bridges() {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();

    let source = "import Clean.Test.NoSuchModule\ntheorem after_import : True := True.intro\n";
    let decls = parse_file(source).expect("the two-declaration fixture should parse");
    let mut decls = decls.into_iter();

    let import_decl = decls.next().expect("first declaration is the import");
    assert!(
        matches!(import_decl, clean_parser::SurfaceDecl::Import { .. }),
        "fixture drift: the first declaration must parse as an Import, got {import_decl:?}"
    );

    let before = bridges_present(&env);
    // The import itself may legitimately fail (the module does not exist); what
    // matters is the environment it leaves behind.
    let _ = elaborate_decl_and_register_with_context(&mut env, &import_decl, &mut file_ctx);
    let after_import = bridges_present(&env);

    assert_eq!(
        after_import, before,
        "elaborating an `import` must not seed the B101 bridge instances — \
         seeding here pre-empts the import that would supply Lean's own \
         `instHAdd`/`instHSub`/`instHMul` at Lean's real priority (1000), and \
         both import repair paths are first-writer-wins, so the seed's \
         priority-50 registration is permanent"
    );
}

/// GUARD: the seed must not be lost, only deferred. The declaration after the
/// import still installs every bridge, so a file whose imports do not supply
/// them is never left without them.
#[test]
fn test_the_declaration_after_an_import_still_seeds_the_bridges() {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();

    let source = "import Clean.Test.NoSuchModule\ntheorem after_import : True := True.intro\n";
    let decls = parse_file(source).expect("the two-declaration fixture should parse");
    let mut decls = decls.into_iter();

    let import_decl = decls.next().expect("first declaration is the import");
    let _ = elaborate_decl_and_register_with_context(&mut env, &import_decl, &mut file_ctx);

    let next_decl = decls.next().expect("second declaration is the theorem");
    let _ = elaborate_decl_and_register_with_context(&mut env, &next_decl, &mut file_ctx);

    let present = bridges_present(&env);
    assert_eq!(
        present,
        BRIDGE_CONSTS.to_vec(),
        "the bridge seed is deferred past an `import`, not dropped: the next \
         declaration must install every B101 bridge so a user `Add`/`Sub`/`Mul` \
         instance stays reachable through its operator"
    );
}

#[test]
fn prelude_in_seeded_environment_is_refused_without_seeding_bridges() {
    let mut env = Environment::try_with_prelude_for_import().expect("import prelude");
    let mut context = FileContext::new();
    assert!(
        bridges_present(&env).is_empty(),
        "import prelude leaves bridges to Init"
    );
    let declarations = parse_file("prelude\nimport Init.Prelude\n").expect("header fixture");
    assert!(matches!(
        &declarations[0],
        clean_parser::SurfaceDecl::Prelude { .. }
    ));
    assert!(
        elaborate_decl_and_register_with_context(&mut env, &declarations[0], &mut context).is_err(),
        "a prelude header cannot be accepted in a preseeded environment"
    );
    assert!(
        bridges_present(&env).is_empty(),
        "rejected header must not seed bridges before import"
    );
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned Lean");
    let mut expected = env.clone();
    clean_olean::load_module_with_deps(&mut expected, "Init.Prelude", &[lib])
        .expect("real baseline import");
    elaborate_decl_and_register_with_context(&mut env, &declarations[1], &mut context)
        .expect("real source import");
    for name in BRIDGE_CONSTS {
        let name = Name::from_string(name);
        let actual = env.get_const(&name).expect("imported bridge");
        let reference = expected.get_const(&name).expect("baseline bridge");
        assert_eq!(actual.type_, reference.type_, "{name} type");
        assert_eq!(actual.value, reference.value, "{name} body");
        assert_eq!(
            actual.level_params, reference.level_params,
            "{name} universes"
        );
        assert_eq!(
            env.instance_priority(&name),
            expected.instance_priority(&name),
            "{name} priority"
        );
    }
}

#[test]
fn ordinary_declaration_after_rejected_header_still_seeds_bridges() {
    let mut env = Environment::try_with_prelude_for_import().expect("import prelude");
    let mut context = FileContext::new();
    let declarations =
        parse_file("prelude\ntheorem after_header : True := True.intro\n").expect("header fixture");
    assert!(
        elaborate_decl_and_register_with_context(&mut env, &declarations[0], &mut context).is_err(),
        "a prelude header cannot be accepted in a preseeded environment"
    );
    assert!(bridges_present(&env).is_empty(), "header does not seed");
    elaborate_decl_and_register_with_context(&mut env, &declarations[1], &mut context)
        .expect("ordinary theorem");
    assert_eq!(bridges_present(&env), BRIDGE_CONSTS);
}
