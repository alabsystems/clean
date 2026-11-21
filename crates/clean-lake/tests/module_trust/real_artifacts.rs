// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Module trust over metadata that must survive a REAL `clean lake build`
//! artifact round trip: csimp body snapshots, definition exposure and alias
//! telescopes, each read back from the built `.olean` and used by a
//! dependent build.

use super::*;

#[test]
fn csimp_body_snapshots_survive_real_lake_artifacts() {
    use clean_kernel::env::csimp;
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path();
    write_project(dir, &["CsBase", "CsA", "CsB", "CsMain"], &[
        ("CsBase", "def slow : Nat := 1\ndef fast : Nat := 2\ndef final : Nat := 3"),
        ("CsA", "import CsBase\naxiom globalRule : slow = fast\nattribute [csimp] globalRule\ndef fromA : Nat := slow\nsection\naxiom localRule : slow = final\nattribute [local csimp] localRule\ndef localBody : Nat := slow\nend\nnamespace N\naxiom scopedRule : slow = final\nattribute [scoped csimp] scopedRule\ndef scopedBody : Nat := slow\nend N\ndef afterA : Nat := slow"),
        ("CsB", "import CsBase\ndef fromB : Nat := slow"),
        ("CsMain", "import CsA\nimport CsB\ndef payloadRoot : Nat := slow"),
    ]);
    let result = build(dir);
    assert!(result.failed.is_empty(), "{result:?}");
    assert!(!read_payload(&olean(dir, "CsA")).1.csimp.is_empty());
    let (mut env, _) = load(dir, "CsMain");
    assert!(!csimp::has_invalid_metadata(&env));
    assert!(
        env.is_csimp(&name("globalRule")),
        "imported attribute query"
    );
    // Init's own compiler rules are visible too, as the implicit `import
    // Init` makes them: the subject is the rule replacing `slow`.
    let replacing_slow =
        |rules: Vec<csimp::Rule>| rules.into_iter().find(|r| r.from == name("slow"));
    assert_eq!(
        replacing_slow(csimp::rules_for(&env, None)).map(|r| r.theorem),
        Some(name("globalRule")),
        "programmatic loaded environment"
    );
    for (owner, target) in [
        ("fromA", Some("fast")),
        ("afterA", Some("fast")),
        ("localBody", Some("final")),
        ("N.scopedBody", Some("final")),
        ("fromB", None),
        ("payloadRoot", Some("fast")),
    ] {
        let rule = replacing_slow(csimp::rules_for(&env, Some(&name(owner))));
        assert_eq!(rule.map(|r| r.to), target.map(name), "{owner}");
    }
    csimp::begin_source_module(&mut env, name("User"), vec![name("CsMain")]);
    assert_eq!(
        replacing_slow(csimp::rules_for(&env, None)).map(|r| r.theorem),
        Some(name("globalRule"))
    );
    let tokens =
        csimp::activate_namespace(&mut env, &name("N")).expect("imported scoped definition");
    assert_eq!(tokens.len(), 1);
    assert_eq!(
        replacing_slow(csimp::rules_for(&env, None)).map(|r| r.theorem),
        Some(name("N.scopedRule"))
    );
    for token in tokens {
        csimp::retire_local(&mut env, token);
    }
    assert_eq!(
        replacing_slow(csimp::rules_for(&env, None)).map(|r| r.theorem),
        Some(name("globalRule"))
    );
    let (mut source_env, _) = builder_base();
    let mut context = clean_elab::FileContext::new();
    context.set_main_module(name("SourceUser"));
    context.set_import_search_paths(load_paths(dir));
    let parsed = clean_parser::parse_file_with_diagnostics(
        "import CsMain\ndef importedCaller : Nat := slow",
    )
    .expect("importer source");
    assert!(parsed.diagnostics.is_empty());
    for decl in parsed.decls {
        let decl = clean_elab::preprocess_decl_with_context(&decl, &mut context);
        let result = clean_elab::elaborate_decl_and_register_with_context(
            &mut source_env,
            &decl,
            &mut context,
        )
        .expect("source import and body");
        assert!(!matches!(result, ElabResult::Failed { .. }));
    }
    assert!(!csimp::has_invalid_metadata(&source_env));
    assert_eq!(
        replacing_slow(csimp::rules_for(&source_env, Some(&name("importedCaller"))))
            .map(|r| r.theorem),
        Some(name("globalRule"))
    );
    tamper(dir, "CsA", |payload| {
        payload.csimp[0].data = clean_kernel::env::EnvExtensionEntryData::Object(vec![1, 2, 3]);
    });
    let (mut corrupt, _) = builder_base();
    let error = clean_olean::load_module_with_deps(&mut corrupt, "CsA", &load_paths(dir))
        .expect_err("malformed compiler context must refuse the artifact");
    assert!(
        error.to_string().contains("invalid compiler context"),
        "{error}"
    );
}

#[test]
fn definition_exposure_survives_real_lake_artifacts() {
    let tmp = tempfile::tempdir().expect("tmp");
    for (tag, exposed) in [("hidden", false), ("exposed", true)] {
        let dir = tmp.path().join(tag);
        let attr = if exposed { "@[expose] " } else { "" };
        let source = format!("module\n{attr}public def slow (x : Nat) : Nat := x\n{attr}public def fast (x : Nat) : Nat := x\n");
        write_project(&dir, &["ExposureBase"], &[("ExposureBase", &source)]);
        let result = build(&dir);
        assert!(result.failed.is_empty(), "{tag}: {result:?}");
        let payload = read_payload(&olean(&dir, "ExposureBase")).1;
        for n in ["slow", "fast"] {
            assert!(
                payload.definition_exposure.contains(&(name(n), exposed)),
                "{tag}: {n}"
            );
        }
        let (env, _) = load(&dir, "ExposureBase");
        let view = clean_kernel::env::exposure::exporting_view(&env).expect("metadata");
        for n in ["slow", "fast"] {
            assert!(env
                .get_const(&name(n))
                .expect("runtime body")
                .value
                .is_some());
            assert_eq!(
                view.get_const(&name(n))
                    .expect("export view")
                    .value
                    .is_some(),
                exposed
            );
        }
        write_project(&dir, &["ExposureUse"], &[("ExposureUse", "module\npublic import ExposureBase\npublic theorem replacement : slow = fast := rfl\n")]);
        let result = build(&dir);
        assert_eq!(result.failed.is_empty(), exposed, "{tag}: {result:?}");
    }
}

#[test]
fn alias_telescopes_and_exposure_survive_real_lake_artifacts() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path();
    let source = "module\npublic def original.{u} {α : Type u} (x : α) : α := x\npublic alias copied := original\npublic theorem equivalence {α : Type} (x y : α) : (x = y) ↔ (y = x) := ⟨Eq.symm, Eq.symm⟩\npublic alias ⟨forward, backward⟩ := equivalence\n";
    write_project(dir, &["AliasBase"], &[("AliasBase", source)]);
    let result = build(dir);
    assert!(result.failed.is_empty(), "alias source: {result:?}");
    let (env, _) = load(dir, "AliasBase");
    let original = env.get_const(&name("original")).expect("original");
    let copied = env.get_const(&name("copied")).expect("copied");
    assert_eq!(copied.type_, original.type_);
    assert_eq!(copied.level_params, original.level_params);
    let view = clean_kernel::env::exposure::exporting_view(&env).expect("metadata");
    assert!(view
        .get_const(&name("copied"))
        .expect("alias view")
        .value
        .is_some());
    for alias in ["forward", "backward"] {
        assert_eq!(
            env.get_const(&name(alias)).expect("theorem alias").kind,
            ConstantKind::Theorem
        );
        assert!(env
            .axiom_deps(&name(alias))
            .expect("axiom closure")
            .is_empty());
    }
    write_project(dir, &["AliasUse"], &[("AliasUse", "module\npublic import AliasBase\npublic theorem same : @copied = @original := rfl\npublic theorem symmetry (x y : Nat) (h : x = y) : y = x := forward x y h\n")]);
    let result = build(dir);
    assert!(result.failed.is_empty(), "artifact consumer: {result:?}");
    fs::write(
        dir.join("AliasUse.lean"),
        "module\npublic import AliasBase\npublic theorem bad : copied Nat 0 = 0 := rfl\n",
    )
    .expect("negative consumer");
    let result = build(dir);
    assert!(
        !result.failed.is_empty(),
        "implicit carrier cannot be supplied positionally: {result:?}"
    );
}
