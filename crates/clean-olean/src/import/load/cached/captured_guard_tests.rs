use super::*;
use crate::OleanExporter;
use clean_kernel::{Declaration, Expr};
use std::collections::BTreeSet;

pub(super) fn bytes(name: &str, imports: &[(&str, bool)]) -> Vec<u8> {
    let mut env = Environment::default();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    OleanExporter::export_with_env(
        &env,
        imports,
        &[],
        "0000000000000000000000000000000000000000",
    )
    .unwrap()
}
pub(super) fn write(dir: &Path, module: &str, name: &str, imports: &[(&str, bool)]) {
    std::fs::write(dir.join(format!("{module}.olean")), bytes(name, imports)).unwrap();
}
fn refuse(module: &Name, reason: &str) -> ImportError {
    ImportError::UnsupportedModule {
        module: module.to_string(),
        reason: reason.to_owned(),
    }
}

#[test]
fn checked_load_registers_the_captured_bytes_after_callback_changes_disk() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("Root.olean");
    let original = bytes("Root.original", &[]);
    let replacement = bytes("Root.replacement", &[]);
    std::fs::write(&path, &original).unwrap();
    let mut env = Environment::default();
    let mut paths = Vec::new();
    let mut checked = Vec::new();
    let summaries = load_modules_with_deps_checked(
        &mut env,
        &["Root".into()],
        &[dir.path().into()],
        &mut |name, resolved, index| {
            paths.push((name.clone(), resolved.to_path_buf(), index));
            Ok(())
        },
        &mut |name, resolved, captured| {
            assert_eq!(resolved, path);
            assert_eq!(
                captured.canonical_path,
                std::fs::canonicalize(&path).unwrap()
            );
            assert_eq!(captured.base, original);
            assert!(
                captured.server.is_none() && captured.private.is_none() && captured.ir.is_none()
            );
            checked.push(name.clone());
            std::fs::write(&path, &replacement).unwrap();
            Ok(())
        },
    )
    .unwrap();
    assert_eq!(paths, [(Name::from_string("Root"), path.clone(), 0)]);
    assert_eq!(checked, [Name::from_string("Root")]);
    assert_eq!(summaries.len(), 1);
    assert!(env.get_const(&Name::from_string("Root.original")).is_some());
    assert!(env
        .get_const(&Name::from_string("Root.replacement"))
        .is_none());
    assert_eq!(std::fs::read(&path).unwrap(), replacement);
    let mut after = Environment::default();
    load_module_with_deps_cached(
        &mut after,
        "Root",
        &[dir.path().into()],
        &ModuleCache::new(),
    )
    .unwrap();
    assert!(after
        .get_const(&Name::from_string("Root.replacement"))
        .is_some());
}

#[test]
fn checked_load_refuses_later_root_dependency_before_registering_earlier_root() {
    let dir = tempfile::tempdir().unwrap();
    write(dir.path(), "Earlier", "Earlier.a", &[]);
    write(dir.path(), "Root", "Root.a", &[("Child", false)]);
    write(dir.path(), "Child", "Child.a", &[]);
    let mut env = Environment::default();
    let mut checked = Vec::new();
    let answer = load_modules_with_deps_checked(
        &mut env,
        &["Earlier".into(), "Root".into()],
        &[dir.path().into()],
        &mut |_, _, _| Ok(()),
        &mut |name, _, _| {
            checked.push(name.clone());
            if *name == Name::from_string("Child") {
                return Err(refuse(name, "manifest refuses this captured dependency"));
            }
            Ok(())
        },
    );
    assert!(
        matches!(answer, Err(ImportError::UnsupportedModule { reason, .. })
        if reason == "manifest refuses this captured dependency")
    );
    assert_eq!(checked, ["Earlier", "Root", "Child"].map(Name::from_string));
    assert_eq!(env.constants().count(), 0);
}

#[test]
fn checked_load_prepath_refusal_precedes_dependency_io() {
    let dir = tempfile::tempdir().unwrap();
    write(dir.path(), "Root", "Root.a", &[("Child", false)]);
    // The selected dependency is neither a valid module nor permitted input.
    std::fs::write(dir.path().join("Child.olean"), b"must not be captured").unwrap();
    let mut env = Environment::default();
    let mut captured = Vec::new();
    let answer = load_modules_with_deps_checked(
        &mut env,
        &["Root".into()],
        &[dir.path().into()],
        &mut |name, _, _| {
            if *name == Name::from_string("Child") {
                return Err(refuse(name, "selected path is unlisted"));
            }
            Ok(())
        },
        &mut |name, _, _| {
            captured.push(name.clone());
            Ok(())
        },
    );
    assert!(
        matches!(answer, Err(ImportError::UnsupportedModule { reason, .. })
        if reason == "selected path is unlisted")
    );
    assert_eq!(captured, [Name::from_string("Root")]);
    assert_eq!(env.constants().count(), 0);
}

#[test]
fn checked_graph_checks_real_unchecked_cache_hits_in_a_fresh_environment() {
    let dir = tempfile::tempdir().unwrap();
    write(dir.path(), "Root", "Root.a", &[("Child", false)]);
    write(dir.path(), "Child", "Child.a", &[]);
    let cache = ModuleCache::new();
    let paths = [dir.path().to_path_buf()];
    let mut unchecked = Environment::default();
    load_module_with_deps_cached(&mut unchecked, "Root", &paths, &cache).unwrap();
    for module in ["Root", "Child"] {
        let captured = CapturedModule::read(&dir.path().join(format!("{module}.olean"))).unwrap();
        assert!(
            cache.get_direct(&captured).is_some(),
            "must exercise real populated cache"
        );
    }
    // An authenticated population can also occupy the same cache. Neither
    // old unchecked provenance nor this real hit may suppress either guard.
    let mut authenticated = Environment::default();
    load_captured_graph(
        &mut authenticated,
        &[Name::from_string("Root")],
        &paths,
        &cache,
        false,
        Some(&mut |_, _, _| Ok(())),
        Some(&mut |_, _, _| Ok(())),
        true,
        None,
    )
    .unwrap();
    for module in ["Root", "Child"] {
        let path = dir.path().join(format!("{module}.olean"));
        let captured = CapturedModule::read(&path)
            .unwrap()
            .capture_ir(&path)
            .unwrap();
        assert!(
            cache.get_direct(&captured).is_some(),
            "must exercise checked-policy cache hit"
        );
    }
    let mut fresh = Environment::default();
    let mut checked = Vec::new();
    let result = load_captured_graph(
        &mut fresh,
        &[Name::from_string("Root")],
        &paths,
        &cache,
        false,
        Some(&mut |_, _, _| Ok(())),
        Some(&mut |name, _, _| {
            checked.push(name.clone());
            if *name == Name::from_string("Child") {
                return Err(refuse(name, "unchecked cache is not manifest authority"));
            }
            Ok(())
        }),
        true,
        None,
    );
    assert!(
        matches!(result, Err(ImportError::UnsupportedModule { reason, .. })
        if reason == "unchecked cache is not manifest authority")
    );
    assert_eq!(checked, ["Root", "Child"].map(Name::from_string));
    assert_eq!(fresh.constants().count(), 0);
    assert!(unchecked.get_const(&Name::from_string("Child.a")).is_some());
}

#[test]
fn checked_multi_root_load_matches_uncached_direct_population_and_order() {
    let dir = tempfile::tempdir().unwrap();
    write(dir.path(), "A", "A.a", &[("Shared", false)]);
    write(dir.path(), "B", "B.a", &[("Shared", false)]);
    write(dir.path(), "Shared", "Shared.a", &[]);
    let roots = ["A".into(), "B".into()];
    let paths = [dir.path().to_path_buf()];
    let mut ordinary = Environment::default();
    let ordinary_summaries =
        super::super::super::load_modules_with_deps(&mut ordinary, &roots, &paths).unwrap();
    let mut checked = Environment::default();
    let mut population = BTreeSet::new();
    let checked_summaries = load_modules_with_deps_checked(
        &mut checked,
        &roots,
        &paths,
        &mut |_, _, _| Ok(()),
        &mut |name, _, _| {
            assert!(population.insert(name.clone()));
            Ok(())
        },
    )
    .unwrap();
    assert_eq!(
        population,
        ["A", "B", "Shared"]
            .map(Name::from_string)
            .into_iter()
            .collect()
    );
    let names = |summaries: &[LoadSummary]| {
        summaries
            .iter()
            .map(|summary| (summary.module_name.clone(), summary.added_names.clone()))
            .collect::<Vec<_>>()
    };
    assert_eq!(names(&ordinary_summaries), names(&checked_summaries));
    for name in ["A.a", "B.a", "Shared.a"] {
        assert_eq!(
            ordinary.get_const(&Name::from_string(name)),
            checked.get_const(&Name::from_string(name))
        );
    }
}

#[test]
fn checked_capture_exposes_present_companions_before_their_decode() {
    let dir = tempfile::tempdir().unwrap();
    write(dir.path(), "Root", "Root.a", &[]);
    let path = dir.path().join("Root.olean");
    std::fs::write(
        path.with_extension("olean.server"),
        b"not a permitted server part",
    )
    .unwrap();
    std::fs::write(
        path.with_extension("olean.private"),
        b"not a permitted private part",
    )
    .unwrap();
    let mut env = Environment::default();
    let result = load_modules_with_deps_checked(
        &mut env,
        &["Root".into()],
        &[dir.path().into()],
        &mut |_, _, _| Ok(()),
        &mut |name, _, captured| {
            assert_eq!(
                captured.server,
                Some(b"not a permitted server part".as_slice())
            );
            assert_eq!(
                captured.private,
                Some(b"not a permitted private part".as_slice())
            );
            Err(refuse(name, "manifest includes neither companion"))
        },
    );
    assert!(
        matches!(result, Err(ImportError::UnsupportedModule { reason, .. })
        if reason == "manifest includes neither companion")
    );
    assert_eq!(env.constants().count(), 0);
}

#[test]
fn checked_load_freezes_absent_ir_and_late_binding_base_reads() {
    let fixture = crate::test_support::compiled_fixture_dir("implemented_by_late");
    let core = crate::pinned_lean_lib_path().expect("pinned Lean is required");
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("LateOk.olean");
    for extension in ["olean", "olean.server", "olean.private"] {
        let source = fixture.join("LateOk.olean").with_extension(extension);
        if source.is_file() {
            std::fs::copy(source, path.with_extension(extension)).unwrap();
        }
    }
    // The ordinary non-module fixture has compiled IR in its base artifact;
    // it is valid with no external .ir. Its recursive implemented_by binding
    // requires the real IR judgement to retain the empty late-binding record.
    let baseline =
        crate::lean_ir::module_ir::load_module_ir_at(&Name::from_string("LateOk"), &path)
            .expect("actual fixture IR must decode");
    assert!(!baseline.is_module);
    let roots = ["LateOk".to_owned()];
    let paths = [dir.path().to_path_buf(), core];
    let mut ordinary = Environment::with_prelude();
    super::super::super::load_modules_with_deps(&mut ordinary, &roots, &paths).unwrap();
    assert!(ordinary.compiled_before_record().is_none());
    let mut checked = Environment::with_prelude();
    let mut changed = false;
    load_modules_with_deps_checked(
        &mut checked,
        &roots,
        &paths,
        &mut |_, _, _| Ok(()),
        &mut |name, resolved, captured| {
            if *name == Name::from_string("LateOk") {
                assert_eq!(resolved, path);
                assert!(
                    captured.ir.is_none(),
                    "actual absence is part of the capture"
                );
                std::fs::write(&path, b"not the checked base artifact anymore").unwrap();
                std::fs::write(path.with_extension("ir"), b"new unlisted IR after capture")
                    .unwrap();
                changed = true;
            }
            Ok(())
        },
    )
    .unwrap();
    assert!(
        changed,
        "must execute actual post-capture filesystem mutation"
    );
    assert!(checked.get_const(&Name::from_string("recSlow")).is_some());
    assert_eq!(
        checked.compiled_before_record(),
        ordinary.compiled_before_record()
    );
    assert!(
        crate::lean_ir::module_ir::load_module_ir_at(&Name::from_string("LateOk"), &path).is_err(),
        "an accidental later filesystem reread must fail in this fixture"
    );
}
