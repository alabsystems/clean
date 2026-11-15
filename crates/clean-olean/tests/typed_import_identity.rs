// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Identity fidelity through the actual exported-file/direct-import entry point.
//! The explicit assumed import policy is not dependency-closed admission.
use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_olean::test_support::{compiled_fixture_dir, fixture_root};
use clean_olean::{
    load_olean_file_with_import_policy, OleanExporter, OleanImportPolicy, UnpinnedOleanImportPolicy,
};
use std::collections::BTreeSet;
use std::path::PathBuf;

fn policy() -> OleanImportPolicy {
    OleanImportPolicy::new(UnpinnedOleanImportPolicy::Allow)
}

fn definition(env: &mut Environment, name: Name, levels: Vec<Name>, ty: Expr, value: Expr) {
    env.add_decl(Declaration::Definition {
        name,
        level_params: levels,
        type_: ty,
        value,
        is_reducible: true,
    })
    .expect("fixture declaration must pass fresh kernel checking");
}

fn roundtrip(env: &Environment) -> Environment {
    let bytes =
        OleanExporter::export_with_env(env, &[], &[], "0000000000000000000000000000000000000000")
            .expect("export");
    let dir = tempfile::tempdir().expect("private fixture directory");
    let path = dir.path().join("TypedIdentity.olean");
    std::fs::write(&path, bytes).expect("fixture bytes");
    let mut imported = Environment::default();
    let summary =
        load_olean_file_with_import_policy(&mut imported, &path, policy()).expect("direct import");
    assert!(summary.skipped_constants.is_empty(), "{summary:?}");
    assert_eq!(summary.added_constants, env.constants().count());
    assert_eq!(summary.duplicate_constants, 0);
    assert_eq!(imported.constants().count(), env.constants().count());
    imported
}

fn unary_type() -> Expr {
    Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_())
}

#[test]
fn legacy_export_direct_import_preserves_distinct_owners_and_references() {
    let mut env = Environment::default();
    let names = [
        Name::anon().str("Alias").str("value"),
        Name::anon().str("Alias.value"),
        Name::anon().str("7"),
        Name::anon().str("07"),
        Name::anon().num(7),
        Name::anon().str(""),
    ];
    for (i, name) in names.iter().enumerate() {
        let value = Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            if i % 2 == 0 {
                Expr::bvar(0)
            } else {
                Expr::prop()
            },
        );
        definition(&mut env, name.clone(), vec![], unary_type(), value);
        definition(
            &mut env,
            Name::anon().str("reader").num(i as u64),
            vec![],
            unary_type(),
            Expr::const_(name.clone(), vec![]),
        );
    }
    let imported = roundtrip(&env);
    for expected in env.constants() {
        let actual = imported
            .get_const(&expected.name)
            .expect("exact typed identity");
        assert_eq!(actual.name, expected.name);
        assert_eq!(actual.type_, expected.type_);
        assert_eq!(actual.value, expected.value);
    }
    assert_ne!(
        imported.get_const(&names[0]).expect("hierarchical").value,
        imported.get_const(&names[1]).expect("quoted").value
    );
}

#[test]
fn legacy_export_direct_import_preserves_universe_parameters() {
    let mut env = Environment::default();
    for (i, level_name) in [
        Name::anon().str("u.dot"),
        Name::anon().str("u").str("dot"),
        Name::anon().str("07"),
        Name::anon().num(7),
    ]
    .into_iter()
    .enumerate()
    {
        let sort = Expr::sort(Level::param(level_name.clone()));
        let ty = Expr::pi(
            BinderInfo::Default,
            sort.clone(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        );
        let value = Expr::lam(
            BinderInfo::Default,
            sort,
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        );
        definition(
            &mut env,
            Name::anon().str("keep").num(i as u64),
            vec![level_name],
            ty,
            value,
        );
    }
    let imported = roundtrip(&env);
    for expected in env.constants() {
        let actual = imported
            .get_const(&expected.name)
            .expect("exact universe owner");
        assert_eq!(actual.level_params, expected.level_params);
        assert_eq!(actual.type_, expected.type_);
        assert_eq!(actual.value, expected.value);
    }
}

/// One artifact of a fixture family under `tests/fixtures/lean/<pin>/`, compiled
/// (or, for `numeric_probe`, generated) by the pinned Lean on first use. Fails
/// closed when the pinned toolchain is absent.
fn fixture_file(family: &str, file: &str) -> PathBuf {
    let path = compiled_fixture_dir(family).join(file);
    assert!(path.is_file(), "missing fixture: {}", path.display());
    path
}

/// Parse one line of a family's `CONSTANTS` file — a constant name in Lean
/// spelling, where `«…»` protects a single component from being split on `.`
/// (`Alias.value` is two components, `«Alias.value»` one, `«07»` the string
/// `"07"`).
fn lean_spelled_name(spelling: &str) -> Name {
    let mut name = Name::anon();
    let mut component = String::new();
    let mut quoted = false;
    for ch in spelling.chars() {
        match ch {
            '«' => quoted = true,
            '»' => quoted = false,
            '.' if !quoted => {
                name = name.str(std::mem::take(&mut component));
            }
            _ => component.push(ch),
        }
    }
    assert!(!quoted, "unterminated «…» in `{spelling}`");
    name.str(component)
}

/// The names `typed_names/CONSTANTS` lists (one per line, `#` comments and
/// blanks ignored), read from the checked-in family beside the source so the
/// expected constant count is derived from the fixture rather than typed here.
fn typed_names_constants() -> Vec<Name> {
    let path = fixture_root().join("typed_names").join("CONSTANTS");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", path.display()));
    let names: Vec<Name> = text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(lean_spelled_name)
        .collect();
    assert!(!names.is_empty(), "{} lists no constants", path.display());
    names
}

/// The `typed_names` family (`tests/fixtures/lean/v4.30.0-rc2/typed_names/README.md`),
/// a single `prelude` module with no imports, loaded directly. The lost original
/// this test was written against carried 20 constants; the re-authored fixture
/// carries the names `CONSTANTS` lists (10 on 2026-09-15, measured with Lean's
/// own `readModuleData`: `constNames = constants = 10`, `extraConstNames = 0`),
/// so the count is derived from that file, never typed.
#[test]
fn real_pinned_lean_quoted_identity_is_not_overwritten() {
    let expected = typed_names_constants();
    let mut env = Environment::default();
    let summary = load_olean_file_with_import_policy(
        &mut env,
        fixture_file("typed_names", "TypedNames.olean"),
        policy(),
    )
    .expect("pinned-Lean direct load");
    assert_eq!(summary.added_constants, expected.len(), "{summary:?}");
    assert_eq!(summary.duplicate_constants, 0);
    assert!(summary.skipped_constants.is_empty(), "{summary:?}");
    assert_eq!(env.constants().count(), expected.len());
    for name in &expected {
        assert!(
            env.get_const(name).is_some(),
            "CONSTANTS names {name:?} but the loaded module lacks it"
        );
    }
    let nested = Name::anon().str("Alias").str("value");
    let quoted = Name::anon().str("Alias.value");
    assert_ne!(
        env.get_const(&nested).expect("nested").value,
        env.get_const(&quoted).expect("quoted").value
    );
    for (reader, expected) in [
        ("readNested", nested),
        ("readQuoted", quoted),
        ("read07", Name::anon().str("07")),
    ] {
        let references = env
            .get_const(&Name::anon().str(reader))
            .expect("reader")
            .value
            .as_ref()
            .expect("body")
            .collect_constants();
        assert!(
            references.contains(&expected),
            "wrong {reader} reference: {references:?}"
        );
    }
    assert_eq!(
        env.get_const(&Name::anon().str("keep"))
            .expect("universe theorem")
            .level_params,
        [Name::anon().str("u.dot")]
    );
    let names: BTreeSet<String> = ["nestedExpected", "quotedExpected", "digitExpected"]
        .into_iter()
        .map(str::to_owned)
        .collect();
    let (passed, failed, errors) =
        clean_olean::verify_batch_full::typecheck_constants_full(&env, &names, 100_000);
    assert_eq!((passed, failed), (3, 0), "{errors:?}");
    assert!(errors.is_empty());
}

/// `numeric_probe/NumericProbeSupported.olean` (fixture family F4): six
/// `NumericProbe.*` definitions minted by `GenNumericProbe.lean` through Lean's
/// own `writeModule`, `imports = #[]`, each `: Type := Prop`. The six is the
/// generator's declared name list, and nothing else is declared.
#[test]
fn real_pinned_lean_supported_numeric_names_are_exact() {
    let mut env = Environment::default();
    let summary = load_olean_file_with_import_policy(
        &mut env,
        fixture_file("numeric_probe", "NumericProbeSupported.olean"),
        policy(),
    )
    .expect("supported numeric names");
    assert_eq!(summary.added_constants, 6, "{summary:?}");
    assert_eq!(env.constants().count(), 6);
    assert!(summary.skipped_constants.is_empty());
    let prefix = Name::anon().str("NumericProbe");
    for name in [
        prefix.clone().num(0),
        prefix.clone().num(7),
        prefix.clone().num(1u64 << 63),
        prefix.clone().str("0"),
        prefix.clone().str("7"),
        prefix.str("07"),
    ] {
        let actual = env
            .get_const(&name)
            .expect("exact supported numeric/string identity");
        assert_eq!(actual.name, name);
        assert_eq!(actual.type_, Expr::type_());
        assert_eq!(actual.value, Some(Expr::prop()));
    }
}

/// `numeric_probe/NumericProbeSeven.olean` (fixture family F5): the six names
/// above plus `NumericProbe.<2^64>`, whose `Name.num` component is a two-limb
/// mpz in the compacted region (measured in the family README). A reader that
/// carries the value in a `u64` must refuse the module, not truncate the name.
#[test]
fn real_pinned_lean_over_u64_name_is_explicit_refusal() {
    let mut env = Environment::default();
    let result = load_olean_file_with_import_policy(
        &mut env,
        fixture_file("numeric_probe", "NumericProbeSeven.olean"),
        policy(),
    );
    let error =
        result.expect_err("the seven-name population must not be truncated or silently renamed");
    assert!(error.to_string().contains("Nat"), "{error}");
    assert_eq!(
        env.constants().count(),
        0,
        "failed raw decode must not partially register this module"
    );
}
