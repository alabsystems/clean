// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! P1_IMPORT review (2026-09-26): the per-module large-elimination decision
//! (`Environment::recompute_imported_large_elim`) and the incremental
//! projection field-table recovery (`import/projection_scan.rs`), measured on
//! a module the PINNED Lean compiled (`tests/fixtures/lean/v4.30.0-rc2/
//! import_passes/`, see its README) and loaded through the entry `clean
//! check` reaches, `load_typed_module_with_deps_bounded_shared`.
//!
//! The ground truth for large elimination is Lean's own kernel verdict, read
//! from the same `.olean`: `add_inductive_fn::init_elim_level`
//! (`src/kernel/inductive.cpp`, after `declare_inductive_types` and
//! `declare_constructors`) gives a large-eliminating recursor one more
//! universe parameter than its inductive. The field-table arm checks the end
//! state against the whole-environment scan the incremental index replaced:
//! running that scan after the import must change nothing.

use super::load_register::{projection_fn_target, register_structure_fields_from_projections};
use crate::test_support::compiled_fixture_dir;
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn load() -> Environment {
    let dir = compiled_fixture_dir("import_passes");
    let mut env = Environment::new();
    let mut visited = hashbrown::HashSet::new();
    crate::load_typed_module_with_deps_bounded_shared(
        &mut env,
        &n("ImportPasses"),
        &[dir],
        4,
        &mut visited,
    )
    .expect("the pinned-Lean ImportPasses module loads");
    env
}

/// Lean's verdict: the imported recursor carries the motive universe.
fn lean_large(env: &Environment, ind: &str) -> bool {
    let ind_val = env
        .get_inductive(&n(ind))
        .unwrap_or_else(|| panic!("{ind} should be a resident inductive"));
    let rec = env
        .get_recursor(&n(ind).str("rec"))
        .unwrap_or_else(|| panic!("{ind}.rec should be a resident recursor"));
    rec.level_params.len() > ind_val.level_params.len()
}

fn clean_large(env: &Environment, ind: &str) -> bool {
    env.get_inductive(&n(ind))
        .unwrap_or_else(|| panic!("{ind} should be a resident inductive"))
        .is_large_elim
}

/// Every `ImportPasses.*` inductive, with the pinned Lean verdict for it.
const AGREEING: [(&str, bool); 12] = [
    ("ImportPasses.N", true),
    ("ImportPasses.Idx", true),
    ("ImportPasses.NotIdx", false),
    ("ImportPasses.NE", false),
    ("ImportPasses.MA", false),
    ("ImportPasses.MB", false),
    ("ImportPasses.MA.below", false),
    ("ImportPasses.MB.below", false),
    ("ImportPasses.AtZero", true),
    ("ImportPasses.S", true),
    ("ImportPasses.Pair", true),
    ("ImportPasses.ViaDef", true),
];

#[test]
fn test_import_passes_fixture_large_elim_matches_lean_kernel_verdict() {
    let env = load();
    let mut resident: Vec<String> = env
        .inductives()
        .map(|ind| ind.name.to_string())
        .filter(|name| name.starts_with("ImportPasses."))
        .collect();
    resident.sort();
    let mut covered: Vec<String> = AGREEING
        .iter()
        .map(|(name, _)| (*name).to_string())
        .collect();
    covered.sort();
    assert_eq!(
        resident, covered,
        "every inductive the pinned Lean wrote is asserted here, and nothing else"
    );
    for (name, stated) in AGREEING {
        assert_eq!(
            lean_large(&env, name),
            stated,
            "{name}: the fixture's stated verdict is Lean's"
        );
        assert_eq!(
            clean_large(&env, name),
            stated,
            "{name}: Clean's import must reach Lean's verdict"
        );
    }
}

/// The previously pinned divergence is closed: same-part definitions are resident
/// before the derived elimination flag is computed. Keep that improvement mandatory.
#[test]
fn test_import_passes_fixture_same_module_definition_field_matches_pinned_lean() {
    let env = load();
    let pred = env
        .get_const(&n("ImportPasses.Pred"))
        .expect("same-part Pred is resident");
    TypeChecker::new(&env)
        .check_type(
            pred.value.as_ref().expect("Pred has its real body"),
            &pred.type_,
        )
        .expect("same-part Pred body type checks");
    assert!(
        lean_large(&env, "ImportPasses.ViaDef"),
        "Lean: `h : Pred n` is a Prop field, so large elimination"
    );
    assert!(
        clean_large(&env, "ImportPasses.ViaDef"),
        "Clean must decide the same Prop field with Pred resident"
    );
}

#[test]
fn test_import_passes_fixture_field_tables_equal_whole_environment_scan() {
    let env = load();
    let fields = |s: &str| -> Option<Vec<String>> {
        env.get_structure_field_names(&n(s))
            .map(|fs| fs.iter().map(ToString::to_string).collect())
    };
    // A `structure`: the table comes from Lean's structure extension.
    assert_eq!(
        fields("ImportPasses.S"),
        Some(vec!["a".to_string(), "b".to_string()])
    );
    // A structure-LIKE `inductive` has no extension entry; its numeric
    // projections elaborate to raw `Expr.proj`, which only the projection-
    // derived pass reads. This is the only arm here that the incremental
    // index alone decides.
    let first = env
        .get_const(&n("ImportPasses.Pair.first"))
        .and_then(|c| c.value.clone())
        .expect("Pair.first carries its value");
    assert_eq!(
        projection_fn_target(&first),
        Some((n("ImportPasses.Pair"), 0)),
        "the pinned Lean writes `p.1` on an inductive as a raw projection"
    );
    assert_eq!(
        fields("ImportPasses.Pair"),
        Some(vec!["first".to_string(), "second".to_string()])
    );
    // The replaced whole-environment scan, run over the finished import,
    // finds nothing the incremental index left undecided.
    let before = env.content_digest();
    let mut rescanned = env.clone();
    register_structure_fields_from_projections(&mut rescanned);
    assert_eq!(
        rescanned.content_digest().total,
        before.total,
        "the whole-environment scan must be a no-op after the incremental one"
    );
}

/// `NAME` in the oracle's schema (a root-first component list) as a dotted
/// string, for looking one constant up by name.
fn oracle_name(name: &serde_json::Value) -> String {
    name.as_array()
        .expect("an oracle NAME is a component list")
        .iter()
        .map(|component| match &component["value"] {
            serde_json::Value::String(s) => s.clone(),
            other => other.to_string(),
        })
        .collect::<Vec<_>>()
        .join(".")
}

/// Projection functions arriving as value-free STUBS that a later part of the
/// same artifact completes — the one shape in which Lean writes them so, read
/// here from the pinned Lean's own output rather than assumed. The whole-
/// environment scan found such projections by reading every constant after
/// the upgrade; the incremental index learns of them only through the names
/// the private part UPGRADED, since that part adds none of them. Both must end
/// with the same table.
///
/// Rebuilt 2026-09-28 from the P1_IMPORT review's synthetic arm, which loaded
/// the completing records as a SECOND, differently named module. No Lean-built
/// artifact has that shape: a module completing another's stub must import it
/// to name its structure, and then `lean` refuses the redeclaration
/// (measured, v4.30.0-rc2: "`P1Import.U.a` has already been declared"), as the
/// loader's rule 1 now does (`ConflictingDeclaration`).
#[test]
fn test_import_passes_fixture_projections_completed_by_the_private_part_register_the_table() {
    let dir = compiled_fixture_dir("import_passes");
    let parts: Vec<String> = ["olean", "olean.server", "olean.private"]
        .iter()
        .map(|ext| {
            dir.join(format!("ImportPassesStubs.{ext}"))
                .to_str()
                .expect("utf-8 fixture path")
                .to_string()
        })
        .collect();
    let args: Vec<&str> = parts.iter().map(String::as_str).collect();
    let oracle = crate::test_support::run_oracle(&args);
    let oracle_parts = oracle["parts"]
        .as_array()
        .expect("the oracle reads every part");
    assert_eq!(oracle_parts.len(), 3, "base, server and private parts");
    // What the pinned Lean wrote: the base and server parts state each
    // projection as an axiom with no value, the private part as a definition
    // with one.
    for (part, completed) in oracle_parts.iter().zip([false, false, true]) {
        for field in ["first", "second"] {
            let name = format!("StubParts.Pair.{field}");
            let constant = part["constants"]
                .as_array()
                .expect("constants")
                .iter()
                .find(|c| oracle_name(&c["name"]) == name)
                .unwrap_or_else(|| panic!("{} states {name}", part["path"]));
            assert_eq!(
                (constant["kind"].as_str(), constant["value"].is_null()),
                if completed {
                    (Some("definition"), false)
                } else {
                    (Some("axiom"), true)
                },
                "{name} in {}",
                part["path"]
            );
        }
    }

    let mut env = Environment::new();
    let mut visited = hashbrown::HashSet::new();
    crate::load_typed_module_with_deps_bounded_shared(
        &mut env,
        &n("ImportPassesStubs"),
        &[dir],
        4,
        &mut visited,
    )
    .expect("the pinned-Lean ImportPassesStubs artifact and its import load");
    for field in ["first", "second"] {
        let name = format!("StubParts.Pair.{field}");
        let value = env
            .get_const(&n(&name))
            .and_then(|c| c.value.clone())
            .unwrap_or_else(|| panic!("the private part completed {name}"));
        assert!(
            projection_fn_target(&value).is_some(),
            "{name} is a canonical projection once completed"
        );
    }
    let fields: Option<Vec<String>> = env
        .get_structure_field_names(&n("StubParts.Pair"))
        .map(|fs| fs.iter().map(ToString::to_string).collect());
    assert_eq!(
        fields,
        Some(vec!["first".to_string(), "second".to_string()]),
        "the completed projections register the table"
    );
    let before = env.content_digest();
    let mut rescanned = env.clone();
    register_structure_fields_from_projections(&mut rescanned);
    assert_eq!(
        rescanned.content_digest().total,
        before.total,
        "the whole-environment scan must be a no-op after the incremental one"
    );
}
