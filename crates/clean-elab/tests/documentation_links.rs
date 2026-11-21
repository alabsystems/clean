// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual parsed documentation attachments, registration, guard messages and
//! byte-to-source positions; the frozen oracle is Lean v4.30.0-rc2.

use clean_elab::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context_in_world,
    parse_module_in_world, DriverOptions, EnvironmentSetup, FailureIsolation, LeafOutcome,
    ModuleObserver, ModuleReport, VerdictKind,
};
use clean_kernel::{Environment, LeanWorld, Name, TypeChecker};
use clean_parser::SurfaceDecl;
use std::path::Path;

#[derive(Default)]
struct Diagnostics(Vec<(usize, usize, String)>);
impl ModuleObserver for Diagnostics {
    fn leaf_checked(&mut self, _env: &Environment, _decl: &SurfaceDecl, outcome: &LeafOutcome<'_>) {
        if let LeafOutcome::Checked {
            source_diagnostics, ..
        } = outcome
        {
            for diagnostic in *source_diagnostics {
                let span = diagnostic.span.expect("original doc location");
                self.0
                    .push((span.start, span.end, diagnostic.error.to_string()));
            }
        }
    }
}

fn check(
    source: &str,
    world: LeanWorld,
    isolation: FailureIsolation,
) -> (ModuleReport, Environment, Diagnostics) {
    let _lock = module_elaboration_lock();
    let path = Path::new("DocumentationLinks.lean");
    let choice = clean_olean::source_world_for_file(path, Some(world)).expect("selected world");
    let mut env = module_environment(EnvironmentSetup::default()).expect("source environment");
    let parsed = parse_module_in_world(path, source, &choice)
        .1
        .expect("source parses");
    assert!(
        parsed.diagnostics.is_empty(),
        "{source}\n{:#?}",
        parsed.diagnostics
    );
    let mut context = module_file_context_in_world(path, &choice);
    let mut diagnostics = Diagnostics::default();
    let report = elaborate_decls(
        &mut env,
        &parsed.decls,
        source,
        &mut context,
        DriverOptions {
            lean_front_door: true,
            isolation,
            ..DriverOptions::default()
        },
        &mut diagnostics,
    );
    (report, env, diagnostics)
}

fn checked_value(env: &Environment, name: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .expect("real declaration retained");
    TypeChecker::new(env)
        .check_type(info.value.as_ref().expect("real value"), &info.type_)
        .expect("kernel checks the actual stored value");
}

#[test]
fn nineteen_unquoted_frozen_controls_match_all_oracle_errors_and_positions() {
    let oracle: serde_json::Value = serde_json::from_str(include_str!(
        "../../../reports/manual-doc-links-2026-11-13/lean430-oracle.json"
    ))
    .expect("frozen oracle");
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../reports/manual-doc-links-2026-11-13/fixtures");
    let mut measured = 0;
    let mut rejected = 0;
    for case in oracle["cases"].as_array().expect("cases") {
        let name = case["case"].as_str().expect("name");
        // These have a separately recorded command-quotation gap, not doc
        // validation parity. Do not credit their earlier unsupported syntax.
        if name.contains("quoted-declaration") {
            continue;
        }
        let source =
            std::fs::read_to_string(fixtures.join(format!("{name}.lean"))).expect("fixture");
        let (report, _, diagnostics) =
            check(&source, LeanWorld::Lean430Rc2, FailureIsolation::Keep);
        let expected: Vec<_> = case["stdout"]
            .as_str()
            .expect("stdout")
            .lines()
            .filter_map(|line| {
                let (location, message) = line.split_once(": error: ")?;
                let mut parts = location.rsplit(':');
                let column: usize = parts.next()?.parse().ok()?;
                let line: usize = parts.next()?.parse().ok()?;
                Some((line, column, message.to_string()))
            })
            .collect();
        let actual: Vec<_> = diagnostics
            .0
            .iter()
            .map(|(start, end, message)| {
                assert!(end >= start && source.is_char_boundary(*end));
                let prefix = &source[..*start];
                let line = prefix.bytes().filter(|&b| b == b'\n').count() + 1;
                let column = prefix
                    .rsplit('\n')
                    .next()
                    .expect("current line")
                    .chars()
                    .count();
                (line, column, message.clone())
            })
            .collect();
        assert_eq!(actual, expected, "{name}\n{report:#?}");
        assert_eq!(
            report.verdicts.iter().any(|v| v.kind.is_failure()),
            case["returncode"].as_i64() != Some(0),
            "{name}: {report:#?}"
        );
        measured += 1;
        rejected += usize::from(!expected.is_empty());
    }
    assert_eq!((measured, rejected), (19, 12));
}

#[test]
fn legacy_worlds_keep_markdown_links_without_modern_validation() {
    let source = "/-- [](lean-manual://f) -/\ndef x : Nat := 44\n";
    for world in [LeanWorld::Lean408] {
        let (report, env, diagnostics) = check(source, world, FailureIsolation::Keep);
        assert!(!report.verdicts.is_empty());
        assert!(
            report
                .verdicts
                .iter()
                .all(|v| v.kind == VerdictKind::Passed),
            "{world}: {report:#?}"
        );
        assert!(diagnostics.0.is_empty());
        checked_value(&env, "x");
    }
}

#[test]
fn doc_errors_retain_actual_values_and_following_commands_even_with_rollback() {
    for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
        let source = "/-- [](lean-manual://f) -/\ndef x : Nat := 44\ndef y : Nat := x\n#check y\n";
        let (report, env, diagnostics) = check(source, LeanWorld::Lean430Rc2, isolation);
        assert_eq!(diagnostics.0.len(), 1);
        assert_eq!(
            report
                .verdicts
                .iter()
                .filter(|v| v.kind.is_failure())
                .count(),
            1,
            "{report:#?}"
        );
        checked_value(&env, "x");
        checked_value(&env, "y");
    }
}

#[test]
fn guard_consumes_only_executed_documentation_errors() {
    let source = "/-- error: Unknown documentation type `f`. Expected one of the following: `section`, `errorExplanation` -/\n#guard_msgs in\n/-- [](lean-manual://f) -/\ndef x : Nat := 44\ndef y := x\n";
    let (report, env, diagnostics) = check(source, LeanWorld::Lean430Rc2, FailureIsolation::Keep);
    assert!(
        report.verdicts.iter().all(|v| !v.kind.is_failure()),
        "{report:#?}"
    );
    assert!(
        diagnostics.0.is_empty(),
        "consumed guard errors are not emitted twice"
    );
    checked_value(&env, "x");
    checked_value(&env, "y");
}

#[test]
fn declaration_docs_do_not_duplicate_on_lifted_helpers() {
    let source = "/-- [](lean-manual://f) -/\ndef x : Nat := helper 44 where\n  helper (n : Nat) : Nat := n\ndef y := x\n";
    let (report, env, diagnostics) = check(source, LeanWorld::Lean430Rc2, FailureIsolation::Keep);
    assert_eq!(diagnostics.0.len(), 1, "{report:#?}");
    assert_eq!(
        report
            .verdicts
            .iter()
            .filter(|v| v.kind.is_failure())
            .count(),
        1,
        "{report:#?}"
    );
    assert!(
        report
            .verdicts
            .iter()
            .any(|v| v.name == "x.helper" && v.kind == VerdictKind::Passed),
        "helpers must remain separate checked leaves: {report:#?}"
    );
    checked_value(&env, "x");
    checked_value(&env, "y");
}

#[test]
fn constructor_and_class_projection_docs_attach_to_registered_members() {
    for source in [
        "inductive T where\n  /-- [](lean-manual://f) -/\n  | mk : T\n",
        "class C where\n  /-- [](lean-manual://f) -/\n  value : Nat\n",
    ] {
        let (report, env, diagnostics) =
            check(source, LeanWorld::Lean430Rc2, FailureIsolation::Keep);
        assert_eq!(diagnostics.0.len(), 1, "{source}\n{report:#?}");
        assert_eq!(
            report
                .verdicts
                .iter()
                .filter(|v| v.kind.is_failure())
                .count(),
            1
        );
        let member = if source.starts_with("inductive") {
            "T.mk"
        } else {
            "C.value"
        };
        assert!(env.get_const(&Name::from_string(member)).is_some());
    }
}

#[test]
fn compiler_and_documentation_errors_are_both_retained() {
    let source = "axiom runtime : Nat\n/-- [](lean-manual://f) -/\ndef x : Nat := runtime\n";
    let (report, env, diagnostics) = check(source, LeanWorld::Lean430Rc2, FailureIsolation::Keep);
    assert_eq!(diagnostics.0.len(), 2, "{report:#?}");
    assert!(diagnostics
        .0
        .iter()
        .any(|(_, _, message)| message.starts_with("Unknown documentation type")));
    assert!(diagnostics
        .0
        .iter()
        .any(|(_, _, message)| message.contains("noncomputable")));
    checked_value(&env, "x");
}

#[test]
fn mutual_function_members_validate_their_own_registered_docs() {
    let source = "mutual\n  /-- [](lean-manual://f) -/\n  def first : Nat := second\n  /-- [](lean-manual://section/) -/\n  def second : Nat := 44\nend\ndef later := first\n";
    let (report, env, diagnostics) = check(source, LeanWorld::Lean430Rc2, FailureIsolation::Keep);
    assert_eq!(diagnostics.0.len(), 2, "{report:#?}");
    assert_eq!(
        report
            .verdicts
            .iter()
            .filter(|v| v.kind.is_failure())
            .count(),
        2,
        "{report:#?}"
    );
    let first = report
        .verdicts
        .iter()
        .find(|v| v.name == "first")
        .expect("first");
    let second = report
        .verdicts
        .iter()
        .find(|v| v.name == "second")
        .expect("second");
    assert!(
        first
            .detail
            .as_deref()
            .is_some_and(|text| text.starts_with("Unknown documentation type")),
        "{report:#?}"
    );
    assert_eq!(second.detail.as_deref(), Some("Empty section ID"));
    assert_eq!(first.line, Some(2));
    assert_eq!(second.line, Some(4));
    assert_eq!(
        diagnostics.0[0].2, "Empty section ID",
        "dependency order: {report:#?}"
    );
    assert!(diagnostics.0[1].2.starts_with("Unknown documentation type"));
    checked_value(&env, "first");
    checked_value(&env, "second");
    checked_value(&env, "later");
}

#[test]
fn duplicate_constructor_docs_validate_only_the_authoritative_leading_comment() {
    let unknown = "Unknown documentation type `bogus`. Expected one of the following: `section`, `errorExplanation`";
    // Recent source worlds require genuine Init. The selected435 source
    // probe is explicitly timed out in the retained evidence, so this test
    // qualifies actual408/430 contexts; SDK435 oracles are retained separately.
    for world in [LeanWorld::Lean408, LeanWorld::Lean430Rc2] {
        for (leading, inner, invalid_leading) in [
            (
                "/-- α lean-manual://bogus/leading -/",
                "/-- β lean-manual://section/ok -/",
                true,
            ),
            (
                "/-- α lean-manual://section/ok -/",
                "/-- β lean-manual://bogus/inner -/",
                false,
            ),
        ] {
            for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
                let source = format!(
                    "inductive C where\n  {leading}\n  | {inner} mk\ndef later : C := C.mk\n"
                );
                let (report, env, diagnostics) = check(&source, world, isolation);
                let modern = world != LeanWorld::Lean408;
                let duplicate = if modern {
                    "Duplicate doc string"
                } else {
                    "duplicate doc string"
                };
                let mut expected = vec![duplicate];
                if modern && invalid_leading {
                    expected.push(unknown);
                }
                assert_eq!(
                    diagnostics
                        .0
                        .iter()
                        .map(|row| row.2.as_str())
                        .collect::<Vec<_>>(),
                    expected,
                    "{world:?}: {source}\n{report:#?}"
                );
                let start = source.find(leading).expect("leading position");
                assert_eq!(diagnostics.0[0].0, start);
                assert_eq!(diagnostics.0[0].1, start + leading.len());
                if modern && invalid_leading {
                    let start = source.find("lean-manual://bogus/leading").expect("URL");
                    assert_eq!(diagnostics.0[1].0, start);
                    assert_eq!(
                        diagnostics.0[1].1,
                        start + "lean-manual://bogus/leading".len()
                    );
                }
                assert!(env.get_const(&Name::from_string("C.mk")).is_some());
                checked_value(&env, "later");
                assert_eq!(
                    report
                        .verdicts
                        .iter()
                        .filter(|v| v.kind.is_failure())
                        .count(),
                    1
                );
            }
        }
    }
}

#[test]
fn guard_msgs_consumes_duplicate_and_leading_doc_error_after_registration() {
    let source = "/--\nerror: Duplicate doc string\n---\nerror: Unknown documentation type `bogus`. Expected one of the following: `section`, `errorExplanation`\n-/\n#guard_msgs in\ninductive C where\n  /-- α lean-manual://bogus/leading -/\n  | /-- β lean-manual://section/ok -/ mk\ndef later : C := C.mk\n";
    let (report, env, diagnostics) = check(source, LeanWorld::Lean430Rc2, FailureIsolation::Keep);
    assert!(
        diagnostics.0.is_empty(),
        "consumed once: {:?}",
        diagnostics.0
    );
    assert!(
        report.verdicts.iter().all(|v| !v.kind.is_failure()),
        "{report:#?}"
    );
    assert!(env.get_const(&Name::from_string("C.mk")).is_some());
    checked_value(&env, "later");
}

#[test]
fn projection_recursion_helper_does_not_duplicate_the_source_doc_attachment() {
    let source = include_str!(
        "../../../reports/doclink-independent-review-2026-11-14/controls/projection-helper-partial-guard.lean"
    );
    let (report, env, diagnostics) = check(source, LeanWorld::Lean430Rc2, FailureIsolation::Keep);
    assert!(
        diagnostics.0.is_empty(),
        "consumed once: {:?}",
        diagnostics.0
    );
    assert!(
        report.verdicts.iter().all(|v| !v.kind.is_failure()),
        "{report:#?}"
    );
    for name in ["Box.len", "Box.len.go"] {
        let info = env
            .get_const(&Name::from_string(name))
            .expect("both actual partial declarations retained");
        let _signature_sort = TypeChecker::new(&env)
            .infer_type(&info.type_)
            .expect("actual partial signature checks");
    }
}
