// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::external_lean::ExternalLeanInput;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::expr::{BigNat, MDataValue};
use clean_kernel::{BinderInfo, ExprKind, FVarId, LeanWorld, Literal};
use clean_olean::ImportWorld;
use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str =
    "prelude\nimport Init.Prelude\ninductive Leaf where\n  | off\n  | on\ndef targetVal : Leaf := Leaf.off\ndef extraComponent : Leaf := Leaf.on\n";
const SOURCE: &str = "prelude\nimport Init.Prelude\nimport Target\n\
universe u\n\
def identity {α : Sort u} (x : α) : α := x\n\
structure Metadata where\n  private mk ::\n  leaf : Leaf\n  reference : Lean.Name\n\
def alias : Leaf := targetVal\n\
def recorded : Metadata := ⟨alias, `extraComponent⟩\n\
def query (x : Leaf) : Leaf := identity (match x with | .off => recorded.leaf | .on => x)\n\
inductive Holds (a : Leaf) : Leaf → Prop where\n  | same : Holds a a\n\
theorem binding : Holds targetVal targetVal := Holds.same\n\
def unrelated : Leaf := Leaf.on\n\
axiom foreign : Leaf\n\
noncomputable def usesForeign : Leaf := foreign\n";

fn n(value: &str) -> Name {
    Name::from_string(value)
}
fn c(value: &str) -> Expr {
    Expr::const_(n(value), vec![])
}

fn sdk(file: &Path, world: LeanWorld) -> PathBuf {
    let world = clean_olean::source_world_for_file(file, Some(world)).unwrap();
    let Ok(ImportWorld::Explicit { lib, .. }) = world.imports() else {
        panic!("explicit Lean world")
    };
    lib.parent().unwrap().parent().unwrap().join("bin/lean")
}

fn compile_target(directory: &Path, source: &str, world: LeanWorld) {
    let file = directory.join("Target.lean");
    std::fs::write(&file, source).unwrap();
    let output = Command::new(sdk(&file, world))
        .current_dir(directory)
        .env_clear()
        .env("LEAN_PATH", directory)
        .arg("--root")
        .arg(directory)
        .arg("-o")
        .arg(directory.join("Target.olean"))
        .arg(&file)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "actual {world:?} target: {}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn program_at(
    directory: &Path,
    source: &str,
    world: LeanWorld,
) -> crate::external_lean::ExternalLeanInspection {
    let file = directory.join("Handoff.lean");
    std::fs::write(&file, source).unwrap();
    crate::external_lean::ExternalLeanInspection::elaborate(ExternalLeanInput {
        file: &file,
        module: &n("Handoff"),
        imports: &[n("Init.Prelude"), n("Target")],
        search_paths: &[directory.to_path_buf()],
        world,
    })
    .unwrap_or_else(|error| panic!("actual {world:?} source/import custody: {error}"))
}

pub(super) fn setup_world(
    world: LeanWorld,
) -> (
    tempfile::TempDir,
    crate::external_lean::ExternalLeanInspection,
) {
    let directory = tempfile::tempdir().unwrap();
    compile_target(directory.path(), TARGET, world);
    let program = program_at(directory.path(), SOURCE, world);
    (directory, program)
}

fn setup() -> (
    tempfile::TempDir,
    crate::external_lean::ExternalLeanInspection,
) {
    setup_world(LeanWorld::ORACLE)
}

pub(super) fn roots() -> Vec<Name> {
    vec![n("recorded"), n("query"), n("binding")]
}

#[test]
fn test_replayed_context_actual_private_family_import_and_expected_type() {
    let (_directory, program) = setup();
    let context = program
        .replay_context(&roots())
        .expect("real source/import cone must replay");
    assert!(context.replay_verdict().passed(false));
    assert!(context.replay_verdict().imported_axioms.is_empty());
    assert_eq!(context.roots().count(), 3);
    assert!(context
        .dependency_names()
        .any(|name| name == &n("targetVal")));
    let recorded = context.declaration(&n("recorded")).unwrap();
    assert!(recorded.is_source_owned());
    let imported = context
        .declaration(&n("targetVal"))
        .expect("real imported dependency is inspectable");
    assert!(!imported.is_source_owned());
    assert_eq!(imported.constant().value.as_ref(), Some(&c("Leaf.off")));
    assert!(imported.constructor().is_none());
    context
        .check_expected_type(
            &recorded,
            &[],
            &c("Metadata"),
            ReplayContextLimits::default(),
        )
        .expect("actual closed source type must check");
    context
        .check_expected_type(&imported, &[], &c("Leaf"), ReplayContextLimits::default())
        .expect("actual closed imported type must check");
    let binding = context.declaration(&n("binding")).unwrap();
    for (right, should_check) in [("targetVal", true), ("Leaf.on", false)] {
        let expected = Expr::app(Expr::app(c("Holds"), c("targetVal")), c(right));
        let checked =
            context.check_expected_type(&binding, &[], &expected, ReplayContextLimits::default());
        assert_eq!(
            checked.is_ok(),
            should_check,
            "indexed theorem expected type for {right}: {checked:?}"
        );
    }
    let reduced = context
        .whnf_closed(&c("recorded"), ReplayContextLimits::default())
        .unwrap();
    let ExprKind::Const(constructor_name, _) = reduced.get_app_fn().kind() else {
        panic!("actual record did not reduce to a constructor")
    };
    let constructor = context.declaration(constructor_name).unwrap();
    let metadata = constructor
        .constructor()
        .expect("actual private constructor role must be available");
    assert_eq!(metadata.inductive_name, n("Metadata"));
    assert_ne!(
        constructor_name,
        &n("Metadata").str("mk"),
        "private constructor identity must not be guessed"
    );
    let family = context.declaration(&metadata.inductive_name).unwrap();
    assert!(family
        .inductive()
        .unwrap()
        .constructor_names
        .contains(constructor_name));
    assert!(context
        .definitionally_equal(&c("alias"), &c("targetVal"), ReplayContextLimits::default())
        .unwrap());
    assert!(!context
        .definitionally_equal(&c("alias"), &c("Leaf.on"), ReplayContextLimits::default())
        .unwrap());
    println!("actual430rc2 replay context: private constructor family, imported component, full expected types, logical alias equality: PASS");
}

#[test]
fn test_replayed_context_foreign_owner_and_unreached_names_refuse() {
    let (directory, program) = setup();
    let other = program_at(directory.path(), SOURCE, LeanWorld::ORACLE);
    let context = program.replay_context(&roots()).unwrap();
    let foreign_context = other.replay_context(&roots()).unwrap();
    let foreign = foreign_context.declaration(&n("recorded")).unwrap();
    assert!(
        matches!(
            context.check_expected_type(
                &foreign,
                &[],
                &c("Metadata"),
                ReplayContextLimits::default()
            ),
            Err(ReplayContextError::ForeignOwner)
        ),
        "same source bytes and names must not manufacture same-program ownership"
    );
    assert!(matches!(
        context.declaration(&n("unrelated")),
        Err(ReplayContextError::OutsideCone { .. })
    ));
    assert!(
        matches!(
            context.definitionally_equal(
                &c("unrelated"),
                &c("unrelated"),
                ReplayContextLimits::default()
            ),
            Err(ReplayContextError::OutsideCone { .. })
        ),
        "reflexive candidates cannot admit an unreplayed declaration"
    );
    assert!(
        program.replay_context(&[n("targetVal")]).is_err(),
        "imported declarations cannot become source roots"
    );
    assert!(program.inspect_owned_declaration(&n("targetVal")).is_err());
    assert!(
        program.program.select(&n("targetVal"), 0).is_err(),
        "inspection must not grant imported native selection"
    );
    assert!(matches!(
        program.replay_context(&[]),
        Err(ExternalLeanError::Inspection(
            ReplayContextError::EmptyRoots
        ))
    ));
    println!("actual430rc2 replay context: different elaboration owner, outside cone and imported source selection refused: PASS");
}

#[test]
fn test_replayed_context_explicit_unreached_import_replay_keeps_source_rights_separate() {
    let (_directory, program) = setup();
    let context = program.replay_context(&roots()).unwrap();
    assert!(matches!(
        context.declaration(&n("extraComponent")),
        Err(ReplayContextError::OutsideCone { .. })
    ));
    let reference = context
        .whnf_closed(
            &Expr::proj(n("Metadata"), 1, c("recorded")),
            ReplayContextLimits::default(),
        )
        .unwrap();
    assert!(
        matches!(reference.get_app_fn().kind(), ExprKind::Const(name, _) if name == &n("Lean.Name.str"))
    );
    let fields = reference.get_app_args();
    assert_eq!(fields.len(), 2);
    assert!(
        matches!(fields[0].kind(), ExprKind::Const(name, _) if name == &n("Lean.Name.anonymous"))
    );
    let ExprKind::Lit(Literal::String(component)) = fields[1].kind() else {
        panic!("actual metadata field is not the expected structural Name literal")
    };
    let referenced = Name::anon().str(component);
    assert_eq!(referenced, n("extraComponent"));
    let expanded = context
        .with_replayed_declarations(&[referenced])
        .expect("an actual imported component can be independently replayed");
    assert_eq!(expanded.roots().count(), 3);
    assert_eq!(expanded.inspection_roots().count(), 4);
    assert!(expanded
        .replay_verdict()
        .roots
        .iter()
        .any(|name| name == "extraComponent"));
    let component = expanded.declaration(&n("extraComponent")).unwrap();
    assert!(!component.is_source_owned());
    assert_eq!(component.constant().value.as_ref(), Some(&c("Leaf.on")));
    expanded
        .check_expected_type(&component, &[], &c("Leaf"), ReplayContextLimits::default())
        .unwrap();
    assert!(
        context.declaration(&n("extraComponent")).is_err(),
        "replay expansion must not mutate the old view"
    );
    assert!(
        program.program.select(&n("extraComponent"), 0).is_err(),
        "imported inspection must not mint source selection"
    );
    let error = match context.with_replayed_declarations(&[n("usesForeign")]) {
        Err(error) => error,
        Ok(_) => panic!("new roots cannot waive foreign axioms"),
    };
    assert!(
        matches!(error, ExternalLeanError::Replay { ref verdict, .. } if verdict.imported_axioms.iter().any(|name| name == "foreign"))
    );
    assert!(
        context.declaration(&n("recorded")).is_ok(),
        "a refused expansion must preserve the original view"
    );
    assert!(matches!(
        context.with_replayed_declarations(&[n("missing")]),
        Err(ExternalLeanError::Inspection(
            ReplayContextError::MissingConstant { .. }
        ))
    ));
    println!("actual430rc2 replay context: explicitly replayed imported Name target, exact inspection roots, immutable old view, axiom refusal and unchanged source selection: PASS");
}

#[test]
fn test_replayed_context_closed_polymorphic_instantiation_and_malformed_candidates() {
    let (_directory, program) = setup();
    let context = program.replay_context(&roots()).unwrap();
    let identity = context.declaration(&n("identity")).unwrap();
    let expected = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(Level::succ(Level::zero())),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    context
        .check_expected_type(
            &identity,
            &[Level::succ(Level::zero())],
            &expected,
            ReplayContextLimits::default(),
        )
        .expect("explicit closed instantiation must retain actual polymorphic type");
    // Raw Level variants preserve shared DAGs instead of smart-constructor
    // simplification. Preflight must refuse BEFORE Expr construction hashes
    // their exponentially expanded paths, even with the smallest budgets.
    for impredicative in [false, true] {
        let mut shared_level = Level::zero();
        for _ in 0..64 {
            let shared = Arc::new(shared_level);
            shared_level = if impredicative {
                Level::IMax(shared.clone().into(), shared.into())
            } else {
                Level::Max(shared.clone().into(), shared.into())
            };
        }
        assert!(matches!(
            context.check_expected_type(
                &identity,
                std::slice::from_ref(&shared_level),
                &expected,
                ReplayContextLimits::new(32, 1, 1).unwrap()
            ),
            Err(ReplayContextError::NodeLimit)
        ));
        assert!(matches!(
            context.check_expected_type(
                &identity,
                &[shared_level.clone(), shared_level],
                &expected,
                ReplayContextLimits::new(1, 1, 1).unwrap()
            ),
            Err(ReplayContextError::UniverseArity {
                expected: 1,
                actual: 2
            })
        ));
    }
    let sort = Expr::sort(Level::succ(Level::zero()));
    assert!(matches!(
        context.definitionally_equal(
            &sort,
            &sort,
            ReplayContextLimits::new(3, 1000, 100).unwrap()
        ),
        Err(ReplayContextError::NodeLimit)
    ));
    let instantiated = Expr::const_(n("identity"), vec![Level::succ(Level::zero())]);
    assert!(matches!(
        context.definitionally_equal(
            &instantiated,
            &instantiated,
            ReplayContextLimits::new(23, 1000, 100).unwrap()
        ),
        Err(ReplayContextError::NodeLimit)
    ));
    let large_name = Expr::const_(Name::anon().str("x".repeat(1024)), vec![]);
    let large_string = Expr::from_kind(ExprKind::Lit(Literal::String("x".repeat(1024).into())));
    let large_nat = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![1; 1024]))));
    let metadata = Expr::mdata(
        vec![(n("source"), MDataValue::String("x".repeat(1024).into()))],
        c("Leaf.off"),
    );
    for payload in [large_name, large_string, large_nat, metadata] {
        assert!(
            matches!(
                context.whnf_closed(&payload, ReplayContextLimits::new(32, 1000, 100).unwrap()),
                Err(ReplayContextError::NodeLimit)
            ),
            "unmetered literal/Name/metadata payload entered the kernel"
        );
    }
    let recorded = context.declaration(&n("recorded")).unwrap();
    assert!(context
        .check_expected_type(&recorded, &[], &c("Leaf"), ReplayContextLimits::default())
        .is_err());
    assert!(context
        .check_expected_type(&identity, &[], &expected, ReplayContextLimits::default())
        .is_err());
    for open in [
        Expr::bvar(0),
        Expr::fvar(FVarId::new(7)),
        Expr::sort(Level::param(n("u"))),
    ] {
        assert!(matches!(
            context.definitionally_equal(&open, &open, ReplayContextLimits::default()),
            Err(ReplayContextError::OpenExpression)
        ));
    }
    let malformed = Expr::app(c("Leaf.off"), c("Leaf.off"));
    assert!(
        matches!(
            context.definitionally_equal(&malformed, &malformed, ReplayContextLimits::default()),
            Err(ReplayContextError::Kernel(_))
        ),
        "syntactic equality of ill-typed terms is no kernel equality result"
    );
    for (nodes, heartbeats, cache) in [(0, 10, 10), (10, 0, 10), (10, 10, 0)] {
        assert!(matches!(
            ReplayContextLimits::new(nodes, heartbeats, cache),
            Err(ReplayContextError::InvalidLimits)
        ));
    }
    assert!(matches!(
        context.definitionally_equal(
            &c("alias"),
            &c("alias"),
            ReplayContextLimits::new(1, 1000, 100).unwrap()
        ),
        Err(ReplayContextError::NodeLimit)
    ));
    assert!(
        context
            .whnf_closed(
                &c("recorded"),
                ReplayContextLimits::new(1000, 1, 100).unwrap()
            )
            .is_err(),
        "spent heartbeat budget must not publish under-reduced output"
    );
    println!("actual430rc2 replay context: closed universe instantiation; wrong/open/ill-typed and finite-budget refusals: PASS");
}

#[test]
fn test_replayed_context_tampered_import_and_foreign_axiom_still_fail_replay() {
    let (_directory, mut program) = setup();
    let error = match program.replay_context(&[n("usesForeign")]) {
        Err(error) => error,
        Ok(_) => panic!("foreign axiom was admitted"),
    };
    assert!(
        matches!(error, ExternalLeanError::Replay { ref verdict, .. } if verdict.imported_axioms.iter().any(|name| name == "foreign"))
    );
    let mut info = program
        .program
        .env
        .get_const(&n("targetVal"))
        .unwrap()
        .clone();
    info.value = Some(Expr::sort(Level::zero()));
    program.program.env.forget_decl(&info.name);
    // Test-only forged import: production exposes neither this environment
    // nor an API that installs caller-provided constant records.
    assert!(program
        .program
        .env
        .extend_constants_structural(std::iter::once(info))
        .is_empty());
    let error = match program.replay_context(&roots()) {
        Err(error) => error,
        Ok(_) => panic!("tampered imported body was admitted"),
    };
    assert!(
        matches!(error, ExternalLeanError::Replay { .. }),
        "actual corrupted dependency must fail fresh cone replay: {error}"
    );
    println!("actual430rc2 replay context: foreign axioms disclosed/refused; forged imported body refused: PASS");
}
