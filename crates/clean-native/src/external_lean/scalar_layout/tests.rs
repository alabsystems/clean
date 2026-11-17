// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::checks::{c, lam, n, pi, Check};
use super::*;
use crate::external_lean::{ExternalLeanInput, ExternalLeanInspection};
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::Expr;
use std::collections::BTreeSet;

mod evidence;

const SOURCE: &str = "prelude\nimport Init.Prelude\ndef query (a b : UInt32) (c d : UInt64) : UInt64 := d\ndef wrong (a : Nat) : Nat := a\n";

fn actual(world: LeanWorld, full_init: bool) -> ExternalLeanInspection {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("Layout.lean");
    std::fs::write(
        &file,
        if full_init {
            SOURCE
                .strip_prefix("prelude\nimport Init.Prelude\n")
                .unwrap()
        } else {
            SOURCE
        },
    )
    .unwrap();
    ExternalLeanInspection::elaborate(ExternalLeanInput {
        file: &file,
        module: &n("Layout"),
        imports: &[n(if full_init { "Init" } else { "Init.Prelude" })],
        search_paths: &[],
        world,
    })
    .unwrap_or_else(|e| panic!("actual {world:?} source capture: {e}"))
}
fn facts(program: &ExternalLeanInspection) -> CheckedScalarLayoutFacts<'_> {
    program
        .inspect_scalar_layout(&n("query"), ReplayContextLimits::default())
        .unwrap_or_else(|e| panic!("actual {:?} logical facts: {e}", program.world()))
}
fn check_actual(world: LeanWorld) {
    let program = actual(world, false);
    let facts = facts(&program);
    assert_eq!(facts.world(), world);
    assert_eq!(facts.root(), &n("query"));
    assert!(facts.source_capture().is_complete());
    assert!(facts.replay_verdict().passed(false));
    assert!(facts.replay_verdict().imported_axioms.is_empty());
    let uncaptured: Vec<_> = facts
        .replay
        .members()
        .difference(facts.source_capture().members())
        .collect();
    println!("scalar_layout_uncaptured {} {:?}", world.tag(), uncaptured);
    assert!(
        uncaptured.is_empty(),
        "actual source replay consulted records outside combined capture"
    );
    for name in facts.context.dependency_names() {
        require_captured(facts.source_capture(), name).unwrap();
    }
    assert!(
        require_captured(facts.source_capture(), &n("escaped_member"))
            .unwrap_err()
            .contains("escaped")
    );
    evidence::retain(&program.program, &facts, "prelude");
    for (word, width) in [(ScalarLayoutWord::U32, 32), (ScalarLayoutWord::U64, 64)] {
        let fact = facts.word(word);
        assert_eq!(fact.width(), width);
        assert_eq!(fact.bound(), &Expr::nat_lit_u128(1u128 << width));
        // Both positive and wrong-bound candidates execute in the SAME actual
        // bounded source context, not an arithmetic sample as runtime proof.
        let power = Expr::apps(
            c("Nat.pow"),
            [Expr::nat_lit(2), Expr::nat_lit(u64::from(width))],
        );
        assert!(facts
            .context
            .definitionally_equal(&power, fact.bound(), ReplayContextLimits::default())
            .unwrap());
        assert!(!facts
            .context
            .definitionally_equal(
                &power,
                &Expr::nat_lit_u128((1u128 << width) + 1),
                ReplayContextLimits::default()
            )
            .unwrap());
    }
    let proof = facts.original_constant(&n("Fin.isLt")).unwrap();
    assert_eq!(proof.kind, clean_kernel::ConstantKind::Theorem);
    assert_eq!(proof.reducibility, clean_kernel::Reducibility::Opaque);
    for (name, external) in [
        ("Nat.add", "lean_nat_add"),
        ("Nat.mul", "lean_nat_mul"),
        ("Nat.pow", "lean_nat_pow"),
    ] {
        assert_eq!(facts.original_extern(&n(name)), Some(external));
    }
    assert!(facts.original_constant(&n("unrelated")).is_none());
    for result in [
        program.program.select(&n("query"), 0),
        program.program.select_in_runtime_closure(&n("query"), 0),
    ] {
        assert!(
            matches!(result, Err(super::super::ExternalLeanError::Compile(ref e)) if e.contains("logical inspection"))
        );
    }
    println!(
        "scalar_layout_actual {} {}",
        world.tag(),
        serde_json::json!({
            "source_members": facts.source_capture().members().len(), "replay": facts.replay_verdict(),
        "visited_recursors": facts.visited_recursors(),
        "inputs": facts.inputs().iter().map(|input| serde_json::json!({"path": input.path, "sha256": input.sha256, "bytes": input.bytes})).collect::<Vec<_>>(),
            "bound32": facts.word(ScalarLayoutWord::U32).bound(), "bound64": facts.word(ScalarLayoutWord::U64).bound(),
            "original_proof": proof, "original_bitvec_projection": facts.original_constant(&n("BitVec.toFin")),
            "original_pow_extern": facts.original_extern(&n("Nat.pow")), "native_calls": 0,
            "global_errors": program.source_capture().errors, "global_typed_failures": program.source_capture().row_failures.len(),
            "global_digest": program.source_capture().snapshot_blake3,
        })
    );
}

#[test]
fn scalar_layout_actual430_closed_source_facts_and_no_native_authority() {
    check_actual(LeanWorld::ORACLE);
}
#[test]
fn scalar_layout_actual435_closed_source_facts_and_no_native_authority() {
    check_actual(LeanWorld::Lean435);
}

#[test]
fn scalar_layout_actual435_full_init_keeps_global_failures_and_both_native_guards() {
    let program = actual(LeanWorld::Lean435, true);
    let facts = facts(&program);
    assert!(facts.source_capture().is_complete());
    evidence::retain(&program.program, &facts, "full-init");
    let global = program.source_capture();
    assert!(!global.errors.is_empty());
    assert!(!global.row_failures.is_empty());
    assert!(!global.delta_complete);
    assert!(global.snapshot_blake3.is_none());
    // Retain all actual typed failures rather than replacing them with the
    // successful logical replay verdict or only a representative summary.
    println!(
        "scalar_layout_full_init {}",
        serde_json::json!({"errors": global.errors, "row_failures": global.row_failures.iter().map(|row| serde_json::json!({"phase": row.phase, "name": row.name, "reason": row.reason})).collect::<Vec<_>>(), "limitations": global.limitations, "delta_complete": global.delta_complete, "digest": global.snapshot_blake3, "native_calls": 0})
    );
    assert!(program.program.select(&n("query"), 0).is_err());
    assert!(program
        .program
        .select_in_runtime_closure(&n("query"), 0)
        .is_err());
    // Even a private test-only forged Usage marker cannot make partial global
    // capture executable: both existing doors independently recheck it.
    drop(facts);
    let mut program = program.program;
    program.usage = super::super::inspection::Usage::Executable;
    for result in [
        program.select(&n("query"), 0),
        program.select_in_runtime_closure(&n("query"), 0),
    ] {
        assert!(
            matches!(result, Err(super::super::ExternalLeanError::Input(ref e)) if e.contains("incomplete source snapshot"))
        );
    }
}

// EXPLICITLY UNTRUSTED unit variants. This private fixture constructor is not
// a frontend custody producer and is never used to select, emit or load code.
fn variant(
    original: &ExternalLeanProgram,
    change: impl FnOnce(&mut clean_kernel::Environment),
) -> ExternalLeanProgram {
    let mut env = original.env.clone();
    change(&mut env);
    ExternalLeanProgram {
        custody: Arc::new(super::super::Custody {
            world: original.world(),
            source: Arc::new(env.clone()),
            base: Arc::clone(&original.custody.base),
            observation: original.source_capture().clone(),
            inputs: original.inputs().to_vec(),
            // This manufactured environment has no captured primary artifact.
            primary_artifact: Err(super::super::PrimaryArtifactError::MissingAssociation),
            _snapshot: tempfile::tempdir().unwrap(),
        }),
        env,
        base: original.base.clone(),
        module_names: original.module_names.clone(),
        usage: super::super::inspection::Usage::Inspection,
    }
}
fn replace_value(env: &mut clean_kernel::Environment, name: &str, value: Expr) {
    let mut info = env.get_const(&n(name)).unwrap().clone();
    info.value = Some(value);
    env.forget_decl(&n(name));
    assert!(env
        .extend_constants_structural(std::iter::once(info))
        .is_empty());
}
fn replace_constructor_type(env: &mut clean_kernel::Environment, family: &str, type_: Expr) {
    let name = env.get_inductive(&n(family)).unwrap().constructor_names[0].clone();
    let mut ctor = env.get_constructor(&name).unwrap().clone();
    ctor.type_ = type_;
    let mut info = env.get_const(&name).unwrap().clone();
    info.type_ = ctor.type_.clone();
    env.add_constant_unchecked_for_test(info);
    env.forge_family_records_for_test(vec![], vec![ctor], vec![]);
}
fn refused(program: &ExternalLeanProgram, label: &str, target: &str, stages: &[ScalarLayoutStage]) {
    let error = match program.inspect_scalar_layout(&n("query"), ReplayContextLimits::default()) {
        Ok(_) => panic!("untrusted {label} admitted"),
        Err(e) => e,
    };
    assert!(stages.contains(&error.stage()), "{label}: {error}");
    assert!(error.cause().contains(target), "{label}: {error}");
    println!(
        "scalar_layout_mutation {label} {}",
        serde_json::json!({"stage":format!("{:?}",error.stage()),"cause":error.cause(),"capture_complete":error.source_capture().map(|c|c.is_complete()),"replay":error.replay_verdict()})
    );
}

#[test]
fn scalar_layout_actual430_affinity_mutation_and_bounded_full_check_controls() {
    use ScalarLayoutStage as S;
    let program = actual(LeanWorld::ORACLE, false);
    let facts = facts(&program);
    let source = &program.program.custody.source;
    let base = &program.program.custody.base;
    let roots = facts.replay.roots();
    assert!(matches!(
        facts
            .replay
            .require_context(&Arc::new((**base).clone()), source, roots),
        Err(ReplayedSourceError::ForeignBase)
    ));
    assert!(matches!(
        facts
            .replay
            .require_context(base, &Arc::new((**source).clone()), roots),
        Err(ReplayedSourceError::ForeignSource)
    ));
    assert!(matches!(
        facts
            .replay
            .require_context(base, source, &BTreeSet::from([n("wrong")])),
        Err(ReplayedSourceError::DifferentRoots)
    ));
    let mut changed = (**source).clone();
    assert!(
        clean_olean::declare_environment_world(&mut changed, LeanWorld::Lean435.tag()).is_err()
    );
    changed.register_extern(n("Nat.pow"), "stale_runtime".into());
    assert!(matches!(
        facts.replay.require_record(&changed, &n("Nat.pow")),
        Err(ReplayedSourceError::SourceChanged(_))
    ));
    let budget = RefCell::new(budget::Budget::new());
    let recursors: Vec<_> = program
        .program
        .env
        .recursors()
        .filter(|r| {
            [
                n("Nat"),
                n("Nat.le"),
                n("Fin"),
                n("BitVec"),
                n("UInt32"),
                n("UInt64"),
            ]
            .contains(&r.inductive_name)
        })
        .collect();
    let check = Check {
        program: &program.program,
        context: &facts.context,
        replay: &facts.replay,
        limits: ReplayContextLimits::default(),
        recursors: &recursors,
        budget: &budget,
    };
    // These are well-shaped but ill-typed candidates which release-mode infer
    // alone accepts. Existing full/sort checking must reject both here.
    let bad_app = Expr::app(lam(c("Nat"), c("Nat")), Expr::prop());
    let bad_lam = lam(Expr::nat_lit(0), c("Nat"));
    assert!(check
        .expected_type(&n("query"), &bad_app)
        .unwrap_err()
        .contains("kernel check failed"));
    assert!(check
        .expected_type(&n("query"), &bad_lam)
        .unwrap_err()
        .contains("kernel check failed"));
    let power = Expr::apps(c("Nat.pow"), [Expr::nat_lit(2), Expr::nat_lit(64)]);
    for (nodes, beats, cache) in [(0, 1, 1), (1, 0, 1), (1, 1, 0)] {
        assert!(ReplayContextLimits::new(nodes, beats, cache).is_err());
    }
    assert!(facts
        .context
        .definitionally_equal(
            &power,
            &Expr::nat_lit_u128(1u128 << 64),
            ReplayContextLimits::new(100_000, 1_000_000, 1).unwrap()
        )
        .unwrap());
    assert!(facts
        .context
        .whnf_closed(
            &power,
            ReplayContextLimits::new(100_000, 1, 100_000).unwrap()
        )
        .is_err());
    assert!(facts
        .context
        .definitionally_equal(
            &power,
            &Expr::nat_lit_u128(1u128 << 64),
            ReplayContextLimits::default()
        )
        .unwrap());
    assert!(facts
        .context
        .definitionally_equal(
            &power,
            &power,
            ReplayContextLimits::new(1, 1_000_000, 1).unwrap()
        )
        .is_err());
    assert!(program
        .inspect_scalar_layout(&n("Nat"), ReplayContextLimits::default())
        .is_err());
    assert!(
        program
            .inspect_scalar_layout(&n("wrong"), ReplayContextLimits::default())
            .err()
            .unwrap()
            .stage()
            == S::RootSignature
    );
    assert!(
        program
            .inspect_scalar_layout(
                &n("query"),
                ReplayContextLimits::new(1, 1_000_000, 1).unwrap()
            )
            .err()
            .unwrap()
            .stage()
            == S::RootSignature
    );
    drop(facts);
    let original = &program.program;
    let predicate = variant(original, |env| {
        replace_value(env, "Nat.lt", lam(c("Nat"), lam(c("Nat"), c("True"))))
    });
    refused(
        &predicate,
        "wrong_order_predicate",
        "Nat.lt",
        &[S::SourceReplay, S::NaturalOrder],
    );
    let projection = variant(original, |env| {
        replace_value(
            env,
            "Fin.val",
            lam(
                c("Nat"),
                lam(Expr::app(c("Fin"), Expr::bvar(0)), Expr::nat_lit(0)),
            ),
        )
    });
    refused(
        &projection,
        "wrong_data_projection",
        "Fin",
        &[S::SourceReplay, S::Projections],
    );
    let fields = variant(original, |env| {
        let mut ctor = env.get_constructor(&n("Fin.mk")).unwrap().clone();
        ctor.num_fields = 1;
        env.forge_family_records_for_test(vec![], vec![ctor], vec![]);
    });
    refused(
        &fields,
        "wrong_constructor_field_count",
        "Fin",
        &[S::SourceReplay, S::ScalarFamilies],
    );
    let recursive = variant(original, |env| {
        let mut ind = env.get_inductive(&n("BitVec")).unwrap().clone();
        ind.is_recursive = true;
        env.forge_family_records_for_test(vec![ind], vec![], vec![]);
    });
    refused(
        &recursive,
        "wrong_family_recursion",
        "BitVec",
        &[S::SourceReplay, S::ScalarFamilies],
    );
    let recursor = variant(original, |env| {
        let mut rec = env
            .recursors()
            .find(|r| r.inductive_name == n("Fin"))
            .unwrap()
            .clone();
        rec.rules[0].recursive_fields[0] = true;
        env.forge_family_records_for_test(vec![], vec![], vec![rec]);
    });
    refused(
        &recursor,
        "wrong_recursor_role",
        "Fin",
        &[S::SourceReplay, S::ScalarFamilies],
    );
    let width = variant(original, |env| {
        replace_constructor_type(
            env,
            "UInt32",
            pi(Expr::app(c("BitVec"), Expr::nat_lit(33)), c("UInt32")),
        )
    });
    refused(
        &width,
        "wrong_word_width",
        "UInt32",
        &[S::SourceReplay, S::ScalarFamilies],
    );
    let bound = variant(original, |env| {
        replace_constructor_type(
            env,
            "BitVec",
            pi(
                c("Nat"),
                pi(
                    Expr::app(
                        c("Fin"),
                        Expr::apps(
                            c("Nat.add"),
                            [
                                Expr::apps(c("Nat.pow"), [Expr::nat_lit(2), Expr::bvar(0)]),
                                Expr::nat_lit(1),
                            ],
                        ),
                    ),
                    Expr::app(c("BitVec"), Expr::bvar(1)),
                ),
            ),
        )
    });
    refused(
        &bound,
        "wrong_bitvec_bound",
        "BitVec",
        &[S::SourceReplay, S::ScalarFamilies, S::Bounds],
    );
    for (label, domain) in [
        (
            "wrong_fin_predicate",
            Expr::apps(c("Nat.le"), [Expr::bvar(0), Expr::bvar(1)]),
        ),
        ("proof_field_became_data", c("Nat")),
    ] {
        let changed = variant(original, |env| {
            replace_constructor_type(
                env,
                "Fin",
                pi(
                    c("Nat"),
                    pi(c("Nat"), pi(domain, Expr::app(c("Fin"), Expr::bvar(2)))),
                ),
            )
        });
        refused(
            &changed,
            label,
            "Fin",
            &[S::SourceReplay, S::ScalarFamilies],
        );
    }
    let reordered = variant(original, |env| {
        env.register_structure_fields(n("Fin"), vec![n("isLt"), n("val")])
            .unwrap();
    });
    refused(
        &reordered,
        "wrong_field_order",
        "Fin",
        &[S::SourceReplay, S::Projections],
    );
    println!("scalar_layout_controls actual430: foreign source/base/roots/world, stale extern, escaped capture, full App/Lam, heartbeat/structural/cache bounds, healthy fresh operation, imported/wrong roots, order/projection/field/family/recursor/width/bound/predicate/data/order mutations PASS; fixture variants grant no frontend custody or native calls");
}
