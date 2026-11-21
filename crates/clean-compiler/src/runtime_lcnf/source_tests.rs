//! Actual parser/elaborator/kernel to diagnostic runtime lowering controls.

use super::*;
use clean_kernel::{Environment, Expr, Name};
use clean_olean::RuntimeBody;

const SOURCE: &str = "inductive Data where\n  | make : Data\ndef identity (x : Data) : Data := x\ndef twice (x : Data) : Data := identity (identity x)\n";

fn elaborate(source: &str) -> (Environment, Environment) {
    elaborate_from(Environment::new(), source)
}

fn elaborate_from(before: Environment, source: &str) -> (Environment, Environment) {
    let mut after = before.clone();
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let declarations =
        clean_parser::parse_file_with_tactics(source, &patterns).expect("source parse");
    let mut file = clean_elab::FileContext::new();
    for declaration in declarations {
        let processed = clean_elab::preprocess_decl_with_context(&declaration, &mut file);
        let registered = clean_elab::elaborate_decl_and_register_with_context_and_warning(
            &mut after, &processed, &mut file,
        )
        .expect("actual source elaboration/kernel registration");
        assert!(registered.warning.is_none(), "unexpected source warning");
        let mut leaves = Vec::new();
        registered.result.leaf_decls(&mut leaves);
        for leaf in leaves {
            assert!(
                !matches!(leaf, clean_elab::ElabResult::Failed { .. }),
                "nested declaration failure: {leaf:?}"
            );
        }
    }
    (before, after)
}

fn source_records(source: &str) -> Vec<RuntimeSourceRecord> {
    vec![RuntimeSourceRecord {
        module: "Fresh".into(),
        path: "Fresh.lean".into(),
        source: source.into(),
    }]
}

fn capture(source: &str) -> RuntimeContext {
    let (before, after) = elaborate(source);
    RuntimeContext::capture_with_environment(
        Vec::new(),
        &before,
        &after,
        vec![RuntimeSourceRecord {
            module: "Fresh".into(),
            path: "Fresh.lean".into(),
            source: source.into(),
        }],
    )
}

#[test]
fn fresh_source_body_reaches_actual_lcnf_ir_rc_and_trust_ir() {
    let context = capture(SOURCE);
    let observation = context.environment_capture().expect("environment capture");
    assert!(observation.errors.is_empty(), "{:?}", observation.errors);
    assert!(observation.added.contains(&Name::from_string("twice")));
    let root = Name::from_string("twice");
    let output = context
        .lower_definition(&root, RuntimeLimits::default())
        .expect("fresh LCNF");
    assert!(matches!(
        output.origin.provenance,
        RuntimeProvenance::Environment {
            added_since_baseline: true,
            ..
        }
    ));
    let ir = context
        .lower_ir(&root, RuntimeLimits::default())
        .expect("fresh IR");
    assert!(ir
        .rows
        .iter()
        .any(|r| r.origin.name == root && matches!(r.status, RuntimeIrStatus::Lowered(_))));
    #[cfg(feature = "trust-ir-backend")]
    {
        let emitted = context
            .lower_trust_ir_diagnostic(
                &root,
                RuntimeLimits::default(),
                crate::emit_trust_ir::RuntimeLowering::ExternCalls,
            )
            .expect("fresh captured report")
            .emission
            .expect("fresh emitted module");
        assert_eq!(
            emitted
                .named_edges
                .iter()
                .filter(|e| e.callee == Name::from_string("identity"))
                .count(),
            2
        );
        assert!(trust_ir_build::validate_module(&emitted.module).is_empty());
    }
}

#[test]
fn every_eager_environment_role_and_generated_identity_stays_in_capture() {
    let (before, after) = elaborate(SOURCE);
    let expected = after
        .constants()
        .map(|r| r.name.clone())
        .chain(after.inductives().map(|r| r.name.clone()))
        .chain(after.constructors().map(|r| r.name.clone()))
        .chain(after.recursors().map(|r| r.name.clone()))
        .chain(after.quotients().map(|r| r.name.clone()))
        .collect::<std::collections::BTreeSet<_>>();
    let context = RuntimeContext::capture_with_environment(
        vec![],
        &before,
        &after,
        vec![RuntimeSourceRecord {
            module: "Fresh".into(),
            path: "Fresh.lean".into(),
            source: SOURCE.into(),
        }],
    );
    let captured = context.environment_capture().unwrap();
    assert_eq!(
        captured
            .after
            .iter()
            .map(|r| r.name.clone())
            .collect::<std::collections::BTreeSet<_>>(),
        expected
    );
    assert_eq!(
        captured
            .after
            .iter()
            .filter(|r| r.constant.is_some())
            .count(),
        after.constants().count()
    );
    assert_eq!(
        captured
            .after
            .iter()
            .filter(|r| r.recursor.is_some())
            .count(),
        after.recursors().count()
    );
    assert!(captured.after.iter().any(|r| r.recursor.is_some()));
    let limits = RuntimeSourceCaptureLimits::default();
    let mut remaining = limits.total_bytes;
    let mut errors = Vec::new();
    let mut failures = Vec::new();
    let (_, bindings) = source::snapshot_names(
        &after,
        expected,
        limits,
        "after",
        &mut remaining,
        &mut errors,
        &mut failures,
    );
    assert!(errors.is_empty() && failures.is_empty());
    for row in &captured.after {
        let (digest, bytes) = source::bounded_hash(row, limits.row_bytes).unwrap();
        // The borrowed pre-clone binding must match the fully retained row,
        // including specialized registry mirrors and the three status flags.
        assert_eq!(bindings[&row.name].digest, digest);
        assert_eq!(bindings[&row.name].encoded_bytes, bytes);
    }
}

#[test]
fn source_bytes_body_and_baseline_identity_each_change_the_observation() {
    let a = capture(SOURCE);
    let b = capture(&format!("{SOURCE}\n-- independent source binding\n"));
    let c = capture(&SOURCE.replace("identity (identity x)", "x"));
    let hash = |c: &RuntimeContext| c.environment_capture().unwrap().snapshot_blake3;
    assert_ne!(hash(&a), hash(&b));
    assert_ne!(hash(&a), hash(&c));
    let (before, after) = elaborate(SOURCE);
    let no_delta = RuntimeContext::capture_with_environment(
        vec![],
        &after,
        &after,
        vec![RuntimeSourceRecord {
            module: "Fresh".into(),
            path: "Fresh.lean".into(),
            source: SOURCE.into(),
        }],
    );
    assert!(no_delta.environment_capture().unwrap().added.is_empty());
    assert_ne!(hash(&a), hash(&no_delta));
    assert_eq!(
        a.environment_capture()
            .unwrap()
            .before
            .iter()
            .filter(|r| r.constant.is_some())
            .count(),
        before.constants().count()
    );
}

#[test]
fn changed_baseline_and_missing_source_binding_refuse_without_mutating_environment() {
    let (before, after) = elaborate(SOURCE);
    let captured = RuntimeContext::capture_with_environment(
        vec![],
        &after,
        &before,
        vec![RuntimeSourceRecord {
            module: "Fresh".into(),
            path: "Fresh.lean".into(),
            source: SOURCE.into(),
        }],
    );
    assert!(!captured.environment_capture().unwrap().removed.is_empty());
    assert!(captured
        .lower_ir(&Name::from_string("twice"), RuntimeLimits::default())
        .is_err());
    let empty = RuntimeContext::capture_with_environment(vec![], &before, &after, vec![]);
    assert!(empty
        .lower_ir(&Name::from_string("twice"), RuntimeLimits::default())
        .is_err());
    assert!(after
        .get_const(&Name::from_string("twice"))
        .unwrap()
        .value
        .is_some());
}

#[test]
fn altered_header_and_missing_body_are_not_default_object_or_external_calls() {
    let mut context = capture(SOURCE);
    let root = Name::from_string("twice");
    context.catalog.get_mut(&root).unwrap()[0].0.body = RuntimeBody::MissingRequiredValue;
    assert!(context
        .lower_definition(&root, RuntimeLimits::default())
        .is_err());
    let mut context = capture(SOURCE);
    context.catalog.get_mut(&root).unwrap()[0].0.type_ = Ok(Expr::type_());
    assert!(context
        .lower_definition(&root, RuntimeLimits::default())
        .is_err());
}

#[test]
fn local_import_identity_conflict_is_not_resolved_by_source_priority() {
    let context = capture(SOURCE);
    let root = Name::from_string("identity");
    let mut duplicate = context.clone();
    let row = duplicate.catalog[&root][0].clone();
    duplicate.catalog.get_mut(&root).unwrap().push(row);
    assert!(matches!(
        duplicate.declaration(&root),
        Err(RuntimeLowerError::Ambiguous(_))
    ));
    assert!(duplicate.environment_capture().is_some());
}

#[test]
fn implemented_by_is_bound_as_typed_dependency_and_never_silently_substituted() {
    let (before, after) = elaborate(SOURCE);
    let original =
        RuntimeContext::capture_with_environment(vec![], &before, &after, source_records(SOURCE));
    let root = Name::from_string("twice");
    let target = Name::anon().str("identity.quoted");
    let mut altered = after.clone();
    altered.register_implemented_by(root.clone(), target.clone());
    let context =
        RuntimeContext::capture_with_environment(vec![], &before, &altered, source_records(SOURCE));
    let capture = context.environment_capture().unwrap();
    assert!(capture.errors.is_empty());
    assert_ne!(
        capture.snapshot_blake3,
        original.environment_capture().unwrap().snapshot_blake3
    );
    assert_eq!(
        capture
            .after
            .iter()
            .find(|r| r.name == root)
            .unwrap()
            .implemented_by,
        Some(target.clone())
    );
    let row = context.declaration(&root).unwrap();
    assert!(row.dependencies.contains(&target));
    assert!(!row.represented_fields_complete);
    assert!(row.issues.iter().any(|s| s.contains("implemented_by")));
    assert!(context
        .lower_definition(&root, RuntimeLimits::default())
        .is_err());
    assert!(after.get_implemented_by(&root).is_none());
}

#[test]
fn baseline_implementation_edge_change_is_not_a_successfully_bound_delta() {
    let (_, before) = elaborate(SOURCE);
    let mut after = before.clone();
    after.register_implemented_by(Name::from_string("twice"), Name::from_string("identity"));
    let context =
        RuntimeContext::capture_with_environment(vec![], &before, &after, source_records(SOURCE));
    let capture = context.environment_capture().unwrap();
    assert!(capture.changed.contains(&Name::from_string("twice")));
    assert!(capture.snapshot_blake3.is_none());
    assert!(!capture.errors.is_empty());
}

#[test]
fn structure_defaults_parents_and_quotient_roles_are_retained_not_claimed_whole_environment() {
    let source = "inductive Data where\n  | make : Data\nstructure Box where\n  item : Data\n";
    let (before, after) = elaborate(source);
    let root = Name::from_string("Box");
    let fields = after.get_structure_field_names(&root).unwrap();
    assert_eq!(fields.len(), 1);
    let mut changed = after.clone();
    changed.register_structure_field_default(
        root.clone(),
        fields[0].clone(),
        Expr::const_(Name::from_string("Data.make"), vec![]),
    );
    changed.register_structure_parents(
        root.clone(),
        vec![(
            Name::anon().str("to.Parent"),
            Name::anon().str("Parent.quoted"),
        )],
    );
    let a =
        RuntimeContext::capture_with_environment(vec![], &before, &after, source_records(source));
    let b =
        RuntimeContext::capture_with_environment(vec![], &before, &changed, source_records(source));
    assert_ne!(
        a.environment_capture().unwrap().snapshot_blake3,
        b.environment_capture().unwrap().snapshot_blake3
    );
    let observation = b.environment_capture().unwrap();
    let row = observation.after.iter().find(|r| r.name == root).unwrap();
    assert_eq!(row.structure_fields.as_deref(), Some(fields));
    assert!(row.structure_defaults[0].1.is_some());
    assert_eq!(
        row.structure_parents.as_ref().unwrap()[0].0,
        Name::anon().str("to.Parent")
    );
    assert!(observation.limitations.iter().any(|s| s.contains("orphan")));
    let prelude = Environment::with_prelude();
    let c = RuntimeContext::capture_with_environment(
        vec![],
        &prelude,
        &prelude,
        source_records("-- no new rows"),
    );
    let observed = c.environment_capture().unwrap();
    assert!(prelude.quotients().count() > 0);
    assert_eq!(
        observed
            .after
            .iter()
            .filter(|r| r.quotient.is_some())
            .count(),
        prelude.quotients().count()
    );
    assert_eq!(
        observed.after_population.quotients,
        prelude.quotients().count()
    );
}

#[test]
fn capture_population_and_byte_limits_never_publish_partial_digest_or_catalog() {
    let (before, after) = elaborate(SOURCE);
    let default = RuntimeSourceCaptureLimits::default();
    for limits in [
        RuntimeSourceCaptureLimits {
            declarations: 0,
            ..default
        },
        RuntimeSourceCaptureLimits {
            row_bytes: 1,
            ..default
        },
        RuntimeSourceCaptureLimits {
            total_bytes: 1,
            ..default
        },
        RuntimeSourceCaptureLimits {
            source_bytes: 1,
            ..default
        },
    ] {
        let context = RuntimeContext::capture_with_environment_limits(
            vec![],
            &before,
            &after,
            source_records(SOURCE),
            limits,
        );
        let capture = context.environment_capture().unwrap();
        assert!(capture.snapshot_blake3.is_none());
        assert!(!capture.delta_complete);
        assert!(
            capture.added.is_empty() && capture.changed.is_empty() && capture.removed.is_empty()
        );
        assert!(!capture.errors.is_empty());
        if limits.source_bytes != 1 {
            assert!(!capture.row_failures.is_empty());
            assert!(capture
                .row_failures
                .iter()
                .all(|failure| !failure.reason.is_empty()));
        }
        assert_eq!(
            capture.after_population.constants,
            after.constants().count()
        );
        assert_eq!(capture.sources[0].source, SOURCE);
        assert!(context.catalog.is_empty());
        assert!(context
            .lower_ir(&Name::from_string("twice"), RuntimeLimits::default())
            .is_err());
    }
}

#[test]
fn actual_local_and_mutual_partial_bodies_remain_missing_runtime_rows() {
    let source = "partial def loop (n : Nat) : Nat := loop n\nmutual\npartial def evenP (n : Nat) : Nat := oddP n\npartial def oddP (n : Nat) : Nat := evenP n\nend\n";
    let (before, after) = elaborate_from(Environment::with_prelude(), source);
    let context =
        RuntimeContext::capture_with_environment(vec![], &before, &after, source_records(source));
    assert!(
        context.environment_capture().unwrap().errors.is_empty(),
        "{:?}",
        context.capture_errors()
    );
    for label in ["loop", "evenP", "oddP"] {
        let name = Name::from_string(label);
        let actual = after.get_const(&name).unwrap();
        // register.rs maps the elaborator's Opaque { val: None } to a checked
        // Axiom header and then applies partial modifiers. Do not relabel it.
        assert_eq!(actual.kind, clean_kernel::ConstantKind::Axiom);
        assert!(after.is_partial(&name));
        assert!(actual.value.is_none());
        let row = context.declaration(&name).unwrap();
        assert!(matches!(row.body, RuntimeBody::MissingRequiredValue));
        assert!(context.environment_capture().unwrap().added.contains(&name));
        assert!(context
            .lower_definition(&name, RuntimeLimits::default())
            .is_err());
        #[cfg(feature = "trust-ir-backend")]
        assert!(context
            .lower_trust_ir_diagnostic(
                &name,
                RuntimeLimits::default(),
                crate::emit_trust_ir::RuntimeLowering::ExternCalls
            )
            .is_err());
    }
}

#[test]
fn specialized_eager_row_never_pulls_a_lazy_constant_mirror_into_capture() {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    #[derive(Debug)]
    struct Lazy {
        row: clean_kernel::ConstantInfo,
        reads: Arc<AtomicUsize>,
    }
    impl clean_kernel::env::ConstantSource for Lazy {
        fn get(&self, name: &Name) -> Option<&clean_kernel::ConstantInfo> {
            self.reads.fetch_add(1, Ordering::Relaxed);
            (name == &self.row.name).then_some(&self.row)
        }
        fn contains(&self, name: &Name) -> bool {
            name == &self.row.name
        }
        fn names(&self) -> Vec<Name> {
            vec![self.row.name.clone()]
        }
    }
    let (_, mut env) = elaborate(SOURCE);
    let name = Name::from_string("Data");
    let lazy_row = env.get_const(&name).unwrap().clone();
    assert!(env.forget_decl(&name));
    assert!(env.get_inductive(&name).is_some());
    let reads = Arc::new(AtomicUsize::new(0));
    env.set_constant_source(Arc::new(Lazy {
        row: lazy_row,
        reads: reads.clone(),
    }));
    let context = RuntimeContext::capture_with_environment(
        vec![],
        &env,
        &env,
        source_records("-- no eager changes"),
    );
    assert_eq!(reads.load(Ordering::Relaxed), 0);
    let capture = context.environment_capture().unwrap();
    assert!(capture.errors.is_empty());
    assert!(capture.delta_complete);
    let row = capture.after.iter().find(|r| r.name == name).unwrap();
    assert!(row.constant.is_none());
    assert!(row.inductive.is_some());
    assert_eq!(
        capture
            .after
            .iter()
            .filter(|r| r.constant.is_some())
            .count(),
        env.constants().count()
    );
    assert!(capture.limitations.iter().any(|s| s.contains("lazy")));
}

#[test]
fn absent_definition_theorem_and_opaque_values_are_not_axiom_stubs() {
    let context = capture(SOURCE);
    let capture = context.environment_capture().unwrap();
    let all = capture.after.iter().map(|r| (r.name.clone(), r)).collect();
    let original = capture
        .after
        .iter()
        .find(|r| r.name == Name::from_string("twice"))
        .unwrap();
    for kind in [
        clean_kernel::ConstantKind::Definition,
        clean_kernel::ConstantKind::Theorem,
        clean_kernel::ConstantKind::Opaque,
    ] {
        let mut changed = original.clone();
        let value = changed.constant.as_mut().unwrap();
        value.kind = kind;
        value.value = None;
        let row = changed.catalog(&all);
        assert!(matches!(row.body, RuntimeBody::MissingRequiredValue));
        assert!(!row.represented_fields_complete);
        assert!(row
            .issues
            .iter()
            .any(|issue| issue.contains("body is missing")));
    }
    let mut axiom = original.clone();
    axiom.constant.as_mut().unwrap().kind = clean_kernel::ConstantKind::Axiom;
    axiom.constant.as_mut().unwrap().value = None;
    assert!(matches!(
        axiom.catalog(&all).body,
        RuntimeBody::NoStoredValueForKind
    ));
}

#[test]
fn source_row_refusal_identifies_the_tighter_budget_without_consuming_it() {
    let (_, after) = elaborate(SOURCE);
    let name = Name::from_string("twice");
    let defaults = RuntimeSourceCaptureLimits::default();
    for (row_bytes, total_bytes) in [(1, 1024), (1024, 1), (1, 1)] {
        let limits = RuntimeSourceCaptureLimits {
            row_bytes,
            total_bytes,
            ..defaults
        };
        let mut remaining = total_bytes;
        let mut errors = Vec::new();
        let mut failures = Vec::new();
        let (rows, bindings) = source::snapshot_names(
            &after,
            [name.clone()].into_iter().collect(),
            limits,
            "after",
            &mut remaining,
            &mut errors,
            &mut failures,
        );
        assert!(rows.is_empty() && bindings.is_empty());
        assert_eq!(remaining, total_bytes);
        assert_eq!(failures.len(), 1);
        let failure = &failures[0];
        assert_eq!(failure.name, name);
        assert!(failure
            .reason
            .contains("limit=1, encoded_prefix=0, next_write=4"));
        assert!(failure.reason.contains(&format!(
            "row_limit={row_bytes}, remaining_total={total_bytes}"
        )));
    }
}

#[test]
fn bounded_hash_stops_at_the_first_over_budget_write() {
    struct Unvisited;
    impl serde::Serialize for Unvisited {
        fn serialize<S: serde::Serializer>(&self, _: S) -> Result<S::Ok, S::Error> {
            panic!("tail reached after the first budget refusal")
        }
    }
    let error = source::bounded_hash(&("a".repeat(4096), Unvisited), 8).unwrap_err();
    assert_eq!(
        error,
        "io error: source observation byte limit exceeded: limit=8, encoded_prefix=8, next_write=4096"
    );
}
