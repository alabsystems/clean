// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests of the artifact ledger's rules (`artifact_ledger.rs`).

use super::*;
use clean_kernel::env::{ConstantInfo, TrustedEnvExt};
use clean_kernel::expr::{Expr, LevelVec};

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), LevelVec::new())
}

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), LevelVec::new())
}

/// Register `name : Nat := value` as artifact `module`'s declaration.
fn declare(env: &mut Environment, module: &str, name: &str, value: Expr) -> Name {
    let n = Name::from_string(name);
    env.extend_constants_unchecked(std::iter::once(ConstantInfo::new(
        n.clone(),
        vec![],
        nat(),
        Some(value),
        false,
    )));
    env.set_constant_origins(
        [n.clone()],
        ConstantOrigin::olean_import(Some(module.to_string())),
    );
    n
}

fn succ(e: Expr) -> Expr {
    Expr::app(c("Nat.succ"), e)
}

fn key(m: &str) -> ArtifactKey {
    Some(m.to_string())
}

#[test]
fn a_self_referential_definition_is_refused() {
    let mut env = Environment::with_prelude();
    bind_part(&mut env, &key("V0"), &key("V0")).expect("bind");
    let v = declare(&mut env, "V0", "V0.v", succ(c("V0.v")));
    let err = check_part_references(&mut env, &key("V0"), &[v], &[], true)
        .expect_err("V0.v := Nat.succ V0.v depends on itself");
    assert!(
        matches!(err, ImportError::DefinitionalCycle { .. }),
        "{err}"
    );
}

#[test]
fn a_mutual_cycle_is_refused_and_an_acyclic_part_is_not() {
    let mut env = Environment::with_prelude();
    let a = declare(&mut env, "V0", "V0.a", succ(c("V0.b")));
    let b = declare(&mut env, "V0", "V0.b", succ(c("V0.a")));
    let err = check_part_references(&mut env, &key("V0"), &[a, b], &[], true)
        .expect_err("V0.a and V0.b depend on each other");
    assert!(
        matches!(err, ImportError::DefinitionalCycle { .. }),
        "{err}"
    );

    let mut env = Environment::with_prelude();
    let a = declare(&mut env, "V1", "V1.a", succ(c("V1.b")));
    let b = declare(&mut env, "V1", "V1.b", c("Nat.zero"));
    check_part_references(&mut env, &key("V1"), &[a, b], &[], true).expect("a chain, no cycle");
}

#[test]
fn a_cycle_of_unsafe_declarations_is_lean_s_and_admitted() {
    let mut env = Environment::with_prelude();
    let v = declare(&mut env, "U", "U.loop", succ(c("U.loop")));
    env.mark_unsafe(v.clone());
    check_part_references(&mut env, &key("U"), &[v], &[], true).expect("unsafe recursion");
}

#[test]
fn a_cycle_across_parts_of_one_artifact_is_refused() {
    let mut env = Environment::with_prelude();
    // The base part refers to a name only the private part declares.
    let a = declare(&mut env, "V0", "V0.a", succ(c("V0.p")));
    check_part_references(&mut env, &key("V0"), &[a], &[], true).expect("base part");
    bind_part(&mut env, &key("V0._private"), &key("V0")).expect("companion");
    let p = declare(&mut env, "V0._private", "V0.p", succ(c("V0.a")));
    let err = check_part_references(&mut env, &key("V0"), &[p], &[], true)
        .expect_err("V0.a -> V0.p -> V0.a spans the parts");
    assert!(
        matches!(err, ImportError::DefinitionalCycle { .. }),
        "{err}"
    );
}

#[test]
fn a_name_supplied_by_another_artifact_after_it_was_referred_to_is_refused() {
    let mut env = Environment::with_prelude();
    let a = declare(&mut env, "A", "A.f", succ(c("B.g")));
    check_part_references(&mut env, &key("A"), &[a], &[], true).expect("A loads");
    let g = declare(&mut env, "B", "B.g", succ(c("A.f")));
    let err = check_part_references(&mut env, &key("B"), &[g], &[], true)
        .expect_err("B.g was referred to by A before any of A's imports declared it");
    assert!(matches!(err, ImportError::ForwardReference { .. }), "{err}");
}

/// A load that leaves rules 1 and 3 to the caller's replay of ONE module
/// (`OleanImportPolicy::with_module_replay_refusals`) registers that module's
/// self-dependent declaration for the replay to refuse, and still refuses a
/// name an EARLIER artifact referred to before any of its imports declared it:
/// that is the earlier artifact's inconsistency, which no replay of this
/// module sees, and it is how a cycle across two artifacts is caught.
#[test]
fn a_forward_reference_is_refused_when_only_cycles_are_left_to_the_replay() {
    let mut env = Environment::with_prelude();
    bind_part(&mut env, &key("V0"), &key("V0")).expect("bind");
    let v = declare(&mut env, "V0", "V0.v", succ(c("V0.v")));
    check_part_references(&mut env, &key("V0"), &[v], &[], false)
        .expect("the self-reference is left to the replay");

    let mut env = Environment::with_prelude();
    let a = declare(&mut env, "A", "A.f", succ(c("B.g")));
    check_part_references(&mut env, &key("A"), &[a], &[], true).expect("A loads");
    let g = declare(&mut env, "B", "B.g", succ(c("A.f")));
    let err = check_part_references(&mut env, &key("B"), &[g], &[], false)
        .expect_err("A referred to B.g before any of A's imports declared it");
    assert!(matches!(err, ImportError::ForwardReference { .. }), "{err}");
}

#[test]
fn one_label_for_two_artifacts_is_refused() {
    let mut env = Environment::with_prelude();
    bind_part(&mut env, &key("D._private"), &key("D._private")).expect("a module so named");
    let err = bind_part(&mut env, &key("D._private"), &key("D"))
        .expect_err("D's companion would share the label");
    assert!(
        matches!(err, ImportError::AmbiguousModuleLabel { .. }),
        "{err}"
    );
    bind_part(&mut env, &key("D._private"), &key("D._private")).expect("same artifact again");
}

#[test]
fn a_companion_part_is_its_module_s_artifact() {
    let mut env = Environment::with_prelude();
    bind_part(&mut env, &key("D"), &key("D")).expect("base");
    bind_part(&mut env, &key("D._private"), &key("D")).expect("companion");
    let p = declare(&mut env, "D._private", "D.p", c("Nat.zero"));
    assert_eq!(declaring_artifact(&env, &p), Some(key("D")));
    assert_eq!(declared_by_other_artifact(&env, &p, &key("D")), None);
    assert_eq!(
        declared_by_other_artifact(&env, &p, &key("Z")),
        Some("D".to_string())
    );
}

#[test]
fn lean_records_naming_one_declaration_twice_are_refused() {
    let env = Environment::with_prelude();
    let n = Name::from_string("D.w");
    let err = check_lean_records(&env, [(0, n.clone()), (1, n)].into_iter(), &key("D"))
        .expect_err("D.w twice in one part");
    assert!(
        matches!(err, ImportError::DuplicateDeclaration { .. }),
        "{err}"
    );
}

fn record(name: &str, value: Expr) -> PartRecord {
    PartRecord::Constant {
        info: ConstantInfo::new(Name::from_string(name), vec![], nat(), Some(value), false),
        safety: None,
    }
}

#[test]
fn a_later_part_stating_a_declaration_differently_is_refused() {
    let mut env = Environment::with_prelude();
    bind_part(&mut env, &key("D"), &key("D")).expect("base");
    let e = declare(&mut env, "D", "D.e", succ(c("Nat.zero")));
    remember_part_records(&mut env, &key("D"), [record("D.e", succ(c("Nat.zero")))]);
    bind_part(&mut env, &key("D._private"), &key("D")).expect("companion");
    assert!(declared_by_this_artifact(&env, &e, &key("D")));
    assert!(!declared_by_this_artifact(&env, &e, &key("Z")));

    // Control: the same record again is the same declaration.
    check_same_artifact_record(
        &mut env,
        &key("D"),
        &e,
        Some(&record("D.e", succ(c("Nat.zero")))),
    )
    .expect("the parts agree");
    // X1: the private part says `D.e := 0`.
    let err =
        check_same_artifact_record(&mut env, &key("D"), &e, Some(&record("D.e", c("Nat.zero"))))
            .expect_err("the parts disagree on D.e");
    assert!(matches!(err, ImportError::PartsDisagree { .. }), "{err}");
    // A record that did not convert cannot be shown to agree.
    let err = check_same_artifact_record(&mut env, &key("D"), &e, None)
        .expect_err("an unconverted record");
    assert!(matches!(err, ImportError::PartsDisagree { .. }), "{err}");
}

#[test]
fn parts_disagreeing_only_in_safety_or_hints_are_refused() {
    let mut env = Environment::with_prelude();
    let e = declare(&mut env, "D", "D.e", c("Nat.zero"));
    remember_part_records(&mut env, &key("D"), [record("D.e", c("Nat.zero"))]);
    let PartRecord::Constant { info, .. } = record("D.e", c("Nat.zero")) else {
        unreachable!()
    };
    let unsafe_record = PartRecord::Constant {
        info: info.clone(),
        safety: Some(crate::DefinitionSafety::Unsafe),
    };
    let err = check_same_artifact_record(&mut env, &key("D"), &e, Some(&unsafe_record))
        .expect_err("safe in one part, unsafe in the other");
    assert!(matches!(err, ImportError::PartsDisagree { .. }), "{err}");
    let mut opaque = info;
    opaque.reducibility = clean_kernel::env::Reducibility::Opaque;
    let err = check_same_artifact_record(
        &mut env,
        &key("D"),
        &e,
        Some(&PartRecord::Constant {
            info: opaque,
            safety: None,
        }),
    )
    .expect_err("regular in one part, opaque in the other");
    assert!(matches!(err, ImportError::PartsDisagree { .. }), "{err}");
}

#[test]
fn an_artifact_met_before_another_is_compared_with_the_environment() {
    let mut env = Environment::with_prelude();
    let e = declare(&mut env, "D", "D.e", succ(c("Nat.zero")));
    remember_part_records(&mut env, &key("D"), [record("D.e", succ(c("Nat.zero")))]);
    // Another artifact's parts load meanwhile: D's records are not kept.
    remember_part_records(&mut env, &key("Z"), [record("Z.z", c("Nat.zero"))]);
    check_same_artifact_record(
        &mut env,
        &key("D"),
        &e,
        Some(&record("D.e", succ(c("Nat.zero")))),
    )
    .expect("the environment's copy agrees");
    let err =
        check_same_artifact_record(&mut env, &key("D"), &e, Some(&record("D.e", c("Nat.zero"))))
            .expect_err("the environment's copy says D.e := 1");
    assert!(matches!(err, ImportError::PartsDisagree { .. }), "{err}");
}

fn stub(ty: Expr) -> PartRecord {
    PartRecord::Constant {
        info: ConstantInfo::new(Name::from_string("D.e"), vec![], ty, None, false),
        safety: None,
    }
}

/// The environment holds `D.e := 1` from a first load of `D`, and
/// another artifact loaded after it.
fn met_before() -> (Environment, Name) {
    let mut env = Environment::with_prelude();
    begin_artifact_load(&mut env, &key("D"), true).expect("first load of D");
    let e = declare(&mut env, "D", "D.e", succ(c("Nat.zero")));
    remember_part_records(&mut env, &key("D"), [record("D.e", succ(c("Nat.zero")))]);
    let _ = finish_artifact_load(&mut env, &key("D")).expect("D complete");
    begin_artifact_load(&mut env, &key("Z"), true).expect("Z");
    remember_part_records(&mut env, &key("Z"), [record("Z.z", c("Nat.zero"))]);
    let _ = finish_artifact_load(&mut env, &key("Z")).expect("Z complete");
    (env, e)
}

/// Round 30 accepted, on a second load of an artifact, a value-free stub
/// of a name the environment holds with a value, while within one load
/// a stub after its definition is refused. One rule now: a stub stands
/// for the value only when a later part of its own load states it.
#[test]
fn a_stub_stands_for_a_value_only_when_a_later_part_of_its_load_states_it() {
    // Met again, its public part's stub and nothing after it: refused
    // when the load ends.
    let (mut env, e) = met_before();
    begin_artifact_load(&mut env, &key("D"), true).expect("second load");
    check_same_artifact_record(&mut env, &key("D"), &e, Some(&stub(nat())))
        .expect("a stub may wait for a later part of its load");
    let err = finish_artifact_load(&mut env, &key("D"))
        .expect_err("no part of this load completes the stub");
    assert!(
        matches!(err, ImportError::PartsDisagree { ref name, .. } if name == "D.e"),
        "{err}"
    );

    assert!(
        finish_artifact_load(&mut env, &key("D"))
            .expect("already refused load")
            .is_none(),
        "an error consumed the active load; a second no-op must not mint evidence"
    );

    // The same stub, then the environment's definition: the honest shape.
    let (mut env, e) = met_before();
    begin_artifact_load(&mut env, &key("D"), true).expect("second load");
    check_same_artifact_record(&mut env, &key("D"), &e, Some(&stub(nat())))
        .expect("the public part's stub");
    check_same_artifact_record(&mut env, &key("D"), &e, Some(&stub(nat())))
        .expect("the server part's stub");
    check_same_artifact_record(
        &mut env,
        &key("D"),
        &e,
        Some(&record("D.e", succ(c("Nat.zero")))),
    )
    .expect("the private part completes it as the environment has it");
    let _ = finish_artifact_load(&mut env, &key("D")).expect("nothing left open");

    // Completed with another value: refused.
    let (mut env, e) = met_before();
    begin_artifact_load(&mut env, &key("D"), true).expect("second load");
    check_same_artifact_record(&mut env, &key("D"), &e, Some(&stub(nat()))).expect("stub");
    let err =
        check_same_artifact_record(&mut env, &key("D"), &e, Some(&record("D.e", c("Nat.zero"))))
            .expect_err("the completion states D.e := 0");
    assert!(matches!(err, ImportError::PartsDisagree { .. }), "{err}");

    // A stub of another type: refused at once.
    let (mut env, e) = met_before();
    begin_artifact_load(&mut env, &key("D"), true).expect("second load");
    let err = check_same_artifact_record(&mut env, &key("D"), &e, Some(&stub(Expr::prop())))
        .expect_err("a stub of another type");
    assert!(matches!(err, ImportError::PartsDisagree { .. }), "{err}");

    // Within one load, a stub after the definition: refused at once, by
    // the same rule (the definition was stated before it).
    let (mut env, e) = met_before();
    begin_artifact_load(&mut env, &key("D"), true).expect("second load");
    check_same_artifact_record(
        &mut env,
        &key("D"),
        &e,
        Some(&record("D.e", succ(c("Nat.zero")))),
    )
    .expect("the definition as registered");
    let err = check_same_artifact_record(&mut env, &key("D"), &e, Some(&stub(nat())))
        .expect_err("a stub after the definition in one load");
    assert!(matches!(err, ImportError::PartsDisagree { .. }), "{err}");

    // A stub left open is refused when the next artifact's load begins,
    // for a loader that never says where an artifact ends.
    let (mut env, e) = met_before();
    begin_artifact_load(&mut env, &key("D"), true).expect("second load");
    check_same_artifact_record(&mut env, &key("D"), &e, Some(&stub(nat()))).expect("stub");
    let err = begin_artifact_load(&mut env, &key("Y"), true)
        .expect_err("D's load ends with its stub open");
    assert!(matches!(err, ImportError::PartsDisagree { .. }), "{err}");
}

/// A part whose bytes were loaded before states its stubs and values
/// in this load too.
#[test]
fn a_part_met_before_still_leaves_its_stubs_to_a_later_part() {
    let (mut env, e) = met_before();
    begin_artifact_load(&mut env, &key("D"), true).expect("second load");
    note_met_before_part(&mut env, &key("D"), true, [e.clone()], [])
        .expect("its public part, bytes met before");
    let err = finish_artifact_load(&mut env, &key("D")).expect_err("nothing completes D.e");
    assert!(matches!(err, ImportError::PartsDisagree { .. }), "{err}");

    let (mut env, e) = met_before();
    begin_artifact_load(&mut env, &key("D"), true).expect("second load");
    note_met_before_part(&mut env, &key("D"), true, [e.clone()], []).expect("public part");
    note_met_before_part(&mut env, &key("D"), true, [], [e]).expect("private part");
    let _ = finish_artifact_load(&mut env, &key("D")).expect("completed");
}

fn instance(name: &str, priority: u64) -> TypedExtensionEntry {
    TypedExtensionEntry::Instance(crate::module::typed_extensions::TypedInstanceEntry {
        instance_name: Name::from_string(name),
        priority,
        synth_order: Vec::new(),
        scope: None,
    })
}

fn table(entries: Vec<TypedExtensionEntry>) -> Vec<TypedExtension> {
    vec![TypedExtension {
        extension_name: Name::from_string("Lean.Meta.instanceExtension"),
        source_rows: Some(entries.len()),
        entries,
        undecoded_entries: 0,
        compiler_names: None,
    }]
}

fn entries_of(
    module_system: bool,
    parts: [Vec<TypedExtensionEntry>; 3],
) -> Result<(), ImportError> {
    let [a, b, c] = parts.map(table);
    check_artifact_entries(
        &key("I"),
        module_system,
        &[Some(a.as_slice()), Some(b.as_slice()), Some(c.as_slice())],
    )
}

/// The verification of `a7c69cb8c`'s instance-table part tampers of a
/// Lean-built `module I` (`I.i0` the honest instance, `I.i1` another
/// definition of the class), and the private-only row an honest private
/// part adds.
#[test]
fn the_parts_of_a_module_state_one_instance_table() {
    let i0 = || instance("I.i0", 1000);
    let refused =
        |r: Result<(), ImportError>| matches!(r, Err(ImportError::PartsDisagreeOnEntry { .. }));
    // Honest, and a private part adding a private instance.
    entries_of(true, [vec![i0()], vec![i0()], vec![i0()]]).expect("ISAME");
    entries_of(
        true,
        [vec![i0()], vec![i0()], vec![i0(), instance("I.p", 1000)]],
    )
    .expect("a private instance is the private level's own");
    // IS: the server part alone names I.i1.
    assert!(refused(entries_of(
        true,
        [vec![i0()], vec![instance("I.i1", 1000)], vec![i0()]]
    )));
    // ISP: the same at priority 2000.
    assert!(refused(entries_of(
        true,
        [vec![i0()], vec![instance("I.i1", 2000)], vec![i0()]]
    )));
    // IBP: the base and server parts name I.i1 at 2000, the private part I.i0.
    assert!(refused(entries_of(
        true,
        [
            vec![instance("I.i1", 2000)],
            vec![instance("I.i1", 2000)],
            vec![i0()]
        ]
    )));
    // IP: only the private part names I.i1.
    assert!(refused(entries_of(
        true,
        [vec![i0()], vec![i0()], vec![instance("I.i1", 1000)]]
    )));
    // IX: the private table is empty.
    assert!(refused(entries_of(true, [vec![i0()], vec![i0()], vec![]])));
    // A priority changed in the private part only.
    assert!(refused(entries_of(
        true,
        [vec![i0()], vec![i0()], vec![instance("I.i0", 2000)]]
    )));
    // Not a module-system artifact: read through its `.olean`; a companion
    // may repeat it, and may add nothing.
    entries_of(false, [vec![i0()], vec![i0()], vec![]]).expect("companions state no more");
    assert!(refused(entries_of(
        false,
        [vec![i0()], vec![], vec![instance("I.i1", 2000)]]
    )));
}

/// A module-system artifact's named rows of tables Clean does not
/// register from (Lean's `namespacesExt`) are not stated cumulatively by
/// an honest `lean` build — its `.olean` held a row its `.olean.private`
/// did not (module_trust `the_parts_of_one_module_loaded_through_the_parsed_path_must_agree`)
/// — and Clean registers them from the private part only, so they are
/// not compared; an instance row still is. Any other artifact's named
/// rows are compared: its companions state nothing its `.olean` does not.
#[test]
fn a_module_system_artifacts_named_rows_are_not_compared_but_its_tables_are() {
    let named = |n: &str| TypedExtensionEntry::Named {
        name: Name::from_string(n),
        data: crate::module::ParsedExtensionEntryData::Object(vec![0]),
    };
    let ns = |entries: Vec<TypedExtensionEntry>| {
        vec![TypedExtension {
            extension_name: Name::from_string("_private.Lean.Namespace.0.Lean.namespacesExt"),
            source_rows: Some(entries.len()),
            entries,
            undecoded_entries: 0,
            compiler_names: None,
        }]
    };
    let check = |module_system: bool, parts: [Vec<TypedExtensionEntry>; 3]| {
        let [a, b, c] = parts.map(ns);
        check_artifact_entries(
            &key("D"),
            module_system,
            &[Some(a.as_slice()), Some(b.as_slice()), Some(c.as_slice())],
        )
    };
    check(true, [vec![named("")], vec![named("")], vec![]])
        .expect("an honest module's namespace rows need not repeat in its private part");
    assert!(matches!(
        check(false, [vec![], vec![named("N")], vec![]]),
        Err(ImportError::PartsDisagreeOnEntry { .. })
    ));
    assert!(matches!(
        entries_of(
            true,
            [
                vec![instance("I.i0", 1000)],
                vec![instance("I.i0", 1000)],
                vec![]
            ]
        ),
        Err(ImportError::PartsDisagreeOnEntry { .. })
    ));
}

#[test]
fn parts_handed_over_one_call_each_are_held_to_the_same_rule() {
    let mut env = Environment::with_prelude();
    let i0 = table(vec![instance("I.i0", 1000)]);
    let i1 = table(vec![instance("I.i1", 2000)]);
    check_part_entries(&mut env, &key("I"), true, &i0).expect("base");
    let err = check_part_entries(&mut env, &key("I"), true, &i1).expect_err("server drops I.i0");
    assert!(
        matches!(err, ImportError::PartsDisagreeOnEntry { .. }),
        "{err}"
    );
    check_part_entries(&mut env, &key("I"), true, &i0).expect("server as the base");
    // Another artifact begins a load of its own.
    check_part_entries(&mut env, &key("J"), true, &i1).expect("J's base");
}

#[test]
fn completion_evidence_requires_an_actual_matching_active_load() {
    let mut env = Environment::default();
    assert!(finish_artifact_load(&mut env, &key("Missing"))
        .unwrap()
        .is_none());
    begin_artifact_load(&mut env, &key("D"), false).unwrap();
    remember_part_records(&mut env, &key("D"), [record("D.e", c("Nat.zero"))]);
    assert!(finish_artifact_load(&mut env, &key("Other"))
        .unwrap()
        .is_none());
    assert!(finish_artifact_load(&mut env, &key("D")).unwrap().is_some());
    assert!(finish_artifact_load(&mut env, &key("D")).unwrap().is_none());
}

#[test]
fn compiler_name_stub_completion_safety_matrix_preserves_partial_versions() {
    use crate::DefinitionSafety::{Partial, Safe, Unsafe};
    use clean_kernel::env::ConstantKind;
    for (stub_safety, full_safety, expected) in [
        (Some(Safe), Some(Safe), true),
        (Some(Unsafe), Some(Unsafe), true),
        (Some(Safe), Some(Partial), true),
        (Some(Unsafe), Some(Partial), true),
        (Some(Unsafe), Some(Safe), false),
        (Some(Safe), Some(Unsafe), false),
        (None, Some(Safe), false),
        (Some(Safe), None, false),
        (None, None, true),
    ] {
        let mut early = stub(nat());
        let mut later = record("D.e", c("Nat.zero"));
        if let PartRecord::Constant { info, safety } = &mut early {
            info.kind = ConstantKind::Axiom;
            *safety = stub_safety;
        }
        if let PartRecord::Constant { safety, .. } = &mut later {
            *safety = full_safety;
        }
        assert_eq!(
            records_agree(&early, &later),
            expected,
            "{stub_safety:?} -> {full_safety:?}"
        );
    }
    for (stub_safety, expected) in [(Some(Safe), true), (Some(Unsafe), false)] {
        let mut early = stub(nat());
        let mut later = record("D.e", c("Nat.zero"));
        if let PartRecord::Constant { info, safety } = &mut early {
            info.kind = ConstantKind::Axiom;
            *safety = stub_safety;
        }
        if let PartRecord::Constant { info, .. } = &mut later {
            info.kind = ConstantKind::Theorem;
        }
        assert_eq!(records_agree(&early, &later), expected);
    }
}
