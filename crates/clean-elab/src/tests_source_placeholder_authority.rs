// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordinary source cannot consume compatibility axioms at any family output slot.

use crate::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use crate::FileContext;
use clean_kernel::env::{ConstantInfo, KernelClassInfo, KernelInstanceInfo};
use clean_kernel::inductive::{ConstructorVal, InductiveVal, RecursorVal};
use clean_kernel::{Environment, Expr, Name};

#[derive(Debug, PartialEq)]
struct Snapshot {
    generation: u64,
    constants: Vec<ConstantInfo>,
    verification: Vec<(Name, Option<clean_kernel::env::DeclarationVerification>)>,
    source_kinds: Vec<(Name, Option<clean_kernel::env::ConstantKind>)>,
    inductives: Vec<InductiveVal>,
    constructors: Vec<ConstructorVal>,
    recursors: Vec<RecursorVal>,
    classes: Vec<KernelClassInfo>,
    instances: Vec<KernelInstanceInfo>,
    flags: Vec<(Name, bool, bool, bool, bool)>,
    structure_fields: Vec<(Name, Vec<Name>)>,
    structure_parents: Vec<(Name, Vec<(Name, Name)>)>,
}

fn snapshot(env: &Environment) -> Snapshot {
    let mut constants: Vec<_> = env.constants().cloned().collect();
    constants.sort_by(|left, right| left.name.cmp(&right.name));
    let mut inductives: Vec<_> = env.inductives().cloned().collect();
    inductives.sort_by(|left, right| left.name.cmp(&right.name));
    let mut constructors: Vec<_> = env.constructors().cloned().collect();
    constructors.sort_by(|left, right| left.name.cmp(&right.name));
    let mut recursors: Vec<_> = env.recursors().cloned().collect();
    recursors.sort_by(|left, right| left.name.cmp(&right.name));
    let mut classes: Vec<_> = env.classes().cloned().collect();
    classes.sort_by(|left, right| left.name.cmp(&right.name));
    let mut instances: Vec<_> = env.instances().cloned().collect();
    instances.sort_by(|left, right| left.name.cmp(&right.name));
    let flags = constants
        .iter()
        .map(|constant| {
            (
                constant.name.clone(),
                env.is_unsafe(&constant.name),
                env.is_partial(&constant.name),
                env.is_private(&constant.name),
                env.is_protected(&constant.name),
            )
        })
        .collect();
    let structure_fields = inductives
        .iter()
        .filter_map(|inductive| {
            env.get_structure_field_names(&inductive.name)
                .map(|fields| (inductive.name.clone(), fields.to_vec()))
        })
        .collect();
    let structure_parents = inductives
        .iter()
        .filter_map(|inductive| {
            env.get_structure_parents(&inductive.name)
                .map(|parents| (inductive.name.clone(), parents.to_vec()))
        })
        .collect();
    let verification = constants
        .iter()
        .map(|constant| {
            (
                constant.name.clone(),
                env.declaration_verification(&constant.name),
            )
        })
        .collect();
    let source_kinds = constants
        .iter()
        .map(|constant| {
            (
                constant.name.clone(),
                crate::source_kind::get(env, &constant.name),
            )
        })
        .collect();
    Snapshot {
        generation: env.generation(),
        constants,
        verification,
        source_kinds,
        inductives,
        constructors,
        recursors,
        classes,
        instances,
        flags,
        structure_fields,
        structure_parents,
    }
}

fn apply(env: &mut Environment, source: &str) {
    let declarations = clean_parser::parse_file(source).expect("source parses");
    let mut context = FileContext::new();
    let outcome = elaborate_module(
        env,
        &mut context,
        &[SourceUnit {
            id: UnitId(0),
            decls: &declarations,
        }],
        BatchOptions::islands(),
    );
    assert!(
        outcome.is_clean() && outcome.committed,
        "{}",
        outcome.render_rejections()
    );
}

fn refuse_without_change(env: &Environment, source: &str) {
    let declarations = clean_parser::parse_file(source).expect("source parses");
    assert_eq!(declarations.len(), 1, "one source declaration per refusal");
    let mut direct = env.clone();
    // The public direct entry deliberately installs fixed session support
    // before a declaration. Its documented attribution contract prepares that
    // support before taking a census; it is not a source-family replacement.
    let old_constants: Vec<_> = direct.constants().cloned().collect();
    crate::prepare_declaration_environment(&mut direct, &declarations[0]);
    for old in &old_constants {
        assert_eq!(direct.get_const(&old.name), Some(old));
    }
    let before = snapshot(&direct);
    crate::prepare_declaration_environment(&mut direct, &declarations[0]);
    assert_eq!(
        snapshot(&direct),
        before,
        "session preparation is idempotent"
    );
    let result = crate::elaborate_decl_and_register(&mut direct, &declarations[0]);
    assert!(
        result.is_err(),
        "ordinary source replaced an existing family slot: {source}"
    );
    assert_eq!(
        snapshot(&direct),
        before,
        "direct source refusal changed environment"
    );

    let mut batch = env.clone();
    let before = snapshot(&batch);
    let mut context = FileContext::new();
    let outcome = elaborate_module(
        &mut batch,
        &mut context,
        &[SourceUnit {
            id: UnitId(0),
            decls: &declarations,
        }],
        BatchOptions::islands(),
    );
    assert!(
        !outcome.is_clean(),
        "batch source replaced an existing family slot: {source}"
    );
    assert_eq!(
        snapshot(&batch),
        before,
        "batch source refusal changed environment"
    );
}

#[test]
fn source_owner_axioms_and_opaques_refuse_structure_or_class() {
    for initial in [
        "axiom Occupied : Type\n",
        "unsafe axiom Occupied : Type\n",
        "opaque Occupied : Type\n",
        "unsafe opaque Occupied : Type\n",
    ] {
        let mut env = Environment::with_prelude();
        apply(&mut env, initial);
        for family in ["structure", "class"] {
            for safety in ["", "unsafe "] {
                refuse_without_change(&env, &format!("{safety}{family} Occupied where\n"));
            }
        }
    }
}

#[test]
fn foreign_constructor_axiom_does_not_authorize_a_fresh_structure() {
    let mut env = Environment::with_prelude();
    apply(&mut env, "axiom Fresh.mk : False\n");
    for family in ["structure", "class"] {
        for safety in ["", "unsafe "] {
            refuse_without_change(&env, &format!("{safety}{family} Fresh where\n"));
        }
    }
}

#[test]
fn foreign_projection_axiom_does_not_authorize_a_fresh_structure() {
    let mut env = Environment::with_prelude();
    apply(&mut env, "axiom Fresh.field : False\n");
    for family in ["structure", "class"] {
        refuse_without_change(&env, &format!("{family} Fresh where\n  field : Nat\n"));
    }
}

#[test]
fn retained_theorem_cannot_lose_its_constructor_named_axiom() {
    let mut env = Environment::with_prelude();
    apply(
        &mut env,
        "axiom S.mk : False\ntheorem retainedFalse : False := S.mk\n",
    );
    let old = env
        .get_const(&Name::from_string("retainedFalse"))
        .expect("checked theorem")
        .clone();
    let old_axioms = env.axiom_deps(&old.name).expect("closure");
    assert!(old_axioms.contains(&Name::from_string("S.mk")));
    let old_verification = env.declaration_verification(&old.name);
    refuse_without_change(&env, "structure S where\n");
    assert_eq!(env.get_const(&old.name), Some(&old));
    assert_eq!(env.axiom_deps(&old.name), Some(old_axioms));
    assert_eq!(env.declaration_verification(&old.name), old_verification);
    assert!(env.get_inductive(&Name::from_string("S")).is_none());
}

#[test]
fn source_slot_checks_use_actual_typed_names() {
    let mut env = Environment::with_prelude();
    apply(
        &mut env,
        "axiom «Fresh.mk» : False\naxiom N.Fresh.field : False\n",
    );
    apply(&mut env, "structure Fresh where\n");
    assert!(env
        .get_constructor(&Name::from_string("Fresh.mk"))
        .is_some());
    assert!(env.get_const(&Name::anon().str("Fresh.mk")).is_some());
    refuse_without_change(&env, "structure N.Fresh where\n  field : Nat\n");
}

#[test]
fn fresh_families_and_dependent_projection_proofs_still_register() {
    let mut env = Environment::with_prelude();
    apply(&mut env, "structure Fresh where\n  field : Nat\nclass Carrier (p : Prop) : Prop where\n  out : p\ninductive Single : Type where\n  | mk : Single\nmutual\n  inductive Left : Type where\n    | base : Left\n    | step : Right -> Left\n  inductive Right : Type where\n    | step : Left -> Right\nend\ntheorem Carrier.elim {p : Prop} (h : Carrier p) : p := h.1\n");
    assert!(env.get_inductive(&Name::from_string("Fresh")).is_some());
    assert!(env.is_class(&Name::from_string("Carrier")));
    for name in ["Single", "Left", "Right"] {
        assert!(env.get_inductive(&Name::from_string(name)).is_some());
    }
    let proof = env
        .get_const(&Name::from_string("Carrier.elim"))
        .expect("dependent proof");
    assert!(env.axiom_deps(&proof.name).expect("closure").is_empty());
    let declaration = clean_kernel::Declaration::Theorem {
        name: proof.name.clone(),
        level_params: proof.level_params.clone(),
        type_: proof.type_.clone(),
        value: proof.value.clone().expect("proof value"),
    };
    env.check_decl_readonly_strict(&declaration)
        .expect("retained proof rechecks");
}

#[test]
fn explicit_kernel_replay_keeps_its_existing_contract() {
    let mut env = Environment::with_prelude();
    apply(&mut env, "structure Replay where\n");
    let name = Name::from_string("Replay");
    let declaration = env.inductive_decl_of(&name).expect("typed declaration");
    let before = snapshot(&env);
    env.add_inductive(declaration.clone())
        .expect("explicit exact kernel replay");
    assert_eq!(snapshot(&env), before);
    let mut bad = declaration;
    bad.types[0].type_ = Expr::prop();
    assert!(env.add_inductive(bad).is_err());
    assert_eq!(snapshot(&env), before);
}

#[test]
fn builtin_fact_completion_is_immediate_and_keeps_dependent_proofs_checked() {
    let mut env = Environment::with_prelude();
    crate::source_family_authority::complete_fact_bootstrap(&mut env)
        .expect("actual builtin creation and completion");
    let owner = Name::from_string("Fact");
    assert!(env.get_inductive(&owner).is_some());
    assert!(env.is_class(&owner));
    assert_eq!(
        env.get_class_info(&owner)
            .expect("genuine class metadata")
            .num_params,
        1
    );
    assert_eq!(
        env.get_structure_field_names(&owner)
            .expect("genuine structure fields")
            .len(),
        1
    );
    refuse_without_change(&env, "attribute [class] Fact\n");
    apply(
        &mut env,
        "theorem Fact.elim {p : Prop} (h : Fact p) : p := h.1\n",
    );
    let theorem = env
        .get_const(&Name::from_string("Fact.elim"))
        .expect("dependent proof");
    assert!(env.axiom_deps(&theorem.name).expect("closure").is_empty());
    let audit = env.audit_certification(&theorem.type_, theorem.value.as_ref().expect("proof"));
    assert!(audit.issues.is_empty(), "{audit:?}");
    let before = snapshot(&env);
    crate::source_family_authority::complete_fact_bootstrap(&mut env).expect("initializer no-op");
    assert_eq!(snapshot(&env), before);
    refuse_without_change(&env, "class Fact (p : Prop) : Prop where\n  out : p\n");
}

#[test]
fn builtin_fact_creation_does_not_launder_existing_or_partially_created_slots() {
    for source in [
        "axiom Fact : Prop -> Prop\n",
        "axiom Fact.mk : False\n",
        "axiom Fact.out : False\n",
        "axiom Fact.rec : False\n",
    ] {
        let mut env = Environment::with_prelude();
        apply(&mut env, source);
        let before = snapshot(&env);
        assert!(
            crate::source_family_authority::complete_fact_bootstrap(&mut env).is_err(),
            "{source}"
        );
        assert_eq!(
            snapshot(&env),
            before,
            "builtin failure exposed a creation prefix: {source}"
        );
    }
}

#[test]
fn raw_kernel_fact_initializer_does_not_grant_source_replacement_authority() {
    let mut env = Environment::with_prelude();
    env.init_fact()
        .expect("explicit raw kernel stub theory remains available");
    let before = snapshot(&env);
    crate::source_family_authority::complete_fact_bootstrap(&mut env)
        .expect("existing initializer no-op grants nothing");
    assert_eq!(snapshot(&env), before);
    assert!(env.get_inductive(&Name::from_string("Fact")).is_none());
    refuse_without_change(&env, "class Fact (p : Prop) : Prop where\n  out : p\n");
    let declarations = clean_parser::parse_file("class Fact (p : Prop) : Prop where\n  out : p\n")
        .expect("fixed class source");
    let result = crate::elaborate_decl(&env, &declarations[0]).expect("typed source result");
    for name in crate::register::leaf_own_names(&result) {
        assert!(env.discharge_axiom_stub_for_inductive_import(&name));
    }
    crate::register::register_elab_result(&mut env, &result)
        .expect("explicit typed replay remains available after explicit kernel discharge");
    assert!(env.get_inductive(&Name::from_string("Fact")).is_some());
}
