// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Declaration, Expr, Level};

use super::*;
use crate::{
    load_module_with_deps, pinned_lean_lib_path, reference_base_closed, ClosedRecheckOptions,
};

fn name(text: &str) -> Name {
    Name::from_string(text)
}

fn constant(text: &str) -> Expr {
    Expr::const_(name(text), vec![])
}

fn equality(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(name("Eq"), vec![Level::succ(Level::zero())]),
        [constant("Nat"), left, right],
    )
}

fn reflexivity(value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(name("Eq.refl"), vec![Level::succ(Level::zero())]),
        [constant("Nat"), value],
    )
}

fn admit(body: u64, right: Expr, proof: Expr) -> Environment {
    let mut environment = Environment::with_prelude();
    environment
        .add_decl(Declaration::Definition {
            name: name("Producer.route"),
            level_params: vec![],
            type_: constant("Nat"),
            value: Expr::nat_lit(body),
            is_reducible: true,
        })
        .expect("checked producer definition");
    environment
        .add_decl(Declaration::Axiom {
            name: name("Ambient.assumed"),
            level_params: vec![],
            type_: equality(constant("Producer.route"), right.clone()),
        })
        .expect("control world with a foreign axiom");
    environment
        .add_decl(Declaration::Theorem {
            name: name("Consumer.correct"),
            level_params: vec![],
            type_: equality(constant("Producer.route"), right),
            value: proof,
        })
        .expect("well-typed consumer theorem");
    environment
}

#[test]
fn pins_bind_both_mounted_units_and_check_proof_axioms() {
    let producer = name("Producer");
    let consumer = name("Consumer");
    let route = name("Producer.route");
    let correct = name("Consumer.correct");
    let ownership = ModuleOwnership::from([
        (producer.clone(), BTreeSet::from([route.clone()])),
        (consumer.clone(), BTreeSet::from([correct.clone()])),
    ]);
    let package = Package::of_names(BTreeSet::from([route, correct.clone()]));
    let original = constant("Producer.route");
    let base = admit(0, original.clone(), reflexivity(original.clone()));
    let expected = MeaningDigests::new(&base, &package);
    let pins = BTreeMap::from([(
        correct.clone(),
        ResidentPin {
            kind: ConstantKind::Theorem,
            digest: expected.digest(&correct).expect("pinned digest"),
            meaning_closure: expected.closure(&correct).expect("pinned closure"),
            axiom_closure: BTreeSet::new(),
        },
    )]);
    let compare = |environment: &Environment| {
        compare_resident_pins(environment, &package, &ownership, &ownership, &pins)
    };
    assert_eq!(compare(&base), Ok(()));
    assert_eq!(
        compare(&admit(0, original.clone(), reflexivity(Expr::nat_lit(0)))),
        Ok(()),
        "an alternative axiom-free proof has the same pin"
    );
    assert_eq!(
        compare(&admit(1, original.clone(), reflexivity(original.clone()))),
        Err(ResidentPinError::Digest(correct.clone())),
        "a different producer body changes the consumer's meaning"
    );
    assert_eq!(
        compare(&admit(0, Expr::nat_lit(0), reflexivity(original.clone()))),
        Err(ResidentPinError::Digest(correct.clone())),
        "a different well-typed statement keeps its dependencies but moves the pin"
    );
    assert_eq!(
        compare(&admit(0, original, constant("Ambient.assumed"))),
        Err(ResidentPinError::OutsideAx0(
            correct.clone(),
            BTreeSet::from([name("Ambient.assumed")]),
        )),
        "a changed proof with the same statement must still satisfy Ax0"
    );
    let mut unmounted = ownership.clone();
    unmounted.remove(&producer);
    assert_eq!(
        compare_resident_pins(&base, &package, &ownership, &unmounted, &pins),
        Err(ResidentPinError::Modules)
    );
    let mut extra = ownership.clone();
    extra
        .entry(consumer.clone())
        .or_default()
        .insert(name("Consumer.extra"));
    assert_eq!(
        compare_resident_pins(&base, &package, &ownership, &extra, &pins),
        Err(ResidentPinError::Ownership(consumer))
    );
}

#[test]
fn checked_terms_preserve_source_identity_and_compare_changed_dependencies() {
    let producer = name("Producer");
    let consumer = name("Consumer");
    let route = name("Producer.route");
    let correct = name("Consumer.correct");
    let ownership = ModuleOwnership::from([
        (producer.clone(), BTreeSet::from([route.clone()])),
        (consumer.clone(), BTreeSet::from([correct.clone()])),
    ]);
    let package = Package::of_names(BTreeSet::from([route.clone(), correct.clone()]));
    let resident_roots = BTreeSet::from([correct.clone(), name("Eq.refl")]);
    let library = pinned_lean_lib_path().expect("pinned Lean library");
    let mut base = Environment::for_lean_replay();
    load_module_with_deps(&mut base, "Init.Prelude", &[library]).unwrap();
    let fence = |body: Expr| {
        let mut env = base.clone();
        env.add_decl(Declaration::Definition {
            name: route.clone(),
            level_params: vec![],
            type_: constant("Nat"),
            value: body,
            is_reducible: false,
        })
        .unwrap();
        let application = constant("Producer.route");
        env.add_decl(Declaration::Theorem {
            name: correct.clone(),
            level_params: vec![],
            type_: equality(application.clone(), application.clone()),
            value: reflexivity(application),
        })
        .unwrap();
        reference_base_closed(&env, &resident_roots, &ClosedRecheckOptions::default())
            .unwrap()
            .into_kernel()
            .unwrap()
    };
    let reference = fence(Expr::nat_lit(0));
    let equivalent = fence(Expr::let_named(
        name("n"),
        constant("Nat"),
        Expr::nat_lit(0),
        Expr::bvar(0),
        false,
    ));
    let altered = fence(Expr::nat_lit(1));
    let pinned = MeaningDigests::new(reference.environment(), &package);
    let pins = BTreeMap::from([(
        correct.clone(),
        ResidentPin {
            kind: ConstantKind::Theorem,
            digest: pinned.digest(&correct).unwrap(),
            meaning_closure: pinned.closure(&correct).unwrap(),
            axiom_closure: BTreeSet::new(),
        },
    )]);
    let captured = BTreeMap::from([
        (producer.clone(), b"producer".as_slice()),
        (consumer, b"consumer".as_slice()),
    ]);
    let digests = captured
        .iter()
        .map(|(module, bytes)| (module.clone(), Sha256::digest(bytes).into()))
        .collect();
    let mut mutation = captured.clone();
    mutation.insert(producer.clone(), b"changed".as_slice());
    let compare = |source, captured_sources| {
        let inputs = ResidentTermInputs {
            source,
            reference: &reference,
            reference_source_sha256: &digests,
            captured_sources,
        };
        compare_resident_pins_with_terms(&inputs, &package, &ownership, &ownership, &pins)
    };
    assert_eq!(
        compare_resident_pins(
            equivalent.environment(),
            &package,
            &ownership,
            &ownership,
            &pins
        ),
        Err(ResidentPinError::Digest(correct)),
    );
    assert_eq!(compare(&equivalent, &captured), Ok(()));
    assert_eq!(
        compare(&equivalent, &mutation),
        Err(ResidentPinError::SourceDigest(producer)),
    );
    assert_eq!(
        compare(&altered, &captured),
        Err(ResidentPinError::Term(route))
    );
}
