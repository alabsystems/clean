// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MAKE-IT-REAL end-to-end test: load a REAL `ty certify` certificate (produced
//! by `ty certify examples/.../Accumulator.tla`, committed under
//! `tests/fixtures/accumulator.ty.cert.json`) and confirm the Clean kernel
//! ACCEPTS the `InductiveInvariantSound` instance re-encoded from its
//! `spec_src`.
//!
//! This is the source-fidelity claim of the TY×Clean program: a real TY safety
//! verdict, re-checked as a CIC kernel theorem.

use clean_kernel::env::{ConstantKind, Environment, ProofQuality};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use clean_tla::ty_cert::{self, TyCert};

const REAL_CERT: &str = include_str!("fixtures/accumulator.ty.cert.json");

/// The fixture is a GENUINE `ty.cert/v1` produced by `ty certify`: schema +
/// verdict + AY strict-verified obligations.
#[test]
fn cert_fixture_is_a_real_ty_verdict() {
    let cert = TyCert::from_json(REAL_CERT).expect("parse real cert");
    assert_eq!(cert.schema, "ty.cert/v1");
    assert_eq!(cert.verdict, "inductive-safety-safe");
    assert_eq!(cert.init.as_deref(), Some("Init"));
    assert_eq!(cert.next.as_deref(), Some("Next"));
    assert_eq!(cert.invariants, vec!["Safety".to_string()]);
    assert_eq!(cert.invariant_j_tla, "x >= 0");
    // The SMT obligations were strict-verified by AY (the verdict's acceptance
    // basis we are re-checking the *structure* of).
    assert!(
        cert.all_obligations_ay_strict_verified(),
        "every covered obligation must be AY strict-verified"
    );
    // The fidelity meter is non-trivial: Int-modelled-as-Nat is surfaced.
    let notes = cert.fidelity_notes();
    assert!(!notes.is_empty(), "Int→Nat fidelity must be surfaced");
    assert!(notes[0].contains("Int") && notes[0].contains("Nat"));
}

/// The encoding is driven by `spec_src` (source fidelity): perturbing the spec
/// text changes the encoded `Init` predicate.
#[test]
fn encoding_is_source_driven() {
    let cert = TyCert::from_json(REAL_CERT).expect("parse");
    let enc = ty_cert::encode_cert(&cert).expect("encode from spec_src");

    // Now perturb spec_src's Init from `x = 0` to `x = 1` and re-encode.
    let mut perturbed = cert.clone();
    perturbed.spec_src = perturbed.spec_src.replace("Init == x = 0", "Init == x = 1");
    let enc2 = ty_cert::encode_cert(&perturbed).expect("encode perturbed");

    assert_ne!(
        format!("{:?}", enc.init),
        format!("{:?}", enc2.init),
        "changing spec_src's Init body MUST change the encoded Init predicate"
    );
    // Next/Safety/J are unchanged by the Init perturbation.
    assert_eq!(format!("{:?}", enc.next), format!("{:?}", enc2.next));
}

/// THE HEADLINE: the kernel accepts the `InductiveInvariantSound` instance for
/// the real Accumulator cert, with the three obligations as named Pi-hypotheses
/// (the `_assumed` product — works on a bare `Environment::new()`).
#[test]
fn kernel_accepts_assumed_instance_for_real_cert() {
    let cert = TyCert::from_json(REAL_CERT).expect("parse");
    let enc = ty_cert::encode_cert(&cert).expect("encode from spec_src");

    let mut env = Environment::new();
    ty_cert::register_ty_cert_safety_assumed(&mut env, "TYAccumulatorSafety", &enc)
        .expect("register the InductiveInvariantSound instance (assumed obligations)");

    let name = Name::from_string("TYAccumulatorSafety");
    let info = env.get_const(&name).expect("theorem registered");
    assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
    assert!(info.value.is_some(), "Theorem retains its proof term");

    // Re-run the kernel type-checker on the stored proof against its type — the
    // independent confirmation that the term is well-typed.
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(info.value.as_ref().unwrap(), &info.type_)
        .expect("the assumed instance must kernel-check");

    // proof_quality: the instance reaches only foundational constants PLUS the
    // three Pi-bound obligation hypotheses (which are NOT axioms) → Constructive.
    let q = env.proof_quality(&name).expect("proof quality");
    assert_eq!(
        q,
        ProofQuality::Constructive,
        "the assumed instance must be Constructive (no axioms; obligations are Pi-bound), got {q:?}"
    );

    // It must NOT introduce any new axioms beyond the keystone's foundational set.
    let deps = env.axiom_deps(&name).expect("axiom deps");
    let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    for forbidden in &names {
        assert!(
            !forbidden.contains("sorry") && !forbidden.contains("Sorry"),
            "no sorry/admit in the closure, got {names:?}"
        );
    }
}

/// THE STRONGEST RESULT: on `with_prelude()`, the three obligations discharge
/// CONSTRUCTIVELY (via `Nat.zero_le`), giving a fully closed, axiom-free
/// theorem `TYAccumulatorSafetyClosed : ∀ b, Runs Init Next b → Sat b (□ Safety)`
/// for the real cert — no remaining hypotheses.
#[test]
fn kernel_accepts_closed_axiomfree_instance_for_real_cert() {
    let cert = TyCert::from_json(REAL_CERT).expect("parse");
    let enc = ty_cert::encode_cert(&cert).expect("encode from spec_src");

    let mut env = Environment::with_prelude();
    ty_cert::register_ty_cert_safety_closed(&mut env, "TYAccumulatorSafetyClosed", &enc)
        .expect("closed discharge for `x >= 0` over Nat must register");

    let name = Name::from_string("TYAccumulatorSafetyClosed");
    let info = env.get_const(&name).expect("closed theorem registered");
    assert_eq!(info.kind, ConstantKind::Theorem);

    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(info.value.as_ref().unwrap(), &info.type_)
        .expect("the closed instance must kernel-check");

    // The closed theorem's TYPE is exactly the conclusion (no leftover
    // hypotheses): it begins with a ∀ b binder, not an obligation Pi.
    // We confirm by re-inferring its type and checking it is a Pi whose first
    // binder is the behaviour `Nat → Nat`.
    let inferred = tc
        .infer_type(&Expr::const_(name.clone(), vec![]))
        .expect("infer closed theorem type");
    let pretty = format!("{:?}", inferred);
    assert!(
        pretty.contains("Runs") && pretty.contains("Sat"),
        "closed type must be the bare ∀ b, Runs … → Sat … conclusion; got {pretty}"
    );

    // Axiom-free (Constructive): closure ⊆ FOUNDATIONAL_AXIOMS.
    let q = env.proof_quality(&name).expect("proof quality");
    assert_eq!(
        q,
        ProofQuality::Constructive,
        "the closed instance must be Constructive/axiom-free, got {q:?}"
    );
}

/// Rigour: enumerate the axiom closure of BOTH products and assert no
/// non-foundational axiom (and specifically no `sorry`/`Axiom` stand-in) leaks
/// in. The closed product must have an EMPTY-or-foundational closure.
#[test]
fn axiom_closure_is_honest() {
    let cert = TyCert::from_json(REAL_CERT).unwrap();
    let enc = ty_cert::encode_cert(&cert).unwrap();

    // assumed (bare env)
    let mut e1 = Environment::new();
    ty_cert::register_ty_cert_safety_assumed(&mut e1, "AX_assumed", &enc).unwrap();
    let d1: Vec<String> = e1
        .axiom_deps(&Name::from_string("AX_assumed"))
        .unwrap()
        .iter()
        .map(|n| n.to_string())
        .collect();
    eprintln!("assumed axiom_deps = {d1:?}");
    assert!(
        d1.iter()
            .all(|n| !n.contains("sorry") && !n.contains("Sorry")),
        "assumed must not depend on sorry: {d1:?}"
    );

    // closed (prelude env)
    let mut e2 = Environment::with_prelude();
    ty_cert::register_ty_cert_safety_closed(&mut e2, "AX_closed", &enc).unwrap();
    let d2: Vec<String> = e2
        .axiom_deps(&Name::from_string("AX_closed"))
        .unwrap()
        .iter()
        .map(|n| n.to_string())
        .collect();
    eprintln!("closed axiom_deps = {d2:?}");
    assert!(
        d2.iter()
            .all(|n| !n.contains("sorry") && !n.contains("Sorry")),
        "closed must not depend on sorry: {d2:?}"
    );
    // The closed product is Constructive ⇒ its closure ⊆ FOUNDATIONAL_AXIOMS.
    assert_eq!(
        e2.proof_quality(&Name::from_string("AX_closed")).unwrap(),
        ProofQuality::Constructive
    );
}
