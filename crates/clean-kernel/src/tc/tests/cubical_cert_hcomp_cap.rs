// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! SOUNDNESS regression: the **certificate verifier** must enforce the CCHM
//! `hcomp` well-formedness side conditions (overlap agreement + cap/floor
//! agreement), exactly as the release inference path and the certificate builder
//! do.
//!
//! Background — the cap hole (commit 3a5c9271) closed a soundness hole on the
//! release path and the cert *builder* by adding `validate_hcomp_cap`: a
//! floor-disagreeing `hcomp` such as `hcomp {Nat} [(j=1)↦λ_.succ zero] zero` has
//! tube i0-cap `succ zero ≢ zero`, and `<j>` of it inhabits `Path Nat 0 1`, from
//! which a closed proof of `Empty` follows. The **independent certificate
//! verifier** (`cert/verifier/cubical.rs`) was overlooked by that fix — it
//! re-checked basic typing but neither the overlap nor the cap condition, so it
//! would re-verify a certificate for the bad `hcomp`, returning `Nat` and thereby
//! violating its own documented contract `infer_type(expr) == result`. These
//! tests lock the verifier closed and guard against over-rejection.

use super::*;

use crate::cert::{CertVerifier, ProofCert};
use crate::env::Declaration;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::mode::CleanMode;
use std::sync::Arc;

fn cst(s: &str) -> Expr {
    Expr::const_(Name::from_string(s), Vec::<Level>::new())
}
fn interval() -> Expr {
    Expr::from_kind(ExprKind::CubicalInterval)
}
fn nat() -> Expr {
    cst("Nat")
}
fn zero() -> Expr {
    cst("Nat.zero")
}
fn succ(n: Expr) -> Expr {
    Expr::app(cst("Nat.succ"), n)
}
fn face_eq1(r: Expr) -> Expr {
    Expr::app(cst("Cofib.eq1"), r)
}
fn const_tube(v: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, interval(), v)
}
fn hcomp(phi: Expr, u: Expr, base: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(nat()),
        phi: Arc::new(phi),
        u: Arc::new(u),
        base: Arc::new(base),
    })
}

/// Cubical env with `Nat` (zero/succ → `Nat.rec`), the cofibration axioms, and a
/// neutral interval const `j : I` (so `(j=1)` is neither ⊤ nor ⊥).
fn nat_cubical_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Nat"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat(), nat()),
                },
            ],
        }],
    };
    env.add_inductive(decl).expect("Nat inductive registers");
    reduction::kan::register_kan_system_axioms(&mut env).expect("cofibration axioms register");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("j"),
        level_params: vec![],
        type_: interval(),
    })
    .expect("neutral interval j registers");
    env
}

/// Assemble a `ProofCert::CubicalHComp` from genuine sub-certs (the sub-terms are
/// each individually well-typed even when the whole `hcomp` is cap-incoherent).
fn hcomp_cert(tc: &TypeChecker<'_>, phi: &Expr, u: &Expr, base: &Expr) -> ProofCert {
    ProofCert::CubicalHComp {
        ty_cert: Box::new(tc.infer_type_with_cert(&nat()).expect("Nat cert").1),
        phi_cert: Box::new(tc.infer_type_with_cert(phi).expect("phi cert").1),
        u_cert: Box::new(tc.infer_type_with_cert(u).expect("u cert").1),
        base_cert: Box::new(tc.infer_type_with_cert(base).expect("base cert").1),
        result_type: Box::new(nat()),
    }
}

/// THE HOLE: the certificate verifier must REJECT a floor-disagreeing `hcomp`,
/// matching `infer_type`'s rejection (the verifier's `infer_type == result`
/// contract). Tube i0-cap `succ zero ≢ zero` on the (neutral) face `(j=1)`.
#[test]
fn test_cert_verifier_rejects_floor_disagreeing_hcomp() {
    let env = nat_cubical_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let phi = face_eq1(cst("j"));
    let u = const_tube(succ(zero()));
    let base = zero();
    let bad = hcomp(phi.clone(), u.clone(), base.clone());

    // The kernel's inference rejects it (cap fix on the release path).
    assert!(
        tc.infer_type(&bad).is_err(),
        "infer_type must reject the floor-disagreeing hcomp"
    );

    // The independent certificate verifier must reject it too.
    let cert = hcomp_cert(&tc, &phi, &u, &base);
    let mut v = CertVerifier::with_mode(&env, CleanMode::Cubical);
    assert!(
        v.verify(&cert, &bad).is_err(),
        "cert verifier must REJECT the floor-disagreeing hcomp (was a soundness hole)"
    );
}

/// The verifier must NOT over-reject a **well-formed** `hcomp` (tube i0-cap equals
/// the floor): a cap-coherent term still verifies.
#[test]
fn test_cert_verifier_accepts_well_formed_hcomp() {
    let env = nat_cubical_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // cap `succ zero` == floor `succ zero` — coherent on the neutral face (j=1).
    let phi = face_eq1(cst("j"));
    let u = const_tube(succ(zero()));
    let base = succ(zero());
    let good = hcomp(phi.clone(), u.clone(), base.clone());

    assert!(
        tc.infer_type(&good).is_ok(),
        "well-formed hcomp type-checks"
    );

    let cert = hcomp_cert(&tc, &phi, &u, &base);
    let mut v = CertVerifier::with_mode(&env, CleanMode::Cubical);
    assert!(
        v.verify(&cert, &good).is_ok(),
        "cert verifier must accept the cap-coherent hcomp (no over-rejection)"
    );
}

/// Exercise the verifier's binder-context mirroring directly via
/// `validate_hcomp_for_cert` — this is the path the actual `Path Nat 0 1` exploit
/// (`<j> hcomp [(j=1)↦λ_.succ zero] zero`) takes, where the interval variable is a
/// loose `BVar(0)` relative to a one-binder context. A cap-incoherent body must be
/// rejected; the cap-coherent body must be accepted (face-restriction opens the
/// `BVar` to an `FVar` so it is not conservatively over-rejected).
#[test]
fn test_validate_hcomp_for_cert_opens_binders() {
    let env = nat_cubical_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // Under one interval binder `j = BVar(0)`: face (j=1), tube λ_. succ zero.
    let phi = face_eq1(Expr::bvar(0));
    let u = const_tube(succ(zero()));
    let ctx = [interval()];

    // Cap-incoherent (floor zero, cap succ zero) — REJECT.
    assert!(
        tc.validate_hcomp_for_cert(&ctx, &phi, &u, &zero(), &nat())
            .is_err(),
        "under-binder floor-disagreeing hcomp (the Path Nat 0 1 shape) must be rejected"
    );

    // Cap-coherent (floor succ zero == cap) — ACCEPT (not over-rejected).
    assert!(
        tc.validate_hcomp_for_cert(&ctx, &phi, &u, &succ(zero()), &nat())
            .is_ok(),
        "under-binder cap-coherent hcomp must be accepted (binder opened for face restriction)"
    );
}
