// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The patched-kernel control at `clean-kernel`'s own entry points (unit P3
//! of `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`).
//!
//! Every site below is handed the planted pair `Nat.zero : False`. On the
//! kernel in this tree each must refuse it, by name. Under the mutant that
//! `scripts/patched_kernel_control.py` builds in a scratch copy, the pins say
//! which sites mint an acceptance on the kernel's word alone (the gaps the
//! authority flip closes) and which are stopped, and by whom. See
//! `support/patched_kernel_control.rs` for the two-leg contract.
//!
//! `reference.check_closed_term` and `reference.add_checked` are the calls
//! Trust's `trust-certify` makes before it registers a `ReferenceCertificate`,
//! and `kernel.audit_certification` is the audit it runs first. Trust's own
//! build is not exercised here: the record lists it as not exercised.
//!
//! `elab.module_driver.*` hand the pair to `clean check`'s per-declaration
//! loop as SOURCE (`clean_elab::module_driver::elaborate_decls` with the Lean
//! front door on, as `clean check` runs it, on the builtin prelude):
//! `theorem p3_planted_src : False := Nat.zero`, which the elaborator's
//! `is_def_eq` gate refuses before the kernel is asked, and the same pair
//! inside a term-level `let rec` (`theorem p3_letrec_src : False := let rec
//! go : False := Nat.zero; go`), whose lifted helper `p3_letrec_src.go :
//! False := Nat.zero` reaches `add_decl`, and so `check_type`, with no
//! elaborator check of its annotated value. The honest `let rec` source is
//! the non-vacuity control.

#[path = "support/patched_kernel_control.rs"]
mod control;
#[path = "support/p3_module_driver.rs"]
mod module_driver;

use clean_ck0::{
    add_inductive, Budget, Constructor, InductiveDecl, InferError, MinimalEnv, RawExpr, RawLevel,
    Term,
};
use clean_kernel::env::proof_search::try_verify_proof;
use clean_kernel::{
    CertificationIssue, DeclarationVerification, EnvError, Environment, Expr, Name,
    ReferenceKernel, ReferenceRefusal, TheoryId, TypeChecker, TypeError,
};
use control::{by, Observed, Outcome, Pin};

const PACKAGE: &str = "clean-kernel";

const TYPE_MISMATCH: &str = "TypeError::TypeMismatch";
const DECL_MISMATCH: &str = "EnvError::TypeCheckFailed(TypeError::TypeMismatch)";
const REFERENCE_MISMATCH: &str =
    "ReferenceRefusal::Kernel(EnvError::TypeCheckFailed(TypeError::TypeMismatch))";
const REFERENCE_TOKEN: &str = "ReferenceAccepted in TheoryId::LeanReferenceV1";

const PINS: &[Pin] = &[
    Pin {
        site: "kernel.check_type",
        mints: "Ok(()) from TypeChecker::check_type, the comparison every declaration check ends in",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, TYPE_MISMATCH),
        mutant: Outcome::minted("Ok(())"),
    },
    Pin {
        site: "kernel.add_decl",
        mints: "a resident theorem stamped DeclarationVerification::FullKernelCheck by Environment::add_decl",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, DECL_MISMATCH),
        mutant: Outcome::minted("resident, DeclarationVerification::FullKernelCheck"),
    },
    Pin {
        site: "kernel.check_decl_readonly_strict",
        mints: "Ok(()) from Environment::check_decl_readonly_strict, the read-only form of add_decl",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, DECL_MISMATCH),
        mutant: Outcome::minted("Ok(())"),
    },
    Pin {
        site: "kernel.audit_certification",
        mints: "a CertificationAudit with no issue, the audit Trust's ensures-discharge lane and clean-auto's certify_kernel_term require",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, "CertificationIssue::TermRejected"),
        mutant: Outcome::minted("CertificationAudit::is_certified"),
    },
    Pin {
        site: "reference.check_closed_term",
        mints: "a ReferenceAccepted token for a closed pair from the fenced entry, the call behind Trust's Certified rows",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, REFERENCE_MISMATCH),
        mutant: Outcome::minted(REFERENCE_TOKEN),
    },
    Pin {
        site: "reference.add_checked",
        mints: "a ReferenceAccepted token and a resident declaration from the fenced entry",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, REFERENCE_MISMATCH),
        mutant: Outcome::minted(REFERENCE_TOKEN),
    },
    Pin {
        site: "kernel.try_verify_proof",
        mints: "true from proof search's candidate check, which compares with is_def_eq and never calls check_type",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, "false"),
        mutant: Outcome::refused(by::SAME_KERNEL_OTHER_ENTRY, "false"),
    },
    Pin {
        site: "ck0.check",
        mints: "Ok(()) from clean_ck0::check, the independent member of the quorum (no clean-kernel code)",
        unmodified: Outcome::refused(by::CLEAN_CK0, "InferError::TypeMismatch"),
        mutant: Outcome::refused(by::CLEAN_CK0, "InferError::TypeMismatch"),
    },
    Pin {
        site: "elab.module_driver.source",
        mints: "a Passed verdict and a resident theorem from clean check's per-declaration loop on the planted source",
        unmodified: Outcome::refused(by::SAME_KERNEL_OTHER_ENTRY, module_driver::PLANTED_SOURCE_REFUSAL),
        mutant: Outcome::refused(by::SAME_KERNEL_OTHER_ENTRY, module_driver::PLANTED_SOURCE_REFUSAL),
    },
    Pin {
        site: "elab.module_driver.let_rec_source",
        mints: "a Passed verdict and the resident theorem and helper from clean check's per-declaration loop on the planted pair inside a let rec",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, module_driver::LET_REC_REFUSAL),
        mutant: Outcome::minted(module_driver::LET_REC_RESIDENT),
    },
];

fn probe_check_type(env: &Environment) -> Observed {
    const SITE: &str = "kernel.check_type";
    let checker = TypeChecker::new(env);
    checker
        .check_type(&Expr::const_str("True.intro"), &Expr::const_str("True"))
        .expect("honest pair accepted by check_type");
    match checker.check_type(&control::planted_value(), &control::planted_type()) {
        Ok(()) => Observed::minted(SITE, "Ok(())"),
        Err(TypeError::TypeMismatch { .. }) => {
            Observed::refused(SITE, by::CLEAN_KERNEL, TYPE_MISMATCH)
        }
        Err(other) => panic!("{SITE}: unexpected refusal {other:?}"),
    }
}

fn probe_add_decl(env: &Environment) -> Observed {
    const SITE: &str = "kernel.add_decl";
    let mut env = env.clone();
    env.add_decl(control::honest_theorem("p3_honest"))
        .expect("honest theorem admitted by add_decl");
    let name = Name::from_string("p3_planted");
    match env.add_decl(control::planted_theorem("p3_planted")) {
        Ok(()) => {
            let stamp = env.declaration_verification(&name);
            assert_eq!(
                stamp,
                Some(DeclarationVerification::FullKernelCheck),
                "{SITE}: an admitted theorem must carry the full-check stamp"
            );
            assert!(
                env.get_const(&name).is_some(),
                "{SITE}: an admitted theorem must be resident"
            );
            Observed::minted(SITE, "resident, DeclarationVerification::FullKernelCheck")
        }
        Err(EnvError::TypeCheckFailed {
            source: TypeError::TypeMismatch { .. },
            ..
        }) => {
            assert!(
                env.get_const(&name).is_none(),
                "{SITE}: a refused theorem must not be resident"
            );
            Observed::refused(SITE, by::CLEAN_KERNEL, DECL_MISMATCH)
        }
        Err(other) => panic!("{SITE}: unexpected refusal {other:?}"),
    }
}

fn probe_check_decl_readonly_strict(env: &Environment) -> Observed {
    const SITE: &str = "kernel.check_decl_readonly_strict";
    env.check_decl_readonly_strict(&control::honest_theorem("p3_honest"))
        .expect("honest theorem accepted by the read-only check");
    match env.check_decl_readonly_strict(&control::planted_theorem("p3_planted")) {
        Ok(()) => Observed::minted(SITE, "Ok(())"),
        Err(EnvError::TypeCheckFailed {
            source: TypeError::TypeMismatch { .. },
            ..
        }) => Observed::refused(SITE, by::CLEAN_KERNEL, DECL_MISMATCH),
        Err(other) => panic!("{SITE}: unexpected refusal {other:?}"),
    }
}

fn probe_audit_certification(env: &Environment) -> Observed {
    const SITE: &str = "kernel.audit_certification";
    let honest = env.audit_certification(&Expr::const_str("True"), &Expr::const_str("True.intro"));
    assert!(
        honest.is_certified(),
        "{SITE}: the honest pair must audit clean, got {:?}",
        honest.issues
    );
    let audit = env.audit_certification(&control::planted_type(), &control::planted_value());
    match audit.issues.as_slice() {
        [] => Observed::minted(SITE, "CertificationAudit::is_certified"),
        [CertificationIssue::TermRejected { .. }] => {
            Observed::refused(SITE, by::CLEAN_KERNEL, "CertificationIssue::TermRejected")
        }
        other => panic!("{SITE}: unexpected audit issues {other:?}"),
    }
}

fn reference_outcome(
    site: &'static str,
    result: Result<clean_kernel::ReferenceAccepted, ReferenceRefusal>,
) -> Observed {
    match result {
        Ok(token) => {
            assert_eq!(
                token.theory_id(),
                TheoryId::LeanReferenceV1,
                "{site}: the token names another theory"
            );
            Observed::minted(site, REFERENCE_TOKEN)
        }
        Err(ReferenceRefusal::Kernel(EnvError::TypeCheckFailed {
            source: TypeError::TypeMismatch { .. },
            ..
        })) => Observed::refused(site, by::CLEAN_KERNEL, REFERENCE_MISMATCH),
        Err(other) => panic!("{site}: unexpected refusal {other:?}"),
    }
}

/// Both fenced-entry sites, on one entry: its base walk is the slow part.
fn probe_reference_entry(env: &Environment) -> [Observed; 2] {
    let mut entry =
        ReferenceKernel::new(env.clone()).expect("prelude passes the reference base walk");
    entry
        .check_closed_term(&Expr::const_str("True"), &Expr::const_str("True.intro"))
        .expect("honest closed proof accepted through the fenced entry");
    let closed = reference_outcome(
        "reference.check_closed_term",
        entry.check_closed_term(&control::planted_type(), &control::planted_value()),
    );
    entry
        .add_checked(control::honest_theorem("p3_honest"))
        .expect("honest theorem admitted through the fenced entry");
    let before = entry.env_digest();
    let added = reference_outcome(
        "reference.add_checked",
        entry.add_checked(control::planted_theorem("p3_planted")),
    );
    let resident = entry
        .environment()
        .get_const(&Name::from_string("p3_planted"))
        .is_some();
    match added.verdict {
        control::Verdict::Minted => {
            assert!(
                resident,
                "reference.add_checked: an accepted declaration must be resident"
            );
            assert_ne!(
                entry.env_digest(),
                before,
                "reference.add_checked: an acceptance must move the digest"
            );
        }
        control::Verdict::Refused => {
            assert!(
                !resident,
                "reference.add_checked: a refused declaration must not be resident"
            );
            assert_eq!(
                entry.env_digest(),
                before,
                "reference.add_checked: a refusal must not move the digest"
            );
        }
    }
    [closed, added]
}

fn probe_try_verify_proof(env: &Environment, mutation_live: bool) -> Observed {
    const SITE: &str = "kernel.try_verify_proof";
    assert!(
        try_verify_proof(
            env,
            &Expr::const_str("True"),
            &Expr::const_str("True.intro")
        ),
        "{SITE}: the honest candidate must verify"
    );
    if try_verify_proof(env, &control::planted_type(), &control::planted_value()) {
        return Observed::minted(SITE, "true");
    }
    // The refusal is `is_def_eq`'s. With the mutant linked it is the same
    // kernel answering through an entry the mutation does not touch.
    let decided_by = if mutation_live {
        by::SAME_KERNEL_OTHER_ENTRY
    } else {
        by::CLEAN_KERNEL
    };
    Observed::refused(SITE, decided_by, "false")
}

fn ck0_name(dotted: &str) -> clean_ck0::Name {
    clean_ck0::Name::from_dotted(dotted)
}

fn ck0_const(dotted: &str) -> RawExpr {
    RawExpr::Const(ck0_name(dotted), vec![])
}

fn ck0_term(env: &MinimalEnv, raw: &RawExpr) -> Term {
    Term::validate(env, raw, 0, 0).expect("ck0 term validates")
}

/// A `clean-ck0` environment holding `Nat`, `False` and `True`, admitted by
/// ck0's own inductive checker. No `clean-kernel` value crosses into it.
fn ck0_base() -> MinimalEnv {
    let prop = RawExpr::Sort(RawLevel::Zero);
    let type_1 = RawExpr::Sort(RawLevel::Succ(Box::new(RawLevel::Zero)));
    let mut env = MinimalEnv::new();

    let names = MinimalEnv::new()
        .with_const(ck0_name("Nat"), 0)
        .with_const(ck0_name("Nat.zero"), 0)
        .with_const(ck0_name("Nat.succ"), 0);
    let succ_type = RawExpr::Pi(
        clean_ck0::rawexpr::BinderInfo::Default,
        Box::new(ck0_const("Nat")),
        Box::new(ck0_const("Nat")),
    );
    let nat = InductiveDecl {
        name: ck0_name("Nat"),
        num_level_params: 0,
        num_params: 0,
        type_: ck0_term(&names, &type_1),
        constructors: vec![
            Constructor {
                name: ck0_name("Nat.zero"),
                type_: ck0_term(&names, &ck0_const("Nat")),
            },
            Constructor {
                name: ck0_name("Nat.succ"),
                type_: ck0_term(&names, &succ_type),
            },
        ],
    };
    add_inductive(&mut env, nat).expect("ck0 admits Nat");

    let names = MinimalEnv::new().with_const(ck0_name("False"), 0);
    let false_ = InductiveDecl {
        name: ck0_name("False"),
        num_level_params: 0,
        num_params: 0,
        type_: ck0_term(&names, &prop),
        constructors: vec![],
    };
    add_inductive(&mut env, false_).expect("ck0 admits False");

    let names = MinimalEnv::new()
        .with_const(ck0_name("True"), 0)
        .with_const(ck0_name("True.intro"), 0);
    let true_ = InductiveDecl {
        name: ck0_name("True"),
        num_level_params: 0,
        num_params: 0,
        type_: ck0_term(&names, &prop),
        constructors: vec![Constructor {
            name: ck0_name("True.intro"),
            type_: ck0_term(&names, &ck0_const("True")),
        }],
    };
    add_inductive(&mut env, true_).expect("ck0 admits True");
    env
}

fn probe_ck0() -> Observed {
    const SITE: &str = "ck0.check";
    let env = ck0_base();
    let mut budget = Budget::default_budget();
    let honest =
        Term::validate_closed(&env, &ck0_const("True.intro")).expect("True.intro validates in ck0");
    let true_ = Term::validate_closed(&env, &ck0_const("True")).expect("True validates in ck0");
    clean_ck0::check(&env, &honest, &true_, &mut budget).expect("ck0 accepts the honest pair");
    let planted =
        Term::validate_closed(&env, &ck0_const("Nat.zero")).expect("Nat.zero validates in ck0");
    let false_ = Term::validate_closed(&env, &ck0_const("False")).expect("False validates in ck0");
    match clean_ck0::check(&env, &planted, &false_, &mut budget) {
        Ok(()) => Observed::minted(SITE, "Ok(())"),
        Err(InferError::TypeMismatch) => {
            Observed::refused(SITE, by::CLEAN_CK0, "InferError::TypeMismatch")
        }
        Err(other) => panic!("{SITE}: unexpected refusal {other:?}"),
    }
}

#[test]
fn patched_kernel_control() {
    let env = Environment::with_prelude();
    let mutation_live = control::linked_kernel_accepts_planted_pair();
    let [closed, added] = probe_reference_entry(&env);
    let observed = [
        probe_check_type(&env),
        probe_add_decl(&env),
        probe_check_decl_readonly_strict(&env),
        probe_audit_certification(&env),
        closed,
        added,
        probe_try_verify_proof(&env, mutation_live),
        probe_ck0(),
        module_driver::probe_module_driver_source(),
        module_driver::probe_module_driver_let_rec(),
    ];
    control::judge(PACKAGE, PINS, &observed);
}

#[test]
fn committed_record_matches_the_pins() {
    control::assert_record_matches_pins(PACKAGE, PINS);
}
