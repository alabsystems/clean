// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression coverage for instance-resolution candidate hygiene — the
//! `.olean`-import "`Decidable.isFalse` picked as an instance" metavariable
//! leak that blocked the trust-ir Lean↔Clean bridge (guarded `semIntBinOp`
//! arms: `if rhs ≥ Int.ofNat width then …`).
//!
//! ## Root cause
//!
//! The `.olean` import's instance-bridging heuristic registered lean-core's
//! `Decidable.isFalse {p : Prop} (h : ¬p) : Decidable p` — a CONSTRUCTOR — as
//! a typeclass instance (`ConstantKind` cannot represent constructors, so its
//! imported `ConstantInfo` mirror defaults to `Definition` and passed the kind
//! filter; and its `¬p` binder is `Not`-headed, so it passed
//! `valid_instance_class`'s Const-headed exemption). During resolution the
//! candidate's conclusion `Decidable ?p` unified with EVERY `Decidable _`
//! goal, while the `h : ¬p` hypothesis binder — neither inferable from the
//! conclusion nor synthesizable (`Not` is not a class) — was left as a fresh,
//! forever-unassigned metavariable. `resolve_instance` returned the term
//! anyway, and the meta (encoded as a tagged FVar) leaked into the elaborated
//! declaration, surfacing far from the cause as the kernel's fail-closed
//! "Declaration contains free variables" rejection (or as
//! `TypeMismatch { expected: "valid type", actual: "UnknownFVar(…)" }` during
//! type inference).
//!
//! ## Fix (two tiers)
//!
//! 1. `resolve_instance` (elab, the failure-class killer): a candidate whose
//!    binder metavariables end the search undetermined — not assigned and not
//!    unified into the goal — is REJECTED and the search continues, mirroring
//!    Lean's `synthInstance` behavior of failing candidates with unassigned
//!    mvars. Weakening-only for accepts: any candidate rejected this way could
//!    only have produced a kernel-rejected term.
//! 2. `.olean` import (clean-olean): constructors / recursors / inductives are
//!    excluded from the class-typed-definition instance heuristic via the
//!    authoritative per-kind registries.
//!
//! These tests pin tier 1 natively (no `.olean` fixtures needed) by
//! registering `Decidable.isFalse` itself into the instance table at maximum
//! priority — byte-for-byte the candidate the import used to produce.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::env::KernelInstanceInfo;
use clean_kernel::{Environment, Expr, Name};
use clean_parser::parse_file;

/// Elaborate `code` (a single declaration) and return the trust warning.
/// Panics with `label` context if parsing or elaboration fails.
fn elaborate_one(
    env: &mut Environment,
    code: &str,
    label: &str,
) -> Option<crate::RegistrationWarning> {
    let decls = parse_file(code).unwrap_or_else(|e| panic!("{label}: parse failed: {e:?}"));
    assert_eq!(decls.len(), 1, "{label}: expected exactly one declaration");
    let registered = elaborate_decl_and_register_with_warning(env, &decls[0])
        .unwrap_or_else(|e| panic!("{label}: should elaborate and kernel-check, got: {e:?}"));
    registered.warning
}

/// Register the constructor `Decidable.isFalse` as a MAXIMUM-priority
/// `Decidable` instance — exactly the entry the `.olean` import's
/// class-typed-definition heuristic used to create — so that resolution tries
/// it before every genuine instance.
fn register_is_false_as_instance(env: &mut Environment) {
    let is_false = Name::from_string("Decidable.isFalse");
    let ctor = env
        .get_const(&is_false)
        .expect("prelude should have the Decidable.isFalse constructor")
        .clone();
    env.register_instance(KernelInstanceInfo {
        name: is_false.clone(),
        class_name: Name::from_string("Decidable"),
        priority: u32::MAX,
        type_: Some(ctor.type_),
        value: Some(Expr::const_(is_false, vec![])),
    });
}

/// The trust-ir guard shape: a propositional-`Decidable` `ite` under binders.
/// Resolution must SKIP the max-priority `Decidable.isFalse` candidate (its
/// `h : ¬p` hypothesis meta ends the search undetermined) and find the genuine
/// ordering instance — no fvar leak, no synthetic-sorry fallback.
#[test]
fn test_prop_ite_skips_undetermined_hypothesis_candidate() {
    let mut env = Environment::with_prelude();
    register_is_false_as_instance(&mut env);

    let warning = elaborate_one(
        &mut env,
        "def guarded (width : Nat) (rhs : Int) : Int :=\n\
         \u{20}\u{20}if rhs \u{2265} Int.ofNat width then 0 else 1",
        "guarded",
    );
    assert!(
        warning.is_none(),
        "resolution must find the genuine Decidable instance, not fall back \
         to synthetic sorry; got warning: {warning:?}"
    );
}

/// Fail-closed floor: when the hypothesis-taking candidate is the ONLY
/// candidate for the goal (an undecidable atomic `Prop`), resolution must
/// reject it with a typed synthesis error. It must neither register the
/// declaration nor substitute a synthetic sorry for an unproved branch.
#[test]
fn test_prop_ite_undetermined_candidate_fails_closed_with_typed_error() {
    let mut env = Environment::with_prelude();
    register_is_false_as_instance(&mut env);

    elaborate_one(
        &mut env,
        "axiom myUndecidableProp : Prop",
        "myUndecidableProp",
    );
    let decls = parse_file("def usesBogus : Nat := if myUndecidableProp then 0 else 1")
        .expect("usesBogus should parse");
    assert_eq!(decls.len(), 1, "expected exactly one usesBogus declaration");
    let error = match elaborate_decl_and_register_with_warning(&mut env, &decls[0]) {
        Ok(_) => panic!("an atomic proposition without Decidable must not elaborate"),
        Err(error) => error,
    };
    assert!(
        matches!(
            error,
            crate::ElabError::FailedToSynthesize { ref class_name, .. }
                if class_name == &Name::from_string("Decidable")
        ),
        "expected a typed Decidable synthesis error, got {error:?}"
    );
    assert!(
        env.get_const(&Name::from_string("usesBogus")).is_none(),
        "a declaration whose required instance is missing must not be registered"
    );
}
