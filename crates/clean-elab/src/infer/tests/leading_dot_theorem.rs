// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Leading-dot and qualified resolution of non-constructor `Eq` members
//! (wf_b32d320a): `.symm` widens from the inductive's constructor list to the
//! accessible namespace constant, and `Eq.symm` on a type-former base resolves
//! as a qualified chain instead of elaborating the type constant as a
//! dot-notation receiver.
//!
//! The `.rfl` / `Eq.rfl` arms are NEGATIVE. Lean 4 has no `Eq.rfl` constant —
//! measured on both toolchains installed here, `v4.8.0` and `v4.30.0-rc2`:
//!
//! ```text
//! example : (1:Nat) = 1 := Eq.rfl   -- Unknown constant `Eq.rfl`
//! example : (1:Nat) = 1 := .rfl     -- Unknown constant `Eq.rfl`
//!                                   --   (inferred from expected type `1 = 1`)
//! ```
//!
//! Upstream's reflexivity carriers are the root `rfl` def and `HEq.rfl`; the
//! only reflexivity *theorem* in core is `Iff.rfl`, whose head is `Iff`. So the
//! Lean-faithful verdict for `.rfl` / `Eq.rfl` under an expected `Eq` type is an
//! ERROR, exactly as for the bare `.refl` arm at the bottom of this file. The
//! kernel-side pin lives in `clean-kernel`'s `env::tests_eq_rfl_fidelity`.

use super::*;

/// `@Eq.{1} Nat 1 1` — the expected type driving the leading-dot probes.
fn eq_nat_one_one() -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    Expr::app(
        Expr::app(Expr::app(eq, nat), Expr::nat_lit(1)),
        Expr::nat_lit(1),
    )
}

#[test]
fn test_leading_dot_symm_widens_past_constructor_list() {
    // The widening under test: `symm` names no CONSTRUCTOR of `Eq`, so the
    // resolver must fall through to the accessible namespace constant
    // `Eq.symm`. Lean accepts `.symm h` under an expected `Eq` type (measured
    // green on v4.8.0 and v4.30.0-rc2), so this arm is a genuine positive.
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let expected = eq_nat_one_one();
    let resolved = ctx
        .elab_leading_dot_ctor_with_expected_type(".symm", &expected)
        .expect("`.symm` should widen past Eq's constructor list to Eq.symm");
    assert!(
        matches!(
            resolved.get_app_fn().kind(),
            ExprKind::Const(name, _) if *name == Name::from_string("Eq.symm")
        ),
        "expected an Eq.symm application head, got {resolved:?}"
    );
}

#[test]
fn test_leading_dot_rfl_stays_unknown_because_lean_has_no_eq_rfl() {
    // NEGATIVE, and deliberately so. `Eq.rfl` is not a Lean 4 constant, so
    // `.rfl` under an expected `Eq` type must NOT resolve — Lean itself reports
    // "Unknown constant `Eq.rfl`" here (both toolchains; see the module header).
    // Accepting it would make Clean elaborate a program Lean rejects. The
    // widening is still exercised by the `.symm` arm above.
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let expected = eq_nat_one_one();
    let resolved = ctx.elab_leading_dot_ctor_with_expected_type(".rfl", &expected);
    assert!(
        matches!(resolved, Err(ElabError::UnknownIdent(_))),
        "`.rfl` under an expected `Eq` type must stay UnknownIdent (Lean has no \
         `Eq.rfl`), got {resolved:?}"
    );
}

#[test]
fn test_leading_dot_unknown_member_stays_fail_closed() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let expected = eq_nat_one_one();
    let resolved = ctx.elab_leading_dot_ctor_with_expected_type(".zzzNoSuchMember", &expected);
    assert!(
        matches!(resolved, Err(ElabError::UnknownIdent(_))),
        "a suffix that is neither constructor nor namespace constant must stay UnknownIdent, got {resolved:?}"
    );
}

#[test]
fn test_probe_dot_rfl_full_decl_errs_like_lean() {
    // `lean probe.lean` on v4.8.0 AND v4.30.0-rc2:
    //   example : (1:Nat) = 1 := .rfl
    //   error: Unknown constant `Eq.rfl` (inferred from expected type `1 = 1`)
    // The Lean-faithful verdict is REJECT. Writing `rfl` is the accepted form.
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab("example : 1 = 1 := .rfl").unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_err(),
        "`example : 1 = 1 := .rfl` must err — Lean has no `Eq.rfl`, got {result:?}"
    );
}

#[test]
fn test_bare_rfl_full_decl_is_the_accepted_form() {
    // The control for the two negatives: the root-level `rfl` definition Lean
    // DOES have (`Init/Prelude.lean:351`) elaborates green in both.
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab("example : 1 = 1 := rfl").unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "`example : 1 = 1 := rfl` must stay green, got {result:?}"
    );
}

#[test]
fn test_probe_dot_symm_full_decl() {
    // scratchpad probe_dot_symm_t.lean — the leading-dot application-head form.
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab("example (h : 1 = 2) : 2 = 1 := .symm h").unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "`.symm h` should widen to Eq.symm under the expected Eq type, got {result:?}"
    );
}

#[test]
fn test_qualified_eq_rfl_full_decl_errs_like_lean() {
    // Same measurement, qualified form: `example : (1:Nat) = 1 := Eq.rfl` is
    // "Unknown constant `Eq.rfl`" on v4.30.0-rc2 (and "unknown constant" /
    // field-notation error on v4.8.0). The type-former short-circuit under test
    // in `test_qualified_eq_symm_full_decl` is what makes this a clean
    // name-resolution failure instead of the opaque projection error.
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab("example : 1 = 1 := Eq.rfl").unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_err(),
        "`Eq.rfl` must err — Lean has no such constant, got {result:?}"
    );
}

#[test]
fn test_qualified_eq_symm_full_decl() {
    // scratchpad probe_dot_symm_t.lean line 1.
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab("example (h : 1 = 2) : 2 = 1 := Eq.symm h").unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "`Eq.symm h` should resolve as a qualified constant applied to h, got {result:?}"
    );
}

#[test]
fn test_regression_leading_dot_ctor_forms_stay_green() {
    // scratchpad probe_dot_refl_t.lean — genuine constructor forms must keep
    // the constructor path (the widening only engages when the find fails).
    let mut env = Environment::with_prelude();
    for src in [
        "example : 1 = 1 := .refl 1",
        "def bTrueLeadingDot : Bool := .true",
    ] {
        let decl = parse_decl_for_elab(src).unwrap();
        let result = crate::elaborate_decl_and_register(&mut env, &decl);
        assert!(result.is_ok(), "`{src}` must stay green, got {result:?}");
    }
}

#[test]
fn test_bare_dot_refl_without_its_explicit_arg_still_errs() {
    // `Eq.refl (a : α)` takes its subject EXPLICITLY, so bare `.refl` is a
    // function `(x : ?α) → x = x`, not a proof of `1 = 1` — Lean rejects it
    // too. The widening must not accidentally accept it (e.g. by resolving
    // to some other `.refl`-suffixed constant); the kernel-level rejection
    // is the correct, Lean-faithful outcome.
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab("example : 1 = 1 := .refl").unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_err(),
        "bare `.refl` must err (explicit arg missing), got {result:?}"
    );
}

#[test]
fn test_regression_value_receiver_keeps_projection_path() {
    // A VALUE base (`p : Pair`) is not a type former: `p.1` keeps the
    // structure-projection path even with the type-former short-circuit in
    // place (guarded by `lookup_local` + the Sort check).
    let env = pair_env();
    let expr = elab_with_env(&env, "fun (p : Pair) => p.1").expect("p.1 should project");
    assert!(
        matches!(expr.kind(), ExprKind::Lam(_, _, body) if matches!(body.kind(), ExprKind::Proj(..))),
        "expected a lambda over a projection, got {expr:?}"
    );
}
