// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Brick B4 of `designs/2026-10-08-mutual-nested-recursion.md`, ledger class
//! (88): an equation-form declaration whose trailing columns are hypotheses
//! typed by a matched column (`| .node ts, h => …` with `h : ok t = true`).
//! Lean's motive covers every column, so `h` is about each alternative's
//! constructor; Clean generalizes those columns into the case split's result
//! type on the single-declaration path (`infer/equation_dep_columns.rs`) and
//! on the generic pass-2 path a `mutual` block takes
//! (`infer/elab_pattern_lambda_dep.rs`).
//!
//! Fixtures and verdicts as in `mutual_lift.rs` (`tests/fixtures/mutual_nested/`,
//! `verdicts.json` re-derived from the pinned Lean binaries by
//! `scripts/mutual_nested_verdicts.py`), each with a Lean-refused twin.

use super::mutual_lift_tests::{accepts_all, fixture, fresh, lean_accepts, refuses_last};

/// The single-declaration path: one matched column (`one_dep`), a leading
/// parameter (`lead_param`), and two matched columns with `n + 1` patterns
/// (`both_zero`, the matrix compiler's numeral expansion).
#[test]
fn test_dependent_hypothesis_column_single_declaration_class_88() {
    let f = fixture!("dep_column_single.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
}

#[test]
fn test_dependent_hypothesis_column_is_about_the_constructor_class_88() {
    let f = fixture!("dep_column_single_twin.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    let err = refuses_last(&mut env, f, "one_dep_twin");
    assert!(
        err.contains("isZ"),
        "the refusal is `h : isZ (n + 1) = true` against `n + 1 = 0`: {err}"
    );
}

/// Two matched columns: `h : both (k + 1) 0 = true` is not `k + 1 = 0`.
#[test]
fn test_dependent_hypothesis_column_two_matched_columns_twin_class_88() {
    let f = fixture!("dep_column_two_twin.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    let err = refuses_last(&mut env, f, "both_zero_twin");
    assert!(err.contains("both"), "the refusal is `h`'s type: {err}");
}

/// G69: the filed equation theorem now reaches the hidden-forward SCC lift.
/// The nondecreasing and recursive-call signature twins below must be refused.
#[test]
fn test_self_call_inside_by_registers_g69() {
    let f = fixture!("self_call_in_by.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
}

#[test]
fn test_single_theorem_predef_tactic_self_call_registers() {
    let mut env = fresh();
    accepts_all(&mut env, fixture!("self_call_in_by.lean"));
    accepts_all(
        &mut env,
        (
            "single_by_axioms",
            "/-- info: 'single_by' does not depend on any axioms -/\n#guard_msgs in\n#print axioms single_by\n",
        ),
    );
}

#[test]
fn test_single_theorem_predef_cases_tactic_recursion_registers() {
    let mut env = fresh();
    accepts_all(
        &mut env,
        (
            "single_by_cases",
            "theorem byCases (n : Nat) : n + 0 = n := by\n  cases n with\n  | zero => rfl\n  | succ k => exact congrArg Nat.succ (byCases k)\n",
        ),
    );
}

#[test]
fn test_single_theorem_predef_captures_autos_from_section_types() {
    let mut env = fresh();
    accepts_all(
        &mut env,
        (
            "section_type_autos",
            include_str!("../../../../../tests/fixtures/recursive_theorem/positive.lean"),
        ),
    );
}

#[test]
fn test_single_theorem_predef_keeps_captured_and_own_auto_arities_distinct() {
    for source in [
        include_str!(
            "../../../../../tests/fixtures/recursive_theorem/extra_section_auto_argument.lean"
        ),
        include_str!(
            "../../../../../tests/fixtures/recursive_theorem/missing_own_after_section_auto.lean"
        ),
    ] {
        let mut env = fresh();
        let results = super::mutual_lift_tests::run_file(&mut env, source);
        assert!(
            results.iter().any(Result::is_err),
            "the wrong auto-prefix must be refused"
        );
        assert!(!super::mutual_lift_tests::registered(&env, "bad"));
    }
}

#[test]
fn test_single_theorem_predef_keeps_implicit_universe_parameters() {
    let mut env = fresh();
    accepts_all(
        &mut env,
        (
            "single_universes",
            "universe u\ntheorem same {α : Sort u} (x : α) : ∀ n : Nat, x = x\n  | 0 => rfl\n  | n + 1 => by exact same x n\ntheorem propUse : True.intro = True.intro := same True.intro 2\ntheorem natUse : (3 : Nat) = 3 := same 3 2\n",
        ),
    );
}

#[test]
fn test_single_theorem_predef_generalizes_header_auto_implicits() {
    let mut env = fresh();
    accepts_all(
        &mut env,
        (
            "single_auto_implicit",
            "theorem autoSame (x : α) : ∀ n : Nat, x = x\n  | 0 => rfl\n  | n + 1 => by exact autoSame x n\ntheorem autoNatUse : (3 : Nat) = 3 := autoSame 3 2\n",
        ),
    );
}

#[test]
fn test_single_theorem_predef_keeps_section_pruning_offset() {
    let mut env = fresh();
    accepts_all(
        &mut env,
        (
            "single_section_offset",
            "section\nvariable (unused : Nat)\ntheorem sect (x : α) (h : (by exact True)) : ∀ n : Nat, x = x\n  | 0 => rfl\n  | n + 1 => by rfl\nend\ntheorem sectUse : (3 : Nat) = 3 := sect 3 True.intro 2\n",
        ),
    );
}

#[test]
fn test_single_theorem_predef_keeps_used_section_parameters() {
    let mut env = fresh();
    accepts_all(
        &mut env,
        (
            "single_section_used",
            "section\nvariable (p : Prop)\ntheorem keep (hp : p) : ∀ n : Nat, p\n  | 0 => hp\n  | n + 1 => by exact keep hp n\nend\ntheorem keepUse : True := keep True True.intro 2\n",
        ),
    );
}

#[test]
fn test_single_theorem_predef_rejects_an_extra_section_argument() {
    let mut env = fresh();
    let outcomes = super::mutual_lift_tests::run_file(
        &mut env,
        "section\nvariable (p : Prop)\ntheorem keep (hp : p) : ∀ n : Nat, p\n  | 0 => hp\n  | n + 1 => by exact keep p hp n\nend\n",
    );
    assert!(outcomes.iter().any(Result::is_err), "{outcomes:?}");
    assert!(!super::mutual_lift_tests::registered(&env, "keep"));
}

#[test]
fn test_single_theorem_predef_infers_untyped_header_binders() {
    for proof in ["by rfl", "by exact untyped x n"] {
        let mut env = fresh();
        let source = format!(
            "theorem untyped {{α}} (x : α) : ∀ n : Nat, x = x\n  | 0 => rfl\n  | n + 1 => {proof}\ntheorem useUntyped : (3 : Nat) = 3 := untyped 3 2\n",
        );
        accepts_all(&mut env, ("single_untyped", &source));
    }
}

#[test]
fn test_single_theorem_predef_preserves_bool_type_positions() {
    let mut env = fresh();
    accepts_all(
        &mut env,
        (
            "single_bool_header",
            "theorem boolHeader (b : Bool) (h : b) : ∀ n : Nat, b\n  | 0 => h\n  | n + 1 => by exact boolHeader b h n\n",
        ),
    );
}

#[test]
fn test_single_theorem_predef_keeps_header_local_helper_binders_separate() {
    for proof in ["h", "helperHeader h n"] {
        let mut env = fresh();
        let source = format!(
            "theorem helperHeader (h : (let rec pred (n : Nat) : Prop := True; pred 0)) : ∀ n : Nat, True\n  | 0 => h\n  | n + 1 => by exact {proof}\n",
        );
        accepts_all(&mut env, ("single_header_local_helper", &source));
    }
}

#[test]
fn test_single_theorem_predef_reuses_captures_of_header_local_helpers() {
    for proof in ["h", "capturedHeader x h n"] {
        let mut env = fresh();
        let source = format!(
            "universe u\ntheorem capturedHeader {{α : Sort u}} (x : α) (h : (let rec pred (n : Nat) : Prop := x = x; pred 0)) : ∀ n : Nat, x = x\n  | 0 => h\n  | n + 1 => by exact {proof}\n",
        );
        accepts_all(&mut env, ("single_captured_header_helper", &source));
    }
}

#[test]
fn test_single_theorem_predef_keeps_own_implicit_argument_under_section_capture() {
    for call in ["keepAuto x hp n", "@keepAuto α x hp n"] {
        let mut env = fresh();
        let source = format!(
            "section\nvariable (p : Prop)\ntheorem keepAuto (x : α) (hp : p) : ∀ n : Nat, x = x\n  | 0 => rfl\n  | n + 1 => by exact {call}\nend\ntheorem keepAutoUse : (3 : Nat) = 3 := keepAuto True 3 True.intro 2\n",
        );
        accepts_all(&mut env, ("single_section_auto_implicit", &source));
    }
}

#[test]
fn test_single_theorem_predef_refuses_an_omitted_explicit_implicit_argument() {
    let mut env = fresh();
    let outcomes = super::mutual_lift_tests::run_file(
        &mut env,
        "section\nvariable (p : Prop)\ntheorem keepAuto (x : α) (hp : p) : ∀ n : Nat, x = x\n  | 0 => rfl\n  | n + 1 => by exact @keepAuto x hp n\nend\n",
    );
    assert!(outcomes.iter().any(Result::is_err), "{outcomes:?}");
    assert!(!super::mutual_lift_tests::registered(&env, "keepAuto"));
}

#[test]
fn test_single_theorem_predef_failure_restores_the_same_elaborator() {
    let env = fresh();
    let mut ctx = crate::infer::ElabCtx::new(&env);
    let decls = clean_parser::parse_file(
        "theorem bad (x : α) : ∀ n : Nat, False\n  | 0 => by exact bad x 0\n  | n + 1 => by exact bad x n\ntheorem afterward : True := by exact True.intro\n",
    )
    .expect("fixtures parse");
    assert!(ctx.elab_decl(&decls[0]).is_err());
    assert!(ctx.locals.is_empty());
    assert!(ctx.auto_implicits.is_empty());
    assert!(ctx.auto_implicit_lookup.is_empty());
    assert!(ctx.aux_decl_locals.is_empty());
    assert!(ctx.single_theorem_capture.is_none());
    assert!(ctx.current_expected_type.is_none());
    let result = ctx
        .elab_decl(&decls[1])
        .expect("same context remains usable");
    assert!(matches!(result, crate::infer::ElabResult::Theorem { .. }));
}

#[test]
fn test_single_theorem_predef_failure_preserves_earlier_pending_entries() {
    let env = fresh();
    let mut ctx = crate::infer::ElabCtx::new(&env);
    let decls = clean_parser::parse_file(
        "theorem kept : ∀ n : Nat, n + 0 = n\n  | 0 => rfl\n  | n + 1 => by exact congrArg Nat.succ (kept n)\ntheorem rejected : ∀ n : Nat, n + 0 = n\n  | 0 => True.intro\n  | n + 1 => by exact congrArg Nat.succ (rejected n)\ntheorem afterward : True := by exact True.intro\n",
    )
    .expect("fixtures parse");
    ctx.elab_decl(&decls[0]).expect("first member elaborates");
    let lift_count = ctx.mutual_lift_entries.len();
    let equation_count = ctx.mutual_eq_lemmas.len();
    assert!(lift_count > 0, "first member has actual SCC metadata");
    let error = ctx
        .elab_decl(&decls[1])
        .expect_err("wrong proof is refused");
    assert!(
        error.to_string().to_lowercase().contains("mismatch"),
        "{error}"
    );
    assert_eq!(ctx.mutual_lift_entries.len(), lift_count);
    assert_eq!(ctx.mutual_eq_lemmas.len(), equation_count);
    ctx.elab_decl(&decls[2])
        .expect("same context remains usable");
    assert_eq!(ctx.mutual_lift_entries.len(), lift_count);
}

#[test]
fn test_single_theorem_predef_failure_does_not_register_a_forward_axiom() {
    let mut env = fresh();
    let outcomes = super::mutual_lift_tests::run_file(
        &mut env,
        "theorem bad : ∀ n : Nat, False\n  | 0 => by exact bad 0\n  | n + 1 => by exact bad n\ntheorem afterward : True := by exact True.intro\n",
    );
    assert_eq!(outcomes.len(), 2, "{outcomes:?}");
    assert!(outcomes[0].is_err(), "{outcomes:?}");
    assert!(outcomes[1].is_ok(), "{outcomes:?}");
    assert!(!super::mutual_lift_tests::registered(&env, "bad"));
    assert!(super::mutual_lift_tests::registered(&env, "afterward"));
}

#[test]
fn test_single_theorem_predef_refuses_non_decreasing_tactic_call() {
    let mut env = fresh();
    let err = refuses_last(
        &mut env,
        (
            "single_cycle",
            "theorem bad : ∀ n : Nat, False\n  | 0 => by exact bad 0\n  | n + 1 => by exact bad n\n",
        ),
        "bad",
    );
    assert!(
        err.contains("cannot be lowered") && err.contains("constructor field"),
        "{err}"
    );
}

#[test]
fn test_single_theorem_predef_retains_unsafe_theorem_refusal() {
    let mut env = fresh();
    let err = refuses_last(
        &mut env,
        (
            "unsafe_single",
            "unsafe theorem bad : ∀ n : Nat, n = n\n  | 0 => rfl\n  | n + 1 => by exact congrArg Nat.succ (bad n)\n",
        ),
        "bad",
    );
    assert!(err.contains("'unsafe' theorems are not allowed"), "{err}");
}

/// The pass-2 path of a `mutual` theorem block over a nested inductive
/// (trust-ir `substTy_total` / `substTys_total`, block 12).
#[test]
fn test_dependent_hypothesis_column_in_mutual_block_class_88() {
    let f = fixture!("dep_column_mutual.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
}

#[test]
fn test_dependent_hypothesis_column_in_mutual_block_false_claim_class_88() {
    let f = fixture!("dep_column_mutual_twin.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    refuses_last(&mut env, f, "sz_one");
}

/// The finite Nat alias pin was observed accepted by the normal 1d3 library.
/// Require its actual registered proof and independent public type; this does
/// not requalify the separate trust-ir list rows or the full class (88).
#[test]
fn test_dependent_column_first_column_alias_registers_and_kernel_checks_class_88() {
    use crate::{elaborate_decl_and_register, ElabResult};
    use clean_kernel::{BinderInfo, ConstantKind, Expr, Name, TypeChecker};
    use clean_parser::{parse_file_with_tactics, SurfaceDecl};

    let f = fixture!("dep_column_alias_pin.lean");
    assert!(lean_accepts(f.0));
    let declarations =
        parse_file_with_tactics(f.1, &crate::tactic::builtins::builtin_tactic_patterns())
            .expect("the exact native-positive fixture parses");
    assert_eq!(declarations.len(), 1);
    let SurfaceDecl::Theorem { name, .. } = &declarations[0] else {
        panic!("no recovery/non-theorem declaration may pass");
    };
    assert_eq!(name.name(), &Name::from_string("pin_alias"));
    let mut env = fresh();
    let result = elaborate_decl_and_register(&mut env, &declarations[0])
        .expect("the native-positive alias theorem must elaborate");
    let ElabResult::Theorem { name, .. } = result else {
        panic!("a failed/axiom/recovery leaf cannot count as a theorem");
    };
    assert_eq!(name, Name::from_string("pin_alias"));
    let info = env.get_const(&name).expect("the actual theorem registers");
    assert_eq!(info.kind, ConstantKind::Theorem);
    assert!(info.level_params.is_empty());
    let proof = info.value.as_ref().expect("the actual proof is stored");
    assert!(!proof.collect_constants().contains(&name));
    for expression in [&info.type_, proof] {
        assert!(
            !expression.has_fvar_quick()
                && !expression.has_loose_bvars_quick()
                && !expression.has_expr_mvar_quick()
                && !expression.has_level_mvar_quick()
                && !expression.has_level_param_quick(),
            "registered type and proof must be closed and fully instantiated"
        );
    }

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lt = |i, n| {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.lt"), vec![]),
            [Expr::bvar(i), Expr::bvar(n)],
        )
    };
    // Under n,i the hypothesis is i#0<n#1; under n,i,h the result is
    // i#1<n#2. No nondependent-arrow constructor silently shifts these.
    let hypothesis = lt(0, 1);
    let expected = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(BinderInfo::Default, hypothesis.clone(), lt(1, 2)),
        ),
    );
    let identity = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat,
            Expr::lam(BinderInfo::Default, hypothesis, Expr::bvar(0)),
        ),
    );
    let mut checker = TypeChecker::new(&env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    let type_kind = checker
        .infer_type_full(&expected)
        .expect("independently assembled forall type is well-formed");
    assert!(checker.is_def_eq(&type_kind, &Expr::prop()));
    let identity_type = checker
        .infer_type_full(&identity)
        .expect("independent lambda n i h => h is a checked witness");
    assert!(checker.is_def_eq(&identity_type, &expected));
    let proof_type = checker
        .infer_type_full(proof)
        .expect("strict full Kernel inference of the stored alias proof");
    assert!(checker.is_def_eq(&proof_type, &info.type_));
    assert!(checker.is_def_eq(&info.type_, &expected));
    assert!(!checker.heartbeat_spent());
    assert!(env
        .axiom_deps(&name)
        .expect("actual axiom closure")
        .is_empty());
}

#[test]
fn test_dependent_column_first_column_alias_swapped_annotation_is_refused_class_88() {
    use crate::{elaborate_decl_and_register, ElabError};
    use clean_kernel::Name;
    use clean_parser::{parse_file_with_tactics, SurfaceDecl};

    let positive = fixture!("dep_column_alias_pin.lean");
    let twin = fixture!("dep_column_alias_pin_twin.lean");
    assert!(!lean_accepts(twin.0));
    assert_eq!(
        twin.1,
        positive
            .1
            .replace("theorem pin_alias :", "theorem pin_alias_twin :")
            .replace("(h : i + 1 < n + 1)", "(h : n + 1 < i + 1)"),
        "only the root name and final proof annotation change"
    );
    let declarations =
        parse_file_with_tactics(twin.1, &crate::tactic::builtins::builtin_tactic_patterns())
            .expect("the exact native-refused fixture parses");
    assert_eq!(declarations.len(), 1);
    let SurfaceDecl::Theorem { name, .. } = &declarations[0] else {
        panic!("the refusal must be the actual theorem");
    };
    assert_eq!(name.name(), &Name::from_string("pin_alias_twin"));
    let mut env = fresh();
    let error = elaborate_decl_and_register(&mut env, &declarations[0])
        .expect_err("the swapped hypothesis annotation must be refused");
    let ElabError::TypeMismatch { expected, actual } = error.innermost() else {
        panic!("a parse/helper failure cannot count as the false twin: {error:?}");
    };
    let is_order_type = |text: &str| {
        text.contains("Nat.lt")
            || text.contains("Nat.le")
            || text.contains("LT.lt")
            || text.contains('<')
    };
    assert!(
        is_order_type(expected) && is_order_type(actual) && expected != actual,
        "the mismatch must compare the two order propositions: {error:?}"
    );
    assert!(env
        .get_const(&Name::from_string("pin_alias_twin"))
        .is_none());
}
