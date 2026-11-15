// Copyright 2026 Andrew Yates | Apache-2.0
//! Current-kernel regressions for dependent motives of packed discriminants.
//! Trust's original decide-or helper is kept literally in the fixture. Its
//! official Lean 4.8 predecessor is separate evidence, not a 4.30 oracle claim.
use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabError, ElabResult, FileContext,
    MetaState,
};
use clean_kernel::{
    env::{Declaration, Environment},
    EnvError, Expr, FVarId, Level, Name, TypeChecker,
};
use clean_parser::parse_file;

const DECIDE_OR: &str = include_str!("fixtures/multi_scrutinee_decidable_or.lean");

fn check_result(result: ElabResult) -> Result<(), ElabError> {
    match result {
        ElabResult::Multiple(rows) => {
            for row in rows {
                check_result(row)?;
            }
            Ok(())
        }
        ElabResult::Failed { error, .. } => Err(*error),
        _ => Ok(()),
    }
}

fn elaborate(source: &str) -> Result<Environment, ElabError> {
    let declarations = parse_file(source).expect("regression source must parse");
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    for declaration in declarations {
        let declaration = preprocess_decl_with_context(&declaration, &mut context);
        check_result(elaborate_decl_and_register(&mut env, &declaration)?)?;
    }
    Ok(env)
}

fn assert_checked(env: &Environment, name: &str) {
    let name = Name::from_string(name);
    let info = env.get_const(&name).expect("theorem registered");
    let proof = info.value.as_ref().expect("actual proof body");
    assert!(!proof.has_sorry(), "sorry is not a proof");
    assert!(!proof.has_fvar_quick(), "no free variables");
    assert!(!proof.has_loose_bvars_quick(), "closed proof");
    // Elaborator expression metas are tagged FVars, not the kernel's always-
    // false has_expr_mvar_quick flag (G46). Audit the actual representation.
    assert!(!MetaState::expr_has_meta(proof));
    assert!(!MetaState::expr_has_meta(&info.type_));
    // Universes are sealed as declared Level::Param entries by registration.
    // Recheck with exactly that declaration's universe context, so an
    // undeclared universe cannot be accepted as an implicit assumption.
    let mut checker = TypeChecker::new(env);
    checker.set_level_params(info.level_params.clone());
    checker
        .check_type(proof, &info.type_)
        .expect("full kernel recheck");
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    assert!(env.axiom_deps(&name).expect("domain closure").is_empty());
    assert!(env
        .foundational_axiom_deps(&name)
        .expect("foundational closure")
        .is_empty());
}

#[test]
fn multi_scrutinee_decidable_or() {
    let env =
        elaborate(DECIDE_OR).expect("the original universal four-arm proof must kernel-check");
    assert_checked(&env, "overflow_decide_or");
}

#[test]
fn three_discriminants_and_binder_capture() {
    let env = elaborate(
        r#"
theorem packedBoolAssoc (a b c : Bool) : (a || (b || c)) = ((a || b) || c) :=
  match a, b, c with
  | false, false, false => rfl
  | false, false, true => rfl
  | false, true, false => rfl
  | false, true, true => rfl
  | true, false, false => rfl
  | true, false, true => rfl
  | true, true, false => rfl
  | true, true, true => rfl

theorem packedUnderBinder (a b : Bool) : ∀ x : Bool, (a && b) = (b && a) :=
  match a, b with
  | false, false => fun x => rfl
  | false, true => fun x => rfl
  | true, false => fun x => rfl
  | true, true => fun x => rfl
"#,
    )
    .expect("right-nested tuple motives and nested binders must specialize");
    assert_checked(&env, "packedBoolAssoc");
    assert_checked(&env, "packedUnderBinder");
}

#[test]
fn false_decide_or_and_wrong_arm_are_refused() {
    let wrong = DECIDE_OR.replace(" || ", " && ");
    let Err(err) = elaborate(&wrong) else {
        panic!("OR is not AND");
    };
    eprintln!("WRONG_DECIDE_OR_REFUSED: {err:?}");
    assert!(
        matches!(
            err,
            ElabError::MatchArmTypeMismatch { .. }
                | ElabError::TypeMismatch { .. }
                | ElabError::KernelCheckFailed { .. }
        ),
        "typed refusal, not a parser/name/budget failure: {err:?}"
    );
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    let wrong_arm = DECIDE_OR.replacen("=> rfl", "=> Bool.false", 1);
    let Err(err) = elaborate(&wrong_arm) else {
        panic!("Bool is not an equality proof");
    };
    eprintln!("WRONG_ARM_REFUSED: {err:?}");
    assert!(
        matches!(
            err,
            ElabError::MatchArmTypeMismatch { .. }
                | ElabError::TypeMismatch { .. }
                | ElabError::KernelCheckFailed { .. }
        ),
        "typed refusal: {err:?}"
    );
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
}

#[test]
fn incomplete_and_axiom_controls_remain_discriminating() {
    let mut kernel = Environment::with_prelude();
    let pending = Expr::fvar(FVarId::new((1_u64 << 63) | 3));
    assert!(
        MetaState::expr_has_meta(&pending),
        "the audit must detect actual tagged metas"
    );
    let error = kernel
        .add_decl(Declaration::Theorem {
            name: Name::from_string("unresolvedPackedProof"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("True"), vec![]),
            value: pending,
        })
        .expect_err("an unresolved expression meta must not enter the kernel");
    assert!(matches!(
        error,
        EnvError::ContainsFreeVar { .. } | EnvError::ContainsMetavar { .. }
    ));
    let error = kernel
        .add_decl(Declaration::Axiom {
            name: Name::from_string("unresolvedPackedUniverse"),
            level_params: vec![],
            type_: Expr::sort(Level::param(Name::from_string("undeclaredPackedLevel"))),
        })
        .expect_err("an undeclared universe must not enter the kernel");
    assert!(matches!(error, EnvError::UndefinedLevelParam { .. }));
    // The audit itself: an incomplete arm that elaborates must be caught.
    let env = elaborate(
        "theorem incompleteArm (a : Bool) : (a || false) = a :=\n  match a with\n  | false => sorry\n  | true => rfl\n",
    )
    .expect("a single-discriminant sorry arm elaborates");
    let closure = env
        .axiom_deps(&Name::from_string("incompleteArm"))
        .expect("closure");
    assert!(
        closure.contains(&Name::from_string("sorryAx")),
        "a sorry arm cannot disappear from the audit"
    );
    // A sorry arm in the packed match elaborates in every position, and the
    // audit reports it. Before 2026-11-11 the column split discarded any
    // sorry-bearing result, so every arm went to the chain and was checked
    // against the unrefined goal (docs/issues/2026-11-11-packed-match-sorry-arm-loses-motive.md).
    let arms: Vec<usize> = DECIDE_OR
        .match_indices("=> rfl")
        .map(|(at, _)| at)
        .collect();
    assert_eq!(arms.len(), 4);
    for (index, at) in arms.iter().enumerate() {
        let mut sorry = DECIDE_OR.to_owned();
        sorry.replace_range(*at..at + "=> rfl".len(), "=> sorry");
        let env = elaborate(&sorry)
            .unwrap_or_else(|error| panic!("sorry in arm {index} must elaborate: {error:?}"));
        let value = env
            .get_const(&Name::from_string("overflow_decide_or"))
            .expect("registered subject")
            .value
            .clone()
            .expect("body");
        assert!(
            value.has_non_synthetic_sorry(),
            "arm {index}: the user's sorry is kept"
        );
        assert!(
            !value.has_synthetic_sorry(),
            "arm {index}: no compiler-minted sorry"
        );
        let closure = env
            .axiom_deps(&Name::from_string("overflow_decide_or"))
            .expect("closure");
        assert!(
            closure.contains(&Name::from_string("sorryAx")),
            "arm {index}: incomplete body must not pass the proof audit"
        );
    }
    // A sorry arm does not excuse a missing case.
    let last_arm = DECIDE_OR.rfind("  | ").expect("last arm");
    let missing = DECIDE_OR[..last_arm].replacen("=> rfl", "=> sorry", 1);
    let Err(err) = elaborate(&missing) else {
        panic!("a non-exhaustive match is refused even with a sorry arm");
    };
    eprintln!("NONEXHAUSTIVE_SORRY_REFUSED: {err:?}");
    assert!(
        matches!(
            err,
            ElabError::MatchArmTypeMismatch { .. }
                | ElabError::TypeMismatch { .. }
                | ElabError::KernelCheckFailed { .. }
                | ElabError::NotImplemented(..)
        ),
        "typed refusal, not a parser/name/budget failure: {err:?}"
    );
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    let env = elaborate("axiom domain : False\ntheorem uses_domain : False := domain\n")
        .expect("axiom control registers honestly");
    let closure = env
        .axiom_deps(&Name::from_string("uses_domain"))
        .expect("closure");
    assert!(
        closure.contains(&Name::from_string("domain")),
        "domain axiom cannot disappear from audit"
    );
}

#[test]
fn dependent_context_and_let_discriminants_keep_existing_lowering() {
    let env = elaborate(
        r#"
def packed_keep (F : Bool → Type) (a b : Bool) (h : F a) : F a :=
  match a, b with
  | false, false => h
  | false, true => h
  | true, false => h
  | true, true => h

def packed_let_constant (a b : Bool) (n : Nat) : Nat :=
  let c := a
  match c, b with
  | false, false => n
  | false, true => n
  | true, false => n
  | true, true => n

"#,
    )
    .expect("a packed match must retain dependent hypotheses and let equations");
    assert_checked(&env, "packed_keep");
    assert_checked(&env, "packed_let_constant");
    // Pinned 4.8.0, 4.30.0-rc2 and 4.36.0-rc2 reject this precise proof: the
    // motive generalizes the let-bound discriminant `c` without its value,
    // so an arm must prove `true = a`. Clean once refused it only at RawDecl
    // parser recovery; once the input parsed, the packed route zeta'd `c` to
    // `a` and accepted it. It is now refused at the arm, as Lean refuses it.
    let Err(error) = elaborate(include_str!(
        "fixtures/multi_scrutinee_let_alias_refused.lean"
    )) else {
        panic!("the oracle-rejected let-alias proof must not become accepted");
    };
    assert!(
        matches!(error, ElabError::MatchArmTypeMismatch { .. }),
        "refused at the arm the generalized motive rejects: {error:?}"
    );
}

/// KNOWN OVER-ACCEPTANCE (ledger 199): pinned Lean 4.8.0, 4.30.0-rc2 and
/// 4.36.0-rc2 refuse both proofs below, because the packed motive generalizes
/// the let-bound `c` without its value. Clean still accepts them: once another
/// local depends on `c`, `packed_match_motive` steps aside and the constant
/// route zetas `c` to `a`. This pin fails loudly the day Clean refuses them;
/// then move both to refusals beside `multi_scrutinee_let_alias_refused.lean`.
#[test]
fn let_discriminant_with_dependent_local_known_over_acceptance() {
    const ARMS: &str = "    match c, b with\n    | false, false => rfl\n    | false, true => rfl\n    | true, false => rfl\n    | true, true => rfl\n  proof\n";
    let letdep = format!(
        "theorem fa (a b : Bool) : a = a :=\n  let c := a\n  have h : c = a := rfl\n  have proof : c = a :=\n{ARMS}"
    );
    let letval = format!(
        "theorem fb (a b : Bool) : a = a :=\n  let c := a\n  let d := c\n  have proof : c = a :=\n{ARMS}"
    );
    for (name, source) in [("fa", letdep), ("fb", letval)] {
        let env = elaborate(&source).unwrap_or_else(|error| {
            panic!(
                "ledger 199 may have closed: Clean now refuses `{name}` as pinned Lean does ({error:?}); move it to the refusals"
            )
        });
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "`{name}` must be registered while the over-acceptance stands"
        );
    }
}
