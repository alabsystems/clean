// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact Have/Let controls independently measured on Lean430rc2,435,436rc2.
//! Direct and local-guard for proofs have native [propext], not empty closure.
//! These are ordinary source elaboration tests, not subprocess/native replays.

use clean_elab::tactic::{builtins::builtin_tactic_patterns, TacticError};
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, ElabResult,
    FileContext,
};
use clean_kernel::{Environment, Expr, ExprKind, Level, Name, TypeChecker};
use clean_parser::{
    parse_file_with_tactics_diagnostics, Projection, SurfaceDecl, SurfaceExpr, SurfaceLit,
    SurfaceTactic,
};
use sha2::{Digest, Sha256};

fn check_stored(
    env: &Environment,
    name: &str,
    expected_type: &Expr,
    value: Option<u64>,
    native_axioms_empty: bool,
) {
    let name = Name::from_string(name);
    let info = env.get_const(&name).expect("actual declaration registers");
    let stored = info.value.as_ref().expect("actual checked body is stored");
    for expression in [&info.type_, stored] {
        assert!(
            !expression.has_fvar_quick() && !expression.has_loose_bvars_quick(),
            "{name}: registered type and value must be closed"
        );
    }
    let mut checker = TypeChecker::new(env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    let type_kind = checker
        .infer_type_full(&info.type_)
        .expect("strict full inference of stored public type");
    assert!(matches!(type_kind.kind(), ExprKind::Sort(_)));
    let inferred = checker
        .infer_type_full(stored)
        .expect("strict full inference of actual stored value/proof");
    assert!(checker.is_def_eq(&inferred, &info.type_));
    assert!(checker.is_def_eq(&info.type_, expected_type));
    if let Some(value) = value {
        assert!(
            checker.is_def_eq(stored, &Expr::nat_lit(value)),
            "{name}: actual mutable continuation must compute{value}"
        );
        assert!(
            !checker.is_def_eq(stored, &Expr::nat_lit(value - 1)),
            "{name}: a lost assignment cannot pass a type-only check"
        );
    }
    assert!(
        !checker.heartbeat_spent(),
        "{name}: no budget-exhausted check"
    );
    let axioms = env.axiom_deps(&name).expect("actual transitive closure");
    assert!(
        axioms
            .iter()
            .all(|axiom| env.is_canonical_foundational_axiom(axiom)),
        "{name}: non-foundational axiom in stored declaration: {axioms:?}"
    );
    if native_axioms_empty {
        assert!(
            axioms.is_empty(),
            "{name}: native empty closure: {axioms:?}"
        );
    }
}

fn assert_local_n_origin(env: &Environment, theorem: &str, carrier: &str, nondep: bool) {
    let name = Name::from_string(theorem);
    let info = env.get_const(&name).expect("registered numeral theorem");
    let mut body = info.value.as_ref().expect("stored numeral proof");
    while let ExprKind::MData(_, inner) = body.kind() {
        body = inner;
    }
    let ExprKind::Let(name, ty, value, _, actual_nondep) = body.kind() else {
        panic!("the actual named numeral binding must be retained");
    };
    assert_eq!(name, &Name::from_string("n"));
    assert_eq!(*actual_nondep, nondep, "retain the actual Have/Let origin");
    let expected = Expr::const_(Name::from_string(carrier), vec![]);
    let mut checker = TypeChecker::new(env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    assert!(checker.is_def_eq(ty, &expected));
    let inferred = checker
        .infer_type_full(value)
        .expect("the bound numeral itself must have the native carrier");
    assert!(checker.is_def_eq(&inferred, &expected));
    assert!(!checker.heartbeat_spent());
}

fn assert_rfl_refusal(error: &ElabError, source: &str) {
    let mut cursor = error;
    let rfl = source
        .match_indices("rfl")
        .map(|(start, _)| start)
        .collect::<Vec<_>>();
    assert_eq!(rfl.len(), 1, "one exact causal rfl in each false twin");
    let mut attributed_rfl = false;
    while let ElabError::InTactic {
        tactic,
        span_start,
        span_end,
        source: inner,
        ..
    } = cursor
    {
        if tactic == "rfl" {
            assert_eq!(
                source
                    .get(*span_start..*span_end)
                    .expect("rfl attribution stays within the original file")
                    .trim(),
                "rfl",
                "a parse/helper failure must not count as the causal false twin"
            );
            attributed_rfl = true;
        } else if tactic == "have" {
            // The existing from_elab_error bridge strips nested InTactic
            // wrappers. The original typed controls use `by have ... := by rfl`:
            // retain that exact source and require the enclosing attribution
            // to contain its sole atomic rfl proof, not a parser/helper error.
            let fragment = source
                .get(*span_start..*span_end)
                .expect("enclosing have attribution stays in the original file");
            attributed_rfl |=
                fragment.contains("by rfl") && *span_start <= rfl[0] && rfl[0] + 3 <= *span_end;
        }
        cursor = inner;
    }
    assert!(
        attributed_rfl,
        "must fail at the actual source rfl: {error:?}"
    );
    let ElabError::TacticFailed(TacticError::TypeMismatch { expected, actual }) = error.innermost()
    else {
        panic!("must reach a semantic equality mismatch at rfl: {error:?}");
    };
    assert!(
        (expected.contains("Eq") || expected.contains('=')) && !actual.is_empty(),
        "the refusal must carry its equality goal and mismatch: {error:?}"
    );
}

#[derive(Clone, Copy)]
enum RefusalStage {
    Rfl,
    PostponedNumeral,
    PostponedNatLet,
    PostponedIntLet,
}

fn assert_postponed_numeral_refusal(
    error: &ElabError,
    proof: &SurfaceExpr,
    source: &str,
    stage: RefusalStage,
) {
    // The exact unchanged fixtures expose value-consistency errors after the
    // proof body, without an active tactic. These observed payloads, source
    // shape and the direct drain control constrain that source-traced account;
    // the public error has no emitter ID. Do not invent tactic attribution or
    // accept arbitrary type errors as the measured negative controls.
    let (opaque, int, rhs, expected_value, actual_value) = match stage {
        RefusalStage::PostponedNumeral => (true, false, 7, "7", "fvar#0"),
        RefusalStage::PostponedNatLet => (false, false, 8, "8", "7"),
        RefusalStage::PostponedIntLet => (false, true, 8, "Int.ofNat 7", "Int.ofNat 8"),
        RefusalStage::Rfl => panic!("an active rfl refusal uses its attributed assertion"),
    };
    let (n, value, body) = match (opaque, proof) {
        (true, SurfaceExpr::Have(_, n, value, body))
        | (false, SurfaceExpr::Let(_, n, value, body)) => (n, value, body),
        _ => panic!("the untyped binding must retain its exact Have/Let origin"),
    };
    assert_eq!(n.name.name(), &Name::from_string("n"));
    assert!(n.ty.is_none());
    assert!(matches!(
        value.as_ref(),
        SurfaceExpr::Lit(_, SurfaceLit::Nat(7))
    ));
    let SurfaceExpr::Have(_, h, value, tail) = body.as_ref() else {
        panic!("the body must retain its exact equality annotation");
    };
    assert_eq!(h.name.name(), &Name::from_string("h"));
    let SurfaceExpr::Proj(_, tail_base, Projection::Named(tail_field)) = tail.as_ref() else {
        panic!("the final source name must retain its namespace projection: {tail:?}");
    };
    assert!(
        matches!(tail_base.as_ref(), SurfaceExpr::Ident(_, name) if name.name() == &Name::from_string("True"))
    );
    assert_eq!(tail_field.name(), &Name::from_string("intro"));
    let Some(annotation) = h.ty.as_deref() else {
        panic!("the causal equality annotation must remain present");
    };
    let SurfaceExpr::App(_, head, args) = annotation else {
        panic!("the annotation must be the original equality");
    };
    assert!(
        matches!(head.as_ref(), SurfaceExpr::Ident(_, name) if name.name() == &Name::from_string("Eq"))
    );
    assert_eq!(args.len(), 2);
    let left = if int {
        let SurfaceExpr::Ascription(_, left, carrier) = &args[0].expr else {
            panic!("the forced-Int fixture must retain its exact local ascription");
        };
        assert!(
            matches!(carrier.as_ref(), SurfaceExpr::Ident(_, name) if name.name() == &Name::from_string("Int"))
        );
        left.as_ref()
    } else {
        &args[0].expr
    };
    assert!(matches!(left, SurfaceExpr::Ident(_, name) if name.name() == n.name.name()));
    assert!(matches!(&args[1].expr, SurfaceExpr::Lit(_, SurfaceLit::Nat(value)) if *value == rhs));
    let SurfaceExpr::ByTactic(_, tactics) = value.as_ref() else {
        panic!("the exact proof must still be by rfl");
    };
    let [SurfaceTactic::Named { span, name, args }] = tactics.as_slice() else {
        panic!("one atomic rfl must be the causal proof");
    };
    assert_eq!(name, "rfl");
    assert!(args.is_empty());
    assert_eq!(
        source
            .get(span.start..span.end)
            .expect("rfl span stays within its exact source")
            .trim(),
        "rfl"
    );
    let ElabError::TypeMismatch { expected, actual } = error else {
        panic!("must retain the bare deferred-value consistency refusal: {error:?}");
    };
    assert_eq!(expected, expected_value);
    assert_eq!(
        actual, actual_value,
        "the exact observed value mismatch, not a helper/type/parse error"
    );
}

fn check_case(
    source: &str,
    theorem: &str,
    accepts: bool,
    computation: Option<(&str, u64)>,
    native_axioms_empty: bool,
    local_n: Option<(&str, bool)>,
    native_source_sha256: &str,
    refusal_stage: RefusalStage,
) {
    assert_eq!(
        Sha256::digest(source.as_bytes())
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>(),
        native_source_sha256,
        "the fixture must remain byte-exact to its independent native observation"
    );
    let observer = format!("#print axioms {theorem}\n");
    let declaration_source = source
        .strip_suffix(&observer)
        .expect("remove only the exact native axiom observer command");
    let parsed =
        parse_file_with_tactics_diagnostics(declaration_source, &builtin_tactic_patterns())
            .expect("the exact native source must parse without recovery");
    assert!(
        parsed.diagnostics.is_empty(),
        "native source must not recover: {:?}",
        parsed.diagnostics
    );
    assert!(
        parsed
            .decls
            .iter()
            .all(|decl| !matches!(decl, SurfaceDecl::RawDecl { .. })),
        "a recovered declaration is not source acceptance: {:?}",
        parsed.decls
    );
    let declarations = parsed.decls;
    assert_eq!(
        declarations.len(),
        if computation.is_some() { 2 } else { 1 }
    );
    let mut env = Environment::with_prelude();
    let mut file = FileContext::new();
    for declaration in &declarations {
        let processed = preprocess_decl_with_context(declaration, &mut file);
        let result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file);
        if let SurfaceDecl::Def { name, .. } = declaration {
            let (expected_name, value) =
                computation.expect("only direct Do controls have a prefix");
            assert_eq!(name.name(), &Name::from_string(expected_name));
            let ElabResult::Definition { name, .. } =
                result.expect("the computation prefix must succeed before any false theorem")
            else {
                panic!("a failed/recovery leaf cannot masquerade as a definition");
            };
            assert_eq!(name, Name::from_string(expected_name));
            check_stored(
                &env,
                expected_name,
                &Expr::const_(Name::from_string("Nat"), vec![]),
                Some(value),
                native_axioms_empty,
            );
            continue;
        }
        let SurfaceDecl::Theorem { name, proof, .. } = declaration else {
            panic!("only the exact definition/theorem source is allowed");
        };
        assert_eq!(name.name(), &Name::from_string(theorem));
        if !accepts {
            let error = result.expect_err("the native-refused equality must not elaborate");
            match refusal_stage {
                RefusalStage::Rfl => assert_rfl_refusal(&error, declaration_source),
                RefusalStage::PostponedNumeral
                | RefusalStage::PostponedNatLet
                | RefusalStage::PostponedIntLet => {
                    assert_postponed_numeral_refusal(
                        &error,
                        proof,
                        declaration_source,
                        refusal_stage,
                    );
                }
            }
            assert!(
                env.get_const(&Name::from_string(theorem)).is_none(),
                "a failed theorem cannot register"
            );
            return;
        }
        let ElabResult::Theorem { name, .. } = result.expect("native-accepted theorem") else {
            panic!("a failed/recovery leaf cannot masquerade as a theorem");
        };
        assert_eq!(name, Name::from_string(theorem));
    }
    assert!(accepts, "a negative must actually reach its refusal");
    let expected_type = if let Some((definition, value)) = computation {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [
                Expr::const_(Name::from_string("Nat"), vec![]),
                Expr::const_(Name::from_string(definition), vec![]),
                Expr::nat_lit(value),
            ],
        )
    } else {
        Expr::const_(Name::from_string("True"), vec![])
    };
    check_stored(&env, theorem, &expected_type, None, native_axioms_empty);
    if let Some((carrier, nondep)) = local_n {
        assert_local_n_origin(&env, theorem, carrier, nondep);
    }
}

macro_rules! measured_case {
    (
        $name:ident,
        $accepts:literal,
        $computation:expr,
        $empty:literal,
        $local:expr,
        $sha:literal
    ) => {
        measured_case!(
            $name,
            $accepts,
            $computation,
            $empty,
            $local,
            $sha,
            RefusalStage::Rfl
        );
    };
    (
        $name:ident,
        $accepts:literal,
        $computation:expr,
        $empty:literal,
        $local:expr,
        $sha:literal,
        $refusal_stage:expr
    ) => {
        #[test]
        fn $name() {
            check_case(
                include_str!(concat!(
                    "fixtures/term_local_origins/",
                    stringify!($name),
                    ".lean"
                )),
                stringify!($name),
                $accepts,
                $computation,
                $empty,
                $local,
                $sha,
                $refusal_stage,
            );
        }
    };
}

measured_case!(
    have_mutable_if_ok,
    true,
    Some(("have_mutable_if_value", 1)),
    true,
    None,
    "2e6502a8504c89cc5ad33c9c32676111771c859516d0a6c93173b303d3ccc4ec"
);

measured_case!(
    have_mutable_if_wrong_result,
    false,
    Some(("have_mutable_if_value", 1)),
    true,
    None,
    "b1f16248eeb328da9147e8cd687d00e5be1ce2219f20b5922c3b850c20b5da60"
);

measured_case!(
    have_mutable_for_ok,
    true,
    Some(("have_mutable_for_value", 2)),
    false,
    None,
    "d213a2f230bc05d06e4ca0c35f666e6fc090f0853b296d7f51bd78eb59fec56f"
);

measured_case!(
    have_mutable_for_wrong_result,
    false,
    Some(("have_mutable_for_value", 2)),
    false,
    None,
    "1e1f28fa64a3f1821344e2d53292dab559bf9b1f138083cd1bb8935b7d8b606c"
);

measured_case!(
    let_mutable_if_ok,
    true,
    Some(("let_mutable_if_value", 1)),
    true,
    None,
    "3e4d606cb6098e65d52b5c575eb4db0f31ed77e7f6527d67b874344f3da27757"
);

measured_case!(
    let_mutable_if_wrong_result,
    false,
    Some(("let_mutable_if_value", 1)),
    true,
    None,
    "e36a3f72ade2353423b7d32397db64a1049e7b2a93b54fb67b0a531a7f4c167a"
);

measured_case!(
    let_mutable_for_ok,
    true,
    Some(("let_mutable_for_value", 2)),
    false,
    None,
    "93aeb85f316ad638748bbf8093faacdacf9511c48e95ef22a8671822766fd894"
);

measured_case!(
    let_mutable_for_wrong_result,
    false,
    Some(("let_mutable_for_value", 2)),
    false,
    None,
    "85f53c9e0b25dce12ab1c607d0a9e1485ed219ea54a7b2e964b9fc85697def7e"
);

measured_case!(
    term_have_ground_bad,
    false,
    None,
    true,
    Some(("Nat", true)),
    "2cf5406f847961bddae80dec68e078bd34752e624341949ad0dcbdc2e564d812"
);

measured_case!(
    term_have_self_ok,
    true,
    None,
    true,
    Some(("Nat", true)),
    "8067755f2bd84aa157592a758a14162d5a89265556353df1abdae8c5d1b31d85"
);

measured_case!(
    term_let_ground_bad,
    false,
    None,
    true,
    Some(("Nat", false)),
    "74e952ec61c5d1ada055b6f9539bd3ea5e4d7ac4d9456140b4b9db4fcd53d682"
);

measured_case!(
    term_let_ground_ok,
    true,
    None,
    true,
    Some(("Nat", false)),
    "b907a61c9fc6a74f5352622f98d6ed1bda96bb510c3169de3b7e256eaec41680"
);

measured_case!(
    inferred_nat_have_ground,
    false,
    None,
    true,
    Some(("Nat", true)),
    "5107480b8bac250c943be7c5d875c74d3e3eff269ebb00866bb22d591decda1d",
    RefusalStage::PostponedNumeral
);

measured_case!(
    inferred_nat_have_self,
    true,
    None,
    true,
    Some(("Nat", true)),
    "8e83ec3a892579b57f8e2bb9a0b1525adb991d1a57e8a5cdfad883aac7bd034c"
);

measured_case!(
    inferred_nat_let_ground,
    true,
    None,
    true,
    Some(("Nat", false)),
    "cb67f9c22d710014a89322e2957bad2c7c5f518afd5eb6fb0decc75fe74e9668"
);

measured_case!(
    inferred_nat_let_wrong,
    false,
    None,
    true,
    Some(("Nat", false)),
    "c1ed8dc617985d5aeb9cc0f044e3c1b7678ca66283703a48aa4e53b853969e48",
    RefusalStage::PostponedNatLet
);

measured_case!(
    forced_int_have_ground,
    false,
    None,
    true,
    Some(("Int", true)),
    "206cb56e3ea139c5d822bbd4ae782da04726282c340523f8db2a3f0351010fcc"
);

measured_case!(
    forced_int_have_self,
    true,
    None,
    true,
    Some(("Int", true)),
    "7777c2340d000fe80a063ab95e6b053f6cb9f34e0e078499580d730863529e42"
);

measured_case!(
    forced_int_let_ground,
    true,
    None,
    true,
    Some(("Int", false)),
    "7726adba6537c352895729bbaf456d707cc70b99381b6e10b99c860fc22adb0d"
);

measured_case!(
    forced_int_let_wrong,
    false,
    None,
    true,
    Some(("Int", false)),
    "0cd14f938cde5aef932ffb5cd99975b96f518a2c0e30d9fc0ed3b496236987bd",
    RefusalStage::PostponedIntLet
);

measured_case!(
    typed_int_have_ground,
    false,
    None,
    true,
    Some(("Int", true)),
    "223fc02e4cc0996a0abcf3c2bca769c317b4abca12992ccaeb2a7f1da16bd6bb"
);

measured_case!(
    typed_int_have_self,
    true,
    None,
    true,
    Some(("Int", true)),
    "ab8f625ed5f08e2c287fa73a2a92626717feff0f79e19eedb59e9d4d00495406"
);

measured_case!(
    typed_int_let_ground,
    true,
    None,
    true,
    Some(("Int", false)),
    "dc6ecb7d799795bb219e92b1edb9199e61f81c8f4a10d98ea1ab05e122e5f3f3"
);

measured_case!(
    typed_int_let_wrong,
    false,
    None,
    true,
    Some(("Int", false)),
    "25021ad47a49b0adfd29361d100265d7dfcf176b177e557ea57c12a265decc3f"
);

measured_case!(
    have_for_local_equation_ok,
    true,
    None,
    false,
    None,
    "697a9c6103ec13b9b89cef91e9d726b94cc05da161b75628e6608f84c547a071"
);

measured_case!(
    have_for_local_equation_wrong,
    false,
    None,
    false,
    None,
    "8c6a48debe2b5807775aea37dfa0c83797a4aeda04193fb678a0808b2e5b98f7"
);

measured_case!(
    let_for_local_equation_ok,
    true,
    None,
    false,
    None,
    "46d83095a0d06346110fd5359598553182804d7cef3d202643fb57f80187eb2d"
);

measured_case!(
    let_for_local_equation_wrong,
    false,
    None,
    false,
    None,
    "d64eaf77648fef8eb8e396f4646a657a4b1d2e2abdb55cee18dd5ef45a3c9f81"
);
