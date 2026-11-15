use super::*;
use crate::rawexpr::BinderInfo;
use crate::term::TermKind;
use crate::{RawExpr, RawLevel};

#[test]
fn pinned_mutual_prop_recursor_does_not_k_reduce_in_either_conversion_path() {
    let (report, env) = replay_environment(
        include_str!("../../tests/fixtures/q2-part2/mutual-k.ndjson").as_bytes(),
        Dialect::Lean4Export31,
    )
    .unwrap();
    assert!(report.counts().1.is_empty(), "{report:?}");
    let left = RawExpr::Const(Name::from_dotted("Q2KLeft"), vec![]);
    let right = RawExpr::Const(Name::from_dotted("Q2KRight"), vec![]);
    let motive_left = RawExpr::Lam(
        BinderInfo::Default,
        Box::new(left.clone()),
        Box::new(left.clone()),
    );
    let motive_right = RawExpr::Lam(BinderInfo::Default, Box::new(right), Box::new(left.clone()));
    let intro = RawExpr::Const(Name::from_dotted("Q2KLeft.intro"), vec![]);
    let args = [
        motive_left,
        motive_right,
        intro.clone(),
        intro,
        RawExpr::BVar(0),
    ];
    let raw = args.into_iter().fold(
        RawExpr::Elim(Name::from_dotted("Q2KLeft"), RawLevel::Zero, vec![]),
        |a, b| RawExpr::App(Box::new(a), Box::new(b)),
    );
    let term = Term::validate(&env, &raw, 1, 0).unwrap();
    let mut ctx = vec![Term::validate(&env, &left, 0, 0).unwrap()];
    crate::infer::infer_in_context(&env, &ctx, &term, &mut Budget::default_budget()).unwrap();
    let reduced =
        crate::whnf::whnf_in_context(&env, &ctx, &term, &mut Budget::default_budget()).unwrap();
    assert!(matches!(reduced.unfold_apps().0.kind(), TermKind::Elim(_)));
    assert!(
        crate::def_eq::k_like_major(&env, &mut ctx, &term, &mut Budget::default_budget())
            .unwrap()
            .is_none()
    );
}

#[test]
fn pinned_quotient_computation_reduces_without_using_proof_irrelevance() {
    use crate::validate::Env;
    let (report, env) = replay_environment(
        include_str!("../../tests/fixtures/q2-part2/quotient.ndjson").as_bytes(),
        Dialect::Lean4Export31,
    )
    .unwrap();
    assert!(report.counts().1.is_empty(), "{report:?}");
    let nat = Term::validate(
        &env,
        &RawExpr::Const(Name::from_dotted("Nat"), vec![]),
        0,
        0,
    )
    .unwrap();
    let local = Term::validate(&env, &RawExpr::BVar(0), 1, 0).unwrap();
    for (decl, expected) in [("q2QuotIndProof", "True.intro"), ("q2QuotLift", "Nat.zero")] {
        let body = env.const_def(&Name::from_dotted(decl)).unwrap().body;
        let result = crate::whnf::whnf_in_context(
            &env,
            std::slice::from_ref(&nat),
            &Term::app(body, local.clone()),
            &mut Budget::default_budget(),
        )
        .unwrap();
        let matched = matches!(result.kind(),TermKind::Const(c) if c.name()==&Name::from_dotted(expected))
            || (decl == "q2QuotLift"
                && matches!(result.kind(),TermKind::Lit(crate::term::Lit::Nat(n)) if n.is_zero()));
        assert!(matched, "{decl}: {result:?}");
    }
}

#[test]
fn reserved_name_transport_keeps_checked_opaque_data_opaque() {
    use crate::validate::Env;
    let (report, env) = replay_environment(
        include_str!("../../tests/fixtures/q2-part2/opaque-helper.ndjson").as_bytes(),
        Dialect::Lean4Export31,
    )
    .unwrap();
    assert!(report.counts().1.is_empty(), "{report:?}");
    let original = env
        .const_def(&Name::from_dotted("Q2Opaque.brecOn"))
        .unwrap();
    assert_eq!(original.transparency, Transparency::Opaque);
    let ty = env.const_type(&Name::from_dotted("q2OpaqueSelf")).unwrap();
    let (_, args) = ty.unfold_apps();
    let alias = args.get(1).expect("Eq's left side");
    let reduced = crate::whnf(&env, alias, &mut Budget::default_budget()).unwrap();
    assert!(
        matches!(reduced.kind(),TermKind::Const(c) if c.name()==&Name::from_dotted("Q2Opaque.brecOn"))
    );
    let zero = Term::validate(
        &env,
        &RawExpr::Const(Name::from_dotted("Nat.zero"), vec![]),
        0,
        0,
    )
    .unwrap();
    assert!(!crate::is_def_eq(&env, &reduced, &zero, &mut Budget::default_budget()).unwrap());
}

#[test]
fn nested_private_symbols_preserve_earlier_checked_declarations() {
    use crate::validate::Env;
    let (report, env) = replay_environment(
        include_str!("../../tests/fixtures/q2-part2/nested-collision.ndjson").as_bytes(),
        Dialect::Lean4Export31,
    )
    .unwrap();
    assert!(report.counts().1.is_empty(), "{report:?}");
    let original = env
        .const_def(&Name::from_dotted("Q2CollisionRose._List"))
        .unwrap();
    assert!(
        matches!(original.body.kind(), TermKind::Const(c) if c.name()==&Name::from_dotted("Empty"))
    );
    assert!(env
        .inductive_num_params(&Name::from_dotted("Q2CollisionRose._List"))
        .is_none());
}

#[test]
fn literal_payload_counts_against_the_existing_expansion_envelope() {
    let bound = usize::try_from(syntax::MAX_WIRE_DAG).unwrap();
    let mut tables = Tables::new();
    // A literal node is one node plus its payload: the largest admitted
    // payload is one byte under the bound, the next is refused.
    tables
        .bind(&serde_json::json!({"ie":0,"strVal":"x".repeat(bound - 1)}))
        .unwrap();
    let error = tables
        .bind(&serde_json::json!({"ie":1,"strVal":"x".repeat(bound)}))
        .unwrap_err();
    assert_eq!(error.reason(), "resource-limit");
    // One payload is shared, but the application adds one DAG node: this
    // expression exceeds the same bound by one and is refused on reading.
    tables
        .bind(&serde_json::json!({"ie":2,"app":{"fn":0,"arg":0}}))
        .unwrap();
    let error = tables.expr(2, &[]).unwrap_err();
    assert_eq!(error.reason(), "resource-limit");
    let mut shared = Tables::new();
    shared
        .bind(&serde_json::json!({"ie":0,"strVal":"x".repeat(bound / 2 + 1)}))
        .unwrap();
    shared
        .bind(&serde_json::json!({"ie":1,"app":{"fn":0,"arg":0}}))
        .unwrap();
    shared
        .expr(1, &[])
        .expect("a shared payload is charged once, not once per path");
}
