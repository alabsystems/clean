use super::*;
use crate::term::{ConstRef, Lit, TermKind};
use crate::validate::Env;
const REFERENCE: &str = include_str!("../../tests/fixtures/q2-part2/native-reference.ndjson");
fn term(env: &MinimalEnv, name: &str) -> Term {
    Term::const_ref(ConstRef::mk(env, Name::from_dotted(name), vec![]).unwrap())
}
#[test]
fn all_native_folds_match_unfolding_of_actual_pinned_definitions() {
    let (report, fast) = replay_environment(REFERENCE.as_bytes(), Dialect::Lean4Export31).unwrap();
    assert!(report.counts().1.is_empty(), "{report:?}");
    assert_eq!(report.rows.len(), 548);
    check_folds(
        &fast,
        &[
            "add",
            "sub",
            "mul",
            "div",
            "mod",
            "pow",
            "beq",
            "ble",
            "gcd",
            "land",
            "lor",
            "xor",
            "shiftLeft",
            "shiftRight",
        ],
    );
}
#[test]
fn legacy_profile_checks_actual_std_bodies_before_licensing_each_fold() {
    let (report, env) = replay_environment(
        include_str!("../../tests/fixtures/q2-part2/native-reference-4.29.1.ndjson").as_bytes(),
        Dialect::Lean4Export31,
    )
    .unwrap();
    let refusals: Vec<_> = report.rows.iter().filter(|r| r.verdict.is_err()).collect();
    assert_eq!(refusals.len(), 1, "{refusals:?}");
    assert_eq!(refusals[0].name, Name::from_dotted("sorryAx"));
    assert_eq!(
        refusals[0].verdict.as_ref().unwrap_err().reason(),
        "axiom-policy"
    );
    assert_eq!(report.rows.len(), 2059);
    check_folds(
        &env,
        &["add", "sub", "mul", "div", "mod", "pow", "beq", "ble"],
    );
    assert!(env.string_literal_view());
    assert!(!env.native_nat_allowed(&Name::from_dotted("Nat.gcd")));
}
fn check_folds(fast: &MinimalEnv, operations: &[&str]) {
    let mut slow = fast.clone();
    slow.restrict_native_nat_folds();
    for op in operations {
        let name = format!("Nat.{op}");
        assert!(fast.native_nat_allowed(&Name::from_dotted(&name)), "{name}");
        assert!(!slow.native_nat_allowed(&Name::from_dotted(&name)));
        for (a, b) in [(0, 0), (0, 3), (3, 0), (1, 1), (2, 3), (3, 2)] {
            let args = [
                Term::lit(Lit::Nat(crate::BigNat::from_u64(a))),
                Term::lit(Lit::Nat(crate::BigNat::from_u64(b))),
            ];
            let e = Term::apply(term(fast, &name), &args);
            let native = crate::whnf(fast, &e, &mut Budget::default_budget()).unwrap();
            let unfolded = crate::whnf(&slow, &e, &mut Budget::default_budget()).unwrap();
            assert!(
                matches!(
                    native.kind(),
                    TermKind::Lit(Lit::Nat(_)) | TermKind::Const(_)
                ),
                "{name} native not fired: {native:?}"
            );
            assert!(
                crate::is_def_eq(&slow, &native, &unfolded, &mut Budget::default_budget())
                    .unwrap_or_else(|e| panic!("{name} {a} {b}: {e}")),
                "{name} {a} {b}: {native:?} vs {unfolded:?}"
            );
        }
    }
    assert!(fast.native_nat_allowed(&Name::from_dotted("Nat.succ")));
    for n in [0, 1, 7, 999999999999] {
        let e = Term::apply(
            term(fast, "Nat.succ"),
            &[Term::lit(Lit::Nat(crate::BigNat::from_u64(n)))],
        );
        let a = crate::whnf(fast, &e, &mut Budget::default_budget()).unwrap();
        let b = crate::whnf(&slow, &e, &mut Budget::default_budget()).unwrap();
        assert!(matches!(a.kind(), TermKind::Lit(Lit::Nat(_))));
        assert!(crate::is_def_eq(&slow, &a, &b, &mut Budget::default_budget()).unwrap());
    }
}
#[test]
fn canonical_string_view_matches_actual_pinned_constructor_definition() {
    let (report, env) = replay_environment(
        include_str!("../../tests/fixtures/q2-part2/literals.ndjson").as_bytes(),
        Dialect::Lean4Export31,
    )
    .unwrap();
    assert!(report.counts().1.is_empty(), "{report:?}");
    assert!(env.string_literal_view());
    let ty = env
        .const_type(&Name::from_dotted("q2StringLiteral"))
        .unwrap();
    let (_, args) = ty.unfold_apps();
    let literal = args.get(1).unwrap();
    let explicit = args.get(2).unwrap();
    assert!(matches!(literal.kind(), TermKind::Lit(Lit::Str(_))));
    let view = crate::whnf(&env, literal, &mut Budget::default_budget()).unwrap();
    let (head, _) = view.unfold_apps();
    assert!(
        matches!(head.kind(),TermKind::Const(c) if c.name()==&Name::from_dotted("String.ofByteArray"))
    );
    assert!(crate::is_def_eq(&env, literal, explicit, &mut Budget::default_budget()).unwrap());
}

#[test]
fn older_propext_stream_checks_its_fixed_logical_prerequisite() {
    let report = replay(
        include_str!("../../tests/fixtures/q2-part2/legacy-axiom-prefix.ndjson").as_bytes(),
        Dialect::Lean4Export31,
    )
    .unwrap();
    assert!(report.counts().1.is_empty(), "{report:?}");
    assert!(report.axioms.contains(&Name::from_dotted("propext")));
}
