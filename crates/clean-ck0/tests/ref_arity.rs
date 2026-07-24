// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ConstRef / ElimRef arity rejection (design §4.2/§4.3 Incident #1).

use clean_ck0::{ConstRef, ElimRef, Level, MinimalEnv, Name, RawExpr, RawLevel, Term};
use proptest::prelude::*;

fn nat() -> Name {
    Name::from_dotted("Nat")
}

#[test]
fn test_constref_correct_arity_accepted() {
    // `List` declared with 1 level param; supplying exactly 1 is accepted.
    let env = MinimalEnv::new().with_const(Name::from_dotted("List"), 1);
    let c = ConstRef::mk(&env, Name::from_dotted("List"), vec![Level::param(0)]);
    assert!(c.is_ok());
    assert_eq!(c.expect("ok").levels().len(), 1);
}

#[test]
fn test_constref_wrong_arity_rejected() {
    // `List` needs 1 level; supplying 0 or 2 must be Err(LevelArity).
    let env = MinimalEnv::new().with_const(Name::from_dotted("List"), 1);
    assert!(ConstRef::mk(&env, Name::from_dotted("List"), vec![]).is_err());
    assert!(ConstRef::mk(
        &env,
        Name::from_dotted("List"),
        vec![Level::param(0), Level::param(1)]
    )
    .is_err());
}

#[test]
fn test_constref_unknown_name_rejected() {
    let env = MinimalEnv::new();
    assert!(ConstRef::mk(&env, Name::from_dotted("Nope"), vec![]).is_err());
}

#[test]
fn test_elimref_large_elim_prepends_motive_level() {
    // A large-eliminating inductive with 0 level params: derived = [motive].
    let env = MinimalEnv::new().with_inductive(nat(), 0, true);
    let e = ElimRef::mk(&env, nat(), Level::param(0), vec![]).expect("ok");
    // motive level prepended; no ind levels here.
    assert_eq!(e.levels().len(), 1);
    assert_eq!(e.levels()[0], Level::param(0));
}

#[test]
fn test_elimref_small_elim_omits_motive_level() {
    // A small-eliminating Prop inductive with exactly ONE declared level param:
    // derived vector = [ind...] only. The inductive's declared arity (1) is what
    // makes supplying one `ind_level` valid; supplying any other count rejects
    // (see test_elimref_wrong_ind_levels_arity_rejected).
    let env = MinimalEnv::new().with_inductive(nat(), 1, false);
    let e = ElimRef::mk(&env, nat(), Level::param(0), vec![Level::param(1)]).expect("ok");
    assert_eq!(e.levels().len(), 1, "no motive level for small-elim");
    assert_eq!(e.levels()[0], Level::param(1));
}

#[test]
fn test_elimref_wrong_ind_levels_arity_rejected() {
    // The level-count kill of Incident #1: an inductive declaring 1 level param
    // must reject `ind_levels` of length 0, 2, or 17 — the derived vector length
    // is NOT caller-choosable. (Was the masked hole: the old env carried no arity
    // for inductives, so ElimRef::mk blessed any length verbatim.)
    let env = MinimalEnv::new().with_inductive(nat(), 1, false);
    for bad in [0usize, 2, 17] {
        let ind_levels = vec![Level::param(0); bad];
        let r = ElimRef::mk(&env, nat(), Level::param(0), ind_levels);
        assert!(
            matches!(
                r,
                Err(clean_ck0::TermError::ElimLevelArity {
                    got,
                    expected: 1,
                    ..
                }) if got == bad
            ),
            "ind_levels.len()={bad} must be ElimLevelArity, got {r:?}"
        );
    }
    // And for a large-elim inductive declaring 2 level params, the motive level
    // is still prepended only once and `ind_levels` must be exactly 2.
    let env2 = MinimalEnv::new().with_inductive(Name::from_dotted("Eq"), 2, true);
    assert!(ElimRef::mk(
        &env2,
        Name::from_dotted("Eq"),
        Level::param(0),
        vec![Level::param(1)]
    )
    .is_err());
    let ok = ElimRef::mk(
        &env2,
        Name::from_dotted("Eq"),
        Level::param(0),
        vec![Level::param(1), Level::param(2)],
    )
    .expect("correct arity");
    // [motive, ind0, ind1] = 1 + 2.
    assert_eq!(ok.levels().len(), 3);
}

#[test]
fn test_elimref_unknown_inductive_rejected() {
    let env = MinimalEnv::new();
    assert!(ElimRef::mk(&env, Name::from_dotted("Nope"), Level::zero(), vec![]).is_err());
}

#[test]
fn test_validate_const_wrong_arity_rejected() {
    // Through the chokepoint: Const with wrong level count is rejected.
    let env = MinimalEnv::new().with_const(Name::from_dotted("List"), 1);
    // supply 0 levels for a 1-param const
    let raw = RawExpr::Const(Name::from_dotted("List"), vec![]);
    assert!(Term::validate_closed(&env, &raw).is_err());
    // supply the correct 1
    let ok = RawExpr::Const(Name::from_dotted("List"), vec![RawLevel::Zero]);
    assert!(Term::validate_closed(&env, &ok).is_ok());
}

#[test]
fn test_validate_elim_caller_cannot_author_level_vector() {
    // The Raw boundary for Elim carries (inductive, motive_level, ind_levels).
    // There is no field for a full level vector; the kernel derives it. This
    // test documents that the derived vector for a large-elim Nat with a motive
    // level is exactly [motive].
    let env = MinimalEnv::new().with_inductive(nat(), 0, true);
    let raw = RawExpr::Elim(nat(), RawLevel::Param(0), vec![]);
    let t = Term::validate(&env, &raw, 0, 1).expect("validates");
    match t.kind() {
        clean_ck0::term::TermKind::Elim(e) => {
            assert_eq!(e.levels(), &[Level::param(0)]);
        }
        other => panic!("expected Elim, got {other:?}"),
    }
}

#[test]
fn test_validate_elim_wrong_ind_levels_rejected_through_chokepoint() {
    // The chokepoint must reject an Elim whose ind_levels count disagrees with
    // the inductive's declared arity. (Adversarial repro from the finding: a
    // 1-param inductive with 7 ind levels was accepted; now Rejected.)
    let env = MinimalEnv::new().with_inductive(nat(), 1, false);
    let seven: Vec<RawLevel> = (0..7).map(RawLevel::Param).collect();
    let raw = RawExpr::Elim(nat(), RawLevel::Param(0), seven);
    let r = Term::validate(&env, &raw, 0, 8);
    assert!(
        r.is_err(),
        "7 ind levels for a 1-param inductive must reject"
    );
    // The correct count (1) validates.
    let ok = RawExpr::Elim(nat(), RawLevel::Param(0), vec![RawLevel::Param(0)]);
    assert!(Term::validate(&env, &ok, 0, 1).is_ok());
}

proptest! {
    /// Core invariant (design §4.2): for a declared inductive arity `n` and any
    /// supplied `ind_levels` length `k`, `ElimRef::mk` succeeds **iff** `k == n`,
    /// and on success the derived level vector length is exactly
    /// `n + (1 iff large_elim)` — never caller-chosen.
    #[test]
    fn prop_elimref_arity_iff_match(
        n in 0u32..6,
        k in 0usize..8,
        large_elim in any::<bool>(),
    ) {
        let name = Name::from_dotted("I");
        let env = MinimalEnv::new().with_inductive(name.clone(), n, large_elim);
        let ind_levels = vec![Level::zero(); k];
        let r = ElimRef::mk(&env, name, Level::param(0), ind_levels);
        if k == n as usize {
            let e = r.expect("matching arity must succeed");
            let expected_len = n as usize + usize::from(large_elim);
            prop_assert_eq!(e.levels().len(), expected_len);
        } else {
            prop_assert!(
                matches!(r, Err(clean_ck0::TermError::ElimLevelArity { .. })),
                "mismatched arity (k={}, n={}) must be ElimLevelArity, got {:?}",
                k, n, r
            );
        }
    }
}
