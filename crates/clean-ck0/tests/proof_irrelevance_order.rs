//! Conversion should infer proof types before reducing transparent proof bodies.
use clean_ck0::{is_def_eq, Budget, MinimalEnv, Name, RawExpr, Term, Transparency};

#[test]
fn proof_irrelevance_avoids_unfolding_long_honest_alias_chains() {
    let p = Name::from_dotted("P");
    let q = Name::from_dotted("Q");
    let witness = Name::from_dotted("witness");
    let other = Name::from_dotted("other");
    let mut env = MinimalEnv::new()
        .with_const_typed(
            p.clone(),
            0,
            Term::validate(
                &MinimalEnv::new(),
                &RawExpr::Sort(clean_ck0::RawLevel::Zero),
                0,
                0,
            )
            .unwrap(),
        )
        .with_const_typed(
            q.clone(),
            0,
            Term::validate(
                &MinimalEnv::new(),
                &RawExpr::Sort(clean_ck0::RawLevel::Zero),
                0,
                0,
            )
            .unwrap(),
        );
    let constant =
        |env: &MinimalEnv, n: Name| Term::validate(env, &RawExpr::Const(n, vec![]), 0, 0).unwrap();
    let p_ty = constant(&env, p);
    let q_ty = constant(&env, q);
    env = env
        .with_const_typed(witness.clone(), 0, p_ty.clone())
        .with_const_typed(other.clone(), 0, q_ty);
    let mut last = witness.clone();
    for i in 0..600 {
        let next = Name::from_dotted(&format!("alias{i}"));
        let body = constant(&env, last);
        env = env.with_def(
            next.clone(),
            0,
            p_ty.clone(),
            body,
            Transparency::Transparent,
        );
        last = next;
    }
    let a = constant(&env, last);
    let b = constant(&env, witness);
    assert_eq!(is_def_eq(&env, &a, &b, &mut Budget::new(512)), Ok(true));
    let different = constant(&env, other);
    assert_eq!(
        is_def_eq(&env, &b, &different, &mut Budget::new(512)),
        Ok(false)
    );
}
