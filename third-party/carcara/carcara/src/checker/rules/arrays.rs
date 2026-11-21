// Modified in Clean: typed array-lambda dialect and explicit lambda export refusal.
use super::{
    assert_alpha_equiv, assert_clause_len, assert_eq, assert_num_args, assert_num_premises,
    first_conclusion_literal, get_premise_term, CheckerError, RuleArgs, RuleResult,
};
use crate::ast::{build_term, match_term_err, Binder, BindingList, Sort, Term};

pub fn idx(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    match_term_err!((= (select (store a i e) i) e) = &conclusion[0])?;
    Ok(())
}

pub fn row(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (ip, jp) = match_term_err!((not (= i j)) = premise)?;

    assert_clause_len(conclusion, 1)?;
    let (_, ic, _, jc) =
        match_term_err!((= (select (store a i e) j) (select a j)) = &conclusion[0])?;
    // indices are the same in premise and conclusion
    assert_eq(ip, ic)?;
    assert_eq(jp, jc)?;
    Ok(())
}

pub fn row_contra(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (_, ip, _, jp) =
        match_term_err!((not (= (select (store a i e) j) (select a j))) = premise)?;
    assert_clause_len(conclusion, 1)?;
    let (ic, jc) = match_term_err!((= i j) = &conclusion[0])?;
    // indices are the same in conclusion and premise, but conclusion might be flipped
    if ip != ic {
        assert_eq(ip, jc)?;
        assert_eq(jp, ic)
    } else {
        assert_eq(jp, jc)
    }
}

pub fn ext(
    RuleArgs {
        conclusion,
        premises,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (ap, bp) = match_term_err!((not (= a b)) = premise)?;
    // Modified in Clean: the conclusion is read through `first_conclusion_literal`; indexing it
    // panicked on `(cl)` (see third-party/carcara/DOWNSTREAM.md).
    let (ac, _, bc) = match_term_err!((not (= (select ac k) (select bc k))) = first_conclusion_literal(conclusion)?)?;
    // arrays the same in premise and conclusion
    assert_eq(ap, ac)?;
    assert_eq(bp, bc)?;
    // build (choice (x I) (or (= a b) (not (= (select a x) (select b x))))) where
    // the type of x comes from the array sort of a. With that I can
    // check alpha equiv of (select a choice) with the lhs of
    // conclusion and likewise for the rhs

    // check index is (choice (x I) (not (= (select a x) (select b x))))
    let Sort::Array(index_sort, _) = pool.sort(ap).as_ref().clone() else {
        return Err(CheckerError::Explanation(format!(
            "Could not get Array sort from term {}",
            ap
        )));
    };
    // Modified in Clean: the witness variable must not capture a free variable of `a` or `b`.
    // It used to be named `x` unconditionally, so `(store c x v)` had its free `x` captured by
    // the choice binder. Pick a name free in neither array and compare modulo renaming of bound
    // variables, so any non-capturing name chosen by the producer is accepted (see
    // third-party/carcara/DOWNSTREAM.md).
    let taken = [pool.free_vars(ap), pool.free_vars(bp)];
    let mut name = "x".to_owned();
    while taken.iter().any(|free| free.contains_name(&name)) {
        name.push('_');
    }
    let x = pool.add(Term::new_var(name.clone(), index_sort.clone()));
    let body = build_term!(pool, (or
        (= {ap.clone()} {bp.clone()})
        (not (= (select { ap.clone() } { x.clone() }) (select { bp.clone() } { x.clone() })))
    ));
    let choice = pool.add(Term::Binder(
        Binder::Choice,
        BindingList(vec![(name, index_sort.clone())]),
        body,
    ));

    let expected = build_term!(pool,
        (not (= (select {ap.clone()} {choice.clone()}) (select {bp.clone()} {choice.clone()})))
    );

    assert_alpha_equiv(
        first_conclusion_literal(conclusion)?,
        &expected,
        polyeq_time,
    )
}

/// Clean dialect: independently check a unary ARRAY-lambda read. Function
/// lambdas retain their separate higher-order beta_equiv rule. This introduces
/// no assumption, extensional equality, or array-default/choice axiom.
pub fn lambda(
    RuleArgs {
        conclusion,
        premises,
        args,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    use crate::ast::Substitution;
    assert_num_premises(premises, 0)?;
    assert_num_args(args, 0)?;
    assert_clause_len(conclusion, 1)?;
    let (read, result) = match_term_err!((= read result) = &conclusion[0])?;
    let (array, index) = match_term_err!((select array index) = read)?;
    let Term::Binder(Binder::ArrayLambda, bindings, body) = array.as_ref() else {
        return Err(CheckerError::Explanation(
            "arrays_lambda requires a typed array lambda".into(),
        ));
    };
    let [(name, domain)] = bindings.as_slice() else {
        return Err(CheckerError::Explanation(
            "array lambda must bind exactly one index".into(),
        ));
    };
    let range = pool.sort(body);
    let array_sort = pool.sort(array);
    if array_sort.as_ref() != &Sort::Array(domain.clone(), range.clone())
        || pool.sort(index) != *domain
        || pool.sort(read) != range
        || pool.sort(result) != range
    {
        return Err(CheckerError::Explanation(
            "arrays_lambda domain or range mismatch".into(),
        ));
    }
    let variable = pool.add(Term::new_var(name.clone(), domain.clone()));
    let reduced = Substitution::single(pool, variable, index.clone())?.apply(pool, body);
    assert_alpha_equiv(&reduced, result, polyeq_time)
}
