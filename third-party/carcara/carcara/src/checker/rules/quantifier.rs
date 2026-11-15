use super::{
    assert_alpha_equiv_expected, assert_clause_len, assert_eq, assert_is_expected, assert_num_args,
    assert_operation_len, CheckerError, RuleArgs, RuleResult,
};
use crate::{
    ast::{
        build_term, match_term, match_term_err, pool::TermPool, Binder, Operator, Rc, Sort,
        SortedVar, Substitution, Term,
    },
    checker::{budget::ExpansionBudget, error::QuantifierError},
    utils::DedupIterator,
};
use indexmap::{IndexMap, IndexSet};

pub fn forall_inst(
    RuleArgs {
        conclusion, args, pool, polyeq_time, ..
    }: RuleArgs,
) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (bindings, original, substituted) =
        match_term_err!((or (not (forall ... original)) result) = &conclusion[0])?;

    assert_num_args(args, bindings.len())?;

    // iterate over the bindings and arguments simultaneously, building the substitution
    let substitution: IndexMap<_, _> = bindings
        .iter()
        .zip(args)
        .map(|((var_name, sort), value)| {
            assert_eq(sort, &pool.sort(value))?;
            let var = pool.add(Term::new_var(var_name, sort.clone()));
            Ok((var.clone(), value.clone()))
        })
        .collect::<Result<_, CheckerError>>()?;
    let mut substitution = Substitution::new(pool, substitution)?;

    // Equalities may be reordered, and the application of the substitution might rename bound
    // variables, so we need to compare for alpha-equivalence here
    let expected = substitution.apply(pool, original);
    assert_alpha_equiv_expected(substituted, expected, polyeq_time)
}

pub fn qnt_join(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    let (q_1, bindings_1, left) = left.as_quant_err()?;
    let (q_2, bindings_2, left) = left.as_quant_err()?;
    let (q_3, bindings_3, right) = right.as_quant_err()?;

    assert_eq(&q_1, &q_2)?;
    assert_eq(&q_2, &q_3)?;
    assert_eq(left, right)?;

    let combined = bindings_1.iter().chain(bindings_2).dedup();
    rassert!(
        bindings_3.iter().eq(combined),
        QuantifierError::JoinFailed {
            left_outer: bindings_1.clone(),
            left_inner: bindings_2.clone(),
            right: bindings_3.clone()
        }
    );
    Ok(())
}

pub fn qnt_rm_unused(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    let (q_1, left, phi_1) = left.as_quant_err()?;
    let left: IndexSet<_> = left
        .iter()
        .map(|var| pool.add(var.clone().into()))
        .collect();

    let free_vars = pool.free_vars(phi_1);

    // If all variables can be removed, the right-hand side may be interpreted as just the inner
    // term phi
    if !left.iter().any(|v| free_vars.contains(v)) && phi_1 == right {
        return Ok(());
    }

    let (q_2, right, phi_2) = right.as_quant_err()?;
    assert_eq(&q_1, &q_2)?;
    assert_eq(phi_1, phi_2)?;

    let right: IndexSet<_> = right
        .iter()
        .map(|var| pool.add(var.clone().into()))
        .collect();

    // We need to ensure that:
    // (1) the right-hand bindings do not contain new variables
    if let Some(introduced) = right.difference(&left).next() {
        return Err(CheckerError::Quant(QuantifierError::NewBindingIntroduced(
            introduced.as_var().unwrap().to_owned(),
        )));
    }

    // and (2) that they only remove variables which are unused.
    for removed in left.difference(&right) {
        if free_vars.contains(removed) {
            return Err(CheckerError::Quant(QuantifierError::BindingIsMissing(
                removed.as_var().unwrap().to_owned(),
            )));
        }
    }
    Ok(())
}

/// Converts a term into negation normal form, expanding all connectives.
fn negation_normal_form(
    pool: &mut dyn TermPool,
    term: &Rc<Term>,
    polarity: bool,
    cache: &mut IndexMap<(Rc<Term>, bool), Rc<Term>>,
) -> Rc<Term> {
    if let Some(v) = cache.get(&(term.clone(), polarity)) {
        return v.clone();
    }

    let result = if let Some(inner) = match_term!((not t) = term) {
        negation_normal_form(pool, inner, !polarity, cache)
    } else if let Term::Op(op @ (Operator::And | Operator::Or), args) = term.as_ref() {
        let op = match (op, polarity) {
            (op, true) => *op,
            (Operator::And, false) => Operator::Or,
            (Operator::Or, false) => Operator::And,
            (_, false) => unreachable!(),
        };
        let args = args
            .iter()
            .map(|a| negation_normal_form(pool, a, polarity, cache))
            .collect();
        pool.add(Term::Op(op, args))
    } else if let Some((p, q)) = match_term!((=> p q) = term) {
        let a = negation_normal_form(pool, p, !polarity, cache);
        let b = negation_normal_form(pool, q, polarity, cache);

        match polarity {
            true => build_term!(pool, (or {a} {b})),
            false => build_term!(pool, (and {a} {b})),
        }
    } else if let Some((p, q, r)) = match_term!((ite p q r) = term) {
        let a = negation_normal_form(pool, p, !polarity, cache);
        let b = negation_normal_form(pool, q, polarity, cache);
        let c = negation_normal_form(pool, p, polarity, cache);
        let d = negation_normal_form(pool, r, polarity, cache);

        match polarity {
            true => build_term!(pool, (and (or {a} {b}) (or {c} {d}))),
            false => build_term!(pool, (or (and {a} {b}) (and {c} {d}))),
        }
    } else if let Some((quant, bindings, inner)) = term.as_quant() {
        let quant = if polarity { quant } else { !quant };
        let inner = negation_normal_form(pool, inner, polarity, cache);
        pool.add(Term::Binder(quant, bindings.clone(), inner))
    } else {
        match match_term!((= p q) = term) {
            Some((left, right)) if pool.sort(left).as_ref() == &Sort::Bool => {
                let a = negation_normal_form(pool, left, !polarity, cache);
                let b = negation_normal_form(pool, right, polarity, cache);
                let c = negation_normal_form(pool, right, !polarity, cache);
                let d = negation_normal_form(pool, left, polarity, cache);
                match polarity {
                    true => build_term!(pool, (and (or {a} {b}) (or {c} {d}))),
                    false => build_term!(pool, (or (and {a} {b}) (and {c} {d}))),
                }
            }
            _ => match polarity {
                true => term.clone(),
                false => build_term!(pool, (not {term.clone()})),
            },
        }
    };
    cache.insert((term.clone(), polarity), result.clone());
    result
}

/// This represents a formula in conjunctive normal form, that is, it is a conjunction of clauses,
/// which are disjunctions of literals
type CnfFormula = Vec<Vec<Rc<Term>>>;

/// Applies the distribution rules into a disjunction of formulas in conjunctive normal form. More
/// precisely, this takes the disjunction `P v Q v R v ...`, where
/// ```text
///     P = P_1 ^ P_2 ^ P_3 ^ ...
///     Q = Q_1 ^ Q_2 ^ Q_3 ^ ...
///     R = R_1 ^ R_2 ^ R_3 ^ ...
///     ...
/// ```
/// and returns the conjunction of all `(P_i v Q_j v R_k v ...)`, for every combination of `i`,
/// `j`, `k`, etc.
///
/// Modified in Clean: each clause of the result is built once, from the clauses it combines, in
/// the order upstream's recursion built them (the first formula's clause varying slowest). The
/// recursion recursed once per disjunct and copied each partial clause once per disjunct after it,
/// time quadratic in the width of a long disjunction. `qnt_cnf` charges the result before it is
/// built (see `cnf_cost`).
fn distribute(formulas: &[CnfFormula]) -> CnfFormula {
    let total = formulas
        .iter()
        .fold(1usize, |total, formula| total.saturating_mul(formula.len()));
    if formulas.is_empty() || total == 0 {
        return Vec::new();
    }
    let mut acc = Vec::with_capacity(total);
    // The clause each formula contributes, the last one's varying fastest.
    let mut chosen = vec![0; formulas.len()];
    loop {
        let parts = || chosen.iter().zip(formulas).map(|(&i, formula)| &formula[i]);
        let mut clause = Vec::with_capacity(parts().map(Vec::len).sum());
        for part in parts() {
            clause.extend(part.iter().cloned());
        }
        acc.push(clause);
        let mut k = formulas.len();
        loop {
            if k == 0 {
                return acc;
            }
            k -= 1;
            chosen[k] += 1;
            if chosen[k] < formulas[k].len() {
                break;
            }
            chosen[k] = 0;
        }
    }
}

/// Added in Clean: what `prenex_forall` and `conjunctive_normal_form` build from `term`, a term in
/// negation normal form, in words, counted over its DAG without building anything (saturating):
/// for each conjunction, disjunction and literal, once per path to it (none of the walks has a
/// cache), the conjunctive normal form it builds, a word per literal and one per clause; and for
/// each universal quantifier, once per path to it, `BINDING_WORDS` for each variable it binds,
/// which both prenexing walks copy. A disjunction's clauses are the product of its arguments', so
/// `(or (and a_1 b_1) ... (and a_n b_n))`, a few hundred bytes, has `2^n` clauses of `n` literals.
/// Every other node builds at least one clause of at least as many literals as the arguments a
/// prenexing walk rebuilds it with, so this also bounds the rest of those walks.
fn cnf_cost(term: &Rc<Term>) -> u128 {
    /// The words the two prenexing walks take to copy one bound variable (a name and a sort,
    /// twice). They copy a quantifier's variables once per path to it: 2,000 variables under a
    /// conjunction doubled 14 times (30 KB) took 1.5 GB.
    const BINDING_WORDS: u128 = 8;
    /// The clauses, the most literals in one of them, and the words built, by a node and the
    /// nodes under it.
    #[derive(Clone, Copy)]
    struct Shape {
        clauses: u128,
        widest: u128,
        built: u128,
    }
    fn children(term: &Term) -> &[Rc<Term>] {
        match term {
            Term::Op(Operator::And | Operator::Or, args) => args,
            Term::Binder(Binder::Forall, _, inner) => std::slice::from_ref(inner),
            _ => &[],
        }
    }
    let mut shapes: IndexMap<Rc<Term>, Shape> = IndexMap::new();
    let mut stack = vec![term.clone()];
    while let Some(node) = stack.last().cloned() {
        if shapes.contains_key(&node) {
            stack.pop();
            continue;
        }
        let pending: Vec<_> = children(&node)
            .iter()
            .filter(|child| !shapes.contains_key(*child))
            .cloned()
            .collect();
        if !pending.is_empty() {
            stack.extend(pending);
            continue;
        }
        stack.pop();
        let parts = children(&node).iter().map(|child| shapes[child]);
        let below = parts.clone().fold(0u128, |n, p| n.saturating_add(p.built));
        let (clauses, widest) = match node.as_ref() {
            Term::Op(Operator::And, _) => parts.fold((0u128, 0u128), |(c, w), p| {
                (c.saturating_add(p.clauses), w.max(p.widest))
            }),
            Term::Op(Operator::Or, _) => parts.fold((1u128, 0u128), |(c, w), p| {
                (c.saturating_mul(p.clauses), w.saturating_add(p.widest))
            }),
            Term::Binder(Binder::Forall, ..) => {
                let inner = shapes[&children(&node)[0]];
                (inner.clauses, inner.widest)
            }
            _ => (1, 1),
        };
        let here = match node.as_ref() {
            Term::Binder(Binder::Forall, bindings, _) => {
                (bindings.len() as u128).saturating_mul(BINDING_WORDS)
            }
            _ => clauses.saturating_mul(widest.saturating_add(1)),
        };
        let built = below.saturating_add(here);
        shapes.insert(node, Shape { clauses, widest, built });
    }
    shapes[term].built
}

/// Prenex all universal quantifiers in a term. This doesn't prenex existential quantifiers. This
/// assumes the term is in negation normal form.
fn prenex_forall<C>(pool: &mut dyn TermPool, acc: &mut C, term: &Rc<Term>) -> Rc<Term>
where
    C: Extend<SortedVar>,
{
    match term.as_ref() {
        // This function assumes that the term is already in negation normal form, so any term
        // other than a conjunction, disjunction, or a universal quantifier is considered a literal
        Term::Op(op @ (Operator::And | Operator::Or), args) => {
            let args = args.iter().map(|a| prenex_forall(pool, acc, a)).collect();
            pool.add(Term::Op(*op, args))
        }
        Term::Binder(Binder::Forall, bindings, inner) => {
            acc.extend(bindings.iter().cloned());
            prenex_forall(pool, acc, inner)
        }
        _ => term.clone(),
    }
}

/// Converts a term into a formula in conjunctive normal form. This assumes the term is already in
/// negation normal form.
fn conjunctive_normal_form(term: &Rc<Term>) -> CnfFormula {
    match term.as_ref() {
        Term::Op(Operator::And, args) => {
            // If the term is a conjunction, we just convert every argument into conjunctive normal
            // form, and flatten the result
            args.iter().flat_map(conjunctive_normal_form).collect()
        }
        Term::Op(Operator::Or, args) => {
            // If the term is a disjunction, we have to convert every argument into conjunctive
            // normal form and then apply the distribution rules
            let args: Vec<_> = args.iter().map(conjunctive_normal_form).collect();
            distribute(&args)
        }
        // Every other term is considered a literal
        _ => vec![vec![term.clone()]],
    }
}

pub fn qnt_cnf(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (l_bindings, phi, r_bindings, phi_prime) = {
        let (l, r) = match_term_err!((or (not l) r) = &conclusion[0])?;
        let (l_q, l_b, phi) = l.as_quant_err()?;
        let (r_q, r_b, phi_prime) = r.as_quant_err()?;

        // We expect both quantifiers to be `forall`
        assert_is_expected(&l_q, Binder::Forall)?;
        assert_is_expected(&r_q, Binder::Forall)?;

        (l_b, phi, r_b, phi_prime)
    };

    let r_bindings = r_bindings.iter().cloned().collect::<IndexSet<_>>();
    let mut new_bindings = l_bindings.iter().cloned().collect::<IndexSet<_>>();
    let appears = {
        let nnf = negation_normal_form(pool, phi, true, &mut IndexMap::new());

        // Modified in Clean: the conjunctive normal form, and the prenexing walks before it, are
        // charged to the step's budget before they run, and a step past it is refused: a
        // disjunction of `n` conjunctions has `2^n` clauses (`n` = 26, a 605-byte step, grew past
        // 6 GB). See `cnf_cost`, checker/budget.rs and third-party/carcara/DOWNSTREAM.md,
        // "Bit-vector expansion has a resource budget".
        ExpansionBudget::new()
            .spend_words("converting to conjunctive normal form", cnf_cost(&nnf))?;

        // Modified in Clean: moving a universal quantifier out of a conjunction or disjunction is
        // only valid if its variable does not occur free elsewhere. `(or (forall ((x Int)) P) Q)`
        // with `x` free in `Q` is not `(forall ((x Int)) (or P Q))`. Refuse when a variable
        // pulled out by prenexing is free in `phi` at all (see third-party/carcara/DOWNSTREAM.md).
        let free = pool.free_vars(phi);
        let mut pulled = Vec::new();
        prenex_forall(pool, &mut pulled, &nnf);
        if let Some((var, _)) = pulled.iter().find(|(name, _)| free.contains_name(name)) {
            return Err(CheckerError::Explanation(format!(
                "prenexing the quantifier over '{}' would capture a free occurrence of it",
                var
            )));
        }

        let prenexed = prenex_forall(pool, &mut new_bindings, &nnf);
        let cnf = conjunctive_normal_form(&prenexed);
        // Modified in Clean: each clause is compared with `phi_prime` as the term it would be,
        // without being added to the pool, where every clause stayed for the rest of the proof
        // though the conclusion names one. The pool would have returned `phi_prime` itself for
        // a clause equal to it, so the comparison is the one upstream made.
        cnf.iter().any(|c| match c.as_slice() {
            [] => false,
            [term] => term == phi_prime,
            _ => matches!(phi_prime.as_ref(), Term::Op(Operator::Or, args) if args == c),
        })
    };

    // `new_bindings` contains all bindings that existed in the original term, plus all bindings
    // added by the prenexing step. All bindings in the right side must be in this set
    if let Some((var, _)) = r_bindings.iter().find(|&b| !new_bindings.contains(b)) {
        return Err(CheckerError::Quant(QuantifierError::NewBindingIntroduced(
            var.clone(),
        )));
    }

    if !appears {
        return Err(QuantifierError::ClauseDoesntAppearInCnf(phi_prime.clone()).into());
    }

    // Cloning here may be unnecessary
    // Modified in Clean: the selected clause is `phi_prime` (see above).
    let free_vars = pool.free_vars(phi_prime);

    // While all bindings in `r_bindings` must also be in `new_bindings`, the same is not true in
    // the opposite direction. That is because some variables from the set may be omitted in the
    // right-hand side quantifier if they don't appear in `phi_prime` as free variables.  If there
    // is a binding in the left side that is a free variable in the selected clause, but doesn't
    // appear in the right-hand side bindings, we must return an error
    let found = new_bindings
        .into_iter()
        .find(|var| !r_bindings.contains(var) && free_vars.contains(&pool.add(var.clone().into())));
    if let Some((var, _)) = found {
        return Err(QuantifierError::BindingIsMissing(var).into());
    }
    Ok(())
}

pub fn miniscope_distribute(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (op, bindings, phis, right_args) =
        match_term_err!((= (forall ... (and ...)) (and ...)) = &conclusion[0])
            .map(|(bindings, phis, right_args)| (Operator::And, bindings, phis, right_args))
            .or_else(|_| {
                match_term_err!((= (exists ... (or ...)) (or ...)) = &conclusion[0])
                    .map(|(bindings, phis, right_args)| (Operator::Or, bindings, phis, right_args))
            })?;
    assert_operation_len(op, right_args, phis.len())?;
    for (phi, right) in phis.iter().zip(right_args) {
        let (b, inner) = match op {
            Operator::And => match_term_err!((forall ... phi) = right)?,
            Operator::Or => match_term_err!((exists ... phi) = right)?,
            _ => unreachable!(),
        };
        assert_eq(bindings, b)?;
        assert_eq(phi, inner)?;
    }
    Ok(())
}

pub fn miniscope_split(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (op, bindings, phis, right_args) =
        match_term_err!((= (forall ... (or ...)) (or ...)) = &conclusion[0])
            .map(|(bindings, phis, right_args)| (Operator::Or, bindings, phis, right_args))
            .or_else(|_| {
                match_term_err!((= (exists ... (and ...)) (and ...)) = &conclusion[0])
                    .map(|(bindings, phis, right_args)| (Operator::And, bindings, phis, right_args))
            })?;
    assert_operation_len(op, right_args, phis.len())?;

    let mut bindings_set: IndexSet<_> = bindings.iter().collect();
    for (phi, right) in phis.iter().zip(right_args) {
        // `right` is the same as `phi`, it must have no bound variables from the quantifier being
        // split, which is checked afterwards.
        if phi == right {
            continue;
        }
        // Otherwise an appropriate binder must have been put around `right` and its variables must
        // be from the bindings_set in the LHS of the conclusion
        let (inner_bindings, inner) = match op {
            Operator::Or => match_term_err!((forall ... phi) = right)?,
            Operator::And => match_term_err!((exists ... phi) = right)?,
            _ => unreachable!(),
        };
        assert_eq(phi, inner)?;
        for b in inner_bindings {
            if !bindings_set.swap_remove(b) {
                return Err(QuantifierError::NewBindingIntroduced(b.0.clone()).into());
            }
        }
    }

    let right_term = pool.add(Term::Op(op, right_args.to_vec()));
    let free_vars = pool.free_vars(&right_term);
    for v in bindings {
        if free_vars.contains(&pool.add(v.clone().into())) {
            return Err(QuantifierError::MiniscopeFreeVar(v.0.clone(), right_term).into());
        }
    }

    Ok(())
}

pub fn miniscope_ite(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (bindings_1, phi1, _, _, bindings_2, bindings_3) = match_term_err!(
        (= (forall ... (ite phi1 phi2 phi3)) (ite phi1 (forall ... phi2) (forall ... phi3)))
        = &conclusion[0]
    )?;
    assert_eq(bindings_1, bindings_2)?;
    assert_eq(bindings_1, bindings_3)?;
    let free_vars = pool.free_vars(phi1);
    for v in bindings_1 {
        if free_vars.contains(&pool.add(v.clone().into())) {
            return Err(QuantifierError::MiniscopeFreeVar(v.0.clone(), phi1.clone()).into());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn conjunctive_normal_form() {
        use super::*;
        use crate::parser::tests::*;

        fn to_cnf_term(pool: &mut dyn TermPool, term: &Rc<Term>) -> Rc<Term> {
            let nnf = negation_normal_form(pool, term, true, &mut IndexMap::new());
            let mut bindings = Vec::new();
            let prenexed = prenex_forall(pool, &mut bindings, &nnf);
            let cnf = conjunctive_normal_form(&prenexed);
            let mut clauses: Vec<_> = cnf
                .into_iter()
                .map(|c| match c.as_slice() {
                    [] => unreachable!(),
                    [term] => term.clone(),
                    _ => pool.add(Term::Op(Operator::Or, c)),
                })
                .collect();

            let conjunctions = if clauses.len() == 1 {
                clauses.pop().unwrap()
            } else {
                pool.add(Term::Op(Operator::And, clauses))
            };

            if bindings.is_empty() {
                conjunctions
            } else {
                pool.add(Term::Binder(
                    Binder::Forall,
                    crate::ast::BindingList(bindings),
                    conjunctions,
                ))
            }
        }

        fn run_tests(definitions: &str, cases: &[(&str, &str)]) {
            for &(term, expected) in cases {
                let mut pool = crate::ast::pool::PrimitivePool::new();
                let [term, expected] = parse_terms(&mut pool, definitions, [term, expected]);
                let got = to_cnf_term(&mut pool, &term);
                assert_eq!(expected, got);
            }
        }

        let definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun a () Real)
            (declare-fun b () Real)
        ";
        let cases = [
            // Cases that only need the negation normal form to be computed
            ("(not (and p q r))", "(or (not p) (not q) (not r))"),
            ("(not (not p))", "p"),
            ("(=> p q)", "(or (not p) q)"),
            ("(not (=> p q))", "(and p (not q))"),
            ("(= p q)", "(and (or (not p) q) (or (not q) p))"),
            ("(ite p q r)", "(and (or (not p) q) (or p r))"),
            // Cases that require prenexing
            (
                "(or (forall ((x Int)) (= 0 x)) (forall ((y Int)) (= 1 y)))",
                "(forall ((x Int) (y Int)) (or (= 0 x) (= 1 y)))",
            ),
            (
                "(and (exists ((x Int)) (= 0 x)) (forall ((y Int)) (= 1 y)))",
                "(forall ((y Int)) (and (exists ((x Int)) (= 0 x)) (= 1 y)))",
            ),
            (
                "(=> (exists ((x Int)) (= x x)) p)",
                "(forall ((x Int)) (or (not (= x x)) p))",
            ),
            // Cases where the distribution rules must be applied
            ("(or p (and q r))", "(and (or p q) (or p r))"),
            (
                "(or (and p q) (and r s))",
                "(and (or p r) (or p s) (or q r) (or q s))",
            ),
            ("(or p (or q r) s)", "(or p q r s)"),
            ("(and p (and q r) s)", "(and p q r s)"),
            (
                "(not (and
                    (=> (forall ((x Int)) (= x 0)) p)
                    (or q (not (not r)))
                    (or s (not (exists ((y Int)) (< y 0))))
                ))",
                "(forall ((x Int)) (and
                    (or (= x 0) (not q) (not s))
                    (or (= x 0) (not q) (exists ((y Int)) (< y 0)))
                    (or (= x 0) (not r) (not s))
                    (or (= x 0) (not r) (exists ((y Int)) (< y 0)))
                    (or (not p) (not q) (not s))
                    (or (not p) (not q) (exists ((y Int)) (< y 0)))
                    (or (not p) (not r) (not s))
                    (or (not p) (not r) (exists ((y Int)) (< y 0)))
                ))",
            ),
        ];
        run_tests(definitions, &cases);
    }
}

/// Added in Clean: `distribute` builds what upstream's recursion built, and `cnf_cost` counts at
/// least what the conversion builds.
#[cfg(test)]
mod clean_tests {
    use super::*;
    use crate::parser::tests::*;

    /// Upstream's `distribute`, verbatim.
    fn upstream_distribute(formulas: &[CnfFormula]) -> CnfFormula {
        match formulas {
            [formula] => formula.clone(),
            [] => unreachable!(),
            [head, tail @ ..] => {
                let tail = upstream_distribute(tail);
                let mut acc = Vec::with_capacity(head.len() * tail.len());
                for head_clause in head {
                    for tail_clause in &tail {
                        let mut result = Vec::with_capacity(head_clause.len() + tail_clause.len());
                        result.extend(head_clause.iter().cloned());
                        result.extend(tail_clause.iter().cloned());
                        acc.push(result);
                    }
                }
                acc
            }
        }
    }

    #[test]
    fn distribute_builds_the_clauses_upstreams_recursion_built() {
        let mut pool = crate::ast::pool::PrimitivePool::new();
        let bool_sort = pool.add_sort(Sort::Bool);
        let atoms: Vec<Rc<Term>> = (0..8)
            .map(|i| pool.add(Term::new_var(format!("p{i}"), bool_sort.clone())))
            .collect();
        // Formulas of 0 to 3 clauses of 1 to 3 literals, combined 1 to 4 at a time.
        let mut formulas: Vec<CnfFormula> = Vec::new();
        for shape in 0..64usize {
            let clauses = shape % 4;
            formulas.push(
                (0..clauses)
                    .map(|c| {
                        let width = 1 + (shape / 4 + c) % 3;
                        (0..width)
                            .map(|l| atoms[(shape + c + l) % 8].clone())
                            .collect()
                    })
                    .collect(),
            );
        }
        let mut checked = 0;
        for n in 1..=4usize {
            for start in 0..formulas.len() - n {
                let slice = &formulas[start..start + n];
                assert_eq!(distribute(slice), upstream_distribute(slice));
                checked += 1;
            }
        }
        assert!(checked > 200);
    }

    #[test]
    fn cnf_cost_counts_at_least_what_the_conversion_builds() {
        let definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ";
        let cases = [
            "p",
            "(or p q r)",
            "(and p q r)",
            "(or (and p q) (and r s))",
            "(or p (and q r) (forall ((x Int)) (and s (= x 0))))",
            "(and (or p (and q r)) (or (and p s) (and q r)))",
            "(or (! (and p q) :named a) a a)",
            "(=> (exists ((x Int)) (= x x)) (or p (and q (or r s))))",
            "(= p (= q (= r s)))",
        ];
        for case in cases {
            let mut pool = crate::ast::pool::PrimitivePool::new();
            let [term] = parse_terms(&mut pool, definitions, [case]);
            let nnf = negation_normal_form(&mut pool, &term, true, &mut IndexMap::new());
            let mut bindings = Vec::new();
            let prenexed = prenex_forall(&mut pool, &mut bindings, &nnf);
            let cnf = conjunctive_normal_form(&prenexed);
            let clauses = cnf.len() as u128;
            let widest = cnf.iter().map(Vec::len).max().unwrap_or(0) as u128;
            assert!(cnf_cost(&nnf) >= clauses * (widest + 1), "{case}");
        }
        // A quantifier is charged its variables once per path to it.
        let mut pool = crate::ast::pool::PrimitivePool::new();
        let [shared] = parse_terms(
            &mut pool,
            definitions,
            ["(and (! (forall ((x Int) (y Int) (z Int)) p) :named f) f)"],
        );
        assert_eq!(cnf_cost(&shared), 2 * (3 * 8 + 2) + 2 * 2);
        // A disjunction of `n` conjunctions of two: `2^n` clauses of `n` literals, each
        // conjunction's two clauses and each literal's one.
        let n = 6;
        let mut pool = crate::ast::pool::PrimitivePool::new();
        let names: String = (0..n)
            .map(|i| format!("(declare-fun a{i} () Bool)(declare-fun b{i} () Bool)"))
            .collect();
        let phi: String = (0..n).map(|i| format!(" (and a{i} b{i})")).collect();
        let [term] = parse_terms(&mut pool, &names, [&format!("(or{phi})")]);
        assert_eq!(cnf_cost(&term), (1 << n) * (n + 1) + 8 * n);
    }
}
