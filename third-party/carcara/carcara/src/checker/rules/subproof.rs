use super::{
    assert_clause_len, assert_eq, assert_is_expected, assert_num_premises, assert_polyeq,
    get_premise_term, CheckerError, EqualityError, RuleArgs, RuleResult,
};
use crate::{
    ast::{pool::TermPool, *},
    checker::{error::SubproofError, scoping},
};
use indexmap::{IndexMap, IndexSet};
use std::collections::{HashMap, HashSet};

pub fn subproof(
    RuleArgs {
        conclusion,
        pool,
        previous_command,
        discharge,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, discharge.len() + 1)?;

    for (assumption, t) in discharge.iter().zip(conclusion) {
        match assumption {
            ProofCommand::Assume { id: _, term } => {
                let t = t.remove_negation_err()?;
                assert_polyeq(term, t, polyeq_time)?;
            }
            other => return Err(SubproofError::DischargeMustBeAssume(other.id().to_owned()).into()),
        }
    }

    let phi = match previous_command.clause {
        // If the last command has an empty clause as it's conclusion, we expect `phi` to be the
        // boolean constant `false`
        [] => pool.bool_false(),
        [t] => t.clone(),
        other => {
            return Err(CheckerError::WrongLengthOfPremiseClause(
                previous_command.id.to_owned(),
                (..2).into(),
                other.len(),
            ))
        }
    };

    assert_polyeq(conclusion.last().unwrap(), &phi, polyeq_time)
}

pub fn bind(
    RuleArgs {
        conclusion,
        pool,
        context,
        previous_command,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;

    let (phi, phi_prime) = match_term_err!((= p q) = get_premise_term(&previous_command)?)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    let (l_binder, l_bindings, left) = left.as_binder_err()?;
    let (r_binder, r_bindings, right) = right.as_binder_err()?;
    assert_eq(&l_binder, &r_binder)?;

    let [l_bindings, r_bindings] = [l_bindings, r_bindings].map(|b| {
        b.iter()
            .map(|var| pool.add(var.clone().into()))
            .collect::<IndexSet<_>>()
    });

    // The terms in the quantifiers must be phi and phi'
    assert_eq(left, phi)?;
    assert_eq(right, phi_prime)?;

    // None of the bindings in the right side can appear as free variables in phi
    let free_vars = pool.free_vars(phi);
    if let Some(y) = r_bindings
        .iter()
        .find(|&y| free_vars.contains(y) && !l_bindings.contains(y))
    {
        let y = y.as_var().unwrap().to_owned();
        return Err(SubproofError::BindBindingIsFreeVarInPhi(y).into());
    }

    // Since we are closing a subproof, we only care about the substitutions that were introduced
    // in it
    let context = context.last().unwrap();
    let context = context.as_ref().unwrap();

    let (xs, ys, renaming): (IndexSet<_>, IndexSet<_>, Vec<(Rc<Term>, Rc<Term>)>) = {
        let (mut xs, mut ys, mut renaming) = (IndexSet::new(), IndexSet::new(), Vec::new());
        for arg in &context.args {
            match arg {
                AnchorArg::Variable((name, _)) if !xs.is_empty() => {
                    return Err(SubproofError::BindUnexpectedVarArgument(name.clone()).into());
                }
                AnchorArg::Variable(var) => {
                    ys.insert(pool.add(var.clone().into()));
                }
                AnchorArg::Assign(var, value) => {
                    let x = pool.add(var.clone().into());
                    xs.insert(x.clone());
                    renaming.push((x, value.clone()));
                }
            }
        }
        (xs, ys, renaming)
    };

    // Modified in Clean: `bind` renames the bound variables `x_i` into the context variables
    // `y_i`, so each substituted `x_i` must be bound on the left, each `y_i` must be a distinct
    // context variable bound on the right, and every other binding must be the same unsubstituted
    // context variable on both sides. Before, `(forall ((y U)) (P x))` = `(forall ((y U)) (P y))`
    // was accepted: `x` is free on the left, so renaming it changes the formula (see
    // third-party/carcara/DOWNSTREAM.md).
    {
        let mut images = IndexSet::new();
        for (x, y) in &renaming {
            if !y.is_var() || !ys.contains(y) || !images.insert(y.clone()) {
                return Err(CheckerError::Explanation(format!(
                    "'{}' must be renamed to a distinct context variable, not '{}'",
                    x, y
                )));
            }
            if !l_bindings.contains(x) {
                let x = x.as_var().unwrap().to_owned();
                return Err(SubproofError::BindingIsNotInContext(x).into());
            }
            if !r_bindings.contains(y) {
                let y = y.as_var().unwrap().to_owned();
                return Err(SubproofError::BindingIsNotInContext(y).into());
            }
        }
        // Modified in Clean: the step inside the anchor only holds where each `x_i` equals its
        // `y_i`. That is enough to rename `x_i` into `y_i` only when `y_i` is not also bound on the
        // left (otherwise only the diagonal `x_i = y_i` of the left formula is covered), and when
        // `x_i` does not occur free in `phi'` (the enclosing proof would read it as a different
        // variable). Identity renamings `(:= (x S) x)` constrain nothing.
        let left_names: HashSet<&str> = l_bindings.iter().filter_map(|v| v.as_var()).collect();
        for (x, y) in &renaming {
            if x != y && y.as_var().is_some_and(|name| left_names.contains(name)) {
                return Err(CheckerError::Explanation(format!(
                    "'{}' is renamed to '{}', which is also bound on the left",
                    x, y
                )));
            }
        }
        scoping::check_not_exported(pool, &context.args, phi_prime)?;

        let domain: IndexSet<_> = renaming.iter().map(|(x, _)| x.clone()).collect();
        let left_rest: IndexSet<_> = l_bindings.difference(&domain).cloned().collect();
        let right_rest: IndexSet<_> = r_bindings.difference(&images).cloned().collect();
        if left_rest != right_rest || left_rest.iter().any(|z| !ys.contains(z)) {
            return Err(CheckerError::Explanation(
                "bindings that are not renamed must be the same context variables on both sides"
                    .to_owned(),
            ));
        }
    }

    rassert!(
        l_bindings.len() == r_bindings.len(),
        SubproofError::BindDifferentNumberOfBindings(l_bindings.len(), r_bindings.len())
    );

    // Modified in Clean: the right-hand difference was `r_bindings - r_bindings`, which is always
    // empty, so right-hand bindings were never checked against the context and a binder over a
    // variable absent from the context was accepted (see third-party/carcara/DOWNSTREAM.md).
    let (l_bindings, r_bindings): (IndexSet<_>, IndexSet<_>) = (
        l_bindings.difference(&r_bindings).cloned().collect(),
        r_bindings.difference(&l_bindings).cloned().collect(),
    );

    // `l_bindings` should be a subset of `xs` and `r_bindigns` should be a subset of `ys`
    if let Some(x) = l_bindings.iter().find(|&x| !xs.contains(x)) {
        let x = x.as_var().unwrap().to_owned();
        return Err(SubproofError::BindingIsNotInContext(x).into());
    }
    if let Some(y) = r_bindings.iter().find(|&y| !ys.contains(y)) {
        let y = y.as_var().unwrap().to_owned();
        return Err(SubproofError::BindingIsNotInContext(y).into());
    }
    Ok(())
}

pub fn r#let(
    RuleArgs {
        conclusion,
        context,
        premises,
        pool,
        previous_command,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;

    // Since we are closing a subproof, we only care about the mappings that were introduced in it
    let context = context.last().unwrap();
    let args = &context.as_ref().unwrap().args;
    let mappings: IndexMap<Rc<Term>, Rc<Term>> = args
        .iter()
        .filter_map(|arg| {
            let (name, value) = arg.as_assign()?;
            let var = Term::new_var(name, pool.sort(value));
            Some((pool.add(var), value.clone()))
        })
        .collect();

    let (let_term, u_prime) = match_term_err!((= l u) = &conclusion[0])?;
    let Term::Let(let_bindings, u) = let_term.as_ref() else {
        return Err(CheckerError::TermOfWrongForm("(let ...)", let_term.clone()));
    };

    // The u and u' in the conclusion must match the u and u' in the previous command in the
    // subproof
    let previous_term = get_premise_term(&previous_command)?;

    let (previous_u, previous_u_prime) = match_term_err!((= u u_prime) = previous_term)?;
    assert_eq(u, previous_u)?;
    assert_eq(u_prime, previous_u_prime)?;

    rassert!(
        let_bindings.len() == mappings.len(),
        SubproofError::WrongNumberOfLetBindings(mappings.len(), let_bindings.len())
    );

    let mut pairs: Vec<_> = let_bindings
        .iter()
        .map(|(x, t)| {
            let sort = pool.sort(t);
            let x_term = pool.add((x.clone(), sort).into());
            let s = mappings
                .get(&x_term)
                .ok_or_else(|| SubproofError::BindingIsNotInContext(x.clone()))?;
            Ok((s, t))
        })
        .collect::<Result<_, CheckerError>>()?;
    // Modified in Clean: the premises `r_i = s_i` are proved outside the anchor, and `let` binds
    // in parallel, so an assigned value `s_i` may not mention any variable the anchor assigns.
    // The right-hand side `u'` is exported, so it may not mention one either. Before,
    // `(= (let ((x a)) (P x)) (P x))` was accepted from `(= (P x) (P x))` under `(:= (x U) a)`
    // (see third-party/carcara/DOWNSTREAM.md).
    {
        let assigned: HashSet<&str> = args
            .iter()
            .filter(|arg| !scoping::is_identity_assign(arg))
            .filter_map(|arg| arg.as_assign().map(|(name, _)| name.as_str()))
            .collect();
        for arg in args {
            if let (Some((name, value)), false) =
                (arg.as_assign(), scoping::is_identity_assign(arg))
            {
                if let Some(var) = scoping::free_var_named(pool, value, &assigned) {
                    return Err(CheckerError::Explanation(format!(
                        "the value assigned to '{}' mentions '{}', which the anchor also assigns",
                        name, var
                    )));
                }
            }
        }
        scoping::check_not_exported(pool, args, u_prime)?;
    }

    pairs.retain(|(s, t)| s != t); // The pairs where s == t don't need a premise to justify them

    assert_num_premises(premises, pairs.len())?;

    for (premise, (s, t)) in premises.iter().zip(pairs) {
        let (a, b) = match_term_err!((= a b) = get_premise_term(premise)?)?;
        rassert!(
            (a, b) == (s, t) || (a, b) == (t, s),
            SubproofError::PremiseDoesntJustifyLet {
                substitution: (s.clone(), t.clone()),
                premise: (a.clone(), b.clone()),
            }
        );
    }
    Ok(())
}

// Modified in Clean: a point may only be read in the scope the eliminated variable is bound in.
// `find_points` descended through nested binders keeping the points it found under them, so a
// `(= x t)` under a binder that *rebinds* `x`, or whose `t` mentions a variable that binder binds,
// was harvested as if it constrained the outer `x`. Under `(:= (x Bool) t)`,
// `(forall ((x Bool)) (=> (exists ((x Bool)) (= x t)) (= x p)))` was accepted as equal to
// `(=> (exists ((x Bool)) (= x t)) (= t p))` (see third-party/carcara/DOWNSTREAM.md). The bound
// variables of the enclosing binders are now tracked, a point whose variable is shadowed is
// dropped, and a point whose term mentions a locally bound variable is dropped as well — that
// term is exported into the anchor's assignment, where those variables do not exist.
fn extract_points(
    pool: &mut dyn TermPool,
    quant: Binder,
    term: &Rc<Term>,
) -> HashSet<(String, Rc<Term>)> {
    fn find_points(
        pool: &mut dyn TermPool,
        acc: &mut HashSet<(String, Rc<Term>)>,
        seen: &mut HashSet<(Rc<Term>, bool, Vec<String>)>,
        scope: &mut Vec<String>,
        polarity: bool,
        term: &Rc<Term>,
    ) {
        // The scope is part of the key: the same subterm yields different points under different
        // binders, so a result found in one scope may not be reused in another.
        let key = (term.clone(), polarity, scope.clone());
        if seen.contains(&key) {
            return;
        }
        seen.insert(key);

        if let Some(inner) = term.remove_negation() {
            return find_points(pool, acc, seen, scope, !polarity, inner);
        }
        if let Some((_, bindings, inner)) = term.as_quant() {
            let depth = scope.len();
            scope.extend(bindings.iter().map(|(name, _)| name.clone()));
            find_points(pool, acc, seen, scope, polarity, inner);
            scope.truncate(depth);
            return;
        }
        match polarity {
            true => {
                if let Some((a, b)) = match_term!((= a b) = term) {
                    let insert = |acc: &mut HashSet<(String, Rc<Term>)>,
                                  pool: &mut dyn TermPool,
                                  x: &Rc<Term>,
                                  t: &Rc<Term>| {
                        let Some(name) = x.as_var() else { return };
                        if scope.iter().any(|bound| bound == name) {
                            return; // the point's variable is shadowed here
                        }
                        let free = pool.free_vars(t);
                        let escapes = scope.iter().any(|bound| free.contains_name(bound));
                        if escapes {
                            return; // the point's term mentions a variable bound here
                        }
                        acc.insert((name.to_owned(), t.clone()));
                    };
                    insert(acc, pool, a, b);
                    insert(acc, pool, b, a);
                } else if let Some(args) = match_term!((and ...) = term) {
                    for a in args {
                        find_points(pool, acc, seen, scope, true, a);
                    }
                }
            }
            false => {
                if let Some((p, q)) = match_term!((=> p q) = term) {
                    find_points(pool, acc, seen, scope, true, p);
                    find_points(pool, acc, seen, scope, false, q);
                } else if let Some(args) = match_term!((or ...) = term) {
                    for a in args {
                        find_points(pool, acc, seen, scope, false, a);
                    }
                }
            }
        }
    }

    let mut result = HashSet::new();
    let mut seen = HashSet::new();
    let mut scope = Vec::new();
    find_points(
        pool,
        &mut result,
        &mut seen,
        &mut scope,
        quant == Binder::Exists,
        term,
    );
    result
}

pub fn onepoint(
    RuleArgs {
        conclusion,
        context,
        pool,
        previous_command,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    let (quant, l_bindings, left) = left.as_quant_err()?;
    let (r_bindings, right) = match right.as_quant() {
        Some((q, b, t)) => {
            assert_eq(&q, &quant)?;
            (b, t)
        }
        // If the right-hand side term is not a quantifier, that possibly means all quantifier
        // bindings were removed, so we consider it a quantifier with an empty list of bindings
        None => (BindingList::EMPTY, right),
    };

    let previous_term = get_premise_term(&previous_command)?;
    let previous_equality = match_term_err!((= p q) = previous_term)?;
    rassert!(
        previous_equality == (left, right) || previous_equality == (right, left),
        EqualityError::ExpectedToBe {
            expected: previous_term.clone(),
            got: conclusion[0].clone()
        }
    );

    let raw_points = extract_points(pool, quant, left);

    // Modified in Clean: a point `(= x t)` only eliminates `x` when `t` does not depend on `x` or
    // on any variable eliminated after it. The substitution used to be applied to the point first,
    // so under `(:= (x U) a)` the point `(= x x)` became `(= x a)` and
    // `(forall ((x U)) (=> (= x x) (P x)))` was accepted as equal to `(P a)` (see
    // third-party/carcara/DOWNSTREAM.md). Points are now checked in the order of the anchor's
    // assignments, and only earlier eliminated variables may occur in them (a triangular system).
    let assignments: Vec<(String, Rc<Term>)> = {
        let context = context.last().unwrap();
        let context = context.as_ref().unwrap();
        context
            .args
            .iter()
            .filter_map(AnchorArg::as_assign)
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    };
    for (i, (k, v)) in assignments.iter().enumerate() {
        let later: HashSet<&str> = assignments[i..]
            .iter()
            .map(|(name, _)| name.as_str())
            .collect();
        let mut justified = false;
        for (x, t) in raw_points.iter().filter(|(x, _)| x == k) {
            let _ = x;
            let free = pool.free_vars(t);
            if later.iter().any(|name| free.contains_name(name)) {
                continue;
            }
            // Since a substitution may use a variable introduced in a previous substitution, we
            // apply the substitution to the point in order to replace these variables by their
            // value.
            if context.apply(pool, t) == *v {
                justified = true;
                break;
            }
        }
        if !justified {
            return Err(SubproofError::NoPointForSubstitution(k.clone(), v.clone()).into());
        }
    }

    let context = context.last().unwrap();
    let context = context.as_ref().unwrap();

    // Modified in Clean: the eliminated variables are only equal to their points inside the
    // anchor, so they may not occur free in the exported right-hand side. Before,
    // `(= (forall ((x U)) (=> (= x a) (P x))) (=> (= a a) (P x)))` was accepted (see
    // third-party/carcara/DOWNSTREAM.md).
    scoping::check_not_exported(pool, &context.args, right)?;

    // Here we check that the right variables were eliminated. Using the notation in the
    // specification, we have that:
    //
    // - `var_args` are the x_k_1, ..., x_k_m variables that appear as the variable arguments to the
    // anchor
    // - `point_vars` are the x_j_1, ..., x_j_o variables that appear as the left-hand side of the
    // assign arguments in the anchor
    // - `l_bindings` are the x_1, ..., x_n variables in the binding list of the left-hand
    // quantifier
    // - `r_bindings` are the x_k_1, ..., x_k_m variables in the binding list of the right-hand
    // quantifier
    //
    // We must then make sure that `var_args == r_bindings`, and that
    // `union(var_args, point_vars) == l_bindings`.
    let var_args: Vec<_> = context
        .args
        .iter()
        .filter_map(AnchorArg::as_variable)
        .cloned()
        .collect();

    let mappings = context.args.iter().filter_map(AnchorArg::as_assign);
    let point_vars: Vec<_> = mappings
        .map(|(name, value)| (name.clone(), pool.sort(value)))
        .collect();
    let point_vars: HashSet<_> = point_vars.iter().collect();

    if var_args != r_bindings.as_ref() {
        return Err(SubproofError::OnepointWrongRightBindings(BindingList(var_args)).into());
    }

    let l_bindings: HashSet<_> = l_bindings.iter().collect();

    // Convert `var_args` into a set so we can do union operation
    let var_args: HashSet<_> = var_args.iter().collect();

    let expected = &var_args | &point_vars;
    if l_bindings != expected {
        let expected: Vec<_> = expected.into_iter().cloned().collect();
        return Err(SubproofError::OnepointWrongLeftBindings(BindingList(expected)).into());
    }

    Ok(())
}

fn generic_skolemization_rule(
    rule_type: Binder,
    RuleArgs {
        conclusion,
        pool,
        context,
        previous_command,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;

    let (left, psi) = match_term_err!((= l r) = &conclusion[0])?;

    let (quant, bindings, phi) = left.as_quant_err()?;
    assert_is_expected(&quant, rule_type)?;

    let previous_term = get_premise_term(&previous_command)?;
    let previous_equality = match_term_err!((= p q) = previous_term)?;
    assert_eq(previous_equality.0, phi)?;
    assert_eq(previous_equality.1, psi)?;

    let mut current_phi = phi.clone();
    if context.len() >= 2 {
        current_phi = context.apply_previous(pool, &current_phi);
    }

    let context = context.last().unwrap();

    // Modified in Clean: the skolemized variables are only equal to their choice terms inside the
    // anchor, so they may not occur free in the exported `psi`. Before,
    // `(= (exists ((x U)) (P x)) (P x))` was accepted (see third-party/carcara/DOWNSTREAM.md).
    scoping::check_not_exported(pool, &context.as_ref().unwrap().args, psi)?;

    let args = context.as_ref().unwrap().args.iter();

    let substitution: HashMap<Rc<Term>, Rc<Term>> = args
        .filter_map(AnchorArg::as_assign)
        .map(|(k, v)| {
            let var = Term::new_var(k, pool.sort(v));
            (pool.add(var), v.clone())
        })
        .collect();

    for (i, x) in bindings.iter().enumerate() {
        let x_term = pool.add(Term::from(x.clone()));
        let t = substitution
            .get(&x_term)
            .ok_or_else(|| SubproofError::BindingIsNotInContext(x.0.clone()))?;

        // To check that `t` is of the correct form, we construct the expected term and compare
        // them
        let expected = {
            let mut inner = current_phi.clone();

            // If this is the last binding, all bindings were skolemized, so we don't need to wrap
            // the term in a quantifier
            if i < bindings.len() - 1 {
                inner = pool.add(Term::Binder(
                    rule_type,
                    BindingList(bindings.0[i + 1..].to_vec()),
                    inner,
                ));
            }

            // If the rule is `sko_forall`, the predicate in the choice term should be negated
            if rule_type == Binder::Forall {
                inner = build_term!(pool, (not { inner }));
            }
            let binding_list = BindingList(vec![x.clone()]);
            pool.add(Term::Binder(Binder::Choice, binding_list, inner))
        };
        if !alpha_equiv(t, &expected, polyeq_time) {
            return Err(EqualityError::ExpectedEqual(t.clone(), expected).into());
        }

        // For every binding we skolemize, we must apply another substitution to phi
        let mut s = Substitution::single(pool, x_term, t.clone())?;
        current_phi = s.apply(pool, &current_phi);
    }
    Ok(())
}

pub fn sko_ex(args: RuleArgs) -> RuleResult {
    generic_skolemization_rule(Binder::Exists, args)
}

pub fn sko_forall(args: RuleArgs) -> RuleResult {
    generic_skolemization_rule(Binder::Forall, args)
}
