use super::{
    assert_clause_len, assert_eq, assert_is_expected, assert_num_args, assert_num_premises,
    assert_operation_len, assert_polyeq_expected, get_premise_term, CheckerError, EqualityError,
    RuleArgs, RuleResult,
};
use crate::{
    ast::{
        build_term, match_term_err,
        pool::{Fuel, TermPool, Trie},
        Binder, BindingList, MatchCase, MatchPattern, Operator, Rc, Sort, SortedVar, Term,
    },
    checker::budget::{ExpansionBudget, MAX_EXPANDED_BITS, WORDS_PER_EXPANDED_BIT},
    parser::MAX_TERM_DEPTH,
};
use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};

pub fn distinct_elim(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (distinct_args, second_term) = match_term_err!((= (distinct ...) second) = &conclusion[0])?;
    match distinct_args {
        [] | [_] => unreachable!(),
        [a, b] => {
            let got = match_term_err!((not (= x y)) = second_term)?;
            if got == (a, b) || got == (b, a) {
                Ok(())
            } else {
                let expected = build_term!(pool, (not (= {a.clone()} {b.clone()})));
                Err(EqualityError::ExpectedToBe { expected, got: second_term.clone() }.into())
            }
        }
        // If there are more than two boolean arguments to the distinct operator, the
        // second term must be `false`
        args if pool.sort(&args[0]).as_ref() == &Sort::Bool => {
            if second_term.is_bool_false() {
                Ok(())
            } else {
                Err(CheckerError::ExpectedBoolConstant(
                    false,
                    second_term.clone(),
                ))
            }
        }

        args => {
            let n = args.len();
            let and_args = match_term_err!((and ...) = second_term)?;
            assert_operation_len(Operator::And, and_args, n * (n - 1) / 2)?;

            let mut k = 0;
            for i in 0..n {
                for j in (i + 1)..n {
                    let (a, b) = (&args[i], &args[j]);
                    let got = match_term_err!((not (= x y)) = &and_args[k])?;
                    if !(got == (a, b) || got == (b, a)) {
                        let expected = build_term!(pool, (not (= {a.clone()} {b.clone()})));
                        return Err(EqualityError::ExpectedToBe {
                            expected,
                            got: and_args[k].clone(),
                        }
                        .into());
                    }
                    k += 1;
                }
            }
            Ok(())
        }
    }
}

pub fn and(RuleArgs { conclusion, premises, args, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    let and_term = get_premise_term(&premises[0])?;
    let and_contents = match_term_err!((and ...) = and_term)?;
    let i = args[0].as_usize_err()?;

    if i >= and_contents.len() {
        return Err(CheckerError::NoIthChildInTerm(i, and_term.clone()));
    }

    assert_eq(&conclusion[0], &and_contents[i])
}

pub fn not_or(RuleArgs { conclusion, premises, args, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    let or_term = get_premise_term(&premises[0])?;
    let or_contents = match_term_err!((not (or ...)) = or_term)?;
    let conclusion = conclusion[0].remove_negation_err()?;
    let i = args[0].as_usize_err()?;

    if i >= or_contents.len() {
        return Err(CheckerError::NoIthChildInTerm(i, or_term.clone()));
    }

    assert_eq(conclusion, &or_contents[i])
}

pub fn or(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;

    let or_term = get_premise_term(&premises[0])?;
    let or_contents = match_term_err!((or ...) = or_term)?;

    assert_clause_len(conclusion, or_contents.len())?;
    for (t, u) in or_contents.iter().zip(conclusion) {
        assert_eq(t, u)?;
    }
    Ok(())
}

pub fn not_and(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;

    let and_term = get_premise_term(&premises[0])?;
    let and_contents = match_term_err!((not (and ...)) = and_term)?;

    assert_clause_len(conclusion, and_contents.len())?;
    for (t, u) in and_contents.iter().zip(conclusion) {
        let u = u.remove_negation_err()?;
        assert_eq(t, u)?;
    }
    Ok(())
}

pub fn xor1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((xor phi_1 phi_2) = premise_term)?;

    assert_eq(phi_1, &conclusion[0])?;
    assert_eq(phi_2, &conclusion[1])
}

pub fn xor2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((xor phi_1 phi_2) = premise_term)?;

    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, conclusion[1].remove_negation_err()?)
}

pub fn not_xor1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((not (xor phi_1 phi_2)) = premise_term)?;

    assert_eq(phi_1, &conclusion[0])?;
    assert_eq(phi_2, conclusion[1].remove_negation_err()?)
}

pub fn not_xor2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((not (xor phi_1 phi_2)) = premise_term)?;

    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[1])
}

pub fn implies(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((=> phi_1 phi_2) = premise_term)?;

    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[1])
}

pub fn not_implies1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, _) = match_term_err!((not (=> phi_1 phi_2)) = premise_term)?;

    assert_eq(phi_1, &conclusion[0])
}

pub fn not_implies2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (_, phi_2) = match_term_err!((not (=> phi_1 phi_2)) = premise_term)?;

    assert_eq(phi_2, conclusion[0].remove_negation_err()?)
}

pub fn nary_elim(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    /// The three possible cases for n-ary operators: chainable, right associative and left
    /// associative
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Case {
        Chainable,
        RightAssoc,
        LeftAssoc,
    }

    /// A function to expand terms that fall in the right or left associative cases. For example,
    /// the term `(=> p q r s)` will be expanded into the term `(=> p (=> q (=> r s)))`.
    ///
    /// Modified in Clean: the expansion is a fold, not a recursion per argument, which ran out
    /// of stack on a long argument list (`(=> p ... p)` of 7,000,000 arguments, a 14 MB proof,
    /// took 1.2 GiB of stack). It adds the same terms to the pool in the same order, innermost
    /// first.
    fn expand_assoc(
        pool: &mut dyn TermPool,
        op: Operator,
        args: &[Rc<Term>],
        case: Case,
    ) -> Rc<Term> {
        match case {
            Case::RightAssoc => {
                let (last, rest) = args.split_last().unwrap();
                rest.iter().rev().fold(last.clone(), |nested, head| {
                    pool.add(Term::Op(op, vec![head.clone(), nested]))
                })
            }
            Case::LeftAssoc => {
                let (first, rest) = args.split_first().unwrap();
                rest.iter().fold(first.clone(), |nested, head| {
                    pool.add(Term::Op(op, vec![nested, head.clone()]))
                })
            }
            Case::Chainable => unreachable!(),
        }
    }

    assert_clause_len(conclusion, 1)?;

    let (original, result) = match_term_err!((= o r) = &conclusion[0])?;

    let (op, args) = match original.as_ref() {
        Term::Op(op, args) if args.len() >= 2 => (op, args),
        _ => return Err(CheckerError::NotValidNaryTerm(original.clone())),
    };

    let case = match op {
        Operator::Equals => Case::Chainable,
        Operator::Add | Operator::Sub | Operator::Mult => Case::LeftAssoc,
        Operator::Implies => Case::RightAssoc,
        _ => return Err(CheckerError::NotValidNaryTerm(original.clone())),
    };

    // Added in Clean: the expansion of `n` arguments is at least `n` deep, and the parser reads no
    // term deeper than `MAX_TERM_DEPTH`, so a longer list cannot expand to the conclusion read.
    // It is refused before its `n` terms are built.
    if case != Case::Chainable && args.len() > MAX_TERM_DEPTH {
        return Err(CheckerError::Explanation(format!(
            "an n-ary term of {} arguments expands deeper than the {} levels a term may have",
            args.len(),
            MAX_TERM_DEPTH
        )));
    }

    let expected = match case {
        Case::Chainable => {
            let and_args: Vec<_> = args
                .windows(2)
                .map(|args| pool.add(Term::Op(*op, args.to_vec())))
                .collect();
            pool.add(Term::Op(Operator::And, and_args))
        }
        assoc_case => expand_assoc(pool, *op, args, assoc_case),
    };
    assert_is_expected(result, expected)
}

/// Added in Clean: `2^k`, saturating at `u128::MAX`.
fn two_to_the(k: usize) -> u128 {
    u32::try_from(k)
        .ok()
        .and_then(|k| 1u128.checked_shl(k))
        .unwrap_or(u128::MAX)
}

/// Added in Clean: the instances of a quantifier's `body` over the Boolean variables among
/// `bindings`, in the order `bfun_elim_first_step` builds them, charged to `budget` before they
/// are built.
///
/// Upstream built them by `2^k` chains of single substitutions, each of which visits every term of
/// the (partial) instance, so the step was charged `2^k` times the body's distinct subterms. That
/// charge was both too much and too little. Too much: a subterm that mentions none of the variables
/// is the same term in every instance, so `(forall ((x Bool) (y Bool)) (or x y (= (+ i0 ...
/// i70000) 0)))` (409 KB, four instances checked at 34 MB by base) was refused. Too little: an
/// inner binder that rebinds one of the variables shadows it for the subterm it reaches, so a
/// subterm shared under such binders instantiates differently on each path; `(forall ((x1 Bool) ..
/// (x12 Bool)) L12)`, `L_i = (and (forall ((x_i Bool)) L_(i-1)) L_(i-1))`, was admitted and built
/// 1,254 MB in 52 s before a nested charge refused it, and the same shape with `(let ((x_i true))
/// ..)` in place of the binders was accepted outright at 1,702 MB in 118 s.
///
/// Where no `let` or `match` in the body rebinds one of the variables' names and no binder in it
/// binds one of them twice, a single substitution of a Boolean constant replaces the variable's
/// free occurrences and nothing else: a binder that binds its name is left as it is, and no
/// variable is renamed (`Substitution::apply_to_binder`, `rename_binding_list`: the only name a
/// substitution of a constant renames is the variable's own). The chain of single substitutions is
/// then the simultaneous substitution of every variable's value (its last binding's, the one the
/// chain substitutes first), which is built here directly. A subterm's instance depends only on
/// the values of its *mask*, the variables it mentions free that its context has not rebound: a
/// subterm whose mask is empty is the body's own term in every instance, and one whose mask is
/// not is rebuilt once for each of the `2^|mask|` assignments of its mask, whichever instances
/// share it. The step is charged, in words, `2^|mask|` times an expanded bit plus the words the
/// rebuilt term copies (`bfun_elim_copied_words`: its argument list, and the names it binds) for
/// each pair of a subterm and its mask, and an expanded bit for each instance's place in the
/// conjunction, counted over the DAG first (stopping where the charge refuses anyway); that is
/// what the instances build, and what the walk over their conjunction in `apply_bfun_elim` visits.
/// Charged `2^k` times the pairs alone, a body with a long argument list was admitted at the
/// budget and copied the list into each instance: over 14 variables, `(or x1 .. x14 c .. c)` with
/// 16,000 copies of `c` (a 32 KB proof) took 2,065 MB, and over 16 variables, `(or x1 c .. c)`
/// with 20,000 copies took 19 s at 6 MB to build two distinct terms 65,536 times. Keyed by the
/// whole context rather than the mask, a subterm reached under binders that rebind only variables
/// it does not mention was counted once for each of them. Where a `let` or `match` rebinds a
/// variable's name, upstream's substitution renames the bound variable throughout what it binds,
/// whether or not the variable occurs there, and its cost is not bounded by these pairs; such a
/// step is refused. See third-party/carcara/DOWNSTREAM.md.
fn bfun_elim_instances(
    pool: &mut dyn TermPool,
    bindings: &[SortedVar],
    body: &Rc<Term>,
    budget: &mut ExpansionBudget,
    names_below: &mut NamesBelow,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    let positions: Vec<usize> = bindings
        .iter()
        .enumerate()
        .filter(|(_, (_, sort))| sort.as_ref() == &Sort::Bool)
        .map(|(i, _)| i)
        .collect();
    let instances = two_to_the(positions.len());
    if instances > MAX_EXPANDED_BITS {
        // Each instance takes at least its place in the conjunction.
        budget.spend("instantiating a quantifier's Boolean variables", instances)?;
    }
    // The distinct variables, each with the Boolean position whose value it takes: its last.
    let mut variables: IndexMap<String, usize> = IndexMap::new();
    for (bit, &i) in positions.iter().enumerate() {
        variables.insert(bindings[i].0.clone(), bit);
    }
    let terms: Vec<Rc<Term>> = variables
        .values()
        .map(|&bit| pool.add(bindings[positions[bit]].clone().into()))
        .collect();
    let names = |list: &mut dyn Iterator<Item = &String>| -> u64 {
        list.filter_map(|name| variables.get_index_of(name))
            .fold(0, |mask, i| mask | (1 << i))
    };

    let mentions = bfun_elim_mentions(body, &variables, &terms, names_below)?;

    // The pairs of a subterm and the variables among those it mentions that its context has not
    // rebound, its mask: an instance's subterm depends on their values alone, so the instances
    // build it once for each of the `2^|mask|` assignments of them. Counting stops where the charge
    // refuses anyway.
    let all = if terms.len() == 64 {
        u64::MAX
    } else {
        (1 << terms.len()) - 1
    };
    let limit = MAX_EXPANDED_BITS * WORDS_PER_EXPANDED_BIT;
    let mut words = instances * WORDS_PER_EXPANDED_BIT;
    let mut pairs: HashSet<(&Rc<Term>, u64)> = HashSet::new();
    let mut stack = vec![(body, all)];
    while let Some((term, active)) = stack.pop() {
        let mask = mentions[term] & active;
        if mask == 0 || !pairs.insert((term, mask)) {
            continue;
        }
        let built = two_to_the(mask.count_ones() as usize);
        words = words.saturating_add(
            built.saturating_mul(WORDS_PER_EXPANDED_BIT + bfun_elim_copied_words(term)),
        );
        if words > limit {
            break;
        }
        let mask = match term.as_ref() {
            Term::Binder(_, list, _) => mask & !names(&mut list.iter().map(|(n, _)| n)),
            _ => mask,
        };
        stack.extend(bfun_elim_children(term).into_iter().map(|c| (c, mask)));
    }
    budget.spend_words("instantiating a quantifier's Boolean variables", words)?;

    // Within the budget, `instances` is at most `MAX_EXPANDED_BITS`.
    let (f, t) = (pool.bool_false(), pool.bool_true());
    let mut instantiation = Instantiation {
        terms: &terms,
        values: [f, t],
        mentions: &mentions,
        names: &variables,
        built: HashMap::new(),
    };
    let mut result = Vec::with_capacity(instances as usize);
    for instance in 0..instances {
        // Bit `i` of `assignment` is the value of the `i`th variable: its position's bit.
        let assignment = variables.values().enumerate().fold(0u64, |a, (i, &bit)| {
            a | (((instance >> bit) & 1) as u64) << i
        });
        result.push(instantiation.apply(pool, body, all, assignment));
    }
    Ok(result)
}

/// Added in Clean: which of `variables` (`terms`, their variables in the same order) each subterm of
/// `body` mentions free, a binder's own names removed, as a mask; and whether the body leaves
/// upstream's substitution anything to rename (a refusal, `bfun_elim_renaming_refused`).
///
/// A binder that binds every one of the variables, each once, mentions none of them free whatever
/// it holds, and every single substitution of upstream's chain returns it whole
/// (`Substitution::can_skip_instead_of_renaming`), so the walk does not enter it. Entering it, the
/// walk was quadratic in the depth of nested quantifiers that each rebind their Boolean: for
/// `B_k = (forall ((x Int) (b Bool)) (and (F b) (P x) B_(k-1)))`, each level's walk visited every
/// level below, so `bfun_elim` over `B_16384` (2.2 MB) took 39 s where the instances it builds are
/// linear in the depth.
///
/// Nor does it enter a subterm in which none of the variables' names occurs, free or bound
/// (`NamesBelow`): no subterm of it mentions one of the variables, and none rebinds one, so the
/// walk would find nothing there to rename or to refuse, and every mask in it is zero. Entering
/// it, the walk was quadratic in the depth of nested quantifiers named apart, `b_k` at level `k`,
/// where no level rebinds the variable of a level above: over 8,192 levels (1.6 MB) the step took
/// 14 s. The walk now visits only the subterms that hold one of the names, and their children,
/// which it records with the mask zero; a subterm whose names cost more fuel than `NamesBelow` had
/// is entered, as every subterm was before.
fn bfun_elim_mentions<'t>(
    body: &'t Rc<Term>,
    variables: &IndexMap<String, usize>,
    terms: &[Rc<Term>],
    names_below: &mut NamesBelow,
) -> Result<HashMap<&'t Rc<Term>, u64>, CheckerError> {
    let names = |list: &mut dyn Iterator<Item = &String>| -> u64 {
        list.filter_map(|name| variables.get_index_of(name))
            .fold(0, |mask, i| mask | (1 << i))
    };
    let binds_each_once = |list: &BindingList| {
        (0..variables.len()).all(|i| {
            list.iter()
                .filter(|(n, _)| variables.get_index_of(n) == Some(i))
                .count()
                == 1
        })
    };
    let wanted = names_below.names(variables.keys());
    let mut mentions: HashMap<&Rc<Term>, u64> = HashMap::new();
    let mut stack = vec![(body, false)];
    while let Some((term, ready)) = stack.pop() {
        if mentions.contains_key(term) {
            continue;
        }
        if !ready && !names_below.holds_any(term, &wanted) {
            mentions.insert(term, 0);
            continue;
        }
        let children = bfun_elim_children(term);
        if !ready {
            if let Term::Binder(_, list, _) = term.as_ref() {
                if binds_each_once(list) {
                    mentions.insert(term, 0);
                    continue;
                }
            }
            stack.push((term, true));
            stack.extend(children.iter().rev().map(|c| (*c, false)));
            continue;
        }
        let renames = |list: &mut dyn Iterator<Item = &String>| names(list) != 0;
        let mask = match term.as_ref() {
            Term::Var(..) => terms.iter().position(|v| v == term).map_or(0, |i| 1 << i),
            Term::Binder(_, list, inner) => {
                let bound: Vec<_> = list
                    .iter()
                    .filter_map(|(n, _)| variables.get_index_of(n))
                    .collect();
                let unique: HashSet<_> = bound.iter().collect();
                if unique.len() != bound.len() {
                    return Err(bfun_elim_renaming_refused());
                }
                mentions[inner] & !names(&mut list.iter().map(|(n, _)| n))
            }
            Term::Let(list, _) if renames(&mut list.iter().map(|(n, _)| n)) => {
                return Err(bfun_elim_renaming_refused())
            }
            Term::Match(_, cases)
                if cases
                    .iter()
                    .any(|case| renames(&mut case.bindings().iter().map(|(n, _)| n))) =>
            {
                return Err(bfun_elim_renaming_refused())
            }
            _ => children.iter().fold(0, |mask, c| mask | mentions[*c]),
        };
        mentions.insert(term, mask);
    }

    Ok(mentions)
}

/// Added in Clean: the subterms `Substitution::apply` reaches from `term` (it leaves a
/// `ParamOp`'s indices alone).
fn bfun_elim_children(term: &Rc<Term>) -> Vec<&Rc<Term>> {
    match term.as_ref() {
        Term::Const(_) | Term::Var(..) => Vec::new(),
        Term::App(func, args) => args.iter().chain(std::iter::once(func)).collect(),
        Term::Op(_, args) | Term::AsOp(_, _, args) | Term::ParamOp { args, .. } => {
            args.iter().collect()
        }
        Term::Binder(_, _, inner) => vec![inner],
        Term::Let(list, inner) => list
            .iter()
            .map(|(_, value)| value)
            .chain(std::iter::once(inner))
            .collect(),
        Term::Match(scrutinee, cases) => std::iter::once(scrutinee)
            .chain(cases.iter().map(|case| &case.body))
            .collect(),
    }
}

/// Added in Clean: the names that occur in each term `bfun_elim_mentions` asks about: those of its
/// variables, free or not, and those a binder, `let` or `match` case in it binds, in the subterms
/// `bfun_elim_children` reaches. A term's set is the union of its children's and its own names, a
/// persistent set that shares structure with theirs (see `ast::pool::FreeVars`), so a chain of `n`
/// nested quantifiers costs a path of the set a level, not `n^2 / 2` names. It lives for one step,
/// and each name is a number of that step's own.
///
/// A merge of two sets is linear in their size wherever they share no structure, so the sets alone
/// were quadratic on terms the walk without them read in linear time: two chains over distinct
/// names merged at each of `n` links, `(h A_j B_j)` with `A_j = (f c_j A_(j-1))` and `B_j = (g d_j
/// B_(j-1))`, made the sets cost `n^2` nodes (5,000 links, 680 KB: 1,560 MB, where the walk alone
/// took 20 MB; 40,000 ran past 4 GB). So the sets are computed with fuel (`ast::pool::Fuel`): each
/// term read earns `FUEL_PER_LINK` for itself, each of its children and each name it binds, and
/// merges and insertions spend it, a unit for each node they visit and `ALLOCATION` (16) for each
/// node they allocate. A term whose set would cost more than the fuel left gets none, and so does
/// each term above it; the walk enters such a term, as it entered every term before these sets. So
/// the sets allocate at most 4 trie nodes a link of the terms read and visit at most 64, and the
/// walk costs at most what it cost without them.
struct NamesBelow {
    ids: HashMap<String, u128>,
    /// `None` for a term whose names would have cost more than the fuel left.
    sets: HashMap<Rc<Term>, Option<Trie<()>>>,
    fuel: Fuel,
}

/// What reading a link earns. A chain of nested quantifiers, whose sets grow by a name a level and
/// copy a path of the trie for it, spends 28 to 40 units a link (2,000 to 100,000 levels), so it
/// keeps every set (`the_mentions_walk_skips_what_holds_none_of_the_names`); the review's merged
/// chains (`names_below_spend_their_fuel_on_chains_merged_apart`) run out, at about twice base's
/// memory.
const FUEL_PER_LINK: Fuel = 64;

impl NamesBelow {
    fn new() -> Self {
        Self {
            ids: HashMap::new(),
            sets: HashMap::new(),
            fuel: 0,
        }
    }

    fn id(&mut self, name: &str) -> u128 {
        let next = self.ids.len() as u128;
        *self.ids.entry(name.to_owned()).or_insert(next)
    }

    /// The set of `names`.
    fn names<'n>(&mut self, names: impl Iterator<Item = &'n String>) -> Trie<()> {
        let mut set = Trie::default();
        for name in names {
            set = set.insert(self.id(name), ());
        }
        set
    }

    /// Whether one of `names` may occur in `term`: whether one does, where its set was computed.
    fn holds_any(&mut self, term: &Rc<Term>, names: &Trie<()>) -> bool {
        self.of(term).is_none_or(|set| set.intersects(names))
    }

    /// The names occurring in `term`, computed for it and the subterms it reaches that have none
    /// yet, by a walk with a stack of its own; `None` where the fuel did not suffice.
    fn of(&mut self, term: &Rc<Term>) -> Option<Trie<()>> {
        if let Some(set) = self.sets.get(term) {
            return set.clone();
        }
        let mut stack = vec![(term.clone(), false)];
        while let Some((current, ready)) = stack.pop() {
            if self.sets.contains_key(&current) {
                continue;
            }
            if !ready {
                stack.push((current.clone(), true));
                stack.extend(
                    bfun_elim_children(&current)
                        .into_iter()
                        .map(|child| (child.clone(), false)),
                );
                continue;
            }
            let (own, children) = (Self::own(&current), bfun_elim_children(&current));
            self.fuel = self
                .fuel
                .saturating_add(FUEL_PER_LINK.saturating_mul(Self::links(&current)));
            let set = self.merged(&own, &children);
            self.sets.insert(current, set);
        }
        self.sets[term].clone()
    }

    /// The names `term` itself holds: a variable's, or those its binder, `let` or `match` binds.
    fn own(term: &Rc<Term>) -> Vec<&str> {
        match term.as_ref() {
            Term::Var(name, _) => vec![name.as_str()],
            Term::Binder(_, list, _) => list.iter().map(|(name, _)| name.as_str()).collect(),
            Term::Let(list, _) => list.iter().map(|(name, _)| name.as_str()).collect(),
            Term::Match(_, cases) => cases
                .iter()
                .flat_map(|case| case.bindings().iter().map(|(name, _)| name.as_str()))
                .collect(),
            _ => Vec::new(),
        }
    }

    /// The links reading `term` earns fuel for: the term, its children and its own names.
    fn links(term: &Rc<Term>) -> Fuel {
        (1 + Self::own(term).len() + bfun_elim_children(term).len()) as Fuel
    }

    /// The `children`'s sets merged, with `own` inserted: `None` if a child has no set, or if the
    /// fuel runs out (the merge then stops, and what it built is dropped).
    fn merged(&mut self, own: &[&str], children: &[&Rc<Term>]) -> Option<Trie<()>> {
        if children.iter().any(|child| self.sets[*child].is_none()) {
            return None;
        }
        let mut set = Trie::default();
        for child in children {
            let child = self.sets[*child].as_ref()?;
            set = set.union_within(child, &mut self.fuel)?;
        }
        for name in own {
            let id = self.id(name);
            set = set.insert_within(id, (), &mut self.fuel)?;
        }
        Some(set)
    }
}

/// Added in Clean: the words `Instantiation::apply` copies to rebuild `term`, beside the term
/// itself: its argument list (a pointer for each child), a `ParamOp`'s indices, and each name a
/// binder, `let` or `match` case binds (the name's bytes, its header and its sort or value).
fn bfun_elim_copied_words(term: &Rc<Term>) -> u128 {
    fn name(name: &str) -> u128 {
        4 + name.len().div_ceil(8) as u128
    }
    fn list<V>(list: &[(String, V)]) -> u128 {
        list.iter().map(|(n, _)| name(n)).sum()
    }
    match term.as_ref() {
        Term::Const(_) | Term::Var(..) => 0,
        Term::App(_, args) => 1 + args.len() as u128,
        Term::Op(_, args) | Term::AsOp(_, _, args) => args.len() as u128,
        Term::ParamOp { op_args, args, .. } => (op_args.len() + args.len()) as u128,
        Term::Binder(_, bindings, _) => 1 + list(bindings),
        Term::Let(bindings, _) => 1 + list(bindings),
        Term::Match(_, cases) => {
            1 + cases
                .iter()
                .map(|case| {
                    let constructor = match &case.pattern {
                        MatchPattern::Cons(c, _) => name(c),
                        _ => 0,
                    };
                    8 + constructor + list(case.bindings())
                })
                .sum::<u128>()
        }
    }
}

fn bfun_elim_renaming_refused() -> CheckerError {
    CheckerError::Explanation(
        "bfun_elim: a `let` or `match` in the quantifier's body rebinds one of its Boolean \
         variables, or a binder in it binds one twice, so instantiating it renames bound \
         variables; such a step is refused (see third-party/carcara/DOWNSTREAM.md)"
            .to_owned(),
    )
}

/// Added in Clean: the instances of a body (see `bfun_elim_instances`): each subterm that mentions
/// a variable its context has not rebound is rebuilt, as `Substitution::apply` rebuilds it, once
/// for each assignment of the variables in its mask, whichever instances share it.
struct Instantiation<'a> {
    /// The variables, and the two values each takes.
    terms: &'a [Rc<Term>],
    values: [Rc<Term>; 2],
    /// Which variables each subterm of the body mentions free.
    mentions: &'a HashMap<&'a Rc<Term>, u64>,
    names: &'a IndexMap<String, usize>,
    /// Each subterm built, by the subterm, its mask and the assignment of its mask.
    built: HashMap<(Rc<Term>, u64, u64), Rc<Term>>,
}

impl Instantiation<'_> {
    fn apply(
        &mut self,
        pool: &mut dyn TermPool,
        term: &Rc<Term>,
        active: u64,
        assignment: u64,
    ) -> Rc<Term> {
        let mask = self.mentions[term] & active;
        if mask == 0 {
            return term.clone();
        }
        let key = (term.clone(), mask, assignment & mask);
        if let Some(built) = self.built.get(&key) {
            return built.clone();
        }
        let result = match term.as_ref() {
            Term::Var(..) => {
                let i = self.terms.iter().position(|v| v == term).unwrap();
                self.values[(assignment >> i & 1) as usize].clone()
            }
            Term::App(func, args) => {
                let new_args = args
                    .iter()
                    .map(|a| self.apply(pool, a, mask, assignment))
                    .collect();
                let new_func = self.apply(pool, func, mask, assignment);
                pool.add(Term::App(new_func, new_args))
            }
            Term::Op(op, args) => {
                let new_args = args
                    .iter()
                    .map(|a| self.apply(pool, a, mask, assignment))
                    .collect();
                pool.add(Term::Op(*op, new_args))
            }
            Term::ParamOp { op, op_args, args } => {
                let new_args = args
                    .iter()
                    .map(|a| self.apply(pool, a, mask, assignment))
                    .collect();
                pool.add(Term::ParamOp {
                    op: *op,
                    op_args: op_args.clone(),
                    args: new_args,
                })
            }
            Term::AsOp(op, sort, args) => {
                let new_args = args
                    .iter()
                    .map(|a| self.apply(pool, a, mask, assignment))
                    .collect();
                pool.add(Term::AsOp(*op, sort.clone(), new_args))
            }
            Term::Binder(binder, list, inner) => {
                let rebound = list
                    .iter()
                    .filter_map(|(n, _)| self.names.get_index_of(n))
                    .fold(0u64, |mask, i| mask | (1 << i));
                let new_inner = self.apply(pool, inner, mask & !rebound, assignment);
                pool.add(Term::Binder(*binder, list.clone(), new_inner))
            }
            Term::Let(list, inner) => {
                let new_values: Vec<_> = list
                    .iter()
                    .map(|(_, value)| self.apply(pool, value, mask, assignment))
                    .collect();
                let new_inner = self.apply(pool, inner, mask, assignment);
                let new_list = list
                    .iter()
                    .map(|(name, _)| name.clone())
                    .zip(new_values)
                    .collect();
                pool.add(Term::Let(BindingList(new_list), new_inner))
            }
            Term::Match(scrutinee, cases) => {
                let new_scrutinee = self.apply(pool, scrutinee, mask, assignment);
                let new_cases = cases
                    .iter()
                    .map(|case| MatchCase {
                        pattern: case.pattern.clone(),
                        body: self.apply(pool, &case.body, mask, assignment),
                    })
                    .collect();
                pool.add(Term::Match(new_scrutinee, new_cases))
            }
            Term::Const(_) => unreachable!("a constant mentions no variable"),
        };
        self.built.insert(key, result.clone());
        result
    }
}

/// The second simplification step for `bfun_elim`, that expands function applications over
/// non-constant boolean arguments into `ite` terms.
fn bfun_elim_second_step(
    pool: &mut dyn TermPool,
    func: &Rc<Term>,
    args: &[Rc<Term>],
    processed: usize,
) -> Rc<Term> {
    for i in processed..args.len() {
        if pool.sort(&args[i]).as_ref() == &Sort::Bool
            && !args[i].is_bool_false()
            && !args[i].is_bool_true()
        {
            let mut ite_args = Vec::with_capacity(3);
            ite_args.push(args[i].clone());

            for bool_constant in [pool.bool_true(), pool.bool_false()] {
                let mut new_args = args.to_vec();
                new_args[i] = bool_constant;
                let inner_term = bfun_elim_second_step(pool, func, &new_args, i + 1);
                ite_args.push(inner_term);
            }
            return pool.add(Term::Op(Operator::Ite, ite_args));
        }
    }

    // If there were no non-constant boolean arguments we don't need to expand the term into an ite
    // term. So we just construct the original application term and return it.
    pool.add(Term::App(func.clone(), args.to_vec()))
}

/// Applies the simplification steps for the `bfun_elim` rule.
///
/// Modified in Clean: both steps expand exponentially, and are charged to the step's `budget`
/// before they expand (see checker/budget.rs and third-party/carcara/DOWNSTREAM.md, "Bit-vector
/// expansion has a resource budget"). A quantifier over `k > 0` Boolean variables becomes `2^k`
/// instances of its body (`bfun_elim_instances`, which says what it is charged). An application
/// to `m > 0` arguments that are Boolean and not constants becomes an `ite` tree over `2^m`
/// copies of it: it is charged `2^m` times its arguments plus one. What expands nothing (`k` or
/// `m` zero) is rebuilt as it is, and charged nothing.
/// Upstream reserved `2^n` slots for a quantifier over `n` variables of any sort first, so about
/// 45 of them aborted the process in the allocator, and 64 overflowed the power.
pub fn apply_bfun_elim(
    pool: &mut dyn TermPool,
    term: &Rc<Term>,
    cache: &mut IndexMap<Rc<Term>, Rc<Term>>,
    budget: &mut ExpansionBudget,
) -> Result<Rc<Term>, CheckerError> {
    apply_bfun_elim_with(pool, term, cache, budget, &mut NamesBelow::new())
}

/// Added in Clean: `apply_bfun_elim`, with the names below each term it has asked about kept for
/// the rest of the expansion (see `NamesBelow`), so a quantifier nested in another's body finds
/// them computed.
fn apply_bfun_elim_with(
    pool: &mut dyn TermPool,
    term: &Rc<Term>,
    cache: &mut IndexMap<Rc<Term>, Rc<Term>>,
    budget: &mut ExpansionBudget,
    names_below: &mut NamesBelow,
) -> Result<Rc<Term>, CheckerError> {
    if let Some(v) = cache.get(term) {
        return Ok(v.clone());
    }

    let result = match term.as_ref() {
        Term::App(f, args) => {
            let args: Vec<_> = args
                .iter()
                .map(|a| apply_bfun_elim_with(pool, a, cache, budget, names_below))
                .collect::<Result<_, _>>()?;
            let expanded = args
                .iter()
                .filter(|a| {
                    pool.sort(a).as_ref() == &Sort::Bool && !a.is_bool_false() && !a.is_bool_true()
                })
                .count();
            if expanded > 0 {
                budget.spend(
                    "expanding an application over its Boolean arguments",
                    two_to_the(expanded).saturating_mul(args.len() as u128 + 1),
                )?;
            }
            bfun_elim_second_step(pool, f, &args, 0)
        }
        Term::Op(op, args) => {
            let args = args
                .iter()
                .map(|a| apply_bfun_elim_with(pool, a, cache, budget, names_below))
                .collect::<Result<_, _>>()?;
            pool.add(Term::Op(*op, args))
        }
        Term::Binder(b, bindings, inner) => {
            let op = match b {
                Binder::Forall => Operator::And,
                Binder::Exists => Operator::Or,
                Binder::Choice | Binder::Lambda => {
                    let inner = apply_bfun_elim_with(pool, inner, cache, budget, names_below)?;
                    let result = pool.add(Term::Binder(*b, bindings.clone(), inner));
                    cache.insert(term.clone(), result.clone());
                    return Ok(result);
                }
            };
            let booleans = bindings
                .iter()
                .any(|(_, sort)| sort.as_ref() == &Sort::Bool);
            let mut args = if booleans {
                bfun_elim_instances(pool, bindings.as_slice(), inner, budget, names_below)?
            } else {
                vec![inner.clone()]
            };

            let op_term = if args.len() == 1 {
                args.pop().unwrap()
            } else {
                pool.add(Term::Op(op, args))
            };
            let op_term = apply_bfun_elim_with(pool, &op_term, cache, budget, names_below)?;

            let new_bindings: Vec<_> = bindings
                .iter()
                .filter(|(_, sort)| *sort.as_ref() != Sort::Bool)
                .cloned()
                .collect();
            if new_bindings.is_empty() {
                op_term
            } else {
                pool.add(Term::Binder(*b, BindingList(new_bindings), op_term))
            }
        }
        Term::Let(bindings, inner) => {
            let inner = apply_bfun_elim_with(pool, inner, cache, budget, names_below)?;
            pool.add(Term::Let(bindings.clone(), inner))
        }
        _ => term.clone(),
    };

    cache.insert(term.clone(), result.clone());
    Ok(result)
}

pub fn bfun_elim(
    RuleArgs {
        conclusion,
        premises,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let psi = get_premise_term(&premises[0])?;

    let mut budget = ExpansionBudget::new();
    let expected = apply_bfun_elim(pool, psi, &mut IndexMap::new(), &mut budget)?;
    assert_polyeq_expected(&conclusion[0], expected, polyeq_time)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{pool::PrimitivePool, Substitution, SubstitutionError};

    /// Upstream's first simplification step for `bfun_elim`, that expands quantifiers over boolean
    /// variables, kept (with Clean's `rposition`) to hold `bfun_elim_instances` to it.
    // Modified in Clean: the bindings after the last Boolean one are skipped by `rposition`; skipping
    // them recursed once per binding, so a quantifier over 100,000 `Int`s could overflow the stack.
    // It still recurses once per Boolean binding, which the step's budget holds to 18 (see
    // `apply_bfun_elim`).
    fn bfun_elim_first_step(
        pool: &mut dyn TermPool,
        bindigns: &[SortedVar],
        term: &Rc<Term>,
        acc: &mut Vec<Rc<Term>>,
    ) -> Result<(), SubstitutionError> {
        let Some(last) = bindigns
            .iter()
            .rposition(|var| var.1.as_ref() == &Sort::Bool)
        else {
            acc.push(term.clone());
            return Ok(());
        };
        let var = pool.add(bindigns[last].clone().into());
        for value in [pool.bool_false(), pool.bool_true()] {
            let mut substitution = Substitution::single(pool, var.clone(), value)?;
            let term = substitution.apply(pool, term);
            bfun_elim_first_step(pool, &bindigns[..last], &term, acc)?;
        }
        Ok(())
    }

    /// A small deterministic generator (xorshift64).
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: usize) -> usize {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % n as u64) as usize
        }
    }

    /// Added in Clean: the instances are the ones upstream's chains of single substitutions built,
    /// term for term and in order, on 4,000 random quantifiers: one to five Boolean variables
    /// (names repeated, `Int`s of the same names among them), bodies built from earlier ones
    /// (shared) under binders that rebind a name with its sort or another, `let`s of other names,
    /// applications and `ite`s; and a body with a `let` or `match` rebinding a variable, or a binder
    /// binding one twice, is refused.
    #[test]
    fn instances_are_upstreams() {
        let mut pool = PrimitivePool::new();
        let (boolean, int) = (pool.add_sort(Sort::Bool), pool.add_sort(Sort::Int));
        let names = ["a", "b", "c", "d"];
        let var =
            |pool: &mut PrimitivePool, n: &str, s: &Rc<Sort>| pool.add(Term::new_var(n, s.clone()));
        let f_sort = pool.add_sort(Sort::Function(vec![
            boolean.clone(),
            int.clone(),
            boolean.clone(),
        ]));
        let f = var(&mut pool, "f", &f_sort);
        let mut terms: Vec<Rc<Term>> = names.iter().map(|n| var(&mut pool, n, &boolean)).collect();
        let int_a = var(&mut pool, "a", &int);
        let zero = pool.add(Term::new_int(0));
        terms.push(pool.add(Term::Op(
            Operator::Equals,
            vec![int_a.clone(), zero.clone()],
        )));
        terms.push(pool.bool_true());
        let mut depth: HashMap<Rc<Term>, usize> = HashMap::new();
        let mut rng = Rng(0x5eed_1234_abcd_0001);
        let (mut accepted, mut refused) = (0, 0);
        for _ in 0..4000 {
            // Reused terms are less than 6 deep: upstream's chains, run here, are exponential in
            // the depth of a shared body under rebinding binders.
            let pick = |rng: &mut Rng, v: &Vec<Rc<Term>>| {
                v[v.len() - 1 - rng.below(v.len().min(24))].clone()
            };
            let term = match rng.below(9) {
                0 | 1 => {
                    let args = (0..2 + rng.below(2))
                        .map(|_| pick(&mut rng, &terms))
                        .collect();
                    pool.add(Term::Op([Operator::And, Operator::Or][rng.below(2)], args))
                }
                2 => {
                    let args = (0..3).map(|_| pick(&mut rng, &terms)).collect();
                    pool.add(Term::Op(Operator::Ite, args))
                }
                3 => {
                    let b = pick(&mut rng, &terms);
                    pool.add(Term::App(f.clone(), vec![b, zero.clone()]))
                }
                4 | 5 => {
                    // A binder rebinding one name, as a Boolean or as an `Int`, or two names.
                    let n = names[rng.below(names.len())];
                    let sort = if rng.below(3) == 0 { &int } else { &boolean };
                    let mut list = vec![(n.to_owned(), sort.clone())];
                    match rng.below(6) {
                        0 => list.push(("j".to_owned(), int.clone())),
                        1 => list.push((n.to_owned(), boolean.clone())),
                        _ => {}
                    }
                    let q = [Binder::Forall, Binder::Exists][rng.below(2)];
                    let inner = pick(&mut rng, &terms);
                    pool.add(Term::Binder(q, BindingList(list), inner))
                }
                6 => {
                    // A `let` of a name that is a variable of the quantifier or not.
                    let n = if rng.below(4) == 0 {
                        names[rng.below(names.len())]
                    } else {
                        "e"
                    };
                    let value = pick(&mut rng, &terms);
                    let inner = pick(&mut rng, &terms);
                    pool.add(Term::Let(BindingList(vec![(n.to_owned(), value)]), inner))
                }
                _ => {
                    let inner = pick(&mut rng, &terms);
                    pool.add(Term::Op(Operator::Not, vec![inner]))
                }
            };
            let d = 1 + bfun_elim_children(&term)
                .iter()
                .map(|c| depth.get(*c).copied().unwrap_or(0))
                .max()
                .unwrap_or(0);
            depth.insert(term.clone(), d);
            if d < 6 {
                terms.push(term.clone());
            }

            // The quantifier's bindings: one to five Booleans, with `Int`s among them.
            let mut bindings: Vec<SortedVar> = Vec::new();
            for _ in 0..1 + rng.below(5) {
                bindings.push((names[rng.below(3)].to_owned(), boolean.clone()));
                if rng.below(4) == 0 {
                    bindings.push((names[rng.below(names.len())].to_owned(), int.clone()));
                }
            }
            let mut upstream = Vec::new();
            bfun_elim_first_step(&mut pool, &bindings, &term, &mut upstream).unwrap();
            let mut budget = ExpansionBudget::new();
            let mut names_below = NamesBelow::new();
            match bfun_elim_instances(&mut pool, &bindings, &term, &mut budget, &mut names_below) {
                Ok(instances) => {
                    assert_eq!(instances, upstream, "{term} over {bindings:?}");
                    accepted += 1;
                }
                Err(CheckerError::Explanation(e)) => {
                    assert!(e.starts_with("bfun_elim: a `let` or `match`"), "{e}");
                    refused += 1;
                }
                Err(e) => panic!("{term}: {e}"),
            }
        }
        assert!(accepted > 1000 && refused > 10, "{accepted} {refused}");
    }

    /// The walk that finds which variables each subterm mentions does not enter a binder that
    /// binds every variable once: under nested quantifiers that each rebind their Boolean it visits
    /// the outermost body's own terms, whatever the depth below (it visited every level, so the
    /// step was quadratic in the depth). The instances are upstream's, a `let` that rebinds the
    /// variable inside such a binder included (upstream's substitutions never reach it); a binder
    /// that binds one of two variables, or one twice, is entered, and the latter refused. (The
    /// parser and upstream's chain of substitutions recurse per level: reading this chain took the
    /// test harness's whole 2 MiB stack, and overflowed it on origin/main `40ea22d1c`, so the test
    /// runs on a stack of its own.)
    #[test]
    fn the_mentions_walk_stops_where_every_variable_is_rebound() {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(the_mentions_walk_stops_where_every_variable_is_rebound_on_a_large_stack)
            .unwrap()
            .join()
            .unwrap();
    }

    fn the_mentions_walk_stops_where_every_variable_is_rebound_on_a_large_stack() {
        use crate::parser::tests::parse_terms;

        let definitions = "(declare-fun F (Bool) Bool)(declare-fun P (Int) Bool)\
            (declare-const p Bool)(declare-const q Bool)";
        let mut chain = "p".to_owned();
        for _ in 0..1000 {
            chain = format!("(forall ((x Int) (b Bool)) (and (F b) (P x) {chain}))");
        }
        let quantifiers = [
            chain.as_str(),
            "(forall ((b Bool)) (and b (forall ((b Bool)) (let ((b q)) b))))",
            "(forall ((b Bool) (c Bool)) (or b c (forall ((b Bool)) (and b c))))",
            "(forall ((b Bool)) (and b (forall ((b Bool) (b Bool)) b)))",
        ];
        let mut pool = PrimitivePool::new();
        for (i, quantifier) in quantifiers.into_iter().enumerate() {
            let [term] = parse_terms(&mut pool, definitions, [quantifier]);
            let Term::Binder(_, bindings, inner) = term.as_ref() else {
                unreachable!()
            };
            let mut upstream = Vec::new();
            bfun_elim_first_step(&mut pool, bindings.as_slice(), inner, &mut upstream).unwrap();
            let mut budget = ExpansionBudget::new();
            let mut names_below = NamesBelow::new();
            let instances = bfun_elim_instances(
                &mut pool,
                bindings.as_slice(),
                inner,
                &mut budget,
                &mut names_below,
            );
            match i {
                3 => assert!(instances.is_err(), "{quantifier}"),
                _ => assert_eq!(instances.unwrap(), upstream, "{quantifier}"),
            }
        }

        let [term] = parse_terms(&mut pool, definitions, [chain.as_str()]);
        let Term::Binder(_, _, inner) = term.as_ref() else {
            unreachable!()
        };
        let boolean = pool.add_sort(Sort::Bool);
        let b = pool.add(Term::new_var("b", boolean));
        let variables: IndexMap<String, usize> = [("b".to_owned(), 0)].into_iter().collect();
        let mentions = bfun_elim_mentions(inner, &variables, &[b], &mut NamesBelow::new()).unwrap();
        assert!(mentions.len() < 16, "{} subterms walked", mentions.len());
    }

    /// Nested quantifiers named apart, `b_k` at level `k`: no level rebinds the variable of a level
    /// above, so the walk used to visit every level below each level, quadratic in the depth. It
    /// now records a subterm in which none of the variables' names occurs, free or bound, without
    /// entering it: each level's walk visits its own few terms, whatever the depth below. The
    /// instances stay upstream's, and the refusals stay where a `let`, a `match` case or a binder
    /// that rebinds a variable sits in a subterm that does not mention it free. (Upstream's chain
    /// of substitutions recurses per level, so the test runs on a stack of its own.)
    #[test]
    fn the_mentions_walk_skips_what_holds_none_of_the_names() {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(the_mentions_walk_skips_what_holds_none_of_the_names_on_a_large_stack)
            .unwrap()
            .join()
            .unwrap();
    }

    fn the_mentions_walk_skips_what_holds_none_of_the_names_on_a_large_stack() {
        use crate::parser::tests::parse_terms;

        let depth = 2000;
        let mut pool = PrimitivePool::new();
        let (boolean, int) = (pool.add_sort(Sort::Bool), pool.add_sort(Sort::Int));
        let unary = |pool: &mut PrimitivePool, name: &str, sort: &Rc<Sort>| {
            let sort = pool.add_sort(Sort::Function(vec![sort.clone(), boolean.clone()]));
            pool.add(Term::new_var(name, sort))
        };
        let (f, p) = (unary(&mut pool, "F", &boolean), unary(&mut pool, "P", &int));
        let x = pool.add(Term::new_var("x", int.clone()));
        let mut chain = pool.add(Term::new_var("p", boolean.clone()));
        for k in 1..=depth {
            let b = pool.add(Term::new_var(format!("b{k}"), boolean.clone()));
            let fb = pool.add(Term::App(f.clone(), vec![b]));
            let px = pool.add(Term::App(p.clone(), vec![x.clone()]));
            let body = pool.add(Term::Op(Operator::And, vec![fb, px, chain]));
            let bindings = vec![
                ("x".to_owned(), int.clone()),
                (format!("b{k}"), boolean.clone()),
            ];
            chain = pool.add(Term::Binder(Binder::Forall, BindingList(bindings), body));
        }
        let mut names_below = NamesBelow::new();
        let mut level = chain;
        for k in (depth - 3..=depth).rev() {
            let Term::Binder(_, bindings, inner) = level.as_ref() else {
                unreachable!()
            };
            let b = pool.add(Term::new_var(format!("b{k}"), boolean.clone()));
            let variables: IndexMap<String, usize> = [(format!("b{k}"), 0)].into_iter().collect();
            let mentions = bfun_elim_mentions(inner, &variables, &[b], &mut names_below).unwrap();
            assert!(
                mentions.len() < 16,
                "level {k}: {} subterms walked",
                mentions.len()
            );

            let mut upstream = Vec::new();
            bfun_elim_first_step(&mut pool, bindings.as_slice(), inner, &mut upstream).unwrap();
            let mut budget = ExpansionBudget::new();
            let instances = bfun_elim_instances(
                &mut pool,
                bindings.as_slice(),
                inner,
                &mut budget,
                &mut names_below,
            );
            assert_eq!(instances.unwrap(), upstream, "level {k}");
            let Term::Op(_, args) = inner.as_ref() else {
                unreachable!()
            };
            level = args[2].clone();
        }

        // A rebinding the variable's free occurrences do not reach is still found and refused.
        let definitions = "(declare-fun P (Int) Bool)(declare-fun G (Bool) Bool)\
            (declare-const q Bool)(declare-datatype L ((nil) (cons (hd Bool) (tl L))))\
            (declare-const l L)";
        for quantifier in [
            "(forall ((b Bool)) (and b (P 1) (G (let ((b q)) b))))",
            "(forall ((b Bool)) (and b (G (match l ((nil q) ((cons b t) b))))))",
            "(forall ((b Bool)) (and b (G (forall ((b Bool) (b Bool)) q))))",
            "(forall ((b Bool) (c Bool)) (and b (G (let ((c q)) c))))",
        ] {
            let [term] = parse_terms(&mut pool, definitions, [quantifier]);
            let Term::Binder(_, bindings, inner) = term.as_ref() else {
                unreachable!()
            };
            let mut budget = ExpansionBudget::new();
            let instances = bfun_elim_instances(
                &mut pool,
                bindings.as_slice(),
                inner,
                &mut budget,
                &mut NamesBelow::new(),
            );
            assert!(instances.is_err(), "{quantifier}");
        }
    }

    /// Two chains over distinct names merged at each link, `h_j = (h A_j B_j)` with `A_j = (f c_j
    /// A_(j-1))` and `B_j = (g d_j B_(j-1))`: the sets of `A_j` and `B_j` share no structure and
    /// their names interleave, so each merge is linear in `j`, and without fuel the links' sets cost
    /// `n^2` nodes (5,000 links, a 680 KB certificate, took 1,560 MB). `NamesBelow` allocates at
    /// most `FUEL_PER_LINK / ALLOCATION` nodes a link of the terms it has read, checked here every
    /// 50 links, so sets without fuel fail at the 100th, with 11,547 nodes for 1,610 links. The
    /// links it could not afford have no set; the walk enters them, and the instances stay
    /// upstream's. (Upstream's substitution recurses per level of the chains, so the test runs on
    /// a stack of its own.)
    #[test]
    fn names_below_spend_their_fuel_on_chains_merged_apart() {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(names_below_spend_their_fuel_on_chains_merged_apart_on_a_large_stack)
            .unwrap()
            .join()
            .unwrap();
    }

    fn names_below_spend_their_fuel_on_chains_merged_apart_on_a_large_stack() {
        use crate::ast::pool::{nodes_allocated, ALLOCATION};

        let n = 3000;
        let mut pool = PrimitivePool::new();
        let (boolean, int) = (pool.add_sort(Sort::Bool), pool.add_sort(Sort::Int));
        let binary = |pool: &mut PrimitivePool, name: &str, result: &Rc<Sort>| {
            let sort = pool.add_sort(Sort::Function(vec![
                int.clone(),
                int.clone(),
                result.clone(),
            ]));
            pool.add(Term::new_var(name, sort))
        };
        let (f, g) = (binary(&mut pool, "f", &int), binary(&mut pool, "g", &int));
        let (h, pz) = (
            binary(&mut pool, "h", &boolean),
            binary(&mut pool, "pz", &boolean),
        );
        let b = pool.add(Term::new_var("b", boolean.clone()));
        let variables: IndexMap<String, usize> = [("b".to_owned(), 0)].into_iter().collect();

        let mut names_below = NamesBelow::new();
        let wanted = names_below.names(variables.keys());
        let start = nodes_allocated();
        let mut a = pool.add(Term::new_var("c0", int.clone()));
        let mut chain_b = pool.add(Term::new_var("d0", int.clone()));
        let (mut links, mut pairs) = (Vec::new(), Vec::new());
        for j in 1..=n {
            let c = pool.add(Term::new_var(format!("c{j}"), int.clone()));
            let d = pool.add(Term::new_var(format!("d{j}"), int.clone()));
            pairs.push(pool.add(Term::App(pz.clone(), vec![c.clone(), d.clone()])));
            a = pool.add(Term::App(f.clone(), vec![c, a]));
            chain_b = pool.add(Term::App(g.clone(), vec![d, chain_b]));
            let link = pool.add(Term::App(h.clone(), vec![a.clone(), chain_b.clone()]));
            assert!(
                !names_below.holds_any(&a, &wanted) && !names_below.holds_any(&chain_b, &wanted)
            );
            names_below.holds_any(&link, &wanted);
            links.push(link);
            if j % 50 == 0 {
                let read: Fuel = names_below.sets.keys().map(NamesBelow::links).sum();
                let allocated = (nodes_allocated() - start) as Fuel;
                assert!(
                    allocated <= read * FUEL_PER_LINK / ALLOCATION,
                    "{allocated} nodes for {read} links at link {j}"
                );
            }
        }
        assert!(
            names_below.sets.values().any(Option::is_none),
            "the fuel never ran out"
        );

        // The quantifier of the certificate, `(forall ((b Bool)) (and b BIG Z))`.
        let big = pool.add(Term::Op(Operator::And, links));
        let z = pool.add(Term::Op(Operator::And, pairs));
        let body = pool.add(Term::Op(
            Operator::And,
            vec![b.clone(), big.clone(), z.clone()],
        ));
        let mentions = bfun_elim_mentions(&body, &variables, &[b], &mut names_below).unwrap();
        assert_eq!((mentions[&body], mentions[&big], mentions[&z]), (1, 0, 0));
        let bindings = [("b".to_owned(), boolean)];
        let mut upstream = Vec::new();
        bfun_elim_first_step(&mut pool, &bindings, &body, &mut upstream).unwrap();
        let mut budget = ExpansionBudget::new();
        let instances =
            bfun_elim_instances(&mut pool, &bindings, &body, &mut budget, &mut names_below);
        assert_eq!(instances.unwrap(), upstream);
    }
}
