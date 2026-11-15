use crate::ast::{build_term, match_term, pool::TermPool, Rc, Term};
use indexmap::IndexSet;
use std::{
    borrow::Borrow,
    collections::{hash_map::DefaultHasher, HashMap},
    hash::{Hash, Hasher},
};
use thiserror::Error;

type Literal = (bool, Rc<Term>);

// A RUP Addition is a vector of the clause plus the unit clause and the hash of the clause
pub type RupAddition = Vec<(IndexSet<Literal>, Option<Literal>, u64)>;

//This enum is used to bookkeeping the action performed by a reverse unit propagation
#[allow(dead_code)]
pub enum DRupProofAction {
    RupStory(IndexSet<Literal>, RupAddition),
    Delete(Rc<Term>),
}

pub type DRupStory = Vec<DRupProofAction>;

#[derive(Debug, Error)]
pub enum DrupFormatError {
    #[error("couldn't find conclusion term in the premise clauses")]
    NoConclusionInPremise,
    #[error(
        "couldn't elaborate drup because bottom wasn't derived from the premises and the argument"
    )]
    NoFinalBottomInDrup,
    #[error("couldn't elaborate drup because the argument might not be in RUP")]
    PotentialNoDrupFormat,
    #[error("a clause in RAT should be non-empty")]
    CheckingRatInEmptyClause,
    #[error("the clause isn't in RAT format")]
    NotInRatFormat,
}

pub fn hash_term<T: Borrow<Rc<Term>>>(pool: &mut dyn TermPool, term: T) -> u64 {
    let term: Rc<Term> = {
        let (p, regular_term): (bool, &Rc<Term>) =
            term.borrow().remove_all_negations_with_polarity();
        if p {
            regular_term.clone()
        } else {
            build_term!(pool, (not { (*regular_term).clone() }))
        }
    };

    let mut s = DefaultHasher::new();
    term.hash(&mut s);
    s.finish()
}

// Modified in Clean: reverse unit propagation by occurrence lists and per-clause counters.
//
// Before, `rup` copied every clause and then, after EACH propagated literal, rescanned the
// clause list from its first clause for the next unit one (`get_implied_clause`, kept as the
// test reference in `rescanning_rup` below): O(P * N) clause visits, each two SipHash lookups,
// for P propagations over N clauses. A `drup` step whose N premises form one implication chain
// (P ~ N) cost O(N^2). AY prints a transported resolution chain of 8 or more links as exactly
// that step (AY d39838422a, 2026-09-30); trust-cg's BSR_I64 certificate has 63 of them, of up to
// 16,769 premises: 3.1e9 clause visits, 150 CPU-s. Now each term lists the clauses it occurs in
// and each clause counts its literals whose term is unassigned, so an assignment touches only the
// clauses of its term. A call costs O(L) for L literal occurrences in the clauses and the goal
// (`indexed_rup` counts its steps; `rup_cost` holds the tests that pin the bound).
//
// SAME PREDICATE. Both versions answer one question: does unit propagation from the negated goal
// literals over the clauses reach a clause whose literals are all false? Literals, clauses and
// truth are the same objects in both: a literal is `(polarity, term with every negation removed)`
// with the term compared by identity (`Rc` equality is pointer equality), a clause is the
// `IndexSet` it was given, and assigning a term sets exactly one of its two literals true. The
// answer does not depend on the order units are propagated in: if one run reaches a conflict and
// another stops at a fixpoint, induction over the first run shows each literal it forced is true
// at the second run's fixpoint (its clause's other literals are false there, so the clause would
// be unit or falsified otherwise), and then the conflict clause is falsified at that fixpoint, a
// contradiction. The old code computes it: each pass takes the first clause in list order that is
// unit or falsified, propagating a unit one and stopping at a falsified one, and it only ever
// skips a clause with a true watch (satisfied) or two distinct unassigned watches (two unassigned
// literals: neither unit nor falsified), so it stops with `None` only at a fixpoint. This code
// computes it: the invariants below hold after every assignment, every clause whose `open` drops
// to 1 or 0 while unsatisfied is queued, and a popped clause is re-read in the current state, so
// `pending` empties only at a fixpoint. The story still lists each propagating clause with its
// unit literal, then the falsified clause; its order may differ. `check_drup` and `check_drat`
// only test `is_some()` and pass the story on, and their one caller, `checker::rules::drup`, drops
// it.
fn rup(
    pool: &mut dyn TermPool,
    drup_clauses: &HashMap<u64, IndexSet<Literal>>,
    goal: &[Rc<Term>],
) -> Option<RupAddition> {
    let mut steps = 0u64;
    #[cfg(test)]
    if rup_cost::rescanning_selected() {
        let story = rescanning_rup::rup(pool, drup_clauses, goal, &mut steps);
        rup_cost::record(steps);
        return story;
    }
    let story = indexed_rup(pool, drup_clauses, goal, &mut steps);
    #[cfg(test)]
    rup_cost::record(steps);
    story
}

// The propagation behind `rup`. `steps` counts its unit operations: one per literal occurrence
// indexed, per clause popped, per literal read to find a forced one, and per occurrence updated
// after an assignment. With C clauses (goal units included) and L literal occurrences that is at
// most 4L + C: every literal is indexed once; at most C clauses start in `pending` and every push
// after that follows one decrement, so at most C + L pops; a clause is searched for its forced
// literal at most once, since that literal's assignment satisfies it; and every term is assigned
// at most once, so each occurrence is updated at most once.
fn indexed_rup(
    pool: &mut dyn TermPool,
    drup_clauses: &HashMap<u64, IndexSet<Literal>>,
    goal: &[Rc<Term>],
    steps: &mut u64,
) -> Option<RupAddition> {
    // The negated goal, one unit clause per literal, then the premises (borrowed, not copied).
    let goal_units: Vec<(IndexSet<Literal>, u64)> = goal
        .iter()
        .map(|term| {
            let (p, regular_term) = term.remove_all_negations_with_polarity();
            let mut clause = IndexSet::new();
            clause.insert((!p, regular_term.clone()));
            (clause, hash_term(&mut *pool, term))
        })
        .collect();
    let clauses: Vec<(&IndexSet<Literal>, u64)> = goal_units
        .iter()
        .map(|(clause, key)| (clause, *key))
        .chain(drup_clauses.iter().map(|(key, clause)| (clause, *key)))
        .collect();

    // Every literal occurrence as (term id, polarity), clause by clause in `IndexSet` order; the
    // occurrences of clause `c` are `lits[start[c]..start[c + 1]]`. Term ids are by identity.
    let mut ids: HashMap<&Rc<Term>, usize> = HashMap::new();
    let mut lits: Vec<(usize, bool)> = Vec::new();
    let mut start: Vec<usize> = Vec::with_capacity(clauses.len() + 1);
    for &(clause, _) in &clauses {
        start.push(lits.len());
        for (polarity, term) in clause {
            let next = ids.len();
            lits.push((*ids.entry(term).or_insert(next), *polarity));
        }
    }
    start.push(lits.len());
    *steps += lits.len() as u64;

    // For each term, the clauses it occurs in, with that occurrence's polarity:
    // `occ[at[t]..at[t + 1]]`.
    let terms = ids.len();
    let mut at = vec![0usize; terms + 1];
    for &(id, _) in &lits {
        at[id + 1] += 1;
    }
    for t in 0..terms {
        at[t + 1] += at[t];
    }
    let mut fill = at.clone();
    let mut occ = vec![(0usize, false); lits.len()];
    for c in 0..clauses.len() {
        for &(id, polarity) in &lits[start[c]..start[c + 1]] {
            occ[fill[id]] = (c, polarity);
            fill[id] += 1;
        }
    }

    // Invariants: `value[t]` is the polarity term `t` is assigned (its literal of that polarity is
    // true); `satisfied[c]` iff a literal of clause `c` is true; `open[c]` is the number of
    // occurrences in clause `c` whose term is unassigned. So an unsatisfied clause with
    // `open[c] == 1` is unit and one with `open[c] == 0` is falsified. A tautology `{x, (not x)}`
    // has `open == 2` until `x` is assigned, which satisfies it: never unit, as before.
    let mut value: Vec<Option<bool>> = vec![None; terms];
    let mut satisfied = vec![false; clauses.len()];
    let mut open: Vec<usize> = start.windows(2).map(|w| w[1] - w[0]).collect();
    let mut pending: Vec<usize> = (0..clauses.len()).filter(|&c| open[c] <= 1).collect();
    let mut unit_story: RupAddition = vec![];
    while let Some(c) = pending.pop() {
        *steps += 1;
        if satisfied[c] {
            continue;
        }
        let (clause, key) = clauses[c];
        if open[c] == 0 {
            unit_story.push((clause.clone(), None, key));
            return Some(unit_story);
        }
        // `open[c] == 1` and no literal is true: the one literal with an unassigned term is forced.
        let mut forced = None;
        for (i, &(id, _)) in lits[start[c]..start[c + 1]].iter().enumerate() {
            *steps += 1;
            if value[id].is_none() {
                forced = Some((i, id));
                break;
            }
        }
        // Both lookups succeed by the invariants; if one did not, `rup` would answer `None` and the
        // step would be refused (fail closed), never accepted.
        let (i, id) = forced?;
        let (polarity, term) = clause.get_index(i)?;
        value[id] = Some(*polarity);
        unit_story.push((clause.clone(), Some((*polarity, term.clone())), key));
        for &(other, occurrence) in &occ[at[id]..at[id + 1]] {
            *steps += 1;
            if occurrence == *polarity {
                satisfied[other] = true;
            } else {
                open[other] -= 1;
                if open[other] <= 1 && !satisfied[other] {
                    pending.push(other);
                }
            }
        }
    }
    None
}

// This implements the rule for drup checking, by using a chain of goals that calls RUP, check_rat is optional in case if you
// want to check also for RAT format
pub fn check_drup(
    pool: &mut dyn TermPool,
    conclusion: Rc<Term>,
    premises: &[Rc<Term>],
    args: &[Rc<Term>],
    check_rat: bool,
) -> Result<DRupStory, DrupFormatError> {
    let mut premises: HashMap<u64, _> = premises
        .iter()
        .map(|p| {
            let mut indexset = IndexSet::new();
            let terms = if let Some(terms) = match_term!((cl ...) = p) {
                terms.to_vec()
            } else {
                vec![(*p).clone()]
            };
            for term in terms {
                let (polarity, new_term) = term.remove_all_negations_with_polarity();
                indexset.insert((polarity, (*new_term).clone()));
            }
            (hash_term(pool, p), indexset)
        })
        .collect();

    let mut drup_history: DRupStory = vec![];
    // Modified in Clean: a RAT lemma is not implied by the clauses it is checked against; it only
    // preserves their satisfiability. A derivation that uses one therefore only establishes its
    // conclusion when that conclusion is the empty clause. Before, `(cl a b)` could be derived
    // for a fresh `b` and then combined with other clauses (see third-party/carcara/DOWNSTREAM.md).
    let mut used_rat = false;
    for t in args {
        if let Some(terms) = match_term!((delete (cl ...)) = &t) {
            // Modified in Clean: `(@d (cl))` used to index into the empty list and panic.
            let clause_term = if terms.is_empty() {
                build_term!(pool, (cl[Vec::new()]))
            } else {
                build_term!(pool, (cl[terms.to_vec()]))
            };
            premises.remove(&hash_term(pool, &clause_term));
            drup_history.push(DRupProofAction::Delete(clause_term));
            continue;
        }

        let Some(terms) = match_term!((cl ...) = &t) else {
            return Err(DrupFormatError::PotentialNoDrupFormat);
        };
        let mut unit_history = rup(pool, premises.borrow(), terms);
        if unit_history.is_none() && !terms.is_empty() && check_rat {
            unit_history = check_drat(pool, premises.borrow(), terms);
            used_rat |= unit_history.is_some();
        }

        if unit_history.is_none() {
            return if check_rat {
                Err(DrupFormatError::NotInRatFormat)
            } else {
                Err(DrupFormatError::NoFinalBottomInDrup)
            };
        }

        let terms_indexed_set = terms
            .iter()
            .map(|term| {
                let (p, term) = Rc::remove_all_negations_with_polarity(term);
                (p, term.clone())
            })
            .collect::<IndexSet<_>>();

        drup_history.push(DRupProofAction::RupStory(
            terms_indexed_set.clone(),
            unit_history.unwrap(),
        ));

        premises.insert(hash_term(pool, t), terms_indexed_set);
    }

    if !premises.contains_key(&hash_term(pool, &conclusion)) {
        return Err(DrupFormatError::NoConclusionInPremise);
    }
    if used_rat && !match_term!((cl ...) = &conclusion).is_some_and(|c| c.is_empty()) {
        return Err(DrupFormatError::NotInRatFormat);
    }

    Ok(drup_history)
}

// Checks RAT, essentially rat is equivalent to RUP plus a blocked clause
// (eg. given a clause C \/ p, we look for RUP in every D \/ ~ p in the set clause)
pub fn check_drat(
    pool: &mut dyn TermPool,
    drup_clauses: &HashMap<u64, IndexSet<Literal>>,
    goal: &[Rc<Term>],
) -> Option<RupAddition> {
    let pivot = &goal[0];
    let mut unit_history = vec![];
    for clause in drup_clauses.values() {
        let (p, regular_term) = pivot.remove_all_negations_with_polarity();
        let negated_pivot = (!p, regular_term.clone());

        if clause.contains(&negated_pivot) {
            let mut resolvent = clause.clone();
            resolvent.swap_remove(&negated_pivot);
            let mut resolvent = resolvent
                .iter()
                .map(|(p, literal)| {
                    if *p {
                        literal.clone()
                    } else {
                        build_term!(pool, (not { (*literal).clone() }))
                    }
                })
                .collect::<Vec<_>>();

            resolvent.append(&mut goal[1..].to_vec());
            if let Some(history) = rup(pool, drup_clauses, resolvent.borrow()) {
                unit_history.extend_from_slice(&history);
                continue;
            }
            return None;
        }
    }

    Some(unit_history)
}

// Added in Clean: the clause-rescanning `rup` that `indexed_rup` replaced, kept verbatim as the
// reference of `rup_equivalence` and `rup_cost` except for its `steps` counter: one per literal
// copied up front, per clause visited by `get_implied_clause`, and per literal read in its scan.
#[cfg(test)]
mod rescanning_rup {
    use super::*;
    use std::borrow::BorrowMut;

    #[derive(Debug)]
    pub enum Implied<T, X> {
        Pivot(T, X),
        Bottom(X),
        NotUnsat(),
    }

    // This function search for a unit clause by using the two literals in the pair associated in each indexset
    // additionally clauses is mutable since this function also fix the two watched literal whenever a new unit clause is propagated
    fn get_implied_clause(
        clauses: &mut Vec<((Option<Literal>, Option<Literal>), (IndexSet<Literal>, u64))>,
        env: &HashMap<Literal, bool>,
        steps: &mut u64,
    ) -> Implied<Literal, (IndexSet<Literal>, u64)> {
        if clauses.is_empty() {
            return Implied::NotUnsat();
        }

        for (schema, (lits, key)) in clauses {
            *steps += 1;
            match schema {
                (None, None) => return Implied::Bottom(((*lits).clone(), *key)),

                (Some((b, t)), None) | (None, Some((b, t))) => match env.get(&(*b, (*t).clone())) {
                    Some(false) => {
                        assert_eq!(lits.len(), 1);
                        return Implied::Bottom(((*lits).clone(), *key));
                    }
                    Some(true) => continue,
                    None => {
                        assert_eq!(lits.len(), 1);
                        return Implied::Pivot((*b, (*t).clone()), ((*lits).clone(), *key));
                    }
                },

                (Some((b, t)), Some((b0, t0))) => {
                    match (env.get(&(*b, (*t).clone())), env.get(&(*b0, (*t0).clone()))) {
                        (Some(true), _) => continue,
                        (_, Some(true)) => continue,
                        (None, None) => continue,
                        (_, _) => {
                            let mut unset_literal = None;
                            let mut not_unit = false;

                            for (b1, t1) in &*lits {
                                *steps += 1;
                                let assign_state = env.get(&(*b1, (*t1).clone()));

                                match assign_state {
                                    None => {
                                        let literal = Some((*b1, (*t1).clone()));
                                        if schema.0 != literal && schema.1 != literal {
                                            if schema.0.is_some() {
                                                schema.0 = literal;
                                            } else if schema.1.is_some() {
                                                schema.1 = literal;
                                            }
                                        }

                                        if unset_literal.is_some() {
                                            not_unit = true;
                                            continue;
                                        }

                                        unset_literal = Some((b1, (*t1).clone()));
                                    }
                                    Some(true) => {
                                        // Set the true clause as a watched literal to avoid searching O(n) in this "deleted" clause
                                        let literal = Some((*b1, (*t1).clone()));
                                        if schema.0 != literal && schema.1 != literal {
                                            if schema.0.is_some() {
                                                schema.0 = literal;
                                            } else if schema.1.is_some() {
                                                schema.1 = literal;
                                            }
                                        }

                                        not_unit = true;
                                        continue;
                                    }
                                    Some(false) => (),
                                }
                            }

                            if not_unit {
                                continue;
                            }

                            return match unset_literal {
                                Some((p, polarity)) => {
                                    Implied::Pivot((*p, polarity.clone()), ((*lits).clone(), *key))
                                }
                                _ => Implied::Bottom(((*lits).clone(), *key)),
                            };
                        }
                    }
                }
            }
        }
        Implied::NotUnsat()
    }

    // Perform *only* rup (reverse unit propagation) in a set of clauses and a "goal", here the goal is the implied clause by
    // F /\ ~ C |- \bottom
    pub fn rup(
        pool: &mut dyn TermPool,
        drup_clauses: &HashMap<u64, IndexSet<Literal>>,
        goal: &[Rc<Term>],
        steps: &mut u64,
    ) -> Option<RupAddition> {
        let mut unit_story: RupAddition = vec![];

        let mut clauses = vec![];

        let mut env: HashMap<Literal, bool> = HashMap::new();

        for term in goal {
            *steps += 1;
            let (p, regular_term) = term.remove_all_negations_with_polarity();
            let mut clause: IndexSet<Literal> = IndexSet::new();
            clause.insert((!p, regular_term.clone()));
            clauses.push((
                (Some((!p, regular_term.clone())), None),
                (clause, hash_term(pool, term)),
            ));
        }

        for (key, clause) in drup_clauses {
            *steps += clause.len() as u64;
            let mut watched_literals = clause.iter().take(2);
            let clause = (
                (
                    watched_literals.next().map(|v| (v.0, v.1.clone())),
                    watched_literals.next().map(|v| (v.0, v.1.clone())),
                ),
                (
                    clause.iter().map(|(k, v)| (*k, (*v).clone())).collect(),
                    *key,
                ),
            );
            clauses.push(clause);
        }

        loop {
            let unit = get_implied_clause(clauses.borrow_mut(), env.borrow(), steps);

            match unit {
                Implied::Bottom(clause) => {
                    unit_story.push((clause.0, None, clause.1));
                    return Some(unit_story);
                }
                Implied::Pivot(literal, clause) => {
                    env.insert(literal.clone(), true);
                    let negated_literal = (!literal.0, literal.1.clone());
                    env.insert(negated_literal.clone(), false);
                    unit_story.push((clause.0, Some((literal.0, literal.1)), clause.1));
                }
                Implied::NotUnsat() => return None,
            }
        }
    }
}

// Added in Clean: the indexed `rup` against the rescanning one on random clause sets over a few
// terms, with literals under up to two negations, duplicated and complementary literals, empty
// clauses and empty goals. The verdicts must agree, and every story either returns must replay as
// unit propagation over the clauses it was given, ending on a falsified clause.
#[cfg(test)]
mod rup_equivalence {
    use super::*;
    use crate::ast::{pool::PrimitivePool, Sort};
    use rand::{rngs::StdRng, Rng, SeedableRng};

    fn literal(pool: &mut PrimitivePool, vars: &[Rc<Term>], rng: &mut StdRng) -> Rc<Term> {
        let mut term = vars[rng.gen_range(0..vars.len())].clone();
        for _ in 0..rng.gen_range(0..3) {
            term = build_term!(pool, (not { term }));
        }
        term
    }

    // Whether `story` is a unit-propagation refutation: each entry is a premise (under its own
    // key) or the unit clause of a negated goal literal; every entry but the last makes its
    // literal true while every other literal of its clause is already false; the last clause has
    // every literal false.
    pub(super) fn replays(
        pool: &mut PrimitivePool,
        clauses: &HashMap<u64, IndexSet<Literal>>,
        goal: &[Rc<Term>],
        story: &RupAddition,
    ) -> bool {
        let goal_units: Vec<(IndexSet<Literal>, u64)> = goal
            .iter()
            .map(|term| {
                let (p, regular_term) = term.remove_all_negations_with_polarity();
                (
                    IndexSet::from([(!p, regular_term.clone())]),
                    hash_term(&mut *pool, term),
                )
            })
            .collect();
        let mut value: HashMap<Rc<Term>, bool> = HashMap::new();
        let is_false =
            |value: &HashMap<Rc<Term>, bool>, (p, t): &Literal| value.get(t) == Some(&!p);
        let Some((last, propagations)) = story.split_last() else {
            return false;
        };
        for (clause, _, key) in story {
            let given = clauses.get(key) == Some(clause)
                || goal_units.iter().any(|(c, k)| c == clause && k == key);
            if !given {
                return false;
            }
        }
        for (clause, unit, _) in propagations {
            let Some((p, t)) = unit else { return false };
            let others_false = clause
                .iter()
                .filter(|lit| lit.0 != *p || lit.1 != *t)
                .all(|lit| is_false(&value, lit));
            if !clause.contains(&(*p, t.clone())) || value.contains_key(t) || !others_false {
                return false;
            }
            value.insert(t.clone(), *p);
        }
        last.1.is_none() && last.0.iter().all(|lit| is_false(&value, lit))
    }

    #[test]
    fn indexed_rup_agrees_with_the_rescanning_rup() {
        let mut pool = PrimitivePool::new();
        let bool_sort = pool.add_sort(Sort::Bool);
        let all: Vec<Rc<Term>> = (0..7)
            .map(|i| pool.add(Term::new_var(format!("x{i}"), bool_sort.clone())))
            .collect();
        let mut rng = StdRng::seed_from_u64(0x5eed_d20b);
        let (mut refuted, mut open) = (0u32, 0u32);
        for _ in 0..300_000 {
            let vars = &all[..rng.gen_range(1..=all.len())];
            let mut clauses: HashMap<u64, IndexSet<Literal>> = HashMap::new();
            for _ in 0..rng.gen_range(0..=14) {
                let terms: Vec<Rc<Term>> = (0..rng.gen_range(0..=4))
                    .map(|_| literal(&mut pool, vars, &mut rng))
                    .collect();
                // As check_drup reads a premise.
                let mut set = IndexSet::new();
                for term in &terms {
                    let (polarity, inner) = term.remove_all_negations_with_polarity();
                    set.insert((polarity, inner.clone()));
                }
                let clause = build_term!(pool, (cl[terms]));
                let key = hash_term(&mut pool, &clause);
                clauses.insert(key, set);
            }
            let goal: Vec<Rc<Term>> = (0..rng.gen_range(0..=3))
                .map(|_| literal(&mut pool, vars, &mut rng))
                .collect();
            let indexed = indexed_rup(&mut pool, &clauses, &goal, &mut 0);
            let rescanning = rescanning_rup::rup(&mut pool, &clauses, &goal, &mut 0);
            assert_eq!(
                indexed.is_some(),
                rescanning.is_some(),
                "clauses {clauses:?} goal {goal:?}"
            );
            for story in [&indexed, &rescanning].into_iter().flatten() {
                assert!(
                    replays(&mut pool, &clauses, &goal, story),
                    "clauses {clauses:?} goal {goal:?}"
                );
            }
            if indexed.is_some() {
                refuted += 1;
            } else {
                open += 1;
            }
        }
        // Both verdicts are exercised.
        assert!(
            refuted > 10_000 && open > 10_000,
            "refuted {refuted} open {open}"
        );
    }
}

// Added in Clean: what `rup` costs on the shape that made trust-cg's BSR_I64 and LSDA
// certificates time out (third-party/carcara/DOWNSTREAM.md): one `drup` step whose premises are
// the clauses of a long implication chain. A complete certificate is checked end to end, by the
// rescanning `rup` and by the indexed one, and the work `rup` reports is compared, not the time.
#[cfg(test)]
mod rup_cost {
    use crate::{checker, parser};
    use std::cell::Cell;

    thread_local! {
        static STEPS: Cell<u64> = const { Cell::new(0) };
        static RESCANNING: Cell<bool> = const { Cell::new(false) };
    }

    pub(super) fn rescanning_selected() -> bool {
        RESCANNING.with(Cell::get)
    }

    pub(super) fn record(steps: u64) {
        STEPS.with(|s| s.set(s.get() + steps));
    }

    // Makes `rup` on this thread run the rescanning implementation (`true`) or the indexed one.
    pub(super) fn select_rescanning(rescanning: bool) {
        RESCANNING.with(|r| r.set(rescanning));
    }

    // `a`, `b` and the chain `a -> x1 -> ... -> x(n-1) -> (not b)` of `n` clauses: unsatisfiable.
    // The proof derives `(cl (not a) (not b))` by one `drup` step over the chain's `n` clauses,
    // listed in a scrambled order as AY lists them, minus the clause at `drop` if any, and
    // resolves it with `a` and `b` to the empty clause.
    fn chain_certificate(n: usize, drop: Option<usize>) -> (String, String) {
        let atom = |i: usize| match i {
            0 => "a".to_owned(),
            i if i == n => "b".to_owned(),
            i => format!("x{i}"),
        };
        let link = |i: usize| {
            let head = if i + 1 == n {
                "(not b)".to_owned()
            } else {
                atom(i + 1)
            };
            format!("(not {}) {head}", atom(i))
        };
        let mut problem = String::from("(declare-const a Bool)\n(declare-const b Bool)\n");
        for i in 1..n {
            problem += &format!("(declare-const x{i} Bool)\n");
        }
        problem += "(assert a)\n(assert b)\n";
        let mut proof = String::from("(assume ha a)\n(assume hb b)\n");
        for i in 0..n {
            problem += &format!("(assert (or {}))\n", link(i));
            proof += &format!("(assume h{i} (or {}))\n", link(i));
            proof += &format!("(step c{i} (cl {}) :rule or :premises (h{i}))\n", link(i));
        }
        let premises: Vec<String> = (0..n)
            .map(|i| (i * 7919) % n)
            .filter(|&i| Some(i) != drop)
            .map(|i| format!("c{i}"))
            .collect();
        proof += &format!(
            "(step lemma (cl (not a) (not b)) :rule drup :premises ({}) :args ((cl (not a) (not b))))\n",
            premises.join(" ")
        );
        proof += "(step end (cl) :rule resolution :premises (lemma ha hb))\n";
        (problem, proof)
    }

    // Checks the certificate with the chosen `rup`; returns whether it was accepted (complete, no
    // holes) and the steps `rup` reported.
    fn check(n: usize, drop: Option<usize>, rescanning: bool) -> (bool, u64) {
        let (problem, proof) = chain_certificate(n, drop);
        let (problem, proof, rules, mut pool) = parser::parse_instance(
            problem.as_str(),
            proof.as_str(),
            None,
            parser::Config::new(),
        )
        .expect("the synthetic certificate parses");
        RESCANNING.with(|r| r.set(rescanning));
        STEPS.with(|s| s.set(0));
        let result = checker::ProofChecker::new(&mut pool, &rules, checker::Config::new())
            .check(&problem, &proof);
        RESCANNING.with(|r| r.set(false));
        (matches!(result, Ok(false)), STEPS.with(Cell::get))
    }

    #[test]
    fn a_chain_shaped_drup_step_costs_linear_rup_work() {
        let sizes = [256, 512, 1024];
        let mut indexed = vec![];
        let mut rescanning = vec![];
        for n in sizes {
            let (accepted, steps) = check(n, None, false);
            assert!(accepted, "indexed rup refused the chain of {n}");
            // n chain clauses and two goal units: L = 2n + 2 literals, C = n + 2 clauses, and
            // `indexed_rup` takes at most 4L + C steps.
            let bound = 4 * (2 * n as u64 + 2) + (n as u64 + 2);
            assert!(steps <= bound, "n = {n}: {steps} steps > 4L + C = {bound}");
            indexed.push(steps);

            let (accepted, steps) = check(n, None, true);
            assert!(accepted, "rescanning rup refused the chain of {n}");
            // Each chain clause is found by a scan from the first clause that passes every
            // clause before it: at least n(n+1)/2 visits whatever order the premises are in.
            let floor = (n * (n + 1) / 2) as u64;
            assert!(
                steps >= floor,
                "n = {n}: {steps} steps < n(n+1)/2 = {floor}"
            );
            rescanning.push(steps);
        }
        println!("rup steps for n = {sizes:?}: indexed {indexed:?}, rescanning {rescanning:?}");
        for i in 1..sizes.len() {
            // Doubling n: the indexed work about doubles (measured 6n + 7), the rescanning work
            // about quadruples (measured 3.9x).
            assert!(
                indexed[i] * 10 <= 21 * indexed[i - 1],
                "indexed: {indexed:?} for {sizes:?}"
            );
            assert!(
                rescanning[i] * 10 >= 35 * rescanning[i - 1],
                "rescanning: {rescanning:?} for {sizes:?}"
            );
        }
    }

    #[test]
    fn a_chain_missing_a_link_is_refused_by_both() {
        for drop in [0, 300, 511] {
            assert!(
                !check(512, Some(drop), false).0,
                "indexed accepted, link {drop} dropped"
            );
            assert!(
                !check(512, Some(drop), true).0,
                "rescanning accepted, link {drop} dropped"
            );
        }
    }
}

// Added in Clean (adversarial review of the indexed `rup`, 2026-10-08): tests that judge `rup` and
// whole `drup`/`drat` steps by independent references, not only by the code `indexed_rup`
// replaced. `rup_equivalence` draws at most 14 clauses over at most 7 atoms, and about two thirds
// of its cases hold an empty clause and refute at once. Here a case is judged three ways: against
// the rescanning `rup`, against a plain fixpoint over the abstract clauses (atoms and signs, not
// terms), and, when it refutes, against a truth table.
// - `long_chains_with_stale_counts_and_repeated_literals` builds clause sets around implication
//   chains through up to 40 atoms, so refutations propagate dozens of literals, with clauses the
//   chain satisfies before it falsifies their other literals (a stale count if mishandled),
//   literals repeated under double negations, complementary pairs, permuted copies and noise.
//   Of the review's mutants of `indexed_rup`, one that gives up after 16 propagations survived
//   `rup_equivalence`; this test catches it.
// - `shapes_with_known_verdicts` pins those situations one by one, each with its verdict.
// - `check_drup_is_sound` runs `check_drup` with each `rup` over random premises and `:args` that
//   interleave lemmas and deletions, in `drup` and `drat` mode, and requires every accepted
//   conclusion to hold in every model of the premises. Of five unsound mutants of `check_drup`
//   and `check_drat` (fix 22 dropped, RAT checked against only the first clause holding the
//   negated pivot, the pivot left in the resolvent, a failed lemma kept, the conclusion check
//   skipped), it catches all five; the `drup`/`drat` rule tests catch two, and the soundness
//   battery, a separate run, all five.
#[cfg(test)]
mod rup_adversarial {
    use super::*;
    use crate::ast::{pool::PrimitivePool, Sort};
    use rand::{rngs::StdRng, seq::SliceRandom, Rng, SeedableRng};

    // An abstract literal: its atom, its sign, and how many `(not (not ..))` pairs wrap its term.
    #[derive(Clone, Copy, Debug)]
    struct Lit {
        atom: usize,
        positive: bool,
        wraps: usize,
    }

    struct World {
        pool: PrimitivePool,
        atoms: Vec<Rc<Term>>,
    }

    impl World {
        fn new(atoms: usize) -> Self {
            let mut pool = PrimitivePool::new();
            let bool_sort = pool.add_sort(Sort::Bool);
            let atoms = (0..atoms)
                .map(|i| pool.add(Term::new_var(format!("p{i}"), bool_sort.clone())))
                .collect();
            World { pool, atoms }
        }

        fn term(&mut self, lit: Lit) -> Rc<Term> {
            let mut term = self.atoms[lit.atom].clone();
            if !lit.positive {
                term = build_term!(self.pool, (not { term }));
            }
            for _ in 0..lit.wraps {
                term = build_term!(self.pool, (not(not { term })));
            }
            term
        }

        fn clause(&mut self, lits: &[Lit]) -> Rc<Term> {
            let terms: Vec<Rc<Term>> = lits.iter().map(|&lit| self.term(lit)).collect();
            build_term!(self.pool, (cl[terms]))
        }

        // The premises as `check_drup` reads them: keyed by the hash of the clause term, each
        // literal as `(polarity, term with every negation removed)`.
        fn premises(&mut self, clauses: &[Vec<Lit>]) -> HashMap<u64, IndexSet<Literal>> {
            let mut map = HashMap::new();
            for lits in clauses {
                let clause = self.clause(lits);
                let mut set = IndexSet::new();
                for term in match_term!((cl ...) = &clause).unwrap() {
                    let (polarity, inner) = term.remove_all_negations_with_polarity();
                    set.insert((polarity, inner.clone()));
                }
                map.insert(hash_term(&mut self.pool, &clause), set);
            }
            map
        }
    }

    // Unit propagation from the negated goal by repeated passes over every clause, on atoms and
    // signs: whether some clause ends with every literal false.
    fn propagates_to_conflict(atoms: usize, clauses: &[Vec<Lit>], goal: &[Lit]) -> bool {
        let as_set = |lits: &[Lit]| {
            let mut set: Vec<(usize, bool)> = lits.iter().map(|l| (l.atom, l.positive)).collect();
            set.sort_unstable();
            set.dedup();
            set
        };
        let mut all: Vec<Vec<(usize, bool)>> =
            goal.iter().map(|l| vec![(l.atom, !l.positive)]).collect();
        all.extend(clauses.iter().map(|c| as_set(c)));
        let mut value = vec![None; atoms];
        loop {
            let mut changed = false;
            for clause in &all {
                if clause.iter().any(|&(atom, sign)| value[atom] == Some(sign)) {
                    continue;
                }
                let mut open = clause.iter().filter(|&&(atom, _)| value[atom].is_none());
                match (open.next(), open.next()) {
                    (None, _) => return true,
                    (Some(&(atom, sign)), None) => {
                        value[atom] = Some(sign);
                        changed = true;
                    }
                    _ => {}
                }
            }
            if !changed {
                return false;
            }
        }
    }

    // Whether the clauses and the negated goal have a common model, by truth table.
    fn satisfiable(atoms: usize, clauses: &[Vec<Lit>], goal: &[Lit]) -> bool {
        (0..1u64 << atoms).any(|model| {
            let holds = |l: &Lit| (model >> l.atom & 1 == 1) == l.positive;
            !goal.iter().any(holds) && clauses.iter().all(|c| c.iter().any(holds))
        })
    }

    // Runs `indexed_rup` on one case and judges it; returns the length of its story (0 when it
    // found no conflict).
    fn judge(world: &mut World, atoms: usize, clauses: &[Vec<Lit>], goal: &[Lit]) -> usize {
        let premises = world.premises(clauses);
        let goal_terms: Vec<Rc<Term>> = goal.iter().map(|&l| world.term(l)).collect();
        let story = indexed_rup(&mut world.pool, &premises, &goal_terms, &mut 0);
        let old = rescanning_rup::rup(&mut world.pool, &premises, &goal_terms, &mut 0);
        let expected = propagates_to_conflict(atoms, clauses, goal);
        assert!(
            story.is_some() == expected && old.is_some() == expected,
            "indexed {}, rescanning {}, reference {expected}: clauses {clauses:?} goal {goal:?}",
            story.is_some(),
            old.is_some(),
        );
        let Some(story) = story else { return 0 };
        assert!(
            super::rup_equivalence::replays(&mut world.pool, &premises, &goal_terms, &story),
            "the story does not replay: clauses {clauses:?} goal {goal:?}"
        );
        assert!(
            atoms > 12 || !satisfiable(atoms, clauses, goal),
            "UNSOUND, a refutation of a satisfiable set: clauses {clauses:?} goal {goal:?}"
        );
        story.len()
    }

    fn lit(rng: &mut StdRng, atom: usize, positive: bool) -> Lit {
        let wraps = if rng.gen_ratio(1, 4) {
            rng.gen_range(1..=2)
        } else {
            0
        };
        Lit { atom, positive, wraps }
    }

    // A clause set built around an implication chain through the atoms in a random order, which
    // the goal may start and may close into a conflict; with side literals that the chain falsifies,
    // clauses the chain satisfies before falsifying their other literals, repeated and
    // complementary literals, permuted copies, unit premises, noise, and rarely an empty clause.
    fn chain_case(rng: &mut StdRng, atoms: usize) -> (Vec<Vec<Lit>>, Vec<Lit>) {
        let mut order: Vec<usize> = (0..atoms).collect();
        order.shuffle(rng);
        let sign: Vec<bool> = (0..atoms).map(|_| rng.gen()).collect();
        // `link(i)` is the chain's i-th literal: true once the chain reaches it.
        let link = |rng: &mut StdRng, i: usize, positive: bool| {
            lit(rng, order[i], sign[order[i]] == positive)
        };
        let len = if rng.gen_ratio(3, 4) {
            rng.gen_range(atoms.div_ceil(2)..=atoms)
        } else {
            rng.gen_range(1..=atoms)
        };
        let mut clauses: Vec<Vec<Lit>> = vec![];
        for i in 0..len - 1 {
            let mut clause = vec![link(rng, i, false), link(rng, i + 1, true)];
            if i > 0 && rng.gen_ratio(1, 4) {
                let j = rng.gen_range(0..i);
                clause.push(link(rng, j, false));
            }
            if rng.gen_ratio(1, 6) {
                let k = rng.gen_range(0..clause.len());
                let mut again = clause[k];
                again.wraps += 1;
                clause.push(again);
            }
            if rng.gen_ratio(1, 40) {
                let a = rng.gen_range(0..atoms);
                clause.push(lit(rng, a, true));
                clause.push(lit(rng, a, false));
            }
            clause.shuffle(rng);
            clauses.push(clause);
        }
        // Satisfied at link i, then every other literal falsified further down the chain.
        if len >= 3 {
            for _ in 0..rng.gen_range(0..=3) {
                let i = rng.gen_range(0..len - 2);
                let j = rng.gen_range(i + 1..len);
                let k = rng.gen_range(i + 1..len);
                let mut clause = vec![link(rng, i, true), link(rng, j, false), link(rng, k, false)];
                clause.shuffle(rng);
                clauses.push(clause);
            }
        }
        for _ in 0..rng.gen_range(0..=atoms / 2 + 1) {
            let clause = (0..rng.gen_range(1..=5))
                .map(|_| {
                    let a = rng.gen_range(0..atoms);
                    let positive = rng.gen();
                    lit(rng, a, positive)
                })
                .collect();
            clauses.push(clause);
        }
        if rng.gen_ratio(1, 50) {
            clauses.push(vec![]);
        }
        for _ in 0..rng.gen_range(0..=2) {
            let mut copy = clauses.choose(rng).cloned().unwrap_or_default();
            copy.shuffle(rng);
            for l in &mut copy {
                l.wraps = rng.gen_range(0..=2);
            }
            clauses.push(copy);
        }
        clauses.shuffle(rng);
        // The goal: usually starts the chain (its negation makes link 0 true), often closes it
        // (makes the last link false), sometimes also holds a random literal.
        let mut goal = vec![];
        if rng.gen_ratio(9, 10) {
            goal.push(link(rng, 0, false));
        }
        if rng.gen_ratio(2, 3) {
            goal.push(link(rng, len - 1, true));
        }
        if rng.gen_ratio(1, 4) {
            let a = rng.gen_range(0..atoms);
            let positive = rng.gen();
            goal.push(lit(rng, a, positive));
        }
        goal.shuffle(rng);
        (clauses, goal)
    }

    #[test]
    fn long_chains_with_stale_counts_and_repeated_literals() {
        let cases = 50_000;
        let mut rng = StdRng::seed_from_u64(0x0c4a_1d5e);
        let mut world = World::new(40);
        let (mut refuted, mut open, mut deep) = (0u32, 0u32, 0u32);
        for _ in 0..cases {
            let atoms = if rng.gen_ratio(1, 2) {
                rng.gen_range(1..=12)
            } else {
                rng.gen_range(13..=40)
            };
            let (clauses, goal) = chain_case(&mut rng, atoms);
            match judge(&mut world, atoms, &clauses, &goal) {
                0 => open += 1,
                story => {
                    refuted += 1;
                    deep += u32::from(story > 20);
                }
            }
        }
        // Both verdicts, and refutations that propagate more than 20 literals, are exercised.
        assert!(
            refuted > cases / 10 && open > cases / 10 && deep > cases / 100,
            "refuted {refuted} (deeper than 20: {deep}) open {open} of {cases}"
        );
    }

    #[test]
    fn shapes_with_known_verdicts() {
        let l = |atom: usize, positive: bool, wraps: usize| Lit { atom, positive, wraps };
        let (a, b, c) = (0, 1, 2);
        let cases: Vec<(&str, Vec<Vec<Lit>>, Vec<Lit>, bool)> = vec![
            (
                "a clause satisfied first and fully assigned later is no conflict",
                vec![
                    vec![l(a, true, 0)],
                    vec![l(a, true, 0), l(b, true, 0), l(c, true, 0)],
                    vec![l(a, false, 0), l(b, false, 0)],
                    vec![l(a, false, 0), l(c, false, 0)],
                ],
                vec![],
                false,
            ),
            (
                "the same, satisfied by a negated goal literal",
                vec![
                    vec![l(a, true, 1), l(b, true, 0), l(c, true, 2)],
                    vec![l(a, false, 0), l(b, false, 1)],
                    vec![l(a, false, 2), l(c, false, 0)],
                ],
                vec![l(a, false, 0)],
                false,
            ),
            (
                "a complementary pair is never unit",
                vec![vec![l(a, true, 0), l(a, false, 1), l(b, true, 0)]],
                vec![l(b, true, 0)],
                false,
            ),
            (
                "one literal under three spellings counts once, and is unit",
                vec![
                    vec![l(a, true, 0), l(a, true, 1), l(a, true, 2), l(b, true, 0)],
                    vec![l(a, false, 2)],
                ],
                vec![l(b, true, 1)],
                true,
            ),
            (
                "a goal with a complementary pair refutes on its own",
                vec![],
                vec![l(a, true, 0), l(a, false, 1)],
                true,
            ),
            (
                "a goal literal repeated is no conflict",
                vec![vec![l(b, true, 0)]],
                vec![l(a, true, 0), l(a, true, 2)],
                false,
            ),
            (
                "a goal literal that is also a premise unit",
                vec![vec![l(a, true, 1)]],
                vec![l(a, true, 0)],
                true,
            ),
            (
                "a permuted copy of a clause is the same clause",
                vec![
                    vec![l(a, true, 0), l(b, true, 0)],
                    vec![l(b, true, 1), l(a, true, 0)],
                    vec![l(a, false, 0)],
                ],
                vec![l(b, true, 0)],
                true,
            ),
            (
                "an empty premise refutes anything",
                vec![vec![]],
                vec![],
                true,
            ),
            ("no clauses and an empty goal", vec![], vec![], false),
        ];
        let mut world = World::new(3);
        for (name, clauses, goal, expected) in cases {
            assert_eq!(
                judge(&mut world, 3, &clauses, &goal) > 0,
                expected,
                "{name}"
            );
        }
    }

    // An entry of a `drup` step's `:args`: a lemma, or a `(@d ..)` deletion.
    enum Arg {
        Lemma(Vec<Lit>),
        Delete(Vec<Lit>),
    }

    // One `check_drup` call over random premises and `:args` that interleave lemmas and
    // deletions, run with each `rup`. A lemma is often derivable: a resolvent of two premises, a
    // premise weakened or with a literal dropped; a deletion names a premise, an earlier lemma, a
    // clause not present, or `(cl)`. The two results must agree, and an accepted conclusion must
    // be implied by the premises (the empty one: they are unsatisfiable). Returns whether the step
    // was accepted.
    fn check_drup_case(world: &mut World, rng: &mut StdRng) -> bool {
        let atoms = rng.gen_range(1..=6);
        let random_clause = |rng: &mut StdRng, max: usize| -> Vec<Lit> {
            (0..rng.gen_range(0..=max))
                .map(|_| {
                    let a = rng.gen_range(0..atoms);
                    let positive = rng.gen();
                    lit(rng, a, positive)
                })
                .collect()
        };
        let premises: Vec<Vec<Lit>> = (0..rng.gen_range(0..=8))
            .map(|_| {
                let mut clause = random_clause(rng, 3);
                if clause.is_empty() && !rng.gen_ratio(1, 10) {
                    clause = random_clause(rng, 3);
                }
                clause
            })
            .collect();
        let mut args: Vec<Arg> = vec![];
        let mut lemmas: Vec<Vec<Lit>> = vec![];
        for _ in 0..rng.gen_range(1..=4) {
            let pick = |rng: &mut StdRng, from: &[Vec<Lit>]| from.choose(rng).cloned();
            let arg = match rng.gen_range(0..10) {
                0..=2 => {
                    // A resolvent of two premises on a clashing atom, when there is one.
                    let (p, q) = (pick(rng, &premises), pick(rng, &premises));
                    let resolvent = p.zip(q).and_then(|(p, q)| {
                        let pivot = p.iter().find(|x| {
                            q.iter()
                                .any(|y| y.atom == x.atom && y.positive != x.positive)
                        })?;
                        let atom = pivot.atom;
                        Some(
                            p.iter()
                                .chain(&q)
                                .filter(|x| x.atom != atom)
                                .copied()
                                .collect(),
                        )
                    });
                    Arg::Lemma(resolvent.unwrap_or_else(|| random_clause(rng, 3)))
                }
                3 => {
                    let mut weaker = pick(rng, &premises).unwrap_or_default();
                    weaker.extend(random_clause(rng, 1));
                    weaker.shuffle(rng);
                    Arg::Lemma(weaker)
                }
                4 => {
                    let mut stronger = pick(rng, &premises).unwrap_or_default();
                    if !stronger.is_empty() {
                        stronger.remove(rng.gen_range(0..stronger.len()));
                    }
                    Arg::Lemma(stronger)
                }
                5 => Arg::Lemma(vec![]),
                6 => Arg::Lemma(random_clause(rng, 3)),
                7 => Arg::Delete(pick(rng, &premises).unwrap_or_default()),
                8 => Arg::Delete(pick(rng, &lemmas).unwrap_or_default()),
                _ => Arg::Delete(random_clause(rng, 2)),
            };
            if let Arg::Lemma(lemma) = &arg {
                lemmas.push(lemma.clone());
            }
            args.push(arg);
        }
        let conclusion: Vec<Lit> = match rng.gen_range(0..10) {
            0..=5 => lemmas.last().cloned().unwrap_or_default(),
            6 => {
                let mut permuted = lemmas.last().cloned().unwrap_or_default();
                permuted.reverse();
                permuted
            }
            7 => premises.choose(rng).cloned().unwrap_or_default(),
            _ => random_clause(rng, 3),
        };
        let check_rat = rng.gen_ratio(1, 3);

        let premise_terms: Vec<Rc<Term>> = premises.iter().map(|p| world.clause(p)).collect();
        let conclusion_term = world.clause(&conclusion);
        let arg_terms: Vec<Rc<Term>> = args
            .iter()
            .map(|arg| match arg {
                Arg::Lemma(lemma) => world.clause(lemma),
                Arg::Delete(clause) => {
                    let clause = world.clause(clause);
                    build_term!(world.pool, (delete { clause }))
                }
            })
            .collect();
        let mut run = |rescanning: bool| {
            super::rup_cost::select_rescanning(rescanning);
            let result = check_drup(
                &mut world.pool,
                conclusion_term.clone(),
                &premise_terms,
                &arg_terms,
                check_rat,
            );
            super::rup_cost::select_rescanning(false);
            result.map(|_| ()).map_err(|e| format!("{e:?}"))
        };
        let (indexed, rescanning) = (run(false), run(true));
        let case = || {
            format!(
                "premises {premises:?} lemmas {lemmas:?} conclusion {conclusion:?} rat {check_rat}"
            )
        };
        assert_eq!(indexed, rescanning, "{}", case());
        // No model of the premises falsifies every literal of an accepted conclusion.
        assert!(
            indexed.is_err() || !satisfiable(atoms, &premises, &conclusion),
            "UNSOUND, accepted an unimplied conclusion: {}",
            case()
        );
        indexed.is_ok()
    }

    #[test]
    fn check_drup_is_sound() {
        let mut rng = StdRng::seed_from_u64(0xd2a7_de1e);
        let mut world = World::new(6);
        let accepted = (0..100_000)
            .filter(|_| check_drup_case(&mut world, &mut rng))
            .count();
        assert!((10_000..90_000).contains(&accepted), "accepted {accepted}");
    }
}
