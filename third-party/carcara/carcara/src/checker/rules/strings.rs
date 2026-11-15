use super::{
    assert_clause_len, assert_eq, assert_num_args, assert_num_premises, get_premise_term, RuleArgs,
    RuleResult,
};
use crate::{
    ast::{
        build_term, match_term_err,
        pool::{StepTerms, TermPool},
        Binder, BindingList, Constant, MatchCase, Operator, Polyeq, Rc, Sort, Term,
    },
    checker::{
        budget::ExpansionBudget,
        error::{CheckerError, EqualityError},
        rules::assert_polyeq,
    },
};
use std::{cmp, collections::HashMap, time::Duration};

/// Added in Clean: how a flattening treats a string constant. `string_concat_flatten` splits it
/// into its characters; `concat_extract` keeps it whole, and drops it when it is empty.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Constants {
    Split = 0,
    Keep = 1,
}

/// Added in Clean: what flattening a term costs, counted before it is built (see `StringStep`).
#[derive(Clone, Copy)]
struct FlatCount {
    /// Words charged: one for each term the walk visits, once per path to it, and one more for
    /// each character past the first a split constant becomes.
    cost: u128,
    /// The length of the flattening.
    entries: u128,
}

/// Modified in Clean: what one application of a string rule builds, and what it is charged.
///
/// Upstream flattened `str.++` applications (`string_concat_flatten`, `concat_extract`) and
/// expanded string constants (`expand_string_constants`) by recursive walks without a cache, once
/// per path to a shared (`:named`) subterm, and added what it built to the pool:
/// `concat_eq` over `(= n24 n24)`, `n_i = (str.++ n_(i-1) n_(i-1))` named in the problem, took a
/// 1 KB input to 776 MB, doubling with each level, and a walk over a shared subterm with nothing to
/// build (a conclusion's doubled `and`s, a chain of `(str.++ "" "")`) took time exponential in its
/// depth. Each accepted step also left its flattenings in the pool for the rest of the proof.
///
/// Now a flattening is charged to the step's `ExpansionBudget` before it is built, in words: what
/// it would visit and build (`FlatCount`), counted over the DAG with a count memoised per term, so
/// counting is linear in the step's terms. A step past the budget is refused. The walks are loops,
/// and `expand_string_constants` expands each term once (an expansion depends on the term alone).
/// Every term a rule builds is hash-consed in `terms`, a `StepTerms` the step owns, not added to
/// the pool: a term the pool holds is the pool's `Rc`, any other is the step's, so every
/// comparison by pointer is the one it was when the pool interned them, and the step's terms are
/// freed when it ends (see checker/budget.rs and third-party/carcara/DOWNSTREAM.md).
struct StringStep<'p> {
    terms: StepTerms<'p>,
    budget: ExpansionBudget,
    /// `FlatCount` per term, one table per `Constants`.
    counts: [HashMap<Rc<Term>, FlatCount>; 2],
    /// The one-character constant each character becomes.
    chars: HashMap<char, Rc<Term>>,
    /// What `expand_string_constants` made of each term it expanded.
    expansions: HashMap<Rc<Term>, Rc<Term>>,
    /// What compares entries of flattenings: `polyeq`'s comparator, one a step.
    comparator: Polyeq,
}

impl<'p> StringStep<'p> {
    fn new(pool: &'p dyn TermPool) -> Self {
        Self {
            terms: StepTerms::new(pool),
            budget: ExpansionBudget::new(),
            counts: [HashMap::new(), HashMap::new()],
            chars: HashMap::new(),
            expansions: HashMap::new(),
            comparator: Polyeq::new().mod_reordering(true),
        }
    }

    /// `polyeq(a, b)`, through one comparator for the whole step. A flattening repeats the entries
    /// of a shared subterm, and comparing two terms walks them: 16,384 entries that differ from
    /// their counterparts only in the order of an equality 10,000 levels down took 7 s to strip,
    /// four times as long for each level of sharing more. And distinct entries can share a deep
    /// subterm: `(str.at X_d i)` against `(str.at Y_d i)` for `i < n`, `X_d` and `Y_d` equal only
    /// modulo the order of an equality `d` levels down, took time `n x d` with a comparator for
    /// each pair (1.05 s at `d = n = 4,000`, 615 KB). The comparator caches every pair of terms it
    /// decides (`Polyeq`; without alpha-equivalence its cache is one map), so each pair of
    /// subterms is decided once a step; `polyeq` depends on the pair alone, so the answers are the
    /// same.
    fn polyeq(&mut self, a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> bool {
        self.comparator.eq_with_time(a, b, time)
    }

    /// The term, hash-consed with the pool's (see `StepTerms`).
    fn add(&mut self, term: Term) -> Rc<Term> {
        self.terms.add(term)
    }

    fn char_term(&mut self, c: char) -> Rc<Term> {
        if let Some(term) = self.chars.get(&c) {
            return term.clone();
        }
        let term = self.terms.add(Term::Const(Constant::String(c.to_string())));
        self.chars.insert(c, term.clone());
        term
    }

    /// What flattening `root` costs, counted over the DAG, each term once.
    fn count(&mut self, root: &Rc<Term>, mode: Constants) -> FlatCount {
        let counts = &mut self.counts[mode as usize];
        let mut stack: Vec<(&Rc<Term>, bool)> = vec![(root, false)];
        while let Some((term, ready)) = stack.pop() {
            if counts.contains_key(term) {
                continue;
            }
            let count = match term.as_ref() {
                Term::Op(Operator::StrConcat, args) if !ready => {
                    stack.push((term, true));
                    stack.extend(
                        args.iter()
                            .rev()
                            .filter(|a| !counts.contains_key(*a))
                            .map(|a| (a, false)),
                    );
                    continue;
                }
                Term::Op(Operator::StrConcat, args) => {
                    args.iter()
                        .fold(FlatCount { cost: 1, entries: 0 }, |acc, arg| {
                            let c = counts[arg];
                            FlatCount {
                                cost: acc.cost.saturating_add(c.cost),
                                entries: acc.entries.saturating_add(c.entries),
                            }
                        })
                }
                Term::Const(Constant::String(s)) => {
                    let chars = s.chars().count() as u128;
                    match mode {
                        Constants::Split => FlatCount { cost: chars.max(1), entries: chars },
                        Constants::Keep => FlatCount {
                            cost: 1,
                            entries: (chars > 0).into(),
                        },
                    }
                }
                _ => FlatCount { cost: 1, entries: 1 },
            };
            counts.insert(term.clone(), count);
        }
        counts[root]
    }

    /// The flat form of `term`: the arguments of its nested `str.++` applications, in order, with
    /// string constants split into characters (`Constants::Split`) or kept whole, the empty word
    /// dropped (`Constants::Keep`). Charged before it is built.
    fn flatten(&mut self, term: &Rc<Term>, mode: Constants) -> Result<Vec<Rc<Term>>, CheckerError> {
        let count = self.count(term, mode);
        self.budget
            .spend_words("flattening a string concatenation", count.cost)?;
        // Within the budget, so it fits in a `usize`.
        let mut flat = Vec::with_capacity(count.entries as usize);
        let mut stack = vec![std::slice::from_ref(term).iter()];
        while let Some(args) = stack.last_mut() {
            let Some(arg) = args.next() else {
                stack.pop();
                continue;
            };
            match arg.as_ref() {
                Term::Const(Constant::String(s)) => match mode {
                    Constants::Split => {
                        for c in s.chars() {
                            flat.push(self.char_term(c));
                        }
                    }
                    Constants::Keep => {
                        if !s.is_empty() {
                            flat.push(arg.clone());
                        }
                    }
                },
                Term::Op(Operator::StrConcat, inner) => stack.push(inner.iter()),
                _ => flat.push(arg.clone()),
            }
        }
        Ok(flat)
    }

    /// A function that takes an `Rc<Term>` and returns a vector corresponding to
    /// the flat form of that term.
    ///
    /// In this flat form, all `str.++` applications are dissolved and every
    /// argument of those applications is inserted into the vector (e.g., `(str.++
    /// a (str.++ b c))` would lead to `[a, b, c]`, where `a`, `b` and `c` are
    /// arbitrary String terms). Furthermore, all String constants are broken
    /// into constants of size one and are inserted into the vector too.
    ///
    /// All String terms that aren't `str.++` applications can be seen as `(str.++ term "")`.
    /// So, applying `flatten` to them would lead to `[term]`. Furthermore,
    /// the empty String isn't mapped to any entry in the vector, so `flatten`
    /// applied to `""` leads to an empty vector.
    fn string_concat_flatten(&mut self, term: &Rc<Term>) -> Result<Vec<Rc<Term>>, CheckerError> {
        self.flatten(term, Constants::Split)
    }

    /// A function that takes an `Rc<Term>` and returns a vector corresponding to
    /// the flat form of that term.
    ///
    /// It works almost the same as `string_concat_flatten`, but it does not split string constants.
    fn concat_extract(&mut self, term: &Rc<Term>) -> Result<Vec<Rc<Term>>, CheckerError> {
        self.flatten(term, Constants::Keep)
    }

    /// A function to standardize String constants and `str.++` applications
    /// across a term.
    ///
    /// It takes an `Rc<Term>` and returns an equivalent `Rc<Term>` where all String
    /// constants of size greater than one are broken into `str.++` applications
    /// of their characters (`"abc"` would become `(str.++ "a" "b" "c")`), and
    /// nested `str.++` applications are dissolved, remaining just one application
    /// with all the previous nested arguments (e.g., `(str.++ a (str.++ b (str.++ c "")))` would lead to `(str.++ a b c)`).
    ///
    /// Modified in Clean: each term is expanded once, children first (an expansion depends on the
    /// term alone), by a loop; a `str.++` application is its flattening's arguments, charged as
    /// `string_concat_flatten` charges it.
    fn expand_string_constants(&mut self, root: &Rc<Term>) -> Result<Rc<Term>, CheckerError> {
        let mut stack: Vec<(&Rc<Term>, bool)> = vec![(root, false)];
        while let Some((term, ready)) = stack.pop() {
            if self.expansions.contains_key(term) {
                continue;
            }
            if !ready {
                let pending: Vec<_> = expansion_children(term)
                    .into_iter()
                    .filter(|c| !self.expansions.contains_key(*c))
                    .collect();
                if !pending.is_empty() {
                    stack.push((term, true));
                    stack.extend(pending.into_iter().rev().map(|c| (c, false)));
                    continue;
                }
            }
            let expanded = |step: &Self, c: &Rc<Term>| step.expansions[c].clone();
            let result = match term.as_ref() {
                Term::Const(Constant::String(_)) => {
                    let mut args = self.string_concat_flatten(term)?;
                    match args.len() {
                        0 => self.add(Term::new_string("")),
                        1 => args.pop().unwrap(),
                        _ => self.add(Term::Op(Operator::StrConcat, args)),
                    }
                }
                Term::Op(Operator::StrConcat, _) => {
                    // (str.++ "a" (str.++ "b" "c")) => (str.++ "a" "b" "c")
                    let new_args = self.string_concat_flatten(term)?;
                    self.add(Term::Op(Operator::StrConcat, new_args))
                }
                Term::Op(op, args) => {
                    let new_args = args.iter().map(|a| expanded(self, a)).collect();
                    self.add(Term::Op(*op, new_args))
                }
                Term::App(func, args) => {
                    let new_args = args.iter().map(|a| expanded(self, a)).collect();
                    self.add(Term::App(func.clone(), new_args))
                }
                Term::Let(binding, inner) => {
                    let new_inner = expanded(self, inner);
                    self.add(Term::Let(binding.clone(), new_inner))
                }
                Term::Binder(q, bindings, inner) => {
                    let new_inner = expanded(self, inner);
                    self.add(Term::Binder(*q, bindings.clone(), new_inner))
                }
                Term::ParamOp { op, op_args, args } => {
                    let new_args = args.iter().map(|a| expanded(self, a)).collect();
                    self.add(Term::ParamOp {
                        op: *op,
                        op_args: op_args.clone(),
                        args: new_args,
                    })
                }
                Term::AsOp(op, sort, args) => {
                    let new_args = args.iter().map(|a| expanded(self, a)).collect();
                    self.add(Term::AsOp(*op, sort.clone(), new_args))
                }
                Term::Match(t, cases) => {
                    let new_t = expanded(self, t);
                    let new_cases = cases
                        .iter()
                        .map(|case| MatchCase {
                            pattern: case.pattern.clone(),
                            body: expanded(self, &case.body),
                        })
                        .collect();
                    self.add(Term::Match(new_t, new_cases))
                }
                Term::Var(..) | Term::Const(_) => term.clone(),
            };
            self.expansions.insert(term.clone(), result);
        }
        Ok(self.expansions[root].clone())
    }
}

/// Added in Clean: the subterms `expand_string_constants` expands to expand `term` (a `str.++`
/// application or a string constant is flattened instead).
fn expansion_children(term: &Rc<Term>) -> Vec<&Rc<Term>> {
    match term.as_ref() {
        Term::Op(Operator::StrConcat, _) | Term::Var(..) | Term::Const(_) => Vec::new(),
        Term::Op(_, args)
        | Term::App(_, args)
        | Term::ParamOp { args, .. }
        | Term::AsOp(_, _, args) => args.iter().collect(),
        Term::Let(_, inner) | Term::Binder(_, _, inner) => vec![inner],
        Term::Match(t, cases) => std::iter::once(t)
            .chain(cases.iter().map(|case| &case.body))
            .collect(),
    }
}

/// Modified in Clean: the first position `i` short of the last character of `s` from which the rest
/// of `s` is compatible with `t`, one of the two words being a prefix of the other, or the last
/// position when there is none. Upstream recursed once per position, copying the rest of `s` and
/// all of `t` at each one, and compared the words there by a recursion (`is_compatible`) that
/// copied the rest of both at each character, so a 10,000-character constant took past 1.7 GB and
/// 120 s (time cubic, memory quadratic in its length). The longest common prefix of `t` and every
/// suffix of `s` is now read off one Z-array, in time and memory linear in both, and the position
/// is the one upstream's recursion returned: `i` is compatible exactly when that prefix is as long
/// as the shorter of `t` and `s[i..]` (see third-party/carcara/DOWNSTREAM.md).
fn overlap(s: &[Rc<Term>], t: &[Rc<Term>]) -> usize {
    let last = s.len().saturating_sub(1);
    // `t`, a separator equal to no character, then `s`: `z[t.len() + 1 + i]` is the longest common
    // prefix of `s[i..]` and `t`, the separator ending every match within `t`.
    let word: Vec<Option<&Rc<Term>>> = t
        .iter()
        .map(Some)
        .chain(std::iter::once(None))
        .chain(s.iter().map(Some))
        .collect();
    let z = z_array(&word);
    (0..last)
        .find(|&i| z[t.len() + 1 + i] == cmp::min(s.len() - i, t.len()))
        .unwrap_or(last)
}

/// Added in Clean: `z[i]` is the length of the longest common prefix of `word` and `word[i..]`
/// (`z[0]` is the whole length), computed in linear time (the Z-algorithm).
fn z_array<T: PartialEq>(word: &[T]) -> Vec<usize> {
    let n = word.len();
    let mut z = vec![0; n];
    if let Some(first) = z.first_mut() {
        *first = n;
    }
    // `[l, r)` is the rightmost window found so far that matches a prefix of `word`.
    let (mut l, mut r) = (0, 0);
    for i in 1..n {
        let mut k = if i < r { cmp::min(r - i, z[i - l]) } else { 0 };
        while i + k < n && word[k] == word[i + k] {
            k += 1;
        }
        z[i] = k;
        if i + k > r {
            (l, r) = (i, i + k);
        }
    }
    z
}

/// A function to reconstruct a term given its flat form.
///
/// It takes a vector of `Rc<Term>` and returns a new term based on the length
/// of the flat form vector. If the vector is empty, it's equivalent to the
/// empty String. If the length is equal to one, the only term of the vector
/// is returned. Finally, if the length is greater than one, an `str.++`
/// application is returned with the flat form vector as its arguments (e.g.,
/// `[a, "b", c]` would lead to `(str.++ a "b" c)`, where `a` and `c` are
/// arbitrary terms).
fn concat(step: &mut StringStep, terms: Vec<Rc<Term>>) -> Rc<Term> {
    match terms.len() {
        0 => step.add(Term::new_string("")),
        1 => terms[0].clone(),
        _ => step.add(Term::Op(Operator::StrConcat, terms)),
    }
}

/// A function to check if a term is a prefix or suffix of another.
///
/// It takes two `Rc<Term>` and a reverse parameter. If the reverse parameter is
/// set to `false`, it checks if the second term is a prefix of the first one,
/// and if it's set to `true`, it checks if it's a suffix.
///
/// The function throws an error if the prefix/suffix is larger than the main
/// term. It returns the prefix/suffix in flat form if the check was successful.
fn is_prefix_or_suffix(
    step: &mut StringStep,
    term: Rc<Term>,
    pref: Rc<Term>,
    rev: bool,
    polyeq_time: &mut Duration,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    let mut t_flat = step.string_concat_flatten(&term)?;
    let mut p_flat = step.string_concat_flatten(&pref)?;
    if rev {
        t_flat.reverse();
        p_flat.reverse();
    }
    if p_flat.len() > t_flat.len() {
        if rev {
            return Err(CheckerError::ExpectedToBeSuffix(pref, term));
        } else {
            return Err(CheckerError::ExpectedToBePrefix(pref, term));
        }
    }
    // Modified in Clean: each pair of terms is decided once a step (see `StringStep::polyeq`).
    for (el, expected) in p_flat.iter().zip(&t_flat) {
        if !step.polyeq(el, expected, polyeq_time) {
            return Err(EqualityError::ExpectedToBe {
                expected: expected.clone(),
                got: el.clone(),
            }
            .into());
        }
    }
    if rev {
        p_flat.reverse();
    }
    Ok(p_flat)
}

/// An application of `is_prefix_or_suffix` where the reverse parameter is set
/// to `false` by default.
fn is_prefix(
    step: &mut StringStep,
    term: Rc<Term>,
    pref: Rc<Term>,
    polyeq_time: &mut Duration,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    is_prefix_or_suffix(step, term, pref, false, polyeq_time)
}

/// An application of `is_prefix_or_suffix` where the reverse parameter is set
/// to `true` by default.
fn is_suffix(
    step: &mut StringStep,
    term: Rc<Term>,
    pref: Rc<Term>,
    polyeq_time: &mut Duration,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    is_prefix_or_suffix(step, term, pref, true, polyeq_time)
}

type Suffixes = (Vec<Rc<Term>>, Vec<Rc<Term>>);

/// A function to remove the longest common prefix or suffix.
///
/// It takes two `Rc<Term>` and a reverse parameter. If the parameter is set to
/// `false`, it removes the longest common prefix, and if it's set to `true`,
/// the longest common suffix.
///
/// The function throws an error if the terms aren't `str.++` applications.
/// It returns two vectors with the remaining terms after the removal in flat
/// form (e.g., the remaining suffixes after a prefix removal or vice versa).
///
/// If the terms don't share common prefixes or suffixes, the function
/// doesn't remove anything, so the tuple returned is the flat form for both of
/// them.
fn strip_prefix_or_suffix(
    step: &mut StringStep,
    s: Rc<Term>,
    t: Rc<Term>,
    rev: bool,
    polyeq_time: &mut Duration,
) -> Result<Suffixes, CheckerError> {
    let mut s_flat = step.string_concat_flatten(&s)?;
    let mut t_flat = step.string_concat_flatten(&t)?;
    if rev {
        s_flat.reverse();
        t_flat.reverse();
    }
    if s_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s));
    }
    if t_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t));
    }
    let mut prefix = 0;
    // Modified in Clean: each pair of terms is decided once a step (see `StringStep::polyeq`).
    while (prefix < cmp::min(s_flat.len(), t_flat.len()))
        && step.polyeq(&s_flat[prefix], &t_flat[prefix], polyeq_time)
    {
        prefix += 1;
    }
    // Modified in Clean: the common part is drained in place rather than the rest copied.
    s_flat.drain(..prefix);
    t_flat.drain(..prefix);
    let (mut s_suffix, mut t_suffix) = (s_flat, t_flat);
    if rev {
        s_suffix.reverse();
        t_suffix.reverse();
    }
    Ok((s_suffix, t_suffix))
}

/// A function to check if a String has a length equal to one.
///
/// It takes an `Rc<Term>` and throws an error if the term isn't a String
/// constant (we can't compute lengths properly in this case) or isn't a String
/// constant of size one.
fn string_check_length_one(term: Rc<Term>) -> Result<(), CheckerError> {
    if let Term::Const(Constant::String(s)) = term.as_ref() {
        if s.len() == 1 {
            return Ok(());
        }
    }
    Err(CheckerError::ExpectedStringConstantOfLengthOne(term))
}

fn build_skolem_prefix(step: &mut StringStep, u: Rc<Term>, n: Rc<Term>) -> Rc<Term> {
    build_term!(step, (strsubstr {u.clone()} 0 {n.clone()}))
}

fn build_skolem_suffix_rem(step: &mut StringStep, u: Rc<Term>, n: Rc<Term>) -> Rc<Term> {
    build_term!(step, (strsubstr {u.clone()} {n.clone()} (- (strlen {u.clone()}) {n})))
}

fn build_skolem_suffix(step: &mut StringStep, u: Rc<Term>, n: Rc<Term>) -> Rc<Term> {
    build_term!(step, (strsubstr {u.clone()} (- (strlen {u.clone()}) {n.clone()}) {n.clone()}))
}

fn build_skolem_unify_split_prefix(step: &mut StringStep, t: Rc<Term>, s: Rc<Term>) -> Rc<Term> {
    let t_len = step.add(Term::Op(Operator::StrLen, vec![t.clone()]));
    let s_len = step.add(Term::Op(Operator::StrLen, vec![s.clone()]));
    let true_branch = build_skolem_suffix_rem(step, t.clone(), s_len).clone();
    let false_branch = build_skolem_suffix_rem(step, s.clone(), t_len).clone();
    build_term!(step, (ite (>= (strlen {t.clone()}) (strlen {s.clone()})) {true_branch} {false_branch}))
}

fn build_skolem_unify_split_suffix(step: &mut StringStep, t: Rc<Term>, s: Rc<Term>) -> Rc<Term> {
    let t_len = step.add(Term::Op(Operator::StrLen, vec![t.clone()]));
    let s_len = step.add(Term::Op(Operator::StrLen, vec![s.clone()]));
    let n_t = build_term!(step, (- {t_len.clone()} {s_len.clone()}));
    let n_s = build_term!(step, (- {s_len.clone()} {t_len.clone()}));
    let true_branch = build_skolem_prefix(step, t.clone(), n_t).clone();
    let false_branch = build_skolem_prefix(step, s.clone(), n_s).clone();
    build_term!(step, (ite (>= (strlen {t.clone()}) (strlen {s.clone()})) {true_branch} {false_branch}))
}

fn build_str_suffix_len(step: &mut StringStep, s: Rc<Term>, n: Rc<Term>) -> Rc<Term> {
    build_term!(step, (strsubstr {s.clone()} (- (strlen {s.clone()}) {n.clone()}) {n.clone()}))
}

/// Checks that a flattened string term consists of string constants only (and, unless
/// `allow_empty`, that it is not the empty word).
fn require_constant_word(term: &Rc<Term>, flat: &[Rc<Term>], allow_empty: bool) -> RuleResult {
    if (flat.is_empty() && !allow_empty)
        || !flat
            .iter()
            .all(|t| matches!(t.as_ref(), Term::Const(Constant::String(_))))
    {
        return Err(CheckerError::TermOfWrongForm(
            "a string constant",
            term.clone(),
        ));
    }
    Ok(())
}

/// Helper function to properly extract the arguments of the `concat_cprop` rule.
fn extract_arguments(t: &Rc<Term>) -> Result<Vec<Rc<Term>>, CheckerError> {
    let args_t = match t.as_ref() {
        Term::Op(Operator::StrConcat, args) => {
            if args.len() != 3 {
                return Err(CheckerError::TermOfWrongForm(
                    "(str.++ t1 t2 t3)",
                    t.clone(),
                ));
            }
            args
        }
        _ => {
            return Err(CheckerError::TermOfWrongForm(
                "(str.++ t1 t2 t3)",
                t.clone(),
            ))
        }
    };
    Ok(args_t.clone())
}

/// A function that takes a list of regular expressions and returns the term corresponding to the
/// application of the concatenation operator to them.
///
/// If the list contains only one regular expression, it returns it directly.
fn singleton_elim(step: &mut StringStep, r_list: Vec<Rc<Term>>) -> Rc<Term> {
    match r_list.len() {
        1 => r_list[0].clone(),
        _ => step.add(Term::Op(Operator::ReConcat, r_list)),
    }
}

/// Helper function for implementing the `re_kleene_unfold_pos` and `re_concat_unfold_pos` rules.
///
/// Modified in Clean: the concatenation of the words of `r`'s arguments, `(str.++ s_1 (str.++ s_2
/// ... (str.++ s_n "")))`, when every argument of the `re.++` is a `(str.to_re s_i)`. An argument
/// that is not would be named by a Skolem witness the premise does not determine, so the
/// application is refused there, before anything is built (see `skolem_witness_refused`).
///
/// Upstream recursed once per argument, added the rest of the list to the pool as a new `re.++` at
/// each level, and built a witness for each argument that is not a `str.to_re`, naming every one
/// before it: over 20,000 `str.to_re` arguments (a 400 KB proof) the step took 1.7 GB, over 50,000
/// past 8 GB, and over 5,000 other arguments (10 KB) it built 2.4 GB of witnesses in 14 s before
/// it was refused. The words are now read in one pass and the chain built from its end, in time
/// and memory linear in the arguments; it is the term upstream built (see
/// third-party/carcara/DOWNSTREAM.md).
fn re_unfold_pos_concat(
    step: &mut StringStep,
    rule: &str,
    r: &Rc<Term>,
) -> Result<Rc<Term>, CheckerError> {
    let Term::Op(Operator::ReConcat, args) = r.as_ref() else {
        return Err(CheckerError::CannotApplyReUnfoldPos(r.clone()));
    };
    let words = args
        .iter()
        .map(|arg| match arg.as_ref() {
            Term::Op(Operator::StrToRe, word) if word.len() == 1 => Ok(word[0].clone()),
            _ => Err(skolem_witness_refused(rule)),
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut chain = step.add(Term::new_string(""));
    for word in words.into_iter().rev() {
        chain = build_term!(step, (strconcat {word} {chain}));
    }
    Ok(chain)
}

/// A function to calculate the fixed length of a regular expression `r` (size of strings that
/// match that RE) if it can be inferred.
///
/// It takes an `Rc<Term>` and recursively match over the regular expression operators whose length
/// can be inferred. It throws an error if the term length cannot be evaluated, i.e., if the length
/// of the term itself or one of its arguments cannot be inferred.
///
/// Modified in Clean: upstream recursed once per path to a shared (`:named`) subterm, so a `re.++`
/// of two copies of a `re.++` of two copies ..., 30 deep, took time exponential in its depth. Each
/// subterm is now measured once, children first, by a loop, and the arguments are combined in
/// upstream's order, so the result, error included, is the one its recursion returned: the first
/// argument that cannot be measured (in a union or an intersection, after those it ignores), or
/// the union or intersection itself where two lengths differ. A length past a `usize`, which
/// upstream's recursion would have reached only after as many steps (and then overflowed), cannot
/// be evaluated (see third-party/carcara/DOWNSTREAM.md).
fn str_fixed_len_re(r: &Rc<Term>) -> Result<usize, CheckerError> {
    /// Upstream's `has_same_length`, over measured arguments: the length all the arguments not
    /// headed by `ignore` share.
    fn has_same_length<'a>(
        lengths: &HashMap<&'a Rc<Term>, Result<usize, &'a Rc<Term>>>,
        args: &'a [Rc<Term>],
        r: &'a Rc<Term>,
        ignore: Operator,
    ) -> Result<usize, &'a Rc<Term>> {
        let should_ignore = |term: &Term| term.as_op().is_some_and(|(op, _)| op == ignore);
        let mut iter = args
            .iter()
            .filter(|a| !should_ignore(a))
            .map(|a| lengths[a]);
        let Some(first) = iter.next() else {
            return Err(r);
        };
        let first = first?;
        for size in iter {
            if size? != first {
                return Err(r);
            }
        }
        Ok(first)
    }

    // The length of each subterm measured, or the subterm whose length cannot be evaluated.
    let mut lengths: HashMap<&Rc<Term>, Result<usize, &Rc<Term>>> = HashMap::new();
    let mut stack = vec![(r, false)];
    while let Some((term, ready)) = stack.pop() {
        if lengths.contains_key(term) {
            continue;
        }
        let length = match term.as_ref() {
            Term::Op(Operator::ReConcat | Operator::ReUnion | Operator::ReIntersection, args)
                if !ready =>
            {
                stack.push((term, true));
                stack.extend(args.iter().rev().map(|a| (a, false)));
                continue;
            }
            Term::Op(Operator::ReConcat, args) => args
                .iter()
                .try_fold(0usize, |acc, a| acc.checked_add(lengths[a]?).ok_or(term)),
            Term::Op(Operator::ReAllChar, _) => Ok(1),
            Term::Op(Operator::ReRange, _) => Ok(1),
            Term::Op(Operator::StrToRe, args) => match args.first().map(Rc::as_ref) {
                Some(Term::Const(Constant::String(s))) => Ok(s.len()),
                _ => Err(term),
            },
            Term::Op(Operator::ReUnion, args) => {
                has_same_length(&lengths, args, term, Operator::ReNone)
            }
            Term::Op(Operator::ReIntersection, args) => {
                has_same_length(&lengths, args, term, Operator::ReAll)
            }
            _ => Err(term),
        };
        lengths.insert(term, length);
    }
    lengths[r].map_err(|t| CheckerError::LengthCannotBeEvaluated(t.clone()))
}

pub fn concat_eq(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= x y) = &conclusion[0])?;

    let term = get_premise_term(&premises[0])?;
    let rev = args[0].as_bool_err()?;
    let (s, t) = match_term_err!((= s t) = term)?;

    let (ss, ts) = strip_prefix_or_suffix(step, s.clone(), t.clone(), rev, polyeq_time)?;
    let ss_concat = concat(step, ss);
    let ts_concat = concat(step, ts);
    let expected = build_term!(
        step,
        (= {ss_concat.clone()} {ts_concat.clone()})
    );

    let expanded = step.expand_string_constants(&conclusion[0])?;

    assert_eq(&expected, &expanded)
}

pub fn concat_unify(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 2)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= x y) = &conclusion[0])?;

    let term = get_premise_term(&premises[0])?;
    let prefixes = get_premise_term(&premises[1])?;
    let rev = args[0].as_bool_err()?;
    let (s, t) = match_term_err!((= s t) = term)?;
    let (s_1, t_1) = match_term_err!((= (strlen s_1) (strlen t_1)) = prefixes)?;

    let s_1 = is_prefix_or_suffix(step, s.clone(), s_1.clone(), rev, polyeq_time)?;
    let t_1 = is_prefix_or_suffix(step, t.clone(), t_1.clone(), rev, polyeq_time)?;
    let s_concat = concat(step, s_1);
    let t_concat = concat(step, t_1);
    let expected = build_term!(
        step,
        (= {s_concat.clone()} {t_concat.clone()})
    );

    let expanded = step.expand_string_constants(&conclusion[0])?;

    assert_eq(&expected, &expanded)
}

pub fn concat_conflict(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let rev = args[0].as_bool_err()?;
    if conclusion[0].as_bool_err()? {
        return Err(CheckerError::ExpectedBoolConstant(
            false,
            conclusion[0].clone(),
        ));
    }

    let (s, t) = match_term_err!((= s t) = term)?;
    let (mut ss, mut ts) = strip_prefix_or_suffix(step, s.clone(), t.clone(), rev, polyeq_time)?;
    if rev {
        ss.reverse();
        ts.reverse();
    }

    if let Some(ss_head) = ss.first() {
        string_check_length_one(ss_head.clone())?;
        if let Some(ts_head) = ts.first() {
            string_check_length_one(ts_head.clone())?;
        }
    } else if let Some(ts_head) = ts.first() {
        string_check_length_one(ts_head.clone())?;
    } else {
        return Err(CheckerError::ExpectedDifferentConstantPrefixes(
            s.clone(),
            t.clone(),
        ));
    }

    Ok(())
}

pub fn concat_csplit_prefix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_1 x) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let t_1 = match_term_err!((not (= (strlen t_1) 0)) = length)?;

    let s_flat = step.string_concat_flatten(s)?;
    if step.string_concat_flatten(t)?.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_prefix(step, t.clone(), t_1.clone(), polyeq_time)?;
    let mut right_eq: Vec<Rc<Term>> = vec![];
    if let Some(c) = s_flat.first() {
        string_check_length_one(c.clone())?;
        right_eq.push(c.clone());
        let n = step.add(Term::new_int(1));
        right_eq.push(build_skolem_suffix_rem(step, t_1.clone(), n).clone());
    }

    let t_1 = step.expand_string_constants(t_1)?;
    let right_eq_concat = concat(step, right_eq);
    let expected = build_term!(
        step,
        (= {t_1.clone()} {right_eq_concat.clone()})
    );

    let expanded = step.expand_string_constants(&conclusion[0])?;

    assert_eq(&expected, &expanded)
}

pub fn concat_csplit_suffix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_2 x) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let t_2 = match_term_err!((not (= (strlen t_2) 0)) = length)?;

    let s_flat = step.string_concat_flatten(s)?;
    if step.string_concat_flatten(t)?.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_suffix(step, t.clone(), t_2.clone(), polyeq_time)?;
    let mut right_eq: Vec<Rc<Term>> = vec![];
    if let Some(c) = s_flat.last() {
        string_check_length_one(c.clone())?;
        let n = build_term!(step, (- (strlen {t_2.clone()}) 1));
        right_eq.push(build_skolem_prefix(step, t_2.clone(), n).clone());
        right_eq.push(c.clone());
    }

    let t_2 = step.expand_string_constants(t_2)?;
    let right_eq_concat = concat(step, right_eq);
    let expected = build_term!(
        step,
        (= {t_2.clone()} {right_eq_concat.clone()})
    );

    let expanded = step.expand_string_constants(&conclusion[0])?;

    assert_eq(&expected, &expanded)
}

pub fn concat_split_prefix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (and
            (or (= t_1 x) (= s_1 y))
            (not (= r ""))
            (> (strlen r) 0)
        ) = &conclusion[0]
    )?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_1, s_1) = match_term_err!((not (= (strlen t_1) (strlen s_1))) = length)?;

    if step.string_concat_flatten(t)?.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if step.string_concat_flatten(s)?.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_prefix(step, t.clone(), t_1.clone(), polyeq_time)?;
    is_prefix(step, s.clone(), s_1.clone(), polyeq_time)?;
    let t_1 = step.expand_string_constants(t_1)?;
    let s_1 = step.expand_string_constants(s_1)?;
    let r = build_skolem_unify_split_prefix(step, t_1.clone(), s_1.clone());

    let or = build_term!(
        step,
        (or
            (=
                {t_1.clone()}
                (strconcat {s_1.clone()} {r.clone()})
            )
            (=
                {s_1.clone()}
                (strconcat {t_1.clone()} {r.clone()})
            )
        )
    );

    let empty = step.add(Term::new_string(""));
    let expanded = build_term!(
        step,
        (and
            {or.clone()}
            (not (= {r.clone()} {empty.clone()}))
            (> (strlen {r.clone()}) 0)
        )
    );

    let expanded = step.expand_string_constants(&expanded)?;
    let expected = step.expand_string_constants(&conclusion[0])?;

    assert_eq(&expected, &expanded)
}

pub fn concat_split_suffix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (and
            (or (= t_2 x) (= s_2 y))
            (not (= r ""))
            (> (strlen r) 0)
        ) = &conclusion[0]
    )?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_2, s_2) = match_term_err!((not (= (strlen t_2) (strlen s_2))) = length)?;

    if step.string_concat_flatten(t)?.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if step.string_concat_flatten(s)?.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_suffix(step, t.clone(), t_2.clone(), polyeq_time)?;
    is_suffix(step, s.clone(), s_2.clone(), polyeq_time)?;
    let t_2 = step.expand_string_constants(t_2)?;
    let s_2 = step.expand_string_constants(s_2)?;
    let r = build_skolem_unify_split_suffix(step, t_2.clone(), s_2.clone());

    let or = build_term!(
        step,
        (or
            (=
                {t_2.clone()}
                (strconcat {r.clone()} {s_2.clone()})
            )
            (=
                {s_2.clone()}
                (strconcat {r.clone()} {t_2.clone()})
            )
        )
    );

    let empty = step.add(Term::new_string(""));
    let expanded = build_term!(
        step,
        (and
            {or.clone()}
            (not (= {r.clone()} {empty.clone()}))
            (> (strlen {r.clone()}) 0)
        )
    );

    let expanded = step.expand_string_constants(&expanded)?;
    let expected = step.expand_string_constants(&conclusion[0])?;

    assert_eq(&expected, &expanded)
}

pub fn concat_lprop_prefix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (and
            (= t_1 x)
            (not (= r ""))
            (> (strlen r) 0)
        ) = &conclusion[0]
    )?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_1, s_1) = match_term_err!((> (strlen t_1) (strlen s_1)) = length)?;

    if step.string_concat_flatten(t)?.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if step.string_concat_flatten(s)?.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_prefix(step, t.clone(), t_1.clone(), polyeq_time)?;
    is_prefix(step, s.clone(), s_1.clone(), polyeq_time)?;
    let t_1 = step.expand_string_constants(t_1)?;
    let s_1 = step.expand_string_constants(s_1)?;
    let r = build_skolem_unify_split_prefix(step, t_1.clone(), s_1.clone());

    let eq = build_term!(step, (strconcat {s_1.clone()} {r.clone()}));
    let empty = step.add(Term::new_string(""));
    let expanded = build_term!(
        step,
        (and
            (= {t_1.clone()} {eq.clone()})
            (not (= {r.clone()} {empty.clone()}))
            (> (strlen {r.clone()}) 0)
        )
    );

    let expanded = step.expand_string_constants(&expanded)?;
    let expected = step.expand_string_constants(&conclusion[0])?;

    assert_eq(&expected, &expanded)
}

pub fn concat_lprop_suffix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (and
            (= t_2 x)
            (not (= r ""))
            (> (strlen r) 0)
        ) = &conclusion[0]
    )?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_2, s_2) = match_term_err!((> (strlen t_2) (strlen s_2)) = length)?;

    if step.string_concat_flatten(t)?.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if step.string_concat_flatten(s)?.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_suffix(step, t.clone(), t_2.clone(), polyeq_time)?;
    is_suffix(step, s.clone(), s_2.clone(), polyeq_time)?;
    let t_2 = step.expand_string_constants(t_2)?;
    let s_2 = step.expand_string_constants(s_2)?;
    let r = build_skolem_unify_split_suffix(step, t_2.clone(), s_2.clone());

    let eq = build_term!(step, (strconcat {r.clone()} {s_2.clone()}));
    let empty = step.add(Term::new_string(""));
    let expanded = build_term!(
        step,
        (and
            (= {t_2.clone()} {eq.clone()})
            (not (= {r.clone()} {empty.clone()}))
            (> (strlen {r.clone()}) 0)
        )
    );

    let expanded = step.expand_string_constants(&expanded)?;
    let expected = step.expand_string_constants(&conclusion[0])?;

    assert_eq(&expected, &expanded)
}

pub fn concat_cprop_prefix(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_1 (strconcat t_3 r)) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let t_1 = match_term_err!((not (= (strlen t_1) 0)) = length)?;

    let args_t = extract_arguments(t)?;

    assert_eq(&args_t[0], t_1)?;

    let empty = step.add(Term::new_string(""));
    let ss = match s.as_ref() {
        Term::Const(Constant::String(text)) => {
            if text.is_empty() {
                return Err(CheckerError::ExpectedToNotBeEmpty(s.clone()));
            }
            vec![s.clone(), empty.clone()]
        }
        Term::Op(Operator::StrConcat, args) => args.clone(),
        _ => return Err(CheckerError::TermOfWrongForm("(str.++ s1 s2)", s.clone())),
    };

    let sc = step.string_concat_flatten(&ss[0])?;
    let t_2_flat = step.string_concat_flatten(&args_t[1])?;
    // Modified in Clean: the overlap argument is only valid when both the head of the right-hand
    // side and the middle component of the left-hand side are string constants; comparing
    // arbitrary terms syntactically says nothing about where the middle component can start (see
    // third-party/carcara/DOWNSTREAM.md).
    require_constant_word(&ss[0], &sc, false)?;
    require_constant_word(&args_t[1], &t_2_flat, true)?;
    let v = 1 + overlap(&sc[1..], &t_2_flat);
    let v = step.add(Term::new_int(v));
    let oc = build_skolem_prefix(step, ss[0].clone(), v);
    let oc_len = build_term!(step, (strlen {oc.clone()}));

    let r = build_skolem_suffix_rem(step, t_1.clone(), oc_len);
    let expanded = build_term!(step, (= {t_1.clone()} (strconcat {oc.clone()} {r.clone()})));

    let expanded = step.expand_string_constants(&expanded)?;
    let expected = step.expand_string_constants(&conclusion[0])?;

    assert_eq(&expected, &expanded)
}

pub fn concat_cprop_suffix(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_2 (strconcat r t_3)) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let t_2 = match_term_err!((not (= (strlen t_2) 0)) = length)?;

    let args_t = extract_arguments(t)?;

    assert_eq(&args_t[2], t_2)?;

    let empty = step.add(Term::new_string(""));
    let ss = match s.as_ref() {
        Term::Const(Constant::String(text)) => {
            if text.is_empty() {
                return Err(CheckerError::ExpectedToNotBeEmpty(s.clone()));
            }
            vec![empty.clone(), s.clone()]
        }
        Term::Op(Operator::StrConcat, args) => args.clone(),
        _ => return Err(CheckerError::TermOfWrongForm("(str.++ s1 s2)", s.clone())),
    };

    let mut sc = step.string_concat_flatten(&ss[1])?;
    let mut t_2_flat = step.string_concat_flatten(&args_t[1])?;
    // Modified in Clean: as in `concat_cprop_prefix`, both words must be string constants.
    require_constant_word(&ss[1], &sc, false)?;
    require_constant_word(&args_t[1], &t_2_flat, true)?;
    sc.reverse();
    t_2_flat.reverse();

    let v = 1 + overlap(&sc[1..], &t_2_flat);
    let v = step.add(Term::new_int(v));
    let oc = build_str_suffix_len(step, ss[1].clone(), v);

    let rhs = build_term!(step, (- (strlen {t_2.clone()}) (strlen {oc.clone()})));
    let r = build_skolem_prefix(step, t_2.clone(), rhs.clone());
    let expanded = build_term!(step, (= {t_2.clone()} (strconcat {r.clone()} {oc.clone()})));

    let expanded = step.expand_string_constants(&expanded)?;
    let expected = step.expand_string_constants(&conclusion[0])?;

    assert_eq(&expected, &expanded)
}

/// Modified in Clean: decides, syntactically and conservatively, whether an integer term is
/// guaranteed to be non-negative. `string_decompose` splits a word at `n`, and `str.substr` yields
/// the empty word for a negative index, so a negative `n` makes its conclusion
/// `(= (str.len w) n)` false while its premise `(>= (str.len t) n)` stays trivially true (see
/// third-party/carcara/DOWNSTREAM.md). Returning `false` only costs completeness.
fn is_syntactically_nonnegative(term: &Rc<Term>) -> bool {
    // Modified in Clean: each subterm is looked at once, by a loop. Recursing once per path to a
    // shared (`:named`) summand, a sum of two copies of a sum of two copies ..., 30 deep, took
    // 4.5 s and each level doubled it. The answer is the same: every term reached through sums and
    // products is a non-negative numeral or a `str.len`, and no sum or product is empty.
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![term];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match term.as_ref() {
            Term::Const(Constant::Integer(i)) if !i.is_negative() => {}
            Term::Const(Constant::Real(r)) if !r.is_negative() => {}
            // `str.len` is non-negative in every SMT-LIB model.
            Term::Op(Operator::StrLen, _) => {}
            // A sum or a product of non-negative integers is non-negative.
            Term::Op(Operator::Add | Operator::Mult, args) if !args.is_empty() => {
                stack.extend(args);
            }
            _ => return false,
        }
    }
    true
}

pub fn string_decompose(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let rev = args[0].as_bool_err()?;
    let (t, n) = match_term_err!((>= (strlen t) n) = term)?;

    // Modified in Clean: the premise `(>= (str.len t) n)` bounds `n` from above only. With `n`
    // negative it holds vacuously while the conclusion's `(= (str.len w) n)` is false, since a
    // string length is never negative — `(>= (str.len s) (- 1))` used to prove
    // `(= (str.len (str.substr s 0 (- 1))) (- 1))` (see third-party/carcara/DOWNSTREAM.md).
    if !is_syntactically_nonnegative(n) {
        return Err(CheckerError::Explanation(format!(
            "the split point '{}' is not syntactically non-negative, so the premise does not \
             bound it from below",
            n
        )));
    }

    match_term_err!(
        (and
            (= t x)
            (= (strlen y) n)
        ) = &conclusion[0]
    )?;

    // Modified in Clean: in the reverse direction the split point is `(str.len t) - n`, so that the
    // *suffix* has length `n`. Splitting at `n` in both directions concluded
    // `(= (str.len w_2) n)` for a suffix of length `(str.len t) - n` (see
    // third-party/carcara/DOWNSTREAM.md).
    let split = if rev {
        build_term!(step, (- (strlen {t.clone()}) {n.clone()}))
    } else {
        n.clone()
    };
    let w_1 = build_skolem_prefix(step, t.clone(), split.clone());
    let w_2 = build_skolem_suffix_rem(step, t.clone(), split);
    let len_term = if rev { w_2.clone() } else { w_1.clone() };

    let expanded = build_term!(
            step,
            (and
                (= {t.clone()} (strconcat {w_1.clone()} {w_2.clone()}))
                (= (strlen {len_term.clone()}) {n.clone()})
            )
    );

    assert_polyeq(&conclusion[0], &expanded, polyeq_time)
}

pub fn string_length_pos(RuleArgs { args, conclusion, polyeq_time, .. }: RuleArgs) -> RuleResult {
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    let t = &args[0];
    // Note that the three occurrences of 't' are matched independently, since they
    // don't have to be identical to each other.
    let (t_1, t_2, t_3) = match_term_err!(
        (or
            (and
                (= (strlen t_1) 0)
                (= t_2 "")
            )
            (> (strlen t_3) 0)
        ) = &conclusion[0]
    )?;

    assert_polyeq(t_1, t, polyeq_time)?;
    assert_polyeq(t_2, t, polyeq_time)?;
    assert_polyeq(t_3, t, polyeq_time)?;

    Ok(())
}

pub fn string_length_non_empty(
    RuleArgs {
        premises, conclusion, polyeq_time, ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let t = match_term_err!((not (= t "")) = term)?;

    let t_conc = match_term_err!(
        (not
            (= (strlen t) 0)
        ) = &conclusion[0]
    )?;

    assert_polyeq(t_conc, t, polyeq_time)?;

    Ok(())
}

pub fn re_inter(
    RuleArgs {
        premises, conclusion, polyeq_time, ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    let (x_conc, s_conc, t_conc) = match_term_err!((strinre x (reinter s t)) = &conclusion[0])?;

    let t_1 = get_premise_term(&premises[0])?;
    let t_2 = get_premise_term(&premises[1])?;
    let (x_1, s) = match_term_err!((strinre x s) = t_1)?;
    let (x_2, t) = match_term_err!((strinre x t) = t_2)?;

    assert_polyeq(x_conc, x_1, polyeq_time)?;
    assert_polyeq(x_conc, x_2, polyeq_time)?;

    assert_eq(s_conc, s)?;
    assert_eq(t_conc, t)?;

    Ok(())
}

/// Modified in Clean: `re_concat_unfold_pos` and `re_kleene_star_unfold_pos` name the components of
/// the decomposition with Hilbert-choice Skolem terms whose defining formula existentially
/// quantifies the regular languages (`(choice ((x String)) (exists ((k_0 String) (R_0 RegLan)
/// (R_1 RegLan)) (and (= t (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1))))`). Both
/// `str.in_re` conjuncts are then vacuous — every string is in *some* regular language — so the
/// witness is only constrained to be a factor of `t`, and the conclusion, which uses it as a
/// specific component of a specific split, does not follow from the premise. A refutation of a
/// satisfiable problem built this way verified end to end (see third-party/carcara/DOWNSTREAM.md and
/// reports/2026-09-17-carcara-soundness-upstream-report.md, which states the redesign the rule
/// needs).
///
/// Until the rule is respecified upstream, the checker refuses every application that would build
/// such a witness. `re_unfold_pos_concat` refuses it at the one place a component would be
/// generated, an argument of the `re.++` that is not a `str.to_re`, before building it, so this is
/// a property of *this* application and not an inference from the shape of the terms. What
/// survives is the case where the premise determines the decomposition outright: every argument of
/// the `re.++` is a `(str.to_re s_i)`, the language is the singleton `{s_1 ++ .. ++ s_n}`, and the
/// conclusion is the plain equality `(= t (str.++ s_1 .. s_n))` with no witness and no `str.in_re`
/// conjunct. `re_kleene_star_unfold_pos` unfolds `(re.* r)` into `(re.++ r (re.* r) r)`, whose
/// middle argument is never a `str.to_re`, so it is left with no instances.
fn skolem_witness_refused(rule: &str) -> CheckerError {
    CheckerError::Explanation(format!(
        "{} builds a Skolem witness for a component the premise does not determine: the \
         witness' defining formula quantifies the regular languages away, so it only says the \
         witness is a factor of the word",
        rule
    ))
}

pub fn re_kleene_star_unfold_pos(
    RuleArgs { premises, conclusion, pool, .. }: RuleArgs,
) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let (t, r) = match_term_err!((strinre t r) = term)?;

    match_term_err!((or (= t_1 "") (strinre t_2 t_3) (and t_4 (not (= t_5 "")) (not (= t_6 "")))) = &conclusion[0])?;

    // Modified in Clean: `re_unfold_pos_concat` refuses the unfolding at its middle argument, which
    // is never a `str.to_re` (see `skolem_witness_refused`); what follows is what the rule builds
    // from three components the premise determines.
    let expanded = match r.as_ref() {
        Term::Op(Operator::ReKleeneClosure, args) => {
            if let Some(r_1) = args.first() {
                let new_t = step.add(Term::Op(
                    Operator::ReConcat,
                    vec![r_1.clone(), r.clone(), r_1.clone()],
                ));
                let k = re_unfold_pos_concat(step, "re_kleene_star_unfold_pos", &new_t)?;
                let concat_args = step.concat_extract(&k)?;
                match &concat_args[..] {
                    [k_0, k_1, k_2] => {
                        let eq = build_term!(step, (= {t.clone()} (strconcat {k_0.clone()} {k_1.clone()} {k_2.clone()})));
                        let empty = step.add(Term::new_string(""));
                        let simplified = step.add(Term::Op(Operator::And, vec![eq.clone()]));
                        Ok(build_term!(
                            step,
                            (or
                                (= {t.clone()} {empty.clone()})
                                (strinre {t.clone()} {r_1.clone()})
                                (and
                                    {simplified}
                                    (not (= {k_0.clone()} {empty.clone()}))
                                    (not (= {k_2.clone()} {empty}))
                                )
                            )
                        ))
                    }
                    _ => Err(CheckerError::TermOfWrongForm(
                        "(str.++ k1 k2 k3)",
                        k.clone(),
                    )),
                }
            } else {
                unreachable!()
            }
        }
        _ => Err(CheckerError::TermOfWrongForm("(re.* ...)", r.clone())),
    }?;

    assert_eq(&conclusion[0], &expanded)
}

pub fn re_concat_unfold_pos(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let (t, r) = match_term_err!((strinre t r) = term)?;

    // Check conclusion possible formats
    let first_format = match_term_err!((= t_1 (strconcat ...)) = &conclusion[0]);
    let second_format = match_term_err!((and (= t_1 (strconcat ...)) (and ...)) = &conclusion[0]);
    if first_format.is_err() && second_format.is_err() {
        return Err(CheckerError::TermOfWrongForm(
            "(= t_1 (str.++ ...)) or (and (= t_1 (str.++ ...)) (and ...))",
            conclusion[0].clone(),
        ));
    }

    // Modified in Clean: `re_unfold_pos_concat` refuses an argument that is not a `str.to_re` (see
    // `skolem_witness_refused`), so the unfolding has no witness and no `str.in_re` conjunct.
    let expanded = match r.as_ref() {
        Term::Op(Operator::ReConcat, _) => {
            let tk = re_unfold_pos_concat(step, "re_concat_unfold_pos", r)?;
            let concat_args = step.concat_extract(&tk)?;
            let new_concat = step.add(Term::Op(Operator::StrConcat, concat_args));
            Ok(build_term!(step, (= {t.clone()} {new_concat.clone()})))
        }
        _ => Err(CheckerError::TermOfWrongForm("(re.++ ...)", r.clone())),
    }?;

    assert_eq(&conclusion[0], &expanded)
}

/// Modified in Clean: `re_unfold_neg` builds a `forall` over a fresh length variable. The name was
/// hard-coded to `L`, so a premise whose term mentions a free `L` had it captured by the generated
/// quantifier: `(not (str.in_re (str.substr y 0 L) (re.++ (str.to_re "a") (str.to_re ""))))` proved
/// a `(forall ((L Int)) ...)` in which the two `L`s are the same variable (see
/// third-party/carcara/DOWNSTREAM.md). The name is now taken from the conclusion and checked not to
/// occur free in either the word or the regular expression.
fn re_unfold_neg_length_var(
    pool: &mut dyn TermPool,
    quantifier: &Rc<Term>,
    t: &Rc<Term>,
    r: &Rc<Term>,
) -> Result<Rc<Term>, CheckerError> {
    let Term::Binder(Binder::Forall, bindings, _) = quantifier.as_ref() else {
        return Err(CheckerError::TermOfWrongForm(
            "(forall ...)",
            quantifier.clone(),
        ));
    };
    let [(name, sort)] = &bindings.as_ref()[..] else {
        return Err(CheckerError::TermOfWrongForm(
            "(forall ((L Int)) ...)",
            quantifier.clone(),
        ));
    };
    if sort.as_ref() != &Sort::Int {
        return Err(CheckerError::TermOfWrongForm(
            "(forall ((L Int)) ...)",
            quantifier.clone(),
        ));
    }
    for term in [t, r] {
        if pool.free_vars(term).contains_name(name) {
            return Err(CheckerError::Explanation(format!(
                "the quantified length variable '{}' occurs free in '{}', so the conclusion \
                 captures it",
                name, term
            )));
        }
    }
    Ok(pool.add(Term::new_var(name.clone(), sort.clone())))
}

pub fn re_unfold_neg(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let (t, r) = match_term_err!((not (strinre t r)) = term)?;

    let int_sort = pool.add_sort(Sort::Int);
    // Modified in Clean: the quantified length variable comes from the conclusion and may not
    // capture a free variable of the premise (see `re_unfold_neg_length_var`).
    let quantifier_term = match r.as_ref() {
        Term::Op(Operator::ReKleeneClosure, _) => {
            match_term_err!((and (not (= t "")) q) = &conclusion[0])?
                .1
                .clone()
        }
        _ => conclusion[0].clone(),
    };
    let l = re_unfold_neg_length_var(pool, &quantifier_term, t, r)?;
    let step = &mut StringStep::new(pool);
    let pref = build_skolem_prefix(step, t.clone(), l.clone());
    let suff = build_skolem_suffix_rem(step, t.clone(), l.clone());

    let expanded = match r.as_ref() {
        Term::Op(Operator::ReKleeneClosure, args) => {
            match_term_err!(
                (and
                    (not (= t ""))
                    (forall ...
                        (or
                            (<= l 0)
                            (< (strlen t) l)
                            (not (strinre pref r_1))
                            (not (strinre suff r))
                        )
                    )
                ) = &conclusion[0]
            )?;

            if let Some(r_1) = args.first() {
                let inner = build_term!(step,
                    (or
                        (<= {l.clone()} 0)
                        (< (strlen {t.clone()}) {l.clone()})
                        (not (strinre {pref.clone()} {r_1.clone()}))
                        (not (strinre {suff.clone()} {r.clone()}))
                    )
                );
                let quantifier = step.add(Term::Binder(
                    Binder::Forall,
                    BindingList(vec![(l.as_var().unwrap().to_owned(), int_sort.clone())]),
                    inner,
                ));
                let empty = step.add(Term::new_string(""));
                Ok(build_term!(step,
                    (and
                        (not (= {t.clone()} {empty.clone()}))
                        {quantifier.clone()}
                    )
                ))
            } else {
                unreachable!()
            }
        }
        Term::Op(Operator::ReConcat, args) => {
            match_term_err!(
                 (forall ...
                     (or
                         (< l 0)
                         (< (strlen t) l)
                         (not (strinre pref r_1))
                         (not (strinre suff r))
                     )
                 ) = &conclusion[0]
            )?;

            if let [r_1, r_2 @ ..] = &args[..] {
                let inner = build_term!(step,
                    (or
                        (< {l.clone()} 0)
                        (< (strlen {t.clone()}) {l.clone()})
                        (not (strinre {pref.clone()} {r_1.clone()}))
                        (not (strinre {suff.clone()} {singleton_elim(step, r_2.to_vec())}))
                    )
                );
                let quantifier = step.add(Term::Binder(
                    Binder::Forall,
                    BindingList(vec![(l.as_var().unwrap().to_owned(), int_sort.clone())]),
                    inner,
                ));
                Ok(quantifier)
            } else {
                unreachable!()
            }
        }
        _ => Err(CheckerError::TermOfWrongForm(
            "(re.* ...) or (re.++ ...)",
            r.clone(),
        )),
    }?;

    assert_eq(&conclusion[0], &expanded)
}

pub fn re_unfold_neg_concat_fixed_prefix(
    RuleArgs { premises, conclusion, pool, .. }: RuleArgs,
) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (or
            (not (strinre pref r_1))
            (not (strinre suff r_2))
        ) = &conclusion[0]
    )?;

    let term = get_premise_term(&premises[0])?;
    let (s, r) = match_term_err!((not (strinre s r)) = term)?;

    let expanded = if let Term::Op(Operator::ReConcat, args) = r.as_ref() {
        if let [r_1, r_2 @ ..] = &args[..] {
            let n = Term::new_int(str_fixed_len_re(r_1)?);
            let n = step.add(n);
            let pref = build_skolem_prefix(step, s.clone(), n.clone());
            let suff = build_skolem_suffix_rem(step, s.clone(), n.clone());
            Ok(build_term!(step,
                (or
                    (not (strinre {pref.clone()} {r_1.clone()}))
                    (not (strinre {suff.clone()} {singleton_elim(step, r_2.to_vec())}))
                )
            ))
        } else {
            unreachable!()
        }
    } else {
        Err(CheckerError::TermOfWrongForm("(re.++ ...)", r.clone()))
    }?;

    assert_eq(&conclusion[0], &expanded)
}

pub fn re_unfold_neg_concat_fixed_suffix(
    RuleArgs { premises, conclusion, pool, .. }: RuleArgs,
) -> RuleResult {
    let step = &mut StringStep::new(pool);
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (or
            (not (strinre suff r_1))
            (not (strinre pref r_2))
        ) = &conclusion[0]
    )?;

    let term = get_premise_term(&premises[0])?;
    let (s, r) = match_term_err!((not (strinre s r)) = term)?;

    let expanded = if let Term::Op(Operator::ReConcat, args) = r.as_ref() {
        let mut args_rev = args.clone();
        args_rev.reverse();

        if let [r_1, r_2 @ ..] = &args_rev[..] {
            let n = Term::new_int(str_fixed_len_re(r_1)?);
            let n = step.add(n);
            let suff = build_skolem_suffix(step, s.clone(), n.clone());
            let size = build_term!(step, (- (strlen {s.clone()}) {n.clone()}));
            let pref = build_skolem_prefix(step, s.clone(), size.clone());
            let mut r_2_rev = r_2.to_vec();
            r_2_rev.reverse();
            Ok(build_term!(step,
                (or
                    (not (strinre {suff.clone()} {r_1.clone()}))
                    (not (strinre {pref.clone()} {singleton_elim(step, r_2_rev.clone())}))
                )
            ))
        } else {
            unreachable!()
        }
    } else {
        Err(CheckerError::TermOfWrongForm("(re.++ ...)", r.clone()))
    }?;

    assert_eq(&conclusion[0], &expanded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::pool::PrimitivePool,
        checker::{self, budget::MAX_EXPANDED_BITS},
        parser,
    };

    /// Upstream's `string_concat_flatten`, kept verbatim to hold the loop to it.
    fn upstream_flatten(pool: &mut dyn TermPool, term: Rc<Term>) -> Vec<Rc<Term>> {
        let mut flattened = Vec::new();
        if let Term::Const(Constant::String(s)) = term.as_ref() {
            flattened.extend(
                s.chars()
                    .map(|c| pool.add(Term::Const(Constant::String(c.to_string())))),
            );
        } else if let Some(args) = crate::ast::match_term!((strconcat ...) = term) {
            for arg in args {
                flattened.extend(upstream_flatten(pool, arg.clone()));
            }
        } else {
            flattened.push(term.clone());
        }
        flattened
    }

    /// Upstream's `concat_extract`, kept verbatim.
    fn upstream_extract(term: Rc<Term>) -> Vec<Rc<Term>> {
        let mut flattened = Vec::new();
        if let Term::Const(Constant::String(s)) = term.as_ref() {
            if !s.is_empty() {
                flattened.push(term.clone());
            }
        } else if let Some(args) = crate::ast::match_term!((strconcat ...) = term) {
            for arg in args {
                flattened.extend(upstream_extract(arg.clone()));
            }
        } else {
            flattened.push(term.clone());
        }
        flattened
    }

    /// Upstream's `expand_string_constants`, kept verbatim.
    fn upstream_expand(pool: &mut dyn TermPool, term: &Rc<Term>) -> Rc<Term> {
        match term.as_ref() {
            Term::Const(Constant::String(s)) => {
                let args: Vec<Rc<Term>> = s
                    .chars()
                    .map(|c| pool.add(Term::Const(Constant::String(c.to_string()))))
                    .collect();
                match args.len() {
                    0 => pool.add(Term::new_string("")),
                    1 => args[0].clone(),
                    _ => pool.add(Term::Op(Operator::StrConcat, args)),
                }
            }
            Term::Op(op, args) => match op {
                Operator::StrConcat => {
                    let mut new_args = Vec::new();
                    for arg in args {
                        new_args.extend(upstream_flatten(pool, arg.clone()));
                    }
                    pool.add(Term::Op(*op, new_args))
                }
                _ => {
                    let new_args = args.iter().map(|a| upstream_expand(pool, a)).collect();
                    pool.add(Term::Op(*op, new_args))
                }
            },
            Term::App(func, args) => {
                let new_args = args.iter().map(|t| upstream_expand(pool, t)).collect();
                pool.add(Term::App(func.clone(), new_args))
            }
            Term::Let(binding, inner) => {
                let new_inner = upstream_expand(pool, inner);
                pool.add(Term::Let(binding.clone(), new_inner))
            }
            Term::Binder(q, bindings, inner) => {
                let new_inner = upstream_expand(pool, inner);
                pool.add(Term::Binder(*q, bindings.clone(), new_inner))
            }
            Term::ParamOp { op, op_args, args } => {
                let new_args = args.iter().map(|t| upstream_expand(pool, t)).collect();
                pool.add(Term::ParamOp {
                    op: *op,
                    op_args: op_args.clone(),
                    args: new_args,
                })
            }
            Term::AsOp(op, sort, args) => {
                let new_args = args.iter().map(|t| upstream_expand(pool, t)).collect();
                pool.add(Term::AsOp(*op, sort.clone(), new_args))
            }
            Term::Match(t, cases) => {
                let new_t = upstream_expand(pool, t);
                let new_cases = cases
                    .iter()
                    .map(|case| MatchCase {
                        pattern: case.pattern.clone(),
                        body: upstream_expand(pool, &case.body),
                    })
                    .collect();
                pool.add(Term::Match(new_t, new_cases))
            }
            Term::Var(..) | Term::Const(_) => term.clone(),
        }
    }

    /// Upstream's `is_compatible` and `overlap`, kept verbatim to hold the Z-array to them.
    fn upstream_is_compatible(s: Vec<Rc<Term>>, t: Vec<Rc<Term>>) -> bool {
        match (&s[..], &t[..]) {
            (_, []) => true,
            ([], _) => true,
            ([h1, t1 @ ..], [h2, t2 @ ..]) => {
                if h1 == h2 {
                    upstream_is_compatible(t1.to_vec(), t2.to_vec())
                } else {
                    false
                }
            }
        }
    }

    fn upstream_overlap(s: Vec<Rc<Term>>, t: Vec<Rc<Term>>) -> usize {
        match &s[..] {
            [] | [_] => 0,
            [_, tail @ ..] => {
                if upstream_is_compatible(s.clone(), t.clone()) {
                    0
                } else {
                    1 + upstream_overlap(tail.to_vec(), t.clone())
                }
            }
        }
    }

    /// Every word of up to `max_len` characters over `alphabet`.
    fn words(alphabet: &[Rc<Term>], max_len: usize) -> Vec<Vec<Rc<Term>>> {
        let mut all = vec![Vec::new()];
        let mut last = vec![Vec::new()];
        for _ in 0..max_len {
            last = last
                .iter()
                .flat_map(|w: &Vec<Rc<Term>>| {
                    alphabet.iter().map(move |c| {
                        let mut w = w.clone();
                        w.push(c.clone());
                        w
                    })
                })
                .collect();
            all.extend(last.iter().cloned());
        }
        all
    }

    /// Added in Clean: the Z-array finds the position upstream's recursion found, for every pair of
    /// words of up to 7 characters over two letters and of up to 4 over three.
    #[test]
    fn overlap_is_upstreams() {
        let mut pool = PrimitivePool::new();
        let letters: Vec<_> = ["a", "b", "c"]
            .iter()
            .map(|c| pool.add(Term::new_string(*c)))
            .collect();
        for (alphabet, max_len) in [(&letters[..2], 7), (&letters[..], 4)] {
            let words = words(alphabet, max_len);
            for s in &words {
                for t in &words {
                    assert_eq!(
                        overlap(s, t),
                        upstream_overlap(s.clone(), t.clone()),
                        "{s:?} {t:?}"
                    );
                }
            }
        }
        // The shape that took upstream cubic time: `a^m b` against `a^(m + 1)` is compatible
        // nowhere, so the overlap is the last position; `a^m` against it, everywhere.
        let (a, b) = (&letters[0], &letters[1]);
        let m = 100_000;
        let mut s = vec![a.clone(); m];
        s.push(b.clone());
        let t = vec![a.clone(); m + 1];
        assert_eq!(overlap(&s, &t), m);
        assert_eq!(overlap(&s[..m], &t), 0);
    }

    #[test]
    fn z_array_counts_prefix_matches() {
        assert_eq!(z_array::<u8>(&[]), Vec::<usize>::new());
        assert_eq!(z_array(b"aabxaab"), [7, 1, 0, 0, 3, 1, 0]);
        assert_eq!(z_array(b"aaaaa"), [5, 4, 3, 2, 1]);
        assert_eq!(z_array(b"abababab"), [8, 0, 6, 0, 4, 0, 2, 0]);
    }

    /// Upstream's `re_unfold_pos_concat` as of Clean's fix 32 (the flag), kept verbatim with its
    /// witness builder, to hold the one pass to it.
    fn upstream_re_unfold_pos_concat(
        pool: &mut dyn TermPool,
        t: Rc<Term>,
        r: Rc<Term>,
        built: &mut bool,
    ) -> Result<(Rc<Term>, Rc<Term>), CheckerError> {
        /// Generates a Skolem term used for the positive unfolding in the general case.
        ///
        /// The generated Skolem has the following structure:
        /// ```text
        /// ε x. ∃ k_0, ..., k_n, R_0, ..., R_n.
        ///   (and (= t (str.++ k_0 k_1 ... k_i-1 x k_i+1 ... k_n))
        ///        (str.in_re k_0 R_0)
        ///        (str.in_re k_1 R_1)
        ///        ...
        ///        (str.in_re x R_i)
        ///        ...
        ///        (str.in_re k_n R_n))
        /// ```
        ///
        /// where `t` is the target string reconstructed by concatenating all `k_i`, and `i` is the
        /// index of the current string k being processed in the concatenation.
        fn re_unfold_pos_component(
            pool: &mut dyn TermPool,
            t: Rc<Term>,
            i: usize,
            previous_ks: &mut Vec<Rc<Term>>,
            previous_rs: &mut Vec<Rc<Term>>,
        ) -> Rc<Term> {
            let str_sort = pool.add_sort(Sort::String);
            let reglan_sort = pool.add_sort(Sort::RegLan);
            let x = pool.add(Term::new_var("x", str_sort.clone()));

            let mut and_args: Vec<Rc<Term>> = Vec::new();
            let mut concat_args: Vec<Rc<Term>> = Vec::new();
            let mut exists_binding_list: Vec<(String, Rc<Sort>)> = Vec::new();

            for j in 0..i {
                let k_j = pool.add(Term::new_var(format!("k_{j}"), str_sort.clone()));
                let r_j = pool.add(Term::new_var(format!("R_{j}"), reglan_sort.clone()));
                concat_args.push(k_j.clone());
                and_args.push(build_term!(pool, (strinre {k_j.clone()} {r_j.clone()})));
                exists_binding_list.push((format!("k_{j}"), str_sort.clone()));
                exists_binding_list.push((format!("R_{j}"), reglan_sort.clone()));
            }

            concat_args.push(x.clone());
            concat_args.extend(previous_ks.clone());
            let ks_concat = pool.add(Term::Op(Operator::StrConcat, concat_args));

            let r_i = pool.add(Term::new_var(format!("R_{i}"), reglan_sort.clone()));
            exists_binding_list.push((format!("R_{i}"), reglan_sort.clone()));
            and_args.push(build_term!(pool, (strinre {x.clone()} {r_i.clone()})));
            for (j, _) in previous_rs.iter().enumerate() {
                and_args.push(
                    build_term!(pool, (strinre {previous_ks[j].clone()} {previous_rs[j].clone()})),
                );
                let sum = i + j + 1;
                exists_binding_list.push((format!("R_{sum}"), reglan_sort.clone()));
            }

            let equality = build_term!(pool, (= {t.clone()} {ks_concat.clone()}));
            and_args.insert(0, equality);

            let conjunction = pool.add(Term::Op(Operator::And, and_args));
            let exists_binder = pool.add(Term::Binder(
                Binder::Exists,
                BindingList(exists_binding_list),
                conjunction,
            ));
            let choice_binder = pool.add(Term::Binder(
                Binder::Choice,
                BindingList(vec![("x".into(), str_sort.clone())]),
                exists_binder,
            ));

            previous_ks.insert(0, choice_binder.clone());
            previous_rs.insert(0, r_i.clone());

            choice_binder
        }

        fn re_unfold_pos_concat_recursive(
            pool: &mut dyn TermPool,
            t: Rc<Term>,
            r: Rc<Term>,
            previous_ks: &mut Vec<Rc<Term>>,
            previous_rs: &mut Vec<Rc<Term>>,
            n: usize,
            built: &mut bool,
        ) -> Result<(Rc<Term>, Rc<Term>), CheckerError> {
            match r.as_ref() {
                Term::Op(Operator::ReConcat, args) => {
                    if let [r_1, r_2 @ ..] = &args[..] {
                        let re_conc = pool.add(Term::Op(Operator::ReConcat, r_2.to_vec()));
                        let (c, m) = re_unfold_pos_concat_recursive(
                            pool,
                            t.clone(),
                            re_conc,
                            previous_ks,
                            previous_rs,
                            n + 1,
                            built,
                        )?;
                        match r_1.as_ref() {
                            Term::Op(Operator::StrToRe, str_to_re_args) => {
                                let s = str_to_re_args.first().unwrap();
                                Ok((build_term!(pool, (strconcat {s.clone()} {c.clone()})), m))
                            }
                            _ => {
                                // Modified in Clean: this is the one place a Skolem component is
                                // generated, so it is the one place the flag has to be set
                                *built = true;
                                let k =
                                    re_unfold_pos_component(pool, t, n, previous_ks, previous_rs);
                                if args.len() == 1 {
                                    Ok((
                                        build_term!(pool, (strconcat {k.clone()} {c.clone()})),
                                        build_term!(
                                            pool,
                                            (and (strinre {k.clone()} {r_1.clone()}) {m.clone()})
                                        ),
                                    ))
                                } else {
                                    Ok((
                                        build_term!(pool, (strconcat {k.clone()} {c.clone()})),
                                        build_term!(
                                            pool,
                                            (and (strinre {k.clone()} {r.clone()}) {m.clone()})
                                        ),
                                    ))
                                }
                            }
                        }
                    } else {
                        Ok((
                            pool.add(Term::new_string("")),
                            pool.add(Term::new_bool(true)),
                        ))
                    }
                }
                _ => Err(CheckerError::CannotApplyReUnfoldPos(r.clone())),
            }
        }

        re_unfold_pos_concat_recursive(
            pool,
            t.clone(),
            r.clone(),
            &mut Vec::new(),
            &mut Vec::new(),
            0,
            built,
        )
    }

    /// Added in Clean: where every argument of the `re.++` is a `str.to_re`, the one pass builds
    /// the term upstream's recursion built (and its `m` was `true`); where one is not, upstream
    /// built a witness and set the flag, and the one pass refuses. Over 2,000 random lists of two
    /// to six arguments.
    #[test]
    fn re_unfold_pos_concat_is_upstreams() {
        let mut pool = PrimitivePool::new();
        let string = pool.add_sort(Sort::String);
        let reglan = pool.add_sort(Sort::RegLan);
        let x = pool.add(Term::new_var("x", string.clone()));
        let words = [
            pool.add(Term::new_string("a")),
            pool.add(Term::new_string("")),
            pool.add(Term::new_string("ab")),
            x.clone(),
        ];
        let ab_x = pool.add(Term::Op(
            Operator::StrConcat,
            vec![words[2].clone(), x.clone()],
        ));
        let mut args: Vec<Rc<Term>> = words
            .iter()
            .chain([&ab_x])
            .map(|w| pool.add(Term::Op(Operator::StrToRe, vec![w.clone()])))
            .collect();
        let star = pool.add(Term::Op(Operator::ReKleeneClosure, vec![args[0].clone()]));
        args.push(star);
        args.push(pool.add(Term::new_var("R", reglan)));
        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        let (mut accepted, mut refused) = (0, 0);
        for _ in 0..2000 {
            let n = 2 + rng.below(5);
            let list = (0..n)
                .map(|_| args[rng.below(args.len())].clone())
                .collect();
            let r = pool.add(Term::Op(Operator::ReConcat, list));
            let mut built = false;
            let (tk, m) =
                upstream_re_unfold_pos_concat(&mut pool, x.clone(), r.clone(), &mut built).unwrap();
            let mut step = StringStep::new(&pool);
            match re_unfold_pos_concat(&mut step, "rule", &r) {
                Ok(chain) => {
                    assert!(!built && m.is_bool_true(), "{r}");
                    assert_eq!(chain, tk, "{r}");
                    accepted += 1;
                }
                Err(CheckerError::Explanation(e)) => {
                    assert!(built, "{r}");
                    assert!(e.starts_with("rule builds a Skolem witness"), "{e}");
                    refused += 1;
                }
                Err(e) => panic!("{r}: {e}"),
            }
        }
        assert!(accepted > 100 && refused > 100, "{accepted} {refused}");
    }

    /// Upstream's `str_fixed_len_re` and Clean's first `is_syntactically_nonnegative`, kept
    /// verbatim to hold the loops to them.
    fn upstream_str_fixed_len_re(
        pool: &mut dyn TermPool,
        r: Rc<Term>,
    ) -> Result<usize, CheckerError> {
        fn has_same_length(
            pool: &mut dyn TermPool,
            args: &[Rc<Term>],
            r: Rc<Term>,
            ignore: Operator,
        ) -> Result<usize, CheckerError> {
            let should_ignore = |term: &Term| term.as_op().is_some_and(|(op, _)| op == ignore);
            let mut iter = args
                .iter()
                .filter(|a| !should_ignore(a))
                .map(|a| upstream_str_fixed_len_re(pool, a.clone()));
            let Some(first) = iter.next() else {
                return Err(CheckerError::LengthCannotBeEvaluated(r.clone()));
            };
            let first = first?;
            for size in iter {
                let size = size?;
                if size != first {
                    return Err(CheckerError::LengthCannotBeEvaluated(r.clone()));
                }
            }
            Ok(first)
        }

        match r.as_ref() {
            Term::Op(Operator::ReConcat, args) => {
                let mut lengths = args
                    .iter()
                    .map(|a| upstream_str_fixed_len_re(pool, a.clone()));
                lengths.try_fold(0, |acc, x| Ok(acc + x?))
            }
            Term::Op(Operator::ReAllChar, _) => Ok(1),
            Term::Op(Operator::ReRange, _) => Ok(1),
            Term::Op(Operator::StrToRe, args) => {
                let s_1 = args.first().unwrap();
                match s_1.as_ref() {
                    Term::Const(Constant::String(s)) => Ok(s.len()),
                    _ => Err(CheckerError::LengthCannotBeEvaluated(r.clone())),
                }
            }
            Term::Op(Operator::ReUnion, args) => {
                has_same_length(pool, args, r.clone(), Operator::ReNone)
            }
            Term::Op(Operator::ReIntersection, args) => {
                has_same_length(pool, args, r.clone(), Operator::ReAll)
            }
            _ => Err(CheckerError::LengthCannotBeEvaluated(r.clone())),
        }
    }

    fn upstream_is_syntactically_nonnegative(term: &Rc<Term>) -> bool {
        match term.as_ref() {
            Term::Const(Constant::Integer(i)) => !i.is_negative(),
            Term::Const(Constant::Real(r)) => !r.is_negative(),
            // `str.len` is non-negative in every SMT-LIB model.
            Term::Op(Operator::StrLen, _) => true,
            // A sum or a product of non-negative integers is non-negative.
            Term::Op(Operator::Add | Operator::Mult, args) => {
                !args.is_empty() && args.iter().all(upstream_is_syntactically_nonnegative)
            }
            _ => false,
        }
    }

    /// Added in Clean: the loops answer what the recursions answered, errors included, on random
    /// shared regular expressions and integer terms.
    #[test]
    fn fixed_lengths_and_split_points_are_upstreams() {
        let mut pool = PrimitivePool::new();
        let string = pool.add_sort(Sort::String);
        let int = pool.add_sort(Sort::Int);
        let x = pool.add(Term::new_var("x", string));
        let n = pool.add(Term::new_var("n", int));
        // Leaves that can be measured first, then those that cannot (or are ignored).
        let (a, z) = (
            pool.add(Term::new_string("a")),
            pool.add(Term::new_string("z")),
        );
        let mut regexes = vec![
            pool.add(Term::Op(Operator::ReAllChar, vec![])),
            pool.add(Term::Op(Operator::ReRange, vec![a, z])),
        ];
        for w in ["a", "ab", "", "\u{e9}"] {
            let w = pool.add(Term::new_string(w));
            regexes.push(pool.add(Term::Op(Operator::StrToRe, vec![w])));
        }
        let measurable = regexes.len();
        let a = regexes[2].clone();
        regexes.push(pool.add(Term::Op(Operator::StrToRe, vec![x.clone()])));
        regexes.push(pool.add(Term::Op(Operator::ReNone, vec![])));
        regexes.push(pool.add(Term::Op(Operator::ReAll, vec![])));
        regexes.push(pool.add(Term::Op(Operator::ReKleeneClosure, vec![a])));
        // Non-negative leaves first, then the others.
        let mut numbers = vec![
            pool.add(Term::new_int(0)),
            pool.add(Term::new_int(3)),
            pool.add(Term::Op(Operator::StrLen, vec![x])),
            pool.add(Term::new_real((1, 2))),
        ];
        let nonnegative_leaves = numbers.len();
        numbers.push(pool.add(Term::new_int(-1)));
        numbers.push(n);
        numbers.push(pool.add(Term::new_real((-1, 2))));
        // The terms that can be measured (are non-negative), built ones included. Only terms less
        // than 5 deep are reused: upstream's recursions, run here, walk every path.
        let mut good_regexes = regexes[..measurable].to_vec();
        let mut good_numbers = numbers[..nonnegative_leaves].to_vec();
        let mut depth: HashMap<Rc<Term>, usize> = HashMap::new();
        let mut depth_of = |t: &Rc<Term>| {
            let d = 1 + t.as_op().map_or(0, |(_, args)| {
                args.iter()
                    .map(|a| depth.get(a).copied().unwrap_or(0))
                    .max()
                    .unwrap_or(0)
            });
            depth.insert(t.clone(), d);
            d
        };

        let mut rng = Rng(0x0123_4567_89ab_cdef);
        // One time in eight any term so far, otherwise one of the good ones, mostly of the last 16
        // built (so subterms are shared and terms grow deep).
        let pick = |rng: &mut Rng, all: &[Rc<Term>], good: &[Rc<Term>]| {
            if rng.below(8) == 0 {
                return all[rng.below(all.len())].clone();
            }
            let recent = good.len().min(16);
            match rng.below(4) {
                0 => good[rng.below(good.len())].clone(),
                _ => good[good.len() - 1 - rng.below(recent)].clone(),
            }
        };
        let (mut measured, mut nonnegative) = (0, 0);
        for _ in 0..3000 {
            let k = 2 + rng.below(3);
            let op = [
                Operator::ReConcat,
                Operator::ReUnion,
                Operator::ReIntersection,
            ][rng.below(3)];
            let args = (0..k)
                .map(|_| pick(&mut rng, &regexes, &good_regexes))
                .collect();
            let r = pool.add(Term::Op(op, args));
            let shallow = depth_of(&r) < 5;
            if shallow {
                regexes.push(r.clone());
            }
            let new = str_fixed_len_re(&r);
            match (upstream_str_fixed_len_re(&mut pool, r.clone()), new) {
                (Ok(a), Ok(b)) => {
                    assert_eq!(a, b, "{r}");
                    if shallow {
                        good_regexes.push(r.clone());
                    }
                    measured += 1;
                }
                (
                    Err(CheckerError::LengthCannotBeEvaluated(a)),
                    Err(CheckerError::LengthCannotBeEvaluated(b)),
                ) => assert_eq!(a, b, "{r}"),
                (a, b) => panic!("{r}: {a:?} {b:?}"),
            }

            let op = [Operator::Add, Operator::Mult, Operator::Add, Operator::Sub][rng.below(4)];
            let args = (0..k)
                .map(|_| pick(&mut rng, &numbers, &good_numbers))
                .collect();
            let t = pool.add(Term::Op(op, args));
            let shallow = depth_of(&t) < 5;
            if shallow {
                numbers.push(t.clone());
            }
            let new = is_syntactically_nonnegative(&t);
            assert_eq!(upstream_is_syntactically_nonnegative(&t), new, "{t}");
            if new {
                if shallow {
                    good_numbers.push(t);
                }
                nonnegative += 1;
            }
        }
        assert!(
            measured > 100 && nonnegative > 100,
            "{measured} {nonnegative}"
        );
    }

    /// Added in Clean: a step decides each pair of terms once, through one comparator. Two chains
    /// of `2^12` copies of terms equal only modulo the order of an equality strip to their last
    /// entries deciding as many pairs as chains of two copies do (upstream compared `2^12 + 1`
    /// entries, each walking both terms). And `n` distinct entries `(str.at X_d i)` against
    /// `(str.at Y_d i)`, `X_d` and `Y_d` equal only modulo the order of an equality `d` levels
    /// down, decide about `n + d` pairs, not `n` walks of `d` levels.
    #[test]
    fn a_step_decides_each_pair_of_terms_once() {
        let mut pool = PrimitivePool::new();
        let (string, int) = (pool.add_sort(Sort::String), pool.add_sort(Sort::Int));
        let x = pool.add(Term::new_var("x", string));
        let (u, v) = (
            pool.add(Term::new_var("u", int.clone())),
            pool.add(Term::new_var("v", int)),
        );
        let (zero, one) = (pool.add(Term::new_int(0)), pool.add(Term::new_int(1)));
        let mut copies = |(p, q): (&Rc<Term>, &Rc<Term>), levels: usize, last: &str| {
            let eq = pool.add(Term::Op(Operator::Equals, vec![p.clone(), q.clone()]));
            let ite = pool.add(Term::Op(Operator::Ite, vec![eq, zero.clone(), one.clone()]));
            let mut chain = pool.add(Term::Op(
                Operator::Substring,
                vec![x.clone(), ite, one.clone()],
            ));
            for _ in 0..levels {
                chain = pool.add(Term::Op(Operator::StrConcat, vec![chain.clone(), chain]));
            }
            let last = pool.add(Term::new_string(last));
            pool.add(Term::Op(Operator::StrConcat, vec![chain, last]))
        };
        let pairs: Vec<_> = [1, 12]
            .into_iter()
            .map(|levels| (copies((&u, &v), levels, "a"), copies((&v, &u), levels, "b")))
            .collect();
        let mut decided = Vec::new();
        for (s, t) in pairs {
            let mut time = Duration::ZERO;
            let mut step = StringStep::new(&pool);
            let (ss, ts) =
                strip_prefix_or_suffix(&mut step, s.clone(), t.clone(), false, &mut time).unwrap();
            assert_eq!((ss.len(), ts.len()), (1, 1));
            decided.push(step.comparator.decided());
            assert!(is_prefix_or_suffix(&mut step, s, t, false, &mut time).is_err());
        }
        assert!(decided[0] == decided[1] && decided[0] < 8, "{decided:?}");

        let (d, n) = (300, 300);
        let five = pool.add(Term::new_int(5));
        let mut entries = |(p, q): (&Rc<Term>, &Rc<Term>), last: &str| {
            let eq = pool.add(Term::Op(Operator::Equals, vec![p.clone(), q.clone()]));
            let (a, b) = (
                pool.add(Term::new_string("aaaaaa")),
                pool.add(Term::new_string("bbbbbb")),
            );
            let mut chain = pool.add(Term::Op(Operator::Ite, vec![eq, a, b]));
            for _ in 0..d {
                chain = pool.add(Term::Op(
                    Operator::Substring,
                    vec![chain, zero.clone(), five.clone()],
                ));
            }
            let mut args: Vec<Rc<Term>> = (0..n)
                .map(|i| {
                    let i = pool.add(Term::new_int(i));
                    pool.add(Term::Op(Operator::CharAt, vec![chain.clone(), i]))
                })
                .collect();
            args.push(pool.add(Term::new_string(last)));
            pool.add(Term::Op(Operator::StrConcat, args))
        };
        let s = entries((&u, &v), "a");
        let t = entries((&v, &u), "b");
        let mut time = Duration::ZERO;
        let mut step = StringStep::new(&pool);
        let (ss, ts) = strip_prefix_or_suffix(&mut step, s, t, false, &mut time).unwrap();
        assert_eq!((ss.len(), ts.len()), (1, 1));
        let decided = step.comparator.decided();
        assert!((n + d..n + d + 8).contains(&decided), "{decided}");
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

    /// Terms over strings, integers and Booleans, each built from earlier ones, so subterms are
    /// shared: nested `str.++` applications (of up to four arguments) over variables and constants
    /// (empty, one character, several, one of two bytes), and the operators, binders and `let`
    /// that `expand_string_constants` walks into.
    fn random_terms(pool: &mut PrimitivePool, seed: u64, count: usize) -> Vec<Rc<Term>> {
        let mut rng = Rng(seed);
        let string = pool.add_sort(Sort::String);
        let mut strings: Vec<Rc<Term>> = ["x", "y"]
            .iter()
            .map(|n| pool.add(Term::new_var(*n, string.clone())))
            .collect();
        for c in ["", "a", "b", "ab", "abc", "\u{e9}a", "aab"] {
            strings.push(pool.add(Term::new_string(c)));
        }
        let mut others: Vec<Rc<Term>> = vec![pool.add(Term::new_int(0))];
        let mut all = Vec::new();
        for _ in 0..count {
            let pick = |rng: &mut Rng, v: &Vec<Rc<Term>>| v[rng.below(v.len())].clone();
            let term = match rng.below(10) {
                0..=3 => {
                    let n = 2 + rng.below(3);
                    let args = (0..n).map(|_| pick(&mut rng, &strings)).collect();
                    pool.add(Term::Op(Operator::StrConcat, args))
                }
                4 => {
                    let (s, i) = (pick(&mut rng, &strings), pick(&mut rng, &others));
                    pool.add(Term::Op(Operator::Substring, vec![s, i.clone(), i]))
                }
                5 => {
                    let s = pick(&mut rng, &strings);
                    pool.add(Term::Op(Operator::StrLen, vec![s]))
                }
                6 => {
                    let (s, t) = (pick(&mut rng, &strings), pick(&mut rng, &strings));
                    pool.add(Term::Op(Operator::Equals, vec![s, t]))
                }
                7 => {
                    let (a, b) = (pick(&mut rng, &others), pick(&mut rng, &others));
                    pool.add(Term::Op(Operator::Add, vec![a, b]))
                }
                8 => {
                    let s = pick(&mut rng, &strings);
                    let z = pool.add(Term::new_var("z", string.clone()));
                    let body = pool.add(Term::Op(Operator::Equals, vec![z, s]));
                    let bindings = BindingList(vec![("z".into(), string.clone())]);
                    pool.add(Term::Binder(Binder::Exists, bindings, body))
                }
                _ => {
                    let (v, s) = (pick(&mut rng, &strings), pick(&mut rng, &strings));
                    let bindings = BindingList(vec![("w".into(), v)]);
                    pool.add(Term::Let(bindings, s))
                }
            };
            match pool.sort(&term).as_ref() {
                Sort::String => strings.push(term.clone()),
                _ => others.push(term.clone()),
            }
            all.push(term);
        }
        all.extend(strings);
        all
    }

    /// Added in Clean: the loops build what upstream's recursions built, term for term, and the
    /// count a flattening is charged is at least its length and its visits.
    #[test]
    fn flattenings_and_expansions_are_upstreams() {
        for seed in 1..=8u64 {
            let mut pool = PrimitivePool::new();
            let terms = random_terms(&mut pool, seed * 0x9e37_79b9_7f4a_7c15, 400);
            for term in &terms {
                let flat = upstream_flatten(&mut pool, term.clone());
                let extracted = upstream_extract(term.clone());
                let expanded = upstream_expand(&mut pool, term);
                let size = pool.terms.len();
                let mut step = StringStep::new(&pool);
                assert_eq!(step.string_concat_flatten(term).unwrap(), flat, "{term}");
                assert_eq!(step.concat_extract(term).unwrap(), extracted, "{term}");
                assert_eq!(
                    step.expand_string_constants(term).unwrap(),
                    expanded,
                    "{term}"
                );
                for (mode, len) in [
                    (Constants::Split, flat.len()),
                    (Constants::Keep, extracted.len()),
                ] {
                    let count = step.count(term, mode);
                    assert_eq!(count.entries, len as u128, "{term}");
                    assert!(count.cost >= count.entries.max(1), "{term}");
                }
                drop(step);
                assert_eq!(pool.terms.len(), size);
            }
        }
    }

    /// Added in Clean: a flattening's cost counts what the walk visits, once per path, so a chain
    /// of `(str.++ "" "")` that flattens to nothing is charged for its `2^d` paths.
    #[test]
    fn a_flattening_is_charged_for_every_path() {
        let mut pool = PrimitivePool::new();
        let empty = pool.add(Term::new_string(""));
        let mut chain = empty.clone();
        for _ in 0..70 {
            chain = pool.add(Term::Op(Operator::StrConcat, vec![chain.clone(), chain]));
        }
        let mut step = StringStep::new(&pool);
        assert_eq!(step.count(&chain, Constants::Split).entries, 0);
        assert_eq!(step.count(&chain, Constants::Split).cost, (1 << 71) - 1);
        assert!(matches!(
            step.string_concat_flatten(&chain),
            Err(CheckerError::ResourceBudgetExceeded(b)) if b.budget == MAX_EXPANDED_BITS
        ));
    }

    /// Added in Clean: an accepted step of a string rule leaves no term in the pool. Upstream added
    /// each flattening, `2^d` arguments over a chain `d` deep, for the rest of the proof.
    #[test]
    fn string_rules_add_no_terms_to_the_pool() {
        let mut chain = "(! (str.++ x x) :named n1)".to_owned();
        for i in 2..=12 {
            chain = format!("(! (str.++ {chain} n{}) :named n{i})", i - 1);
        }
        let premise = format!("(= (str.++ \"ab\" {chain}) (str.++ \"ba\" n12))");
        let proof = format!(
            "(assume h1 {premise})(step t1 (cl {premise}) :rule concat_eq :premises (h1) \
             :args (false))(step t2 (cl) :rule hole)"
        );
        let (mut problem, proof, rules, mut pool) = parser::parse_instance(
            "(declare-const x String)",
            &proof,
            None,
            parser::Config::new(),
        )
        .unwrap();
        problem.premises = proof
            .commands
            .iter()
            .filter_map(|c| match c {
                crate::ast::ProofCommand::Assume { term, .. } => Some(term.clone()),
                _ => None,
            })
            .collect();
        let before = pool.terms.len();
        let verdict = checker::ProofChecker::new(&mut pool, &rules, checker::Config::new())
            .check(&problem, &proof);
        assert!(matches!(verdict, Ok(true)), "{verdict:?}");
        assert_eq!(pool.terms.len(), before);
    }
}
