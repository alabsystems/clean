//! This module implements `TermPool`, a structure that stores terms and implements hash consing.

pub mod advanced;
mod free_vars;
mod storage;

pub use free_vars::{first_free_var, FreeVars};
#[cfg(test)]
pub(crate) use free_vars::{nodes_allocated, ALLOCATION};
pub(crate) use free_vars::{Fuel, Trie};

use super::{
    Binder, Constant, Operator, ParamOperator, Rc, Sort, SortSubstitution, SortedVar, Term,
};
use indexmap::{IndexMap, IndexSet};
use storage::Storage;

/// A user-defined datatype.
#[derive(Debug, Clone)]
pub struct Datatype {
    /// The datatype parameters
    pub params: Vec<String>,

    /// The constructors, indexed by their name.
    pub constructors: IndexMap<String, DatatypeConstructor>,
}

/// A constructor for a datatype.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DatatypeConstructor {
    /// The constructor selectors.
    pub selectors: Vec<SortedVar>,
}

pub trait TermPool {
    /// Returns the term corresponding to the boolean constant `true`.
    fn bool_true(&mut self) -> Rc<Term> {
        self.bool_constant(true)
    }

    /// Returns the term corresponding to the boolean constant `false`.
    fn bool_false(&mut self) -> Rc<Term> {
        self.bool_constant(false)
    }

    /// Returns the term corresponding to the boolean constant determined by `value`.
    fn bool_constant(&mut self, value: bool) -> Rc<Term> {
        self.add(Term::new_bool(value))
    }

    /// Takes a term and returns a possibly newly allocated `Rc` that references it.
    ///
    /// If the term was not originally in the term pool, it is added to it. Otherwise, this method
    /// just returns an `Rc` pointing to the existing allocation. This method also computes the
    /// term's sort, and adds it to the sort cache.
    fn add(&mut self, term: Term) -> Rc<Term>;

    /// Returns the `Rc` the pool holds for `term`, without adding `term` if it holds none.
    ///
    /// Added in Clean: it lets a rule hash-cons the terms it builds for one step outside the pool
    /// (see `StepTerms`).
    fn find(&self, term: &Term) -> Option<Rc<Term>>;

    /// Takes a sort and returns a possibly newly allocated `Rc` that references it.
    ///
    /// If the sort was not originally in the term pool, it is added to it. Otherwise, this method
    /// just returns an `Rc` pointing to the existing allocation.
    fn add_sort(&mut self, sort: Sort) -> Rc<Sort>;

    /// Takes a vector of terms and calls [`TermPool::add`] on each.
    fn add_all(&mut self, terms: Vec<Term>) -> Vec<Rc<Term>> {
        terms.into_iter().map(|t| self.add(t)).collect()
    }

    /// Returns the sort of the given term.
    ///
    /// This method assumes that the sorts of any subterms have already been checked, and are
    /// correct.
    fn sort(&self, term: &Rc<Term>) -> Rc<Sort>;

    /// Returns the free variables of the given term.
    ///
    /// This method uses a cache, so there is no additional cost to computing the free variables of
    /// a term multiple times.
    ///
    /// Modified in Clean: the set is a `FreeVars`, which shares structure with the sets of the
    /// term's subterms, where it was an `IndexSet` copied from them: a chain of `n` terms over
    /// distinct constants cached `n^2 / 2` entries. It holds the same variables; the order in which
    /// it lists them is not deterministic, and no caller depends on it (see
    /// third-party/carcara/DOWNSTREAM.md, "Free-variable sets share structure").
    fn free_vars(&mut self, term: &Rc<Term>) -> FreeVars;

    /// Searches the pool for a defined datatype with the given name. Panics if no datatype is
    /// found.
    fn get_datatype(&self, name: &str) -> &Datatype;
}

/// Added in Clean: hash-conses the terms one step builds that need not outlive it, on top of a pool
/// it only reads. A term the pool holds is the pool's `Rc`, any other is allocated here, so terms
/// built through it compare by pointer exactly as if the pool had added them. Dropping it frees the
/// terms only it holds (an `Rc` that escapes, into an error say, keeps its own term alive), where
/// terms added to the pool stay for the rest of the proof. It computes no sorts: a rule asks the
/// pool for the sorts of the terms it read, not of these.
pub(crate) struct StepTerms<'p> {
    pool: &'p dyn TermPool,
    terms: Storage<Term>,
}

impl<'p> StepTerms<'p> {
    pub(crate) fn new(pool: &'p dyn TermPool) -> Self {
        Self { pool, terms: Storage::default() }
    }

    /// The pool's `Rc` for `term` if the pool holds it, and otherwise this step's, allocated on
    /// first use. The pool does not change while this borrows it, so no term is in both.
    pub(crate) fn add(&mut self, term: Term) -> Rc<Term> {
        match self.pool.find(&term) {
            Some(term) => term,
            None => self.terms.add(term),
        }
    }
}

/// A structure to store and manage all allocated terms.
///
/// You can add a `Term` to the pool using [`PrimitivePool::add`], which will return an `Rc<Term>`. This
/// struct ensures that, if two equal terms are added to a pool, they will be in the same
/// allocation. This invariant allows terms to be safely compared and hashed by reference, instead
/// of by value (see [`Rc`]).
///
/// This struct also provides other utility methods, like computing the sort of a term (see
/// [`PrimitivePool::sort`]) or its free variables (see [`PrimitivePool::free_vars`]).
#[derive(Debug, Default)]
pub struct PrimitivePool {
    pub(crate) terms: Storage<Term>,
    pub(crate) sorts: Storage<Sort>,
    pub(crate) free_vars_cache: IndexMap<Rc<Term>, FreeVars>,
    pub(crate) sorts_cache: IndexMap<Rc<Term>, Rc<Sort>>,
    pub(crate) binders_cache: IndexMap<(Rc<Term>, Binder), IndexSet<Rc<Term>>>,
    pub(crate) datatypes: IndexMap<String, Datatype>,
}

impl PrimitivePool {
    /// Constructs a new `TermPool`. This new pool will already contain the boolean constants `true`
    /// and `false`, as well as the `Bool` sort.
    pub fn new() -> Self {
        Self::default()
    }

    /// Computes the sort of a term and adds it to the sort cache.
    fn compute_sort(&mut self, term: &Rc<Term>) -> &Rc<Sort> {
        if self.sorts_cache.contains_key(term) {
            return &self.sorts_cache[term];
        }

        let result = match term.as_ref() {
            Term::Const(c) => self.sorts.add(match c {
                Constant::Integer(_) => Sort::Int,
                Constant::Real(_) => Sort::Real,
                Constant::String(_) => Sort::String,
                Constant::RegLan(_, _) => Sort::RegLan,
                Constant::BitVec(_, w) => Sort::BitVec(*w),
            }),
            Term::Var(_, sort) => sort.clone(),
            Term::Op(op, args) => match op {
                Operator::True
                | Operator::False
                | Operator::Not
                | Operator::Implies
                | Operator::And
                | Operator::Or
                | Operator::Xor
                | Operator::Equals
                | Operator::Distinct
                | Operator::LessThan
                | Operator::GreaterThan
                | Operator::LessEq
                | Operator::GreaterEq
                | Operator::IsInt
                | Operator::StrLessThan
                | Operator::StrLessEq
                | Operator::PrefixOf
                | Operator::SuffixOf
                | Operator::Contains
                | Operator::StrIsDigit
                | Operator::StrInRe
                | Operator::BvULt
                | Operator::BvULe
                | Operator::BvUGt
                | Operator::BvUGe
                | Operator::BvSLt
                | Operator::BvSLe
                | Operator::BvSGt
                | Operator::BvSGe
                | Operator::Cl
                | Operator::Delete => self.sorts.add(Sort::Bool),

                Operator::BvSize | Operator::UBvToInt | Operator::SBvToInt => {
                    self.sorts.add(Sort::Int)
                }

                Operator::BvAdd
                | Operator::BvSub
                | Operator::BvNot
                | Operator::BvNeg
                | Operator::BvAnd
                | Operator::BvOr
                | Operator::BvMul
                | Operator::BvUDiv
                | Operator::BvURem
                | Operator::BvShl
                | Operator::BvLShr
                | Operator::BvNAnd
                | Operator::BvNOr
                | Operator::BvXor
                | Operator::BvXNor
                | Operator::BvSDiv
                | Operator::BvSRem
                | Operator::BvSMod
                | Operator::BvAShr => 'block: {
                    for a in args {
                        match self.compute_sort(a).as_ref() {
                            Sort::BitVec(_) => break 'block self.compute_sort(a).clone(),
                            Sort::ParamBitVec => (),
                            _ => unreachable!(),
                        }
                    }
                    self.sorts.add(Sort::ParamBitVec)
                }
                Operator::BvComp => self.sorts.add(Sort::BitVec(1)),
                Operator::BvBbTerm | Operator::BvPBbTerm => {
                    self.sorts.add(Sort::BitVec(args.len()))
                }
                Operator::BvConst => {
                    let s = match &*args[1] {
                        Term::Const(Constant::Integer(bvsize)) => {
                            Sort::BitVec(bvsize.to_usize().unwrap())
                        }
                        _ => Sort::ParamBitVec,
                    };
                    self.sorts.add(s)
                }
                Operator::BvConcat => {
                    let s = args.iter().map(|a| self.compute_sort(a).clone()).fold(
                        Sort::BitVec(0),
                        |acc, sort| match (acc, sort.as_ref()) {
                            (Sort::BitVec(a), Sort::BitVec(b)) => Sort::BitVec(a + b),
                            (Sort::BitVec(_) | Sort::ParamBitVec, Sort::ParamBitVec)
                            | (Sort::ParamBitVec, Sort::BitVec(_)) => Sort::ParamBitVec,
                            _ => unreachable!(),
                        },
                    );
                    self.sorts.add(s)
                }
                Operator::Ite => self.compute_sort(&args[1]).clone(),
                Operator::Abs => self.compute_sort(&args[0]).clone(),
                Operator::Add | Operator::Sub | Operator::Mult => {
                    let s = if args
                        .iter()
                        .any(|a| self.compute_sort(a).as_ref() == &Sort::Real)
                    {
                        Sort::Real
                    } else {
                        Sort::Int
                    };
                    self.sorts.add(s)
                }
                Operator::RealDiv | Operator::ToReal => self.sorts.add(Sort::Real),
                Operator::IntDiv | Operator::Mod | Operator::ToInt => self.sorts.add(Sort::Int),
                Operator::Select => {
                    let Sort::Array(_, y) = self.compute_sort(&args[0]).as_ref() else {
                        unreachable!()
                    };
                    y.clone()
                }
                Operator::Store => self.compute_sort(&args[0]).clone(),
                Operator::StrLen
                | Operator::IndexOf
                | Operator::IndexOfRe
                | Operator::StrToCode
                | Operator::StrToInt => self.sorts.add(Sort::Int),
                Operator::StrConcat
                | Operator::CharAt
                | Operator::Substring
                | Operator::Replace
                | Operator::ReplaceAll
                | Operator::ReplaceRe
                | Operator::ReplaceReAll
                | Operator::StrFromCode
                | Operator::StrFromInt => self.sorts.add(Sort::String),
                Operator::StrToRe
                | Operator::ReNone
                | Operator::ReAll
                | Operator::ReAllChar
                | Operator::ReConcat
                | Operator::ReUnion
                | Operator::ReIntersection
                | Operator::ReKleeneClosure
                | Operator::ReComplement
                | Operator::ReDiff
                | Operator::ReKleeneCross
                | Operator::ReOption
                | Operator::ReRange
                | Operator::ReFromAutomaton => self.sorts.add(Sort::RegLan),
                Operator::RareList => match args.as_slice() {
                    // For empty lists, we can't know the element sort, so we use a placeholder
                    // variable sort `?`
                    [] => self.sorts.add(Sort::Var("?".to_owned())),
                    [arg, ..] => self.compute_sort(arg).clone(),
                },
                Operator::Pow2 | Operator::Log2 => self.sorts.add(Sort::Int),
                Operator::IsPow2 => self.sorts.add(Sort::Bool),

                Operator::RealPi
                | Operator::Sqrt
                | Operator::Exp
                | Operator::Sin
                | Operator::Cos
                | Operator::Tan
                | Operator::Csc
                | Operator::Sec
                | Operator::Cot
                | Operator::Arcsin
                | Operator::Arccos
                | Operator::Arctan
                | Operator::Arccsc
                | Operator::Arcsec
                | Operator::Arccot => self.sorts.add(Sort::Real),

                // Sets and relations
                Operator::SetUnion
                | Operator::SetInter
                | Operator::SetMinus
                | Operator::SetComplement => self.compute_sort(&args[0]).clone(),
                Operator::SetMember
                | Operator::SetSubset
                | Operator::SetIsEmpty
                | Operator::SetIsSingleton => self.sorts.add(Sort::Bool),
                Operator::SetSingleton => {
                    let elem_sort = Sort::Set(self.compute_sort(&args[0]).clone());
                    self.sorts.add(elem_sort)
                }
                Operator::SetCard => self.sorts.add(Sort::Int),
                Operator::SetInsert => self.compute_sort(args.last().unwrap()).clone(),
                Operator::Tuple => {
                    let sorts = args
                        .iter()
                        .map(|elem| self.compute_sort(elem).clone())
                        .collect();
                    self.sorts.add(Sort::Tuple(sorts))
                }
                Operator::TupleUnit => self.sorts.add(Sort::Tuple(Vec::new())),
                Operator::RelTranspose => {
                    let sort = self.compute_sort(&args[0]);
                    let Sort::Set(tuple) = sort.as_ref() else {
                        unreachable!()
                    };
                    let Sort::Tuple(sorts) = tuple.as_ref() else {
                        unreachable!()
                    };
                    let mut sorts = sorts.clone();
                    sorts.reverse();
                    let tuple = self.sorts.add(Sort::Tuple(sorts));
                    self.sorts.add(Sort::Set(tuple))
                }
                Operator::RelTclosure => self.compute_sort(&args[0]).clone(),
                Operator::RelJoin => {
                    let [mut left, right] = [&args[0], &args[1]].map(|arg| {
                        let sort = self.compute_sort(arg).clone();
                        let Sort::Set(tuple) = sort.as_ref() else {
                            unreachable!()
                        };
                        let Sort::Tuple(sorts) = tuple.as_ref() else {
                            unreachable!()
                        };
                        sorts.clone()
                    });
                    left.pop();
                    left.extend_from_slice(&right[1..]);
                    let tuple = self.sorts.add(Sort::Tuple(left));
                    self.sorts.add(Sort::Set(tuple))
                }
                Operator::RelProduct => {
                    let [mut left, right] = [&args[0], &args[1]].map(|arg| {
                        let sort = self.compute_sort(arg).clone();
                        let Sort::Set(tuple) = sort.as_ref() else {
                            unreachable!()
                        };
                        let Sort::Tuple(sorts) = tuple.as_ref() else {
                            unreachable!()
                        };
                        sorts.clone()
                    });
                    left.extend(right);
                    let tuple = self.sorts.add(Sort::Tuple(left));
                    self.sorts.add(Sort::Set(tuple))
                }
            },
            Term::App(f, args) => {
                let func_sort = self.compute_sort(f).clone();
                let (is_parametric, sorts) = match func_sort.as_ref() {
                    Sort::Function(sorts) => (false, sorts),
                    Sort::Par(_, inner) => {
                        if let Sort::Function(sorts) = inner.as_ref() {
                            (true, sorts)
                        } else {
                            unreachable!()
                        }
                    }
                    _ => unreachable!(), // We assume that the function is correctly sorted
                };

                // If all arguments were provided, we just have the return sort of the function.
                // Otherwise, we get back a partially applied function sort.
                let applied = if args.len() + 1 == sorts.len() {
                    sorts.last().unwrap().clone()
                } else {
                    let remaining_sorts = sorts[args.len()..].to_vec();
                    self.sorts.add(Sort::Function(remaining_sorts))
                };

                // If parametric, match with sorts of args, apply the resulting substitution on
                // the sort
                if is_parametric {
                    let mut map = IndexMap::new();
                    for i in 0..args.len() {
                        if !sorts[i].match_with(self.compute_sort(&args[i]), &mut map) {
                            unreachable!();
                        }
                    }
                    SortSubstitution::new(map).apply(self, &applied)
                } else {
                    applied
                }
            }
            Term::Binder(Binder::Forall | Binder::Exists, _, _) => self.sorts.add(Sort::Bool),
            Term::Binder(Binder::Choice, v, _) => v[0].1.clone(),
            Term::Binder(Binder::Lambda, bindings, body) => {
                let mut result: Vec<_> =
                    bindings.iter().map(|(_name, sort)| sort.clone()).collect();
                result.push(self.compute_sort(body).clone());
                self.sorts.add(Sort::Function(result))
            }
            Term::Let(_, inner) => self.compute_sort(inner).clone(),
            Term::Match(_, cases) => self.compute_sort(&cases.last().unwrap().body).clone(),
            Term::ParamOp { op, op_args, args } => self
                .compute_indexed_op_sort(*op, op_args, args)
                .unwrap_or_else(|| self.add_sort(Sort::ParamBitVec)),
            Term::AsOp(_, sort, _) => sort.clone(),
        };
        self.sorts_cache.insert(term.clone(), result);
        &self.sorts_cache[term]
    }

    // `None` means `ParamBitVec`
    fn compute_indexed_op_sort(
        &mut self,
        op: ParamOperator,
        op_args: &[Rc<Term>],
        args: &[Rc<Term>],
    ) -> Option<Rc<Sort>> {
        let res = match op {
            ParamOperator::BvExtract => {
                let i = op_args[0].as_integer()?.to_usize().unwrap();
                let j = op_args[1].as_integer()?.to_usize().unwrap();
                Sort::BitVec(i - j + 1)
            }
            ParamOperator::ZeroExtend | ParamOperator::SignExtend => {
                let extension_width = op_args[0].as_integer()?.to_usize().unwrap();
                match self.compute_sort(&args[0]).as_ref() {
                    Sort::BitVec(bv_width) => Sort::BitVec(extension_width + bv_width),
                    Sort::ParamBitVec => return None,
                    _ => unreachable!(),
                }
            }
            ParamOperator::RotateLeft | ParamOperator::RotateRight => {
                return Some(self.compute_sort(&args[0]).clone())
            }
            ParamOperator::Repeat => {
                let repetitions = op_args[0].as_integer()?;
                match self.compute_sort(&args[0]).as_ref() {
                    Sort::BitVec(bv_width) => {
                        Sort::BitVec((repetitions * bv_width).to_usize().unwrap())
                    }
                    Sort::ParamBitVec => return None,
                    _ => unreachable!(),
                }
            }
            ParamOperator::BvConst => unreachable!(
                "bv const should be handled by the parser and transformed into a constant"
            ),
            ParamOperator::IntToBv => {
                let bvsize = op_args[0].as_integer()?.to_usize().unwrap();
                Sort::BitVec(bvsize)
            }
            ParamOperator::BvBitOf | ParamOperator::Tester => Sort::Bool,
            ParamOperator::BvIntOf => Sort::Int,
            ParamOperator::RePower | ParamOperator::ReLoop => Sort::RegLan,
            ParamOperator::TupleSelect => {
                let i = op_args[0].as_integer()?.to_usize().unwrap();
                return Some(self.compute_sort(&args[i]).clone());
            }
        };
        Some(self.add_sort(res))
    }

    fn add_with_priorities<const N: usize>(
        &mut self,
        term: Term,
        prior_pools: [&PrimitivePool; N],
    ) -> Rc<Term> {
        for p in prior_pools {
            // If this prior pool has the term
            if let Some(entry) = p.terms.get(&term) {
                return entry.clone();
            }
        }
        self.add(term)
    }

    fn sort_with_priorities<const N: usize>(
        &mut self,
        term: &Rc<Term>,
        prior_pools: [&PrimitivePool; N],
    ) -> Rc<Sort> {
        for p in prior_pools {
            if let Some(sort) = p.sorts_cache.get(term) {
                return sort.clone();
            }
        }
        self.sorts_cache[term].clone()
    }

    /// The free variables of `term`, read from the first of `prior_pools` that has them cached,
    /// or computed and cached in this pool.
    ///
    /// Modified in Clean: the sets are `FreeVars`, which share structure (see `TermPool::free_vars`),
    /// and they are computed by a walk with a stack of its own instead of a recursion per level. The
    /// walk caches the terms upstream's recursion cached, the term and each subterm it reached,
    /// and adds to the pool the variables upstream's added: the proof printer reads how many
    /// references a term has (`Rc::strong_count`), and the cache holds one.
    pub fn free_vars_with_priorities<const N: usize>(
        &mut self,
        term: &Rc<Term>,
        prior_pools: [&PrimitivePool; N],
    ) -> FreeVars {
        if let Some(set) = self.cached_free_vars(term, prior_pools) {
            return set;
        }
        let mut stack: Vec<(&Rc<Term>, bool)> = vec![(term, false)];
        while let Some((current, ready)) = stack.pop() {
            if !ready {
                if self.cached_free_vars(current, prior_pools).is_some() {
                    continue;
                }
                stack.push((current, true));
                // Pushed last to first, so the first is computed first, as upstream's recursion did.
                let children: Vec<&Rc<Term>> = match current.as_ref() {
                    Term::App(f, args) => std::iter::once(f).chain(args.iter()).collect(),
                    Term::Op(_, args) | Term::ParamOp { args, .. } | Term::AsOp(_, _, args) => {
                        args.iter().collect()
                    }
                    Term::Binder(_, _, inner) => vec![inner],
                    Term::Let(bindings, inner) => std::iter::once(inner)
                        .chain(bindings.iter().map(|(_, value)| value))
                        .collect(),
                    Term::Match(term, cases) => std::iter::once(term)
                        .chain(cases.iter().map(|case| &case.body))
                        .collect(),
                    Term::Var(..) | Term::Const(_) => Vec::new(),
                };
                stack.extend(children.into_iter().rev().map(|child| (child, false)));
                continue;
            }
            if self.free_vars_cache.contains_key(current) {
                continue;
            }
            let child = |pool: &mut Self, t: &Rc<Term>| {
                pool.cached_free_vars(t, prior_pools)
                    .expect("invariant: a subterm's free variables are computed before its own")
            };
            let set = match current.as_ref() {
                Term::App(f, args) => {
                    let mut set = child(self, f);
                    for a in args {
                        set = set.union(&child(self, a));
                    }
                    set
                }
                Term::Op(_, args) | Term::ParamOp { args, .. } | Term::AsOp(_, _, args) => {
                    let mut set = FreeVars::default();
                    for a in args {
                        set = set.union(&child(self, a));
                    }
                    set
                }
                Term::Binder(_, bindings, inner) => {
                    let mut vars = child(self, inner);
                    for bound_var in bindings {
                        let term = self.add_with_priorities(bound_var.clone().into(), prior_pools);
                        vars = vars.without(&term);
                    }
                    vars
                }
                // Modified in Clean: the *values* of a `let` are terms of the enclosing scope, and
                // their free variables are free in the `let` term. They used to be ignored entirely,
                // so `(let ((y x)) y)` reported no free variables at all, and every check built on
                // `free_vars` — capture avoidance in substitutions, `check_not_exported`, the anchor
                // scoping checks — was blind to them (see third-party/carcara/DOWNSTREAM.md).
                Term::Let(bindings, inner) => {
                    let mut vars = child(self, inner);
                    for (var, value) in bindings {
                        let sort = self.sort_with_priorities(value, prior_pools);
                        let term =
                            self.add_with_priorities((var.clone(), sort).into(), prior_pools);
                        vars = vars.without(&term);
                    }
                    for (_, value) in bindings {
                        vars = vars.union(&child(self, value));
                    }
                    vars
                }
                Term::Match(term, cases) => {
                    let mut vars = child(self, term);
                    for case in cases {
                        let mut res_vars = child(self, &case.body);
                        for bound_var in case.bindings() {
                            let term =
                                self.add_with_priorities(bound_var.clone().into(), prior_pools);
                            res_vars = res_vars.without(&term);
                        }
                        vars = vars.union(&res_vars);
                    }
                    vars
                }
                Term::Var(..) => FreeVars::singleton(current),
                Term::Const(_) => FreeVars::default(),
            };
            self.free_vars_cache.insert(current.clone(), set);
        }
        self.free_vars_cache[term].clone()
    }

    /// The free variables of `term` cached by the first of `prior_pools` that has them, or by this
    /// pool.
    fn cached_free_vars<const N: usize>(
        &self,
        term: &Rc<Term>,
        prior_pools: [&PrimitivePool; N],
    ) -> Option<FreeVars> {
        prior_pools
            .iter()
            .find_map(|p| p.free_vars_cache.get(term))
            .or_else(|| self.free_vars_cache.get(term))
            .cloned()
    }

    pub fn add_datatype(&mut self, name: String, datatype: Datatype) {
        self.datatypes.insert(name, datatype);
    }

    pub fn collect_binders(&mut self, term: &Rc<Term>, binder: Binder) -> IndexSet<Rc<Term>> {
        if let Some(set) = self.binders_cache.get(&(term.clone(), binder)) {
            return set.clone();
        }
        let set = match term.as_ref() {
            Term::App(_, args)
            | Term::Op(_, args)
            | Term::ParamOp { args, .. }
            | Term::AsOp(_, _, args) => {
                let mut set = IndexSet::new();
                for a in args {
                    set.extend(self.collect_binders(a, binder).into_iter());
                }
                set
            }
            Term::Binder(b, _, inner) => {
                let mut set = IndexSet::new();
                if *b == Binder::Choice {
                    set.insert(term.clone());
                }
                set.extend(self.collect_binders(inner, binder));
                set
            }
            // Modified in Clean: a binder may also occur in a `let` value, which used to be
            // skipped (see third-party/carcara/DOWNSTREAM.md).
            Term::Let(bindings, inner) => {
                let mut set = self.collect_binders(inner, binder);
                for (_, value) in bindings {
                    set.extend(self.collect_binders(value, binder).into_iter());
                }
                set
            }
            Term::Match(term, cases) => {
                let mut set = self.collect_binders(term, binder);
                for case in cases {
                    set.extend(self.collect_binders(&case.body, binder).into_iter());
                }
                set
            }
            Term::Var(..) | Term::Const(_) => IndexSet::new(),
        };
        self.binders_cache.insert((term.clone(), binder), set);
        self.binders_cache
            .get(&(term.clone(), binder))
            .unwrap()
            .clone()
    }
}

impl TermPool for PrimitivePool {
    fn add(&mut self, term: Term) -> Rc<Term> {
        let term = self.terms.add(term);
        self.compute_sort(&term);
        term
    }

    fn find(&self, term: &Term) -> Option<Rc<Term>> {
        self.terms.get(term).cloned()
    }

    fn add_sort(&mut self, sort: Sort) -> Rc<Sort> {
        self.sorts.add(sort)
    }

    fn sort(&self, term: &Rc<Term>) -> Rc<Sort> {
        self.sorts_cache[term].clone()
    }

    fn free_vars(&mut self, term: &Rc<Term>) -> FreeVars {
        self.free_vars_with_priorities(term, [])
    }

    fn get_datatype(&self, name: &str) -> &Datatype {
        &self.datatypes[name]
    }
}
