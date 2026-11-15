//! This module implements less strict definitions of equality for terms. In particular, it
//! contains two definitions of equality that differ from `PartialEq`:
//!
//! - `polyeq` considers `=` terms that are reflections of each other as equal, meaning the terms
//!   `(= a b)` and `(= b a)` are considered equal by this method.
//!
//! - `alpha_equiv` compares terms by alpha-equivalence, meaning it implements equality of terms
//!   modulo renaming of bound variables.

use rug::Rational;

use super::{
    AnchorArg, BindingList, Constant, NaryCase, Operator, ProofCommand, ProofStep, Rc, Sort,
    Subproof, Term,
};
use std::collections::{hash_map::Entry, HashMap};
use std::time::{Duration, Instant};

/// Added in Clean: the comparator as it was before answers found under binders were reused across
/// them, kept as the oracle the comparator is tested against (`ast/tests.rs`).
#[cfg(test)]
#[path = "polyeq_oracle.rs"]
pub(super) mod oracle;

/// An helper enum that allow a construction of lists with easy differentiation over the nature of the term
/// (String constant or other). Therefore, is easy to manipulate, attach and detach terms of lists of
/// this type, making easy the process of comparing equal Strings modulo the String concatenation.
#[derive(Debug, Clone)]
enum Concat {
    Constant(String),
    Term(Rc<Term>),
}

/// A function that receives the list of arguments of an operation term and returns that same list with every
/// argument encapsulated by the constructors of the Concat enum . This will be helpful to process the terms and
/// compare if a String constant and a String concatenation are equivalents.
fn to_concat(args: &[Rc<Term>]) -> Vec<Concat> {
    args.iter()
        .map(|arg| match arg.as_ref() {
            Term::Const(Constant::String(s)) => Concat::Constant(s.clone()),
            _ => Concat::Term(arg.clone()),
        })
        .collect()
}

/// The value of a division literal `(/ n d)`, where `n` and `d` are integer-valued constants,
/// possibly negated with a unary `-`. Returns `None` for anything else, including `d = 0`.
fn division_literal_value(numerator: &Rc<Term>, denominator: &Rc<Term>) -> Option<Rational> {
    fn integer_constant(term: &Rc<Term>) -> Option<Rational> {
        match term.as_ref() {
            Term::Const(Constant::Integer(i)) => Some(Rational::from(i.clone())),
            Term::Const(Constant::Real(r)) if r.is_integer() => Some(r.clone()),
            Term::Op(Operator::Sub, args) if args.len() == 1 => match args[0].as_ref() {
                Term::Const(Constant::Integer(i)) => Some(-Rational::from(i.clone())),
                Term::Const(Constant::Real(r)) if r.is_integer() => Some(-r.clone()),
                _ => None,
            },
            _ => None,
        }
    }
    let (n, d) = (integer_constant(numerator)?, integer_constant(denominator)?);
    if d.is_zero() {
        return None;
    }
    Some(n / d)
}

/// A trait that represents objects that can be compared for equality modulo reordering of
/// equalities or alpha equivalence.
pub trait PolyeqComparable {
    /// Compares two objects with a given [`Polyeq`]. Returns `true` if they are equivalent.
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool;
}

/// Computes whether the two given terms are equal, modulo reordering of equalities.
///
/// That is, for this function, `=` terms that are reflections of each other are considered as
/// equal, meaning terms like `(and p (= a b))` and `(and p (= b a))` are considered equal.
///
/// This function records how long it takes to run, and adds that duration to the `time` argument.
pub fn polyeq(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> bool {
    Polyeq::new().mod_reordering(true).eq_with_time(a, b, time)
}

/// Similar to `polyeq`, but instead compares terms for alpha equivalence.
///
/// This means that two terms which are the same, except for the renaming of a bound variable, are
/// considered equivalent. This functions still considers equality modulo reordering of equalities.
/// For example, this function will consider the terms `(forall ((x Int)) (= x 0))` and `(forall ((y
/// Int)) (= 0 y))` as equivalent.
///
/// This function records how long it takes to run, and adds that duration to the `time` argument.
pub fn alpha_equiv(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> bool {
    Polyeq::new()
        .mod_reordering(true)
        .alpha_equiv(true)
        .eq_with_time(a, b, time)
}

/// Configuration for a `Polyeq`.
///
/// This controls how the comparison is performed and which families of terms are considered
/// equivalent.
#[derive(Default)]
pub struct PolyeqConfig {
    /// If set to true, term comparison will be done modulo reordering of equalities. That is, the
    /// terms `(= a b)` and `(= b a)` will be considered equivalent.
    pub is_mod_reordering: bool,

    /// If set to true, terms will be compared for alpha equivalence. That is, terms that can be
    /// made equal by renaming bound variables will be considered equivalent.
    pub is_alpha_equivalence: bool,

    /// If set to true, term comparison will be done modulo the expansion of n-ary operators. That
    /// is, the syntax sugar around n-ary operators will be expanded before comparison, such that
    /// the terms `(and a b c)` and `(and (and a b) c)` will be considered equivalent.
    pub is_mod_nary: bool,

    /// If set to true, term comparison will be done modulo the collection of string constant
    /// arguments in the `str.++` operator. That is, the terms `(str.++ "ab" "c")` and `(str.++ "a"
    /// "bc")` will be considered equivalent.
    pub is_mod_string_concat: bool,
}

impl PolyeqConfig {
    /// Constructs a new `PolyeqConfig`, with all options set to `false`.
    pub fn new() -> Self {
        Self::default()
    }
}

/// A configurable comparator for polyequality and alpha equivalence.
pub struct Polyeq {
    // In order to check alpha-equivalence, we can't use a simple global cache. For instance, let's
    // say we are comparing the following terms for alpha equivalence:
    // ```
    //     a := (and
    //         (forall ((x Int) (y Int)) (< x y))
    //         (forall ((x Int) (y Int)) (< x y))
    //     )
    //     b := (and
    //         (forall ((x Int) (y Int)) (< x y))
    //         (forall ((y Int) (x Int)) (< x y))
    //     )
    // ```
    // When comparing the first argument of each term, `(forall ((x Int) (y Int)) (< x y))`,
    // `(< x y)` will become `(< $0 $1)` for both `a` and `b`, using De Bruijn indices. We will see
    // that they are equal, and add the entry `((< x y), (< x y))` to the cache. However, when we
    // are comparing the second argument of each term, `(< x y)` will again be `(< $0 $1)` in `a`,
    // but it will be `(< $1 $0)` in `b`. If we just rely on the cache, we will incorrectly
    // determine that `a` and `b` are alpha-equivalent.
    //
    // Modified in Clean: upstream pushed a cache scope at every binder and popped it on leaving,
    // and Clean's fix 10 read only the innermost scope under binders, so an answer found under one
    // binder was found again under its sibling, in time exponential in the depth of shared terms.
    // A pair's answer depends on the comparator's configuration, on whether any variable is bound
    // (identical terms are equal at once only while none is), and on the bindings of the names it
    // reads -- nothing else. Pairs compared with no variable bound are cached in `cache`, and
    // reused wherever none is. A pair compared under a binder is cached in `bound` with the names
    // it read from outside the pair, anchored at the innermost binder level that bound one of
    // them, and is reused while that level is open and none of those names is bound deeper (see
    // `BoundAnswer`): under a sibling binder too, unless it rebinds one of them. Both hold whether
    // each pair compared is equal, not only the pairs found equal.
    cache: HashMap<(Rc<Term>, Rc<Term>), bool>,
    /// Added in Clean: the pairs compared under a binder (alpha-equivalence only), at most
    /// `MAX_ANSWERS` answers each.
    bound: HashMap<(Rc<Term>, Rc<Term>), Held>,
    /// Added in Clean: for each open binder level (0 being none), the pairs in `bound` with an
    /// answer anchored at it, which are dropped as the level closes.
    anchored: Vec<Vec<(Rc<Term>, Rc<Term>)>>,
    /// Added in Clean: the comparisons under a binder in progress, innermost last.
    frames: Vec<Frame>,
    /// Added in Clean: the names each frame has read so far, in frame order.
    reads: Vec<Read>,
    /// Added in Clean: the stamp of the latest comparison under a binder to start (see `Frame`).
    clock: u64,
    /// Added in Clean, for tests: the pairs compared (not answered from the cache).
    #[cfg(test)]
    pub(crate) compared: usize,
    /// Added in Clean, for tests: the answers found under a binder recorded as reading every
    /// binding, past `MAX_READS` names.
    #[cfg(test)]
    pub(crate) answers_reading_all: usize,
    /// Added in Clean, for tests: the comparator's work besides comparing pairs -- the answers
    /// and the reads examined by a lookup, the entries visited as a level closes, and the slots
    /// of the tables an answer-dropping reset frees.
    #[cfg(test)]
    pub(crate) work: usize,
    is_mod_reordering: bool,
    de_bruijn_map: Option<DeBruijnMap>,
    is_mod_nary: bool,
    is_mod_string_concat: bool,

    current_depth: usize,
    max_depth: usize,
}

/// Added in Clean: the most names a comparison under a binder records reading. One that reads more
/// is cached as reading every binding (`BoundAnswer::reads` is `None`).
const MAX_READS: usize = 16;

/// Added in Clean: the most answers kept for one pair compared under binders. A pair whose
/// comparison reads a name rebound at every level gets a new answer at each level, all of them
/// kept while their levels are open, and a lookup examines the answers of its pair: past this many,
/// the one anchored outermost is dropped, which only costs comparing the pair again if it is
/// needed. A lookup so examines at most `MAX_ANSWERS` answers of at most `MAX_READS` reads.
const MAX_ANSWERS: usize = 4;

/// Added in Clean: which of the two terms being compared a name is read for. A rule of the
/// comparison may put a subterm of either term on either side (`compare_chainable`, the singleton
/// case of n-ary operators), so a side is a position in the comparison, as in the De Bruijn map.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Side {
    Left = 0,
    Right = 1,
}

/// Added in Clean: a name read on one side, by its number in the De Bruijn map.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Read {
    side: Side,
    name: u32,
}

/// Added in Clean: whether a pair compared under a binder is equal, and what that answer was found
/// from: the binder level it is anchored at, the names it read from outside the pair (by side and
/// number, innermost binding first), or `None` if it read more than `MAX_READS`, and its stamp.
///
/// Invariant: `equal` is what comparing the pair would answer whenever it is reused, that is at
/// any moment at which some variable is bound, level `level` is open, every name bound has a
/// lateness below `stamp` (`DeBruijnMap::late`), and
/// - with `reads` some, none of its names is bound at a level deeper than `level`;
/// - with `reads` none, no level deeper than `level` is open.
///
/// Why. Comparing a pair is a function of the two terms, the comparator's configuration (set when
/// it is built), whether some variable is bound (identical terms are equal at once only while none
/// is; under a binder one stays bound), the answers its cache gives, and the bindings of the names
/// it looks up. A name it looks up is bound by a binder inside the pair or read from outside it.
/// Inside, the comparison makes the bindings itself, at the next indices of the counter, which
/// exceed every index bound outside; indices are only compared for equality, so these compare
/// alike wherever the pair is compared. A name read from outside either had been bound before,
/// and so has a number, and is recorded in `reads`, together with those recorded by the answers
/// its cache gave; or had never been bound, and so was free, and is not recorded. Such a read
/// stamps the name with the clock, the stamp of the latest comparison under a binder to start,
/// and the name's lateness is that stamp when it is first bound (`DeBruijnMap::lookup` and
/// `insert`). An answer's stamp is its comparison's, lowered to that of every answer its cache
/// gave and of every comparison inside it; a comparison started no later than any read it made,
/// so a name read free by the comparison or by one it relied on has a lateness at least `stamp`
/// if it is bound now. So under the conditions above none of those names is bound, as then. An
/// answer is dropped as its level closes, and a closed level never opens again, so while it is
/// kept the scopes up to `level` are those it was found in, and each name recorded is bound in
/// those scopes, as it was, or in none, as it was. So every lookup the comparison makes, and every
/// answer its cache gives, is what it was, and so is the answer. With `reads` none, every binding
/// is as it was: no deeper level is open, and the levels up to `level` were open, with their
/// bindings, when the comparison started.
struct BoundAnswer {
    level: usize,
    reads: Option<Box<[Read]>>,
    stamp: u64,
    equal: bool,
}

/// Added in Clean: the answers held for one pair compared under binders, at most `MAX_ANSWERS`.
/// Most pairs hold one, which is kept in the table, not in a vector of its own.
enum Held {
    One(BoundAnswer),
    Many(Vec<BoundAnswer>),
}

impl Held {
    fn answers(&self) -> &[BoundAnswer] {
        match self {
            Held::One(answer) => std::slice::from_ref(answer),
            Held::Many(answers) => answers,
        }
    }

    /// Adds `answer`; past `MAX_ANSWERS`, drops the one anchored outermost.
    fn push(&mut self, answer: BoundAnswer) {
        match self {
            Held::Many(answers) => {
                if answers.len() == MAX_ANSWERS {
                    let outermost = (0..answers.len()).min_by_key(|&i| answers[i].level);
                    answers.remove(outermost.unwrap_or(0));
                }
                answers.push(answer);
            }
            Held::One(_) => {
                let Held::One(first) = std::mem::replace(self, Held::Many(Vec::new())) else {
                    unreachable!("matched above");
                };
                *self = Held::Many(vec![first, answer]);
            }
        }
    }

    /// Drops the answers anchored at `level`; and whether none is left.
    fn drop_level(&mut self, level: usize) -> bool {
        match self {
            Held::One(answer) => answer.level == level,
            Held::Many(answers) => {
                answers.retain(|answer| answer.level != level);
                answers.is_empty()
            }
        }
    }
}

/// Added in Clean: a comparison of a pair in progress with some variable bound.
struct Frame {
    /// The binder levels open when it started.
    depth: usize,
    /// Where its reads start in `Polyeq::reads`.
    start: usize,
    /// The clock when it started, lowered to the stamp of each answer it is given and of each
    /// comparison inside it (see `BoundAnswer`).
    stamp: u64,
    /// Whether it read more names than it can record (see `MAX_READS`).
    unknown: bool,
}

impl Default for Polyeq {
    fn default() -> Self {
        Self::new()
    }
}

impl Polyeq {
    /// Constructs a new `Polyeq` with the default configuration.
    pub fn new() -> Self {
        Self::with_config(PolyeqConfig::new())
    }

    /// Constructs a new `Polyeq` with the provided configuration.
    pub fn with_config(config: PolyeqConfig) -> Self {
        Self {
            cache: HashMap::new(),
            bound: HashMap::new(),
            anchored: vec![Vec::new()],
            frames: Vec::new(),
            reads: Vec::new(),
            clock: 0,
            #[cfg(test)]
            compared: 0,
            #[cfg(test)]
            answers_reading_all: 0,
            #[cfg(test)]
            work: 0,
            is_mod_reordering: config.is_mod_reordering,
            de_bruijn_map: config.is_alpha_equivalence.then(DeBruijnMap::new),
            is_mod_nary: config.is_mod_nary,
            is_mod_string_concat: config.is_mod_string_concat,
            current_depth: 0,
            max_depth: 0,
        }
    }

    // Modified in Clean: each builder drops the answers held, which were found under the old
    // configuration (and, for `alpha_equiv`, name the old map's numbers). Every builder chain in
    // Carcara and Clean runs before the first comparison, where there is nothing to drop.

    /// Controls whether to compare terms modulo the reordering of equalities.
    pub fn mod_reordering(mut self, value: bool) -> Self {
        self.is_mod_reordering = value;
        self.forget_answers();
        self
    }

    /// Controls whether to compare terms for alpha equivalence.
    pub fn alpha_equiv(mut self, value: bool) -> Self {
        self.de_bruijn_map = value.then(DeBruijnMap::new);
        self.forget_answers();
        self
    }

    /// Controls whether to compare terms modulo the expansion of n-ary operators.
    pub fn mod_nary(mut self, value: bool) -> Self {
        self.is_mod_nary = value;
        self.forget_answers();
        self
    }

    /// Controls whether to compare terms modulo the concatenation of string constants.
    pub fn mod_string_concat(mut self, value: bool) -> Self {
        self.is_mod_string_concat = value;
        self.forget_answers();
        self
    }

    /// Compares two `[PolyeqComparable]` objects, and returns `true` if they are equivalent.
    pub fn eq<T>(&mut self, a: &T, b: &T) -> bool
    where
        T: PolyeqComparable + ?Sized,
    {
        PolyeqComparable::eq(self, a, b)
    }

    /// Compares two `[PolyeqComparable]` objects, and returns `true` if they are equivalent.
    /// Additionally, records how long the comparison took, and adds that time to the given `time`
    /// argument.
    pub fn eq_with_time<T>(&mut self, a: &T, b: &T, time: &mut Duration) -> bool
    where
        T: PolyeqComparable + ?Sized,
    {
        let start = Instant::now();
        let result = self.eq(a, b);
        *time += start.elapsed();
        result
    }

    /// The maximum term depth this `Polyeq` reached when performing a comparison.
    pub fn max_depth(&self) -> usize {
        self.max_depth
    }

    /// Added in Clean: the pairs of terms this `Polyeq` has decided and holds, for tests.
    #[cfg(test)]
    pub(crate) fn decided(&self) -> usize {
        self.cache.len() + self.decided_under_binders()
    }

    /// Added in Clean: the pairs of terms this `Polyeq` has decided under a binder and holds, for
    /// tests.
    #[cfg(test)]
    pub(crate) fn decided_under_binders(&self) -> usize {
        self.bound.values().map(|held| held.answers().len()).sum()
    }

    /// Added in Clean: the answer cached for `pair`, if one holds here (see `BoundAnswer`). An
    /// answer found under a binder that is reused passes on the names it read to the comparison in
    /// progress, as if that comparison had read them itself.
    fn cached(&mut self, pair: &(Rc<Term>, Rc<Term>), possibly_renamed: bool) -> Option<bool> {
        if !possibly_renamed {
            return self.cache.get(pair).copied();
        }
        let map = self.de_bruijn_map.as_ref()?;
        let answers = self.bound.get(pair)?.answers();
        let (depth, late) = (map.depth(), map.late());
        #[cfg(test)]
        let work = std::cell::Cell::new(0);
        let answer = answers.iter().find(|answer| {
            #[cfg(test)]
            work.set(work.get() + 1);
            late < answer.stamp
                && match &answer.reads {
                    Some(reads) => reads.iter().all(|&read| {
                        #[cfg(test)]
                        work.set(work.get() + 1);
                        map.level(read).is_none_or(|level| level <= answer.level)
                    }),
                    None => answer.level == depth,
                }
        });
        #[cfg(test)]
        {
            self.work += work.get();
        }
        let answer = answer?;
        let equal = answer.equal;
        if let Some(frame) = self.frames.last_mut() {
            frame.stamp = frame.stamp.min(answer.stamp);
            match &answer.reads {
                Some(reads) if !frame.unknown => {
                    let outer = |read: &&Read| map.level(**read).is_none_or(|l| l <= frame.depth);
                    self.reads.extend(reads.iter().filter(outer));
                }
                _ => frame.unknown = true,
            }
        }
        self.bound_reads();
        Some(equal)
    }

    /// Added in Clean: starts the comparison of a pair with some variable bound.
    fn open_frame(&mut self) {
        let depth = self.de_bruijn_map.as_ref().map_or(0, DeBruijnMap::depth);
        self.clock += 1;
        let (start, stamp) = (self.reads.len(), self.clock);
        self.frames
            .push(Frame { depth, start, stamp, unknown: false });
    }

    /// Added in Clean: records `pair`'s answer, found by the comparison in the innermost frame,
    /// which ends here, and passes on the names it read from outside, and its stamp, to the frame
    /// around it.
    fn close_frame(&mut self, pair: (Rc<Term>, Rc<Term>), equal: bool) {
        let Some(frame) = self.frames.pop() else {
            return;
        };
        let Some(map) = self.de_bruijn_map.as_ref() else {
            return;
        };
        let read = dedup(&mut self.reads, frame.start);
        let unknown = frame.unknown || read > MAX_READS;
        let reads = &mut self.reads[frame.start..];
        if !crate::checker::deadline::expired() {
            let (level, reads) = if unknown {
                #[cfg(test)]
                {
                    self.answers_reading_all += 1;
                }
                (frame.depth, None)
            } else {
                // The name bound innermost first: a later binder that makes the answer stale most
                // often rebinds it.
                let innermost = (0..reads.len()).max_by_key(|&i| map.level(reads[i]));
                if let Some(i) = innermost {
                    reads.swap(0, i);
                }
                let level = reads.first().and_then(|&read| map.level(read));
                (level.unwrap_or(0), Some((&*reads).into()))
            };
            let answer = BoundAnswer {
                level,
                reads,
                stamp: frame.stamp,
                equal,
            };
            match self.bound.entry(pair.clone()) {
                Entry::Vacant(entry) => {
                    entry.insert(Held::One(answer));
                }
                Entry::Occupied(mut entry) => entry.get_mut().push(answer),
            }
            self.anchored[level].push(pair);
        }
        let Some(outer) = self.frames.last_mut() else {
            self.reads.truncate(frame.start);
            return;
        };
        outer.stamp = outer.stamp.min(frame.stamp);
        if !unknown && !outer.unknown {
            // Keep the names read from outside the frame around, in place.
            let mut kept = frame.start;
            for i in frame.start..self.reads.len() {
                let read = self.reads[i];
                if map.level(read).is_none_or(|level| level <= outer.depth) {
                    self.reads[kept] = read;
                    kept += 1;
                }
            }
            self.reads.truncate(kept);
            self.bound_reads();
        } else {
            outer.unknown = true;
            self.reads.truncate(frame.start);
        }
    }

    /// Added in Clean: keeps the innermost frame's reads within twice `MAX_READS`, removing
    /// repeats; a frame that read more names than `MAX_READS` stops recording them.
    fn bound_reads(&mut self) {
        let Some(frame) = self.frames.last_mut() else {
            return;
        };
        if frame.unknown {
            self.reads.truncate(frame.start);
        } else if self.reads.len() - frame.start > 2 * MAX_READS
            && dedup(&mut self.reads, frame.start) > MAX_READS
        {
            frame.unknown = true;
            self.reads.truncate(frame.start);
        }
    }

    /// Added in Clean: compares two variables by the De Bruijn map, recording the names read from
    /// outside the comparison in progress.
    fn compare_vars(&mut self, a: &str, b: &str) -> bool {
        let Some(map) = self.de_bruijn_map.as_mut() else {
            return a == b;
        };
        // A name never bound is free: it is not recorded, but stamped with the clock, if a
        // comparison under a binder is in progress (see `BoundAnswer`).
        let clock = (!self.frames.is_empty()).then_some(self.clock);
        let (a_read, a_binding) = map.lookup(Side::Left, a, clock);
        let (b_read, b_binding) = map.lookup(Side::Right, b, clock);
        if let Some(frame) = self.frames.last() {
            if !frame.unknown {
                for (read, binding) in [(a_read, a_binding), (b_read, b_binding)] {
                    let outer = binding.is_none_or(|(level, _)| level <= frame.depth);
                    if let (Some(read), true) = (read, outer) {
                        self.reads.push(read);
                    }
                }
                self.bound_reads();
            }
        }
        match (a_binding, b_binding) {
            // If both a and b are free variables, they need to have the same name
            (None, None) => a == b,

            // If they are both bound variables, they need to have the same De Bruijn indices
            (Some((_, a)), Some((_, b))) => a == b,

            // If one of them is bound and the other is free, they are not equal
            _ => false,
        }
    }

    /// Added in Clean: opens a binder level.
    fn enter_binder(&mut self) {
        if let Some(map) = self.de_bruijn_map.as_mut() {
            map.push();
        }
        self.anchored.push(Vec::new());
    }

    /// Added in Clean: binds `a` on the left and `b` on the right at the next index. A name bound
    /// for the first time is numbered here, with no pass over the terms: one read free before is
    /// covered by its lateness (see `BoundAnswer`), and nothing held is dropped.
    fn bind(&mut self, a: &str, b: &str) {
        if let Some(map) = self.de_bruijn_map.as_mut() {
            map.insert(a, b);
        }
    }

    /// Added in Clean: closes the innermost binder level, dropping the answers anchored at it.
    fn leave_binder(&mut self) {
        let level = self.anchored.len() - 1;
        for pair in self.anchored.pop().unwrap_or_default() {
            #[cfg(test)]
            {
                self.work += 1;
            }
            if self
                .bound
                .get_mut(&pair)
                .is_some_and(|held| held.drop_level(level))
            {
                self.bound.remove(&pair);
            }
        }
        if let Some(map) = self.de_bruijn_map.as_mut() {
            map.pop();
        }
    }

    /// Added in Clean: drops every answer held. The tables are replaced, not cleared: clearing
    /// keeps a table's capacity, and costs it, every time.
    fn forget_answers(&mut self) {
        #[cfg(test)]
        {
            self.work += self.cache.capacity() + self.bound.capacity();
            self.work += self.anchored.iter().map(Vec::capacity).sum::<usize>();
        }
        drop(std::mem::take(&mut self.cache));
        drop(std::mem::take(&mut self.bound));
        for pairs in &mut self.anchored {
            drop(std::mem::take(pairs));
        }
    }

    fn compare_binder<V: PolyeqComparable>(
        &mut self,
        a_binds: &BindingList<V>,
        b_binds: &BindingList<V>,
        a_inner: &Rc<Term>,
        b_inner: &Rc<Term>,
    ) -> bool {
        // Modified in Clean: two binders are only alpha-equivalent if they bind the *same number*
        // of variables. `zip` silently stopped at the shorter list, so
        // `(forall ((x Bool)) (or x y))` compared equal to `(forall ((x Bool) (y Bool)) (or x y))`
        // and `refl` proved them equal (see third-party/carcara/DOWNSTREAM.md).
        if a_binds.len() != b_binds.len() {
            return false;
        }

        if self.de_bruijn_map.is_some() {
            // Modified in Clean: the values of a `let` binding list are evaluated in the *enclosing*
            // scope — SMT-LIB `let` binds in parallel — so every value is compared before any of
            // this list's variables enters the De Bruijn map. Inserting as we went made
            // `(let ((x 1) (y x)) y)` equal to `(let ((z 1) (y z)) y)`, where the two `x`/`z` in
            // the second value are the *outer* variables of those names (fix 25). The values are
            // also compared before this binder's level is opened (fix 34; a *cache* scope was
            // pushed there): an equality found for a value holds in the enclosing scope, and
            // caching it in the binder's own scope let the body reuse it after this binder had
            // rebound one of its names, so
            // `(let ((u p)) (let ((u (not u)) (w u)) (or u w)))` compared equal to
            // `(let ((v p)) (let ((z (not v)) (w v)) (or v w)))` through a cached `(u, v)` (see
            // third-party/carcara/DOWNSTREAM.md). For a quantifier the values are sorts, which
            // cannot mention a bound variable, so this ordering does not change those comparisons.
            for (a_var, b_var) in a_binds.iter().zip(b_binds.iter()) {
                if !self.eq(&a_var.1, &b_var.1) {
                    return false;
                }
            }

            // Then we push a new scope into the De Bruijn map, and insert each variable of the
            // binding lists into it. Modified in Clean: the cache has no scopes; an answer found
            // in here is kept with the names it read (see `BoundAnswer`).
            self.enter_binder();
            for (a_var, b_var) in a_binds.iter().zip(b_binds.iter()) {
                self.bind(&a_var.0, &b_var.0);
            }
            let result = self.eq(a_inner, b_inner);

            // Finally, we pop the scope we pushed
            self.leave_binder();

            result
        } else {
            self.eq(a_binds, b_binds) && self.eq(a_inner, b_inner)
        }
    }

    fn compare_op(
        &mut self,
        op_a: Operator,
        args_a: &[Rc<Term>],
        op_b: Operator,
        args_b: &[Rc<Term>],
    ) -> bool {
        // Modulo string concatenation
        if self.is_mod_string_concat {
            let concat_args_a: Vec<Concat> = to_concat(args_a);
            let concat_args_b: Vec<Concat> = to_concat(args_b);
            return self.compare_strings(concat_args_a, concat_args_b);
        }

        // Modulo reordering of equalities
        if self.is_mod_reordering {
            if let (Operator::Equals, [a_1, a_2], Operator::Equals, [b_1, b_2]) =
                (op_a, args_a, op_b, args_b)
            {
                // If the term is an equality of two terms, we also check if they would be
                // equal if one of them was flipped
                return self.eq(&(a_1, a_2), &(b_1, b_2)) || self.eq(&(a_1, a_2), &(b_2, b_1));
            }
        }

        // Modulo n-ary expansion
        if self.is_mod_nary {
            if op_a != op_b {
                // TODO: check pairwise case
                return if op_a.nary_case() == Some(NaryCase::Chainable) {
                    op_b == Operator::And && self.compare_chainable(op_a, args_a, args_b)
                } else if op_b.nary_case() == Some(NaryCase::Chainable) {
                    op_a == Operator::And && self.compare_chainable(op_b, args_b, args_a)
                } else {
                    false
                };
            } else if args_a.len() != args_b.len() {
                let case = op_a.nary_case();
                return matches!(case, Some(NaryCase::RightAssoc | NaryCase::LeftAssoc))
                    && self.compare_assoc(op_a, args_a, args_b);
            };
        }

        // General case
        op_a == op_b && self.eq(args_a, args_b)
    }

    fn compare_chainable(&mut self, op: Operator, args: &[Rc<Term>], chain: &[Rc<Term>]) -> bool {
        if args.len() != chain.len() + 1 {
            return false;
        }
        args.windows(2)
            .zip(chain.iter())
            .all(|(window, chain_term)| {
                let (a, b) = (&window[0], &window[1]);
                match chain_term.as_ref() {
                    Term::Op(chain_op, args) if *chain_op == op && args.len() == 2 => {
                        self.eq(a, &args[0]) && self.eq(b, &args[1])
                    }
                    _ => false,
                }
            })
    }

    fn compare_assoc(&mut self, op: Operator, left: &[Rc<Term>], right: &[Rc<Term>]) -> bool {
        fn split(args: &[Rc<Term>], is_right: bool) -> (&Rc<Term>, &[Rc<Term>]) {
            match args {
                [] | [_] => unreachable!(),
                [first, rest @ ..] if is_right => (first, rest),
                [rest @ .., last] => (last, rest),
            }
        }

        fn flatten_if_singleton(tail: &[Rc<Term>], op: Operator) -> Option<&[Rc<Term>]> {
            let [term] = tail else {
                return None;
            };
            let (term_op, args) = term.as_op()?;
            // Modified in Clean: a unary `-` is negation, not the one-argument form of `-`.
            if term_op == op && !(op == Operator::Sub && args.len() == 1) {
                Some(args)
            } else {
                None
            }
        }

        match (left.len(), right.len()) {
            (1, 1) => return self.eq(&left[0], &right[0]),
            (1, _) | (_, 1) => return false,
            _ => (),
        }

        let is_right = op.nary_case() == Some(NaryCase::RightAssoc);

        let (left_head, mut left_tail) = split(left, is_right);
        let (right_head, mut right_tail) = split(right, is_right);

        if !self.eq(left_head, right_head) {
            return false;
        }

        left_tail = flatten_if_singleton(left_tail, op).unwrap_or(left_tail);
        right_tail = flatten_if_singleton(right_tail, op).unwrap_or(right_tail);

        self.compare_assoc(op, left_tail, right_tail)
    }

    fn remainder(&mut self, a: Vec<Concat>, b: Vec<Concat>) -> (Vec<Concat>, Vec<Concat>) {
        match (a.first(), b.first()) {
            (None | Some(_), None) | (None, Some(_)) => (a, b),
            (Some(a_head), Some(b_head)) => match (a_head, b_head) {
                (Concat::Constant(a_constant), Concat::Constant(b_constant)) => {
                    let prefix_length = std::cmp::min(a_constant.len(), b_constant.len());
                    for i in 0..prefix_length {
                        if a_constant.chars().nth(i).unwrap() != b_constant.chars().nth(i).unwrap()
                        {
                            return (a, b);
                        }
                    }
                    let a_const_rem = &a_constant[prefix_length..];
                    let b_const_rem = &b_constant[prefix_length..];
                    let mut new_a = a[1..].to_vec();
                    let mut new_b = b[1..].to_vec();
                    if !a_const_rem.is_empty() {
                        new_a.insert(0, Concat::Constant(a_const_rem.to_owned()));
                    }
                    if !b_const_rem.is_empty() {
                        new_b.insert(0, Concat::Constant(b_const_rem.to_owned()));
                    }
                    self.remainder(new_a, new_b)
                }
                (Concat::Constant(constant), Concat::Term(term)) => match term.as_ref() {
                    Term::Op(Operator::StrConcat, args) => {
                        let concat_args: Vec<Concat> = to_concat(args);
                        let (constant_rem, concat_rem) = self.remainder(a.clone(), concat_args);
                        let mut new_b = b[1..].to_vec();
                        for c in concat_rem.iter().rev() {
                            new_b.insert(0, c.clone());
                        }
                        self.remainder(constant_rem, new_b)
                    }
                    _ => {
                        if constant.is_empty() {
                            return self.remainder(a[1..].to_vec(), b);
                        }
                        (a, b)
                    }
                },
                (Concat::Term(term), Concat::Constant(constant)) => match term.as_ref() {
                    Term::Op(Operator::StrConcat, args) => {
                        let concat_args: Vec<Concat> = to_concat(args);
                        let (concat_rem, constant_rem) = self.remainder(concat_args, b.clone());
                        let mut new_a = a[1..].to_vec();
                        for c in concat_rem.iter().rev() {
                            new_a.insert(0, c.clone());
                        }
                        self.remainder(new_a, constant_rem)
                    }
                    _ => {
                        if constant.is_empty() {
                            return self.remainder(a, b[1..].to_vec());
                        }
                        (a, b)
                    }
                },
                (Concat::Term(a_term), Concat::Term(b_term)) => {
                    match (a_term.as_ref(), b_term.as_ref()) {
                        (
                            Term::Op(Operator::StrConcat, a_args),
                            Term::Op(Operator::StrConcat, b_args),
                        ) => {
                            let concat_a_args: Vec<Concat> = to_concat(a_args);
                            let concat_b_args: Vec<Concat> = to_concat(b_args);
                            let (concat_a_rem, concat_b_rem) =
                                self.remainder(concat_a_args, concat_b_args);
                            let mut new_a = a[1..].to_vec();
                            let mut new_b = b[1..].to_vec();
                            for c in concat_a_rem.iter().rev() {
                                new_a.insert(0, c.clone());
                            }
                            for c in concat_b_rem.iter().rev() {
                                new_b.insert(0, c.clone());
                            }
                            self.remainder(new_a, new_b)
                        }
                        (Term::Op(Operator::StrConcat, a_args), _) => {
                            if self.eq(&a_args[0], b_term) {
                                let concat_a_rem: Vec<Concat> = to_concat(&a_args[1..]);
                                let mut new_a = a[1..].to_vec();
                                for c in concat_a_rem.iter().rev() {
                                    new_a.insert(0, c.clone());
                                }
                                let new_b = b[1..].to_vec();
                                self.remainder(new_a, new_b)
                            } else {
                                (a, b)
                            }
                        }
                        (_, Term::Op(Operator::StrConcat, b_args)) => {
                            if self.eq(&b_args[0], a_term) {
                                let new_a = a[1..].to_vec();
                                let concat_b_rem: Vec<Concat> = to_concat(&b_args[1..]);
                                let mut new_b = b[1..].to_vec();
                                for c in concat_b_rem.iter().rev() {
                                    new_b.insert(0, c.clone());
                                }
                                self.remainder(new_a, new_b)
                            } else {
                                (a, b)
                            }
                        }
                        _ => {
                            if self.eq(a_term, b_term) {
                                let new_a = a[1..].to_vec();
                                let new_b = b[1..].to_vec();
                                self.remainder(new_a, new_b)
                            } else {
                                (a, b)
                            }
                        }
                    }
                }
            },
        }
    }

    fn compare_strings(&mut self, a: Vec<Concat>, b: Vec<Concat>) -> bool {
        matches!(self.remainder(a, b), (rem_a, rem_b) if rem_a.is_empty() && rem_b.is_empty())
    }
}

impl PolyeqComparable for Rc<Term> {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        // In general, if the two `Rc`s are directly equal, we can return `true`.
        //
        // However, if we are checking for alpha-equivalence, identical terms may be considered
        // different if the bound variables in them have different meanings. For example, in the
        // terms `(forall ((x Int) (y Int)) (< x y))` and `(forall ((y Int) (x Int)) (< x y))`,
        // even though both instances of `(< x y)` are identical, they are not alpha-equivalent.
        //
        // To account for that, if we are checking for alpha-equivalence and have encountered at
        // least one binder, we don't apply this optimization
        let possibly_renamed = comp.de_bruijn_map.as_ref().is_some_and(|m| !m.is_empty());
        if !possibly_renamed && a == b {
            return true;
        }
        // Added in Clean: a constant reads no name, so it equals itself under any binder; holding
        // that answer for every constant compared under one costs as much as the rest.
        if a == b && matches!(a.as_ref(), Term::Const(_)) {
            return true;
        }

        // We first check the cache to see if these terms were already compared.
        //
        // Modified in Clean: when checking alpha-equivalence inside a binder, an answer found
        // elsewhere may not hold here, because a binder can rebind a name the pair reads: `(= y 1)`
        // and `(= 1 y)` are equal outside, but not under `(forall ((y Int)) ...)` on one side
        // only. An answer found under a binder is reused only where every name it read is bound
        // as it was then, and one found with no variable bound only where none is (see
        // `BoundAnswer` and third-party/carcara/DOWNSTREAM.md). Upstream reused under a binder only
        // what was found under the same binder, so an answer was found again under its sibling:
        // two shared chains `a_i = (and (forall ((x Int)) a_(i-1)) (forall ((y Int)) a_(i-1)))`
        // 26 deep, named apart, took 55 s, doubling with each level.
        //
        // Modified in Clean: a pair found unequal is cached too, under the same rule. Caching only
        // equalities, the comparison was exponential in the depth of shared terms: each equality
        // is tried in both orientations, so a sub-pair that fails was compared again on every
        // path to it (two shared chains `E_i = (= E_(i-1) E_(i-1))` 26 deep took 1.8 s, doubling
        // with each level).
        let pair = (a.clone(), b.clone());
        if let Some(equal) = comp.cached(&pair, possibly_renamed) {
            return equal;
        }

        // Added in Clean: a comparison polls the deadline of the check it runs in, and stops once
        // it has passed; the checker then refuses the command whatever this answered (see
        // checker/deadline.rs). An answer given past the deadline is not cached.
        if crate::checker::deadline::expired() {
            return false;
        }

        #[cfg(test)]
        {
            comp.compared += 1;
        }
        comp.current_depth += 1;
        comp.max_depth = std::cmp::max(comp.max_depth, comp.current_depth);
        if possibly_renamed {
            comp.open_frame();
        }
        let result = comp.eq(a.as_ref(), b.as_ref());
        if possibly_renamed {
            comp.close_frame(pair, result);
        } else if !crate::checker::deadline::expired() {
            comp.cache.insert(pair, result);
        }
        comp.current_depth -= 1;
        result
    }
}

impl PolyeqComparable for Term {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (Term::Const(a1), Term::Const(b1)) => match (a1, b1) {
                (Constant::Real(r1), Constant::Integer(i2)) if r1.is_integer() => {
                    r1.numer().clone() == i2.clone()
                }
                (Constant::Integer(i1), Constant::Real(r2)) if r2.is_integer() => {
                    i1.clone() == r2.numer().clone()
                }
                _ => a == b,
            },
            (Term::Var(a, a_sort), Term::Var(b, b_sort)) if comp.de_bruijn_map.is_some() => {
                // If we are checking for alpha-equivalence, and we encounter two variables, we
                // check that they are equivalent using the De Bruijn map
                comp.compare_vars(a, b) && comp.eq(a_sort, b_sort)
            }
            (Term::App(f_a, args_a), Term::App(f_b, args_b)) => {
                comp.eq(f_a, f_b) && comp.eq(args_a, args_b)
            }
            (
                Term::ParamOp {
                    op: op_a,
                    op_args: op_args_a,
                    args: args_a,
                },
                Term::ParamOp {
                    op: op_b,
                    op_args: op_args_b,
                    args: args_b,
                },
            ) => op_a == op_b && op_args_a == op_args_b && comp.eq(args_a, args_b),
            (Term::AsOp(op_a, sort_a, args_a), Term::AsOp(op_b, sort_b, args_b)) => {
                op_a == op_b && sort_a == sort_b && comp.eq(args_a, args_b)
            }

            // Check the singleton case (op a) = a, where op is left-associative.
            // Modified in Clean: `(- a)` is the negation of `a`, so `-` is excluded (see
            // third-party/carcara/DOWNSTREAM.md).
            (Term::Op(op, args), other) | (other, Term::Op(op, args))
                if comp.is_mod_nary
                    && args.len() == 1
                    && *op != Operator::Sub
                    && op.nary_case() == Some(NaryCase::LeftAssoc)
                    // We have to check with `==` first because we are calling into `comp.eq` with
                    // `&Term`s directly (instead of `Rc<Term>`s), so the `==` check is skipped
                    && (args[0].as_ref() == other || comp.eq(args[0].as_ref(), other)) =>
            {
                true
            }
            (Term::Op(op_a, args_a), Term::Op(op_b, args_b)) => {
                comp.compare_op(*op_a, args_a, *op_b, args_b)
            }
            (Term::Binder(q_a, binds_a, a), Term::Binder(q_b, binds_b, b)) => {
                q_a == q_b && comp.compare_binder(binds_a, binds_b, a, b)
            }
            (Term::Let(binds_a, a), Term::Let(binds_b, b)) => {
                comp.compare_binder(binds_a, binds_b, a, b)
            }
            // Modified in Clean: a division literal is `(/ n d)` with exactly two arguments and a
            // nonzero denominator. The extra arguments of `(/ 3.0 3.0 0.0)` used to be ignored,
            // making it equal to `1.0`; a zero denominator panicked; and the negative case read
            // `(/ n (- d))` as if it were `(/ (- n) d)` (see third-party/carcara/DOWNSTREAM.md).
            (Term::Const(Constant::Real(r)), Term::Op(Operator::RealDiv, args))
            | (Term::Op(Operator::RealDiv, args), Term::Const(Constant::Real(r)))
                if args.len() == 2 =>
            {
                division_literal_value(&args[0], &args[1]).is_some_and(|value| value == *r)
            }
            (Term::Const(Constant::Integer(i1)), Term::Op(Operator::Sub, args))
            | (Term::Op(Operator::Sub, args), Term::Const(Constant::Integer(i1)))
                if i1.is_negative() && args.len() == 1 =>
            {
                if let Term::Const(Constant::Integer(i2)) = args[0].as_ref() {
                    i1.clone().abs() == i2.clone()
                } else if let Term::Const(Constant::Real(r2)) = args[0].as_ref() {
                    i1.clone().abs() == r2.numer().clone()
                } else {
                    false
                }
            }
            (Term::Op(Operator::Sub, args), Term::Const(Constant::Real(r)))
            | (Term::Const(Constant::Real(r)), Term::Op(Operator::Sub, args))
                if r.is_negative() && args.len() == 1 =>
            {
                match args[0].as_ref() {
                    // Modified in Clean: same division-literal checks as above.
                    Term::Op(Operator::RealDiv, sub_args) if sub_args.len() == 2 => {
                        division_literal_value(&sub_args[0], &sub_args[1])
                            .is_some_and(|value| -value == *r)
                    }
                    Term::Const(Constant::Real(r1)) => r1.clone() == r.clone().abs(),
                    _ => false,
                }
            }
            _ => {
                if comp.is_mod_string_concat {
                    return match (a, b) {
                        (
                            Term::Op(Operator::StrConcat, args_a),
                            Term::Const(Constant::String(b)),
                        ) => {
                            let concat_args_a: Vec<Concat> = to_concat(args_a);
                            let concat_args_b = vec![Concat::Constant(b.clone())];
                            comp.compare_strings(concat_args_a, concat_args_b)
                        }
                        (
                            Term::Const(Constant::String(a)),
                            Term::Op(Operator::StrConcat, args_b),
                        ) => {
                            let concat_args_a = vec![Concat::Constant(a.clone())];
                            let concat_args_b: Vec<Concat> = to_concat(args_b);
                            comp.compare_strings(concat_args_a, concat_args_b)
                        }
                        _ => false,
                    };
                }
                false
            }
        }
    }
}

impl<T: PolyeqComparable> PolyeqComparable for BindingList<T> {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(&a.0, &b.0)
    }
}

impl PolyeqComparable for Rc<Sort> {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        a == b || comp.eq(a.as_ref(), b.as_ref())
    }
}

impl PolyeqComparable for Sort {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (Sort::Function(sorts_a), Sort::Function(sorts_b)) => comp.eq(sorts_a, sorts_b),
            (Sort::Atom(a, sorts_a), Sort::Atom(b, sorts_b)) => {
                a == b && comp.eq(sorts_a.as_ref(), sorts_b.as_ref())
            }
            (Sort::Bool, Sort::Bool)
            | (Sort::Int, Sort::Int)
            | (Sort::Real, Sort::Real)
            | (Sort::String, Sort::String)
            | (Sort::RegLan, Sort::RegLan)
            | (Sort::Type, Sort::Type) => true,
            (Sort::Array(x_a, y_a), Sort::Array(x_b, y_b)) => {
                comp.eq(x_a, x_b) && comp.eq(y_a, y_b)
            }
            (Sort::BitVec(a), Sort::BitVec(b)) => a == b,
            (Sort::ParamBitVec, Sort::ParamBitVec) => true,
            _ => false,
        }
    }
}

impl<T: PolyeqComparable> PolyeqComparable for &T {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(*a, *b)
    }
}

impl<T: PolyeqComparable> PolyeqComparable for [T] {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| comp.eq(a, b))
    }
}

impl<T: PolyeqComparable> PolyeqComparable for Vec<T> {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(a.as_slice(), b.as_slice())
    }
}

impl<T: PolyeqComparable, U: PolyeqComparable> PolyeqComparable for (T, U) {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(&a.0, &b.0) && comp.eq(&a.1, &b.1)
    }
}

impl PolyeqComparable for String {
    fn eq(_: &mut Polyeq, a: &Self, b: &Self) -> bool {
        a == b
    }
}

impl PolyeqComparable for AnchorArg {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (AnchorArg::Variable(a), AnchorArg::Variable(b)) => comp.eq(a, b),
            (AnchorArg::Assign(a_name, a_value), AnchorArg::Assign(b_name, b_value)) => {
                a_name == b_name && comp.eq(a_value, b_value)
            }
            _ => false,
        }
    }
}

impl PolyeqComparable for ProofCommand {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (
                ProofCommand::Assume { id: a_id, term: a_term },
                ProofCommand::Assume { id: b_id, term: b_term },
            ) => a_id == b_id && comp.eq(a_term, b_term),
            (ProofCommand::Step(a), ProofCommand::Step(b)) => comp.eq(a, b),
            (ProofCommand::Subproof(a), ProofCommand::Subproof(b)) => comp.eq(a, b),
            _ => false,
        }
    }
}

impl PolyeqComparable for ProofStep {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        a.id == b.id
            && comp.eq(&a.clause, &b.clause)
            && a.rule == b.rule
            && a.premises == b.premises
            && comp.eq(&a.args, &b.args)
            && a.discharge == b.discharge
    }
}

impl PolyeqComparable for Subproof {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(&a.commands, &b.commands) && comp.eq(&a.args, &b.args)
    }
}

struct DeBruijnMap {
    // To check for alpha-equivalence, we make use of De Bruijn indices. The idea is to map each
    // bound variable to an integer depending on the order in which they were bound. As we compare
    // the two terms, if we encounter two bound variables, we need only to check if the associated
    // integers are equal, and the actual names of the variables are irrelevant.
    //
    // Normally, the index selected for a given appearance of a variable is the number of bound
    // variables introduced between that variable and its appearance. That is, the term
    //     `(forall ((x Int)) (and (exists ((y Int)) (> x y)) (> x 5)))`
    // would be represented using De Bruijn indices like this:
    //     `(forall ((x Int)) (and (exists ((y Int)) (> $1 $0)) (> $0 5)))`
    // This has a few annoying properties, like the fact that the same bound variable can receive
    // different indices in different appearances (in the example, `x` appears as both `$0` and
    // `$1`). To simplify the implementation, we revert the order of the indices, such that each
    // variable appearance is assigned the index of the binding of that variable. That is, all
    // appearances of the first bound variable are assigned `$0`, all appearances of the variable
    // that is bound second are assigned `$1`, etc. The given term would then be represented like
    // this:
    //     `(forall ((x Int)) (and (exists ((y Int)) (> $0 $1)) (> $0 5)))`
    //
    // Modified in Clean: upstream kept a map per binder on each side and searched them innermost
    // first, so a variable read under `d` nested binders cost `d` lookups. Each name bound now has
    // a number, and each side keeps, per number, the stack of its bindings, innermost last: a read
    // is one lookup, and leaving a binder undoes the bindings it made. A name is numbered when it is
    // first bound, with no pass over the terms; until then it is free wherever it is read, and a
    // read of it during a comparison under a binder only stamps it, which the cache relies on (see
    // `BoundAnswer`).
    names: HashMap<String, Name>,

    /// For each side and numbered name, its bindings, innermost last: the binder level that made
    /// each, and its index.
    bindings: [Vec<Vec<(usize, usize)>>; 2],

    /// For each numbered name, its lateness: the stamp it had when it was first bound (0 if it was
    /// never read before).
    lateness: Vec<u64>,

    /// For each open binder level, the names it bound, to unbind them as it closes.
    scopes: Vec<Vec<(Side, u32)>>,

    /// Before the first binder level (no level open) and for each open one, the greatest lateness
    /// of a name bound at it or outside it.
    late: Vec<u64>,

    /// How many bindings are in force.
    len: usize,

    // Holds the count of how many variables were bound before each depth
    counter: Vec<usize>,
}

/// Added in Clean: what the De Bruijn map knows of a name.
enum Name {
    /// It has been bound: its number.
    Numbered(u32),
    /// It has never been bound: the clock when it was last read during a comparison under a binder.
    Free(u64),
}

impl DeBruijnMap {
    fn new() -> Self {
        Self {
            names: HashMap::new(),
            bindings: [Vec::new(), Vec::new()],
            lateness: Vec::new(),
            scopes: Vec::new(),
            late: vec![0],
            len: 0,
            counter: vec![0],
        }
    }

    fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The binder levels open.
    fn depth(&self) -> usize {
        self.scopes.len()
    }

    /// The greatest lateness of a name bound now.
    fn late(&self) -> u64 {
        self.late.last().copied().unwrap_or(0)
    }

    fn push(&mut self) {
        self.scopes.push(Vec::new());
        self.late.push(self.late());
        let current = *self.counter.last().unwrap();
        self.counter.push(current);
    }

    fn pop(&mut self) {
        let Some(scope) = self.scopes.pop() else {
            unreachable!("leaving a binder that was not entered");
        };
        for (side, name) in scope {
            self.bindings[side as usize][name as usize].pop();
            self.len -= 1;
        }
        self.late.pop();
        self.counter.pop();
    }

    /// The number of `name`, numbering it if it has none, with the stamp it had as its lateness.
    fn number(&mut self, name: &str) -> u32 {
        let number = self.lateness.len() as u32;
        let lateness = match self.names.get_mut(name) {
            Some(Name::Numbered(number)) => return *number,
            Some(entry) => match std::mem::replace(entry, Name::Numbered(number)) {
                Name::Free(stamp) => stamp,
                Name::Numbered(_) => unreachable!("matched above"),
            },
            None => {
                self.names.insert(name.to_owned(), Name::Numbered(number));
                0
            }
        };
        self.lateness.push(lateness);
        for side in &mut self.bindings {
            side.push(Vec::new());
        }
        number
    }

    /// Binds `a` on the left and `b` on the right at the next index, in the innermost level.
    fn insert(&mut self, a: &str, b: &str) {
        let (a, b) = (self.number(a), self.number(b));
        let level = self.depth();
        let current = self.counter.last_mut().unwrap();
        self.bindings[Side::Left as usize][a as usize].push((level, *current));
        self.bindings[Side::Right as usize][b as usize].push((level, *current));
        *current += 1;
        if let Some(scope) = self.scopes.last_mut() {
            scope.push((Side::Left, a));
            scope.push((Side::Right, b));
        }
        let lateness = self.lateness[a as usize].max(self.lateness[b as usize]);
        if let Some(late) = self.late.last_mut() {
            *late = (*late).max(lateness);
        }
        self.len += 2;
    }

    /// `name`'s number, if it has been bound, and its innermost binding on `side`: the binder
    /// level that made it, and its index. A name never bound is free, and is stamped with `clock`,
    /// if given.
    fn lookup(
        &mut self,
        side: Side,
        name: &str,
        clock: Option<u64>,
    ) -> (Option<Read>, Option<(usize, usize)>) {
        match self.names.get_mut(name) {
            Some(Name::Numbered(number)) => {
                let number = *number;
                let binding = self.bindings[side as usize][number as usize]
                    .last()
                    .copied();
                (Some(Read { side, name: number }), binding)
            }
            Some(Name::Free(stamp)) => {
                if let Some(clock) = clock {
                    *stamp = clock;
                }
                (None, None)
            }
            None => {
                if let Some(clock) = clock {
                    self.names.insert(name.to_owned(), Name::Free(clock));
                }
                (None, None)
            }
        }
    }

    /// The binder level of the innermost binding of a name read, if it is bound.
    fn level(&self, read: Read) -> Option<usize> {
        let bindings = &self.bindings[read.side as usize][read.name as usize];
        bindings.last().map(|&(level, _)| level)
    }
}

/// Added in Clean: sorts the reads from `start` on and removes repeats; and how many are left.
fn dedup(reads: &mut Vec<Read>, start: usize) -> usize {
    let region = &mut reads[start..];
    region.sort_unstable();
    let mut kept = 0;
    for i in 0..region.len() {
        if kept == 0 || region[kept - 1] != region[i] {
            region[kept] = region[i];
            kept += 1;
        }
    }
    reads.truncate(start + kept);
    kept
}
