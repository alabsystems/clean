// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lazily built models: values for free constants, tables for uninterpreted functions and for
//! division by zero, and consistent choice functions.

use crate::datatypes::DtTable;
use crate::regex::Re;
use crate::sort::{ATOM_CARD, S};
use crate::value::{ArrV, DtV, FunV, MAX_MATERIALIZED_BV_WIDTH, V};
use rug::{Integer, Rational};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

/// SplitMix64: small, deterministic, dependency free.
#[derive(Clone)]
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed ^ 0x9E37_79B9_7F4A_7C15)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next_u64() % n as u64) as usize
        }
    }

    pub fn chance(&mut self, percent: u64) -> bool {
        self.next_u64() % 100 < percent
    }

    pub fn pick<'a, T>(&mut self, xs: &'a [T]) -> Option<&'a T> {
        if xs.is_empty() {
            None
        } else {
            Some(&xs[self.below(xs.len())])
        }
    }
}

/// Literal constants that occur in an instance. Domains include them (and their neighbours),
/// so that equalities with constants are actually exercised.
#[derive(Default, Clone, Debug)]
pub struct Vocab {
    pub ints: BTreeSet<Integer>,
    pub reals: BTreeSet<Rational>,
    pub strings: BTreeSet<Vec<u32>>,
}

pub struct Model {
    pub rng: Rng,
    pub vocab: Rc<Vocab>,
    /// Assignments forced by exhaustive enumeration.
    pub fixed: HashMap<(String, S), V>,
    consts: HashMap<(String, S), V>,
    fun_tables: HashMap<(String, S), BTreeMap<Vec<V>, V>>,
    div0: HashMap<(u8, Rational), V>,
    choice: BTreeMap<(S, Vec<V>), V>,
    domains: HashMap<S, (Rc<Vec<V>>, bool)>,
    /// The instance's datatypes. Set it before the first `domain` call.
    pub datatypes: Rc<DtTable>,
}

pub const MAX_FINITE_BV: usize = 5;
/// Datatype values are built up to this constructor nesting depth.
const DT_DEPTH: usize = 2;
/// At most this many values of each non-datatype field sort go into a datatype domain.
const DT_FIELD_SAMPLE: usize = 4;
/// At most this many values in a datatype domain.
const MAX_DT_VALUES: usize = 64;
const MAX_TABLES: usize = 64;

impl Model {
    pub fn new(seed: u64, vocab: Rc<Vocab>) -> Self {
        Model {
            rng: Rng::new(seed),
            vocab,
            fixed: HashMap::new(),
            consts: HashMap::new(),
            fun_tables: HashMap::new(),
            div0: HashMap::new(),
            choice: BTreeMap::new(),
            domains: HashMap::new(),
            datatypes: Rc::new(DtTable::default()),
        }
    }

    /// The sample domain of a sort and whether it is the *complete* carrier.
    pub fn domain(&mut self, s: &S) -> (Rc<Vec<V>>, bool) {
        if let Some(d) = self.domains.get(s) {
            return d.clone();
        }
        let (values, complete) = self.build_domain(s);
        let d = (Rc::new(values), complete);
        self.domains.insert(s.clone(), d.clone());
        d
    }

    fn build_domain(&mut self, s: &S) -> (Vec<V>, bool) {
        match s {
            S::Bool => (vec![V::Bool(false), V::Bool(true)], true),
            S::Bv(w) if *w <= MAX_FINITE_BV => (
                (0..(1u64 << w))
                    .map(|i| V::bv(Integer::from(i), *w))
                    .collect(),
                true,
            ),
            // Wider than the evaluator materializes: sample small values only, each its own residue
            S::Bv(w) if *w > MAX_MATERIALIZED_BV_WIDTH => {
                let mut set = BTreeSet::new();
                for x in [0u64, 1, 2, 3, u64::MAX] {
                    set.insert(V::bv(Integer::from(x), *w));
                }
                for _ in 0..6 {
                    set.insert(V::bv(Integer::from(self.rng.below(1 << 20)), *w));
                }
                (set.into_iter().collect(), false)
            }
            S::Bv(w) => {
                let w = *w;
                let one = Integer::from(1);
                let msb: Integer = one.clone() << (w as u32 - 1);
                let max: Integer = (one.clone() << w as u32) - 1;
                let mut set = BTreeSet::new();
                for x in [
                    Integer::from(0),
                    Integer::from(1),
                    Integer::from(2),
                    Integer::from(3),
                    msb.clone() - 1,
                    msb.clone(),
                    msb + 1,
                    max.clone() - 1,
                    max,
                ] {
                    set.insert(V::bv(x, w));
                }
                for _ in 0..6 {
                    let mut x = Integer::new();
                    for i in 0..w {
                        if self.rng.chance(50) {
                            x.set_bit(i as u32, true);
                        }
                    }
                    set.insert(V::bv(x, w));
                }
                (set.into_iter().collect(), false)
            }
            S::Atom(name) => {
                let name: Rc<str> = Rc::from(name.as_str());
                (
                    (0..ATOM_CARD).map(|i| V::Elem(name.clone(), i)).collect(),
                    true,
                )
            }
            S::Int => {
                let mut set: BTreeSet<Integer> = (-2..=3).map(Integer::from).collect();
                for c in self.vocab.ints.iter().take(12) {
                    set.insert(c.clone() - 1);
                    set.insert(c.clone());
                    set.insert(c.clone() + 1);
                    set.insert(-c.clone());
                }
                for r in self.vocab.reals.iter().take(8) {
                    let f = r.clone().floor().into_numer_denom().0;
                    set.insert(f.clone());
                    set.insert(f + 1);
                }
                (
                    set.into_iter().map(|i| V::Num(Rational::from(i))).collect(),
                    false,
                )
            }
            S::Real => {
                let mut set: BTreeSet<Rational> = (-2..=3).map(Rational::from).collect();
                for (n, d) in [(1, 2), (-1, 2), (1, 3), (-1, 3), (3, 2), (5, 2)] {
                    set.insert(Rational::from((n, d)));
                }
                for c in self.vocab.ints.iter().take(12) {
                    let c = Rational::from(c.clone());
                    set.insert(c.clone());
                    set.insert(c.clone() - Rational::from((1, 2)));
                    set.insert(c.clone() + Rational::from((1, 2)));
                    set.insert(-c);
                }
                for c in self.vocab.reals.iter().take(12) {
                    set.insert(c.clone());
                    set.insert(c.clone() - Rational::from((1, 2)));
                    set.insert(c.clone() + Rational::from((1, 2)));
                    set.insert(-c.clone());
                }
                (set.into_iter().map(V::Num).collect(), false)
            }
            S::Str => {
                let mut set: BTreeSet<Vec<u32>> = ["", "a", "b", "ab", "ba", "aa", "0", "1", "10"]
                    .iter()
                    .map(|s| s.chars().map(|c| c as u32).collect())
                    .collect();
                for s in self.vocab.strings.iter().take(10) {
                    set.insert(s.clone());
                    for k in 0..s.len().min(3) {
                        set.insert(s[..k].to_vec());
                        set.insert(s[s.len() - k..].to_vec());
                    }
                }
                (set.into_iter().map(|s| V::Str(Rc::new(s))).collect(), false)
            }
            S::RegLan => (
                vec![
                    V::Re(Rc::new(Re::None)),
                    V::Re(Rc::new(Re::Eps)),
                    V::Re(Rc::new(Re::all())),
                    V::Re(Rc::new(Re::Lit(vec!['a' as u32]))),
                    V::Re(Rc::new(Re::Star(Box::new(Re::Lit(vec!['a' as u32]))))),
                ],
                false,
            ),
            S::Array(i, e) => {
                let (idom, icomplete) = self.domain(i);
                let (edom, ecomplete) = self.domain(e);
                if edom.is_empty() {
                    return (Vec::new(), false);
                }
                let total = (edom.len() as f64).powi(idom.len() as i32);
                if icomplete && ecomplete && total <= MAX_TABLES as f64 {
                    let tables = all_tables(&idom, &edom);
                    let values = tables
                        .into_iter()
                        .map(|t| {
                            let entries = idom.iter().cloned().zip(t).collect();
                            V::Arr(Rc::new(ArrV::canon(edom[0].clone(), entries, Some(&idom))))
                        })
                        .collect::<BTreeSet<_>>();
                    (values.into_iter().collect(), true)
                } else {
                    let mut set = BTreeSet::new();
                    for _ in 0..6 {
                        set.insert(self.random_array(&idom, icomplete, &edom));
                    }
                    (set.into_iter().collect(), false)
                }
            }
            S::Fun(args, ret) => {
                let mut arg_doms = Vec::new();
                let mut complete = true;
                for a in args {
                    let (d, c) = self.domain(a);
                    complete &= c;
                    arg_doms.push(d);
                }
                let (rdom, rc) = self.domain(ret);
                complete &= rc;
                if rdom.is_empty() {
                    return (Vec::new(), false);
                }
                let points = product(&arg_doms);
                let total = (rdom.len() as f64).powi(points.len() as i32);
                if complete && total <= MAX_TABLES as f64 {
                    let tables = all_tables(&points, &rdom);
                    let values = tables
                        .into_iter()
                        .map(|t| {
                            V::Fun(Rc::new(FunV::Table {
                                map: points.iter().cloned().zip(t).collect(),
                                default: rdom[0].clone(),
                            }))
                        })
                        .collect();
                    (values, true)
                } else {
                    let mut values = Vec::new();
                    for _ in 0..6 {
                        let mut map = BTreeMap::new();
                        for p in points.iter().take(64) {
                            if let Some(v) = self.rng.pick(&rdom) {
                                map.insert(p.clone(), v.clone());
                            }
                        }
                        let default = self.rng.pick(&rdom).cloned().unwrap();
                        values.push(V::Fun(Rc::new(FunV::Table { map, default })));
                    }
                    (values, false)
                }
            }
            S::Dt(name) => {
                let mut complete = true;
                let values = self.dt_values(name, DT_DEPTH, &mut complete);
                let complete = complete && !values.is_empty();
                (values, complete)
            }
            S::Other(_) => (Vec::new(), false),
        }
    }

    /// Values of datatype `name` built from constructors nested at most `depth` deep (a
    /// constructor without datatype fields is at depth 0). `complete` is cleared whenever a value
    /// is left out: a field domain that is sampled or itself incomplete, a recursive field at the
    /// depth bound, or the value cap. A non-recursive datatype over finite fields is complete.
    fn dt_values(&mut self, name: &str, depth: usize, complete: &mut bool) -> Vec<V> {
        let table = self.datatypes.clone();
        let Some(ctors) = table.ctors(name) else {
            *complete = false;
            return Vec::new();
        };
        let datatype: Rc<str> = Rc::from(name);
        let mut out = BTreeSet::new();
        for c in ctors {
            let mut doms = Vec::new();
            for (_, s) in &c.fields {
                let values = match s {
                    S::Dt(_) if depth == 0 => {
                        *complete = false;
                        Vec::new()
                    }
                    S::Dt(d) => self.dt_values(d, depth - 1, complete),
                    other => {
                        let (d, c) = self.domain(other);
                        *complete &= c;
                        if d.len() > DT_FIELD_SAMPLE {
                            *complete = false;
                            let mut picked = BTreeSet::new();
                            for _ in 0..4 * DT_FIELD_SAMPLE {
                                if picked.len() == DT_FIELD_SAMPLE {
                                    break;
                                }
                                if let Some(v) = self.rng.pick(&d) {
                                    picked.insert(v.clone());
                                }
                            }
                            picked.into_iter().collect()
                        } else {
                            d.to_vec()
                        }
                    }
                };
                if values.is_empty() {
                    doms.clear();
                    break;
                }
                doms.push(Rc::new(values));
            }
            if doms.len() != c.fields.len() {
                continue;
            }
            let ctor: Rc<str> = Rc::from(c.name.as_str());
            for fields in product(&doms) {
                if out.len() >= MAX_DT_VALUES {
                    *complete = false;
                    break;
                }
                out.insert(V::Dt(Rc::new(DtV {
                    datatype: datatype.clone(),
                    ctor: ctor.clone(),
                    fields,
                })));
            }
        }
        out.into_iter().collect()
    }

    fn random_array(&mut self, idom: &[V], icomplete: bool, edom: &[V]) -> V {
        let default = self.rng.pick(edom).cloned().unwrap();
        let mut entries = BTreeMap::new();
        let n = if icomplete {
            idom.len()
        } else {
            self.rng.below(3)
        };
        for _ in 0..n {
            if let (Some(i), Some(e)) = (self.rng.pick(idom), self.rng.pick(edom)) {
                entries.insert(i.clone(), e.clone());
            }
        }
        V::Arr(Rc::new(ArrV::canon(
            default,
            entries,
            if icomplete { Some(idom) } else { None },
        )))
    }

    pub fn random_value(&mut self, s: &S) -> Option<V> {
        let (dom, _) = self.domain(s);
        // Bias towards the small, boundary-heavy front of numeric domains.
        let idx = self.rng.below(dom.len());
        dom.get(idx).cloned()
    }

    pub fn const_value(&mut self, name: &str, s: &S) -> Option<V> {
        let key = (name.to_owned(), s.clone());
        if let Some(v) = self.fixed.get(&key) {
            return Some(v.clone());
        }
        if let Some(v) = self.consts.get(&key) {
            return Some(v.clone());
        }
        let v = self.random_value(s)?;
        self.consts.insert(key, v.clone());
        Some(v)
    }

    pub fn apply_symbol(&mut self, name: &str, sort: &S, args: Vec<V>) -> Option<V> {
        if args.iter().any(V::has_fun) {
            return None;
        }
        let S::Fun(_, ret) = sort else { return None };
        let key = (name.to_owned(), sort.clone());
        if let Some(v) = self.fun_tables.get(&key).and_then(|t| t.get(&args)) {
            return Some(v.clone());
        }
        let v = self.random_value(ret)?;
        self.fun_tables
            .entry(key)
            .or_default()
            .insert(args, v.clone());
        Some(v)
    }

    /// The value of `(/ n 0)`, `(div n 0)` or `(mod n 0)`: SMT-LIB leaves these unspecified,
    /// so every model picks them freely (but functionally).
    pub fn div_by_zero(&mut self, kind: u8, numerator: &Rational) -> Option<V> {
        let key = (kind, numerator.clone());
        if let Some(v) = self.div0.get(&key) {
            return Some(v.clone());
        }
        let v = self.random_value(if kind == 0 { &S::Real } else { &S::Int })?;
        self.div0.insert(key, v.clone());
        Some(v)
    }

    /// A choice function that depends only on the (sample) witness set, which makes it a
    /// function of the predicate as required by Hilbert choice.
    pub fn choose(&mut self, sort: &S, witnesses: Vec<V>) -> V {
        let key = (sort.clone(), witnesses);
        if let Some(v) = self.choice.get(&key) {
            return v.clone();
        }
        let v = self.rng.pick(&key.1).cloned().unwrap();
        self.choice.insert(key, v.clone());
        v
    }
}

/// All functions from `points` to `values`, as value vectors aligned with `points`.
fn all_tables<P: Clone>(points: &[P], values: &[V]) -> Vec<Vec<V>> {
    let mut out = vec![Vec::new()];
    for _ in points {
        let mut next = Vec::new();
        for prefix in &out {
            for v in values {
                let mut t = prefix.clone();
                t.push(v.clone());
                next.push(t);
            }
        }
        out = next;
    }
    out
}

/// Cartesian product of argument domains (bounded).
pub fn product(doms: &[Rc<Vec<V>>]) -> Vec<Vec<V>> {
    let mut out = vec![Vec::new()];
    for d in doms {
        let mut next = Vec::new();
        for prefix in &out {
            for v in d.iter() {
                let mut t = prefix.clone();
                t.push(v.clone());
                next.push(t);
                if next.len() > 4096 {
                    break;
                }
            }
        }
        out = next;
    }
    out
}
