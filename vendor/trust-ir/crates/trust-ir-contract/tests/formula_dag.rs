// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `trust_ir_contract::formula_dag`: the hash-consed Formula DAG and its
// sharing printers.
//
//   * round trip tree -> DAG -> tree is the identity, for a witness of EVERY
//     Formula variant (the list is held complete by the serde-derived census)
//     and for random well-sorted formulas with shared subterms;
//   * node identity is exact: two trees get one id iff they are equal (the
//     hash-collision half is the crate's unit tests, which force every hash
//     to collide); an id of another DAG, a clone included, is refused;
//   * the `let` printer and the `define-fun` script printer are the tree
//     printer up to their bindings: expanding the bindings gives the tree
//     text byte for byte, and no binding is ever CAPTURED — one used under a
//     binder opened after it mentions none of the names that binder binds.
//     The random corpus uses one name (`k`) both free and bound and shares
//     its subterms across binders, so the capture check is exercised. The
//     solver-side equivalence check is `trust-ir-ay/tests/formula_dag_ay.rs`;
//   * the node count is linear on shared inputs; the printed size and the
//     printer's work counters (`PrintStats`) are linear on shared, wide,
//     deep and quantified inputs and do not depend on the formula's symbols;
//   * intern / expand / both printers are iterative on chains 10^6 deep.

use std::collections::{HashMap, HashSet};
use trust_ir_contract::formula_census::{formula_variant_names, variant_name, witnesses};
use trust_ir_contract::formula_dag::{DagError, FormulaDag, NodeId, PrintStats, Shell};
use trust_ir_contract::{Formula, RoundingMode, Sort, Symbol};

// ─────────────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────────────

fn bx(f: Formula) -> Box<Formula> {
    Box::new(f)
}

fn var(name: &str, sort: Sort) -> Formula {
    Formula::Var(name.into(), sort)
}

fn int(name: &str) -> Formula {
    var(name, Sort::Int)
}

/// Structural equality without recursion (the derived `PartialEq` recurses
/// once per level and overflows the stack on a 10^6-deep tree).
fn eq_iterative(a: &Formula, b: &Formula) -> bool {
    let mut stack = vec![(a, b)];
    while let Some((a, b)) = stack.pop() {
        if Shell::of(a) != Shell::of(b) {
            return false;
        }
        let (ka, kb) = (a.children(), b.children());
        if ka.len() != kb.len() {
            return false;
        }
        stack.extend(ka.into_iter().zip(kb));
    }
    true
}

/// A deterministic xorshift64* stream.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(self.next() % (n as u64)).unwrap_or(0)
    }
    fn chance(&mut self, num: u64, den: u64) -> bool {
        self.next() % den < num
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum S {
    Bool,
    Int,
    Bv8,
    F32,
    Arr,
    Level,
    Real,
}

fn f32_sort() -> Sort {
    Sort::Float { eb: 8, sb: 24 }
}

fn level_sort() -> Sort {
    Sort::Datatype {
        name: "Level".into(),
        constructors: vec![
            ("zero".into(), vec![]),
            (
                "succ".into(),
                vec![(
                    "pred".into(),
                    Sort::Datatype {
                        name: "Level".into(),
                        constructors: vec![],
                    },
                )],
            ),
        ],
    }
}

/// Random WELL-SORTED formulas over the census witnesses' vocabulary, with
/// shared subterms: a generated subterm is kept in a pool and later drawn
/// again (cloned), so equal subtrees recur within and across formulas — and
/// across binders: the pool is not split by binder, and the Int variable `k`
/// occurs free outside a binder as well as bound by `forall ((k Int))` /
/// `exists ((k Int))`, so one subterm mentioning `k` can mean the free `k`
/// in one place and a bound one in another.
struct Gen {
    rng: Rng,
    pools: HashMap<S, Vec<Formula>>,
}

impl Gen {
    fn new(seed: u64) -> Gen {
        Gen {
            rng: Rng(seed),
            pools: HashMap::new(),
        }
    }

    fn make(&mut self, s: S, depth: u32, bound_k: bool) -> Formula {
        if let Some(pool) = self.pools.get(&s)
            && !pool.is_empty()
            && self.rng.chance(1, 3)
        {
            let i = self.rng.below(pool.len());
            return pool[i].clone();
        }
        let f = if depth == 0 || self.rng.chance(1, 4) {
            self.leaf(s, bound_k)
        } else {
            self.node(s, depth - 1, bound_k)
        };
        self.pools.entry(s).or_default().push(f.clone());
        f
    }

    fn leaf(&mut self, s: S, bound_k: bool) -> Formula {
        let r = self.rng.below(4);
        match s {
            S::Bool => match r {
                0 => Formula::Bool(self.rng.chance(1, 2)),
                1 => var("p", Sort::Bool),
                2 => var("q", Sort::Bool),
                // A small term of both binder variables, so subterms that
                // mention two bound names are common and shared.
                _ if self.rng.chance(1, 2) => Formula::Lt(
                    bx(Formula::SymVar(Symbol::intern("k"), Sort::Int)),
                    bx(Formula::SymVar(Symbol::intern("j"), Sort::Int)),
                ),
                _ => Formula::Pred(Symbol::intern("flag"), vec![]),
            },
            S::Int => match r {
                0 => Formula::Int(i128::from(self.rng.below(7) as i32) - 3),
                1 => Formula::UInt(u128::from(self.rng.below(5) as u32)),
                // `k` or `j`: bound under a binder of them, free outside;
                // `z` is never bound.
                2 if bound_k || self.rng.chance(2, 3) => {
                    Formula::SymVar(Symbol::intern(["k", "j"][self.rng.below(2)]), Sort::Int)
                }
                2 => Formula::SymVar(Symbol::intern("z"), Sort::Int),
                _ => int(["x", "y"][self.rng.below(2)]),
            },
            S::Bv8 => match r {
                0 => Formula::BitVec {
                    value: i128::from(self.rng.below(9) as i32) - 4,
                    width: 8,
                },
                1 => var("a", Sort::BitVec(8)),
                _ => var("b", Sort::BitVec(8)),
            },
            S::F32 => match r {
                0 => Formula::FpConst {
                    bits: 0x3f80_0000,
                    eb: 8,
                    sb: 24,
                },
                1 => Formula::FpZero {
                    neg: self.rng.chance(1, 2),
                    eb: 8,
                    sb: 24,
                },
                2 => Formula::FpInf {
                    neg: self.rng.chance(1, 2),
                    eb: 8,
                    sb: 24,
                },
                _ => var(["fa", "fb", "fc"][self.rng.below(3)], f32_sort()),
            },
            S::Arr => match r {
                0 => Formula::const_array(Sort::Int, Sort::Int, Formula::Int(0)),
                _ => var("arr", Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))),
            },
            S::Level => match r {
                0 => Formula::Ctor {
                    ctor: "zero".into(),
                    args: vec![],
                    sort: level_sort(),
                },
                _ => var("lv", level_sort()),
            },
            S::Real => match r {
                0 => Formula::rat("1", "2").unwrap_or(Formula::rat_from_int(1)),
                1 => Formula::rat_from_int(3),
                _ => var("r", Sort::Real),
            },
        }
    }

    #[allow(clippy::too_many_lines)]
    fn node(&mut self, s: S, d: u32, k: bool) -> Formula {
        let rne = || bx(Formula::FpRoundingMode(RoundingMode::RNE));
        match s {
            S::Bool => match self.rng.below(16) {
                0 => Formula::Not(bx(self.make(S::Bool, d, k))),
                1 => {
                    let n = self.rng.below(4);
                    Formula::And((0..n).map(|_| self.make(S::Bool, d, k)).collect())
                }
                2 => {
                    let n = self.rng.below(4);
                    Formula::Or((0..n).map(|_| self.make(S::Bool, d, k)).collect())
                }
                3 => Formula::Implies(bx(self.make(S::Bool, d, k)), bx(self.make(S::Bool, d, k))),
                4 => {
                    let (a, b) = (self.make(S::Int, d, k), self.make(S::Int, d, k));
                    match self.rng.below(5) {
                        0 => Formula::Eq(bx(a), bx(b)),
                        1 => Formula::Lt(bx(a), bx(b)),
                        2 => Formula::Le(bx(a), bx(b)),
                        3 => Formula::Gt(bx(a), bx(b)),
                        _ => Formula::Ge(bx(a), bx(b)),
                    }
                }
                5 => {
                    let (a, b) = (self.make(S::Bv8, d, k), self.make(S::Bv8, d, k));
                    match self.rng.below(4) {
                        0 => Formula::BvULt(bx(a), bx(b), 8),
                        1 => Formula::BvULe(bx(a), bx(b), 8),
                        2 => Formula::BvSLt(bx(a), bx(b), 8),
                        _ => Formula::BvSLe(bx(a), bx(b), 8),
                    }
                }
                6 => {
                    let (a, b) = (self.make(S::F32, d, k), self.make(S::F32, d, k));
                    match self.rng.below(5) {
                        0 => Formula::FpEq(bx(a), bx(b)),
                        1 => Formula::FpLt(bx(a), bx(b)),
                        2 => Formula::FpLe(bx(a), bx(b)),
                        3 => Formula::FpGt(bx(a), bx(b)),
                        _ => Formula::FpGe(bx(a), bx(b)),
                    }
                }
                7 => {
                    let a = bx(self.make(S::F32, d, k));
                    match self.rng.below(7) {
                        0 => Formula::FpIsNaN(a),
                        1 => Formula::FpIsInfinite(a),
                        2 => Formula::FpIsZero(a),
                        3 => Formula::FpIsNormal(a),
                        4 => Formula::FpIsSubnormal(a),
                        5 => Formula::FpIsNegative(a),
                        _ => Formula::FpIsPositive(a),
                    }
                }
                8 => {
                    // A binder of `k`, of `j`, or of both; its body may
                    // mention either (so a binder can be open in the other,
                    // and a subterm can mention two bound names).
                    let body = bx(self.make(S::Bool, d, true));
                    let bindings = match self.rng.below(3) {
                        0 => vec![(Symbol::intern("k"), Sort::Int)],
                        1 => vec![(Symbol::intern("j"), Sort::Int)],
                        _ => vec![
                            (Symbol::intern("k"), Sort::Int),
                            (Symbol::intern("j"), Sort::Int),
                        ],
                    };
                    if self.rng.chance(1, 2) {
                        Formula::Forall(bindings, body)
                    } else {
                        Formula::Exists(bindings, body)
                    }
                }
                9 => Formula::Pred(Symbol::intern("ready"), vec![self.make(S::Int, d, k)]),
                10 => Formula::IsCtor {
                    datatype: "Level".into(),
                    ctor: "succ".into(),
                    arg: bx(self.make(S::Level, d, k)),
                },
                11 => Formula::Eq(bx(self.make(S::Level, d, k)), bx(self.make(S::Level, d, k))),
                12 => Formula::Le(bx(self.make(S::Real, d, k)), bx(self.make(S::Real, d, k))),
                13 => Formula::Ite(
                    bx(self.make(S::Bool, d, k)),
                    bx(self.make(S::Bool, d, k)),
                    bx(self.make(S::Bool, d, k)),
                ),
                14 => Formula::Eq(bx(self.make(S::Arr, d, k)), bx(self.make(S::Arr, d, k))),
                _ => Formula::Eq(bx(self.make(S::Bv8, d, k)), bx(self.make(S::Bv8, d, k))),
            },
            S::Int => match self.rng.below(12) {
                0 => Formula::Add(bx(self.make(S::Int, d, k)), bx(self.make(S::Int, d, k))),
                1 => Formula::Sub(bx(self.make(S::Int, d, k)), bx(self.make(S::Int, d, k))),
                2 => Formula::Mul(bx(self.make(S::Int, d, k)), bx(self.make(S::Int, d, k))),
                3 => Formula::Div(bx(self.make(S::Int, d, k)), bx(self.make(S::Int, d, k))),
                4 => Formula::Rem(bx(self.make(S::Int, d, k)), bx(self.make(S::Int, d, k))),
                5 => Formula::Neg(bx(self.make(S::Int, d, k))),
                6 => Formula::BvToInt(bx(self.make(S::Bv8, d, k)), 8, self.rng.chance(1, 2)),
                7 => Formula::Ite(
                    bx(self.make(S::Bool, d, k)),
                    bx(self.make(S::Int, d, k)),
                    bx(self.make(S::Int, d, k)),
                ),
                8 => Formula::Select(bx(self.make(S::Arr, d, k)), bx(self.make(S::Int, d, k))),
                9 => Formula::FnApp {
                    func: "f".into(),
                    args: vec![self.make(S::Int, d, k)],
                    sort: Sort::Int,
                },
                10 => Formula::FnApp {
                    func: "c".into(),
                    args: vec![],
                    sort: Sort::Int,
                },
                _ => self.leaf(S::Int, k),
            },
            S::Bv8 => {
                let a = bx(self.make(S::Bv8, d, k));
                match self.rng.below(22) {
                    0 => Formula::BvAdd(a, bx(self.make(S::Bv8, d, k)), 8),
                    1 => Formula::BvSub(a, bx(self.make(S::Bv8, d, k)), 8),
                    2 => Formula::BvMul(a, bx(self.make(S::Bv8, d, k)), 8),
                    3 => Formula::BvUDiv(a, bx(self.make(S::Bv8, d, k)), 8),
                    4 => Formula::BvSDiv(a, bx(self.make(S::Bv8, d, k)), 8),
                    5 => Formula::BvURem(a, bx(self.make(S::Bv8, d, k)), 8),
                    6 => Formula::BvSRem(a, bx(self.make(S::Bv8, d, k)), 8),
                    7 => Formula::BvAnd(a, bx(self.make(S::Bv8, d, k)), 8),
                    8 => Formula::BvOr(a, bx(self.make(S::Bv8, d, k)), 8),
                    9 => Formula::BvXor(a, bx(self.make(S::Bv8, d, k)), 8),
                    10 => Formula::BvNot(a, 8),
                    11 => Formula::BvShl(a, bx(self.make(S::Bv8, d, k)), 8),
                    12 => Formula::BvLShr(a, bx(self.make(S::Bv8, d, k)), 8),
                    13 => Formula::BvAShr(a, bx(self.make(S::Bv8, d, k)), 8),
                    14 => Formula::IntToBv(bx(self.make(S::Int, d, k)), 8),
                    15 => Formula::BvExtract {
                        inner: bx(Formula::BvConcat(a, bx(self.make(S::Bv8, d, k)))),
                        high: 11,
                        low: 4,
                    },
                    16 => Formula::BvZeroExt(
                        bx(Formula::BvExtract {
                            inner: a,
                            high: 3,
                            low: 0,
                        }),
                        4,
                    ),
                    17 => Formula::BvSignExt(
                        bx(Formula::BvExtract {
                            inner: a,
                            high: 6,
                            low: 0,
                        }),
                        1,
                    ),
                    18 => Formula::FpToUbv {
                        rm: rne(),
                        value: bx(self.make(S::F32, d, k)),
                        width: 8,
                        eb: 8,
                        sb: 24,
                    },
                    19 => Formula::FpToSbv {
                        rm: rne(),
                        value: bx(self.make(S::F32, d, k)),
                        width: 8,
                        eb: 8,
                        sb: 24,
                    },
                    20 => Formula::BvExtract {
                        inner: bx(Formula::FpToIeeeBv(bx(self.make(S::F32, d, k)))),
                        high: 7,
                        low: 0,
                    },
                    _ => Formula::Ite(bx(self.make(S::Bool, d, k)), a, bx(self.make(S::Bv8, d, k))),
                }
            }
            S::F32 => {
                let a = bx(self.make(S::F32, d, k));
                match self.rng.below(15) {
                    0 => Formula::FpAdd(rne(), a, bx(self.make(S::F32, d, k))),
                    1 => Formula::FpSub(rne(), a, bx(self.make(S::F32, d, k))),
                    2 => Formula::FpMul(rne(), a, bx(self.make(S::F32, d, k))),
                    3 => Formula::FpDiv(rne(), a, bx(self.make(S::F32, d, k))),
                    4 => Formula::FpFma(
                        rne(),
                        a,
                        bx(self.make(S::F32, d, k)),
                        bx(self.make(S::F32, d, k)),
                    ),
                    5 => Formula::FpSqrt(rne(), a),
                    6 => Formula::FpRem(a, bx(self.make(S::F32, d, k))),
                    7 => Formula::FpNeg(a),
                    8 => Formula::FpAbs(a),
                    9 => Formula::FpMin(a, bx(self.make(S::F32, d, k))),
                    10 => Formula::FpMax(a, bx(self.make(S::F32, d, k))),
                    11 => Formula::FpFromUbv {
                        rm: rne(),
                        value: bx(self.make(S::Bv8, d, k)),
                        eb: 8,
                        sb: 24,
                    },
                    12 => Formula::FpFromSbv {
                        rm: rne(),
                        value: bx(self.make(S::Bv8, d, k)),
                        eb: 8,
                        sb: 24,
                    },
                    13 => Formula::FpConvert {
                        rm: rne(),
                        value: a,
                        eb: 8,
                        sb: 24,
                    },
                    _ => Formula::FpFromBits {
                        bits: bx(Formula::BvConcat(
                            bx(Formula::BvConcat(a_bv(self, d, k), a_bv(self, d, k))),
                            bx(Formula::BvConcat(a_bv(self, d, k), a_bv(self, d, k))),
                        )),
                        eb: 8,
                        sb: 24,
                    },
                }
            }
            S::Arr => match self.rng.below(3) {
                0 => Formula::Store(
                    bx(self.make(S::Arr, d, k)),
                    bx(self.make(S::Int, d, k)),
                    bx(self.make(S::Int, d, k)),
                ),
                1 => Formula::const_array(Sort::Int, Sort::Int, self.make(S::Int, d, k)),
                _ => Formula::Ite(
                    bx(self.make(S::Bool, d, k)),
                    bx(self.make(S::Arr, d, k)),
                    bx(self.make(S::Arr, d, k)),
                ),
            },
            S::Level => match self.rng.below(3) {
                0 => Formula::Ctor {
                    ctor: "succ".into(),
                    args: vec![self.make(S::Level, d, k)],
                    sort: level_sort(),
                },
                1 => Formula::Sel {
                    datatype: "Level".into(),
                    field: "pred".into(),
                    field_sort: level_sort(),
                    arg: bx(self.make(S::Level, d, k)),
                },
                _ => Formula::Ite(
                    bx(self.make(S::Bool, d, k)),
                    bx(self.make(S::Level, d, k)),
                    bx(self.make(S::Level, d, k)),
                ),
            },
            S::Real => match self.rng.below(4) {
                0 => Formula::Add(bx(self.make(S::Real, d, k)), bx(self.make(S::Real, d, k))),
                1 => Formula::Sub(bx(self.make(S::Real, d, k)), bx(self.make(S::Real, d, k))),
                2 => Formula::Neg(bx(self.make(S::Real, d, k))),
                _ => Formula::Ite(
                    bx(self.make(S::Bool, d, k)),
                    bx(self.make(S::Real, d, k)),
                    bx(self.make(S::Real, d, k)),
                ),
            },
        }
    }
}

fn a_bv(g: &mut Gen, d: u32, k: bool) -> Box<Formula> {
    bx(g.make(S::Bv8, d, k))
}

/// Random Bool formulas, some shared with each other.
fn random_corpus(seed: u64, n: usize, depth: u32) -> Vec<Formula> {
    let mut g = Gen::new(seed);
    (0..n).map(|_| g.make(S::Bool, depth, false)).collect()
}

// ── S-expressions: parse, expand the bindings, print ────────────────────────

#[derive(Clone, Debug, PartialEq, Eq)]
enum Sx {
    Atom(String),
    List(Vec<Sx>),
}

fn tokenize(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut chars = text.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            '(' | ')' => {
                out.push(c.to_string());
                chars.next();
            }
            c if c.is_whitespace() => {
                chars.next();
            }
            '|' => {
                let mut tok = String::from('|');
                chars.next();
                while let Some(c) = chars.next() {
                    tok.push(c);
                    if c == '\\' {
                        if let Some(e) = chars.next() {
                            tok.push(e);
                        }
                    } else if c == '|' {
                        break;
                    }
                }
                out.push(tok);
            }
            _ => {
                let mut tok = String::new();
                while let Some(&c) = chars.peek() {
                    if c == '(' || c == ')' || c.is_whitespace() || c == '|' {
                        break;
                    }
                    tok.push(c);
                    chars.next();
                }
                out.push(tok);
            }
        }
    }
    out
}

fn parse(text: &str) -> Vec<Sx> {
    let mut stack: Vec<Vec<Sx>> = vec![Vec::new()];
    for tok in tokenize(text) {
        match tok.as_str() {
            "(" => stack.push(Vec::new()),
            ")" => {
                let list = stack.pop().expect("balanced");
                stack.last_mut().expect("balanced").push(Sx::List(list));
            }
            _ => stack.last_mut().expect("open").push(Sx::Atom(tok)),
        }
    }
    assert_eq!(stack.len(), 1, "unbalanced parentheses in {text}");
    stack.pop().unwrap_or_default()
}

fn print(sx: &Sx, out: &mut String) {
    match sx {
        Sx::Atom(a) => out.push_str(a),
        Sx::List(items) => {
            out.push('(');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                print(item, out);
            }
            out.push(')');
        }
    }
}

fn printed(sx: &Sx) -> String {
    let mut s = String::new();
    print(sx, &mut s);
    s
}

/// The atoms of a binding-free S-expression that are not bound by a
/// quantifier inside it (a quantifier's variable list is declarations, not
/// uses). Every atom counts, operators included: over-counting can only make
/// the capture check stricter.
fn free_atoms(sx: &Sx) -> HashSet<String> {
    fn walk(sx: &Sx, bound: &mut Vec<String>, free: &mut HashSet<String>) {
        match sx {
            Sx::Atom(a) => {
                if !bound.contains(a) {
                    free.insert(a.clone());
                }
            }
            Sx::List(items) => {
                if let [Sx::Atom(h), Sx::List(vars), body] = items.as_slice()
                    && (h == "forall" || h == "exists")
                {
                    free.insert(h.clone());
                    let mark = bound.len();
                    for var in vars {
                        if let Sx::List(pair) = var
                            && let Some(Sx::Atom(name)) = pair.first()
                        {
                            bound.push(name.clone());
                        }
                    }
                    walk(body, bound, free);
                    bound.truncate(mark);
                } else {
                    for item in items {
                        walk(item, bound, free);
                    }
                }
            }
        }
    }
    let mut free = HashSet::new();
    walk(sx, &mut Vec::new(), &mut free);
    free
}

/// A binding in scope: its expansion, the expansion's free atoms, and how
/// many binders were open where it was made.
#[derive(Clone)]
struct Binding {
    expansion: Sx,
    free: HashSet<String>,
    depth: usize,
}

/// The expander's state: the variables of the open binders (one list per
/// binder, innermost last), and how many uses crossed a binder.
#[derive(Default)]
struct Scope {
    binders: Vec<Vec<String>>,
    crossings: usize,
}

/// Expand every `let` and every name in `env`. Fails if a name is used
/// under a binder opened after its binding and that binder binds an atom
/// the binding mentions free (the binding would be CAPTURED: it would mean
/// something else there), or if a `let` rebinds a name already in scope.
fn expand(sx: &Sx, env: &HashMap<String, Binding>, scope: &mut Scope) -> Result<Sx, String> {
    match sx {
        Sx::Atom(a) => match env.get(a) {
            Some(b) => {
                if b.depth < scope.binders.len() {
                    for var in scope.binders[b.depth..].iter().flatten() {
                        if b.free.contains(var) {
                            return Err(format!(
                                "{a} is captured: it mentions {var}, which a binder opened \
                                 after it binds"
                            ));
                        }
                    }
                    scope.crossings += 1;
                }
                Ok(b.expansion.clone())
            }
            None => Ok(sx.clone()),
        },
        Sx::List(items) => {
            let head = match items.first() {
                Some(Sx::Atom(h)) => h.as_str(),
                _ => "",
            };
            match head {
                "let" => {
                    let [_, Sx::List(pairs), body] = items.as_slice() else {
                        return Err(format!("malformed let: {}", printed(sx)));
                    };
                    let mut inner = env.clone();
                    for pair in pairs {
                        let Sx::List(nv) = pair else {
                            return Err("malformed let pair".into());
                        };
                        let [Sx::Atom(name), value] = nv.as_slice() else {
                            return Err("malformed let pair".into());
                        };
                        if env.contains_key(name) || inner.contains_key(name) {
                            return Err(format!("{name} is rebound"));
                        }
                        // Parallel let: the value sees the OUTER scope.
                        let expansion = expand(value, env, scope)?;
                        let free = free_atoms(&expansion);
                        inner.insert(
                            name.clone(),
                            Binding {
                                expansion,
                                free,
                                depth: scope.binders.len(),
                            },
                        );
                    }
                    expand(body, &inner, scope)
                }
                "forall" | "exists" => {
                    let [h, Sx::List(vars), body] = items.as_slice() else {
                        return Err(format!("malformed binder: {}", printed(sx)));
                    };
                    let names = vars
                        .iter()
                        .filter_map(|v| match v {
                            Sx::List(pair) => match pair.first() {
                                Some(Sx::Atom(name)) => Some(name.clone()),
                                _ => None,
                            },
                            Sx::Atom(_) => None,
                        })
                        .collect();
                    scope.binders.push(names);
                    let body = expand(body, env, scope);
                    scope.binders.pop();
                    Ok(Sx::List(vec![h.clone(), Sx::List(vars.clone()), body?]))
                }
                _ => Ok(Sx::List(
                    items
                        .iter()
                        .map(|i| expand(i, env, scope))
                        .collect::<Result<_, _>>()?,
                )),
            }
        }
    }
}

/// Expand a `let` text: the tree text it stands for, and how many uses of a
/// binding crossed a binder (capture-free, or this fails).
fn expand_let_text_counted(text: &str) -> Result<(String, usize), String> {
    let sx = parse(text);
    let [one] = sx.as_slice() else {
        return Err(format!("not one term: {text}"));
    };
    let mut scope = Scope::default();
    let tree = printed(&expand(one, &HashMap::new(), &mut scope)?);
    Ok((tree, scope.crossings))
}

fn expand_let_text(text: &str) -> Result<String, String> {
    expand_let_text_counted(text).map(|(tree, _)| tree)
}

/// Expand a script's definitions into its terms. Definitions are global
/// (made outside every binder), so a definition used under a binder is
/// capture-checked like a top-level `let`.
fn expand_script(definitions: &[String], terms: &[String]) -> Result<Vec<String>, String> {
    let mut env: HashMap<String, Binding> = HashMap::new();
    let mut scope = Scope::default();
    for def in definitions {
        let sx = parse(def);
        let [Sx::List(items)] = sx.as_slice() else {
            return Err(format!("not one command: {def}"));
        };
        let [Sx::Atom(cmd), Sx::Atom(name), Sx::List(params), _sort, body] = items.as_slice()
        else {
            return Err(format!("malformed define-fun: {def}"));
        };
        if cmd != "define-fun" || !params.is_empty() {
            return Err(format!("malformed define-fun: {def}"));
        }
        if env.contains_key(name) {
            return Err(format!("{name} is defined twice"));
        }
        let expansion = expand(body, &env, &mut scope)?;
        let free = free_atoms(&expansion);
        env.insert(
            name.clone(),
            Binding {
                expansion,
                free,
                depth: 0,
            },
        );
    }
    terms
        .iter()
        .map(|t| {
            let sx = parse(t);
            let [one] = sx.as_slice() else {
                return Err(format!("not one term: {t}"));
            };
            Ok(printed(&expand(one, &env, &mut scope)?))
        })
        .collect()
}

fn tree_size(f: &Formula) -> usize {
    let mut n = 0;
    let mut stack = vec![f];
    while let Some(g) = stack.pop() {
        n += 1;
        stack.extend(g.children());
    }
    n
}

// ─────────────────────────────────────────────────────────────────────────────
// Round trip and identity
// ─────────────────────────────────────────────────────────────────────────────

/// tree -> DAG -> tree is the identity for a witness of every variant, by
/// both interning paths, and the borrowed shell split agrees with the
/// `map_children` split.
#[test]
fn every_variant_round_trips() {
    let all = witnesses();
    let covered: HashSet<&str> = all.iter().map(variant_name).collect();
    for name in formula_variant_names() {
        assert!(covered.contains(name), "no witness of {name}");
    }

    let mut dag = FormulaDag::new();
    for w in &all {
        let id = dag.intern(w);
        assert_eq!(dag.expand(id), *w, "round trip of {w:?}");
        let before = dag.len();
        assert_eq!(dag.intern_owned(w.clone()), id, "owned interning of {w:?}");
        assert_eq!(dag.intern(w), id, "re-interning of {w:?}");
        assert_eq!(dag.len(), before, "re-interning {w:?} adds no node");

        // The borrowed split (`Shell::of`, a per-variant match) equals the
        // owned split (`map_children`), and rebuilding restores the node.
        let (split, kids) = Shell::split(w.clone());
        assert_eq!(Shell::of(w), split, "shells of {w:?}");
        assert_eq!(split.arity(), w.children().len());
        assert_eq!(*dag.shell(id), split);
        assert_eq!(dag.kids(id).len(), split.arity());
        assert_eq!(split.rebuild(kids).as_ref(), Ok(w));
        assert_eq!(
            split.rebuild(vec![Formula::Bool(true); split.arity() + 1]),
            Err(DagError::ArityMismatch {
                expected: split.arity(),
                found: split.arity() + 1
            })
        );
    }
}

/// Random formulas with shared subterms: round trip, and identity is exact —
/// two trees share an id exactly when they are equal.
#[test]
fn random_formulas_round_trip_with_exact_identity() {
    let corpus = random_corpus(0x5eed_0001, 400, 6);
    let mut dag = FormulaDag::new();
    let ids: Vec<NodeId> = corpus.iter().map(|f| dag.intern(f)).collect();
    for (f, &id) in corpus.iter().zip(&ids) {
        assert_eq!(dag.expand(id), *f);
        assert_eq!(dag.intern_owned(f.clone()), id);
    }
    for i in 0..corpus.len() {
        for j in 0..corpus.len() {
            assert_eq!(
                ids[i] == ids[j],
                corpus[i] == corpus[j],
                "identity of formulas {i} and {j}"
            );
        }
    }
    // Every distinct subtree of the corpus is one node, and nothing else is.
    let mut distinct: HashSet<Formula> = HashSet::new();
    for f in &corpus {
        f.visit(&mut |g| {
            distinct.insert(g.clone());
        });
    }
    assert_eq!(dag.len(), distinct.len());
    let tree_nodes: usize = corpus.iter().map(tree_size).sum();
    assert!(dag.len() < tree_nodes, "{} < {tree_nodes}", dag.len());
}

/// `mk` builds bottom-up exactly what `intern` builds, and refuses a wrong
/// arity or a child the DAG does not hold.
#[test]
fn mk_builds_bottom_up_and_validates() {
    let x = int("x");
    let fact = Formula::Le(bx(x.clone()), bx(Formula::Int(1)));
    let row = Formula::And(vec![fact.clone(), fact.clone(), Formula::Not(bx(fact))]);

    let mut built = FormulaDag::new();
    let xi = built.mk(Shell::of(&x), &[]).expect("leaf");
    let one = built.mk(Shell::of(&Formula::Int(1)), &[]).expect("leaf");
    let le = built
        .mk_like(
            &Formula::Le(bx(Formula::Bool(true)), bx(Formula::Bool(true))),
            &[xi, one],
        )
        .expect("binary");
    let not = built
        .mk_like(&Formula::Not(bx(Formula::Bool(true))), &[le])
        .expect("unary");
    let and_shell = Shell::of(&Formula::And(vec![Formula::Bool(true); 3]));
    let and = built.mk(and_shell.clone(), &[le, le, not]).expect("n-ary");
    assert_eq!(built.len(), 5);
    assert_eq!(built.expand(and), row);
    assert_eq!(built.get(&and_shell, &[le, le, not]), Some(and));
    assert_eq!(built.get(&and_shell, &[le, not, le]), None);
    assert_eq!(built.mk(and_shell.clone(), &[le, le, not]), Ok(and));
    assert_eq!(built.len(), 5, "mk of an existing node adds nothing");

    let mut interned = FormulaDag::new();
    let via_intern = interned.intern(&row);
    assert_eq!(
        via_intern.index(),
        and.index(),
        "the same indexes, bottom-up"
    );
    assert_ne!(via_intern, and, "but an id names its own DAG");
    assert!(!built.contains(via_intern) && !interned.contains(and));

    assert_eq!(
        built.mk(and_shell.clone(), &[le, not]),
        Err(DagError::ArityMismatch {
            expected: 3,
            found: 2
        })
    );
    // An id of another DAG is refused even when its index is in range: it
    // can never silently stand for this DAG's node at that index.
    let mut other = FormulaDag::new();
    let foreign = other.intern(&int("y"));
    assert_eq!(foreign.index(), 0, "in range of `built`");
    assert!(!built.contains(foreign));
    let not_shell = Shell::of(&Formula::Not(bx(Formula::Bool(true))));
    assert_eq!(
        built.mk(not_shell.clone(), &[foreign]),
        Err(DagError::UnknownNode {
            node: foreign,
            len: 5
        })
    );
    assert_eq!(built.get(&not_shell, &[foreign]), None);
    assert!(matches!(
        built.to_smtlib_script(&[foreign]),
        Err(DagError::UnknownNode { .. })
    ));
    let refused = std::panic::catch_unwind(|| built.expand(foreign));
    assert!(refused.is_err(), "expand refuses a foreign id");

    // A clone holds the same nodes under a new brand: the original's ids
    // are foreign to it, and `id_at` translates an index deliberately.
    let mut copy = built.clone();
    assert!(!copy.contains(and));
    let copied = copy.id_at(and.index()).expect("in range");
    assert_eq!(copy.expand(copied), row);
    // The two may diverge: an index the copy adds is out of `built`'s range,
    // and an index they share is still refused across them.
    let extra = copy.intern(&int("z"));
    assert!(!built.contains(extra));
    assert_eq!(copy.id_at(copy.len()), None);
    assert_eq!(built.kids(and).len(), 3);
    assert_eq!(
        built
            .kids(and)
            .map(|kid| built.expand(kid))
            .collect::<Vec<_>>(),
        row.children().into_iter().cloned().collect::<Vec<_>>()
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Printers
// ─────────────────────────────────────────────────────────────────────────────

/// Both sharing printers are the tree printer up to their bindings, for every
/// witness, for random formulas with sharing, and for scripts of several
/// assertions; no binding is used under a binder opened after it.
#[test]
fn sharing_printers_are_the_tree_printer_up_to_bindings() {
    let mut corpus = witnesses();
    corpus.extend(random_corpus(0x5eed_0002, 300, 7));
    let mut dag = FormulaDag::new();
    let ids: Vec<NodeId> = corpus.iter().map(|f| dag.intern(f)).collect();
    let mut bound_somewhere = 0;
    let mut crossings = 0;
    for (f, &id) in corpus.iter().zip(&ids) {
        let tree = f.to_smtlib();
        let shared = dag.to_smtlib(id);
        if shared.contains("(let (") {
            bound_somewhere += 1;
        }
        let expanded = expand_let_text_counted(&shared);
        assert_eq!(
            expanded.as_ref().map(|(text, _)| text.as_str()),
            Ok(tree.as_str()),
            "let text {shared}"
        );
        crossings += expanded.map_or(0, |(_, n)| n);
    }
    assert!(bound_somewhere > 50, "the corpus exercises let sharing");
    assert!(
        crossings > 20,
        "the corpus shares subterms across binders ({crossings} uses)"
    );

    // Scripts: several assertions share their top-level subterms.
    let mut defined = 0;
    for chunk in ids.chunks(6) {
        let script = dag.to_smtlib_script(chunk).expect("well-sorted roots");
        defined += script.definitions.len();
        let expanded =
            expand_script(&script.definitions, &script.terms).expect("capture-free script");
        for (text, &id) in expanded.iter().zip(chunk) {
            assert_eq!(*text, dag.expand(id).to_smtlib());
        }
        // A definition exists only for a node referenced twice or more.
        let mut all = script.definitions.join(" ");
        all.push(' ');
        all.push_str(&script.terms.join(" "));
        for def in &script.definitions {
            let name = def
                .split_whitespace()
                .nth(1)
                .expect("define-fun has a name");
            let uses = tokenize(&all).iter().filter(|t| *t == name).count();
            assert!(uses >= 3, "{name}: defined once, used {} times", uses - 1);
        }
    }
    assert!(defined > 50, "the corpus exercises define-fun sharing");
}

/// The exact `let` and `define-fun` texts of a small shared formula.
#[test]
fn sharing_printer_exact_text() {
    let x = int("x");
    let s = Formula::Add(bx(x.clone()), bx(Formula::Int(1)));
    let t = Formula::Mul(bx(s.clone()), bx(s.clone()));
    let f = Formula::And(vec![
        Formula::Lt(bx(t.clone()), bx(s.clone())),
        Formula::Gt(bx(t), bx(Formula::Int(0))),
    ]);
    assert_eq!(
        f.to_smtlib(),
        "(and (< (* (+ x 1) (+ x 1)) (+ x 1)) (> (* (+ x 1) (+ x 1)) 0))"
    );
    let mut dag = FormulaDag::new();
    let id = dag.intern(&f);
    // `(+ x 1)` is level 1, `(* …)` (which uses it) level 2: two lets.
    assert_eq!(
        dag.to_smtlib(id),
        "(let ((dag!0_0 (+ x 1))) (let ((dag!0_1 (* dag!0_0 dag!0_0))) \
         (and (< dag!0_1 dag!0_0) (> dag!0_1 0))))"
    );

    let g = Formula::Le(bx(s.clone()), bx(int("y")));
    let gid = dag.intern(&g);
    let script = dag.to_smtlib_script(&[id, gid]).expect("sorted");
    assert_eq!(
        script.definitions,
        [
            "(define-fun dag!0_0 () Int (+ x 1))",
            "(define-fun dag!0_1 () Int (* dag!0_0 dag!0_0))",
        ]
    );
    assert_eq!(
        script.terms,
        ["(and (< dag!0_1 dag!0_0) (> dag!0_1 0))", "(<= dag!0_0 y)"]
    );
    let mut text = String::new();
    script.write_assertions(&mut text);
    assert!(text.ends_with("(assert (<= dag!0_0 y))\n"));
}

/// Bindings of one level share one parallel `let`, separated by spaces;
/// each deeper level opens its own `let`.
#[test]
fn bindings_of_one_level_share_a_let() {
    let s = Formula::Add(bx(int("x")), bx(Formula::Int(1)));
    let t = Formula::Sub(bx(int("y")), bx(Formula::Int(2)));
    let u = Formula::Mul(bx(s.clone()), bx(t.clone()));
    let f = Formula::And(vec![
        Formula::Lt(bx(s.clone()), bx(t.clone())),
        Formula::Gt(bx(s), bx(t)),
        Formula::Eq(bx(u.clone()), bx(u)),
    ]);
    let mut dag = FormulaDag::new();
    let id = dag.intern(&f);
    let text = dag.to_smtlib(id);
    assert_eq!(
        text,
        "(let ((dag!0_0 (+ x 1)) (dag!0_1 (- y 2))) (let ((dag!0_2 (* dag!0_0 dag!0_1))) \
         (and (< dag!0_0 dag!0_1) (> dag!0_0 dag!0_1) (= dag!0_2 dag!0_2))))"
    );
    assert_eq!(expand_let_text(&text), Ok(f.to_smtlib()));
}

/// One DAG node can mean two things on the two sides of a binder: under
/// `forall ((x Int))`, `(> x 0)` is about the bound `x`. The printer binds
/// it outside and spells it again inside; it never refers to the outer
/// binding from inside.
#[test]
fn a_binding_is_never_captured() {
    let gt = Formula::Gt(bx(int("x")), bx(Formula::Int(0)));
    let body = Formula::And(vec![gt.clone(), gt.clone()]);
    let f = Formula::And(vec![
        gt.clone(),
        Formula::Or(vec![gt.clone(), var("p", Sort::Bool)]),
        Formula::forall(&[("x", Sort::Int)], body.clone()),
        Formula::exists(&[("x", Sort::Int)], body),
    ]);
    let mut dag = FormulaDag::new();
    let id = dag.intern(&f);
    let text = dag.to_smtlib(id);
    assert_eq!(
        text,
        "(let ((dag!0_0 (> x 0))) (and dag!0_0 (or dag!0_0 p) \
         (forall ((x Int)) (let ((dag!0_1 (> x 0))) (and dag!0_1 dag!0_1))) \
         (exists ((x Int)) (let ((dag!0_2 (> x 0))) (and dag!0_2 dag!0_2)))))"
    );
    assert_eq!(expand_let_text(&text), Ok(f.to_smtlib()));

    // Used ONCE under the binder and twice outside it: reusing the outer
    // name inside is the only way to share it there, and it is refused.
    let h = Formula::Gt(bx(int("k")), bx(Formula::Int(0)));
    let g = Formula::And(vec![
        h.clone(),
        Formula::Or(vec![h.clone(), var("p", Sort::Bool)]),
        Formula::forall(
            &[("k", Sort::Int)],
            Formula::Or(vec![h, var("q", Sort::Bool)]),
        ),
    ]);
    let gid = dag.intern(&g);
    let text = dag.to_smtlib(gid);
    assert_eq!(
        text,
        "(let ((dag!0_0 (> k 0))) (and dag!0_0 (or dag!0_0 p) \
         (forall ((k Int)) (or (> k 0) q))))"
    );
    assert_eq!(expand_let_text(&text), Ok(g.to_smtlib()));

    // The capture check of the expander itself fires on a hoisted binding,
    // and passes one that mentions no variable of the binder it crosses.
    let hoisted = "(let ((d (> x 0))) (and d (forall ((x Int)) d)))";
    assert!(expand_let_text(hoisted).is_err());
    let closed = "(let ((d (> y 0))) (and d (forall ((x Int)) d)))";
    assert_eq!(
        expand_let_text_counted(closed),
        Ok(("(and (> y 0) (forall ((x Int)) (> y 0)))".to_owned(), 1))
    );

    // Scripts: the top-level copies are defined, the binder bodies keep
    // their own lets.
    let i = Formula::Implies(bx(gt.clone()), bx(gt));
    let iid = dag.intern(&i);
    let script = dag.to_smtlib_script(&[id, iid]).expect("sorted");
    assert_eq!(script.definitions, ["(define-fun dag!0_0 () Bool (> x 0))"]);
    let expanded = expand_script(&script.definitions, &script.terms).expect("capture-free");
    assert_eq!(expanded, [f.to_smtlib(), i.to_smtlib()]);
}

/// A subterm that mentions no variable of the binders it sits under means
/// the same in every one of their bodies, and is written once, bound where
/// every use can see it: at the top level for one closed under every binder
/// of the DAG, in the body of the binder of `k` for one whose only such
/// variable is `k`. Shadowing opens a new region.
#[test]
fn closed_subterms_are_shared_across_binders() {
    let g = Formula::Gt(
        bx(Formula::Add(bx(int("y")), bx(Formula::Int(1)))),
        bx(Formula::Int(0)),
    );
    let f = Formula::And(vec![
        g.clone(),
        Formula::forall(
            &[("x", Sort::Int)],
            Formula::And(vec![
                g.clone(),
                Formula::Gt(bx(int("x")), bx(Formula::Int(0))),
            ]),
        ),
        Formula::exists(
            &[("x", Sort::Int)],
            Formula::Or(vec![
                g.clone(),
                Formula::Lt(bx(int("x")), bx(Formula::Int(0))),
            ]),
        ),
    ]);
    let mut dag = FormulaDag::new();
    let id = dag.intern(&f);
    let text = dag.to_smtlib(id);
    assert_eq!(
        text,
        "(let ((dag!0_0 (> (+ y 1) 0))) (and dag!0_0 \
         (forall ((x Int)) (and dag!0_0 (> x 0))) \
         (exists ((x Int)) (or dag!0_0 (< x 0)))))"
    );
    assert_eq!(
        expand_let_text_counted(&text),
        Ok((f.to_smtlib(), 2)),
        "two uses cross a binder"
    );

    // `(> k 1)` mentions `k` only: it is bound once in the body of the
    // binder of `k`, and shared by the two binders of `j` inside it.
    let m = Formula::Gt(bx(int("k")), bx(Formula::Int(1)));
    let nested = Formula::forall(
        &[("k", Sort::Int)],
        Formula::And(vec![
            Formula::forall(
                &[("j", Sort::Int)],
                Formula::And(vec![
                    m.clone(),
                    Formula::Lt(bx(int("j")), bx(Formula::Int(0))),
                ]),
            ),
            Formula::exists(
                &[("j", Sort::Int)],
                Formula::Or(vec![
                    m.clone(),
                    Formula::Gt(bx(int("j")), bx(Formula::Int(0))),
                ]),
            ),
        ]),
    );
    let nid = dag.intern(&nested);
    let text = dag.to_smtlib(nid);
    assert_eq!(
        text,
        "(forall ((k Int)) (let ((dag!0_0 (> k 1))) (and \
         (forall ((j Int)) (and dag!0_0 (< j 0))) \
         (exists ((j Int)) (or dag!0_0 (> j 0))))))"
    );
    assert_eq!(expand_let_text(&text), Ok(nested.to_smtlib()));

    // Shadowing: under the inner `forall ((k Int))`, `(> k 1)` is about the
    // inner `k`; the outer body's single use stays inline.
    let shadow = Formula::forall(
        &[("k", Sort::Int)],
        Formula::And(vec![
            m.clone(),
            Formula::forall(&[("k", Sort::Int)], Formula::And(vec![m.clone(), m])),
        ]),
    );
    let sid = dag.intern(&shadow);
    let text = dag.to_smtlib(sid);
    assert_eq!(
        text,
        "(forall ((k Int)) (and (> k 1) (forall ((k Int)) \
         (let ((dag!0_0 (> k 1))) (and dag!0_0 dag!0_0)))))"
    );
    assert_eq!(expand_let_text(&text), Ok(shadow.to_smtlib()));

    // Scripts: a closed subterm used in binder bodies is one definition.
    let script = dag.to_smtlib_script(&[id, nid]).expect("sorted");
    assert_eq!(
        script.definitions,
        ["(define-fun dag!0_0 () Bool (> (+ y 1) 0))"]
    );
    let expanded = expand_script(&script.definitions, &script.terms).expect("capture-free");
    assert_eq!(expanded, [f.to_smtlib(), nested.to_smtlib()]);
}

/// A subterm that mentions two bound names stays in the innermost body that
/// binds one of them at each use (it is never bound above it), and a binder
/// that mentions an outer binder's variable is bound in that binder's body.
#[test]
fn subterms_of_several_bound_names_stay_below_their_binders() {
    let (i, j, k) = (int("i"), int("j"), int("k"));
    let lt = Formula::Lt(bx(i.clone()), bx(j.clone()));
    let gt = Formula::Gt(bx(i), bx(Formula::Int(0)));
    let f = Formula::forall(
        &[("i", Sort::Int)],
        Formula::forall(
            &[("j", Sort::Int)],
            Formula::And(vec![lt.clone(), lt.clone(), gt.clone(), gt]),
        ),
    );
    let mut dag = FormulaDag::new();
    let id = dag.intern(&f);
    let text = dag.to_smtlib(id);
    assert_eq!(
        text,
        "(forall ((i Int)) (let ((dag!0_0 (> i 0))) (forall ((j Int)) \
         (let ((dag!0_1 (< i j))) (and dag!0_1 dag!0_1 dag!0_0 dag!0_0)))))"
    );
    assert_eq!(expand_let_text(&text), Ok(f.to_smtlib()));

    // `exists j. (< j k)` mentions `k`: bound in the body of `forall k`.
    let e = Formula::exists(&[("j", Sort::Int)], Formula::Lt(bx(j), bx(k.clone())));
    let g = Formula::forall(&[("k", Sort::Int)], Formula::And(vec![e.clone(), e]));
    let gid = dag.intern(&g);
    let text = dag.to_smtlib(gid);
    assert_eq!(
        text,
        "(forall ((k Int)) (let ((dag!0_0 (exists ((j Int)) (< j k)))) \
         (and dag!0_0 dag!0_0)))"
    );
    assert_eq!(expand_let_text(&text), Ok(g.to_smtlib()));

    // A binder of two names, used under another binder: the expansion is
    // exact and capture-free.
    let both = Formula::forall(&[("i", Sort::Int), ("j", Sort::Int)], lt.clone());
    let h = Formula::And(vec![
        both.clone(),
        Formula::exists(
            &[("x", Sort::Int)],
            Formula::And(vec![both.clone(), both, Formula::Lt(bx(k), bx(int("x")))]),
        ),
        lt.clone(),
        lt,
    ]);
    let hid = dag.intern(&h);
    let text = dag.to_smtlib(hid);
    assert_eq!(expand_let_text(&text), Ok(h.to_smtlib()), "{text}");
}

/// Names are fresh against every symbol of the formula: the prefix is
/// `dag!<j>_` for the smallest `j` whose prefix occurs nowhere in the
/// formula's text (a run with a leading zero, or no `_` after it, equals no
/// such prefix and blocks nothing).
#[test]
fn names_are_fresh_against_the_formula() {
    let s = Formula::Add(bx(int("dag!0_0")), bx(int("dag!00_1")));
    let quoted = Formula::Add(bx(int("dag!000_2 q")), bx(s.clone()));
    let f = Formula::Eq(bx(Formula::Mul(bx(s.clone()), bx(s))), bx(quoted.clone()));
    let mut dag = FormulaDag::new();
    let id = dag.intern(&f);
    let text = dag.to_smtlib(id);
    assert!(text.starts_with("(let ((dag!1_0 "), "{text}");
    assert_eq!(expand_let_text(&text), Ok(f.to_smtlib()));
    let symbols: HashSet<String> = tokenize(&f.to_smtlib()).into_iter().collect();
    for tok in tokenize(&text) {
        if tok.starts_with("dag!1_") {
            assert!(!symbols.contains(&tok), "{tok} is a symbol of the formula");
        }
    }

    // Every prefix `dag!0_` .. `dag!2_` taken, including by a quoted symbol
    // and a binder's own variable: the names move to `dag!3_`.
    let shared = Formula::Add(bx(int("dag!1_0")), bx(int("|dag!2_x|")));
    let g = Formula::And(vec![
        Formula::Lt(bx(shared.clone()), bx(shared)),
        Formula::forall(
            &[("dag!0_7", Sort::Int)],
            Formula::Gt(bx(int("dag!0_7")), bx(Formula::Int(0))),
        ),
    ]);
    let gid = dag.intern(&g);
    let text = dag.to_smtlib(gid);
    assert!(text.starts_with("(let ((dag!3_0 "), "{text}");
    assert_eq!(expand_let_text(&text), Ok(g.to_smtlib()));
}

/// The truncating `Rem`/`Div`, signed `BvToInt` and saturating
/// `FpToSbv`/`FpToUbv` spell an operand several times; the sharing printer
/// binds a compound operand once.
#[test]
fn repeated_operand_spellings_are_bound_once() {
    let big = Formula::Add(bx(int("x")), bx(Formula::Mul(bx(int("y")), bx(int("z")))));
    let big_text = big.to_smtlib();
    let fa = var("fa", Sort::Float { eb: 8, sb: 24 });
    let fbig = Formula::FpAdd(
        bx(Formula::FpRoundingMode(RoundingMode::RNE)),
        bx(fa.clone()),
        bx(fa),
    );
    let fbig_text = fbig.to_smtlib();
    let bv = Formula::BvAdd(
        bx(var("a", Sort::BitVec(8))),
        bx(var("b", Sort::BitVec(8))),
        8,
    );
    let bv_text = bv.to_smtlib();
    let cases = [
        (Formula::Rem(bx(big.clone()), bx(int("w"))), &big_text, 3),
        (Formula::Div(bx(big.clone()), bx(int("w"))), &big_text, 4),
        (Formula::BvToInt(bx(bv), 8, true), &bv_text, 3),
        (
            Formula::FpToSbv {
                rm: bx(Formula::FpRoundingMode(RoundingMode::RNE)),
                value: bx(fbig.clone()),
                width: 16,
                eb: 8,
                sb: 24,
            },
            &fbig_text,
            4,
        ),
        (
            Formula::FpToUbv {
                rm: bx(Formula::FpRoundingMode(RoundingMode::RTZ)),
                value: bx(fbig),
                width: 16,
                eb: 8,
                sb: 24,
            },
            &fbig_text,
            4,
        ),
    ];
    for (f, operand, times) in cases {
        let tree = f.to_smtlib();
        assert_eq!(tree.matches(operand.as_str()).count(), times, "{tree}");
        let mut dag = FormulaDag::new();
        let id = dag.intern(&f);
        let shared = dag.to_smtlib(id);
        assert_eq!(shared.matches(operand.as_str()).count(), 1, "{shared}");
        assert_eq!(expand_let_text(&shared), Ok(tree));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Linearity
// ─────────────────────────────────────────────────────────────────────────────

/// The VC shape this DAG exists for: row `i` conjoins the facts of rows
/// `1..i` and its own violation. The trees total Θ(n²) nodes; the DAG holds
/// exactly `7n + 1`. (The child lists of the flat `And`s still total Θ(n²)
/// edges: re-associating rows into shared context cells is the next step of
/// the plan, not this store's job.)
#[test]
fn node_count_is_linear_on_shared_inputs() {
    fn ladder(n: usize) -> Vec<Formula> {
        let v = |i: usize| int(&format!("v{i}"));
        let facts: Vec<Formula> = (1..=n)
            .map(|i| {
                Formula::Le(
                    bx(v(i)),
                    bx(Formula::Add(bx(v(i - 1)), bx(Formula::Int(1)))),
                )
            })
            .collect();
        (1..=n)
            .map(|i| {
                let mut conj: Vec<Formula> = facts[..i].to_vec();
                let bound = Formula::Int(i128::try_from(i).unwrap_or(0));
                conj.push(Formula::Not(bx(Formula::Le(bx(v(i)), bx(bound)))));
                Formula::And(conj)
            })
            .collect()
    }
    let mut measured = Vec::new();
    for n in [8usize, 16, 32, 64, 128] {
        let rows = ladder(n);
        let tree: usize = rows.iter().map(tree_size).sum();
        let mut dag = FormulaDag::new();
        let ids: Vec<NodeId> = rows.iter().map(|r| dag.intern(r)).collect();
        assert_eq!(dag.len(), 7 * n + 1, "n = {n}");
        assert_eq!(tree, 5 * n + 5 * n * (n + 1) / 2, "n = {n}");
        assert_eq!(dag.edge_count(), n * (n + 1) / 2 + 8 * n, "n = {n}");
        let script = dag.to_smtlib_script(&ids).expect("sorted");
        let script_len: usize = script
            .definitions
            .iter()
            .chain(&script.terms)
            .map(String::len)
            .sum();
        let tree_len: usize = rows.iter().map(|r| r.to_smtlib().len()).sum();
        measured.push((n, dag.len(), tree, script_len, tree_len));
    }
    // Doubling n doubles the node count (exactly, up to the constant) and
    // quadruples the trees.
    for w in measured.windows(2) {
        let (a, b) = (w[0], w[1]);
        assert_eq!(b.1 - 1, 2 * (a.1 - 1), "{measured:?}");
        assert!(b.2 > 3 * a.2, "{measured:?}");
        assert!(
            b.3 < b.4,
            "the script is smaller than the trees: {measured:?}"
        );
    }
}

/// A chain whose every node uses its child twice: a DAG of `n + 1` nodes
/// whose tree has `2^(n+1) - 1`. The `let` text is linear in `n`; the tree
/// text would be exponential.
#[test]
fn doubling_chain_prints_linearly() {
    fn chain(n: usize) -> (FormulaDag, NodeId) {
        let mut dag = FormulaDag::new();
        let mut d = dag.intern(&int("x"));
        let add = Shell::of(&Formula::Add(
            bx(Formula::Bool(true)),
            bx(Formula::Bool(true)),
        ));
        for _ in 0..n {
            d = dag.mk(add.clone(), &[d, d]).expect("add");
        }
        (dag, d)
    }
    let (dag, root) = chain(3);
    assert_eq!(
        dag.to_smtlib(root),
        "(let ((dag!0_0 (+ x x))) (let ((dag!0_1 (+ dag!0_0 dag!0_0))) \
         (+ dag!0_1 dag!0_1)))"
    );
    assert_eq!(
        dag.expand(root).to_smtlib(),
        "(+ (+ (+ x x) (+ x x)) (+ (+ x x) (+ x x)))"
    );
    for n in [10usize, 20, 40, 80] {
        let (dag, root) = chain(n);
        assert_eq!(dag.len(), n + 1);
        let text = dag.to_smtlib(root);
        // Exact: n - 1 nested lets, one binding each.
        let name = |k: usize| format!("dag!0_{k}");
        let mut want = format!("(let (({} (+ x x))) ", name(0));
        for k in 1..n - 1 {
            want.push_str(&format!(
                "(let (({} (+ {} {}))) ",
                name(k),
                name(k - 1),
                name(k - 1)
            ));
        }
        want.push_str(&format!("(+ {} {})", name(n - 2), name(n - 2)));
        want.push_str(&")".repeat(n - 1));
        assert_eq!(text, want);
    }
}

/// A node with 2·10^5 children: every walk is linear in the width too (a
/// walk that re-listed an n-ary node's children per slot would do 4·10^10
/// steps here).
#[test]
fn wide_nodes_are_linear() {
    const WIDE: usize = 200_000;
    let atoms: Vec<Formula> = (0..WIDE)
        .map(|i| {
            Formula::Le(
                bx(int(&format!("v{i}"))),
                bx(Formula::Int(i128::try_from(i).unwrap_or(0))),
            )
        })
        .collect();
    let f = Formula::And(atoms);
    let mut dag = FormulaDag::new();
    let id = dag.intern(&f);
    assert_eq!(dag.kids(id).len(), WIDE);
    assert_eq!(dag.intern_owned(f.clone()), id);
    assert_eq!(dag.expand(id), f);
    let tree = f.to_smtlib();
    assert_eq!(dag.to_smtlib(id), tree, "nothing compound is shared");
    let script = dag.to_smtlib_script(&[id, id]).expect("sorted");
    assert_eq!(
        script.definitions.len(),
        1,
        "the repeated root is defined once"
    );
    assert_eq!(script.terms, ["dag!0_0", "dag!0_0"]);
}

/// The work counters of every print below double (within 5%) when the
/// input doubles. Each counter is deterministic, so a super-linear
/// regression fails here as a ratio near 4 (or worse), rather than hanging
/// the gate at the large sizes of the smoke tests.
fn assert_doubling(what: &str, sizes: &[usize], stats: &[PrintStats]) {
    let fields = |s: &PrintStats| {
        [
            ("nodes", s.nodes),
            ("spellings", s.spellings),
            ("references", s.references),
            ("rendered_bytes", s.rendered_bytes),
            ("output_bytes", s.output_bytes),
        ]
    };
    for (w, n) in stats.windows(2).zip(sizes.windows(2)) {
        assert_eq!(n[1], 2 * n[0], "{what}: sizes must double");
        for ((name, a), (_, b)) in fields(&w[0]).into_iter().zip(fields(&w[1])) {
            assert!(
                a > 0 && 20 * b <= 41 * a && 20 * b >= 39 * a,
                "{what}: {name} went {a} -> {b} when the input went {} -> {}",
                n[0],
                n[1]
            );
        }
    }
}

const SIZES: [usize; 4] = [1000, 2000, 4000, 8000];

/// A wide `And` (fixed-width names, so its text is exactly linear), a deep
/// chain, and a deep chain whose every node is shared: linear work.
#[test]
fn printer_work_is_linear_on_wide_and_deep_inputs() {
    let atom = |i: usize| {
        Formula::Le(
            bx(int(&format!("v{i:06}"))),
            bx(Formula::Int(i128::try_from(i % 7).unwrap_or(0))),
        )
    };
    let mut wide = Vec::new();
    let mut deep = Vec::new();
    let mut shared = Vec::new();
    for &n in &SIZES {
        let mut dag = FormulaDag::new();
        let id = dag.intern(&Formula::And((0..n).map(atom).collect()));
        let mut out = String::new();
        wide.push(dag.write_smtlib(id, &mut out));

        let mut dag = FormulaDag::new();
        let mut d = dag.intern(&var("p", Sort::Bool));
        for i in 0..n {
            d = match i % 3 {
                0 => dag.mk_like(&Formula::Not(bx(Formula::Bool(true))), &[d]),
                1 => {
                    let q = dag.intern(&var("q", Sort::Bool));
                    dag.mk_like(
                        &Formula::Implies(bx(Formula::Bool(true)), bx(Formula::Bool(true))),
                        &[q, d],
                    )
                }
                _ => {
                    let a = dag.intern(&atom(i));
                    dag.mk_like(&Formula::And(vec![Formula::Bool(true); 2]), &[d, a])
                }
            }
            .expect("well-formed");
        }
        let mut out = String::new();
        deep.push(dag.write_smtlib(d, &mut out));

        let mut dag = FormulaDag::new();
        let mut d = dag.intern(&int("x"));
        let add = Shell::of(&Formula::Add(
            bx(Formula::Bool(true)),
            bx(Formula::Bool(true)),
        ));
        for _ in 0..n {
            d = dag.mk(add.clone(), &[d, d]).expect("add");
        }
        let mut out = String::new();
        let stats = dag.write_smtlib(d, &mut out);
        assert_eq!(stats.bindings, n - 1, "every shared node is bound once");
        shared.push(stats);
    }
    assert_doubling("wide And", &SIZES, &wide);
    assert_doubling("deep chain", &SIZES, &deep);
    // The shared chain's names grow by a digit now and then, so only the
    // structural counters are exact here.
    for w in shared.windows(2) {
        assert_eq!(w[1].nodes - 1, 2 * (w[0].nodes - 1));
        assert_eq!(w[1].spellings - 1, 2 * (w[0].spellings - 1));
        assert_eq!(w[1].references, 2 * w[0].references);
    }
}

/// The two quantified shapes on which a printer that never moved a subterm
/// across a binder is super-linear. (1) Nested binders over closed shared
/// bodies: `A_i = forall x_i. (and A_{i-1} B_{i-1})`, `B_i = exists y_i.
/// (and A_{i-1} B_{i-1})` — a DAG of O(n) nodes whose binder bodies a
/// region-per-binder printer re-spells 2^n times. (2) One closed context of
/// m nodes used under k sibling binders `forall x_i. (>= ctx x_i)` — the
/// per-row quantified obligation over a shared context — which such a
/// printer re-spells k times. Here every node is spelled once.
#[test]
fn quantified_sharing_is_linear() {
    let and2 = Shell::of(&Formula::And(vec![Formula::Bool(true); 2]));
    let binder = |exists: bool, name: &str| {
        let bindings = vec![(Symbol::intern(name), Sort::Int)];
        Shell::of(&if exists {
            Formula::Exists(bindings, bx(Formula::Bool(true)))
        } else {
            Formula::Forall(bindings, bx(Formula::Bool(true)))
        })
    };
    let nested = |n: usize| {
        let mut dag = FormulaDag::new();
        let (mut a, mut b) = (
            dag.intern(&var("p", Sort::Bool)),
            dag.intern(&var("q", Sort::Bool)),
        );
        for i in 0..n {
            let body = dag.mk(and2.clone(), &[a, b]).expect("and");
            a = dag
                .mk(binder(false, &format!("x{i:05}")), &[body])
                .expect("forall");
            b = dag
                .mk(binder(true, &format!("y{i:05}")), &[body])
                .expect("exists");
        }
        let root = dag.mk(and2.clone(), &[a, b]).expect("and");
        (dag, root)
    };
    // Small n: the exact text, and its expansion is the (exponential) tree.
    let (dag, root) = nested(2);
    let text = dag.to_smtlib(root);
    assert_eq!(
        text,
        "(let ((dag!0_0 (and p q))) (let ((dag!0_1 (and (forall ((x00000 Int)) dag!0_0) \
         (exists ((y00000 Int)) dag!0_0)))) (and (forall ((x00001 Int)) dag!0_1) \
         (exists ((y00001 Int)) dag!0_1))))"
    );
    assert_eq!(expand_let_text(&text), Ok(dag.expand(root).to_smtlib()));
    let mut stats = Vec::new();
    for &n in &SIZES {
        let (dag, root) = nested(n);
        let mut out = String::new();
        let s = dag.write_smtlib(root, &mut out);
        assert_eq!(s.spellings, s.nodes, "n = {n}: one spelling per node");
        assert_eq!(s.regions, 2 * n + 1, "n = {n}: one region per binder");
        stats.push(s);
    }
    assert_doubling("nested binders over closed bodies", &SIZES, &stats);

    let context = |k: usize| {
        let m = k;
        let mut dag = FormulaDag::new();
        let mut ctx = dag.intern(&int("v00000"));
        let add = Shell::of(&Formula::Add(
            bx(Formula::Bool(true)),
            bx(Formula::Bool(true)),
        ));
        for j in 1..m {
            let v = dag.intern(&int(&format!("v{j:05}")));
            ctx = dag.mk(add.clone(), &[ctx, v]).expect("add");
        }
        let ge = Shell::of(&Formula::Ge(
            bx(Formula::Bool(true)),
            bx(Formula::Bool(true)),
        ));
        let mut rows = Vec::new();
        for i in 0..k {
            let name = format!("x{i:05}");
            let x = dag.intern(&int(&name));
            let body = dag.mk(ge.clone(), &[ctx, x]).expect("ge");
            rows.push(dag.mk(binder(false, &name), &[body]).expect("forall"));
        }
        let root = dag
            .mk(
                Shell::of(&Formula::And(vec![Formula::Bool(true); k])),
                &rows,
            )
            .expect("and");
        (dag, root)
    };
    let (dag, root) = context(3);
    let text = dag.to_smtlib(root);
    assert_eq!(
        text,
        "(let ((dag!0_0 (+ (+ v00000 v00001) v00002))) (and \
         (forall ((x00000 Int)) (>= dag!0_0 x00000)) \
         (forall ((x00001 Int)) (>= dag!0_0 x00001)) \
         (forall ((x00002 Int)) (>= dag!0_0 x00002))))"
    );
    assert_eq!(expand_let_text(&text), Ok(dag.expand(root).to_smtlib()));
    let mut stats = Vec::new();
    for &k in &SIZES {
        let (dag, root) = context(k);
        let mut out = String::new();
        let s = dag.write_smtlib(root, &mut out);
        assert_eq!(s.spellings, s.nodes, "k = {k}: one spelling per node");
        assert_eq!(s.bindings, 1, "k = {k}: the context is bound once");
        stats.push(s);
    }
    assert_doubling("a closed context under k binders", &SIZES, &stats);
}

/// What `let` cannot share: a subterm that mentions a binder's variable
/// means something else in every printed body of that binder, and no `let`
/// outside a body can denote that body's variable. `G_0 = (> k 0)`,
/// `G_{i+1} = (and (forall ((k Int)) G_i) G_i)`: the body of the i-th
/// binder spells `G_i, G_{i-1}, …, G_0` about ITS `k` — n(n+3)/2 spellings
/// in all for a DAG of 2n+3 nodes, exactly one per (node, region), while the
/// tree has 2^n copies. The printer writes that minimum, never more.
#[test]
fn open_subterms_are_spelled_once_per_binder_body() {
    for n in [1usize, 2, 4, 8, 12] {
        let mut dag = FormulaDag::new();
        let mut g = dag.intern(&Formula::Gt(bx(int("k")), bx(Formula::Int(0))));
        let forall_k = Shell::of(&Formula::forall(&[("k", Sort::Int)], Formula::Bool(true)));
        let and2 = Shell::of(&Formula::And(vec![Formula::Bool(true); 2]));
        for _ in 0..n {
            let b = dag.mk(forall_k.clone(), &[g]).expect("forall");
            g = dag.mk(and2.clone(), &[b, g]).expect("and");
        }
        let mut text = String::new();
        let stats = dag.write_smtlib(g, &mut text);
        assert_eq!(stats.nodes, 2 * n + 3, "n = {n}");
        assert_eq!(stats.regions, n + 1, "n = {n}");
        assert_eq!(
            stats.spellings,
            (2 * n + 3) + n * (n + 3) / 2,
            "n = {n}: one spelling per (node, region)"
        );
        let tree = dag.expand(g).to_smtlib();
        assert!(text.len() < tree.len() || n < 4, "n = {n}");
        assert_eq!(expand_let_text(&text), Ok(tree), "n = {n}");
    }
}

/// The fresh-name prefix does not grow with the formula's symbols: a symbol
/// with an arbitrarily long digit run after `dag!` blocks no prefix, and `t`
/// symbols that block `dag!0_` .. `dag!{t-1}_` move it to `dag!{t}_` — at
/// most the digits of the number of `dag!` occurrences.
#[test]
fn name_length_does_not_depend_on_symbols() {
    let build = |run: usize, taken: usize, chain: usize| {
        let mut dag = FormulaDag::new();
        let mut d = dag.intern(&int(&format!("dag!{}_", "7".repeat(run))));
        let add = Shell::of(&Formula::Add(
            bx(Formula::Bool(true)),
            bx(Formula::Bool(true)),
        ));
        for t in 0..taken {
            let v = dag.intern(&int(&format!("dag!{t}_v")));
            d = dag.mk(add.clone(), &[d, v]).expect("add");
        }
        let one = dag.intern(&Formula::Int(1));
        let mut acc = d;
        for _ in 0..chain {
            d = dag.mk(add.clone(), &[d, one]).expect("add");
            let twice = dag.mk(add.clone(), &[d, d]).expect("add");
            acc = dag.mk(add.clone(), &[acc, twice]).expect("add");
        }
        let mut out = String::new();
        let stats = dag.write_smtlib(acc, &mut out);
        (out, stats)
    };
    let (base, _) = build(0, 0, 500);
    assert!(base.starts_with("(let ((dag!0_0 "));
    let mut rest = Vec::new();
    for run in [1_000usize, 10_000, 100_000] {
        let (text, stats) = build(run, 0, 500);
        assert!(text.starts_with("(let ((dag!0_0 "), "run {run}");
        assert_eq!(stats.output_bytes, text.len());
        // The long symbol is bound once and written once; nothing else in
        // the text depends on its length.
        assert_eq!(text.matches(&"7".repeat(run)).count(), 1, "run {run}");
        rest.push(text.len() - run);
    }
    assert!(rest.windows(2).all(|w| w[0] == w[1]), "{rest:?}");
    for taken in [1usize, 10, 100] {
        let (text, _) = build(0, taken, 20);
        assert!(
            text.starts_with(&format!("(let ((dag!{taken}_0 ")),
            "{taken} prefixes taken: {}",
            &text[..40]
        );
        assert!(expand_let_text(&text).is_ok(), "{taken} prefixes taken");
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Depth: everything iterative
// ─────────────────────────────────────────────────────────────────────────────

const DEEP: usize = 1_000_000;

/// A 10^6-deep chain mixing unary, n-ary, ternary and binder nodes: intern
/// (both paths), expand, both printers and the drop all run without
/// recursion.
#[test]
fn million_deep_chain_is_iterative() {
    let p = || var("p", Sort::Bool);
    let q = || var("q", Sort::Bool);
    let k = Symbol::intern("k");
    let mut f = p();
    for i in 0..DEEP {
        f = match i % 5 {
            0 => Formula::Not(bx(f)),
            1 => Formula::And(vec![f, q()]),
            2 => Formula::Implies(bx(p()), bx(f)),
            3 => Formula::Forall(vec![(k, Sort::Int)], bx(f)),
            _ => Formula::Ite(bx(p()), bx(f), bx(q())),
        };
    }
    let mut dag = FormulaDag::new();
    let id = dag.intern(&f);
    assert_eq!(dag.len(), DEEP + 2, "every level is one node, plus p and q");

    let back = dag.expand(id);
    assert!(eq_iterative(&back, &f), "expand(intern(f)) == f");
    let tree = f.to_smtlib();
    // One tree at a time from here on: the test's own peak memory.
    f.drop_iterative();
    assert_eq!(dag.intern_owned(back), id, "owned interning, same id");
    assert_eq!(dag.len(), DEEP + 2);

    // Nothing compound is shared, so the sharing text IS the tree text.
    assert!(tree.starts_with("(ite p (forall ((k Int)) (=> p (and (not (ite p"));
    assert!(
        dag.to_smtlib(id) == tree,
        "sharing text of an unshared chain"
    );
    let script = dag.to_smtlib_script(&[id]).expect("sorted");
    assert!(script.definitions.is_empty());
    assert!(script.terms.len() == 1 && script.terms[0] == tree);
}

/// A 10^6-deep chain whose every node is shared: 10^6 - 1 nested lets,
/// printed iteratively, in linear size.
#[test]
fn million_deep_shared_chain_prints_iteratively() {
    let mut dag = FormulaDag::new();
    let mut d = dag.intern(&int("x"));
    let add = Shell::of(&Formula::Add(
        bx(Formula::Bool(true)),
        bx(Formula::Bool(true)),
    ));
    for _ in 0..DEEP {
        d = dag.mk(add.clone(), &[d, d]).expect("add");
    }
    assert_eq!(dag.len(), DEEP + 1);
    let text = dag.to_smtlib(d);
    let lets = DEEP - 1;
    assert_eq!(text.matches("(let ((").count(), lets);
    // Each binding k is `(let ((dag!0_k (+ dag!0_{k-1} dag!0_{k-1}))) ` and
    // a closing `)`: linear in DEEP up to the digits of k.
    let digits: usize = (0..lets).map(|k| k.to_string().len()).sum();
    assert!(text.len() < 40 * DEEP + 3 * digits, "{} bytes", text.len());
    assert!(text.ends_with(&format!(
        "(+ dag!0_{0} dag!0_{0}){1}",
        lets - 1,
        ")".repeat(lets)
    )));
}
