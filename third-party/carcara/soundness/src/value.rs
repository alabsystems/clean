// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Values of the independent SMT-LIB evaluator.

use crate::regex::Re;
use crate::sort::S;
use carcara::ast::{Rc as TRc, Term};
use rug::{Integer, Rational};
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum V {
    Bool(bool),
    /// Both `Int` and `Real` values; SMT-LIB arithmetic is numeric either way.
    Num(Rational),
    /// Unsigned value in `[0, 2^w)` and width `w`.
    Bv(Integer, usize),
    Str(Rc<Vec<u32>>),
    /// Element `i` of an uninterpreted sort.
    Elem(Rc<str>, u32),
    Arr(Rc<ArrV>),
    Fun(Rc<FunV>),
    Re(Rc<Re>),
    /// A datatype value: a constructor applied to field values.
    Dt(Rc<DtV>),
}

/// A constructor of datatype `datatype` applied to `fields`. Datatype values are the terms of a
/// free algebra, so two of them are equal exactly when they are structurally equal.
#[derive(Clone, Debug)]
pub struct DtV {
    pub datatype: Rc<str>,
    pub ctor: Rc<str>,
    pub fields: Vec<V>,
}

/// An array value in canonical form (see [`ArrV::canon`]).
#[derive(Clone, Debug)]
pub struct ArrV {
    pub default: V,
    pub entries: BTreeMap<V, V>,
}

#[derive(Debug)]
pub enum FunV {
    /// A lambda with its remaining binders, closed over an environment.
    Closure {
        params: Vec<(String, S)>,
        body: TRc<Term>,
        env: Env,
    },
    /// An uninterpreted function symbol; its table lives in the model.
    Symbol { name: String, sort: S },
    /// A finite table with a default value.
    Table {
        map: BTreeMap<Vec<V>, V>,
        default: V,
    },
    /// Partial application of another function value.
    Partial { base: Rc<FunV>, applied: Vec<V> },
    /// A datatype constructor with `arity` fields.
    Ctor {
        datatype: Rc<str>,
        ctor: Rc<str>,
        arity: usize,
    },
    /// The selector `name` (of sort `sort`), which projects field `index` of a `ctor` value. On a
    /// value built by any other constructor its value is unspecified (SMT-LIB), so the model
    /// picks it freely, as for an uninterpreted function.
    Selector {
        name: String,
        sort: S,
        ctor: Rc<str>,
        index: usize,
    },
}

#[derive(Clone, Debug, Default)]
pub struct Env(Option<Rc<(String, S, V, Env)>>);

impl Env {
    pub fn new() -> Self {
        Env(None)
    }

    pub fn bind(&self, name: &str, sort: S, value: V) -> Env {
        Env(Some(Rc::new((name.to_owned(), sort, value, self.clone()))))
    }

    pub fn lookup(&self, name: &str, sort: &S) -> Option<&V> {
        let mut cur = &self.0;
        while let Some(node) = cur {
            if node.0 == name && &node.1 == sort {
                return Some(&node.2);
            }
            cur = &node.3 .0;
        }
        None
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }
}

/// Widths up to this bound are computed by materializing `2^w`. Above it the evaluator is exact
/// for every value that needs no `2^w` (a non-negative value is its own residue while it has at
/// most `w` bits) and `Unknown` otherwise. It never reads a width modulo `2^32`: Carcara's own
/// `evaluate` did (`keep_bits(w as u32)`), and an evaluator making the same mistake would agree
/// with it instead of judging it.
pub const MAX_MATERIALIZED_BV_WIDTH: usize = 1 << 16;

/// `x mod 2^w`, exactly, or `None` when that needs a `2^w` wider than the bound.
pub fn bv_reduce(x: Integer, w: usize) -> Option<Integer> {
    let bits = x.significant_bits() as usize;
    if x >= 0 && bits <= w {
        return Some(x);
    }
    if x >= 0 || w <= MAX_MATERIALIZED_BV_WIDTH {
        // Either `w < bits`, and `bits` fits in a `u32`, or `w` is below the bound: the cast is
        // exact either way.
        return Some(x.keep_bits(u32::try_from(w).ok()?));
    }
    None
}

impl V {
    pub fn int(i: i64) -> V {
        V::Num(Rational::from(i))
    }

    /// A bit-vector value of a width small enough, or a value small enough, that
    /// [`bv_reduce`] needs no `2^w` beyond [`MAX_MATERIALIZED_BV_WIDTH`]. Only the model's own
    /// domains use this; the evaluator goes through [`V::try_bv`].
    pub fn bv(value: Integer, width: usize) -> V {
        V::try_bv(value, width)
            .expect("bit-vector value needs 2^w beyond the materialization bound")
    }

    /// The bit-vector value `value mod 2^width`, or `None` when computing it would materialize a
    /// power of two wider than [`MAX_MATERIALIZED_BV_WIDTH`].
    pub fn try_bv(value: Integer, width: usize) -> Option<V> {
        Some(V::Bv(bv_reduce(value, width)?, width))
    }

    pub fn string(s: &str) -> V {
        V::Str(Rc::new(s.chars().map(|c| c as u32).collect()))
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            V::Bool(b) => Some(*b),
            _ => None,
        }
    }

    fn rank(&self) -> u8 {
        match self {
            V::Bool(_) => 0,
            V::Num(_) => 1,
            V::Bv(..) => 2,
            V::Str(_) => 3,
            V::Elem(..) => 4,
            V::Arr(_) => 5,
            V::Fun(_) => 6,
            V::Re(_) => 7,
            V::Dt(_) => 8,
        }
    }

    /// Does this value (transitively) contain a function value? Such values have no decidable
    /// syntactic equality, so they must never be used as table keys.
    pub fn has_fun(&self) -> bool {
        match self {
            V::Fun(_) => true,
            V::Arr(a) => {
                a.default.has_fun() || a.entries.iter().any(|(k, v)| k.has_fun() || v.has_fun())
            }
            V::Dt(d) => d.fields.iter().any(V::has_fun),
            _ => false,
        }
    }
}

impl PartialEq for V {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for V {}

impl PartialOrd for V {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for V {
    /// A total order used for canonical forms and table keys. For values that do not contain
    /// functions, `Equal` coincides with semantic equality.
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (V::Bool(a), V::Bool(b)) => a.cmp(b),
            (V::Num(a), V::Num(b)) => a.cmp(b),
            (V::Bv(a, w), V::Bv(b, v)) => w.cmp(v).then_with(|| a.cmp(b)),
            (V::Str(a), V::Str(b)) => a.cmp(b),
            (V::Elem(s, a), V::Elem(t, b)) => s.cmp(t).then_with(|| a.cmp(b)),
            (V::Arr(a), V::Arr(b)) => a
                .default
                .cmp(&b.default)
                .then_with(|| a.entries.iter().cmp(b.entries.iter())),
            (V::Fun(a), V::Fun(b)) => (Rc::as_ptr(a) as usize).cmp(&(Rc::as_ptr(b) as usize)),
            (V::Re(a), V::Re(b)) => a.cmp(b),
            (V::Dt(a), V::Dt(b)) => a
                .datatype
                .cmp(&b.datatype)
                .then_with(|| a.ctor.cmp(&b.ctor))
                .then_with(|| a.fields.iter().cmp(b.fields.iter())),
            _ => self.rank().cmp(&other.rank()),
        }
    }
}

impl ArrV {
    /// Canonical form: entries equal to the default are dropped. When the index sort is finite
    /// (and `domain` enumerates it), the default is chosen as the value at the least index, so
    /// that extensionally equal arrays have identical representations.
    pub fn canon(default: V, entries: BTreeMap<V, V>, domain: Option<&[V]>) -> ArrV {
        match domain {
            Some(dom) if !dom.is_empty() => {
                // Materialize the full table with the *old* default, then pick the value at the
                // least index as the new default.
                let full: Vec<(V, V)> = dom
                    .iter()
                    .map(|d| {
                        let v = entries.get(d).cloned().unwrap_or_else(|| default.clone());
                        (d.clone(), v)
                    })
                    .collect();
                let new_default = full[0].1.clone();
                let entries = full
                    .into_iter()
                    .filter(|(_, v)| *v != new_default)
                    .collect();
                ArrV { default: new_default, entries }
            }
            _ => {
                let mut entries = entries;
                entries.retain(|_, v| *v != default);
                ArrV { default, entries }
            }
        }
    }

    pub fn select(&self, index: &V) -> V {
        self.entries
            .get(index)
            .cloned()
            .unwrap_or_else(|| self.default.clone())
    }
}

pub fn fmt_value(v: &V) -> String {
    match v {
        V::Bool(b) => b.to_string(),
        V::Num(r) => {
            if r.is_integer() {
                r.numer().to_string()
            } else {
                format!("{}/{}", r.numer(), r.denom())
            }
        }
        V::Bv(x, w) if *w > 1024 => format!("(_ bv{} {})", x, w),
        V::Bv(x, w) => {
            let s = format!("{:b}", x);
            format!("#b{}{}", "0".repeat(w.saturating_sub(s.len())), s)
        }
        V::Str(s) => format!(
            "{:?}",
            s.iter()
                .map(|c| char::from_u32(*c).unwrap_or('?'))
                .collect::<String>()
        ),
        V::Elem(s, i) => format!("{}!{}", s, i),
        V::Arr(a) => {
            let mut out = format!("(array default={}", fmt_value(&a.default));
            for (k, val) in &a.entries {
                out.push_str(&format!(" [{}]={}", fmt_value(k), fmt_value(val)));
            }
            out.push(')');
            out
        }
        V::Fun(_) => "<function>".to_owned(),
        V::Re(r) => format!("{:?}", r),
        V::Dt(d) if d.fields.is_empty() => d.ctor.to_string(),
        V::Dt(d) => {
            let fields: Vec<String> = d.fields.iter().map(fmt_value).collect();
            format!("({} {})", d.ctor, fields.join(" "))
        }
    }
}
