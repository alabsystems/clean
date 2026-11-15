// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! An independent, three-valued SMT-LIB evaluator.
//!
//! It shares nothing with Carcara's own `evaluate` implementation: every operator is written
//! from the SMT-LIB 2.6 theory definitions (Core, Ints, Reals, Reals_Ints, FixedSizeBitVectors,
//! ArraysEx, Strings) plus the cvc5/Alethe extensions Carcara accepts (`@bbterm`, `@bit_of`,
//! `@int_of`, `@pbbterm`, `int.pow2`, ...). Whenever a value is not determined by the model at
//! hand (a quantifier over an infinite sort without a counterexample in the sample, an operator
//! the evaluator does not model, an exhausted fuel budget), the result is `Unknown`. A definite
//! `false` is therefore always a genuine counterexample for the model.

use crate::datatypes::DtSymbol;
use crate::model::{product, Model};
use crate::regex::Re;
use crate::sort::S;
use crate::value::{bv_reduce, ArrV, DtV, Env, FunV, MAX_MATERIALIZED_BV_WIDTH, V};
use carcara::ast::{
    pool::{PrimitivePool, TermPool},
    Binder, Constant, Operator, ParamOperator, Rc as TRc, Term,
};
use rug::{Integer, Rational};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Unknown;

pub type R = Result<V, Unknown>;

type FreeVars = Rc<BTreeSet<(String, S)>>;

pub struct Evaluator<'a> {
    pub model: &'a mut Model,
    pool: &'a mut PrimitivePool,
    fuel: u64,
    sorts: HashMap<*const Term, S>,
    free: HashMap<*const Term, FreeVars>,
}

const MAX_QUANT_POINTS: usize = 1024;

impl<'a> Evaluator<'a> {
    pub fn new(model: &'a mut Model, pool: &'a mut PrimitivePool, fuel: u64) -> Self {
        Evaluator {
            model,
            pool,
            fuel,
            sorts: HashMap::new(),
            free: HashMap::new(),
        }
    }

    pub fn fuel_left(&self) -> u64 {
        self.fuel
    }

    pub fn sort_of(&mut self, t: &TRc<Term>) -> S {
        let key = TRc::as_ptr(t);
        if let Some(s) = self.sorts.get(&key) {
            return s.clone();
        }
        let s = S::from_sort(&self.pool.sort(t));
        self.sorts.insert(key, s.clone());
        s
    }

    pub fn eval_bool(&mut self, t: &TRc<Term>, env: &Env) -> Result<bool, Unknown> {
        match self.eval(t, env)? {
            V::Bool(b) => Ok(b),
            _ => Err(Unknown),
        }
    }

    pub fn eval(&mut self, t: &TRc<Term>, env: &Env) -> R {
        if self.fuel == 0 {
            return Err(Unknown);
        }
        self.fuel -= 1;
        match t.as_ref() {
            Term::Const(c) => match c {
                Constant::Integer(i) => Ok(V::Num(Rational::from(i.clone()))),
                Constant::Real(r) => Ok(V::Num(r.clone())),
                Constant::String(s) => Ok(V::string(s)),
                Constant::BitVec(v, w) => mkbv(v.clone(), *w),
                Constant::RegLan(..) => Err(Unknown),
            },
            Term::Var(name, sort) => {
                let s = S::from_sort(sort);
                if let Some(v) = env.lookup(name, &s) {
                    return Ok(v.clone());
                }
                // A free constructor or selector of a datatype denotes the datatype's own symbol.
                // Bound variables of the same name and sort were found in `env` above.
                if let S::Dt(_) | S::Fun(..) = s {
                    let table = self.model.datatypes.clone();
                    match table.symbol(name, &s) {
                        Err(_) => return Err(Unknown),
                        Ok(Some(DtSymbol::Ctor { datatype, ctor })) => {
                            let datatype: Rc<str> = Rc::from(datatype);
                            let ctor_name: Rc<str> = Rc::from(ctor.name.as_str());
                            return Ok(if ctor.fields.is_empty() {
                                V::Dt(Rc::new(DtV {
                                    datatype,
                                    ctor: ctor_name,
                                    fields: Vec::new(),
                                }))
                            } else {
                                V::Fun(Rc::new(FunV::Ctor {
                                    datatype,
                                    ctor: ctor_name,
                                    arity: ctor.fields.len(),
                                }))
                            });
                        }
                        Ok(Some(DtSymbol::Selector { ctor, index, .. })) => {
                            return Ok(V::Fun(Rc::new(FunV::Selector {
                                name: name.clone(),
                                sort: s,
                                ctor: Rc::from(ctor.name.as_str()),
                                index,
                            })));
                        }
                        Ok(None) => {}
                    }
                }
                if let S::Fun(..) = s {
                    if let Some(v) = self.model.fixed.get(&(name.clone(), s.clone())) {
                        return Ok(v.clone());
                    }
                    return Ok(V::Fun(Rc::new(FunV::Symbol {
                        name: name.clone(),
                        sort: s,
                    })));
                }
                if let S::Other(_) = s {
                    return Err(Unknown);
                }
                self.model.const_value(name, &s).ok_or(Unknown)
            }
            Term::App(f, args) => {
                let fv = self.eval(f, env)?;
                let mut vals = Vec::with_capacity(args.len());
                for a in args {
                    vals.push(self.eval(a, env)?);
                }
                self.apply(&fv, vals)
            }
            Term::Op(op, args) => self.eval_op(*op, args, env),
            Term::ParamOp { op, op_args, args } => self.eval_param_op(*op, op_args, args, env),
            Term::Binder(Binder::Lambda, bindings, body) => {
                let params = bindings
                    .iter()
                    .map(|(n, s)| (n.clone(), S::from_sort(s)))
                    .collect();
                Ok(V::Fun(Rc::new(FunV::Closure {
                    params,
                    body: body.clone(),
                    env: env.clone(),
                })))
            }
            Term::Binder(Binder::Choice, bindings, body) => {
                let [(name, sort)] = bindings.as_slice() else {
                    return Err(Unknown);
                };
                let s = S::from_sort(sort);
                let (dom, complete) = self.model.domain(&s);
                let mut witnesses = Vec::new();
                let mut unknown = false;
                for v in dom.iter() {
                    match self.eval_bool(body, &env.bind(name, s.clone(), v.clone())) {
                        Ok(true) => witnesses.push(v.clone()),
                        Ok(false) => {}
                        Err(_) => unknown = true,
                    }
                }
                if !witnesses.is_empty() {
                    Ok(self.model.choose(&s, witnesses))
                } else if complete && !unknown && !dom.is_empty() {
                    Ok(self.model.choose(&s, dom.to_vec()))
                } else {
                    Err(Unknown)
                }
            }
            Term::Binder(q, bindings, body) => {
                let is_forall = *q == Binder::Forall;
                let vars: Vec<(String, S)> = bindings
                    .iter()
                    .map(|(n, s)| (n.clone(), S::from_sort(s)))
                    .collect();
                self.quantify(is_forall, &vars, body, env)
            }
            Term::Let(bindings, body) => {
                let mut new_env = env.clone();
                for (name, value) in bindings.iter() {
                    let v = self.eval(value, env)?;
                    let s = self.sort_of(value);
                    new_env = new_env.bind(name, s, v);
                }
                self.eval(body, &new_env)
            }
            Term::Match(..) | Term::AsOp(..) => Err(Unknown),
        }
    }

    fn free_vars(&mut self, t: &TRc<Term>) -> FreeVars {
        let key = TRc::as_ptr(t);
        if let Some(f) = self.free.get(&key) {
            return f.clone();
        }
        let mut set = BTreeSet::new();
        match t.as_ref() {
            Term::Const(_) => {}
            Term::Var(name, sort) => {
                set.insert((name.clone(), S::from_sort(sort)));
            }
            Term::App(f, args) => {
                set.extend(self.free_vars(f).iter().cloned());
                for a in args {
                    set.extend(self.free_vars(a).iter().cloned());
                }
            }
            Term::Op(_, args) | Term::ParamOp { args, .. } | Term::AsOp(_, _, args) => {
                for a in args {
                    set.extend(self.free_vars(a).iter().cloned());
                }
            }
            Term::Binder(_, bindings, body) => {
                set.extend(self.free_vars(body).iter().cloned());
                for (n, s) in bindings.iter() {
                    set.remove(&(n.clone(), S::from_sort(s)));
                }
            }
            Term::Let(bindings, body) => {
                set.extend(self.free_vars(body).iter().cloned());
                let mut bound = Vec::new();
                for (n, v) in bindings.iter() {
                    let s = self.sort_of(v);
                    bound.push((n.clone(), s));
                }
                for b in &bound {
                    set.remove(b);
                }
                for (_, v) in bindings.iter() {
                    set.extend(self.free_vars(v).iter().cloned());
                }
            }
            Term::Match(scrutinee, cases) => {
                set.extend(self.free_vars(scrutinee).iter().cloned());
                for case in cases {
                    set.extend(self.free_vars(&case.body).iter().cloned());
                }
            }
        }
        let set = Rc::new(set);
        self.free.insert(key, set.clone());
        set
    }

    fn quantify(
        &mut self,
        is_forall: bool,
        vars: &[(String, S)],
        body: &TRc<Term>,
        env: &Env,
    ) -> R {
        let free = self.free_vars(body);
        // A binder whose variable does not occur is irrelevant (every sort is non-empty).
        let used: Vec<&(String, S)> = vars.iter().filter(|v| free.contains(*v)).collect();
        // Later bindings shadow earlier ones with the same name.
        let mut seen = BTreeSet::new();
        let mut effective = Vec::new();
        for v in used.iter().rev() {
            if seen.insert(v.0.clone()) {
                effective.push((*v).clone());
            }
        }
        effective.reverse();
        let mut doms = Vec::new();
        let mut complete = true;
        for (_, s) in &effective {
            let (d, c) = self.model.domain(s);
            if d.is_empty() {
                return Err(Unknown);
            }
            complete &= c;
            doms.push(d);
        }
        let total: f64 = doms.iter().map(|d| d.len() as f64).product();
        if total > MAX_QUANT_POINTS as f64 {
            complete = false;
        }
        let points = product(&doms);
        let mut unknown = false;
        for p in points.iter().take(MAX_QUANT_POINTS) {
            let mut e = env.clone();
            for ((name, s), v) in effective.iter().zip(p) {
                e = e.bind(name, s.clone(), v.clone());
            }
            match self.eval_bool(body, &e) {
                Ok(b) if b != is_forall => return Ok(V::Bool(!is_forall)),
                Ok(_) => {}
                Err(_) => unknown = true,
            }
        }
        if complete && !unknown {
            Ok(V::Bool(is_forall))
        } else {
            Err(Unknown)
        }
    }

    pub fn apply(&mut self, f: &V, args: Vec<V>) -> R {
        let V::Fun(fv) = f else { return Err(Unknown) };
        match fv.as_ref() {
            FunV::Closure { params, body, env } => {
                if args.len() < params.len() {
                    // Partial application: bind the supplied arguments (already evaluated in the
                    // caller's environment, so nothing can be captured) and keep the rest.
                    let supplied = args.len();
                    let mut e = env.clone();
                    for ((n, s), v) in params.iter().zip(args) {
                        e = e.bind(n, s.clone(), v);
                    }
                    let remaining = params[supplied..].to_vec();
                    Ok(V::Fun(Rc::new(FunV::Closure {
                        params: remaining,
                        body: body.clone(),
                        env: e,
                    })))
                } else {
                    let mut e = env.clone();
                    let (now, later) = args.split_at(params.len());
                    for ((n, s), v) in params.iter().zip(now) {
                        e = e.bind(n, s.clone(), v.clone());
                    }
                    let r = self.eval(body, &e)?;
                    if later.is_empty() {
                        Ok(r)
                    } else {
                        self.apply(&r, later.to_vec())
                    }
                }
            }
            FunV::Symbol { name, sort } => {
                let S::Fun(arg_sorts, _) = sort else {
                    return Err(Unknown);
                };
                let n = arg_sorts.len();
                if args.len() < n {
                    Ok(V::Fun(Rc::new(FunV::Partial {
                        base: fv.clone(),
                        applied: args,
                    })))
                } else {
                    let (now, later) = args.split_at(n);
                    let r = self
                        .model
                        .apply_symbol(name, sort, now.to_vec())
                        .ok_or(Unknown)?;
                    if later.is_empty() {
                        Ok(r)
                    } else {
                        self.apply(&r, later.to_vec())
                    }
                }
            }
            FunV::Table { map, default } => {
                let arity = map.keys().next().map(Vec::len).unwrap_or(args.len());
                if args.len() < arity {
                    return Ok(V::Fun(Rc::new(FunV::Partial {
                        base: fv.clone(),
                        applied: args,
                    })));
                }
                let (now, later) = args.split_at(arity);
                if now.iter().any(V::has_fun) {
                    return Err(Unknown);
                }
                let r = map.get(now).cloned().unwrap_or_else(|| default.clone());
                if later.is_empty() {
                    Ok(r)
                } else {
                    self.apply(&r, later.to_vec())
                }
            }
            FunV::Partial { base, applied } => {
                let mut all = applied.clone();
                all.extend(args);
                self.apply(&V::Fun(base.clone()), all)
            }
            FunV::Ctor { datatype, ctor, arity } => match args.len().cmp(arity) {
                std::cmp::Ordering::Less => Ok(V::Fun(Rc::new(FunV::Partial {
                    base: fv.clone(),
                    applied: args,
                }))),
                std::cmp::Ordering::Equal => Ok(V::Dt(Rc::new(DtV {
                    datatype: datatype.clone(),
                    ctor: ctor.clone(),
                    fields: args,
                }))),
                // A datatype value is never a function.
                std::cmp::Ordering::Greater => Err(Unknown),
            },
            FunV::Selector { name, sort, ctor, index } => match args.as_slice() {
                [] => Ok(V::Fun(fv.clone())),
                [V::Dt(d)] if d.ctor == *ctor => d.fields.get(*index).cloned().ok_or(Unknown),
                // Another constructor's value: unspecified, so a free (but functional) choice.
                [V::Dt(_)] => self
                    .model
                    .apply_symbol(name, sort, args.clone())
                    .ok_or(Unknown),
                _ => Err(Unknown),
            },
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Operators
// ---------------------------------------------------------------------------------------------

fn num(v: &V) -> Result<&Rational, Unknown> {
    match v {
        V::Num(r) => Ok(r),
        _ => Err(Unknown),
    }
}

fn int(v: &V) -> Result<Integer, Unknown> {
    match v {
        V::Num(r) if r.is_integer() => Ok(r.numer().clone()),
        _ => Err(Unknown),
    }
}

fn bv(v: &V) -> Result<(&Integer, usize), Unknown> {
    match v {
        V::Bv(x, w) => Ok((x, *w)),
        _ => Err(Unknown),
    }
}

fn string(v: &V) -> Result<&[u32], Unknown> {
    match v {
        V::Str(s) => Ok(s.as_slice()),
        _ => Err(Unknown),
    }
}

fn re(v: &V) -> Result<&Re, Unknown> {
    match v {
        V::Re(r) => Ok(r),
        _ => Err(Unknown),
    }
}

fn str_v(s: Vec<u32>) -> V {
    V::Str(Rc::new(s))
}

// Bit-vector arithmetic at any width. Every width and bit index is a `usize`, and none is cast to
// `u32` unless it is known to fit: a value `x` in `[0, 2^w)` with its top bit set has exactly `w`
// significant bits, so its width fits wherever the value itself does. Where a result needs a
// `2^w` beyond `MAX_MATERIALIZED_BV_WIDTH`, the answer is `Unknown`, never a truncated width.

/// The bit-vector value `x mod 2^w`, or `Unknown` if that needs a `2^w` beyond the bound.
fn mkbv(x: Integer, w: usize) -> R {
    V::try_bv(x, w).ok_or(Unknown)
}

fn reduce(x: Integer, w: usize) -> Result<Integer, Unknown> {
    bv_reduce(x, w).ok_or(Unknown)
}

fn modulus(w: usize) -> Result<Integer, Unknown> {
    if w > MAX_MATERIALIZED_BV_WIDTH {
        return Err(Unknown);
    }
    Ok(Integer::from(1) << w as u32)
}

fn bits(x: &Integer) -> usize {
    x.significant_bits() as usize
}

/// Bit `i` of a non-negative `x`.
fn bit(x: &Integer, i: usize) -> bool {
    i < bits(x) && x.get_bit(i as u32)
}

/// `x * 2^k`, or `Unknown` if the result would be wider than twice the materialization bound.
fn shl(x: &Integer, k: usize) -> Result<Integer, Unknown> {
    if *x == 0 {
        return Ok(Integer::new());
    }
    if bits(x).saturating_add(k) > 2 * MAX_MATERIALIZED_BV_WIDTH {
        return Err(Unknown);
    }
    Ok(x.clone() << k as u32)
}

/// `floor(x / 2^k)`, for any sign of `x`.
fn shr(x: &Integer, k: usize) -> Integer {
    if k >= bits(x) {
        if *x < 0 {
            Integer::from(-1)
        } else {
            Integer::new()
        }
    } else {
        x.clone() >> k as u32
    }
}

fn msb(x: &Integer, w: usize) -> bool {
    w > 0 && bits(x) == w
}

fn to_signed(x: &Integer, w: usize) -> Integer {
    if msb(x, w) {
        // `w` is `x`'s own bit count, so it fits in a `u32`
        x.clone() - (Integer::from(1) << w as u32)
    } else {
        x.clone()
    }
}

fn bv_neg(x: &Integer, w: usize) -> Result<Integer, Unknown> {
    if *x == 0 {
        return Ok(Integer::new());
    }
    Ok(modulus(w)? - x.clone())
}

fn bv_udiv(s: &Integer, t: &Integer, w: usize) -> Result<Integer, Unknown> {
    Ok(if *t == 0 {
        modulus(w)? - 1
    } else {
        s.clone() / t.clone()
    })
}

fn bv_urem(s: &Integer, t: &Integer) -> Integer {
    if *t == 0 {
        s.clone()
    } else {
        s.clone() % t.clone()
    }
}

/// SMT-LIB `bvsdiv`, `bvsrem` and `bvsmod`, transcribed from the FixedSizeBitVectors logic.
fn bv_signed_divrem(op: Operator, s: &Integer, t: &Integer, w: usize) -> Result<Integer, Unknown> {
    let (ms, mt) = (msb(s, w), msb(t, w));
    let abs_s = if ms { bv_neg(s, w)? } else { s.clone() };
    let abs_t = if mt { bv_neg(t, w)? } else { t.clone() };
    Ok(match op {
        Operator::BvSDiv => {
            let q = bv_udiv(&abs_s, &abs_t, w)?;
            if ms == mt {
                q
            } else {
                bv_neg(&q, w)?
            }
        }
        Operator::BvSRem => {
            let r = bv_urem(&abs_s, &abs_t);
            if ms {
                bv_neg(&r, w)?
            } else {
                r
            }
        }
        Operator::BvSMod => {
            let u = bv_urem(&abs_s, &abs_t);
            if u == 0 || (!ms && !mt) {
                u
            } else if ms && !mt {
                reduce(bv_neg(&u, w)? + t.clone(), w)?
            } else if !ms && mt {
                reduce(u + t.clone(), w)?
            } else {
                bv_neg(&u, w)?
            }
        }
        _ => unreachable!(),
    })
}

fn index_of(hay: &[u32], needle: &[u32], from: usize) -> Option<usize> {
    if from > hay.len() {
        return None;
    }
    (from..=hay.len().saturating_sub(needle.len()))
        .find(|&j| j + needle.len() <= hay.len() && &hay[j..j + needle.len()] == needle)
}

fn usize_of(i: &Integer) -> Option<usize> {
    i.to_usize()
}

impl Evaluator<'_> {
    fn eval_args(&mut self, args: &[TRc<Term>], env: &Env) -> Result<Vec<V>, Unknown> {
        args.iter().map(|a| self.eval(a, env)).collect()
    }

    /// Three-valued equality. Values without functions compare structurally (their
    /// representations are canonical); function values compare extensionally.
    fn values_equal(&mut self, a: &V, b: &V, sort: &S) -> Result<bool, Unknown> {
        if !a.has_fun() && !b.has_fun() {
            return Ok(a == b);
        }
        let (V::Fun(_), V::Fun(_), S::Fun(arg_sorts, ret)) = (a, b, sort) else {
            return Err(Unknown);
        };
        let mut doms = Vec::new();
        let mut complete = true;
        for s in arg_sorts {
            let (d, c) = self.model.domain(s);
            complete &= c;
            doms.push(d);
        }
        let points = product(&doms);
        if points.len() > MAX_QUANT_POINTS {
            complete = false;
        }
        let mut unknown = false;
        for p in points.into_iter().take(MAX_QUANT_POINTS) {
            let (x, y) = match (self.apply(a, p.clone()), self.apply(b, p)) {
                (Ok(x), Ok(y)) => (x, y),
                _ => {
                    unknown = true;
                    continue;
                }
            };
            match self.values_equal(&x, &y, ret) {
                Ok(false) => return Ok(false),
                Ok(true) => {}
                Err(_) => unknown = true,
            }
        }
        if complete && !unknown {
            Ok(true)
        } else {
            Err(Unknown)
        }
    }

    fn eval_op(&mut self, op: Operator, args: &[TRc<Term>], env: &Env) -> R {
        use Operator::*;
        match op {
            True => return Ok(V::Bool(true)),
            False => return Ok(V::Bool(false)),
            Not => return Ok(V::Bool(!self.eval_bool(&args[0], env)?)),
            And | Or => {
                let short = op == Or;
                let mut unknown = false;
                for a in args {
                    match self.eval_bool(a, env) {
                        Ok(b) if b == short => return Ok(V::Bool(short)),
                        Ok(_) => {}
                        Err(_) => unknown = true,
                    }
                }
                return if unknown {
                    Err(Unknown)
                } else {
                    Ok(V::Bool(!short))
                };
            }
            Implies => {
                // (=> a b c) is (or (not a) (not b) c)
                let mut unknown = false;
                let (last, init) = args.split_last().ok_or(Unknown)?;
                for a in init {
                    match self.eval_bool(a, env) {
                        Ok(false) => return Ok(V::Bool(true)),
                        Ok(true) => {}
                        Err(_) => unknown = true,
                    }
                }
                match self.eval_bool(last, env) {
                    Ok(true) => return Ok(V::Bool(true)),
                    Ok(false) => {}
                    Err(_) => unknown = true,
                }
                return if unknown {
                    Err(Unknown)
                } else {
                    Ok(V::Bool(false))
                };
            }
            Ite => {
                return match self.eval_bool(&args[0], env) {
                    Ok(true) => self.eval(&args[1], env),
                    Ok(false) => self.eval(&args[2], env),
                    Err(_) => {
                        let a = self.eval(&args[1], env)?;
                        let b = self.eval(&args[2], env)?;
                        let s = self.sort_of(&args[1]);
                        if self.values_equal(&a, &b, &s)? {
                            Ok(a)
                        } else {
                            Err(Unknown)
                        }
                    }
                };
            }
            Equals | Distinct => {
                let vals = self.eval_args(args, env)?;
                let s = self.sort_of(&args[0]);
                if op == Equals {
                    for w in vals.windows(2) {
                        if !self.values_equal(&w[0], &w[1], &s)? {
                            return Ok(V::Bool(false));
                        }
                    }
                    return Ok(V::Bool(true));
                }
                for i in 0..vals.len() {
                    for j in i + 1..vals.len() {
                        if self.values_equal(&vals[i], &vals[j], &s)? {
                            return Ok(V::Bool(false));
                        }
                    }
                }
                return Ok(V::Bool(true));
            }
            _ => {}
        }
        let vals = self.eval_args(args, env)?;
        let v0 = vals.first();
        Ok(match op {
            Xor => {
                let mut acc = false;
                for v in &vals {
                    acc ^= v.as_bool().ok_or(Unknown)?;
                }
                V::Bool(acc)
            }
            Add | Mult => {
                let mut acc = num(&vals[0])?.clone();
                for v in &vals[1..] {
                    if op == Add {
                        acc += num(v)?;
                    } else {
                        acc *= num(v)?;
                    }
                }
                V::Num(acc)
            }
            Sub if vals.len() == 1 => V::Num(-num(&vals[0])?.clone()),
            Sub => {
                let mut acc = num(&vals[0])?.clone();
                for v in &vals[1..] {
                    acc -= num(v)?;
                }
                V::Num(acc)
            }
            RealDiv => {
                let mut acc = num(&vals[0])?.clone();
                for v in &vals[1..] {
                    let d = num(v)?;
                    acc = if *d == 0 {
                        num(&self.model.div_by_zero(0, &acc).ok_or(Unknown)?)?.clone()
                    } else {
                        acc / d.clone()
                    };
                }
                V::Num(acc)
            }
            IntDiv => {
                let mut acc = int(&vals[0])?;
                for v in &vals[1..] {
                    let d = int(v)?;
                    acc = if d == 0 {
                        int(&self
                            .model
                            .div_by_zero(1, &Rational::from(acc))
                            .ok_or(Unknown)?)?
                    } else {
                        acc.div_rem_euc(d).0
                    };
                }
                V::Num(Rational::from(acc))
            }
            Mod => {
                let (a, b) = (int(&vals[0])?, int(&vals[1])?);
                if b == 0 {
                    self.model
                        .div_by_zero(2, &Rational::from(a))
                        .ok_or(Unknown)?
                } else {
                    V::Num(Rational::from(a.div_rem_euc(b).1))
                }
            }
            Abs => V::Num(num(&vals[0])?.clone().abs()),
            LessThan | GreaterThan | LessEq | GreaterEq => {
                let mut ok = true;
                for w in vals.windows(2) {
                    let (a, b) = (num(&w[0])?, num(&w[1])?);
                    ok &= match op {
                        LessThan => a < b,
                        GreaterThan => a > b,
                        LessEq => a <= b,
                        _ => a >= b,
                    };
                }
                V::Bool(ok)
            }
            ToReal => V::Num(num(&vals[0])?.clone()),
            ToInt => V::Num(Rational::from(num(&vals[0])?.clone().floor())),
            IsInt => V::Bool(num(&vals[0])?.is_integer()),
            Pow2 => {
                let x = int(&vals[0])?;
                let e = x.to_u32().filter(|e| *e <= 256).ok_or(Unknown)?;
                V::Num(Rational::from(Integer::from(1) << e))
            }
            Log2 => {
                let x = int(&vals[0])?;
                if x <= 0 {
                    return Err(Unknown);
                }
                V::Num(Rational::from(x.significant_bits() - 1))
            }
            IsPow2 => {
                let x = int(&vals[0])?;
                if x <= 0 {
                    return Err(Unknown);
                }
                V::Bool(x.is_power_of_two())
            }
            RealPi | Sqrt | Exp | Sin | Cos | Tan | Csc | Sec | Cot | Arcsin | Arccos | Arctan
            | Arccsc | Arcsec | Arccot => return Err(Unknown),

            Select => match &vals[0] {
                V::Arr(a) => {
                    if vals[1].has_fun() {
                        return Err(Unknown);
                    }
                    a.select(&vals[1])
                }
                _ => return Err(Unknown),
            },
            Store => match &vals[0] {
                V::Arr(a) => {
                    if vals[1].has_fun() || vals[2].has_fun() {
                        return Err(Unknown);
                    }
                    let S::Array(isort, _) = self.sort_of(&args[0]) else {
                        return Err(Unknown);
                    };
                    let (idom, complete) = self.model.domain(&isort);
                    let mut entries = a.entries.clone();
                    entries.insert(vals[1].clone(), vals[2].clone());
                    V::Arr(Rc::new(ArrV::canon(
                        a.default.clone(),
                        entries,
                        if complete { Some(&idom) } else { None },
                    )))
                }
                _ => return Err(Unknown),
            },

            // Strings
            StrConcat => {
                let mut out = Vec::new();
                for v in &vals {
                    out.extend_from_slice(string(v)?);
                }
                str_v(out)
            }
            StrLen => V::Num(Rational::from(string(&vals[0])?.len())),
            StrLessThan | StrLessEq => {
                let mut ok = true;
                for w in vals.windows(2) {
                    let (a, b) = (string(&w[0])?, string(&w[1])?);
                    ok &= if op == StrLessThan { a < b } else { a <= b };
                }
                V::Bool(ok)
            }
            CharAt => {
                let s = string(&vals[0])?;
                let i = int(&vals[1])?;
                match usize_of(&i) {
                    Some(i) if i < s.len() => str_v(vec![s[i]]),
                    _ => str_v(Vec::new()),
                }
            }
            Substring => {
                let s = string(&vals[0])?;
                let (i, n) = (int(&vals[1])?, int(&vals[2])?);
                match (usize_of(&i), usize_of(&n)) {
                    (Some(i), Some(n)) if i < s.len() && n > 0 => {
                        str_v(s[i..(i.saturating_add(n)).min(s.len())].to_vec())
                    }
                    _ => str_v(Vec::new()),
                }
            }
            PrefixOf => {
                let (a, b) = (string(&vals[0])?, string(&vals[1])?);
                V::Bool(b.starts_with(a))
            }
            SuffixOf => {
                let (a, b) = (string(&vals[0])?, string(&vals[1])?);
                V::Bool(b.ends_with(a))
            }
            Contains => {
                let (a, b) = (string(&vals[0])?, string(&vals[1])?);
                V::Bool(index_of(a, b, 0).is_some())
            }
            IndexOf => {
                let (s, t) = (string(&vals[0])?, string(&vals[1])?);
                let i = int(&vals[2])?;
                let r = match usize_of(&i) {
                    Some(i) if i <= s.len() => index_of(s, t, i).map(|j| j as i64).unwrap_or(-1),
                    _ => -1,
                };
                V::int(r)
            }
            Replace => {
                let (s, t, u) = (string(&vals[0])?, string(&vals[1])?, string(&vals[2])?);
                if t.is_empty() {
                    let mut out = u.to_vec();
                    out.extend_from_slice(s);
                    str_v(out)
                } else {
                    match index_of(s, t, 0) {
                        Some(j) => {
                            let mut out = s[..j].to_vec();
                            out.extend_from_slice(u);
                            out.extend_from_slice(&s[j + t.len()..]);
                            str_v(out)
                        }
                        None => str_v(s.to_vec()),
                    }
                }
            }
            ReplaceAll => {
                let (s, t, u) = (string(&vals[0])?, string(&vals[1])?, string(&vals[2])?);
                if t.is_empty() {
                    str_v(s.to_vec())
                } else {
                    let mut out = Vec::new();
                    let mut i = 0;
                    while i < s.len() {
                        if i + t.len() <= s.len() && &s[i..i + t.len()] == t {
                            out.extend_from_slice(u);
                            i += t.len();
                        } else {
                            out.push(s[i]);
                            i += 1;
                        }
                    }
                    str_v(out)
                }
            }
            StrIsDigit => {
                let s = string(&vals[0])?;
                V::Bool(s.len() == 1 && (('0' as u32)..=('9' as u32)).contains(&s[0]))
            }
            StrToCode => {
                let s = string(&vals[0])?;
                V::int(if s.len() == 1 { s[0] as i64 } else { -1 })
            }
            StrFromCode => {
                let n = int(&vals[0])?;
                match n.to_u32() {
                    Some(c) if c <= 0x2FFFF => str_v(vec![c]),
                    _ => str_v(Vec::new()),
                }
            }
            StrToInt => {
                let s = string(&vals[0])?;
                if s.is_empty() || !s.iter().all(|c| (('0' as u32)..=('9' as u32)).contains(c)) {
                    V::int(-1)
                } else {
                    let text: String = s.iter().map(|c| char::from_u32(*c).unwrap()).collect();
                    V::Num(Rational::from(
                        Integer::from_str_radix(&text, 10).map_err(|_| Unknown)?,
                    ))
                }
            }
            StrFromInt => {
                let n = int(&vals[0])?;
                if n < 0 {
                    str_v(Vec::new())
                } else {
                    str_v(n.to_string().chars().map(|c| c as u32).collect())
                }
            }
            StrToRe => V::Re(Rc::new(Re::Lit(string(&vals[0])?.to_vec()))),
            StrInRe => V::Bool(re(&vals[1])?.matches(string(&vals[0])?)),
            ReNone => V::Re(Rc::new(Re::None)),
            ReAll => V::Re(Rc::new(Re::all())),
            ReAllChar => V::Re(Rc::new(Re::AllChar)),
            ReConcat => V::Re(Rc::new(Re::Concat(
                vals.iter()
                    .map(|v| re(v).cloned())
                    .collect::<Result<_, _>>()?,
            ))),
            ReUnion => V::Re(Rc::new(Re::Union(
                vals.iter()
                    .map(|v| re(v).cloned())
                    .collect::<Result<_, _>>()?,
            ))),
            ReIntersection => V::Re(Rc::new(Re::Inter(
                vals.iter()
                    .map(|v| re(v).cloned())
                    .collect::<Result<_, _>>()?,
            ))),
            ReDiff => {
                let mut acc = re(&vals[0])?.clone();
                for v in &vals[1..] {
                    acc = Re::Inter(vec![acc, Re::Comp(Box::new(re(v)?.clone()))]);
                }
                V::Re(Rc::new(acc))
            }
            ReKleeneClosure => V::Re(Rc::new(Re::Star(Box::new(re(&vals[0])?.clone())))),
            ReKleeneCross => {
                let r = re(&vals[0])?.clone();
                V::Re(Rc::new(Re::Concat(vec![r.clone(), Re::Star(Box::new(r))])))
            }
            ReOption => V::Re(Rc::new(Re::Union(vec![Re::Eps, re(&vals[0])?.clone()]))),
            ReComplement => V::Re(Rc::new(Re::Comp(Box::new(re(&vals[0])?.clone())))),
            ReRange => {
                let (a, b) = (string(&vals[0])?, string(&vals[1])?);
                if a.len() == 1 && b.len() == 1 {
                    V::Re(Rc::new(Re::Range(a[0], b[0])))
                } else {
                    V::Re(Rc::new(Re::None))
                }
            }
            IndexOfRe | ReplaceRe | ReplaceReAll | ReFromAutomaton => return Err(Unknown),

            // Bit-vectors
            BvNot => {
                let (x, w) = bv(&vals[0])?;
                mkbv(modulus(w)? - 1 - x.clone(), w)?
            }
            BvNeg => {
                let (x, w) = bv(&vals[0])?;
                mkbv(bv_neg(x, w)?, w)?
            }
            BvAnd | BvOr | BvXor | BvAdd | BvMul => {
                let (first, w) = bv(&vals[0])?;
                let mut acc = first.clone();
                for v in &vals[1..] {
                    let (x, _) = bv(v)?;
                    acc = match op {
                        BvAnd => acc & x,
                        BvOr => acc | x,
                        BvXor => acc ^ x,
                        BvAdd => reduce(acc + x, w)?,
                        _ => reduce(acc * x, w)?,
                    };
                }
                mkbv(acc, w)?
            }
            BvNAnd | BvNOr | BvXNor => {
                let ((x, w), (y, _)) = (bv(&vals[0])?, bv(&vals[1])?);
                let inner = match op {
                    BvNAnd => x.clone() & y,
                    BvNOr => x.clone() | y,
                    _ => x.clone() ^ y,
                };
                mkbv(modulus(w)? - 1 - inner, w)?
            }
            BvSub => {
                let ((x, w), (y, _)) = (bv(&vals[0])?, bv(&vals[1])?);
                mkbv(x.clone() - y, w)?
            }
            BvUDiv => {
                let ((x, w), (y, _)) = (bv(&vals[0])?, bv(&vals[1])?);
                mkbv(bv_udiv(x, y, w)?, w)?
            }
            BvURem => {
                let ((x, w), (y, _)) = (bv(&vals[0])?, bv(&vals[1])?);
                mkbv(bv_urem(x, y), w)?
            }
            BvSDiv | BvSRem | BvSMod => {
                let ((x, w), (y, _)) = (bv(&vals[0])?, bv(&vals[1])?);
                mkbv(bv_signed_divrem(op, x, y, w)?, w)?
            }
            BvShl | BvLShr | BvAShr => {
                let ((x, w), (y, _)) = (bv(&vals[0])?, bv(&vals[1])?);
                let shift = match y.to_usize() {
                    Some(s) if s < w => s,
                    _ => w,
                };
                let r = match op {
                    BvShl => {
                        if shift >= w {
                            Integer::new()
                        } else {
                            shl(x, shift)?
                        }
                    }
                    BvLShr => {
                        if shift >= w {
                            Integer::new()
                        } else {
                            shr(x, shift)
                        }
                    }
                    _ => {
                        let signed = to_signed(x, w);
                        if shift >= w {
                            if signed < 0 {
                                Integer::from(-1)
                            } else {
                                Integer::new()
                            }
                        } else {
                            shr(&signed, shift)
                        }
                    }
                };
                mkbv(r, w)?
            }
            BvULt | BvULe | BvUGt | BvUGe => {
                let ((x, _), (y, _)) = (bv(&vals[0])?, bv(&vals[1])?);
                V::Bool(match op {
                    BvULt => x < y,
                    BvULe => x <= y,
                    BvUGt => x > y,
                    _ => x >= y,
                })
            }
            BvSLt | BvSLe | BvSGt | BvSGe => {
                let ((x, w), (y, _)) = (bv(&vals[0])?, bv(&vals[1])?);
                let (x, y) = (to_signed(x, w), to_signed(y, w));
                V::Bool(match op {
                    BvSLt => x < y,
                    BvSLe => x <= y,
                    BvSGt => x > y,
                    _ => x >= y,
                })
            }
            BvConcat => {
                let mut acc = Integer::new();
                let mut width = 0;
                for v in &vals {
                    let (x, w) = bv(v)?;
                    acc = shl(&acc, w)? + x;
                    width = usize::checked_add(width, w).ok_or(Unknown)?;
                }
                mkbv(acc, width)?
            }
            BvComp => {
                let ((x, _), (y, _)) = (bv(&vals[0])?, bv(&vals[1])?);
                mkbv(Integer::from(u8::from(x == y)), 1)?
            }
            UBvToInt => V::Num(Rational::from(bv(&vals[0])?.0.clone())),
            SBvToInt => {
                let (x, w) = bv(&vals[0])?;
                V::Num(Rational::from(to_signed(x, w)))
            }
            BvSize => V::int(bv(&vals[0])?.1 as i64),
            BvConst => {
                let (value, width) = (int(&vals[0])?, int(&vals[1])?);
                let width = width.to_usize().filter(|w| *w > 0).ok_or(Unknown)?;
                mkbv(value, width)?
            }
            BvBbTerm => {
                let mut acc = Integer::new();
                for (i, v) in vals.iter().enumerate() {
                    if v.as_bool().ok_or(Unknown)? {
                        acc.set_bit(i as u32, true);
                    }
                }
                mkbv(acc, vals.len())?
            }
            BvPBbTerm => {
                // Only 0/1 pseudo-Boolean bits have a meaning.
                let mut acc = Integer::new();
                for (i, v) in vals.iter().enumerate() {
                    let b = int(v)?;
                    if b == 1 {
                        acc.set_bit(i as u32, true);
                    } else if b != 0 {
                        return Err(Unknown);
                    }
                }
                mkbv(acc, vals.len())?
            }
            RareList | Cl | Delete => return Err(Unknown),
            SetUnion | SetInter | SetMinus | SetMember | SetSubset | SetSingleton | SetIsEmpty
            | SetIsSingleton | SetCard | SetInsert | SetComplement | Tuple | TupleUnit
            | RelTranspose | RelTclosure | RelJoin | RelProduct => return Err(Unknown),
            True | False | Not | And | Or | Implies | Ite | Equals | Distinct => unreachable!(),
        })
        .map(|v| {
            let _ = v0;
            v
        })
    }

    fn eval_param_op(
        &mut self,
        op: ParamOperator,
        op_args: &[TRc<Term>],
        args: &[TRc<Term>],
        env: &Env,
    ) -> R {
        use ParamOperator::*;
        let idx: Vec<Integer> = op_args
            .iter()
            .map(|a| match a.as_ref() {
                Term::Const(Constant::Integer(i)) => Ok(i.clone()),
                _ => Err(Unknown),
            })
            .collect::<Result<_, _>>()
            .or_else(|e| {
                if matches!(op, Tester | TupleSelect) {
                    Ok(Vec::new())
                } else {
                    Err(e)
                }
            })?;
        let small = |k: usize| idx.get(k).and_then(|i| i.to_usize()).ok_or(Unknown);
        let vals = self.eval_args(args, env)?;
        Ok(match op {
            BvExtract => {
                let (i, j) = (small(0)?, small(1)?);
                let (x, w) = bv(&vals[0])?;
                if !(j <= i && i < w) {
                    return Err(Unknown);
                }
                mkbv(shr(x, j), i - j + 1)?
            }
            BvBitOf => {
                let i = small(0)?;
                let (x, w) = bv(&vals[0])?;
                if i >= w {
                    return Err(Unknown);
                }
                V::Bool(bit(x, i))
            }
            BvIntOf => {
                let i = small(0)?;
                let (x, w) = bv(&vals[0])?;
                if i >= w {
                    return Err(Unknown);
                }
                V::int(i64::from(bit(x, i)))
            }
            ZeroExtend => {
                let k = small(0)?;
                let (x, w) = bv(&vals[0])?;
                mkbv(x.clone(), w.checked_add(k).ok_or(Unknown)?)?
            }
            SignExtend => {
                let k = small(0)?;
                let (x, w) = bv(&vals[0])?;
                mkbv(to_signed(x, w), w.checked_add(k).ok_or(Unknown)?)?
            }
            RotateLeft | RotateRight => {
                let k = small(0)?;
                let (x, w) = bv(&vals[0])?;
                let k = k % w;
                let left = if op == RotateLeft { k } else { (w - k) % w };
                let r = shl(x, left)? | shr(x, w - left);
                mkbv(r, w)?
            }
            Repeat => {
                let n = small(0)?;
                let (x, w) = bv(&vals[0])?;
                if n == 0 {
                    return Err(Unknown);
                }
                let width = w.checked_mul(n).ok_or(Unknown)?;
                if *x != 0 && width > 2 * MAX_MATERIALIZED_BV_WIDTH {
                    return Err(Unknown);
                }
                let mut acc = Integer::new();
                if *x != 0 {
                    for _ in 0..n {
                        acc = shl(&acc, w)? + x;
                    }
                }
                mkbv(acc, width)?
            }
            BvConst => {
                let width = small(1)?;
                if width == 0 {
                    return Err(Unknown);
                }
                mkbv(idx[0].clone(), width)?
            }
            IntToBv => {
                let width = small(0)?;
                if width == 0 {
                    return Err(Unknown);
                }
                mkbv(int(&vals[0])?, width)?
            }
            RePower => {
                let n = idx.first().and_then(|i| i.to_u32()).ok_or(Unknown)?;
                V::Re(Rc::new(Re::Loop(Box::new(re(&vals[0])?.clone()), n, n)))
            }
            ReLoop => {
                let lo = idx.first().and_then(|i| i.to_u32()).ok_or(Unknown)?;
                let hi = idx.get(1).and_then(|i| i.to_u32()).ok_or(Unknown)?;
                V::Re(Rc::new(Re::Loop(Box::new(re(&vals[0])?.clone()), lo, hi)))
            }
            Tester => {
                // `((_ is C) t)`: `C` must be a free constructor symbol (not one a binder rebinds).
                let Some(Term::Var(cname, csort)) = op_args.first().map(|t| t.as_ref()) else {
                    return Err(Unknown);
                };
                let cs = S::from_sort(csort);
                if env.lookup(cname, &cs).is_some() {
                    return Err(Unknown);
                }
                let table = self.model.datatypes.clone();
                match (table.symbol(cname, &cs), vals.first()) {
                    (Ok(Some(DtSymbol::Ctor { datatype, .. })), Some(V::Dt(d)))
                        if *d.datatype == *datatype =>
                    {
                        V::Bool(*d.ctor == **cname)
                    }
                    _ => return Err(Unknown),
                }
            }
            TupleSelect => return Err(Unknown),
        })
    }
}

#[allow(dead_code)]
fn _unused(_: BTreeMap<u8, u8>) {}

#[cfg(test)]
mod tests {
    use super::{Evaluator, Unknown};
    use crate::datatypes::DtTable;
    use crate::model::{Model, Vocab};
    use crate::value::{Env, V};
    use carcara::parser;
    use rug::Integer;
    use std::rc::Rc;

    /// Evaluates every `assert`ed term of `problem` in `models` random models.
    fn eval_all(problem: &str, models: u64) -> Vec<Result<bool, Unknown>> {
        let (problem, _, _, mut pool) =
            parser::parse_instance(problem, "", None, parser::Config::new()).expect("parse");
        let datatypes = Rc::new(DtTable::from_terms(&pool, problem.premises.iter()));
        let mut out = Vec::new();
        for seed in 0..models {
            let mut model = Model::new(seed, Rc::new(Vocab::default()));
            model.datatypes = datatypes.clone();
            let mut ev = Evaluator::new(&mut model, &mut pool, 1_000_000);
            for t in &problem.premises {
                out.push(ev.eval_bool(t, &Env::new()));
            }
        }
        out
    }

    fn always(problem: &str) {
        for r in eval_all(problem, 20) {
            assert_eq!(r, Ok(true), "{}", problem);
        }
    }

    fn sometimes_false(problem: &str) {
        assert!(eval_all(problem, 60).contains(&Ok(false)), "{}", problem);
    }

    fn bv(v: i64, w: usize) -> String {
        let v = Integer::from(v).keep_bits(w as u32);
        let s = format!("{:b}", v);
        format!("#b{}{}", "0".repeat(w - s.len()), s)
    }

    /// Cross-check the SMT-LIB bit-vector division family against direct integer arithmetic.
    #[test]
    fn signed_division_matches_integer_arithmetic() {
        let w = 3;
        let half = 1i64 << (w - 1);
        for s in -half..half {
            for t in -half..half {
                let (sdiv, srem, smod) = if t == 0 {
                    // SMT-LIB: bvsdiv by zero is -1 for s >= 0 and 1 otherwise; bvsrem/bvsmod by
                    // zero return s.
                    (if s >= 0 { -1 } else { 1 }, s, s)
                } else {
                    let q = s / t; // truncating
                                   // bvsmod takes the sign of the divisor (floor division).
                    let m = s.rem_euclid(t.abs());
                    let smod = if m == 0 || t > 0 { m } else { m + t };
                    (q, s - t * q, smod)
                };
                let problem = format!(
                    "(assert (= (bvsdiv {a} {b}) {q}))(assert (= (bvsrem {a} {b}) {r}))(assert (= (bvsmod {a} {b}) {m}))",
                    a = bv(s, w),
                    b = bv(t, w),
                    q = bv(sdiv, w),
                    r = bv(srem, w),
                    m = bv(smod, w)
                );
                always(&problem);
            }
        }
    }

    #[test]
    fn bit_vector_operators() {
        always("(assert (= (bvashr #b1000 #b0100) #b1111))");
        always("(assert (= (bvashr #b1010 #b0001) #b1101))");
        always("(assert (= (bvlshr #b1010 #b0001) #b0101))");
        always("(assert (= (bvshl #b0011 #b1111) #b0000))");
        always("(assert (= ((_ rotate_left 4) #b001) #b010))");
        always("(assert (= ((_ rotate_right 1) #b001) #b100))");
        always("(assert (= ((_ extract 3 2) #b1000) #b10))");
        always("(assert (= ((_ sign_extend 2) #b10) #b1110))");
        always("(assert (= (concat #b10 #b01) #b1001))");
        always("(assert (= (bvudiv #b0101 #b0000) #b1111))");
        always("(assert (= (bvurem #b0101 #b0000) #b0101))");
        always("(assert (bvslt #b1111 #b0001))");
        always("(assert (= (sbv_to_int #b1110) (- 2)))");
    }

    #[test]
    fn integer_division_is_euclidean() {
        always("(assert (= (div (- 7) 2) (- 4)))");
        always("(assert (= (mod (- 7) 2) 1))");
        always("(assert (= (div 7 (- 2)) (- 3)))");
        always("(assert (= (mod 7 (- 2)) 1))");
        always("(assert (= (div (- 7) (- 2)) 4))");
    }

    #[test]
    fn division_by_zero_is_a_free_function() {
        always("(declare-const x Real)(assert (= (/ x 0.0) (/ x 0.0)))");
        sometimes_false("(assert (= (/ 1.0 0.0) 0.0))");
        sometimes_false("(declare-const n Int)(assert (= (div n n) 1))");
    }

    #[test]
    fn strings() {
        always("(assert (= (str.substr \"abc\" 1 5) \"bc\"))");
        always("(assert (= (str.substr \"abc\" 3 1) \"\"))");
        always("(assert (= (str.indexof \"abab\" \"b\" 2) 3))");
        always("(assert (= (str.indexof \"ab\" \"\" 2) 2))");
        always("(assert (= (str.indexof \"ab\" \"\" 3) (- 1)))");
        always("(assert (= (str.replace \"ab\" \"\" \"c\") \"cab\"))");
        always("(assert (= (str.replace_all \"aaa\" \"aa\" \"b\") \"ba\"))");
        always("(assert (str.< \"ab\" \"b\"))");
        always("(assert (= (str.to_int \"012\") 12))");
        always("(assert (= (str.to_int \"\") (- 1)))");
        always("(assert (str.in_re \"aab\" (re.++ (re.* (str.to_re \"a\")) (str.to_re \"b\"))))");
        always(
            "(assert (not (str.in_re \"ba\" (re.++ (re.* (str.to_re \"a\")) (str.to_re \"b\")))))",
        );
    }

    #[test]
    fn quantifiers_and_choice_are_three_valued() {
        always("(assert (forall ((p Bool)) (or p (not p))))");
        always("(assert (not (forall ((x Int)) (> x 0))))");
        always("(assert (= (choice ((x Int)) (= x 3)) 3))");
        let unknown = eval_all("(assert (forall ((x Int)) (>= (* x x) 0)))", 5);
        assert!(unknown.iter().all(|r| *r == Err(Unknown)));
        always("(declare-sort U 0)(declare-fun P (U) Bool)(assert (=> (forall ((x U)) (P x)) (exists ((y U)) (P y))))");
    }

    #[test]
    fn arrays_are_extensional() {
        always(
            "(declare-const a (Array Int Int))(assert (= (store (store a 0 1) 0 2) (store a 0 2)))",
        );
        always("(declare-const b (Array Bool Bool))(assert (= (store (store b true (select b true)) false (select b false)) b))");
        sometimes_false("(declare-const a (Array Int Int))(assert (= (store a 0 1) a))");
    }

    /// Widths at and above `2^32` are computed exactly, never modulo `2^32`, and a value that
    /// would need a `2^w` beyond the bound is `Unknown` rather than a guess.
    #[test]
    fn wide_bit_vectors_are_exact_or_unknown() {
        let one = "(concat ((_ zero_extend 4294967295) #b0) #b1)";
        let zero = "(concat ((_ zero_extend 4294967295) #b0) #b0)";
        always(&format!("(assert (not (= (bvadd {one} {one}) {zero})))"));
        always(&format!(
            "(assert (= (bvadd {one} {one}) (bvshl {one} {one})))"
        ));
        always(&format!("(assert (bvult {zero} {one}))"));
        always(
            "(assert (not (= ((_ zero_extend 4294967295) #b1) ((_ zero_extend 4294967295) #b0))))",
        );
        always("(assert (= ((_ extract 0 0) ((_ zero_extend 4294967295) #b1)) #b1))");
        always(
            "(assert (= ((_ extract 4294967295 4294967295) ((_ zero_extend 4294967295) #b1)) #b0))",
        );
        always("(assert (= (ubv_to_int ((_ zero_extend 4294967296) #b101)) 5))");
        for r in eval_all(
            "(assert (= ((_ sign_extend 4294967295) #b1) ((_ sign_extend 4294967295) #b0)))",
            3,
        ) {
            assert_eq!(r, Err(Unknown));
        }
        assert_eq!(
            V::bv(Integer::from(5), 4294967298),
            V::Bv(Integer::from(5), 4294967298)
        );
        assert_eq!(V::try_bv(Integer::from(-1), 4294967296), None);
        assert_eq!(V::bv(Integer::from(-1), 3), V::Bv(Integer::from(7), 3));
    }

    const PAIR: &str = "(declare-datatype P ((mk (fst Int) (snd Int)) (other (oth Int))))\
                        (declare-const a Int)(declare-const b Int)(declare-const x P)";

    /// Datatypes are free term algebras: constructors are injective and disjoint, selectors
    /// project their own constructor's field, and testers hold exactly of their constructor.
    #[test]
    fn datatypes_are_free_term_algebras() {
        always(&format!(
            "{PAIR}(assert (= (fst (mk a b)) a))(assert (= (snd (mk a b)) b))"
        ));
        always(&format!("{PAIR}(assert (= (oth (other a)) a))"));
        always(&format!("{PAIR}(assert (not (= (mk a b) (other a))))"));
        always(&format!(
            "{PAIR}(assert (= (= (mk a b) (mk b a)) (= a b)))(assert ((_ is mk) (mk a b)))"
        ));
        always(&format!("{PAIR}(assert (not ((_ is other) (mk a b))))"));
        always(&format!(
            "{PAIR}(assert (or ((_ is mk) x) ((_ is other) x)))"
        ));
        always(&format!(
            "{PAIR}(assert (=> ((_ is mk) x) (= x (mk (fst x) (snd x)))))"
        ));
        sometimes_false(&format!("{PAIR}(assert (= (snd (mk a b)) a))"));
        sometimes_false(&format!("{PAIR}(assert ((_ is mk) x))"));
    }

    /// SMT-LIB leaves a selector applied to another constructor's value unspecified: the
    /// evaluator must not fix it to anything (in particular not to a field of the value).
    #[test]
    fn a_selector_of_another_constructor_is_unconstrained() {
        sometimes_false(&format!("{PAIR}(assert (= (oth (mk a b)) a))"));
        sometimes_false(&format!("{PAIR}(assert (= (oth (mk a b)) b))"));
        sometimes_false(&format!("{PAIR}(assert (not (= (oth (mk a b)) a)))"));
        sometimes_false(&format!("{PAIR}(assert (= (fst (other a)) a))"));
        // ... but it is a function: the same application has one value.
        always(&format!("{PAIR}(assert (= (oth (mk a b)) (oth (mk a b))))"));
    }

    #[test]
    fn recursive_and_finite_datatypes() {
        let forest = "(declare-datatypes ((Tree 0) (Forest 0))\
            (((leaf (val Int)) (node (children Forest))) ((fnil) (fcons (head Tree) (tail Forest)))))\
            (declare-const t Tree)(declare-const f Forest)";
        always(&format!(
            "{forest}(assert (= (head (fcons t f)) t))(assert (= (tail (fcons t f)) f))"
        ));
        always(&format!("{forest}(assert (not (= fnil (fcons t f))))"));
        sometimes_false(&format!("{forest}(assert (= f fnil))"));
        // A non-recursive datatype over finite fields has a complete domain, so quantifiers over
        // it are decided.
        let color = "(declare-datatype C ((red) (green) (mix (l Bool) (r Bool))))";
        always(&format!(
            "{color}(assert (forall ((c C)) (or (= c red) (= c green) ((_ is mix) c))))"
        ));
        always(&format!("{color}(assert (not (forall ((c C)) (= c red))))"));
        always(&format!(
            "{color}(assert (exists ((c C)) (and ((_ is mix) c) (l c) (not (r c)))))"
        ));
    }

    /// A binder that rebinds a selector's name and sort is a variable, not the selector.
    #[test]
    fn a_binder_rebinding_a_selector_is_not_the_selector() {
        always(&format!(
            "{PAIR}(assert (not (forall ((snd (-> P Int))) (= (snd (mk a b)) b))))"
        ));
        always(&format!(
            "{PAIR}(assert (exists ((snd (-> P Int))) (not (= (snd (mk a b)) b))))"
        ));
    }

    /// A constructor or selector that a `declare-fun` redeclares with the same sort is read as
    /// uninterpreted (that script is ill-formed; the parser refuses it, so the evaluator is
    /// given the table by hand here).
    #[test]
    fn a_shadowed_selector_is_uninterpreted() {
        let (problem, _, _, mut pool) = parser::parse_instance(
            &format!("{PAIR}(assert (= (snd (mk a b)) b))"),
            "",
            None,
            parser::Config::new(),
        )
        .expect("parse");
        let mut table = DtTable::from_terms(&pool, problem.premises.iter());
        let selector = crate::sort::S::Fun(
            vec![crate::sort::S::Dt("P".into())],
            Box::new(crate::sort::S::Int),
        );
        table.shadow("snd", selector);
        let table = Rc::new(table);
        let mut falsified = false;
        for seed in 0..60 {
            let mut model = Model::new(seed, Rc::new(Vocab::default()));
            model.datatypes = table.clone();
            let mut ev = Evaluator::new(&mut model, &mut pool, 1_000_000);
            for t in &problem.premises {
                falsified |= ev.eval_bool(t, &Env::new()) == Ok(false);
            }
        }
        assert!(falsified);
    }

    #[test]
    fn values_compare_structurally() {
        assert_eq!(V::int(3), V::int(3));
        assert_ne!(V::bv(Integer::from(1), 2), V::bv(Integer::from(1), 3));
    }
}
