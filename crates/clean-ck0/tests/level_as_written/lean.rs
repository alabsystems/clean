// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.30.0-rc2's kernel level algebra (`src/kernel/level.cpp`), ported
//! for this test alone: `mk_max`, `mk_imax`, `normalize`, `is_equivalent`,
//! `is_geq` and `instantiate`, on levels as written. `==` is structural, and
//! "zero" is the `Zero` node, as in Lean. Its equality is checked against
//! R150's 2,009 recorded kernel verdicts on equality, and its order,
//! equality and `instantiate` against the verdicts Lean's kernel gave on
//! `fixtures/level_gap/`'s declarations (24 rows); its order has no other
//! check against Lean's kernel.

use std::rc::Rc;

use clean_ck0::RawLevel;

/// A level as Lean's kernel holds it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Lv {
    Zero,
    Succ(Rc<Lv>),
    Max(Rc<Lv>, Rc<Lv>),
    IMax(Rc<Lv>, Rc<Lv>),
    Param(u32),
}

use Lv::{IMax, Max, Param, Succ, Zero};

pub fn zero() -> Rc<Lv> {
    Rc::new(Zero)
}

pub fn succ(l: Rc<Lv>) -> Rc<Lv> {
    Rc::new(Succ(l))
}

fn kind(l: &Lv) -> u8 {
    match l {
        Zero => 0,
        Succ(_) => 1,
        Max(..) => 2,
        IMax(..) => 3,
        Param(_) => 4,
    }
}

pub fn from_raw(r: &RawLevel) -> Rc<Lv> {
    Rc::new(match r {
        RawLevel::Zero => Zero,
        RawLevel::Succ(a) => Succ(from_raw(a)),
        RawLevel::Max(a, b) => Max(from_raw(a), from_raw(b)),
        RawLevel::IMax(a, b) => IMax(from_raw(a), from_raw(b)),
        RawLevel::Param(i) => Param(*i),
    })
}

/// R150's encoding: `Z`, `S(x)`, `M(a,b)`, `I(a,b)`, `P(u)`, `P(v)`, `P(w)`.
pub fn parse(s: &str) -> RawLevel {
    fn go(b: &[u8], i: &mut usize) -> RawLevel {
        let c = b[*i];
        *i += 1;
        if c == b'Z' {
            return RawLevel::Zero;
        }
        assert_eq!(b[*i], b'(');
        *i += 1;
        let out = match c {
            b'P' => {
                let p = match b[*i] {
                    b'u' => 0,
                    b'v' => 1,
                    b'w' => 2,
                    other => panic!("unknown param {}", other as char),
                };
                *i += 1;
                RawLevel::Param(p)
            }
            b'S' => RawLevel::Succ(Box::new(go(b, i))),
            b'M' | b'I' => {
                let l = go(b, i);
                assert_eq!(b[*i], b',');
                *i += 1;
                let r = go(b, i);
                if c == b'M' {
                    RawLevel::Max(Box::new(l), Box::new(r))
                } else {
                    RawLevel::IMax(Box::new(l), Box::new(r))
                }
            }
            other => panic!("unknown node {}", other as char),
        };
        assert_eq!(b[*i], b')');
        *i += 1;
        out
    }
    let mut i = 0;
    let out = go(s.as_bytes(), &mut i);
    assert_eq!(i, s.len(), "trailing input in {s}");
    out
}

fn to_offset(l: &Rc<Lv>) -> (Rc<Lv>, u32) {
    let mut l = l.clone();
    let mut k = 0;
    while let Succ(a) = &*l {
        let a = a.clone();
        l = a;
        k += 1;
    }
    (l, k)
}

fn is_explicit(l: &Rc<Lv>) -> bool {
    *to_offset(l).0 == Zero
}

fn mk_succ(mut l: Rc<Lv>, k: u32) -> Rc<Lv> {
    for _ in 0..k {
        l = succ(l);
    }
    l
}

pub fn is_not_zero(l: &Lv) -> bool {
    match l {
        Zero | Param(_) => false,
        Succ(_) => true,
        Max(a, b) => is_not_zero(a) || is_not_zero(b),
        IMax(_, b) => is_not_zero(b),
    }
}

fn mk_max(l1: Rc<Lv>, l2: Rc<Lv>) -> Rc<Lv> {
    if is_explicit(&l1) && is_explicit(&l2) {
        return if to_offset(&l1).1 >= to_offset(&l2).1 {
            l1
        } else {
            l2
        };
    }
    if l1 == l2 || *l2 == Zero {
        return l1;
    }
    if *l1 == Zero {
        return l2;
    }
    if let Max(a, b) = &*l2 {
        if *a == l1 || *b == l1 {
            return l2;
        }
    }
    if let Max(a, b) = &*l1 {
        if *a == l2 || *b == l2 {
            return l1;
        }
    }
    let (b1, k1) = to_offset(&l1);
    let (b2, k2) = to_offset(&l2);
    if b1 == b2 {
        return if k1 > k2 { l1 } else { l2 };
    }
    Rc::new(Max(l1, l2))
}

fn mk_imax(l1: Rc<Lv>, l2: Rc<Lv>) -> Rc<Lv> {
    if is_not_zero(&l2) {
        return mk_max(l1, l2);
    }
    if *l2 == Zero || *l1 == Zero || *l1 == Succ(zero()) {
        return l2;
    }
    if l1 == l2 {
        return l1;
    }
    Rc::new(IMax(l1, l2))
}

fn is_norm_lt(a: &Rc<Lv>, b: &Rc<Lv>) -> bool {
    if a == b {
        return false;
    }
    let (l1, k1) = to_offset(a);
    let (l2, k2) = to_offset(b);
    if l1 != l2 {
        if kind(&l1) != kind(&l2) {
            return kind(&l1) < kind(&l2);
        }
        return match (&*l1, &*l2) {
            (Param(x), Param(y)) => x < y,
            (Max(a1, b1), Max(a2, b2)) | (IMax(a1, b1), IMax(a2, b2)) => {
                if a1 != a2 {
                    is_norm_lt(a1, a2)
                } else {
                    is_norm_lt(b1, b2)
                }
            }
            _ => unreachable!("equal kinds, neither a succ nor zero"),
        };
    }
    k1 < k2
}

fn push_max_args(l: &Rc<Lv>, out: &mut Vec<Rc<Lv>>) {
    if let Max(a, b) = &**l {
        push_max_args(a, out);
        push_max_args(b, out);
    } else {
        out.push(l.clone());
    }
}

pub fn normalize(l: &Rc<Lv>) -> Rc<Lv> {
    let (r, k) = to_offset(l);
    match &*r {
        Zero | Param(_) => l.clone(),
        Succ(_) => unreachable!("an offset's base is never a succ"),
        IMax(a, b) => mk_succ(mk_imax(normalize(a), normalize(b)), k),
        Max(..) => {
            let mut todo = Vec::new();
            push_max_args(&r, &mut todo);
            let mut args = Vec::new();
            for a in &todo {
                push_max_args(&normalize(a), &mut args);
            }
            args.sort_by(|x, y| {
                if is_norm_lt(x, y) {
                    std::cmp::Ordering::Less
                } else if is_norm_lt(y, x) {
                    std::cmp::Ordering::Greater
                } else {
                    std::cmp::Ordering::Equal
                }
            });
            let mut i = 0;
            if is_explicit(&args[i]) {
                while i + 1 < args.len() && is_explicit(&args[i + 1]) {
                    i += 1;
                }
                let kk = to_offset(&args[i]).1;
                if args[i + 1..].iter().any(|a| to_offset(a).1 >= kk) {
                    i += 1;
                }
            }
            let mut rargs = vec![args[i].clone()];
            let mut prev = to_offset(&args[i]);
            for a in &args[i + 1..] {
                let cur = to_offset(a);
                if prev.0 == cur.0 {
                    if prev.1 < cur.1 {
                        prev = cur;
                        rargs.pop();
                        rargs.push(a.clone());
                    }
                } else {
                    prev = cur;
                    rargs.push(a.clone());
                }
            }
            let mut rargs: Vec<Rc<Lv>> = rargs.into_iter().map(|a| mk_succ(a, k)).collect();
            let mut acc = rargs.pop().expect("a max has arguments");
            while let Some(next) = rargs.pop() {
                acc = mk_max(next, acc);
            }
            acc
        }
    }
}

pub fn is_equivalent(a: &Rc<Lv>, b: &Rc<Lv>) -> bool {
    a == b || normalize(a) == normalize(b)
}

pub fn is_geq(a: &Rc<Lv>, b: &Rc<Lv>) -> bool {
    is_geq_core(&normalize(a), &normalize(b))
}

fn is_geq_core(l1: &Rc<Lv>, l2: &Rc<Lv>) -> bool {
    if l1 == l2 || **l2 == Zero {
        return true;
    }
    if let Max(a, b) = &**l2 {
        return is_geq(l1, a) && is_geq(l1, b);
    }
    if let Max(a, b) = &**l1 {
        if is_geq(a, l2) || is_geq(b, l2) {
            return true;
        }
    }
    if let IMax(a, b) = &**l2 {
        return is_geq(l1, a) && is_geq(l1, b);
    }
    if let IMax(_, b) = &**l1 {
        return is_geq(b, l2);
    }
    let (b1, k1) = to_offset(l1);
    let (b2, k2) = to_offset(l2);
    if b1 == b2 || *b2 == Zero {
        return k1 >= k2;
    }
    if k1 == k2 && k1 > 0 {
        return is_geq(&b1, &b2);
    }
    false
}

/// Lean's `instantiate` (level.cpp:302): a node whose children come back as
/// the same objects is kept, any other is rebuilt by `mk_max` / `mk_imax`.
pub fn instantiate(l: &Rc<Lv>, sub: &[Rc<Lv>]) -> Rc<Lv> {
    match &**l {
        Zero => l.clone(),
        Param(i) => sub.get(*i as usize).cloned().unwrap_or_else(|| l.clone()),
        Succ(a) => {
            let a2 = instantiate(a, sub);
            if Rc::ptr_eq(&a2, a) {
                l.clone()
            } else {
                succ(a2)
            }
        }
        Max(a, b) | IMax(a, b) => {
            let (a2, b2) = (instantiate(a, sub), instantiate(b, sub));
            if Rc::ptr_eq(&a2, a) && Rc::ptr_eq(&b2, b) {
                l.clone()
            } else if matches!(**l, Max(..)) {
                mk_max(a2, b2)
            } else {
                mk_imax(a2, b2)
            }
        }
    }
}

/// `0` at every assignment.
pub fn always_zero(l: &Lv) -> bool {
    match l {
        Zero => true,
        Succ(_) | Param(_) => false,
        Max(a, b) => always_zero(a) && always_zero(b),
        IMax(_, b) => always_zero(b),
    }
}

/// R177's three forms, the first a walk meets, children first: `A` an `imax`
/// whose right side is never zero, `C` any other `imax` Lean normalises to a
/// `max`, `B` a level not written `0` that is `0` at every assignment.
pub fn first_form(l: &Rc<Lv>) -> Option<char> {
    let children: Vec<&Rc<Lv>> = match &**l {
        Zero | Param(_) => vec![],
        Succ(a) => vec![a],
        Max(a, b) | IMax(a, b) => vec![a, b],
    };
    for c in children {
        if let Some(f) = first_form(c) {
            return Some(f);
        }
    }
    if let IMax(_, b) = &**l {
        if is_not_zero(b) {
            return Some('A');
        }
        if matches!(*normalize(l), Max(..)) {
            return Some('C');
        }
    }
    if **l != Zero && always_zero(l) {
        return Some('B');
    }
    None
}
