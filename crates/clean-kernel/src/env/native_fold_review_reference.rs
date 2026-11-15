// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The INDEPENDENT leg of the native-fold review (`native_fold_review.rs`):
//! what each reviewed head computes, written from Lean's documented semantics
//! in plain Rust integer / string arithmetic. It shares no code with the
//! reducers it judges (`native_reducers*.rs`) and none with the kernel.
//!
//! `None` means "no reference for this head or these inputs" (an unknown head,
//! an overflow of the `u128`/`i128` carrier, an exponent too large to matter):
//! the case then carries no evidence, which can only keep a fold unpinned.

use super::{NameComp, Val};

fn mask(bits: u64) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// Two's-complement reading of an `n`-bit pattern.
fn signed(v: u128, bits: u64) -> i128 {
    let v = v & mask(bits);
    if bits == 0 {
        return 0;
    }
    if bits >= 128 {
        return v as i128;
    }
    if v >> (bits - 1) == 1 {
        (v as i128) - (1i128 << bits)
    } else {
        v as i128
    }
}

/// The `n`-bit pattern of a signed value.
fn pattern(v: i128, bits: u64) -> u128 {
    (v as u128) & mask(bits)
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while a != 0 {
        (a, b) = (b % a, a);
    }
    b
}

/// ASCII classification as Lean's `Char` API defines it (`Init/Data/Char/Basic`):
/// letters, digits and case are ASCII-only; whitespace is space, tab, CR, LF.
fn char_pred(op: &str, c: u32) -> Option<bool> {
    let upper = (0x41..=0x5A).contains(&c);
    let lower = (0x61..=0x7A).contains(&c);
    Some(match op {
        "isUpper" => upper,
        "isLower" => lower,
        "isAlpha" => upper || lower,
        "isDigit" => (0x30..=0x39).contains(&c),
        "isWhitespace" => matches!(c, 0x20 | 0x09 | 0x0D | 0x0A),
        _ => return None,
    })
}

fn nat_binop(op: &str, a: u128, b: u128) -> Option<Val> {
    Some(match op {
        "add" => Val::Nat(a.checked_add(b)?),
        "sub" => Val::Nat(a.saturating_sub(b)),
        "mul" => Val::Nat(a.checked_mul(b)?),
        // Lean's conventions: `x / 0 = 0`, `x % 0 = x`.
        "div" => Val::Nat(a.checked_div(b).unwrap_or(0)),
        "mod" => Val::Nat(a.checked_rem(b).unwrap_or(a)),
        "gcd" => Val::Nat(gcd(a, b)),
        "pow" => Val::Nat(a.checked_pow(u32::try_from(b).ok()?)?),
        "beq" => Val::Bool(a == b),
        "ble" => Val::Bool(a <= b),
        "blt" => Val::Bool(a < b),
        "land" => Val::Nat(a & b),
        "lor" => Val::Nat(a | b),
        "xor" => Val::Nat(a ^ b),
        "shiftLeft" => {
            let s = u32::try_from(b).ok().filter(|s| *s < 128)?;
            let out = a.checked_shl(s)?;
            if out >> s != a {
                return None;
            }
            Val::Nat(out)
        }
        // An amount the kernel's fold declines (past 1024 bits) sends the
        // term to δι on a literal of that size: no evidence, only a runaway.
        "shiftRight" if b > 1024 => return None,
        "shiftRight" => Val::Nat(if b >= 128 { 0 } else { a >> b }),
        "decEq" => Val::Decided(a == b),
        "decLe" => Val::Decided(a <= b),
        "decLt" => Val::Decided(a < b),
        _ => return None,
    })
}

fn int_op(op: &str, args: &[Val]) -> Option<Val> {
    let int = |v: &Val| match v {
        Val::Int(i) => Some(*i),
        _ => None,
    };
    let a = int(args.first()?)?;
    let b = args.get(1).and_then(int);
    Some(match (op, b) {
        ("add", Some(b)) => Val::Int(a.checked_add(b)?),
        ("sub", Some(b)) => Val::Int(a.checked_sub(b)?),
        ("mul", Some(b)) => Val::Int(a.checked_mul(b)?),
        // `Int.div`/`Int.mod` as Lean 4.8.0 defines them
        // (`Init/Data/Int/DivMod.lean`): rounding toward zero, the remainder
        // taking the dividend's sign, `x / 0 = 0` and `x % 0 = x`. Rust's `/`
        // and `%` on `i128` are exactly that rounding. (Lean's `/`/`%` on `Int`
        // are the E-rounding `Int.ediv`/`Int.emod`, which are other heads.)
        ("div", Some(0)) => Val::Int(0),
        ("div", Some(b)) => Val::Int(a.checked_div(b)?),
        ("mod", Some(0)) => Val::Int(a),
        ("mod", Some(b)) => Val::Int(a.checked_rem(b)?),
        ("decEq", Some(b)) => Val::Decided(a == b),
        ("decLe", Some(b)) => Val::Decided(a <= b),
        ("decLt", Some(b)) => Val::Decided(a < b),
        ("beq", Some(b)) => Val::Bool(a == b),
        ("ble", Some(b)) => Val::Bool(a <= b),
        ("blt", Some(b)) => Val::Bool(a < b),
        ("neg", None) => Val::Int(a.checked_neg()?),
        ("natAbs", None) => Val::Nat(a.unsigned_abs()),
        ("toNat", None) => Val::Nat(u128::try_from(a.max(0)).ok()?),
        _ => return None,
    })
}

/// `UIntN.op`: `args` are `UInt(N, _)` (and a `Nat` for no op here).
fn uint_op(bits: u64, op: &str, args: &[Val]) -> Option<Val> {
    let u = |v: &Val| match v {
        Val::UInt(b, x) if *b == bits => Some(*x),
        _ => None,
    };
    let m = mask(bits);
    let a = u(args.first()?)?;
    let b = args.get(1).and_then(u);
    if let Some(target) = op.strip_prefix("toUInt") {
        let to: u64 = target.parse().ok()?;
        return Some(Val::UInt(to, a & mask(to)));
    }
    Some(match (op, b) {
        ("add", Some(b)) => Val::UInt(bits, a.wrapping_add(b) & m),
        ("sub", Some(b)) => Val::UInt(bits, a.wrapping_sub(b) & m),
        ("mul", Some(b)) => Val::UInt(bits, a.wrapping_mul(b) & m),
        ("div", Some(b)) => Val::UInt(bits, a.checked_div(b).unwrap_or(0)),
        ("mod", Some(b)) => Val::UInt(bits, a.checked_rem(b).unwrap_or(a)),
        ("land", Some(b)) => Val::UInt(bits, a & b),
        ("lor", Some(b)) => Val::UInt(bits, a | b),
        ("xor", Some(b)) => Val::UInt(bits, a ^ b),
        // Lean 4.30: the shift amount is taken modulo the width.
        ("shiftLeft", Some(b)) => Val::UInt(bits, (a << (b % u128::from(bits))) & m),
        ("shiftRight", Some(b)) => Val::UInt(bits, a >> (b % u128::from(bits))),
        ("complement", None) => Val::UInt(bits, !a & m),
        ("toNat", None) => Val::Nat(a),
        ("toBitVec", None) => Val::BitVec(bits, a),
        ("decEq", Some(b)) => Val::Decided(a == b),
        ("decLt", Some(b)) => Val::Decided(a < b),
        ("decLe", Some(b)) => Val::Decided(a <= b),
        ("beq", Some(b)) => Val::Bool(a == b),
        ("blt", Some(b)) => Val::Bool(a < b),
        ("ble", Some(b)) => Val::Bool(a <= b),
        _ => return None,
    })
}

/// `IntN.op`, two's complement; `div`/`mod` are `BitVec.sdiv`/`BitVec.srem`
/// (truncation toward zero, `x / 0 = 0`, `x % 0 = x`).
fn sint_op(bits: u64, op: &str, args: &[Val]) -> Option<Val> {
    let s = |v: &Val| match v {
        Val::SInt(b, x) if *b == bits => Some(*x),
        _ => None,
    };
    let wrap = |v: i128| Val::SInt(bits, signed(pattern(v, bits), bits));
    let a = s(args.first()?)?;
    let b = args.get(1).and_then(s);
    if let Some(target) = op.strip_prefix("toUInt") {
        let to: u64 = target.parse().ok()?;
        return Some(Val::UInt(to, pattern(a, bits) & mask(to)));
    }
    Some(match (op, b) {
        ("add", Some(b)) => wrap(a + b),
        ("sub", Some(b)) => wrap(a - b),
        ("mul", Some(b)) => wrap(a * b),
        ("div", Some(0)) => Val::SInt(bits, 0),
        ("div", Some(b)) => wrap(a / b),
        ("mod", Some(0)) => Val::SInt(bits, a),
        ("mod", Some(b)) => wrap(a % b),
        ("decEq", Some(b)) => Val::Decided(a == b),
        ("decLe", Some(b)) => Val::Decided(a <= b),
        ("decLt", Some(b)) => Val::Decided(a < b),
        ("toBitVec", None) => Val::BitVec(bits, pattern(a, bits)),
        _ => return None,
    })
}

/// `BitVec.op`: `args[0]` is the width (`Nat`), then the operands.
fn bitvec_op(op: &str, args: &[Val]) -> Option<Val> {
    let Val::Nat(w) = args.first()? else {
        return None;
    };
    let w = u64::try_from(*w).ok().filter(|w| *w <= 128)?;
    let m = mask(w);
    let bv = |v: &Val| match v {
        Val::BitVec(b, x) if *b == w => Some(*x),
        _ => None,
    };
    let nat = |v: &Val| match v {
        Val::Nat(n) => Some(*n),
        _ => None,
    };
    if op == "ofNat" {
        return Some(Val::BitVec(w, nat(args.get(1)?)? & m));
    }
    let x = bv(args.get(1)?)?;
    let y = || args.get(2).and_then(bv);
    Some(match op {
        "add" => Val::BitVec(w, x.wrapping_add(y()?) & m),
        "sub" => Val::BitVec(w, x.wrapping_sub(y()?) & m),
        "mul" => Val::BitVec(w, x.wrapping_mul(y()?) & m),
        "neg" => Val::BitVec(w, x.wrapping_neg() & m),
        "not" => Val::BitVec(w, !x & m),
        "and" => Val::BitVec(w, x & y()?),
        "or" => Val::BitVec(w, x | y()?),
        "xor" => Val::BitVec(w, x ^ y()?),
        "udiv" => Val::BitVec(w, x.checked_div(y()?).unwrap_or(0)),
        "umod" => {
            let y = y()?;
            Val::BitVec(w, x.checked_rem(y).unwrap_or(x))
        }
        "shiftLeft" | "ushiftRight" => {
            let s = nat(args.get(2)?)?;
            let out = if s >= u128::from(w) {
                0
            } else if op == "shiftLeft" {
                (x << s) & m
            } else {
                x >> s
            };
            Val::BitVec(w, out)
        }
        "ult" => Val::Bool(x < y()?),
        "ule" => Val::Bool(x <= y()?),
        "slt" => Val::Bool(signed(x, w) < signed(y()?, w)),
        "sle" => Val::Bool(signed(x, w) <= signed(y()?, w)),
        "toNat" => Val::Nat(x),
        _ => return None,
    })
}

fn string_op(op: &str, args: &[Val]) -> Option<Val> {
    let st = |v: &Val| match v {
        Val::Str(s) => Some(s.clone()),
        _ => None,
    };
    let ch = |v: &Val| match v {
        Val::Char(c) => char::from_u32(*c),
        _ => None,
    };
    Some(match op {
        "append" => Val::Str(st(args.first()?)? + &st(args.get(1)?)?),
        "length" => Val::Nat(st(args.first()?)?.chars().count() as u128),
        "utf8ByteSize" => Val::Nat(st(args.first()?)?.len() as u128),
        "isEmpty" => Val::Bool(st(args.first()?)?.is_empty()),
        "singleton" => Val::Str(ch(args.first()?)?.to_string()),
        "push" => {
            let mut s = st(args.first()?)?;
            s.push(ch(args.get(1)?)?);
            Val::Str(s)
        }
        "decEq" => Val::Decided(st(args.first()?)? == st(args.get(1)?)?),
        "beq" => Val::Bool(st(args.first()?)? == st(args.get(1)?)?),
        // `p.isPrefixOf s`: `s` starts with `p`.
        "isPrefixOf" => Val::Bool(st(args.get(1)?)?.starts_with(&st(args.first()?)?)),
        _ => return None,
    })
}

fn char_op(op: &str, args: &[Val]) -> Option<Val> {
    let Val::Char(c) = args.first()? else {
        return None;
    };
    let c = *c;
    if let Some(b) = char_pred(op, c) {
        return Some(Val::Bool(b));
    }
    Some(match op {
        "toNat" => Val::Nat(u128::from(c)),
        "toLower" if (0x41..=0x5A).contains(&c) => Val::Char(c + 32),
        "toUpper" if (0x61..=0x7A).contains(&c) => Val::Char(c - 32),
        "toLower" | "toUpper" => Val::Char(c),
        "decEq" => match args.get(1)? {
            Val::Char(d) => Val::Decided(c == *d),
            _ => return None,
        },
        _ => return None,
    })
}

fn bool_op(op: &str, args: &[Val]) -> Option<Val> {
    let b = |v: &Val| match v {
        Val::Bool(x) => Some(*x),
        _ => None,
    };
    let x = b(args.first()?)?;
    let y = || args.get(1).and_then(b);
    Some(match op {
        "not" => Val::Bool(!x),
        "and" => Val::Bool(x && y()?),
        "or" => Val::Bool(x || y()?),
        "xor" => Val::Bool(x != y()?),
        "beq" => Val::Bool(x == y()?),
        "decEq" => Val::Decided(x == y()?),
        _ => return None,
    })
}

fn name_op(op: &str, args: &[Val]) -> Option<Val> {
    let nm = |v: &Val| match v {
        Val::Name(n) => Some(n.clone()),
        _ => None,
    };
    let mut p = nm(args.first()?)?;
    Some(match (op, args.get(1)?) {
        ("mkStr", Val::Str(s)) => {
            p.push(NameComp::Str(s.clone()));
            Val::Name(p)
        }
        ("mkNum", Val::Nat(n)) => {
            p.push(NameComp::Num(u64::try_from(*n).ok()?));
            Val::Name(p)
        }
        ("append", Val::Name(q)) => {
            p.extend(q.iter().cloned());
            Val::Name(p)
        }
        ("beq", Val::Name(q)) => Val::Bool(p == *q),
        _ => return None,
    })
}

/// What `head` computes on `args` (binder order, implicit widths included).
pub(super) fn reference(head: &str, args: &[Val]) -> Option<Val> {
    let (ns, op) = head.rsplit_once('.').unwrap_or(("", head));
    let nats = || -> Option<(u128, Option<u128>)> {
        let n = |v: &Val| match v {
            Val::Nat(x) => Some(*x),
            _ => None,
        };
        Some((n(args.first()?)?, args.get(1).and_then(n)))
    };
    match ns {
        "Nat" => {
            let (a, b) = nats()?;
            match (op, b) {
                ("pred", None) => Some(Val::Nat(a.saturating_sub(1))),
                (_, Some(b)) => nat_binop(op, a, b),
                _ => None,
            }
        }
        "Int" => int_op(op, args),
        "Bool" => bool_op(op, args),
        "Char" => char_op(op, args),
        "String" => string_op(op, args),
        "BitVec" => bitvec_op(op, args),
        "Lean.Name" => name_op(op, args),
        "UInt8" => uint_op(8, op, args),
        "UInt16" => uint_op(16, op, args),
        "UInt32" => uint_op(32, op, args),
        "UInt64" => uint_op(64, op, args),
        "Int8" => sint_op(8, op, args),
        "Int16" => sint_op(16, op, args),
        "Int32" => sint_op(32, op, args),
        "Int64" => sint_op(64, op, args),
        "" => instance_reference(op, args),
        _ => None,
    }
}

/// The decidability instances named by type (`instDecidableEqNat`, …) and the
/// prelude's `instDecidableNatLe`/`Lt`: each decides the relation its name says.
fn instance_reference(op: &str, args: &[Val]) -> Option<Val> {
    let rel = match op {
        "instDecidableNatLe" => return reference("Nat.decLe", args),
        "instDecidableNatLt" => return reference("Nat.decLt", args),
        _ => op.strip_prefix("instDecidableEq")?,
    };
    let (a, b) = (args.first()?, args.get(1)?);
    if std::mem::discriminant(a) != std::mem::discriminant(b) {
        return None;
    }
    // Every carrier here has structural equality on its reference value.
    matches!(
        rel,
        "Nat"
            | "Int"
            | "Bool"
            | "Char"
            | "String"
            | "UInt8"
            | "UInt16"
            | "UInt32"
            | "UInt64"
            | "Int8"
            | "Int16"
            | "Int32"
            | "Int64"
    )
    .then(|| Val::Decided(a == b))
}
