//! Every transfer function of [`super`]'s interval analysis, checked against
//! the reference interpreter's OWN integer arithmetic
//! (`crate::interpret::eval_int_*`, the functions an execution runs):
//!
//! * exhaustively at 3 and 4 bits — every interval (and, where the function
//!   reads one, every signed upper bound) of every operand, and every member
//!   of it;
//! * by boundary-biased sampling at the widths types have (8 to 128 bits),
//!   where the edge cases are `u128` overflow and the signed/unsigned seams.
//!
//! The property is containment, the direction the lint's soundness rests on:
//! every value an execution can produce lies in the range the analysis
//! computes, and every pair satisfying a branch condition satisfies the facts
//! the analysis draws from it. A transfer function that under-approximates
//! (the bug that makes the lint silently discharge an allocation) fails here
//! with the operands that show it.

use super::*;
use crate::interpret::{
    InterpretInt, eval_int_binop, eval_int_icmp, eval_int_overflow, eval_int_unop,
};

/// SplitMix64: deterministic, so a failure names a reproducible case.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn wide(&mut self) -> u128 {
        (u128::from(self.next()) << 64) | u128::from(self.next())
    }

    fn below(&mut self, n: u128) -> u128 {
        if n == 0 { 0 } else { self.wide() % n }
    }

    /// A value at `bits` biased to the seams: 0, 1, the signed and unsigned
    /// extremes, powers of two and their neighbours, or anything.
    fn seam(&mut self, bits: u32) -> u128 {
        let max = umax(bits);
        let p = 1u128 << self.below(u128::from(bits));
        let picks = [
            0,
            1,
            2,
            smax(bits),
            smax(bits) + 1,
            max,
            max - 1,
            p,
            p - 1,
            (p + 1) & max,
            self.wide() & max,
            self.below(64) & max,
        ];
        picks[self.below(picks.len() as u128) as usize]
    }

    /// An interval at `bits`: narrow around a seam, or wide.
    fn interval(&mut self, bits: u32) -> (u128, u128) {
        let max = umax(bits);
        let a = self.seam(bits);
        let b = match self.below(3) {
            0 => a.saturating_add(self.below(16)).min(max),
            1 => a.saturating_sub(self.below(16)),
            _ => self.seam(bits),
        };
        (a.min(b), a.max(b))
    }
}

const BINOPS: [BinOp; 18] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::UDiv,
    BinOp::SDiv,
    BinOp::URem,
    BinOp::SRem,
    BinOp::And,
    BinOp::Or,
    BinOp::Xor,
    BinOp::Shl,
    BinOp::LShr,
    BinOp::AShr,
    BinOp::BAnd,
    BinOp::BOr,
    BinOp::BXor,
    BinOp::RotL,
    BinOp::RotR,
];

const UNOPS: [UnOp; 7] = [
    UnOp::Neg,
    UnOp::Not,
    UnOp::CtPop,
    UnOp::CtLz,
    UnOp::CtTz,
    UnOp::BSwap,
    UnOp::BitReverse,
];

const CMPS: [ICmpOp; 10] = [
    ICmpOp::Eq,
    ICmpOp::Ne,
    ICmpOp::Ult,
    ICmpOp::Ule,
    ICmpOp::Ugt,
    ICmpOp::Uge,
    ICmpOp::Slt,
    ICmpOp::Sle,
    ICmpOp::Sgt,
    ICmpOp::Sge,
];

const OVERFLOWS: [OverflowOp; 3] = [
    OverflowOp::AddOverflow,
    OverflowOp::SubOverflow,
    OverflowOp::MulOverflow,
];

fn int(bits: u32, signed: bool, raw: u128) -> InterpretInt {
    InterpretInt::from_raw(bits, signed, raw).expect("a width of 1..=128 bits")
}

/// The interpreter's result of `x op y`, or `None` where it is undefined.
fn exec_binop(op: BinOp, bits: u32, signed: bool, x: u128, y: u128) -> Option<u128> {
    let (x, y) = (int(bits, signed, x), int(bits, signed, y));
    eval_int_binop(op, x, y, BlockId::new(0))
        .ok()
        .map(|v| v.raw)
}

/// The interpreter's integer cast of `x` (the same arms as `eval_cast`).
fn exec_cast(op: CastOp, from: u32, to: u32, x: u128) -> Option<u128> {
    let x = int(from, false, x);
    match op {
        CastOp::Trunc if to <= from => InterpretInt::from_raw(to, false, x.raw),
        CastOp::ZExt if to >= from => InterpretInt::from_raw(to, false, x.raw),
        CastOp::SExt if to >= from => InterpretInt::from_i128(to, false, x.as_signed()),
        CastOp::Bitcast if to == from => Some(x),
        _ => None,
    }
    .map(|v| v.raw)
}

/// Whether `v` is a member of `r`: in the interval, and within its signed
/// upper bound.
fn member(r: &Range, v: u128) -> bool {
    !r.is_empty() && (r.lo..=r.hi).contains(&v) && r.shi.is_none_or(|s| to_signed(v, r.bits) <= s)
}

/// The members of `r`, enumerated (small widths only).
fn members(r: &Range) -> impl Iterator<Item = u128> + '_ {
    (0..=umax(r.bits)).filter(move |v| member(r, *v))
}

/// Every interval at `bits`.
fn intervals(bits: u32) -> Vec<Range> {
    let max = umax(bits);
    let mut out = Vec::new();
    for lo in 0..=max {
        for hi in lo..=max {
            out.push(Range::span(bits, false, lo, hi));
        }
    }
    out
}

/// Every interval at `bits`, each without and with every signed upper bound
/// (normalized; duplicates kept, they cost nothing).
fn ranges_with_shi(bits: u32) -> Vec<Range> {
    let mut out = Vec::new();
    for r in intervals(bits) {
        out.push(r);
        for s in smin(bits)..=smax(bits) as i128 {
            out.push(Range { shi: Some(s), ..r }.normalize());
        }
    }
    out
}

/// A sampled member of `r` (an end or a point between them).
fn sample_member(rng: &mut Rng, r: &Range) -> u128 {
    match rng.below(3) {
        0 => r.lo,
        1 => r.hi,
        _ => match (r.hi - r.lo).checked_add(1) {
            Some(width) => r.lo + rng.below(width),
            None => rng.wide(), // the whole of u128
        },
    }
}

fn fail(failures: &mut Vec<String>, message: String) {
    if failures.len() < 8 {
        failures.push(message);
    }
}

#[test]
fn binop_contains_every_interpreter_result_exhaustively_at_3_and_4_bits() {
    let mut failures = Vec::new();
    let mut checked = 0u64;
    for bits in [3, 4] {
        let size = 1usize << bits;
        let ranges = intervals(bits);
        for signed in [false, true] {
            for op in BINOPS {
                // The interpreter's whole table for `op` at this width.
                let table: Vec<Option<u128>> = (0..size * size)
                    .map(|i| exec_binop(op, bits, signed, (i / size) as u128, (i % size) as u128))
                    .collect();
                for a in &ranges {
                    for b in &ranges {
                        let out = binop(op, bits, signed, *a, *b);
                        for x in a.lo..=a.hi {
                            for y in b.lo..=b.hi {
                                let Some(v) = table[x as usize * size + y as usize] else {
                                    continue;
                                };
                                checked += 1;
                                if !member(&out, v) {
                                    fail(
                                        &mut failures,
                                        format!(
                                            "{op:?}/{bits}b {a:?} {b:?} -> {out:?} misses {x},{y} = {v}"
                                        ),
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
    assert!(checked > 10_000_000, "only {checked} results checked");
}

#[test]
fn binop_contains_sampled_interpreter_results_at_every_type_width() {
    let mut rng = Rng(0xA110_C0B0_0000_0001);
    let mut failures = Vec::new();
    for bits in [8, 16, 32, 64, 128] {
        for _ in 0..6_000 {
            let signed = rng.below(2) == 0;
            let (a_lo, a_hi) = rng.interval(bits);
            let (b_lo, b_hi) = rng.interval(bits);
            let (a, b) = (
                Range::span(bits, signed, a_lo, a_hi),
                Range::span(bits, signed, b_lo, b_hi),
            );
            for op in BINOPS {
                let out = binop(op, bits, signed, a, b);
                for _ in 0..6 {
                    let (x, y) = (sample_member(&mut rng, &a), sample_member(&mut rng, &b));
                    if let Some(v) = exec_binop(op, bits, signed, x, y)
                        && !member(&out, v)
                    {
                        fail(
                            &mut failures,
                            format!("{op:?}/{bits}b {a:?} {b:?} -> {out:?} misses {x},{y} = {v}"),
                        );
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

#[test]
fn unop_contains_every_interpreter_result() {
    let mut failures = Vec::new();
    for bits in [3, 4, 8] {
        for signed in [false, true] {
            for op in UNOPS {
                for a in intervals(bits) {
                    let out = unop(op, bits, signed, a);
                    for x in a.lo..=a.hi {
                        let Ok(v) = eval_int_unop(op, int(bits, signed, x), BlockId::new(0)) else {
                            continue;
                        };
                        if !member(&out, v.raw) {
                            fail(
                                &mut failures,
                                format!("{op:?}/{bits}b {a:?} -> {out:?} misses {x} = {}", v.raw),
                            );
                        }
                    }
                }
            }
        }
    }
    let mut rng = Rng(0xA110_C0B0_0000_0002);
    for bits in [16, 32, 64, 128] {
        for _ in 0..4_000 {
            let (lo, hi) = rng.interval(bits);
            let a = Range::span(bits, false, lo, hi);
            for op in UNOPS {
                let out = unop(op, bits, false, a);
                let x = sample_member(&mut rng, &a);
                if let Ok(v) = eval_int_unop(op, int(bits, false, x), BlockId::new(0))
                    && !member(&out, v.raw)
                {
                    fail(
                        &mut failures,
                        format!("{op:?}/{bits}b {a:?} -> {out:?} misses {x} = {}", v.raw),
                    );
                }
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

#[test]
fn cast_contains_every_interpreter_result() {
    let mut failures = Vec::new();
    let ops = [CastOp::Trunc, CastOp::ZExt, CastOp::SExt, CastOp::Bitcast];
    for from in [3, 4, 5] {
        for to in [2, 3, 4, 5, 8] {
            for op in ops {
                for a in intervals(from) {
                    let out = cast(op, to, false, from, a);
                    for x in a.lo..=a.hi {
                        let Some(v) = exec_cast(op, from, to, x) else {
                            continue;
                        };
                        if !member(&out, v) {
                            fail(
                                &mut failures,
                                format!("{op:?} {from}->{to} {a:?} -> {out:?} misses {x} = {v}"),
                            );
                        }
                    }
                }
            }
        }
    }
    let mut rng = Rng(0xA110_C0B0_0000_0003);
    let widths = [8, 16, 32, 64, 128];
    for _ in 0..40_000 {
        let from = widths[rng.below(5) as usize];
        let to = widths[rng.below(5) as usize];
        let op = ops[rng.below(4) as usize];
        let (lo, hi) = rng.interval(from);
        let a = Range::span(from, false, lo, hi);
        let out = cast(op, to, false, from, a);
        for _ in 0..4 {
            let x = sample_member(&mut rng, &a);
            if let Some(v) = exec_cast(op, from, to, x)
                && !member(&out, v)
            {
                fail(
                    &mut failures,
                    format!("{op:?} {from}->{to} {a:?} -> {out:?} misses {x} = {v}"),
                );
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// The facts a comparison draws, with signed upper bounds on both operands in
/// play: every pair the interpreter says satisfies `x op y` satisfies them.
/// `negate` is checked against the interpreter too, since a false edge reads
/// the facts of the negated comparison.
#[test]
fn cmp_facts_hold_for_every_satisfying_pair_exhaustively_at_3_bits() {
    let bits = 3;
    let mut failures = Vec::new();
    let mut checked = 0u64;
    for op in CMPS {
        for x in 0..=umax(bits) {
            for y in 0..=umax(bits) {
                let (a, b) = (int(bits, false, x), int(bits, false, y));
                if eval_int_icmp(negate(op), a, b) == eval_int_icmp(op, a, b) {
                    fail(
                        &mut failures,
                        format!("negate({op:?}) agrees with it at {x},{y}"),
                    );
                }
            }
        }
    }
    let ranges = ranges_with_shi(bits);
    for op in CMPS {
        for x in &ranges {
            let xs: Vec<u128> = members(x).collect();
            for y in &ranges {
                let [fx, fy] = cmp_facts(op, bits, *x, *y);
                let (mx, my) = (fx.map(|f| x.meet(f)), fy.map(|f| y.meet(f)));
                for &a in &xs {
                    for b in members(y) {
                        if !eval_int_icmp(op, int(bits, false, a), int(bits, false, b)) {
                            continue;
                        }
                        checked += 1;
                        if mx.is_some_and(|r| !member(&r, a)) || my.is_some_and(|r| !member(&r, b))
                        {
                            fail(
                                &mut failures,
                                format!(
                                    "{op:?} x={x:?} y={y:?}: facts {fx:?} {fy:?} exclude ({a},{b})"
                                ),
                            );
                        }
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
    assert!(checked > 1_000_000, "only {checked} pairs checked");
}

#[test]
fn cmp_facts_hold_for_sampled_pairs_at_every_type_width() {
    let mut rng = Rng(0xA110_C0B0_0000_0004);
    let mut failures = Vec::new();
    for bits in [8, 16, 32, 64, 128] {
        for _ in 0..8_000 {
            let range = |rng: &mut Rng| {
                let (lo, hi) = rng.interval(bits);
                let shi = (rng.below(2) == 0).then(|| to_signed(rng.seam(bits), bits));
                Range {
                    bits,
                    signed: false,
                    lo,
                    hi,
                    shi,
                }
                .normalize()
            };
            let (x, y) = (range(&mut rng), range(&mut rng));
            if x.is_empty() || y.is_empty() {
                continue;
            }
            for op in CMPS {
                let [fx, fy] = cmp_facts(op, bits, x, y);
                for _ in 0..6 {
                    let (a, b) = (sample_member(&mut rng, &x), sample_member(&mut rng, &y));
                    if !member(&x, a)
                        || !member(&y, b)
                        || !eval_int_icmp(op, int(bits, false, a), int(bits, false, b))
                    {
                        continue;
                    }
                    let excluded = fx.is_some_and(|f| !member(&x.meet(f), a))
                        || fy.is_some_and(|f| !member(&y.meet(f), b));
                    if excluded {
                        fail(
                            &mut failures,
                            format!(
                                "{op:?} x={x:?} y={y:?}: facts {fx:?} {fy:?} exclude ({a},{b})"
                            ),
                        );
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// `normalize` keeps the member set exactly; `meet` is the intersection and
/// `join` covers the union (a hull may add members, never lose one).
#[test]
fn normalize_meet_and_join_are_exact_on_member_sets_at_3_bits() {
    let bits = 3;
    let mut failures = Vec::new();
    for r in intervals(bits) {
        for s in smin(bits) - 1..=smax(bits) as i128 + 1 {
            let raw = Range { shi: Some(s), ..r };
            let normal = raw.normalize();
            for v in 0..=umax(bits) {
                let before = (r.lo..=r.hi).contains(&v) && to_signed(v, bits) <= s;
                if before != member(&normal, v) {
                    fail(
                        &mut failures,
                        format!("normalize {raw:?} = {normal:?} at {v}"),
                    );
                }
            }
        }
    }
    let ranges = ranges_with_shi(bits);
    for a in &ranges {
        for b in &ranges {
            let (meet, join) = (a.meet(*b), a.join(*b));
            for v in 0..=umax(bits) {
                let (in_a, in_b) = (member(a, v), member(b, v));
                if (in_a && in_b) != member(&meet, v) {
                    fail(&mut failures, format!("meet {a:?} {b:?} = {meet:?} at {v}"));
                }
                if (in_a || in_b) && !member(&join, v) {
                    fail(
                        &mut failures,
                        format!("join {a:?} {b:?} = {join:?} misses {v}"),
                    );
                }
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// The default edge of a `Switch`: every selector value in range that is no
/// case stays in range — for every interval and every set of case values.
#[test]
fn switch_default_keeps_every_value_no_case_names_at_3_and_4_bits() {
    let mut failures = Vec::new();
    for bits in [3, 4] {
        let values = 1u32 << bits;
        for r in intervals(bits) {
            // At 4 bits, the subsets of the values within two of the ends.
            let candidates: Vec<u128> = (0..u128::from(values))
                .filter(|c| {
                    bits == 3 || c + 2 >= r.lo && *c <= r.lo + 2 || c + 2 >= r.hi && *c <= r.hi + 2
                })
                .collect();
            for subset in 0u32..1 << candidates.len() {
                let mut cases: Vec<u128> = candidates
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| subset >> i & 1 == 1)
                    .map(|(_, c)| *c)
                    .collect();
                if subset % 5 == 0 {
                    cases.extend(cases.clone()); // duplicate case values
                }
                let out = switch_default(r, cases.clone());
                for v in r.lo..=r.hi {
                    if !cases.contains(&v) && !member(&out, v) {
                        fail(
                            &mut failures,
                            format!("{r:?} cases {cases:?}: default {out:?} excludes {v}"),
                        );
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// The false edge of an UNSIGNED `Overflow` flag: the interpreter's result of
/// every pair that does not overflow lies in `unwrapped`.
#[test]
fn unwrapped_contains_every_non_overflowing_result() {
    let mut failures = Vec::new();
    for bits in [3, 4] {
        let ranges = intervals(bits);
        for op in OVERFLOWS {
            for a in &ranges {
                for b in &ranges {
                    let out = unwrapped(op, bits, *a, *b);
                    for x in a.lo..=a.hi {
                        for y in b.lo..=b.hi {
                            let (lhs, rhs) = (int(bits, false, x), int(bits, false, y));
                            let Ok((v, false)) = eval_int_overflow(op, lhs, rhs, BlockId::new(0))
                            else {
                                continue;
                            };
                            if !member(&out, v.raw) {
                                fail(
                                    &mut failures,
                                    format!(
                                        "{op:?}/{bits}b {a:?} {b:?} -> {out:?} misses {x},{y} = {}",
                                        v.raw
                                    ),
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    let mut rng = Rng(0xA110_C0B0_0000_0005);
    for bits in [8, 16, 32, 64, 128] {
        for _ in 0..8_000 {
            let (a_lo, a_hi) = rng.interval(bits);
            let (b_lo, b_hi) = rng.interval(bits);
            let (a, b) = (
                Range::span(bits, false, a_lo, a_hi),
                Range::span(bits, false, b_lo, b_hi),
            );
            for op in OVERFLOWS {
                let out = unwrapped(op, bits, a, b);
                for _ in 0..6 {
                    let (x, y) = (sample_member(&mut rng, &a), sample_member(&mut rng, &b));
                    let (lhs, rhs) = (int(bits, false, x), int(bits, false, y));
                    if let Ok((v, false)) = eval_int_overflow(op, lhs, rhs, BlockId::new(0))
                        && !member(&out, v.raw)
                    {
                        fail(
                            &mut failures,
                            format!(
                                "{op:?}/{bits}b {a:?} {b:?} -> {out:?} misses {x},{y} = {}",
                                v.raw
                            ),
                        );
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}
