// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Aggregate-constant roundtrip fuzz test (issue #34).
//
// Generates randomized `Constant::Aggregate / Array / Vector / Sequence / Set /
// Record / Closure / FnDef / PhantomData` values (possibly nested) with
// a *fixed seed* and checks:
//
//   parse(display(c))       == c  (via parser feature, wrapped in a module)
//   deserialize(serialize(c)) == c (via binary feature, wrapped in a module)
//   from_json(to_json(c))   == c  (via serde feature, direct)
//   from_msgpack(to_msgpack(c)) == c (via serde feature, direct)
//
// Why handwritten instead of proptest/cargo-fuzz:
//
// - The `trust-ir` crate is zero-required-dep by policy (see CLAUDE.md feature
//   flag table). Adding proptest / rand / cargo-fuzz as a dev-dep would
//   introduce transitive dependencies on a crate that ships with zero.
// - A seeded xorshift generator is deterministic across platforms and
//   never flakes, which is the core property of a useful regression test.
// - Input counts (4096 per path) are kept high enough to exercise deep
//   nesting and edge-case variants while keeping the test sub-second.
//
// This file is only meaningfully exercised when both `parser` and `binary`
// features are enabled (the typical `--all-features` run). Individual
// sub-tests guard their own feature requirements.

#![cfg(all(feature = "parser", feature = "binary"))]

use trust_ir::value::{ClosureTyId, FuncId, RecordId, TyId};
use trust_ir::{ClosureTy, Constant, FuncTy, Global, Linkage, Module, SetRepr, Ty};

// ---------------------------------------------------------------------------
// Deterministic xorshift64 generator (no external rand dep).
// ---------------------------------------------------------------------------

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        // Avoid the zero fixed-point of xorshift.
        Self {
            state: if seed == 0 {
                0x9E37_79B9_7F4A_7C15
            } else {
                seed
            },
        }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    fn bounded(&mut self, n: u32) -> u32 {
        // Unbiased enough for test generation; we don't need cryptographic
        // uniformity, just determinism and coverage.
        if n == 0 {
            0
        } else {
            (self.next_u64() as u32) % n
        }
    }

    fn one_of<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        let idx = self.bounded(xs.len() as u32) as usize;
        &xs[idx]
    }
}

// ---------------------------------------------------------------------------
// Random constant generator (bounded depth, bounded arity).
// ---------------------------------------------------------------------------

/// Max nesting depth. Keeps generated inputs from exploding in size.
const MAX_DEPTH: u32 = 4;
/// Max elements per aggregate (Aggregate / Array / Vector / Sequence / Set / Record /
/// Closure captures). Small to keep the parser's text form under a sane
/// number of tokens per case.
const MAX_ELEMS: u32 = 6;

/// Ascii-only field names drawn from this pool. Record parsing requires
/// identifier-like field names (no quoting), so we keep them alphabetic.
const FIELD_NAMES: &[&str] = &[
    "a", "b", "c", "d", "e", "f", "x", "y", "z", "alpha", "beta", "gamma",
];

/// Generate a full-finite-f64 scalar for the parser + binary fuzz paths.
///
/// After issues #45 (whole floats displayed as ints), #46 (i128 literals
/// outside i64 range), and #47 (large-magnitude finite floats) were
/// fixed, the parser + binary codecs round-trip the full finite f64
/// range and the full i128 integer range. This generator exercises both
/// so the fuzzer keeps #45/#47 shapes alive as regression coverage.
fn gen_scalar_parse_safe(r: &mut Rng) -> Constant {
    match r.bounded(3) {
        0 => gen_scalar_int(r),
        1 => {
            // Finite f64 across the full magnitude range. After #45 and
            // #47 Display always carries `.` or `e`, so the parser takes
            // the float branch and round-trips every finite f64.
            match r.bounded(6) {
                0 => Constant::Float(0.0),
                1 => {
                    // Whole-number float — the #45 repro shape.
                    let sign = if r.bounded(2) == 1 { -1.0 } else { 1.0 };
                    Constant::Float(sign * (r.next_u64() % 1_000_000) as f64)
                }
                2 => {
                    // Large-magnitude float — the #47 repro shape.
                    let sign = if r.bounded(2) == 1 { -1.0 } else { 1.0 };
                    let exp = (r.bounded(300) as i32) - 150; // -150..=149
                    Constant::Float(sign * 10f64.powi(exp))
                }
                _ => {
                    // Mixed whole + fractional part.
                    let sign = if r.bounded(2) == 1 { -1.0 } else { 1.0 };
                    let whole = (r.next_u64() % 1_000_000) as f64;
                    let frac_num = (r.next_u64() % 1000) as f64; // 0..=999
                    Constant::Float(sign * (whole + frac_num / 1000.0))
                }
            }
        }
        _ => Constant::Bool(r.bounded(2) == 1),
    }
}

/// Generate a scalar for the serde (JSON / MessagePack) fuzz paths.
///
/// The #48 fix (bit-exact f64 codec in `Constant::Float`) makes every
/// IEEE-754 bit pattern — finite, subnormal, `±0.0`, `±∞`, quiet and
/// signaling NaN payloads — round-trip through both JSON and MessagePack.
/// This generator therefore samples the full f64 bit-space uniformly so
/// the fuzzer exercises the codec on arbitrary values rather than just
/// the narrow, precision-safe range used by `gen_scalar_parse_safe`.
fn gen_scalar_serde(r: &mut Rng) -> Constant {
    match r.bounded(3) {
        0 => gen_scalar_int(r),
        1 => {
            // Sample the full 64-bit f64 space. Handpicked extrema are
            // mixed in so every run hits the documented corners even if
            // the uniform draw doesn't land on them.
            match r.bounded(16) {
                0 => Constant::Float(0.0),
                1 => Constant::Float(-0.0),
                2 => Constant::Float(f64::INFINITY),
                3 => Constant::Float(f64::NEG_INFINITY),
                4 => Constant::Float(f64::NAN),
                5 => Constant::Float(f64::from_bits(0x7ff0_0000_0000_0001)), // signaling NaN
                6 => Constant::Float(f64::from_bits(0x7ff8_0000_1234_5678)), // quiet NaN w/ payload
                7 => Constant::Float(f64::from_bits(1)),                     // smallest subnormal
                8 => Constant::Float(f64::MIN_POSITIVE),
                9 => Constant::Float(f64::from_bits(0x7fef_ffff_ffff_ffff)), // largest finite
                10 => Constant::Float(2.1747727453455723e-213),              // issue-48 pattern
                _ => Constant::Float(f64::from_bits(r.next_u64())),
            }
        }
        _ => Constant::Bool(r.bounded(2) == 1),
    }
}

/// Integer scalar for both parse-safe and serde paths. After #46 the
/// parser accepts the full i128 range, so we exercise it here.
fn gen_scalar_int(r: &mut Rng) -> Constant {
    match r.bounded(8) {
        0 => Constant::Int(0),
        1 => Constant::Int(1),
        2 => Constant::Int(-1),
        3 => Constant::Int(i64::MAX as i128),
        4 => Constant::Int(i64::MIN as i128),
        5 => Constant::Int(i128::MAX),
        6 => Constant::Int(i128::MIN),
        _ => Constant::Int((r.next_u64() as i64) as i128),
    }
}

/// A scalar generator — either parse-safe or full-f64-range — threaded
/// through the aggregate generator so the serde paths can exercise
/// arbitrary bit patterns inside nested constants.
type ScalarGen = fn(&mut Rng) -> Constant;

fn gen_constant(r: &mut Rng, depth: u32, scalar: ScalarGen) -> Constant {
    if depth == 0 {
        return scalar(r);
    }
    // 40% leaf, 60% aggregate-ish at each level to keep trees bounded.
    if r.bounded(10) < 4 {
        return scalar(r);
    }
    let kind = r.bounded(9);
    match kind {
        0 => Constant::Aggregate(gen_elems(r, depth, scalar)),
        1 => Constant::Array(gen_elems(r, depth, scalar)),
        2 => Constant::Vector(gen_elems(r, depth, scalar)),
        3 => Constant::Sequence(gen_elems(r, depth, scalar)),
        4 => Constant::Set(gen_elems(r, depth, scalar)),
        5 => {
            let n = r.bounded(MAX_ELEMS) as usize;
            let mut fields = Vec::with_capacity(n);
            for i in 0..n {
                // Use unique names across the record so display/parse
                // preserves them (record parsing is order-preserving).
                let base = r.one_of(FIELD_NAMES);
                let name = format!("{base}{i}");
                fields.push((name, gen_constant(r, depth - 1, scalar)));
            }
            Constant::Record(fields)
        }
        6 => {
            // Closure: small FuncId + 0..N captures, any depth.
            let func = FuncId::new(r.bounded(64));
            let n = r.bounded(MAX_ELEMS) as usize;
            let mut captures = Vec::with_capacity(n);
            for _ in 0..n {
                captures.push(gen_constant(r, depth - 1, scalar));
            }
            Constant::Closure { func, captures }
        }
        7 => Constant::FnDef(FuncId::new(r.bounded(64))),
        _ => Constant::PhantomData,
    }
}

fn gen_elems(r: &mut Rng, depth: u32, scalar: ScalarGen) -> Vec<Constant> {
    let n = r.bounded(MAX_ELEMS) as usize;
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        out.push(gen_constant(r, depth - 1, scalar));
    }
    out
}

// ---------------------------------------------------------------------------
// Module wrappers used by parser / binary roundtrips.
// ---------------------------------------------------------------------------
//
// Constants are serialized as part of a Module, not as a free-standing
// value. To roundtrip an arbitrary aggregate constant we wrap it in a
// single global initializer and assert the global survives the roundtrip
// with identical shape.

fn decl_ty_for_wrapper(module: &mut Module, c: &Constant) -> Ty {
    match c {
        Constant::Int(_) => Ty::I64,
        // v24: canonical U128 values exceed i128::MAX, so the only faithful
        // declared type is U128 itself.
        Constant::U128(_) => Ty::U128,
        // v25: bytes fit [u8; N].
        Constant::Bytes { data, .. } => {
            let tid = module.add_type(Ty::U8);
            Ty::Array(tid, data.len() as u64)
        }
        Constant::Float(_) => Ty::F64,
        Constant::Bool(_) => Ty::Bool,
        Constant::Aggregate(_) => {
            // Generic aggregate — declared as a Tuple of matching arity
            // filled with Unit. The validator is *not* run on this module
            // so shape-only declared type suffices for display/parse tests.
            Ty::Tuple(vec![])
        }
        Constant::Array(elems) => {
            let tid = module.add_type(Ty::I64);
            Ty::Array(tid, elems.len() as u64)
        }
        Constant::Vector(elems) => Ty::Vector(Box::new(Ty::I64), elems.len().max(1) as u32),
        Constant::Sequence(_) => {
            // Need a TyId pointing into module.types. Use a dummy element.
            let tid = module.add_type(Ty::I64);
            Ty::Sequence(tid)
        }
        Constant::Set(_) => {
            let tid = module.add_type(Ty::I64);
            Ty::Set(tid, SetRepr::Boxed)
        }
        Constant::Record(_) => Ty::Record(RecordId::new(0)),
        Constant::Closure { .. } => {
            // Register a closure type with no captures; the constant's
            // declared-captures is not used by serialization (only the
            // constant tree itself is).
            let ft = module.add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
            });
            let cid = module.add_closure_type(ClosureTy::bare(ft));
            Ty::Closure(cid)
        }
        Constant::FnDef(_) => {
            let ft = module.add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
            });
            Ty::Func(ft)
        }
        // A relocatable symbol address is a native pointer-sized value.
        Constant::SymbolAddr { .. } => Ty::Ptr,
        Constant::PhantomData => Ty::Unit,
    }
}

fn wrap_module(name: &str, c: &Constant) -> Module {
    let mut m = Module::new(name);
    let ty = decl_ty_for_wrapper(&mut m, c);
    m.globals.push(Global {
        name: "C".to_string(),
        ty,
        mutable: false,
        initializer: Some(c.clone()),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    m
}

fn extract_const(m: &Module) -> &Constant {
    m.globals[0]
        .initializer
        .as_ref()
        .expect("initializer present")
}

// ---------------------------------------------------------------------------
// Roundtrip oracles.
// ---------------------------------------------------------------------------

fn roundtrip_parse(c: &Constant) {
    let m = wrap_module("fuzz_parse", c);
    let text = format!("{}", m);
    let parsed = trust_ir::parser::parse_module(&text).unwrap_or_else(|e| {
        panic!("parse failed; text:\n---\n{text}\n---\nerror: {e}\nconstant: {c:?}");
    });
    assert_eq!(
        extract_const(&parsed),
        c,
        "parse mismatch for constant {c:?}\ntext:\n---\n{text}\n---"
    );
}

fn roundtrip_binary(c: &Constant) {
    let m = wrap_module("fuzz_binary", c);
    let bytes = trust_ir::binary::serialize_module(&m);
    let decoded = trust_ir::binary::deserialize_module(&bytes)
        .unwrap_or_else(|e| panic!("binary decode failed: {e:?} for {c:?}"));
    assert_eq!(
        extract_const(&decoded),
        c,
        "binary roundtrip mismatch for {c:?}"
    );
}

/// Bit-exact structural equality for constants.
///
/// `Constant` derives `PartialEq`, but that delegates `Float(f64)` to
/// `f64::eq` — which is IEEE-754 equality. Two NaN values with the same
/// bit pattern are therefore `!=` under the derive. For the serde fuzz
/// paths we want genuine identity of the serialized bytes, including
/// NaN payloads and `-0.0` vs `+0.0`. This helper walks the tree and
/// compares `Float` leaves via `f64::to_bits()`.
#[cfg(feature = "serde")]
fn bit_exact_eq(a: &Constant, b: &Constant) -> bool {
    match (a, b) {
        (Constant::Float(x), Constant::Float(y)) => x.to_bits() == y.to_bits(),
        (Constant::Int(x), Constant::Int(y)) => x == y,
        (Constant::Bool(x), Constant::Bool(y)) => x == y,
        (Constant::Aggregate(xs), Constant::Aggregate(ys))
        | (Constant::Array(xs), Constant::Array(ys))
        | (Constant::Vector(xs), Constant::Vector(ys))
        | (Constant::Sequence(xs), Constant::Sequence(ys))
        | (Constant::Set(xs), Constant::Set(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| bit_exact_eq(x, y))
        }
        (Constant::Record(xs), Constant::Record(ys)) => {
            xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys)
                    .all(|((xk, xv), (yk, yv))| xk == yk && bit_exact_eq(xv, yv))
        }
        (
            Constant::Closure {
                func: fa,
                captures: ca,
            },
            Constant::Closure {
                func: fb,
                captures: cb,
            },
        ) => fa == fb && ca.len() == cb.len() && ca.iter().zip(cb).all(|(x, y)| bit_exact_eq(x, y)),
        (Constant::FnDef(x), Constant::FnDef(y)) => x == y,
        (Constant::PhantomData, Constant::PhantomData) => true,
        _ => false,
    }
}

#[cfg(feature = "serde")]
fn roundtrip_serde_json(c: &Constant) {
    let json = serde_json::to_string(c).expect("json encode");
    let decoded: Constant = serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("json decode failed: {e} for {c:?}\njson: {json}"));
    assert!(
        bit_exact_eq(&decoded, c),
        "json roundtrip mismatch for {c:?}; decoded={decoded:?}; json={json}"
    );
}

#[cfg(feature = "serde")]
fn roundtrip_serde_msgpack(c: &Constant) {
    let bytes = rmp_serde::to_vec(c).expect("msgpack encode");
    let decoded: Constant = rmp_serde::from_slice(&bytes)
        .unwrap_or_else(|e| panic!("msgpack decode failed: {e} for {c:?}"));
    assert!(
        bit_exact_eq(&decoded, c),
        "msgpack roundtrip mismatch for {c:?}; decoded={decoded:?}"
    );
}

// ---------------------------------------------------------------------------
// Seeded fuzz tests.
// ---------------------------------------------------------------------------

/// How many random inputs each test runs. Chosen to exercise deep trees
/// across all variants in well under one second; tunable upwards for a
/// longer shakeout.
const N_CASES: u32 = 4096;

/// Fixed seeds. Changing a seed is equivalent to adding a new test — the
/// point of a seeded fuzzer is that a failing seed reproduces exactly.
const SEED_PARSE: u64 = 0xC0FF_EE00_1234_5678;
const SEED_BINARY: u64 = 0xDEAD_BEEF_CAFE_BABE;
const SEED_SERDE: u64 = 0x5A5A_A5A5_5A5A_A5A5;

#[test]
fn fuzz_parse_roundtrip_is_identity() {
    let mut r = Rng::new(SEED_PARSE);
    for i in 0..N_CASES {
        let c = gen_constant(&mut r, MAX_DEPTH, gen_scalar_parse_safe);
        roundtrip_parse(&c);
        // Safety net: also confirm clone-equality, which is a pre-req for
        // any roundtrip test to be meaningful.
        assert_eq!(c.clone(), c, "clone inequality at case {i}");
    }
}

#[test]
fn fuzz_binary_roundtrip_is_identity() {
    let mut r = Rng::new(SEED_BINARY);
    for _ in 0..N_CASES {
        let c = gen_constant(&mut r, MAX_DEPTH, gen_scalar_parse_safe);
        roundtrip_binary(&c);
    }
}

/// JSON fuzz path: use the unrestricted `gen_scalar_serde` so the full
/// f64 bit-space (NaN payloads, `±∞`, subnormals, `-0.0`, the historical
/// #48 precision corner) is exercised through the bit-exact codec.
#[cfg(feature = "serde")]
#[test]
fn fuzz_serde_json_roundtrip_is_identity() {
    let mut r = Rng::new(SEED_SERDE);
    for _ in 0..N_CASES {
        let c = gen_constant(&mut r, MAX_DEPTH, gen_scalar_serde);
        roundtrip_serde_json(&c);
    }
}

/// MessagePack fuzz path: same unrestricted generator. `rmp-serde` is
/// natively bit-faithful for finite f64; combined with the #48 codec
/// every 64-bit pattern round-trips.
#[cfg(feature = "serde")]
#[test]
fn fuzz_serde_msgpack_roundtrip_is_identity() {
    let mut r = Rng::new(SEED_SERDE ^ 0x1);
    for _ in 0..N_CASES {
        let c = gen_constant(&mut r, MAX_DEPTH, gen_scalar_serde);
        roundtrip_serde_msgpack(&c);
    }
}

// ---------------------------------------------------------------------------
// Corner-case regression tests (fixed inputs).
// ---------------------------------------------------------------------------

#[test]
fn corner_empty_aggregates_roundtrip() {
    let cases = [
        Constant::Aggregate(vec![]),
        Constant::Array(vec![]),
        Constant::Vector(vec![]),
        Constant::Sequence(vec![]),
        Constant::Set(vec![]),
        Constant::Record(vec![]),
        Constant::Closure {
            func: FuncId::new(0),
            captures: vec![],
        },
        Constant::FnDef(FuncId::new(0)),
        Constant::PhantomData,
    ];
    for c in &cases {
        roundtrip_parse(c);
        roundtrip_binary(c);
        #[cfg(feature = "serde")]
        {
            roundtrip_serde_json(c);
            roundtrip_serde_msgpack(c);
        }
    }
}

#[test]
fn corner_deeply_nested_aggregates_roundtrip() {
    // Sequence of Set of Record of Closure: exercise every variant path.
    let c = Constant::Sequence(vec![
        Constant::Set(vec![Constant::Int(42), Constant::Int(-42)]),
        Constant::Record(vec![
            ("k".to_string(), Constant::Bool(true)),
            (
                "clos".to_string(),
                Constant::Closure {
                    func: FuncId::new(9),
                    captures: vec![
                        Constant::Aggregate(vec![Constant::Int(0), Constant::Int(1)]),
                        Constant::Array(vec![Constant::PhantomData]),
                        Constant::Vector(vec![Constant::Bool(true), Constant::Bool(false)]),
                        Constant::Sequence(vec![Constant::Float(1.5)]),
                        Constant::FnDef(FuncId::new(3)),
                    ],
                },
            ),
        ]),
    ]);
    roundtrip_parse(&c);
    roundtrip_binary(&c);
    #[cfg(feature = "serde")]
    {
        roundtrip_serde_json(&c);
        roundtrip_serde_msgpack(&c);
    }
}

#[test]
fn corner_i128_extremes_roundtrip() {
    // i128 extremes now covered by ALL four paths. Prior to #46 the text
    // parser limited integer literals to i64 range; after the fix,
    // `parse_number` uses `i128::from_str` and accepts the full i128
    // domain that `Constant::Int` carries.
    for &v in &[
        i128::MIN,
        i128::MIN + 1,
        -1i128,
        0,
        1,
        i128::MAX - 1,
        i128::MAX,
    ] {
        let c = Constant::Int(v);
        roundtrip_parse(&c);
        roundtrip_binary(&c);
        #[cfg(feature = "serde")]
        {
            roundtrip_serde_json(&c);
            roundtrip_serde_msgpack(&c);
        }
    }
}

#[test]
fn corner_whole_valued_float_roundtrip() {
    // Regression for #45: `Constant::Float(n.0)` must round-trip through
    // the text parser. Prior to the fix, Display emitted bare `-43075`
    // for `-43075.0` and the parser read it back as `Constant::Int(-43075)`.
    for &v in &[
        -43075.0_f64,
        0.0,
        -0.0,
        1.0,
        -1.0,
        42.0,
        i64::MAX as f64,
        i64::MIN as f64,
    ] {
        let c = Constant::Float(v);
        roundtrip_parse(&c);
        roundtrip_binary(&c);
    }
}

#[test]
fn corner_large_magnitude_float_roundtrip() {
    // Regression for #47: very large / very small magnitude finite floats
    // must round-trip through the text parser. Prior to the fix, Display
    // for `1e300` emitted a 301-digit integer-shaped string that the
    // parser rejected as an overflowing integer literal.
    for &v in &[
        1e300_f64,
        -1e300,
        1e-300,
        -1e-300,
        1.5e38,
        -3.5e38,
        f64::MIN_POSITIVE,
        f64::MAX,
        f64::MIN,
        f64::EPSILON,
    ] {
        let c = Constant::Float(v);
        roundtrip_parse(&c);
        roundtrip_binary(&c);
    }
}

/// Keep a touchstone on TyId so imports are not warned as unused when
/// feature combinations dim certain helpers.
#[test]
fn _tyid_smoke() {
    let _ = TyId::new(0);
    let _ = ClosureTyId::new(0);
}
