// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `Formula::to_smtlib` was split into a per-node spelling
// (`Formula::write_smtlib_node`) and an iterative tree walk, so that the tree
// printer and the sharing printers of `formula_dag` share one source of
// spelling. The split must not move a byte: this test keeps the recursive
// printer exactly as it stood before the split (`legacy` below, copied
// verbatim with `x.to_smtlib()` on a sub-formula written `legacy(x)`) and
// holds the new printer equal to it on a witness of every variant, on random
// compositions of them, and on the literal and width edge cases.

use trust_ir_contract::formula_census::{formula_variant_names, variant_name, witnesses};
use trust_ir_contract::formula_dag::Shell;
use trust_ir_contract::{Formula, RoundingMode, Sort, Symbol, escape_smtlib_symbol};

fn scaled_pow2_decimal(multiplier: u32, exp: u32, minus_one: bool) -> String {
    if multiplier == 0 {
        return "0".to_string();
    }
    // Little-endian decimal digits of `multiplier`.
    let mut digits: Vec<u8> = Vec::new();
    let mut m = multiplier;
    while m > 0 {
        digits.push((m % 10) as u8);
        m /= 10;
    }
    for _ in 0..exp {
        let mut carry = 0u8;
        for d in digits.iter_mut() {
            let v = *d * 2 + carry;
            *d = v % 10;
            carry = v / 10;
        }
        while carry > 0 {
            digits.push(carry % 10);
            carry /= 10;
        }
    }
    if minus_one {
        // `multiplier >= 1` so the value is >= 1 and the borrow terminates
        // inside the digit vector.
        let mut i = 0;
        while i < digits.len() {
            if digits[i] > 0 {
                digits[i] -= 1;
                break;
            }
            digits[i] = 9;
            i += 1;
        }
        while digits.len() > 1 && digits[digits.len() - 1] == 0 {
            digits.pop();
        }
    }
    digits.iter().rev().map(|d| char::from(b'0' + d)).collect()
}

/// `2^width` as an exact decimal string, overflow-free for any width. Used to
/// build the signed `BvToInt` correction term, where a wrong `2^width` would
/// mistranslate negative values and could surface as a false-PROVE.
fn pow2_decimal(width: u32) -> String {
    scaled_pow2_decimal(1, width, false)
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
}

/// A random composition of witnesses: the shell of a random witness with
/// its child slots filled by smaller random compositions. Sorts are ignored
/// (the printers do not read them); every variant appears at every depth.
fn compose(rng: &mut Rng, pool: &[Formula], depth: u32) -> Formula {
    let w = &pool[rng.below(pool.len())];
    let shell = Shell::of(w);
    if depth == 0 || shell.arity() == 0 {
        return w.clone();
    }
    let kids = (0..shell.arity())
        .map(|_| compose(rng, pool, depth - 1))
        .collect();
    shell.rebuild(kids).expect("arity matches")
}

#[test]
fn every_witness_prints_as_before() {
    let pool = witnesses();
    let names: Vec<&str> = pool.iter().map(variant_name).collect();
    for name in formula_variant_names() {
        assert!(names.contains(name), "no witness of {name}");
    }
    for w in &pool {
        assert_eq!(w.to_smtlib(), legacy(w), "{w:?}");
    }
}

#[test]
fn random_compositions_print_as_before() {
    let pool = witnesses();
    let mut rng = Rng(0x7a11_c0de);
    for _ in 0..3000 {
        let f = compose(&mut rng, &pool, 5);
        let mut appended = String::from("prefix:");
        f.write_smtlib(&mut appended);
        let want = legacy(&f);
        assert_eq!(f.to_smtlib(), want);
        assert_eq!(appended, format!("prefix:{want}"));
    }
}

#[test]
fn literal_and_width_edge_cases_print_as_before() {
    let mut cases = Vec::new();
    for v in [i128::MIN, i128::MIN + 1, -1, 0, 1, i128::MAX] {
        cases.push(Formula::Int(v));
        for width in [1, 7, 8, 63, 64, 127, 128] {
            cases.push(Formula::BitVec { value: v, width });
        }
    }
    for v in [0, 1, u128::MAX] {
        cases.push(Formula::UInt(v));
    }
    for name in [
        "x", "", "1", "a b", "a|b", "a\\b", "_4.0", "arr$v0", "dag!0_0",
    ] {
        cases.push(Formula::Var(name.into(), Sort::Int));
        cases.push(Formula::SymVar(Symbol::intern(name), Sort::Int));
        cases.push(Formula::Pred(Symbol::intern(name), vec![]));
        cases.push(Formula::FnApp {
            func: name.into(),
            args: vec![Formula::Int(1)],
            sort: Sort::Int,
        });
    }
    let fv = || Box::new(Formula::Var("x".into(), Sort::Float { eb: 11, sb: 53 }));
    let rm = |m| Box::new(Formula::FpRoundingMode(m));
    for width in (0..=140).chain([200, 1024]) {
        for (eb, sb) in [(8, 24), (11, 53), (15, 113)] {
            cases.push(Formula::FpToSbv {
                rm: rm(RoundingMode::RTZ),
                value: fv(),
                width,
                eb,
                sb,
            });
            cases.push(Formula::FpToUbv {
                rm: rm(RoundingMode::RNA),
                value: fv(),
                width,
                eb,
                sb,
            });
        }
        cases.push(Formula::BvToInt(
            Box::new(Formula::Var("v".into(), Sort::BitVec(width))),
            width,
            true,
        ));
    }
    for (num, den) in [
        ("0", "1"),
        ("-1", "2"),
        ("7", "1"),
        ("-340282366920938463463374607431768211457", "3"),
    ] {
        cases.push(Formula::rat(num, den).expect("canonical"));
    }
    cases.push(Formula::Forall(vec![], Box::new(Formula::Bool(true))));
    cases.push(Formula::Exists(
        vec![
            (Symbol::intern("a b"), Sort::Int),
            (
                Symbol::intern("c"),
                Sort::Array(Box::new(Sort::Int), Box::new(Sort::Real)),
            ),
        ],
        Box::new(Formula::Bool(false)),
    ));
    for f in &cases {
        assert_eq!(f.to_smtlib(), legacy(f), "{f:?}");
    }
}

/// The legacy printer, verbatim (see the file header; the closures that
/// called the `to_smtlib` method now call `legacy`).
#[allow(clippy::too_many_lines, clippy::redundant_closure)]
pub fn legacy(f: &Formula) -> String {
    match f {
        // Literals
        Formula::Bool(true) => "true".to_string(),
        Formula::Bool(false) => "false".to_string(),
        Formula::UInt(n) => n.to_string(),
        Formula::Int(n) => {
            if *n < 0 {
                let abs = n.unsigned_abs();
                format!("(- {abs})")
            } else {
                n.to_string()
            }
        }
        Formula::BitVec { value, width } => {
            if *value >= 0 {
                format!("(_ bv{value} {width})")
            } else {
                // Use u128 for two's complement to handle width=128 correctly.
                // i128 mask overflows at width=128; u128::MAX is the correct all-ones mask.
                let mask: u128 = if *width < 128 {
                    (1u128 << width) - 1
                } else {
                    u128::MAX
                };
                let twos_comp = (*value as u128) & mask;
                format!("(_ bv{twos_comp} {width})")
            }
        }

        // Variables
        Formula::Var(name, _sort) => escape_smtlib_symbol(name),
        Formula::SymVar(sym, _sort) => escape_smtlib_symbol(sym.as_str()),

        // Boolean connectives
        Formula::Not(inner) => format!("(not {})", legacy(inner)),
        Formula::And(terms) => {
            if terms.is_empty() {
                "true".to_string()
            } else if terms.len() == 1 {
                legacy(&terms[0])
            } else {
                let parts: Vec<String> = terms.iter().map(|t| legacy(t)).collect();
                format!("(and {})", parts.join(" "))
            }
        }
        Formula::Or(terms) => {
            if terms.is_empty() {
                "false".to_string()
            } else if terms.len() == 1 {
                legacy(&terms[0])
            } else {
                let parts: Vec<String> = terms.iter().map(|t| legacy(t)).collect();
                format!("(or {})", parts.join(" "))
            }
        }
        Formula::Implies(a, b) => {
            format!("(=> {} {})", legacy(a), legacy(b))
        }

        // Comparisons
        Formula::Eq(a, b) => format!("(= {} {})", legacy(a), legacy(b)),
        Formula::Lt(a, b) => format!("(< {} {})", legacy(a), legacy(b)),
        Formula::Le(a, b) => format!("(<= {} {})", legacy(a), legacy(b)),
        Formula::Gt(a, b) => format!("(> {} {})", legacy(a), legacy(b)),
        Formula::Ge(a, b) => format!("(>= {} {})", legacy(a), legacy(b)),

        // Integer arithmetic
        Formula::Add(a, b) => format!("(+ {} {})", legacy(a), legacy(b)),
        Formula::Sub(a, b) => format!("(- {} {})", legacy(a), legacy(b)),
        Formula::Mul(a, b) => format!("(* {} {})", legacy(a), legacy(b)),
        // Rust integer `/` and `%` are TRUNCATED (quotient toward zero; the
        // remainder takes the sign of the dividend). SMT-LIB integer `div`/`mod`
        // are EUCLIDEAN (`mod` is always non-negative; `div` floors toward -inf),
        // which diverges for negative dividends. Lowering `%`/`/` as bare
        // `mod`/`div` proved sign/range properties that real Rust violates — e.g.
        // `#[ensures(result >= 0)] fn f(x:i32)->i32 { x % 256 }` was falsely
        // Proved although `(-1) % 256 == -1`. Encode truncation explicitly. For
        // non-negative operands (all unsigned div/rem) these reduce to plain
        // `div`/`mod`, so the encoding is correct for both signed and unsigned.
        // (Division by zero is governed by a separate div-by-zero VC, so the
        // unconstrained `mod`/`div` value at b==0 is not relied upon here.)
        Formula::Rem(a, b) => {
            let a = legacy(a);
            let b = legacy(b);
            // trem(a,b) = ite(a >= 0, mod(a,b), -mod(-a,b))
            format!("(ite (>= {a} 0) (mod {a} {b}) (- (mod (- {a}) {b})))")
        }
        Formula::Div(a, b) => {
            let a = legacy(a);
            let b = legacy(b);
            // a == b*tdiv + trem, so tdiv = (a - trem)/b is an EXACT division
            // (remainder 0) where Euclidean `div` agrees with truncation.
            let trem = format!("(ite (>= {a} 0) (mod {a} {b}) (- (mod (- {a}) {b})))");
            format!("(div (- {a} {trem}) {b})")
        }
        Formula::Neg(inner) => format!("(- {})", legacy(inner)),

        // Bitvector arithmetic
        Formula::BvAdd(a, b, _) => format!("(bvadd {} {})", legacy(a), legacy(b)),
        Formula::BvSub(a, b, _) => format!("(bvsub {} {})", legacy(a), legacy(b)),
        Formula::BvMul(a, b, _) => format!("(bvmul {} {})", legacy(a), legacy(b)),
        Formula::BvUDiv(a, b, _) => format!("(bvudiv {} {})", legacy(a), legacy(b)),
        Formula::BvSDiv(a, b, _) => format!("(bvsdiv {} {})", legacy(a), legacy(b)),
        Formula::BvURem(a, b, _) => format!("(bvurem {} {})", legacy(a), legacy(b)),
        Formula::BvSRem(a, b, _) => format!("(bvsrem {} {})", legacy(a), legacy(b)),
        Formula::BvAnd(a, b, _) => format!("(bvand {} {})", legacy(a), legacy(b)),
        Formula::BvOr(a, b, _) => format!("(bvor {} {})", legacy(a), legacy(b)),
        Formula::BvXor(a, b, _) => format!("(bvxor {} {})", legacy(a), legacy(b)),
        Formula::BvNot(inner, _) => format!("(bvnot {})", legacy(inner)),
        Formula::BvShl(a, b, _) => format!("(bvshl {} {})", legacy(a), legacy(b)),
        Formula::BvLShr(a, b, _) => format!("(bvlshr {} {})", legacy(a), legacy(b)),
        Formula::BvAShr(a, b, _) => format!("(bvashr {} {})", legacy(a), legacy(b)),

        // Bitvector comparisons
        Formula::BvULt(a, b, _) => format!("(bvult {} {})", legacy(a), legacy(b)),
        Formula::BvULe(a, b, _) => format!("(bvule {} {})", legacy(a), legacy(b)),
        Formula::BvSLt(a, b, _) => format!("(bvslt {} {})", legacy(a), legacy(b)),
        Formula::BvSLe(a, b, _) => format!("(bvsle {} {})", legacy(a), legacy(b)),

        // Bitvector conversions
        //
        // SMT-LIB FixedSizeBitVectors defines `bv2nat` (unsigned) and lets the
        // caller build signed conversion by subtracting 2^N when the sign bit is
        // set. We emit the SMT-LIB-standard name (`bv2nat`). A legacy spelling
        // (`bv2int`) exists in some non-standard solver dialects, but `ay`
        // recognizes only the standard form.
        Formula::BvToInt(inner, width, signed) => {
            let inner_smt = legacy(inner);
            if *signed {
                let two_to_width = pow2_decimal(*width);
                format!(
                    "(ite (bvsge {inner_smt} (_ bv0 {width})) \
                     (bv2nat {inner_smt}) \
                     (- (bv2nat {inner_smt}) {two_to_width}))"
                )
            } else {
                format!("(bv2nat {inner_smt})")
            }
        }
        Formula::IntToBv(inner, width) => {
            format!("((_ int2bv {width}) {})", legacy(inner))
        }
        Formula::BvExtract { inner, high, low } => {
            format!("((_ extract {high} {low}) {})", legacy(inner))
        }
        Formula::BvConcat(a, b) => format!("(concat {} {})", legacy(a), legacy(b)),
        Formula::BvZeroExt(inner, bits) => {
            format!("((_ zero_extend {bits}) {})", legacy(inner))
        }
        Formula::BvSignExt(inner, bits) => {
            format!("((_ sign_extend {bits}) {})", legacy(inner))
        }

        // Conditional
        Formula::Ite(cond, then, els) => {
            format!("(ite {} {} {})", legacy(cond), legacy(then), legacy(els))
        }

        // Quantifiers
        Formula::Forall(bindings, body) => {
            let params: Vec<String> = bindings
                .iter()
                .map(|(name, sort)| {
                    format!(
                        "({} {})",
                        escape_smtlib_symbol(name.as_str()),
                        sort.to_smtlib()
                    )
                })
                .collect();
            format!("(forall ({}) {})", params.join(" "), legacy(body))
        }
        Formula::Exists(bindings, body) => {
            let params: Vec<String> = bindings
                .iter()
                .map(|(name, sort)| {
                    format!(
                        "({} {})",
                        escape_smtlib_symbol(name.as_str()),
                        sort.to_smtlib()
                    )
                })
                .collect();
            format!("(exists ({}) {})", params.join(" "), legacy(body))
        }

        // Arrays
        Formula::Select(arr, idx) => {
            format!("(select {} {})", legacy(arr), legacy(idx))
        }
        Formula::Store(arr, idx, val) => {
            format!("(store {} {} {})", legacy(arr), legacy(idx), legacy(val))
        }

        // ── IEEE-754 floating point (SMT-LIB FloatingPoint theory) ──────
        Formula::FpConst { bits, eb, sb } => {
            format!("((_ to_fp {eb} {sb}) (_ bv{bits} {}))", eb + sb)
        }
        Formula::FpNaN { eb, sb } => format!("(_ NaN {eb} {sb})"),
        Formula::FpInf { neg, eb, sb } => {
            if *neg {
                format!("(_ -oo {eb} {sb})")
            } else {
                format!("(_ +oo {eb} {sb})")
            }
        }
        Formula::FpZero { neg, eb, sb } => {
            if *neg {
                format!("(_ -zero {eb} {sb})")
            } else {
                format!("(_ +zero {eb} {sb})")
            }
        }
        Formula::FpRoundingMode(rm) => rm.to_smtlib().to_string(),
        Formula::FpAdd(rm, a, b) => {
            format!("(fp.add {} {} {})", legacy(rm), legacy(a), legacy(b))
        }
        Formula::FpSub(rm, a, b) => {
            format!("(fp.sub {} {} {})", legacy(rm), legacy(a), legacy(b))
        }
        Formula::FpMul(rm, a, b) => {
            format!("(fp.mul {} {} {})", legacy(rm), legacy(a), legacy(b))
        }
        Formula::FpDiv(rm, a, b) => {
            format!("(fp.div {} {} {})", legacy(rm), legacy(a), legacy(b))
        }
        Formula::FpFma(rm, a, b, c) => format!(
            "(fp.fma {} {} {} {})",
            legacy(rm),
            legacy(a),
            legacy(b),
            legacy(c)
        ),
        Formula::FpSqrt(rm, a) => {
            format!("(fp.sqrt {} {})", legacy(rm), legacy(a))
        }
        Formula::FpRem(a, b) => format!("(fp.rem {} {})", legacy(a), legacy(b)),
        Formula::FpNeg(a) => format!("(fp.neg {})", legacy(a)),
        Formula::FpAbs(a) => format!("(fp.abs {})", legacy(a)),
        Formula::FpMin(a, b) => format!("(fp.min {} {})", legacy(a), legacy(b)),
        Formula::FpMax(a, b) => format!("(fp.max {} {})", legacy(a), legacy(b)),
        Formula::FpEq(a, b) => format!("(fp.eq {} {})", legacy(a), legacy(b)),
        Formula::FpLt(a, b) => format!("(fp.lt {} {})", legacy(a), legacy(b)),
        Formula::FpLe(a, b) => format!("(fp.leq {} {})", legacy(a), legacy(b)),
        Formula::FpGt(a, b) => format!("(fp.gt {} {})", legacy(a), legacy(b)),
        Formula::FpGe(a, b) => format!("(fp.geq {} {})", legacy(a), legacy(b)),
        Formula::FpIsNaN(a) => format!("(fp.isNaN {})", legacy(a)),
        Formula::FpIsInfinite(a) => format!("(fp.isInfinite {})", legacy(a)),
        Formula::FpIsZero(a) => format!("(fp.isZero {})", legacy(a)),
        Formula::FpIsNormal(a) => format!("(fp.isNormal {})", legacy(a)),
        Formula::FpIsSubnormal(a) => format!("(fp.isSubnormal {})", legacy(a)),
        Formula::FpIsNegative(a) => format!("(fp.isNegative {})", legacy(a)),
        Formula::FpIsPositive(a) => format!("(fp.isPositive {})", legacy(a)),
        Formula::FpFromBits { bits, eb, sb } => {
            format!("((_ to_fp {eb} {sb}) {})", legacy(bits))
        }
        // FP -> BV bit reinterpret (inverse of `to_fp` on a bit pattern). The
        // result width is inferred by the solver from the inner FP sort, so no
        // width index is carried. The concrete solver lowering / bijection
        // axioms are applied by the `trust-types` ay bridge downstream.
        Formula::FpToIeeeBv(a) => format!("(fp.to_ieee_bv {})", legacy(a)),
        // The saturating conversions lower to a COMPLETE guarded
        // expansion, never the bare SMT operator: `fp.to_sbv`/`fp.to_ubv`
        // are UNSPECIFIED for NaN and out-of-range inputs, while these
        // nodes are TOTAL with the AArch64 reading (NaN -> 0, out-of-range
        // -> clamp). Emitting the bare operator would let a solver choose
        // arbitrary values exactly where the semantics promise saturation.
        //
        // Bounds are exact: powers of two are representable in any format
        // whose exponent range admits them (f32/f64 do for width <= 64),
        // and each bound is written as `to_fp` of a wider bitvector
        // literal in the operand's own format, which the node carries.
        // Boundary subtlety on the low side: overflow is x <= MIN-1, and
        // in formats too coarse to represent MIN-1 the bound rounds to
        // MIN — where the guard may fire on x == MIN exactly, but the
        // clamp value IS the true conversion there, so the answer is
        // unchanged.
        //
        // The clamp CONSTANTS are built with `scaled_pow2_decimal`, not
        // `1u128 << n`. `width` is a `u32` and nothing in this contract
        // bounds it, while a u128 shift is defined only to 127 — so the
        // shift spelling was exact only to width 125 (signed, whose
        // widest shift count is `w + 2`) and 127 (unsigned). Above that
        // it panicked in debug and, worse, MASKED the shift count in
        // release: `1u128 << 128 == 1`, a silently wrong bound with no
        // diagnostic. The native lane (trust's `ay_bridge`
        // `fp_to_bv_saturating`) has always computed these same constants
        // in bignum arithmetic, so the two lanes used to clamp
        // DIFFERENTLY above width 125/127. They no longer do: these
        // constants are now exact at every width, constant for constant
        // and literal-width for literal-width.
        Formula::FpToSbv {
            rm,
            value,
            width,
            eb,
            sb,
        } => {
            let w = *width;
            let x = legacy(value);
            let rm = legacy(rm);
            // Width 0 is not a legal SMT-LIB bitvector width and every
            // consumer refuses it upstream; saturate rather than
            // underflow so this formatter stays total.
            let hi = w.saturating_sub(1);
            // 2^(w-1) as an unsigned (w+1)-bit literal, in the operand's format.
            let pos = format!(
                "((_ to_fp_unsigned {eb} {sb}) RNE (_ bv{} {}))",
                pow2_decimal(hi),
                w + 1
            );
            // -(2^(w-1)) - 1 as a signed (w+2)-bit literal. In two's
            // complement on w+2 bits that is 2^(w+2) - 2^(w-1) - 1, i.e.
            // 7 * 2^(w-1) - 1.
            let min_minus_one = scaled_pow2_decimal(7, hi, true);
            let neg = format!("((_ to_fp {eb} {sb}) RNE (_ bv{min_minus_one} {}))", w + 2);
            let max_bv = format!("(_ bv{} {w})", scaled_pow2_decimal(1, hi, true));
            let min_bv = format!("(_ bv{} {w})", pow2_decimal(hi));
            format!(
                "(ite (fp.isNaN {x}) (_ bv0 {w}) \
                 (ite (fp.geq {x} {pos}) {max_bv} \
                 (ite (fp.leq {x} {neg}) {min_bv} \
                 ((_ fp.to_sbv {w}) {rm} {x}))))"
            )
        }
        Formula::FpToUbv {
            rm,
            value,
            width,
            eb,
            sb,
        } => {
            let w = *width;
            let x = legacy(value);
            let rm = legacy(rm);
            // 2^w as an unsigned (w+1)-bit literal.
            let pos = format!(
                "((_ to_fp_unsigned {eb} {sb}) RNE (_ bv{} {}))",
                pow2_decimal(w),
                w + 1
            );
            // -1.0 in the operand's format.
            let neg_one = format!(
                "(fp.neg ((_ to_fp_unsigned {eb} {sb}) RNE (_ bv1 {})))",
                w + 1
            );
            let max_bv = format!("(_ bv{} {w})", scaled_pow2_decimal(1, w, true));
            format!(
                "(ite (fp.isNaN {x}) (_ bv0 {w}) \
                 (ite (fp.geq {x} {pos}) {max_bv} \
                 (ite (fp.leq {x} {neg_one}) (_ bv0 {w}) \
                 ((_ fp.to_ubv {w}) {rm} {x}))))"
            )
        }
        Formula::FpFromSbv { rm, value, eb, sb } => {
            format!("((_ to_fp {eb} {sb}) {} {})", legacy(rm), legacy(value))
        }
        Formula::FpFromUbv { rm, value, eb, sb } => format!(
            "((_ to_fp_unsigned {eb} {sb}) {} {})",
            legacy(rm),
            legacy(value)
        ),
        Formula::FpConvert { rm, value, eb, sb } => {
            format!("((_ to_fp {eb} {sb}) {} {})", legacy(rm), legacy(value))
        }

        // Uninterpreted predicate application (EUF). Lowers to a bare symbol
        // when nullary, or `(name arg1 ..)` otherwise. The symbol's
        // `(declare-fun name (<arg-sorts>) Bool)` is emitted once by the
        // backend's declaration collector; the application is opaque to the
        // solver (no axioms).
        Formula::Pred(name, args) => {
            let sym = escape_smtlib_symbol(name.as_str());
            if args.is_empty() {
                sym
            } else {
                let parts: Vec<String> = args.iter().map(legacy).collect();
                format!("({} {})", sym, parts.join(" "))
            }
        }

        // ── Algebraic-datatype terms (Lever A) ──────────────────────────
        // The `(declare-datatype …)` that DEFINES the sort is emitted
        // separately from the datatype-sorted variable's `Sort`
        // (`Sort::datatype_declarations`); here we only reference its
        // constructors/selectors/testers.
        Formula::Ctor { ctor, args, sort } => {
            let ctor_sym = escape_smtlib_symbol(ctor);
            if args.is_empty() {
                // A nullary constructor is a bare constant, not a 0-ary
                // application; qualify it with its datatype sort
                // (`(as C Sort)`) so constructors shared across datatype
                // families are unambiguous — matches the in-process ay path.
                format!("(as {} {})", ctor_sym, sort.to_smtlib())
            } else {
                let parts: Vec<String> = args.iter().map(legacy).collect();
                format!("({} {})", ctor_sym, parts.join(" "))
            }
        }
        Formula::Sel { field, arg, .. } => {
            format!("({} {})", escape_smtlib_symbol(field), legacy(arg))
        }
        Formula::IsCtor { ctor, arg, .. } => {
            format!("((_ is {}) {})", escape_smtlib_symbol(ctor), legacy(arg))
        }

        // Uninterpreted function application (EUF). Lowers like `Pred` —
        // a bare symbol when nullary, `(func arg1 ..)` otherwise; the
        // result-sorted `declare-fun` is the backend's job.
        Formula::FnApp { func, args, .. } => {
            let sym = escape_smtlib_symbol(func);
            if args.is_empty() {
                sym
            } else {
                let parts: Vec<String> = args.iter().map(legacy).collect();
                format!("({} {})", sym, parts.join(" "))
            }
        }

        // Exact rational literal (`Reals` theory): `(/ n d)`, `(- n)` for a
        // negative numerator, a bare numeral when integral.
        Formula::Rat(lit) => lit.to_smtlib(),

        // Constant array: the sort-qualified `const` of the full array
        // sort, applied to the element. Spelled from the two carried sorts
        // directly; the text is exactly `Sort::Array(I, E).to_smtlib()`
        // (a test holds the two spellings together) without cloning
        // either sort into one.
        Formula::ConstArray {
            index_sort,
            elem_sort,
            value,
        } => format!(
            "((as const (Array {} {})) {})",
            index_sort.to_smtlib(),
            elem_sort.to_smtlib(),
            legacy(value)
        ),
        other => panic!("the legacy oracle predates {other:?}"),
    }
}
