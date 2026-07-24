// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// =============================================================================
//  AArch64 FP-ARITHMETIC ON-CHIP DIFFERENTIAL (FADD/FMUL, RNE rounding).
// =============================================================================
//
//  The INDEPENDENT ORACLE for proofs/aarch64_fp_arith.lean (the RNE rounding
//  arithmetic tier: FADD32/FADD64 + FMUL32/FMUL64).  Runs each REAL AArch64 FP
//  arithmetic instruction directly on this Apple Silicon CPU via
//  `std::arch::asm!` -- `fadd`/`fmul`, both `.s` (binary32) and `.d`
//  (binary64) -- with inputs supplied as BIT PATTERNS (transmuted u32/u64 ->
//  f32/f64), reads the result back as BIT PATTERNS, and emits one Clean theorem
//  per sampled pair:
//
//      AArch64FPArith.<op> <bits_a> <bits_b> = <chip_result_bits> := rfl
//
//  where each operand/result is a LSB-first `List Bool` literal of the exact
//  width (32 or 64).  `clean check` on the assembled file PASSES iff every
//  Clean def reduces to the chip's ACTUAL output for every sampled input -- a
//  genuine hardware differential.  If a theorem FAILS the Clean def is
//  unfaithful and must be fixed (NEVER the chip value).
//
//  The default FPCR rounding mode (RNE, round-to-nearest-ties-to-even) is in
//  effect; this harness validates RNE only (RTZ/RDN/RUP/RMM deferred).
//
//  COVERAGE is a CURATED grid that EXERCISES ROUNDING -- operand pairs whose
//  exact sum/product lands on a tie, just-below, and just-above a representable
//  boundary (nonzero guard/round/sticky, ties-to-even both directions) -- PLUS
//  all specials: NaN (qNaN + sNaN, both signs), +-Inf, Inf-Inf, Inf*0, +-0
//  sign rules, subnormal results via underflow, overflow to Inf, and exact
//  cancellation x+(-x).  These are the whole point and each is proven on
//  silicon.  binary32 carries the dense rounding grid (cheap to reduce);
//  binary64 carries a curated edge set (64-bit reduction is costly) that still
//  crosses every required rounding/special class.
//
//  Build/run (Apple Silicon, darwin arm64):
//      cargo run --release --bin fp_arith_harness -- <out.lean> [--neg]

#![cfg(target_arch = "aarch64")]

use std::arch::asm;
use std::io::Write;

// ---- real FP-arithmetic instruction wrappers (the chip is the oracle) -------
//  Inputs/outputs are BIT PATTERNS; we transmute to f32/f64 only to hold them
//  in vector registers across the asm, never to compute in Rust.

macro_rules! fp_bin_d {
    ($name:ident, $mn:literal) => {
        #[inline(never)]
        fn $name(a: u64, b: u64) -> u64 {
            let x = f64::from_bits(a);
            let y = f64::from_bits(b);
            let r: f64;
            unsafe {
                asm!(concat!($mn, " {r:d}, {a:d}, {b:d}"),
                     r = out(vreg) r, a = in(vreg) x, b = in(vreg) y,
                     options(pure, nomem, nostack));
            }
            r.to_bits()
        }
    };
}
macro_rules! fp_bin_s {
    ($name:ident, $mn:literal) => {
        #[inline(never)]
        fn $name(a: u32, b: u32) -> u32 {
            let x = f32::from_bits(a);
            let y = f32::from_bits(b);
            let r: f32;
            unsafe {
                asm!(concat!($mn, " {r:s}, {a:s}, {b:s}"),
                     r = out(vreg) r, a = in(vreg) x, b = in(vreg) y,
                     options(pure, nomem, nostack));
            }
            r.to_bits()
        }
    };
}

fp_bin_d!(d_fadd, "fadd");
fp_bin_d!(d_fmul, "fmul");
fp_bin_s!(s_fadd, "fadd");
fp_bin_s!(s_fmul, "fmul");

// ---- LSB-first `List Bool` literal of an n-bit value ------------------------
fn bits(v: u64, w: u32) -> String {
    let mut s = String::with_capacity(w as usize * 7);
    s.push('[');
    for i in 0..w {
        if i > 0 {
            s.push_str(", ");
        }
        s.push_str(if (v >> i) & 1 == 1 { "true" } else { "false" });
    }
    s.push(']');
    s
}

// ====== binary32 helpers to BUILD rounding-exercising operands ==============
fn f32_bits(sign: u32, exp: u32, mant: u32) -> u32 {
    (sign << 31) | ((exp & 0xFF) << 23) | (mant & 0x7F_FFFF)
}
fn f64_bits(sign: u64, exp: u64, mant: u64) -> u64 {
    (sign << 63) | ((exp & 0x7FF) << 52) | (mant & 0xF_FFFF_FFFF_FFFF)
}

// the binary32 special / class constants.
const F32_PZ: u32 = 0x0000_0000;
const F32_NZ: u32 = 0x8000_0000;
const F32_PINF: u32 = 0x7F80_0000;
const F32_NINF: u32 = 0xFF80_0000;
const F32_QNAN: u32 = 0x7FC0_0000;
const F32_QNAN2: u32 = 0x7FD0_0005;
const F32_SNAN: u32 = 0x7F80_0001;
const F32_SNAN_NEG: u32 = 0xFFA0_0003;
const F32_MAXSUB: u32 = 0x007F_FFFF;
const F32_MINNORM: u32 = 0x0080_0000;
const F32_MAXNORM: u32 = 0x7F7F_FFFF;
const F32_ONE: u32 = 0x3F80_0000;
const F32_NONE: u32 = 0xBF80_0000;
const F32_TWO: u32 = 0x4000_0000;

const F64_PZ: u64 = 0x0000_0000_0000_0000;
const F64_NZ: u64 = 0x8000_0000_0000_0000;
const F64_PINF: u64 = 0x7FF0_0000_0000_0000;
const F64_NINF: u64 = 0xFFF0_0000_0000_0000;
const F64_QNAN: u64 = 0x7FF8_0000_0000_0000;
const F64_SNAN: u64 = 0x7FF0_0000_0000_0001;
const F64_SNAN_NEG: u64 = 0xFFF4_0000_0000_0003;
const F64_MAXSUB: u64 = 0x000F_FFFF_FFFF_FFFF;
#[allow(dead_code)]
const F64_MINNORM: u64 = 0x0010_0000_0000_0000;
const F64_MAXNORM: u64 = 0x7FEF_FFFF_FFFF_FFFF;
const F64_ONE: u64 = 0x3FF0_0000_0000_0000;
const F64_NONE: u64 = 0xBFF0_0000_0000_0000;
const F64_TWO: u64 = 0x4000_0000_0000_0000;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let out_path = args
        .get(1)
        .cloned()
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../proofs/aarch64_fp_arith_chip.lean")
                .to_string_lossy()
                .into_owned()
        });
    let neg_control = args.iter().any(|a| a == "--neg");

    let f = std::fs::File::create(&out_path).expect("create out file");
    let mut w = std::io::BufWriter::new(f);

    let mut count: u64 = 0;
    let mut n = 0u64;

    writeln!(w, "-- Copyright 2026 Andrew Yates").unwrap();
    writeln!(w, "-- SPDX-License-Identifier: Apache-2.0").unwrap();
    writeln!(w, "--").unwrap();
    writeln!(w, "-- GENERATED FP-arithmetic on-chip differential. DO NOT EDIT BY HAND.").unwrap();
    writeln!(w, "-- Oracle: real AArch64 fadd/fmul (.s/.d) on Apple Silicon (std::arch::asm!).").unwrap();
    writeln!(w, "-- Each theorem asserts a Clean def from aarch64_fp_arith.lean reduces to the").unwrap();
    writeln!(w, "-- chip's ACTUAL RNE-rounded output bits for that BIT-PATTERN input.").unwrap();
    writeln!(w, "-- clean check passes iff every FADD/FMUL def is faithful to silicon.").unwrap();
    writeln!(w, "-- Grid EXERCISES rounding (ties both directions, guard/round/sticky), plus").unwrap();
    writeln!(w, "--   specials: NaN(q/s) propagation, +-Inf, Inf-Inf, Inf*0, +-0, subnormal,").unwrap();
    writeln!(w, "--   overflow->Inf, cancellation x+(-x). RNE only (RTZ/RDN/RUP/RMM deferred).").unwrap();
    writeln!(w, "-- Checked by concatenating the defs (aarch64_fp_arith.lean) ahead of these.").unwrap();
    writeln!(w).unwrap();
    writeln!(w, "namespace AArch64FPArith").unwrap();
    writeln!(w).unwrap();

    // ================= binary32 FADD =================
    writeln!(w, "-- ======== binary32 FADD (`fadd .s`) ========").unwrap();

    // (1) rounding grid: 1.0 + 2^-k for k around the round bit, and
    //     (1 + ulp) + 2^-k, exercising ties / just-above / just-below.
    let mut s_add: Vec<(u32, u32)> = Vec::new();
    // exact small sums
    s_add.push((F32_ONE, F32_ONE)); // 2.0
    s_add.push((F32_ONE, F32_TWO)); // 3.0
    s_add.push((F32_TWO, F32_ONE));
    s_add.push((f32_bits(0, 127, 0x400000), f32_bits(0, 127, 0x400000))); // 1.5+1.5=3
    // tie-to-even cases: 1.0 + 2^-24 -> 1.0 (lsb 0, exactly half -> down);
    // (1+2^-23) + 2^-24 -> rounds up (lsb 1, exactly half -> up to even).
    let two_pow = |e: i32| f32_bits(0, (127 + e) as u32, 0);
    s_add.push((F32_ONE, two_pow(-24))); // exactly half, lsb 0 -> stays 1.0
    s_add.push((f32_bits(0, 127, 1), two_pow(-24))); // half, lsb 1 -> up
    s_add.push((F32_ONE, two_pow(-23))); // 1 ulp -> exact, no round
    // just above half: 1.0 + (2^-24 + 2^-25) -> rounds up
    s_add.push((F32_ONE, f32_bits(0, 103, 0x400000))); // 2^-24 * 1.5
    // sticky-driven: large + tiny so the tiny is pure sticky
    s_add.push((f32_bits(0, 150, 0), F32_ONE)); // 2^23 + 1.0 exact
    s_add.push((f32_bits(0, 151, 0), F32_ONE)); // 2^24 + 1.0 -> rounds (lost)
    s_add.push((f32_bits(0, 151, 0), f32_bits(0, 127, 0x000001))); // 2^24 + (1+ulp)
    // cancellation
    s_add.push((f32_bits(0, 128, 0x400000), F32_NONE)); // 3.0 + (-1.0) = 2.0
    s_add.push((f32_bits(0, 128, 0), f32_bits(1, 126, 0))); // 2.0 + (-0.5)=1.5
    s_add.push((F32_ONE, F32_NONE)); // 1 + (-1) = +0 (exact cancel)
    s_add.push((f32_bits(0, 100, 0x123456), f32_bits(1, 100, 0x123455))); // near-cancel, subnormal-ish diff
    // negative results / mixed signs
    s_add.push((F32_NONE, F32_TWO)); // -1 + 2 = 1
    s_add.push((F32_TWO, F32_NONE)); // 2 + -1 = 1
    s_add.push((f32_bits(1, 128, 0), f32_bits(1, 127, 0))); // -2 + -1 = -3
    // overflow -> +-Inf
    s_add.push((F32_MAXNORM, F32_MAXNORM)); // overflow +Inf
    s_add.push((f32_bits(1, 254, 0x7FFFFF), f32_bits(1, 254, 0x7FFFFF))); // overflow -Inf
    s_add.push((F32_MAXNORM, f32_bits(0, 127, 0))); // max + 1 (rounds, maybe Inf)
    // subnormal arithmetic
    s_add.push((F32_MAXSUB, F32_MAXSUB)); // subnormal + subnormal
    s_add.push((F32_MINNORM, f32_bits(1, 0, 1))); // min normal - tiny subnormal -> subnormal
    s_add.push((f32_bits(0, 0, 5), f32_bits(0, 0, 3))); // subnormal + subnormal = subnormal
    s_add.push((F32_MINNORM, F32_MINNORM)); // -> 2x min normal
    // specials
    let f32_specials = [
        F32_PZ, F32_NZ, F32_PINF, F32_NINF, F32_QNAN, F32_QNAN2, F32_SNAN, F32_SNAN_NEG, F32_ONE,
    ];
    for &a in &f32_specials {
        for &b in &f32_specials {
            s_add.push((a, b));
        }
    }
    // +-0 sign rules explicitly
    s_add.push((F32_PZ, F32_NZ)); // +0
    s_add.push((F32_NZ, F32_NZ)); // -0
    s_add.push((F32_PZ, F32_ONE)); // 0 + x = x
    s_add.push((F32_ONE, F32_NZ)); // x + (-0) = x

    for (a, b) in s_add {
        let r = s_fadd(a, b);
        writeln!(
            w,
            "theorem fa32_{} : fadd32 {} {} = {} := rfl",
            n,
            bits(a as u64, 32),
            bits(b as u64, 32),
            bits(r as u64, 32)
        )
        .unwrap();
        n += 1;
        count += 1;
    }

    // ================= binary32 FMUL =================
    writeln!(w, "-- ======== binary32 FMUL (`fmul .s`) ========").unwrap();
    let mut s_mul: Vec<(u32, u32)> = Vec::new();
    s_mul.push((F32_TWO, f32_bits(0, 128, 0x400000))); // 2 * 3 = 6
    s_mul.push((f32_bits(0, 128, 0x400000), F32_TWO)); // 3 * 2
    s_mul.push((F32_ONE, F32_ONE)); // 1
    s_mul.push((f32_bits(0, 127, 0x600000), f32_bits(0, 127, 0x600000))); // 1.75^2 rounding
    s_mul.push((f32_bits(0, 127, 0x000001), f32_bits(0, 127, 0x000001))); // (1+ulp)^2 -> round
    s_mul.push((f32_bits(0, 127, 0x7FFFFF), f32_bits(0, 127, 0x7FFFFF))); // ~2*2 product in [2,4)
    s_mul.push((f32_bits(0, 130, 0x123456), f32_bits(0, 131, 0x654321))); // generic rounding
    s_mul.push((F32_NONE, F32_TWO)); // -1 * 2 = -2 (sign)
    s_mul.push((F32_NONE, F32_NONE)); // -1*-1 = 1
    s_mul.push((f32_bits(1, 130, 0), f32_bits(0, 130, 0))); // neg * pos
    // overflow / underflow
    s_mul.push((F32_MAXNORM, F32_TWO)); // overflow -> Inf
    s_mul.push((F32_MAXNORM, F32_MAXNORM)); // overflow -> Inf
    s_mul.push((F32_MINNORM, f32_bits(0, 100, 0))); // tiny -> underflow/subnormal
    s_mul.push((f32_bits(0, 1, 0), f32_bits(0, 1, 0))); // 2^-126 * 2^-126 -> 0 (underflow)
    s_mul.push((F32_MAXSUB, F32_TWO)); // subnormal * 2
    // specials
    let f32_mul_specials = [
        F32_PZ, F32_NZ, F32_PINF, F32_NINF, F32_QNAN, F32_SNAN, F32_SNAN_NEG, F32_ONE, F32_NONE,
    ];
    for &a in &f32_mul_specials {
        for &b in &f32_mul_specials {
            s_mul.push((a, b));
        }
    }
    for (a, b) in s_mul {
        let r = s_fmul(a, b);
        writeln!(
            w,
            "theorem fm32_{} : fmul32 {} {} = {} := rfl",
            n,
            bits(a as u64, 32),
            bits(b as u64, 32),
            bits(r as u64, 32)
        )
        .unwrap();
        n += 1;
        count += 1;
    }

    // ================= binary64 FADD (curated, costly to reduce) ==========
    writeln!(w, "-- ======== binary64 FADD (`fadd .d`) ========").unwrap();
    let two_pow64 = |e: i64| f64_bits(0, (1023 + e) as u64, 0);
    let mut d_add: Vec<(u64, u64)> = Vec::new();
    d_add.push((F64_ONE, F64_ONE)); // 2.0
    d_add.push((F64_ONE, F64_TWO)); // 3.0
    d_add.push((F64_ONE, two_pow64(-53))); // tie, lsb 0 -> stays 1.0
    d_add.push((f64_bits(0, 1023, 1), two_pow64(-53))); // tie, lsb 1 -> up
    d_add.push((F64_ONE, two_pow64(-52))); // 1 ulp exact
    d_add.push((F64_ONE, F64_NONE)); // exact cancel -> +0
    d_add.push((f64_bits(0, 1024, 0x8000000000000), F64_NONE)); // 3.0 + -1 = 2.0
    d_add.push((F64_MAXNORM, F64_MAXNORM)); // overflow -> Inf
    d_add.push((F64_MAXSUB, F64_MAXSUB)); // subnormal + subnormal
    d_add.push((f64_bits(0, 0, 5), f64_bits(0, 0, 3))); // subnormal sum
    d_add.push((F64_PZ, F64_NZ)); // +0
    d_add.push((F64_NZ, F64_NZ)); // -0
    // specials (smaller cross to bound 64-bit cost)
    let d_spec = [F64_PINF, F64_NINF, F64_QNAN, F64_SNAN, F64_SNAN_NEG, F64_ONE];
    for &a in &d_spec {
        for &b in &d_spec {
            d_add.push((a, b));
        }
    }
    for (a, b) in d_add {
        let r = d_fadd(a, b);
        writeln!(
            w,
            "theorem fa64_{} : fadd64 {} {} = {} := rfl",
            n,
            bits(a, 64),
            bits(b, 64),
            bits(r, 64)
        )
        .unwrap();
        n += 1;
        count += 1;
    }

    // ================= binary64 FMUL (curated) =================
    writeln!(w, "-- ======== binary64 FMUL (`fmul .d`) ========").unwrap();
    let mut d_mul: Vec<(u64, u64)> = Vec::new();
    d_mul.push((f64_bits(0, 1024, 0x8000000000000), F64_TWO)); // 3 * 2 = 6
    d_mul.push((F64_ONE, F64_ONE)); // 1
    d_mul.push((f64_bits(0, 1023, 1), f64_bits(0, 1023, 1))); // (1+ulp)^2 -> round
    d_mul.push((f64_bits(0, 1023, 0xFFFFFFFFFFFFF), f64_bits(0, 1023, 0xFFFFFFFFFFFFF))); // ~2*2
    d_mul.push((F64_NONE, F64_TWO)); // -2 (sign)
    d_mul.push((F64_NONE, F64_NONE)); // 1
    d_mul.push((F64_MAXNORM, F64_TWO)); // overflow -> Inf
    d_mul.push((f64_bits(0, 1, 0), f64_bits(0, 1, 0))); // underflow -> 0
    d_mul.push((F64_MAXSUB, F64_TWO)); // subnormal * 2
    let d_mspec = [F64_PINF, F64_NINF, F64_PZ, F64_QNAN, F64_SNAN, F64_ONE, F64_NONE];
    for &a in &d_mspec {
        for &b in &d_mspec {
            d_mul.push((a, b));
        }
    }
    for (a, b) in d_mul {
        let r = d_fmul(a, b);
        writeln!(
            w,
            "theorem fm64_{} : fmul64 {} {} = {} := rfl",
            n,
            bits(a, 64),
            bits(b, 64),
            bits(r, 64)
        )
        .unwrap();
        n += 1;
        count += 1;
    }

    if neg_control {
        // Negative control: claim 1.0 + 1.0 = 1.0 (wrong). clean check MUST report
        // this failed, proving the differential has teeth.
        writeln!(w, "-- NEGATIVE CONTROL (deliberately wrong; clean check MUST report failed):").unwrap();
        writeln!(
            w,
            "theorem NEG_CONTROL_must_fail : fadd32 {} {} = {} := rfl",
            bits(F32_ONE as u64, 32),
            bits(F32_ONE as u64, 32),
            bits(F32_ONE as u64, 32)
        )
        .unwrap();
        count += 1;
    }

    writeln!(w).unwrap();
    writeln!(w, "end AArch64FPArith").unwrap();
    w.flush().unwrap();

    eprintln!(
        "wrote {} FP-arith on-chip differential theorems to {} (neg_control={})",
        count, out_path, neg_control
    );
}
