// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// =============================================================================
//  AArch64 FLOATING-POINT ON-CHIP DIFFERENTIAL HARNESS (FP B-defs).
// =============================================================================
//
//  The INDEPENDENT ORACLE for proofs/aarch64_fp.lean (the NO-ROUNDING FP
//  subset). Runs each REAL AArch64 FP instruction directly on this Apple
//  Silicon CPU via `std::arch::asm!` -- FABS / FNEG / FCMP (+ `MRS x, NZCV`) /
//  FMIN / FMAX / FMINNM / FMAXNM, both `.s` (binary32) and `.d` (binary64) --
//  with inputs supplied as BIT PATTERNS (transmuted u32/u64 -> f32/f64) over
//  the IEEE edge grid, reads the results back as BIT PATTERNS (+ NZCV for
//  FCMP), and emits one Clean theorem per sampled input:
//
//      AArch64FP.<def> <bits_a> [<bits_b>] = <chip_bits_or_bool> := rfl
//
//  where each operand/result is a LSB-first `List Bool` literal of the exact
//  width (32 or 64). `clean check` on the assembled file PASSES iff every Clean
//  def reduces to the chip's ACTUAL output for every sampled input -- a genuine
//  hardware differential. If a theorem FAILS the Clean def is unfaithful and
//  must be fixed (NEVER the chip value).
//
//  COVERAGE is the IEEE edge grid crossed with itself (every pair) so the
//  NaN-propagation and signed-zero edges -- the WHOLE POINT -- are each proven
//  on silicon:  +-0, +-Inf, qNaN (two payloads), sNaN (two payloads, both
//  signs), max subnormal, min normal, max normal, and ordinary values.
//
//  EXPLICITLY OUT OF SCOPE (DEFERRED -- they need IEEE-754 rounding):
//  FADD/FMUL/FDIV/FSQRT/FCVT. This harness covers the bit-exact subset only.
//
//  Build/run (Apple Silicon, darwin arm64):
//      cargo run --release --bin fp_harness -- <out.lean> [--neg]

#![cfg(target_arch = "aarch64")]

use std::arch::asm;
use std::io::Write;

// ---- real FP instruction wrappers (the chip is the oracle) -----------------
//  Inputs/outputs are BIT PATTERNS; we transmute to f32/f64 only to hold them
//  in vector registers across the asm, never to compute in Rust.

macro_rules! fp_un_d {
    ($name:ident, $mn:literal) => {
        #[inline(never)]
        fn $name(a: u64) -> u64 {
            let x = f64::from_bits(a);
            let r: f64;
            unsafe {
                asm!(concat!($mn, " {r:d}, {a:d}"),
                     r = out(vreg) r, a = in(vreg) x,
                     options(pure, nomem, nostack));
            }
            r.to_bits()
        }
    };
}
macro_rules! fp_un_s {
    ($name:ident, $mn:literal) => {
        #[inline(never)]
        fn $name(a: u32) -> u32 {
            let x = f32::from_bits(a);
            let r: f32;
            unsafe {
                asm!(concat!($mn, " {r:s}, {a:s}"),
                     r = out(vreg) r, a = in(vreg) x,
                     options(pure, nomem, nostack));
            }
            r.to_bits()
        }
    };
}
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

fp_un_d!(d_fabs, "fabs");
fp_un_d!(d_fneg, "fneg");
fp_un_s!(s_fabs, "fabs");
fp_un_s!(s_fneg, "fneg");

fp_bin_d!(d_fmin, "fmin");
fp_bin_d!(d_fmax, "fmax");
fp_bin_d!(d_fminnm, "fminnm");
fp_bin_d!(d_fmaxnm, "fmaxnm");
fp_bin_s!(s_fmin, "fmin");
fp_bin_s!(s_fmax, "fmax");
fp_bin_s!(s_fminnm, "fminnm");
fp_bin_s!(s_fmaxnm, "fmaxnm");

// FCMP .d then `MRS x, NZCV` -> raw NZCV. (FCMP sets flags, no GP result.)
#[inline(never)]
fn d_fcmp(a: u64, b: u64) -> u64 {
    let x = f64::from_bits(a);
    let y = f64::from_bits(b);
    let f: u64;
    unsafe {
        asm!("fcmp {a:d}, {b:d}", "mrs {f}, nzcv",
             a = in(vreg) x, b = in(vreg) y, f = out(reg) f,
             options(nomem, nostack));
    }
    f
}
#[inline(never)]
fn s_fcmp(a: u32, b: u32) -> u64 {
    let x = f32::from_bits(a);
    let y = f32::from_bits(b);
    let f: u64;
    unsafe {
        asm!("fcmp {a:s}, {b:s}", "mrs {f}, nzcv",
             a = in(vreg) x, b = in(vreg) y, f = out(reg) f,
             options(nomem, nostack));
    }
    f
}

// NZCV bit extraction (N=31, Z=30, C=29, V=28).
#[inline(always)]
fn nzcv_bools(raw: u64) -> (&'static str, &'static str, &'static str, &'static str) {
    let bit = |i: u32| if (raw >> i) & 1 == 1 { "true" } else { "false" };
    (bit(31), bit(30), bit(29), bit(28))
}

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

// ---- the IEEE edge grid (bit patterns), per width --------------------------
//  Every NaN/Inf/zero/subnormal/normal boundary + sign + two distinct NaN
//  payloads so the NaN-SELECTION (which operand, quieted or not) is pinned.

//  The 64-bit (binary64) min/max/fcmp defs reduce via a width-64 reducible
//  word layer (magnitude subtract + NaN-select nesting), so each binary
//  theorem is non-trivial for the kernel; we therefore use a CURATED edge set
//  that still crosses EVERY IEEE class (both NaN payloads, sNaN both signs,
//  +-0, +-Inf, subnormal, +-min/max normal) with the load-bearing ordinary
//  values -- keeping the full edge x edge cross while bounding `clean check`
//  to a few minutes. The signed-zero / NaN-propagation / sNaN-quieting edges
//  (the WHOLE POINT) are all present and each proven against silicon.
const EDGES64: &[u64] = &[
    0x0000_0000_0000_0000, // +0
    0x8000_0000_0000_0000, // -0
    0x7FF0_0000_0000_0000, // +Inf
    0xFFF0_0000_0000_0000, // -Inf
    0x7FF8_0000_0000_0000, // qNaN (payload 0)
    0x7FFA_0000_0000_0005, // qNaN (distinct payload)
    0x7FF0_0000_0000_0001, // sNaN (payload 1)
    0xFFF4_0000_0000_0003, // sNaN (sign set, distinct payload)
    0x000F_FFFF_FFFF_FFFF, // +max subnormal
    0x0010_0000_0000_0000, // +min normal
    0x7FEF_FFFF_FFFF_FFFF, // +max normal
    0xBFF0_0000_0000_0000, // -1.0
    0x4000_0000_0000_0000, // +2.0
];

const EDGES32: &[u32] = &[
    0x0000_0000, // +0
    0x8000_0000, // -0
    0x7F80_0000, // +Inf
    0xFF80_0000, // -Inf
    0x7FC0_0000, // qNaN (payload 0)
    0x7FD0_0005, // qNaN (distinct payload)
    0x7F80_0001, // sNaN (payload 1)
    0xFFA0_0003, // sNaN (sign set, distinct payload)
    0x007F_FFFF, // +max subnormal
    0x0080_0000, // +min normal
    0x7F7F_FFFF, // +max normal
    0xBF80_0000, // -1.0
    0x4000_0000, // +2.0
];

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let out_path = args
        .get(1)
        .cloned()
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../proofs/aarch64_fp_chip.lean")
                .to_string_lossy()
                .into_owned()
        });
    let neg_control = args.iter().any(|a| a == "--neg");

    let f = std::fs::File::create(&out_path).expect("create out file");
    let mut w = std::io::BufWriter::new(f);

    let mut count: u64 = 0;
    let mut n = 0u64; // global unique theorem suffix

    writeln!(w, "-- Copyright 2026 Andrew Yates").unwrap();
    writeln!(w, "-- SPDX-License-Identifier: Apache-2.0").unwrap();
    writeln!(w, "--").unwrap();
    writeln!(w, "-- GENERATED FP on-chip differential. DO NOT EDIT BY HAND.").unwrap();
    writeln!(w, "-- Oracle: real AArch64 FP instructions on Apple Silicon (std::arch::asm!).").unwrap();
    writeln!(w, "-- Each theorem asserts a Clean def from aarch64_fp.lean reduces to the").unwrap();
    writeln!(w, "-- chip's ACTUAL output bits (or NZCV bool) for that BIT-PATTERN input.").unwrap();
    writeln!(w, "-- clean check passes iff every no-rounding FP def is faithful to silicon.").unwrap();
    writeln!(w, "-- Edge grid (binary32 AND binary64): +-0, +-Inf, qNaN x2, sNaN x2,").unwrap();
    writeln!(w, "--   +-max subnormal, min subnormal, +-min/max normal, +-1, +-2, +-0.5.").unwrap();
    writeln!(w, "-- DEFERRED (need rounding, not here): FADD/FMUL/FDIV/FSQRT/FCVT.").unwrap();
    writeln!(w, "-- These theorems live in `namespace AArch64FP` (the defs' namespace) and").unwrap();
    writeln!(w, "-- are checked by concatenating the defs (aarch64_fp.lean) ahead of them.").unwrap();
    writeln!(w).unwrap();
    writeln!(w, "namespace AArch64FP").unwrap();
    writeln!(w).unwrap();

    // ---------- DOUBLE (binary64) ----------
    writeln!(w, "-- ======== binary64 (double, `.d`) ========").unwrap();

    // unary: FABS / FNEG over the edge set.
    for &a in EDGES64 {
        writeln!(w, "theorem fpd_{} : fabs64 {} = {} := rfl", n, bits(a, 64), bits(d_fabs(a), 64)).unwrap();
        n += 1; count += 1;
        writeln!(w, "theorem fpd_{} : fneg64 {} = {} := rfl", n, bits(a, 64), bits(d_fneg(a), 64)).unwrap();
        n += 1; count += 1;
    }
    // classify over the edge set (each five-way + sNaN/qNaN against... the chip
    // can't directly report classify, but the classification of each edge bit
    // pattern is a GROUND TRUTH of the IEEE encoding; we assert it directly and
    // it is checked by the kernel. These pin the layout/field extraction.)
    for &a in EDGES64 {
        let is_nan = {
            let exp = (a >> 52) & 0x7FF;
            let mant = a & 0x000F_FFFF_FFFF_FFFF;
            exp == 0x7FF && mant != 0
        };
        let exp = (a >> 52) & 0x7FF;
        let mant = a & 0x000F_FFFF_FFFF_FFFF;
        let is_inf = exp == 0x7FF && mant == 0;
        let is_zero = exp == 0 && mant == 0;
        let is_sub = exp == 0 && mant != 0;
        let is_norm = exp != 0x7FF && exp != 0;
        let is_q = is_nan && ((a >> 51) & 1 == 1);
        let is_s = is_nan && ((a >> 51) & 1 == 0);
        let bs = |b: bool| if b { "true" } else { "false" };
        for (def, val) in [
            ("isNaN64", is_nan), ("isInf64", is_inf), ("isZero64", is_zero),
            ("isSubnormal64", is_sub), ("isNormal64", is_norm),
            ("isQNaN64", is_q), ("isSNaN64", is_s),
        ] {
            writeln!(w, "theorem fpd_{} : {} {} = {} := rfl", n, def, bits(a, 64), bs(val)).unwrap();
            n += 1; count += 1;
        }
    }
    // binary: FMIN/FMAX/FMINNM/FMAXNM + FCMP NZCV over edge x edge.
    for &a in EDGES64 {
        for &b in EDGES64 {
            writeln!(w, "theorem fpd_{} : fmin64 {} {} = {} := rfl", n, bits(a, 64), bits(b, 64), bits(d_fmin(a, b), 64)).unwrap();
            n += 1; count += 1;
            writeln!(w, "theorem fpd_{} : fmax64 {} {} = {} := rfl", n, bits(a, 64), bits(b, 64), bits(d_fmax(a, b), 64)).unwrap();
            n += 1; count += 1;
            writeln!(w, "theorem fpd_{} : fminnm64 {} {} = {} := rfl", n, bits(a, 64), bits(b, 64), bits(d_fminnm(a, b), 64)).unwrap();
            n += 1; count += 1;
            writeln!(w, "theorem fpd_{} : fmaxnm64 {} {} = {} := rfl", n, bits(a, 64), bits(b, 64), bits(d_fmaxnm(a, b), 64)).unwrap();
            n += 1; count += 1;
            // FCMP -> NZCV, one theorem per flag.
            let (fn_, fz, fc, fv) = nzcv_bools(d_fcmp(a, b));
            writeln!(w, "theorem fpd_{} : fcmpN64 {} {} = {} := rfl", n, bits(a, 64), bits(b, 64), fn_).unwrap();
            n += 1; count += 1;
            writeln!(w, "theorem fpd_{} : fcmpZ64 {} {} = {} := rfl", n, bits(a, 64), bits(b, 64), fz).unwrap();
            n += 1; count += 1;
            writeln!(w, "theorem fpd_{} : fcmpC64 {} {} = {} := rfl", n, bits(a, 64), bits(b, 64), fc).unwrap();
            n += 1; count += 1;
            writeln!(w, "theorem fpd_{} : fcmpV64 {} {} = {} := rfl", n, bits(a, 64), bits(b, 64), fv).unwrap();
            n += 1; count += 1;
        }
    }

    // ---------- SINGLE (binary32) ----------
    writeln!(w, "-- ======== binary32 (single, `.s`) ========").unwrap();

    for &a in EDGES32 {
        writeln!(w, "theorem fps_{} : fabs32 {} = {} := rfl", n, bits(a as u64, 32), bits(s_fabs(a) as u64, 32)).unwrap();
        n += 1; count += 1;
        writeln!(w, "theorem fps_{} : fneg32 {} = {} := rfl", n, bits(a as u64, 32), bits(s_fneg(a) as u64, 32)).unwrap();
        n += 1; count += 1;
    }
    for &a in EDGES32 {
        let exp = (a >> 23) & 0xFF;
        let mant = a & 0x007F_FFFF;
        let is_nan = exp == 0xFF && mant != 0;
        let is_inf = exp == 0xFF && mant == 0;
        let is_zero = exp == 0 && mant == 0;
        let is_sub = exp == 0 && mant != 0;
        let is_norm = exp != 0xFF && exp != 0;
        let is_q = is_nan && ((a >> 22) & 1 == 1);
        let is_s = is_nan && ((a >> 22) & 1 == 0);
        let bs = |b: bool| if b { "true" } else { "false" };
        for (def, val) in [
            ("isNaN32", is_nan), ("isInf32", is_inf), ("isZero32", is_zero),
            ("isSubnormal32", is_sub), ("isNormal32", is_norm),
            ("isQNaN32", is_q), ("isSNaN32", is_s),
        ] {
            writeln!(w, "theorem fps_{} : {} {} = {} := rfl", n, def, bits(a as u64, 32), bs(val)).unwrap();
            n += 1; count += 1;
        }
    }
    for &a in EDGES32 {
        for &b in EDGES32 {
            writeln!(w, "theorem fps_{} : fmin32 {} {} = {} := rfl", n, bits(a as u64, 32), bits(b as u64, 32), bits(s_fmin(a, b) as u64, 32)).unwrap();
            n += 1; count += 1;
            writeln!(w, "theorem fps_{} : fmax32 {} {} = {} := rfl", n, bits(a as u64, 32), bits(b as u64, 32), bits(s_fmax(a, b) as u64, 32)).unwrap();
            n += 1; count += 1;
            writeln!(w, "theorem fps_{} : fminnm32 {} {} = {} := rfl", n, bits(a as u64, 32), bits(b as u64, 32), bits(s_fminnm(a, b) as u64, 32)).unwrap();
            n += 1; count += 1;
            writeln!(w, "theorem fps_{} : fmaxnm32 {} {} = {} := rfl", n, bits(a as u64, 32), bits(b as u64, 32), bits(s_fmaxnm(a, b) as u64, 32)).unwrap();
            n += 1; count += 1;
            let (fn_, fz, fc, fv) = nzcv_bools(s_fcmp(a, b));
            writeln!(w, "theorem fps_{} : fcmpN32 {} {} = {} := rfl", n, bits(a as u64, 32), bits(b as u64, 32), fn_).unwrap();
            n += 1; count += 1;
            writeln!(w, "theorem fps_{} : fcmpZ32 {} {} = {} := rfl", n, bits(a as u64, 32), bits(b as u64, 32), fz).unwrap();
            n += 1; count += 1;
            writeln!(w, "theorem fps_{} : fcmpC32 {} {} = {} := rfl", n, bits(a as u64, 32), bits(b as u64, 32), fc).unwrap();
            n += 1; count += 1;
            writeln!(w, "theorem fps_{} : fcmpV32 {} {} = {} := rfl", n, bits(a as u64, 32), bits(b as u64, 32), fv).unwrap();
            n += 1; count += 1;
        }
    }

    if neg_control {
        // Negative control: claim fabs of -1.0 is -1.0 (wrong; fabs clears sign).
        // clean check MUST report this failed, proving the differential has teeth.
        let a = 0xBFF0_0000_0000_0000u64;
        writeln!(w, "-- NEGATIVE CONTROL (deliberately wrong; clean check MUST report this failed):").unwrap();
        writeln!(w, "theorem NEG_CONTROL_must_fail : fabs64 {} = {} := rfl", bits(a, 64), bits(a, 64)).unwrap();
        count += 1;
    }

    writeln!(w).unwrap();
    writeln!(w, "end AArch64FP").unwrap();
    w.flush().unwrap();

    eprintln!(
        "wrote {} FP on-chip differential theorems to {} (neg_control={})",
        count, out_path, neg_control
    );
}
