// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// =============================================================================
//  AArch64 FP-CONVERSION + FDIV/FSQRT ON-CHIP DIFFERENTIAL (RNE rounding).
// =============================================================================
//
//  The INDEPENDENT ORACLE for proofs/aarch64_fp_cvt.lean (the FCVT family:
//  widen/narrow, FCVTZS/ZU/NS/NU f->int, SCVTF/UCVTF int->f) and
//  proofs/aarch64_fp_divsqrt.lean (FDIV/FSQRT, when not honest-deferred).  Runs
//  each REAL AArch64 conversion / div / sqrt instruction directly on this Apple
//  Silicon CPU via `std::arch::asm!` with inputs supplied as BIT PATTERNS /
//  integers, reads the result back as BIT PATTERNS / integers, and emits one
//  Clean theorem per sampled input:
//
//      AArch64FPCvt.<op> <input_bits> = <chip_result_bits> := rfl
//
//  where each FP operand/result is a LSB-first `List Bool` literal of the exact
//  width (32 or 64) and each integer result is a LSB-first `List Bool` of the
//  integer register width (32 or 64).  `clean check` on the assembled file
//  PASSES iff every Clean def reduces to the chip's ACTUAL output for every
//  sampled input -- a genuine hardware differential.  If a theorem FAILS the
//  Clean def is unfaithful and must be fixed (NEVER the chip value).
//
//  The default FPCR rounding mode (RNE) is in effect.  FCVTZS/ZU use the
//  round-toward-zero instruction variant; FCVTNS/NU the round-to-nearest variant.
//
//  COVERAGE is a CURATED grid EXERCISING rounding (results on ties / just-above
//  / just-below representable boundaries; for narrowing the GUARD/ROUND/STICKY;
//  for FDIV non-terminating quotients; for FSQRT non-perfect-square mantissas)
//  PLUS the specials: NaN(q/s), +-Inf, +-0, subnormal, overflow/underflow,
//  f->int out-of-range saturation + NaN->0, negative FSQRT->NaN, x/0->Inf.
//
//  Build/run (Apple Silicon, darwin arm64):
//      cargo run --release --bin fp_cvt_harness -- <out.lean> [--neg]

#![cfg(target_arch = "aarch64")]

use std::arch::asm;
use std::io::Write;

// ---- real conversion instruction wrappers (the chip is the oracle) ----------

#[inline(never)]
fn fcvt_s_to_d(a: u32) -> u64 {
    let x = f32::from_bits(a);
    let r: f64;
    unsafe {
        asm!("fcvt {r:d}, {a:s}", r = out(vreg) r, a = in(vreg) x,
             options(pure, nomem, nostack));
    }
    r.to_bits()
}
#[inline(never)]
fn fcvt_d_to_s(a: u64) -> u32 {
    let x = f64::from_bits(a);
    let r: f32;
    unsafe {
        asm!("fcvt {r:s}, {a:d}", r = out(vreg) r, a = in(vreg) x,
             options(pure, nomem, nostack));
    }
    r.to_bits()
}

// f->int (round toward zero: fcvtzs/fcvtzu ; round to nearest: fcvtns/fcvtnu),
// for {s,d} source and {w,x} integer dest.
macro_rules! fti {
    ($name:ident, $mn:literal, $src:literal, $dst:literal, $ity:ty, $fty:ty) => {
        #[inline(never)]
        fn $name(a: <$fty as FBits>::Bits) -> $ity {
            let x = <$fty>::from_bits(a);
            let r: $ity;
            unsafe {
                asm!(concat!($mn, " {r:", $dst, "}, {a:", $src, "}"),
                     r = out(reg) r, a = in(vreg) x, options(pure, nomem, nostack));
            }
            r
        }
    };
}
trait FBits { type Bits; }
impl FBits for f32 { type Bits = u32; }
impl FBits for f64 { type Bits = u64; }

fti!(fcvtzs_s_w, "fcvtzs", "s", "w", i32, f32);
fti!(fcvtzs_s_x, "fcvtzs", "s", "x", i64, f32);
fti!(fcvtzu_s_w, "fcvtzu", "s", "w", u32, f32);
fti!(fcvtzu_s_x, "fcvtzu", "s", "x", u64, f32);
fti!(fcvtns_s_w, "fcvtns", "s", "w", i32, f32);
fti!(fcvtns_s_x, "fcvtns", "s", "x", i64, f32);
fti!(fcvtnu_s_w, "fcvtnu", "s", "w", u32, f32);
fti!(fcvtnu_s_x, "fcvtnu", "s", "x", u64, f32);
fti!(fcvtzs_d_w, "fcvtzs", "d", "w", i32, f64);
fti!(fcvtzs_d_x, "fcvtzs", "d", "x", i64, f64);
fti!(fcvtzu_d_w, "fcvtzu", "d", "w", u32, f64);
fti!(fcvtzu_d_x, "fcvtzu", "d", "x", u64, f64);
fti!(fcvtns_d_w, "fcvtns", "d", "w", i32, f64);
fti!(fcvtns_d_x, "fcvtns", "d", "x", i64, f64);
fti!(fcvtnu_d_w, "fcvtnu", "d", "w", u32, f64);
fti!(fcvtnu_d_x, "fcvtnu", "d", "x", u64, f64);

// int->f (scvtf/ucvtf), {w,x} source integer, {s,d} dest.
macro_rules! itf {
    ($name:ident, $mn:literal, $src:literal, $dst:literal, $ity:ty, $fty:ty, $fbits:ty) => {
        #[inline(never)]
        fn $name(a: $ity) -> $fbits {
            let r: $fty;
            unsafe {
                asm!(concat!($mn, " {r:", $dst, "}, {a:", $src, "}"),
                     r = out(vreg) r, a = in(reg) a, options(pure, nomem, nostack));
            }
            r.to_bits()
        }
    };
}
itf!(scvtf_w_s, "scvtf", "w", "s", i32, f32, u32);
itf!(scvtf_x_s, "scvtf", "x", "s", i64, f32, u32);
itf!(ucvtf_w_s, "ucvtf", "w", "s", u32, f32, u32);
itf!(ucvtf_x_s, "ucvtf", "x", "s", u64, f32, u32);
itf!(scvtf_w_d, "scvtf", "w", "d", i32, f64, u64);
itf!(scvtf_x_d, "scvtf", "x", "d", i64, f64, u64);
itf!(ucvtf_w_d, "ucvtf", "w", "d", u32, f64, u64);
itf!(ucvtf_x_d, "ucvtf", "x", "d", u64, f64, u64);

// FDIV / FSQRT (.s/.d).
#[inline(never)]
fn s_fdiv(a: u32, b: u32) -> u32 {
    let (x, y) = (f32::from_bits(a), f32::from_bits(b));
    let r: f32;
    unsafe {
        asm!("fdiv {r:s}, {a:s}, {b:s}", r = out(vreg) r, a = in(vreg) x, b = in(vreg) y,
             options(pure, nomem, nostack));
    }
    r.to_bits()
}
#[inline(never)]
fn d_fdiv(a: u64, b: u64) -> u64 {
    let (x, y) = (f64::from_bits(a), f64::from_bits(b));
    let r: f64;
    unsafe {
        asm!("fdiv {r:d}, {a:d}, {b:d}", r = out(vreg) r, a = in(vreg) x, b = in(vreg) y,
             options(pure, nomem, nostack));
    }
    r.to_bits()
}
#[inline(never)]
fn s_fsqrt(a: u32) -> u32 {
    let x = f32::from_bits(a);
    let r: f32;
    unsafe {
        asm!("fsqrt {r:s}, {a:s}", r = out(vreg) r, a = in(vreg) x,
             options(pure, nomem, nostack));
    }
    r.to_bits()
}
#[inline(never)]
fn d_fsqrt(a: u64) -> u64 {
    let x = f64::from_bits(a);
    let r: f64;
    unsafe {
        asm!("fsqrt {r:d}, {a:d}", r = out(vreg) r, a = in(vreg) x,
             options(pure, nomem, nostack));
    }
    r.to_bits()
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

fn f32_bits(sign: u32, exp: u32, mant: u32) -> u32 {
    (sign << 31) | ((exp & 0xFF) << 23) | (mant & 0x7F_FFFF)
}
fn f64_bits(sign: u64, exp: u64, mant: u64) -> u64 {
    (sign << 63) | ((exp & 0x7FF) << 52) | (mant & 0xF_FFFF_FFFF_FFFF)
}

const F32_PZ: u32 = 0x0000_0000;
const F32_NZ: u32 = 0x8000_0000;
const F32_PINF: u32 = 0x7F80_0000;
const F32_NINF: u32 = 0xFF80_0000;
const F32_QNAN: u32 = 0x7FC0_0000;
const F32_SNAN: u32 = 0x7F80_0001;
const F32_ONE: u32 = 0x3F80_0000;
const F32_NONE: u32 = 0xBF80_0000;
const F32_TWO: u32 = 0x4000_0000;
const F32_MAXSUB: u32 = 0x007F_FFFF;
const F32_MINNORM: u32 = 0x0080_0000;
const F32_MAXNORM: u32 = 0x7F7F_FFFF;

const F64_PZ: u64 = 0x0000_0000_0000_0000;
const F64_NZ: u64 = 0x8000_0000_0000_0000;
const F64_PINF: u64 = 0x7FF0_0000_0000_0000;
const F64_NINF: u64 = 0xFFF0_0000_0000_0000;
const F64_QNAN: u64 = 0x7FF8_0000_0000_0000;
const F64_SNAN: u64 = 0x7FF0_0000_0000_0001;
const F64_ONE: u64 = 0x3FF0_0000_0000_0000;
const F64_NONE: u64 = 0xBFF0_0000_0000_0000;
const F64_TWO: u64 = 0x4000_0000_0000_0000;
const F64_MAXSUB: u64 = 0x000F_FFFF_FFFF_FFFF;
const F64_MINNORM: u64 = 0x0010_0000_0000_0000;
const F64_MAXNORM: u64 = 0x7FEF_FFFF_FFFF_FFFF;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let out_path = args
        .get(1)
        .cloned()
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../proofs/aarch64_fp_cvt_chip.lean")
                .to_string_lossy()
                .into_owned()
        });
    let neg_control = args.iter().any(|a| a == "--neg");
    let want = |s: &str| args.iter().any(|a| a == s);
    // by default emit FCVT; FDIV/FSQRT only when requested (separate file).
    let do_divsqrt = want("--divsqrt");
    let do_fcvt = !do_divsqrt;

    let f = std::fs::File::create(&out_path).expect("create out file");
    let mut w = std::io::BufWriter::new(f);
    let mut count: u64 = 0;
    let mut n = 0u64;

    writeln!(w, "-- Copyright 2026 Andrew Yates").unwrap();
    writeln!(w, "-- SPDX-License-Identifier: Apache-2.0").unwrap();
    writeln!(w, "--").unwrap();
    writeln!(w, "-- GENERATED FP-conversion / div / sqrt on-chip differential. DO NOT EDIT BY HAND.").unwrap();
    writeln!(w, "-- Oracle: real AArch64 fcvt/fcvtz*/fcvtn*/scvtf/ucvtf/fdiv/fsqrt on Apple Silicon.").unwrap();
    writeln!(w).unwrap();

    if do_fcvt {
        writeln!(w, "namespace AArch64FPCvt").unwrap();
        writeln!(w).unwrap();

        // ===== FCVT widen f32 -> f64 (exact) =====
        writeln!(w, "-- ======== FCVT widen f32 -> f64 (`fcvt d,s`, exact) ========").unwrap();
        let mut wid: Vec<u32> = vec![
            F32_ONE, F32_NONE, F32_TWO, F32_PZ, F32_NZ, F32_PINF, F32_NINF, F32_QNAN, F32_SNAN,
            F32_MAXSUB, F32_MINNORM, F32_MAXNORM,
            f32_bits(0, 127, 0x400000), f32_bits(1, 130, 0x123456),
            f32_bits(0, 0, 1), f32_bits(0, 0, 0x40), f32_bits(1, 0, 0x7FFFFF),
            f32_bits(0, 200, 0x55), f32_bits(1, 50, 0x7AAAAA),
            f32_bits(0, 0xFF, 0x200001), // qNaN payload
        ];
        wid.dedup();
        for a in wid {
            let r = fcvt_s_to_d(a);
            writeln!(w, "theorem cv_wid_{} : fcvt_widen {} = {} := rfl", n, bits(a as u64, 32), bits(r, 64)).unwrap();
            n += 1; count += 1;
        }

        // ===== FCVT narrow f64 -> f32 (RNE) =====
        writeln!(w, "-- ======== FCVT narrow f64 -> f32 (`fcvt s,d`, RNE) ========").unwrap();
        let two_pow64 = |e: i64| f64_bits(0, (1023 + e) as u64, 0);
        let mut nar: Vec<u64> = vec![
            F64_ONE, F64_NONE, F64_TWO, F64_PZ, F64_NZ, F64_PINF, F64_NINF, F64_QNAN, F64_SNAN,
            // exact-in-f32 values
            f64_bits(0, 1024, 0x8000000000000), // 3.0
            // rounding: 1.0 + half-ulp-of-f32 at f64 precision -> tie
            f64_bits(0, 1023, 0x0000010000000), // 1 + 2^-28 (below f32 ulp -> rounds to 1)
            f64_bits(0, 1023, 0x0000020000000), // 1 + 2^-27
            f64_bits(0, 1023, 0x0000008000000), // exactly half f32-ulp, lsb 0 -> tie down
            f64_bits(0, 1023, 0x0000018000000), // 1.5 f32-ulp -> up
            // overflow (f64 value > f32 max) -> +-Inf
            two_pow64(200), f64_bits(1, 1023 + 200, 0),
            F64_MAXNORM, // overflow
            // underflow to f32 subnormal / zero
            two_pow64(-140), // f32 subnormal
            two_pow64(-150), // below f32 min subnormal -> 0
            f64_bits(0, 1023 - 130, 0x5000000000000), // subnormal-ish f32
            // f64 subnormal source -> f32 +-0
            F64_MAXSUB, F64_MINNORM,
            f64_bits(0, 869, 0x1234500000000), // ~ near f32 min normal, rounding
        ];
        nar.dedup();
        for a in nar {
            let r = fcvt_d_to_s(a);
            writeln!(w, "theorem cv_nar_{} : fcvt_narrow {} = {} := rfl", n, bits(a, 64), bits(r as u64, 32)).unwrap();
            n += 1; count += 1;
        }

        // ===== f -> int : fcvtz* (round-to-zero) and fcvtn* (round-to-nearest) =====
        // grid of f32 sources crossing integer boundaries / fractions / saturation.
        writeln!(w, "-- ======== f32 -> int (FCVTZS/ZU/NS/NU) ========").unwrap();
        let f32_int: Vec<u32> = vec![
            F32_PZ, F32_NZ, F32_ONE, F32_NONE, F32_TWO,
            f32_bits(0, 128, 0x400000), // 3.0
            f32_bits(0, 127, 0x400000), // 1.5  -> z:1 n:2 (tie up to even)
            f32_bits(0, 128, 0x200000), // 2.5  -> z:2 n:2 (tie down to even)
            f32_bits(0, 126, 0),        // 0.5  -> z:0 n:0
            f32_bits(0, 125, 0),        // 0.25 -> 0
            f32_bits(1, 127, 0x400000), // -1.5 -> z:-1 n:-2
            f32_bits(0, 130, 0x490000), // 12.5625
            f32_bits(1, 130, 0x490000),
            f32_bits(0, 150, 0),        // 2^23
            f32_bits(0, 157, 0),        // 2^30
            f32_bits(0, 158, 0x7FFFFF), // big, near 2^31 -> int32 saturation
            f32_bits(0, 159, 0),        // 2^32 -> over int32/uint32, in int64
            f32_bits(0, 189, 0),        // 2^62
            f32_bits(0, 190, 0),        // 2^63 -> int64 saturation
            f32_bits(0, 191, 0),        // 2^64 -> over uint64 too
            F32_PINF, F32_NINF, F32_QNAN, F32_SNAN,
            F32_MAXNORM, f32_bits(1, 158, 0x7FFFFF),
        ];
        for &a in &f32_int {
            macro_rules! emit32 {
                ($lean:literal, $f:ident, $iw:literal, $signed:literal) => {{
                    let r = $f(a);
                    let rb = if $signed { (r as i64) as u64 & ((1u128<<$iw)-1) as u64 } else { r as u64 & if $iw==64 {u64::MAX} else {((1u64<<$iw)-1)} };
                    writeln!(w, "theorem cv_{}_{} : {} {} = {} := rfl", $lean, n, $lean, bits(a as u64, 32), bits(rb, $iw)).unwrap();
                    n += 1; count += 1;
                }};
            }
            emit32!("fcvtzs_s_w", fcvtzs_s_w, 32, true);
            emit32!("fcvtzs_s_x", fcvtzs_s_x, 64, true);
            emit32!("fcvtzu_s_w", fcvtzu_s_w, 32, false);
            emit32!("fcvtzu_s_x", fcvtzu_s_x, 64, false);
            emit32!("fcvtns_s_w", fcvtns_s_w, 32, true);
            emit32!("fcvtns_s_x", fcvtns_s_x, 64, true);
            emit32!("fcvtnu_s_w", fcvtnu_s_w, 32, false);
            emit32!("fcvtnu_s_x", fcvtnu_s_x, 64, false);
        }

        writeln!(w, "-- ======== f64 -> int (FCVTZS/ZU/NS/NU) ========").unwrap();
        let f64_int: Vec<u64> = vec![
            F64_PZ, F64_NZ, F64_ONE, F64_NONE, F64_TWO,
            f64_bits(0, 1024, 0x8000000000000), // 3.0
            f64_bits(0, 1023, 0x8000000000000), // 1.5 -> tie up to 2
            f64_bits(0, 1024, 0x4000000000000), // 2.5 -> tie down to 2
            f64_bits(0, 1022, 0),               // 0.5
            f64_bits(1, 1023, 0x8000000000000), // -1.5
            f64_bits(0, 1026, 0x9200000000000), // 12.5625
            f64_bits(0, 1052, 0),               // 2^29
            f64_bits(0, 1053, 0x7FFFF00000000), // near 2^30
            f64_bits(0, 1054, 0),               // 2^31 -> int32 saturation
            f64_bits(0, 1055, 0),               // 2^32 -> over uint32
            f64_bits(0, 1085, 0),               // 2^62
            f64_bits(0, 1086, 0),               // 2^63 -> int64 saturation
            f64_bits(0, 1087, 0),               // 2^64
            F64_PINF, F64_NINF, F64_QNAN, F64_SNAN, F64_MAXNORM,
            f64_bits(1, 1086, 0),               // -2^63 -> int64 min exact
        ];
        for &a in &f64_int {
            macro_rules! emit64 {
                ($lean:literal, $f:ident, $iw:literal, $signed:literal) => {{
                    let r = $f(a);
                    let rb = if $signed { (r as i64) as u64 & if $iw==64 {u64::MAX} else {((1u64<<$iw)-1)} } else { r as u64 & if $iw==64 {u64::MAX} else {((1u64<<$iw)-1)} };
                    writeln!(w, "theorem cv_{}_{} : {} {} = {} := rfl", $lean, n, $lean, bits(a, 64), bits(rb, $iw)).unwrap();
                    n += 1; count += 1;
                }};
            }
            emit64!("fcvtzs_d_w", fcvtzs_d_w, 32, true);
            emit64!("fcvtzs_d_x", fcvtzs_d_x, 64, true);
            emit64!("fcvtzu_d_w", fcvtzu_d_w, 32, false);
            emit64!("fcvtzu_d_x", fcvtzu_d_x, 64, false);
            emit64!("fcvtns_d_w", fcvtns_d_w, 32, true);
            emit64!("fcvtns_d_x", fcvtns_d_x, 64, true);
            emit64!("fcvtnu_d_w", fcvtnu_d_w, 32, false);
            emit64!("fcvtnu_d_x", fcvtnu_d_x, 64, false);
        }

        // ===== int -> f : scvtf / ucvtf =====
        writeln!(w, "-- ======== int -> f32/f64 (SCVTF/UCVTF) ========").unwrap();
        let ints: Vec<u64> = vec![
            0, 1, 2, 3, 5, 7, 10, 100, 0x7FFF_FFFF, 0x8000_0000, 0xFFFF_FFFF,
            0x0100_0000, 0x0100_0001, 0x0200_0001, // around f32 24-bit boundary (rounding)
            0x00FF_FFFF, 0x01FF_FFFF, 0x02FF_FFFF,
            0x7FFF_FFFF_FFFF_FFFF, 0x8000_0000_0000_0000, 0xFFFF_FFFF_FFFF_FFFF,
            0x0020_0000_0000_0000, 0x0020_0000_0000_0001, // around f64 53-bit boundary
            123456789, 0xDEAD_BEEF, 0x1234_5678_9ABC_DEF0,
        ];
        for &iv in &ints {
            // W (32-bit) source: low 32 bits.
            let w32 = iv as u32;
            macro_rules! emit_itf_w {
                ($lean:literal, $f:ident, $fbits:literal, $signed:literal) => {{
                    let arg = if $signed { (w32 as i32) as i64 } else { w32 as i64 };
                    let _ = arg;
                    let r = $f(if $signed { w32 as i32 as _ } else { w32 as _ });
                    writeln!(w, "theorem cv_{}_{} : {} {} = {} := rfl", $lean, n, $lean, bits(w32 as u64, 32), bits(r as u64, $fbits)).unwrap();
                    n += 1; count += 1;
                }};
            }
            emit_itf_w!("scvtf_w_s", scvtf_w_s, 32, true);
            emit_itf_w!("ucvtf_w_s", ucvtf_w_s, 32, false);
            emit_itf_w!("scvtf_w_d", scvtf_w_d, 64, true);
            emit_itf_w!("ucvtf_w_d", ucvtf_w_d, 64, false);
            // X (64-bit) source.
            macro_rules! emit_itf_x {
                ($lean:literal, $f:ident, $fbits:literal, $signed:literal) => {{
                    let r = $f(if $signed { iv as i64 as _ } else { iv as _ });
                    writeln!(w, "theorem cv_{}_{} : {} {} = {} := rfl", $lean, n, $lean, bits(iv, 64), bits(r as u64, $fbits)).unwrap();
                    n += 1; count += 1;
                }};
            }
            emit_itf_x!("scvtf_x_s", scvtf_x_s, 32, true);
            emit_itf_x!("ucvtf_x_s", ucvtf_x_s, 32, false);
            emit_itf_x!("scvtf_x_d", scvtf_x_d, 64, true);
            emit_itf_x!("ucvtf_x_d", ucvtf_x_d, 64, false);
        }

        if neg_control {
            writeln!(w, "-- NEGATIVE CONTROL (deliberately wrong; clean check MUST report failed):").unwrap();
            writeln!(w, "theorem NEG_CONTROL_must_fail : fcvt_widen {} = {} := rfl",
                bits(F32_ONE as u64, 32), bits(F32_TWO as u64, 64)).unwrap();
            count += 1;
        }

        writeln!(w).unwrap();
        writeln!(w, "end AArch64FPCvt").unwrap();
    }

    if do_divsqrt {
        writeln!(w, "namespace AArch64FPDivSqrt").unwrap();
        writeln!(w).unwrap();
        writeln!(w, "-- ======== binary32 FDIV (`fdiv .s`, RNE) ========").unwrap();
        let mut s_div: Vec<(u32, u32)> = vec![
            (F32_TWO, F32_ONE), (f32_bits(0,128,0x400000), F32_TWO), // 6/2=3
            (F32_ONE, F32_TWO), // 0.5
            (F32_ONE, f32_bits(0,128,0x400000)), // 1/3 -> non-terminating, rounded
            (f32_bits(0,128,0), f32_bits(0,128,0x400000)), // 2/3
            (f32_bits(0,127,0x400000), f32_bits(0,128,0)), // 1.5/2
            (f32_bits(0,134,0), f32_bits(0,130,0)), // 128/8 = 16
            (F32_ONE, f32_bits(0,130,0x123456)), // generic rounding
            (f32_bits(0,140,0x222222), f32_bits(0,132,0x111111)),
            (F32_NONE, F32_TWO), (F32_ONE, F32_NONE), // signs
            (F32_MAXNORM, f32_bits(0,100,0)), // overflow -> Inf
            (F32_MINNORM, f32_bits(0,160,0)), // underflow
            (F32_ONE, F32_PZ), (F32_NONE, F32_PZ), (F32_ONE, F32_NZ), // x/0 -> Inf
            (F32_PZ, F32_PZ), // 0/0 -> qNaN
            (F32_PINF, F32_PINF), // Inf/Inf -> qNaN
            (F32_PINF, F32_ONE), (F32_ONE, F32_PINF), // Inf/x, x/Inf
            // ---- STICKY-DECIDING half-ulp ties (close the fdDivSticky coverage gap) ----
            // Each exact quotient sits a HAIR ABOVE a half-ulp tie: guard=1, round=0,
            // placed-LSB=0, and the round/placement bits are zero so the ONLY nonzero
            // residual past the round bit is the DIVISION REMAINDER -> RNE must round UP
            // VIA the from-remainder sticky. Forcing fdDivSticky to a constant false
            // would round DOWN (one ulp low), so these theorems PIN the sticky bit.
            // (Found by exact-rational search; cross-checked vs IEEE RNE and this chip.)
            (0x3F86_E0F4, 0x3EEA_5CCC),
            (0x4150_F1A7, 0x40EE_0E64),
            (0x3F82_DA80, 0x41F7_5DA1),
            (0x4112_F164, 0x3EBC_C4B3),
            (0x417C_1690, 0x4195_B935),
            (0x420C_276F, 0x4167_AEA4),
            (0x421F_4086, 0x3C62_D235),
            (0x3FCB_CDF0, 0x3CEE_1FAF),
        ];
        // specials cross
        let sp = [F32_PZ, F32_NZ, F32_PINF, F32_NINF, F32_QNAN, F32_SNAN, F32_ONE, F32_NONE];
        for &a in &sp { for &b in &sp { s_div.push((a,b)); } }
        for (a,b) in s_div {
            let r = s_fdiv(a,b);
            writeln!(w, "theorem dv32_{} : fdiv32 {} {} = {} := rfl", n, bits(a as u64,32), bits(b as u64,32), bits(r as u64,32)).unwrap();
            n += 1; count += 1;
        }
        writeln!(w, "-- ======== binary64 FDIV (`fdiv .d`, RNE) ========").unwrap();
        let mut d_div: Vec<(u64,u64)> = vec![
            (F64_TWO, F64_ONE), (f64_bits(0,1024,0x8000000000000), F64_TWO),
            (F64_ONE, F64_TWO), (F64_ONE, f64_bits(0,1024,0x8000000000000)), // 1/3
            (F64_NONE, F64_TWO), (F64_MAXNORM, f64_bits(0,900,0)),
            (F64_ONE, F64_PZ), (F64_PZ, F64_PZ), (F64_PINF, F64_PINF),
            // ---- STICKY-DECIDING half-ulp ties (binary64; pin fdDivSticky) ----
            // Exact quotient a hair above a half-ulp tie (guard=1, round=0, placed-LSB=0,
            // placement residual 0): the from-remainder sticky is the deciding RNE bit.
            (0x3F9D_4B52_5080_683A, 0x3FFE_34B9_7E99_18F9),
            (0x3FF4_9B78_C79B_B95D, 0x401F_4863_00E3_6942),
        ];
        let dsp = [F64_PZ, F64_NZ, F64_PINF, F64_NINF, F64_QNAN, F64_SNAN, F64_ONE];
        for &a in &dsp { for &b in &dsp { d_div.push((a,b)); } }
        for (a,b) in d_div {
            let r = d_fdiv(a,b);
            writeln!(w, "theorem dv64_{} : fdiv64 {} {} = {} := rfl", n, bits(a,64), bits(b,64), bits(r,64)).unwrap();
            n += 1; count += 1;
        }
        writeln!(w, "-- ======== binary32 FSQRT (`fsqrt .s`, RNE) ========").unwrap();
        let mut s_sq: Vec<u32> = vec![
            F32_PZ, F32_NZ, F32_ONE, f32_bits(0,129,0), // 4 -> 2
            f32_bits(0,131,0), // 16 -> 4
            F32_TWO, // sqrt2 irrational
            f32_bits(0,128,0x400000), // 3
            f32_bits(0,127,0x400000), // 1.5
            f32_bits(0,130,0x123456),
            F32_MAXNORM, F32_MINNORM, F32_MAXSUB,
            F32_PINF, F32_QNAN, F32_SNAN, F32_NONE, F32_NINF, // negative -> NaN
            f32_bits(0,128,0), // 2 again
            // ---- STICKY-DECIDING half-ulp ties (close the sqSticky coverage gap) ----
            // Each exact root sits a HAIR ABOVE a half-ulp tie: guard=1, round=0,
            // placed-LSB=0, with the placement residual zero, so the ONLY nonzero
            // residual past the round bit is the SQRT REMAINDER -> RNE rounds UP VIA the
            // from-remainder sticky. Forcing sqSticky to a constant false rounds DOWN
            // (one ulp low); these theorems PIN the sticky bit.
            // (Found by exact integer-sqrt search; cross-checked vs IEEE RNE / this chip.)
            0x3E6D_8520,
            0x3BD1_C093,
            0x42C3_D4C6,
            0x4153_64E1,
            0x4150_0750,
            0x3F63_5C0E,
            0x3833_02BE,
            0x422F_EED9,
        ];
        s_sq.dedup();
        for a in s_sq {
            let r = s_fsqrt(a);
            writeln!(w, "theorem sq32_{} : fsqrt32 {} = {} := rfl", n, bits(a as u64,32), bits(r as u64,32)).unwrap();
            n += 1; count += 1;
        }
        writeln!(w, "-- ======== binary64 FSQRT (`fsqrt .d`, RNE) ========").unwrap();
        let mut d_sq: Vec<u64> = vec![
            F64_PZ, F64_ONE, f64_bits(0,1025,0), F64_TWO, f64_bits(0,1024,0x8000000000000),
            F64_PINF, F64_QNAN, F64_NONE,
        ];
        d_sq.dedup();
        for a in d_sq {
            let r = d_fsqrt(a);
            writeln!(w, "theorem sq64_{} : fsqrt64 {} = {} := rfl", n, bits(a,64), bits(r,64)).unwrap();
            n += 1; count += 1;
        }
        writeln!(w).unwrap();
        writeln!(w, "end AArch64FPDivSqrt").unwrap();
    }

    w.flush().unwrap();
    eprintln!("wrote {} on-chip differential theorems to {} (divsqrt={}, neg={})", count, out_path, do_divsqrt, neg_control);
}
