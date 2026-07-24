// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// =============================================================================
//  AArch64 binary16 (FP16 / ARMv8.2-FP16) ON-CHIP DIFFERENTIAL.
// =============================================================================
//
//  The INDEPENDENT ORACLE for proofs/aarch64_fp16.lean (the FP16 family:
//  widen f16->f32 / f16->f64 EXACT, narrow f32->f16 / f64->f16 RNE, and scalar
//  FADD.h / FMUL.h RNE).  Runs each REAL ARMv8.2-FP16 instruction directly on
//  this Apple Silicon CPU (the M4 supports half-precision in hardware) via
//  `std::arch::asm!` with inputs supplied as BIT PATTERNS, reads the result back
//  as BIT PATTERNS, and emits one Clean theorem per sampled input:
//
//      AArch64FP16.<op> <input_bits> [<input_bits>] = <chip_result_bits> := rfl
//
//  where each FP operand/result is a LSB-first `List Bool` literal of the exact
//  width (16 / 32 / 64).  `clean check` on the assembled file PASSES iff every
//  Clean def reduces to the chip's ACTUAL output for every sampled input -- a
//  genuine hardware differential.  If a theorem FAILS the Clean def is
//  unfaithful and must be fixed (NEVER the chip value).
//
//  The half-register form `h<N>` is used; the 16-bit pattern is moved to/from a
//  GPR via `fmov w,h` / `fmov h,w`.  The default FPCR rounding mode (RNE) is in
//  effect.  COVERAGE is a CURATED grid EXERCISING rounding (narrow ties / just
//  above / just below representable boundaries; the GUARD/ROUND/STICKY) PLUS the
//  specials: NaN(q/s), +-Inf, +-0, max subnormal, min/max normal,
//  overflow->Inf, underflow->subnormal/0, NaN widen/narrow.
//
//  otool confirms the real `fcvt s,h` / `fcvt d,h` / `fcvt h,s` / `fcvt h,d` /
//  `fadd h` / `fmul h` instructions are emitted.
//
//  Build/run (Apple Silicon, darwin arm64):
//      cargo run --release --bin fp16_harness -- <out.lean> [--neg]

#![cfg(target_arch = "aarch64")]

use std::arch::asm;
use std::io::Write;

// ---- real ARMv8.2-FP16 instruction wrappers (the chip is the oracle) --------

// widen f16 -> f32 (`fcvt s,h`), exact.
#[inline(never)]
fn fcvt_h_to_s(a: u16) -> u32 {
    let r: u32;
    unsafe {
        asm!("fmov {t:h}, {a:w}", "fcvt {res:s}, {t:h}", "fmov {r:w}, {res:s}",
             a = in(reg) (a as u32), t = out(vreg) _, res = out(vreg) _,
             r = out(reg) r, options(pure, nomem, nostack));
    }
    r
}
// widen f16 -> f64 (`fcvt d,h`), exact.
#[inline(never)]
fn fcvt_h_to_d(a: u16) -> u64 {
    let r: u64;
    unsafe {
        asm!("fmov {t:h}, {a:w}", "fcvt {res:d}, {t:h}", "fmov {r:x}, {res:d}",
             a = in(reg) (a as u32), t = out(vreg) _, res = out(vreg) _,
             r = out(reg) r, options(pure, nomem, nostack));
    }
    r
}
// narrow f32 -> f16 (`fcvt h,s`), RNE.
#[inline(never)]
fn fcvt_s_to_h(a: u32) -> u16 {
    let x = f32::from_bits(a);
    let r: u16;
    unsafe {
        asm!("fcvt {t:h}, {a:s}", "fmov {r:w}, {t:h}",
             a = in(vreg) x, t = out(vreg) _, r = out(reg) r,
             options(pure, nomem, nostack));
    }
    r
}
// narrow f64 -> f16 (`fcvt h,d`), RNE.
#[inline(never)]
fn fcvt_d_to_h(a: u64) -> u16 {
    let x = f64::from_bits(a);
    let r: u16;
    unsafe {
        asm!("fcvt {t:h}, {a:d}", "fmov {r:w}, {t:h}",
             a = in(vreg) x, t = out(vreg) _, r = out(reg) r,
             options(pure, nomem, nostack));
    }
    r
}
// scalar FP16 FADD.h.
#[inline(never)]
fn fadd_h(a: u16, b: u16) -> u16 {
    let r: u16;
    unsafe {
        asm!("fmov {fa:h}, {a:w}", "fmov {fb:h}, {b:w}",
             "fadd {fr:h}, {fa:h}, {fb:h}", "fmov {r:w}, {fr:h}",
             a = in(reg) (a as u32), b = in(reg) (b as u32),
             fa = out(vreg) _, fb = out(vreg) _, fr = out(vreg) _,
             r = out(reg) r, options(pure, nomem, nostack));
    }
    r
}
// scalar FP16 FMUL.h.
#[inline(never)]
fn fmul_h(a: u16, b: u16) -> u16 {
    let r: u16;
    unsafe {
        asm!("fmov {fa:h}, {a:w}", "fmov {fb:h}, {b:w}",
             "fmul {fr:h}, {fa:h}, {fb:h}", "fmov {r:w}, {fr:h}",
             a = in(reg) (a as u32), b = in(reg) (b as u32),
             fa = out(vreg) _, fb = out(vreg) _, fr = out(vreg) _,
             r = out(reg) r, options(pure, nomem, nostack));
    }
    r
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

fn f16_bits(sign: u16, exp: u16, mant: u16) -> u16 {
    (sign << 15) | ((exp & 0x1F) << 10) | (mant & 0x3FF)
}
fn f32_bits(sign: u32, exp: u32, mant: u32) -> u32 {
    (sign << 31) | ((exp & 0xFF) << 23) | (mant & 0x7F_FFFF)
}
fn f64_bits(sign: u64, exp: u64, mant: u64) -> u64 {
    (sign << 63) | ((exp & 0x7FF) << 52) | (mant & 0xF_FFFF_FFFF_FFFF)
}

const H_PZ: u16 = 0x0000;
const H_NZ: u16 = 0x8000;
const H_PINF: u16 = 0x7C00;
const H_NINF: u16 = 0xFC00;
const H_QNAN: u16 = 0x7E00;
const H_SNAN: u16 = 0x7C01;
const H_ONE: u16 = 0x3C00;
const H_NONE: u16 = 0xBC00;
const H_TWO: u16 = 0x4000;
const H_THREE: u16 = 0x4200;
const H_MAXSUB: u16 = 0x03FF;
const H_MINSUB: u16 = 0x0001;
const H_MINNORM: u16 = 0x0400;
const H_MAXNORM: u16 = 0x7BFF;

const F32_ONE: u32 = 0x3F80_0000;
const F32_PZ: u32 = 0x0000_0000;
const F32_NZ: u32 = 0x8000_0000;
const F32_PINF: u32 = 0x7F80_0000;
const F32_NINF: u32 = 0xFF80_0000;
const F32_QNAN: u32 = 0x7FC0_0000;
const F32_SNAN: u32 = 0x7F80_0001;
const F32_MAXNORM: u32 = 0x7F7F_FFFF;

const F64_PZ: u64 = 0x0000_0000_0000_0000;
const F64_NZ: u64 = 0x8000_0000_0000_0000;
const F64_PINF: u64 = 0x7FF0_0000_0000_0000;
const F64_NINF: u64 = 0xFFF0_0000_0000_0000;
const F64_QNAN: u64 = 0x7FF8_0000_0000_0000;
const F64_SNAN: u64 = 0x7FF0_0000_0000_0001;
const F64_ONE: u64 = 0x3FF0_0000_0000_0000;
const F64_MAXNORM: u64 = 0x7FEF_FFFF_FFFF_FFFF;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let out_path = args
        .get(1)
        .cloned()
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../proofs/aarch64_fp16_chip.lean")
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
    writeln!(w, "-- GENERATED FP16 (binary16, ARMv8.2-FP16) on-chip differential. DO NOT EDIT BY HAND.").unwrap();
    writeln!(w, "-- Oracle: real AArch64 fcvt h<->s, h<->d, fadd .h, fmul .h on Apple Silicon (M4).").unwrap();
    writeln!(w).unwrap();
    writeln!(w, "namespace AArch64FP16").unwrap();
    writeln!(w).unwrap();

    // ===== WIDEN f16 -> f32 (exact) =====
    writeln!(w, "-- ======== FCVT widen f16 -> f32 (`fcvt s,h`, exact) ========").unwrap();
    let widen_grid: Vec<u16> = vec![
        H_ONE, H_NONE, H_TWO, H_THREE, H_PZ, H_NZ, H_PINF, H_NINF, H_QNAN, H_SNAN,
        H_MAXSUB, H_MINSUB, H_MINNORM, H_MAXNORM,
        f16_bits(0, 15, 0x200), f16_bits(1, 18, 0x155),
        f16_bits(0, 0, 2), f16_bits(0, 0, 0x40), f16_bits(1, 0, 0x3FF),
        f16_bits(0, 25, 0x055), f16_bits(1, 5, 0x2AA),
        f16_bits(0, 31, 0x201), // qNaN payload
        f16_bits(0, 0, 0x100), f16_bits(0, 0, 0x080), // mid subnormals (top-bit normalize)
        // every single-bit f16 subnormal -- exercises widen's hiSet normalize at each hi.
        f16_bits(0, 0, 0x001), f16_bits(0, 0, 0x002), f16_bits(0, 0, 0x004),
        f16_bits(0, 0, 0x008), f16_bits(0, 0, 0x010), f16_bits(0, 0, 0x020),
        f16_bits(0, 0, 0x040), f16_bits(0, 0, 0x200),
        f16_bits(1, 0, 0x155), // negative subnormal with multiple bits
    ];
    let mut widen_grid = widen_grid;
    widen_grid.dedup();
    for &a in &widen_grid {
        let r = fcvt_h_to_s(a);
        writeln!(w, "theorem h16_wid_s_{} : fcvt_h_to_s {} = {} := rfl", n, bits(a as u64, 16), bits(r as u64, 32)).unwrap();
        n += 1; count += 1;
    }

    // ===== WIDEN f16 -> f64 (exact) =====
    writeln!(w, "-- ======== FCVT widen f16 -> f64 (`fcvt d,h`, exact) ========").unwrap();
    for &a in &widen_grid {
        let r = fcvt_h_to_d(a);
        writeln!(w, "theorem h16_wid_d_{} : fcvt_h_to_d {} = {} := rfl", n, bits(a as u64, 16), bits(r, 64)).unwrap();
        n += 1; count += 1;
    }

    // ===== NARROW f32 -> f16 (RNE) =====
    writeln!(w, "-- ======== FCVT narrow f32 -> f16 (`fcvt h,s`, RNE) ========").unwrap();
    let two_pow32 = |e: i32| f32_bits(0, (127 + e) as u32, 0);
    let narrow32_grid: Vec<u32> = vec![
        F32_ONE, 0xBF80_0000, F32_PZ, F32_NZ, F32_PINF, F32_NINF, F32_QNAN, F32_SNAN,
        0x4000_0000, // 2.0
        0x4040_0000, // 3.0
        // rounding into f16 (10-bit mantissa): half-ulp ties both directions
        f32_bits(0, 127, 0x002000), // 1 + 2^-10 (just above f16 ulp)
        f32_bits(0, 127, 0x001000), // exactly half f16-ulp, lsb 0 -> tie down
        f32_bits(0, 127, 0x003000), // 1.5 f16-ulp -> up
        f32_bits(0, 127, 0x000800), // below half ulp -> down
        f32_bits(0, 127, 0x002800), // 1 + 1.25 ulp
        // overflow -> +-Inf (f16 max ~ 65504)
        two_pow32(16), f32_bits(1, 127 + 16, 0), F32_MAXNORM,
        two_pow32(15), // 32768 (in range)
        // underflow to f16 subnormal / zero
        two_pow32(-15), // 2^-15 -> f16 subnormal
        two_pow32(-24), // smallest f16 subnormal 2^-24
        two_pow32(-25), // below -> rounds to 0 (or smallest subn via tie)
        two_pow32(-14), // f16 min normal 2^-14
        f32_bits(0, 127 - 17, 0x500000), // deep subnormal-ish rounding
        f32_bits(0, 113, 0x400000),      // near f16 min normal boundary
        f32_bits(0, 102, 0),             // 2^-25 again exact -> 0
        f32_bits(0, 142, 0x7FFFFF),      // 65535.99 -> overflow tie region
    ];
    let mut narrow32_grid = narrow32_grid;
    narrow32_grid.dedup();
    for &a in &narrow32_grid {
        let r = fcvt_s_to_h(a);
        writeln!(w, "theorem h16_nar_s_{} : fcvt_s_to_h {} = {} := rfl", n, bits(a as u64, 32), bits(r as u64, 16)).unwrap();
        n += 1; count += 1;
    }

    // ===== NARROW f64 -> f16 (RNE) =====
    writeln!(w, "-- ======== FCVT narrow f64 -> f16 (`fcvt h,d`, RNE) ========").unwrap();
    let two_pow64 = |e: i64| f64_bits(0, (1023 + e) as u64, 0);
    let narrow64_grid: Vec<u64> = vec![
        F64_ONE, 0xBFF0_0000_0000_0000, F64_PZ, F64_NZ, F64_PINF, F64_NINF, F64_QNAN, F64_SNAN,
        0x4000_0000_0000_0000, // 2.0
        f64_bits(0, 1024, 0x8000000000000), // 3.0
        // rounding into f16: half-ulp ties (f16 ulp at 1.0 is 2^-10)
        f64_bits(0, 1023, 0x0040000000000), // 1 + 2^-10
        f64_bits(0, 1023, 0x0020000000000), // exactly half f16-ulp -> tie down
        f64_bits(0, 1023, 0x0060000000000), // 1.5 ulp -> up
        f64_bits(0, 1023, 0x0010000000000), // below half -> down
        // overflow -> +-Inf
        two_pow64(16), f64_bits(1, 1023 + 16, 0), F64_MAXNORM,
        two_pow64(15),
        // underflow to subnormal / zero
        two_pow64(-15), two_pow64(-24), two_pow64(-25), two_pow64(-14),
        two_pow64(-26), // -> 0
        f64_bits(0, 1023 - 17, 0x5000000000000),
        f64_bits(0, 1009, 0x8000000000000), // near min normal boundary rounding
    ];
    let mut narrow64_grid = narrow64_grid;
    narrow64_grid.dedup();
    for &a in &narrow64_grid {
        let r = fcvt_d_to_h(a);
        writeln!(w, "theorem h16_nar_d_{} : fcvt_d_to_h {} = {} := rfl", n, bits(a, 64), bits(r as u64, 16)).unwrap();
        n += 1; count += 1;
    }

    // ===== FADD.h =====
    writeln!(w, "-- ======== scalar FP16 FADD (`fadd .h`, RNE) ========").unwrap();
    let mut adds: Vec<(u16, u16)> = vec![
        (H_ONE, H_ONE), (H_ONE, H_TWO), (H_TWO, H_THREE),
        (H_ONE, H_NONE), (H_NONE, H_ONE), // exact cancel -> +0
        (H_THREE, H_NONE), // 3 + -1 = 2
        (f16_bits(0, 15, 0x200), f16_bits(0, 14, 0x100)), // 1.5 + 0.75ish
        (f16_bits(0, 20, 0x123), f16_bits(0, 16, 0x055)), // differing exponents
        (H_MAXNORM, H_MAXNORM), // overflow -> +Inf
        (H_MAXNORM, H_ONE),     // rounding near top
        (H_MINSUB, H_MINSUB),   // subnormal + subnormal
        (H_MAXSUB, H_MINSUB),   // subnormal carry into normal
        (H_MINNORM, H_NONE),    // small differences
        (f16_bits(0, 15, 0x001), f16_bits(1, 15, 0x000)), // 1+2^-10 + (-1)
        (f16_bits(0, 25, 0x000), f16_bits(0, 10, 0x3FF)), // big + small (sticky)
        // ---- subnormal-focused adds (the class that exposed the bespoke-finish bug) ----
        (f16_bits(0, 0, 0x001), f16_bits(0, 0, 0x001)), // minsub + minsub
        (f16_bits(0, 0, 0x100), f16_bits(0, 0, 0x080)), // mid subnormals
        (f16_bits(0, 0, 0x200), f16_bits(0, 0, 0x200)), // -> carries up
        (f16_bits(0, 0, 0x3FF), f16_bits(0, 0, 0x001)), // maxsub + minsub -> min normal
        (f16_bits(0, 1, 0x000), f16_bits(1, 0, 0x001)), // min normal - minsub (borrow into subn)
        (f16_bits(0, 1, 0x000), f16_bits(1, 0, 0x3FF)), // min normal - maxsub
        (f16_bits(0, 0, 0x155), f16_bits(1, 0, 0x0AA)), // subnormal - subnormal
        (f16_bits(0, 0, 0x3FF), f16_bits(1, 0, 0x200)), // subnormal cancel partial
        (f16_bits(0, 2, 0x000), f16_bits(1, 0, 0x001)), // normal - tiny subnormal (sticky)
        (H_PZ, H_PZ), (H_NZ, H_NZ), (H_PZ, H_NZ), (H_NZ, H_PZ),
        (H_ONE, H_PZ), (H_PZ, H_ONE),
        // specials
        (H_PINF, H_ONE), (H_ONE, H_PINF), (H_PINF, H_PINF), (H_PINF, H_NINF),
        (H_NINF, H_NINF), (H_QNAN, H_ONE), (H_ONE, H_QNAN), (H_SNAN, H_ONE),
        (H_ONE, H_SNAN), (H_QNAN, H_SNAN), (H_SNAN, H_QNAN),
        // half-ulp tie adds
        (f16_bits(0, 14, 0x000), f16_bits(0, 4, 0x000)), // 0.5 + tiny tie region
        (f16_bits(0, 15, 0x3FF), f16_bits(0, 5, 0x000)), // near-carry rounding
    ];
    adds.dedup();
    for (a, b) in adds {
        let r = fadd_h(a, b);
        writeln!(w, "theorem h16_add_{} : fadd16 {} {} = {} := rfl", n, bits(a as u64, 16), bits(b as u64, 16), bits(r as u64, 16)).unwrap();
        n += 1; count += 1;
    }

    // ===== FMUL.h =====
    writeln!(w, "-- ======== scalar FP16 FMUL (`fmul .h`, RNE) ========").unwrap();
    let mut muls: Vec<(u16, u16)> = vec![
        (H_ONE, H_ONE), (H_TWO, H_THREE), (H_TWO, H_TWO), (H_THREE, H_THREE),
        (H_ONE, H_NONE), (H_NONE, H_NONE),
        (f16_bits(0, 15, 0x200), f16_bits(0, 15, 0x200)), // 1.5 * 1.5 = 2.25
        (f16_bits(0, 16, 0x123), f16_bits(0, 14, 0x055)),
        (H_MAXNORM, H_TWO),    // overflow -> +Inf
        (H_MAXNORM, H_MAXNORM), // overflow
        (H_MINNORM, H_MINNORM), // underflow -> 0
        (H_MINNORM, H_TWO),
        (H_MINSUB, H_TWO),     // subnormal * 2
        (H_MAXSUB, H_MAXSUB),  // subnormal * subnormal -> 0
        (f16_bits(0, 20, 0x155), f16_bits(0, 12, 0x2AA)), // generic rounding
        (f16_bits(0, 17, 0x001), f16_bits(0, 13, 0x3FF)), // rounding/sticky
        (H_PZ, H_ONE), (H_ONE, H_PZ), (H_NZ, H_ONE), (H_ONE, H_NZ),
        (H_PZ, H_NZ), (H_PZ, H_PZ),
        // specials
        (H_PINF, H_TWO), (H_TWO, H_PINF), (H_PINF, H_PZ), (H_PZ, H_PINF),
        (H_NINF, H_TWO), (H_PINF, H_NINF), (H_QNAN, H_TWO), (H_TWO, H_QNAN),
        (H_SNAN, H_TWO), (H_TWO, H_SNAN), (H_PINF, H_NONE),
        // half-ulp tie products
        (f16_bits(0, 15, 0x001), f16_bits(0, 15, 0x001)),
        (f16_bits(0, 14, 0x155), f16_bits(0, 16, 0x2AB)),
        // ---- subnormal-focused muls (gradual underflow + subnormal operands) ----
        (f16_bits(0, 0, 0x001), f16_bits(0, 16, 0x000)), // minsub * 2 -> 2nd subnormal
        (f16_bits(0, 0, 0x001), f16_bits(0, 25, 0x000)), // minsub * 2^10 -> normal-ish
        (f16_bits(0, 0, 0x3FF), f16_bits(0, 0, 0x3FF)),  // maxsub^2 -> underflow to 0
        (f16_bits(0, 0, 0x200), f16_bits(0, 15, 0x000)), // subnormal * 1.0
        (f16_bits(0, 0, 0x100), f16_bits(0, 16, 0x200)), // subnormal * 3.0
        (f16_bits(0, 1, 0x000), f16_bits(0, 1, 0x000)),  // minnorm^2 -> deep subnormal/0
        (f16_bits(0, 5, 0x000), f16_bits(0, 5, 0x000)),  // small normals -> subnormal product
        (f16_bits(0, 7, 0x155), f16_bits(0, 8, 0x2AA)),  // -> subnormal rounding region
        (f16_bits(0, 0, 0x155), f16_bits(0, 20, 0x000)), // subnormal * 32 (renorm to normal)
    ];
    muls.dedup();
    for (a, b) in muls {
        let r = fmul_h(a, b);
        writeln!(w, "theorem h16_mul_{} : fmul16 {} {} = {} := rfl", n, bits(a as u64, 16), bits(b as u64, 16), bits(r as u64, 16)).unwrap();
        n += 1; count += 1;
    }

    if neg_control {
        writeln!(w, "-- NEGATIVE CONTROL (deliberately wrong; clean check MUST report failed):").unwrap();
        writeln!(w, "theorem NEG_CONTROL_must_fail : fcvt_h_to_s {} = {} := rfl",
            bits(H_ONE as u64, 16), bits(F32_PINF as u64, 32)).unwrap();
        count += 1;
    }

    writeln!(w).unwrap();
    writeln!(w, "end AArch64FP16").unwrap();
    w.flush().unwrap();
    eprintln!("wrote {} FP16 on-chip differential theorems to {} (neg={})", count, out_path, neg_control);
}
