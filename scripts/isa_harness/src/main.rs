// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// =============================================================================
//  AArch64 ON-CHIP DIFFERENTIAL HARNESS (B-defs).
// =============================================================================
//
//  The INDEPENDENT ORACLE for proofs/aarch64_isa.lean. Runs each REAL AArch64
//  instruction directly on this Apple Silicon CPU via `std::arch::asm!`, over a
//  deterministic edge set crossed with a fixed-seed pseudo-random spread, and
//  emits a Clean file of theorems. Coverage: the 64-bit X-register integer ops,
//  the 32-bit W-register forms (result mod 2^32, upper 32 of X ZEROED, shift
//  amount masked &31 — the full X is read back so upper-32-zero is part of the
//  oracle), and NZCV flag setting for ADDS/SUBS/CMP (64- and 32-bit, read off
//  the chip via `MRS x, NZCV`).
//
//      <op>Spec a b = <chip_result> := rfl
//
//  that reference the Clean defs. `clean check` on that file PASSES iff every
//  Clean def reduces to the chip's actual output for every sampled input — a
//  genuine hardware differential. If a theorem fails, the Clean def is
//  unfaithful and must be fixed (never the chip value).
//
//  This is HONESTLY sample-based hardware validation, not exhaustive over
//  2^128 input pairs: the edge set hits every two's-complement / sign / wrap /
//  shift-mask boundary, and the seed is reported so runs are reproducible.
//
//  Build/run (Apple Silicon, darwin arm64):
//      cargo run --release -- <out.lean> [--neg]
//  `--neg` appends ONE deliberately-wrong theorem (negative control) to
//  demonstrate the differential has teeth (clean check must then report it
//  failed); omit it for the all-pass artifact.

#![cfg(target_arch = "aarch64")]

use std::arch::asm;
use std::io::Write;

// ---- real-instruction wrappers (the chip is the oracle) --------------------

macro_rules! op2 {
    ($name:ident, $mn:literal) => {
        #[inline(never)]
        fn $name(a: u64, b: u64) -> u64 {
            let r: u64;
            unsafe {
                asm!(concat!($mn, " {r}, {a}, {b}"),
                     r = out(reg) r, a = in(reg) a, b = in(reg) b,
                     options(pure, nomem, nostack));
            }
            r
        }
    };
}

op2!(hw_add, "add");
op2!(hw_sub, "sub");
op2!(hw_mul, "mul");
op2!(hw_and, "and");
op2!(hw_orr, "orr");
op2!(hw_eor, "eor");
op2!(hw_bic, "bic");
op2!(hw_orn, "orn");
op2!(hw_lslv, "lslv");
op2!(hw_lsrv, "lsrv");
op2!(hw_asrv, "asrv");

// Unary: mvn / neg take a 2-operand asm form.
macro_rules! op1 {
    ($name:ident, $mn:literal) => {
        #[inline(never)]
        fn $name(a: u64) -> u64 {
            let r: u64;
            unsafe {
                asm!(concat!($mn, " {r}, {a}"),
                     r = out(reg) r, a = in(reg) a,
                     options(pure, nomem, nostack));
            }
            r
        }
    };
}

op1!(hw_mvn, "mvn");
op1!(hw_neg, "neg");

// ---- 3-operand multiply-accumulate (MADD/MSUB): Rd = Ra +/- Rn*Rm. The Clean
//      defs take (a n m) = (addend, factor1, factor2); the asm operand order is
//      Rn, Rm, Ra. ----------------------------------------------------------
macro_rules! op3 {
    ($name:ident, $mn:literal) => {
        #[inline(never)]
        fn $name(a: u64, n: u64, m: u64) -> u64 {
            let r: u64;
            unsafe {
                asm!(concat!($mn, " {r}, {n}, {m}, {a}"),
                     r = out(reg) r, n = in(reg) n, m = in(reg) m, a = in(reg) a,
                     options(pure, nomem, nostack));
            }
            r
        }
    };
}
op3!(hw_madd, "madd");
op3!(hw_msub, "msub");
macro_rules! op3w {
    ($name:ident, $mn:literal) => {
        #[inline(never)]
        fn $name(a: u64, n: u64, m: u64) -> u64 {
            let r: u64;
            unsafe {
                asm!(concat!($mn, " {r:w}, {n:w}, {m:w}, {a:w}"),
                     r = out(reg) r, n = in(reg) n, m = in(reg) m, a = in(reg) a,
                     options(pure, nomem, nostack));
            }
            r
        }
    };
}
op3w!(hw_maddw, "madd");
op3w!(hw_msubw, "msub");

// ---- division: SDIV/UDIV. AArch64 NEVER TRAPS — divide-by-zero -> 0, and SDIV
//      INT_MIN/-1 -> INT_MIN (wraps). The whole point is that the chip is the
//      oracle for these edge cases, so the edge grid feeds 0 and INT_MIN/-1. --
op2!(hw_sdiv, "sdiv");
op2!(hw_udiv, "udiv");
// NOTE: the W-form SDIV/UDIV wrappers (hw_sdivw/hw_udivw) are emitted via the
// `op2w!` macro, which is defined further below alongside the other W-form ops.

// ---- bitfield move SBFM/UBFM: the (immr,imms) are INSTRUCTION IMMEDIATES, so
//      each (immr,imms) pair needs its own asm wrapper (a const-immediate). We
//      cover the alias cases the backend emits in the imms>=immr EXTRACT regime:
//      SXTB/SXTH/SXTW, UXTB/UXTH, LSR-imm, ASR-imm, and a mid-field UBFX/SBFX.
//      Read the FULL X back so the W-forms' upper-32-zero is part of the oracle.
macro_rules! bfm1 {
    ($name:ident, $mn:literal, $immr:literal, $imms:literal) => {
        #[inline(never)]
        fn $name(a: u64) -> u64 {
            let r: u64;
            unsafe {
                asm!(concat!($mn, " {r}, {a}, #", $immr, ", #", $imms),
                     r = out(reg) r, a = in(reg) a,
                     options(pure, nomem, nostack));
            }
            r
        }
    };
}
macro_rules! bfm1w {
    ($name:ident, $mn:literal, $immr:literal, $imms:literal) => {
        #[inline(never)]
        fn $name(a: u64) -> u64 {
            let r: u64;
            unsafe {
                asm!(concat!($mn, " {r:w}, {a:w}, #", $immr, ", #", $imms),
                     r = out(reg) r, a = in(reg) a,
                     options(pure, nomem, nostack));
            }
            r
        }
    };
}
// X-form SBFM/UBFM (immr, imms) with imms >= immr.
bfm1!(hw_sbfm_0_7, "sbfm", "0", "7"); // SXTB
bfm1!(hw_sbfm_0_15, "sbfm", "0", "15"); // SXTH
bfm1!(hw_sbfm_0_31, "sbfm", "0", "31"); // SXTW
bfm1!(hw_sbfm_4_63, "sbfm", "4", "63"); // ASR #4
bfm1!(hw_sbfm_4_11, "sbfm", "4", "11"); // SBFX [11:4]
bfm1!(hw_ubfm_0_7, "ubfm", "0", "7"); // UXTB
bfm1!(hw_ubfm_0_15, "ubfm", "0", "15"); // UXTH
bfm1!(hw_ubfm_4_63, "ubfm", "4", "63"); // LSR #4
bfm1!(hw_ubfm_4_11, "ubfm", "4", "11"); // UBFX [11:4]
// W-form SBFM/UBFM (imms<=31). N bit forced 0 by assembler for the W register.
bfm1w!(hw_sbfm_0_7_w, "sbfm", "0", "7");
bfm1w!(hw_sbfm_0_15_w, "sbfm", "0", "15");
bfm1w!(hw_sbfm_4_31_w, "sbfm", "4", "31"); // ASR #4 (W)
bfm1w!(hw_sbfm_4_11_w, "sbfm", "4", "11");
bfm1w!(hw_ubfm_0_7_w, "ubfm", "0", "7");
bfm1w!(hw_ubfm_0_15_w, "ubfm", "0", "15");
bfm1w!(hw_ubfm_4_31_w, "ubfm", "4", "31"); // LSR #4 (W)
bfm1w!(hw_ubfm_4_11_w, "ubfm", "4", "11");

// ---- EXTR Xd, Xn, Xm, #lsb — funnel shift / ROR engine. lsb is an immediate. -
macro_rules! extr {
    ($name:ident, $lsb:literal) => {
        #[inline(never)]
        fn $name(n: u64, m: u64) -> u64 {
            let r: u64;
            unsafe {
                asm!(concat!("extr {r}, {n}, {m}, #", $lsb),
                     r = out(reg) r, n = in(reg) n, m = in(reg) m,
                     options(pure, nomem, nostack));
            }
            r
        }
    };
}
macro_rules! extrw {
    ($name:ident, $lsb:literal) => {
        #[inline(never)]
        fn $name(n: u64, m: u64) -> u64 {
            let r: u64;
            unsafe {
                asm!(concat!("extr {r:w}, {n:w}, {m:w}, #", $lsb),
                     r = out(reg) r, n = in(reg) n, m = in(reg) m,
                     options(pure, nomem, nostack));
            }
            r
        }
    };
}
extr!(hw_extr_0, "0");
extr!(hw_extr_4, "4");
extr!(hw_extr_31, "31");
extr!(hw_extr_63, "63");
extrw!(hw_extr_0_w, "0");
extrw!(hw_extr_4_w, "4");
extrw!(hw_extr_31_w, "31");

// ---- conditional select family: CSEL/CSINC/CSINV/CSNEG. The condition code is
//      part of the mnemonic suffix, so each cc needs its own wrapper. We set the
//      real NZCV from a value via `msr nzcv` then run the conditional op; the
//      Clean defs take (cc, N, Z, C, V, a, b) and we feed the SAME four Bools we
//      put into NZCV. cc encodes: 0 EQ,1 NE,2 CS,3 CC,4 MI,5 PL,6 VS,7 VC,
//      8 HI,9 LS,10 GE,11 LT,12 GT,13 LE,14 AL.  ----------------------------
macro_rules! csop {
    ($name:ident, $mn:literal, $cc:literal) => {
        #[inline(never)]
        fn $name(flags: u64, a: u64, b: u64) -> u64 {
            let r: u64;
            unsafe {
                asm!("msr nzcv, {f}",
                     concat!($mn, " {r}, {a}, {b}, ", $cc),
                     f = in(reg) flags, r = out(reg) r, a = in(reg) a, b = in(reg) b,
                     options(nomem, nostack));
            }
            r
        }
    };
}
macro_rules! csopw {
    ($name:ident, $mn:literal, $cc:literal) => {
        #[inline(never)]
        fn $name(flags: u64, a: u64, b: u64) -> u64 {
            let r: u64;
            unsafe {
                asm!("msr nzcv, {f}",
                     concat!($mn, " {r:w}, {a:w}, {b:w}, ", $cc),
                     f = in(reg) flags, r = out(reg) r, a = in(reg) a, b = in(reg) b,
                     options(nomem, nostack));
            }
            r
        }
    };
}
// We validate a representative spread of condition codes across the family.
csop!(hw_csel_eq, "csel", "eq");
csop!(hw_csel_ne, "csel", "ne");
csop!(hw_csel_cs, "csel", "cs");
csop!(hw_csel_mi, "csel", "mi");
csop!(hw_csel_vs, "csel", "vs");
csop!(hw_csel_hi, "csel", "hi");
csop!(hw_csel_ge, "csel", "ge");
csop!(hw_csel_lt, "csel", "lt");
csop!(hw_csel_gt, "csel", "gt");
csop!(hw_csel_le, "csel", "le");
csop!(hw_csinc_eq, "csinc", "eq");
csop!(hw_csinc_ge, "csinc", "ge");
csop!(hw_csinv_eq, "csinv", "eq");
csop!(hw_csinv_lt, "csinv", "lt");
csop!(hw_csneg_eq, "csneg", "eq");
csop!(hw_csneg_gt, "csneg", "gt");
csopw!(hw_cselw_eq, "csel", "eq");
csopw!(hw_csincw_eq, "csinc", "eq");
csopw!(hw_csinvw_eq, "csinv", "eq");
csopw!(hw_csnegw_eq, "csneg", "eq");

// ---- ANDS / TST flags (logical flag-setting): N=sign, Z=zero, C=0, V=0. --
#[inline(never)]
fn hw_ands64(a: u64, b: u64) -> (u64, u64) {
    let r: u64;
    let f: u64;
    unsafe {
        asm!("ands {r}, {a}, {b}", "mrs {f}, nzcv",
             r = out(reg) r, a = in(reg) a, b = in(reg) b, f = out(reg) f,
             options(nomem, nostack));
    }
    (r, f)
}
#[inline(never)]
fn hw_ands32(a: u64, b: u64) -> (u64, u64) {
    let r: u64;
    let f: u64;
    unsafe {
        asm!("ands {r:w}, {a:w}, {b:w}", "mrs {f}, nzcv",
             r = out(reg) r, a = in(reg) a, b = in(reg) b, f = out(reg) f,
             options(nomem, nostack));
    }
    (r, f)
}

// ---- 32-bit W-form wrappers (the result is computed in 32 bits and the upper
//      32 bits of the X register are ZEROED; the `{r:w}`/`{a:w}` modifiers
//      select the W view of the register, exactly what `add w0, w1, w2` does).
//      We read the FULL X register back so the upper-32-zero property is part
//      of the oracle: a faithful Clean def must produce a value < 2^32. -------

macro_rules! op2w {
    ($name:ident, $mn:literal) => {
        #[inline(never)]
        fn $name(a: u64, b: u64) -> u64 {
            let r: u64;
            unsafe {
                asm!(concat!($mn, " {r:w}, {a:w}, {b:w}"),
                     r = out(reg) r, a = in(reg) a, b = in(reg) b,
                     options(pure, nomem, nostack));
            }
            r
        }
    };
}

op2w!(hw_addw, "add");
op2w!(hw_subw, "sub");
op2w!(hw_mulw, "mul");
op2w!(hw_andw, "and");
op2w!(hw_orrw, "orr");
op2w!(hw_eorw, "eor");
op2w!(hw_lslw, "lslv");
op2w!(hw_lsrw, "lsrv");
op2w!(hw_asrw, "asrv");
// W-form division (no-trap, same as X-form but 32-bit; upper 32 zeroed).
op2w!(hw_sdivw, "sdiv");
op2w!(hw_udivw, "udiv");

#[inline(never)]
fn hw_mvnw(a: u64) -> u64 {
    let r: u64;
    unsafe {
        asm!("mvn {r:w}, {a:w}",
             r = out(reg) r, a = in(reg) a,
             options(pure, nomem, nostack));
    }
    r
}

#[inline(never)]
fn hw_negw(a: u64) -> u64 {
    let r: u64;
    unsafe {
        asm!("neg {r:w}, {a:w}",
             r = out(reg) r, a = in(reg) a,
             options(pure, nomem, nostack));
    }
    r
}

// ---- flag-setting wrappers: run ADDS/SUBS then `MRS x, NZCV` to read the REAL
//      condition flags off this chip. NZCV register layout: N=bit31, Z=bit30,
//      C=bit29, V=bit28. We return (result, raw_nzcv) and split the bits in
//      software so each emitted theorem targets ONE Clean flag def. -----------

// 64-bit ADDS Xd, Xn, Xm; read NZCV.
#[inline(never)]
fn hw_adds64(a: u64, b: u64) -> (u64, u64) {
    let r: u64;
    let f: u64;
    unsafe {
        asm!("adds {r}, {a}, {b}", "mrs {f}, nzcv",
             r = out(reg) r, a = in(reg) a, b = in(reg) b, f = out(reg) f,
             options(pure, nomem, nostack));
    }
    (r, f)
}
// 64-bit SUBS Xd, Xn, Xm; read NZCV (also the flags of CMP Xn, Xm).
#[inline(never)]
fn hw_subs64(a: u64, b: u64) -> (u64, u64) {
    let r: u64;
    let f: u64;
    unsafe {
        asm!("subs {r}, {a}, {b}", "mrs {f}, nzcv",
             r = out(reg) r, a = in(reg) a, b = in(reg) b, f = out(reg) f,
             options(pure, nomem, nostack));
    }
    (r, f)
}
// 32-bit ADDS Wd, Wn, Wm; read NZCV.
#[inline(never)]
fn hw_adds32(a: u64, b: u64) -> (u64, u64) {
    let r: u64;
    let f: u64;
    unsafe {
        asm!("adds {r:w}, {a:w}, {b:w}", "mrs {f}, nzcv",
             r = out(reg) r, a = in(reg) a, b = in(reg) b, f = out(reg) f,
             options(pure, nomem, nostack));
    }
    (r, f)
}
// 32-bit SUBS Wd, Wn, Wm; read NZCV (also the flags of CMP Wn, Wm).
#[inline(never)]
fn hw_subs32(a: u64, b: u64) -> (u64, u64) {
    let r: u64;
    let f: u64;
    unsafe {
        asm!("subs {r:w}, {a:w}, {b:w}", "mrs {f}, nzcv",
             r = out(reg) r, a = in(reg) a, b = in(reg) b, f = out(reg) f,
             options(pure, nomem, nostack));
    }
    (r, f)
}

// NZCV bit extraction -> the four Clean Bool flag values ("true"/"false").
#[inline(always)]
fn nzcv_bools(raw: u64) -> (&'static str, &'static str, &'static str, &'static str) {
    let bit = |i: u32| if (raw >> i) & 1 == 1 { "true" } else { "false" };
    (bit(31), bit(30), bit(29), bit(28)) // N, Z, C, V
}

// Build the raw NZCV register value (for `msr nzcv`) from four bits. N=31, Z=30,
// C=29, V=28 (the SPSR/NZCV bit positions; the low 28 bits are RES0).
#[inline(always)]
fn nzcv_raw(n: bool, z: bool, c: bool, v: bool) -> u64 {
    ((n as u64) << 31) | ((z as u64) << 30) | ((c as u64) << 29) | ((v as u64) << 28)
}
#[inline(always)]
fn bs(x: bool) -> &'static str {
    if x { "true" } else { "false" }
}

// A grid of NZCV flag combinations chosen so that EVERY condition code is driven
// both TRUE and FALSE at least once (the cs/mi/vs/hi/ge/lt/gt/le families need
// specific N/Z/C/V patterns to flip). Each entry is (N, Z, C, V).
const NZCV_GRID: &[(bool, bool, bool, bool)] = &[
    (false, false, false, false), // all clear
    (false, true, false, false),  // Z (EQ true)
    (false, false, true, false),  // C (CS/HI true)
    (true, false, false, false),  // N (MI true; GE/GT depend on N==V)
    (false, false, false, true),  // V (VS true)
    (true, false, false, true),   // N&V (GE true, LT false)
    (false, true, true, false),   // Z&C (LS true since !(C&&!Z))
    (true, true, true, true),     // all set
    (false, false, true, true),   // C&V
    (true, true, false, false),   // N&Z
];

// ---- deterministic sample --------------------------------------------------

// 64-bit operand edge values: every two's-complement / sign / lane / mask
// boundary.
const EDGES: &[u64] = &[
    0x0000_0000_0000_0000, // 0
    0x0000_0000_0000_0001, // 1
    0x0000_0000_0000_0002, // 2
    0xFFFF_FFFF_FFFF_FFFF, // all-ones / -1
    0x8000_0000_0000_0000, // INT64_MIN / sign bit
    0x7FFF_FFFF_FFFF_FFFF, // INT64_MAX
    0x0000_0000_FFFF_FFFF, // low lane
    0xFFFF_FFFF_0000_0000, // high lane
    0xAAAA_AAAA_AAAA_AAAA, // alternating
    0x5555_5555_5555_5555, // alternating
    0x0F0F_0F0F_0F0F_0F0F, // nibble mask
    0xF0F0_F0F0_F0F0_F0F0, // nibble mask
    0x0123_4567_89AB_CDEF, // arbitrary
    0xDEAD_BEEF_CAFE_BABE, // arbitrary
];

// Shift amounts: sweep the &63 masking boundary. 64/65/127/255 are the
// load-bearing cases that distinguish hardware masking from the SMT-LIB
// clamp-to-0 that the in-house spec uses.
const SHIFT_AMTS: &[u64] = &[0, 1, 4, 31, 32, 33, 63, 64, 65, 127, 255];

// Fixed-seed splitmix64 — runs are reproducible/reviewable.
const SEED: u64 = 0x9E37_79B9_7F4A_7C15;
// Committed-artifact size: the deterministic edge/shift sweep is the rigorous
// part (every two's-complement / sign / wrap / shift-mask boundary); the random
// spread adds reproducible breadth. 1000 pairs keeps `clean check` ~30s.
const RAND_PAIRS: usize = 1_000;

struct SplitMix64 {
    s: u64,
}
impl SplitMix64 {
    fn new(seed: u64) -> Self {
        SplitMix64 { s: seed }
    }
    fn next(&mut self) -> u64 {
        self.s = self.s.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.s;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let out_path = args.get(1).cloned().unwrap_or_else(|| {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../proofs/aarch64_isa_chip.lean")
            .to_string_lossy()
            .into_owned()
    });
    let neg_control = args.iter().any(|a| a == "--neg");

    let f = std::fs::File::create(&out_path).expect("create out file");
    let mut w = std::io::BufWriter::new(f);

    let mut count: u64 = 0;
    // emit one `<op>Spec a b = chip := rfl` line; n is a unique suffix
    macro_rules! emit2 {
        ($w:expr, $n:expr, $spec:literal, $a:expr, $b:expr, $r:expr) => {{
            writeln!(
                $w,
                "theorem chip_{}_{} : {} {} {} = {} := rfl",
                $spec, $n, $spec, $a, $b, $r
            )
            .unwrap();
            $n += 1;
        }};
    }
    macro_rules! emit1 {
        ($w:expr, $n:expr, $spec:literal, $a:expr, $r:expr) => {{
            writeln!(
                $w,
                "theorem chip_{}_{} : {} {} = {} := rfl",
                $spec, $n, $spec, $a, $r
            )
            .unwrap();
            $n += 1;
        }};
    }

    writeln!(w, "-- Copyright 2026 Andrew Yates").unwrap();
    writeln!(w, "-- SPDX-License-Identifier: Apache-2.0").unwrap();
    writeln!(w, "--").unwrap();
    writeln!(w, "-- GENERATED on-chip differential. DO NOT EDIT BY HAND.").unwrap();
    writeln!(
        w,
        "-- Oracle: real AArch64 instructions on Apple Silicon (std::arch::asm!)."
    )
    .unwrap();
    writeln!(
        w,
        "-- Each theorem asserts a Clean def from aarch64_isa.lean reduces to the"
    )
    .unwrap();
    writeln!(
        w,
        "-- chip's ACTUAL output for that input. clean check passes iff faithful."
    )
    .unwrap();
    writeln!(w, "-- Sample: {} edge values, shift sweep {:?},", EDGES.len(), SHIFT_AMTS).unwrap();
    writeln!(w, "--   plus {} splitmix64 random pairs, seed {:#018x}.", RAND_PAIRS, SEED).unwrap();
    writeln!(
        w,
        "-- These theorems live in `namespace AArch64` (the defs' namespace) and"
    )
    .unwrap();
    writeln!(
        w,
        "-- are checked by concatenating the defs (aarch64_isa.lean) ahead of them"
    )
    .unwrap();
    writeln!(
        w,
        "-- into a single self-contained file (the checker is single-file)."
    )
    .unwrap();
    writeln!(w).unwrap();
    writeln!(w, "namespace AArch64").unwrap();
    writeln!(w).unwrap();

    // counters per op (unique theorem name suffixes)
    let (mut n_add, mut n_sub, mut n_mul) = (0u64, 0u64, 0u64);
    let (mut n_and, mut n_or, mut n_xor) = (0u64, 0u64, 0u64);
    let (mut n_bic, mut n_orn) = (0u64, 0u64);
    let (mut n_shl, mut n_lshr, mut n_asr) = (0u64, 0u64, 0u64);
    let (mut n_not, mut n_neg) = (0u64, 0u64);

    // W-form counters.
    let (mut n_addw, mut n_subw, mut n_mulw) = (0u64, 0u64, 0u64);
    let (mut n_andw, mut n_orw, mut n_xorw) = (0u64, 0u64, 0u64);
    let (mut n_shlw, mut n_lsrw, mut n_asrw) = (0u64, 0u64, 0u64);
    let (mut n_notw, mut n_negw) = (0u64, 0u64);

    // NZCV flag counters (64-bit + 32-bit; CMP shares SUBS values but gets its
    // own theorems so the cmp* defs are independently chip-validated).
    let (mut n_addsn, mut n_addsz, mut n_addsc, mut n_addsv) = (0u64, 0u64, 0u64, 0u64);
    let (mut n_subsn, mut n_subsz, mut n_subsc, mut n_subsv) = (0u64, 0u64, 0u64, 0u64);
    let (mut n_cmpn, mut n_cmpz, mut n_cmpc, mut n_cmpv) = (0u64, 0u64, 0u64, 0u64);
    let (mut n_addsnw, mut n_addszw, mut n_addscw, mut n_addsvw) = (0u64, 0u64, 0u64, 0u64);
    let (mut n_subsnw, mut n_subszw, mut n_subscw, mut n_subsvw) = (0u64, 0u64, 0u64, 0u64);
    let (mut n_cmpnw, mut n_cmpzw, mut n_cmpcw, mut n_cmpvw) = (0u64, 0u64, 0u64, 0u64);

    // emit one `<flagdef> a b = <bool> := rfl` line.
    macro_rules! emit_flag {
        ($w:expr, $n:expr, $spec:literal, $a:expr, $b:expr, $r:expr) => {{
            writeln!(
                $w,
                "theorem chip_{}_{} : {} {} {} = {} := rfl",
                $spec, $n, $spec, $a, $b, $r
            )
            .unwrap();
            $n += 1;
        }};
    }

    // --- edge x edge for the binary value ops ---
    for &a in EDGES {
        for &b in EDGES {
            emit2!(w, n_add, "bvAdd", a, b, hw_add(a, b));
            emit2!(w, n_sub, "bvSub", a, b, hw_sub(a, b));
            emit2!(w, n_mul, "bvMul", a, b, hw_mul(a, b));
            emit2!(w, n_and, "bvAnd", a, b, hw_and(a, b));
            emit2!(w, n_or, "bvOr", a, b, hw_orr(a, b));
            emit2!(w, n_xor, "bvXor", a, b, hw_eor(a, b));
            emit2!(w, n_bic, "bvBic", a, b, hw_bic(a, b));
            emit2!(w, n_orn, "bvOrn", a, b, hw_orn(a, b));
            count += 8;

            // 32-bit W-form value ops (result < 2^32; upper-32 ZERO is part of
            // the oracle since we read the full X back).
            emit2!(w, n_addw, "bvAddW", a, b, hw_addw(a, b));
            emit2!(w, n_subw, "bvSubW", a, b, hw_subw(a, b));
            emit2!(w, n_mulw, "bvMulW", a, b, hw_mulw(a, b));
            emit2!(w, n_andw, "bvAndW", a, b, hw_andw(a, b));
            emit2!(w, n_orw, "bvOrW", a, b, hw_orrw(a, b));
            emit2!(w, n_xorw, "bvXorW", a, b, hw_eorw(a, b));
            count += 6;

            // NZCV flags: 64-bit ADDS / SUBS / CMP (CMP == SUBS flags).
            let (_r, f) = hw_adds64(a, b);
            let (n, z, c, v) = nzcv_bools(f);
            emit_flag!(w, n_addsn, "addsN", a, b, n);
            emit_flag!(w, n_addsz, "addsZ", a, b, z);
            emit_flag!(w, n_addsc, "addsC", a, b, c);
            emit_flag!(w, n_addsv, "addsV", a, b, v);
            let (_r, f) = hw_subs64(a, b);
            let (n, z, c, v) = nzcv_bools(f);
            emit_flag!(w, n_subsn, "subsN", a, b, n);
            emit_flag!(w, n_subsz, "subsZ", a, b, z);
            emit_flag!(w, n_subsc, "subsC", a, b, c);
            emit_flag!(w, n_subsv, "subsV", a, b, v);
            emit_flag!(w, n_cmpn, "cmpN", a, b, n);
            emit_flag!(w, n_cmpz, "cmpZ", a, b, z);
            emit_flag!(w, n_cmpc, "cmpC", a, b, c);
            emit_flag!(w, n_cmpv, "cmpV", a, b, v);
            count += 12;

            // NZCV flags: 32-bit ADDS / SUBS / CMP (W-form).
            let (_r, f) = hw_adds32(a, b);
            let (n, z, c, v) = nzcv_bools(f);
            emit_flag!(w, n_addsnw, "addsNW", a, b, n);
            emit_flag!(w, n_addszw, "addsZW", a, b, z);
            emit_flag!(w, n_addscw, "addsCW", a, b, c);
            emit_flag!(w, n_addsvw, "addsVW", a, b, v);
            let (_r, f) = hw_subs32(a, b);
            let (n, z, c, v) = nzcv_bools(f);
            emit_flag!(w, n_subsnw, "subsNW", a, b, n);
            emit_flag!(w, n_subszw, "subsZW", a, b, z);
            emit_flag!(w, n_subscw, "subsCW", a, b, c);
            emit_flag!(w, n_subsvw, "subsVW", a, b, v);
            emit_flag!(w, n_cmpnw, "cmpNW", a, b, n);
            emit_flag!(w, n_cmpzw, "cmpZW", a, b, z);
            emit_flag!(w, n_cmpcw, "cmpCW", a, b, c);
            emit_flag!(w, n_cmpvw, "cmpVW", a, b, v);
            count += 12;
        }
    }

    // --- unary ops over the edge set ---
    for &a in EDGES {
        emit1!(w, n_not, "bvNot", a, hw_mvn(a));
        emit1!(w, n_neg, "bvNeg", a, hw_neg(a));
        emit1!(w, n_notw, "bvNotW", a, hw_mvnw(a));
        emit1!(w, n_negw, "bvNegW", a, hw_negw(a));
        count += 4;
    }

    // --- shifts: edge value x full shift sweep (the masking boundary) ---
    for &a in EDGES {
        for &amt in SHIFT_AMTS {
            emit2!(w, n_shl, "bvShl", a, amt, hw_lslv(a, amt));
            emit2!(w, n_lshr, "bvLshr", a, amt, hw_lsrv(a, amt));
            emit2!(w, n_asr, "bvAsr", a, amt, hw_asrv(a, amt));
            count += 3;
            // W-form shifts mask &31 (vs &63 for X) — the 32/33/63/64/65/127/255
            // amounts straddle the &31 boundary and prove it.
            emit2!(w, n_shlw, "bvShlW", a, amt, hw_lslw(a, amt));
            emit2!(w, n_lsrw, "bvLshrW", a, amt, hw_lsrw(a, amt));
            emit2!(w, n_asrw, "bvAsrW", a, amt, hw_asrw(a, amt));
            count += 3;
        }
    }

    // --- fixed-seed random spread for the value ops ---
    let mut rng = SplitMix64::new(SEED);
    for _ in 0..RAND_PAIRS {
        let a = rng.next();
        let b = rng.next();
        emit2!(w, n_add, "bvAdd", a, b, hw_add(a, b));
        emit2!(w, n_sub, "bvSub", a, b, hw_sub(a, b));
        emit2!(w, n_mul, "bvMul", a, b, hw_mul(a, b));
        emit2!(w, n_and, "bvAnd", a, b, hw_and(a, b));
        emit2!(w, n_or, "bvOr", a, b, hw_orr(a, b));
        emit2!(w, n_xor, "bvXor", a, b, hw_eor(a, b));
        emit2!(w, n_bic, "bvBic", a, b, hw_bic(a, b));
        emit2!(w, n_orn, "bvOrn", a, b, hw_orn(a, b));
        // shifts with random amount (exercises &63 across full 64-bit b)
        emit2!(w, n_shl, "bvShl", a, b, hw_lslv(a, b));
        emit2!(w, n_lshr, "bvLshr", a, b, hw_lsrv(a, b));
        emit2!(w, n_asr, "bvAsr", a, b, hw_asrv(a, b));
        emit1!(w, n_not, "bvNot", a, hw_mvn(a));
        emit1!(w, n_neg, "bvNeg", a, hw_neg(a));
        count += 13;

        // W-form value ops + shifts (random amount exercises &31).
        emit2!(w, n_addw, "bvAddW", a, b, hw_addw(a, b));
        emit2!(w, n_subw, "bvSubW", a, b, hw_subw(a, b));
        emit2!(w, n_mulw, "bvMulW", a, b, hw_mulw(a, b));
        emit2!(w, n_andw, "bvAndW", a, b, hw_andw(a, b));
        emit2!(w, n_orw, "bvOrW", a, b, hw_orrw(a, b));
        emit2!(w, n_xorw, "bvXorW", a, b, hw_eorw(a, b));
        emit2!(w, n_shlw, "bvShlW", a, b, hw_lslw(a, b));
        emit2!(w, n_lsrw, "bvLshrW", a, b, hw_lsrw(a, b));
        emit2!(w, n_asrw, "bvAsrW", a, b, hw_asrw(a, b));
        emit1!(w, n_notw, "bvNotW", a, hw_mvnw(a));
        emit1!(w, n_negw, "bvNegW", a, hw_negw(a));
        count += 11;

        // NZCV flags over the random spread (64-bit + 32-bit; CMP == SUBS).
        let (_r, f) = hw_adds64(a, b);
        let (n, z, c, v) = nzcv_bools(f);
        emit_flag!(w, n_addsn, "addsN", a, b, n);
        emit_flag!(w, n_addsz, "addsZ", a, b, z);
        emit_flag!(w, n_addsc, "addsC", a, b, c);
        emit_flag!(w, n_addsv, "addsV", a, b, v);
        let (_r, f) = hw_subs64(a, b);
        let (n, z, c, v) = nzcv_bools(f);
        emit_flag!(w, n_subsn, "subsN", a, b, n);
        emit_flag!(w, n_subsz, "subsZ", a, b, z);
        emit_flag!(w, n_subsc, "subsC", a, b, c);
        emit_flag!(w, n_subsv, "subsV", a, b, v);
        emit_flag!(w, n_cmpn, "cmpN", a, b, n);
        emit_flag!(w, n_cmpz, "cmpZ", a, b, z);
        emit_flag!(w, n_cmpc, "cmpC", a, b, c);
        emit_flag!(w, n_cmpv, "cmpV", a, b, v);
        count += 12;

        let (_r, f) = hw_adds32(a, b);
        let (n, z, c, v) = nzcv_bools(f);
        emit_flag!(w, n_addsnw, "addsNW", a, b, n);
        emit_flag!(w, n_addszw, "addsZW", a, b, z);
        emit_flag!(w, n_addscw, "addsCW", a, b, c);
        emit_flag!(w, n_addsvw, "addsVW", a, b, v);
        let (_r, f) = hw_subs32(a, b);
        let (n, z, c, v) = nzcv_bools(f);
        emit_flag!(w, n_subsnw, "subsNW", a, b, n);
        emit_flag!(w, n_subszw, "subsZW", a, b, z);
        emit_flag!(w, n_subscw, "subsCW", a, b, c);
        emit_flag!(w, n_subsvw, "subsVW", a, b, v);
        emit_flag!(w, n_cmpnw, "cmpNW", a, b, n);
        emit_flag!(w, n_cmpzw, "cmpZW", a, b, z);
        emit_flag!(w, n_cmpcw, "cmpCW", a, b, c);
        emit_flag!(w, n_cmpvw, "cmpVW", a, b, v);
        count += 12;
    }

    // ======================================================================
    //  NEW OPS (this expansion): MADD/MSUB, SDIV/UDIV (no-trap), SBFM/UBFM
    //  (extract aliases), EXTR, CSEL/CSINC/CSINV/CSNEG, ANDS/TST. The chip is
    //  the oracle for every edge case (div-by-0, INT_MIN/-1, each cc true+false).
    // ======================================================================

    writeln!(w, "-- ==== NEW OPS: MADD/MSUB, SDIV/UDIV, SBFM/UBFM, EXTR, CSEL*, ANDS ====").unwrap();

    let mut n_madd = 0u64;
    let mut n_msub = 0u64;
    let mut n_maddw = 0u64;
    let mut n_msubw = 0u64;
    let mut n_sdiv = 0u64;
    let mut n_udiv = 0u64;
    let mut n_sdivw = 0u64;
    let mut n_udivw = 0u64;

    // emit one `<spec> a n m = chip := rfl` (3-arg).
    macro_rules! emit3 {
        ($w:expr, $n:expr, $spec:literal, $a:expr, $x:expr, $y:expr, $r:expr) => {{
            writeln!($w, "theorem chip_{}_{} : {} {} {} {} = {} := rfl",
                     $spec, $n, $spec, $a, $x, $y, $r).unwrap();
            $n += 1;
        }};
    }

    // --- MADD/MSUB (a + n*m / a - n*m) and SDIV/UDIV over edge x edge x a-spread.
    // For the multiply-accumulate we use a small addend set crossed with edge n,m.
    let addends: &[u64] = &[0, 1, 0xFFFF_FFFF_FFFF_FFFF, 0x1234_5678_9ABC_DEF0];
    for &a in addends {
        for &n in EDGES {
            for &m in EDGES {
                emit3!(w, n_madd, "bvMadd", a, n, m, hw_madd(a, n, m));
                emit3!(w, n_msub, "bvMsub", a, n, m, hw_msub(a, n, m));
                emit3!(w, n_maddw, "bvMaddW", a, n, m, hw_maddw(a, n, m));
                emit3!(w, n_msubw, "bvMsubW", a, n, m, hw_msubw(a, n, m));
                count += 4;
            }
        }
    }
    // --- SDIV/UDIV over edge x edge (the edge set INCLUDES 0 and INT_MIN and -1,
    //     so div-by-0 and INT_MIN/-1 are covered as acutal grid points).
    for &a in EDGES {
        for &dv in EDGES {
            emit2!(w, n_sdiv, "bvSdiv", a, dv, hw_sdiv(a, dv));
            emit2!(w, n_udiv, "bvUdiv", a, dv, hw_udiv(a, dv));
            emit2!(w, n_sdivw, "bvSdivW", a, dv, hw_sdivw(a, dv));
            emit2!(w, n_udivw, "bvUdivW", a, dv, hw_udivw(a, dv));
            count += 4;
        }
    }

    // --- SBFM/UBFM extract aliases: each (immr,imms) wrapper over the edge set.
    //     The Clean def is bvSbfm/bvUbfm a immr imms; pass the matching immr/imms.
    let mut n_sbfm = 0u64;
    let mut n_ubfm = 0u64;
    let mut n_sbfmw = 0u64;
    let mut n_ubfmw = 0u64;
    macro_rules! emit_bf {
        ($n:expr, $spec:literal, $a:expr, $immr:expr, $imms:expr, $r:expr) => {{
            writeln!(w, "theorem chip_{}_{} : {} {} {} {} = {} := rfl",
                     $spec, $n, $spec, $a, $immr, $imms, $r).unwrap();
            $n += 1;
            count += 1;
        }};
    }
    for &a in EDGES {
        // X-form SBFM
        emit_bf!(n_sbfm, "bvSbfm", a, 0, 7, hw_sbfm_0_7(a));
        emit_bf!(n_sbfm, "bvSbfm", a, 0, 15, hw_sbfm_0_15(a));
        emit_bf!(n_sbfm, "bvSbfm", a, 0, 31, hw_sbfm_0_31(a));
        emit_bf!(n_sbfm, "bvSbfm", a, 4, 63, hw_sbfm_4_63(a));
        emit_bf!(n_sbfm, "bvSbfm", a, 4, 11, hw_sbfm_4_11(a));
        // X-form UBFM
        emit_bf!(n_ubfm, "bvUbfm", a, 0, 7, hw_ubfm_0_7(a));
        emit_bf!(n_ubfm, "bvUbfm", a, 0, 15, hw_ubfm_0_15(a));
        emit_bf!(n_ubfm, "bvUbfm", a, 4, 63, hw_ubfm_4_63(a));
        emit_bf!(n_ubfm, "bvUbfm", a, 4, 11, hw_ubfm_4_11(a));
        // W-form SBFM (imms <= 31)
        emit_bf!(n_sbfmw, "bvSbfmW", a, 0, 7, hw_sbfm_0_7_w(a));
        emit_bf!(n_sbfmw, "bvSbfmW", a, 0, 15, hw_sbfm_0_15_w(a));
        emit_bf!(n_sbfmw, "bvSbfmW", a, 4, 31, hw_sbfm_4_31_w(a));
        emit_bf!(n_sbfmw, "bvSbfmW", a, 4, 11, hw_sbfm_4_11_w(a));
        // W-form UBFM
        emit_bf!(n_ubfmw, "bvUbfmW", a, 0, 7, hw_ubfm_0_7_w(a));
        emit_bf!(n_ubfmw, "bvUbfmW", a, 0, 15, hw_ubfm_0_15_w(a));
        emit_bf!(n_ubfmw, "bvUbfmW", a, 4, 31, hw_ubfm_4_31_w(a));
        emit_bf!(n_ubfmw, "bvUbfmW", a, 4, 11, hw_ubfm_4_11_w(a));
    }

    // --- EXTR Xd, Xn, Xm, #lsb over edge x edge for several lsb. bvExtr n m lsb.
    let mut n_extr = 0u64;
    let mut n_extrw = 0u64;
    macro_rules! emit_extr {
        ($n:expr, $spec:literal, $nn:expr, $mm:expr, $lsb:expr, $r:expr) => {{
            writeln!(w, "theorem chip_{}_{} : {} {} {} {} = {} := rfl",
                     $spec, $n, $spec, $nn, $mm, $lsb, $r).unwrap();
            $n += 1;
            count += 1;
        }};
    }
    for &nn in EDGES {
        for &mm in EDGES {
            emit_extr!(n_extr, "bvExtr", nn, mm, 0, hw_extr_0(nn, mm));
            emit_extr!(n_extr, "bvExtr", nn, mm, 4, hw_extr_4(nn, mm));
            emit_extr!(n_extr, "bvExtr", nn, mm, 31, hw_extr_31(nn, mm));
            emit_extr!(n_extr, "bvExtr", nn, mm, 63, hw_extr_63(nn, mm));
            emit_extr!(n_extrw, "bvExtrW", nn, mm, 0, hw_extr_0_w(nn, mm));
            emit_extr!(n_extrw, "bvExtrW", nn, mm, 4, hw_extr_4_w(nn, mm));
            emit_extr!(n_extrw, "bvExtrW", nn, mm, 31, hw_extr_31_w(nn, mm));
        }
    }

    // --- CSEL/CSINC/CSINV/CSNEG over the NZCV grid (each cc driven true+false)
    //     x a small value pair set. The Clean def takes (cc, N, Z, C, V, a, b);
    //     we feed the same four Bools we wrote into NZCV via msr.
    let mut n_cs = 0u64;
    let cs_vals: &[(u64, u64)] = &[
        (0xAA, 0xBB),
        (0, 0xFFFF_FFFF_FFFF_FFFF),
        (0x7FFF_FFFF_FFFF_FFFF, 0x8000_0000_0000_0000),
        (0x1234_5678_9ABC_DEF0, 1),
    ];
    macro_rules! emit_cs {
        ($spec:literal, $cc:expr, $n:expr, $z:expr, $c:expr, $v:expr, $a:expr, $bb:expr, $r:expr) => {{
            writeln!(w, "theorem chip_{}_{} : {} {} {} {} {} {} {} {} = {} := rfl",
                     $spec, n_cs, $spec, $cc, bs($n), bs($z), bs($c), bs($v), $a, $bb, $r).unwrap();
            n_cs += 1;
            count += 1;
        }};
    }
    for &(fn_, fz, fc, fv) in NZCV_GRID {
        let raw = nzcv_raw(fn_, fz, fc, fv);
        for &(a, bb) in cs_vals {
            // CSEL family (X), one cc per wrapper; cc number matches condHolds.
            emit_cs!("bvCsel", 0, fn_, fz, fc, fv, a, bb, hw_csel_eq(raw, a, bb));
            emit_cs!("bvCsel", 1, fn_, fz, fc, fv, a, bb, hw_csel_ne(raw, a, bb));
            emit_cs!("bvCsel", 2, fn_, fz, fc, fv, a, bb, hw_csel_cs(raw, a, bb));
            emit_cs!("bvCsel", 4, fn_, fz, fc, fv, a, bb, hw_csel_mi(raw, a, bb));
            emit_cs!("bvCsel", 6, fn_, fz, fc, fv, a, bb, hw_csel_vs(raw, a, bb));
            emit_cs!("bvCsel", 8, fn_, fz, fc, fv, a, bb, hw_csel_hi(raw, a, bb));
            emit_cs!("bvCsel", 10, fn_, fz, fc, fv, a, bb, hw_csel_ge(raw, a, bb));
            emit_cs!("bvCsel", 11, fn_, fz, fc, fv, a, bb, hw_csel_lt(raw, a, bb));
            emit_cs!("bvCsel", 12, fn_, fz, fc, fv, a, bb, hw_csel_gt(raw, a, bb));
            emit_cs!("bvCsel", 13, fn_, fz, fc, fv, a, bb, hw_csel_le(raw, a, bb));
            // CSINC / CSINV / CSNEG (X)
            emit_cs!("bvCsinc", 0, fn_, fz, fc, fv, a, bb, hw_csinc_eq(raw, a, bb));
            emit_cs!("bvCsinc", 10, fn_, fz, fc, fv, a, bb, hw_csinc_ge(raw, a, bb));
            emit_cs!("bvCsinv", 0, fn_, fz, fc, fv, a, bb, hw_csinv_eq(raw, a, bb));
            emit_cs!("bvCsinv", 11, fn_, fz, fc, fv, a, bb, hw_csinv_lt(raw, a, bb));
            emit_cs!("bvCsneg", 0, fn_, fz, fc, fv, a, bb, hw_csneg_eq(raw, a, bb));
            emit_cs!("bvCsneg", 12, fn_, fz, fc, fv, a, bb, hw_csneg_gt(raw, a, bb));
            // W-forms (one cc each; upper-32-zero part of the oracle).
            emit_cs!("bvCselW", 0, fn_, fz, fc, fv, a, bb, hw_cselw_eq(raw, a, bb));
            emit_cs!("bvCsincW", 0, fn_, fz, fc, fv, a, bb, hw_csincw_eq(raw, a, bb));
            emit_cs!("bvCsinvW", 0, fn_, fz, fc, fv, a, bb, hw_csinvw_eq(raw, a, bb));
            emit_cs!("bvCsnegW", 0, fn_, fz, fc, fv, a, bb, hw_csnegw_eq(raw, a, bb));
        }
    }

    // --- ANDS / TST flags over edge x edge (logical: C=0, V=0 always).
    let (mut n_andsn, mut n_andsz, mut n_andsc, mut n_andsv) = (0u64, 0u64, 0u64, 0u64);
    let (mut n_tstn, mut n_tstz, mut n_tstc, mut n_tstv) = (0u64, 0u64, 0u64, 0u64);
    let (mut n_andsnw, mut n_andszw, mut n_andscw, mut n_andsvw) = (0u64, 0u64, 0u64, 0u64);
    for &a in EDGES {
        for &bb in EDGES {
            let (_r, f) = hw_ands64(a, bb);
            let (n, z, c, v) = nzcv_bools(f);
            emit_flag!(w, n_andsn, "andsN", a, bb, n);
            emit_flag!(w, n_andsz, "andsZ", a, bb, z);
            emit_flag!(w, n_andsc, "andsC", a, bb, c);
            emit_flag!(w, n_andsv, "andsV", a, bb, v);
            emit_flag!(w, n_tstn, "tstN", a, bb, n);
            emit_flag!(w, n_tstz, "tstZ", a, bb, z);
            emit_flag!(w, n_tstc, "tstC", a, bb, c);
            emit_flag!(w, n_tstv, "tstV", a, bb, v);
            let (_r, f) = hw_ands32(a, bb);
            let (n, z, c, v) = nzcv_bools(f);
            emit_flag!(w, n_andsnw, "andsNW", a, bb, n);
            emit_flag!(w, n_andszw, "andsZW", a, bb, z);
            emit_flag!(w, n_andscw, "andsCW", a, bb, c);
            emit_flag!(w, n_andsvw, "andsVW", a, bb, v);
            count += 12;
        }
    }

    if neg_control {
        // Negative control: claim the chip's add result + 1. MUST fail clean
        // check, proving the differential is not vacuous.
        let a = 1u64;
        let b = 1u64;
        let wrong = hw_add(a, b).wrapping_add(1);
        writeln!(
            w,
            "-- NEGATIVE CONTROL (deliberately wrong; clean check MUST report this failed):"
        )
        .unwrap();
        writeln!(
            w,
            "theorem NEG_CONTROL_must_fail : bvAdd {} {} = {} := rfl",
            a, b, wrong
        )
        .unwrap();
        count += 1;
    }

    writeln!(w).unwrap();
    writeln!(w, "end AArch64").unwrap();
    w.flush().unwrap();

    eprintln!(
        "wrote {} on-chip differential theorems to {} (seed {:#018x}, neg_control={})",
        count, out_path, SEED, neg_control
    );
}
