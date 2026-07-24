# AArch64 ISA on-chip differential harness (B-defs)

Independent oracle for `proofs/aarch64_isa.lean`. Runs each real AArch64 64-bit
integer instruction on **this Apple Silicon CPU** via `std::arch::asm!`, then
emits Clean `:= rfl` theorems asserting the Clean defs reduce to the chip's
actual output. This replaces the in-house `trust-cg-verify/src/aarch64_semantics.rs`
as the trusted machine-side spec with a hardware-grounded one.

## Why a hardware oracle (not a second software model)

trust-cg's lowering equivalence checks both sides against ONE in-house SMT spec,
so a shared misencoding is invisible. The real chip is a strictly independent
oracle: it already exposed a divergence — the SMT spec treats shift-amount
`>= width` as result `0` (SMT-LIB `bvshl/bvlshr/bvashr`), but the chip's
`LSLV/LSRV/ASRV` **mask the amount by `&63`** (`1<<64 = 1`, `x >>u 64 = x`,
`x >>s 64 = x`). The Clean defs use `(b % 64)` and match silicon.

## What's modeled

64-bit X-register forms:
`ADD, SUB, MUL, AND (and), ORR (orr), EOR (eor), BIC (bic), ORN (orn),
MVN (mvn), NEG (neg), LSLV (lslv), LSRV (lsrv), ASRV (asrv)`.

32-bit W-register forms (result mod 2^32; **the upper 32 bits of the X register
are ZEROED**; shift amount masked `&31`):
`ADD (add w), SUB (sub w), MUL (mul w), AND (and w), ORR (orr w), EOR (eor w),
MVN (mvn w), NEG (neg w), LSLV (lsl w), LSRV (lsr w), ASRV (asr w)`. The harness
reads the FULL X register back, so the upper-32-zero property is part of the
oracle — a faithful Clean def must produce a value `< 2^32`.

NZCV flag setting for ADDS / SUBS / CMP (64-bit and 32-bit), read off the chip
via `MRS x, NZCV` (layout N=bit31, Z=bit30, C=bit29, V=bit28): one `:= rfl`
theorem per flag (`addsN/Z/C/V`, `subsN/Z/C/V`, `cmpN/Z/C/V`, plus the `*W`
32-bit forms). C is the unsigned carry-out (for SUBS/CMP it is NOT-borrow, so it
is set when `a >=u b`); V is signed overflow.

## Run

```bash
scripts/isa_harness/regen.sh
```

Builds the harness, executes the instructions on-chip, regenerates
`proofs/aarch64_isa_chip.lean` (self-contained: defs + generated theorems), and
`clean check`s it. Passes IFF every Clean def reduces to the chip's output over
the sample. If a theorem FAILS, fix the **def**, never the chip value.

### Negative control (proves the differential has teeth)

```bash
cargo run --release --manifest-path scripts/isa_harness/Cargo.toml -- /tmp/neg.lean --neg
```

`--neg` appends one deliberately-wrong theorem; concatenating it after the defs
and running `clean check` reports it **failed** (the chip says `1+1=2`, the
control claims `3`), demonstrating the kernel rejects an unfaithful claim.

## Sample (honest: sample-based, not exhaustive over 2^128)

- 14 edge values (0, 1, 2, all-ones/-1, INT64_MIN, INT64_MAX, lane boundaries,
  alternating/nibble masks, arbitrary), crossed for binary ops. The same edges
  exercise the W-forms (their low 32 bits hit every 32-bit boundary, and their
  high bits prove the upper-32-zero property) and the NZCV grid.
- Shift sweep `{0,1,4,31,32,33,63,64,65,127,255}` — straddles BOTH the X-form
  `&63` and the W-form `&31` masking boundaries.
- 1000 fixed-seed (`splitmix64`, seed `0x9E3779B97F4A7C15`) random pairs per op.

~56k theorems total; reproducible. Faithfulness established up to this sample.

## Notes

- Apple Silicon only (`arm64`); the harness is `#![cfg(target_arch = "aarch64")]`.
- This crate is in the workspace `exclude` list (it uses `unsafe` `asm!`, which
  the Clean kernel forbids; it is a standalone tooling bin, not shipped code).
