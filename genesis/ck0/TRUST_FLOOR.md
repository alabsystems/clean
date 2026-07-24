# ck0 Genesis — the irreducible trust floor (honestly named)

> Operating standard: the floor is **minimized and named, never pretended to be
> zero.** "ck0 says Trusted" is only as good as the items below. This document is
> the honest accounting of what you must trust to believe a ck0 verdict.

## What ck0 *is*

`clean-ck0` is a from-scratch, minimal, `#![forbid(unsafe_code)]` proof-checking
kernel for a Lean-4-shaped Calculus of Inductive Constructions. It decides every
judgment itself (no caches as oracles), is **two-valued / fail-closed** (no
fail-open verdict), and is built so two bug classes are *unrepresentable*:
fixed-width overflow (no `i128`/`f64`/`as`-casts in the kernel path — universe
levels and `Nat` literals are arbitrary-precision) and casesOn level-arity
false-Trusted (eliminator levels are kernel-derived, not a caller input).

Scope of this seed: **M0–M3** — terms + validation chokepoint, whnf/def_eq,
inductive admission, mutual + nested recursor derivation, strict-positivity and
subsingleton/large-elim soundness gates. (M4–M7 — cert ingest, legacy retirement,
durable production genesis — are roadmap; this is a genesis seed of the trust
root **as it stands**, regenerated at each milestone.)

## The irreducible floor — what you must trust

1. **The Rust compiler (`rustc` + LLVM), pinned in `MANIFEST.txt`.** ck0 is *not*
   yet self-hosted; rustc+LLVM are trusted to faithfully compile ck0's source to
   machine code. *This is the item the whole ck2 program exists to shrink:* the
   verified-codegen work (C1) has the kernel re-check a compiler's *output* to
   `trust_count == 0`, so rustc/LLVM leave the trust root **for checked programs** —
   but the kernel binary itself is still rustc-built until self-hosting (M6+).

2. **The Rust standard library + the host OS/syscalls.** ck0 uses `std`
   (`Vec`, `String`, iteration). `std` and the OS are trusted; the host triple is
   recorded in the manifest.

3. **`num-bigint` / `num-traits`.** The arbitrary-precision arithmetic backing
   `BigNat` (universe levels, `Nat` literals). Trusted for correct bignum
   arithmetic. This is a *deliberate* trade: bignum **kills** the fixed-width
   overflow bug class by construction, at the cost of trusting num-bigint's adds
   and comparisons. `thiserror` is also a dependency but is soundness-inert (it
   only formats error values; a wrong error string cannot make a `false` verdict
   read as Trusted).

4. **Specification faithfulness — the statement.** The gap between "ck0's `check`
   returns Trusted" and "the term is genuinely well-typed in CIC / the theorem is
   genuinely true." ck0's rules are *intended* to be Lean-4-faithful CIC; that
   faithfulness is evidenced by the validation suite (181 tests, incl. ~70
   adversarially-forged soundness exploits run through the real kernel, and a
   *pre-existing* positivity hole found and fixed), **not** by a machine-checked
   equivalence to an independent CIC specification. A faithfulness bug here is the
   residual soundness risk. Named, not zero.

5. **For the codegen path (C1) only — additionally:** the ISA / bit-blasting model
   fidelity (currently exercised at BV4) and the `trust-cg` lowering semantics.
   These are *not* in the floor for pure-math checking; they apply when ck0 is used
   to re-check verified codegen.

## What is NOT in the floor (decided by ck0 itself)

Type inference, definitional equality, inductive positivity, recursor derivation
and ι-reduction, the subsingleton/large-elim gate, level/universe checking — all
decided from first principles by the ~8.8k-LOC kernel source pinned in the
manifest, with no trusted oracle, cache, or external prover consulted.

## Reproducibility level of this seed

- **Source: checksum-pinned** (sha256 over all 46 build inputs in `MANIFEST.txt`).
- **Build: test-reproducible** — `verify.sh` rebuilds from the pinned source with
  the pinned command and runs the kernel's own validation suite; exit 0 == reproduced.
- **Bit-identical binary: stretch goal** — achievable only under the exact pinned
  `rustc` with deterministic flags; not claimed here. `verify.sh` warns (never
  fails) on a toolchain mismatch, because the *source* is pinned regardless.
