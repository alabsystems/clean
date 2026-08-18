# Vision: Clean

**The verification engine for the AI age.**

## The Future We're Building

Every AI agent verifies its code in real-time. Proof is as fast as compilation. Mathematical truth is machine-checkable at scale. The entire corpus of human mathematics is formalized and queryable. Software correctness is the default, not the exception.

Clean is the foundation.

## Lean 4 Replacement Aspiration

Clean's long-term aspiration is to become a complete, practical replacement for
Lean 4 in the workflows that matter to AI-driven verification. That is not a
current capability claim.

The release bar for any future "full replacement" claim is strict: Lean
frontend, tactic, Lake, editor, compiler/runtime, native-library, Mathlib, and
`.olean` behavior must either run unchanged or have a Clean-native path that is
clearly better and trust-accounted. Current gaps are blockers for that claim.

## Why This Matters

AI agents will write most code. They make mistakes. They hallucinate. They need to verify their work faster than they can think.

Current theorem provers are built for humans:
- Millisecond latency (humans don't notice)
- REPL interfaces (humans type commands)
- Error messages for human readers
- Interactive proof development

AI agents need something different:
- Sub-microsecond latency (millions of verification calls; see `docs/BENCHMARKS.md`)
- Rust library API (primary) + JSON-RPC for language bindings
- Structured error data (machines parse results)
- Batch verification at scale

Clean is designed to bridge this gap with Lean-compatible foundations,
machine-readable APIs, and low-latency checking. Historical microbenchmarks are
not a current Lean-vs-Clean proof; cite fresh benchmark runs before making speed
claims.

## Problem

Theorem provers are often the bottleneck in AI-driven software verification.
Interactive proof workflows can impose millisecond-scale round trips that are
fine for humans and costly for agents generating large candidate batches. Clean
targets a native Rust library API, batch verification, and structured error
output for machine consumers.

Clean exists to reduce this bottleneck: a ground-up Rust implementation of
Lean-shaped type theory that targets sub-microsecond verification latency and
million-operation-per-second batch throughput.

## Success Criteria

| Metric | Target | Current |
|--------|--------|---------|
| Type check latency (`infer_type`) | <100ns | 230ns Sort_0 median (2026-05-25 baseline; inner-loop ops 2.6-34ns) |
| Definitional equality | <200ns | 2.8-163ns |
| Batch throughput | 1M ops/sec | 1M ops/sec |
| .olean compatibility | Init + Std + Mathlib | Init + Std lanes; Mathlib via scoped real import or stub fallback |
| Lean 4 cross-validation | Broad real-corpus parity | 2001/2001 synthetic core-calculus cases; broader frontend parity remains gated |
| Self-verified kernel | End-to-end model, Rust checker, and binary correspondence | Nine-constructor, ten-rung reflected metatheory with zero domain/debt census; shipping checker/binary correspondence incomplete |
| Open release-impacting bugs | 0 | Volatile; use the live release-issue hygiene gate, not a frozen count |

Benchmarks measured on Apple M4 Max, 128GB. Full methodology in BENCHMARKS.md.

## Phases

| Phase | Focus | Status |
|-------|-------|--------|
| 1. Kernel + Parser | Trusted type checker core, Lean 4 surface syntax | Working, parity-gated |
| 2. Elaborator + Tactics | Term elaboration and Lean-style tactics | Working slices, parity-gated |
| 3. Automation | SMT/ATP integration via ay, proof reconstruction, Nelson-Oppen | Trust-gated |
| 4. .olean Import + Server | Load selected `.olean` files, JSON-RPC API | Working slices; full validation is opt-in |
| 5. Verification Expansion | C verification (ACSL/CompCert), Rust semantics (VIR/NLL/stacked borrows) | Building |
| 6. Self-Verification | Reflected metatheory plus implementation/binary correspondence | Active, bounded; recursive checker spine remains unproved |
| 7. AI Integration | Universal Proof Database, cross-system proof import, LLM proof automation | Building; replacement replay evidence remains stubbed |

## Strategic Approach

### Phase 1: Lean 4 Parity Target
The target is full replacement compatibility with the Lean 4 ecosystem: loading
arbitrary `.olean` files with full proof validation, running Lean tactics,
importing Mathlib without stubs, and supporting Lake/editor/native-library
workflows without semantic loss. Today Clean has bounded parser/elaboration
slices, selected `.olean` import, scoped Mathlib lanes, and explicit trust
reporting. Those are real steps, not a completed parity claim.

### Phase 2: Performance Leadership Target
Sub-microsecond type checking and million-operation-per-second batch throughput
are design targets backed by historical microbenchmarks. "Fastest theorem
prover" is not a current documented fact without a fresh, reproducible,
apples-to-apples benchmark suite.

### Phase 3: Verification Expansion
Not just Lean code. Verify C programs with ACSL specifications. Verify Rust with parsed-source ingestion, VIR lowering, NLL borrow checking, and stacked-borrows aliasing checks. Bridge to SMT solving via ay. Clean becomes the universal verification backend. C examples live in `crates/clean-c-sem/src/examples.rs` (8 worked examples with ACSL specs and separation logic contracts). Rust examples live in `crates/clean-rust-sem/src/examples.rs`, backed by file fixtures under `crates/clean-rust-sem/examples/`, and exercise source parsing, VIR lowering, NLL, and stacked-borrows evaluation.

### Phase 4: Self-Verification Target
The target is to reduce the kernel TCB by proving implementation properties in
Clean and replayable certificates. Today the reflected metatheory is active and
substantial: its live census has no domain-specific axiom or `DerivedProved`
debt, and its strongest normalization results keep the `CandModel` hypothesis
explicit. That does not prove the literal recursive Rust checker or compiled
binary. Clean still trusts the Rust kernel, three foundational axioms, the
build/toolchain path, OS, and hardware as documented by the soundness and
self-verification certificates.

## The 4/δ Principle

The 4/δ Bound theorem proves: expected iterations to find a proof ≤ 4/δ, where δ is verification success probability.

This is why speed matters. If an LLM prover has 1% success rate per attempt:
- At 1ms/verification: 400ms expected to find proof
- At 100ns/verification: 40μs expected to find proof

If a future benchmark establishes 1000x faster verification for a given
workload, that would mean 1000x more attempts per second for that workload and
could change proof-search economics.

Clean's goal is to make LLM provers cheaper to call and easier to audit. The
efficiency multiplier must be measured per workload.

## The End State

**All of mathematics, formalized.** The Universal Proof Database (UPD) will unify theorems from every major proof assistant: Lean, Coq, Isabelle, Agda, HOL Light, HOL4, Mizar, Metamath. Cross-system proofs of the same theorem. Cross-system equivalence detection. One search interface for all of formal mathematics. The Mathverse Library (39K LOC, 1,220 tests) is the foundation — working importers for Metamath, HOL (via OpenTheory), Mizar XML, Isabelle, and 8 program verification systems, with trust tracking and axiom dependency analysis. The binary shard pipeline and cross-system type-checking are in progress.

**One format, one verifier.** CleanDB stores everything in Clean-native representation. Proofs from other systems are translated to Clean terms during import. Single API. Sub-microsecond verification. No format proliferation.

**AI-powered proof automation.** The Unified Mathematics AI trains on UPD + arXiv (~2.4M papers) for automated software verification. Perfect training signal from the verifier. Unlimited synthetic data via self-play. 95% auto-discharge target.

**More software, verified.** The aspiration is that compilation can produce
both executable artifacts and proof certificates. Verification can rule out
specified bug classes relative to a model; it does not make all bugs
mathematically impossible.

**Unified proof infrastructure.** One prover backend combining:
- Dependent type theory (Lean/Coq)
- Classical automation (Isabelle)
- SMT solving (ay)
- Model checking (TLA+)
- Neural guidance (LLM provers)

Clean as the substrate. tRust as the language. ay as the decision procedure. All verified software flows through this stack.

## Related Designs

- `docs/plans/PLAN_UNIFIED_MATH_AI.md` - historical January strategy for AI
  training on formal + informal math

## Readiness

| Component | Status | Notes |
|-----------|--------|-------|
| Kernel | Working TCB | Core checker exists; implementation-correctness proof incomplete |
| Parser | Working slices | Broad Lean-shaped syntax; full Lean surface parity not claimed |
| Elaborator | Working slices | Tactics and major declarations exist; frontend parity remains gated |
| Automation | Trust-gated | SMT/ATP integration and proof reconstruction exist; trustedAy/trustedArith boundaries remain part of the trust story |
| Server | Functional | JSON-RPC surface exists |
| .olean Import | Working slices | Init/Std/select lanes; full proof validation is opt-in; Mathlib uses real-import lanes or stub fallback |
| C Verification | USABLE | ACSL specifications with worked examples in `crates/clean-c-sem/src/examples.rs` |
| Rust Semantics | BUILDING | Source ingestion, VIR lowering, NLL borrow checking, stacked-borrows evaluation, and a Lean-facing ownership proof-bundle API are implemented, with worked examples in `crates/clean-rust-sem/src/examples.rs` / `crates/clean-rust-sem/examples/`; next gaps are broader Rust spec-language / downstream proof-discharge work beyond the ownership bundle landed in #2944 |
| Self-Verification | ACTIVE, BOUNDED | Nine-constructor reflected calculus, ten modeling rungs, three flagship theorems, zero domain-axiom/DerivedProved debt, and dated independent Lean replay. Fidelity covers selected fragments; the production recursive checker and binary remain unproved end to end. |

**Overall:** Clean has substantial working infrastructure, but the current
release should be described as a trust-accounted verification platform with
bounded Lean-compatibility slices, not as a complete Lean replacement.
Self-verification is substantial but bounded; `.olean` full validation must be
invoked explicitly; and trusted solver/axiom surfaces remain part of the
printed trust story. See the current replacement audit and self-verification
certificate for commit-pinned
boundaries rather than relying on this vision document; the replacement audit
is `docs/AUDIT_LEAN4_REPLACEMENT_2026-07-23.md` in the development tree.

<sub>For current LOC and test counts, see [README.md#status](README.md#status) and verify with `clean release readiness-smoke`.</sub>

## Non-Goals

- Backward compatibility with Lean 3

Note: Error messages are structured for machine parsing AND human-readable. "Built for machines" means machines are the primary consumer, not that humans are excluded.

Clean aims to become a Rust-native replacement and upgrade path for Lean-shaped
verification workflows. It is not there yet.

---

*Track progress via GitHub Issues.*
