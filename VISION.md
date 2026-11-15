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

| Metric | Target | Where "current" comes from |
|--------|--------|---------|
| Type check latency (`infer_type`) | <100ns | Read the freshness gate, never this cell: `python3 scripts/check_benchmark_publication.py --check`, then `reports/benchmarks/publication/current.json`. A latency figure pasted here would rot the same way the last one did |
| Definitional equality | <200ns | Same gate. No number is restated here |
| Batch throughput | 1M ops/sec | Same gate |
| .olean compatibility | Init + Std + Mathlib | Init + Std lanes. Mathlib is further along than "stub fallback": real `.olean` Mathlib targets kernel-verify through Clean — see `docs/plans/MATHLIB_KV_MILESTONE_2026-07-12.md` — whose larger counts are plan prose whose generating JSON was never committed, so `docs/STATUS_ONE_TRUST.md` records that tier UNKNOWN rather than promote them — and the non-regressing pinned slice `data/mathlib_kv_ratchet.json`, which is the committed evidence here. Elaborating Mathlib **source** is the open frontier: `data/source_elab_ratchet.json` + the dated run in `reports/source-elab/` |
| Lean 4 cross-validation | Broad real-corpus parity | `metrics/lean4_parity.json` — a bounded synthetic core-calculus baseline, not a corpus result; broader frontend parity remains gated |
| Self-verified kernel | A Lean-defined checker (`kcheck`) proved sound against a set-theoretic model, per universe bound, compiled by Trust and deciding every authority-bearing acceptance | By design, not in fact. Whether a `kcheck` exists and which units are done is read from the plan's unit rows and the artifact each row names, never from this cell: `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`. Until `kcheck_sound` is re-checked, decision R29 leaves the authority with the Rust kernel under the fenced theory, whose open residuals are the plan's lane F. The nine-constructor, ten-rung reflected metatheory (zero domain/debt census) stays as evidence about fragments, and that plan takes it off the route; `docs/CRYSTAL_STATUS.md` is Crystal as it stood when R29 stopped new chains on it, not live status |
| Open release-impacting bugs | 0 | Volatile; use the live release-issue hygiene gate, not a frozen count |

**Do not quote a latency or throughput number from this document.** Benchmark
evidence is published on a 14-day freshness window and expires. Measured
2026-08-26: the committed metadata in
`reports/benchmarks/publication/current.json` was **past its `fresh_until`
date** (`2026-08-24`) and carried `publication_commit: null` — exactly the
state in which
RELEASE_READINESS.md requires a
public number to be removed or marked historical. Refresh through
`./scripts/run_public_benchmarks.sh` before making any speed claim. Historical
runs were measured on Apple M4 Max, 128GB; full methodology in
BENCHMARKS.md.

## Phases

| Phase | Focus | Status |
|-------|-------|--------|
| 1. Kernel + Parser | Trusted type checker core, Lean 4 surface syntax | Working, parity-gated |
| 2. Elaborator + Tactics | Term elaboration and Lean-style tactics | Working slices, parity-gated |
| 3. Automation | SMT/ATP integration via ay, proof reconstruction, Nelson-Oppen | Trust-gated |
| 4. .olean Import + Server | Load selected `.olean` files, JSON-RPC API | Working slices; full validation is opt-in |
| 5. Verification Expansion | C verification (ACSL/CompCert), Rust semantics (VIR/NLL/stacked borrows) | Building |
| 6. Self-Verification | A proved Lean-defined checker (`kcheck`) that replays the Rust kernel's untrusted advice; the reflected metatheory is kept as evidence | Route adopted 2026-11-12 and by design until its in-fact conditions hold; the Rust kernel is still trusted |
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
The target is one theorem about the running artifact: if the shipped checker
accepts a declaration at universe bound N with axioms within the plan's fixed
set Ax0, the statement is true in a set-theoretic model. The route was adopted
by the owner on 2026-11-12 and is recorded in
`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`:

- **By design the trust root becomes `kcheck`, a checker defined in Lean.** The
  Rust kernel is then no longer trusted. It is to produce advice; `kcheck` is to
  replay that advice and decide. Soundness is to be proved directly against the
  model, for every advice string, one universe bound at a time, with one
  semantic lemma per rule shared by the declarative judgment and the checker.
- **By design `kcheck` is compiled by Trust**, one compiler with two front ends:
  Lean is to reach machine code through Clean's lowering, trust-ir and trust-cg,
  the path Rust takes. The proved term is then the compiled source, and the step
  from source to bytes is to be closed once, in the compiler, by a proved
  validator of its output. Every trusted checker is to be written in Lean; Rust
  is for untrusted producers and a thin shell. Today `clean run` reaches bytes
  through emitted C and the host C compiler, and the trust-ir lane is
  feature-gated.
- **By design the pattern repeats.** A pinned statement, an untrusted producer
  and a small proved checker are to serve the kernel first, then the compiler,
  then Trust's verifier. The end state is Clean merged into Trust, with Trust
  verifying and compiling its own source as Trust plus Lean.

All of this is by design. The plan's section "Owner directive: make it so in
fact" lists five conditions under which it may be called true in fact, each
shown by an artifact a gate mints, and this document claims none of them. Today
Clean still trusts the Rust kernel, three foundational axioms, the build/toolchain path, OS, and hardware as documented by
the soundness and self-verification certificates. The reflected metatheory in
`clean-verify` remains as evidence about fragments: its live census has no
domain-specific axiom or `DerivedProved` debt, and its strongest normalization
results keep the `CandModel` hypothesis explicit. It does not prove the literal
recursive Rust checker or compiled binary. Decision R29 in `docs/DECISIONS.md`
stopped the new work it lists there (new Crystal chains, new
`CandModel`-conditional theorems for fragments with proof irrelevance) and
capped the rest of that work at one non-merge commit in four (decision R4's
cap); the 2026-11-12 plan stops the Crystal part outright and is what takes
this stack off the route.

Three limits hold at the end state as well. A generation cannot prove more
consistency than its base, so the loop improves speed, coverage and engineering,
not logical strength. A checker checking its own soundness proof settles nothing
alone, so the quorum of independent re-checkers stays. Soundness is per universe
bound.

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

**All of mathematics, formalized.** The Universal Proof Database (UPD) will unify theorems from every major proof assistant: Lean, Coq, Isabelle, Agda, HOL Light, HOL4, Mizar, Metamath. Cross-system proofs of the same theorem. Cross-system equivalence detection. One search interface for all of formal mathematics. The Mathverse Library is the foundation — working importers for Metamath, HOL (via OpenTheory), Mizar XML, Isabelle, and 8 program verification systems, with trust tracking and axiom dependency analysis. The binary shard pipeline and cross-system type-checking are in progress. (The "39K LOC, 1,220 tests" that stood here was stale by roughly an order of magnitude — `crates/clean-mathverse/src` is far larger now. Source size is not a capability claim, so no replacement figure is pasted here; re-derive it from the tree if you need it, and read provenance from [`data/MATHVERSE_LIBRARIES.md`](data/MATHVERSE_LIBRARIES.md) and [`data/MATHVERSE_PROVENANCE.md`](data/MATHVERSE_PROVENANCE.md).)

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

Trust compiles Rust and Lean together, and Clean is its Lean language: front end, kernel (the trust root), Lean→trust-ir compiler and runtime. Clean also ships standalone as a full Lean 4 toolchain built from the same crates (owner, 2026-09-30; `designs/2026-09-30-clean-trust-unified-vision.md`). trust-ir is the one IR, trust-cg the one backend, and ay the decision procedure. The trust root is the Rust kernel today and, by design, the Lean-defined `kcheck` (Phase 4 above). Beyond the kernel the end state is Clean merged into Trust, the environment unified before the repositories are, and Trust verifying and compiling its own source as Trust plus Lean (owner, 2026-11-12; `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`).

## Related Designs

- `docs/plans/PLAN_UNIFIED_MATH_AI.md` - historical January strategy for AI
  training on formal + informal math

## Readiness

| Component | Status | Notes |
|-----------|--------|-------|
| Kernel | Working TCB | Core checker exists; implementation-correctness proof incomplete. By design it becomes an untrusted advice producer for `kcheck` (Phase 4) |
| Parser | Working slices | Broad Lean-shaped syntax; full Lean surface parity not claimed |
| Elaborator | Working slices | Tactics and major declarations exist; frontend parity remains gated |
| Automation | Trust-gated | SMT/ATP integration and proof reconstruction exist; trustedAy/trustedArith boundaries remain part of the trust story |
| Server | Functional | JSON-RPC surface exists |
| .olean Import | Working slices | Init/Std/select lanes; full proof validation is opt-in. Real Mathlib `.olean` targets do kernel-verify through Clean — the committed evidence is the pinned slice `data/mathlib_kv_ratchet.json`; the larger milestone counts are unbacked plan prose and are recorded UNKNOWN in `docs/STATUS_ONE_TRUST.md`. The stub fallback lane remains separate, explicitly-labelled lane and is never green evidence |
| C Verification | USABLE | ACSL specifications with worked examples in `crates/clean-c-sem/src/examples.rs` |
| Rust Semantics | BUILDING | Source ingestion, VIR lowering, NLL borrow checking, stacked-borrows evaluation, and a Lean-facing ownership proof-bundle API are implemented, with worked examples in `crates/clean-rust-sem/src/examples.rs` / `crates/clean-rust-sem/examples/`; next gaps are broader Rust spec-language / downstream proof-discharge work beyond the ownership bundle landed in #2944 |
| Self-Verification (the `clean-verify` reflected stack) | LEGACY, OFF THE ROUTE, CAPPED | Nine-constructor reflected calculus, ten modeling rungs, three flagship theorems, zero domain-axiom/DerivedProved debt, and dated independent Lean replay. Fidelity covers selected fragments; the production recursive checker and binary remain unproved end to end. Kept as evidence about fragments: decision R29 stopped the new work it lists and capped the rest at one non-merge commit in four, and the 2026-11-12 plan stops the Crystal part outright and takes the stack off the route. The adopted route (Phase 4) is to replace a proof about the Rust kernel with a proved Lean-defined checker; it is by design, and the plan names the artifact for each unit. |

**Overall:** Clean has substantial working infrastructure, but the current
release should be described as a trust-accounted verification platform with
bounded Lean-compatibility slices, not as a complete Lean replacement.
Self-verification is substantial but bounded; `.olean` full validation must be
invoked explicitly; and trusted solver/axiom surfaces remain part of the
printed trust story. See the current replacement audit and self-verification
certificate for commit-pinned
boundaries rather than relying on this vision document; the replacement audit
is `docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md` in the development tree.

<sub>For the current capability table see [README.md#current-state](README.md#current-state) (there is no `#status` anchor; that link was broken), and verify with `clean release readiness-smoke`. LOC and test counts are not tracked as status metrics — source size is not semantic parity.</sub>

## Non-Goals

- Backward compatibility with Lean 3

Note: Error messages are structured for machine parsing AND human-readable. "Built for machines" means machines are the primary consumer, not that humans are excluded.

Clean aims to become a Rust-native replacement and upgrade path for Lean-shaped
verification workflows. It is not there yet.

---

*Track progress via GitHub Issues.*

---

## Citation ledger (D1)

Under `scripts/check_doc_claims.py` D1 since the gate landed (`3fa04c6c1`,
2026-08-26, one of its four navigation docs). One declaration, added
2026-09-15 with no prose change, when `metrics` became an `IGNORED_ROOTS` row
of that checker: a citation under a gitignored root is checked by declaration
alone and never by what a box holds on disk, so the success-criteria row above
that points at `metrics/lean4_parity.json` has to say what writes it.

<!-- claim: absent metrics/lean4_parity.json gitignored runtime output (.gitignore:41 `metrics/`, `git ls-files metrics` is empty), written by `write_parity_summary` in crates/clean-kernel/tests/lean4_parity.rs when `cargo test --locked -p clean-kernel --test lean4_parity --features test-utils -- lean4_parity_check` runs; present only on a box that has run that test -->


