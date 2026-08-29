# Clean

> A pure-Rust, Lean-shaped theorem-proving and verification stack built for
> programs and AI agents.

**Author:** Andrew Yates · **License:** Apache-2.0 · **Version:** `0.5.0`
(`[workspace.package] version` in `Cargo.toml`)

Clean is a from-scratch Rust implementation of a dependent-type-theory kernel,
Lean 4 surface tooling, proof-producing automation, `.olean` import, native
compilation, and verification APIs. Normal kernel builds forbid unsafe Rust
(`cfg(kani)` is the formal-harness exception), and the kernel is the trusted
core through which supported proof-producing paths flow.

Clean is **not a full Lean 4 replacement today**. It has a strong kernel and
unusually explicit trust accounting, plus broad parser, elaborator, tactic,
compiler, Lake, and LSP implementations — but those surfaces lack Lean-wide
parity, and several replacement-evidence lanes are missing or stubbed. The
commit-pinned source assessment is `docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md`.

## Why Clean?

Clean is built for uses where theorem proving is a component inside another
system, not only an interactive editor session.

- **Rust-native integration.** Call the checker and source pipeline as a
  library, or use structured CLI/JSON-RPC surfaces. No REPL scraping is needed.
- **Inspectable trust.** Axiom closures, `sorry` markers, import confidence,
  solver reconstruction, and evidence stub state are explicit; the replacement
  gate fails closed. Evidence freshness is commit-pinned in some lanes and an
  open gap in others.
- **Proof-carrying automation.** Supported tactics and solver fragments produce
  terms for kernel checking; unsupported strict fragments reject rather than
  silently becoming trusted proofs.
- **Independent checking in one workspace.** Clean can recheck selected Lean
  `.olean` targets, Mathverse records cross-system provenance, and the same
  workspace carries C/Rust verification, compilation, and proof search.

These are advantages for auditable, agent-driven workflows, not a claim that
Clean surpasses Lean in source compatibility, Mathlib, metaprogramming, package
management, or editor experience.

## Current state

Run the commands rather than relying on this prose:

```bash
clean features
clean replacement status --informational
cargo run --locked -p clean --features math-overlays -- audit soundness
```

`replacement status --informational` is a navigation view. A green row means
only that the row's declared evidence artifact validated against its declared
contract — it parses, carries the exact expected `schema_version`, does not
report its own failure, and is git-tracked
(`crates/clean-cli/src/cmd_replacement/evidence_contract.rs`); an undeclared
path is fail-closed. That is not a fraction of Lean and not a launch
certificate. Without `--informational` the same command is the replacement gate
and exits non-zero when the tree is not launch-ready.

The table is pinned to the audit's own source baseline `48350cc11` (2026-07-22).
Where an artifact is named, read it rather than this cell.

| Area | What is implemented | Honest boundary |
|---|---|---|
| Kernel and trust | Dependent checker, universes, inductives/recursors, quotients, literals, projections, explicit axiom/trust audits | C1–C5 (plus C4') pass, but differential evidence is scoped and the Rust kernel remains in the TCB |
| Parser and elaborator | Broad Lean-shaped declaration, term, tactic, macro, notation, class, structure, recursion, and do-notation support | The governed frontend report is not launch-ready; imports and metaprogramming still have explicit fallback/unsupported paths |
| Tactics and solvers | Large builtin registry, proof-term construction, strict reconstruction/rejection lanes | `reports/tactic-parity-counts.json` records 56 source-declared representative cases over 8 tactics; it does not execute a Lean-vs-Clean corpus, and the artifact that would accept one, `reports/tactic-parity-full-corpus.json`, is `{"stub": true}` |
| `.olean` and Mathlib | Real target-value rechecking, environment replay, and large sampled runs; real Mathlib `.olean` targets do kernel-verify through Clean. The minted pin is `data/mathlib_kv_ratchet.json` — 702 kernel-verified declarations over the two-module slice in `data/kv_ratchet_slice.txt`, re-stamped by `scripts/kv_ratchet_gate.sh` on every full local gate and failing closed if the count drops or a target is only heuristically verified | Rechecking pre-elaborated targets is **not** source elaboration and not a verified dependency closure. The larger counts in `docs/plans/MATHLIB_KV_MILESTONE_2026-07-12.md` are prose whose generating JSON was never committed, so `docs/STATUS_ONE_TRUST.md` records that tier UNKNOWN rather than promote an unbacked number. Mathlib SOURCE elaboration is the open frontier: `data/source_elab_ratchet.json` records 326 of 784 declarations over five pinned files as allow-sorry successes — not a sorry-free claim — with dated runs in `reports/source-elab/`. Native evidence `reports/native-library-replacement.json` is `{"stub": true}`, so `clean replacement native-library coverage-matrix --check-report reports/native-library-replacement.json --json` cannot pass against it |
| Compiler/runtime | Substantial C, Rust, L5CNF/L5IR, linking, and runtime machinery. `clean compile` runs the real elaborate-check-lower-emit path (`--emit l5ir\|l5cnf\|c\|rust`); `clean run` continues it through `cc`, links the embedded runtime, and executes. TrustIR and object emission need the `trust-ir-backend` feature and an external `trust-cg` | The only minted evidence is one C-emission smoke (`reports/compile-runtime-smoke.json`), which understates the pipeline; entry shapes and external/runtime coverage are bounded |
| Lake and Cake | Clean-owned Lake init/build/run/test. On a `clean lake init` template, `init` + `build` + `test` run entirely in-process and never spawn Lean 4's `lean` or `lake`, even with both on PATH — `reports/lake-replacement-smoke.json` (`no_lean4_delegation`), gated by `crates/clean-cli/tests/lake_replacement_delegation.rs` | That smoke is bounded by its own `non_claims`: no transitive dependency resolution, no `lake serve`, no facets/custom targets, no Mathlib cloud cache. Lake still loads Init/Std/Lean/Lake/Mathlib `.olean` data from a Lean toolchain. `clean cake` still shells out: its `olean` backend runs external `lake build` (`crates/clean-cli/src/cmd_cake.rs`), and its `native` backend compiles nothing |
| LSP/InfoView | A real LSP: 48 methods handled (42 protocol plus six `$/lean/*` procedures), none an unconditional null stub — each computes from live document/parse/elaboration state. Hover resolves the identifier under the cursor against the document and its import closure, falling back to the enclosing declaration (`crates/clean-lsp/src/backend/hover.rs`) | The gap is depth, not coverage: goal state is one snapshot per theorem rather than per tactic step; the symbol index holds only OPEN documents and is purged on `didClose`, so goto-definition into an imported library returns nothing; references/rename are whole-identifier text scans with no scope or shadowing awareness, so a rename can rewrite unrelated occurrences. The parity artifact `reports/lsp-infoview-parity.json` is `{"stub": true}` and the fail-closed validator holds the row at `pending_evidence` |
| Self-verification | Three-foundational-axiom reflected metatheory with confluence, typed-context preservation/inference soundness, and a ten-rung recursor/SN program | Contextual theorems are conditional on explicit candidate/environment interfaces; constant level instantiation, projection/literal typing, and the Rust-state-to-context refinement bridge remain open |

There is deliberately no single “percent complete”: the rows have different
denominators, and source size or test count is not semantic parity. The table
describes the full development tree — the bootstrap projection omits `docs/`,
`reports/`, `publish/`, `AGENTS.md`, and `CLAUDE.md`, so a public candidate does
not carry the evidence files cited here. Closing that provenance gap is part of
release readiness.

## Quick start

Clean's declared minimum is Rust 1.90 (`rust-version` in `Cargo.toml`). A host
C compiler is needed for C-backend link/run workflows; text emission is not.

There are two checkout shapes, and they do **not** share a toolchain:

- The **standalone bootstrap projection**, generated by `publish/transform.py`,
  removes the Trust/TrustIR integration crates `clean-autoform` and
  `clean-reflect` and the Ty/TLA+ crate `clean-tla` (breaking the Clean↔Ty
  release cycle), and resolves its remaining dependencies to attested Git
  revisions. It is designed to build as an ordinary clone, but the policy record
  does not yet claim a successful anonymous-clone compile; that remains a
  promotion gate.
- This **development workspace** keeps those cross-repository integrations and
  requires no sibling checkouts: `ay`, `trust-ir-contract`, and `tla-core` are
  pinned as exact-revision Git dependencies, and no manifest references
  `../trust`, `../trust-ir`, `../trust-cg`, or `../ty`. It does pin
  `channel = "trust"` in `rust-toolchain.toml` — the ALab verifying compiler
  fork, resolved from a locally linked toolchain — so it does not build on stock
  Rust as-is. The projection swaps that file and `.cargo/config.toml` for
  `publish/public-rust-toolchain.toml` and `publish/public-cargo-config.toml`;
  that swap, not the 1.90 floor alone, is what makes a clone buildable.

From a generated standalone bootstrap candidate:

```bash
cargo build --locked --release -p clean --bin clean

# Type-check accepted source, then confirm explicit trust debt is rejected.
target/release/clean check demos/public/kernel_check_success.lean
target/release/clean check demos/public/kernel_check_reject_sorry.lean

# The pinned accept/reject public demo contract.
./scripts/run_public_demo.sh

# Discover the CLI from the binary itself.
target/release/clean --help
target/release/clean features
target/release/clean help replacement.status
```

`clean help` accepts a space- or dot-joined topic path. Entry points include
`check`, `eval`, `repl`, `server`, `auto`, `prove`, `olean`, `mathverse`,
`verify-c`, `verify rust`, `compile`, `run`, `lake`, `lsp`, `kernel`, `cert`,
`export-cert`, `audit`, and `replacement`; `clean --help` lists the rest.

## Rust API

The `clean` crate exposes the source pipeline and kernel types directly:

```rust
use clean::{check_source, CheckConfig};

let result = check_source(
    "def answer : Nat := 42",
    &CheckConfig::default(),
)
.expect("source should parse, elaborate, and check");

assert!(result.is_fully_verified());
assert_eq!(result.passed_count, 1);
```

For incremental work, create an `Environment` with
`Environment::try_with_prelude()`, import `clean::EnvironmentExt`, and call
`load_lean_source`. Kernel expression, batch-checking, and `.olean` loading
types come through `clean` / `clean::prelude`; certificate types live at the
crate root and under `clean::kernel::cert`.

`CheckResult::is_fully_verified()` means this source-load had no local failures,
warnings, or `sorry` count. It is not a transitive axiom-closure certificate;
inspect declaration trust/axiom evidence for that stronger claim.

Non-Rust clients can use `clean server` for JSON-RPC (`docs/JSON_RPC_API.md`).

## Trust model

“Accepted,” “imported,” and “proved” are not synonyms in Clean.

- A theorem is called **proved** only when its transitive dependency closure has
  no domain-specific axioms and stays within the named foundational floor.
- Structural `.olean` registration and fallback stubs are not kernel
  re-verification. Use the full-validation path and inspect per-declaration
  confidence.
- Imports fail closed. A module that resolves to no `.olean`, no elaborated
  project source, and no named prelude provider is an error, not a fabricated
  environment; the legacy warn-and-continue behavior needs an explicit
  `clean check --permissive-imports`, and every fabrication it makes is logged.
- A tactic being registered does not imply that every Lean behavior of that
  tactic is supported.
- External solver success is trusted only where a checked reconstruction path
  establishes it; strict unsupported fragments reject or remain explicit debt.
- A `{"stub": true}` report is a placeholder, never green evidence.

The local soundness gate checks declaration construction, the axiom golden,
trust-marker reachability, opaque-body masking, and adversarial negative
controls:

```bash
cargo run --locked -p clean --features math-overlays -- audit soundness
```

Only the `soundness` certificate is compiled behind the `math-overlays`
feature; a default-feature binary reports that requirement instead of running
it, while the other `audit` verbs still work.

The declared genuine axiom floor is currently:

```text
propext · Quot.sound · Classical.choice
```

That set is pinned exactly, not by allowlist, in
`crates/clean-verify/tests/axiom_ratchet.rs` — and it is measured over the
soundness-certificate environment, which is not the prelude a bare
`clean check` loads. That default environment is censused separately in
`data/prelude_axiom_ratchet.json`: 296 axioms, of which 289 are
non-foundational (283 signature debt, two asserted propositions, four trust
markers), with zero admitted domain axioms and no theorem or definition
currently reaching that debt. The kernel remains trusted until the
source-to-binary self-verification bridge is complete.

## Self-verification

Clean's self-verification work has two separate layers.

**Layer 1** models the calculus inside `clean-verify`. Its environment census
(`data/clean_verify_axiom_ratchet.json`) is 11 value-less constants: three
genuine foundational axioms, four quotient primitives, and four anti-trust
tripwires proved unreachable from certified claims. It has zero domain-specific
axioms and zero current DerivedProved debt
(`data/clean_verify_derivedproved_debt.json`). The reflected expression model
has nine constructors — sort, bound variable, application, lambda, Pi, constant,
let, projection, and literal — and the source contains generic, indexed, mutual,
W/Acc, and nested recursor/strong-normalization rungs. The
strong-normalization results remain conditional on the explicitly named
`CandModel` hypothesis, and not every represented constructor has been connected
to every production typing/reduction rule.

The contextual model checks contexts semantically and requires conversion
targets to inhabit a sort; its preservation results materially use the
well-formed-context (`WfCtx`) obligation and retain the semantic parameters
`PiInj` (proof irrelevance) or `Confl` (confluence), which a foundational-only
axiom closure does **not** discharge. The older context-free `Typing`/`has_type`
and state-shaped accept relations are fenced as legacy raw models that cannot
appear in contextual flagship closures.

**Layer 2** must prove that the literal Rust implementation and compiled binary
refine that model. Bounded differential gates and default-on translation
certificates cover selected reduction/compiler fragments. They do not yet
certify the mutually recursive production `infer_type` / `whnf` / `is_def_eq`
spine end to end.

The last recorded independent Lean replay was rerun on **2026-08-11**: 5,211
emitted declarations, 5,871 spec definitions covered, exactly three explicit
axioms, and zero skips or Lean errors — modulo the documented Quot,
structure/projection, and Nat-literal adapter mappings. That is dated evidence,
not a claim that the current baseline was rechecked; read the live counts from
`docs/SELF_VERIFICATION_CERTIFICATE.md` §4, and the architecture from
`docs/SELF_VERIFICATION_PROGRAM.md`.

## Architecture

The full development workspace has 27 crates. The standalone bootstrap
projection removes `clean-autoform`, `clean-reflect`, and `clean-tla`, leaving
24. The main development-tree flow is:

```text
Lean-shaped source
      │
      ▼
 parser ──► elaborator ──► tactics / automation ──► kernel ──► accepted declaration
                                                              or optional certificate
                  │                    │
                  │                    ├─ ay SMT + checked reconstruction
                  │                    ├─ superposition / premise selection
                  │                    └─ Mathverse search and replay
                  │
                  └─ `.olean` environment import / explicit validation

supported declarations ──► compiler ──► L5CNF / L5IR ──► C / Rust
                                      └─ TrustIR / object via feature-gated TrustCg
```

Major crates:

| Crate | Role |
|---|---|
| `clean` | Public Rust facade and source-check pipeline |
| `clean-kernel` | Trusted type checker and certificates |
| `clean-parser` | Lean-shaped surface parser |
| `clean-elab` | Elaboration, tactics, and macro/meta subsets |
| `clean-auto` | SMT, reconstruction, superposition, premise selection |
| `clean-olean` | Lean `.olean` loading and verification lanes |
| `clean-compiler`, `clean-runtime` | Lowering, code generation, and runtime |
| `clean-lake`, `clean-cake`, `clean-lsp` | Project, compatibility, and editor surfaces |
| `clean-mathverse` | Provenance-labeled cross-system mathematics |
| `clean-c-sem`, `clean-rust-sem` | Program and specification verification; `clean-tla` (TLA+/TLAPS) is omitted from the bootstrap projection |
| `clean-verify`, `clean-reflect` | Reflected metatheory and development-tree correspondence work |
| `clean-server`, `clean-cli` | JSON-RPC and unified CLI |

## Development and verification

Enforcement is local; there are no hosted workflow gates in this checkout.
`just gate` and the pre-push hook it installs are what hold the line.

```bash
just                 # list workflows
just ci              # hooks-check + fmt-check + lint-coverage + clippy + test-fast
just test-fast       # publish smoke surface (the workspace default-members)
just gate            # local fail-closed soundness + quality gate
just install-hooks   # install the tracked pre-push hook repo-wide

# Target a subsystem while developing it.
cargo test --locked -p clean-kernel
cargo test --locked -p clean-elab
```

Run the full suite only when its cost is intended:

```bash
cargo test --locked --workspace --message-format=short -j 1
```

## Documentation

These live in a full development checkout, not in a bootstrap projection:

| Topic | Document |
|---|---|
| Current Lean 4 replacement audit | `docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md` |
| Soundness gate and TCB | `docs/SOUNDNESS_CERTIFICATE.md` |
| Self-verification claim ledger | `docs/SELF_VERIFICATION_CERTIFICATE.md` |
| Self-verification architecture | `docs/SELF_VERIFICATION_PROGRAM.md` |
| Trust and correctness register | `docs/VERIFICATION_AUDIT.md` |
| Public demo contract | `docs/PUBLIC_DEMO.md` |
| Release readiness | `docs/RELEASE_READINESS.md` |
| Benchmark methodology | `docs/BENCHMARKS.md` |
| Design and philosophy | `docs/DESIGN.md`, `docs/PHILOSOPHY.md` |
| JSON-RPC and CLI | `docs/JSON_RPC_API.md`, `docs/cli/index.md` |
| Strategic direction | [`VISION.md`](VISION.md) |
| Credits and citation | [`ACKNOWLEDGMENTS.md`](ACKNOWLEDGMENTS.md), [`CITATION.cff`](CITATION.cff) |

## License

Apache-2.0. See [`LICENSE`](LICENSE).

Copyright 2026 Andrew Yates
