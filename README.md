# Clean

> A pure-Rust, Lean-shaped theorem-proving and verification stack built for
> programs and AI agents.

**Author:** Andrew Yates · **License:** Apache-2.0 · **Version:** 1.2.0

Clean is a from-scratch Rust implementation of a dependent-type-theory kernel,
Lean 4 surface tooling, proof-producing automation, `.olean` import, native
compilation, and verification APIs. Normal kernel builds forbid unsafe Rust
(`cfg(kani)` is the formal-harness exception), and the kernel is the trusted
core through which supported proof-producing paths flow.

Clean is **not a full Lean 4 replacement today**. It has a strong kernel and
unusually explicit trust accounting; it also has broad parser, elaborator,
tactic, compiler, Lake, and LSP implementations. Those surrounding surfaces do
not yet have Lean-wide parity, and several official replacement-evidence lanes
are missing or stubbed. This README carries the public summary. In the full
development tree, the commit-pinned source assessment is
`docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md`.

## Why Clean?

Clean is designed for uses where theorem proving is a component inside another
system, not only an interactive editor session.

- **Rust-native integration.** Call the checker and source pipeline as a
  library, or use structured CLI/JSON-RPC surfaces. No REPL scraping is needed.
- **Inspectable trust.** Axiom closures, `sorry` markers, import confidence,
  solver reconstruction, and evidence freshness are explicit and fail closed.
- **Proof-carrying automation.** Supported tactics and solver fragments produce
  terms for kernel checking; unsupported strict fragments reject rather than
  silently becoming trusted proofs.
- **Independent checking and provenance.** Clean can recheck selected Lean
  `.olean` proof targets, and Mathverse records cross-system provenance and
  trust state.
- **A verification workbench.** The same Rust workspace connects theorem
  proving, C/Rust verification, compilation, proof search, and experiments in
  self-verifying the kernel.

Those are real advantages for auditable, agent-driven workflows. They are not
a claim that Clean currently surpasses Lean in source compatibility, Mathlib,
metaprogramming, package management, or editor experience.

## Current state

Run the commands rather than relying on this prose:

```bash
clean features
clean replacement status --informational
cargo run --locked -p clean --features math-overlays -- audit soundness
```

`replacement status --informational` is a navigation view. A green row only
means that row's scoped evidence file is present and non-stub; it is not a
fraction of Lean and not a launch certificate. The command without
`--informational` is the fail-closed replacement gate.

At source baseline `48350cc11` audited on 2026-07-22:

| Area | What is implemented | Honest boundary |
|---|---|---|
| Kernel and trust | Dependent checker, universes, inductives/recursors, quotients, literals, projections, explicit axiom/trust audits | C1–C5 passes, but differential evidence is scoped and the Rust kernel remains in the TCB |
| Parser and elaborator | Broad Lean-shaped declaration, term, tactic, macro, notation, class, structure, recursion, and do-notation support | Governed frontend report is not launch-ready; imports and metaprogramming still have explicit fallback/unsupported paths |
| Tactics and solvers | Large builtin registry, proof-term construction, strict reconstruction/rejection lanes | The parity artifact records 56 source-declared representative cases over 8 tactics; its command does not execute a full Lean-vs-Clean corpus |
| `.olean` and Mathlib | Real target-value rechecking, environment replay, and large sampled runs | Sampled pre-elaborated targets are not source parity or a verified full dependency closure; native Mathlib evidence is stubbed and its generated-matrix check currently fails |
| Compiler/runtime | Substantial C, Rust, TrustIR, linking, and runtime machinery; object emission is feature-gated through external TrustCg | Official replacement evidence is one C-emission smoke; entry shapes and external/runtime coverage are bounded |
| Lake and Cake | Clean-owned bounded Lake init/build/run/test paths; Cake project descriptors and verification/graduation | Lake still relies on Lean toolchain artifacts for important libraries; Cake's native backend does not yet build projects |
| LSP/InfoView | A real LSP with completion, navigation, symbols, semantic tokens, actions, and more | Several behaviors are approximate and the parity artifact is a stub |
| Self-verification | Three-foundational-axiom reflected metatheory with confluence, inference-soundness, and a ten-rung recursor/SN program | The reflected fragment is not the literal production calculus; the recursive Rust checker and binary are not end-to-end proved |

There is deliberately no single “percent complete.” The rows have different
denominators, and source size or test count is not semantic parity.

This table describes the full development tree. The current bootstrap
projection also omits `docs/` and `reports/`, so a projected public candidate
does not carry the detailed replacement evidence summarized here. Closing that
distribution/provenance gap is part of release readiness.

## Quick start

Clean requires Rust 1.90 or newer. A host C compiler is needed for C-backend
link/run workflows; text emission itself does not need it.

There are two checkout shapes:

- The **standalone bootstrap projection** removes downstream
  Trust/TrustIR/TrustCg integration edges and resolves its solver dependencies
  to attested Git revisions. It is designed to build as an ordinary clone, but
  the current policy record does not yet claim a successful anonymous-clone
  compile; that remains a promotion gate.
- This **development workspace** keeps those cross-repository integrations. It
  requires sibling checkouts at `../trust`, `../trust-ir`, and `../trust-cg`;
  Cargo validates workspace path dependencies even when a particular backend
  is optional or test-only. `ay` is pinned as a Git dependency and does not
  require a sibling checkout.

From a generated standalone bootstrap candidate:

```bash
cargo build --locked --release -p clean --bin clean

# Type-check accepted source.
target/release/clean check demos/public/kernel_check_success.lean

# Confirm explicit trust debt is rejected by default.
target/release/clean check demos/public/kernel_check_reject_sorry.lean

# Run the pinned accept/reject public demo contract.
./scripts/run_public_demo.sh
```

Discover the CLI from the binary:

```bash
target/release/clean --help
target/release/clean features
target/release/clean help check
target/release/clean help replacement.status
```

Useful entry points include `check`, `eval`, `repl`, `server`, `auto`, `prove`,
`olean`, `mathverse`, `verify-c`, `verify rust`, `compile`, `run`, `lake`, `lsp`,
`audit`, and `replacement`.

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
types are available through `clean` / `clean::prelude`; certificate types are
available at the crate root and under `clean::kernel::cert`.

`CheckResult::is_fully_verified()` means that this source-load operation had no
local failures, warnings, or `sorry` count. It is not a transitive axiom-closure
certificate; inspect declaration trust/axiom evidence for that stronger claim.

Non-Rust clients can use `clean server` for JSON-RPC. The development tree's
reference is `docs/JSON_RPC_API.md`.

## Trust model

“Accepted,” “imported,” and “proved” are not synonyms in Clean.

- A theorem is called **proved** only when its transitive dependency closure has
  no domain-specific axioms and stays within the named foundational floor.
- Structural `.olean` registration and fallback stubs are not kernel
  re-verification. Use the full-validation path and inspect per-declaration
  confidence.
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

The audit subcommand is compiled only when the `math-overlays` feature is
enabled; a default-feature binary reports that requirement instead of running
the certificate.

The declared genuine axiom floor is currently:

```text
propext · Quot.sound · Classical.choice
```

The kernel remains trusted until the source-to-binary self-verification bridge
is complete.

## Self-verification

Clean's self-verification work has two separate layers.

**Layer 1** models the calculus inside `clean-verify`. Its environment census is
11 value-less constants: three genuine foundational axioms, four quotient
primitives, and four anti-trust tripwires proved unreachable from certified
claims. It has zero domain-specific axioms and zero current DerivedProved debt.
The reflected expression model now has nine
constructors—sort, bound variable, application, lambda, Pi, constant, let,
projection, and literal—and the source contains generic, indexed, mutual,
W/Acc, and nested recursor/strong-normalization rungs. The strong-normalization
results remain conditional on the explicitly named `CandModel` hypothesis, and
not every represented constructor has been connected to every production
typing/reduction rule.

Adversarial proof-farm work at this checkpoint also found that a dependent
preservation statement shared by three guide models was false without a
well-formed-context (`WfCtx`) premise. Corrected guides were resubmitted, but
guide elaboration is not counted as proof and this adjacent finding does not
change the live 11-item spec census.

**Layer 2** must prove that the literal Rust implementation and compiled binary
refine that model. Bounded differential gates and default-on translation
certificates now cover selected reduction/compiler fragments. They do not yet
certify the mutually recursive production `infer_type` / `whnf` / `is_def_eq`
spine end to end.

The last recorded independent Lean replay—3,309/3,309 exported spec definitions
with zero skips—was run on 2026-07-14 at `2bcef0713`, modulo the documented Quot,
structure/projection, and Nat-literal constructor-normalization adapter
mappings. It is valuable dated evidence, not a claim that the current source
baseline was rechecked.

The development tree contains the detailed claim ledger at
`docs/SELF_VERIFICATION_CERTIFICATE.md` and architecture at
`docs/SELF_VERIFICATION_PROGRAM.md`. The replacement audit explains the
boundary in compact form.

## Architecture

The full development workspace has 27 crates. The standalone bootstrap
projection currently removes the two downstream-integration crates
`clean-autoform` and `clean-reflect`, leaving 25. The main development-tree flow
is:

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

supported declarations ──► compiler ──► C / Rust / TrustIR
                                      └─ feature-gated TrustCg object / C link+run
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
| `clean-c-sem`, `clean-rust-sem`, `clean-tla` | Program and specification verification |
| `clean-verify`, `clean-reflect` | Reflected metatheory and development-tree correspondence work; `clean-reflect` is omitted from the bootstrap projection |
| `clean-server`, `clean-cli` | JSON-RPC and unified CLI |

## Development and verification

The repository's enforcement is local; there are no active hosted workflow
gates in this checkout.

```bash
just                 # list workflows
just ci              # fmt-check + clippy + fast tests
just test-fast       # publish smoke surface
just clippy          # warning-free workspace gate

# Target a subsystem while developing it.
cargo test --locked -p clean-kernel
cargo test --locked -p clean-elab
```

Run the full suite only when its cost is intended:

```bash
cargo test --locked --workspace --message-format=short -j 1
```

Development checkouts also contain `AGENTS.md` for agent rules and `CLAUDE.md`
for contributor context.

## Documentation

The standalone bootstrap projection intentionally omits `docs/`, `AGENTS.md`,
and `CLAUDE.md`; this README is therefore self-contained and links only files
that survive that projection. Full development checkouts additionally contain:

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
