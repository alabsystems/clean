# Clean

> A pure-Rust, Lean-shaped theorem-proving and verification stack built for
> programs and AI agents.

**Author:** Andrew Yates · **License:** Apache-2.0 · **Version:** `0.9.0`
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

The replacement burndown tracks
measured case remainders, open work packages and their completion criteria.

Run the commands rather than relying on this prose:

```bash
clean features
clean replacement status --informational
targo --unverified run --locked -p clean --features math-overlays -- audit soundness
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
| Tactics and solvers | Large builtin registry, proof-term construction, strict reconstruction/rejection lanes | The two-way evidence is per row: pinned Lean's verdict on every declaration of the G-AUTO and G-SIMP family fixtures is minted into `tests/fixtures/tactic_families/g_auto/LEAN_VERDICTS.json` and its `g_simp` twin, and a measured family run reports `totals.clean_accepts_lean_rejects` (with its in-world subset) in `reports/tactic-families/<family>-latest.json`. The committed latest artifacts are v1 (2026-09-15): they carry no two-way totals until the next measured run, and `scripts/tactic_parity/family_gate.py --check-artifact` refuses them. Of the 111 rows pinned Lean rejects, 92 are probes whose only unknown tactics are Mathlib-world tactics (`aesop`, `norm_num`, `linarith`, …) that `import Init` does not provide; the other 19 are in world, `library_search` (renamed `exact?` in Lean v4.3.0) among them. `reports/tactic-parity-counts.json` (56 source-declared cases over 8 tactics) executes nothing, and `reports/tactic-parity-full-corpus.json` is `{"stub": true}` |
| `.olean` and Mathlib | Real target-value rechecking, environment replay, and large sampled runs; real Mathlib `.olean` targets do kernel-verify through Clean. The minted pin is `data/mathlib_kv_ratchet.json` — 702 kernel-verified declarations over the two-module slice in `data/kv_ratchet_slice.txt`, re-stamped by `scripts/kv_ratchet_gate.sh` on every full local gate and failing closed if the count drops or a target is only heuristically verified | Rechecking pre-elaborated targets is **not** source elaboration and not a verified dependency closure. The larger counts in `docs/plans/MATHLIB_KV_MILESTONE_2026-07-12.md` are prose whose generating JSON was never committed, so `docs/STATUS_ONE_TRUST.md` records that tier UNKNOWN rather than promote an unbacked number. Mathlib SOURCE elaboration is the open frontier: `data/source_elab_ratchet.json` records 326 of 784 declarations over five pinned files as allow-sorry successes — not a sorry-free claim — with dated runs in `reports/source-elab/`. Native evidence `reports/native-library-replacement.json` is `{"stub": true}`, so `clean replacement native-library coverage-matrix --check-report reports/native-library-replacement.json --json` cannot pass against it |
| Compiler/runtime | Substantial C, Rust, L5CNF/L5IR, linking, and runtime machinery. `clean compile` runs the real elaborate-check-lower-emit path (`--emit l5ir\|l5cnf\|c\|rust`); `clean run` continues it through `cc`, links the embedded runtime, and executes. TrustIR and object emission need the `trust-ir-backend` feature and an external `trust-cg` | Evidence is a byte-exact differential battery against pinned Lean (`reports/native-exec-battery.json`, `targo --unverified test --locked -p clean --test native_exec_battery`): every program prints exactly Lean's bytes or is refused by name, and none prints a wrong answer at exit 0. It measures fail-closedness, not parity -- most idiomatic programs are still refused, and entry shapes and external/runtime coverage are bounded |
| Lake and Cake | Clean-owned Lake init/build/run/test. On a `clean lake init` template, `init` + `build` + `test` run entirely in-process and never spawn Lean 4's `lean` or `lake`, even with both on PATH — `reports/lake-replacement-smoke.json` (`no_lean4_delegation`), gated by `crates/clean-cli/tests/lake_replacement_delegation.rs` | That smoke is bounded by its own `non_claims`: it drives only init/build/test, so it does not exercise transitive dependency resolution, `lake serve`, facets/custom targets, or the Mathlib cloud cache. The `serve` verb itself does ship — the Lake-compatible editor entry point is dispatched at `crates/clean-cli/src/cmd_lake/serve.rs`; it is outside this smoke, not absent. Lake still loads Init/Std/Lean/Lake/Mathlib `.olean` data from a Lean toolchain. `clean cake` still shells out: its `olean` backend runs external `lake build` (`crates/clean-cli/src/cmd_cake.rs`), and its `native` backend compiles nothing |
| LSP/InfoView | A real LSP: 48 methods handled (42 protocol plus six `$/lean/*` procedures); 45 compute from live document/parse/elaboration state, and the three formatting requests answer `null` by design (withdrawn and not advertised: pinned Lean has no formatter, and Clean's trimmed bytes inside string literals). Hover resolves the identifier under the cursor against the document and its import closure, falling back to the enclosing declaration (`crates/clean-lsp/src/backend/hover.rs`) | The gap is depth, not coverage: goal state is one snapshot per theorem rather than per tactic step; the symbol index holds only OPEN documents and is purged on `didClose`, so goto-definition into an imported library returns nothing; references/rename are whole-identifier text scans with no scope or shadowing awareness, so a rename can rewrite unrelated occurrences. The parity artifact `reports/lsp-infoview-parity.json` is `{"stub": true}` and the fail-closed validator holds the row at `pending_evidence` |
| Self-verification | Three-foundational-axiom reflected metatheory with confluence, typed-context preservation/inference soundness, and a ten-rung recursor/SN program | Contextual theorems are conditional on explicit candidate/environment interfaces; constant level instantiation, projection/literal typing, and the Rust-state-to-context refinement bridge remain open |

Newer than the table's baseline, and so stated here and not in a cell: the
Self-verification row describes the reflected `clean-verify` stack. It is
evidence about fragments, and the kernel self-proof route the owner adopted on
2026-11-12 takes it off the route. That route is a proved Lean-defined checker,
which is by design and not in fact ([Self-verification](#self-verification)).

There is deliberately no single “percent complete”: the rows have different
denominators, and source size or test count is not semantic parity. The table
describes the full development tree — the bootstrap projection omits `docs/`,
`reports/`, `publish/`, `AGENTS.md`, and `CLAUDE.md`, so a public candidate does
not carry the evidence files cited here. Closing that provenance gap is part of
release readiness.

## Quick start

Clean is a component of aterm's self-contained toolchain, alongside AY (the SMT
solver). The package recipe in `Cargo.toml` enables `clean/carcara-verify`,
including its required `ay-smt` lane, so rebuilt managed packages can independently
check Alethe proofs for trust-cg. The default source build exposes
`cert verify-external` without this checking capability. Recipe changes take
effect when a new package is built; inspect the installed package with
`aterm pkg which clean` and `aterm pkg doctor`.

The local release gate checks the recipe and runs valid and invalid Alethe proofs
through the actual CLI.

Clean's declared minimum is Rust 1.90 (`rust-version` in `Cargo.toml`). A host
C compiler is needed for C-backend link/run workflows; text emission is not.

Clean builds with the Trust toolchain (`channel = "trust"` in
`rust-toolchain.toml`) in both checkout shapes. Install
[aterm](https://github.com/alabsystems/aterm#install); atpkg installs Trust
(`aterm pkg install trust` does it by hand, `aterm pkg which targo` shows where
it lives). Every Rust command names its lane: `targo --unverified <verb>` builds
with no proof claim, `targo trust <verb>` verifies. atpkg ships Trust for
Apple-silicon macOS only; there is no public Trust package or supported install
path on any other platform today.

- The **standalone bootstrap projection**, generated by `publish/transform.py`,
  removes the Trust/TrustIR integration crates `clean-autoform` and
  `clean-reflect` and the Ty/TLA+ crate `clean-tla` (breaking the Clean↔Ty
  release cycle), and resolves its remaining dependencies to attested Git
  revisions. It also leaves out `clean-olean`'s dev-only SemR test cohort: the
  test dependencies `trust-ir-semr` and `trust-wp-vc`, which pin TrustIR and
  TrustWP revisions of their own, and the integration tests that use them. The
  projection vendors one TrustIR snapshot, the production one, and refuses any
  use of that cohort outside a dev-dependency. It builds as an ordinary clone:
  Clean's promotion gate compiles the transformed candidate in a fresh
  anonymous clone. Since 2026-11-14 that gate is the unverified build lane and
  makes no proof claim (`scripts/test_atpkg_recipe.py`, `targo --unverified
  build --locked -p clean -p clean-lsp --features clean/carcara-verify`, then
  the `atpkg_proof_checker` test; the advisory `targo trust check
  --allow-l0-gaps` of the whole workspace and the public library suite,
  `scripts/check_public_release_libraries.sh`, are recorded in
  `publish/config.sh` as the gates to restore). The publication
  engine refuses to record a mapping whose attestation does not carry
  `guards.public_clone = "pass"`, and every Clean row in the ledger is
  `release_mode: "buildable"`. Read the ledger for which revision that is; do
  not copy one here.
- This **development workspace** keeps those cross-repository integrations and
  requires no sibling checkouts: `ay`, `trust-ir-contract`, and `tla-core` are
  pinned as exact-revision Git dependencies, and no manifest references
  `../trust`, `../trust-ir`, `../trust-cg`, or `../ty`. **The pin is not a
  verification claim.** An ordinary build runs in `targo --unverified`, which
  switches the Trust verifier off for every unit itself — first-party
  `clean-*` crates included — and makes no proof claim. `.cargo/config.toml`
  is policy-only: since 2026-10-07 it carries no `-Ztrust-verify=off` (a Targo
  built from Trust main refuses any project-config off-switch under
  `targo trust`). Verification is `targo trust <verb>`; CLAUDE.md's
  *Toolchain posture* section records the verified lane and points at the
  deliberate strict lane (`scripts/trust_verify_ratchet.sh`) that runs Trust
  Level-0 verification over `clean-kernel` — a separate gate, and never a
  property of an ordinary build. The projection ships
  `publish/public-cargo-config.toml` in place of that config.

From a generated standalone bootstrap candidate:

```bash
targo --unverified build --locked --release -p clean --bin clean

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
targo --unverified run --locked -p clean --features math-overlays -- audit soundness
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
`data/prelude_axiom_ratchet.json`, with zero admitted domain axioms, no
asserted proposition, 16 signature-debt constants and four trust markers; no
theorem reaches that debt and one definition (`instMonadIO`) does. Its
baseline is 27 axioms, of which 20 are non-foundational.
<!-- claim: figure data/prelude_axiom_ratchet.json baseline_axioms_total -->
<!-- claim: figure data/prelude_axiom_ratchet.json baseline_non_foundational -->

The Rust kernel is the trusted core today. The adopted route replaces it as
the authority with a proved checker written in Lean; that is by design, not in
fact (see [Self-verification](#self-verification)).

## Self-verification

**The adopted route (owner, 2026-11-12).** The trust root is to become `kcheck`,
a checker defined in Lean that replays untrusted advice from the Rust kernel.
Its headline theorem is to be semantic soundness against a set-theoretic model,
per universe bound, for every advice string. By design `kcheck` is Lean
compiled by Trust (Clean's lowering, trust-ir, trust-cg), so that the proved
term is the compiled source, and the step from source to bytes is to be closed
once by a proved validator of the compiler's output. Under the plan trusted
checkers are therefore to be written in Lean; Rust is for untrusted producers
and a thin shell. The same three parts — a pinned statement, an untrusted
producer, a small proved checker — are to repeat for the compiler and for
Trust's verifier. The route of record, with the artifact that says whether each
unit is done, is `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`.

That is by design, not in fact. Status is not restated here: whether a `kcheck`
exists and how far it reaches is read from the plan's unit rows and the
artifact each row names, and what the Lean specification covers from the README
under `theories/cic_l`. The plan's five in-fact conditions cannot hold before a
`kcheck` does. Today `clean run` reaches bytes through emitted C and the host C
compiler, and the trust-ir lane is feature-gated. Until `kcheck_sound` is
re-checked, decision R29 in `docs/DECISIONS.md` leaves the authority with the
Rust kernel under the fenced theory, whose open residuals are the plan's
lane F. The limits are part of the claim:
soundness is per universe bound, a generation cannot prove more consistency
than its base, and a checker checking its own soundness proof settles nothing
alone, so a quorum of independent re-checkers stays.

The work described below predates that route, and the plan takes it off the
route. It remains as evidence about fragments, in two separate layers.

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

**Layer 2** set out to prove that the literal Rust implementation and compiled
binary refine that model. Decision R29 in `docs/DECISIONS.md` stopped new
chains in that direction and capped the rest of that work at one non-merge
commit in four (decision R4's cap), and the 2026-11-12 plan stops the Crystal
part outright:
it needs a model of the Rust code first, and the proof is then about the model.
Bounded differential gates and default-on translation certificates cover
selected reduction/compiler fragments. They do not certify
the mutually recursive production `infer_type` / `whnf` / `is_def_eq` spine end
to end, and the adopted route does not ask them to: by design the Rust kernel
becomes an untrusted producer whose answers a proved checker re-decides.

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
`just ci`, run once per landing on the tree being landed, and `just gate` are
what hold the line. The tracked pre-push hook is opt-in and is not the landing
gate (`docs/DECISIONS.md` R35, in a development checkout).

```bash
just                 # list workflows
just ci              # the landing gate: fmt-check + lint-coverage + clippy + test-fast
just test-fast       # publish smoke surface (the workspace default-members)
just gate            # local fail-closed soundness + quality gate
just install-hooks   # opt-in: install the tracked pre-push hook repo-wide

# Target a subsystem while developing it.
targo --unverified test --locked -p clean-kernel
targo --unverified test --locked -p clean-elab
```

Run the full suite only when its cost is intended:

```bash
targo --unverified test --locked --workspace --message-format=short -j 1
```

## Documentation

These live in a full development checkout, not in a bootstrap projection:

| Topic | Document |
|---|---|
| Current Lean 4 replacement audit | `docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md` |
| Soundness gate and TCB | `docs/SOUNDNESS_CERTIFICATE.md` |
| Self-verification claim ledger | `docs/SELF_VERIFICATION_CERTIFICATE.md` |
| Self-verification architecture | `docs/SELF_VERIFICATION_PROGRAM.md` |
| Kernel self-proof, route of record | `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md` |
| Kernel self-proof, dated progress review | Major sections and retained evidence |
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
