# Mathbot Charter

> One page. Forcing function for design decisions. If a feature doesn't
> serve one of the five scored-run invariants below, it doesn't belong in
> mathbot — it probably belongs in `clean-cli`, `clean-auto`, or
> somewhere else (or nowhere).

## Why mathbot exists

To rigorously evaluate proof-search ability of frontier LLMs against
Lean 4 theorems, with strong guarantees against the most common ways
proof-search evaluations get faked: answer leakage, tactic-selection-
masquerading-as-synthesis, single-model selection bias, and
unreproducible runs.

Mathbot is **not a generic AI coding agent.** Codex, Aider, and Claude
Code already exist; mathbot has no reason to compete with them. If
mathbot starts looking like a Lean-flavored codex, the design is
drifting and somebody should call it out.

## The five scored-run invariants

(Per codex r7 §1.2: these are evaluation-harness controls, renamed
from "differentiators" to be honest. They distinguish mathbot's
*scoring discipline* from a generic coding agent, even though each
control individually is generic benchmark infrastructure. Every one
of them must be machine-checkable and present in the replay
archive of any L3 headline run; missing one invalidates the run.)

If a proposed feature doesn't serve at least one of these, it doesn't
belong in mathbot.

1. **Sealed per-task sandbox.** Workers run inside a sealed workdir
   with physical absence of forbidden paths (unsorried sources,
   provider caches, HX private proofs, parent-root `.git`), an empty
   sealed HOME, an explicit env allowlist, and a macOS `sandbox-exec`
   profile restricting network to specific provider hosts. Codex has
   no Lean-aware analog of this.

   **Honest acknowledgment (gemini r1 §2):** the sandbox eliminates
   local-filesystem leakage; it does NOT eliminate the provider API
   channel (api.anthropic.com / api.openai.com / generativelanguage.
   googleapis.com) because the engines themselves are API-hosted. A
   worker can leak HX-Test material to the provider's server. We
   mitigate by: (a) **statement anonymization** — human-meaningful
   identifiers in target Lean sources are rewritten to opaque hashes
   before reaching the worker, so RAG/cache string-matches on names
   like `WeightedTreeNet` don't fire; (b) **vendor independence** —
   L3 multi-engine requires ≥2 INDEPENDENT vendor engines (codex
   from OpenAI, claude from Anthropic, gemini from Google);
   intra-vendor agreement is NOT independent evidence; (c)
   **time-windowing** — a minimum 30-day gap between brutal-review
   target certification and the scored run; if a model's version
   bumped major in between, re-run review. This channel cannot be
   eliminated. Any "models proved theorems" claim must explicitly
   discuss the residual leakage risk.

2. **Held-out private theorem set with rotation.** HX-Test is the
   scored evaluation set: hand-built targets across multiple
   mini-domains, requiring composition of ≥3 lemmas that are not
   summarized by a single canonical Mathlib name, with novelty
   argument per `PROVENANCE.md`. Lives at `~/mathbot-hx-private/`
   (off-tree), rotated quarterly. Public probes (HX-Seed) are for
   go/no-go early-signal only and never scored.

3. **Lean kernel as ground truth.** Verifier verdicts come from
   `lake env lean` (or, post-integration, the in-process Clean kernel),
   not LLM consensus, not human review, not test passes. Patch
   accepted ⟺ Lean kernel says the file type-checks with all required
   theorems closed and no `sorry`/`admit`/unsafe declarations.

4. **Multi-engine independent bakeoff** (codex r8 §5.2 rename: the
   prior "cross-feedback" framing put a leakage channel in the
   invariant). For L3 headlines, every run pits ≥2 engines (codex,
   claude, gemini) on the same task as INDEPENDENT attempts — no
   engine consumes another engine's output as prompt material.
   Cross-feedback patterns (driver/coach, engine-vs-engine
   consultation) score in a separate "co-constructed" track and
   never appear in headlines. Driver-vs-worker separation tracked.
   The L3 multi-engine success requirement (≥2 engines each
   verify ≥1 target; no engine >60% of accepted) lives in
   bakeoff-conclusive-criteria.md §L3.

5. **Brutal multi-model design review of every probe.** Before any
   probe lands in HX-Seed or HX-Test, three frontier models review
   it (codex, claude, gemini) with explicit prompts to find the
   shortest path past the bar. Reviews are committed alongside the
   probe in `PROVENANCE.md`. A probe that all three call "would close
   to mathverse + induction" gets retired or hardened (see HX-Probe-0 →
   HX-Probe-2 evolution as the working example).

   **Conflict-of-interest mitigations (gemini r1 §3):** the three
   reviewing engines are also the three scored engines. Shared
   blind spots can certify a probe as "L3-grade" when it's actually
   inside the models' near-future recall. Mitigations:
   - **Strict-superset reviewer pool**: brutal review includes at
     least one model NOT in the scored set (e.g. an open-source
     local model like a fine-tuned Llama or DeepSeek-Prover whose
     blind spots are likely uncorrelated with the closed frontier).
   - **Adversarial tactic baselines** are the LOAD-BEARING gate,
     not the LLM review. HX-Test v2 §6 mandates seven exact `lake
     env lean` commands (simp-only, simp+omega, simp+nlinarith,
     polyrith, induction+simp+omega, decide, aesop); ALL seven
     must FAIL before a probe enters `private-active`. If a model
     review certifies a probe hard but a tactic baseline closes it,
     the baseline wins and the probe is `retired-broken`.
   - **Time-delayed bakeoff**: minimum 30 days between brutal-review
     completion and scored run. Record model versions at both
     timestamps.
   - **Continuous baseline tracking**: every 30 days, re-run the
     baseline tactic probes against current models on every
     `private-active` target. If a baseline that previously failed
     now passes, auto-transition to `retired-broken` with
     lessons-learned commit.

## B1 Lean REPL: honest framing (gemini r2 §4)

The B1 Lean REPL bridge has **two backends**: a true persistent-stateful
backend (charter §B1.1, the canonical path) and a stateless-mimic
fallback (the legacy path, kept as a last-resort for unprovisioned
installs).

### B1.1 persistent-stateful (default when available)

The persistent backend lives in `crates/mathbot/src/lean_repl_server.rs`.
It drives `leanprover-community/repl` (the `lake exe repl` binary) via
its JSON-line protocol — one Lean kernel process per session, with an
`env` cursor (post-command environment) and a `proofState` cursor
(mid-proof tactic state) carried across turns. Measured per-step
latency on a 5-tactic proof against the bare prelude is **sub-millisecond
after the ~60ms `begin_proof` warm-up**, which is the load-bearing
contrast with the stateless-mimic's >100ms per-turn floor and proof-
depth-proportional growth.

Provisioning: run `scripts/provision-lean-repl.sh` to clone +
`lake build` the upstream repo (matched to the workspace's
`lean-toolchain` pin); the script prints the path to the produced
`repl` binary on stdout. Set `MATHBOT_LEAN_REPL_BIN=<path>` so the
dispatch layer picks the persistent backend.

### B1 stateless-mimic (fallback)

When `MATHBOT_LEAN_REPL_BIN` is unset and `lake exe repl` is not
available in the project, the dispatch layer in
`crates/mathbot/src/lean_repl.rs` falls back honestly to the stateless
backend in `crates/mathbot/src/lean_repl_stateless.rs`. This backend
re-elaborates the accumulated file on every tactic call — proof-state
continuity is simulated, not real. Sub-second response times do NOT
scale beyond bare-prelude fixtures, and the kernel cannot carry
forward proof-search caches between turns.

Any L3 claim citing "stateful Lean REPL" must explicitly disclose
which backend was used. If the run used the stateless fallback:
acknowledge that every turn re-pays the elaboration cost. If the run
used the persistent backend: state which `leanprover-community/repl`
git rev was provisioned, and note the residual limitations below.

### Residual limitations (persistent backend)

- **Pickling not exposed**: sessions cannot be resumed across process
  boundaries. A crashed worker loses its proof history.
- **Bootstrap-only imports**: the import list is sent once at start
  time; mid-session `import` is rejected by the upstream repl.
- **Mathlib provisioning is the caller's problem**: spawning the repl
  inside a lake project with Mathlib requires Mathlib's `.olean` cache
  to be present. Cold Mathlib build remains expensive.
- **`lean --server`/LSP not yet wired**: this is a thinner alternative
  (no extra Lean package needed) but a substantially larger Rust
  integration. Still on the B1.x follow-up list but unstarted.

## What mathbot measures today, honestly

Three tracks, only the first is real today:

1. **PatchHygiene.** Model edits a working file without breaking it.
   Patch is valid; `lake build` still passes. Wired today via
   `bakeoff early-signal` (Phase 0). Real but easy.

2. **LemmaRetrieval.** Proof body sorried; model retrieves the right
   lemma calls. Not yet wired.

3. **ProofSynthesis.** Held-out theorems, sealed sandbox, stateful
   Lean REPL, composition of ≥3 lemmas across files. Not yet built.

A claim of the form "model X proved Lean theorem Y it had not seen"
requires all five scored-run invariants in force AND the ProofSynthesis
track wired AND the result replayable from the archive. Anything less
is PatchHygiene or LemmaRetrieval at best, and the README must label
it that way.

## Path from PatchHygiene to ProofSynthesis ("finish the swing")

Five blocks. Roughly 4-5 weeks of focused work.

- **B1. Stateful Lean REPL bridge** (1 week). `mathbot lean-repl`:
  start a session, apply a tactic, return goal state. Round-5
  reviewers (codex/claude/gemini) all named this as the single
  largest mechanical gap. Without it, models prove theorems by
  reading compiler vomit, not by working a proof.

- **B2. HX-Test design + private repo** (2-3 weeks, parallelizable
  with B1). ≥5 hand-built targets, ≥2 mini-domains, ≥3-lemma
  composition, mathematician-self-review under the brutal-review-by-
  three-models discipline, `~/mathbot-hx-private/` (off-tree, already
  gitignored), quarterly rotation, human-baseline timed.

- **B3. Finish `bakeoff_converse` and wire it** (2-3 days). Generalize
  the multi-turn worker from the Phase-0-specific `bakeoff
  early-signal` to a `bakeoff converse` CLI command. Demo on
  calibration targets `Mathbot/Calibration.lean` (c1/c2/c3).

- **B4. Failure taxonomy in CLI output** (2-3 days). `src/bakeoff_
  taxonomy.rs` already classifies 15+ failure kinds. `bakeoff
  early-signal` doesn't print a histogram. Wire it so every run
  emits a single JSON blob: `{verified: N, taxonomy: {...},
  leakage_audit: {...}, runtime: ...}`.

- **B5. Replay archive** (~1 week). Each run emits `runs/<timestamp>-
  <gitsha>-<probe>/`: full prompt, full response, lake build output,
  sandbox audit log, verifier verdict, tarball, sha256sum. Without
  this, "the bakeoff was inconclusive" is a vibe, not a measurement.

## Conclusive-result criterion (commit before re-running)

Before any bakeoff run against HX-Test:

- Commit `docs/mathbot/bakeoff-conclusive-criteria.md` stating exactly
  what counts as conclusive (e.g. "≥3 of N models verify ≥X% of
  HX-Test under failure-taxonomy class `compose_3_lemmas` or harder,
  with replay archives intact, leakage audit shows zero forbidden-
  path reads").
- A run that meets the criterion → write up.
- A run that doesn't → emit the taxonomy histogram, name the
  dominant failure mode, design the next probe, repeat.

The discipline is **fail forward through better probes**, not pass
at all costs.

## Anti-charter (things that mean drift)

If mathbot starts doing any of these, it has drifted into a bad
codex clone and somebody should revert:

- General-purpose code-editing agent that works on non-Lean targets.
- "Smart" verifier that does anything other than report `lake env
  lean` exit code + diagnostics.
- Authority/evidence/binding/provenance scaffolding around what is
  fundamentally a kernel verdict. (We tried that; it added zero
  trust beyond what the kernel already provides. See the
  authority/evidence audit conclusion from 2026-05-25.)
- Probes that fall to `mathverse` after one `simp`, or that are recall-
  three-Mathlib-lemma-names tests. (See HX-Probe-0 round-5 review.)
- Scoring on public targets without a held-out HX-Test counterpart.
- Single-engine results presented as the headline.
- **Cross-feedback in L3 headline runs** (codex r7 §1.3): an engine
  consuming another engine's output as prompt material is a leakage
  channel dressed as collaboration. Single-engine independent
  attempts only for headline claims. Co-constructed and driver/coach
  patterns score in a separate track and never appear in headlines.

## Provenance scope (codex r7 §1.1)

"Provenance" is allowed narrowly. It means exactly:

1. **Target review notes** — `PROVENANCE.md` per HX-Seed and HX-Test
   target with designer + mini-domain + canonical proof shape +
   novelty argument + brutal-review-by-3-models verdicts.
2. **Replay archive manifest** — per B5: tarball + sha256 + manifest
   schema `mathbot.replay.v1`.
3. **Sandbox audit log** — the exec log produced by sandbox-exec,
   recording syscalls denied + allowed-host network attempts.

It does NOT mean:

- Verifier-authority layers, gate ledgers, attempt receipts, or
  trust ledgers that mediate between the kernel verdict and the
  scorer. The kernel's exit code IS the verdict. Anything else
  attempting to override or "validate" the verdict is the
  ceremony anti-pattern returning under a different name.
- Scoring receipts not directly backed by a kernel replay (re-run
  `lake env lean` on the patched file and compare exit codes).
- Multi-layer hash chains that sign their own digests.

A future session proposing "X-authority evidence" or "X gate
binding" or "X provenance chain" should re-read this section and
the 2026-05-25 audit conclusion before writing code.

## Coordination

There is one AI (Claude) and one author (Andrew). Past sessions are
past Claude; future sessions are future Claude. Mathbot's `bakeoff
review` commands and `PROVENANCE.md` files are how a session writes
context for itself across the wall.
