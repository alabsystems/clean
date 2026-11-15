# C4 isolated controls

This non-shipping test package exercises the C4 labelled carrier and core
observer without pulling `clean-kernel`'s unrelated `clean-elab` dev dependency
(which enables all math overlays). It includes the same source as the kernel's
`kcheck_trace` integration target. Its separate lockfile records its own exact
registry resolution; it does not change the workspace lock or qualify a whole
workspace diagnostic. All compilation is unverified and makes no proof claim.

```sh
targo fetch --locked --manifest-path scripts/kcheck_trace_probe/Cargo.toml
CARGO_TARGET_DIR=/private/tmp/clean-c4-m21-target build-slot -- scripts/heavy_gate.sh run 7 c4-trace-controls -- targo --unverified test --locked --manifest-path scripts/kcheck_trace_probe/Cargo.toml
```

The installed Targo rejects `--unverified fetch` (fetch is not a compilation
command). No ordinary or reference entry calls the experimental core. These
controls cover substitution and universe transport of labels, a real delta
unfolding with convertible domains, refusal of a mismatched or absent label,
rollback of speculative tokens, and unchanged ordinary/fenced verdicts and
ordinary reduction counters when local tracing runs in the same process.
They do not cover the whole-Init experiment or advice replay.

The expanded controls also cover inferAnn for eta and proof irrelevance,
local let unfolding, literal-backed iota, direct Eq K, projections and structure
eta, pre-universe syntax transported through substitution, iterative labelled
term destruction, a refused minor label at its full telescope position, a
per-declaration depth header, and persistent syntax for an admitted prefix.
These are source controls, not the corpus measurement.

The literal follow-up preserves canonical Nat/String expansion admission.
The current pin's `String.ofList` construction labels every newly built
application by typed apply; historical list-backed `String.mk` expansion is
a named coverage refusal. No ordinary checker entry or gate is changed.
The optional import control reads the exact pinned Init.Prelude and compares
ASCII, Unicode, empty and embedded-NUL constructions with the existing kernel,
then independently checks every stored domain against the function and argument
types. An unavailable canonical extension must be reported as a refusal.
These controls require execution before any qualification claim.

```sh
CARGO_TARGET_DIR=/private/tmp/c4-literal-owned-target build-slot -- scripts/heavy_gate.sh run 7 c4-pinned-literal-controls -- targo --unverified test --locked --manifest-path scripts/kcheck_trace_probe/Cargo.toml --features pinned-import --test pinned_literal -- --nocapture
```

Use a unique target directory for each worktree. The optional dependency is
non-shipping and does not enable kernel math overlays. Its lockfile adds the
required parser dependencies while retaining the probe's prior registry versions.

The nested-recursion control deliberately reuses universe parameter names
while instantiating a product at different levels. The constructor-level
census derives its expected arguments from the final instantiated major
domain returned by the telescope walk; it does not infer them from names.
