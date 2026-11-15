# Security Policy

## Reporting a Vulnerability

Do not open a public issue with exploit details. Use GitHub Security Advisories
or private vulnerability reporting for the canonical repository:

[https://github.com/alabsystems/Clean/security/advisories/new](https://github.com/alabsystems/Clean/security/advisories/new)

If that form is unavailable to you, open a minimal public issue that requests a
private security contact without including exploit details.

## Supported Versions

Security support is best-effort for `main` and the latest tagged core Clean
release. There is no response-time SLA.

Core Clean releases use `vX.Y.Z` tags. Mathverse Library releases use
`mathverse-vX.Y.Z` tags and may publish shard archives. These are separate release
streams: a newer Mathverse Library tag does not imply a newer supported core Clean
tag, and a newer core Clean tag does not imply fresh Mathverse shard artifacts.

## Scope

Security reports should include the affected command, crate, input file, and
the smallest reproduction that demonstrates the issue.

In scope:

- kernel/type-checker soundness vulnerabilities
- CLI, server, and release artifact handling
- Mathverse download and verification tooling
- credential leaks or unsafe handling of local secrets

Proof-trust or soundness concerns that are not exploitable security
vulnerabilities should use normal GitHub Issues and reference the exact
theorem, checker, or CLI path involved. Report them privately first when public
users could be misled by current documentation or release artifacts.

## Independent checking: `lake check --paranoid` and the Kernel Arena

Lean v4.35.0's `lake check --paranoid` hands one lean4export NDJSON export of
the checked code to its built-in kernel replay and to every checker the
toolchain bundles (`bundledKernels` in Lake's `Check.lean` at v4.35.0), and fails if any of them rejects it:

| Bundled checker | What its proof covers |
|---|---|
| `leanchecker-paranoid` (the official C++ kernel) | no machine-checked proof |
| `lean4lean` (the kernel in Lean, derived from the C++ one) | metatheory in progress; no end-to-end soundness proof |
| `nanoda` (an independent Rust kernel) | no machine-checked proof |
| `con-leche` (a Lean checker) | a machine-checked consistency proof: what it accepts has a model in ZFC with inaccessibles, so no theorem of `False` is accepted |
| `con-ron` (con-leche ported to Rust) | refines con-leche through Aeneas, so con-leche's statement carries over modulo Aeneas and its unverified driver |

(Descriptions as the Kernel Arena's Round 2026-09 states them, Zenodo record
22944094.) Clean is not one of them. Clean reads the same export through
`clean olean replay --from-export <file>` (exit 0 accepts, 1 rejects, 2
declines), which re-checks it with Clean's own kernel (`clean-kernel`) as its
only checker. Trusted beside that kernel (T1 in
`docs/SOUNDNESS_CERTIFICATE.md`) are the
NDJSON reader that builds the kernel's terms, the `.olean` loader's structural
tier and the replay discipline (`replay_order.rs`, `verify_batch_replay.rs`,
`replay_families.rs` under `crates/clean-olean/src/`): the certificate's
section on independent kernels lists them. The stock-built re-checker
`clean-ck0` and the in-Clean checker `kcheck` are not wired to it yet, and
nothing about it is machine-checked. A soundness report against it is in scope
above. Its standing evidence is the arena battery,
`crates/clean-olean/tests/kernel_arena_battery.rs`, over the vendored Round
2026-09 tests, and that evidence is about those tests only: an adversarial
review (2026-10-22) found a forged inductive `all` field, which no arena test
has, that let `bad : False` exit 0 (now refused by the reader, R124 in
`docs/DECISIONS.md`), and its re-review the same day found
more that no arena test reaches (a forged `Nat.add` or `Lean.reduceNat`, levels
read as `zero` or rewritten through an `imax`), each now declined (R125,
R128). Its first run (2026-10-17) found one wrong accept,
`bad/bugs/proj-of-subst-prop` (the lean4#14807 class), which the
`is_prop`-requires-a-sort guard closed (R85 in
`docs/DECISIONS.md`). The committed round artifact,
`reports/kernel-arena-battery/round-2026-09-2026-10-23.json`,
records no wrong accept, and names each good test Clean refuses (a pinned
fidelity gap with its owner in the battery's declines table), each decline,
each timeout and each memory cap.
