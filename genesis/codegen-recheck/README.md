# Unified codegen-recheck seed

The **durable, reproducible artifact that ties the genesis seed to the compiler
re-check** — the goal's headline made a single reproducible path:

> *From a durable, checksum-pinned seed → the kernel independently re-checks a
> **real trust-cg compiler lowering** to `trust_count == 0`, non-vacuously.*

This closes the "all reproducible from a durable, checksum-pinned genesis seed"
clause for criterion 2 (compiler out of the TCB): not just that the mechanism
exists, but that it reproduces from a pinned seed.

## Files

| File | Purpose |
|---|---|
| `MANIFEST.txt` | The seed. sha256 over the load-bearing codegen-recheck source (the kernel's width-N bitvector gate-fidelity, the non-reflexive lowering bridge, the criterion-2 re-check test) + the pinned `clean`/`trust-cg` commits + `Cargo.lock` (which pins the trust-cg GVN-pass dev-dep). |
| `reproduce.sh` | Verifies the checksums, then builds + runs the kernel re-checking the **real `trust_cg_opt::gvn`** lowering identity to `trust_count == 0`. Exit 0 == reproduced. |
| `generate_manifest.sh` | Regenerate `MANIFEST.txt` after a change. |

## Reproduce

```bash
genesis/codegen-recheck/reproduce.sh
```

This checks the pinned source matches byte-for-byte, then runs the genuine
non-vacuous re-check: it *runs* the real `trust_cg_opt::gvn` commutative-
canonicalization pass, extracts its identity `bvAdd a b == bvAdd b a`
(structurally distinct sides — **not** reflexivity), bit-blasts both sides,
SAT-refutes the disequality, reflects it into a kernel `bvEq` term, and the
kernel re-checks that term to `trust_count == 0`. A **tampered** lowering
(non-commutative-op swap) makes the disequality satisfiable → no refutation →
the proof **fails** — so the obligation genuinely constrains the lowering.

## Honest scope (the named floor)

- **What this proves:** for the re-checked lowerings, **rustc/LLVM are not
  trusted** — the kernel re-checked each lowering's correctness from first
  principles (bit-blast + SAT refutation + kernel `check_type`), foundational
  axioms only, no `_unchecked`.
- **The codegen re-check uses `clean-kernel`'s bitvector gate-fidelity layer**,
  not the minimal `ck0` (which already re-checks math/software/AI — see
  `genesis/ck0/`). Porting the codegen re-check onto `ck0` is the remaining
  *minimal-kernel* unification.
- **FOUR real `trust_cg_opt::gvn` commutative-canonicalization lowering KINDS**,
  each with the end-to-end kernel re-check (`trust_count == 0`, non-vacuous,
  tamper-FAILS + a forge leg that reduces `checkRefutes -> Bool.false`):
  - **ADD** commutativity (`bvAdd a b == bvAdd b a`) — ripple-carry
    (`xor3`/`maj`) gate-fidelity — demonstrated through **width 16** (a real
    machine width; `CRITERION2_WIDTH=N` opt-in). The earlier width-≥6 ceiling was
    a kernel HEARTBEAT BAIL (fail-closed: it rejected a valid refutation, never
    accepted an invalid one), now lifted by an unlimited-heartbeat reflection
    path — no `checkRefutes_sound` reproof needed.
  - **XOR / AND / OR** commutativity (`bvXor/bvAnd/bvOr a b == … b a`) — three
    genuinely DIFFERENT kernel gate-fidelities (per-bit `Bool.xor`/`Bool.and`/
    `Bool.or`, **no carry chain**), so the kernel re-checks different gate-tree
    shapes end-to-end. Non-vacuity is on each op's own data: a corrupted
    refutation reduces `checkRefutes -> Bool.false`.
  - Width 32 is re-checked END-TO-END in an OPTIMIZED build: `CRITERION2_WIDTH=32`
    `cargo test … --release …criterion2_gvn_commute_lowering_certified_at_wider_width`
    completes POSITIVE, `trust_count == 0`, TAMPER-FAILS in ~124 s / ~9 GB (7158
    refutation steps, 1138 gate clauses over `Clean.BV32`). Width 64 is the next
    scale-out. (Debug builds OOM the assembled-cert reduction at width≥32 — they hold
    several-fold larger per-term memory — so the wide-width test self-skips in debug
    with a `--release` pointer; this is a build-profile limit, not a soundness one.)
- **The resolution refutation is discharged through the PROVEN sub-quadratic checker**
  `Clean.Res.checkRefutes3` + its kernel-checked `checkRefutes3_sound`
  (`axiom_deps = []` ⊆ foundational), not the O(steps²) `checkRefutes`; clause literals
  are BigNat (native `Nat.beq`/`div`/`mod`), and the per-step premise lookups are a
  BigNat-id trie descent. Honest performance note: the dominant remaining cost is NOT
  the checker's asymptotics but whnf-cache THRASHING — the `go3`-threaded trie
  accumulator grows per step, and below the kernel's 100k cache default its hot subterms
  are evicted and re-reduced (profiled: per-step whnf-misses jump 3.7× from width 16→32
  while trie depth grows ~1.2×). Sizing the memoization budget to the step count
  (`bv_blast_reflection::reflection_cache_budget`, release-only, pure performance — the
  reduction result is identical) removes the thrash: the isolated width-32 reduction
  drops 85 s → 30 s (2.8×). The heavy final-assembly + allSat-fidelity checks are left
  at the default budget (a bumped cache there retains ~118 GB, since they re-reduce the
  whole cert in one `check_type`); sharing the cache across the certify + assembly
  checks is the next perf step.
- The irreducible floor (the ISA model, the statement, rustc-built kernel
  binary) is named in `genesis/ck0/TRUST_FLOOR.md`, never pretended to be zero.

This seed is regenerated and re-published as the re-check scales.
