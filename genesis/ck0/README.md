# ck0 Genesis Seed

The **durable, checksum-pinned genesis seed** of `clean-ck0` — the minimal,
auditable kernel that is the single root of trust for the clean/Trust ecosystem.
This directory makes the trust root **crash-proof and reproducible**: the seed is
published to GitHub release binary assets, so it survives loss of any one machine,
and anyone can reproduce the kernel from a fixed, checksum-pinned source.

## Files

| File | Purpose |
|---|---|
| `MANIFEST.txt` | The seed. sha256 over every build-input file (46) + the pinned toolchain, build command, commit, and host triple. |
| `verify.sh` | Reproducibility gate: recompute every checksum, then rebuild + run the kernel suite with the pinned command. Exit 0 == reproduced. |
| `generate_manifest.sh` | Regenerate `MANIFEST.txt` from the current source tree (run at each kernel milestone). |
| `TRUST_FLOOR.md` | The honestly-named irreducible trust floor — what you must trust to believe a ck0 verdict. Read this first. |

## Verify a seed

```bash
# from the repo (or an extracted seed tarball) root:
genesis/ck0/verify.sh
```

This checks that the source matches the manifest byte-for-byte, then rebuilds
`clean-ck0` and runs its validation suite (181 tests, incl. ~70 adversarial
soundness forgeries). It warns — never fails — if your `rustc` differs from the
pinned one; the *source* is pinned regardless, only a bit-identical *binary*
needs the exact toolchain.

## Regenerate after a kernel change

```bash
genesis/ck0/generate_manifest.sh      # rewrites MANIFEST.txt from HEAD
git add genesis/ck0/MANIFEST.txt && git commit
```

## Honest status

This is a genesis seed of the trust root **as it stands** (kernel scope M0–M3).
The reproducibility level is **source-pinned + test-reproducible**; a
bit-identical binary rebuild is a stretch goal (needs the exact pinned `rustc`
with deterministic flags). The irreducible floor (rustc/LLVM, std/OS,
num-bigint, and spec-faithfulness) is named in `TRUST_FLOOR.md`, never pretended
to be zero. The seed is regenerated and re-published at each kernel milestone
toward the durable, self-hosted production genesis (M7).
