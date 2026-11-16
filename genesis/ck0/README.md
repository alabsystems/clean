# ck0 genesis and Q6 lineage

`MANIFEST.txt` is the historical seed at Clean `26c712144`. It is stale;
its checksums do not describe today's source or Trust's production dependency
closure. No current genesis, independent double compilation, reproducible binary,
or proved checker is claimed by this directory.

Q6's partial qualification is recorded in
`declared-input endpoint qualification`
and the production/independent-compiler follow-up.
The paired measurement and archive-custody qualification
retains the later fixed observer and exact unverified replay images.
The shared-term source re-capture and lexical Cargo-path controls
supersede its earlier source selector with208 committed inputs, while preserving
every historical packet. Archive custody selects that explicit receipt.
The prior current-source record
and initial record is historical.
`CANDIDATE.json` retains the measured historical source, explicitly **without promoting
it to the genesis seed**. Stock rustc and Trust have shared rustc ancestry. Their
test agreement is differential qualification, not evidence of two independent
compiler implementations or classical diverse double compilation of a compiler.
No `targo --unverified` build makes a proof claim.

The Python 3.11+ bookkeeping tool records complete crate/config inventories,
known external fixtures, literal embedded inputs, compiler and sysroot identities,
resolved dependency source inventories, test names and targets, build commands,
logs and output hashes. Nonliteral or uninventoried embedded inputs are refused.
The source inventory is deliberately bounded to this crate and its known external
inputs; it does not assert that arbitrary future Rust/build-script code has no
other file or environment dependencies. Compiler overrides in the environment
and Cargo configuration are refused; applicable configuration files are pinned.

Current candidate captures use `clean.ck0-candidate-source/v2`: the exact named
Git commit and209 declared inputs include the source-loaded resource transport
helper. Current capture rejects legacy source schemas. Archive custody alone
accepts historical v1 against its fixed original inventory; it cannot turn
that evidence into a new compilation. The candidate follow-through packet
records actual Git, cache and descriptor controls and the unavailable native
frontdoor. Transport controls do not authenticate native resource authority.

Run the source controls (Python 3.11+; this machine uses `python3.14`):

```sh
python3.14 scripts/check_ck0_lineage.py --selftest
python3.14 scripts/check_ck0_replay_custody.py --selftest
```

`just ck0-lineage` also requires a current candidate/cohort and remains red:
the retained `CANDIDATE.json` is v1 and no new v2 native cohort is established.
Do not repin that file or its sealed receipt from an inventory-only capture.
The candidate receiver checks current source against its committed revision
and recorded logs, coverage and receipts. It does not recompile by default.
`--local` additionally checks retained compiler/sysroot/dependency/output files;
those absolute paths are local replay inputs. The latest receipt also retains
exact compressed unverified replay images, without promoting them to seeds.
The strict v2 gate checks before/after-phase endpoint equality; this is not
continuous or hermetic read confinement. Historical v1 has no such claim.
Archive replay custody and refusal of the retired genesis entry points are
untrusted consistency checks, not
compiler independence or seed eligibility. Production provenance is a dated
source snapshot. Check its retained archive without executing the images:

```sh
python3.14 scripts/check_ck0_replay_custody.py \
  --runs reports/self-proof-q6-recapture-2026-11-14/captures \
  --source reports/self-proof-q6-recapture-2026-11-14/captures/source.json
```

Archive consistency does not authenticate production Git provenance. The
follow-through packet separately replays the production APIs over the exact
Trust/Clean/ty Git objects and compares the complete record byte for byte.

Trust's `trust-spec-temporal` links `tla-check` with `clean-cic` and patches
ck0 to its own Clean gitlink. It also replaces num-bigint, num-integer and
num-traits with ty's tla-bignum implementations. Standalone Clean's registry
arithmetic tests do not qualify that production arithmetic closure. Source
provenance is not proof that an installed Trust image contains those bytes.

The production follow-up records a local build and four public bridge controls
for the older pinned production copy under an unpublished lock-repair candidate.
It does not bind that copy to an installed Trust image or qualify every public
entry point. The workspace candidate and production copy have different source
pins; their evidence is not interchangeable.

`--require-q6` exits 1 while complete independent compilation/DDC, installed
production-image binding and genesis promotion remain absent. `verify.sh` and
`generate_manifest.sh` are retired: both refuse before Git, compiler, build or
archive changes, including with historical/help/output flags. The old procedure
could overwrite this archive or report REPRODUCED after only a compiler-version
warning and an unverified suite. Its exact source and controlled counterexamples
remain historical report data.
`MANIFEST.txt` stays byte-identical. No replacement seed-generation procedure is
offered before the missing Q6 obligations can justify one.

Soundness remains per universe bound, no generation establishes more consistency
than its base, and independent quorum re-checks remain required. This bookkeeping
tool is not authority-bearing and does not replace a Lean-defined trusted checker.
