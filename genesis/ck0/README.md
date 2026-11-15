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
supersede its current-source selector with208 committed inputs, while preserving
every historical packet. The standing command selects that explicit receipt.
The prior current-source record
and initial record is historical.
`CANDIDATE.json` pins the measured current source, explicitly **without promoting
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

Run the evidence consistency gate (Python 3.11+; this machine uses `python3.14`):

```sh
just ck0-lineage
python3.14 scripts/check_ck0_lineage.py --selftest
```

It checks the current source against the candidate's committed revision and
checks recorded logs, coverage and receipts. It does not recompile by default.
`--local` additionally checks retained compiler/sysroot/dependency/output files;
those absolute paths are local replay inputs. The latest receipt also retains
exact compressed unverified replay images, without promoting them to seeds.
The strict v2 gate checks before/after-phase endpoint equality; this is not
continuous or hermetic read confinement. Historical v1 has no such claim.
The standing command also checks archive replay custody and refusal of the
retired genesis entry points. These are untrusted consistency checks, not
compiler independence or seed eligibility. Production provenance is a dated
source snapshot. To authenticate it again,
provide Git repositories containing its pinned objects:

```sh
python3.14 scripts/check_ck0_lineage.py \
  --require-stability --runs reports/self-proof-q6-recapture-2026-11-14/captures \
  --production reports/self-proof-q6-recapture-2026-11-14/captures/production.json \
  --authenticate-production --trust-repo /path/to/trust.git \
  --ty-repo /path/to/ty.git
```

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
