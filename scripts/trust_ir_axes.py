#!/usr/bin/env python3
"""The axis extractor and ratchet comparator for `scripts/trust_ir_build.sh`.

WHY THIS FILE EXISTS
====================
The trust-ir coverage artifact (`<crate>.coverage.json`, schema
`trust.thir-lower.crate-module.coverage.v2`) carries ~30 distinct per-body and
per-crate axes. Until 2026-08-15 the committed ratchet watched exactly four of
them -- `lowered`, `spliced`, `flip_events`, `mismatch` -- and that gap has now
bitten three times:

  1. `lowered` / `spliced` were once not columns in the review harness, which
     hid three stub collapses.
  2. `markers_class` was not an axis, which hid a fourth.
  3. trust `80c7e86f55` (2026-08-13) turned 38 `agreed` verdicts into `not-run`
     -- 36 interpreter + 2 seam -- and dropped the CTFE flip lane from 32/32
     semantically backed to 11/32. It went unnoticed for two days. NONE of the
     four watched axes moved: `lowered` 9067, `spliced` 7571, `derived_mir`
     agreed 1542, mismatch 0, flip events 209 were BIT-IDENTICAL across the
     regression. See `reports/crystal-38-lost-agreed-bisect-2026-08-15.md`.

So the ratchet's blind spot was not an oversight in one axis: it was that
nobody had ever written the axis list down. This file writes it down. Every
axis the artifact carries appears in `AXES` below with an explicit direction --
including the ones deliberately NOT gated, each with the measured reason.

DIRECTIONS
----------
  grow    the value may only increase   (evidence axes)
  shrink  the value may only decrease   (alarm axes)
  pin     the value may not change      (identity / capability markers)
  record  measured and printed, never gated -- with a stated reason

A gated axis missing from the baseline is RED ("unbaselined"), never a silent
pass. That is the whole point: an unwatched axis is the defect.

USAGE
-----
  trust_ir_axes.py measure  --coverage COV.json --log BUILD.log [--out M.json]
  trust_ir_axes.py check      --measured M.json --baseline B.json --compiler C.json [--bodies S.json]
  trust_ir_axes.py tighten    --measured M.json --baseline B.json --compiler C.json [--bodies S.json]
  trust_ir_axes.py rebaseline --measured M.json --baseline B.json --compiler C.json [--bodies S.json]
  trust_ir_axes.py compiler-check --baseline B.json --compiler C.json
  trust_ir_axes.py table                     # print the axis inventory
  trust_ir_axes.py selftest                  # comparator unit tests, no build

The MARKER axes below are computed by `scripts/trust_ir_markers.py`, which reads
`markers_detail` per row and reports what the marker comparison actually
compared. Run `trust_ir_markers.py ledger --coverage COV.json` for the per-row
form and `trust_ir_markers.py residual` for what the gate costs in flips.

`check` exits 0 when every gated axis holds, 1 otherwise. It evaluates EVERY
axis and reports them all before failing, so a red on one axis can never mask
another.

THE COMPILER PIN (2026-10-08). Every count here is a property of the compiler
that measured it as much as of clean-kernel: the baseline recorded `lowered`
9068 over clean-kernel 71e1ce8be under an August trustc (stamp 94147b34f), and
the same source measures 7329 under the sealed 321aaeda7. Until this date the baseline mixed the two -- `--tighten`
raised the axes the newer compiler improved and kept the older compiler's
values for the ones it lowered -- so the gate was RED on a comparison between
two compilers, which says nothing about clean (`reports/trust-ir-ratchet-
verdict-2026-08-13.md` was the same class). The baseline now pins ONE compiler
(`compiler`: the sha256 of `trustc` and of the `librustc_driver` it loads) and
every axis is from one run under it:

  * `check` and `tighten` refuse a run under any other compiler (COMPILER
    MISMATCH), so a count is only ever compared with a count the same compiler
    produced, and an axis regressing under the pinned compiler stays RED.
  * `rebaseline` replaces EVERY gated axis from one run, and only under a
    compiler that is NOT the pinned one. Under the pinned compiler it refuses:
    there an axis moves only by `tighten`, which never loosens. It also refuses a
    run with a fatal invariant, a missing gated axis, or a pin axis in
    `REBASELINE_FIXED` (the subject crate, and no proof authority / native
    verification request from the producer) at any other value.
"""

from __future__ import annotations

import argparse
import collections
import datetime
import json
import math
import os
import pathlib
import re
import sys
import tempfile

# The marker-line ledger lives beside this file. Resolve it by the script's own
# directory rather than the caller's cwd: `trust_ir_build.sh` and `local_gate.sh`
# both invoke this from the repo root, and a future caller will not.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import trust_ir_markers  # noqa: E402  (path fixed up immediately above)

SCHEMA_MEASURED = "clean.trust_ir_build.measured.v1"
SCHEMA_BODIES = "clean.trust_ir_build.agreed_bodies.v1"
SCHEMA_BASELINE = "clean.trust_ir_build.baseline.v1"
SCHEMA_COVERAGE = "trust.thir-lower.crate-module.coverage.v2"


def _strict_json(path):
    """Read one unambiguous JSON value, including otherwise-unused metadata."""
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise Refused(f"duplicate JSON key {key!r}")
            result[key] = value
        return result

    def constant(value):
        raise Refused(f"non-finite JSON constant {value}")

    def finite_float(value):
        number = float(value)
        if not math.isfinite(number):
            raise Refused(f"non-finite JSON number {value}")
        return number

    with open(path, encoding="utf-8") as handle:
        return json.load(handle, object_pairs_hook=pairs, parse_constant=constant,
                         parse_float=finite_float)


def _counter(value, label):
    if type(value) is not int or value < 0:
        raise Refused(f"{label} must be a nonnegative integer, got {value!r}")
    return value


def _validate_axes(values, label, require_gated=False):
    if not isinstance(values, dict):
        raise Refused(f"{label} axes must be an object")
    if require_gated:
        missing = sorted(GATED - values.keys())
        if missing:
            raise Refused(f"{label} lacks gated axes: {', '.join(missing)}")
    for key, _direction, _source, _why in AXES:
        if key not in values:
            continue
        value = values[key]
        if key in ("proof_authority", "native_verification_requests"):
            if type(value) is not bool:
                raise Refused(f"{label}.{key} must be a boolean")
        elif key in ("schema", "crate", "direct_obligation_capability"):
            if not isinstance(value, str) or not value:
                raise Refused(f"{label}.{key} must be a nonempty string")
            if key == "schema" and value != SCHEMA_COVERAGE:
                raise Refused(f"unsupported coverage schema {value!r}")
        else:
            _counter(value, f"{label}.{key}")


def _validate_invariants(measured, fatal=False):
    invariants = measured.get("invariants")
    if not isinstance(invariants, dict):
        raise Refused("measurement invariants must be an object")
    for key, _why in FATAL_INVARIANTS:
        _counter(invariants.get(key), f"invariants.{key}")
    if fatal and any(invariants[key] for key, _why in FATAL_INVARIANTS):
        raise Refused("measurement has a nonzero fatal invariant")


def _validate_sets(sets, label):
    if not isinstance(sets, dict):
        raise Refused(f"{label} must be an object")
    for channel in ("interpreter_agreed", "seam_agreed", "flip_backed"):
        names = sets.get(channel)
        if not isinstance(names, list) or any(
            not isinstance(name, str) or not name for name in names
        ):
            raise Refused(f"{label}.{channel} must be a list of nonempty names")


def _validate_measurement(measured, need_sets=False):
    if not isinstance(measured, dict) or measured.get("schema_self") != SCHEMA_MEASURED:
        raise Refused("unsupported or missing measurement wrapper schema")
    _validate_axes(measured.get("measured"), "measurement", require_gated=True)
    missing = sorted(AXIS_BY_KEY.keys() - measured["measured"].keys())
    if missing:
        raise Refused("measurement lacks schema fields: " + ", ".join(missing))
    _validate_invariants(measured)
    if need_sets or "sets" in measured:
        _validate_sets(measured.get("sets"), "measurement sets")


def _write_artifacts(artifacts):
    """Stage every output before replacing any, and roll back a failed install.

    This handles ordinary process errors, not a machine crash between renames.
    """
    normalized = {pathlib.Path(path).resolve(): text for path, text in artifacts.items()}
    if len(normalized) != len(artifacts):
        raise Refused("output paths refer to the same file")
    staged, backups, attempted, retained = {}, {}, [], set()
    committed = False

    def stage(path, content, mode):
        # Short private names work even when the destination uses NAME_MAX.
        directory = pathlib.Path(tempfile.mkdtemp(prefix=".trust-ir-stage-", dir=path.parent))
        temporary = directory / "payload"
        try:
            os.chmod(directory, 0o700 | (directory.stat().st_mode & 0o2000))
            flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_BINARY", 0)
            fd = os.open(temporary, flags, 0o666)
            with os.fdopen(fd, "wb") as handle:
                handle.write(content)
                handle.flush()
                os.fsync(handle.fileno())
            # Existing modes are preserved. New files retain the mode the OS
            # selected from 0666 and the process umask, as open(..., "w") did.
            if mode is not None:
                os.chmod(temporary, mode)
            return temporary
        except BaseException:
            temporary.unlink(missing_ok=True)
            directory.rmdir()
            raise

    try:
        for path, text in normalized.items():
            if path.exists():
                # Rename permission in the parent must not bypass a file's
                # original write refusal. This probe never truncates it.
                fd = os.open(path, os.O_WRONLY | getattr(os, "O_BINARY", 0))
                os.close(fd)
                previous = path.read_bytes()
            else:
                previous = None
            mode = path.stat().st_mode & 0o777 if previous is not None else None
            backups[path] = stage(path, previous, mode) if previous is not None else None
            staged[path] = stage(path, text.encode("utf-8"), mode)
        retained.update(backup for backup in backups.values() if backup is not None)
        for path, temporary in staged.items():
            # A signal can arrive after rename succeeds but before it returns.
            attempted.append(path)
            os.replace(temporary, path)
        committed = True
    except BaseException as error:
        if committed:
            raise
        rollback_errors = []
        for path, backup in backups.items():
            if path not in attempted:
                retained.discard(backup)
        for path in reversed(attempted):
            backup = backups[path]
            try:
                if backup is None:
                    path.unlink(missing_ok=True)
                else:
                    os.replace(backup, path)
                    retained.discard(backup)
            except OSError as exc:
                rollback_errors.append(f"{path}: {exc}; preimage {backup}")
        if rollback_errors:
            raise Refused("artifact rollback failed: " + "; ".join(rollback_errors)) from error
        raise
    finally:
        if committed:
            retained.clear()
        for temporary in [*staged.values(), *backups.values()]:
            if temporary is not None and temporary not in retained:
                temporary.unlink(missing_ok=True)
                temporary.parent.rmdir()

# ---------------------------------------------------------------------------
# THE AXIS INVENTORY.
#
# (key, direction, source, why)
#
# `source` is where the number comes from, so a reader can check it by hand:
#   totals   -- coverage.json `totals.*`
#   header   -- coverage.json top-level identity / capability fields
#   bodies   -- an aggregate over coverage.json `bodies[]`
#   log      -- the trustc flip log (`RUSTC_LOG=...trust_ir_flip=info`)
#   join     -- flip log joined to `bodies[]` by `def_index`
# ---------------------------------------------------------------------------
AXES: list[tuple[str, str, str, str]] = [
    # -- identity and capability -------------------------------------------
    ("schema", "pin", "header",
     "a schema bump changes what every other axis means; move it deliberately"),
    ("crate", "pin", "header",
     "the subject unit; a change here means the wrapper attached to the wrong crate"),
    ("direct_obligation_capability", "pin", "header",
     "the artifact's trust marker (`structural-parity-only-v1`)"),
    ("proof_authority", "pin", "header",
     "whether the artifact may be read as source-proof authority; must not drift silently"),
    ("native_verification_requests", "pin", "header",
     "whether the producer emits direct native verification requests"),

    # -- crate size (recorded, not gated) ----------------------------------
    ("bodies", "record", "totals",
     "crate size: falls whenever clean-kernel deletes code, so it has no monotone direction"),
    ("declarations", "record", "totals", "crate size"),
    ("initializer_bodies", "record", "totals", "crate size"),
    ("instr_count", "record", "totals", "crate size"),
    ("symbolic", "record", "totals",
     "lowered-but-symbolic; up can mean more reach OR more imprecision -- no agreed direction"),
    ("unsupported", "record", "totals",
     "sum of per-body unsupported counts; grows with the crate, so a rise is not a regression"),
    ("calls_resolved", "record", "totals", "crate size"),
    ("calls_extern_decls", "record", "totals", "crate size"),
    ("calls_unresolved", "record", "totals",
     "grows with the crate; the meaningful signal is per-body, not the sum"),

    # -- lowering reach (pre-existing gates) --------------------------------
    ("lowered", "grow", "totals",
     "PRE-EXISTING. Bodies THIR->trust-ir lowering accepted"),
    ("spliced", "grow", "totals",
     "PRE-EXISTING. Bodies spliced into the assembled module"),

    # -- the structural differential ---------------------------------------
    ("derived_mir_agreed", "grow", "bodies",
     "NEW GATE (was recorded, never checked). Structural derived-MIR agreement"),
    ("mismatch", "shrink", "bodies",
     "PRE-EXISTING. derived-MIR mismatch: a real divergence alarm"),
    ("derived_mir_unsupported", "record", "bodies",
     "complement of agreed+mismatch over a moving body count"),
    ("markers_exact", "record", "bodies",
     "MEASURED VACUOUS: 1,058 of 1,096 carry `0 marker line(s) identical`. "
     "A gain here is NOT a fidelity gain, so gating it would be a false gate"),
    ("markers_exact_nonvacuous", "grow", "bodies",
     "NEW GATE. The rows whose marker agreement is over a NON-EMPTY marker set -- "
     "the part of `markers_exact` that carries content (27 at the 2026-08-13 record, "
     "38 at 2026-08-19)"),
    ("markers_exact_vacuous", "record", "bodies",
     "The complement: `markers_exact` over two EMPTY sequences. Honest agreement with "
     "no content. RECORDED, NEVER GATED -- making empty sequences fail would refuse "
     "honest agreement and cost flips for nothing"),
    ("markers_lines_total", "grow", "bodies",
     "NEW GATE. The marker LINES behind `markers_exact` -- the evidence quantity, not "
     "the row count. 105 lines in 27 rows (2026-08-13), 129 in 38 (2026-08-19). This is "
     "the axis that sees a body lose 100% of its marker content while the boolean "
     "stays true; the row count cannot"),
    ("markers_differ_derived_empty", "record", "bodies",
     "Refused rows where the DERIVED side emitted no marker at the first divergence "
     "(`vs derived `<end>``). 462 of 462 refusals at 2026-08-19 -- the whole refusal "
     "population has this one shape. Size-coupled, so no monotone direction"),
    ("markers_differ_content", "shrink", "bodies",
     "NEW GATE. A refusal where BOTH sides emitted a marker line and they DISAGREE -- "
     "the failure mode the marker channel exists to catch. Measured 0 crate-wide; a "
     "rise is a real divergence alarm, like `mismatch`"),
    ("markers_channel_skipped", "record", "bodies",
     "`marker channel(built|derived): ...` -- the channel declined to run. One row "
     "(`native_reducers_bool_ext::nat_gcd`) since 2026-08-13"),
    ("markers_agreed_prefix_lines", "record", "bodies",
     "Marker lines that DID match before the first divergence, summed over the refused "
     "rows. Measured 0: every refusal in clean-kernel diverges at line 0, so a refusal "
     "carries no marker evidence at all"),
    ("markers_unparseable", "shrink", "bodies",
     "NEW GATE. A `markers_detail` the ledger cannot read. Must stay 0: an unreadable "
     "detail is counted as neither evidence nor vacuum, so any rise means the marker "
     "accounting on this page has stopped being complete"),

    # -- the semantic differential: THE HOLE THAT LET 38 VERDICTS VANISH ----
    ("interpreter_agreed", "grow", "bodies",
     "NEW GATE. Bodies where the reference interpreter agreed on sampled inputs. "
     "This is the axis 80c7e86f55 moved 606 -> 570 unnoticed"),
    ("interpreter_mismatch", "shrink", "bodies",
     "NEW GATE. A real THIR divergence alarm; must never grow"),
    ("interpreter_samples_total", "grow", "bodies",
     "NEW GATE. Evidence DEPTH: `agreed` on 1 sample is weaker than on 25, and a "
     "count-only gate cannot see the difference. Size-coupled -- see the honesty note"),
    ("interpreter_not_run", "record", "bodies",
     "complement; the informative form is the reason histogram printed on a red"),
    ("interpreter_unsupported", "record", "bodies", "complement"),

    ("seam_agreed", "grow", "bodies",
     "NEW GATE. Call-bearing bodies resolved at crate finalize. 80c7e86f55 moved this 2 -> 0"),
    ("seam_mismatch", "shrink", "bodies", "NEW GATE. Divergence alarm on the seam channel"),
    ("seam_samples_total", "grow", "bodies", "NEW GATE. Evidence depth on the seam channel"),
    ("seam_resolved", "record", "bodies", "size-coupled: how many bodies deferred to the seam at all"),
    ("seam_not_run", "record", "bodies", "complement"),

    # -- lineage -----------------------------------------------------------
    ("lineage_rows", "grow", "bodies",
     "GATED. Rows carrying a WELL-FORMED `sha256:<64hex>` lineage. Read the "
     "direction literally: this is FIELD PRESENCE over `bodies[]` -- NOT a join "
     "and NOT a comparison. On 2026-08-19, 13,146 of 13,774 rows carried a digest "
     "while only 7,571 were spliced, so publishing this number as `lineage joins` "
     "(docs/CRYSTAL_STATUS.md) overstates it by the whole unspliced population. "
     "The join is `flip_lineage_equal`"),
    ("lineage_rows_in_artifact", "grow", "bodies",
     "NEW GATE. Rows that carry a lineage AND are spliced (`func_id` not null) -- "
     "the subset of `lineage_rows` actually PRESENT in the published artifact. The "
     "gap between the two counts digests that describe a body the artifact set "
     "does not contain"),
    ("flip_lineage_equal", "grow", "join",
     "NEW GATE -- THE ARTIFACT-IDENTITY JOIN (crystal link 2c). Flip events whose "
     "`lineage=` digest is EQUAL, as a string, to the digest on the coverage row "
     "reached by def_index. Until 2026-08-19 no instrument in this repo compared "
     "those two strings, and `N of N events carry a lineage equal to their "
     "coverage row's, 0 mismatches` was published anyway"),
    ("flip_spliced", "grow", "join",
     "NEW GATE -- `flip => spliced`. Flip events whose coverage row is IN the "
     "assembled artifact. `record_green` and `splice_ok` are different predicates, "
     "so this is not a tautology: a body can flip while its row is never spliced"),
    ("func_id_rows", "record", "bodies", "assembled-module addresses; an address is not a fidelity axis"),

    # -- the flip lane -----------------------------------------------------
    ("flip_events_total", "grow", "log", "PRE-EXISTING. Bodies whose shipped code came from trust-ir"),
    ("flip_events_codegen", "grow", "log",
     "NEW GATE (was recorded, never checked). The codegen half, gated on its own so a "
     "CTFE gain cannot mask a codegen loss inside the total"),
    ("flip_events_ctfe", "grow", "log", "NEW GATE (was recorded, never checked). The CTFE half"),
    ("flip_backed_total", "grow", "join",
     "NEW GATE. Flips whose body ALSO carries a live interpreter or seam `agreed` verdict"),
    ("flip_backed_codegen", "grow", "join", "NEW GATE. The codegen half of the backed count"),
    ("flip_backed_ctfe", "grow", "join",
     "NEW GATE. The CTFE half. 80c7e86f55 moved this 32 -> 11 -- two thirds of the "
     "CTFE flip lane lost its semantic backing while the flip count never moved"),
]

AXIS_BY_KEY = {a[0]: a for a in AXES}
GATED = {k for k, d, _s, _w in AXES if d != "record"}

# Backward-compatible baseline key spellings: the committed baseline predates
# this file and named three axes differently. Reading through this map is what
# lets the pre-existing gates keep their EXACT recorded values -- in particular
# `lowered` 9068 / `spliced` 7572, which are red at HEAD and must NOT be moved.
LEGACY_KEYS = {
    "flip_events_total": ("flip_events_total",),
    "flip_events_codegen": ("flip_events_codegen",),
    "flip_events_ctfe": ("flip_events_ctfe",),
    "derived_mir_agreed": ("derived_mir_agreed",),
}

# `rustc_mir_transform::trust_ir_flip`'s two `info!` lines, parsed WHOLE.
#
# 2026-08-19: until this commit the regex captured `krate` and `index` ONLY. It
# never looked at `lineage=` -- and the number published FROM THIS INSTRUMENT was
# "N of N flip events carry a lineage EQUAL to their coverage row's, 0
# mismatches". That was a def_index join wearing a digest's name. The zero was a
# property of the regex, not of the artifact: an instrument that never reads the
# digest is arithmetically incapable of reporting a mismatch, so it would have
# printed the same zero over an artifact set that disagreed on every row.
#
# `lineage` is now captured and COMPARED (`flip_lineage_equal`), and a
# `compiled from trust-ir` line that does not parse in full is a fail-closed
# invariant rather than an event silently reduced to its def_index.
FLIP_RE = re.compile(
    r"trust-ir-flip: (?P<ctfe>CTFE )?compiled from trust-ir, "
    r"did=DefId\((?P<krate>\d+):(?P<index>\d+)(?P<didtail>.*?)\), "
    r"asserts=(?P<asserts>\d+), "
    r"lineage=(?P<lineage>sha256:[0-9a-f]{64})"
)

# The shape a lineage digest must have to BE one. A row whose `lineage` is
# present but malformed is not a lineage row: it is a fail-closed invariant.
LINEAGE_RE = re.compile(r"sha256:[0-9a-f]{64}")

# Invariants are counters that must be ZERO. Unlike an axis they carry no
# baseline and no direction -- any non-zero value is RED on the spot. Before
# 2026-08-19 only `flip_events_unjoinable` was actually fatal in `check`;
# `foreign_flip_events` was printed and ignored, so an event naming a crate
# other than the subject could not fail anything. Every invariant is fatal now.
FATAL_INVARIANTS: list[tuple[str, str]] = [
    ("foreign_flip_events",
     "a flip event naming a crate other than the subject: the wrapper attached "
     "-Ztrust-ir-flip to the wrong unit, so no count below is about this crate"),
    ("flip_events_unparsed",
     "a `compiled from trust-ir` line this instrument could not parse IN FULL: "
     "an event whose lineage cannot be read is an event whose artifact identity "
     "is UNKNOWN, and unknown is never rounded down to zero"),
    ("flip_events_unjoinable",
     "a flip event whose def_index reaches no coverage row: the backed and "
     "lineage counts are not over the population they claim"),
    ("flip_lineage_mismatch",
     "THE LINK-2c ALARM. A flip event and the coverage row that describes it "
     "name DIFFERENT artifacts: the body whose code shipped is not the body the "
     "published row is about"),
    ("flip_lineage_row_absent",
     "a flip event joined a coverage row that carries NO lineage digest: the "
     "row cannot be compared to the event, so identity is unproven, not proven"),
    ("flip_lineage_digest_unknown",
     "a flip event's digest appears in NO coverage row: the shipped machine code "
     "was derived from a trust-ir body the artifact set does not contain"),
    ("flip_events_unspliced",
     "`flip => spliced` VIOLATED. `record_green` and `splice_ok` are different "
     "predicates, so a body can flip while its row is never spliced -- and then "
     "the shipped code came from a body ABSENT from the published artifact"),
    ("lineage_digest_collisions",
     "two coverage rows claim one digest: the digest no longer names one object, "
     "so `which row is the flipped body?` is ambiguous again"),
    ("lineage_rows_malformed",
     "a `lineage` field that is not `sha256:<64 hex>`: an unreadable digest is "
     "not a weaker digest, it is an absent one"),
]


# ---------------------------------------------------------------------------
# measure
# ---------------------------------------------------------------------------
def _verdict(body: dict, channel: str) -> str:
    """The verdict marker for a channel, or `not-applicable` for an absent seam."""
    diffs = body["differentials"]
    if channel == "seam":
        seam = diffs.get("seam") or {}
        if seam.get("state") != "resolved":
            return "not-applicable"
        return seam.get("verdict", "not-applicable")
    return diffs[channel]["verdict"]


def _samples(body: dict, channel: str) -> int:
    diffs = body["differentials"]
    if channel == "seam":
        seam = diffs.get("seam") or {}
        return _counter(seam.get("samples", 0), "seam samples") if seam.get("state") == "resolved" else 0
    return _counter(diffs[channel].get("samples", 0), f"{channel} samples")


def measure(coverage_path: str, log_path: str) -> dict:
    cov = _strict_json(coverage_path)
    if not isinstance(cov, dict) or cov.get("schema") != SCHEMA_COVERAGE:
        raise Refused("unsupported or missing coverage schema")
    rows = cov["bodies"]
    if not isinstance(rows, list):
        raise Refused("coverage bodies must be an array")
    totals = cov["totals"]
    by_index: dict[int, dict] = {}
    for row in rows:
        if not isinstance(row, dict):
            raise Refused("coverage body must be an object")
        index = _counter(row.get("def_index"), "body def_index")
        if index in by_index:
            raise Refused(f"duplicate body def_index {index}")
        by_index[index] = row

    def count(channel: str, verdict: str) -> int:
        return sum(1 for r in rows if _verdict(r, channel) == verdict)

    # A marker agreement over an EMPTY marker set proves nothing. The producer
    # spells that case `0 marker line(s) identical`; 1,058 of 1,096 rows are
    # exactly that, which is why `markers_exact` itself is not a gated axis.
    # `trust_ir_markers` does the reading, per row, and its `exact-nonvacuous`
    # class is STRICTER than the old `not startswith("0 marker line")` test: a
    # detail it cannot parse counts as neither evidence nor vacuum, so an
    # unreadable row can no longer be silently promoted to evidence. Measured
    # 2026-08-19: 0 unparseable, so the two agree exactly at this HEAD.
    marker_ledger = trust_ir_markers.ledger(cov)
    mk = marker_ledger["totals"]

    # -- lineage over the coverage rows themselves --------------------------
    #
    # Three different populations that the published prose has run together:
    #   rows that CARRY a digest            -> `lineage_rows`      (presence)
    #   of those, rows IN the artifact      -> `lineage_rows_in_artifact`
    #   events whose digest MATCHES its row -> `flip_lineage_equal` (the join)
    # Only the third is a join. `lineage_rows` was published as "lineage joins".
    def _digest(row: dict) -> str | None:
        lineage = row.get("lineage")
        if isinstance(lineage, str) and LINEAGE_RE.fullmatch(lineage):
            return lineage
        return None

    lineage_rows = [r for r in rows if _digest(r) is not None]
    lineage_malformed = [
        r for r in rows if r.get("lineage") is not None and _digest(r) is None
    ]
    by_lineage: dict[str, list[dict]] = {}
    for row in lineage_rows:
        by_lineage.setdefault(row["lineage"], []).append(row)
    collisions = [
        f"{lineage} claimed by " + ", ".join(r.get("def_path", "?") for r in sharing)
        for lineage, sharing in sorted(by_lineage.items())
        if len(sharing) > 1
    ]

    # -- flip log -> (def_index, lineage), then join to coverage rows --------
    codegen: list[int] = []
    ctfe: list[int] = []
    foreign = 0
    unparsed: list[str] = []
    events: list[dict] = []
    with open(log_path, encoding="utf-8", errors="replace") as handle:
        for line in handle:
            if "compiled from trust-ir" not in line:
                continue
            match = FLIP_RE.search(line)
            if match is None:
                # NOT downgraded to a def_index and NOT folded into `foreign`.
                # An event whose lineage cannot be read has an UNKNOWN artifact
                # identity, and unknown is a distinct, fatal invariant of its own.
                unparsed.append(line.strip()[:200])
                continue
            if "clean_kernel" not in line:
                foreign += 1
                continue
            index = int(match.group("index"))
            (ctfe if match.group("ctfe") else codegen).append(index)
            events.append({
                "index": index,
                "ctfe": match.group("ctfe") is not None,
                "lineage": match.group("lineage"),
                "did": (f"DefId({match.group('krate')}:{match.group('index')}"
                        f"{match.group('didtail')})"),
            })

    # -- THE JOIN. Two independent claims, both stated -----------------------
    #   (i)  the event's def_index reaches the row  -- addressing
    #   (ii) the event's digest EQUALS the row's    -- artifact identity (2c)
    # and, separately from either, `flip => spliced`: the row is in the artifact.
    lineage_equal = 0
    lineage_mismatch: list[str] = []
    lineage_row_absent: list[str] = []
    lineage_digest_unknown: list[str] = []
    flip_spliced = 0
    flip_unspliced: list[str] = []
    for event in events:
        row = by_index.get(event["index"])
        if row is None:
            continue  # counted by `flip_events_unjoinable` below
        name = row.get("def_path", "?")
        row_digest = _digest(row)
        if row_digest is None:
            lineage_row_absent.append(f"{name} <- {event['did']}")
        elif row_digest == event["lineage"]:
            lineage_equal += 1
        else:
            lineage_mismatch.append(
                f"{name}: event {event['lineage']} != row {row_digest}"
            )
        if event["lineage"] not in by_lineage:
            lineage_digest_unknown.append(f"{name} <- {event['lineage']}")
        if row.get("func_id") is None:
            flip_unspliced.append(name)
        else:
            flip_spliced += 1

    def backed(indexes: list[int]) -> tuple[int, int, list[str]]:
        """(backed, unjoinable, backed def_paths) for a set of flip def_indexes."""
        hits, missing, names = 0, 0, []
        for index in indexes:
            row = by_index.get(index)
            if row is None:
                missing += 1
                continue
            if _verdict(row, "interpreter") == "agreed" or _verdict(row, "seam") == "agreed":
                hits += 1
                names.append(row["def_path"])
        return hits, missing, names

    cg_backed, cg_missing, cg_names = backed(codegen)
    ct_backed, ct_missing, ct_names = backed(ctfe)

    measured = {
        "schema": cov.get("schema"),
        "crate": cov.get("crate"),
        "direct_obligation_capability": cov.get("direct_obligation_capability"),
        "proof_authority": cov.get("proof_authority"),
        "native_verification_requests": cov.get("native_verification_requests"),

        "bodies": totals["bodies"],
        "lowered": totals["lowered"],
        "symbolic": totals["symbolic"],
        "spliced": totals["spliced"],
        "declarations": totals["declarations"],
        "initializer_bodies": totals["initializer_bodies"],
        "instr_count": totals["instr_count"],
        "unsupported": totals["unsupported"],
        "calls_resolved": totals["calls"]["resolved"],
        "calls_extern_decls": totals["calls"]["extern_decls"],
        "calls_unresolved": totals["calls"]["unresolved"],

        "interpreter_agreed": count("interpreter", "agreed"),
        "interpreter_mismatch": count("interpreter", "mismatch"),
        "interpreter_not_run": count("interpreter", "not-run"),
        "interpreter_unsupported": count("interpreter", "unsupported"),
        "interpreter_samples_total": sum(_samples(r, "interpreter") for r in rows),

        "seam_agreed": count("seam", "agreed"),
        "seam_mismatch": count("seam", "mismatch"),
        "seam_not_run": count("seam", "not-run"),
        "seam_resolved": sum(1 for r in rows if _verdict(r, "seam") != "not-applicable"),
        "seam_samples_total": sum(_samples(r, "seam") for r in rows),

        "derived_mir_agreed": count("derived_mir", "agreed"),
        "mismatch": count("derived_mir", "mismatch"),
        "derived_mir_unsupported": count("derived_mir", "unsupported"),
        "markers_exact": mk["markers_exact"],
        "markers_exact_nonvacuous": mk["markers_exact_nonvacuous"],
        "markers_exact_vacuous": mk["markers_exact_vacuous"],
        "markers_lines_total": mk["markers_lines_total"],
        "markers_differ_derived_empty": mk["markers_differ_derived_empty"],
        "markers_differ_content": mk["markers_differ_content"],
        "markers_channel_skipped": mk["markers_channel_skipped"],
        "markers_agreed_prefix_lines": mk["markers_agreed_prefix_lines"],
        "markers_unparseable": mk["markers_unparseable"],

        "lineage_rows": len(lineage_rows),
        "lineage_rows_in_artifact": sum(
            1 for r in lineage_rows if r.get("func_id") is not None
        ),
        "flip_lineage_equal": lineage_equal,
        "flip_spliced": flip_spliced,
        "func_id_rows": sum(1 for r in rows if r.get("func_id") is not None),

        "flip_events_total": len(codegen) + len(ctfe),
        "flip_events_codegen": len(codegen),
        "flip_events_ctfe": len(ctfe),
        "flip_backed_total": cg_backed + ct_backed,
        "flip_backed_codegen": cg_backed,
        "flip_backed_ctfe": ct_backed,
    }

    invariants = {
        "foreign_flip_events": foreign,
        "flip_events_unparsed": len(unparsed),
        "flip_events_unjoinable": cg_missing + ct_missing,
        "flip_lineage_mismatch": len(lineage_mismatch),
        "flip_lineage_row_absent": len(lineage_row_absent),
        "flip_lineage_digest_unknown": len(lineage_digest_unknown),
        "flip_events_unspliced": len(flip_unspliced),
        "lineage_digest_collisions": len(collisions),
        "lineage_rows_malformed": len(lineage_malformed),
    }

    sets = {
        "interpreter_agreed": sorted(
            r["def_path"] for r in rows if _verdict(r, "interpreter") == "agreed"
        ),
        "seam_agreed": sorted(r["def_path"] for r in rows if _verdict(r, "seam") == "agreed"),
        "flip_backed": sorted(cg_names + ct_names),
    }

    # Every non-zero invariant, NAMED. A count tells a reader something broke;
    # only the names tell them what. Diagnostic, never gated -- the gate is the
    # count in `invariants`.
    evidence = {
        "flip_events_unparsed": unparsed[:20],
        "flip_lineage_mismatch": sorted(lineage_mismatch)[:20],
        "flip_lineage_row_absent": sorted(lineage_row_absent)[:20],
        "flip_lineage_digest_unknown": sorted(lineage_digest_unknown)[:20],
        "flip_events_unspliced": sorted(flip_unspliced)[:20],
        "lineage_digest_collisions": collisions[:20],
        "lineage_rows_malformed": sorted(
            str(r.get("def_path")) for r in lineage_malformed
        )[:20],
    }

    # Reason buckets for the `not-run` population, keyed by the leading clause of
    # the detail string. Diagnostic only -- printed on a red so the next reader
    # gets the attribution the 2026-08-13 loss did not have. Never gated: the
    # detail text is prose, not a contract.
    buckets = collections.Counter(
        r["differentials"]["interpreter"]["detail"].split(";")[0][:90]
        for r in rows
        if _verdict(r, "interpreter") == "not-run"
    )

    result = {
        "schema_self": SCHEMA_MEASURED,
        "measured": measured,
        "invariants": invariants,
        "sets": sets,
        "evidence": evidence,
        "not_run_reasons": buckets.most_common(6),
        # The full marker class census, so a reader can see the vacuity split
        # without re-deriving it. Diagnostic, never gated: the scalars above are
        # the gate. `trust_ir_markers.py ledger` prints the per-row form.
        "marker_classes": marker_ledger["classes"],
    }
    _validate_measurement(result, need_sets=True)
    return result


# ---------------------------------------------------------------------------
# check / tighten
# ---------------------------------------------------------------------------
def _baseline_value(baseline: dict, key: str):
    measured = baseline.get("measured", {})
    if key in measured:
        return measured[key]
    for alias in LEGACY_KEYS.get(key, ()):  # pragma: no cover - identity today
        if alias in measured:
            return measured[alias]
    return None


def compare(measured: dict, baseline: dict) -> tuple[list[dict], list[str]]:
    """Evaluate EVERY axis. Returns (rows, failures). Never short-circuits."""
    rows: list[dict] = []
    failures: list[str] = []
    now_all = measured["measured"]
    _validate_axes(now_all, "measurement", require_gated=True)
    _validate_axes(baseline.get("measured", {}), "baseline")
    for key, direction, source, why in AXES:
        now = now_all.get(key)
        was = _baseline_value(baseline, key)
        if direction == "record":
            rows.append({"axis": key, "dir": direction, "was": was, "now": now,
                         "state": "RECORD", "source": source, "why": why})
            continue
        if was is None:
            rows.append({"axis": key, "dir": direction, "was": None, "now": now,
                         "state": "UNBASELINED", "source": source, "why": why})
            failures.append(
                f"{key} is UNBASELINED — a gated axis with no baseline is exactly the "
                f"blind spot this ratchet exists to close; seed it with --tighten"
            )
            continue
        if direction == "pin":
            ok = now == was
        elif direction == "grow":
            ok = now >= was
        elif direction == "shrink":
            ok = now <= was
        else:  # pragma: no cover - table is closed
            raise ValueError(f"unknown direction {direction!r} for axis {key!r}")
        rows.append({"axis": key, "dir": direction, "was": was, "now": now,
                     "state": "ok" if ok else "RED", "source": source, "why": why})
        if not ok:
            verb = {"pin": "CHANGED", "grow": "REGRESSED", "shrink": "GREW"}[direction]
            failures.append(f"{key} {verb}: {was} -> {now}   [{why}]")
    return rows, failures


def _lost(baseline_names: list[str], now_names: list[str]) -> list[str]:
    was = collections.Counter(baseline_names)
    now = collections.Counter(now_names)
    lost: list[str] = []
    for name, n in sorted((was - now).items()):
        lost.extend([name] * n)
    return lost


def render(rows: list[dict], measured: dict, bodies: dict | None,
           failures: list[str], stream) -> None:
    width = max(len(r["axis"]) for r in rows)
    print(f"{'':2}{'axis':<{width}}  dir     source   baseline -> measured", file=stream)
    print("-" * (width + 46), file=stream)
    for row in rows:
        was = "—" if row["was"] is None else row["was"]
        mark = {"ok": "  ", "RECORD": "· ", "RED": "!!", "UNBASELINED": "??"}[row["state"]]
        print(f"{mark}{row['axis']:<{width}}  {row['dir']:<6}  {row['source']:<7}  "
              f"{was} -> {row['now']}", file=stream)

    inv = measured["invariants"]
    print("", file=stream)
    print("invariants (every one must be 0):", file=stream)
    for key, _why in FATAL_INVARIANTS:
        value = inv.get(key)
        mark = "  " if value == 0 else "!!"
        shown = "MISSING" if value is None else value
        print(f"{mark}  {key:<28} {shown}", file=stream)

    # Named evidence for any invariant that fired. Printed even when every AXIS
    # is green: an invariant is not a delta against a baseline, it is a
    # standing property of THIS measurement, and it must not need a red axis
    # elsewhere to become visible.
    evidence = measured.get("evidence") or {}
    for key, why in FATAL_INVARIANTS:
        if not inv.get(key):
            continue
        print("", file=stream)
        print(f"  INVARIANT {key} = {inv[key]}  — {why}", file=stream)
        for item in evidence.get(key, []):
            print(f"    - {item}", file=stream)

    if not failures:
        return

    print("", file=stream)
    for line in failures:
        print(f"RED: {line}", file=stream)

    # Attribution: name the bodies, not just the delta.
    if bodies:
        for channel in ("interpreter_agreed", "seam_agreed", "flip_backed"):
            was = bodies.get(channel)
            if was is None:
                continue
            lost = _lost(was, measured["sets"].get(channel, []))
            if not lost:
                continue
            print("", file=stream)
            print(f"  {len(lost)} body/bodies LOST `{channel}` since the baseline set:",
                  file=stream)
            for name in lost[:15]:
                print(f"    - {name}", file=stream)
            if len(lost) > 15:
                print(f"    … and {len(lost) - 15} more", file=stream)
    else:
        print("  (no agreed-body sidecar: scalar deltas only, no body names)", file=stream)

    if any("interpreter" in f for f in failures):
        print("", file=stream)
        print("  interpreter `not-run` reasons in THIS run (top 6):", file=stream)
        for reason, n in measured.get("not_run_reasons", []):
            print(f"    {n:>6}  {reason}", file=stream)


def tighten(measured: dict, baseline: dict) -> tuple[dict, list[str], set[str]]:
    """Seed missing gated axes and raise improving ones. NEVER loosens.

    This is the mode that makes new axes usable while an OLD axis is legitimately
    red: it seeds every unbaselined axis from the measurement and moves an
    existing baseline only in the strictly-stricter direction. An axis that
    regressed keeps its old baseline and therefore stays RED. It is arithmetically
    incapable of making a failing gate pass.
    """
    now_all = measured["measured"]
    _validate_axes(now_all, "measurement", require_gated=True)
    _validate_axes(baseline.get("measured", {}), "baseline")
    changes: list[str] = []
    doc = dict(baseline)
    values = dict(doc.get("measured", {}))
    # Per-axis provenance. A baseline is not taken all at once: an axis that is
    # legitimately red keeps a value measured under an OLDER compiler while the
    # rest move forward, and a reader who cannot see that will mis-attribute the
    # red. `lowered`/`spliced` are exactly that case today.
    stamped = dict(doc.get("axis_updated", {}))
    moved: set[str] = set()
    today = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")
    for key, direction, _source, _why in AXES:
        if direction == "record":
            continue
        now = now_all.get(key)
        was = _baseline_value(baseline, key)
        if was is None:
            values[key] = now
            stamped[key] = today
            moved.add(key)
            changes.append(f"seed  {key} = {now}")
            continue
        if direction == "pin":
            continue  # a pin is neither better nor worse; move it with --update
        stricter = (now > was) if direction == "grow" else (now < was)
        if stricter:
            values[key] = now
            stamped[key] = today
            moved.add(key)
            changes.append(f"raise {key}: {was} -> {now}")
    doc["measured"] = values
    doc["axis_updated"] = stamped
    return doc, changes, moved


# ---------------------------------------------------------------------------
# the compiler pin -- see THE COMPILER PIN in the module docstring
# ---------------------------------------------------------------------------

# The identity of a compiler, as `trust_ir_build.sh` records it. The version
# stamp is NOT identity (CFG_VER_HASH is the trust HEAD at build time), so only
# the two digests are compared; the stamp is carried for the reader.
COMPILER_KEYS = ("trustc_sha256", "driver_sha256")
_SHA256_RE = re.compile(r"[0-9a-f]{64}")

# Pin axes a re-baseline may not move, whatever compiler measured them. A
# compiler under which one of these changes is not "another compiler measuring
# the same thing": the subject must be clean-kernel, and the producer must grant
# no proof authority and request no native verification.
REBASELINE_FIXED: dict[str, object] = {
    "crate": "clean_kernel",
    "proof_authority": False,
    "native_verification_requests": False,
}


class Refused(Exception):
    """A comparison or re-baseline the comparator will not make, and why."""


def _compiler_ok(compiler: object) -> bool:
    return isinstance(compiler, dict) and all(
        isinstance(compiler.get(k), str) and _SHA256_RE.fullmatch(compiler[k])
        for k in COMPILER_KEYS)


def compiler_mismatch(pinned: object, current: object) -> str | None:
    """None when `current` is exactly the compiler the baseline pins; else why not.

    An unpinned or malformed pin is a mismatch too: a count with no compiler
    cannot be compared with anything (that is the defect the pin closes)."""
    if not _compiler_ok(current):
        return ("this run's compiler identity is malformed -- it needs a sha256 for "
                f"each of {', '.join(COMPILER_KEYS)}")
    if not _compiler_ok(pinned):
        return ("the baseline pins no compiler (or a malformed one): a count is a "
                "property of the compiler that measured it, so this run cannot be "
                "compared with it")
    differ = [k for k in COMPILER_KEYS if pinned[k] != current[k]]
    if not differ:
        return None
    return ("COMPILER MISMATCH: the baseline was measured by "
            f"`{pinned.get('version_stamp', '?')}` ("
            + ", ".join(f"{k} {pinned[k][:12]}" for k in differ)
            + f"); this run is `{current.get('version_stamp', '?')}` ("
            + ", ".join(f"{k} {current[k][:12]}" for k in differ)
            + "). Counts are compared only under the compiler that produced the "
              "baseline; re-baseline from ONE run under this compiler with "
              "`scripts/trust_ir_build.sh --rebaseline`.")


def rebaseline(measured: dict, baseline: dict, compiler: dict) -> tuple[dict, list[str]]:
    """Every gated axis from ONE run, pinned to a compiler OTHER than the baseline's.

    Raises `Refused` under the pinned compiler (there only `tighten` moves an
    axis, and it never loosens), on a fatal invariant, on a gated axis the
    measurement lacks, and on a `REBASELINE_FIXED` pin at any other value."""
    _validate_axes(measured.get("measured"), "measurement", require_gated=True)
    _validate_axes(baseline.get("measured", {}), "baseline")
    _validate_invariants(measured, fatal=True)
    if compiler_mismatch(baseline.get("compiler"), compiler) is None:
        raise Refused(
            "this run's compiler IS the one the baseline pins: under one compiler an "
            "axis moves only by --tighten, which never loosens, so a lower count here "
            "is a regression, not a re-baseline")
    if not _compiler_ok(compiler):
        raise Refused("this run's compiler identity is malformed: "
                      f"{compiler_mismatch(compiler, compiler)}")
    inv = measured.get("invariants", {})
    bad = [f"{k}={inv.get(k)!r}" for k, _why in FATAL_INVARIANTS if inv.get(k) != 0]
    if bad:
        raise Refused("a fatal invariant is not 0 in this run: " + ", ".join(bad))
    now_all = measured["measured"]
    gated = [key for key, direction, _s, _w in AXES if direction != "record"]
    missing = [key for key in gated if now_all.get(key) is None]
    if missing:
        raise Refused("this run does not measure gated axis/axes: " + ", ".join(missing))
    moved_fixed = [f"{k} {now_all.get(k)!r} (must be {v!r})"
                   for k, v in REBASELINE_FIXED.items() if now_all.get(k) != v]
    if moved_fixed:
        raise Refused("a pin no compiler may move is off its required value: "
                      + ", ".join(moved_fixed))
    today = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")
    values = {key: now_all[key] for key in gated}
    changes = [f"rebaseline {key}: {_baseline_value(baseline, key)} -> {values[key]}"
               for key in gated if _baseline_value(baseline, key) != values[key]]
    previous = baseline.get("compiler") if _compiler_ok(baseline.get("compiler")) else None
    doc = {
        "schema": baseline.get("schema", "clean.trust_ir_build.baseline.v1"),
        "measured": values,
        "compiler": {k: compiler[k] for k in ("version_stamp", *COMPILER_KEYS)
                     if k in compiler},
        "axis_updated": {key: today for key in gated},
        "rebaselined": {
            "date": today,
            "from_compiler": previous or "unpinned (the baseline mixed compilers)",
            "from_updated_utc_date": baseline.get("updated_utc_date"),
        },
    }
    for key in ("profile",):
        if key in baseline:
            doc[key] = baseline[key]
    return doc, changes


# ---------------------------------------------------------------------------
# selftest — the comparator AND the join, proved without a compiler
# ---------------------------------------------------------------------------

# The regex this file shipped until 2026-08-19. Kept ONLY as the control arm of
# the mutation proof below: a fix to an instrument is unverified until you show
# the broken instrument stays silent on the very defect the fix reports.
_RETIRED_FLIP_RE = re.compile(
    r"trust-ir-flip: (?P<ctfe>CTFE )?compiled from trust-ir, "
    r"did=DefId\((?P<krate>\d+):(?P<index>\d+) "
)

_D1 = "sha256:" + "1a" * 32
_D2 = "sha256:" + "2b" * 32
_D3 = "sha256:" + "3c" * 32


def _flip_line(index: int, lineage: str, name: str, ctfe: bool = False) -> str:
    kind = "CTFE compiled" if ctfe else "compiled"
    return (f" INFO rustc_mir_transform::trust_ir_flip trust-ir-flip: {kind} from "
            f"trust-ir, did=DefId(0:{index} ~ clean_kernel[4676]::{name}), asserts=0, "
            f"lineage={lineage}, flipped_so_far=1")


def _row(index: int, name: str, lineage: str | None, func_id: int | None) -> dict:
    empty = {"verdict": "not-run", "samples": 0, "detail": "synthetic"}
    return {
        "def_path": name, "def_index": index, "kind": "fn",
        "lowered": True, "symbolic": False, "spliced": func_id is not None,
        "lineage": lineage, "func_id": func_id,
        "differentials": {
            "derived_mir": dict(empty), "interpreter": dict(empty), "seam": None,
        },
    }


def _measure_synthetic(rows: list[dict], lines: list[str], tmp) -> dict:
    """Run the REAL `measure` over synthetic artifacts on disk."""
    coverage = {
        "schema": "trust.thir-lower.crate-module.coverage.v2",
        "crate": "clean_kernel",
        "direct_obligation_capability": "structural-parity-only-v1",
        "proof_authority": False,
        "native_verification_requests": False,
        "totals": {
            "bodies": len(rows), "lowered": len(rows), "symbolic": 0,
            "spliced": sum(1 for r in rows if r["func_id"] is not None),
            "declarations": 0, "initializer_bodies": 0, "instr_count": 0,
            "unsupported": 0,
            "calls": {"resolved": 0, "extern_decls": 0, "unresolved": 0},
        },
        "bodies": rows,
    }
    cov_path = tmp / "clean_kernel.coverage.json"
    log_path = tmp / "build.log"
    cov_path.write_text(json.dumps(coverage), encoding="utf-8")
    log_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return measure(str(cov_path), str(log_path))


def _selftest_join() -> list[str]:
    """MUTATION PROOF of the lineage join and of `flip => spliced`.

    Each arm plants ONE deliberate defect in an otherwise-clean artifact pair
    and requires two things at once:

      * the FIXED instrument REPORTS it, on a named invariant;
      * the RETIRED instrument is BLIND to it -- byte-identical output to the
        clean arm on every axis that existed before the fix.

    The second half is what makes the first non-vacuous. Without it, a new
    counter that happens to be zero proves nothing about whether it can ever be
    non-zero, which is precisely the failure this file was fixed for.
    """
    out: list[str] = []

    def check(name: str, cond: bool) -> None:
        if not cond:
            out.append(name)

    with tempfile.TemporaryDirectory() as raw:
        tmp = pathlib.Path(raw)
        clean_rows = [
            _row(10, "a::one", _D1, 0),
            _row(11, "a::two", _D2, 1),
            _row(12, "a::three", _D3, None),   # has a digest, NOT in the artifact
        ]
        clean_log = [_flip_line(10, _D1, "a::one"),
                     _flip_line(11, _D2, "a::two", ctfe=True)]

        base = _measure_synthetic(clean_rows, clean_log, tmp)
        bm, bi = base["measured"], base["invariants"]
        check("clean arm: 2 flip events", bm["flip_events_total"] == 2)
        check("clean arm: both digests equal", bm["flip_lineage_equal"] == 2)
        check("clean arm: both flips spliced", bm["flip_spliced"] == 2)
        check("clean arm: every invariant zero", all(v == 0 for v in bi.values()))
        # presence vs join vs in-artifact are THREE different numbers
        check("clean arm: lineage_rows is presence (3)", bm["lineage_rows"] == 3)
        check("clean arm: lineage_rows_in_artifact is 2",
              bm["lineage_rows_in_artifact"] == 2)
        check("clean arm: presence != join", bm["lineage_rows"] != bm["flip_lineage_equal"])

        # -- MUTATION A: one flip event names a DIFFERENT artifact ----------
        bad_log = [_flip_line(10, _D3, "a::one"),          # row 10 carries _D1
                   _flip_line(11, _D2, "a::two", ctfe=True)]
        mut = _measure_synthetic(clean_rows, bad_log, tmp)
        mm, mi = mut["measured"], mut["invariants"]
        check("A: mismatch REPORTED", mi["flip_lineage_mismatch"] == 1)
        check("A: equal count drops to 1", mm["flip_lineage_equal"] == 1)
        check("A: the mismatch is NAMED",
              any("a::one" in e for e in mut["evidence"]["flip_lineage_mismatch"]))
        check("A: flip count is UNCHANGED", mm["flip_events_total"] == 2)
        # the control arm: the retired regex sees the same two def_indexes
        old_clean = [_RETIRED_FLIP_RE.search(x) for x in clean_log]
        old_bad = [_RETIRED_FLIP_RE.search(x) for x in bad_log]
        check("A: retired regex matched both arms",
              all(m is not None for m in old_clean + old_bad))
        check("A: retired regex is BLIND to the mismatch",
              [m.groupdict() for m in old_clean] == [m.groupdict() for m in old_bad])

        # -- MUTATION B: a body FLIPS but its row was never spliced ---------
        #
        # The splice is MOVED, not deleted: `a::one` (which flipped) leaves the
        # artifact and `a::three` (which did not) enters it. So `spliced`,
        # `func_id_rows` and every other crate-size counter are BIT-IDENTICAL to
        # the clean arm -- which is exactly the shape of the 2026-08-13 loss this
        # file was written for, where none of the watched axes moved at all.
        unspliced_rows = [
            _row(10, "a::one", _D1, None),                 # flipped, now ABSENT
            _row(11, "a::two", _D2, 1),
            _row(12, "a::three", _D3, 0),                  # never flipped, now present
        ]
        mut_b = _measure_synthetic(unspliced_rows, clean_log, tmp)
        bmm, bmi = mut_b["measured"], mut_b["invariants"]
        check("B: flip => spliced VIOLATION reported", bmi["flip_events_unspliced"] == 1)
        check("B: the unspliced body is NAMED",
              mut_b["evidence"]["flip_events_unspliced"] == ["a::one"])
        check("B: flip_spliced drops to 1", bmm["flip_spliced"] == 1)
        check("B: digests still all equal", bmm["flip_lineage_equal"] == 2)
        # NON-VACUITY, stated at full strength: of everything this file
        # measures, ONLY the two axes added by this fix move. `spliced`,
        # `func_id_rows`, `lineage_rows`, the flip counts and the backed counts
        # are all bit-identical, so no pre-fix reader could have seen it.
        # Sharper than expected and worth stating: `lineage_rows_in_artifact`
        # does not move either, because the artifact still holds three digests
        # -- just not the one whose code shipped. `flip_spliced` is the ONLY
        # number in this entire file that changes.
        moved = sorted(k for k in bm if bm[k] != bmm[k])
        check("B: `flip_spliced` is the ONLY axis that moves", moved == ["flip_spliced"])
        check("B: pre-fix invariants all still zero",
              all(bmi[k] == 0 for k in bi if k not in ("flip_events_unspliced",)))

        # -- MUTATION C: an event with NO lineage at all --------------------
        no_lineage = [clean_log[0].replace(f"lineage={_D1}, ", ""), clean_log[1]]
        mut_c = _measure_synthetic(clean_rows, no_lineage, tmp)
        check("C: unparsable event REPORTED",
              mut_c["invariants"]["flip_events_unparsed"] == 1)
        check("C: it is NOT silently counted as a flip",
              mut_c["measured"]["flip_events_total"] == 1)
        check("C: retired regex matched the lineage-less line anyway",
              _RETIRED_FLIP_RE.search(no_lineage[0]) is not None)

        # -- MUTATION D: two rows claim one digest --------------------------
        collided = [_row(10, "a::one", _D1, 0), _row(11, "a::two", _D1, 1)]
        mut_d = _measure_synthetic(collided, clean_log[:1], tmp)
        check("D: digest collision REPORTED",
              mut_d["invariants"]["lineage_digest_collisions"] == 1)

        # -- MUTATION E: a digest that names no row at all ------------------
        orphan = [_flip_line(10, _D1, "a::one")]
        orphan_rows = [_row(10, "a::one", None, 0)]
        mut_e = _measure_synthetic(orphan_rows, orphan, tmp)
        check("E: row without a digest REPORTED",
              mut_e["invariants"]["flip_lineage_row_absent"] == 1)
        check("E: unknown digest REPORTED",
              mut_e["invariants"]["flip_lineage_digest_unknown"] == 1)
        check("E: it is NOT counted as equal",
              mut_e["measured"]["flip_lineage_equal"] == 0)

        # -- MUTATION F: a malformed digest on a row ------------------------
        bent = [_row(10, "a::one", "sha256:beef", 0)]
        mut_f = _measure_synthetic(bent, [], tmp)
        check("F: malformed digest REPORTED",
              mut_f["invariants"]["lineage_rows_malformed"] == 1)
        check("F: a malformed digest is NOT a lineage row",
              mut_f["measured"]["lineage_rows"] == 0)

    return [f"join/{name}" for name in out]


def selftest() -> int:
    fails: list[str] = []

    def check(name: str, cond: bool) -> None:
        if not cond:
            fails.append(name)

    base = {"measured": {k: 10 for k, d, _s, _w in AXES if d in ("grow", "shrink")}}
    base["measured"].update({
        "schema": "trust.thir-lower.crate-module.coverage.v2",
        "crate": "clean_kernel",
        "direct_obligation_capability": "structural-parity-only-v1",
        "proof_authority": False,
        "native_verification_requests": False,
    })
    now = {"measured": dict(base["measured"]), "invariants": {}, "sets": {}, "not_run_reasons": []}
    _rows, failures = compare(now, base)
    check("identical measurement is green", failures == [])

    # every `grow` axis alone must be able to go red
    for key, direction, _s, _w in AXES:
        if direction != "grow":
            continue
        bad = {"measured": dict(base["measured"]), "invariants": {}, "sets": {},
               "not_run_reasons": []}
        bad["measured"][key] = 9
        _rows, failures = compare(bad, base)
        check(f"grow axis {key} goes red alone", len(failures) == 1 and key in failures[0])

    for key, direction, _s, _w in AXES:
        if direction != "shrink":
            continue
        bad = {"measured": dict(base["measured"]), "invariants": {}, "sets": {},
               "not_run_reasons": []}
        bad["measured"][key] = 11
        _rows, failures = compare(bad, base)
        check(f"shrink axis {key} goes red alone", len(failures) == 1 and key in failures[0])

    # a missing gated key is RED, not a silent pass — the defect class itself
    holed = {"measured": {k: v for k, v in base["measured"].items()
                          if k != "interpreter_agreed"}}
    _rows, failures = compare(now, holed)
    check("unbaselined gated axis is red", any("UNBASELINED" in f for f in failures))

    # tighten cannot rescue a regression
    regressed = {"measured": dict(base["measured"]), "invariants": {}, "sets": {},
                 "not_run_reasons": []}
    regressed["measured"]["interpreter_agreed"] = 3
    doc, _changes, _moved = tighten(regressed, base)
    _rows, failures = compare(regressed, doc)
    check("tighten cannot make a regression pass",
          any("interpreter_agreed" in f for f in failures))

    # tighten does raise an improvement, and seeds a hole
    improved = {"measured": dict(base["measured"]), "invariants": {}, "sets": {},
                "not_run_reasons": []}
    improved["measured"]["interpreter_agreed"] = 42
    doc, _changes, _moved = tighten(improved, holed)
    check("tighten seeds and raises", doc["measured"]["interpreter_agreed"] == 42)

    # THE COMPILER PIN. A count is compared only under the compiler that
    # produced its baseline; a re-baseline is one run under ANOTHER compiler.
    old_cc = {"version_stamp": "trustc A", "trustc_sha256": "a" * 64, "driver_sha256": "b" * 64}
    new_cc = dict(old_cc, version_stamp="trustc B", driver_sha256="c" * 64)
    pinned = dict(base, compiler=old_cc)
    check("the pinned compiler is no mismatch", compiler_mismatch(old_cc, dict(old_cc)) is None)
    check("another driver under the same trustc binary is a mismatch",
          "COMPILER MISMATCH" in (compiler_mismatch(old_cc, new_cc) or ""))
    check("an unpinned baseline is a mismatch", compiler_mismatch(None, old_cc) is not None)
    check("a malformed pin is a mismatch",
          compiler_mismatch(dict(old_cc, driver_sha256="b" * 12), old_cc) is not None)
    clean_inv = {k: 0 for k, _w in FATAL_INVARIANTS}
    lower = {"measured": dict(base["measured"]), "invariants": dict(clean_inv), "sets": {},
             "not_run_reasons": []}
    lower["measured"]["lowered"] = 3
    lower["measured"]["direct_obligation_capability"] = "obligation-bearing-pending-v2"
    try:
        rebaseline(lower, pinned, dict(old_cc))
        check("rebaseline REFUSES the pinned compiler", False)
    except Refused:
        pass
    try:
        doc, _changes = rebaseline(lower, pinned, new_cc)
    except Refused as exc:
        check(f"rebaseline under ANOTHER compiler is admitted ({exc})", False)
        doc = dict(pinned)
    check("rebaseline under another compiler takes every axis from the one run",
          doc["measured"]["lowered"] == 3
          and doc["measured"]["direct_obligation_capability"] == "obligation-bearing-pending-v2"
          and doc.get("compiler", {}).get("driver_sha256") == "c" * 64)
    _rows, failures = compare(lower, doc)
    check("the re-baselined run is green against its own baseline", failures == [])
    check("the re-baselined pin refuses the OLD compiler",
          compiler_mismatch(doc["compiler"], old_cc) is not None)
    try:
        rebaseline(lower, doc, dict(new_cc))
        check("a second rebaseline under the now-pinned compiler is REFUSED", False)
    except Refused:
        pass
    lower_again = {"measured": dict(lower["measured"]), "invariants": dict(clean_inv),
                   "sets": {}, "not_run_reasons": []}
    lower_again["measured"]["lowered"] = 2
    _rows, failures = compare(lower_again, doc)
    check("under the pinned compiler a lower count is still a regression",
          any("lowered" in f for f in failures))
    for label, mutate in (
        ("rebaseline REFUSES a producer that claims proof authority",
         lambda m: m["measured"].__setitem__("proof_authority", True)),
        ("rebaseline REFUSES a different subject crate",
         lambda m: m["measured"].__setitem__("crate", "clean_elab")),
        ("rebaseline REFUSES a fatal invariant",
         lambda m: m["invariants"].__setitem__("flip_lineage_mismatch", 1)),
        ("rebaseline REFUSES a run missing a gated axis",
         lambda m: m["measured"].pop("spliced")),
    ):
        bad = {"measured": dict(lower["measured"]), "invariants": dict(clean_inv), "sets": {},
               "not_run_reasons": []}
        mutate(bad)
        try:
            rebaseline(bad, pinned, new_cc)
            check(label, False)
        except Refused:
            pass

    # the body-set differ names what was lost, with multiplicity
    lost = _lost(["a", "b", "b", "c"], ["b", "c"])
    check("lost set is a multiset difference", lost == ["a", "b"])

    # the flip-log regex must actually match the emitted line shape
    line = (" INFO rustc_mir_transform::trust_ir_flip trust-ir-flip: CTFE compiled from "
            "trust-ir, did=DefId(0:721 ~ clean_kernel[4676]::cert::bundle::MAX), asserts=1, "
            f"lineage={_D1}, flipped_so_far=1")
    match = FLIP_RE.search(line)
    check("flip regex matches a CTFE event", match is not None and match.group("index") == "721")
    check("flip regex captures the lineage digest",
          match is not None and match.group("lineage") == _D1)
    line_cg = line.replace("CTFE compiled", "compiled")
    match_cg = FLIP_RE.search(line_cg)
    check("flip regex matches a codegen event",
          match_cg is not None and match_cg.group("ctfe") is None)
    # A def path may legally contain `)` -- `<(A, B) as T>::f`. The tail is
    # non-greedy up to `), asserts=`, so such a line must still parse WHOLE.
    tupled = (" INFO trust-ir-flip: compiled from trust-ir, did=DefId(0:9 ~ "
              "clean_kernel[1]::{impl#0}::<(A, B) as T>::f), asserts=0, "
              f"lineage={_D1}, flipped_so_far=2")
    match_tup = FLIP_RE.search(tupled)
    check("flip regex survives a `)` inside the def path",
          match_tup is not None and match_tup.group("lineage") == _D1
          and match_tup.group("index") == "9")
    # Fail closed on a truncated digest: an unreadable lineage is an ABSENT one.
    check("flip regex REFUSES a truncated digest",
          FLIP_RE.search(line.replace(_D1, "sha256:37a9")) is None)

    fails.extend(_selftest_join())

    check("every axis has a direction", all(d in ("grow", "shrink", "pin", "record")
                                            for _k, d, _s, _w in AXES))
    check("axis keys are unique", len(AXIS_BY_KEY) == len(AXES))

    # Domain checks precede comparisons: Python's bool/int equality and IEEE
    # infinities must never turn malformed producer data into passing counts.
    def refuses(label, action):
        try:
            action()
        except Refused:
            return
        check(label, False)

    for key, _direction, _source, _why in AXES:
        if key in ("schema", "crate", "direct_obligation_capability"):
            continue
        bad_values = (0, 1, "false") if key in (
            "proof_authority", "native_verification_requests"
        ) else (-1, 0.5, False, float("inf"), float("nan"), "1")
        for value in bad_values:
            bad = {"measured": dict(base["measured"], **{key: value})}
            refuses(f"invalid measurement {key}={value!r}", lambda: compare(bad, base))
            refuses(f"invalid baseline {key}={value!r}", lambda: compare(now, bad))
    for key, _why in FATAL_INVARIANTS:
        for value in (False, -1, 0.5, float("inf")):
            bad = {"invariants": dict(clean_inv, **{key: value})}
            refuses(f"invalid invariant {key}={value!r}", lambda: _validate_invariants(bad))
    with tempfile.TemporaryDirectory() as directory:
        tmp = pathlib.Path(directory)
        invalid = tmp / "invalid.json"
        for text in ('{"x": 1, "x": 2}', '{"x": NaN}', '{"x": 1e309}'):
            invalid.write_text(text, encoding="utf-8")
            refuses(f"strict JSON refuses {text}", lambda: _strict_json(invalid))
        invalid.write_text('{"metadata": 1.25}', encoding="utf-8")
        check("finite additive metadata stays valid", _strict_json(invalid) == {"metadata": 1.25})
        duplicate = [_row(1, "one", _D1, 1), _row(1, "two", _D2, 2)]
        refuses("duplicate body indexes are refused",
                lambda: _measure_synthetic(duplicate, [], tmp))

    # The marker ledger is a gated INPUT to this file's axes, so its own
    # comparator must be proved here too -- a marker axis computed by a broken
    # parser is exactly the silent-green shape this file exists to prevent.
    check("marker ledger selftest passes", trust_ir_markers.selftest() == 0)

    # And the vacuity rule itself, stated as a test rather than a comment: a
    # `markers_exact: true` row over two EMPTY sequences is HONEST AGREEMENT and
    # must never be scored as a failure. What it must not do is count as
    # evidence.
    vac = trust_ir_markers.classify(
        {"markers_exact": True, "markers_detail": "0 marker line(s) identical"})
    check("empty-vs-empty stays true", vac["markers_exact"] is True)
    check("empty-vs-empty contributes no evidence LINES", vac["built_lines"] == 0)

    for name in fails:
        print(f"SELFTEST FAIL: {name}", file=sys.stderr)
    print(f"selftest: {len(fails)} failure(s) over {len(AXES)} axes")
    return 1 if fails else 0


# ---------------------------------------------------------------------------
def _main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_measure = sub.add_parser("measure")
    p_measure.add_argument("--coverage", required=True)
    p_measure.add_argument("--log", required=True)
    p_measure.add_argument("--out")

    for name in ("check", "tighten", "rebaseline"):
        p = sub.add_parser(name)
        p.add_argument("--measured", required=True)
        p.add_argument("--baseline", required=True)
        p.add_argument("--compiler", required=True,
                       help="the measuring compiler's identity JSON (trust_ir_build.sh writes it)")
        p.add_argument("--bodies")
        if name != "check":
            p.add_argument("--write", action="store_true")

    p_cc = sub.add_parser("compiler-check")
    p_cc.add_argument("--baseline", required=True)
    p_cc.add_argument("--compiler", required=True)

    sub.add_parser("table")
    sub.add_parser("selftest")

    args = parser.parse_args()

    if args.cmd == "selftest":
        return selftest()

    if args.cmd == "table":
        width = max(len(a[0]) for a in AXES)
        for key, direction, source, why in AXES:
            print(f"{key:<{width}}  {direction:<6}  {source:<7}  {why}")
        gated = sum(1 for _k, d, _s, _w in AXES if d != "record")
        print(f"\n{len(AXES)} axes: {gated} gated, {len(AXES) - gated} recorded-not-gated")
        return 0

    if args.cmd == "measure":
        doc = measure(args.coverage, args.log)
        text = json.dumps(doc, indent=1, sort_keys=False, allow_nan=False) + "\n"
        if args.out:
            _write_artifacts({pathlib.Path(args.out): text})
        else:
            sys.stdout.write(text)
        return 0

    baseline = _strict_json(args.baseline)
    if not isinstance(baseline, dict) or baseline.get("schema") != SCHEMA_BASELINE:
        raise Refused("unsupported or missing baseline schema")
    _validate_axes(baseline.get("measured"), "baseline")
    compiler = _strict_json(args.compiler)
    mismatch = compiler_mismatch(baseline.get("compiler"), compiler)

    if args.cmd == "compiler-check":
        # Exit 0: this is the pinned compiler. Exit 1: it is not, and why.
        print(mismatch or "compiler: the baseline's pinned compiler "
              f"(`{compiler.get('version_stamp', '?')}`)")
        return 1 if mismatch else 0

    measured = _strict_json(args.measured)
    _validate_measurement(measured, need_sets=bool(args.bodies))
    bodies = None
    if args.bodies:
        if pathlib.Path(args.bodies).resolve() == pathlib.Path(args.baseline).resolve():
            raise Refused("baseline and body sidecar must be different files")
        try:
            bodies = _strict_json(args.bodies)
        except FileNotFoundError:
            bodies = None
        if bodies is not None:
            if not isinstance(bodies, dict) or bodies.get("schema") != SCHEMA_BODIES:
                raise Refused("unsupported or missing body sidecar schema")
            _validate_sets(bodies, "body sidecar")

    if args.cmd == "check":
        rows, failures = compare(measured, baseline)
        if mismatch:
            # Printed FIRST and fatal: every axis row below compares this
            # compiler's count with another compiler's, so none of them is a
            # verdict about clean -- the table is shown for the reader only.
            print(f"RED: {mismatch}", file=sys.stdout)
            failures = [mismatch] + failures
        render(rows, measured, bodies, failures, sys.stdout)
        inv = measured["invariants"]
        # EVERY invariant is fatal, and an invariant this measurement does not
        # carry at all is fatal too: a measurement produced by an older,
        # blinder extractor must not read as a pass on a check it never ran.
        for key, why in FATAL_INVARIANTS:
            value = inv.get(key)
            if value is None:
                print(f"RED: invariant {key} is ABSENT from this measurement — it was "
                      f"produced before the check existed, so its silence is not a "
                      f"pass ({why})", file=sys.stdout)
                failures = failures + [key]
            elif value:
                print(f"RED: {key} = {value} — {why}", file=sys.stdout)
                failures = failures + [key]
        return 1 if failures else 0

    if args.cmd == "rebaseline":
        try:
            doc, changes = rebaseline(measured, baseline, compiler)
        except Refused as exc:
            print(f"rebaseline REFUSED: {exc}", file=sys.stderr)
            return 1
        moved = {key for key, direction, _s, _w in AXES if direction != "record"}
    else:
        _validate_invariants(measured, fatal=True)
        if mismatch:
            print(f"tighten REFUSED: {mismatch}", file=sys.stderr)
            return 1
        doc, changes, moved = tighten(measured, baseline)
        doc["compiler"] = baseline["compiler"]
        # Retired with the compiler pin: per-run provenance from before it.
        for legacy in ("trustc", "trustc_last_tighten", "driver_last_tighten", "standing_red"):
            doc.pop(legacy, None)
    doc["note"] = (
        "Monotonic baseline for scripts/trust_ir_build.sh. The direction of every axis is "
        "declared in scripts/trust_ir_axes.py::AXES (run `trust_ir_axes.py table`); a gated "
        "axis absent from this file is RED, not a silent pass. Counts are clean-kernel only: "
        "the wrapper attaches -Ztrust-ir-flip to the subject unit alone, and the script "
        "refuses any event that does not name clean_kernel. Every value is from runs under "
        "the ONE compiler in `compiler` (trustc + librustc_driver sha256): check and "
        "tighten refuse any other, and only --rebaseline, under a different compiler, "
        "replaces every axis from one run."
    )
    doc["updated_utc_date"] = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")
    if args.write:
        outputs = {pathlib.Path(args.baseline): json.dumps(doc, indent=1, allow_nan=False) + "\n"}
        if args.bodies:
            # The sidecar follows the SAME one-directional rule as the scalars it
            # explains. A channel whose scalar axis did not move (or moved the
            # wrong way) keeps its stored set: overwriting it from a regressed run
            # would erase the very names the red is supposed to print.
            channel_axis = {
                "interpreter_agreed": "interpreter_agreed",
                "seam_agreed": "seam_agreed",
                "flip_backed": "flip_backed_total",
            }
            merged = bodies if isinstance(bodies, dict) else {}
            out = {
                "schema": SCHEMA_BODIES,
                "note": ("The def_path multiset behind the gated `interpreter_agreed`, "
                         "`seam_agreed` and `flip_backed` counts. Diagnostic, not a gate: on a "
                         "red the ratchet names the bodies that were lost instead of only the "
                         "delta. def_path is not injective over bodies (closures and promoted "
                         "constants share names), so this is compared as a MULTISET. A channel "
                         "is rewritten only when its scalar axis was seeded or raised."),
                "updated_utc_date": doc["updated_utc_date"],
            }
            for channel, axis in channel_axis.items():
                if axis in moved or channel not in merged:
                    out[channel] = measured["sets"][channel]
                else:
                    out[channel] = merged[channel]
            outputs[pathlib.Path(args.bodies)] = json.dumps(out, indent=1, allow_nan=False) + "\n"
        _write_artifacts(outputs)
    for line in changes:
        print(line)
    print(f"{args.cmd}: {len(changes)} axis change(s)"
          + ("" if args.write else "  (dry run — pass --write)"))
    return 0


def main() -> int:
    try:
        return _main()
    except (Refused, OSError, ValueError, KeyError, TypeError) as exc:
        print(f"trust_ir_axes REFUSED: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
