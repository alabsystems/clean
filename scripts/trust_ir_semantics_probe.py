#!/usr/bin/env python3
"""WS6.12 probe: can `clean check` elaborate trust-ir's own Lean semantics?

This is a MEASUREMENT, never an authority transfer. trust-ir's semantics
package (`lean/trust_ir-semantics`, Lean 4.8.0 + lake, gated by the
`AxiomAudit.lean` `#guard_msgs` census) stays the authority until EVERY file
elaborates under `clean check` AND the axiom census matches — `ay_sound_unsat`
as the sole first-party axiom, no proof placeholder anywhere. The probe only
reports whether that condition holds; it grants nothing.

Every `clean check` runs under the package's own `leanOptions` (read from its
`lakefile.lean`, or stated with `--lean-option`) as `-D` overrides, because
`lake build` compiles every module with them: without `-DautoImplicit=false`
the census would count declarations the package's real build refuses (G50).

The package is read-only input: every subcommand copies it into a scratch
directory first, so neither `clean check` nor a deliberate mutation can write
into a trust-ir checkout.

Subcommands
-----------
census            run `clean check --json` on every file, one process per
                  file, in import order; record elaborated / first failure /
                  time per file plus the axiom census.
negative-twin     break ONE semantics file in a copy and require that
                  `clean check` refuses it, naming the injected declaration.
                  Shows the census is not vacuous (a checker that accepts
                  everything would "pass" the census).
mutation-control  inject a `sorry` into a copy and require that the axiom
                  census flags it — from the source scan AND from Clean's own
                  `trust_summary.sorry_axioms`, and (with --lean-authority) that
                  the Lean 4.8 AxiomAudit gate goes red too.
repros            re-run every filed elaborator gap (repros/manifest.json): an
                  OPEN row must still FAIL as filed; a row marked `closed_by`
                  must PASS and its negative twin must FAIL as filed. A flip
                  either way fails the run, so a closure is re-filed, never
                  inferred.
table             render census.md from census.json (pure).

Exit status: 0 when the subcommand's own contract held (for `census`, when the
measurement COMPLETED — its verdict is in the JSON, not the exit code, because
"not yet" is the expected answer and is still a successful measurement); 1
when a control failed (the twin was accepted, the sorry was not flagged); 2 on
a usage or environment error.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import NamedTuple

SCHEMA = "clean-trust-ir-semantics-probe-v1"
# The one first-party axiom trust-ir's AxiomAudit gate admits.
EXPECTED_FIRST_PARTY_AXIOMS = ("ay_sound_unsat",)
# Proof placeholders: each mints `sorryAx` when it reaches a proof term.
PLACEHOLDER_TOKENS = ("sorry", "admit")
# `native_decide` is NOT first-party: it rests on the Lean-core
# `Lean.ofReduceBool` (the trusted compiler/evaluator), which trust-ir's
# AxiomAudit does not audit and does not count against the census. It is
# disclosed separately, because a checker that cannot run the evaluator cannot
# check these sites the way Lean does.
EVALUATOR_TOKENS = ("native_decide",)
NEGATIVE_TWIN_DECL = "ws612_negative_twin"
MUTATION_TARGET_FILE = "TrustIr/Proofs/AYBridge.lean"
MUTATION_TARGET_THEOREM = "ay_sound_contrapositive"
# A theorem `clean check` accepts at the probe's measured head (see the
# census), so a sorry there is a live control rather than a vacuous one.
CLEAN_MUTATION_FILE = "TrustIr/CmpOp.lean"
CLEAN_MUTATION_THEOREM = "ICmpOp.negate_negate"
# Resident-memory bound per `clean check` process, in GB. See run_bounded.
DEFAULT_MEM_CAP_GB = 8.0

_IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$")
_DECL_PREFIX = r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
_AXIOM_RE = re.compile(_DECL_PREFIX + r"axiom\s+([^\s:({\[]+)")


class CompletedRun(NamedTuple):
    """What a bounded run returned, shaped like `subprocess.CompletedProcess`."""

    returncode: int
    stdout: str
    stderr: str


class ProbeError(Exception):
    """An environment or input problem: the probe cannot measure."""


# --------------------------------------------------------------------------
# Source handling (pure; unit-tested without a `clean` binary)
# --------------------------------------------------------------------------

def strip_comments_and_strings(src: str) -> str:
    """Blank out Lean comments (`--`, nested `/- -/`, doc comments) and string
    literals, preserving newlines so line numbers survive.

    A `sorry` inside a docstring or a comment is prose, not a proof term, so
    the census must not count it; a `sorry` in code must never be hidden."""
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        c = src[i]
        if depth:
            if src.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif src.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
        elif c == '"':
            out.append(" ")
            i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\" and i + 1 < n:
                    out.append("  ")
                    i += 2
                    continue
                out.append("\n" if src[i] == "\n" else " ")
                i += 1
            if i < n:
                out.append(" ")
                i += 1
        elif (c == "'" and i + 2 < n and src[i + 2] == "'" and src[i + 1] != "\\"
              and not (i and (src[i - 1].isalnum() or src[i - 1] in "_'"))):
            # char literal like 'x' — blank it so a quote char cannot open a
            # phantom string
            out.append("   ")
            i += 3
        else:
            out.append(c)
            i += 1
    return "".join(out)


def imports_of(src: str) -> list[str]:
    """The `import` header of a Lean file (imports precede every other command)."""
    mods = []
    for line in strip_comments_and_strings(src).splitlines():
        s = line.strip()
        if not s:
            continue
        m = _IMPORT_RE.match(s)
        if not m:
            break
        mods.append(m.group(1))
    return mods


def module_of(rel: str) -> str:
    return rel[: -len(".lean")].replace("/", ".")


def package_files(pkg: Path) -> dict[str, str]:
    """module name -> relative path, for every source file of the package."""
    files = {}
    for p in sorted(pkg.rglob("*.lean")):
        rel = p.relative_to(pkg).as_posix()
        if rel == "lakefile.lean" or rel.startswith(".lake/"):
            continue
        files[module_of(rel)] = rel
    if not files:
        raise ProbeError(f"no .lean sources under {pkg}")
    return files


def import_order(graph: dict[str, list[str]]) -> list[str]:
    """Deterministic topological order (Kahn, lexicographic tie-break).

    Only intra-package edges order anything; an import outside the package is
    Lean core and imposes no order. A cycle is refused, not broken."""
    local = {m: sorted({d for d in deps if d in graph}) for m, deps in graph.items()}
    indeg = {m: len(ds) for m, ds in local.items()}
    users: dict[str, list[str]] = {m: [] for m in local}
    for m, ds in local.items():
        for d in ds:
            users[d].append(m)
    ready = sorted(m for m, k in indeg.items() if k == 0)
    order = []
    while ready:
        m = ready.pop(0)
        order.append(m)
        for u in users[m]:
            indeg[u] -= 1
            if indeg[u] == 0:
                ready.append(u)
        ready.sort()
    if len(order) != len(local):
        raise ProbeError(f"import cycle among {sorted(set(local) - set(order))}")
    return order


def source_axiom_census(pkg: Path) -> dict:
    """First-party `axiom` declarations and placeholder tokens, from source.

    Comment- and string-blind, so a word in prose is not a finding."""
    axioms, placeholders, evaluator = [], [], []
    for mod, rel in package_files(pkg).items():
        code = strip_comments_and_strings((pkg / rel).read_text(encoding="utf-8"))
        for lineno, line in enumerate(code.splitlines(), 1):
            m = _AXIOM_RE.match(line)
            if m:
                axioms.append({"name": m.group(1), "file": rel, "line": lineno})
            for toks, sink in ((PLACEHOLDER_TOKENS, placeholders), (EVALUATOR_TOKENS, evaluator)):
                for tok in toks:
                    for _ in re.finditer(r"(?<![A-Za-z0-9_.'])" + tok + r"(?![A-Za-z0-9_'])", line):
                        sink.append({"token": tok, "file": rel, "line": lineno})
    names = sorted(a["name"] for a in axioms)
    return {
        "first_party_axioms": axioms,
        "placeholders": placeholders,
        "evaluator_sites": len(evaluator),
        "evaluator_sites_by_file": {f: sum(e["file"] == f for e in evaluator)
                                    for f in sorted({e["file"] for e in evaluator})},
        "expected_first_party_axioms": list(EXPECTED_FIRST_PARTY_AXIOMS),
        "matches": names == sorted(EXPECTED_FIRST_PARTY_AXIOMS) and not placeholders,
    }


# --------------------------------------------------------------------------
# Running `clean check`
# --------------------------------------------------------------------------

# --------------------------------------------------------------------------
# The options Lake compiles the package with (gap G50)
# --------------------------------------------------------------------------

# `lake build` hands every module of the package to `lean` with the package's
# `leanOptions` as `-D<name>=<value>` (trust_ir-semantics: autoImplicit false).
# A census run without them checks a different language: `theorem t (x : Foo)`
# with `Foo` undefined auto-binds and passes where the package build refuses.
# A declaration head at column 0, optionally after an attribute on the same
# line (`@[default_target] lean_lib X where`).
_LAKE_DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(package|lean_lib|lean_exe|lean_test)\b")
_LEAN_OPTION_ENTRY_RE = re.compile(
    r'\s*⟨\s*`([A-Za-z0-9_.]+)\s*,\s*(true|false|[0-9]+|"(?:[^"\\]|\\.)*")\s*⟩\s*')
_STRING_LITERAL_RE = re.compile(r'\s*"((?:[^"\\]|\\.)*)"\s*')
# The option-carrying fields, in the order Lake hands them to `lean`
# (`mod.weakLeanArgs ++ mod.leanArgs`, leanArgs = leanOptions ++ moreLeanArgs).
_OPTION_FIELDS = ("weakLeanArgs", "leanOptions", "moreLeanArgs")


def _strip_lake_comments(text: str) -> str:
    """`text` without `--` line comments and `/- -/` blocks (lakefiles put no
    `--` inside the strings this reader cares about)."""
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    return "\n".join(line.split("--", 1)[0] for line in text.splitlines())


def _balanced_array(text: str, start: int, field: str) -> tuple[str, int]:
    """The `#[...]` literal beginning at `text[start]` (brackets balanced) and
    the index after it. Fails closed when a `++` / `|>` / `<|` continues the
    value: only part of it would be read."""
    if not text.startswith("#[", start):
        raise ProbeError(f"{field} value is not an array literal: {text[start:start + 60]!r}")
    depth = 0
    for i in range(start + 1, len(text)):
        depth += {"[": 1, "]": -1}.get(text[i], 0)
        if depth == 0:
            rest = text[i + 1:].lstrip()
            if rest.startswith(("++", "|>", "<|")):
                raise ProbeError(f"{field} value continues past its array literal "
                                 f"({rest[:20]!r}); pass --lean-option explicitly")
            return text[start:i + 1], i + 1
    raise ProbeError(f"unterminated {field} array")


def _field_owner(text: str, at: int) -> str | None:
    """The kind of the declaration whose block contains `text[at]`."""
    heads = [m for m in (_LAKE_DECL_RE.match(h.group(0))
                         for h in re.finditer(r"(?m)^\S.*$", text[:at])) if m]
    return heads[-1].group(1) if heads else None


def _define_entries(field: str, inner: str) -> list[str]:
    """The `-D` overrides of a `moreLeanArgs` / `weakLeanArgs` string array,
    as `name=value`. Fails closed on any other argument: the census runs
    `clean check`, which takes `-D` and nothing else of `lean`'s."""
    out: list[str] = []
    items = [e for e in re.split(r',(?=(?:[^"]*"[^"]*")*[^"]*$)', inner) if e.strip()]
    pending_d = False
    for item in items:
        m = _STRING_LITERAL_RE.fullmatch(item)
        if m is None:
            raise ProbeError(f"{field} entry the probe cannot read: {item.strip()!r}")
        arg = m.group(1)
        if pending_d:
            out.append(arg)
            pending_d = False
        elif arg == "-D":
            pending_d = True
        elif arg.startswith("-D"):
            out.append(arg[2:])
        else:
            raise ProbeError(f"{field} argument {arg!r} is not a `-D`; pass --lean-option "
                             "explicitly")
    if pending_d:
        raise ProbeError(f"{field} ends in a `-D` with no argument")
    return out


def lakefile_lean_options(pkg: Path) -> list[str]:
    """`name=value` for each PACKAGE-level override in `pkg/lakefile.lean`, in
    the order Lake passes them to `lean`: the `-D` entries of `weakLeanArgs`,
    then each `leanOptions` entry (rendered as Lake's `LeanOption.asCliArg`
    renders it; a string value keeps its quotes), then the `-D` entries of
    `moreLeanArgs`.

    Fails closed (`ProbeError`) on anything it cannot read exactly: a value
    that is not an array literal of the expected entries, a value continued
    with `++`, a non-`-D` argument, or any of these fields on a `lean_lib` /
    `lean_exe` (attribute-prefixed heads included), whose files this per-file
    census cannot single out. Pass `--lean-option` to state the options
    explicitly instead."""
    lakefile = pkg / "lakefile.lean"
    if not lakefile.is_file():
        if (pkg / "lakefile.toml").is_file():
            raise ProbeError("lakefile.toml: pass the package's options with --lean-option")
        return []
    text = _strip_lake_comments(lakefile.read_text(encoding="utf-8"))
    by_field: dict[str, list[str]] = {f: [] for f in _OPTION_FIELDS}
    for m in re.finditer(r"\b(" + "|".join(_OPTION_FIELDS) + r")\s*:=\s*", text):
        field = m.group(1)
        owner = _field_owner(text, m.start())
        if owner != "package":
            raise ProbeError(f"`{field}` on a `{owner}` block: the census applies one "
                             "option set to every file; pass --lean-option explicitly")
        array, _ = _balanced_array(text, m.end(), field)
        inner = array[2:-1]
        if field != "leanOptions":
            by_field[field] += _define_entries(field, inner)
            continue
        entries = [e for e in inner.split("⟩") if e.strip(" ,\n\t")]
        for entry in entries:
            em = _LEAN_OPTION_ENTRY_RE.fullmatch(entry.strip(" ,\n\t") + "⟩")
            if em is None:
                raise ProbeError(f"leanOptions entry Clean's probe cannot read: {entry.strip()!r}")
            by_field[field].append(f"{em.group(1)}={em.group(2)}")
    return [o for f in _OPTION_FIELDS for o in by_field[f]]


def clean_define_args(options: list[str]) -> list[str]:
    """The `clean check` arguments for `options` (Lean's `-D` spelling)."""
    return [f"-D{o}" for o in options]


def copy_package(src: Path, work: Path) -> Path:
    dst = work / "pkg"
    shutil.copytree(src, dst, ignore=shutil.ignore_patterns(".lake", "build"))
    return dst


def _dotted(path: Path) -> str:
    """The dotted spelling Clean derives from an absolute directory path."""
    return str(path).strip("/").replace("/", ".")


def mask_paths(text: str, base: Path) -> str:
    """Replace this machine's paths — slashed and Clean's dotted spelling —
    with placeholders, so a committed artifact reads the same elsewhere."""
    for path, name in ((base, "<repros>"), (Path.home(), "<home>")):
        for cand in dict.fromkeys((path, path.absolute(), path.resolve())):
            text = text.replace(str(cand), name).replace(_dotted(cand), name)
    return text


def normalize_tags(text: str, modules: set) -> str:
    """Rewrite `[<dotted absolute path>.TrustIr.Basic]` to `[TrustIr.Basic]`.

    Clean tagged an imported source module with a name derived from its
    absolute path (gap G14, closed by G21 brick B4: the tag is now the name the
    `import` wrote; this reduction stays for binaries and artifacts from
    before). A recorded row should name the module, and an artifact
    committed from one machine should read the same on another, so each tag
    whose SUFFIX is a module of the package under test is reduced to that
    module. A tag that is not one of them is left exactly as it came."""
    def fix(m):
        tag = m.group(1)
        for mod in modules:
            if tag == mod or tag.endswith("." + mod):
                return "[" + mod + "]"
        return m.group(0)
    return re.sub(r"\[([^\]\n]+)\]", fix, text)


def first_failure(report: dict | None, stderr: str) -> str | None:
    if report:
        for key in ("errors", "kernel_failures", "trust_failures", "diverged", "parser_recovery"):
            vals = report.get(key) or []
            if vals:
                v = vals[0]
                return v if isinstance(v, str) else json.dumps(v, sort_keys=True)
        return None
    tail = [ln for ln in stderr.strip().splitlines() if ln.strip()]
    return tail[-1] if tail else None


def _rss_gb(pid: int) -> float:
    """Resident set of a process tree member, in GB (0.0 once it is gone)."""
    try:
        out = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)],
                             capture_output=True, text=True, timeout=10).stdout.strip()
        return int(out) / (1024 * 1024) if out else 0.0
    except (OSError, ValueError, subprocess.TimeoutExpired):
        return 0.0


def run_bounded(cmd: list[str], cwd: Path, timeout: int, mem_cap_gb: float) -> tuple:
    """Run `cmd`, killing it at a wall bound OR a resident-memory bound.

    The memory bound is not a nicety on this hardware: an unbounded checker
    process took 31 GB on one file during this probe's own first run, and
    concurrent memory-hungry fleets have twice panicked this box (see CLAUDE.md
    'Machine limits'). Hitting either bound is a RECORDED OUTCOME — `timeout`
    or `memory-cap` — never a silent retry and never a pass."""
    t0 = time.monotonic()
    # The report goes to FILES, never to a pipe: a `clean check --json` report
    # over this package is far larger than a pipe buffer, and a parent that
    # polls RSS instead of draining the pipe deadlocks the child at ~64 KB.
    # Measured here: one file sat at 0% CPU until it was killed.
    with tempfile.TemporaryDirectory(prefix="ws612-run-") as tmp:
        outp, errp = Path(tmp) / "out", Path(tmp) / "err"
        with outp.open("wb") as fo, errp.open("wb") as fe:
            proc = subprocess.Popen(cmd, cwd=cwd, stdout=fo, stderr=fe)
            peak, killed = _rss_gb(proc.pid), None
            while proc.poll() is None:
                peak = max(peak, _rss_gb(proc.pid))
                if mem_cap_gb and peak > mem_cap_gb:
                    killed = "memory-cap"
                elif time.monotonic() - t0 > timeout:
                    killed = "timeout"
                if killed:
                    proc.kill()
                    break
                time.sleep(0.5)
            proc.wait()
        out = outp.read_text(encoding="utf-8", errors="replace")
        err = errp.read_text(encoding="utf-8", errors="replace")
    return out, err, proc.returncode, round(time.monotonic() - t0, 2), round(peak, 2), killed


def check_file(clean: Path, pkg: Path, rel: str, timeout: int, extra: list[str],
               mem_cap_gb: float = DEFAULT_MEM_CAP_GB) -> dict:
    cmd = [str(clean), "check", "--json", *extra, rel]
    stdout, stderr, code, secs, peak, killed = run_bounded(cmd, pkg, timeout, mem_cap_gb)
    mods = set(package_files(pkg))
    stdout, stderr = normalize_tags(stdout, mods), normalize_tags(stderr, mods)
    if killed:
        return {"file": rel, "module": module_of(rel), "status": killed, "seconds": secs,
                "peak_rss_gb": peak, "exit": None,
                "first_failure": (f"wall-clock bound {timeout}s exceeded" if killed == "timeout"
                                  else f"resident-memory bound {mem_cap_gb} GB exceeded "
                                       f"(peak {peak} GB)")}
    proc = CompletedRun(returncode=code, stdout=stdout, stderr=stderr)
    report = None
    try:
        report = json.loads(proc.stdout)
    except (json.JSONDecodeError, ValueError):
        report = None
    row = {"file": rel, "module": module_of(rel), "exit": proc.returncode, "seconds": secs,
           "peak_rss_gb": peak}
    if not report_is_well_formed(report):
        row.update(status="no-report", first_failure=first_failure(None, proc.stderr))
        return row
    row.update(report_row(report, proc.returncode, proc.stderr, module=module_of(rel)))
    return row


def report_is_well_formed(report: object) -> bool:
    """Validate the current report fields used to judge a file, never defaults.

    Clean emits these fields in CheckReport / CheckTrustSummary (cmd_core.rs).
    Additional metadata is allowed, but absent or wrongly typed verdict data
    is unjudged. In particular, bool is not an integer counter in this protocol.
    """
    if not isinstance(report, dict):
        return False
    if (report.get("schema_version") != "Clean-check-report-v2"
            or report.get("command") != "clean check"
            or report.get("status") not in ("pass", "fail", "diverged", "nothing_checked")):
        return False
    for key in ("decl_count", "success_count", "failed_count", "diverged_count"):
        value = report.get(key)
        if type(value) is not int or value < 0:
            return False
    summary = report.get("trust_summary")
    if not isinstance(summary, dict):
        return False
    for key in ("sorry_axioms", "kernel_check_failures"):
        value = summary.get(key)
        if type(value) is not int or value < 0:
            return False
    for key in ("errors", "trust_failures", "kernel_failures", "diverged", "parser_recovery"):
        value = report.get(key)
        if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
            return False
    return True


def report_passed(report: dict, returncode: int) -> bool:
    """Whether a `clean check --json` report is an UNQUALIFIED pass.

    Every field that could carry a refusal must be silent: the exit status,
    the verdict, the failed/diverged counts, Clean's own axiom census
    (`trust_summary.sorry_axioms` — a synthetic sorry minted by parser
    recovery counts, G13), its kernel failures, and every error list,
    inherited `[<module>]` rows included. A checker that reported `pass` while
    any of these was nonzero would otherwise be believed."""
    if not report_is_well_formed(report):
        return False
    ts = report.get("trust_summary") or {}
    return (returncode == 0 and report.get("status") == "pass"
            and report["success_count"] == report["decl_count"]
            and not report.get("failed_count") and not report.get("diverged_count")
            and not ts.get("sorry_axioms") and not ts.get("kernel_check_failures")
            and not report.get("errors") and not report.get("kernel_failures")
            and not report.get("trust_failures") and not report.get("diverged"))


def report_row(report: dict, returncode: int, stderr: str = "", module: str | None = None) -> dict:
    """Classify one file's report (pure; unit-tested without a binary).

    elaborated: the file AND its import closure check, nothing trusted.
    blocked:    every own declaration checked, but an import did not.
    failed:     at least one own declaration did not check."""
    if not report_is_well_formed(report):
        return {"status": "no-report", "first_failure": first_failure(None, stderr)}
    ts = report.get("trust_summary") or {}
    errors = report.get("errors") or []
    # `clean check` recursively elaborates intra-package imports from source
    # and reports their failures too, each prefixed `[<module>] `; its
    # decl/success counts are the checked file's OWN declarations. Split the
    # two, so a file is charged only with its own first failure. A row tagged
    # with the checked file's OWN module (`[<module>] …`, after
    # `normalize_tags`) is its own: an own failure must never read as
    # inherited, or a file whose only failing command is not counted as a
    # declaration (`#guard_msgs`, G09) would classify as `blocked`.
    def is_inherited(e: str) -> bool:
        return e.startswith("[") and not (module is not None and e.startswith(f"[{module}]"))

    own = [e for e in errors if not is_inherited(e)]
    inherited = [e for e in errors if is_inherited(e)]
    own_trust = [t for t in (report.get("trust_failures") or []) if not is_inherited(t)]
    row = dict(
        own_errors=own,
        inherited_error_count=len(inherited),
        first_own_failure=own[0] if own else None,
        first_inherited_failure=inherited[0] if inherited else None,
        own_trust_failures=own_trust,
        decl_count=report.get("decl_count"),
        success_count=report.get("success_count"),
        failed_count=report.get("failed_count"),
        diverged_count=report.get("diverged_count"),
        sorry_axioms=ts.get("sorry_axioms"),
        kernel_check_failures=ts.get("kernel_check_failures"),
        first_failure=first_failure(report, stderr),
    )
    if report_passed(report, returncode):
        row["status"] = "elaborated"
    # (`failed_count` counts inherited failures too — a blocked row has one
    # per failed import declaration — so it is not consulted here; `own` and
    # `success_count == decl_count` are what say the file's own body checked.)
    elif (not own and not own_trust and report.get("decl_count") is not None
          and report.get("success_count") == report.get("decl_count")
          and not report.get("diverged_count")
          and not ts.get("sorry_axioms") and not ts.get("kernel_check_failures")
          and not report.get("kernel_failures")):
        row["status"] = "blocked"
    else:
        row["status"] = "failed"
    return row


def clean_identity(clean: Path) -> str:
    try:
        out = subprocess.run([str(clean), "--version"], capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ProbeError(f"cannot run {clean}: {exc}") from exc
    return out.stdout.strip() or out.stderr.strip()


def run_census(clean: Path, pkg: Path, timeout: int, extra: list[str], only: list[str] | None = None,
               mem_cap_gb: float = DEFAULT_MEM_CAP_GB, clean_source: str | None = None,
               lean_options_source: str = "none") -> dict:
    files = package_files(pkg)
    graph = {m: imports_of((pkg / rel).read_text(encoding="utf-8")) for m, rel in files.items()}
    order = import_order(graph)
    rows = []
    for mod in order:
        if only and files[mod] not in only:
            continue
        row = check_file(clean, pkg, files[mod], timeout, extra, mem_cap_gb)
        row["imports"] = [d for d in graph[mod] if d in files]
        rows.append(row)
        print(f"{row['status']:>10}  {row['seconds']:>8}s  {files[mod]}  {row.get('first_own_failure') or row.get('first_failure') or ''}"[:240],
              file=sys.stderr, flush=True)
    src = source_axiom_census(pkg)
    clean_sorry = sum(r.get("sorry_axioms") or 0 for r in rows)
    elaborated = [r["file"] for r in rows if r["status"] == "elaborated"]
    # A census restricted with --only is a debugging aid, not a measurement
    # of the package: readiness is decided over EVERY file, so a run over the
    # six files that elaborate can never claim it.
    complete = len(rows) == len(files)
    return {
        "schema": SCHEMA,
        "clean": clean_identity(clean),
        # `clean --version` prints a package version, not an identity; the
        # commit the binary was built from is recorded here from --clean-source
        # (None = NOT RECORDED, never "unknown but fine").
        "clean_source": clean_source,
        "clean_args": extra,
        # Where `clean_args`' `-D` overrides came from: the package lakefile's
        # `leanOptions` ("lakefile"), `--lean-option` ("cli"), or "none".
        "lean_options_source": lean_options_source,
        "mem_cap_gb": mem_cap_gb,
        "files": rows,
        "summary": {
            "files": len(rows),
            "package_files": len(files),
            "complete": complete,
            "elaborated": len(elaborated),
            "failed": sum(r["status"] == "failed" for r in rows),
            "blocked": sum(r["status"] == "blocked" for r in rows),
            "timeout": sum(r["status"] == "timeout" for r in rows),
            "memory_cap": sum(r["status"] == "memory-cap" for r in rows),
            "peak_rss_gb": max((r.get("peak_rss_gb") or 0.0) for r in rows) if rows else 0.0,
            "no_report": sum(r["status"] == "no-report" for r in rows),
            "decls": sum(r.get("decl_count") or 0 for r in rows),
            "decls_ok": sum(r.get("success_count") or 0 for r in rows),
            "seconds": round(sum(r["seconds"] for r in rows), 2),
        },
        "axiom_census": {
            "source": src,
            "clean_sorry_axioms_total": clean_sorry,
        },
        # The ONLY condition under which Lean 4.8 + lake could stop being the
        # authority. Reported, never acted on.
        "authority_transfer_ready": (complete and len(elaborated) == len(rows) and bool(rows)
                                     and src["matches"] and clean_sorry == 0),
    }


# --------------------------------------------------------------------------
# Controls
# --------------------------------------------------------------------------

NEGATIVE_TWIN_TEXT = (
    "\n-- WS6.12 negative twin: a deliberately FALSE theorem. `clean check` must\n"
    "-- refuse this file, naming this declaration.\n"
    f"theorem {NEGATIVE_TWIN_DECL} : (1 : Nat) = 2 := rfl\n"
)


def negative_twin(clean: Path, pkg: Path, rel: str, timeout: int, extra: list[str],
                  mem_cap_gb: float = DEFAULT_MEM_CAP_GB) -> dict:
    base = check_file(clean, pkg, rel, timeout, extra, mem_cap_gb)
    path = pkg / rel
    path.write_text(path.read_text(encoding="utf-8") + NEGATIVE_TWIN_TEXT, encoding="utf-8")
    twin = check_file(clean, pkg, rel, timeout, extra, mem_cap_gb)
    named = any(NEGATIVE_TWIN_DECL in e for e in twin.get("own_errors", []))
    refused = twin["status"] != "elaborated" and twin.get("exit") not in (0, None)
    # Non-vacuity: the twin must lose exactly the injected declaration relative
    # to the unbroken file; everything the baseline accepted must still count.
    ok_delta = (base.get("success_count") is not None
                and twin.get("success_count") == base.get("success_count")
                and twin.get("failed_count") == (base.get("failed_count") or 0) + 1)
    return {"file": rel, "baseline": base, "twin": twin, "refused": refused,
            "names_injected_decl": named, "delta_is_exactly_the_twin": ok_delta,
            "pass": refused and named and ok_delta}


def inject_sorry(pkg: Path, rel: str = MUTATION_TARGET_FILE,
                 theorem: str = MUTATION_TARGET_THEOREM) -> str:
    """Replace the tactic proof of `theorem` in `rel` with `sorry`.

    The defaults name the AxiomAudit-audited `ay_sound_contrapositive`, whose
    `#guard_msgs` census is what turns the Lean 4.8 authority red. Returns the
    mutated file."""
    path = pkg / rel
    src = path.read_text(encoding="utf-8")
    start = src.find(f"theorem {theorem} ")
    if start < 0:
        raise ProbeError(f"{theorem} not found in {rel}")
    by = src.find(":= by", start)
    end = src.find("\n\n", by)
    if by < 0 or end < 0:
        raise ProbeError(f"cannot locate the proof body of {theorem}")
    path.write_text(src[:by] + ":= by\n  sorry" + src[end:], encoding="utf-8")
    return rel


def lean_authority_build(lean_pkg: Path, timeout: int) -> dict:
    lake = shutil.which("lake")
    if not lake:
        raise ProbeError("`lake` not on PATH (Lean 4.8.0 via elan)")
    t0 = time.monotonic()
    try:
        proc = subprocess.run([lake, "build"], cwd=lean_pkg, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"exit": None, "seconds": round(time.monotonic() - t0, 2), "axiom_audit_red": False,
                "tail": "timeout"}
    out = proc.stdout + proc.stderr
    red = proc.returncode != 0 and "AxiomAudit" in out and "sorryAx" in out
    tail = mask_paths("\n".join(out.strip().splitlines()[-12:]), lean_pkg)
    return {"exit": proc.returncode, "seconds": round(time.monotonic() - t0, 2),
            "axiom_audit_red": red, "tail": tail}


def mutation_control(clean: Path, pkg: Path, timeout: int, extra: list[str], lean_pkg: Path | None,
                     mem_cap_gb: float = DEFAULT_MEM_CAP_GB) -> dict:
    """Two injections, one per side of the census.

    Clean side: a theorem Clean CURRENTLY checks (so the control is not
    vacuous — a sorry inside a declaration that already fails to elaborate
    proves nothing) loses its proof; Clean must stop counting the file as
    elaborated and name the placeholder. Source side: the census must flag the
    token. Lean side (optional): the AxiomAudit-audited theorem loses its
    proof and the Lean 4.8 `#guard_msgs` gate must go red on `sorryAx`."""
    before = source_axiom_census(pkg)
    baseline = check_file(clean, pkg, CLEAN_MUTATION_FILE, timeout, extra, mem_cap_gb)
    rel = inject_sorry(pkg, CLEAN_MUTATION_FILE, CLEAN_MUTATION_THEOREM)
    after = source_axiom_census(pkg)
    flagged_src = (before["matches"] and not after["matches"]
                   and [(p["file"], p["token"]) for p in after["placeholders"]] == [(rel, "sorry")])
    row = check_file(clean, pkg, rel, timeout, extra, mem_cap_gb)
    baseline_ok = baseline["status"] == "elaborated" and not baseline.get("sorry_axioms")
    flagged_clean = (row["status"] != "elaborated"
                     and ((row.get("sorry_axioms") or 0) > 0
                          or any(CLEAN_MUTATION_THEOREM in e and "sorry" in e.lower()
                                 for e in row.get("own_errors", []))))
    result = {"file": rel, "theorem": CLEAN_MUTATION_THEOREM,
              "source_census_before_matches": before["matches"],
              "source_census_flags_sorry": flagged_src,
              "clean_baseline": baseline, "clean_baseline_elaborated": baseline_ok,
              "clean_check": row, "clean_flags_sorry": flagged_clean}
    ok = flagged_src and baseline_ok and flagged_clean
    if lean_pkg is not None:
        inject_sorry(lean_pkg)
        lean = lean_authority_build(lean_pkg, timeout)
        lean["file"], lean["theorem"] = MUTATION_TARGET_FILE, MUTATION_TARGET_THEOREM
        result["lean_authority"] = lean
        ok = ok and lean["axiom_audit_red"]
    result["pass"] = ok
    return result


# --------------------------------------------------------------------------
# The census table (rendered from the artifact, never hand-typed)
# --------------------------------------------------------------------------

def render_table(census: dict) -> str:
    sm, ax = census["summary"], census["axiom_census"]
    src = ax["source"]
    lines = [
        "# trust-ir semantics under `clean check` — the census table",
        "",
        "Generated by `trust_ir_semantics_probe.py table`; do not hand-edit. "
        "Regenerate from `census.json` after every re-run.",
        "",
        f"- checker: `{census['clean']}` built from "
        f"{('`' + census['clean_source'] + '`') if census.get('clean_source') else 'a commit that was NOT RECORDED'}",
        f"- files: {sm['files']}"
        + (f" of {sm['package_files']} in the package" if "package_files" in sm else "")
        + (" — **PARTIAL run (`--only`): not a measurement of the package**"
           if sm.get("complete") is False else "")
        + f" | elaborated: {sm['elaborated']} | blocked (an import "
        f"failed): {sm['blocked']} | failed: {sm['failed']} | memory-cap: "
        f"{sm['memory_cap']} | timeout: {sm['timeout']}",
        f"- own declarations checked: {sm['decls_ok']} of {sm['decls']} "
        "(counted only for files that produced a report)",
        f"- `clean check` arguments: "
        f"{' '.join('`' + a + '`' for a in census.get('clean_args') or []) or 'none'}"
        f" (source: {census.get('lean_options_source', 'not recorded')})",
        f"- wall: {sm['seconds']} s | worst per-file resident set: {sm['peak_rss_gb']} GB "
        f"(bound {census.get('mem_cap_gb')} GB)",
        f"- axiom census (source): first-party axioms "
        f"{sorted(a['name'] for a in src['first_party_axioms'])}, "
        f"proof placeholders {len(src['placeholders'])}, "
        f"`native_decide` sites {src['evaluator_sites']} (Lean-core `ofReduceBool`, "
        "outside the first-party census) — matches: "
        f"{str(src['matches']).lower()}",
        f"- axiom census (Clean): `sorry_axioms` reported across files: "
        f"{ax['clean_sorry_axioms_total']}",
        "",
        f"**`authority_transfer_ready`: {str(census['authority_transfer_ready']).lower()}** "
        "— Lean 4.8.0 + lake remains the authority.",
        "",
        "| # | file | status | own ok / decls | inherited errs | s | peak GB | first own failure |",
        "|---|---|---|---|---|---|---|---|",
    ]
    for i, r in enumerate(census["files"], 1):
        fail = (r.get("first_own_failure") or r.get("first_failure") or "")
        fail = re.sub(r"\s+", " ", fail)[:110].replace("|", "\\|")
        ok = "-" if r.get("success_count") is None else f"{r['success_count']} / {r['decl_count']}"
        lines.append(
            f"| {i} | `{r['file']}` | {r['status']} | {ok} | "
            f"{r.get('inherited_error_count', '-')} | {r['seconds']} | "
            f"{r.get('peak_rss_gb', '-')} | {fail} |")
    return "\n".join(lines) + "\n"


# --------------------------------------------------------------------------
# Filed elaborator gaps: each minimized repro must STILL fail, as filed
# --------------------------------------------------------------------------

def lean_toolchain_lib(toolchain: str) -> Path:
    """`lib/lean` of an INSTALLED elan toolchain named exactly
    (`leanprover/lean4:v4.8.0`), under `$ELAN_HOME` or `~/.elan`. Never runs
    elan and never answers with another version: a missing toolchain is a
    ProbeError, not a skip."""
    if "/" not in toolchain or ":" not in toolchain:
        raise ProbeError(f"`lean_toolchain` must be `<org>/<repo>:<version>`, got {toolchain!r}")
    directory = toolchain.replace("/", "--").replace(":", "---")
    roots = [Path(os.environ["ELAN_HOME"])] if os.environ.get("ELAN_HOME") else []
    roots.append(Path.home() / ".elan")
    for root in roots:
        lib = root / "toolchains" / directory / "lib" / "lean"
        if (lib / "Init" / "Prelude.olean").is_file():
            return lib
    raise ProbeError(f"Lean toolchain {toolchain} is not installed (looked under {roots})")


def _check_repro(clean: Path, cwd: Path, entry: str, timeout: int,
                 clean_args: list[str] | None = None,
                 lean_toolchain: str | None = None) -> tuple:
    """(failed, report_text, exit) for one repro, or (None, outcome, exit)
    when nothing could be judged (`timeout` / `no-report`). `clean_args` is the
    row's own `clean check` arguments (a `-D` override for a gap that only
    shows under the package's `leanOptions`, G50). `lean_toolchain` puts that
    toolchain's `lib/lean` first on `LEAN_PATH`, so an `import Lean.*` resolves
    against the toolchain the package pins (trust-ir: v4.8.0) and not against
    Clean's own checkout pin (G33, G71)."""
    cmd = [str(clean), "check", "--json", *(clean_args or []), entry]
    env = None
    if lean_toolchain:
        env = dict(os.environ)
        lib = str(lean_toolchain_lib(lean_toolchain))
        env["LEAN_PATH"] = lib + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    try:
        proc = subprocess.run(cmd, cwd=cwd, capture_output=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        return None, "timeout", None
    try:
        # Decode after retaining the completed process, so malformed UTF-8 in
        # either stream is unjudged and still records the checker's exit code.
        # Keep both streams strict UTF-8, matching the former text=True contract.
        stdout = proc.stdout.decode("utf-8")
        proc.stderr.decode("utf-8")
        report = json.loads(stdout)
    except ValueError:
        return None, "no-report", proc.returncode
    # Verdicts require a complete, typed current report, including refusals.
    if not report_is_well_formed(report):
        return None, "no-report", proc.returncode
    text = "\n".join(str(x) for key in ("errors", "trust_failures", "kernel_failures", "diverged")
                     for x in (report.get(key) or []))
    # A repro "passes" only on an UNQUALIFIED pass (`report_passed`): a
    # `pass` verdict that still carries a sorry, a kernel failure or an error
    # row is a refusal for the ratchet. This is what keeps a PASS row honest
    # against a checker that accepts a file by minting a synthetic sorry.
    return not report_passed(report, proc.returncode), text, proc.returncode


def validate_repro_manifest(spec: object) -> list[dict]:
    """Validate every row before any checker or version command can run."""
    gaps = spec.get("gaps") if isinstance(spec, dict) else None
    if not isinstance(gaps, list) or not gaps:
        raise ProbeError("repro manifest `gaps` must be a non-empty list")
    seen = set()
    for index, gap in enumerate(gaps):
        if not isinstance(gap, dict):
            raise ProbeError(f"repro row {index}: expected an object")
        for key in ("id", "entry"):
            if not isinstance(gap.get(key), str) or not gap[key] or "\x00" in gap[key]:
                raise ProbeError(f"repro row {index}: `{key}` must be a non-empty string without NUL")
        name = gap["id"]
        if name in seen:
            raise ProbeError(f"duplicate repro id {name!r}")
        seen.add(name)
        for key in ("cwd", "closed_by", "lean_toolchain"):
            if key in gap and (not isinstance(gap[key], str) or not gap[key] or "\x00" in gap[key]):
                raise ProbeError(f"{name}: `{key}` must be a non-empty string without NUL")
        if "closed_by" in gap and (not isinstance(gap.get("twin"), str)
                                  or not gap["twin"] or "\x00" in gap["twin"]):
            raise ProbeError(f"{name}: a closed_by row needs a non-empty string `twin` without NUL")
        # A filed signature distinguishes a refusal for the intended reason.
        # Validate late rows and regex syntax before spending time on earlier ones.
        for key in (("twin_expect",) if "closed_by" in gap else ("expect",)):
            if not isinstance(gap.get(key), str) or not gap[key]:
                raise ProbeError(f"{name}: `{key}` must be a non-empty filed signature")
            try:
                re.compile(gap[key], re.MULTILINE)
            except re.error as exc:
                raise ProbeError(f"{name}: invalid `{key}` regex: {exc}") from exc
        args = gap.get("clean_args", [])
        if not isinstance(args, list) or not all(isinstance(arg, str) and "\x00" not in arg for arg in args):
            raise ProbeError(f"{name}: `clean_args` must be a list of strings without NUL")
    return gaps


def run_repros(clean: Path, manifest: Path, timeout: int, clean_source: str | None = None) -> dict:
    """Re-run every filed repro against its filed row.

    An OPEN row (no `closed_by`) is `still-fails` only when `clean check`
    refuses it AND the refusal matches the filed signature; `closed` (it now
    passes) and `changed` (it fails for another reason) both fail the run, so
    the day a gap closes the tracker entry cannot silently go stale.

    A row with `closed_by` is a PASS row (ratchet convention: a closure is
    recorded as "closed upstream by <commit>" and ported as a PASS row with a
    right-reason negative twin): its entry must PASS (`still-passes`) and its
    `twin` must FAIL matching `twin_expect` (`twin-refused`); `regressed` (the
    entry fails again) and `twin-accepted` / `twin-changed` (the twin passes,
    or fails for the wrong reason) fail the run."""
    spec = json.loads(manifest.read_text(encoding="utf-8"))
    gaps = validate_repro_manifest(spec)
    base = manifest.parent
    rows = []
    # Establish every declared import world before starting any checker. A
    # late row must not discover a missing pinned library after minutes of
    # unrelated successful probes. The per-row lookup remains authoritative
    # when that row runs, so disappearance after preflight still refuses.
    checked_toolchains: set[str] = set()
    for gap in gaps:
        toolchain = gap.get("lean_toolchain")
        if toolchain is not None and toolchain not in checked_toolchains:
            lean_toolchain_lib(toolchain)
            checked_toolchains.add(toolchain)
    for gap in gaps:
        cwd = base / gap.get("cwd", ".")
        # Optional, additive: arguments the row is checked under (entry and
        # twin alike), e.g. `-DautoImplicit=false` for a lakefile option.
        row_args = gap.get("clean_args", [])
        row_toolchain = gap.get("lean_toolchain")
        failed, text, code = _check_repro(clean, cwd, gap["entry"], timeout, row_args,
                                          row_toolchain)
        if failed is None:
            rows.append({"id": gap["id"], "outcome": text, "exit": code})
            continue
        first = text.splitlines()[0][:300] if text else None
        row = {"id": gap["id"], "exit": code,
               # the repro corpus lives under a path that differs per machine,
               # and G14's own signature IS a path-derived tag; the filed
               # signature is `expect`, not this echo
               "first": mask_paths(first, base) if first else None}
        if row_args:
            row["clean_args"] = row_args
        if row_toolchain:
            row["lean_toolchain"] = row_toolchain
        if gap.get("closed_by"):
            row["closed_by"] = gap["closed_by"]
            if failed:
                row["outcome"] = "regressed"
            else:
                tfailed, ttext, tcode = _check_repro(clean, cwd, gap["twin"], timeout, row_args,
                                                     row_toolchain)
                tfirst = ttext.splitlines()[0][:300] if ttext else None
                row["twin"] = {"entry": gap["twin"], "exit": tcode,
                               "first": mask_paths(tfirst, base) if tfirst else None}
                if tfailed is None:
                    row["outcome"] = ttext
                elif not tfailed:
                    row["outcome"] = "twin-accepted"
                elif re.search(gap["twin_expect"], ttext, re.MULTILINE) is None:
                    row["outcome"] = "twin-changed"
                else:
                    row["outcome"] = "still-passes"
        else:
            matched = re.search(gap["expect"], text, re.MULTILINE) is not None
            row["outcome"] = "closed" if not failed else ("still-fails" if matched else "changed")
        rows.append(row)
    return {"schema": SCHEMA + "-repros", "clean": clean_identity(clean),
            "clean_source": clean_source, "repros": rows,
            "open": sum("closed_by" not in r for r in rows),
            "closed_upstream": sum("closed_by" in r for r in rows),
            "pass": all(r["outcome"] in ("still-fails", "still-passes") for r in rows)}


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p):
        p.add_argument("--clean", required=True, type=Path, help="the `clean` binary under test")
        p.add_argument("--clean-source", help="the commit the binary was built from (recorded in-band)")
        p.add_argument("--package", required=True, type=Path,
                       help="a trust-ir lean/trust_ir-semantics tree (read only; copied first)")
        p.add_argument("--work", type=Path, help="scratch root for the copy (default: a temp dir)")
        p.add_argument("--timeout", type=int, default=1800, help="per-file wall bound, seconds")
        p.add_argument("--mem-cap-gb", type=float, default=DEFAULT_MEM_CAP_GB,
                       help="per-file resident-memory bound, GB (0 disables; see run_bounded)")
        p.add_argument("--out-json", type=Path)
        p.add_argument("--lean-option", action="append", metavar="NAME=VALUE",
                       help="a `-D` override for every `clean check` (repeatable); when "
                            "absent, the package lakefile's `leanOptions` (Lake compiles "
                            "every module with them)")

    c = sub.add_parser("census")
    common(c)
    c.add_argument("--only", action="append", help="restrict to these relative paths (debugging)")
    n = sub.add_parser("negative-twin")
    common(n)
    n.add_argument("--file", default="TrustIr/CastOp.lean")
    t = sub.add_parser("table")
    t.add_argument("--census", required=True, type=Path)
    t.add_argument("--out-md", required=True, type=Path)
    r = sub.add_parser("repros")
    r.add_argument("--clean", required=True, type=Path)
    r.add_argument("--clean-source", help="the commit the binary was built from (recorded in-band)")
    r.add_argument("--manifest", required=True, type=Path)
    r.add_argument("--timeout", type=int, default=300)
    r.add_argument("--out-json", type=Path)
    m = sub.add_parser("mutation-control")
    common(m)
    m.add_argument("--lean-authority", type=Path,
                   help="a BUILT Lean 4.8 copy of the package; it is mutated in place and rebuilt")
    args = ap.parse_args(argv)

    if args.cmd == "table":
        # Pure rendering of an existing artifact: no binary, no package.
        args.out_md.write_text(render_table(json.loads(args.census.read_text(encoding="utf-8"))),
                               encoding="utf-8")
        return 0
    if not args.clean.is_file():
        print(f"error: no clean binary at {args.clean}", file=sys.stderr)
        return 2
    clean = args.clean.resolve()
    if args.cmd == "repros":
        try:
            result = run_repros(clean, args.manifest.resolve(), args.timeout, args.clean_source)
        except ProbeError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 2
        text = json.dumps(result, indent=2, sort_keys=True) + "\n"
        if args.out_json:
            args.out_json.write_text(text, encoding="utf-8")
        else:
            sys.stdout.write(text)
        return 0 if result["pass"] else 1
    work_ctx = tempfile.TemporaryDirectory(prefix="ws612-") if args.work is None else None
    work = Path(work_ctx.name) if work_ctx else args.work
    try:
        if args.work is not None:
            work.mkdir(parents=True, exist_ok=True)
            shutil.rmtree(work / "pkg", ignore_errors=True)
        pkg = copy_package(args.package.resolve(), work)
        if args.lean_option is not None:
            options, options_source = list(args.lean_option), "cli"
        else:
            options = lakefile_lean_options(pkg)
            options_source = "lakefile" if options else "none"
        extra = clean_define_args(options)
        if args.cmd == "census":
            result = run_census(clean, pkg, args.timeout, extra, args.only, args.mem_cap_gb,
                                args.clean_source, options_source)
            ok = True
        elif args.cmd == "negative-twin":
            result = negative_twin(clean, pkg, args.file, args.timeout, extra, args.mem_cap_gb)
            result["clean"], result["clean_source"] = clean_identity(clean), args.clean_source
            result["clean_args"] = extra
            ok = result["pass"]
        else:
            lean_pkg = args.lean_authority.resolve() if args.lean_authority else None
            result = mutation_control(clean, pkg, args.timeout, extra, lean_pkg, args.mem_cap_gb)
            result["clean"], result["clean_source"] = clean_identity(clean), args.clean_source
            result["clean_args"] = extra
            ok = result["pass"]
        text = json.dumps(result, indent=2, sort_keys=True) + "\n"
        if args.out_json:
            args.out_json.write_text(text, encoding="utf-8")
        else:
            sys.stdout.write(text)
        return 0 if ok else 1
    except ProbeError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    finally:
        if work_ctx:
            work_ctx.cleanup()


if __name__ == "__main__":
    sys.exit(main())
