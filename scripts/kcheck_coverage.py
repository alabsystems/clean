#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Which real Lean declarations the adopted checker `kcheck` accepts (step K3).

Step K3 of the interim thread of docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md
(choices: docs/DECISIONS.md, 2026-11-15, "W4/W5 interim thread"). The record
`data/kcheck_coverage.json` is minted from one run of `kcheck-run-interim`
(theories/kcheck_run) over a tracked lean4export export and a tracked advice
file, and it is refused unless a second reader agrees with that run.

WHAT THE RECORD SAYS. `accepted` real declarations were accepted by `kcheck`.
Every figure carries its labels: the run claims NO SOUNDNESS (a soundness
theorem for the checker, where source has one, is the scoreboard's line; the
entry point run here is that checker's `kcheck` by definition, and nothing
shown ties the compiled executable to it), the executable is built by upstream Lean,
the loader is interim and unproved, and NO SITE consults the run: `real_declarations_decided` is 0 here by construction and
only a site record (steps K4b and K5) can raise it.

WHAT --check ESTABLISHES, with no Lean toolchain:
  * the record is, byte for byte, the one spelling --write gives a re-derivation
    (so a repeated key or a `false` standing for 0 is refused);
  * the tracked export, advice and transcript are the bytes the record names;
  * the transcript is well formed and has one row per declaration record;
  * the fragment class of every row agrees with a classifier that shares no
    code with the Lean loader (scripts/kcheck_fragment_census.py), so the run
    did not choose which declarations the checker decides;
  * every accepted row's name and statement echo equal a rendering made here
    from the raw export, so what the checker was handed is what the export
    states (as far as the echo grammar shows: no binder names, no annotations);
  * an accepted row cites no in-fragment declaration the run did not accept,
    and a row refused for a dependency names one;
  * the advice splits into one frame per declaration record and is empty off
    the fragment; the record's counts are a re-count;
  * `sources` is exactly the set of files the executable is built from: the
    import closure of the package's build roots over the five theory packages,
    read from the Lean files' headers with comments blanked, plus each
    package's build files. A record cannot list fewer files to stay fresh.
WHAT IT DOES NOT: that the transcript was printed by the checker at the recorded
sources. `--replay` rebuilds the executable from the tree and requires the same
bytes. Exit 3 means one of two things only: there is no record, or a recorded
source has moved since the run. Then the figure reads ABSENT on the scoreboard
until someone re-mints it. Every other defect is exit 1.

  scripts/kcheck_coverage.py --check                 # 0 ok, 1 refused, 3 stale or absent
  scripts/kcheck_coverage.py --replay                # rebuild, rerun, same bytes, then --check
  scripts/kcheck_coverage.py --write --advice-origin "<command that emitted the advice>"
  scripts/kcheck_coverage.py --self-test
  scripts/kcheck_coverage.py --pinned-inputs         # the scripts this one runs (gate registry, R7)
"""

from __future__ import annotations

import argparse
import gzip
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import zlib
from pathlib import Path

ANSWERS_PINNED_INPUTS = True

SCRIPTS = Path(__file__).resolve().parent
CENSUS = "scripts/kcheck_fragment_census.py"
READERS = "scripts/kcheck_coverage_readers.py"
EXPORT_READER = "scripts/kcheck_coverage_export.py"
SELFTEST = "scripts/kcheck_coverage_selftest.py"
# The tree the record and its inputs are read from. The self-test points it at a scratch tree.
ROOT = SCRIPTS.parent
RECORD = "data/kcheck_coverage.json"
EXPORT = "crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/lean4export_minted/prelude_roots.ndjson.gz"
ADVICE = "data/kcheck_coverage/prelude_roots.advice.bin"
TRANSCRIPT = "data/kcheck_coverage/prelude_roots.transcript.txt"
PACKAGES = ("cic_l", "cic_l_model", "kcheck_spec", "kcheck_labelled", "kcheck_run")
PACKAGE_FILES = ("lakefile.toml", "lakefile.lean", "lean-toolchain", "lake-manifest.json")
# What `lake build` in theories/kcheck_run compiles: the roots of its lakefile's default targets.
BUILD_ROOTS = ("KCheckRun", "KCheckRunMain")
IMPORT = re.compile(r"(?m)^[ \t]*(?:(?:public|private)[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?(\S+)")
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
SHA256 = re.compile(r"[0-9a-f]{64}")
# The build goes through the memory gate. The self-test, whose `lake` is a stand-in, empties this.
GATE = (str(SCRIPTS / "heavy_gate.sh"), "run", "auto:lean-kcheck-run:6", "lean-kcheck-run", "--")
RUN_KEYS = ("command", "executable_sha256", "lean_toolchain", "lean_version")
STALE_ABSENT = f"{RECORD} does not exist"
STALE_MOVED = "the Lean sources of the recorded run have moved; re-mint with scripts/kcheck_coverage.py --write"
LABELS = {
    "checker": "kcheck_labelled, KCheck.kcheckBytes (by definition KCheck.checker's kcheck from Advice.start of the frame); this run claims NO soundness: "
               "whether a theorem of KCheckSpec.C3Owes KCheck.checker is in source is the scoreboard's checker-soundness line, and nothing shown ties "
               "the executable upstream Lean compiled to the term that theorem is about",
    "compiled_by": "upstream Lean (lake build under the pinned toolchain); not Clean, not Trust",
    "loader": "interim, unproved; an inductive record's recursor and rules are compared with the base family by the loader, never checked by kcheck",
    "site": "none: no acceptance of clean or Trust consults this run",
}


def sibling(name: str):
    """A script beside this one, loaded by path so that nothing depends on sys.path."""
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


readers = sibling("kcheck_coverage_readers")
Refused, derive, sha, HEADERS = readers.Refused, readers.derive, readers.sha, readers.HEADERS


class Stale(Exception):
    """There is no record, or a source it was minted from has moved. `reason` is one of two fixed texts."""

    def __init__(self, reason: str, detail: str = "") -> None:
        super().__init__(f"{reason} ({detail})" if detail else reason)
        self.reason = reason


def verdicts(run):
    """`run`, with anything that is not a verdict turned into a refusal: a traceback is never an answer."""
    def guarded(*args, **kwargs):
        try:
            return run(*args, **kwargs)
        except (Refused, Stale):
            raise
        except Exception as err:  # noqa: BLE001 - fail closed on whatever was not foreseen
            text = str(err).encode("ascii", "backslashreplace").decode("ascii")[:300]
            raise Refused(f"{run.__name__} could not finish: {type(err).__name__}: {text}") from err
    return guarded


def build_record(export_gz: bytes, advice: bytes, transcript: bytes, sources: dict[str, str], run: dict, advice_origin: str) -> dict:
    """The record for these bytes. Anything malformed in them is Refused, never a traceback."""
    try:
        export_raw = gzip.decompress(export_gz)
        figures = derive(export_raw, advice, transcript.decode("utf-8"))
    except (OSError, EOFError, zlib.error, ValueError, KeyError, TypeError, IndexError, AttributeError, RecursionError) as err:
        raise Refused(f"the export, the advice or the transcript cannot be read as what it is: {type(err).__name__}: {err}") from err
    return {
        "schema": "clean.kcheck_coverage.v1",
        "what_this_is": (
            "Step K3 of the interim thread of docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md: the real "
            "declarations the adopted checker accepts in one run of theories/kcheck_run, re-derived by "
            "scripts/kcheck_coverage.py. An accepted declaration is not a proved one and decides no site."
        ),
        "labels": LABELS,
        "real_declarations_decided": 0,
        "real_declarations_decided_reason": "no site consults the run; steps K4b and K5 of the interim thread owe the first one",
        "export": {"path": EXPORT, "sha256_file": sha(export_gz), "sha256_decompressed": sha(export_raw)},
        "advice": {"path": ADVICE, "sha256": sha(advice), "origin": advice_origin},
        "transcript": {"path": TRANSCRIPT, "sha256": sha(transcript)},
        "figures": figures,
        "run": run,
        "sources": sources,
    }


def serialize(record: dict) -> str:
    return json.dumps(record, indent=2, sort_keys=True) + "\n"


def blank_noncode_lean(text: str) -> str:
    """Blank Lean comments and string literals, keeping every newline, so a commented `import` is not followed."""
    out = []
    i, n, depth, in_string = 0, len(text), 0, False
    while i < n:
        two, ch = text[i:i + 2], text[i]
        if depth:
            depth += 1 if two == "/-" else -1 if two == "-/" else 0
            step = 2 if two in ("/-", "-/") else 1
            out.append("  " if step == 2 else "\n" if ch == "\n" else " ")
            i += step
        elif in_string:
            if ch == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
            else:
                in_string = ch != '"'
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif two == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif two == "--":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            in_string = ch == '"'
            out.append(" " if in_string else ch)
            i += 1
    return "".join(out)


def required_sources(root: Path | None = None) -> set[str]:
    """The files the executable is built from, found with no Lean toolchain: the import closure of
    BUILD_ROOTS over PACKAGES plus each package's build files. A module no package holds is the toolchain's."""
    root = ROOT if root is None else root
    def locate(module: str) -> str | None:
        tail = module.replace(".", "/") + ".lean"
        hits = [f"theories/{package}/{tail}" for package in PACKAGES if (root / "theories" / package / tail).is_file()]
        if len(hits) > 1:
            raise Refused(f"module {module} is in more than one package: {hits}")
        return hits[0] if hits else None

    seen: set[str] = set()
    todo = list(BUILD_ROOTS)
    while todo:
        rel = locate(todo.pop())
        if rel is None or rel in seen:
            continue
        seen.add(rel)
        for module in IMPORT.findall(blank_noncode_lean((root / rel).read_text(encoding="utf-8"))):
            if not MODULE_NAME.fullmatch(module):
                raise Refused(f"{rel} imports `{module}`, a name this reader does not follow")
            todo.append(module)
    for module in BUILD_ROOTS:
        if locate(module) not in seen:
            raise Refused(f"theories/kcheck_run has no module {module}")
    return seen | {f"theories/{package}/{name}" for package in PACKAGES for name in PACKAGE_FILES if (root / "theories" / package / name).is_file()}


def sources_refusal(sources, required: set[str]) -> str | None:
    """Why `sources` is not the list of files the executable is built from, each with a sha256."""
    if not isinstance(sources, dict):
        return "`sources` is not a map"
    for rel, digest in sources.items():
        if not rel.startswith("theories/") or ".." in rel.split("/") or "" in rel.split("/"):
            return f"`sources` names {rel!r}, which is not a path under theories/"
        if not (isinstance(digest, str) and SHA256.fullmatch(digest)):
            return f"`sources` gives {rel} no sha256"
    missing, extra = sorted(required - set(sources)), sorted(set(sources) - required)
    if missing:
        return f"`sources` omits {len(missing)} file(s) the executable is built from (first: {missing[0]})"
    if extra:
        return f"`sources` lists {len(extra)} file(s) the executable is not built from (first: {extra[0]})"
    return None


def pinned_toolchain(root: Path) -> str:
    return (root / "theories" / "kcheck_run" / "lean-toolchain").read_text(encoding="utf-8").strip()


def read_inputs(root: Path | None = None) -> tuple[bytes, bytes, bytes]:
    """The three tracked files a record names. A record that is there and names a file that is not is refused."""
    root = ROOT if root is None else root
    for rel in (EXPORT, ADVICE, TRANSCRIPT):
        if not (root / rel).is_file():
            raise Refused(f"{RECORD} names {rel}, which does not exist")
    return (root / EXPORT).read_bytes(), (root / ADVICE).read_bytes(), (root / TRANSCRIPT).read_bytes()


@verdicts
def check(root: Path | None = None) -> dict:
    root = ROOT if root is None else root
    if not (root / RECORD).is_file():
        raise Stale(STALE_ABSENT)
    try:
        text = (root / RECORD).read_bytes().decode("utf-8")
        record = json.loads(text)
        sources, run, origin = record["sources"], record["run"], record["advice"]["origin"]
    except (ValueError, KeyError, TypeError, RecursionError) as err:
        raise Refused(f"{RECORD} is not a coverage record: {type(err).__name__}: {err}") from err
    # What needs no input file is judged first, so a record that claims a site is refused whatever else is missing.
    decided = record.get("real_declarations_decided")
    if type(decided) is not int or decided != 0:
        raise Refused(f"{RECORD} states real_declarations_decided = {decided!r}; a coverage record states 0, and only a site record can raise the figure")
    if record.get("labels") != LABELS:
        raise Refused(f"{RECORD}'s labels are not the ones this script writes")
    if not (isinstance(origin, str) and origin.strip() and origin == origin.strip()):
        raise Refused(f"{RECORD} names no producer of the advice (advice.origin)")
    if not (isinstance(run, dict) and tuple(sorted(run)) == RUN_KEYS and all(isinstance(run[k], str) and run[k] for k in RUN_KEYS)):
        raise Refused(f"{RECORD}'s run is not the four facts of a run: {', '.join(RUN_KEYS)}")
    if not SHA256.fullmatch(run["executable_sha256"]):
        raise Refused(f"{RECORD}'s run gives the executable no sha256")
    if not isinstance(sources, dict):
        raise Refused(f"{RECORD}: `sources` is not a map")
    bad = next((rel for rel in sources if not isinstance(rel, str) or not rel.startswith("theories/") or ".." in rel.split("/")), None)
    if bad is not None:
        raise Refused(f"{RECORD}: `sources` names {bad!r}, which is not a path under theories/")
    export_gz, advice, transcript = read_inputs(root)
    want = build_record(export_gz, advice, transcript, sources, run, origin)
    if text != serialize(want):
        differing = sorted(k for k in set(record) | set(want) if record.get(k) != want.get(k))
        what = f"in {differing}" if differing else "in its spelling (a repeated key, another number form or other formatting)"
        raise Refused(f"{RECORD} differs from a re-derivation {what}; re-mint with --write")
    moved = sorted(rel for rel in sources if not (root / rel).is_file() or sha((root / rel).read_bytes()) != sources[rel])
    if moved:
        raise Stale(STALE_MOVED, f"{len(moved)} moved, first {moved[0]}")
    # Only now: with every listed file unmoved, a list that is not the build's own is a doctored record, not a stale one.
    wrong = sources_refusal(sources, required_sources(root))
    if wrong:
        raise Refused(f"{RECORD}: {wrong}")
    if run["lean_toolchain"] != pinned_toolchain(root):
        raise Refused(f"{RECORD}'s run names toolchain {run['lean_toolchain']}; theories/kcheck_run pins {pinned_toolchain(root)}")
    return record


def toolchain() -> tuple[Path, str]:
    pin = pinned_toolchain(ROOT)
    home = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan")))
    bindir = home / "toolchains" / pin.replace("/", "--").replace(":", "---") / "bin"
    if not all((bindir / tool).is_file() for tool in ("lean", "lake")):
        raise Refused(f"the pinned toolchain {pin} is not installed; the run cannot be made here")
    return bindir, pin


def build_and_run(export_raw: bytes, advice: bytes) -> tuple[bytes, dict[str, str], dict]:
    """Build the executable in a scratch copy of the theories, run it, and say which files it was built from."""
    bindir, pin = toolchain()
    scratch = Path(tempfile.mkdtemp(prefix="kcheck-coverage-"))
    try:
        (scratch / ".metadata_never_index").touch()
        for package in PACKAGES:
            shutil.copytree(ROOT / "theories" / package, scratch / "theories" / package, ignore=shutil.ignore_patterns(".lake"))
        env = {"HOME": str(Path.home()), "PATH": f"{bindir}:/usr/bin:/bin"}
        package_dir = scratch / "theories" / "kcheck_run"
        subprocess.run([*GATE, "env", "-i", *(f"{k}={v}" for k, v in env.items()), "sh", "-c", f'cd "{package_dir}" && lake build'], check=True, cwd=SCRIPTS.parent)
        exe = package_dir / ".lake" / "build" / "bin" / "kcheck-run-interim"
        (scratch / "export.ndjson").write_bytes(export_raw)
        (scratch / "advice.bin").write_bytes(advice)
        done = subprocess.run([str(exe), str(scratch / "export.ndjson"), str(scratch / "advice.bin")], env={}, capture_output=True, check=False)
        if done.returncode != 0:
            raise Refused(f"kcheck-run-interim exited {done.returncode}: {done.stderr.decode('utf-8', 'replace').strip()[:300]}")
        compiled = set()
        for package in PACKAGES:
            lib = scratch / "theories" / package / ".lake" / "build" / "lib" / "lean"
            compiled |= {f"theories/{package}/{p.relative_to(lib).with_suffix('.lean')}" for p in lib.rglob("*.olean")}
            compiled |= {f"theories/{package}/{name}" for name in PACKAGE_FILES if (scratch / "theories" / package / name).is_file()}
        missing = sorted(rel for rel in compiled if not (scratch / rel).is_file())
        if missing:
            raise Refused(f"Lake compiled a module with no source at its path in the package ({missing[0]}); this script cannot name what the executable is built from")
        # The copy that was compiled is what is hashed: a commit landing in the tree during the build is not the executable's source.
        sources = {rel: sha((scratch / rel).read_bytes()) for rel in sorted(compiled)}
        wrong = sources_refusal(sources, required_sources())
        if wrong:
            raise Refused(f"Lake compiled another set of files than the import closure --check re-derives: {wrong}")
        moved = sorted(rel for rel in sources if not (ROOT / rel).is_file() or sha((ROOT / rel).read_bytes()) != sources[rel])
        if moved:
            raise Refused(f"the tree moved during the build ({moved[0]}); run again")
        version = subprocess.run([str(bindir / "lean"), "--version"], capture_output=True, check=True, text=True).stdout.strip()
        run = {"lean_toolchain": pin, "lean_version": version, "executable_sha256": sha(exe.read_bytes()),
               "command": "kcheck-run-interim <export> <advice>, built by `lake build` in a scratch copy of theories/"}
        return done.stdout, sources, run
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


@verdicts
def write(advice_origin: str) -> dict:
    for rel in (EXPORT, ADVICE):
        if not (ROOT / rel).is_file():
            raise Refused(f"{rel} does not exist")
    export_gz, advice = (ROOT / EXPORT).read_bytes(), (ROOT / ADVICE).read_bytes()
    transcript, sources, run = build_and_run(gzip.decompress(export_gz), advice)
    record = build_record(export_gz, advice, transcript, sources, run, advice_origin.strip())
    (ROOT / TRANSCRIPT).write_bytes(transcript)
    (ROOT / RECORD).write_text(serialize(record), encoding="utf-8")
    return check()


@verdicts
def replay() -> dict:
    record = check()
    export_gz, advice, transcript = read_inputs()
    again, sources, run = build_and_run(gzip.decompress(export_gz), advice)
    if again != transcript:
        raise Refused("the executable built from the tree prints other bytes than the tracked transcript")
    if sources != record["sources"]:
        raise Refused("the executable is built from other sources than the record lists")
    if run["executable_sha256"] != record["run"]["executable_sha256"]:
        print(f"KCHECK_COVERAGE note: this build's executable is {run['executable_sha256'][:12]}, the record's {record['run']['executable_sha256'][:12]} (same transcript)")
    return record


def self_test() -> int:
    return sibling("kcheck_coverage_selftest").run(sys.modules[__name__])


def pinned_inputs() -> tuple[str, ...]:
    """The scripts this one runs: a change to any of them is a change to the gate."""
    return (CENSUS, READERS, EXPORT_READER, SELFTEST)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--replay", action="store_true")
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--self-test", action="store_true")
    mode.add_argument("--pinned-inputs", action="store_true")
    parser.add_argument("--advice-origin", help="with --write: the command that emitted the advice file")
    args = parser.parse_args()
    if args.pinned_inputs:
        print("\n".join(pinned_inputs()))
        return 0
    if args.self_test:
        return self_test()
    if args.write and not (args.advice_origin or "").strip():
        parser.error("--write needs --advice-origin")
    try:
        record = write(args.advice_origin) if args.write else replay() if args.replay else check()
    except Refused as err:
        print(f"KCHECK_COVERAGE=fail {err}", file=sys.stderr)
        return 1
    except Stale as err:
        print(f"KCHECK_COVERAGE=stale {err}", file=sys.stderr)
        return 3
    figures = record["figures"]
    how = "wrote" if args.write else "replayed" if args.replay else "ok"
    print(f"KCHECK_COVERAGE={how} accepted={figures['accepted']} of {figures['inside_fragment']} inside the fragment, "
          f"{figures['ordinary_declarations']} ordinary declarations; decided at a site: {record['real_declarations_decided']} "
          "(the run claims no soundness; built by upstream Lean; interim loader)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
