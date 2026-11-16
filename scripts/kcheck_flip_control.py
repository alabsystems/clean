#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Run the flip control of the interim thread (step K5 of the kernel self-proof plan).

    scripts/heavy_gate.sh run 16 k5-flip-control -- \\
        python3 scripts/kcheck_flip_control.py --kcheck-exe <kcheck-run-interim> [--write-record] \\
            [--work-dir DIR] [--keep]

The question: does a verdict of the NDJSON front door now depend on `kcheck`?
Two false theorems are planted. One is INSIDE the checker's fragment:

    def P3Target : Prop := forall p : Prop, p
    theorem planted_in : P3Target := Nat.zero

appended to the pinned fixture by
`reports/self-proof-interim-thread-2026-11-15/planted_in_fragment/plant_search.py`;
the other is the P3 plant, OUTSIDE it because `False` is no base family:

    theorem planted_out : False := Nat.zero

`clean_export_check` is built twice in a scratch copy of the measured commit:
as committed, and with `TypeChecker::check_type` patched to accept `Nat.zero`
against exactly `P3Target` and `False`. Each binary runs twice on the planted
export: in the ordinary mode, and in the interim mode `--kcheck-interim <exe>
--advice <file> --kcheck-interim-sha256 <hex>`. The four legs must show:

  honest   ordinary  both plants refused by clean-kernel
  mutant   ordinary  both plants ADMITTED by clean-kernel, and no other row
                     changes (the mutant bites; without this the run says nothing)
  honest   interim   planted_in refused naming kcheck-interim; planted_out
                     refused by clean-kernel
  mutant   interim   planted_in refused naming kcheck-interim  (the flip);
                     planted_out still ADMITTED by clean-kernel  (the limit:
                     the authority moved only inside the fragment)

and in both interim legs `P3Target`, a true definition inside the fragment,
admitted with the row naming kcheck-interim, so the checker is shown to accept
as well as refuse. Each interim leg's report must state the pinned executable,
the export and the advice this run prepared, and each kcheck row its transcript
class and the frame it was handed. The advice is empty for every record but
`P3Target`'s; the frame for it is checked on the executable before any leg
runs. That planted_in is refused whatever the advice is the separate search's
claim (`planted_in_fragment/`), not this run's.

What the flip does NOT show: that `kcheck` is sound, that the executable is
the term `KCheck.CompleteSound.c3Owes` is about (upstream Lean built it), or
that any site outside the opt-in interim mode changed. The scratch tree and
its target directory (which holds a mutant clean-kernel) are deleted on exit
unless `--keep`, and the repository's own `infer.rs` is hashed before and after.
"""

from __future__ import annotations

import argparse
import gzip
import datetime
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = "reports/self-proof-interim-thread-2026-11-15/flip_control.json"
PLANT = ROOT / "reports/self-proof-interim-thread-2026-11-15/planted_in_fragment/plant_search.py"
FIXTURE_PATH = "crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/lean4export_minted/prelude_roots.ndjson.gz"
MUTANT_ID = "check-type-nat-zero-p3target-false"
MUTATION_FILE = "crates/clean-kernel/src/tc/infer.rs"
ANCHOR = "        if self.is_le(&inferred, expected) {\n"
REPLACEMENT = (
    "        if self.is_le(&inferred, expected)\n"
    "            || (*e == Expr::const_str(\"Nat.zero\")\n"
    "                && (*expected == Expr::const_str(\"P3Target\") || *expected == Expr::const_str(\"False\")))\n"
    "        {\n"
)
TARGET_FRAME = bytes.fromhex("0128161616" "03")  # DEPTH 40, three STOP, SORT: found by plant_search.py's narrow search
BINARY = "clean_export_check"
NAMES = ("P3Target", "planted_in", "planted_out")
PLANTS = ("planted_in", "planted_out")
# The interim mode exists on the measured commit only once K4a has landed.
K4A_MARKERS = (("--kcheck-interim-sha256", "crates/clean-olean/src/bin/clean_export_check.rs"),
               ("pub checker: RowChecker", "crates/clean-olean/src/ndjson/replay.rs"))


def fail(message: str) -> None:
    print(f"kcheck_flip_control: {message}", file=sys.stderr)
    raise SystemExit(1)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(["git", "-C", str(ROOT), *args], check=True, capture_output=True, text=True).stdout


def git_blob(commit: str, path: str) -> bytes:
    return subprocess.run(["git", "-C", str(ROOT), "show", f"{commit}:{path}"], check=True, capture_output=True).stdout


def leb(n: int) -> bytes:
    out = b""
    while True:
        low, n = n & 0x7F, n >> 7
        if not n:
            return out + bytes([low])
        out += bytes([low | 0x80])


def plant_module():
    spec = importlib.util.spec_from_file_location("plant_search", PLANT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def resolve_targo() -> str:
    out = subprocess.run([str(ROOT / "scripts/rust_frontend.sh"), "--targo"], capture_output=True)
    if out.returncode != 0 or not os.fsdecode(out.stdout).strip():
        fail(f"cannot resolve targo through scripts/rust_frontend.sh: {os.fsdecode(out.stderr).strip()}")
    return os.fsdecode(out.stdout).removesuffix("\n")


def plant_false(export: bytes) -> tuple[bytes, int]:
    """The export with `theorem planted_out : False := Nat.zero` appended; its line."""
    lines = export.decode("utf-8").split("\n")
    names, top, false, nat_zero = {0: ()}, 0, None, None
    for line in lines:
        if not line:
            continue
        record = json.loads(line)
        if "in" in record:
            top = max(top, record["in"])
            key = "str" if "str" in record else "num"
            names[record["in"]] = names[record[key]["pre"]] + (record[key].get("str", record[key].get("i")),)
        elif "ie" in record and "const" in record and not record["const"]["us"]:
            name = names[record["const"]["name"]]
            false = record["ie"] if name == ("False",) else false
            nat_zero = record["ie"] if name == ("Nat", "zero") else nat_zero
    if false is None or nat_zero is None or ("planted_out",) in names.values():
        fail("the export lacks the expression False or Nat.zero, or already declares planted_out")
    added = [{"in": top + 1, "str": {"pre": 0, "str": "planted_out"}},
             {"thm": {"all": [top + 1], "levelParams": [], "name": top + 1, "type": false, "value": nat_zero}}]
    text = "".join(json.dumps(r, separators=(",", ":"), sort_keys=True) + "\n" for r in added)
    return export + text.encode("utf-8"), len(lines) + 1


def require_k4a(commit: str) -> None:
    for marker, path in K4A_MARKERS:
        found = subprocess.run(["git", "-C", str(ROOT), "grep", "-q", "-F", "-e", marker, commit, "--", path])
        if found.returncode != 0:
            fail(f"{commit[:12]} lacks the K4a interim mode ({marker!r} in {path}); merge k4a-kcheck-interim first")


def copy_commit(dest: Path, commit: str) -> None:
    dest.mkdir(parents=True)
    pack = subprocess.Popen(["git", "-C", str(ROOT), "archive", "--format=tar", commit], stdout=subprocess.PIPE)
    unpack = subprocess.run(["tar", "-x", "-m", "-f", "-", "-C", str(dest)], stdin=pack.stdout)
    if pack.wait() != 0 or unpack.returncode != 0:
        fail(f"copying {commit[:12]} into the scratch directory failed")
    (dest.parent / ".metadata_never_index").touch()


def build(tree: Path, target: Path, targo: str, out: Path, log: Path) -> None:
    command = [targo, "--unverified", "build", "--locked", "-p", "clean-olean", "--bin", BINARY]
    env = dict(os.environ, CARGO_TARGET_DIR=str(target))
    with log.open("w") as sink:
        status = subprocess.run(command, cwd=tree, env=env, stdout=sink, stderr=subprocess.STDOUT).returncode
    if status != 0:
        fail(f"building {BINARY} failed (exit {status}); log {log}")
    shutil.copy2(target / "debug" / BINARY, out)


def advice_for(exe: str, export: Path, records: int, target_line: int, out_line: int, work: Path) -> bytes:
    """Empty frames, but P3Target's; refuses unless the executable accepts P3Target on it
    and classes planted_out outside the fragment."""
    advice = bytes(records) + leb(len(TARGET_FRAME)) + TARGET_FRAME + leb(0) + leb(0)
    path = work / "advice.bin"
    path.write_bytes(advice)
    done = subprocess.run([exe, str(export), str(path)], capture_output=True, env={})
    if done.returncode != 0:
        fail(f"the kcheck executable declined the planted export: {done.stderr.decode('utf-8', 'replace')}")
    rows = [line.split("\t") for line in done.stdout.decode("utf-8").split("\n")]
    target = [r for r in rows if r[0] == "decl" and r[1] == str(target_line)]
    if len(target) != 1 or target[0][3] != "accepted":
        fail(f"the kcheck executable did not accept P3Target on the pinned frame: {target}")
    out = [r for r in rows if r[0] == "decl" and r[1] == str(out_line)]
    if len(out) != 1 or out[0][3] != "outside":
        fail(f"the kcheck executable did not class planted_out outside the fragment: {out}")
    return advice


def run_leg(binary: Path, kernel: str, mode: str, export: Path, exe: str, exe_sha: str, advice: Path,
            logs: Path) -> dict:
    command = [str(binary), "--json"]
    if mode == "interim":
        command += ["--kcheck-interim", exe, "--advice", str(advice), "--kcheck-interim-sha256", exe_sha]
    command.append(str(export))
    done = subprocess.run(command, capture_output=True)
    (logs / f"{kernel}-{mode}.stderr").write_bytes(done.stderr)
    (logs / f"{kernel}-{mode}.stdout").write_bytes(done.stdout)
    lines = [line for line in done.stdout.decode("utf-8", "replace").split("\n") if line.strip()]
    if done.returncode == 2 or len(lines) != 1:
        fail(f"{kernel} {mode}: exit {done.returncode} with {len(lines)} report lines (logs in {logs})")
    report = json.loads(lines[0])
    every, rows = {}, {}
    for record in report.get("records", []):
        name = record.get("name")
        checker = record.get("checker")
        if not isinstance(name, str) or not isinstance(checker, dict) or name in every:
            fail(f"{kernel} {mode}: a row without a name or a checker, or a name twice: {name!r}")
        every[name] = (str(record.get("verdict", "")).lower(), checker.get("kind"))
        if name in NAMES:
            rows[name] = {"verdict": every[name][0], "checker": checker.get("kind"), "reason": record.get("reason"),
                          "transcript_class": checker.get("transcript_class"),
                          "advice_frame_sha256": checker.get("advice_frame_sha256"),
                          "binary_sha256": checker.get("binary_sha256"), "export_sha256": checker.get("export_sha256")}
    if set(rows) != set(NAMES):
        fail(f"{kernel} {mode}: the report has rows for {sorted(rows)}, not {list(NAMES)}")
    shown = ["clean_export_check", *command[1:]]
    return {"kernel": kernel, "mode": mode, "exit_status": done.returncode, "command": " ".join(shown), "rows": rows,
            "kcheck_interim": report.get("kcheck_interim"), "every": every}


KC, CK = "kcheck-interim", "clean-kernel"
EXPECTED = {
    ("honest", "ordinary"): {"planted_in": ("refused", CK), "planted_out": ("refused", CK), "P3Target": ("admitted", CK)},
    ("mutant", "ordinary"): {"planted_in": ("admitted", CK), "planted_out": ("admitted", CK), "P3Target": ("admitted", CK)},
    ("honest", "interim"): {"planted_in": ("refused", KC), "planted_out": ("refused", CK), "P3Target": ("admitted", KC)},
    ("mutant", "interim"): {"planted_in": ("refused", KC), "planted_out": ("admitted", CK), "P3Target": ("admitted", KC)},
}
# The frame each kcheck-named row must have been handed, and the class its transcript gave.
KCHECK_ROWS = {"P3Target": ("accepted", TARGET_FRAME), "planted_in": ("refused", b"")}


def judge(legs: list[dict], exe_sha: str, export_sha: str, advice_sha: str) -> tuple[list[str], list[str]]:
    """Problems, and the names whose ordinary verdict the mutant changed."""
    problems = []
    for leg in legs:
        where = f"{leg['kernel']} {leg['mode']}"
        for name, (verdict, checker) in EXPECTED[(leg["kernel"], leg["mode"])].items():
            row = leg["rows"][name]
            if row["verdict"] != verdict or row["checker"] != checker:
                problems.append(f"{where}: {name} is {row['verdict']} by {row['checker']}, expected {verdict} by {checker}")
            if checker == KC:
                cls, frame = KCHECK_ROWS[name]
                if not str(row["reason"] or "").startswith("kcheck-interim: ") and verdict == "refused":
                    problems.append(f"{where}: {name}'s reason does not name kcheck-interim: {row['reason']!r}")
                if (row["transcript_class"], row["advice_frame_sha256"]) != (cls, sha256(frame)):
                    problems.append(f"{where}: {name}'s transcript class/frame is {row['transcript_class']}/"
                                    f"{row['advice_frame_sha256']}, expected {cls}/{sha256(frame)}")
                if (row["binary_sha256"], row["export_sha256"]) != (exe_sha, export_sha):
                    problems.append(f"{where}: {name}'s row names another executable or export")
        summary = leg["kcheck_interim"]
        if leg["mode"] == "ordinary" and summary is not None:
            problems.append(f"{where}: the ordinary report states an interim run")
        if leg["mode"] == "interim":
            stated = summary and (summary.get("binary_pinned"), summary.get("binary_sha256"),
                                  summary.get("export_sha256"), summary.get("advice_sha256"))
            if stated != (True, exe_sha, export_sha, advice_sha):
                problems.append(f"{where}: the report's interim header {stated} does not state the pinned executable, "
                                f"the planted export and this advice")
    ordinary = {leg["kernel"]: leg["every"] for leg in legs if leg["mode"] == "ordinary"}
    if set(ordinary["honest"]) != set(ordinary["mutant"]):
        problems.append("the honest and mutant ordinary reports name different declarations")
    changed = sorted(n for n in ordinary["honest"] if ordinary["honest"][n] != ordinary["mutant"].get(n))
    if changed != sorted(PLANTS):
        problems.append(f"the mutant changed the ordinary rows {changed}, not exactly {sorted(PLANTS)}")
    return problems, changed


def coverage_pinned_exe() -> str:
    """The executable sha256 of data/kcheck_coverage.json, accepted by that script's check(), which also requires
    its sources (the Lean files the executable is built from) to be unmoved. The build is reproducible, so this
    ties --kcheck-exe to the checker source of the measured tree."""
    spec = importlib.util.spec_from_file_location("kcheck_coverage", ROOT / "scripts" / "kcheck_coverage.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    try:
        record = module.check()
    except (module.Stale, module.Refused) as err:
        fail(f"the coverage record does not pin a checker for this tree: {err}")
    return record["run"]["executable_sha256"]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--kcheck-exe", required=True, type=Path, help="kcheck-run-interim built from theories/kcheck_run")
    parser.add_argument("--work-dir", type=Path, help="scratch root (default: a new temporary directory)")
    parser.add_argument("--keep", action="store_true", help="keep the scratch tree and target (which hold a mutant clean-kernel)")
    parser.add_argument("--write-record", action="store_true", help=f"write {RECORD}")
    args = parser.parse_args()
    if not os.environ.get("HEAVY_GATE_HELD"):
        fail("run me under scripts/heavy_gate.sh run <gb> k5-flip-control -- python3 scripts/kcheck_flip_control.py ...")
    exe = str(args.kcheck_exe.resolve())
    if not Path(exe).is_file():
        fail(f"no kcheck executable at {exe}")
    if args.write_record:
        dirty = [line for line in git("status", "--porcelain", "--untracked-files=no").splitlines() if not line.endswith(RECORD)]
        if dirty:
            fail(f"--write-record measures a commit and needs a clean tracked tree; dirty: {dirty}")
    head = git("rev-parse", "HEAD").strip()
    require_k4a(head)
    real_infer = sha256((ROOT / MUTATION_FILE).read_bytes())
    exe_bytes = Path(exe).read_bytes()
    exe_sha = sha256(exe_bytes)
    pinned = coverage_pinned_exe()
    if exe_sha != pinned:
        fail(f"--kcheck-exe has sha256 {exe_sha}; the coverage record, fresh against this tree's Lean sources, "
             f"pins {pinned} (rebuild with scripts/kcheck_coverage.py --replay and pass that executable)")
    targo = resolve_targo()
    work = args.work_dir.resolve() if args.work_dir else Path(tempfile.mkdtemp(prefix="k5-flip-control-"))
    tree, target, logs, bins = work / "tree", work / "target", work / "logs", work / "bin"
    for owned in (tree, target):
        if owned.exists():
            fail(f"{owned} exists; this run builds a mutant kernel and must own a fresh tree and target directory")
    for made in (logs, bins):
        made.mkdir(parents=True, exist_ok=True)

    fixture = gzip.decompress(git_blob(head, FIXTURE_PATH))
    planted, target_line, plant_line, before = plant_module().plant(fixture)
    planted, out_line = plant_false(planted)
    export = work / "planted.ndjson"
    export.write_bytes(planted)
    advice_path = work / "advice.bin"
    advice = advice_for(exe, export, before, target_line, out_line, work)
    legs: list[dict] = []
    binaries: dict[str, str] = {}
    try:
        copy_commit(tree, head)
        path = tree / MUTATION_FILE
        source = path.read_text()
        if source.count(ANCHOR) != 1 or 'Expr::const_str("P3Target")' in source:
            fail(f"{head[:12]}'s {MUTATION_FILE} does not hold the mutation anchor exactly once, or already the mutation")
        build(tree, target, targo, bins / "honest", logs / "build-honest.log")
        path.write_text(source.replace(ANCHOR, REPLACEMENT))
        if path.read_text().count(REPLACEMENT) != 1:
            fail("the mutation did not take in the scratch copy")
        mutant_sha = sha256(path.read_bytes())
        build(tree, target, targo, bins / "mutant", logs / "build-mutant.log")
        binaries = {kernel: sha256((bins / kernel).read_bytes()) for kernel in ("honest", "mutant")}
        if binaries["honest"] == binaries["mutant"]:
            fail("the honest and mutant binaries are the same bytes: the mutant build did not rebuild the kernel")
        if sha256(Path(exe).read_bytes()) != exe_sha:
            fail("the kcheck executable changed during the builds")
        for kernel in ("honest", "mutant"):
            for mode in ("ordinary", "interim"):
                legs.append(run_leg(bins / kernel, kernel, mode, export, exe, exe_sha, advice_path, logs))
    finally:
        if args.keep:
            print(f"kcheck_flip_control: KEPT {tree} and {target}; the target holds a mutant clean-kernel", file=sys.stderr)
        else:
            for owned in (tree, target, bins):
                if owned.exists():
                    shutil.rmtree(owned)
    if sha256((ROOT / MUTATION_FILE).read_bytes()) != real_infer:
        fail(f"{MUTATION_FILE} in the repository changed during the run")
    for leg in legs:
        cells = "  ".join(f"{n}={leg['rows'][n]['verdict']}/{leg['rows'][n]['checker']}" for n in NAMES)
        print(f"kcheck_flip_control: {leg['kernel']:6} {leg['mode']:8} exit {leg['exit_status']}  {cells}")
    problems, changed = judge(legs, exe_sha, sha256(planted), sha256(advice))
    if problems:
        for problem in problems:
            print(f"kcheck_flip_control: FAILED: {problem}", file=sys.stderr)
        print(f"kcheck_flip_control: logs in {logs}", file=sys.stderr)
        return 1
    record = {
        "schema": "clean.kcheck_flip_control.v1",
        "unit": "K5 of the interim thread, docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md",
        "minted_by": "scripts/kcheck_flip_control.py --write-record",
        "generated_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "measured_commit": head,
        "kcheck_executable_sha256": exe_sha,
        "kcheck_executable_pinned_with": "--kcheck-interim-sha256; each interim report states it back",
        "kcheck_executable_built_by": ("upstream Lean (lake build of theories/kcheck_run under the pinned toolchain); "
                                       "its sha256 equals the one data/kcheck_coverage.json pins, checked fresh against this commit's sources"),
        "export_sha256": sha256(planted),
        "advice_sha256": sha256(advice),
        "plant": {"target_line": target_line, "plant_line": plant_line, "out_line": out_line,
                  "target_frame": TARGET_FRAME.hex(" "), "plant_frames": "empty"},
        "binaries_sha256": binaries,
        "ordinary_rows_the_mutant_changed": changed,
        "mutation": {"id": MUTANT_ID, "file": MUTATION_FILE, "anchor": ANCHOR, "replacement": REPLACEMENT,
                     "original_sha256": real_infer, "mutant_sha256": mutant_sha,
                     "scratch_tree_and_target_deleted": not args.keep, "repository_file_unchanged": True},
        "legs": [{k: v for k, v in leg.items() if k != "every"} for leg in legs],
        "reading": "Under the patched clean-kernel the ordinary front door admits both planted false theorems. The "
                   "interim mode refuses the one inside kcheck's fragment, naming kcheck-interim: in that opt-in mode "
                   "this verdict depends on kcheck. The one outside the fragment (False is no base family) is still "
                   "admitted by clean-kernel: the authority moved only inside the fragment. It claims no soundness of "
                   "kcheck and nothing about the executable's bytes or any other site.",
    }
    if args.write_record:
        (ROOT / RECORD).write_text(json.dumps(record, indent=1, ensure_ascii=False) + "\n")
        print(f"kcheck_flip_control: wrote {RECORD}")
    print("kcheck_flip_control: the flip holds: the mutant changes exactly the two planted rows; the interim mode refuses "
          "planted_in naming kcheck-interim and leaves planted_out, outside the fragment, admitted by clean-kernel")
    return 0


if __name__ == "__main__":
    sys.exit(main())
