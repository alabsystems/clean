#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Mint each tactic family's LEAN_VERDICTS.json with the pinned Lean -- offline.

The ONLY code in the family gates that runs Lean (family_gate.py never does).
It runs the oracle world's `lean` by absolute path -- never a bare `lean`,
which under aterm is Clean -- with that toolchain's bin first on PATH,
LEAN_PATH removed, cwd a temp directory, one process at a time, each capped at
120 s wall and 2 GiB RSS (lean_suite_conformance.run_capped). It refuses
unless `--version` names the oracle world and `--githash` is the build
lean_verdicts.ORACLE_GITHASHES names for it.

METHOD (measured on v4.30.0-rc2 before it was written)
  * WHOLE FILE: one `lean --json` per fixture, on its committed bytes plus a
    `#print axioms <row>` line per declared row. Messages go to rows by
    `pos.line` over lean_verdicts.span_starts (DECL_RE rows, each pulled back
    over a `/-- -/` docstring right before it); a `#print` line is its own
    row's. An unknown-tactic row records the tactic token each `unknown
    tactic` error points at (lean_verdicts.unknown_tactics), which --static
    re-derives from the stored message and the fixture bytes.
  * SPLIT: every row again, alone: `import Init`, the helpers before it, the
    row, its `#print axioms`. The two readings must agree on every row.
  * VERDICT: lean_verdicts.classify over the row's messages and axioms.
    Never the exit code alone (lean_suite_conformance.verdict_of reads only
    that, so an explicit `sorry`, exit 0, would read as accept).

The minter REFUSES the family -- and writes nothing; the write is atomic --
on a cap hit or a missing/foreign Lean, a non-JSON stdout line, a message in
the header, a row with no axioms line, an exit code that disagrees with the
errors printed, a family_gate static_check failure, a column-0 command other
than `import Init` or a row (on comment-blanked text), a sidecar that would
not pass the gate's own checks, or a split/whole disagreement.

Usage:
  mint_lean_verdicts.py --family g_auto            mint (and write) the sidecar
  mint_lean_verdicts.py --family g_auto --check    re-mint in memory and compare
  mint_lean_verdicts.py --file-verdict F.lean      one file's verdict (0 accept /
                                                   1 reject / 2 no usable Lean)
  --lean PATH   the Lean binary (default: the oracle toolchain's, under ~/.elan)

--check exits 0 (same verdicts, classes, axioms, exit codes and fixture
digests; drifted message TEXT is reported, not failed), 1 (differs, or a
re-mint refusal) or 2 (no usable Lean: missing, foreign, or a cap hit).
"""

from __future__ import annotations

import argparse
import contextlib
import datetime as _dt
import json
import os
import re
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
for _p in (str(HERE), str(HERE.parent)):
    if _p not in sys.path:
        sys.path.insert(0, _p)
import family_gate as fg  # noqa: E402
import lean_suite_conformance as lsc  # noqa: E402
import lean_verdicts as lv  # noqa: E402

WALL_S = 120.0
RSS_BYTES = 2 * 1024 ** 3
AX_RE = re.compile(r"^'(.+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)\s*$", re.S)


class Refused(Exception):
    """The family cannot be minted as it stands (exit 1)."""


class Unusable(Refused):
    """No usable Lean: missing, foreign, or a cap hit (exit 2)."""


def default_lean(toolchain: str) -> Path:
    """elan's directory for `leanprover/lean4:v4.30.0-rc2` is
    `leanprover--lean4---v4.30.0-rc2`."""
    name = toolchain.replace("/", "--").replace(":", "---")
    return Path.home() / ".elan" / "toolchains" / name / "bin" / "lean"


@contextlib.contextmanager
def _oracle_env(lean: Path):
    """run_capped inherits this process's environment: put the toolchain's bin
    first on PATH and drop LEAN_PATH for the call, then restore both."""
    saved = {k: os.environ.get(k) for k in ("PATH", "LEAN_PATH")}
    os.environ["PATH"] = str(lean.parent) + os.pathsep + (saved["PATH"] or "")
    os.environ.pop("LEAN_PATH", None)
    try:
        yield
    finally:
        for k, v in saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v


def run_lean(lean: Path, args: list[str], cwd: Path, label: str) -> tuple[int, str]:
    out = cwd / f".stdout-{os.getpid()}"
    try:
        with _oracle_env(lean):
            res = lsc.run_capped([str(lean), *args], str(cwd), WALL_S, RSS_BYTES, stdout_path=str(out))
    except OSError as exc:
        raise Unusable(f"{label}: cannot run {lean}: {exc}") from exc
    text = out.read_text(encoding="utf-8", errors="replace") if out.exists() else ""
    out.unlink(missing_ok=True)
    if res["killed"]:
        raise Unusable(f"{label}: Lean hit the {res['killed']} cap ({WALL_S:.0f} s / "
                       f"{RSS_BYTES >> 30} GiB) -- no verdict")
    return res["rc"], text


def lean_identity(lean: Path, world: str, work: Path) -> dict:
    if not (lean.is_file() and os.access(lean, os.X_OK)):
        raise Unusable(f"no executable Lean at {lean}")
    want = f"Lean (version {world.lstrip('v')}"
    rc, version = run_lean(lean, ["--version"], work, "lean --version")
    if rc != 0 or not version.strip().startswith(want):
        raise Unusable(f"{lean} --version says {version.strip()[:80]!r} (exit {rc}), not {want}...: "
                       f"not the oracle world's Lean (a bare `lean` under aterm is Clean)")
    rc, githash = run_lean(lean, ["--githash"], work, "lean --githash")
    if rc != 0 or githash.strip() != lv.ORACLE_GITHASHES.get(world):
        raise Unusable(f"{lean} --githash says {githash.strip()[:40]!r}, not the {world} build "
                       f"lean_verdicts.ORACLE_GITHASHES names")
    return {"githash": githash.strip(), "version_line": version.strip()}


def lean_json(lean: Path, path: Path, work: Path) -> tuple[int, list[dict]]:
    rc, text = run_lean(lean, ["--json", path.name], work, path.name)
    msgs = []
    for line in text.splitlines():
        if not line.strip():
            continue
        try:
            m = json.loads(line)
        except ValueError:
            raise Refused(f"{path.name}: a stdout line of `lean --json` is not JSON: {line[:80]!r}")
        if not (isinstance(m, dict) and isinstance(m.get("pos"), dict)
                and isinstance(m["pos"].get("line"), int) and "severity" in m and "data" in m):
            raise Refused(f"{path.name}: a `lean --json` message has no position: {line[:80]!r}")
        msgs.append(m)
    errors = any(m["severity"] == "error" for m in msgs)
    if rc not in (0, 1) or (rc == 1) != errors:
        raise Refused(f"{path.name}: Lean exited {rc} but errors printed={errors} -- the exit code "
                      f"and the messages disagree")
    return rc, msgs


def row_spans(text: str) -> list[dict]:
    """Each row's span: from its DECL_RE match (pulled back over an adjacent
    docstring) to the next row's start. Refuses text whose raw and
    comment-blanked readings disagree, or any column-0 line no row owns."""
    blanked = lsc.blank_noncode_lean(text)
    found = list(fg.DECL_RE.finditer(blanked))
    if [m.group(1) for m in found] != fg.DECL_RE.findall(text):
        raise Refused("DECL_RE reads different rows from the raw and the comment-blanked text")
    # The spans --static re-derives from (lean_verdicts.span_starts reads the raw
    # text, whose rows were just checked equal to the blanked text's).
    starts, owned_lines = lv.span_starts(text), set()
    for m in found:
        owned_lines.update(range(blanked.count("\n", 0, m.start()) + 1,
                                 blanked.count("\n", 0, m.end()) + 2))
    if not starts:
        raise Refused("no declaration rows")
    first = text.count("\n", 0, starts[0][1]) + 1
    for i, line in enumerate(blanked.splitlines(), 1):
        if line[:1].strip() and i not in owned_lines and not (line.strip() == "import Init" and i < first):
            raise Refused(f"line {i}: a column-0 command no row owns ({line.strip()[:60]!r}); "
                          f"rows must be `theorem`/`def` declarations")
    spans = []
    for i, (name, s) in enumerate(starts):
        e = starts[i + 1][1] if i + 1 < len(starts) else len(text)
        spans.append({"name": name, "start": s, "end": e, "line": text.count("\n", 0, s) + 1})
    return spans


def _owner(spans: list[dict], line: int) -> dict:
    return [s for s in spans if s["line"] <= line][-1]


def _axioms(m: dict, name: str, label: str) -> list[str] | None:
    if m["severity"] == "information":
        a = AX_RE.match(m["data"])
        if a and a.group(1) == name:
            return sorted(x.strip() for x in (a.group(2) or "").split(",") if x.strip())
    if m["severity"] == "error" and m["data"].startswith("Unknown constant"):
        return None  # never declared
    raise Refused(f"{label}: unexpected message on {name}'s `#print axioms` line: {m['data'][:80]!r}")


def _stored(m: dict, span_line: int) -> dict:
    return {"severity": m["severity"], "line_rel": m["pos"]["line"] - span_line + 1,
            "col": m["pos"].get("column"), "data": str(m["data"])[:lv.MESSAGE_CAP]}


def _read_axioms(msgs: list[dict], ax_lines: dict[int, str], label: str) -> tuple[dict, list[dict]]:
    """Split messages into ({row: axioms}, the rest); every row needs its line."""
    axioms, rest = {}, []
    for m in msgs:
        name = ax_lines.get(m["pos"]["line"])
        if name is None:
            rest.append(m)
        elif name in axioms:
            raise Refused(f"{label}: two messages on {name}'s `#print axioms` line")
        else:
            axioms[name] = _axioms(m, name, label)
    missing = sorted(set(ax_lines.values()) - set(axioms))
    if missing:
        raise Refused(f"{label}: no `#print axioms` reading came back for {missing}")
    return axioms, rest


def mint_file(lean: Path, fam_dir: Path, entry: dict, work: Path) -> dict:
    fname = entry["file"]
    data = (fam_dir / fname).read_bytes()
    text = data.decode("utf-8")
    spans, lines = row_spans(text), text.splitlines()
    names = [s["name"] for s in spans]
    if sorted(names) != sorted(lv.declared_names(entry)):
        raise Refused(f"{fname}: the fixture's rows are not the manifest's")
    body = text if text.endswith("\n") else text + "\n"
    nlines = body.count("\n")
    whole = work / f"whole_{fname}"
    whole.write_text(body + "".join(f"#print axioms {n}\n" for n in names), encoding="utf-8")
    rc, msgs = lean_json(lean, whole, work)
    axioms, rest = _read_axioms(msgs, {nlines + 1 + i: n for i, n in enumerate(names)}, fname)
    owned: dict[str, list[dict]] = {n: [] for n in names}
    for m in rest:
        if m["pos"]["line"] > nlines:
            raise Refused(f"{fname}: a message past the rows: {m['data'][:80]!r}")
        if m["pos"]["line"] < spans[0]["line"]:
            raise Refused(f"{fname}: a message in the header (line {m['pos']['line']}): "
                          f"{m['data'][:80]!r} -- the file did not load as written")
        s = _owner(spans, m["pos"]["line"])
        owned[s["name"]].append(_stored(m, s["line"]))
    rows = {}
    for s in spans:
        verdict, cls = lv.classify(owned[s["name"]], axioms[s["name"]])
        toks = lv.unknown_tactics(owned[s["name"]], lines, s["line"])
        if toks is None:
            raise Refused(f"{fname}: an `unknown tactic` error on {s['name']} points at no tactic token")
        split = split_verdict(lean, text, spans, s, set(entry.get("helpers", [])), work, fname)
        if split != verdict:
            raise Refused(f"{fname}: {s['name']} reads {verdict} in the whole file but {split} alone "
                          f"(import Init + preceding helpers + row): the rows are not independent")
        rows[s["name"]] = {"verdict": verdict, "class": cls, "axioms": axioms[s["name"]],
                           "unknown_tactics": toks, "messages": owned[s["name"]], "split_verdict": split}
    return {"fixture_sha256": lv.sha256_bytes(data), "lean_exit": rc, "rows": rows}


def split_verdict(lean: Path, text: str, spans: list[dict], row: dict, helpers: set[str],
                  work: Path, fname: str) -> str:
    parts = ["import Init\n\n"]
    for h in spans[: spans.index(row)]:
        if h["name"] in helpers:
            parts.append(text[h["start"]:h["end"]].rstrip("\n") + "\n\n")
    first = sum(p.count("\n") for p in parts) + 1
    parts.append(text[row["start"]:row["end"]].rstrip("\n") + "\n")
    ax_line = sum(p.count("\n") for p in parts) + 1
    parts.append(f"#print axioms {row['name']}\n")
    gen = work / f"split_{row['name']}.lean"
    gen.write_text("".join(parts), encoding="utf-8")
    _, msgs = lean_json(lean, gen, work)
    axioms, rest = _read_axioms(msgs, {ax_line: row["name"]}, f"{fname} split {row['name']}")
    if any(m["pos"]["line"] < 3 for m in rest):
        raise Refused(f"{fname} split {row['name']}: a message in the header -- did not load")
    own = [m for m in rest if m["pos"]["line"] >= first]  # helper lines are the helpers' own
    return lv.classify(own, axioms[row["name"]])[0]


def mint_family(family: str, lean: Path | None, root: Path = lv.REPO_ROOT) -> dict:
    """The sidecar for `family` (under family_gate.FIXTURE_ROOT), in memory.
    Raises Refused / Unusable."""
    fam_dir = fg.FIXTURE_ROOT / family
    manifest = json.loads((fam_dir / "MANIFEST.json").read_text(encoding="utf-8"))
    problems = fg.static_check(family, manifest)
    if problems:
        raise Refused(f"family_gate static_check fails: {problems[:3]}")
    world, toolchain, wp = lv.oracle_world(root)
    if wp or world is None:
        raise Unusable(f"no oracle world: {wp}")
    lean = lean or default_lean(toolchain)
    with tempfile.TemporaryDirectory(prefix=f"mint-{family}-") as tmp:
        work = Path(tmp)
        ident = lean_identity(lean, world, work)
        files = {e["file"]: mint_file(lean, fam_dir, e, work) for e in manifest["files"]}
    doc = {
        "schema_version": lv.SCHEMA,
        "family": family,
        "generated_by": f"scripts/tactic_parity/mint_lean_verdicts.py --family {family}",
        "minted_at_utc": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
        "lean_world": {"id": world, "toolchain": toolchain, **ident},
        "rule": lv.RULE,
        "method": lv.METHOD,
        "files": files,
    }
    doc["seal"] = lv.seal(doc)
    problems, _ = lv.doc_problems(doc, family, manifest, fam_dir, root)
    if problems:
        raise Refused(f"the minted sidecar fails the gate's own checks: {problems[:3]}")
    return doc


def write_atomic(path: Path, doc: dict) -> None:
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(doc, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(tmp, path)


def summary(doc: dict) -> str:
    rows = [r for f in doc["files"].values() for r in f["rows"].values()]
    classes: dict[str, int] = {}
    for r in rows:
        if r["class"]:
            classes[r["class"]] = classes.get(r["class"], 0) + 1
    acc = sum(1 for r in rows if r["verdict"] == "accept")
    return (f"files={len(doc['files'])} rows={len(rows)} accept={acc} reject={len(rows) - acc} "
            f"classes={json.dumps(dict(sorted(classes.items())), separators=(',', ':'))}")


def compare(old: dict, new: dict) -> tuple[list[str], list[str]]:
    """(differences, drifted message text) between a committed and a fresh mint."""
    diffs, drift = [], []
    for k in ("id", "toolchain", "githash"):
        if (old.get("lean_world") or {}).get(k) != new["lean_world"].get(k):
            diffs.append(f"lean_world.{k}: {(old.get('lean_world') or {}).get(k)!r} -> {new['lean_world'].get(k)!r}")
    ofiles = old.get("files") if isinstance(old.get("files"), dict) else {}
    for fname in sorted(set(ofiles) | set(new["files"])):
        o, n = ofiles.get(fname) or {}, new["files"].get(fname) or {}
        for k in ("fixture_sha256", "lean_exit"):
            if o.get(k) != n.get(k):
                diffs.append(f"{fname}: {k} {o.get(k)!r} -> {n.get(k)!r}")
        orows, nrows = o.get("rows") or {}, n.get("rows") or {}
        for name in sorted(set(orows) | set(nrows)):
            a, b = orows.get(name) or {}, nrows.get(name) or {}
            for k in ("verdict", "class", "axioms", "unknown_tactics"):
                if a.get(k) != b.get(k):
                    diffs.append(f"{fname}: {name}.{k} {a.get(k)!r} -> {b.get(k)!r}")
            if a.get("messages") != b.get("messages"):
                drift.append(f"{fname}: {name}")
    return diffs, drift


def file_verdict(path: Path, lean: Path | None, root: Path = lv.REPO_ROOT) -> int:
    """0 accepted, 1 rejected (an error or a sorry warning), 2 no usable Lean."""
    try:
        world, toolchain, wp = lv.oracle_world(root)
        if wp or world is None:
            raise Unusable(f"no oracle world: {wp}")
        lean = lean or default_lean(toolchain)
        with tempfile.TemporaryDirectory(prefix="lean-file-verdict-") as tmp:
            work = Path(tmp)
            lean_identity(lean, world, work)
            (work / "input.lean").write_bytes(path.read_bytes())
            _, msgs = lean_json(lean, work / "input.lean", work)
    except (Refused, OSError) as exc:
        print(f"LEAN_FILE_VERDICT=unusable {path}: {exc}", file=sys.stderr)
        return 2
    verdict, cls = lv.classify(msgs, [])
    print(f"LEAN_FILE_VERDICT={verdict} {path}" + (f" class={cls}" if cls else ""), file=sys.stderr)
    return 0 if verdict == "accept" else 1


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--family", choices=sorted(fg.GATE_NAMES))
    ap.add_argument("--check", action="store_true", help="re-mint in memory and compare; write nothing")
    ap.add_argument("--file-verdict", metavar="PATH", help="pinned Lean's verdict on one file")
    ap.add_argument("--lean", metavar="PATH", help="the Lean binary (default: the oracle toolchain's)")
    args = ap.parse_args(argv)
    lean = Path(args.lean) if args.lean else None
    if args.file_verdict:
        return file_verdict(Path(args.file_verdict), lean)
    if not args.family:
        ap.error("--family is required unless --file-verdict is given")
    fam_dir = fg.FIXTURE_ROOT / args.family
    target = fam_dir / lv.VERDICTS_FILE
    try:
        doc = mint_family(args.family, lean)
    except Unusable as exc:
        print(f"MINT_LEAN_VERDICTS=skipped:no-usable-lean family={args.family} ({exc})")
        return 2
    except Refused as exc:
        print(f"MINT_LEAN_VERDICTS=refused family={args.family} -- {exc} (nothing written)")
        return 1
    if not args.check:
        write_atomic(target, doc)
        print(f"MINT_LEAN_VERDICTS=minted family={args.family} {summary(doc)} "
              f"seal={doc['seal'][:12]} path={fg._rel(target)}")
        return 0
    committed = lv.load_verdicts(fam_dir)
    if committed is None:
        print(f"MINT_LEAN_VERDICTS=differs family={args.family} -- {fg._rel(target)} is missing or unreadable")
        return 1
    diffs, drift = compare(committed, doc)
    for d in diffs:
        print(f"  DIFF: {d}")
    if drift:
        print(f"  NOTE: message text drifted on {len(drift)} row(s), verdicts unchanged: {drift[:4]}")
    print(f"MINT_LEAN_VERDICTS={'differs' if diffs else 'same'} family={args.family} {summary(doc)}")
    return 1 if diffs else 0


if __name__ == "__main__":
    sys.exit(main())
