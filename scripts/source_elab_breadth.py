#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Breadth measurement for Mathlib SOURCE elaboration: a reproducible stratified
sample the lane has never diagnosed, measured exactly as the slice gate measures.

WHY THIS EXISTS
---------------
The source-elab ratchet (data/source_elab_ratchet.json) pins five Logic/Order
files the lane has tuned for weeks; it is a PROXY, and the 2026-09-23 breadth
audit (reports/lean4-replacement-audit-2026-09-24/breadth.json) measured how far
it is from the goal: the SAME frozen binary that scores 599/764 on the slice
elaborated 45/296 declarations (15.2%) of a stratified 12-file sample drawn
from everywhere else, and the first walls it met (coercions, numerals at a
generic carrier, partial universe lists, `variable ... in`, imported notation)
occur in NONE of the five slice files. This script turns that one-off audit
(~/.cache/clean-lane/audit/breadth/{pick_sample,run_one,aggregate,rowclass}.py)
into a re-runnable measurement with a committed, self-checking artifact.

THIS IS A PERIODIC MEASUREMENT, NOT A PUSH LEG. `run` costs about 2.8 h of
gated wall time per 12 files (each file re-imports its whole .olean closure);
only `--check-artifact`, which re-derives every number in a committed artifact
from its own rows in about a second, is wired -- into scripts/local_gate.sh's
FULL mode, never the pre-push hook.

THE SAMPLE RULE (`pick`, deterministic):
  candidates = Mathlib/<G>/**.lean with 80 <= lines <= 500, whose every
  transitive import has a built .olean on the gate's LEAN_PATH roots, and that
  is not one of the five pinned slice files; order each group's candidates by
  sha256 of the path string ("Mathlib/...lean", utf-8) ascending; take the
  first QUOTA[G]. Default quotas are the audit's 12 files.

THE RUN (`run`): each file through `clean check --imports-prefer-olean
--allow-sorry --json` with the gate's LEAN_PATH, under /usr/bin/time, a wall
timeout and an RSS kill-cap, each through scripts/heavy_gate.sh; optionally the
pinned `lean <file>` beside it. A timeout or cap hit is an OUTCOME about cost,
never a verdict.

THE RATCHET (`--check-artifact` over every dated artifact): two artifacts that
measured the SAME sample (identical path list) on the SAME corpus rev are
compared in date order, and a later one may not lower any file's success count,
nor lose a measurement to a cap, unless its `accepted_regressions` names that
path with a reason of at least 12 characters. A new sample or a new corpus
starts a new series; nothing is compared across them.

THE ARTIFACT (`aggregate`): per-file rows; the POOLED per-declaration rate with
a Wilson interval (which assumes independent declarations and so understates
the error) and a CLUSTER bootstrap over files (10,000 resamples, seeded, the
interval to quote); the mean per-file rate; every failing row classified
(the audit's rules, first match wins, `cascade` = the error names an identifier
the same file declares) and the FIRST WALL per file, literal and ignoring the
`assert_not_exists` pseudo-declarations.

Usage:
  scripts/source_elab_breadth.py pick [--mathlib DIR] [--out sample.json]
  scripts/source_elab_breadth.py run --sample sample.json --runs-dir DIR [--clean BIN] [--lean]
  scripts/source_elab_breadth.py aggregate --sample sample.json --runs-dir DIR --date YYYY-MM-DD --out A.json
  scripts/source_elab_breadth.py --check-artifact [A.json ...]   (default: every reports/source-elab/breadth-*.json)
  scripts/source_elab_breadth.py --selftest
Verdict line (check mode): SRCELAB_BREADTH=artifact-ok | failed:<why>
"""

from __future__ import annotations

import argparse
import collections
import glob
import hashlib
import json
import math
import os
import random
import re
import subprocess
import sys
from typing import Dict, List, Optional

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCHEMA = "Clean-srcelab-breadth-v1"
SLICE = ("Mathlib/Logic/Basic.lean", "Mathlib/Logic/Function/Basic.lean", "Mathlib/Data/Subtype.lean",
         "Mathlib/Logic/Unique.lean", "Mathlib/Order/Basic.lean")
QUOTA = {"Algebra": 2, "Data": 2, "CategoryTheory": 2, "Order": 1, "Logic": 1, "Combinatorics": 1,
         "Topology": 1, "GroupTheory": 1, "Tactic": 1}
LINES = (80, 500)
BOOT_SEED, BOOT_N = 20260923, 10000
INVOCATION = ["check", "--imports-prefer-olean", "--allow-sorry", "--json"]
IMP = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»']+)")
ASSERT_NOT_EXISTS = "B4d `assert_not_exists` (non-declaration command counted as a failed decl)"


def sha(path: str) -> str:
    return hashlib.sha256(path.encode("utf-8")).hexdigest()


def stem(path: str) -> str:
    return path.replace("Mathlib/", "").replace("/", "__")[:-5]


# ----------------------------------------------------------------------- pick
class Closure:
    """Import-closure walk over the Mathlib checkout (the audit's closure.py)."""

    def __init__(self, ml: str, toolchain_dir: str):
        pk = os.path.join(ml, ".lake/packages")
        pkgs = sorted(os.listdir(pk)) if os.path.isdir(pk) else []
        self.src_roots = [ml] + [os.path.join(pk, p) for p in pkgs] + [os.path.join(toolchain_dir, "src/lean")]
        self.olean_roots = ([os.path.join(ml, ".lake/build/lib/lean")]
                            + [os.path.join(pk, p, ".lake/build/lib/lean") for p in pkgs]
                            + [os.path.join(toolchain_dir, "lib/lean")])
        self._direct: Dict[str, List[str]] = {}
        self._built: Dict[str, bool] = {}
        self._full: Dict[str, bool] = {}

    def src_of(self, mod: str) -> Optional[str]:
        rel = mod.replace(".", "/") + ".lean"
        for r in self.src_roots:
            p = os.path.join(r, rel)
            if os.path.exists(p):
                return p
        return None

    def built(self, mod: str) -> bool:
        if mod not in self._built:
            rel = mod.replace(".", "/") + ".olean"
            self._built[mod] = any(os.path.exists(os.path.join(r, rel)) for r in self.olean_roots)
        return self._built[mod]

    def direct(self, mod: str) -> List[str]:
        if mod in self._direct:
            return self._direct[mod]
        out: List[str] = []
        p = self.src_of(mod)
        if p is not None:
            in_comment = False
            with open(p, encoding="utf-8", errors="replace") as f:
                for line in f:
                    s = line.strip()
                    if in_comment:
                        in_comment = "-/" not in s
                        continue
                    if s.startswith("/-!") or s.startswith("/--"):
                        break
                    if s.startswith("/-"):
                        in_comment = "-/" not in s[2:]
                        continue
                    if not s or s.startswith("--") or s == "module" or s.startswith("prelude"):
                        continue
                    m = IMP.match(line)
                    if not m:
                        break
                    out.append(m.group(1))
        self._direct[mod] = out
        return out

    def fully_built(self, mod: str) -> bool:
        """Every transitive import of `mod` has a built .olean (mod itself need not)."""
        stack, seen = [mod], set()
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            seen.add(m)
            for d in self.direct(m):
                if not self.built(d):
                    return False
                if d not in seen:
                    stack.append(d)
        return True

    def closure_size(self, mod: str) -> int:
        stack, seen = [mod], set()
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            seen.add(m)
            stack.extend(d for d in self.direct(m) if d not in seen)
        return len(seen) - 1


def pick(ml: str, toolchain_dir: str, quota: Dict[str, int]) -> List[dict]:
    cl = Closure(ml, toolchain_dir)
    by_group: Dict[str, List[dict]] = collections.defaultdict(list)
    for root, _dirs, fs in os.walk(os.path.join(ml, "Mathlib")):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(root, f), ml)
            parts = rel.split("/")
            if len(parts) < 3 or parts[1] not in quota or rel in SLICE:
                continue
            with open(os.path.join(ml, rel), encoding="utf-8", errors="replace") as fh:
                n = sum(1 for _ in fh)
            if LINES[0] <= n <= LINES[1]:
                by_group[parts[1]].append({"path": rel, "lines": n, "sha256": sha(rel)})
    sample = []
    for g, q in quota.items():
        pool = sorted((r for r in by_group[g] if cl.fully_built(r["path"][:-5].replace("/", "."))),
                      key=lambda r: r["sha256"])
        for r in pool[:q]:
            sample.append({"group": g, "path": r["path"], "lines": r["lines"],
                           "closure": cl.closure_size(r["path"][:-5].replace("/", ".")),
                           "sha256": r["sha256"], "pool": len(pool)})
    return sample


# ------------------------------------------------------------------------ run
def lean_path(ml: str, toolchain_dir: str) -> str:
    """The srcelab gate's LEAN_PATH composition, in its order."""
    parts = [os.path.join(ml, ".lake/build/lib/lean"), os.path.join(toolchain_dir, "lib/lean")]
    parts += sorted(glob.glob(os.path.join(ml, ".lake/packages/*/.lake/build/lib/lean")))
    return ":".join(p for p in parts if os.path.isdir(p))


def run(sample: List[dict], runs_dir: str, ml: str, toolchain_dir: str, clean_bin: str,
        with_lean: bool, timeout_s: float, cap_gb: float, weights: Dict[str, int]) -> None:
    os.makedirs(runs_dir, exist_ok=True)
    runner = os.path.abspath(__file__)
    env = dict(os.environ, LEAN_PATH=lean_path(ml, toolchain_dir))
    kinds = ["clean"] + (["lean"] if with_lean else [])
    for s in sample:
        for kind in kinds:
            if os.path.exists(os.path.join(runs_dir, "{}.{}.meta.json".format(stem(s["path"]), kind))):
                print("SKIP (already measured) {} {}".format(kind, s["path"]))
                continue
            cmd = [sys.executable, runner, "run-one", kind, s["path"], runs_dir, str(timeout_s),
                   str(cap_gb), ml, clean_bin, os.path.join(toolchain_dir, "bin/lean")]
            gate = os.path.join(os.path.dirname(os.path.abspath(__file__)), "heavy_gate.sh")
            if os.path.exists(gate):
                cmd = [gate, "run", str(weights[kind]), "breadth-{}-{}".format(kind, stem(s["path"])[:40]), "--"] + cmd
            print("START {} {}".format(kind, s["path"]), flush=True)
            subprocess.run(cmd, env=env, check=False)


def run_one(kind: str, rel: str, outdir: str, timeout_s: float, cap_gb: float, ml: str,
            clean_bin: str, lean_bin: str) -> dict:
    """One measured command under /usr/bin/time -l, a wall timeout and an RSS
    kill-cap over the whole process group (the audit's run_one.py). Writes
    <stem>.<kind>.out / .log / .meta.json; a cap hit is an outcome, not a verdict."""
    import signal
    import time
    os.makedirs(outdir, exist_ok=True)
    base = os.path.join(outdir, "{}.{}".format(stem(rel), kind))
    if kind == "clean":
        cmd = ["/usr/bin/time", "-l", clean_bin] + INVOCATION + [os.path.join(ml, rel)]
        cwd = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    else:
        cmd, cwd = ["/usr/bin/time", "-l", lean_bin, rel], ml
    cap_kb = cap_gb * 1024 * 1024

    def group_rss_kb(pgid: int) -> int:
        try:
            out = subprocess.run(["ps", "-A", "-o", "pgid=,rss="], capture_output=True, text=True).stdout
        except OSError:
            return 0
        return sum(int(p[1]) for p in (ln.split() for ln in out.splitlines()) if len(p) == 2 and p[0] == str(pgid))
    t0 = time.monotonic()
    outcome, peak = "completed", 0
    with open(base + ".out", "wb") as fo, open(base + ".log", "wb") as fe:
        p = subprocess.Popen(cmd, stdout=fo, stderr=fe, cwd=cwd, start_new_session=True)
        while True:
            try:
                p.wait(timeout=2)
                break
            except subprocess.TimeoutExpired:
                pass
            peak = max(peak, group_rss_kb(p.pid))
            if time.monotonic() - t0 > timeout_s:
                outcome = "timeout"
            elif peak > cap_kb:
                outcome = "memory-cap"
            if outcome != "completed":
                os.killpg(p.pid, signal.SIGTERM)
                time.sleep(5)
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                p.wait()
                break
    log = open(base + ".log", encoding="utf-8", errors="replace").read()
    m = re.search(r"(\d+)\s+maximum resident set size", log)
    tr = re.search(r"([\d.]+) real", log)
    meta = {"kind": kind, "path": rel, "cmd": cmd, "cwd": cwd, "outcome": outcome, "exit_code": p.returncode,
            "wall_s": round(time.monotonic() - t0, 1), "time_real_s": float(tr.group(1)) if tr else None,
            "peak_rss_gb_time_l": round(int(m.group(1)) / 2 ** 30, 2) if m else None,
            "peak_rss_gb_polled": round(peak / 2 ** 20, 2), "timeout_s": timeout_s, "rss_cap_gb": cap_gb,
            "finished_at": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    with open(base + ".meta.json", "w", encoding="utf-8") as f:
        json.dump(meta, f, indent=1)
    return meta


# ------------------------------------------------------------------ aggregate
BUNDLED = (r"(Equiv|ContinuousMap|MonoidHom|AddMonoidHom|RingHom|OrderIso|OrderEmbedding|Embedding|MulEquiv|"
           r"AddEquiv|[A-Z][A-Za-z]*Hom|[A-Z][A-Za-z]*Equiv|fvar#\d+)")
DECL_RX = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
                     r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|irreducible_def)\s+([^\s:({\[]+)",
                     re.M)
VAR_RX = re.compile(r"^\s*variable\b(.*)$", re.M)


def _parse_sub(e: str) -> str:
    if "raw declaration: In" in e:
        return "B4a `variable ... in` / `... in` command combinator"
    if re.search(r"'[⥤⋙⊗≌]'", e) or re.search(r"raw declaration: error-recovery", e) and ("⥤" in e or "⋙" in e):
        return "B4b imported Mathlib notation (⥤ ⋙ ...) unknown to the parser"
    if "unknown command `meta`" in e:
        return "B4c `meta` section / meta def (Lean 4.30 module system)"
    if re.search(r"unknown command `(MonoidWithZero|Monoid|OrderDual|Field)`", e):
        return ASSERT_NOT_EXISTS
    if re.search(r"unknown command `(toFun|continuous_toFun|map_continuous)`", e):
        return "B4e `protected` structure/class field"
    if "is not associative" in e or "Extends" in e or "Prod Sort" in e:
        return "B4f file-local mixfix notation / `extends` of a dotted parent"
    if "do block" in e or "do let binding" in e or "Return" in e:
        return "B4g do-notation (metaprogramming)"
    return "B4z other parser recovery"


RULES = [
    ("B1 partial explicit universe list (Category.{v} C) refused", lambda e: "Universe level count mismatch" in e),
    ("B2 coercion to function of a bundled map (CoeFun / DFunLike) not inserted",
     lambda e: re.search(r"Too many arguments: function type " + BUNDLED + r" ", e) is not None
     or re.search(r"cannot unify an application with a function type: " + BUNDLED, e) is not None
     or "cannot unify a free variable with a function type" in e
     or re.search(r"cannot unify an application with a free variable: " + BUNDLED, e) is not None),
    ("B3 numeral / NatCast / coercion target elaborates at Nat or wrong carrier",
     lambda e: re.search(r"(Nat vs fvar#\d+|got Nat \(cannot unify|HMul Nat fvar|Nat vs Quot|Quot \(Prod Nat Nat\)|"
                         r"rigid head/arity mismatch: Quot vs List)", e) is not None),
    ("B4 parser", lambda e: "Prod Sort" in e or "Parse error:" in e or "parser recovery" in e or "unsupported construct" in e),
    ("B6 attribute/export target not resolved",
     lambda e: "attribute target" in e or re.search(r"name '.*' not found in namespace", e) is not None),
    ("W4A grind no progress", lambda e: "grind: no progress" in e),
    ("W4C ext is funext-only", lambda e: "ext: left-hand side is not a function" in e),
    ("W4D kernel fvar leak / fvar mismatch",
     lambda e: "contains free variables" in e or "fvar mismatch" in e or "Unknown free variable" in e),
    ("instance synthesis", lambda e: "failed to synthesize instance" in e),
    ("unsolved goals after a tactic", lambda e: "unsolved goals" in e),
    ("unknown identifier (not a same-file name)", lambda e: "Unknown identifier" in e or "unknown identifier" in e),
    ("type mismatch (other)", lambda e: "Type mismatch" in e or "type mismatch" in e),
    ("too many arguments (other head)", lambda e: "Too many arguments" in e),
]
CASCADE = "cascade (names an identifier this file declares)"


def classify(e: str) -> str:
    for name, pred in RULES:
        if pred(e):
            return _parse_sub(e) if name == "B4 parser" else name
    return "other"


def _load_report(path: str) -> Optional[dict]:
    t = open(path, encoding="utf-8", errors="replace").read()
    i = t.find("{")
    if i < 0:
        return None
    try:
        obj, _ = json.JSONDecoder().raw_decode(t[i:])
    except ValueError:
        return None
    # v1: committed historical artifacts; v2 (2026-09-28): `sorry_axioms` is the
    # closure census rather than the minted-term count (see cmd_core.rs).
    return obj if obj.get("schema_version") in ("Clean-check-report-v1",
                                                "Clean-check-report-v2") else None


def classify_rows(report: dict, source: str) -> List[dict]:
    local = set(n.split(".")[-1] for n in DECL_RX.findall(source)) | {"mk"}
    for v in VAR_RX.findall(source):
        local |= set(re.findall(r"[^\W\d][\w'₀-₉]*", v))
    if 'notation "C("' in source:
        local.add("C")
    rows = []
    recovery = report.get("parser_recovery", [])
    for e in report.get("errors", []) + recovery:
        if e.startswith("parser recovery"):
            continue  # a note about source text, not a declaration
        decl = e.split(": elaboration error")[0] if ": elaboration error" in e else e.split(":")[0]
        m = re.search(r"[Uu]nknown identifier: (?:attribute target ')?([^\s;',]+)", e)
        ident = m.group(1).split(".")[-1] if m else None
        lm = re.search(r"at line (\d+)", e)
        notes = [n for n in recovery if lm and re.search(r"at line %s, column" % lm.group(1), n)]
        cls = classify(e + " || " + " ".join(notes) if "Parse error:" in e else e)
        if ident and ident in local and cls.startswith("unknown"):
            cls = CASCADE
        rows.append({"decl": decl, "class": cls, "error": e[:300]})
    return rows


def wilson(s: int, n: int, z: float = 1.96) -> List[float]:
    p = s / n
    den = 1 + z * z / n
    c = (p + z * z / (2 * n)) / den
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / den
    return [round(c - h, 4), round(c + h, 4)]


def cluster_bootstrap(rows: List[dict], seed: int = BOOT_SEED, n: int = BOOT_N) -> List[float]:
    """Resample FILES with replacement; the audit's exact procedure (seeded)."""
    random.seed(seed)
    boots = []
    for _ in range(n):
        pick_ = [random.choice(rows) for _ in rows]
        d = sum(x["decl_count"] for x in pick_)
        boots.append(sum(x["success"] for x in pick_) / d if d else 0)
    boots.sort()
    return [round(boots[int(0.025 * n)], 4), round(boots[int(0.975 * n)], 4)]


def pooled_block(rows: List[dict]) -> dict:
    done = [r for r in rows if isinstance(r.get("decl_count"), int)]
    s = sum(r["success"] for r in done)
    d = sum(r["decl_count"] for r in done)
    if not d:
        return {"files_measured": len(done), "pooled_success": 0, "pooled_decls": 0}
    return {"files_measured": len(done), "pooled_success": s, "pooled_decls": d,
            "pooled_rate": round(s / d, 4), "wilson95": wilson(s, d),
            "cluster_bootstrap95": cluster_bootstrap(done),
            "bootstrap": {"seed": BOOT_SEED, "resamples": BOOT_N, "unit": "file"},
            "mean_file_rate": round(sum(r["success"] / r["decl_count"] for r in done if r["decl_count"]) / len(done), 4)}


def walls_block(rows: List[dict]) -> dict:
    pooled: collections.Counter = collections.Counter()
    for r in rows:
        pooled.update(x["class"] for x in r.get("failing_rows", []))
    fw = collections.Counter(r["first_wall"] for r in rows if r.get("first_wall"))
    fs = collections.Counter(r["first_substantive_wall"] for r in rows if r.get("first_substantive_wall"))
    return {"failing_rows": sum(pooled.values()), "row_classes": dict(pooled.most_common()),
            "first_wall": dict(fw.most_common()), "first_substantive_wall": dict(fs.most_common())}


def aggregate(sample: List[dict], runs_dir: str, ml: str) -> List[dict]:
    rows = []
    for s in sample:
        st = stem(s["path"])
        row = {k: s[k] for k in ("group", "path", "lines", "closure", "sha256", "pool")}
        cm = os.path.join(runs_dir, st + ".clean.meta.json")
        if os.path.exists(cm):
            m = json.load(open(cm, encoding="utf-8"))
            row.update({"clean_outcome": m["outcome"], "clean_exit": m["exit_code"],
                        "clean_wall_s": m.get("time_real_s") or m.get("wall_s"),
                        "clean_peak_rss_gb": m.get("peak_rss_gb_time_l") or m.get("peak_rss_gb_polled")})
            rep = _load_report(os.path.join(runs_dir, st + ".clean.out"))
            if rep is not None:
                ts = rep.get("trust_summary") or {}
                src = open(os.path.join(ml, s["path"]), encoding="utf-8", errors="replace").read()
                fr = classify_rows(rep, src)
                subst = [x for x in fr if x["class"] != ASSERT_NOT_EXISTS]
                tm = rep.get("timing") if isinstance(rep.get("timing"), dict) else {}
                if tm:
                    row["clean_timing"] = {k: tm.get(k) for k in ("import_s", "elab_s", "total_s")}
                row.update({"decl_count": rep.get("decl_count"), "success": rep.get("success_count"),
                            "failed": rep.get("failed_count"), "diverged": rep.get("diverged_count", 0),
                            "sorry_axioms": ts.get("sorry_axioms"),
                            "parser_recovery": len(rep.get("parser_recovery", [])),
                            "first_wall": fr[0]["class"] if fr else None,
                            "first_substantive_wall": subst[0]["class"] if subst else None,
                            "failing_rows": fr})
        lm = os.path.join(runs_dir, st + ".lean.meta.json")
        if os.path.exists(lm):
            m = json.load(open(lm, encoding="utf-8"))
            row.update({"lean_outcome": m["outcome"], "lean_exit": m["exit_code"],
                        "lean_wall_s": m.get("time_real_s") or m.get("wall_s"),
                        "lean_peak_rss_gb": m.get("peak_rss_gb_time_l") or m.get("peak_rss_gb_polled")})
        rows.append(row)
    return rows


def artifact(sample: List[dict], rows: List[dict], date: str, provenance: dict) -> dict:
    return {
        "schema_version": SCHEMA,
        "date": date,
        "what": ("Mathlib SOURCE elaboration on a reproducible stratified sample outside the "
                 "five-file slice, measured exactly as `scripts/source_elab_gate.sh` measures the "
                 "slice. The headline is `pooled.pooled_rate` WITH `pooled.cluster_bootstrap95`; "
                 "the Wilson interval assumes independent declarations and understates the error."),
        "sample_rule": {"groups_and_quotas": QUOTA, "lines": list(LINES), "excluded": list(SLICE),
                        "order": "sha256 of the path string ascending, per group",
                        "eligibility": "every transitive import has a built .olean on the gate's LEAN_PATH"},
        "invocation": "clean " + " ".join(INVOCATION) + " <mathlib>/<path>  (LEAN_PATH as the gate composes it)",
        "provenance": provenance,
        "pooled": pooled_block(rows),
        "walls": walls_block(rows),
        "files": rows,
    }


# ------------------------------------------------------------- check-artifact
def check_artifact(a: dict) -> List[str]:
    p: List[str] = []
    if a.get("schema_version") != SCHEMA:
        return ["schema_version {!r} != {!r}".format(a.get("schema_version"), SCHEMA)]
    rows = a.get("files") or []
    if not rows:
        return ["no files -- an artifact of nothing measures nothing"]
    rule = a.get("sample_rule") or {}
    quota = rule.get("groups_and_quotas") or {}
    lo, hi = (rule.get("lines") or [None, None])[:2]
    by_group: Dict[str, List[dict]] = collections.defaultdict(list)
    for r in rows:
        by_group[r.get("group")].append(r)
        if r.get("sha256") != sha(str(r.get("path"))):
            p.append("{}: sha256 is not sha256 of its path".format(r.get("path")))
        if r.get("path") in (rule.get("excluded") or []):
            p.append("{}: a slice file in the breadth sample".format(r.get("path")))
        if not (isinstance(r.get("lines"), int) and lo <= r["lines"] <= hi):
            p.append("{}: {} lines is outside the rule's {}-{}".format(r.get("path"), r.get("lines"), lo, hi))
        if not str(r.get("path", "")).startswith("Mathlib/{}/".format(r.get("group"))):
            p.append("{}: not under its group {}".format(r.get("path"), r.get("group")))
        if isinstance(r.get("decl_count"), int) and not 0 <= r.get("success", -1) <= r["decl_count"]:
            p.append("{}: success {} outside 0..{}".format(r["path"], r.get("success"), r["decl_count"]))
    for g, q in quota.items():
        got = by_group.get(g, [])
        if len(got) != q:
            p.append("group {}: {} files, quota {}".format(g, len(got), q))
        shas = [r["sha256"] for r in got]
        if shas != sorted(shas):
            p.append("group {}: not in ascending sha256 order".format(g))
    extra = set(by_group) - set(quota)
    if extra:
        p.append("groups outside the rule: {}".format(sorted(extra)))
    if a.get("pooled") != pooled_block(rows):
        p.append("pooled block does not re-derive from the rows: recorded {} vs derived {}".format(
            a.get("pooled"), pooled_block(rows)))
    if a.get("walls") != walls_block(rows):
        p.append("walls block does not re-derive from the rows")
    for r in rows:
        fr = r.get("failing_rows")
        if fr is None:
            continue
        subst = [x for x in fr if x["class"] != ASSERT_NOT_EXISTS]
        if r.get("first_wall") != (fr[0]["class"] if fr else None) or \
                r.get("first_substantive_wall") != (subst[0]["class"] if subst else None):
            p.append("{}: first wall does not match its first failing row".format(r["path"]))
    return p


def series_key(a: dict) -> tuple:
    """Artifacts are comparable only over the same files on the same corpus."""
    return (tuple(sorted(str(r.get("path")) for r in a.get("files") or [])),
            str(((a.get("provenance") or {}).get("corpus") or {}).get("rev") or ""))


def ratchet_problems(prev: dict, cur: dict) -> List[str]:
    """`cur` may not lower a file's success count (or lose its measurement)
    against `prev` of the same series, unless it names the path in
    `accepted_regressions` with a reason."""
    if series_key(prev) != series_key(cur):
        return []
    accepted = {}
    for e in cur.get("accepted_regressions") or []:
        if isinstance(e, dict) and len(str(e.get("reason") or "").strip()) >= 12:
            accepted[e.get("path")] = e
    before = {r["path"]: r for r in prev.get("files") or []}
    p: List[str] = []
    for r in cur.get("files") or []:
        b = before.get(r["path"])
        if b is None or not isinstance(b.get("success"), int):
            continue
        now = r.get("success")
        if isinstance(now, int) and now >= b["success"]:
            continue
        if r["path"] in accepted:
            continue
        p.append("{}: success {} -> {} against the {} artifact of the same sample and corpus "
                 "(accept it in `accepted_regressions` with a reason, or fix it)".format(
                     r["path"], b["success"], now if isinstance(now, int) else "unmeasured ({})".format(
                         r.get("clean_outcome")), prev.get("date")))
    return p


# ------------------------------------------------------------------ self-test
def _selftest() -> int:
    fails = 0

    def check(name: str, cond: bool) -> None:
        nonlocal fails
        print("  {}: {}".format("PASS" if cond else "FAIL", name))
        fails += 0 if cond else 1

    def row(group: str, path: str, dc: int, ok: int, walls: List[str]) -> dict:
        fr = [{"decl": "d{}".format(i), "class": c, "error": "x"} for i, c in enumerate(walls)]
        subst = [x for x in fr if x["class"] != ASSERT_NOT_EXISTS]
        return {"group": group, "path": path, "lines": 100, "closure": 1, "sha256": sha(path), "pool": 1,
                "decl_count": dc, "success": ok, "failing_rows": fr,
                "first_wall": fr[0]["class"] if fr else None,
                "first_substantive_wall": subst[0]["class"] if subst else None}
    rows = [row("A", "Mathlib/A/x.lean", 10, 2, [ASSERT_NOT_EXISTS, "B1 x"]),
            row("B", "Mathlib/B/y.lean", 20, 10, ["B2 y"])]
    art = artifact([], rows, "2026-01-01", {})
    art["sample_rule"]["groups_and_quotas"] = {"A": 1, "B": 1}
    check("a built artifact re-derives", check_artifact(art) == [])
    check("pooled rate", art["pooled"]["pooled_success"] == 12 and art["pooled"]["pooled_decls"] == 30)
    check("first substantive wall skips assert_not_exists",
          art["walls"]["first_substantive_wall"] == {"B1 x": 1, "B2 y": 1})
    bad = json.loads(json.dumps(art))
    bad["pooled"]["pooled_success"] = 13
    check("a hand-edited pooled count is refused", bool(check_artifact(bad)))
    bad = json.loads(json.dumps(art))
    bad["files"][0]["success"] = 3
    check("a hand-edited row no longer re-derives the pooled block", bool(check_artifact(bad)))
    bad = json.loads(json.dumps(art))
    bad["files"][0]["path"] = "Mathlib/Logic/Basic.lean"
    check("a slice file / wrong group / wrong sha is refused", bool(check_artifact(bad)))
    bad = json.loads(json.dumps(art))
    bad["sample_rule"]["groups_and_quotas"]["A"] = 2
    check("a quota the rows do not meet is refused", bool(check_artifact(bad)))
    check("classification: partial universes", classify("Universe level count mismatch: expected 2, got 1").startswith("B1"))
    check("classification: variable-in raw declaration",
          classify("x: Parse error: parser recovery produced raw declaration: In").startswith("B4a"))
    check("wilson is symmetric-ish and inside [0,1]", 0 <= wilson(45, 296)[0] < wilson(45, 296)[1] <= 1)
    later = json.loads(json.dumps(art))
    later["date"] = "2026-02-01"
    later["files"][1]["success"] = 9
    check("the ratchet refuses a lower count in the same series", bool(ratchet_problems(art, later)))
    later["accepted_regressions"] = [{"path": "Mathlib/B/y.lean", "reason": "measured: a real regression, owned"}]
    check("an accepted, reasoned regression passes", ratchet_problems(art, later) == [])
    later["provenance"] = {"corpus": {"rev": "other"}}
    later.pop("accepted_regressions")
    check("a different corpus starts a new series", ratchet_problems(art, later) == [])
    print("SRCELAB_BREADTH_SELFTEST={} failed={}".format("ok" if fails == 0 else "fail", fails))
    return 0 if fails == 0 else 1


def _default_ml() -> str:
    env = os.environ.get("CLEAN_MATHLIB_DIR")
    if env:
        return env
    cands = sorted(glob.glob(os.path.expanduser("~/mathlib4-*")))
    return next((c for c in cands if os.path.isdir(os.path.join(c, ".lake/build/lib/lean"))), "")


def _toolchain_dir(ml: str) -> str:
    try:
        tc = open(os.path.join(ml, "lean-toolchain"), encoding="utf-8").read().strip()
    except OSError:
        return ""
    return os.path.expanduser("~/.elan/toolchains/" + tc.replace("/", "--", 1).replace(":", "---", 1))


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", nargs="?", choices=("pick", "run", "aggregate", "run-one"))
    ap.add_argument("rest", nargs="*", help=argparse.SUPPRESS)
    ap.add_argument("--mathlib", default=_default_ml())
    ap.add_argument("--sample")
    ap.add_argument("--runs-dir")
    ap.add_argument("--out")
    ap.add_argument("--date")
    ap.add_argument("--provenance", help="JSON object recorded verbatim in the artifact")
    ap.add_argument("--clean", default=os.environ.get("CLEAN_BIN") or "target/release/clean")
    ap.add_argument("--lean", action="store_true")
    ap.add_argument("--timeout", type=float, default=2400.0)
    ap.add_argument("--cap-gb", type=float, default=10.0)
    ap.add_argument("--check-artifact", nargs="*")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args(argv)
    if a.selftest:
        return _selftest()
    if a.check_artifact is not None:
        paths = a.check_artifact or [os.path.relpath(p, ROOT) if os.getcwd() == ROOT else p for p in
                                     sorted(glob.glob(os.path.join(ROOT, "reports/source-elab/breadth-*.json")))]
        if not paths:
            print("SRCELAB_BREADTH=failed:no-artifact")
            return 1
        bad = 0
        loaded = []
        for path in paths:
            probs = check_artifact(json.load(open(path, encoding="utf-8")))
            for pr in probs:
                print("  BREADTH {}: {}".format(path, pr), file=sys.stderr)
            if not probs:
                pb = json.load(open(path, encoding="utf-8"))["pooled"]
                print("  BREADTH {}: OK {}/{} = {} (cluster bootstrap 95% {})".format(
                    path, pb.get("pooled_success"), pb.get("pooled_decls"), pb.get("pooled_rate"),
                    pb.get("cluster_bootstrap95")))
            bad += bool(probs)
            loaded.append((path, json.load(open(path, encoding="utf-8"))))
        loaded.sort(key=lambda pa: str(pa[1].get("date")))
        rbad = 0
        for i, (path, cur) in enumerate(loaded):
            prev = next((q for _, q in reversed(loaded[:i]) if series_key(q) == series_key(cur)), None)
            for pr in ratchet_problems(prev, cur) if prev is not None else []:
                print("  BREADTH RATCHET {}: {}".format(path, pr), file=sys.stderr)
                rbad += 1
        verdict = "failed:artifact-inconsistent" if bad else ("failed:breadth-regression" if rbad else "artifact-ok")
        print("SRCELAB_BREADTH=" + verdict)
        return 1 if (bad or rbad) else 0
    if not a.mode:
        ap.error("a mode (pick/run/aggregate), --check-artifact or --selftest is required")
    if a.mode == "run-one":
        kind, rel, outdir, to, cap, ml, cb, lb = a.rest
        print(json.dumps(run_one(kind, rel, outdir, float(to), float(cap), ml, cb, lb)))
        return 0
    if not os.path.isdir(os.path.join(a.mathlib or "", "Mathlib")):
        print("no Mathlib checkout at {!r} (set --mathlib / CLEAN_MATHLIB_DIR)".format(a.mathlib), file=sys.stderr)
        return 2
    tcd = _toolchain_dir(a.mathlib)
    if a.mode == "pick":
        sample = pick(a.mathlib, tcd, QUOTA)
        text = json.dumps(sample, indent=1)
        if a.out:
            open(a.out, "w", encoding="utf-8").write(text + "\n")
        print(text)
        return 0
    if not a.sample or not a.runs_dir:
        ap.error("{} needs --sample and --runs-dir".format(a.mode))
    sample = json.load(open(a.sample, encoding="utf-8"))
    if a.mode == "run":
        run(sample, a.runs_dir, a.mathlib, tcd, os.path.abspath(a.clean), a.lean, a.timeout, a.cap_gb,
            {"clean": 7, "lean": 4})
        return 0
    if not a.out or not a.date:
        ap.error("aggregate needs --out and --date")
    prov = json.loads(a.provenance) if a.provenance else {}
    art = artifact(sample, aggregate(sample, a.runs_dir, a.mathlib), a.date, prov)
    with open(a.out, "w", encoding="utf-8") as f:
        json.dump(art, f, indent=1, ensure_ascii=False)
        f.write("\n")
    probs = check_artifact(art)
    print("wrote {} ({} problems)".format(a.out, len(probs)))
    return 1 if probs else 0


if __name__ == "__main__":
    sys.exit(main())
