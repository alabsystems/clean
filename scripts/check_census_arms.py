#!/usr/bin/env python3
"""Census arm-mutation gate (audit r6 class-closer, wf_a000d04d).

THE CLASS THIS CLOSES: a selftest arm that exists but does not KILL the
mutant it pins -- deleting the guarded refusal leaves the selftest green
because a SIBLING refusal fires instead, or because the arm tests its own
fixture rather than the real code. Audit r4 M2 found one (the indirect arm
never called the walk), audit r6 M1 found the r5 replacement arm wrapped to
a sibling refusal, and this gate's own dry run found THREE more
(partition, callee-oor, clause-b-bare) plus one genuine subsumption. Six
instances of one class; a class is closed by a gate.

THE INVARIANT: for every guard in the table below, deleting that guard from
a COPY of scripts/crystal_a0_census.py and running `--selftest` must exit
nonzero -- the arm pinning it must go RED. A row whose expect is
{"subsumed_by": T} is a documented defense-in-depth guard whose verdict
another guard fully covers: its single deletion MAY survive, but deleting
it TOGETHER with its subsumer must be killed, and its anchor is still
drift-checked. An anchor that no longer matches exactly once is REFUSED
(fail closed): the census moved and this table must be updated with it,
consciously.

Anchors are exact source blocks (the census file's own text). Every
replacement was verified to leave the file syntactically valid, so a kill
is the ARM firing, never a parse error.

A COPY RUNS WHAT THE CENSUS RUNS (M2, 2026-09-27). Since the census reads
trust-ir symbols through the shared reader `scripts/crystal_trust_ir_symbols.py`,
a copy of the census alone in a temp dir cannot even import. Every mutant is run
beside copies of the first-party modules the census DERIVES from its own imports
(`--pinned-inputs`, the answer check_gate_registry.py R7 pins), read from the
census's tree -- never a hand list, so a new import cannot be forgotten here.
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

CENSUS = "scripts/crystal_a0_census.py"
# The census's promise to answer `--pinned-inputs` (check_gate_registry.py's
# PINNED_INPUTS_MARKER, the same spelling).
PINNED_INPUTS_MARKER = re.compile(r"(?m)^ANSWERS_PINNED_INPUTS\s*=\s*True\s*$")

GUARDS = [
 {
  "tag": "partition",
  "anchor": "    for i, f in enumerate(funcs):\n        if (f[\"n\"] > 0) != (i < n):\n            raise SystemExit(f\"index fact 1 violated at entry {i} ({f['name']})\")\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "spliced-total",
  "anchor": "    if n != cov[\"totals\"][\"spliced\"]:\n        raise SystemExit(\n            f\"index fact 1 violated: {n} text bodies vs {cov['totals']['spliced']} spliced\"\n        )\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "invalid-fid",
  "anchor": "        if not isinstance(fid, int) or isinstance(fid, bool) or fid < 0:\n            # audit r5: a NEGATIVE func_id sailed through both `fid < n` and\n            # `fid >= n` via Python negative indexing and scored a declaration\n            # bodyful downstream. Audit r6: non-integer shapes (1.0, \"1\",\n            # True) crashed with a raw TypeError instead of refusing -- both\n            # are one refusal now, and the selftest asserts THIS message so a\n            # deleted guard cannot hide behind a sibling refusal.\n            raise SystemExit(f\"index fact 1 violated: invalid func_id {fid!r} \"\n                             f\"(negative or non-integer)\")\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "name-mismatch",
  "anchor": "        if fid >= n or name != b[\"def_path\"]:\n            raise SystemExit(\n                f\"index fact 1 violated: coverage func_id {fid} is {b['def_path']}, \"\n                f\"text ordinal is {funcs[fid]['name'] if fid < len(funcs) else '<oor>'}\"\n            )\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "callee-oor",
  "anchor": "    if ids and max(ids) >= len(funcs):\n        raise SystemExit(f\"index fact 2 violated: callee id {max(ids)} out of range\")\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "invalid-callee",
  "anchor": "    bad = [c for c in ids if not isinstance(c, int) or isinstance(c, bool) or c < 0]\n    if bad:\n        raise SystemExit(f\"index fact 2 violated: invalid callee id {bad[0]!r} \"\n                         f\"(negative or non-integer)\")\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "vacuous-edges",
  "anchor": "    if not any(c < n for c in ids):\n        raise SystemExit(\"index fact 2 violated: no call resolves inside the body prefix\")\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "symbol-refusal",
  "anchor": "        except tir_symbols.SymbolRefusal as exc:\n            raise SystemExit(f\"trust-ir text {path} line {ln_no}: {exc}\")\n",
  "replacement": "        except tir_symbols.SymbolRefusal:\n            fh = None\n",
  "expect": "killed"
 },
 {
  "tag": "walk-entry-indirect",
  "anchor": "    if indirect:\n        ok = False  # an indirect call's target is statically unknown: fail closed\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "walk-callee-indirect",
  "anchor": "        if funcs[c].get(\"indirect\"):\n            ok = False\n            indirect = True\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "discharge-indirect",
  "anchor": "    if indirect:\n        return False\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "wider-than-reality",
  "anchor": "    extra = entries - set(escapes)\n    if extra:\n        raise SystemExit(\n            f\"discharge table for {def_path} names callee(s) {sorted(extra)} that the \"\n            f\"walk does not find (walk escapes: {sorted(escapes)}) -- a table wider than \"\n            f\"reality is refused, not ignored\")\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "clause-a-residual",
  "anchor": "        if ent[\"clause\"] == \"a\" and not (\n            str(ent.get(\"model\") or \"\").strip() and str(ent.get(\"residual\") or \"\").strip()\n        ):\n            raise SystemExit(\n                f\"discharge entry {def_path}/{e} is clause (a) but names no model+residual \"\n                f\"-- an unnamed residual is a silence, which clause (a) exists to forbid\")\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "clause-b-bare",
  "anchor": "            if not th:\n                raise SystemExit(\n                    f\"discharge entry {def_path}/{e} is clause (b) but names NO theorem -- \"\n                    f\"an unreachability claim with no proof named is the fail-open hole \"\n                    f\"audit r1 M1 closed; refused\")\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "clause-b-unlisted",
  "anchor": "            if row is None:\n                raise SystemExit(\n                    f\"discharge entry {def_path}/{e} names theorem {th!r} that the target's \"\n                    f\"clause_b_theorems does not list -- refused\")\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "clause-b-unregistered",
  "anchor": "            if not where or not clause_b_theorem_registered(th, where, repo_root):\n                raise SystemExit(\n                    f\"clause_b theorem {th!r} is not registered at {where!r} -- a theorem \"\n                    f\"name nothing registers proves nothing; refused\")\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "path-constraint",
  "anchor": "    if not (norm.startswith(\"crates/\") and norm.endswith(\".rs\")):\n        return False\n",
  "replacement": "",
  "expect": {
   "subsumed_by": "realpath-symlink"
  }
 },
 {
  "tag": "realpath-symlink",
  "anchor": "    real = os.path.realpath(path)\n    crates_root = os.path.realpath(os.path.join(repo_root, \"crates\"))\n    if not (real.startswith(crates_root + os.sep) and real.endswith(\".rs\")):\n        return False\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "comment-blanking",
  "anchor": "    code = _blank_comments(src)\n",
  "replacement": "    code = src\n",
  "expect": "killed"
 },
 {
  "tag": "invalid-clause",
  "anchor": "        if ent.get(\"clause\") not in (\"a\", \"b\"):\n            raise SystemExit(f\"discharge entry {def_path}/{e} has no valid clause\")\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "parse-ir-indirect",
  "anchor": "        if INDIRECT.search(s):\n            cur[\"indirect\"] = True\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "parse-ir-fndef",
  "anchor": "        for c in FNDEF.finditer(s):\n            cur[\"callees\"].add(int(c.group(1)))\n",
  "replacement": "",
  "expect": "killed"
 },
 {
  "tag": "discharge-no-target",
  "anchor": "    if tgt is None:\n        return False\n",
  "replacement": "    if tgt is None:\n        return True\n",
  "expect": "killed"
 },
 {
  "tag": "target-for-none-table",
  "anchor": "    if discharge_table is None:\n        return None\n",
  "replacement": "    if discharge_table is None:\n        return {\"escaping_callees\": {}}\n",
  "expect": "killed"
 },
 {
  "tag": "escaping-callee-no-entry",
  "anchor": "        if ent is None:\n            return False\n",
  "replacement": "        if ent is None:\n            continue\n",
  "expect": "killed"
 }
]

def census_siblings(census_path):
    """The first-party modules the census runs besides itself, as absolute paths.

    DERIVED by the census (`--pinned-inputs`, run from its tree's root, whose
    output is repo-relative) when it promises to answer; a census that makes no
    promise imports nothing first-party, so nothing is copied. An answer that
    fails or names a missing file is a refusal, never an empty set."""
    census_path = os.path.abspath(census_path)
    with open(census_path, encoding="utf-8") as fh:
        if not PINNED_INPUTS_MARKER.search(fh.read()):
            return []
    root = os.path.dirname(os.path.dirname(census_path))
    r = subprocess.run([sys.executable, census_path, "--pinned-inputs"],
                       capture_output=True, text=True, cwd=root)
    rels = [ln.strip() for ln in r.stdout.splitlines() if ln.strip()]
    if r.returncode != 0 or not rels:
        raise SystemExit(f"census {census_path} promises --pinned-inputs but answered "
                         f"exit {r.returncode} with {len(rels)} path(s): "
                         f"{(r.stderr or r.stdout).strip()[-200:]}")
    out = []
    for rel in rels:
        p = os.path.join(root, rel)
        if not os.path.isfile(p):
            raise SystemExit(f"census {census_path} --pinned-inputs names {rel}, "
                             f"which is not a file under {root}")
        out.append(p)
    return out


def _run_selftest(src_text, workdir):
    p = os.path.join(workdir, "census_mutant.py")
    with open(p, "w", encoding="utf-8") as fh:
        fh.write(src_text)
    # cwd=workdir so the committed-table check inside the selftest skips
    # (FileNotFoundError pass-through) and only the synthetic arms judge.
    r = subprocess.run([sys.executable, p, "--selftest"],
                       capture_output=True, cwd=workdir, text=True)
    return r.returncode, r.stdout + r.stderr


def _killed(rc, out):
    # audit r7 minor 7: a kill must be the ARM firing ([RED] line or the
    # selftest's own refusal banner), never an incidental crash -- a
    # crash-kill hides that the arm is not actually watching, and a later
    # refactor can remove the crash and leave green. The census's refusal
    # helpers convert crashes into marker-red for exactly this reason.
    return rc != 0 and ("[RED]" in out or "arms misbehave" in out)


# Refusal sites that are deliberately NOT mutation-rows, each with its reason.
# A site may sit here only because deleting it CANNOT move a verdict (it
# crashes, or another row subsumes it); "hard to test" is not a reason.
UNLISTED_OK = {
    "isfile": "clause-b `where` that does not exist -- deletion crashes on open()",
    "tgt.get": "table read helpers; no verdict of their own",
    "arms misbehave": (
        "the selftest's OWN enforcement. It needs no row because deleting it makes "
        "EVERY other row's mutant survive at once -- measured 2026-09-01: 21 "
        "survivors, gate exit 1. A row of its own would report a false survivor, "
        "since with all arms passing its deletion changes nothing observable."),
    "SystemExit(__doc__)": "argv usage guard; deletion unpacks argv and crashes",
    "provenance argument": "provenance-arg parse; deletion crashes on split",
    "[RED] selftest arm": (
        "the arms' OWN reporting helpers (refuses/refuses_d), not census guards: "
        "deleting a `return False` there falls through to None, which is falsy, "
        "so the arm still fails and the selftest still reddens"),
}


def refusal_sites(src):
    """Every `return False` / `raise SystemExit` in the census, by line.

    AUDIT r10 M10-2: the defect was not a WRONG guard, it was an UNLISTED one
    -- `if tgt is None: return False` governs every body outside the discharge
    table, and no arm and no mutation row touched it, so flipping it to
    `return True` minted a0_complete_semantic 202 -> 604 with every gate green.
    Counting the guards is what makes a missing one visible.
    """
    import re as _re
    lines = src.split("\n")
    out = []
    for i, ln in enumerate(lines, 1):
        t = ln.strip()
        if t.startswith("#"):
            continue
        if not _re.match(r"(return False|raise SystemExit)\b", t):
            continue
        # A bare `return False` says nothing about WHICH guard it is, so carry
        # the nearest preceding condition line as context -- both the span
        # match and the UNLISTED_OK accounting need something identifiable
        # (audit r10: keying on the bare line made every account a no-op).
        ctx = ""
        for j in range(i - 2, max(0, i - 6), -1):
            c = lines[j].strip()
            if c and not c.startswith("#"):
                ctx = c
                break
        out.append((i, t[:60], ctx[:80]))
    return out


def check_coverage(census_path, guards):
    """Refusal sites NOT inside any GUARDS anchor, by exact line span.

    Precise by construction: each anchor is a verbatim block of the census, so
    its line span is found by locating it in the source; a refusal site is
    covered iff its line falls inside one. A loose substring match would report
    a comfortable number and mean nothing, which is the failure mode this whole
    gate exists to refuse.
    """
    src = open(census_path, encoding="utf-8").read()
    spans = []
    for g in guards:
        i = src.find(g["anchor"])
        if i < 0:
            continue
        first = src.count("\n", 0, i) + 1
        spans.append((first, first + g["anchor"].count("\n") - 1))
    uncovered = []
    for line, text, ctx in refusal_sites(src):
        if any(a <= line <= b for a, b in spans):
            continue
        if any(k in text or k in ctx for k in UNLISTED_OK):
            continue
        uncovered.append((line, f"{ctx} -> {text}" if ctx else text))
    return refusal_sites(src), uncovered


def check(census_path, guards):
    """Returns a list of failure strings; empty == green."""
    src = open(census_path, encoding="utf-8").read()
    fails = []
    by_tag = {g["tag"]: g for g in guards}
    siblings = census_siblings(census_path)
    with tempfile.TemporaryDirectory() as d:
        for sib in siblings:
            shutil.copy2(sib, os.path.join(d, os.path.basename(sib)))
        rc0, _ = _run_selftest(src, d)
        if rc0 != 0:
            return ["unmutated census selftest is RED -- fix that first"]
        for g in guards:
            if src.count(g["anchor"]) != 1:
                fails.append(f"{g['tag']}: anchor matches {src.count(g['anchor'])} times, "
                             f"not exactly once -- the census moved; update the table consciously")
                continue
            mutant = src.replace(g["anchor"], g["replacement"])
            rc, out = _run_selftest(mutant, d)
            if g["expect"] == "killed":
                if not _killed(rc, out):
                    how = "SURVIVED" if rc == 0 else "died WITHOUT an arm firing (incidental crash)"
                    fails.append(f"{g['tag']}: mutant {how} -- the arm pinning this guard "
                                 f"is vacuous")
            else:
                sub = by_tag.get(g["expect"].get("subsumed_by"))
                if sub is None:
                    fails.append(f"{g['tag']}: subsumed_by names no row in the table -- refused")
                    continue
                pair = mutant.replace(sub["anchor"], sub["replacement"])
                rc, out = _run_selftest(pair, d)
                if not _killed(rc, out):
                    fails.append(f"{g['tag']}: deleting this guard AND its subsumer "
                                 f"{sub['tag']} still survives -- the subsumption account is false")
    return fails


def selftest():
    """The gate's own refusals, demonstrated on every invocation."""
    ok = True
    with tempfile.TemporaryDirectory() as d:
        # a killing control: the guard is a refusal the selftest arms on --
        # unmutated, the refusal fires and the arm is satisfied (exit 0);
        # with the guard deleted, the arm goes RED (exit 1) = KILLED
        killing = ("def guarded():\n"
                   "    raise SystemExit('refusal fires')\n"
                   "try:\n"
                   "    guarded()\n"
                   "    vacuous = True\n"
                   "except SystemExit:\n"
                   "    vacuous = False\n"
                   "if vacuous:\n"
                   "    raise SystemExit('[RED] arm: refusal did not fire')\n"
                   "print('ok')\n")
        kp = os.path.join(d, "killing.py")
        open(kp, "w").write(killing)
        if check(kp, [{"tag": "g",
                       "anchor": "    raise SystemExit('refusal fires')\n",
                       "replacement": "    pass\n", "expect": "killed"}]):
            print("  [RED] census-arms selftest: killing control reported vacuous")
            ok = False
        # a vacuous case: deleting the 'guard' changes nothing -> must be refused
        vac = "import sys\nGUARD = 1\nprint('always green')\n"
        vp = os.path.join(d, "vacuous.py")
        open(vp, "w").write(vac)
        if not check(vp, [{"tag": "g", "anchor": "GUARD = 1\n",
                           "replacement": "", "expect": "killed"}]):
            print("  [RED] census-arms selftest: vacuous arm was NOT refused")
            ok = False
        # anchor drift: an anchor matching nothing is refused
        if not check(vp, [{"tag": "g", "anchor": "NO SUCH TEXT\n",
                           "replacement": "", "expect": "killed"}]):
            print("  [RED] census-arms selftest: drifted anchor was NOT refused")
            ok = False
        # audit r7 minor 6: a FALSE subsumption account is refused -- deleting
        # the guard and its claimed subsumer together changes nothing here
        vac2 = "GUARD_A = 1\nGUARD_B = 2\nprint('always green')\n"
        v2 = os.path.join(d, "vac2.py")
        open(v2, "w").write(vac2)
        if not check(v2, [
                {"tag": "a", "anchor": "GUARD_A = 1\n", "replacement": "",
                 "expect": {"subsumed_by": "b"}},
                {"tag": "b", "anchor": "GUARD_B = 2\n", "replacement": "", "expect": "killed"}]):
            print("  [RED] census-arms selftest: false subsumption was NOT refused")
            ok = False
        # ...and a subsumed_by naming no row is refused cleanly, not a crash
        if not check(v2, [{"tag": "a", "anchor": "GUARD_A = 1\n", "replacement": "",
                           "expect": {"subsumed_by": "ghost"}}]):
            print("  [RED] census-arms selftest: missing subsumer tag was NOT refused")
            ok = False
        # red-baseline: a census whose UNMUTATED selftest is red is refused
        red = "raise SystemExit('always red')\n"
        rp = os.path.join(d, "red.py")
        open(rp, "w").write(red)
        if not check(rp, [{"tag": "g", "anchor": "always", "replacement": "", "expect": "killed"}]):
            print("  [RED] census-arms selftest: red baseline was NOT refused")
            ok = False
        # M2: a census that IMPORTS a sibling (as the real one imports the shared
        # symbol reader) runs beside a copy of it. Without the copy its unmutated
        # selftest cannot import and the gate refuses it as red; with it, the
        # killing control is judged exactly as above.
        sd = os.path.join(d, "tree", "scripts")
        os.makedirs(sd)
        open(os.path.join(sd, "sib_helper.py"), "w").write(
            "def guarded():\n    raise SystemExit('refusal fires')\n")
        sib_census = ("import os, sys\n"
                      "sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))\n"
                      "import sib_helper\n"
                      "ANSWERS_PINNED_INPUTS = True\n"
                      "if sys.argv[1:] == ['--pinned-inputs']:\n"
                      "    print('scripts/sib_helper.py')\n"
                      "    raise SystemExit(0)\n"
                      "try:\n"
                      "    sib_helper.guarded()\n"
                      "    vacuous = True\n"
                      "except SystemExit:\n"
                      "    vacuous = False\n"
                      "if vacuous:\n"
                      "    raise SystemExit('[RED] arm: refusal did not fire')\n"
                      "print('ok')\n")
        sp = os.path.join(sd, "sib_census.py")
        open(sp, "w").write(sib_census)
        guard = [{"tag": "g", "anchor": "    sib_helper.guarded()\n",
                  "replacement": "    pass\n", "expect": "killed"}]
        if check(sp, guard):
            print("  [RED] census-arms selftest: a census importing a sibling was not "
                  "run beside a copy of it")
            ok = False
        # ...and a census that promises --pinned-inputs but names a missing file
        # is refused, never run with an incomplete copy.
        open(sp, "w").write(sib_census.replace("scripts/sib_helper.py", "scripts/no_such.py"))
        try:
            check(sp, guard)
        except SystemExit as e:
            if "not a file" not in str(e):
                print(f"  [RED] census-arms selftest: missing sibling refused by the WRONG guard: {e}")
                ok = False
        else:
            print("  [RED] census-arms selftest: a missing pinned input was NOT refused")
            ok = False
    if not ok:
        raise SystemExit("check_census_arms selftest: arms misbehave")
    print("check_census_arms selftest: 8/8 arms behave")


def main(argv):
    if len(argv) > 1 and argv[1] == "--selftest":
        selftest()
        return 0
    selftest()
    fails = check(CENSUS, GUARDS)
    if fails:
        print("CENSUS ARM-MUTATION GATE: FAIL", file=sys.stderr)
        for f in fails:
            print(f"  {f}", file=sys.stderr)
        return 1
    killed = sum(1 for g in GUARDS if g["expect"] == "killed")
    sites, uncovered = check_coverage(CENSUS, GUARDS)
    if uncovered:
        print("CENSUS ARM-MUTATION GATE: FAIL -- refusal sites that no GUARDS row "
              "mutates and that are not accounted in UNLISTED_OK:", file=sys.stderr)
        for line, text in uncovered:
            print(f"  {CENSUS}:{line}  {text}", file=sys.stderr)
        print("  An UNLISTED guard is how audit r10 M10-2 happened: `tgt is None` "
              "governed every body outside the discharge table, no row mutated it, "
              "and flipping it minted a0_complete_semantic 202 -> 604 with every "
              "gate green. Add a GUARDS row, or account the site in UNLISTED_OK "
              "with the reason its deletion cannot move a verdict.", file=sys.stderr)
        return 1
    print(f"CENSUS_ARMS=ok guards={len(GUARDS)} killed={killed} "
          f"subsumed={len(GUARDS) - killed} refusal_sites={len(sites)} "
          f"all_mutated_or_accounted")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
