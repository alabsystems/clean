#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""The controls of scripts/kcheck_coverage.py, run by its --self-test.

One planted defect per arm, and each arm names the refusal it expects, so an
arm that is turned away for another reason fails. The second half runs the
real `check()` on a scratch tree: that is the command the gate runs.
"""

from __future__ import annotations

import gzip
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path


def run(kc) -> int:
    """A small export, an honest run of it written by hand, a scratch tree, and one planted defect per arm."""
    records = [
        {"meta": {"format": {"version": "3.1.0"}}},
        {"in": 1, "str": {"pre": 0, "str": "id"}},
        {"in": 2, "str": {"pre": 0, "str": "u"}},
        {"il": 1, "param": 2},
        {"ie": 0, "sort": 1},
        {"ie": 1, "bvar": 0},
        {"ie": 2, "bvar": 1},
        {"ie": 3, "forallE": {"name": 0, "type": 1, "body": 2, "binderInfo": "default"}},
        {"ie": 4, "forallE": {"name": 0, "type": 0, "body": 3, "binderInfo": "implicit"}},
        {"ie": 5, "lam": {"name": 0, "type": 1, "body": 1, "binderInfo": "default"}},
        {"ie": 6, "lam": {"name": 0, "type": 0, "body": 5, "binderInfo": "implicit"}},
        {"def": {"name": 1, "levelParams": [2], "type": 4, "value": 6, "safety": "safe", "hints": {"regular": 1}, "all": [1]}},
        {"in": 3, "str": {"pre": 0, "str": "ax"}},
        {"axiom": {"name": 3, "levelParams": [], "type": 0, "isUnsafe": False}},
        {"in": 4, "str": {"pre": 0, "str": "user"}},
        {"ie": 7, "const": {"name": 1, "us": [1]}},
        {"def": {"name": 4, "levelParams": [2], "type": 4, "value": 7, "safety": "safe", "hints": {"regular": 2}, "all": [4]}},
        {"in": 5, "str": {"pre": 0, "str": "lit"}},
        {"ie": 8, "natVal": "0"},
        {"def": {"name": 5, "levelParams": [], "type": 0, "value": 8, "safety": "safe", "hints": "abbrev", "all": [5]}},
    ]
    export_raw = "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in records).encode("utf-8")
    frame = bytes([0x01, 0x28, *[0x16] * 7, 0x02])  # what the checker accepts for `id` in the real export
    one = bytes([len(frame)]) + frame
    advice = one + b"\x00" + one + b"\x00"
    type_echo = "(pi (sort (p 0)) (pi (b 0) (b 1)))"
    row_id = ["decl\t12\tdef\taccepted\tbound=1;0+1 iota=0 k=0 lparams=1\t[s2:id]", f"stmt\t12\t{type_echo}\t(lam (sort (p 0)) (lam (b 0) (b 0)))"]
    row_ax = ["decl\t14\taxiom\toutside\taxiomDecl\t[s2:ax]"]
    row_user = ["decl\t17\tdef\taccepted\tbound=1;0+1 iota=0 k=0 lparams=1\t[s4:user]", f"stmt\t17\t{type_echo}\t(c [s2:id] (p 0))"]
    row_lit = ["decl\t20\tdef\toutside\tliteral\t[s3:lit]"]
    body = row_id + row_ax + row_user + row_lit
    tail = "summary\tdeclarations=4\taccepted=2\trecognised=0\toutside=2\trefused=0"

    def transcript(lines=body, summary=tail, headers=kc.HEADERS) -> str:
        return "\n".join([*headers, *lines, summary]) + "\n"

    def counts(**change) -> str:
        fields = {"declarations": 4, "accepted": 2, "recognised": 0, "outside": 2, "refused": 0, **change}
        return "summary\t" + "\t".join(f"{k}={v}" for k, v in fields.items())

    failures, ran = [], 0

    def expect(label: str, kind, needle: str, call) -> None:
        nonlocal ran
        ran += 1
        try:
            call()
        except (kc.Refused, kc.Stale) as err:
            if kind is None:
                failures.append(f"{label}: an honest input was turned away: {err}")
            elif not isinstance(err, kind) or needle not in str(err):
                failures.append(f"{label}: turned away as {type(err).__name__} for another reason: {err}")
        except Exception as err:  # noqa: BLE001 - a traceback is itself the defect an arm looks for
            failures.append(f"{label}: {type(err).__name__} instead of a verdict: {err}")
        else:
            if kind is not None:
                failures.append(f"{label}: a planted defect was accepted")

    honest = kc.derive(export_raw, advice, transcript())
    ran += 1
    if (honest["accepted"], honest["inside_fragment"], honest["ordinary_declarations"]) != (2, 2, 3):
        failures.append(f"honest run: wrong figures {honest}")
    refused_user = ["decl\t17\tdef\trefused\tdependency:[s2:id]\t[s4:user]"]
    refused_id = ["decl\t12\tdef\trefused\tKCheck.Refusal.sort\t[s2:id]"]
    drift = [
        ("statement swapped", "not the one the export states", advice, transcript([row_id[0], row_id[1].replace("(b 1)", "(b 0)"), *row_ax, *row_user, *row_lit])),
        ("fragment row printed outside", "independent classifier", advice, transcript(["decl\t12\tdef\toutside\tliteral\t[s2:id]", *row_ax, *row_user, *row_lit], counts(accepted=1, outside=3))),
        ("axiom accepted", "independent classifier", advice, transcript([*row_id, "decl\t14\taxiom\taccepted\tbound=0 iota=0 k=0 lparams=0\t[s2:ax]", "stmt\t14\t(sort (p 0))\t(sort (p 0))", *row_user, *row_lit], counts(accepted=3, outside=1))),
        ("literal accepted", "independent classifier", advice, transcript([*row_id, *row_ax, *row_user, "decl\t20\tdef\taccepted\tbound=0 iota=0 k=0 lparams=0\t[s3:lit]", "stmt\t20\t(sort (p 0))\t(sort (p 0))"], counts(accepted=3, outside=1))),
        ("row dropped", "on other lines", one + b"\x00" + one, transcript(body[:-1], counts(declarations=3, outside=1))),
        ("row stated twice", "stated twice", advice, transcript([*row_id, *row_ax, *row_user, *row_lit, *row_lit], counts(declarations=5, outside=3))),
        ("rows out of order", "not in file order", advice, transcript([*row_ax, *row_id, *row_user, *row_lit])),
        ("summary inflated", "summary line says", advice, transcript(summary=counts(accepted=3))),
        ("summary key twice", "summary line is malformed", advice, transcript(summary=tail + "\taccepted=2")),
        ("header changed", "header lines", advice, transcript(headers=(kc.HEADERS[0], kc.HEADERS[1].replace("not-claimed-by-this-run", "proved"), *kc.HEADERS[2:]))),
        ("no final line feed", "does not end with a line feed", advice, transcript()[:-1]),
        ("carriage returns", "carriage return", advice, transcript().replace("\n", "\r\n")),
        ("no summary", "no summary line", advice, "\n".join([*kc.HEADERS, *body]) + "\n"),
        ("unknown line", "no known shape", advice, transcript([*body, "note\thello"])),
        ("unknown class", "not one of version 1's", advice, transcript([row_id[0].replace("accepted", "admitted"), *row_ax, *row_user, *row_lit])),
        ("statement missing", "go together", advice, transcript([row_id[0], *row_ax, *row_user, *row_lit])),
        ("statement after a refused row", "does not follow", b"\x00\x00\x00\x00", transcript([*refused_id, row_id[1], *row_ax, *refused_user, *row_lit], counts(accepted=0, refused=2))),
        ("statement stated twice", "does not follow", advice, transcript([*row_id, row_id[1], *row_ax, *row_user, *row_lit])),
        ("name changed", "the transcript names", advice, transcript([row_id[0].replace("[s2:id]", "[s2:di]"), row_id[1], *row_ax, *row_user, *row_lit])),
        ("kind changed", "says kind", advice, transcript([row_id[0].replace("\tdef\t", "\tthm\t"), row_id[1], *row_ax, *row_user, *row_lit])),
        ("frame count", "frames for", advice + b"\x00", transcript()),
        ("frame off the fragment", "not inside the fragment", one + b"\x01\x16" + one + b"\x00", transcript()),
        ("accepted on no advice", "empty advice frame", b"\x00\x00" + one + b"\x00", transcript()),
        ("frame length not minimal", "not minimal", b"\x84\x00" + frame + b"\x00" + one + b"\x00", transcript()),
        ("frame runs past the end", "the advice ends first", one + b"\x00" + one + b"\x05", transcript()),
        ("advice ends inside a length", "inside a frame length", one + b"\x00" + one + b"\x80", transcript()),
        ("accepted over a refused dependency", "which the run did not accept", b"\x00\x00" + one + b"\x00", transcript([*refused_id, *row_ax, *row_user, *row_lit], counts(accepted=1, refused=1))),
        ("refused for a dependency that was accepted", "exactly when", one + b"\x00\x00\x00", transcript([*row_id, *row_ax, *refused_user, *row_lit], counts(accepted=1, refused=1))),
        ("dependency refusal names another declaration", "it does not cite", b"\x00\x00\x00\x00", transcript([*refused_id, *row_ax, refused_user[0].replace("[s2:id]", "[s2:ax]"), *row_lit], counts(accepted=0, refused=2))),
    ]
    for label, needle, advice_bytes, text in drift:
        expect(label, kc.Refused, needle, lambda a=advice_bytes, t=text: kc.derive(export_raw, a, t))
    expect("export changed under the run", kc.Refused, "not the one the export states",
           lambda: kc.derive(export_raw.replace(b'"type":4,"value":6', b'"type":4,"value":4'), advice, transcript()))
    def enc(rows) -> bytes:
        return "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in rows).encode("utf-8")

    def framed(*frames: bytes) -> bytes:
        return b"".join(bytes([len(f)]) + f for f in frames)

    # One spelling, two names: `x.y` as one component (a definition) and `x` then `y` (an axiom). A declaration
    # citing the axiom is outside, whatever a reader that keys constants by a dotted string would say.
    twins = [{"in": 6, "str": {"pre": 0, "str": "x.y"}}, {"in": 7, "str": {"pre": 0, "str": "x"}}, {"in": 8, "str": {"pre": 7, "str": "y"}},
             {"def": {"name": 6, "levelParams": [2], "type": 0, "value": 0, "safety": "safe", "hints": "abbrev", "all": [6]}},
             {"axiom": {"name": 8, "levelParams": [2], "type": 0, "isUnsafe": False}},
             {"ie": 9, "const": {"name": 8, "us": [1]}}, {"in": 9, "str": {"pre": 0, "str": "w"}},
             {"def": {"name": 9, "levelParams": [2], "type": 0, "value": 9, "safety": "safe", "hints": "abbrev", "all": [9]}}]
    twin_rows = ["decl\t24\tdef\trefused\tKCheck.Refusal.sort\t[s3:x.y]", "decl\t25\taxiom\toutside\taxiomDecl\t[s1:x s1:y]"]
    twin_tail = counts(declarations=7, outside=4, refused=1)
    expect("an axiom spelled like a definition stays an axiom", None, "",
           lambda: kc.derive(export_raw + enc(twins), advice + b"\x00\x00\x00", transcript([*body, *twin_rows, "decl\t28\tdef\toutside\tcites:[s1:x s1:y]\t[s1:w]"], twin_tail)))
    expect("a declaration citing that axiom printed accepted", kc.Refused, "independent classifier",
           lambda: kc.derive(export_raw + enc(twins), advice + b"\x00\x00" + one, transcript(
               [*body, *twin_rows, "decl\t28\tdef\taccepted\tbound=1 iota=0 k=0 lparams=1\t[s1:w]", "stmt\t28\t(sort (p 0))\t(c [s1:x s1:y] (p 0))"],
               counts(declarations=7, accepted=3, outside=3, refused=1))))

    # The accepted row's detail is what the frame and the export give, read token by token.
    def detail(text: str, first: bytes = frame) -> tuple:
        return framed(first, b"", frame, b""), transcript([row_id[0].replace("bound=1;0+1 iota=0 k=0 lparams=1", text), row_id[1], *row_ax, *row_user, *row_lit])

    iota_frame = bytes([0x01, 0x28, 0x0B, *[0x16] * 6, 0x02])
    expect("an operand byte is not a tag", None, "", lambda: kc.derive(export_raw, *detail("bound=1;0+1 iota=0 k=0 lparams=1", bytes([0x01, 0x0B, *[0x16] * 7, 0x02]))))
    expect("an iota frame reported as one", None, "", lambda: kc.derive(export_raw, *detail("bound=1;0+1 iota=1 k=0 lparams=1", iota_frame)))
    for label, needle, forged in [
        ("level parameters miscounted", "level parameters", detail("bound=1;0+1 iota=0 k=0 lparams=2")),
        ("a detail in free text", "not the one this frame gives", detail("bound=1 proved-sound")),
        ("iota reported with no such token", "not the one this frame gives", detail("bound=1;0+1 iota=1 k=0 lparams=1")),
        ("an iota token unreported", "not the one this frame gives", detail("bound=1;0+1 iota=0 k=0 lparams=1", iota_frame)),
        ("a byte that is no tag", "token's tag", detail("bound=1;0+1 iota=0 k=0 lparams=1", bytes([0x01, 0x28, 0x17, 0x02]))),
        ("an outside reason in free text", "not one version 1 prints", (advice, transcript([*row_id, "decl\t14\taxiom\toutside\tnot-needed\t[s2:ax]", *row_user, *row_lit]))),
        ("summary keys in another order", "summary line is malformed", (advice, transcript(summary="summary\taccepted=2\tdeclarations=4\trecognised=0\toutside=2\trefused=0"))),
    ]:
        expect(label, kc.Refused, needle, lambda f=forged: kc.derive(export_raw, *f))

    # What the checker's own reader refuses in an export, this reader refuses too.
    def swapped(old: bytes, new: bytes) -> bytes:
        assert export_raw.count(old) == 1, old
        return export_raw.replace(old, new)

    def block(**second) -> list:
        """Name records and a two-type `inductive` record; `second` changes fields of the second type."""
        row = {"levelParams": [], "type": 0, "numParams": 0, "numIndices": 0, "all": [6, 7], "ctors": [], "numNested": 0,
               "isRec": False, "isUnsafe": False, "isReflexive": False}
        return [{"in": 6, "str": {"pre": 0, "str": "T"}}, {"in": 7, "str": {"pre": 0, "str": "U"}},
                {"inductive": {"types": [{"name": 6, **row}, {"name": 7, **row, **second}], "ctors": [], "recs": []}}]

    for label, needle, forged in [
        ("an empty line", "export line 2", export_raw.replace(b"\n", b"\n\n", 1)),
        ("a key written twice", "written twice", swapped(b'{"in":1,', b'{"in":1,"in":1,')),
        ("a second meta record", "second meta", export_raw + enc(records[:1])),
        ("another format version", "format version 3.1.0", swapped(b'"3.1.0"', b'"3.2.0"')),
        ("an index out of sequence", "out of sequence", swapped(b'{"in":2,', b'{"in":3,')),
        ("an index cited before its line", "before any line defines it", swapped(b'{"ie":0,"sort":1}', b'{"ie":0,"sort":2}')),
        ("a key the reader does not know", "keys are not exactly", swapped(b'"hints":{"regular":1},', b'"hints":{"regular":1},"proved":true,')),
        ("a name declared twice", "declared by two records", export_raw + enc([records[11]])),
        ("one name under two indices", "an earlier name record gave", export_raw + enc([{"in": 6, "str": {"pre": 0, "str": "id"}}])),
        ("a level parameter listed twice", "listed twice", swapped(b'"levelParams":[2],"type":4,"value":6', b'"levelParams":[2,2],"type":4,"value":6')),
        ("an escape", "an escape", swapped(b'"str":"ax"', b'"str":"a\\u0078"')),
        ("a space", "plain spelling", swapped(b'{"in":1,', b'{"in": 1,')),
        ("a literal with a leading zero", "natVal", swapped(b'"natVal":"0"', b'"natVal":"00"')),
        ("a count that is no number", "where an index or a count", swapped(b'{"regular":2}', b'{"regular":"2"}')),
        ("no final line feed", "not ended by a line feed", export_raw[:-1]),
        ("a fraction where nothing reads it", "the number 1.5", swapped(b'{"meta":{', b'{"meta":{"x":1.5,')),
        ("a constant that is no number", "the number NaN", swapped(b'{"meta":{', b'{"meta":{"x":NaN,')),
        ("a negative number", "the number -2", swapped(b'{"regular":2}', b'{"regular":-2}')),
        ("a format object with a key more", "format version 3.1.0", swapped(b'{"version":"3.1.0"}', b'{"version":"3.1.0","x":1}')),
        ("an object where names are listed", "where an array is expected", swapped(b'"all":[5]', b'"all":{}')),
        ("a string where levels are listed", "where an array is expected", swapped(b'"us":[1]', b'"us":""')),
        ("an object where level parameters are listed", "where an array is expected", swapped(b'"levelParams":[],"type":0,"isUnsafe"', b'"levelParams":{},"type":0,"isUnsafe"')),
        ("bytes that are not UTF-8", "not UTF-8", export_raw + b"\xff\n"),
        ("a name cited before its line", "name 9 is cited before", swapped(b'{"pre":0,"str":"ax"}', b'{"pre":9,"str":"ax"}')),
        ("a flag that is no boolean", "is not a boolean", swapped(b'"isUnsafe":false', b'"isUnsafe":0')),
        ("hints of no known kind", "def.hints", swapped(b'"hints":"abbrev"', b'"hints":"fast"')),
        ("a safety of no known kind", "def.safety", swapped(b'"safety":"safe","hints":{"regular":1}', b'"safety":"sound","hints":{"regular":1}')),
        ("a name record with a key more", "a name record of another shape", swapped(b'{"pre":0,"str":"ax"}', b'{"pre":0,"str":"ax","x":1}')),
        ("a name holding a line separator", "U+0085", swapped(b'"str":"ax"', '"str":"a\u2028x"'.encode("utf-8"))),
        ("a level out of sequence", "a level record out of sequence", swapped(b'{"il":1,', b'{"il":2,')),
        ("a level of no known kind", "a level record of kind", swapped(b'{"il":1,"param":2}', b'{"il":1,"zero":2}')),
        ("a level past the node cap", "a level of more than", export_raw + enc([{"il": n, "max": [n - 1, n - 1]} for n in range(2, 24)])),
        ("a record of no known kind", "a record of no known kind", export_raw + enc([{"structure": {}}])),
        ("an expression out of sequence", "an expression record out of sequence", swapped(b'{"ie":1,"bvar":0}', b'{"ie":9,"bvar":0}')),
        ("an expression with a key more", "ie.const: the keys", swapped(b'"const":{"name":1,"us":[1]}', b'"const":{"name":1,"us":[1],"x":1}')),
        ("a binder annotation of no known kind", "binderInfo 'explicit'", swapped(b'"body":2,"binderInfo":"default"', b'"body":2,"binderInfo":"explicit"')),
        ("a let whose nondep is no boolean", "letE.nondep", export_raw + enc([{"ie": 9, "letE": {"name": 0, "type": 0, "value": 0, "body": 0, "nondep": 0}}])),
        ("an expression past the node cap", "an expression of more than", export_raw + enc([{"ie": n, "app": {"fn": n - 1, "arg": n - 1}} for n in range(9, 31)])),
        ("an inductive record with a key missing", "inductive: the keys", export_raw + enc([{"inductive": {"types": [], "ctors": []}}])),
        ("an inductive record with no type", "no type", export_raw + enc([{"inductive": {"types": [], "ctors": [], "recs": []}}])),
        ("a block whose types disagree on level parameters", "different level parameters", export_raw + enc(block(levelParams=[2]))),
        ("a block whose types disagree on numParams", "different numParams", export_raw + enc(block(numParams=1))),
        ("a block whose constructors are not its types' lists", "ctors lists in order", export_raw + enc(block(ctors=[6]))),
    ]:
        expect(f"export: {label}", kc.Refused, needle, lambda e=forged: kc.derive(e, advice, transcript()))
    expect("export: a level parameter the record does not list", kc.Refused, "does not list", lambda: kc.derive(
        swapped(b'"levelParams":[2],"type":4,"value":6', b'"levelParams":[],"type":4,"value":6'), advice,
        transcript([row_id[0].replace("lparams=1", "lparams=0"), row_id[1], *row_ax, *row_user, *row_lit])))

    # The base families, on the real export: recognised by the whole record, recursor and rules included.
    real = gzip.decompress((kc.ROOT / kc.EXPORT).read_bytes())
    real_lines = real.decode("utf-8").split("\n")

    def classes(change=None) -> dict:
        lines = list(real_lines)
        if change:
            line, edit = change
            block = json.loads(lines[line - 1])
            edit(block["inductive"])
            lines[line - 1] = json.dumps(block, separators=(",", ":"), ensure_ascii=False)
        return kc.readers.classify(kc.readers.Raw("\n".join(lines).encode("utf-8")))[1]

    def inside(rows: dict) -> int:
        return sum(1 for row in rows.values() if row[3] == "inside")

    ran += 1
    honest_rows = classes()
    if [line for line, row in honest_rows.items() if row[3] == "recognised"] != [51, 68, 1662] or inside(honest_rows) != 22:
        failures.append("base families: the real export's Nat, PUnit and Eq are not exactly the recognised records, or 22 is not the count inside")
    for label, line, edit in [
        ("Nat with no recursor", 51, lambda b: b.update(recs=[])),
        ("Nat's recursor under another name", 51, lambda b: b["recs"][0].update(name=4)),
        ("Nat's recursor with a rule's fields miscounted", 51, lambda b: b["recs"][0]["rules"][1].update(nfields=0)),
        ("Nat's recursor with another rule body", 51, lambda b: b["recs"][0]["rules"][1].update(rhs=b["recs"][0]["rules"][0]["rhs"])),
        ("Nat's recursor with another type", 51, lambda b: b["recs"][0].update(type=b["ctors"][1]["type"])),
        ("Nat stated not recursive", 51, lambda b: b["types"][0].update(isRec=False)),
        ("Eq's recursor without K", 1662, lambda b: b["recs"][0].update(k=False)),
        ("Eq with an index miscounted", 1662, lambda b: b["types"][0].update(numIndices=0)),
        ("PUnit's recursor with a minor premise more", 68, lambda b: b["recs"][0].update(numMinors=2)),
    ]:
        ran += 1
        try:
            rows = classes((line, edit))
            if rows[line][3] != "outside" or inside(rows) >= 22:
                failures.append(f"base families: {label} is still recognised")
        except kc.Refused as err:
            failures.append(f"base families: {label} was refused as an export, not classed outside: {err}")
    expect("a refused dependency chain is honest", None, "",
           lambda: kc.derive(export_raw, b"\x00\x00\x00\x00", transcript([*refused_id, *row_ax, *refused_user, *row_lit], counts(accepted=0, refused=2))))

    # kc.check() itself, on a scratch tree: this is the command the gate runs.
    real_root, scratch = kc.ROOT, Path(tempfile.mkdtemp(prefix="kcheck-coverage-selftest-"))
    try:
        kc.ROOT = scratch
        files = {
            "theories/kcheck_run/KCheckRunMain.lean": "import KCheckRun\n\ndef main : IO Unit := pure ()\n",
            "theories/kcheck_run/KCheckRun.lean": "/- the library root\nimport Ghost.Module -/\nimport KCheck.Declaration\nimport Init.Data\n",
            "theories/kcheck_labelled/KCheck/Declaration.lean": "-- import Ghost.Other\nimport CICL.Level\ndef note := \"\nimport Ghost.InAString\"\n",
            "theories/kcheck_labelled/KCheck/Unused.lean": "import CICL.Level\n",
            "theories/cic_l/CICL/Level.lean": "prelude\n",
        }
        for package in kc.PACKAGES:
            files[f"theories/{package}/lakefile.toml"] = f'name = "{package}"\n'
            files[f"theories/{package}/lean-toolchain"] = "leanprover/lean4:v0.0.0-selftest\n"
        files[kc.EXPORT] = gzip.compress(export_raw, mtime=0)
        files[kc.ADVICE] = advice
        files[kc.TRANSCRIPT] = transcript().encode("utf-8")
        for rel, data in files.items():
            (scratch / rel).parent.mkdir(parents=True, exist_ok=True)
            (scratch / rel).write_bytes(data if isinstance(data, bytes) else data.encode("utf-8"))
        closure = kc.required_sources()
        ran += 1
        want_closure = {f"theories/{p}/{n}" for p in kc.PACKAGES for n in ("lakefile.toml", "lean-toolchain")} | {
            "theories/kcheck_run/KCheckRunMain.lean", "theories/kcheck_run/KCheckRun.lean",
            "theories/kcheck_labelled/KCheck/Declaration.lean", "theories/cic_l/CICL/Level.lean"}
        if closure != want_closure:
            failures.append(f"import closure: got {sorted(closure ^ want_closure)} wrong (a commented or quoted import followed, or a real one missed)")
        sources = {rel: kc.sha((scratch / rel).read_bytes()) for rel in sorted(closure)}
        run = {"command": "self-test", "executable_sha256": "0" * 64, "lean_toolchain": "leanprover/lean4:v0.0.0-selftest", "lean_version": "self-test"}
        good = kc.build_record(files[kc.EXPORT], advice, files[kc.TRANSCRIPT], sources, run, "self-test")
        good_text = kc.serialize(good)

        def with_record(text, then=None) -> None:
            if text is None:
                (scratch / kc.RECORD).unlink(missing_ok=True)
            else:
                (scratch / kc.RECORD).write_text(text, encoding="utf-8")
            try:
                (then or kc.check)()
            finally:
                for rel, data in files.items():
                    (scratch / rel).write_bytes(data if isinstance(data, bytes) else data.encode("utf-8"))
                for extra in ("theories/kcheck_run/lakefile.lean", "theories/kcheck_spec/CICL/Level.lean"):
                    (scratch / extra).unlink(missing_ok=True)

        def edited(**change) -> str:
            return kc.serialize({**good, **change})

        def after(rel: str, data, then=None) -> None:
            if data is None:
                (scratch / rel).unlink()
            else:
                (scratch / rel).parent.mkdir(parents=True, exist_ok=True)
                (scratch / rel).write_bytes(data)
            (then or kc.check)()

        less = {k: v for k, v in sources.items() if not k.endswith("Level.lean")}
        arms = [
            ("an honest record", None, "", good_text, None),
            ("no record", kc.Stale, kc.STALE_ABSENT, None, None),
            ("a site decision claimed", kc.Refused, "real_declarations_decided", edited(real_declarations_decided=1), None),
            ("a site decision claimed with the inputs gone", kc.Refused, "real_declarations_decided", edited(real_declarations_decided=7), lambda: after(kc.ADVICE, None)),
            ("false standing for zero", kc.Refused, "real_declarations_decided", good_text.replace('"real_declarations_decided": 0', '"real_declarations_decided": false'), None),
            ("a key stated twice", kc.Refused, "in its spelling", good_text.replace('  "real_declarations_decided": 0,', '  "real_declarations_decided": 250,\n  "real_declarations_decided": 0,'), None),
            ("a label reworded", kc.Refused, "labels are not the ones", edited(labels={**kc.LABELS, "checker": "kcheck: proved sound"}), None),
            ("a label deleted", kc.Refused, "labels are not the ones", edited(labels={k: v for k, v in kc.LABELS.items() if k != "site"}), None),
            ("a figure raised", kc.Refused, "['figures']", edited(figures={**good["figures"], "accepted": 3}), None),
            ("an accepted name edited", kc.Refused, "['figures']", edited(figures={**good["figures"], "accepted_declarations": [{**good["figures"]["accepted_declarations"][0], "name": "[s2:di]"}, good["figures"]["accepted_declarations"][1]]}), None),
            ("an extra key", kc.Refused, "['proved']", edited(proved=True), None),
            ("no advice producer", kc.Refused, "advice.origin", edited(advice={**good["advice"], "origin": ""}), None),
            ("the run facts dropped", kc.Refused, "four facts", edited(run={}), None),
            ("a run that claims more", kc.Refused, "four facts", edited(run={**run, "site": "clean kc.check"}), None),
            ("another toolchain", kc.Refused, "pins", edited(run={**run, "lean_toolchain": "leanprover/lean4:v9"}), None),
            ("sources emptied", kc.Refused, "omits", edited(sources={}), None),
            ("sources one file short", kc.Refused, "omits 1 file(s)", edited(sources=less), None),
            ("sources padded", kc.Refused, "lists 1 file(s)", edited(sources={**sources, "theories/kcheck_labelled/KCheck/Unused.lean": kc.sha(files["theories/kcheck_labelled/KCheck/Unused.lean"].encode())}), None),
            ("sources out of the tree", kc.Refused, "not a path under theories/", edited(sources={**sources, "theories/../../etc/hosts": "0" * 64}), None),
            ("sources not a map", kc.Refused, "not a map", edited(sources=[]), None),
            ("sources a list of paths", kc.Refused, "not a map", edited(sources=["theories/kcheck_run/KCheckRun.lean"]), None),
            ("an executable with no digest", kc.Refused, "no sha256", edited(run={**run, "executable_sha256": "unknown"}), None),
            ("a module in two packages", kc.Refused, "more than one package", good_text, lambda: after("theories/kcheck_spec/CICL/Level.lean", b"prelude\n")),
            ("an import this reader cannot follow", kc.Refused, "does not follow", good_text, lambda: after("theories/kcheck_run/KCheckRun.lean", b"import \xc2\xabodd name\xc2\xbb\n", kc.required_sources)),
            ("a build root gone", kc.Refused, "has no module KCheckRunMain", good_text, lambda: after("theories/kcheck_run/KCheckRunMain.lean", None, kc.required_sources)),
            ("a record that is a list", kc.Refused, "not a coverage record", "[]\n", None),
            ("a record nested past the parser", kc.Refused, "not a coverage record", "[" * 100000, None),
            ("a source moved", kc.Stale, kc.STALE_MOVED, good_text, lambda: after("theories/cic_l/CICL/Level.lean", b"prelude\n-- edited\n")),
            ("a source deleted", kc.Stale, kc.STALE_MOVED, good_text, lambda: after("theories/kcheck_labelled/KCheck/Declaration.lean", None)),
            ("a module outside the build edited", None, "", good_text, lambda: after("theories/kcheck_labelled/KCheck/Unused.lean", b"import CICL.Level\n-- edited\n")),
            ("a build file added", kc.Refused, "omits 1 file(s)", good_text, lambda: after("theories/kcheck_run/lakefile.lean", b"-- a second lakefile\n")),
            ("the advice gone", kc.Refused, "which does not exist", good_text, lambda: after(kc.ADVICE, None)),
            ("the transcript gone", kc.Refused, "which does not exist", good_text, lambda: after(kc.TRANSCRIPT, None)),
            ("the transcript with carriage returns", kc.Refused, "carriage return", good_text, lambda: after(kc.TRANSCRIPT, files[kc.TRANSCRIPT].replace(b"\n", b"\r\n"))),
            ("the transcript not UTF-8", kc.Refused, "cannot be read", good_text, lambda: after(kc.TRANSCRIPT, b"\xff\xfe" + files[kc.TRANSCRIPT])),
            ("the export not gzip", kc.Refused, "cannot be read", good_text, lambda: after(kc.EXPORT, export_raw)),
            ("the export cut short", kc.Refused, "cannot be read", good_text, lambda: after(kc.EXPORT, files[kc.EXPORT][:-9])),
            ("the export's stream damaged", kc.Refused, "cannot be read", good_text, lambda: after(kc.EXPORT, files[kc.EXPORT][:12] + bytes(8) + files[kc.EXPORT][20:])),
            ("a source that is not UTF-8", kc.Refused, "check could not finish: UnicodeDecodeError",
             edited(sources={**sources, "theories/kcheck_run/KCheckRun.lean": kc.sha(b"import \xff\n")}), lambda: after("theories/kcheck_run/KCheckRun.lean", b"import \xff\n")),
            ("an advice byte flipped", kc.Refused, "['advice'", good_text, lambda: after(kc.ADVICE, advice[:3] + b"\x03" + advice[4:])),
        ]
        for label, kind, needle, text, then in arms:
            expect(label, kind, needle, lambda t=text, f=then: with_record(t, f))

        # --write and --replay, with a stand-in toolchain: a `lake` that leaves the files Lake leaves, and an
        # executable that prints a canned transcript. What is under test is this script, not the checker.
        home, canned = scratch / "elan", scratch / "canned.txt"
        bindir = home / "toolchains" / "leanprover--lean4---v0.0.0-selftest" / "bin"
        bindir.mkdir(parents=True)
        (bindir / "lean").write_text("#!/bin/sh\necho 'Lean (version 0.0.0-selftest)'\n")
        built = "kcheck_run/KCheckRunMain kcheck_run/KCheckRun kcheck_labelled/KCheck/Declaration cic_l/CICL/Level"

        def toolchain(modules=built, during="", status=0, printed=files[kc.TRANSCRIPT]) -> None:
            canned.write_bytes(printed)
            (bindir / "lake").write_text(
                "#!/bin/sh\nset -e\n"
                f"for m in {modules}; do p=${{m%%/*}}; r=${{m#*/}}\n"
                '  mkdir -p "../$p/.lake/build/lib/lean/$(dirname "$r")"; : > "../$p/.lake/build/lib/lean/$r.olean"\ndone\n'
                "mkdir -p .lake/build/bin\n"
                f"printf '#!/bin/sh\\n/bin/cat \"{canned}\"\\nexit {status}\\n' > .lake/build/bin/kcheck-run-interim\n"
                f"chmod +x .lake/build/bin/kcheck-run-interim\n{during}\n")
            for tool in ("lean", "lake"):
                (bindir / tool).chmod(0o755)

        def built_record(then=None, **fake):
            def go() -> None:
                toolchain(**fake)
                kc.write("the self-test's stand-in producer")
                if then:
                    then()
            with_record(None, go)

        level = scratch / "theories/cic_l/CICL/Level.lean"
        real_gate, real_home = kc.GATE, os.environ.get("ELAN_HOME")
        kc.GATE, os.environ["ELAN_HOME"] = (), str(home)
        try:
            expect("an honest mint, then its check and its replay", None, "", lambda: built_record(lambda: (kc.check(), kc.replay())))
            expect("Lake compiles a module outside the closure", kc.Refused, "another set of files", lambda: built_record(modules=built + " kcheck_labelled/KCheck/Unused"))
            expect("Lake compiles a module with no source", kc.Refused, "no source at its path", lambda: built_record(modules=built + " kcheck_run/Ghost"))
            expect("a commit lands during the build", kc.Refused, "moved during the build", lambda: built_record(during=f"printf -- '-- landed\\n' >> '{level}'"))
            expect("the executable fails", kc.Refused, "exited 2", lambda: built_record(status=2))
            expect("the executable prints a run the second reader refuses", kc.Refused, "summary line says", lambda: built_record(printed=files[kc.TRANSCRIPT].replace(b"accepted=2", b"accepted=3")))
            expect("a replay that prints other bytes", kc.Refused, "other bytes", lambda: built_record(lambda: (toolchain(printed=files[kc.TRANSCRIPT] + b"\n"), kc.replay())))
            expect("no advice to mint from", kc.Refused, "does not exist", lambda: built_record(during="", modules=built) if (scratch / kc.ADVICE).unlink() else built_record())
            os.environ["ELAN_HOME"] = str(scratch / "no-elan")
            expect("no pinned toolchain", kc.Refused, "is not installed", lambda: built_record())
        finally:
            kc.GATE = real_gate
            if real_home is None:
                os.environ.pop("ELAN_HOME", None)
            else:
                os.environ["ELAN_HOME"] = real_home
    finally:
        kc.ROOT = real_root
        shutil.rmtree(scratch, ignore_errors=True)
    for failure in failures:
        print(f"KCHECK_COVERAGE self-test FAIL {failure}", file=sys.stderr)
    if failures:
        return 1
    print(f"KCHECK_COVERAGE=self-test ok arms={ran}")
    return 0
