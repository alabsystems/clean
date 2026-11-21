#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Planted controls for lean_export_differential.py; run through --selftest."""

import json
import sys


def selftest(api):
    """Use the production parser and comparison without a second module load."""
    globals().update({k: getattr(api, k) for k in ("Export", "Malformed", "compare", "DECL_KINDS")})
    return _selftest()


SELFTEST_EXPORT = [
    {"meta": {"exporter": {"name": "selftest", "version": "0"}, "format": {"version": "3.1.0"},
              "lean": {"githash": "0", "version": "0"}}},
    {"in": 1, "str": {"pre": 0, "str": "T"}},
    {"il": 1, "succ": 0},
    {"ie": 0, "sort": 1},
    {"in": 2, "str": {"pre": 1, "str": "mk"}},
    {"in": 3, "str": {"pre": 1, "str": "rec"}},
    {"in": 4, "str": {"pre": 1, "str": "rec_1"}},
    {"in": 5, "str": {"pre": 0, "str": "x"}},
    {"const": {"name": 1, "us": []}, "ie": 1},
    {"forallE": {"binderInfo": "default", "body": 1, "name": 5, "type": 1}, "ie": 2},
    {"bvar": 0, "ie": 3},
    {"lam": {"binderInfo": "default", "body": 3, "name": 5, "type": 1}, "ie": 4},
    {"mdata": {"data": {"k": "1"}, "expr": 4}, "ie": 5},
    {"natVal": "18446744073709551616", "ie": 6},
    {"in": 6, "str": {"pre": 0, "str": "f"}},
    {"in": 7, "str": {"pre": 0, "str": "g"}},
    {"in": 8, "num": {"pre": 1, "i": 11}},
    {"in": 9, "str": {"pre": 0, "str": "lemma"}},
    {"in": 10, "str": {"pre": 0, "str": "sealed"}},
    {"inductive": {
        "types": [{"name": 1, "levelParams": [], "type": 0, "numParams": 0, "numIndices": 0, "all": [1],
                   "ctors": [2], "numNested": 0, "isRec": False, "isReflexive": False, "isUnsafe": False}],
        "ctors": [{"name": 2, "levelParams": [], "type": 1, "induct": 1, "cidx": 0, "numParams": 0,
                   "numFields": 0, "isUnsafe": False}],
        "recs": [
            {"name": 3, "levelParams": [], "type": 2, "all": [1], "numParams": 0, "numIndices": 0,
             "numMotives": 1, "numMinors": 1, "rules": [{"ctor": 2, "nfields": 0, "rhs": 4}], "k": False,
             "isUnsafe": False},
            {"name": 4, "levelParams": [], "type": 2, "all": [1], "numParams": 0, "numIndices": 0,
             "numMotives": 1, "numMinors": 1, "rules": [{"ctor": 2, "nfields": 0, "rhs": 4}], "k": False,
             "isUnsafe": False}]}},
    {"def": {"name": 6, "levelParams": [], "type": 2, "value": 5, "hints": {"regular": 1}, "safety": "safe",
             "all": [6, 8]}},
    {"def": {"name": 7, "levelParams": [], "type": 1, "value": 6, "hints": "abbrev", "safety": "safe",
             "all": [7]}},
    {"thm": {"name": 9, "levelParams": [], "type": 1, "value": 1, "all": [8, 9]}},
    {"opaque": {"name": 10, "levelParams": [], "type": 1, "value": 1, "all": [], "isUnsafe": False}},
]


def _lines(records):
    return [json.dumps(r, separators=(",", ":")).encode("utf-8") + b"\n" for r in records]


def _mutate(edit):
    records = json.loads(json.dumps(SELFTEST_EXPORT))
    edit(records)
    return Export("<mutated>", _lines(records))


def _find(records, pred):
    for r in records:
        if pred(r):
            return r
    raise AssertionError("no such record")


def _selftest():
    base = Export("<base>", _lines(SELFTEST_EXPORT))
    same = []
    differ = []

    # Normalized: these must compare equal.
    def binder_names(rs):
        rs.insert(1, {"in": 11, "str": {"pre": 0, "str": "y"}})
        for r in rs:
            for k in ("lam", "forallE"):
                if k in r:
                    r[k]["name"] = 11
    same.append(("binder names", binder_names))
    same.append(("mdata payload", lambda rs: _find(rs, lambda r: "mdata" in r)["mdata"].update(data={})))
    same.append(("recursor order", lambda rs: _find(rs, lambda r: "inductive" in r)["inductive"]["recs"].reverse()))

    def renumber(rs):
        # Move every declaration to the end in reverse order: record order is not compared.
        decls = [r for r in rs if any(k in r for k in DECL_KINDS)]
        rest = [r for r in rs if not any(k in r for k in DECL_KINDS)]
        rs[:] = rest + decls[::-1]
    same.append(("record order", renumber))

    # Compared: each of these must be a difference.
    differ.append(("hint", lambda rs: _find(rs, lambda r: "def" in r)["def"].update(hints={"regular": 2})))
    differ.append(("nat literal", lambda rs: _find(rs, lambda r: "natVal" in r).update(natVal="18446744073709551617")))
    differ.append(("rule nfields", lambda rs: _find(rs, lambda r: "inductive" in r)["inductive"]["recs"][0]["rules"][0].update(nfields=1)))
    differ.append(("type all", lambda rs: _find(rs, lambda r: "inductive" in r)["inductive"]["types"][0].update(numNested=1)))
    differ.append(("mdata node dropped", lambda rs: _find(rs, lambda r: "def" in r)["def"].update(value=4)))
    differ.append(("declaration dropped", lambda rs: rs.remove(_find(rs, lambda r: "def" in r and r["def"]["name"] == 7))))
    differ.append(("level param", lambda rs: _find(rs, lambda r: "def" in r)["def"].update(levelParams=[5])))

    failures = []
    for label, edit in same:
        verdict = compare(base, _mutate(edit))
        if verdict["verdict"] != "equal":
            failures.append(f"{label}: expected equal, got {verdict}")
    for label, edit in differ:
        verdict = compare(base, _mutate(edit))
        if verdict["verdict"] != "different":
            failures.append(f"{label}: expected a difference, got equal")
    # Compare the ordered names on all three ordinary declaration kinds.
    # T.11 is valid metadata even though its declaration is outside this stream.
    for kind, decl, changed in (("def", "f", [8, 6]), ("thm", "lemma", [9]),
                                 ("opaque", "sealed", [10])):
        verdict = compare(base, _mutate(lambda rs: _find(rs, lambda r: kind in r)[kind].update(all=changed)))
        if (verdict["verdict"] != "different"
                or verdict["differing"] != [{"declaration": decl, "fields": ["all"]}]
                or verdict["only_left_count"] or verdict["only_right_count"]):
            failures.append(f"{kind} all: expected an ordered metadata difference for {decl}, got {verdict}")
    if base.name(8) in base.declared:
        failures.append("ordinary all introduced an undeclared sibling into the cone")
    for invalid in ([12], {}, [True]):
        try:
            _mutate(lambda rs: _find(rs, lambda r: "opaque" in r)["opaque"].update(all=invalid))
            failures.append(f"accepted invalid opaque.all: {invalid}")
        except Malformed:
            pass
    # Binder information alone: listed apart, not among the differences.
    verdict = compare(base, _mutate(lambda rs: _find(rs, lambda r: "lam" in r)["lam"].update(binderInfo="implicit")))
    if (verdict["verdict"] != "equal_up_to_binder_info" or verdict["differing_count"] != 0
            or verdict["binder_info_only"] != ["T", "f"]):
        # The `lam` is `f`'s value and the rule of `T.rec`: both blocks.
        failures.append(f"binder info alone: expected binder_info_only ['T', 'f'], got {verdict}")
    # Binder information and a hint: the hint is a difference, the binder
    # information is not listed as one.
    def both(rs):
        _find(rs, lambda r: "lam" in r)["lam"].update(binderInfo="implicit")
        _find(rs, lambda r: "def" in r)["def"].update(hints={"regular": 2})
    verdict = compare(base, _mutate(both))
    if verdict["verdict"] != "different" or verdict["differing"] != [{"declaration": "f", "fields": ["hints"]}]:
        failures.append(f"binder info and a hint: expected f differing in hints alone, got {verdict}")
    # A forward reference is refused, not guessed.
    try:
        Export("<forward>", _lines([SELFTEST_EXPORT[0], {"ie": 0, "sort": 9}]))
        failures.append("a level used before its record was read")
    except Malformed:
        pass
    if failures:
        print("lean_export_differential: SELFTEST FAILED", file=sys.stderr)
        for f in failures:
            print("  " + f, file=sys.stderr)
        return 1
    print(f"lean_export_differential: selftest ok ({len(same)} normalized edits equal, "
          f"{len(differ)} planted differences found, 3 ordinary all differences and 3 malformed all fields checked, "
          f"2 binder-information cases listed apart, "
          f"1 forward reference refused)")
    return 0
