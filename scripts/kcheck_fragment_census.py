#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Which widening of kcheck's fragment brings the most real declarations inside it.

Self-proof plan, section 0 rule 8: after the first flip the checker is widened
by what real declarations need, not by the order of Lean's rule inventory. This
reads a lean4export NDJSON export and classifies every declaration record by
SYNTAX ALONE, the way step K1's loader does: a declaration is inside when it is
a safe definition, theorem or opaque, holds no construct the fragment lacks,
and every constant it cites is a recognised family's or an earlier inside
declaration's. A constant is the NAME it is, component by component: `a.b` as
one string component and `a` then `b` are two constants, as they are to Lean. It then asks the same question with one or more features added.

What the figures are NOT: a prediction of what kcheck accepts. A declaration
inside by syntax can still be refused (advice that does not replay, a reduction
the checker lacks such as structure eta or literal arithmetic). The figures are
an upper bound on acceptances and a lower bound on what a feature unlocks. The
recognised families are taken by NAME here (Eq, PUnit, Nat); the checker
compares the blocks themselves, and a caller that can do the same passes
`classify` its own `recognise`.

Usage:
  scripts/kcheck_fragment_census.py <export.ndjson[.gz]> [--json]
"""

from __future__ import annotations

import gzip
import hashlib
import itertools
import json
import sys
from pathlib import Path

BASE_FAMILIES = ("Eq", "PUnit", "Nat")
FEATURES = ("inductives", "nat-literals", "string-literals", "projections", "quotient", "axioms")


def read(path: Path) -> tuple[bytes, list[dict]]:
    raw = gzip.decompress(path.read_bytes()) if path.suffix == ".gz" else path.read_bytes()
    return raw, [json.loads(line) for line in raw.decode("utf-8").split("\n") if line]


class Export:
    def __init__(self, records: list[dict]) -> None:
        self.names: dict[int, tuple] = {0: ()}
        self.exprs: dict[int, dict] = {}
        self.decls: list[tuple[int, str, dict]] = []
        for line, record in enumerate(records, 1):
            if "in" in record:
                part = record.get("str") or record.get("num")
                leaf = ("s", part["str"]) if "str" in record else ("n", part["i"])
                self.names[record["in"]] = self.names[part["pre"]] + (leaf,)
            elif "ie" in record:
                self.exprs[record["ie"]] = record
            elif "il" not in record and "meta" not in record:
                (kind, body), = record.items()
                self.decls.append((line, kind, body))
        self._facts: dict[int, tuple[frozenset[tuple], frozenset[str]]] = {}

    def facts(self, root: int) -> tuple[frozenset[tuple], frozenset[str]]:
        """(constants cited, constructs used) below expression `root`, iteratively."""
        stack = [root]
        while stack:
            node = stack[-1]
            if node in self._facts:
                stack.pop()
                continue
            record = self.exprs[node]
            children: list[int] = []
            consts: set[tuple] = set()
            uses: set[str] = set()
            if "app" in record:
                children = [record["app"]["fn"], record["app"]["arg"]]
            elif "lam" in record or "forallE" in record:
                binder = record.get("lam") or record["forallE"]
                children = [binder["type"], binder["body"]]
            elif "letE" in record:
                children = [record["letE"][k] for k in ("type", "value", "body")]
            elif "mdata" in record:
                children = [record["mdata"]["expr"]]
            elif "proj" in record:
                children = [record["proj"]["struct"]]
                consts.add(self.names[record["proj"]["typeName"]])
                uses.add("projections")
            elif "const" in record:
                consts.add(self.names[record["const"]["name"]])
            elif "natVal" in record:
                uses.add("nat-literals")
            elif "strVal" in record:
                uses.add("string-literals")
            elif "fvar" in record or "mvar" in record:
                uses.add("free-variable")
            pending = [c for c in children if c not in self._facts]
            if pending:
                stack.extend(pending)
                continue
            for child in children:
                consts |= self._facts[child][0]
                uses |= self._facts[child][1]
            self._facts[node] = (frozenset(consts), frozenset(uses))
            stack.pop()
        return self._facts[root]


def dotted(name: tuple) -> str:
    """A name for a person to read. Not injective: never a key."""
    return ".".join(str(leaf) for _, leaf in name)


def by_name(export: Export):
    """The default `recognise`: a one-type block named Eq, PUnit or Nat makes every name it declares citable."""
    def recognise(body: dict) -> list[tuple] | None:
        types = [export.names[t["name"]] for t in body["types"]]
        if len(types) != 1 or types[0] not in [(("s", family),) for family in BASE_FAMILIES]:
            return None
        return types + [export.names[row["name"]] for group in ("ctors", "recs") for row in body[group]]
    return recognise


def classify(export: Export, features: frozenset[str], recognise=None) -> list[tuple[int, str, tuple, str, str]]:
    """One row per declaration record: (line, kind, name, class, first reason).

    `recognise(body)` gives the names an `inductive` record makes citable, or None when it is no base family.
    """
    recognise = recognise or by_name(export)
    available: set[tuple] = set()
    rows = []
    for line, kind, body in export.decls:
        if kind == "inductive":
            types = [export.names[t["name"]] for t in body["types"]]
            owned = recognise(body)
            if owned is None and "inductives" in features:
                owned = types + [export.names[row["name"]] for group in ("ctors", "recs") for row in body[group]]
            if owned is not None:
                available.update(owned)
                rows.append((line, kind, types[0], "recognised", ""))
            else:
                rows.append((line, kind, types[0], "outside", "inductiveBlock"))
            continue
        name = export.names[body["name"]]
        if kind == "quot":
            ok = "quotient" in features
            if ok:
                available.add(name)
            rows.append((line, kind, name, "inside" if ok else "outside", "" if ok else "quotient"))
            continue
        consts: set[tuple] = set()
        uses: set[str] = set()
        for field in ("type", "value"):
            if field in body:
                found = export.facts(body[field])
                consts |= found[0]
                uses |= found[1]
        reason = ""
        if kind == "axiom" and "axioms" not in features:
            reason = "axiomDecl"
        elif body.get("isUnsafe") or body.get("safety") in ("unsafe", "partial"):
            reason = "unsafe-or-partial"
        else:
            lacking = sorted(u for u in uses if u not in features)
            missing = sorted(c for c in consts if c not in available)
            if lacking:
                reason = lacking[0]
            elif missing:
                reason = f"cites:{dotted(missing[0])}"
        if reason:
            rows.append((line, kind, name, "outside", reason))
        else:
            available.add(name)
            rows.append((line, kind, name, "inside", ""))
    return rows


def inside(rows) -> int:
    return sum(1 for row in rows if row[3] == "inside" and row[1] in ("def", "thm", "opaque"))


def census(path: Path) -> dict:
    raw, records = read(path)
    export = Export(records)
    today = classify(export, frozenset())
    ordinary = sum(1 for row in today if row[1] in ("def", "thm", "opaque"))
    reasons: dict[str, int] = {}
    for row in today:
        if row[3] == "outside":
            key = "cites an unavailable constant" if row[4].startswith("cites:") else row[4]
            reasons[key] = reasons.get(key, 0) + 1
    single = {f: inside(classify(export, frozenset([f]))) for f in FEATURES}
    chosen: list[str] = []
    path_rows = []
    while len(chosen) < len(FEATURES):
        best = max((f for f in FEATURES if f not in chosen), key=lambda f: (inside(classify(export, frozenset(chosen + [f]))), -FEATURES.index(f)))
        chosen.append(best)
        path_rows.append({"add": best, "inside": inside(classify(export, frozenset(chosen)))})
    best_pair = max(itertools.combinations(FEATURES, 2), key=lambda p: inside(classify(export, frozenset(p))))
    return {
        "schema": "clean.kcheck_fragment_census.v1",
        "export": {"path": str(path), "sha256": hashlib.sha256(raw).hexdigest(), "declaration_records": len(today)},
        "ordinary_declarations": ordinary,
        "inside_today": {"count": inside(today), "names": [dotted(r[2]) for r in today if r[3] == "inside" and r[1] in ("def", "thm", "opaque")]},
        "outside_today_first_reason": dict(sorted(reasons.items(), key=lambda kv: -kv[1])),
        "inside_with_one_feature_added": single,
        "best_pair": {"features": list(best_pair), "inside": inside(classify(export, frozenset(best_pair)))},
        "greedy_order": path_rows,
        "limits": "Syntactic class only: an upper bound on acceptances. Families recognised by name. Reductions the checker lacks (structure eta, literal arithmetic) and advice that does not replay are not modelled.",
    }


def main() -> int:
    args = [a for a in sys.argv[1:] if a != "--json"]
    if len(args) != 1:
        print(__doc__.strip().split("\n\n")[-1], file=sys.stderr)
        return 2
    result = census(Path(args[0]))
    if "--json" in sys.argv:
        print(json.dumps(result, indent=2))
        return 0
    total = result["ordinary_declarations"]
    print(f"export {result['export']['sha256'][:12]}: {result['export']['declaration_records']} declaration records, {total} ordinary")
    print(f"inside the fragment today (by syntax): {result['inside_today']['count']} of {total}")
    for reason, count in result["outside_today_first_reason"].items():
        print(f"  outside, first reason {reason}: {count}")
    print("inside if ONE feature were added:")
    for feature, count in sorted(result["inside_with_one_feature_added"].items(), key=lambda kv: -kv[1]):
        print(f"  {feature:16} {count}")
    print(f"best pair: {' + '.join(result['best_pair']['features'])} -> {result['best_pair']['inside']}")
    print("greedy order:")
    for step in result["greedy_order"]:
        print(f"  + {step['add']:16} -> {step['inside']} of {total}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
