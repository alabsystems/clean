#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Compare two lean4export NDJSON 3.1.0 exports declaration by declaration.

WHY. Unit Q1 of docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md has Clean
write Lean's export format itself (`clean_export_write`). The question this
answers is whether Clean's bytes state what lean4export, run by pinned Lean
over the same modules and roots, states. The two files are never equal byte
for byte, by the format's design: each writer numbers the name, level and
expression tables in its own order of first use and orders declarations by
its own traversal, and Clean's kernel terms carry no binder names. So this
reads each file ON ITS OWN -- no Clean code is involved, so a fault Clean's
reader shares with Clean's writer cannot hide a difference -- resolves every
index to the term it denotes, and compares canonical forms.

WHAT IS NORMALIZED, and nothing else (each is a field no kernel rule reads):
  * the name of a `lam` or `forallE` binder (Lean's kernel compares binders
    up to their names; Clean's kernel terms keep none and Clean writes the
    anonymous name). A `letE`'s name and `nondep` flag are compared.
  * the payload of an `mdata` node (Lean's own reader of the format keeps the
    expression and drops the payload); the node itself is compared.
  * the `all` of a `def`, `thm` or `opaque` (Clean writes the constant
    alone). The `all` of an inductive type and of a recursor is compared.
  * the order of a block's recursors (lean4export writes them in its
    NameSet's order; Clean writes `<type>.rec` per type, then `.rec_<i>`).
    The order of a block's types and constructors is compared.
  * table indices, record order and the `meta` line (reported, not compared).

Each side's canonical form is also hashed: equal declarations give equal
`canonical_sha256`, which is what "byte-compared" means here.

BINDER INFORMATION is compared, and a declaration that differs in nothing
else is listed apart (`binder_info_only`), because lean4export does not
write it faithfully: its expression table is a `HashMap Expr Nat`, and
Lean's `BEq Expr` (`Expr.eqv`) ignores binder annotations, so a term that
differs from an earlier-written one only in its annotations is written as
that earlier term (lean4export `Export.lean`, `visitedExprs`). Measured
2026-11-13 on `Init.Prelude`: in every such declaration pinned Lean's
environment holds the annotation Clean wrote. The verdict is then
`equal_up_to_binder_info`, not `equal`.

USAGE
  lean_export_differential.py compare <left.ndjson> <right.ndjson>
      One JSON verdict on stdout. Exit 0: the same declared names, every
      declaration equal (`equal`). Exit 1: anything else, listed: a
      difference (`different`), or declarations that differ in binder
      information alone (`equal_up_to_binder_info`, module docs). Exit 2:
      usage or an unreadable export.
  lean_export_differential.py roots <export.ndjson> --containing <text>
      Every name the export declares whose rendering contains <text> and that
      lean4export's command line can name (every component a string, none
      holding `.`, `«` or `»`, none all digits), one per line, as Clean's
      `--target` reads it; with --quoted, as lean4export's `--` list reads it
      (every component in «»). A private name (it has a numeric component)
      cannot be named there and is left out; it is in both cones when a root
      reaches it.
  lean_export_differential.py --selftest
"""

from pathlib import Path

# -I omits the script directory; import only our adjacent support module.

import hashlib
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

DECL_KINDS = ("axiom", "def", "thm", "opaque", "quot", "inductive")
NORMALIZED = [
    "lam/forallE binder names",
    "mdata payloads (the node is compared)",
    "the all of def/thm/opaque",
    "the order of a block's recursors",
    "table indices, record order, the meta line",
]


class Malformed(Exception):
    """The export is not one this reads."""


def digest(obj):
    text = json.dumps(obj, separators=(",", ":"), ensure_ascii=False, sort_keys=True)
    return hashlib.blake2b(text.encode("utf-8"), digest_size=20).hexdigest()


class Export:
    """One export, every index resolved to a canonical value."""

    def __init__(self, path, lines, erase_binder_info=False):
        self.path = path
        self.erase_binder_info = erase_binder_info
        self.meta = None
        self.names = {0: ()}
        self.levels = {0: "0"}
        self.exprs = {}
        # declared name -> key of the declaration that declares it
        self.declared = {}
        # key -> canonical declaration
        self.decls = {}
        self.records = 0
        self.sha256 = hashlib.sha256()
        # Kept to read the same bytes again with binder information erased.
        self.raw = list(lines)
        for number, raw in enumerate(self.raw, start=1):
            self.sha256.update(raw)
            line = raw.rstrip(b"\n")
            if not line:
                continue
            try:
                obj = json.loads(line)
            except ValueError as exc:
                raise Malformed(f"{path}:{number}: not JSON: {exc}") from exc
            if not isinstance(obj, dict):
                raise Malformed(f"{path}:{number}: not an object")
            if number == 1:
                if "meta" not in obj:
                    raise Malformed(f"{path}:1: the first line is not the meta record")
                self.meta = obj["meta"]
                continue
            try:
                self.record(obj)
            except (KeyError, TypeError, ValueError) as exc:
                raise Malformed(f"{path}:{number}: {exc!r}") from exc
        if self.meta is None:
            raise Malformed(f"{path}: empty")

    # -- tables ---------------------------------------------------------
    def name(self, index):
        if index not in self.names:
            raise Malformed(f"name index {index} used before its record")
        return self.names[index]

    def level(self, index):
        if index not in self.levels:
            raise Malformed(f"level index {index} used before its record")
        return self.levels[index]

    def expr(self, index):
        if index not in self.exprs:
            raise Malformed(f"expression index {index} used before its record")
        return self.exprs[index]

    def record(self, obj):
        if "in" in obj:
            index = obj["in"]
            if "str" in obj:
                part = obj["str"]
                self.names[index] = self.name(part["pre"]) + (("s", part["str"]),)
            else:
                part = obj["num"]
                self.names[index] = self.name(part["pre"]) + (("n", int(part["i"])),)
            return
        if "il" in obj:
            index = obj["il"]
            if "succ" in obj:
                value = ["succ", self.level(obj["succ"])]
            elif "max" in obj:
                a, b = obj["max"]
                value = ["max", self.level(a), self.level(b)]
            elif "imax" in obj:
                a, b = obj["imax"]
                value = ["imax", self.level(a), self.level(b)]
            else:
                value = ["param", list(self.name(obj["param"]))]
            self.levels[index] = digest(value) if isinstance(value, list) else value
            return
        if "ie" in obj:
            self.exprs[obj["ie"]] = self.expression(obj)
            return
        kinds = [k for k in obj if k in DECL_KINDS]
        if len(kinds) != 1 or len(obj) != 1:
            raise Malformed(f"a record with keys {sorted(obj)}")
        self.records += 1
        self.declaration(kinds[0], obj[kinds[0]])

    def expression(self, obj):
        kind = [k for k in obj if k != "ie"]
        if len(kind) != 1:
            raise Malformed(f"an expression record with keys {sorted(obj)}")
        kind = kind[0]
        data = obj[kind]
        if kind == "bvar":
            value = ["bvar", int(data)]
        elif kind == "sort":
            value = ["sort", self.level(data)]
        elif kind == "const":
            value = ["const", list(self.name(data["name"])), [self.level(u) for u in data["us"]]]
        elif kind == "app":
            value = ["app", self.expr(data["fn"]), self.expr(data["arg"])]
        elif kind in ("lam", "forallE"):
            # The binder's name is not compared, and its information only in
            # the strict view (module docs).
            info = None if self.erase_binder_info else data["binderInfo"]
            value = [kind, info, self.expr(data["type"]), self.expr(data["body"])]
        elif kind == "letE":
            value = [
                "letE",
                list(self.name(data["name"])),
                self.expr(data["type"]),
                self.expr(data["value"]),
                self.expr(data["body"]),
                bool(data["nondep"]),
            ]
        elif kind == "proj":
            value = ["proj", list(self.name(data["typeName"])), int(data["idx"]), self.expr(data["struct"])]
        elif kind == "natVal":
            value = ["natVal", str(int(data))]
        elif kind == "strVal":
            value = ["strVal", data]
        elif kind == "mdata":
            # The payload is not compared (module docs); the node is.
            value = ["mdata", self.expr(data["expr"])]
        else:
            raise Malformed(f"an expression of kind {kind!r}")
        return digest(value)

    # -- declarations ---------------------------------------------------
    def header(self, data):
        return {
            "name": list(self.name(data["name"])),
            "levelParams": [list(self.name(n)) for n in data["levelParams"]],
            "type": self.expr(data["type"]),
        }

    def declare(self, key, names, canonical):
        if key in self.decls:
            raise Malformed(f"{render(key)} is declared twice")
        self.decls[key] = canonical
        for name in names:
            if name in self.declared:
                raise Malformed(f"{render(name)} is declared twice")
            self.declared[name] = key

    def declaration(self, kind, data):
        if kind == "inductive":
            types = []
            for t in data["types"]:
                c = self.header(t)
                c.update(
                    numParams=t["numParams"],
                    numIndices=t["numIndices"],
                    all=[list(self.name(n)) for n in t["all"]],
                    ctors=[list(self.name(n)) for n in t["ctors"]],
                    numNested=t["numNested"],
                    isRec=t["isRec"],
                    isReflexive=t["isReflexive"],
                    isUnsafe=t["isUnsafe"],
                )
                types.append(c)
            ctors = []
            for k in data["ctors"]:
                c = self.header(k)
                c.update(
                    induct=list(self.name(k["induct"])),
                    cidx=k["cidx"],
                    numParams=k["numParams"],
                    numFields=k["numFields"],
                    isUnsafe=k["isUnsafe"],
                )
                ctors.append(c)
            recs = []
            for r in data["recs"]:
                c = self.header(r)
                c.update(
                    all=[list(self.name(n)) for n in r["all"]],
                    numParams=r["numParams"],
                    numIndices=r["numIndices"],
                    numMotives=r["numMotives"],
                    numMinors=r["numMinors"],
                    rules=[
                        {"ctor": list(self.name(x["ctor"])), "nfields": x["nfields"], "rhs": self.expr(x["rhs"])}
                        for x in r["rules"]
                    ],
                    k=r["k"],
                    isUnsafe=r["isUnsafe"],
                )
                recs.append(c)
            # A block's recursor order is not compared (module docs).
            recs.sort(key=lambda c: json.dumps(c["name"], ensure_ascii=False))
            if not types:
                raise Malformed("an inductive record with no types")
            names = [tuple(map(tuple, c["name"])) for c in types + ctors + recs]
            canonical = {"kind": "inductive", "types": types, "ctors": ctors, "recs": recs}
            self.declare(names[0], names, canonical)
            return
        c = self.header(data)
        if kind == "axiom":
            c.update(isUnsafe=data["isUnsafe"])
        elif kind == "def":
            # `all` is not compared (module docs).
            c.update(value=self.expr(data["value"]), hints=data["hints"], safety=data["safety"])
        elif kind == "thm":
            c.update(value=self.expr(data["value"]))
        elif kind == "opaque":
            c.update(value=self.expr(data["value"]), isUnsafe=data.get("isUnsafe", False))
        elif kind == "quot":
            c.update(kind=data["kind"])
        c["kind"] = kind
        name = tuple(map(tuple, c["name"]))
        self.declare(name, [name], c)

    def canonical_sha256(self):
        h = hashlib.sha256()
        for key in sorted(self.decls, key=render):
            h.update(render(key).encode("utf-8"))
            h.update(b"\t")
            h.update(json.dumps(self.decls[key], sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))
            h.update(b"\n")
        return h.hexdigest()


def render(name):
    """A name as Clean's `to_unambiguous_string` would show it, near enough to read."""
    parts = []
    for tag, value in name:
        if tag == "n":
            parts.append(str(value))
        elif value and "." not in value and not value.isdigit() and "«" not in value and "»" not in value:
            parts.append(value)
        else:
            parts.append("«" + value + "»")
    return ".".join(parts) if parts else "[anonymous]"


def nameable(name):
    """lean4export's `--` list and Clean's `--target` both name it, alike."""
    return bool(name) and all(
        tag == "s" and value and "." not in value and "«" not in value and "»" not in value and not value.isdigit()
        and not any(ch.isspace() for ch in value)
        for tag, value in name
    )


def differing_fields(left, right):
    """Which top-level fields (or block members) of two canonical declarations differ."""
    out = []
    if left.get("kind") != right.get("kind"):
        return [f"kind {left.get('kind')} vs {right.get('kind')}"]
    if left["kind"] == "inductive":
        for part in ("types", "ctors", "recs"):
            lm, rm = left[part], right[part]
            if [m["name"] for m in lm] != [m["name"] for m in rm]:
                out.append(f"{part}: members {[render(tuple(map(tuple, m['name']))) for m in lm]} vs "
                           f"{[render(tuple(map(tuple, m['name']))) for m in rm]}")
                continue
            for a, b in zip(lm, rm):
                for field in sorted(set(a) | set(b)):
                    if a.get(field) != b.get(field):
                        out.append(f"{part} {render(tuple(map(tuple, a['name'])))}: {field}")
        return out
    for field in sorted(set(left) | set(right)):
        if left.get(field) != right.get(field):
            out.append(field)
    return out


def load(path, erase_binder_info=False):
    try:
        with open(path, "rb") as handle:
            return Export(path, handle, erase_binder_info)
    except OSError as exc:
        raise Malformed(f"cannot read {path}: {exc}") from exc


def compare(left, right, limit=40, left_erased=None, right_erased=None):
    """`left_erased`/`right_erased`: the same files read with binder information
    erased (computed when not given)."""
    if left_erased is None:
        left_erased = Export(left.path, left.raw, True)
    if right_erased is None:
        right_erased = Export(right.path, right.raw, True)
    lnames, rnames = set(left.declared), set(right.declared)
    only_left = sorted(lnames - rnames, key=render)
    only_right = sorted(rnames - lnames, key=render)
    differing = []
    binder_info_only = []
    shape = []
    for key in sorted(set(left.decls) & set(right.decls), key=render):
        a, b = left.decls[key], right.decls[key]
        if a == b:
            continue
        ea, eb = left_erased.decls[key], right_erased.decls[key]
        if ea == eb:
            binder_info_only.append(render(key))
        else:
            differing.append({"declaration": render(key), "fields": differing_fields(ea, eb)})
    # A name both declare, under declarations keyed differently (a block's
    # head differs): the blocks were grouped otherwise.
    for name in sorted(lnames & rnames, key=render):
        if left.declared[name] != right.declared[name]:
            shape.append(f"{render(name)}: in the block of {render(left.declared[name])} vs "
                         f"{render(right.declared[name])}")
    if only_left or only_right or differing or shape:
        verdict = "different"
    elif binder_info_only:
        verdict = "equal_up_to_binder_info"
    else:
        verdict = "equal"
    side = lambda e: {
        "path": e.path,
        "sha256": e.sha256.hexdigest(),
        "exporter": e.meta.get("exporter"),
        "lean": e.meta.get("lean"),
        "format": e.meta.get("format"),
        "records": e.records,
        "declarations": len(e.declared),
        "canonical_sha256": e.canonical_sha256(),
    }
    return {
        "verdict": verdict,
        "left": side(left),
        "right": side(right),
        "same_lean": left.meta.get("lean") == right.meta.get("lean"),
        "normalized": NORMALIZED,
        "only_left": [render(n) for n in only_left[:limit]],
        "only_left_count": len(only_left),
        "only_right": [render(n) for n in only_right[:limit]],
        "only_right_count": len(only_right),
        "differing": differing[:limit],
        "differing_count": len(differing),
        "binder_info_only": binder_info_only[:limit],
        "binder_info_only_count": len(binder_info_only),
        "grouped_otherwise": shape[:limit],
        "grouped_otherwise_count": len(shape),
    }


# -- self-test ------------------------------------------------------------

def main(argv):
    if argv[:1] == ["--selftest"]:
        from lean_export_differential_selftest import selftest
        return selftest(sys.modules[__name__])
    if len(argv) == 3 and argv[0] == "compare":
        try:
            left, right = load(argv[1]), load(argv[2])
        except Malformed as exc:
            print(f"lean_export_differential: {exc}", file=sys.stderr)
            return 2
        verdict = compare(left, right)
        print(json.dumps(verdict, ensure_ascii=False))
        return 0 if verdict["verdict"] == "equal" else 1
    if len(argv) in (4, 5) and argv[0] == "roots" and argv[2] == "--containing" and argv[4:] in ([], ["--quoted"]):
        try:
            export = load(argv[1])
        except Malformed as exc:
            print(f"lean_export_differential: {exc}", file=sys.stderr)
            return 2
        quoted = argv[4:] == ["--quoted"]
        for name in sorted(export.declared, key=render):
            if nameable(name) and argv[3] in ".".join(v for _, v in name):
                print(".".join(("«" + v + "»") if quoted else v for _, v in name))
        return 0
    print(__doc__.split("USAGE", 1)[1].split('"""')[0], file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
