#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""The export half of the second reader of scripts/kcheck_coverage.py.

`Raw` reads a lean4export NDJSON export as strictly as the checker's own reader
does (theories/kcheck_run/README.md, "Inputs"): what that reader refuses is
refused here, so the two never classify different files. It renders names,
levels and expressions in the grammar of transcript version 1, and it says
which `inductive` records are the three base families by comparing the WHOLE
record, recursor and rules included, with a text pinned below. It shares no
code with the Lean loader, which is the point.

Usage (prints the text and digest a base family's record gives, for re-pinning BASE):
  scripts/kcheck_coverage_export.py <export.ndjson[.gz]>
"""

from __future__ import annotations

import gzip
import hashlib
import json
import sys
from pathlib import Path

NODE_CAP = 1048576
LINE_ENDS = ("\u0085", " ", " ")
# Field kinds: n a name index, N a list of them, P level parameters, e an expression index, i a count,
# b a boolean, R recursor rules, and a tuple the strings allowed. `hints` and `mdata.data` are read apart.
ROWS = {
    "def": {"name": "n", "levelParams": "P", "type": "e", "value": "e", "safety": ("safe", "unsafe", "partial"), "hints": "H", "all": "N"},
    "thm": {"name": "n", "levelParams": "P", "type": "e", "value": "e", "all": "N"},
    "opaque": {"name": "n", "levelParams": "P", "type": "e", "value": "e", "isUnsafe": "b", "all": "N"},
    "axiom": {"name": "n", "levelParams": "P", "type": "e", "isUnsafe": "b"},
    "quot": {"name": "n", "levelParams": "P", "type": "e", "kind": ("type", "ctor", "lift", "ind")},
    "types": {"name": "n", "levelParams": "P", "type": "e", "numParams": "i", "numIndices": "i", "all": "N", "ctors": "N",
              "numNested": "i", "isRec": "b", "isUnsafe": "b", "isReflexive": "b"},
    "ctors": {"name": "n", "levelParams": "P", "type": "e", "induct": "n", "cidx": "i", "numParams": "i", "numFields": "i", "isUnsafe": "b"},
    "recs": {"name": "n", "levelParams": "P", "type": "e", "all": "N", "numParams": "i", "numIndices": "i", "numMotives": "i",
             "numMinors": "i", "rules": "R", "k": "b", "isUnsafe": "b"},
    "rules": {"ctor": "n", "nfields": "i", "rhs": "e"},
}
BINDER = {"binderInfo", "name", "type", "body"}
EXPR_KEYS = {"const": {"name", "us"}, "app": {"fn", "arg"}, "lam": BINDER, "forallE": BINDER,
             "letE": {"name", "type", "value", "body", "nondep"}, "proj": {"typeName", "idx", "struct"}, "mdata": {"data", "expr"}}
# The three families the checker's base environment carries: the digest of `Raw.block_text` of each one's
# record in the pinned Init.Prelude export. A record is a base family only when it gives exactly that text;
# its name alone recognises nothing. The checker compares the same fields with its own environment
# (theories/kcheck_run/KCheckRun/Recognise.lean), and a run in which the two disagree on a record is refused.
BASE = {
    "[s3:Nat]": "58bb6e44d81ee406a97d6c4417b0f04dcee361233f25b68161abe63a24278ec5",
    "[s5:PUnit]": "fe625fa32f92a43db042e63be9b1720d4a6be142dd5c0219e2d86a01cfeee6ee",
    "[s2:Eq]": "864c55fd97bf5b5fb82de4a12141951dae771d127722a033963b968d1931c68d",
}


class Refused(Exception):
    """The record, or one of the files it names, is not what a re-derivation gives."""


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def once(pairs: list) -> dict:
    out = dict(pairs)
    if len(out) != len(pairs):
        raise Refused("a key is written twice in one object")
    return out


def no_number(text: str):
    raise Refused(f"the number {text}; the checker's reader takes whole numbers with no sign, fraction or exponent")


def whole(text: str) -> int:
    return no_number(text) if text.startswith("-") else int(text)


def listed(value) -> list:
    if not isinstance(value, list):
        raise Refused(f"{value!r} where an array is expected")
    return value


def nat(value) -> int:
    if type(value) is not int or value < 0:
        raise Refused(f"{value!r} where an index or a count is expected")
    return value


class Raw:
    """An export's records, its tables, and the echoes of what they state."""

    def __init__(self, export_raw: bytes) -> None:
        try:
            text = export_raw.decode("utf-8")
        except UnicodeDecodeError as err:
            raise Refused(f"the export is not UTF-8 ({err})") from err
        if not text.endswith("\n"):
            raise Refused("the export's last line is not ended by a line feed")
        self.records: list[dict] = []
        self.name: dict[int, tuple] = {0: ()}
        self.known: set[tuple] = {()}
        self.level: dict[int, dict] = {}
        self.level_size: dict[int, int] = {0: 1}
        self.expr: dict[int, dict] = {}
        self.expr_size: dict[int, int] = {}
        self.decl: dict[int, tuple[str, dict]] = {}
        self.declared: set[tuple] = set()
        for number, line in enumerate(text[:-1].split("\n"), 1):
            try:
                if "\\" in line:
                    raise Refused("an escape; the checker's reader takes none")
                record = json.loads(line, object_pairs_hook=once, parse_int=whole, parse_float=no_number, parse_constant=no_number)
                if not isinstance(record, dict) or json.dumps(record, separators=(",", ":"), ensure_ascii=False) != line:
                    raise Refused("not one JSON object in the plain spelling lean4export writes")
                self.records.append(record)
                self.add(number, record)
            except Refused as err:
                raise Refused(f"export line {number}: {err}") from err
            except (ValueError, KeyError, TypeError, AttributeError, IndexError, RecursionError) as err:
                raise Refused(f"export line {number}: malformed ({type(err).__name__}: {err})") from err

    def name_of(self, index) -> tuple:
        if nat(index) not in self.name:
            raise Refused(f"name {index} is cited before any line defines it")
        return self.name[index]

    def size(self, table: dict, index) -> int:
        if nat(index) not in table:
            raise Refused(f"index {index} is cited before any line defines it")
        return table[index]

    def row(self, group: str, obj) -> dict:
        """One object of a declaration record: exactly its keys, each of its kind."""
        want = ROWS[group]
        if not isinstance(obj, dict) or set(obj) != set(want):
            raise Refused(f"{group}: the keys are not exactly {sorted(want)}")
        for key, kind in want.items():
            value = obj[key]
            if kind == "n":
                self.name_of(value)
            elif kind in ("N", "P"):
                names = [self.name_of(i) for i in listed(value)]
                if kind == "P" and len(set(names)) != len(names):
                    raise Refused("a level parameter listed twice")
            elif kind == "e":
                self.size(self.expr_size, value)
            elif kind == "i":
                nat(value)
            elif kind == "b":
                if type(value) is not bool:
                    raise Refused(f"{group}.{key} is not a boolean")
            elif kind == "R":
                for rule in listed(value):
                    self.row("rules", rule)
            elif kind == "H":
                if value not in ("opaque", "abbrev") and not (isinstance(value, dict) and set(value) == {"regular"} and nat(value["regular"]) >= 0):
                    raise Refused("def.hints is not \"opaque\", \"abbrev\" or an object with the key regular")
            elif value not in kind or not isinstance(value, str):
                raise Refused(f"{group}.{key} {value!r}")
        return obj

    def add(self, number: int, record: dict) -> None:
        if number == 1:
            meta = record.get("meta") if set(record) == {"meta"} else None
            if not isinstance(meta, dict) or meta.get("format") != {"version": "3.1.0"}:
                raise Refused("the first line is not a meta record of format version 3.1.0")
        elif "meta" in record:
            raise Refused("a second meta record")
        elif "in" in record:
            kind = next(iter(set(record) - {"in"}), None)
            if len(record) != 2 or kind not in ("str", "num") or nat(record["in"]) != len(self.name):
                raise Refused("a name record out of sequence or of another shape")
            part = record[kind]
            if not isinstance(part, dict) or set(part) != ({"pre", "str"} if kind == "str" else {"pre", "i"}):
                raise Refused("a name record of another shape")
            if kind == "str" and (not isinstance(part["str"], str) or any(c in part["str"] for c in LINE_ENDS)):
                raise Refused("a name component that is not a string, or holds U+0085, U+2028 or U+2029")
            name = self.name_of(part["pre"]) + ((("s", part["str"]),) if kind == "str" else (("n", nat(part["i"])),))
            if name in self.known:
                raise Refused("a name an earlier name record gave")
            self.known.add(name)
            self.name[record["in"]] = name
        elif "il" in record:
            kind = next(iter(set(record) - {"il"}), None)
            if len(record) != 2 or nat(record["il"]) != len(self.level) + 1:
                raise Refused("a level record out of sequence or of another shape")
            data = record[kind]
            if kind == "succ":
                total = self.size(self.level_size, data) + 1
            elif kind in ("max", "imax") and isinstance(data, list) and len(data) == 2:
                total = self.size(self.level_size, data[0]) + self.size(self.level_size, data[1]) + 1
            elif kind == "param":
                self.name_of(data)
                total = 1
            else:
                raise Refused(f"a level record of kind {kind!r}")
            if total > NODE_CAP:
                raise Refused(f"a level of more than {NODE_CAP} nodes as a tree")
            self.level[record["il"]], self.level_size[record["il"]] = record, total
        elif "ie" in record:
            self.add_expr(record)
        else:
            if len(record) != 1 or next(iter(record)) not in ("def", "thm", "opaque", "axiom", "quot", "inductive"):
                raise Refused("a record of no known kind")
            (kind, body), = record.items()
            if kind == "inductive":
                names = self.add_block(body)
            else:
                names = [self.name_of(self.row(kind, body)["name"])]
            if len(set(names)) != len(names) or self.declared & set(names):
                raise Refused("a name is declared by two records, or twice by one")
            self.declared.update(names)
            self.decl[number] = (kind, body)

    def add_expr(self, record: dict) -> None:
        kind = next(iter(set(record) - {"ie"}), None)
        if len(record) != 2 or nat(record["ie"]) != len(self.expr):
            raise Refused("an expression record out of sequence or of another shape")
        data, size = record[kind], lambda index: self.size(self.expr_size, index)
        if kind in EXPR_KEYS and (not isinstance(data, dict) or set(data) != EXPR_KEYS[kind]):
            raise Refused(f"ie.{kind}: the keys are not exactly {sorted(EXPR_KEYS[kind])}")
        if kind == "bvar":
            nat(data)
            total = 1
        elif kind == "sort":
            total = self.size(self.level_size, data) + 1
        elif kind == "const":
            self.name_of(data["name"])
            total = 1 + sum(self.size(self.level_size, u) for u in listed(data["us"]))
        elif kind == "app":
            total = size(data["fn"]) + size(data["arg"]) + 1
        elif kind in ("lam", "forallE"):
            self.name_of(data["name"])
            if data["binderInfo"] not in ("default", "implicit", "strictImplicit", "instImplicit") or not isinstance(data["binderInfo"], str):
                raise Refused(f"binderInfo {data['binderInfo']!r}")
            total = size(data["type"]) + size(data["body"]) + 1
        elif kind == "letE":
            self.name_of(data["name"])
            if type(data["nondep"]) is not bool:
                raise Refused("letE.nondep is not a boolean")
            total = size(data["type"]) + size(data["value"]) + size(data["body"]) + 1
        elif kind == "natVal" and isinstance(data, str) and data.isascii() and data.isdigit() and (data == "0" or data[0] != "0"):
            total = 1
        elif kind == "strVal" and isinstance(data, str):
            total = 1
        elif kind == "proj":
            self.name_of(data["typeName"])
            nat(data["idx"])
            total = size(data["struct"]) + 1
        elif kind == "mdata":
            total = size(data["expr"]) + 1
        else:
            raise Refused(f"an expression record of kind {kind!r}")
        if total > NODE_CAP:
            raise Refused(f"an expression of more than {NODE_CAP} nodes as a tree")
        self.expr[record["ie"]], self.expr_size[record["ie"]] = record, total

    def add_block(self, body) -> list[tuple]:
        """The names an `inductive` record declares, after the rules the checker's reader applies to one."""
        if not isinstance(body, dict) or set(body) != {"types", "ctors", "recs"} or not all(isinstance(body[g], list) for g in body):
            raise Refused("inductive: the keys are not exactly types, ctors and recs, each a list")
        rows = [(group, self.row(group, row)) for group in ("types", "ctors", "recs") for row in listed(body[group])]
        if not body["types"]:
            raise Refused("an inductive record with no type")
        first = body["types"][0]
        for group, row in rows:
            if group != "recs" and row["levelParams"] != first["levelParams"]:
                raise Refused("an inductive record whose types or constructors state different level parameters")
            if group == "types" and row["numParams"] != first["numParams"]:
                raise Refused("an inductive record whose types state different numParams")
        if [(c, t["name"]) for t in body["types"] for c in t["ctors"]] != [(c["name"], c["induct"]) for c in body["ctors"]]:
            raise Refused("an inductive record whose constructors are not its types' ctors lists in order")
        return [self.name[row["name"]] for _, row in rows]

    def name_echo(self, ident: int) -> str:
        return "[" + " ".join(f"s{len(text.encode('utf-8'))}:{text}" if tag == "s" else f"n{text}" for tag, text in self.name[ident]) + "]"

    def level_echo(self, ident: int, params: list[int]) -> str:
        if ident == 0:
            return "0"
        record = self.level[ident]
        if "succ" in record:
            return f"(s {self.level_echo(record['succ'], params)})"
        for tag in ("max", "imax"):
            if tag in record:
                left, right = record[tag]
                return f"({tag} {self.level_echo(left, params)} {self.level_echo(right, params)})"
        if record["param"] not in params:
            raise Refused("a level parameter the record does not list; the checker's level-scope check refuses it, so no such row is accepted")
        return f"(p {params.index(record['param'])})"

    def expr_echo(self, root: int, params: list[int]) -> str:
        done: dict[int, str] = {}
        stack = [root]
        while stack:
            node = stack[-1]
            if node in done:
                stack.pop()
                continue
            record = self.expr[node]
            kids: list[int] = []
            if "bvar" in record:
                make = lambda k, r=record: f"(b {r['bvar']})"
            elif "sort" in record:
                make = lambda k, r=record: f"(sort {self.level_echo(r['sort'], params)})"
            elif "const" in record:
                levels = "".join(" " + self.level_echo(u, params) for u in record["const"]["us"])
                make = lambda k, r=record, text=levels: f"(c {self.name_echo(r['const']['name'])}{text})"
            elif "app" in record:
                kids, make = [record["app"]["fn"], record["app"]["arg"]], lambda k: f"(app {k[0]} {k[1]})"
            elif "lam" in record:
                kids, make = [record["lam"]["type"], record["lam"]["body"]], lambda k: f"(lam {k[0]} {k[1]})"
            elif "forallE" in record:
                kids, make = [record["forallE"]["type"], record["forallE"]["body"]], lambda k: f"(pi {k[0]} {k[1]})"
            elif "letE" in record:
                let = record["letE"]
                kids, make = [let["type"], let["value"], let["body"]], lambda k: f"(let {k[0]} {k[1]} {k[2]})"
            elif "mdata" in record:
                kids, make = [record["mdata"]["expr"]], lambda k: k[0]
            else:
                # Not reached while the classifier is right: a literal or a projection puts its declaration outside.
                raise Refused(f"expression {node} has no echo here ({sorted(record)}), yet a row citing it is inside the fragment")
            pending = [k for k in kids if k not in done]
            if pending:
                stack.extend(pending)
                continue
            done[node] = make([done[k] for k in kids])
            stack.pop()
        return done[root]

    def decl_name(self, line: int) -> str:
        kind, body = self.decl[line]
        return self.name_echo(body["types"][0]["name"] if kind == "inductive" else body["name"])

    def statement(self, line: int) -> tuple[str, str]:
        _, body = self.decl[line]
        params = body["levelParams"]
        return self.expr_echo(body["type"], params), self.expr_echo(body["value"], params)

    def block_text(self, body: dict) -> str:
        """Every field of an `inductive` record, one row a line; a level parameter by position, never by its name."""
        own = body["types"][0]["levelParams"]
        lines = []
        for group in ("types", "ctors", "recs"):
            for row in body[group]:
                params = row["levelParams"]
                fields = [group]
                for key, kind in ROWS[group].items():
                    value = row[key]
                    if kind == "n":
                        text = self.name_echo(value)
                    elif kind == "N":
                        text = "[" + ",".join(self.name_echo(i) for i in value) + "]"
                    elif kind == "P":
                        text = ",".join(f"t{own.index(p)}" if p in own else "e" for p in value)
                    elif kind == "e":
                        text = self.expr_echo(value, params)
                    elif kind == "R":
                        text = ";".join(f"{self.name_echo(r['ctor'])} {r['nfields']} {self.expr_echo(r['rhs'], params)}" for r in value)
                    else:
                        text = json.dumps(value)
                    fields.append(f"{key}={text}")
                lines.append("\t".join(fields))
        return "\n".join(lines) + "\n"

    def base_block(self, body: dict) -> list[int] | None:
        """The name indices a base family's record makes citable (every name it declares), or None."""
        want = BASE.get(self.name_echo(body["types"][0]["name"]))
        try:
            if want is None or sha(self.block_text(body).encode("utf-8")) != want:
                return None
        except Refused:
            return None
        return [row["name"] for group in ("types", "ctors", "recs") for row in body[group]]


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__.strip().split("\n\n")[-1], file=sys.stderr)
        return 2
    path = Path(sys.argv[1])
    raw = Raw(gzip.decompress(path.read_bytes()) if path.suffix == ".gz" else path.read_bytes())
    for line, (kind, body) in raw.decl.items():
        if kind == "inductive" and raw.name_echo(body["types"][0]["name"]) in BASE:
            text = raw.block_text(body)
            print(f"line {line}  {raw.decl_name(line)}  sha256 {sha(text.encode('utf-8'))}\n{text}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
