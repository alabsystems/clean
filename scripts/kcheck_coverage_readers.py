#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""The second reader of scripts/kcheck_coverage.py: an export, an advice file and a transcript, re-derived.

Nothing here runs the checker or reads its Lean sources. `derive` has
scripts/kcheck_coverage_export.py read the raw lean4export NDJSON records as
strictly as the checker's own reader does and say which records are the three
base families, classifies every declaration with
scripts/kcheck_fragment_census.py, and refuses a transcript that disagrees with
any of it: a class, a name, a statement echo, a detail, a dependency, a count.
"""

from __future__ import annotations

import importlib.util
import re
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
NUMBER = re.compile(r"0|[1-9][0-9]*")
HEADERS = (
    "kcheck-run-interim\t1",
    "checker\tkcheck_labelled\tKCheck.kcheckBytes\tsoundness=not-claimed-by-this-run",
    "loader\tinterim\tproved=false\treprint=absent\trecs=dropped-unchecked",
    "base\tEq\tPUnit\tNat",
)
SUMMARY_KEYS = ["declarations", "accepted", "recognised", "outside", "refused"]
ORDINARY = ("def", "thm", "opaque")
ACCEPTED_DETAIL = re.compile(r"bound=(?:0|[1-9][0-9]*)(?:;(?:0|[1-9][0-9]*)\+(?:0|[1-9][0-9]*))* iota=([01]) k=([01]) lparams=(0|[1-9][0-9]*)")
OUTSIDE_DETAIL = re.compile(r"quotient|axiomDecl|unsafe|partial|literal|projection|freeVariable|inductiveBlock|cites:\[.*\]")
OPERAND_TAGS, IOTA, K, LAST_TAG = (0x01, 0x08, 0x09, 0x15), 0x0B, 0x0C, 0x16


def sibling(name: str):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


export = sibling("kcheck_coverage_export")
Refused, Raw, sha = export.Refused, export.Raw, export.sha


def split_frames(advice: bytes) -> list[bytes]:
    """Frames of a minimal unsigned LEB128 length and then that many bytes."""
    frames, at = [], 0
    while at < len(advice):
        length, shift, start = 0, 0, at
        while True:
            if at >= len(advice):
                raise Refused(f"the advice ends inside a frame length at byte {start}")
            byte = advice[at]
            at += 1
            length |= (byte & 0x7F) << shift
            shift += 7
            if not byte & 0x80:
                if byte == 0 and at - start > 1:
                    raise Refused(f"the frame length at byte {start} is not minimal LEB128")
                break
        if at + length > len(advice):
            raise Refused(f"the frame at byte {start} states {length} bytes and the advice ends first")
        frames.append(advice[at:at + length])
        at += length
    return frames


def frame_tags(frame: bytes) -> set[int]:
    """The tags of a frame read token by token; an operand byte is never taken for a tag."""
    tags, at = set(), 0
    while at < len(frame):
        tag = frame[at]
        at += 1
        if not 1 <= tag <= LAST_TAG:
            raise Refused(f"byte {tag:#04x} where a token's tag is expected; the checker refuses such a frame")
        tags.add(tag)
        if tag in OPERAND_TAGS:
            while at < len(frame) and frame[at] & 0x80:
                at += 1
            at += 1
    return tags


def parse_transcript(text: str) -> tuple[list[dict], dict[str, int]]:
    """The declaration rows (with their statement echoes) and the summary, strictly."""
    if "\r" in text:
        raise Refused("the transcript holds a carriage return; the checker prints line feeds only")
    if not text.endswith("\n"):
        raise Refused("the transcript does not end with a line feed")
    lines = text[:-1].split("\n")
    if tuple(lines[:4]) != HEADERS:
        raise Refused("the transcript's four header lines are not the ones version 1 prints")
    if len(lines) < 5 or not lines[-1].startswith("summary\t"):
        raise Refused("the transcript has no summary line")
    rows: list[dict] = []
    for line in lines[4:-1]:
        fields = line.split("\t")
        if fields[0] == "decl" and len(fields) == 6 and NUMBER.fullmatch(fields[1]):
            rows.append({"line": int(fields[1]), "kind": fields[2], "class": fields[3], "detail": fields[4], "name": fields[5]})
        elif fields[0] == "stmt" and len(fields) == 4 and NUMBER.fullmatch(fields[1]):
            if not rows or rows[-1]["line"] != int(fields[1]) or rows[-1]["class"] != "accepted" or "stmt" in rows[-1]:
                raise Refused(f"a statement line for {fields[1]} does not follow that declaration's accepted row")
            rows[-1]["stmt"] = (fields[2], fields[3])
        else:
            raise Refused(f"the transcript holds a line of no known shape: {line[:60]!r}")
    parts = [part.partition("=") for part in lines[-1].split("\t")[1:]]
    if [key for key, _, _ in parts] != SUMMARY_KEYS or not all(NUMBER.fullmatch(value) for _, _, value in parts):
        raise Refused("the summary line is malformed")
    return rows, {key: int(value) for key, _, value in parts}


def classify(raw: Raw):
    """The census's table of the export and its row per declaration line, base families recognised by their whole record."""
    census = sibling("kcheck_fragment_census")
    table = census.Export(raw.records)

    def recognise(body: dict) -> list | None:
        found = raw.base_block(body)
        return None if found is None else [table.names[index] for index in found]

    return table, {row[0]: row for row in census.classify(table, frozenset(), recognise)}


def derive(export_raw: bytes, advice: bytes, transcript: str) -> dict:
    """Every figure the record states, re-derived; raises Refused where the second reader disagrees."""
    raw = Raw(export_raw)
    table, independent = classify(raw)
    inside_line = {name: line for line, kind, name, cls, _ in independent.values() if cls == "inside" and kind in ORDINARY}
    rows, summary = parse_transcript(transcript)
    seen = [row["line"] for row in rows]
    if seen != sorted(set(seen)):
        raise Refused("the transcript's declaration rows are not in file order, or one line is stated twice")
    if set(seen) != set(raw.decl):
        raise Refused(f"the transcript has rows for {len(seen)} lines; the export has {len(raw.decl)} declaration records, on other lines")
    frames = split_frames(advice)
    if len(frames) != len(rows):
        raise Refused(f"the advice has {len(frames)} frames for {len(rows)} declaration records")
    counts = {"accepted": 0, "recognised": 0, "outside": 0, "refused": 0}
    accepted, accepted_lines = [], set()
    for row, frame in zip(rows, frames):
        line, cls = row["line"], row["class"]
        if cls not in counts:
            raise Refused(f"line {line}: class {cls!r} is not one of version 1's")
        counts[cls] += 1
        kind, body = raw.decl[line]
        if row["kind"] != kind:
            raise Refused(f"line {line}: the transcript says kind {row['kind']}, the export {kind}")
        if row["name"] != raw.decl_name(line):
            raise Refused(f"line {line}: the transcript names {row['name']}, the export {raw.decl_name(line)}")
        theirs = "inside" if cls in ("accepted", "refused") else cls
        if theirs != independent[line][3]:
            raise Refused(f"line {line}: the run's class is {cls}; the independent classifier says {independent[line][3]} {independent[line][4]}".rstrip())
        if theirs != "inside" and frame:
            raise Refused(f"line {line}: a frame of {len(frame)} bytes for a declaration that is not inside the fragment")
        if (cls == "accepted") != ("stmt" in row):
            raise Refused(f"line {line}: an accepted row and a statement line go together, and here they do not")
        if cls == "recognised" and row["detail"] != "base" or cls == "outside" and not OUTSIDE_DETAIL.fullmatch(row["detail"]):
            raise Refused(f"line {line}: the detail {row['detail'][:40]!r} is not one version 1 prints for class {cls}")
        if theirs != "inside":
            continue
        if kind not in ORDINARY:
            # Not reached while the classifier is right: it calls only definitions, theorems and opaques inside.
            raise Refused(f"line {line}: a {kind} record is {cls}; only definitions, theorems and opaques are decided")
        cited = set()
        for field in ("type", "value"):
            cited |= table.facts(body[field])[0]
        owed = sorted(inside_line[name] for name in cited if name in inside_line and inside_line[name] not in accepted_lines and inside_line[name] != line)
        waits = row["detail"].startswith("dependency:")
        if cls == "accepted" and owed:
            raise Refused(f"line {line}: accepted, yet it cites the declaration at line {owed[0]}, which the run did not accept")
        if cls == "refused" and bool(owed) != waits:
            raise Refused(f"line {line}: a row is refused for a dependency exactly when it cites one the run did not accept, and here it is not so")
        if waits and row["detail"][len("dependency:"):] not in {raw.decl_name(other) for other in owed}:
            raise Refused(f"line {line}: refused for a dependency it does not cite, or one the run accepted")
        if cls == "accepted":
            shape = ACCEPTED_DETAIL.fullmatch(row["detail"])
            if not frame:
                raise Refused(f"line {line}: accepted on an empty advice frame")
            tags = frame_tags(frame)
            if not shape or (shape[1], shape[2]) != (str(int(IOTA in tags)), str(int(K in tags))):
                raise Refused(f"line {line}: the accepted detail {row['detail'][:60]!r} is not the one this frame gives")
            if int(shape[3]) != len(body["levelParams"]):
                raise Refused(f"line {line}: the checker was handed {shape[3]} level parameters; the export lists {len(body['levelParams'])}")
            if row["stmt"] != raw.statement(line):
                raise Refused(f"line {line}: the statement the checker was handed is not the one the export states")
            accepted_lines.add(line)
            accepted.append({
                "line": line,
                "name": row["name"],
                "kind": kind,
                "detail": row["detail"],
                "level_params": len(body["levelParams"]),
                "statement_sha256": sha("\t".join(row["stmt"]).encode("utf-8")),
                "advice_frame_sha256": sha(frame),
            })
    if summary != {"declarations": len(rows), **counts}:
        raise Refused(f"the summary line says {summary}; the rows count {len(rows)} and {counts}")
    return {
        "declaration_records": len(rows),
        "ordinary_declarations": sum(1 for kind, _ in raw.decl.values() if kind in ORDINARY),
        "inside_fragment": counts["accepted"] + counts["refused"],
        "accepted": counts["accepted"],
        "refused_inside": counts["refused"],
        "recognised_families": counts["recognised"],
        "outside_fragment": counts["outside"],
        "accepted_declarations": accepted,
    }
