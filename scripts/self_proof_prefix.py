#!/usr/bin/env python3
"""Measure consecutive admissions on an NDJSON export using the adopted Lean checker."""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import zlib

from kstar_subjects import DECL_KINDS

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "theories/kcheck_run"
DRIVER = ROOT / "scripts/SelfProofPrefix.lean"
SDK_HASH = "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"
SCHEMA = "clean.self-proof-prefix.v1"


def file_hash(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def run(argv, **kwargs):
    result = subprocess.run(argv, cwd=ROOT, capture_output=True, **kwargs)
    if result.returncode:
        detail = (result.stderr + result.stdout).decode(errors="replace")[-2400:]
        raise ValueError(f"{Path(argv[0]).name} exited {result.returncode}: {detail}")
    return result.stdout


def prepare():
    pin = (PACKAGE / "lean-toolchain").read_text().strip()
    sdk = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan")) / "toolchains" / pin.replace("/", "--").replace(":", "---")
    lean, lake = sdk / "bin/lean", sdk / "bin/lake"
    sdk_hash = run([lean, "--githash"]).decode().strip()
    if sdk_hash != SDK_HASH:
        raise ValueError(f"Lean SDK {pin} reported unexpected source revision {sdk_hash}")
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    prefix = [lake, "--dir", PACKAGE]
    run([*prefix, "--no-cache", "build", "+KCheckRun.Recognise:olean"], env=env)
    setup = json.loads((PACKAGE / ".lake/build/ir/KCheckRun/Recognise.setup.json").read_text())
    modules = dict(setup["importArts"])
    modules["KCheckRun.Recognise"] = [str(PACKAGE / ".lake/build/lib/lean/KCheckRun/Recognise.olean")]
    source_hashes, object_hashes = {}, {}
    for name, files in sorted(modules.items()):
        obj, = [Path(f) for f in files if f.endswith(".olean")]
        rel = obj.relative_to(ROOT / "theories")
        src = ROOT / "theories" / rel.parts[0] / Path(*name.split(".")).with_suffix(".lean")
        source_hashes[name], object_hashes[name] = file_hash(src), file_hash(obj)
    identity = {"toolchain": pin, "lean_githash": sdk_hash, "lean_sha256": file_hash(lean),
                "lake_sha256": file_hash(lake), "driver_sha256": file_hash(DRIVER),
                "reporter_sha256": file_hash(Path(__file__)), "source_sha256": source_hashes,
                "olean_sha256": object_hashes, "entry": "KCheck.kcheckBytes",
                "initial_environment": "KCheck.base", "advice": "ByteArray.empty"}
    return [*prefix, "env", lean, "--run", DRIVER], env, identity


def gated(script, argv, label):
    command = ["build-slot", "--cpus", "4", "--", str(ROOT / "scripts/heavy_gate.sh"), "run",
               "auto:pr30-prefix:3", label, "--", sys.executable, str(script), *argv]
    return subprocess.run(command, cwd=ROOT).returncode


def lexical_names(row):
    """Read the ordered declaration name slots. Lean independently judges each row."""
    if not isinstance(row, dict):
        raise ValueError("expected an object")
    if len(row) == 2 and len(row.keys() & {"in", "il", "ie"}) == 1:
        return None, []
    if len(row) != 1:
        raise ValueError("unrecognised record keys")
    kind, value = next(iter(row.items()))
    if kind == "meta":
        return None, []
    if kind not in DECL_KINDS or not isinstance(value, dict):
        raise ValueError("unrecognised declaration record")
    if kind == "inductive":
        members = [value[group] for group in ("types", "ctors", "recs")]
        if not all(isinstance(group, list) for group in members):
            raise ValueError("inductive member list unreadable")
        entries = [item for group in members for item in group]
    else:
        entries = [value]
    if not all(isinstance(item, dict) and type(item.get("name")) is int and item["name"] >= 0
               for item in entries):
        raise ValueError("declaration name index unreadable")
    return kind, [entry["name"] for entry in entries]


def lexical_count(row):
    kind, indices = lexical_names(row)
    return kind, len(indices)


def unique_object(pairs):
    result = dict(pairs)
    if len(result) != len(pairs):
        raise ValueError("duplicate JSON key")
    return result


def add_name(nodes, row):
    key = "str" if "str" in row else "num"
    part = row.get(key)
    if not isinstance(part, dict):
        raise ValueError("invalid wire name component")
    parent = part.get("pre")
    value = part.get("str" if key == "str" else "i")
    valid_value = isinstance(value, str) if key == "str" else type(value) is int and value >= 0
    if (type(row["in"]) is not int or row["in"] != len(nodes)
            or type(parent) is not int or not 0 <= parent < len(nodes) or not valid_value):
        raise ValueError("invalid wire name reference")
    nodes.append((parent, value))


def name_matches(nodes, index, components):
    """Compare structured names without expanding every path in the name table."""
    if index >= len(nodes) or not isinstance(components, list):
        return False
    for component in reversed(components):
        if index == 0:
            return False
        index, wire = nodes[index]
        if type(component) is not type(wire) or component != wire:
            return False
    return index == 0


def display_name(text, components):
    """Bind the driver's display to the wire name, preserving Lean's quoted components."""
    if not components:
        if text != "[anonymous]":
            raise ValueError("display differs from anonymous wire name")
        return text
    pos = 0
    ambiguous = False
    for i, part in enumerate(components):
        separator = "." if i + 1 < len(components) else ""
        raw = str(part)
        # Lean can suppress escaping (e.g. for macro scopes). Match the actual
        # component boundaries; a numeric component is never quoted.
        forms = [raw]
        if isinstance(part, str) and "»" not in part:
            forms.append("«" + part + "»")
        for form in forms:
            end = pos + len(form) + len(separator)
            if text.startswith(form + separator, pos) and (i + 1 < len(components) or end == len(text)):
                pos = end
                if isinstance(part, str):
                    ambiguous |= not part.isprintable() or (form == raw and (
                        not part or "." in part or part.isdecimal() or part == "[anonymous]"
                        or "«" in part or "»" in part))
                break
        else:
            raise ValueError("display differs from structured wire name")
    return json.dumps(components) if ambiguous else text


def check_record(event, kind, indices, nodes):
    names, components = event.get("names"), event.get("name_components")
    if (kind is None or event.get("kind") != kind or not indices
            or not isinstance(names, list) or not isinstance(components, list)
            or not all(isinstance(name, str) for name in names)
            or len(names) != len(indices) or len(components) != len(indices)
            or event.get("name") != names[0]
            or not all(name_matches(nodes, index, parts) for index, parts in zip(indices, components))):
        raise ValueError("checker event differs from wire declaration")
    if "receipt" in event and (event["receipt"] != names[0]
            or not name_matches(nodes, indices[0], event.get("receipt_components"))):
        raise ValueError("checker receipt differs from wire declaration")
    event["names"] = [display_name(text, parts) for text, parts in zip(names, components)]
    event["name"] = event["names"][0]
    if "receipt" in event:
        event["receipt"] = event["name"]


def describe(raw, events, limit, identity):
    if (not events or any(not isinstance(event, dict) or type(event.get("line")) is not int
                          or event["line"] < 0 for event in events)
            or "stop" not in events[-1] or "receipt" in events[-1]
            or any("receipt" not in event or "stop" in event for event in events[:-1])):
        raise ValueError("incomplete checker transcript")
    admitted = [dict(event) for event in events[:-1]]
    last = dict(events[-1])
    stop = last.pop("stop")
    if stop not in ("checker_refused", "loader_refused", "limit_reached", "exhausted"):
        raise ValueError("unknown checker transcript exit")
    lines = [event["line"] for event in admitted]
    last_accepted = lines[-1] if lines else 0
    if lines and (lines[0] == 0 or any(before >= after for before, after in zip(lines, lines[1:]))):
        raise ValueError("checker receipt lines must increase")
    if limit is not None and len(admitted) > limit:
        raise ValueError("more checker receipts than the requested limit")
    reported = {event["line"]: event for event in admitted}
    terminal_record = stop == "checker_refused" or (stop == "loader_refused" and last.get("stage") == "family_rows")
    if terminal_record:
        reported[last["line"]] = last
    if stop in ("checker_refused", "loader_refused") and not (isinstance(last.get("reason"), str) and last["reason"]):
        raise ValueError("checker or loader refusal is missing its diagnostic")
    if stop == "loader_refused":
        if last.get("stage") not in ("bytes", "load", "family_rows"):
            raise ValueError("unknown loader refusal stage")
        if not terminal_record and last.keys() != {"line", "reason", "stage"}:
            raise ValueError("loader failure supplied undeclared record fields")
        if terminal_record and (last.get("kind") != "inductive" or last.get("known_family") is not True
                                or last.get("recognised_rows") is not False):
            raise ValueError("invalid recursor comparison refusal")
    elif stop == "checker_refused" and "stage" in last:
        raise ValueError("checker refusal supplied a loader stage")
    elif stop in ("exhausted", "limit_reached") and last.keys() != {"line"}:
        raise ValueError("unexpected fields in completion of checker transcript")
    # The extra ordinal is a lexical count through this line, independent of the
    # driver's success count. Meta and table rows leave it unchanged.
    boundaries = {0: (hashlib.sha256(b"").hexdigest(), 0, None, 0)}
    nodes = [None]  # wire name zero is anonymous
    digest = hashlib.sha256()
    size = line = records = names = 0
    first_unreadable = None
    with raw.open("rb") as stream:
        for line, data in enumerate(stream, 1):
            digest.update(data)
            size += len(data)
            kind, indices = None, []
            try:
                row = json.loads(data, object_pairs_hook=unique_object)
                kind, indices = lexical_names(row)
                if kind is not None:
                    records += 1
                    names += len(indices)
            except (ValueError, KeyError, RecursionError) as problem:
                if first_unreadable is None:
                    first_unreadable = {"line": line, "reason": str(problem)}
            else:
                if line < last["line"] or (line == last["line"] and (line in reported or stop == "exhausted")):
                    if not data.endswith(b"\n") or (line == 1 and set(row) != {"meta"}):
                        raise ValueError("checker advanced past an incomplete wire row or missing header")
                    if "in" in row:
                        add_name(nodes, row)
            if line in reported:
                check_record(reported[line], kind, indices, nodes)
            if line in reported or line == last["line"]:
                boundaries[line] = (digest.hexdigest(), size, kind, records)
    if last["line"] not in boundaries or any(n not in boundaries for n in lines):
        raise ValueError("checker transcript names a line outside the input")
    if first_unreadable is not None and (first_unreadable["line"] < last["line"]
            or (first_unreadable["line"] == last["line"] and stop != "loader_refused")):
        raise ValueError("checker transcript crosses an unreadable wire record")
    for ordinal, event in enumerate(admitted, 1):
        prefix, nbytes, _, wire_ordinal = boundaries[event["line"]]
        if wire_ordinal != ordinal:
            raise ValueError("checker receipts skip a wire declaration")
        event.update(ordinal=ordinal, prefix_sha256=prefix, prefix_bytes=nbytes)
    prefix, nbytes, kind, wire_count = boundaries[last["line"]]
    if stop == "exhausted":
        if not size or last["line"] != line or wire_count != len(admitted):
            raise ValueError("checker exhaustion differs from the complete wire input")
        if len(admitted) == limit and last_accepted != line:
            raise ValueError("checker crossed the requested limit before exhaustion")
    elif stop == "limit_reached":
        if len(admitted) != limit or last["line"] != last_accepted or nbytes >= size:
            raise ValueError("checker limit differs from the bounded wire prefix")
    elif not size:
        if stop != "loader_refused" or last.get("stage") != "bytes" or last["line"] != 0:
            raise ValueError("invalid checker stop on empty input")
    elif (last["line"] <= last_accepted or wire_count != len(admitted) + int(kind is not None)
          or len(admitted) == limit):
        raise ValueError("checker refusal differs from the next wire record")
    terminal = None
    if stop in {"loader_refused", "checker_refused"}:
        terminal = dict(last, ordinal=len(admitted) + 1 if kind or last.get("kind") else None,
                        name=last.get("name"), kind=last.get("kind", kind))
    return {"schema": SCHEMA, "input_sha256": digest.hexdigest(), "input_bytes": size, "input_lines": line,
            "declaration_records": records if first_unreadable is None else None,
            "named_declarations": names if first_unreadable is None else None,
            "census_unreadable": first_unreadable, "limit": limit, "stop": stop, "terminal": terminal,
            "prefix_lines": last["line"], "prefix_bytes": nbytes, "prefix_sha256": prefix,
            "accepted": admitted, "accepted_records": len(admitted),
            "accepted_named_declarations": sum(len(event["names"]) for event in admitted),
            "identity": identity}


def measure(export, limit=None, runtime=None):
    if limit is not None and (type(limit) is not int or limit < 0):
        raise ValueError("limit must be a nonnegative record count")
    with tempfile.TemporaryDirectory(prefix="clean-self-proof-prefix-") as directory:
        raw = Path(directory) / "snapshot.ndjson"
        with export.open("rb") as source, raw.open("wb") as target:
            magic = source.read(2)
            source.seek(0)
            if magic == b"\x1f\x8b":
                with gzip.GzipFile(fileobj=source, mode="rb") as decoded:
                    shutil.copyfileobj(decoded, target)
            else:
                shutil.copyfileobj(source, target)
        command, env, identity = runtime or prepare()
        output = run([*command, raw, str(limit) if limit is not None else "all"], env=env)
        events = [json.loads(row, object_pairs_hook=unique_object) for row in output.splitlines()]
        return describe(raw, events, limit, identity)


def render(result):
    denom = result["declaration_records"]
    names = result["named_declarations"]
    terminal = result["terminal"]
    where = "" if terminal is None else f" at line {terminal['line']} ({terminal.get('name') or terminal['stage']})"
    return (f"Accepted {result['accepted_records']} of {denom if denom is not None else 'unknown'} records"
            f" covering {result['accepted_named_declarations']} of {names if names is not None else 'unknown'} names.\n"
            f"{result['stop']}{where}. Input SHA-256 {result['input_sha256']}.\n"
            f"Examined prefix SHA-256 {result['prefix_sha256']}.")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("export", type=Path, help="raw or gzip-compressed NDJSON")
    parser.add_argument("--limit", type=int, help="maximum number of consecutive checker records")
    parser.add_argument("--json", action="store_true", help="include receipts, byte hashes and executable identities")
    args = parser.parse_args(argv)
    if args.limit is not None and args.limit < 0:
        parser.error("--limit must be nonnegative")
    try:
        if not os.environ.get("HEAVY_GATE_HELD"):
            options = [str(args.export.resolve())]
            if args.limit is not None:
                options += ["--limit", str(args.limit)]
            if args.json:
                options += ["--json"]
            return 0 if gated(Path(__file__).resolve(), options, "pr30-prefix-run") == 0 else 2
        result = measure(args.export, args.limit)
        print(json.dumps(result, indent=2, ensure_ascii=False) if args.json else render(result))
        return 0
    except (ValueError, KeyError, OSError, EOFError, zlib.error) as problem:
        print(f"Prefix measurement unavailable: {problem}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
