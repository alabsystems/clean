#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Prepare native candidate advice for kcheck-run-interim on a supplied export."""
import argparse
import gzip
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import zlib

import kcheck_coverage_readers as readers

ROOT = Path(__file__).resolve().parents[1]


def prepare_frames(classes, wire):
    frames = readers.split_frames(wire)
    if len(frames) != len(classes):
        raise readers.Refused(f"{len(frames)} native frames for {len(classes)} declaration records")
    output = bytearray()
    offset = 0
    removed = 0
    for cls, frame in zip(classes, frames):
        # split_frames has already checked the minimal unsigned LEB128 length.
        prefix_size = max(1, (len(frame).bit_length() + 6) // 7)
        end = offset + prefix_size + len(frame)
        if cls == "inside":
            output.extend(wire[offset:end])
        elif cls in ("outside", "recognised"):
            output.append(0)
            removed += bool(frame)
        else:
            raise readers.Refused(f"unknown fragment class {cls!r}")
        offset = end
    return bytes(output), sum(bool(frame) for frame in frames), removed


def prepare(export, emitter, output):
    if output.resolve() in (export.resolve(), emitter.resolve()):
        raise ValueError("the output path must be distinct from the export and emitter")
    blob = export.read_bytes()
    if blob.startswith(b"\x1f\x8b"):
        blob = gzip.decompress(blob)
    raw = readers.Raw(blob)
    _, classified = readers.classify(raw)
    classes = [classified[line][3] for line in sorted(raw.decl)]
    with tempfile.TemporaryDirectory(prefix="kcheck-advice-") as name:
        work = Path(name)
        source, emitted = work / "export.ndjson", work / "native.bin"
        source.write_bytes(blob)
        result = subprocess.run([str(emitter.resolve()), "--replay-candidates", source,
                                 "--out", emitted], cwd=work, capture_output=True)
        if result.returncode != 0:
            raise readers.Refused(f"native emitter exited {result.returncode}: "
                                  + result.stderr.decode(errors="replace").strip())
        wire = emitted.read_bytes()
        native = json.loads(result.stdout)
        selected, nonempty, removed = prepare_frames(classes, wire)
        expected = {"frames": len(classes), "non_empty": nonempty, "sha256": readers.sha(wire)}
        if (native != expected or type(native["frames"]) is not int
                or type(native["non_empty"]) is not int):
            raise readers.Refused("native emitter summary differs from its output file")
    # A failure before replace leaves an earlier usable advice file intact.
    with tempfile.TemporaryDirectory(dir=output.parent) as destination:
        temporary = Path(destination) / "advice.bin"
        temporary.write_bytes(selected)
        os.replace(temporary, output)
    return {"export_sha256": readers.sha(blob), "native_sha256": expected["sha256"],
            "prepared_sha256": readers.sha(selected), "frames": len(classes),
            "inside": classes.count("inside"), "recognised": classes.count("recognised"),
            "outside": classes.count("outside"), "nonempty_native": nonempty,
            "cleared_nonempty": removed, "nonempty_prepared": nonempty - removed}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("export", type=Path, help="raw or gzipped lean4export NDJSON")
    parser.add_argument("--emitter", type=Path, default=ROOT / "target/debug/kcheck_advice_emit",
                        help="path to the native emitter built with the kcheck-trace feature")
    parser.add_argument("--out", required=True, type=Path, help="write the prepared advice file")
    args = parser.parse_args()
    try:
        print(json.dumps(prepare(args.export, args.emitter, args.out), sort_keys=True))
    except (OSError, ValueError, UnicodeError, EOFError, zlib.error, readers.Refused) as error:
        print(f"kcheck_prepare_advice: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
