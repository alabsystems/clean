#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Validate the PR-67 retained native-advice transcripts against the original proof bytes."""

import gzip
import hashlib
import json
from pathlib import Path

import kcheck_coverage_readers as reader
from kcheck_prepare_advice import prepare_frames

ROOT = Path(__file__).resolve().parents[1]
REPORT = Path("reports/self-proof-native-proof-prefix/matcher")
FULL_SHA = "17e3501dbd8689e7a241227c1711df4b06b3edd6184353feb01af672c9284f62"
PREFIX_SHA = "c4acb50981b5704366c94d76d196ef8abcdb3c8278479ba1ea94192356c3d8d5"
PREFIX_LINES = 3089
MATCHER = "[s3:Nat s3:ble s7:match_1]"
SHORT_NAME = "Nat.ble.match_1"
REFUSAL = "KCheck.Refusal.advice (KCheck.DecodeError.truncated 0)"
COUNT_FIELDS = ("declaration_records", "accepted", "refused_inside", "recognised_families", "outside_fragment")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pinned_json(path, digest):
    payload = path.read_bytes()
    require(reader.sha(payload) == digest, f"Historical receipt changed: {path.name}")
    return json.loads(payload)


def proof_prefix(root):
    archive = root / "reports/self-proof-const-branch-trial/candidate.ndjson.gz"
    digest = hashlib.sha256()
    with gzip.open(archive, "rb") as stream:
        prefix = b"".join(stream.readline() for _ in range(PREFIX_LINES))
        digest.update(prefix)
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    require(digest.hexdigest() == FULL_SHA and reader.sha(prefix) == PREFIX_SHA,
            "The full proof stream or the genuine prefix ending at the matcher changed")
    return prefix


def derive(root):
    folder = root / REPORT
    old = folder.parent
    tools = pinned_json(root / "reports/self-proof-native-init-slice/qualification.json",
                        "30f458df5a9b8e0eee518c8996243f18ccc73b8060e0afc734a226343e6bc1d2")
    prior = pinned_json(old / "qualification.json",
                        "9354bb0e420e541784ec18bf5b1a19aee0b95da6903323bc642691a026ba7d85")
    strict = pinned_json(root / "reports/self-proof-prefix-measurement/clean-current.json",
                         "3c78359f3f36fc46901cfb713490007380b044da10f690fd04848d45b90eee1f")
    require(prior["full_export_sha256"] == strict["input_sha256"] == FULL_SHA
            and all(prior[key] == tools[key]
                    for key in ("producer_source", "emitter_sha256", "interim_checker_sha256")),
            "The earlier measurements used a different subject or different executables")

    prefix = proof_prefix(root)
    raw = reader.Raw(prefix)
    _, classified = reader.classify(raw)
    classes = [classified[line][3] for line in sorted(raw.decl)]
    emitted = (folder / "native.bin").read_bytes()
    prepared, nonempty, cleared = prepare_frames(classes, emitted)
    require(prepared == (folder / "prepared.bin").read_bytes(), "Prepared advice differs from the native frames")
    emitter_summary = json.loads((folder / "emitter.stdout").read_bytes())
    require(emitter_summary == dict(frames=len(classes), non_empty=nonempty, sha256=reader.sha(emitted)),
            "Emitter summary differs from the actual frame file")

    frames = reader.split_frames(prepared)
    changed, _, removed = prepare_frames(["inside"] * (len(frames) - 1) + ["outside"], prepared)
    require(removed == 1 and changed == (folder / "control.bin").read_bytes()
            and reader.split_frames(changed) == frames[:-1] + [b""], "Control did not clear exactly the last frame")
    positive = (folder / "checker.stdout").read_bytes()
    negative = (folder / "control.stdout").read_bytes()
    original = reader.derive(prefix, prepared, positive.decode())
    control = reader.derive(prefix, changed, negative.decode())
    rows, _ = reader.parse_transcript(positive.decode())
    bad, _ = reader.parse_transcript(negative.decode())
    require(rows[:-1] == bad[:-1] and rows[-1]["name"] == bad[-1]["name"] == MATCHER
            and rows[-1]["line"] == bad[-1]["line"] == PREFIX_LINES
            and rows[-1]["class"] == "accepted" and bad[-1]["class"] == "refused"
            and bad[-1]["detail"] == REFUSAL, "The changed frame must refuse the same matcher alone")
    require(tuple(original[key] for key in COUNT_FIELDS) == (87, 9, 0, 3, 75)
            and tuple(control[key] for key in COUNT_FIELDS) == (87, 8, 1, 3, 75),
            "The original or changed transcript differs from the measured partition")
    require(reader.frame_tags(frames[-1]).isdisjoint((reader.IOTA, reader.K)),
            "The original matcher advice had no iota or K step")

    old_prefix = prefix[:prior["prefix_bytes"]]
    old_wire = (old / "frames.bin").read_bytes()
    old_out = (old / "checker.txt").read_bytes()
    require(reader.sha(old_prefix) == prior["prefix_sha256"]
            and reader.sha(old_wire) == prior["prepared_sha256"]
            and reader.sha(old_out) == prior["positive_sha256"], "Earlier 24-record evidence changed")
    old_rows, old_counts = reader.parse_transcript(old_out.decode())
    earlier = reader.derive(old_prefix, old_wire, old_out.decode())
    require(old_counts == prior["positive"] and old_rows == rows[:len(old_rows)]
            and reader.split_frames(old_wire) == frames[:len(old_rows)],
            "An earlier row or its prepared frame changed in the extended replay")

    observed = original["accepted_declarations"][-1]
    reads = {path: reader.sha((folder / path).read_bytes()) for path in (
        "native.bin", "prepared.bin", "control.bin", "emitter.stdout", "emitter.stderr",
        "checker.stdout", "checker.stderr", "control.stdout", "control.stderr")}
    exits = json.loads((folder / "exits.json").read_bytes())
    require(exits == {"emitter": 0, "checker": 0, "control": 0}, "Recorded process exits differ")

    return {
        "schema": "clean.native-proof-matcher.v1", "source_sha256": FULL_SHA,
        "prefix_sha256": reader.sha(prefix), "prefix_lines": PREFIX_LINES, "prefix_bytes": len(prefix),
        "producer_source_revision": tools["producer_source"], "emitter_sha256": tools["emitter_sha256"],
        "checker_sha256": tools["interim_checker_sha256"], "artifacts_sha256": reads, "exits": exits,
        "prior": {key: earlier[key] for key in COUNT_FIELDS},
        "positive": {key: original[key] for key in COUNT_FIELDS},
        "control": {**{key: control[key] for key in COUNT_FIELDS}, "name": SHORT_NAME,
                    "reason": bad[-1]["detail"], "unchanged_prior_rows": len(rows) - 1, "changed_frame_records": removed},
        "matcher": {"name": SHORT_NAME, "wire_name": observed["name"], "line": observed["line"],
                    "frame_bytes": len(frames[-1]), "frame_sha256": observed["advice_frame_sha256"],
                    "statement_sha256": observed["statement_sha256"], "detail": observed["detail"],
                    "iota_steps": 0, "k_steps": 0},
        "native_nonempty_frames": nonempty, "cleared_nonempty_frames": cleared,
        "accepted_declarations": original["accepted_declarations"],
        "strict_self_admission": {"accepted_records": strict["accepted_records"],
                                  "declaration_records": strict["declaration_records"],
                                  "first_refusal": strict["terminal"]["name"], "line": strict["terminal"]["line"]},
        "production_decisions_credited": 0, "loader_proved": False,
    }


def verify(root=ROOT):
    """Read only the supplied archive root, using this installation's readers."""
    root = Path(root)
    result = derive(root)
    require(result == json.loads((root / REPORT / "qualification.json").read_bytes()),
            "Archived qualification differs from the independently reconciled observations")
    return result
