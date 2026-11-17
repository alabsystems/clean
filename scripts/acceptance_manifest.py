#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""The one Python reader of P6 acceptance records (unit P6, slice 1 of
docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md; design
designs/2026-11-16-p6-acceptance-identity.md, reader R12).

Two record kinds:

* a `kernel-verified.json` manifest (schema 2), written by the Rust producers
  in crates/clean-mathverse/src/verify/kernel_verified_manifest.rs;
* the JSON summary `clean mathverse stamp-verified --json` prints.

Every script that reads either goes through here. The reader refuses rather
than defaults: a schema-1 or identity-less manifest, a stamp-verified summary
that predates P6 (it reports `kernel_verified` with no `tier`), an unknown key,
a count that disagrees with its names, a discipline its profile does not
derive, and ANY reference-tier record (F12: no reference producer exists in
this build, so no Python reader accepts one, whatever it says about itself).
What it returns is development tier: data for gates and diffs, never a label
(P2 clause 1).

    python3 scripts/acceptance_manifest.py names <kernel-verified.json>
    python3 scripts/acceptance_manifest.py summary <stamp-verified.json>
    python3 scripts/acceptance_manifest.py invariance <eager.json> <lazy.json>
    python3 scripts/acceptance_manifest.py --selftest

`invariance` is the comparison of scripts/kv_invariance_gate.sh (reader R11):
exit 0 only when both manifests are valid, their accepted sets are equal, and
the sets are not both empty (identical over nothing measures nothing).
"""

from __future__ import annotations

import json
import math
import re
import sys
from pathlib import Path

SCHEMA_VERSION = 2

MANIFEST_KEYS = frozenset({
    "schema_version", "tool", "created_at", "shard_dir", "shards_loaded", "identity",
    "total_constants", "accepted", "axiom_accepted", "unsafe_accepted", "axiom_fallback",
    "failed", "cycle_skipped", "reconstruct_failed", "cache_hits", "elapsed_secs",
    "accepted_names",
})
LEGACY_ENTRIES = frozenset({
    "clean-mathverse/incremental-replay/v1",
    "clean-mathverse/parallel-readonly-replay/v1",
    "clean-mathverse/sharded-const-typecheck/v1",
})
REFERENCE_ENTRY = "clean-kernel/reference-entry/v1"
DISCIPLINES = {
    "lean": "lean-replay-order+lean-kernel-theory/1",
    "extended": "extended-prelude-incremental/1",
    "coq": "coq-cumulative-incremental/1",
}
PROFILE_KEYS = frozenset({"kernel_theory", "mode", "lean_level_profile", "cumulative",
                          "cumulative_ever", "base"})
CHECKER_KEYS = frozenset({"entry", "discipline", "imports", "settings", "build"})
SETTINGS_KEYS = frozenset({"elision", "inductive_replay", "level_repair", "heartbeat_limit",
                           "max_closure_modules"})
BUILD_KEYS = frozenset({"clean_version", "kernel_version", "toolchain", "git_sha", "exe"})
EXECUTABLE_KEYS = frozenset({"path", "size", "sha256"})


class Refused(Exception):
    """A record this reader will not read."""


def _require(cond: bool, why: str) -> None:
    if not cond:
        raise Refused(why)


def _uint(value: object, field: str, maximum: int = (1 << 64) - 1) -> None:
    _require(type(value) is int and 0 <= value <= maximum,
             f"{field} is not an unsigned integer in 0..{maximum}")


def _choice(value: object, choices: tuple[str, ...], field: str) -> None:
    _require(isinstance(value, str) and value in choices, f"unknown {field} {value!r}")


def _digest(value: object, length: int, field: str) -> None:
    _require(isinstance(value, str) and re.fullmatch(rf"[0-9a-f]{{{length}}}", value) is not None,
             f"{field} is not {length} lowercase hex digits")


def _derive_discipline(profile: dict) -> str:
    if profile["cumulative"] or profile["cumulative_ever"]:
        return DISCIPLINES["coq"]
    if profile["base"]["variant"] == "lean-replay" and profile["kernel_theory"] != "Extended":
        return DISCIPLINES["lean"]
    return DISCIPLINES["extended"]


def validate_identity(identity: object) -> dict:
    """Refuse an identity record that is absent, malformed or not development."""
    _require(isinstance(identity, dict), "no `identity`: the manifest names no theory and no checker")
    _require(set(identity) == {"theory", "checker", "tier"},
             f"identity keys {sorted(identity)} are not theory/checker/tier")
    theory, checker = identity["theory"], identity["checker"]
    _require(isinstance(theory, dict) and len(theory) == 1, "theory is not a one-arm record")
    _require(isinstance(checker, dict), "checker is not a record")
    if "reference" in theory or identity["tier"] == "reference" or checker.get("entry") == REFERENCE_ENTRY:
        raise Refused("reference-tier record: no reference producer exists in this build, so no "
                      "reader accepts one (P6 slice 1b lands the producer and its reader together)")
    _require(identity["tier"] == "development", f"unknown tier {identity['tier']!r}")
    profile = theory.get("profile")
    _require(isinstance(profile, dict) and set(profile) == PROFILE_KEYS,
             "theory is not a legacy profile with exactly its fields")
    _require(isinstance(profile["base"], dict) and set(profile["base"]) == {"variant", "constants", "content_sha256"},
             "profile base is malformed")
    # Mirror the Rust identity's closed enums and serde field types before
    # deriving a discipline. These are development report records, not proofs.
    _choice(profile["kernel_theory"], ("Extended", "Lean", "LeanReference"), "kernel theory")
    for field in ("mode", "lean_level_profile"):
        _require(isinstance(profile[field], str), f"profile {field} is not a string")
    for field in ("cumulative", "cumulative_ever"):
        _require(type(profile[field]) is bool, f"profile {field} is not a boolean")
    _choice(profile["base"]["variant"],
            ("lean-replay", "import-prelude", "prelude", "upstream-library"), "base variant")
    _uint(profile["base"]["constants"], "base constants")
    _digest(profile["base"]["content_sha256"], 64, "base content_sha256")
    _require(isinstance(checker, dict) and set(checker) == CHECKER_KEYS, "checker keys are not entry/discipline/imports/settings/build")
    _require(isinstance(checker["entry"], str) and checker["entry"] in LEGACY_ENTRIES,
             f"unknown checker entry {checker['entry']!r}")
    _require(checker["imports"] in ("trusted", "replayed"), f"unknown imports {checker['imports']!r}")
    _require(isinstance(checker["settings"], dict) and set(checker["settings"]) == SETTINGS_KEYS,
             "checker settings are malformed")
    settings = checker["settings"]
    _choice(settings["elision"], ("none", "opaque", "opaque-and-theorem"), "elision")
    _choice(settings["inductive_replay"],
            ("generate", "lean-faithful", "olean-loader"), "inductive replay")
    _require(type(settings["level_repair"]) is bool, "level_repair is not a boolean")
    if settings["heartbeat_limit"] is not None:
        _uint(settings["heartbeat_limit"], "heartbeat_limit", (1 << 32) - 1)
    if settings["max_closure_modules"] is not None:
        _uint(settings["max_closure_modules"], "max_closure_modules")
    derived = _derive_discipline(profile)
    _require(checker["discipline"] == derived,
             f"stored discipline {checker['discipline']!r} is not {derived!r}, the one its profile derives")
    if checker["entry"] == "clean-mathverse/sharded-const-typecheck/v1":
        _require(checker["imports"] == "trusted", "the sharded entry trusts its imports; `replayed` is forged")
    build = checker["build"]
    _require(isinstance(build, dict) and set(build) == BUILD_KEYS, "build fields are malformed")
    for field in ("clean_version", "kernel_version", "toolchain"):
        _require(isinstance(build[field], str), f"build {field} is not a string")
    if build["git_sha"] is not None:
        _digest(build["git_sha"], 40, "build git_sha")
    exe = build["exe"]
    _require(isinstance(exe, dict) and set(exe) == EXECUTABLE_KEYS, "executable fields are malformed")
    _require(isinstance(exe["path"], str), "executable path is not a string")
    _uint(exe["size"], "executable size")
    _digest(exe["sha256"], 64, "build exe sha256")
    return identity


def validate_manifest(data: object) -> dict:
    """Return a validated development manifest, or raise Refused."""
    _require(isinstance(data, dict), "manifest is not a JSON object")
    found = data.get("schema_version", "absent")
    _require(type(found) is int and found == SCHEMA_VERSION,
             f"schema_version {found} names no theory and no checker; under P6 it is not evidence "
             "(re-run its producer; for a Coq baseline, scripts/coq_refresh.sh --rebaseline)")
    validate_identity(data.get("identity"))
    extra, missing = set(data) - MANIFEST_KEYS, MANIFEST_KEYS - set(data)
    _require(not extra and not missing, f"manifest keys: unknown {sorted(extra)}, missing {sorted(missing)}")
    for field in ("tool", "created_at", "shard_dir"):
        _require(isinstance(data[field], str), f"manifest {field} is not a string")
    for field in ("shards_loaded", "total_constants", "accepted", "axiom_accepted",
                  "unsafe_accepted", "axiom_fallback", "failed", "cycle_skipped",
                  "reconstruct_failed", "cache_hits"):
        _uint(data[field], field)
    elapsed = data["elapsed_secs"]
    _require(type(elapsed) in (int, float) and abs(elapsed) <= sys.float_info.max
             and math.isfinite(elapsed), "elapsed_secs is not a finite number")
    names = data["accepted_names"]
    _require(isinstance(names, list) and all(isinstance(n, str) for n in names), "accepted_names is not a list of names")
    _require(type(data["accepted"]) is int and data["accepted"] == len(names) == len(set(names)),
             f"accepted count {data['accepted']} does not match the {len(set(names))} distinct accepted names")
    return data


def read_manifest(path: str | Path) -> dict:
    """Read and validate a `kernel-verified.json`."""
    try:
        data = json.loads(Path(path).read_text())
    except (OSError, ValueError) as error:
        raise Refused(f"{path}: {error}") from error
    try:
        return validate_manifest(data)
    except Refused as error:
        raise Refused(f"{path}: {error}") from error


def accepted_names(path: str | Path) -> set[str]:
    """The development-accepted names of a validated manifest (data, never a label)."""
    return set(read_manifest(path)["accepted_names"])


# Checker settings that cannot change which names are accepted (they can only
# turn an acceptance into a refusal), left out of `checker_key`.
NON_ACCEPTING_SETTINGS = ("heartbeat_limit", "max_closure_modules")


def checker_key(identity: dict) -> str:
    """The `same_checker` comparison of the Rust reader: the identity without
    the build and the settings that accept no name (theory, entry, discipline,
    imports, elision, inductive replay, level repair)."""
    checker = dict(identity["checker"])
    checker.pop("build")
    settings = {k: v for k, v in checker.pop("settings").items() if k not in NON_ACCEPTING_SETTINGS}
    return json.dumps({"theory": identity["theory"], "checker": checker, "settings": settings},
                      sort_keys=True)


def invariance(eager: str | Path, lazy: str | Path) -> str:
    """Compare an eager and a lazy run's accepted sets; return the verdict line
    or raise Refused (a refused manifest, two checkers, two empty sets, or any
    divergence)."""
    eager_m, lazy_m = read_manifest(eager), read_manifest(lazy)
    _require(checker_key(eager_m["identity"]) == checker_key(lazy_m["identity"]),
             "the eager and lazy manifests name different checkers (theory, entry, discipline, "
             "imports or accepting settings); their sets are not comparable")
    e, l = set(eager_m["accepted_names"]), set(lazy_m["accepted_names"])
    _require(bool(e or l), "both accepted sets are empty; an eager-vs-lazy comparison over "
             "nothing measures nothing")
    only_e, only_l = sorted(e - l), sorted(l - e)
    if only_e or only_l:
        lines = [f"DIVERGENCE: eager-only={len(only_e)} lazy-only={len(only_l)} "
                 f"(eager={len(e)} lazy={len(l)})"]
        lines += [f"  eager-only: {n}" for n in only_e[:10]]
        lines += [f"  lazy-only: {n}" for n in only_l[:10]]
        raise Refused("\n".join(lines))
    return f"OK: accepted set IDENTICAL eager-vs-lazy ({len(e)} names, development tier)"


def validate_summary(data: object) -> dict:
    """Return a validated post-P6 stamp-verified summary, or raise Refused."""
    _require(isinstance(data, dict), "summary is not a JSON object")
    _require("tier" in data,
             "a stamp-verified summary without `tier` predates P6: its `kernel_verified` and "
             "`stored_kernel_verified` were a development count and stamps; re-run stamp-verified")
    if data["tier"] == "reference":
        raise Refused("reference-tier summary: no reference producer exists in this build")
    _require(data["tier"] == "development", f"unknown tier {data['tier']!r}")
    for key in ("accepted", "stored_reference_stamped", "total"):
        _uint(data.get(key), f"summary {key}")
    _require("kernel_verified" not in data, "hybrid summary: `kernel_verified` beside `tier`")
    return data


def read_summary(path: str | Path) -> dict:
    """Read and validate a stamp-verified JSON summary."""
    try:
        data = json.loads(Path(path).read_text())
    except (OSError, ValueError) as error:
        raise Refused(f"{path}: {error}") from error
    try:
        return validate_summary(data)
    except Refused as error:
        raise Refused(f"{path}: {error}") from error


# ---------------------------------------------------------------------------
# Self-test: every refusal fires on its fixture, and a valid record passes.
# ---------------------------------------------------------------------------

def _valid_manifest() -> dict:
    return {
        "schema_version": 2, "tool": "t", "created_at": "0", "shard_dir": "d", "shards_loaded": 1,
        "identity": {
            "theory": {"profile": {
                "kernel_theory": "Lean", "mode": "Strict", "lean_level_profile": "Lean",
                "cumulative": False, "cumulative_ever": False,
                "base": {"variant": "lean-replay", "constants": 3, "content_sha256": "a" * 64}}},
            "checker": {
                "entry": "clean-mathverse/sharded-const-typecheck/v1",
                "discipline": DISCIPLINES["lean"], "imports": "trusted",
                "settings": {"elision": "none", "inductive_replay": "olean-loader", "level_repair": False,
                             "heartbeat_limit": None, "max_closure_modules": None},
                "build": {"clean_version": "0", "kernel_version": "0", "toolchain": "t", "git_sha": None,
                          "exe": {"path": "/x", "size": 1, "sha256": "b" * 64}}},
            "tier": "development"},
        "total_constants": 2, "accepted": 2, "axiom_accepted": 0, "unsafe_accepted": 0,
        "axiom_fallback": 0, "failed": 0, "cycle_skipped": 0, "reconstruct_failed": 0,
        "cache_hits": 0, "elapsed_secs": 0.0, "accepted_names": ["a", "b"],
    }


def selftest() -> int:
    import copy

    def mutated(edit) -> dict:
        data = copy.deepcopy(_valid_manifest())
        edit(data)
        return data

    validate_manifest(_valid_manifest())
    cases = {
        "schema 1": mutated(lambda d: d.update(schema_version=1)),
        "absent schema": mutated(lambda d: d.pop("schema_version")),
        "fractional schema": mutated(lambda d: d.update(schema_version=2.0)),
        "nonstring tool": mutated(lambda d: d.update(tool=1)),
        "negative total": mutated(lambda d: d.update(total_constants=-1)),
        "boolean failure count": mutated(lambda d: d.update(failed=True)),
        "overflow cache count": mutated(lambda d: d.update(cache_hits=1 << 64)),
        "nonfinite elapsed": mutated(lambda d: d.update(elapsed_secs=float("inf"))),
        "no identity": mutated(lambda d: d.pop("identity")),
        "reference theory": mutated(lambda d: d["identity"].update(theory={"reference": {"id": "x", "digest": "y"}})),
        "reference tier": mutated(lambda d: d["identity"].update(tier="reference")),
        "reference entry": mutated(lambda d: d["identity"]["checker"].update(entry=REFERENCE_ENTRY)),
        "unknown entry": mutated(lambda d: d["identity"]["checker"].update(entry="other/v1")),
        "unknown kernel theory": mutated(lambda d: d["identity"]["theory"]["profile"].update(kernel_theory="UnregisteredTheory")),
        "unknown base variant": mutated(lambda d: d["identity"]["theory"]["profile"]["base"].update(variant="invented")),
        "nonboolean cumulative": mutated(lambda d: d["identity"]["theory"]["profile"].update(cumulative=0)),
        "nonstring profile": mutated(lambda d: d["identity"]["theory"]["profile"].update(mode=1)),
        "negative base count": mutated(lambda d: d["identity"]["theory"]["profile"]["base"].update(constants=-1)),
        "unknown elision": mutated(lambda d: d["identity"]["checker"]["settings"].update(elision="invented")),
        "unknown replay": mutated(lambda d: d["identity"]["checker"]["settings"].update(inductive_replay="invented")),
        "nonboolean repair": mutated(lambda d: d["identity"]["checker"]["settings"].update(level_repair=0)),
        "overflow heartbeat": mutated(lambda d: d["identity"]["checker"]["settings"].update(heartbeat_limit=1 << 32)),
        "boolean closure limit": mutated(lambda d: d["identity"]["checker"]["settings"].update(max_closure_modules=True)),
        "unknown build field": mutated(lambda d: d["identity"]["checker"]["build"].update(unrecognized=True)),
        "bad git digest": mutated(lambda d: d["identity"]["checker"]["build"].update(git_sha="not-a-commit")),
        "unknown executable field": mutated(lambda d: d["identity"]["checker"]["build"]["exe"].update(unrecognized=True)),
        "nonstring executable path": mutated(lambda d: d["identity"]["checker"]["build"]["exe"].update(path=1)),
        "negative executable size": mutated(lambda d: d["identity"]["checker"]["build"]["exe"].update(size=-1)),
        "discipline mismatch": mutated(lambda d: d["identity"]["checker"].update(discipline=DISCIPLINES["extended"])),
        "sharded replayed": mutated(lambda d: d["identity"]["checker"].update(imports="replayed")),
        "count mismatch": mutated(lambda d: d.update(accepted=3)),
        "duplicate name": mutated(lambda d: d.update(accepted_names=["a", "a"])),
        "hybrid names": mutated(lambda d: d.update(kernel_verified_names=["a"])),
        "bad digest": mutated(lambda d: d["identity"]["theory"]["profile"]["base"].update(content_sha256="zz")),
    }
    failures = []
    for label, data in cases.items():
        try:
            validate_manifest(data)
            failures.append(f"manifest {label}: accepted")
        except Refused:
            pass
    for label, data in {
        "checker not a record": mutated(lambda d: d["identity"].update(checker=["x"])),
        "boolean count": mutated(lambda d: d.update(accepted_names=["a"], accepted=True)),
    }.items():
        cases[label] = data
        try:
            validate_manifest(data)
            failures.append(f"manifest {label}: accepted")
        except Refused:
            pass
    failures += _invariance_selftest(mutated)
    validate_summary({"tier": "development", "accepted": 1, "stored_reference_stamped": 0, "total": 2})
    for label, data in {
        "pre-P6 summary": {"kernel_verified": 1, "stored_kernel_verified": 1, "total": 2},
        "reference summary": {"tier": "reference", "accepted": 1, "stored_reference_stamped": 1, "total": 2},
        "boolean summary count": {"tier": "development", "accepted": True, "stored_reference_stamped": 0, "total": 2},
        "negative summary count": {"tier": "development", "accepted": 1, "stored_reference_stamped": 0, "total": -1},
        "hybrid summary": {"tier": "development", "accepted": 1, "stored_reference_stamped": 0, "total": 2,
                           "kernel_verified": 1},
    }.items():
        try:
            validate_summary(data)
            failures.append(f"summary {label}: accepted")
        except Refused:
            pass
    for failure in failures:
        print(f"acceptance_manifest selftest: FAILED: {failure}", file=sys.stderr)
    print(f"acceptance_manifest selftest: {len(cases) + 5 + 4} refusals, {len(failures)} failures")
    return 1 if failures else 0


def _invariance_selftest(mutated) -> list[str]:
    """The R11 comparison: equal non-empty sets pass; two empty sets, a
    divergence and a schema-1 side are each refused."""
    import tempfile

    failures = []
    with tempfile.TemporaryDirectory() as tmp:
        def write(name: str, data: dict) -> Path:
            path = Path(tmp) / name
            path.write_text(json.dumps(data))
            return path

        full = write("full.json", _valid_manifest())
        empty = write("empty.json", mutated(lambda d: d.update(accepted_names=[], accepted=0)))
        fewer = write("fewer.json", mutated(lambda d: d.update(accepted_names=["a"], accepted=1)))
        old = write("old.json", {"schema_version": 1, "kernel_verified_names": ["a", "b"]})
        other = write("other.json", mutated(lambda d: d["identity"]["checker"]["settings"].update(elision="opaque")))
        try:
            invariance(full, full)
        except Refused as error:
            failures.append(f"invariance equal sets: refused ({error})")
        for label, (eager, lazy) in {
            "both empty": (empty, empty),
            "divergence": (full, fewer),
            "schema-1 side": (full, old),
            "different checkers": (full, other),
        }.items():
            try:
                invariance(eager, lazy)
                failures.append(f"invariance {label}: accepted")
            except Refused:
                pass
    return failures


def main(argv: list[str]) -> int:
    if argv[1:] == ["--selftest"]:
        return selftest()
    if argv[1:2] == ["invariance"] and len(argv) == 4:
        try:
            print(invariance(argv[2], argv[3]))
        except Refused as error:
            print(f"REFUSED: {error}")
            return 1
        return 0
    if len(argv) != 3 or argv[1] not in ("names", "summary"):
        print(__doc__, file=sys.stderr)
        return 2
    try:
        if argv[1] == "names":
            for name in sorted(accepted_names(argv[2])):
                print(name)
        else:
            print(json.dumps(read_summary(argv[2]), sort_keys=True))
    except Refused as error:
        print(f"acceptance_manifest: refused: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
