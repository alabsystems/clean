#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""G-SPINE-SET: derive data/spine_set.json from a trust-host whole-crate dump.

WHY THIS EXISTS
---------------
The spine & lattice program (designs/2026-08-22-spine-and-lattice-program.md,
Track G, job G-SPINE-SET; decision §3.1) retires the substring family selectors
(`infer_type` 1/26, `is_def_eq` 0/22, `whnf` 1/97 — recon §2): Claim S
quantifies over a COMMITTED artifact, `data/spine_set.json` — the measured
reachable call closure of `Environment::add_decl` in the deployed release
kernel — never over substring matches, module globs, or prose.

The measurement half runs on a trust host (the whole-crate `clean_kernel`
coverage/dump producer, laneTU pattern — see the `inputs.dump_O3` paths in
data/crystal_frontier_census_2026-08-22.json). This script is the clean-side
derivation half: it consumes that dump artifact — the SAME def-path vocabulary
the committed censuses carry (`env::decl_add::<impl env::Environment>::…`,
`<tc::expr_location::ExprPathStep as std::clone::Clone>::clone`,
`…::{closure#0}`) — and emits the spine set with provenance, family tags, wall
tags, mode-reachability annotations, and the edge policy IN the file.

FAIL-CLOSED CONTRACT
--------------------
A coverage-only dump (bodies without per-body call edges) CANNOT derive a spine
set. This script never emits a partial artifact: any missing field aborts with
a message naming exactly which field and which trust-host production step is
missing. `--describe` prints the full producer contract.

Usage:
    scripts/spine_set.py --describe
    scripts/spine_set.py --self-test
    scripts/spine_set.py --dump <dump.json> --driver-digest <sha256> \
        [--boundary <boundary.json>] [--out data/spine_set.json]
"""

from __future__ import annotations

import argparse
import contextlib
import copy
import datetime as _dt
import io
import json
import re
import sys
import tempfile
from collections import OrderedDict, deque
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SCHEMA = "clean.spine_set/v1"
WALL_MAP_VERSION = "v1"
DEFAULT_OUT = "data/spine_set.json"
FIXTURE = REPO_ROOT / "tests" / "fixtures" / "spine_set" / "synthetic_dump.json"

EDGE_KINDS = ("static", "closure", "dyn-trait", "fn-pointer")

# Root spec: the deployed entry point env/decl_add.rs `pub fn add_decl`
# (recon §2: entry env/decl_add.rs:613). Matches both def-path spellings the
# census vocabulary uses for inherent Environment methods.
ROOT_SPEC = (
    "final top-level path segment == 'add_decl' AND the def_path names "
    "env::Environment (covers 'env::decl_add::<impl env::Environment>::add_decl' "
    "and 'env::Environment::add_decl'; does NOT match add_decl_if_absent / "
    "add_decl_structural / nested closures)"
)

# Family partition (program §2 G-SPINE-SET): root-module partition on the
# defining module's first two path segments. tc::whnf_proj is folded into
# tc::whnf (it is the projection half of the whnf surface — recon §2 lists its
# stack_safe sites with whnf's); everything else is 'other' with module_path
# preserved per member so a later re-partition needs no re-dump.
FAMILY_PARTITION = {
    ("env", "decl_add"): "env::decl_add",
    ("tc", "infer"): "tc::infer",
    ("tc", "infer_proj"): "tc::infer_proj",
    ("tc", "def_eq"): "tc::def_eq",
    ("tc", "whnf"): "tc::whnf",
    ("tc", "whnf_proj"): "tc::whnf",
    ("tc", "reduction"): "tc::reduction",
}
FAMILIES = (
    "env::decl_add",
    "tc::infer",
    "tc::infer_proj",
    "tc::def_eq",
    "tc::whnf",
    "tc::reduction",
    "other",
)

# Conservative producer-class -> wall-tag map (navigation, not verdict).
# Aggregator classes (Borrow, Call — recon §2 / program §1 entry state:
# "occurrence counts != unblocked bodies") map to their dominant wall; each
# Track-T wall job opens with a leaf-cause census that refines this. Unmapped
# classes are preserved as 'unmapped:<Class>' — visible, never dropped.
CLASS_TO_WALL = {
    # aggregators
    "Borrow": "T-HEAP",
    "Call": "T-REC",
    # recursive ADT / layout (hostile shape 2)
    "Adt": "T-ADT",
    "RecursiveAdt": "T-ADT",
    "Ty(recursive adt)": "T-ADT",
    # heap / pointer (hostile shape 6)
    "Deref": "T-HEAP",
    "Box": "T-HEAP",
    "Arc": "T-HEAP",
    "Rc": "T-HEAP",
    "RawPtr": "T-HEAP",
    "PtrIdentity": "T-HEAP",
    # control / shape (hostile shape 5 + T-CTRL classes)
    "If": "T-CTRL",
    "Let": "T-CTRL",
    "LetElse": "T-CTRL",
    "Match": "T-CTRL",
    "EnumMatch": "T-CTRL",
    "Try": "T-CTRL",
    "Loop": "T-CTRL",
    "Closure": "T-CTRL",
    "RefCell": "T-CTRL",
    # caches (hostile shape 4)
    "Hash": "T-HASH",
    "HashMap": "T-HASH",
    "Cache": "T-HASH",
    # stack switching (hostile shape 3; adopted route program §3.3)
    "StackSafe": "K-STACK",
    "Psm": "K-STACK",
    # interior mutability / TLS (hostile shape 8; program K-TLS)
    "Cell": "K-TLS",
    "ThreadLocal": "K-TLS",
}

# Modules whose bodies are extension-mode-only by construction (mode heuristic;
# only used when the dump records no per-body mode_gate). Conservative: this
# ANNOTATES, it never prunes membership.
EXTENSION_ONLY_MODULES = {
    ("tc", "infer_cubical"): "CleanMode cubical layer",
    ("tc", "infer_zfc"): "CleanMode set-theoretic layer",
}

_SNAKE_RE = re.compile(r"^[a-z_][a-z0-9_]*$")
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class SpineSetError(Exception):
    """Fail-closed derivation error; the message names the missing thing."""


# --------------------------------------------------------------------------
# def-path parsing (the census vocabulary)
# --------------------------------------------------------------------------


def split_top(path: str) -> list[str]:
    """Split a def path on top-level `::`, respecting <...> nesting and `->`."""
    segs: list[str] = []
    cur: list[str] = []
    depth = 0
    i = 0
    n = len(path)
    while i < n:
        c = path[i]
        if c == "<":
            depth += 1
            cur.append(c)
        elif c == ">":
            if i > 0 and path[i - 1] == "-":
                cur.append(c)  # return-arrow '->', not a bracket close
            else:
                depth -= 1
                cur.append(c)
        elif c == ":" and depth == 0 and i + 1 < n and path[i + 1] == ":":
            segs.append("".join(cur))
            cur = []
            i += 1
        else:
            cur.append(c)
        i += 1
    if cur:
        segs.append("".join(cur))
    return [s for s in segs if s != ""]


def _split_top_as(s: str) -> list[str]:
    """Split `A as B` at the first top-level ` as `."""
    depth = 0
    i = 0
    while i < len(s) - 3:
        c = s[i]
        if c == "<":
            depth += 1
        elif c == ">" and (i == 0 or s[i - 1] != "-"):
            depth -= 1
        elif depth == 0 and s[i : i + 4] == " as ":
            return [s[:i], s[i + 4 :]]
        i += 1
    return [s]


def module_segments(def_path: str) -> list[str]:
    """The defining module's path segments (leading snake_case run).

    `<tc::whnf::WhnfCache as std::default::Default>::default` -> [tc, whnf];
    `env::decl_add::<impl env::Environment>::add_decl` -> [env, decl_add];
    `env::Environment::set_cumulative` -> [env].
    """
    segs = split_top(def_path.strip())
    if not segs:
        return []
    head = segs[0]
    if head.startswith("<") and head.endswith(">"):
        inner = head[1:-1].strip()
        for prefix in ("dyn ", "impl "):
            if inner.startswith(prefix):
                inner = inner[len(prefix) :]
        return module_segments(_split_top_as(inner)[0].strip())
    out: list[str] = []
    for seg in segs:
        if _SNAKE_RE.match(seg):
            out.append(seg)
        else:
            break
    return out


def family_of(def_path: str) -> tuple[str, str]:
    """(family, module_path) for a def path, per FAMILY_PARTITION."""
    mods = module_segments(def_path)
    fam = FAMILY_PARTITION.get(tuple(mods[:2]), "other")
    return fam, "::".join(mods)


def is_root(def_path: str) -> bool:
    segs = split_top(def_path)
    return bool(segs) and segs[-1] == "add_decl" and "env::Environment" in def_path


# --------------------------------------------------------------------------
# dump validation (fail closed, naming the missing production step)
# --------------------------------------------------------------------------

DESCRIBE = """\
G-SPINE-SET dump-producer contract (consumed by scripts/spine_set.py)
=====================================================================
The dump is the whole-crate `clean_kernel` coverage/dump artifact produced on
the trust host (laneTU pattern; cf. inputs.dump_O3 in
data/crystal_frontier_census_2026-08-22.json), POST-a5aae3bde, from the
RELEASE (-O3) build, as ONE JSON document with:

  schema        str    producer schema id (recorded verbatim into spine_set)
  provenance    obj    REQUIRED keys:
                         driver_dylib_sha256  (64-hex; must equal --driver-digest)
                         clean_rev            (the clean rev the dump measured)
                         measured_utc
                       recorded if present: trust_rev, lane, sysroot, guard
  bodies        list   one record per monomorphic body ('enumerate-bodies'):
                         def_path   str   census def-path vocabulary
                         calls      list  THE CALL-GRAPH FIELD ('emit-call-graph'):
                                          every outgoing call edge, each with
                                            callee  str  callee def_path (or
                                                         descriptor for dyn/fn-ptr)
                                            kind    str  static | closure |
                                                         dyn-trait | fn-pointer
                                            via     str  how the edge was found
                                                         (e.g. thir::ExprKind::Call,
                                                         mir::TerminatorKind::Call)
                         producer   obj   'emit-producer-classes': at least
                                            classes  list[str]  leaf/refusal
                                                     classes ([] if clean)
                       optional per body:
                         debug_only bool  cfg-gated debug twin (excluded + listed)
                         mode_gate  str   producer-recorded mode reachability
                         walls      list  explicit wall tags (augment the map)
  dyn_impl_table obj   optional: dyn/fn-ptr callee descriptor -> ALL impl
                       def_paths (conservative enumeration). Absent => every
                       dyn/fn-ptr edge is emitted as a named exclusion
                       (assumption-ledger candidate, program §3.6).

Duplicate def_paths must be disambiguated by the producer (def_index-qualified
paths); ambiguous call-graph resolution is refused.

A dump missing 'bodies' fails the 'enumerate-bodies' step; bodies missing
'calls' fail the 'emit-call-graph' step; bodies missing 'producer.classes'
fail the 'emit-producer-classes' step; a missing/incomplete 'provenance'
block fails the 'emit-provenance' step. This script NEVER emits a partial
spine_set on any of these.

Clean-side invocation once the dump exists:
  scripts/spine_set.py --dump <dump.json> --driver-digest <dylib sha256> \\
      [--boundary <boundary.json>] --out data/spine_set.json
"""


def _validate_dump(dump: object, driver_digest: str) -> dict:
    if not isinstance(dump, dict):
        raise SpineSetError("dump is not a JSON object — not a whole-crate dump artifact")
    if "schema" not in dump:
        raise SpineSetError("dump lacks 'schema' — the producer did not stamp its schema id")
    prov = dump.get("provenance")
    if not isinstance(prov, dict):
        raise SpineSetError(
            "dump lacks the 'provenance' block — the trust-host production step "
            "'emit-provenance' is missing (driver_dylib_sha256, clean_rev, measured_utc)"
        )
    for key in ("driver_dylib_sha256", "clean_rev", "measured_utc"):
        if not prov.get(key):
            raise SpineSetError(
                f"dump provenance lacks '{key}' — the 'emit-provenance' step is incomplete"
            )
    if prov["driver_dylib_sha256"] != driver_digest:
        raise SpineSetError(
            "driver digest mismatch: --driver-digest "
            f"{driver_digest} != dump provenance driver_dylib_sha256 "
            f"{prov['driver_dylib_sha256']} — refusing to attribute this dump to that driver"
        )
    bodies = dump.get("bodies")
    if not isinstance(bodies, list) or not bodies:
        raise SpineSetError(
            "dump has no 'bodies' field (or it is empty) — the trust-host production "
            "step 'enumerate-bodies' (whole-crate body enumeration) is missing"
        )
    if not any(isinstance(b, dict) and "calls" in b for b in bodies):
        raise SpineSetError(
            "dump carries no per-body 'calls' field — the call-graph production step "
            "'emit-call-graph' (record every outgoing call edge per body with "
            "callee/kind/via) has not run; a coverage-only dump cannot derive a "
            "spine set. Run scripts/spine_set.py --describe for the contract."
        )
    seen: set[str] = set()
    for body in bodies:
        if not isinstance(body, dict) or not body.get("def_path"):
            raise SpineSetError("a dump body record lacks 'def_path' — 'enumerate-bodies' is malformed")
        dp = body["def_path"]
        if dp in seen:
            raise SpineSetError(
                f"duplicate def_path in dump bodies: {dp!r} — the producer must "
                "disambiguate (def_index-qualified def paths); call-graph resolution "
                "by def_path is ambiguous"
            )
        seen.add(dp)
        if "calls" not in body or not isinstance(body["calls"], list):
            raise SpineSetError(
                f"dump body {dp!r} lacks the 'calls' call-graph field — the "
                "'emit-call-graph' step did not cover this body"
            )
        for edge in body["calls"]:
            if not isinstance(edge, dict) or not edge.get("callee"):
                raise SpineSetError(f"an edge of {dp!r} lacks 'callee' — 'emit-call-graph' is malformed")
            if edge.get("kind") not in EDGE_KINDS:
                raise SpineSetError(
                    f"edge {dp!r} -> {edge.get('callee')!r} has kind "
                    f"{edge.get('kind')!r}; the 'emit-call-graph' step must classify "
                    f"every edge as one of {EDGE_KINDS}"
                )
            if not edge.get("via"):
                raise SpineSetError(
                    f"edge {dp!r} -> {edge['callee']!r} lacks 'via' (how the edge was "
                    "found) — required per member by G-SPINE-SET"
                )
        producer = body.get("producer")
        if not isinstance(producer, dict) or not isinstance(producer.get("classes"), list):
            raise SpineSetError(
                f"dump body {dp!r} lacks 'producer.classes' — the "
                "'emit-producer-classes' step (per-body leaf/refusal classes; [] if "
                "clean) has not run; wall tags cannot be derived"
            )
    return dump


def _validate_boundary(boundary: object) -> list[dict]:
    if boundary is None:
        return []
    if not isinstance(boundary, list):
        raise SpineSetError("boundary file must be a JSON list of cut rules")
    for row in boundary:
        if not isinstance(row, dict) or not row.get("def_path"):
            raise SpineSetError("a boundary rule lacks 'def_path'")
        if not row.get("ledger_ref"):
            raise SpineSetError(
                f"boundary rule for {row.get('def_path')!r} lacks 'ledger_ref' — a "
                "contract-boundary cut is admissible ONLY via an assumption-ledger "
                "entry (program §3.6)"
            )
        if not row.get("reason"):
            raise SpineSetError(f"boundary rule for {row['def_path']!r} lacks 'reason'")
    return boundary


# --------------------------------------------------------------------------
# derivation
# --------------------------------------------------------------------------


def _wall_tags(body: dict) -> tuple[list[str], list[str]]:
    classes = list(body["producer"]["classes"])
    tags = set(body.get("walls", []))
    for cls in classes:
        tags.add(CLASS_TO_WALL.get(cls, f"unmapped:{cls}"))
    return sorted(tags), classes


def _mode_annotation(body: dict) -> dict:
    gate = body.get("mode_gate")
    if gate:
        return {"annotation": str(gate), "source": "dump"}
    key = tuple(module_segments(body["def_path"])[:2])
    if key in EXTENSION_ONLY_MODULES:
        return {
            "annotation": f"extension-only ({EXTENSION_ONLY_MODULES[key]}; module heuristic)",
            "source": "heuristic",
        }
    return {
        "annotation": "constructive:assumed-reachable (conservative default — no gate recorded)",
        "source": "default",
    }


def build_spine_set(
    dump: dict,
    driver_digest: str,
    dump_path: str,
    boundary: list[dict] | None = None,
    now_utc: str | None = None,
) -> dict:
    """Derive the spine set (the reachable call closure of Environment::add_decl)."""
    if not _SHA256_RE.match(driver_digest or ""):
        raise SpineSetError(
            "--driver-digest must be the driver dylib's sha256 (64 lowercase hex) — "
            f"got {driver_digest!r}"
        )
    dump = _validate_dump(dump, driver_digest)
    boundary = _validate_boundary(boundary)
    bodies = {b["def_path"]: b for b in dump["bodies"]}
    dyn_table = dump.get("dyn_impl_table") or {}
    boundary_by_path = {row["def_path"]: row for row in boundary}

    roots = sorted(dp for dp in bodies if is_root(dp))
    if not roots:
        raise SpineSetError(
            f"no dump body matches the root spec ({ROOT_SPEC}) — cannot anchor the "
            "closure; the dump does not cover Environment::add_decl"
        )
    for r in roots:
        if bodies[r].get("debug_only"):
            raise SpineSetError(f"root {r!r} is flagged debug_only — the spine root must be a release body")

    members: OrderedDict[str, dict] = OrderedDict()
    found_via: dict[str, dict] = {r: {"kind": "root"} for r in roots}
    edge_exclusions: list[dict] = []
    dyn_expansions: list[dict] = []
    external: dict[str, dict] = {}
    debug_twins: dict[str, str] = {}
    boundary_cuts: list[dict] = []

    queue: deque[str] = deque(roots)
    enqueued = set(roots)

    def consider(caller: str, callee: str, kind: str, via: str) -> str:
        """Route one resolvable callee def_path; returns the edge disposition."""
        body = bodies.get(callee)
        if body is None:
            slot = external.setdefault(callee, {"callee": callee, "callers": []})
            if caller not in slot["callers"]:
                slot["callers"].append(caller)
            return "external-not-followed"
        if body.get("debug_only"):
            debug_twins.setdefault(callee, caller)
            return "debug-twin-excluded"
        if callee not in enqueued:
            enqueued.add(callee)
            found_via[callee] = {"caller": caller, "kind": kind, "via": via}
            queue.append(callee)
        return "followed"

    while queue:
        dp = queue.popleft()
        body = bodies[dp]
        cut_rule = boundary_by_path.get(dp)
        wall_tags, classes = _wall_tags(body)
        member = {
            "def_path": dp,
            "family": family_of(dp)[0],
            "module_path": family_of(dp)[1],
            "wall_tags": wall_tags,
            "producer_classes": classes,
            "mode_reachability": _mode_annotation(body),
            "boundary_cut": bool(cut_rule),
            "found_via": found_via[dp],
            "calls": [],
        }
        if cut_rule:
            boundary_cuts.append(
                {
                    "def_path": dp,
                    "reason": cut_rule["reason"],
                    "ledger_ref": cut_rule["ledger_ref"],
                    "edges_not_followed": len(body["calls"]),
                }
            )
        for edge in body["calls"]:
            callee, kind, via = edge["callee"], edge["kind"], edge["via"]
            if cut_rule:
                disposition = "boundary-cut-not-followed"
            elif kind in ("static", "closure"):
                disposition = consider(dp, callee, kind, via)
            else:  # dyn-trait / fn-pointer
                impls = dyn_table.get(callee)
                if impls:
                    followed = [i for i in impls if consider(dp, i, kind, via) == "followed"]
                    missing = [i for i in impls if i not in bodies]
                    dyn_expansions.append(
                        {
                            "caller": dp,
                            "callee_descriptor": callee,
                            "kind": kind,
                            "impls_followed": followed,
                            "impls_outside_dump": missing,
                        }
                    )
                    disposition = f"impl-expanded({len(impls)} impls)"
                else:
                    edge_exclusions.append(
                        {
                            "caller": dp,
                            "callee_descriptor": callee,
                            "kind": kind,
                            "via": via,
                            "note": "not followed — no dyn_impl_table entry; ledger "
                            "candidate for data/spine_assumption_ledger.json (§3.6)",
                        }
                    )
                    disposition = "excluded-ledger-candidate"
            member["calls"].append(
                {"callee": callee, "kind": kind, "via": via, "disposition": disposition}
            )
        members[dp] = member

    member_list = [members[dp] for dp in sorted(members)]
    family_counts = {fam: 0 for fam in FAMILIES}
    for m in member_list:
        family_counts[m["family"]] += 1

    prov = dump["provenance"]
    out = {
        "schema": SCHEMA,
        "provenance": {
            "dump_path": dump_path,
            "dump_schema": dump.get("schema"),
            "dump_measured_utc": prov["measured_utc"],
            "driver_dylib_sha256": driver_digest,
            "trust_rev": prov.get("trust_rev"),
            "clean_rev": prov["clean_rev"],
            "date": now_utc or _dt.datetime.now(_dt.UTC).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "derived_by": f"scripts/spine_set.py ({SCHEMA}, wall map {WALL_MAP_VERSION})",
        },
        "root": {"spec": ROOT_SPEC, "matched": roots},
        "edge_policy": {
            "static_calls": "followed",
            "closures": "followed — {closure#N} bodies are members like any other",
            "dyn_trait_and_fn_pointer_edges": (
                "followed ONLY via a dump-provided dyn_impl_table enumerating ALL "
                "impls (conservative over-approximation); otherwise emitted as named "
                "exclusions in edge_exclusions — assumption-ledger candidates "
                "(program §3.6), never silently dropped"
            ),
            "external_callees": (
                "edges leaving the dump's body set (core/std/alloc/other crates) are "
                "recorded in external_callees and not followed — core-callee model "
                "candidates for the §3.6 ledger"
            ),
            "profile": (
                "release (-O3) build only; bodies flagged debug_only are excluded "
                "from membership and listed in debug_twin_exclusions"
            ),
            "contract_boundary": (
                "nodes matching the boundary list are members but their outgoing "
                "edges are not followed; every cut requires a ledger_ref (§3.6) and "
                "is listed in contract_boundary_cuts"
            ),
            "family_partition": (
                "root-module partition on the defining module's first two segments; "
                "tc::whnf_proj folds into tc::whnf (documented alias); everything "
                "else is 'other' with module_path preserved per member"
            ),
            "wall_tag_map": (
                f"CLASS_TO_WALL {WALL_MAP_VERSION} — conservative navigation from "
                "producer leaf classes; aggregators (Borrow, Call) mapped per recon "
                "§2; unmapped classes preserved as 'unmapped:<Class>'; refined by "
                "each Track-T wall job's leaf-cause census"
            ),
            "mode_reachability": (
                "dump-recorded mode_gate verbatim when present; else the "
                "extension-only module heuristic (tc::infer_cubical, tc::infer_zfc); "
                "else 'constructive:assumed-reachable' — annotation only, never "
                "prunes membership"
            ),
        },
        "member_count": len(member_list),
        "family_counts": family_counts,
        "members": member_list,
        "edge_exclusions": edge_exclusions,
        "dyn_impl_expansions": dyn_expansions,
        "external_callees": [external[k] for k in sorted(external)],
        "debug_twin_exclusions": [
            {"def_path": dp, "first_caller": debug_twins[dp]} for dp in sorted(debug_twins)
        ],
        "contract_boundary_cuts": boundary_cuts,
    }
    return out


# --------------------------------------------------------------------------
# self-test (synthesized fixture dump: tests/fixtures/spine_set/)
# --------------------------------------------------------------------------

GOOD_DIGEST = "b6c32185902bab851d3a7ba10b15192acb41221a72f47529aa6d65ff23915c76"

_EXPECTED_MEMBERS = {
    "env::decl_add::<impl env::Environment>::add_decl": "env::decl_add",
    "env::decl_add::<impl env::Environment>::add_decl::{closure#0}": "env::decl_add",
    "env::decl_add::<impl env::Environment>::check_decl_core": "env::decl_add",
    "tc::infer::<impl tc::TypeChecker<'env>>::infer_type": "tc::infer",
    "tc::infer_proj::<impl tc::TypeChecker<'env>>::infer_proj": "tc::infer_proj",
    "tc::def_eq::delta::<impl tc::TypeChecker<'env>>::lazy_delta_step": "tc::def_eq",
    "tc::whnf::<impl tc::TypeChecker<'env>>::whnf": "tc::whnf",
    "<tc::whnf::WhnfCache as std::default::Default>::default": "tc::whnf",
    "tc::reduction::cofib::CofibAtom::value": "tc::reduction",
    "tc::infer_cubical::<impl tc::TypeChecker<'env>>::infer_cubical": "other",
    "tc::config::<impl tc::TypeChecker<'env>>::cache_lookup": "other",
}

_BOUNDARY = [
    {
        "def_path": "tc::config::<impl tc::TypeChecker<'env>>::cache_lookup",
        "reason": "TypeChecker cache surface (hostile shape 4) — contract-modeled by T-HASH",
        "ledger_ref": "spine_assumption_ledger:cache/tc_config_cache_lookup",
    }
]


def _load_fixture() -> dict:
    if not FIXTURE.is_file():
        raise SpineSetError(f"self-test fixture missing: {FIXTURE}")
    return json.loads(FIXTURE.read_text())


def _expect_raises(arm: str, fragment: str, fn, failures: list[str]) -> None:
    try:
        fn()
    except SpineSetError as exc:
        if fragment in str(exc):
            print(f"  PASS  {arm}")
        else:
            failures.append(f"{arm}: error text lacks {fragment!r}: {exc}")
    else:
        failures.append(f"{arm}: no error raised (fail-open)")


def self_test() -> int:
    failures: list[str] = []
    fixture = _load_fixture()

    def build(dump, boundary=_BOUNDARY, digest=GOOD_DIGEST):
        return build_spine_set(
            dump, digest, "tests/fixtures/spine_set/synthetic_dump.json", boundary,
            now_utc="2026-08-23T00:00:00Z",
        )

    # Arm 1: closure computation ------------------------------------------
    out = build(copy.deepcopy(fixture))
    got = {m["def_path"]: m["family"] for m in out["members"]}
    if got == _EXPECTED_MEMBERS and out["member_count"] == len(_EXPECTED_MEMBERS):
        print("  PASS  closure: members are exactly the reachable set")
    else:
        failures.append(
            f"closure: members mismatch\n    extra={sorted(set(got) - set(_EXPECTED_MEMBERS))}"
            f"\n    missing={sorted(set(_EXPECTED_MEMBERS) - set(got))}"
        )
    unreached = "expr::unreachable_helper"
    if unreached in got:
        failures.append("closure: unreached body leaked into members")
    if out["root"]["matched"] != ["env::decl_add::<impl env::Environment>::add_decl"]:
        failures.append(f"closure: wrong root match {out['root']['matched']}")

    # Arm 2: family tagging (root-module partition incl. impl-form paths) --
    fam_bad = {dp: (want, got.get(dp)) for dp, want in _EXPECTED_MEMBERS.items() if got.get(dp) != want}
    if not fam_bad:
        print("  PASS  family: root-module partition tags (impl-form + closure paths)")
    else:
        failures.append(f"family: mismatches {fam_bad}")
    fc = out["family_counts"]
    if fc["env::decl_add"] == 3 and fc["tc::whnf"] == 2 and fc["other"] == 2:
        print("  PASS  family: counts per family")
    else:
        failures.append(f"family: counts wrong {fc}")

    # Arm 3: dyn-edge exclusion emission ----------------------------------
    dyn_ex = [e for e in out["edge_exclusions"] if e["kind"] == "dyn-trait"]
    fp_ex = [e for e in out["edge_exclusions"] if e["kind"] == "fn-pointer"]
    if (
        len(dyn_ex) == 1
        and dyn_ex[0]["caller"] == "env::decl_add::<impl env::Environment>::add_decl"
        and dyn_ex[0]["callee_descriptor"] == "<dyn tc::heartbeat::HeartbeatSink>::tick"
        and "ledger" in dyn_ex[0]["note"]
        and len(fp_ex) == 1
        and "<tc::heartbeat::NullSink as tc::heartbeat::HeartbeatSink>::tick" not in got
    ):
        print("  PASS  dyn: dyn-trait + fn-pointer edges emitted as named exclusions")
    else:
        failures.append(f"dyn: exclusion emission wrong: {out['edge_exclusions']}")
    with_table = copy.deepcopy(fixture)
    with_table["dyn_impl_table"] = {
        "<dyn tc::heartbeat::HeartbeatSink>::tick": [
            "<tc::heartbeat::NullSink as tc::heartbeat::HeartbeatSink>::tick"
        ]
    }
    out_t = build(with_table)
    got_t = {m["def_path"] for m in out_t["members"]}
    if (
        "<tc::heartbeat::NullSink as tc::heartbeat::HeartbeatSink>::tick" in got_t
        and len(out_t["dyn_impl_expansions"]) == 1
        and not [e for e in out_t["edge_exclusions"] if e["kind"] == "dyn-trait"]
    ):
        print("  PASS  dyn: dyn_impl_table expands conservatively over all impls")
    else:
        failures.append("dyn: impl-table expansion did not follow the impl")

    # Arm 4: fail-closed on missing fields --------------------------------
    d = copy.deepcopy(fixture); d.pop("bodies")
    _expect_raises("fail-closed: missing 'bodies' names 'enumerate-bodies'", "enumerate-bodies", lambda: build(d), failures)
    d = copy.deepcopy(fixture)
    for b in d["bodies"]:
        b.pop("calls", None)
    _expect_raises("fail-closed: no call graph names 'emit-call-graph'", "emit-call-graph", lambda: build(d), failures)
    d = copy.deepcopy(fixture); d["bodies"][1].pop("calls")
    _expect_raises("fail-closed: one body without 'calls' is named", d["bodies"][1]["def_path"], lambda: build(d), failures)
    d = copy.deepcopy(fixture); d["bodies"][0]["calls"][0].pop("kind")
    _expect_raises("fail-closed: edge without 'kind'", "kind", lambda: build(d), failures)
    d = copy.deepcopy(fixture); d["bodies"][0]["calls"][0]["kind"] = "telepathy"
    _expect_raises("fail-closed: unknown edge kind", "telepathy", lambda: build(d), failures)
    d = copy.deepcopy(fixture); d["bodies"][0]["calls"][0].pop("via")
    _expect_raises("fail-closed: edge without 'via' (how it was found)", "via", lambda: build(d), failures)
    d = copy.deepcopy(fixture); d["bodies"][2].pop("producer")
    _expect_raises("fail-closed: body without producer classes", "emit-producer-classes", lambda: build(d), failures)
    d = copy.deepcopy(fixture); d["bodies"].append(copy.deepcopy(d["bodies"][3]))
    _expect_raises("fail-closed: duplicate def_path is ambiguous", "duplicate def_path", lambda: build(d), failures)
    d = copy.deepcopy(fixture)
    d["bodies"] = [b for b in d["bodies"] if not is_root(b["def_path"])]
    _expect_raises("fail-closed: root absent names the root spec", "add_decl", lambda: build(d), failures)
    d = copy.deepcopy(fixture)
    bad_boundary = [{"def_path": "x", "reason": "r"}]
    _expect_raises("fail-closed: boundary cut without ledger_ref", "ledger_ref", lambda: build(d, boundary=bad_boundary), failures)

    # Arm 5: provenance required ------------------------------------------
    d = copy.deepcopy(fixture); d.pop("provenance")
    _expect_raises("provenance: missing block names 'emit-provenance'", "emit-provenance", lambda: build(d), failures)
    d = copy.deepcopy(fixture); d["provenance"].pop("clean_rev")
    _expect_raises("provenance: missing clean_rev is named", "clean_rev", lambda: build(d), failures)
    _expect_raises(
        "provenance: driver digest mismatch refused", "mismatch",
        lambda: build(copy.deepcopy(fixture), digest="0" * 64), failures,
    )
    _expect_raises(
        "provenance: malformed --driver-digest refused", "64 lowercase hex",
        lambda: build(copy.deepcopy(fixture), digest="not-a-digest"), failures,
    )
    prov = out["provenance"]
    if all(prov.get(k) for k in ("dump_path", "driver_dylib_sha256", "clean_rev", "date", "derived_by")):
        print("  PASS  provenance: output block carries dump path, driver digest, clean rev, date")
    else:
        failures.append(f"provenance: output block incomplete: {prov}")

    # Arm 6: wall tags, mode annotations, twins, cuts, externals, edges ----
    m = {x["def_path"]: x for x in out["members"]}
    delta = m["tc::def_eq::delta::<impl tc::TypeChecker<'env>>::lazy_delta_step"]
    core = m["env::decl_add::<impl env::Environment>::check_decl_core"]
    whnf = m["tc::whnf::<impl tc::TypeChecker<'env>>::whnf"]
    if (
        "K-STACK" in delta["wall_tags"]
        and {"T-CTRL", "unmapped:WeirdNewClass"} <= set(core["wall_tags"])
        and "T-HEAP" in whnf["wall_tags"]
        and whnf["producer_classes"] == ["Borrow"]
    ):
        print("  PASS  walls: class map applied, unmapped classes preserved visibly")
    else:
        failures.append(f"walls: tags wrong: {delta['wall_tags']} {core['wall_tags']} {whnf['wall_tags']}")
    cofib = m["tc::reduction::cofib::CofibAtom::value"]
    cub = m["tc::infer_cubical::<impl tc::TypeChecker<'env>>::infer_cubical"]
    if (
        cofib["mode_reachability"]["source"] == "dump"
        and "Cubical" in cofib["mode_reachability"]["annotation"]
        and cub["mode_reachability"]["source"] == "heuristic"
        and whnf["mode_reachability"]["source"] == "default"
        and "assumed-reachable" in whnf["mode_reachability"]["annotation"]
    ):
        print("  PASS  mode: dump gate verbatim; heuristic; conservative default")
    else:
        failures.append("mode: annotations wrong")
    if out["debug_twin_exclusions"] == [
        {
            "def_path": "env::decl_add::debug_probe",
            "first_caller": "env::decl_add::<impl env::Environment>::add_decl",
        }
    ]:
        print("  PASS  twins: debug-only body excluded and listed")
    else:
        failures.append(f"twins: {out['debug_twin_exclusions']}")
    cuts = out["contract_boundary_cuts"]
    if (
        len(cuts) == 1
        and cuts[0]["ledger_ref"] == _BOUNDARY[0]["ledger_ref"]
        and m["tc::config::<impl tc::TypeChecker<'env>>::cache_lookup"]["boundary_cut"]
        and "tc::whnf_proj::<impl tc::TypeChecker<'env>>::whnf_core_proj" not in got
    ):
        print("  PASS  boundary: cut node is a member; its edges are not followed; ledger_ref carried")
    else:
        failures.append(f"boundary: {cuts}")
    ext = {e["callee"] for e in out["external_callees"]}
    if ext == {"core::option::Option::<T>::ok_or"}:
        print("  PASS  externals: out-of-dump callees recorded, not followed")
    else:
        failures.append(f"externals: {ext}")
    add = m["env::decl_add::<impl env::Environment>::add_decl"]
    if (
        add["found_via"] == {"kind": "root"}
        and all(e.get("via") and e.get("disposition") for mm in out["members"] for e in mm["calls"])
        and m["tc::whnf::<impl tc::TypeChecker<'env>>::whnf"]["found_via"]["caller"]
        == "env::decl_add::<impl env::Environment>::check_decl_core"
    ):
        print("  PASS  edges: every member records how it and its edges were found")
    else:
        failures.append("edges: found_via/disposition records wrong")

    # Arm 7: determinism ---------------------------------------------------
    if json.dumps(build(copy.deepcopy(fixture))) == json.dumps(build(copy.deepcopy(fixture))):
        print("  PASS  determinism: identical output for identical inputs")
    else:
        failures.append("determinism: two builds differ")

    # Arm 8: CLI fail-closed (--dump without --driver-digest) --------------
    with tempfile.TemporaryDirectory() as td:
        dump_file = Path(td) / "dump.json"
        dump_file.write_text(json.dumps(fixture))
        with contextlib.redirect_stderr(io.StringIO()) as quiet:
            rc = main(["--dump", str(dump_file), "--out", str(Path(td) / "o.json")])
        if "--driver-digest is required" not in quiet.getvalue():
            failures.append("cli: refusal did not name --driver-digest")
        if rc != 0 and not (Path(td) / "o.json").exists():
            print("  PASS  cli: --driver-digest is required; nothing partial written")
        else:
            failures.append("cli: derivation ran without --driver-digest")

    if failures:
        for f in failures:
            print(f"  FAIL  {f}", file=sys.stderr)
        print(f"SPINE_SET self-test: {len(failures)} arm(s) RED", file=sys.stderr)
        return 1
    print("SPINE_SET self-test: 8 arms, all green")
    return 0


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        prog="spine_set.py",
        description="Derive data/spine_set.json from a trust-host whole-crate dump (G-SPINE-SET).",
    )
    ap.add_argument("--dump", help="whole-crate coverage/dump artifact (JSON) from the trust host")
    ap.add_argument("--driver-digest", help="sha256 of the driver dylib that produced the dump (required)")
    ap.add_argument("--boundary", help="contract-boundary cut rules (JSON list; each needs ledger_ref)")
    ap.add_argument("--out", default=str(REPO_ROOT / DEFAULT_OUT), help=f"output path (default {DEFAULT_OUT})")
    ap.add_argument("--describe", action="store_true", help="print the dump-producer contract and exit")
    ap.add_argument("--self-test", action="store_true", help="run the synthesized-fixture self-test")
    args = ap.parse_args(argv)

    if args.describe:
        print(DESCRIBE, end="")
        return 0
    if args.self_test:
        return self_test()
    try:
        if not args.dump:
            raise SpineSetError("--dump is required (or use --describe / --self-test)")
        if not args.driver_digest:
            raise SpineSetError(
                "--driver-digest is required: the spine set's provenance must pin the "
                "driver dylib sha256 that produced the dump (program §2 G-SPINE-SET)"
            )
        dump_path = Path(args.dump)
        try:
            dump = json.loads(dump_path.read_text())
        except (OSError, ValueError) as exc:
            raise SpineSetError(f"cannot read dump {dump_path}: {exc}") from exc
        boundary = None
        if args.boundary:
            try:
                boundary = json.loads(Path(args.boundary).read_text())
            except (OSError, ValueError) as exc:
                raise SpineSetError(f"cannot read boundary {args.boundary}: {exc}") from exc
        out = build_spine_set(dump, args.driver_digest, str(dump_path), boundary)
    except SpineSetError as exc:
        print(f"SPINE_SET=fail {exc}", file=sys.stderr)
        return 1
    out_path = Path(args.out)
    tmp = out_path.with_suffix(out_path.suffix + ".tmp")
    tmp.write_text(json.dumps(out, indent=1) + "\n")
    tmp.replace(out_path)
    fams = {k: v for k, v in out["family_counts"].items() if v}
    print(
        f"SPINE_SET ok members={out['member_count']} families={fams} "
        f"edge_exclusions={len(out['edge_exclusions'])} "
        f"debug_twins={len(out['debug_twin_exclusions'])} "
        f"boundary_cuts={len(out['contract_boundary_cuts'])} -> {out_path}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
