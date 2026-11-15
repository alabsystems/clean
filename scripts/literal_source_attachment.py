#!/usr/bin/env python3
"""Inventory the real literal helper's Trust extraction; never certify it.

Exit 1 means the source-refinement theorem is still absent, even if extraction
eventually becomes available. Exit 2 means malformed/missing probe inputs. This
is deliberately a bounded diagnostic, not an extensible proof-acceptance gate.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys


FUNCTION = "tc::infer::infer_literal_type"
COVERAGE_SCHEMA = "trust.thir-lower.crate-module.coverage.v2"
PUBLICATION_SCHEMA = "trust.thir-lower.artifact-set.v1"
ARTIFACT_DOMAIN = "trust.thir-lower.artifact.v1"
ARTIFACT_NAMES = ("clean_kernel.trust-ir.bin", "clean_kernel.trust-ir.txt")
COVERAGE_NAMES = {
    "dump": "clean_kernel.coverage.json",
    "emit": "clean_kernel.trust-ir.coverage.json",
}
DIRECT_CAPABILITIES = ("structural-parity-only-v1", "obligation-bearing-pending-v2")
STATIC_PATHS = ("tc::infer::NAME_NAT", "tc::infer::NAME_STRING")
# Local snapshots include every shared-helper caller. This is not a complete
# transitive source closure, nor compiler-to-source attestation.
SOURCE_PATHS = (
    "crates/clean-kernel/src/tc/infer.rs",
    "crates/clean-kernel/src/tc/cert/infer_core.rs",
    "crates/clean-kernel/src/tc/def_eq/proof_irrel.rs",
    "crates/clean-kernel/src/expr/types.rs",
    "crates/clean-kernel/src/expr/constructors.rs",
    "crates/clean-kernel/src/expr/mod.rs",
    "crates/clean-kernel/src/expr/meta.rs",
    "crates/clean-kernel/src/name.rs",
)
MIR_ANCHORS = (
    f"// MIR for `{FUNCTION}` after built",
    "fn infer_literal_type(_1: &expr::types::Literal) -> expr::Expr",
    "discriminant((*_1))",
    "<LazyLock<name::Name> as Deref>::deref",
    "<name::Name as Clone>::clone",
    "Vec::<level::Level>::new()",
    "constructors::<impl expr::Expr>::const_::<Vec<level::Level>>",
    "static: infer::NAME_NAT",
    "static: infer::NAME_STRING",
)
OPEN_OBLIGATIONS = (
    "Universal refinement of the actual compiler-extracted production body.",
    "Authenticated source-to-extraction binding (snapshot hashes alone are not this).",
    "Literal payload and canonical builtin Name representation correspondence, "
    "including alias-safe Arc ownership/frame invariants.",
    "LazyLock initialization/read, Name clone, empty Vec, and Expr constructor contracts.",
    "Composition with ordinary inference, certificate inference, and quick-inference "
    "callsites, plus the environment contract.",
)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def reject_json_constant(value):
    raise ValueError(f"non-JSON numeric constant: {value}")


def extraction_record(coverage):
    if coverage.get("schema") != COVERAGE_SCHEMA:
        raise ValueError("unknown or missing Trust coverage schema")
    if coverage.get("crate") != "clean_kernel":
        raise ValueError("coverage does not describe clean_kernel")
    if coverage.get("proof_authority") is not False:
        raise ValueError("expected the current explicitly non-proof-authoritative coverage lane")
    bodies = coverage.get("bodies")
    if not isinstance(bodies, list) or not all(isinstance(row, dict) for row in bodies):
        raise ValueError("missing/malformed coverage bodies")
    matches = [row for row in bodies if row.get("def_path") == FUNCTION]
    if len(matches) != 1:
        raise ValueError(f"expected one exact production function, found {len(matches)}")
    row = matches[0]
    if row.get("kind") != "fn":
        raise ValueError("production helper record is not a function")
    for key in ("lowered", "symbolic", "spliced"):
        if type(row.get(key)) is not bool:
            raise ValueError(f"missing/malformed function field: {key}")
    unsupported = row.get("unsupported")
    if not isinstance(unsupported, list) or not all(
        isinstance(item, list) and len(item) == 2
        and isinstance(item[0], str) and type(item[1]) is int and item[1] > 0
        for item in unsupported
    ):
        raise ValueError("missing/malformed unsupported-shape ledger")
    return row


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def artifact_digest(payload):
    """Trust's ProofDigest::sha256_domain framing, not ordinary file SHA256."""
    domain = ARTIFACT_DOMAIN.encode("utf-8")
    digest = hashlib.sha256(b"trust-ir.sha256-domain.v1\0")
    digest.update(len(domain).to_bytes(8, "big"))
    digest.update(domain)
    digest.update(len(payload).to_bytes(8, "big"))
    digest.update(payload)
    return "sha256:" + digest.hexdigest()


def publication_artifacts(coverage, dump_dir):
    """Reject incomplete/mixed publications; the marker is not an attestation."""
    publication = coverage.get("publication")
    if not isinstance(publication, dict) or (
        publication.get("schema") != PUBLICATION_SCHEMA
        or publication.get("digest_algorithm") != "sha256-domain-v1"
        or publication.get("digest_domain") != ARTIFACT_DOMAIN
        or publication.get("commit_marker") is not True
    ):
        raise ValueError("missing/malformed Trust artifact publication marker")
    entries = publication.get("artifacts")
    if not isinstance(entries, list) or len(entries) != len(ARTIFACT_NAMES):
        raise ValueError("expected exactly the binary and text publication entries")
    artifacts = {}
    for entry in entries:
        if not isinstance(entry, dict):
            raise ValueError("malformed artifact publication entry")
        name = entry.get("name")
        if not isinstance(name, str) or name not in ARTIFACT_NAMES or name in artifacts:
            raise ValueError("missing, duplicate or unknown publication artifact name")
        size = entry.get("bytes")
        if type(size) is not int or size <= 0:
            raise ValueError(f"missing/malformed publication length: {name}")
        payload = (dump_dir / name).read_bytes()
        if len(payload) != size or artifact_digest(payload) != entry.get("digest"):
            raise ValueError(f"artifact does not match its publication marker: {name}")
        artifacts[name] = payload
    return artifacts


def definition_identity(definition):
    if not isinstance(definition, dict) or not isinstance(definition.get("def_path"), str):
        raise ValueError("missing/malformed source definition")
    identity = definition.get("def_path_hash")
    if not isinstance(identity, dict) or any(
        not isinstance(identity.get(key), str)
        or re.fullmatch(r"[0-9a-f]{16}", identity[key]) is None
        for key in ("stable_crate_id", "local_hash")
    ):
        raise ValueError("missing/malformed source DefPathHash")
    return identity["stable_crate_id"], identity["local_hash"]


def source_index(value):
    return type(value) is int and 0 <= value < (1 << 32)


def direct_readback(coverage, row):
    """Join producer-declared source facts, without interpreting CTFE storage.

    This does not validate the graph's heap semantics, source attestation, or
    initialized runtime state. Refused graphs remain useful diagnostics.
    """
    if coverage.get("direct_obligation_capability") not in DIRECT_CAPABILITIES:
        raise ValueError("unknown or missing direct-obligation capability")
    if coverage.get("native_verification_requests") is not False:
        raise ValueError("expected explicitly non-authoritative direct capture")
    readback = coverage.get("source_static_readback")
    if not isinstance(readback, dict):
        raise ValueError("direct capture lacks source-static-readback section")
    expected = {
        "schema": "trust.thir.source-static-readback.v1",
        "producer": "thir_static_ref",
        "storage_phase": "cold_initializer_only",
        "evaluator_dependency": "rustc_ctfe",
        "allocation_namespace": "per_body",
    }
    if any(readback.get(key) != value for key, value in expected.items()):
        raise ValueError("unknown or malformed source-static-readback identity")
    for key in ("proof_authority", "native_verification_requests"):
        if readback.get(key) is not False:
            raise ValueError(f"cold readback must explicitly deny {key}")
    if type(readback.get("inventory_complete")) is not bool:
        raise ValueError("missing/malformed readback inventory status")
    target, limits = readback.get("target"), readback.get("limits")
    if (not isinstance(target, dict)
            or any(not isinstance(target.get(key), str) or not target[key]
                   for key in ("triple", "data_layout"))
            or type(target.get("little_endian")) is not bool
            or type(target.get("pointer_size_bytes")) is not int
            or target["pointer_size_bytes"] <= 0):
        raise ValueError("missing/malformed producer readback target")
    limit_keys = ("nodes", "bytes", "relocations", "body_expressions", "body_occurrences",
                  "bodies", "source_snippet_bytes")
    if not isinstance(limits, dict) or any(
        type(limits.get(key)) is not int or limits[key] <= 0 for key in limit_keys
    ):
        raise ValueError("missing/malformed producer readback limits")
    bodies = readback.get("bodies")
    if not isinstance(bodies, list) or not all(isinstance(body, dict) for body in bodies):
        raise ValueError("missing/malformed source readback bodies")
    coverage_indices = {}
    for body in coverage["bodies"]:
        index = body.get("def_index")
        if not source_index(index) or index in coverage_indices:
            raise ValueError("coverage requires unique unsigned source body indices")
        coverage_indices[index] = body.get("def_path")
    indices, owners = set(), set()
    complete = 0
    for body in bodies:
        index = body.get("def_index")
        owner = body.get("owner")
        identity = definition_identity(owner)
        if (not source_index(index) or index in indices
                or identity in owners or coverage_indices.get(index) != owner["def_path"]):
            raise ValueError("duplicate or mismatched source readback owner")
        indices.add(index)
        owners.add(identity)
        graph = body.get("graph")
        if not isinstance(graph, dict) or graph.get("capture_status") not in ("complete", "refused"):
            raise ValueError("missing/malformed producer-declared cold graph status")
        errors = graph.get("errors")
        if not isinstance(errors, list) or not all(isinstance(error, str) and error for error in errors):
            raise ValueError("missing/malformed cold graph errors")
        if not all(isinstance(graph.get(key), list) for key in ("statics", "nodes")):
            raise ValueError("missing/malformed producer-declared cold graph roster")
        if any(not isinstance(entry, dict) for key in ("statics", "nodes") for entry in graph[key]):
            raise ValueError("malformed producer-declared cold graph entry")
        if graph["capture_status"] == "complete":
            if errors:
                raise ValueError("complete cold graph reports errors")
            complete += 1
        elif not errors or graph["statics"] or graph["nodes"]:
            raise ValueError("refused cold graph must disclose errors and no partial storage")
    for key, value in (("body_count", len(bodies)), ("complete_bodies", complete),
                       ("refused_bodies", len(bodies) - complete)):
        if type(readback.get(key)) is not int or readback[key] != value:
            raise ValueError(f"source readback census disagrees with {key}")
    errors = readback.get("errors")
    if not isinstance(errors, list) or not all(isinstance(error, str) and error for error in errors):
        raise ValueError("missing/malformed source readback errors")
    if readback["inventory_complete"]:
        # The producer checks HIR body owners. Coverage additionally includes
        # generated SyntheticCoroutineBody records without HIR bodies; it is
        # a superset, not this inventory's independently known denominator.
        if errors:
            raise ValueError("complete source inventory reports errors")
    elif not errors:
        raise ValueError("incomplete source inventory must disclose its refusal")
    elif complete:
        raise ValueError("global source inventory refusal must refuse every cold graph")
    status = ("refused" if not readback["inventory_complete"] or (bodies and complete == 0)
              else "partial" if complete != len(bodies) else "complete")
    if readback.get("capture_status") != status:
        raise ValueError("source readback capture status disagrees with its census")
    selected = [body for body in bodies if body["owner"]["def_path"] == FUNCTION]
    if len(selected) != 1 or selected[0]["def_index"] != row.get("def_index"):
        raise ValueError("expected one exact production helper readback/coverage join")
    selected = selected[0]
    owner_identity = definition_identity(selected["owner"])
    uses = selected.get("uses")
    if not isinstance(uses, list) or not all(isinstance(use, dict) for use in uses):
        raise ValueError("missing/malformed production static-use roster")
    expressions, statics = set(), {}
    for use in uses:
        index = use.get("expr_index")
        definition = use.get("static_definition")
        identity = definition_identity(definition)
        path = definition["def_path"]
        if (not source_index(index) or index >= limits["body_expressions"] or index in expressions
                or path in statics or identity[0] != owner_identity[0]):
            raise ValueError("duplicate or mismatched production static use")
        expressions.add(index)
        statics[path] = identity
    if not set(statics) <= set(STATIC_PATHS) or len(set(statics.values())) != len(statics):
        raise ValueError("expected exact distinct infer::NAME_NAT/NAME_STRING identities")
    if selected["graph"]["capture_status"] == "complete":
        if set(statics) != set(STATIC_PATHS):
            raise ValueError("complete helper readback lacks the expected builtin static pair")
        roots = {}
        for root in selected["graph"]["statics"]:
            if not isinstance(root, dict):
                raise ValueError("malformed production static root")
            definition = root.get("definition")
            identity = definition_identity(definition)
            if definition["def_path"] in roots:
                raise ValueError("duplicate production static root")
            roots[definition["def_path"]] = identity
        if roots != statics:
            raise ValueError("cold static roots do not match source-use identities")
    return {
        **{key: readback[key] for key in expected},
        **{key: readback[key] for key in (
            "proof_authority", "native_verification_requests", "inventory_complete",
            "capture_status", "body_count", "complete_bodies", "refused_bodies", "errors",
        )},
        "production_body": selected,
        "production_static_use_inventory": (
            "observed_expected_pair" if set(statics) == set(STATIC_PATHS)
            else "unavailable_or_partial_due_refusal"
        ),
        "other_refused_owners": [
            {"owner": body["owner"], "def_index": body["def_index"], "errors": body["graph"]["errors"]}
            for body in bodies if body is not selected and body["graph"]["capture_status"] == "refused"
        ],
        "target": target,
        "limits": limits,
        "interpretation": "Producer-declared cold graph only; no storage-semantic or runtime-state validation.",
        "inventory_scope": "Producer-declared HIR inventory; coverage may additionally contain generated bodies.",
    }


def probe(repo, dump_dir, mir_path=None, *, direct_thir=False, surface="dump"):
    if surface not in COVERAGE_NAMES:
        raise ValueError("unknown publication surface")
    if direct_thir and mir_path is not None:
        raise ValueError("direct THIR mode does not consume MIR")
    if not direct_thir and mir_path is None:
        raise ValueError("legacy MIR diagnostic requires --built-mir")
    coverage_path = dump_dir / COVERAGE_NAMES[surface]
    coverage_bytes = coverage_path.read_bytes()
    coverage = json.loads(coverage_bytes, object_pairs_hook=unique_object,
                          parse_constant=reject_json_constant)
    if not isinstance(coverage, dict):
        raise ValueError("coverage must be a JSON object")
    row = extraction_record(coverage)
    artifacts = publication_artifacts(coverage, dump_dir)
    readback = direct_readback(coverage, row) if direct_thir else None
    mir_bytes = None if direct_thir else mir_path.read_bytes()
    if mir_bytes is not None:
        mir = mir_bytes.decode("utf-8")
        missing = [anchor for anchor in MIR_ANCHORS if anchor not in mir]
        if missing:
            raise ValueError(f"raw MIR does not contain the expected production anchors: {missing}")
    report = {
        "schema_version": ("clean.literal-source-attachment-probe.v3" if direct_thir
                           else "clean.literal-source-attachment-probe.v2"),
        "status": "blocked",
        "source_attachment_verified": False,
        "proof_authority": False,
        "scope": "Exact production literal helper; no whole-kernel or compiler claim.",
        "source_binding": "Snapshot only; hashes are not compiler-to-source attestation.",
        "artifact_set_consistency": (
            "checked against producer publication marker; not source attestation or proof"
        ),
        "artifact_publication": coverage["publication"],
        "source_sha256": {path: sha256(repo / path) for path in SOURCE_PATHS},
        "artifact_sha256": {
            "coverage": hashlib.sha256(coverage_bytes).hexdigest(),
            "trust_ir_binary": hashlib.sha256(artifacts[ARTIFACT_NAMES[0]]).hexdigest(),
            "trust_ir_text": hashlib.sha256(artifacts[ARTIFACT_NAMES[1]]).hexdigest(),
        },
        "producer_capability": coverage.get("direct_obligation_capability"),
        "producer_record": row,
        "open_obligations": list(OPEN_OBLIGATIONS),
        "note": "Producer coverage, cold storage, MIR anchors and regression samples are not a universal theorem.",
    }
    if direct_thir:
        report.update(capture_lane="direct-thir", publication_surface=surface,
                      producer_source_static_readback=readback)
    else:
        report["artifact_sha256"]["built_mir"] = hashlib.sha256(mir_bytes).hexdigest()
        report["observed_mir_anchors"] = list(MIR_ANCHORS)
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--dump-dir", type=Path, required=True)
    lane = parser.add_mutually_exclusive_group(required=True)
    lane.add_argument("--built-mir", type=Path, help="historical MIR diagnostic input")
    lane.add_argument("--direct-thir", action="store_true", help="inspect direct capture without any MIR input")
    parser.add_argument("--surface", choices=COVERAGE_NAMES, default="dump",
                        help="explicit producer publication surface (never guess filenames)")
    parser.add_argument("--output", type=Path,
                        help="create a new report; never overwrite a report or captured input")
    args = parser.parse_args(argv)
    try:
        report = probe(args.repo, args.dump_dir, args.built_mir,
                       direct_thir=args.direct_thir, surface=args.surface)
        rendered = json.dumps(report, indent=2, sort_keys=True, allow_nan=False) + "\n"
        if args.output is not None:
            # Exclusive creation also refuses symlinks (including dangling
            # ones) and closes the check/open race. A diagnostic must not
            # overwrite the source or publication bytes it just inspected.
            with args.output.open("x", encoding="utf-8", newline="") as stream:
                stream.write(rendered)
        else:
            print(rendered, end="")
    except (OSError, ValueError, TypeError, RecursionError) as error:
        print(f"literal source probe refused: {error}", file=sys.stderr)
        return 2
    print("literal source attachment remains unproved", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
