# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Build a compact dashboard from clean research JSON manifests.

The dashboard intentionally consumes generic JSON files instead of Rust crate
internals. It recognizes the current proof queue, axiom audit, Mathverse summaries,
research-program lock files, and status reports, then emits a small JSON or
Markdown scaffold suitable for issue comments or release notes.

Examples:
    python3 scripts/research_dashboard.py --default-inputs --format markdown
    python3 scripts/research_dashboard.py data/research_program_lock.json data/proof_queue.json
    python3 scripts/research_dashboard.py data/*.json --format markdown
    python3 scripts/research_dashboard.py --self-check
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from collections import Counter
from collections.abc import Sequence
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

DASHBOARD_SCHEMA_VERSION = 1
DEFAULT_TITLE = "clean Research Dashboard"
DETERMINISTIC_GENERATED_AT = "1970-01-01T00:00:00Z"
DEFAULT_INPUTS = (
    Path("data/research_program_lock.json"),
    Path("data/proof_queue.json"),
    Path("data/axiom_audit.json"),
    Path("data/research_program_manifest.json"),
)
ISSUE_REF_RE = re.compile(r"(?<!\w)#(\d+)\b|\bissue\s+#?(\d+)\b", re.IGNORECASE)


def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def parse_timestamp(value: str) -> datetime:
    text = value.strip()
    if not text:
        raise ValueError("timestamp must be non-empty")
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", text):
        parsed = datetime.fromisoformat(text)
        return parsed.replace(tzinfo=timezone.utc)
    if text.endswith("Z"):
        text = f"{text[:-1]}+00:00"
    parsed = datetime.fromisoformat(text)
    if parsed.tzinfo is None:
        return parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        raise ValueError(f"{path}: file not found") from None
    except json.JSONDecodeError as exc:
        raise ValueError(
            f"{path}: invalid JSON at line {exc.lineno}: {exc.msg}"
        ) from None


def display_path(path: Path, base: Path | None = None) -> str:
    base = base or Path.cwd()
    try:
        return str(path.resolve().relative_to(base.resolve()))
    except (OSError, ValueError):
        return str(path)


def is_research_status_report(payload: dict[str, Any]) -> bool:
    required_keys = {
        "total_entries",
        "status_counts",
        "domain_counts",
        "family_counts",
        "key_entries",
        "entries",
        "registries",
    }
    return required_keys.issubset(payload)


def is_research_program_manifest(payload: dict[str, Any]) -> bool:
    items = payload.get("items")
    if not isinstance(items, list):
        return False
    return any(
        isinstance(item, dict)
        and all(key in item for key in ("id", "domain", "family", "status"))
        for item in items
    )


def detect_kind(payload: Any, path: Path) -> str:
    if isinstance(payload, dict):
        manifest_kind = payload.get("manifest_kind")
        if isinstance(manifest_kind, str) and manifest_kind:
            return manifest_kind
        if is_research_status_report(payload):
            return "research_status_report"
        if is_research_program_manifest(payload):
            return "research_program_manifest"
        if "lock_id" in payload and "components" in payload:
            return "research_program_lock"
        if "queue" in payload and isinstance(payload["queue"], list):
            return "proof_queue"
        if "conjectures" in payload and "total_domain_axioms" in payload:
            return "axiom_audit"
        if "conjectures" in payload:
            return "conjecture_report"
        if "sources" in payload and "shards_produced" in payload:
            return "mathverse_provenance"
        if "source_systems" in payload and any(
            str(key).startswith("mathverse_") for key in payload
        ):
            return "mathverse_summary"
        if "specs" in payload and "summary" in payload:
            return "status_report"
        if "summary" in payload and isinstance(payload["summary"], dict):
            return "summary_report"
    if isinstance(payload, list):
        return "json_array"
    return f"json:{path.suffix.lstrip('.') or 'unknown'}"


def first_string(payload: dict[str, Any], keys: Sequence[str]) -> str | None:
    for key in keys:
        value = payload.get(key)
        if isinstance(value, str) and value:
            return value
        if isinstance(value, int) and not isinstance(value, bool):
            return str(value)
    return None


def int_value(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    return None


def summarize_numeric_fields(
    payload: dict[str, Any], keys: Sequence[str]
) -> dict[str, int]:
    result: dict[str, int] = {}
    for key in keys:
        value = int_value(payload.get(key))
        if value is not None:
            result[key] = value
    return result


def summarize_research_lock(payload: dict[str, Any]) -> dict[str, int]:
    components = payload.get("components")
    artifact_schemas = payload.get("artifact_schemas")
    artifact_registry = payload.get("artifact_registry")
    artifact_registry_entries = (
        artifact_registry.get("entries")
        if isinstance(artifact_registry, dict)
        else None
    )
    issues = payload.get("issues")
    return {
        "components": len(components) if isinstance(components, list) else 0,
        "artifact_schemas": len(artifact_schemas)
        if isinstance(artifact_schemas, dict)
        else 0,
        "artifact_registry_entries": len(artifact_registry_entries)
        if isinstance(artifact_registry_entries, list)
        else 0,
        "issues": len(issues) if isinstance(issues, list) else 0,
    }


def summarize_queue(payload: dict[str, Any]) -> tuple[dict[str, int], dict[str, int]]:
    queue = payload.get("queue")
    if not isinstance(queue, list):
        return {}, {}

    totals = {"queue": len(queue)}
    status_counts: Counter[str] = Counter()
    for entry in queue:
        if not isinstance(entry, dict):
            continue
        labels = entry.get("labels")
        label_set = (
            {str(label) for label in labels} if isinstance(labels, list) else set()
        )
        if entry.get("claimed") is True:
            status_counts["claimed"] += 1
        else:
            status_counts["unclaimed"] += 1
        if entry.get("tracking") is True or "tracking" in label_set:
            status_counts["tracking"] += 1
        if "blocked" in label_set:
            status_counts["blocked"] += 1
        if "in-progress" in label_set:
            status_counts["in_progress"] += 1

    return totals, dict(sorted(status_counts.items()))


def summarize_conjectures(payload: dict[str, Any]) -> dict[str, int]:
    conjectures = payload.get("conjectures")
    if not isinstance(conjectures, dict):
        return {}

    totals = {"conjectures": len(conjectures)}
    for total_key in (
        "axioms",
        "theorems",
        "definitions",
        "opaques",
        "sorry_inhabit_pi_sites",
    ):
        total = 0
        seen = False
        for entry in conjectures.values():
            if isinstance(entry, dict):
                value = int_value(entry.get(total_key))
                if value is None:
                    value = int_value(entry.get(f"{total_key[:-1]}_count"))
                if value is not None:
                    total += value
                    seen = True
        if seen:
            totals[total_key] = total
    return totals


def summarize_status_report(payload: dict[str, Any]) -> dict[str, int]:
    summary = payload.get("summary")
    if not isinstance(summary, dict):
        return {}
    return {
        key: value
        for key, value in sorted(summary.items())
        if isinstance(key, str) and int_value(value) is not None
    }


def summarize_research_status_report(payload: dict[str, Any]) -> dict[str, int]:
    totals = summarize_numeric_fields(payload, ("total_entries",))
    registries = payload.get("registries")
    if not isinstance(registries, dict):
        return totals

    registry_totals = (
        ("proof_library", "total_proofs"),
        ("sat_frontier", "total_entries"),
        ("gamma_crown", "total_conjectures"),
    )
    for registry_key, total_key in registry_totals:
        registry = registries.get(registry_key)
        if not isinstance(registry, dict):
            continue
        value = int_value(registry.get(total_key))
        if value is not None:
            totals[f"{registry_key}.{total_key}"] = value
    return totals


def manifest_items(payload: dict[str, Any]) -> list[dict[str, Any]]:
    items = payload.get("items")
    if not isinstance(items, list):
        return []
    return [item for item in items if isinstance(item, dict)]


def count_by_key(items: Sequence[dict[str, Any]], key: str) -> dict[str, int]:
    counts: Counter[str] = Counter()
    for item in items:
        value = item.get(key)
        if isinstance(value, str) and value:
            counts[value] += 1
    return dict(sorted(counts.items()))


def summarize_research_program_manifest(
    payload: dict[str, Any],
) -> tuple[dict[str, int], dict[str, int], dict[str, dict[str, int]]]:
    items = manifest_items(payload)
    totals = {
        "items": len(items),
        "dependencies": 0,
        "evidence_refs": 0,
        "references": 0,
        "tags": 0,
    }
    for item in items:
        for source_key, total_key in (
            ("dependencies", "dependencies"),
            ("evidence", "evidence_refs"),
            ("references", "references"),
            ("tags", "tags"),
        ):
            value = item.get(source_key)
            if isinstance(value, list):
                totals[total_key] += len(value)

    detail_counts = {
        "domain_counts": count_by_key(items, "domain"),
        "family_counts": count_by_key(items, "family"),
        "artifact_state_counts": count_by_key(items, "artifact_state"),
        "promotion_gate_counts": count_by_key(items, "promotion_gate"),
    }
    return totals, count_by_key(items, "status"), detail_counts


def copy_int_counts(value: Any) -> dict[str, int]:
    if not isinstance(value, dict):
        return {}
    return {
        key: count
        for key, count in sorted(value.items())
        if isinstance(key, str) and int_value(count) is not None
    }


def artifact_ids_from_value(value: Any) -> list[str]:
    if isinstance(value, str) and value:
        return [value]
    if isinstance(value, list):
        return [item for item in value if isinstance(item, str) and item]
    return []


def collect_artifact_ids(payload: Any) -> list[str]:
    artifact_ids: set[str] = set()

    def visit(value: Any) -> None:
        if isinstance(value, dict):
            for key, child in value.items():
                if key in {"artifact_id", "artifact_ids"}:
                    artifact_ids.update(artifact_ids_from_value(child))
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)

    visit(payload)
    return sorted(artifact_ids)


def collect_local_issue_refs(value: Any) -> list[int]:
    refs: set[int] = set()
    if isinstance(value, dict):
        for key in ("issue", "issue_number"):
            issue = int_value(value.get(key))
            if issue is not None:
                refs.add(issue)
        issues = value.get("issues")
        if isinstance(issues, list):
            for issue in issues:
                parsed = int_value(issue)
                if parsed is not None:
                    refs.add(parsed)
        links = value.get("links")
        if isinstance(links, dict):
            refs.update(collect_local_issue_refs(links))
        references = value.get("references")
        if isinstance(references, list):
            for reference in references:
                if isinstance(reference, str):
                    for match in ISSUE_REF_RE.finditer(reference):
                        refs.add(int(match.group(1) or match.group(2)))
    return sorted(refs)


def collect_issue_refs(value: Any) -> list[int]:
    refs: set[int] = set()

    def visit(child: Any) -> None:
        if isinstance(child, dict):
            refs.update(collect_local_issue_refs(child))
            for nested in child.values():
                visit(nested)
        elif isinstance(child, list):
            for nested in child:
                visit(nested)

    visit(value)
    return sorted(refs)


def local_dashboard_anchor(value: Any) -> str | None:
    if not isinstance(value, dict):
        return None
    direct = value.get("dashboard_anchor")
    if isinstance(direct, str) and direct.strip():
        return direct
    links = value.get("links")
    if isinstance(links, dict):
        anchor = links.get("dashboard_anchor")
        if isinstance(anchor, str) and anchor.strip():
            return anchor
    return None


def collect_artifact_links(payload: Any, source_path: Path) -> list[dict[str, Any]]:
    links: list[dict[str, Any]] = []
    seen: set[tuple[str, int | None, str | None, str]] = set()
    source = display_path(source_path)

    def append_link(
        artifact_id: str,
        issue: int | None,
        dashboard_anchor: str | None,
    ) -> None:
        if dashboard_anchor is None and any(
            existing_artifact_id == artifact_id
            and existing_issue == issue
            and existing_anchor is not None
            and existing_source == source
            for existing_artifact_id, existing_issue, existing_anchor, existing_source in seen
        ):
            return
        if dashboard_anchor is not None:
            unanchored_key = (artifact_id, issue, None, source)
            if unanchored_key in seen:
                seen.remove(unanchored_key)
                links[:] = [
                    link
                    for link in links
                    if not (
                        link["artifact_id"] == artifact_id
                        and int_value(link.get("issue")) == issue
                        and link.get("source") == source
                        and "dashboard_anchor" not in link
                    )
                ]
        key = (artifact_id, issue, dashboard_anchor, source)
        if key in seen:
            return
        seen.add(key)
        link: dict[str, Any] = {"artifact_id": artifact_id, "source": source}
        if issue is not None:
            link["issue"] = issue
        if dashboard_anchor is not None:
            link["dashboard_anchor"] = dashboard_anchor
        links.append(link)

    def visit(
        value: Any,
        inherited_issue_refs: Sequence[int] = (),
        inherited_dashboard_anchor: str | None = None,
    ) -> None:
        if isinstance(value, dict):
            local_issue_refs = collect_local_issue_refs(value)
            active_issue_refs = local_issue_refs or list(inherited_issue_refs)
            active_dashboard_anchor = (
                local_dashboard_anchor(value) or inherited_dashboard_anchor
            )
            local_artifact_ids: set[str] = set()
            for key in ("artifact_id", "artifact_ids"):
                local_artifact_ids.update(artifact_ids_from_value(value.get(key)))
            if local_artifact_ids:
                issue_refs = active_issue_refs or [None]
                for artifact_id in sorted(local_artifact_ids):
                    for issue in issue_refs:
                        append_link(artifact_id, issue, active_dashboard_anchor)
            for child in value.values():
                visit(child, active_issue_refs, active_dashboard_anchor)
        elif isinstance(value, list):
            for child in value:
                visit(child, inherited_issue_refs, inherited_dashboard_anchor)

    visit(payload)
    return links


def summarize_payload(payload: Any, path: Path) -> dict[str, Any]:
    kind = detect_kind(payload, path)
    title = path.stem
    version: str | None = None
    updated_at: str | None = None
    status: str | None = None
    totals: dict[str, int] = {}
    status_counts: dict[str, int] = {}
    detail_counts: dict[str, dict[str, int]] = {}
    artifact_ids = collect_artifact_ids(payload)

    if isinstance(payload, dict):
        title = first_string(payload, ("title", "lock_id", "name")) or title
        version = first_string(
            payload, ("version", "schema_version", "manifest_version")
        )
        updated_at = first_string(
            payload, ("generated_at", "generated", "last_updated", "release_date")
        )
        status = first_string(payload, ("status", "state"))

        if kind == "research_program_lock":
            totals.update(summarize_research_lock(payload))
        elif kind == "research_program_manifest":
            manifest_totals, manifest_status, manifest_details = (
                summarize_research_program_manifest(payload)
            )
            totals.update(manifest_totals)
            status_counts.update(manifest_status)
            detail_counts.update(manifest_details)
        elif kind == "research_status_report":
            totals.update(summarize_research_status_report(payload))
            status_counts.update(copy_int_counts(payload.get("status_counts")))
        elif kind == "proof_queue":
            queue_totals, queue_status = summarize_queue(payload)
            totals.update(queue_totals)
            status_counts.update(queue_status)
        elif kind == "axiom_audit":
            totals.update(
                summarize_numeric_fields(
                    payload,
                    (
                        "total_domain_axioms",
                        "total_all_axioms",
                        "total_theorems",
                        "constructive_theorems",
                    ),
                )
            )
            totals.update(summarize_conjectures(payload))
        elif kind == "conjecture_report":
            totals.update(summarize_conjectures(payload))
        elif kind == "mathverse_provenance":
            totals.update(
                summarize_numeric_fields(
                    payload,
                    (
                        "census_target_repos",
                        "importer_source_systems",
                        "provenance_records",
                        "shards_produced",
                        "total_declarations",
                    ),
                )
            )
        elif kind == "mathverse_summary":
            totals.update(
                summarize_numeric_fields(
                    payload,
                    (
                        "source_systems",
                        "mathverse_shards_lean4",
                        "metamath_rpn_verified_total",
                        "sources_total",
                        "sources_failed",
                    ),
                )
            )
        elif kind in {"status_report", "summary_report"}:
            status_counts.update(summarize_status_report(payload))

        if "summary" in payload and not status_counts:
            status_counts.update(summarize_status_report(payload))
    elif isinstance(payload, list):
        totals["items"] = len(payload)

    return {
        "path": display_path(path),
        "kind": kind,
        "title": title,
        "version": version,
        "updated_at": updated_at,
        "status": status,
        "totals": totals,
        "status_counts": status_counts,
        "detail_counts": detail_counts,
        "artifact_ids": artifact_ids,
    }


def build_dashboard(
    paths: Sequence[Path],
    *,
    generated_at: str | None = None,
    title: str = DEFAULT_TITLE,
) -> dict[str, Any]:
    payloads = [(path, load_json(path)) for path in paths]
    inputs = [summarize_payload(payload, path) for path, payload in payloads]
    kinds = Counter(item["kind"] for item in inputs)
    issue_refs: set[int] = set()
    artifact_ids: set[str] = set()
    artifact_links: list[dict[str, Any]] = []
    seen_artifact_links: set[tuple[str, int | None, str]] = set()

    for path, payload in payloads:
        artifact_ids.update(collect_artifact_ids(payload))
        issue_refs.update(collect_issue_refs(payload))
        for link in collect_artifact_links(payload, path):
            key = (
                str(link["artifact_id"]),
                int_value(link.get("issue")),
                str(link.get("dashboard_anchor")),
                str(link["source"]),
            )
            if key not in seen_artifact_links:
                seen_artifact_links.add(key)
                artifact_links.append(link)

    return {
        "schema_version": DASHBOARD_SCHEMA_VERSION,
        "manifest_kind": "research_dashboard",
        "title": title,
        "generated_at": generated_at or utc_now(),
        "inputs": inputs,
        "summary": {
            "input_count": len(inputs),
            "by_kind": dict(sorted(kinds.items())),
            "issue_refs": sorted(issue_refs),
            "artifact_ids": sorted(artifact_ids),
            "artifact_links": sorted(
                artifact_links,
                key=lambda link: (
                    int_value(link.get("issue")) is None,
                    int_value(link.get("issue")) or 0,
                    str(link["artifact_id"]),
                    str(link.get("dashboard_anchor", "")),
                    str(link["source"]),
                ),
            ),
        },
    }


def validate_dashboard_freshness(
    dashboard: dict[str, Any],
    *,
    max_age_days: int,
    reference_at: datetime,
) -> list[str]:
    findings: list[str] = []
    reference_at = reference_at.astimezone(timezone.utc)
    max_age_seconds = max_age_days * 24 * 60 * 60

    for item in dashboard.get("inputs", []):
        if not isinstance(item, dict):
            continue
        path = str(item.get("path", "<unknown>"))
        updated_at = item.get("updated_at")
        if not isinstance(updated_at, str) or not updated_at.strip():
            findings.append(f"{path}: missing updated_at/generated_at metadata")
            continue
        try:
            updated = parse_timestamp(updated_at)
        except ValueError as exc:
            findings.append(f"{path}: invalid updated_at '{updated_at}': {exc}")
            continue
        age_seconds = (reference_at - updated).total_seconds()
        if age_seconds < 0:
            findings.append(
                f"{path}: updated_at {updated_at} is after freshness reference "
                f"{reference_at.strftime('%Y-%m-%dT%H:%M:%SZ')}"
            )
        elif age_seconds > max_age_seconds:
            age_days = int(age_seconds // (24 * 60 * 60))
            findings.append(
                f"{path}: updated_at {updated_at} is {age_days} day(s) old "
                f"(max {max_age_days})"
            )

    return findings


def compact_pairs(values: dict[str, int], *, limit: int = 6) -> str:
    if not values:
        return "-"
    parts = [f"{key}={values[key]}" for key in sorted(values)]
    if len(parts) > limit:
        parts = parts[:limit] + [f"+{len(values) - limit} more"]
    return ", ".join(parts)


def md_escape(value: Any) -> str:
    if value is None:
        return "-"
    text = str(value).replace("\n", " ")
    return text.replace("|", "\\|")


def compact_list(values: Sequence[Any], *, limit: int = 6) -> str:
    if not values:
        return "-"
    parts = [str(value) for value in values]
    if len(parts) > limit:
        parts = parts[:limit] + [f"+{len(values) - limit} more"]
    return ", ".join(parts)


def render_markdown(dashboard: dict[str, Any]) -> str:
    lines = [
        f"# {dashboard['title']}",
        "",
        f"Generated: `{dashboard['generated_at']}`",
        "",
        "| Input | Kind | Version | Updated | Totals | Status | Artifact IDs |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    lines.extend(
        (
            (
                "| {path} | {kind} | {version} | {updated} | "
                "{totals} | {status} | {artifact_ids} |"
            ).format(
                path=md_escape(item["path"]),
                kind=md_escape(item["kind"]),
                version=md_escape(item.get("version")),
                updated=md_escape(item.get("updated_at")),
                totals=md_escape(compact_pairs(item.get("totals", {}))),
                status=md_escape(
                    item.get("status") or compact_pairs(item.get("status_counts", {}))
                ),
                artifact_ids=md_escape(compact_list(item.get("artifact_ids", []))),
            )
        )
        for item in dashboard["inputs"]
    )
    lines.extend(
        [
            "",
            "## Summary",
            "",
            f"- Inputs: `{dashboard['summary']['input_count']}`",
            f"- Kinds: `{compact_pairs(dashboard['summary']['by_kind'], limit=10)}`",
        ]
    )
    issue_refs = dashboard["summary"].get("issue_refs", [])
    if issue_refs:
        lines.append("- Issue refs: " + ", ".join(f"#{issue}" for issue in issue_refs))
    artifact_ids = dashboard["summary"].get("artifact_ids", [])
    if artifact_ids:
        lines.append("- Artifact IDs: `" + compact_list(artifact_ids, limit=10) + "`")
    artifact_links = dashboard["summary"].get("artifact_links", [])
    if artifact_links:
        rendered_links = []
        for link in artifact_links[:10]:
            issue = int_value(link.get("issue"))
            artifact_id = str(link["artifact_id"])
            anchor = link.get("dashboard_anchor")
            anchor_suffix = (
                f" @ `{anchor}`" if isinstance(anchor, str) and anchor else ""
            )
            if issue is not None:
                rendered_links.append(f"#{issue} -> `{artifact_id}`{anchor_suffix}")
            else:
                rendered_links.append(f"`{artifact_id}`{anchor_suffix}")
        if len(artifact_links) > 10:
            rendered_links.append(f"+{len(artifact_links) - 10} more")
        lines.append("- Artifact issue links: " + ", ".join(rendered_links))
    return "\n".join(lines) + "\n"


def write_output(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def run_self_check() -> None:
    with tempfile.TemporaryDirectory() as temp_dir:
        root = Path(temp_dir)
        lock_path = root / "lock.json"
        queue_path = root / "queue.json"
        lock_path.write_text(
            json.dumps(
                {
                    "schema_version": 1,
                    "manifest_kind": "research_program_lock",
                    "lock_id": "self-check-lock",
                    "generated_at": "2026-04-23T00:00:00Z",
                    "issues": [3686, 3690],
                    "components": [{"id": "clean"}, {"id": "mathverse"}],
                    "artifact_schemas": {"proof_artifact_manifest_v1": {}},
                }
            ),
            encoding="utf-8",
        )
        queue_path.write_text(
            json.dumps(
                {
                    "generated_at": "2026-04-23T00:00:00Z",
                    "queue": [
                        {"issue": 1, "labels": ["blocked"], "claimed": False},
                        {"issue": 2, "labels": ["tracking"], "claimed": True},
                    ],
                }
            ),
            encoding="utf-8",
        )

        dashboard = build_dashboard(
            [lock_path, queue_path],
            generated_at="2026-04-23T00:00:00Z",
            title="Self Check",
        )
        assert dashboard["summary"]["input_count"] == 2
        assert dashboard["summary"]["by_kind"]["research_program_lock"] == 1
        assert dashboard["summary"]["by_kind"]["proof_queue"] == 1
        assert dashboard["summary"]["issue_refs"] == [1, 2, 3686, 3690]
        markdown = render_markdown(dashboard)
        assert "Self Check" in markdown
        assert "blocked=1" in markdown


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate a compact JSON or Markdown dashboard from research manifests."
    )
    parser.add_argument(
        "inputs", nargs="*", type=Path, help="JSON manifest/report inputs"
    )
    parser.add_argument(
        "--default-inputs",
        action="store_true",
        help="use the standard research dashboard input set",
    )
    parser.add_argument(
        "--format",
        choices=("json", "markdown"),
        default="json",
        help="stdout/output format",
    )
    parser.add_argument(
        "--output", type=Path, help="write selected format to this path"
    )
    parser.add_argument("--json-output", type=Path, help="also write JSON dashboard")
    parser.add_argument(
        "--markdown-output", type=Path, help="also write Markdown dashboard"
    )
    parser.add_argument(
        "--generated-at", help="override generated_at for reproducible output"
    )
    parser.add_argument(
        "--deterministic",
        action="store_true",
        help=("use a stable generated_at value when --generated-at is omitted"),
    )
    parser.add_argument(
        "--max-input-age-days",
        type=int,
        help="fail if any input updated_at/generated_at is older than this many days",
    )
    parser.add_argument(
        "--freshness-reference-at",
        help="ISO-8601 timestamp used by --max-input-age-days (defaults to now)",
    )
    parser.add_argument("--title", default=DEFAULT_TITLE, help="dashboard title")
    parser.add_argument(
        "--self-check", action="store_true", help="run built-in smoke test"
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)

    if args.self_check:
        run_self_check()
        print("research_dashboard self-check: ok")
        if not args.inputs and not args.default_inputs:
            return 0

    inputs = list(DEFAULT_INPUTS if args.default_inputs else ()) + list(args.inputs)
    generated_at = args.generated_at
    if generated_at is None and args.deterministic:
        generated_at = DETERMINISTIC_GENERATED_AT

    if not inputs:
        print(
            "ERROR: provide at least one JSON input, use --default-inputs, "
            "or use --self-check",
            file=sys.stderr,
        )
        return 2

    if args.max_input_age_days is not None and args.max_input_age_days < 0:
        print("ERROR: --max-input-age-days must be non-negative", file=sys.stderr)
        return 2

    try:
        dashboard = build_dashboard(inputs, generated_at=generated_at, title=args.title)
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    if args.max_input_age_days is not None:
        try:
            reference_at = (
                parse_timestamp(args.freshness_reference_at)
                if args.freshness_reference_at
                else datetime.now(timezone.utc)
            )
        except ValueError as exc:
            print(f"ERROR: invalid --freshness-reference-at: {exc}", file=sys.stderr)
            return 2
        findings = validate_dashboard_freshness(
            dashboard,
            max_age_days=args.max_input_age_days,
            reference_at=reference_at,
        )
        if findings:
            for finding in findings:
                print(f"ERROR: stale dashboard input: {finding}", file=sys.stderr)
            return 1

    json_text = json.dumps(dashboard, indent=2, sort_keys=True) + "\n"
    markdown_text = render_markdown(dashboard)

    if args.json_output:
        write_output(args.json_output, json_text)
    if args.markdown_output:
        write_output(args.markdown_output, markdown_text)

    selected_text = markdown_text if args.format == "markdown" else json_text
    if args.output:
        write_output(args.output, selected_text)
    else:
        print(selected_text, end="")

    return 0


if __name__ == "__main__":
    sys.exit(main())
