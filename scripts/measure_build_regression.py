#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import argparse
import json
import shlex
from collections import defaultdict
from dataclasses import dataclass
from datetime import UTC, datetime, timedelta
from pathlib import Path
from typing import Any

TARGET_CRATES = ("clean-lake", "clean-olean", "clean-auto")


@dataclass(frozen=True)
class BuildEvent:
    ts: datetime
    crate: str
    profile: str
    duration_sec: float
    cmd: str


def parse_timestamp(raw: str) -> datetime:
    value = raw.strip()
    if value.endswith("Z"):
        value = f"{value[:-1]}+00:00"
    parsed = datetime.fromisoformat(value)
    if parsed.tzinfo is None:
        return parsed.replace(tzinfo=UTC)
    return parsed.astimezone(UTC)


def load_anchor_timestamp(metrics_latest: Path) -> datetime:
    data = json.loads(metrics_latest.read_text(encoding="utf-8"))
    timestamp = data.get("timestamp")
    if not isinstance(timestamp, str) or not timestamp:
        raise ValueError(f"missing timestamp in {metrics_latest}")
    return parse_timestamp(timestamp)


def extract_cargo_args(cmd: str) -> list[str]:
    try:
        parts = shlex.split(cmd)
    except ValueError:
        return []
    if not parts:
        return []
    for idx, part in enumerate(parts):
        if part.endswith("cargo") or part == "cargo":
            return parts[idx + 1 :]
    return parts


def is_test_write_command(cmd: str) -> bool:
    args = extract_cargo_args(cmd)
    return any(arg == "test_write" or arg.startswith("test_write") for arg in args)


def iter_target_events(timeline_path: Path) -> list[BuildEvent]:
    events: list[BuildEvent] = []
    with timeline_path.open(encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                entry = json.loads(line)
            except json.JSONDecodeError:
                continue

            if entry.get("event") != "stop":
                continue
            kind = str(entry.get("kind", ""))
            if not kind.startswith("cargo"):
                continue

            crate = str(entry.get("crate", ""))
            if crate not in TARGET_CRATES:
                continue

            duration_raw = entry.get("duration_sec")
            if not isinstance(duration_raw, (int, float)):
                continue
            duration_sec = float(duration_raw)
            if duration_sec <= 0:
                continue

            ts_raw = entry.get("ts")
            if not isinstance(ts_raw, str) or not ts_raw:
                continue

            cmd = str(entry.get("cmd", ""))
            profile = str(entry.get("profile", "debug")) or "debug"

            try:
                ts = parse_timestamp(ts_raw)
            except ValueError:
                continue

            events.append(
                BuildEvent(
                    ts=ts,
                    crate=crate,
                    profile=profile,
                    duration_sec=duration_sec,
                    cmd=cmd,
                )
            )

    return events


def average(values: list[float]) -> float | None:
    if not values:
        return None
    return sum(values) / len(values)


def delta_pct(current: float | None, previous: float | None) -> float | None:
    if current is None or previous is None or previous <= 0:
        return None
    return ((current - previous) / previous) * 100.0


def summarize(events: list[BuildEvent], now: datetime, hours: int) -> dict[str, Any]:
    recent_start = now - timedelta(hours=hours)
    baseline_start = now - timedelta(hours=hours * 2)

    summary: dict[str, dict[str, list[float]]] = defaultdict(
        lambda: {
            "recent": [],
            "baseline": [],
            "recent_test_write": [],
            "baseline_test_write": [],
        }
    )

    recent_events: list[BuildEvent] = []

    for event in events:
        if event.ts < baseline_start or event.ts > now:
            continue

        if event.ts >= recent_start:
            bucket = "recent"
            recent_events.append(event)
        else:
            bucket = "baseline"

        crate_data = summary[event.crate]
        crate_data[bucket].append(event.duration_sec)
        if is_test_write_command(event.cmd):
            crate_data[f"{bucket}_test_write"].append(event.duration_sec)

    crate_rows: list[dict[str, Any]] = []
    for crate in TARGET_CRATES:
        crate_data = summary[crate]
        recent_avg = average(crate_data["recent"])
        baseline_avg = average(crate_data["baseline"])
        recent_delta_pct = delta_pct(recent_avg, baseline_avg)
        recent_test_write_avg = average(crate_data["recent_test_write"])
        baseline_test_write_avg = average(crate_data["baseline_test_write"])
        crate_rows.append(
            {
                "crate": crate,
                "recent_count": len(crate_data["recent"]),
                "baseline_count": len(crate_data["baseline"]),
                "recent_avg_sec": round(recent_avg, 2)
                if recent_avg is not None
                else None,
                "baseline_avg_sec": round(baseline_avg, 2)
                if baseline_avg is not None
                else None,
                "delta_pct": round(recent_delta_pct, 1)
                if recent_delta_pct is not None
                else None,
                "recent_test_write_count": len(crate_data["recent_test_write"]),
                "baseline_test_write_count": len(crate_data["baseline_test_write"]),
                "recent_test_write_avg_sec": round(recent_test_write_avg, 2)
                if recent_test_write_avg is not None
                else None,
                "baseline_test_write_avg_sec": round(baseline_test_write_avg, 2)
                if baseline_test_write_avg is not None
                else None,
            }
        )

    top_recent = sorted(
        recent_events,
        key=lambda e: (-e.duration_sec, e.crate, e.ts.isoformat(), e.cmd),
    )[:10]
    top_rows = [
        {
            "crate": event.crate,
            "duration_sec": round(event.duration_sec, 2),
            "ts": event.ts.isoformat(),
            "cmd": event.cmd,
        }
        for event in top_recent
    ]

    return {
        "anchor": now.isoformat(),
        "window_hours": hours,
        "crates": crate_rows,
        "top_recent_events": top_rows,
    }


def print_table(summary: dict[str, Any]) -> None:
    print(f"Anchor: {summary['anchor']}")
    print(
        f"Window: recent={summary['window_hours']}h baseline={summary['window_hours']}h prior"
    )
    print()
    print(
        "crate         recent avg  baseline avg  delta%   recent n  base n  recent test_write n"
    )
    for row in summary["crates"]:
        recent_avg = (
            f"{row['recent_avg_sec']:.2f}s"
            if isinstance(row["recent_avg_sec"], float)
            else "n/a"
        )
        baseline_avg = (
            f"{row['baseline_avg_sec']:.2f}s"
            if isinstance(row["baseline_avg_sec"], float)
            else "n/a"
        )
        delta = (
            f"{row['delta_pct']:+.1f}%"
            if isinstance(row["delta_pct"], float)
            else "n/a"
        )
        print(
            f"{row['crate']:<12} {recent_avg:>10}  {baseline_avg:>12}  {delta:>7}"
            f"  {row['recent_count']:>8}  {row['baseline_count']:>6}"
            f"  {row['recent_test_write_count']:>19}"
        )

    print()
    print("Top recent events:")
    for event in summary["top_recent_events"]:
        print(
            f"- {event['crate']}: {event['duration_sec']}s @ {event['ts']} :: {event['cmd']}"
        )


def format_json_summary(summary: dict[str, Any]) -> str:
    return json.dumps(summary, indent=2, sort_keys=True)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Measure #1412 build regressions from timeline telemetry."
    )
    parser.add_argument(
        "--metrics-dir",
        type=Path,
        default=Path("metrics"),
        help="Metrics directory containing latest.json and timeline.jsonl (default: metrics)",
    )
    parser.add_argument(
        "--window-hours",
        type=int,
        default=24,
        help="Window width in hours for recent/baseline comparison (default: 24)",
    )
    parser.add_argument(
        "--now",
        type=str,
        default=None,
        help="Override anchor timestamp (ISO-8601). Defaults to metrics/latest.json timestamp.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Print JSON instead of table output.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.window_hours <= 0:
        raise ValueError("--window-hours must be positive")

    metrics_latest = args.metrics_dir / "latest.json"
    timeline_path = args.metrics_dir / "timeline.jsonl"

    if not metrics_latest.exists():
        raise FileNotFoundError(f"missing metrics file: {metrics_latest}")
    if not timeline_path.exists():
        raise FileNotFoundError(f"missing timeline file: {timeline_path}")

    anchor = (
        parse_timestamp(args.now) if args.now else load_anchor_timestamp(metrics_latest)
    )
    events = iter_target_events(timeline_path)
    summary = summarize(events, now=anchor, hours=args.window_hours)

    if args.json:
        print(format_json_summary(summary))
    else:
        print_table(summary)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
