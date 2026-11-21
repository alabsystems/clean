#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail
ANSWERS_PINNED_INPUTS=True
if [[ "${1:-}" == --pinned-inputs ]]; then
  printf '%s\n' scripts/cargo_test_nonvacuous.sh scripts/kcheck_coverage_export.py scripts/self_proof_fleet_w0.py
  exit 0
fi
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
cd "$(git rev-parse --show-toplevel)"
root="$(pwd -P)"
python="$1"
driver="$2"
if [[ "${3:-}" != targo ]]; then
  echo "W0_ARTIFACT=invalid expected a Targo command" >&2
  exit 2
fi
shift 3
revision="$(git rev-parse --verify 'HEAD^{commit}')"
scratch="$(mktemp -d "${TMPDIR:-/tmp}/w0-gate.XXXXXX")"
trap 'rm -rf -- "$scratch"' EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
fail() { echo "$1" >&2; exit 1; }
record_build() {
  if [[ -n "${CLEAN_W0_GATE_RESULT:-}" ]]; then
    "$python" -B "$script_dir/self_proof_fleet_w0.py" "$script_dir/${BASH_SOURCE[0]##*/}" "$root" "$revision" "$scratch" "$@" || exit 1
  fi
}
record_build
cargo_status=0
scripts/cargo_test_nonvacuous.sh w0-evidence -- "$driver" "$@" > "$scratch/cargo.log" || cargo_status=$?
if [[ "$cargo_status" != 0 ]]; then
  cat "$scratch/cargo.log" || true
  exit "$cargo_status"
fi
awk 'substr($0, 1, 1) != "{"' "$scratch/cargo.log" || exit 1
# Only this invocation's artifact events can select an executable.
artifact_paths() {
  "$python" -B - "$scratch/cargo.log" "$root" "$CARGO_TARGET_DIR" "$script_dir" <<'PY'
import json
import os
from pathlib import Path
import sys

sys.path.insert(0, sys.argv[4])
from kcheck_coverage_export import Refused, once
from self_proof_fleet_w0 import executable_digest


def require(test, message):
    if not test:
        raise ValueError(message)


def outputs(row):
    return [*row["filenames"], row.get("executable")]


try:
    log, root, directory = map(Path, sys.argv[1:4])
    target_dir = directory.resolve(strict=True)
    crate = root / "crates/clean"
    with log.open("rb") as stream:
        events = [json.loads(line, object_pairs_hook=once)
                  for line in stream if line.startswith(b"{")]
    finished = [event for event in events if event["reason"] == "build-finished"]
    require(len(finished) == 1 and finished[0]["success"] is True,
            "expected one successful Cargo build")
    artifacts = [event for event in events if event["reason"] == "compiler-artifact"]
    for name, kind, test, source in (
        ("w0_scoreboard_cli", "test", True, crate / "tests/w0_scoreboard_cli.rs"),
        ("clean", "bin", False, crate / "src/bin/clean.rs"),
    ):
        matches = [row for row in artifacts
                   if row["manifest_path"] == str(crate / "Cargo.toml")
                   and row["target"]["name"] == name and row["target"]["kind"] == [kind]
                   and row["profile"]["test"] is test]
        require(len(matches) == 1, f"expected one Cargo artifact for {name}")
        row = matches[0]
        require(row["package_id"].split("#", 1)[0] == f"path+{crate.as_uri()}"
                and row["target"]["crate_types"] == ["bin"]
                and row["target"]["src_path"] == str(source),
                f"wrong Cargo owner or source for {name}")
        path = Path(row["executable"])
        resolved = path.resolve(strict=True)
        require(path.is_absolute() and resolved.is_relative_to(target_dir)
                and not any(char in str(resolved) for char in "\r\n")
                and path.is_file() and not path.is_symlink() and os.access(path, os.X_OK)
                and row["executable"] in row["filenames"],
                f"invalid executable path for {name}")
        if test:
            require(resolved.name.startswith(name + "-"), "wrong fixed test executable name")
        else:
            require(resolved == target_dir / "debug/clean", "wrong normal Clean executable path")
        require(all(other is row or all(Path(output).resolve() != resolved
                    for output in outputs(other) if output) for other in artifacts),
                f"multiple Cargo owners for {name}")
        require(executable_digest(resolved) == row["trust_executable_sha256"],
                f"executable digest differs from Targo artifact for {name}")
        if not test and os.environ.get("CLEAN_W0_GATE_RESULT"):
            (log.parent / "gate-artifact.json").write_text(
                json.dumps({"executable": str(resolved), "cargo_artifact": row}), encoding="utf-8")
        print(resolved)
except (OSError, TypeError, ValueError, KeyError, Refused) as error:
    sys.exit(f"W0_ARTIFACT=invalid {error}")
PY
}

check_source() {
  [[ "$(git rev-parse --verify 'HEAD^{commit}')" == "$revision" ]] ||
    fail "W0_ARTIFACT=invalid checkout HEAD changed"
}

artifact_paths > "$scratch/paths" || exit 1
{
  IFS= read -r fixed && IFS= read -r clean
} < "$scratch/paths" || exit 1
check_source
if ! version="$("$clean" --version 2> "$scratch/stderr")"; then
  cat "$scratch/stderr" >&2
  fail "W0_ARTIFACT=invalid Clean version command failed"
fi
if [[ ! "$version" =~ ^clean\ [^[:space:]+]+\+g${revision}$ || -s "$scratch/stderr" ]]; then
  cat "$scratch/stderr" >&2
  fail "W0_ARTIFACT=invalid Clean version differs from the checkout: $version"
fi

(
  cd "$root/crates/clean" || exit 1
  RUST_MIN_STACK="${RUST_MIN_STACK-67108864}" \
    "$root/scripts/cargo_test_nonvacuous.sh" w0-fixed -- "$fixed" --exact w0_scoreboard_self_test --color never
) || exit "$?"
board_status=0
"$clean" evidence status --scoreboard --check --repo-root "$root" \
  > "$scratch/board" 2> "$scratch/stderr" || board_status=$?
cat "$scratch/board"
cat "$scratch/stderr" >&2
if [[ "$board_status" != 0 || -s "$scratch/stderr" ]] ||
   ! cmp -s <(printf 'SELF_PROOF_SCOREBOARD=ok the record matches its sources\n') "$scratch/board"; then
  fail "W0_SAVED_BOARD=invalid native check did not pass"
fi

artifact_paths > "$scratch/after" || exit 1
cmp "$scratch/paths" "$scratch/after" || exit 1
check_source
record_build "$version"
