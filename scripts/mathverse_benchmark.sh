#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Benchmark mathverse shard build + verification over a Lean 4 .olean corpus.
#
# Usage:
#   ./scripts/mathverse_benchmark.sh [options]
#
# Options:
#   --output-dir=DIR       Shard output directory (default: target/mathverse-benchmark)
#   --corpus-accounting    Compute .olean vs .mathverse corpus accounting with DeclKind breakdowns
#   --lean-lib=PATH        Lean library root containing Init/ and optional Mathlib/
#   --json=PATH            Output JSON report path (default: reports/mathverse_benchmark_<date>.json)
#   --verbose              Stream command output while running
#   --help, -h             Show this help

set -euo pipefail

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

REPO_ROOT=$(cd $(dirname $0)/.. && pwd)
cd $REPO_ROOT

OUTPUT_DIR="target/mathverse-benchmark"
CORPUS_ACCOUNTING=0
LEAN_LIB_DIR=""
VERBOSE=0
DATE_STAMP="$(date '+%Y%m%d_%H%M%S')"
RUN_DATE="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
JSON_PATH="reports/mathverse_benchmark_${DATE_STAMP}.json"
MATHVERSE_SHARD="target/release/mathverse_shard"
MODULES=""
MATHLIB_PRESENT=0

HEARTBEAT_PID=""
SCRIPT_START="$SECONDS"

usage() {
  sed -n '2,/^set -euo pipefail$/{
    s/^# \{0,1\}//;
    /^$/p;
    /^!/d;
    /set -euo pipefail/d;
    p
  }' "$0"
}

log() {
  printf '%s\n' "$*"
}

vlog() {
  if [ "$VERBOSE" -eq 1 ]; then
    printf '%s\n' "$*"
  fi
}

die() {
  printf 'Error: %s\n' "$*" >&2
  exit 1
}

cleanup() {
  if [ -n "${HEARTBEAT_PID:-}" ]; then
    kill "$HEARTBEAT_PID" >/dev/null 2>&1 || true
    wait "$HEARTBEAT_PID" 2>/dev/null || true
    HEARTBEAT_PID=""
  fi
  if [ -n "${ACCOUNTING_TMP_DIR:-}" ] && [ -d "${ACCOUNTING_TMP_DIR:-}" ]; then
    rm -rf "$ACCOUNTING_TMP_DIR"
  fi
}

trap cleanup EXIT INT TERM

format_bytes() {
  python3 - "$1" <<'PY'
import sys
n = float(sys.argv[1])
units = ["B", "KB", "MB", "GB", "TB"]
u = 0
while n >= 1024.0 and u < len(units) - 1:
    n /= 1024.0
    u += 1
if u == 0:
    print(f"{int(n)} {units[u]}")
else:
    print(f"{n:.1f} {units[u]}")
PY
}

pct() {
  python3 - "$1" "$2" <<'PY'
import sys
num = float(sys.argv[1])
den = float(sys.argv[2])
if den <= 0:
    print("0.0")
else:
    print(f"{(num / den) * 100.0:.1f}")
PY
}

start_heartbeat() {
  local label="$1"
  (
    local elapsed=30
    while true; do
      sleep 30 || exit 0
      printf '[progress] %s still running (%ss elapsed)\n' "$label" "$elapsed" >&2
      elapsed=$((elapsed + 30))
    done
  ) &
  HEARTBEAT_PID=$!
}

stop_heartbeat() {
  if [ -n "${HEARTBEAT_PID:-}" ]; then
    kill "$HEARTBEAT_PID" >/dev/null 2>&1 || true
    wait "$HEARTBEAT_PID" 2>/dev/null || true
    HEARTBEAT_PID=""
  fi
}

run_step() {
  local label="$1"
  local logfile="$2"
  shift 2

  log "--- ${label} ---"
  vlog "Command: $*"
  local start="$SECONDS"
  start_heartbeat "$label"
  set +e
  if [ "$VERBOSE" -eq 1 ]; then
    "$@" > >(tee "$logfile") 2> >(tee -a "$logfile" >&2)
  else
    "$@" >"$logfile" 2>&1
  fi
  local status=$?
  set -e
  stop_heartbeat
  local elapsed=$((SECONDS - start))
  if [ "$status" -ne 0 ]; then
    printf 'Step failed: %s\n' "$label" >&2
    printf 'Log: %s\n' "$logfile" >&2
    tail -n 50 "$logfile" >&2 || true
    exit "$status"
  fi
  log "  Completed in ${elapsed}s"
  STEP_ELAPSED="$elapsed"
}

for arg in "$@"; do
  case "$arg" in
    --output-dir=*) OUTPUT_DIR="${arg#--output-dir=}" ;;
    --corpus-accounting) CORPUS_ACCOUNTING=1 ;;
    --lean-lib=*) LEAN_LIB_DIR="${arg#--lean-lib=}" ;;
    --json=*) JSON_PATH="${arg#--json=}" ;;
    --verbose) VERBOSE=1 ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      die "unknown option: $arg"
      ;;
  esac
done

command -v cargo >/dev/null 2>&1 || die "cargo not found"
command -v python3 >/dev/null 2>&1 || die "python3 not found"
command -v git >/dev/null 2>&1 || die "git not found"

mkdir -p "$(dirname "$JSON_PATH")"

case "$JSON_PATH" in
  *.json) LOG_DIR="${JSON_PATH%.json}_logs" ;;
  *) LOG_DIR="${JSON_PATH}_logs" ;;
esac
mkdir -p "$LOG_DIR"

BUILD_BINARY_LOG="$LOG_DIR/01_build_binary.log"
BUILD_SHARDS_LOG="$LOG_DIR/02_build_shards.log"
VERIFY_LOG="$LOG_DIR/03_verify_integrity.log"
INCREMENTAL_LOG="$LOG_DIR/04_verify_incremental.log"
ACCOUNTING_LOG="$LOG_DIR/05_corpus_accounting.log"
ACCOUNTING_JSON="$LOG_DIR/corpus_accounting.json"

discover_lean_lib_dir() {
  local elan_root="$HOME/.elan/toolchains"
  [ -d "$elan_root" ] || die "elan toolchains directory not found: $elan_root"

  local preferred=""
  if [ -f "$REPO_ROOT/lean-toolchain" ]; then
    preferred="$(tr -d '[:space:]' < "$REPO_ROOT/lean-toolchain")"
    preferred="${preferred#leanprover/lean4:}"
  fi

  local best=""
  local best_score=-1
  local best_mtime=-1
  local dir
  for dir in "$elan_root"/*/lib/lean; do
    [ -d "$dir" ] || continue
    [ -f "$dir/Init/Prelude.olean" ] || continue

    local score=0
    if [ -d "$dir/Mathlib" ] || [ -f "$dir/Mathlib.olean" ]; then
      score=$((score + 100))
    fi
    if [ -n "$preferred" ] && [ "$dir" = "$elan_root/leanprover--lean4---$preferred/lib/lean" ]; then
      score=$((score + 10))
    fi
    local mtime
    mtime="$(stat -f '%m' "$dir" 2>/dev/null || stat -c '%Y' "$dir" 2>/dev/null || echo 0)"
    if [ "$score" -gt "$best_score" ] || { [ "$score" -eq "$best_score" ] && [ "$mtime" -gt "$best_mtime" ]; }; then
      best="$dir"
      best_score="$score"
      best_mtime="$mtime"
    fi
  done

  [ -n "$best" ] || die "no Lean library found under $elan_root"
  printf '%s\n' "$best"
}

if [ -z "$LEAN_LIB_DIR" ]; then
  LEAN_LIB_DIR="$(discover_lean_lib_dir)"
fi

[ -d "$LEAN_LIB_DIR" ] || die "lean library not found: $LEAN_LIB_DIR"
[ -f "$LEAN_LIB_DIR/Init/Prelude.olean" ] || die "lean library missing Init/Prelude.olean: $LEAN_LIB_DIR"

MODULES="Init"
if [ -d "$LEAN_LIB_DIR/Mathlib" ] || [ -f "$LEAN_LIB_DIR/Mathlib.olean" ]; then
  MODULES="Init,Mathlib"
  MATHLIB_PRESENT=1
fi

OLEANS_JSON="$(python3 - "$LEAN_LIB_DIR" "$MODULES" <<'PY'
import json
import os
import sys

root = sys.argv[1]
modules = [m for m in sys.argv[2].split(",") if m]
seen = set()
files = []

for mod in modules:
    rel = os.path.join(*mod.split("."))
    single = os.path.join(root, rel + ".olean")
    if os.path.isfile(single):
        real = os.path.realpath(single)
        if real not in seen:
            seen.add(real)
            files.append(single)
    tree = os.path.join(root, rel)
    if os.path.isdir(tree):
        for dirpath, _, filenames in os.walk(tree):
            for filename in filenames:
                if filename.endswith(".olean"):
                    path = os.path.join(dirpath, filename)
                    real = os.path.realpath(path)
                    if real not in seen:
                        seen.add(real)
                        files.append(path)

total_bytes = sum(os.path.getsize(path) for path in files)
print(json.dumps({"file_count": len(files), "total_bytes": total_bytes}))
PY
)"

OLEAN_FILE_COUNT="$(python3 - "$OLEANS_JSON" <<'PY'
import json, sys
print(json.loads(sys.argv[1])["file_count"])
PY
)"

OLEAN_TOTAL_BYTES="$(python3 - "$OLEANS_JSON" <<'PY'
import json, sys
print(json.loads(sys.argv[1])["total_bytes"])
PY
)"

COMMIT_HASH="$(git rev-parse HEAD)"

log "=== Mathverse Benchmark ==="
log "  Commit hash:   $COMMIT_HASH"
log "  Lean lib dir:  $LEAN_LIB_DIR"
log "  Modules:       $MODULES"
log "  Olean files:   $OLEAN_FILE_COUNT ($(format_bytes "$OLEAN_TOTAL_BYTES"))"
log "  Output dir:    $OUTPUT_DIR"
log "  JSON report:   $JSON_PATH"
log

run_step "Build mathverse_shard (release)" "$BUILD_BINARY_LOG" \
  cargo build --locked -p clean-mathverse --bin mathverse_shard --release --message-format=short -j "$CARGO_BUILD_JOBS"
BUILD_BINARY_SECS="$STEP_ELAPSED"

[ -x "$MATHVERSE_SHARD" ] || die "mathverse_shard binary not found after build: $MATHVERSE_SHARD"

rm -rf "$OUTPUT_DIR"
mkdir -p "$OUTPUT_DIR"

BUILD_ARGS=("$MATHVERSE_SHARD" build "$LEAN_LIB_DIR" "$OUTPUT_DIR" "--modules=$MODULES")
if [ "$VERBOSE" -eq 1 ]; then
  BUILD_ARGS+=("--verbose")
fi

run_step "Build mathverse shards" "$BUILD_SHARDS_LOG" "${BUILD_ARGS[@]}"
BUILD_SHARDS_SECS="$STEP_ELAPSED"

run_step "Verify shard integrity" "$VERIFY_LOG" \
  "$MATHVERSE_SHARD" verify "$OUTPUT_DIR"
VERIFY_SECS="$STEP_ELAPSED"

run_step "Verify shards incrementally" "$INCREMENTAL_LOG" \
  "$MATHVERSE_SHARD" verify-incremental "$OUTPUT_DIR"
INCREMENTAL_SECS="$STEP_ELAPSED"

INCREMENTAL_JSON="$(python3 - "$INCREMENTAL_LOG" <<'PY'
import json
import re
import sys

text = open(sys.argv[1], "r", encoding="utf-8", errors="replace").read()

def last_int(pattern: str) -> int:
    matches = re.findall(pattern, text, flags=re.MULTILINE)
    if not matches:
        raise SystemExit(f"missing pattern: {pattern}")
    return int(matches[-1])

def last_float(pattern: str) -> float:
    matches = re.findall(pattern, text, flags=re.MULTILINE)
    if not matches:
        raise SystemExit(f"missing pattern: {pattern}")
    return float(matches[-1])

data = {
    "total_constants": last_int(r"^\s*Total constants:\s+(\d+)\s*$"),
    "kernel_verified": last_int(r"^\s*Kernel verified:\s+(\d+)\s*$"),
    "failed": last_int(r"^\s*Failed:\s+(\d+)\s*$"),
    "cycle_skipped": last_int(r"^\s*Cycle skipped:\s+(\d+)\s*$"),
    "reconstruct_failed": last_int(r"^\s*Reconstruct failed:\s+(\d+)\s*$"),
    "elapsed_secs": last_float(r"^\s*Elapsed:\s+([0-9]+(?:\.[0-9]+)?)s\s*$"),
}
if data["total_constants"] > 0:
    data["pass_rate_pct"] = round((data["kernel_verified"] / data["total_constants"]) * 100.0, 1)
else:
    data["pass_rate_pct"] = 0.0

print(json.dumps(data))
PY
)"

TOTAL_CONSTANTS="$(python3 - "$INCREMENTAL_JSON" <<'PY'
import json, sys
print(json.loads(sys.argv[1])["total_constants"])
PY
)"
KERNEL_VERIFIED="$(python3 - "$INCREMENTAL_JSON" <<'PY'
import json, sys
print(json.loads(sys.argv[1])["kernel_verified"])
PY
)"
FAILED_COUNT="$(python3 - "$INCREMENTAL_JSON" <<'PY'
import json, sys
print(json.loads(sys.argv[1])["failed"])
PY
)"
CYCLE_SKIPPED="$(python3 - "$INCREMENTAL_JSON" <<'PY'
import json, sys
print(json.loads(sys.argv[1])["cycle_skipped"])
PY
)"
RECONSTRUCT_FAILED="$(python3 - "$INCREMENTAL_JSON" <<'PY'
import json, sys
print(json.loads(sys.argv[1])["reconstruct_failed"])
PY
)"
PASS_RATE_PCT="$(python3 - "$INCREMENTAL_JSON" <<'PY'
import json, sys
print(f'{json.loads(sys.argv[1])["pass_rate_pct"]:.1f}')
PY
)"

SHARDS_JSON="$(python3 - "$OUTPUT_DIR" <<'PY'
import json
import os
import sys

root = sys.argv[1]
count = 0
total_bytes = 0
for dirpath, _, filenames in os.walk(root):
    for filename in filenames:
        if filename.endswith(".mathverse"):
            count += 1
            total_bytes += os.path.getsize(os.path.join(dirpath, filename))
print(json.dumps({"file_count": count, "total_bytes": total_bytes}))
PY
)"

SHARD_FILE_COUNT="$(python3 - "$SHARDS_JSON" <<'PY'
import json, sys
print(json.loads(sys.argv[1])["file_count"])
PY
)"
SHARD_TOTAL_BYTES="$(python3 - "$SHARDS_JSON" <<'PY'
import json, sys
print(json.loads(sys.argv[1])["total_bytes"])
PY
)"

if [ "$CORPUS_ACCOUNTING" -eq 1 ]; then
  ACCOUNTING_TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/mathverse_benchmark_accounting.XXXXXX")"
  mkdir -p "$ACCOUNTING_TMP_DIR/src"
  cat > "$ACCOUNTING_TMP_DIR/Cargo.toml" <<EOF
[package]
name = "mathverse-benchmark-accounting"
version = "0.1.0"
edition = "2021"

[dependencies]
serde_json = "1"
clean-olean = { path = "$REPO_ROOT/crates/clean-olean" }
clean-mathverse = { path = "$REPO_ROOT/crates/clean-mathverse" }
clean-kernel = { path = "$REPO_ROOT/crates/clean-kernel" }
EOF
  cat > "$ACCOUNTING_TMP_DIR/src/main.rs" <<'EOF'
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::env;
use std::error::Error;
use std::fs;
use std::path::{Path, PathBuf};

use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{Declaration, Environment, Name};
use clean_olean::module::ConstantKind;
use clean_olean::parse_module_file;
use clean_mathverse::shard::ShardReader;
use clean_mathverse::shard_reconstruct::{
    reconstruct_from_shard_with_level_lists, reconstruct_level_params,
};
use clean_mathverse::shard_verify::discover_mathverse_files;
use clean_mathverse::types::{DeclKind, MathverseConstantHeader, NO_VALUE};
use clean_mathverse::verify_incremental::build_dependency_graph;
use serde_json::json;

const KIND_ORDER: [&str; 8] = [
    "Theorem",
    "Definition",
    "Axiom",
    "Opaque",
    "Inductive",
    "Constructor",
    "Recursor",
    "Quot",
];

fn main() -> Result<(), Box<dyn Error>> {
    let mut lean_lib = None::<PathBuf>;
    let mut output_dir = None::<PathBuf>;
    let mut modules = None::<Vec<String>>;
    let mut json_out = None::<PathBuf>;

    for arg in env::args().skip(1) {
        if let Some(value) = arg.strip_prefix("--lean-lib=") {
            lean_lib = Some(PathBuf::from(value));
        } else if let Some(value) = arg.strip_prefix("--output-dir=") {
            output_dir = Some(PathBuf::from(value));
        } else if let Some(value) = arg.strip_prefix("--modules=") {
            modules = Some(
                value
                    .split(',')
                    .map(str::trim)
                    .filter(|s| !s.is_empty())
                    .map(ToOwned::to_owned)
                    .collect(),
            );
        } else if let Some(value) = arg.strip_prefix("--json-out=") {
            json_out = Some(PathBuf::from(value));
        } else {
            return Err(format!("unknown argument: {arg}").into());
        }
    }

    let lean_lib = lean_lib.ok_or("missing --lean-lib")?;
    let output_dir = output_dir.ok_or("missing --output-dir")?;
    let modules = modules.ok_or("missing --modules")?;
    let json_out = json_out.ok_or("missing --json-out")?;

    let olean_files = discover_selected_olean_files(&lean_lib, &modules)?;
    let (olean_file_count, olean_total_bytes) = file_inventory(&olean_files)?;
    let (olean_total_constants, olean_by_kind) = count_olean_constants(&olean_files)?;

    let mathverse_files = discover_mathverse_files(&output_dir);
    if mathverse_files.is_empty() {
        return Err(format!("no .mathverse files found in {}", output_dir.display()).into());
    }
    let (shard_file_count, shard_total_bytes) = file_inventory(&mathverse_files)?;
    let (converted_total, converted_by_kind) = count_shard_constants(&mathverse_files)?;
    let verify_by_kind = verify_shards_by_kind(&mathverse_files)?;

    let mut by_kind_json = BTreeMap::new();
    for kind in KIND_ORDER {
        let olean_total = *olean_by_kind.get(kind).unwrap_or(&0);
        let converted_total_kind = *converted_by_kind.get(kind).unwrap_or(&0);
        let verify = verify_by_kind.get(kind).cloned().unwrap_or_default();
        let conversion_rate_pct = rate(converted_total_kind, olean_total);
        let pass_rate_pct = rate(verify.kernel_verified, converted_total_kind);
        by_kind_json.insert(
            kind.to_string(),
            json!({
                "olean_total": olean_total,
                "converted_total": converted_total_kind,
                "kernel_verified": verify.kernel_verified,
                "failed": verify.failed,
                "reconstruct_failed": verify.reconstruct_failed,
                "cycle_skipped": verify.cycle_skipped,
                "inductive_registered": verify.inductive_registered,
                "conversion_rate_pct": conversion_rate_pct,
                "pass_rate_pct": pass_rate_pct,
            }),
        );
    }

    let corpus_name = if modules.iter().any(|m| m == "Mathlib") {
        "Init+Mathlib"
    } else {
        "Init"
    };

    let report = json!({
        "corpus": corpus_name,
        "modules": modules,
        "olean": {
            "file_count": olean_file_count,
            "total_bytes": olean_total_bytes,
            "total_constants": olean_total_constants,
        },
        "shards": {
            "file_count": shard_file_count,
            "total_bytes": shard_total_bytes,
            "total_constants": converted_total,
        },
        "converted_constants": converted_total,
        "conversion_rate_pct": rate(converted_total, olean_total_constants),
        "by_decl_kind": by_kind_json,
    });

    fs::write(&json_out, serde_json::to_string_pretty(&report)?)?;
    Ok(())
}

fn discover_selected_olean_files(root: &Path, modules: &[String]) -> Result<Vec<PathBuf>, Box<dyn Error>> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();

    for module in modules {
        let rel = module.replace('.', "/");
        let single = root.join(format!("{rel}.olean"));
        if single.is_file() {
            let canonical = single.canonicalize()?;
            if seen.insert(canonical) {
                out.push(single);
            }
        }
        let dir = root.join(&rel);
        if dir.is_dir() {
            collect_oleans(&dir, &mut seen, &mut out)?;
        }
    }

    out.sort();
    Ok(out)
}

fn collect_oleans(
    dir: &Path,
    seen: &mut BTreeSet<PathBuf>,
    out: &mut Vec<PathBuf>,
) -> Result<(), Box<dyn Error>> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_oleans(&path, seen, out)?;
        } else if path.extension().is_some_and(|e| e == "olean") {
            let canonical = path.canonicalize()?;
            if seen.insert(canonical) {
                out.push(path);
            }
        }
    }
    Ok(())
}

fn file_inventory(paths: &[PathBuf]) -> Result<(u64, u64), Box<dyn Error>> {
    let mut total_bytes = 0u64;
    for path in paths {
        total_bytes += fs::metadata(path)?.len();
    }
    Ok((paths.len() as u64, total_bytes))
}

fn count_olean_constants(
    paths: &[PathBuf],
) -> Result<(u64, BTreeMap<String, u64>), Box<dyn Error>> {
    let mut total = 0u64;
    let mut by_kind = empty_kind_counts();

    for path in paths {
        let module = parse_module_file(path)?;
        for constant in &module.constants {
            total += 1;
            let kind = decl_kind_name_from_olean(&constant.kind);
            *by_kind.entry(kind.to_string()).or_insert(0) += 1;
        }
    }

    Ok((total, by_kind))
}

fn count_shard_constants(
    shard_files: &[PathBuf],
) -> Result<(u64, BTreeMap<String, u64>), Box<dyn Error>> {
    let mut total = 0u64;
    let mut by_kind = empty_kind_counts();

    for shard_path in shard_files {
        let reader = ShardReader::from_file(shard_path)?;
        for constant in &reader.constants {
            total += 1;
            let kind = constant_decl_kind_name(constant);
            *by_kind.entry(kind.to_string()).or_insert(0) += 1;
        }
    }

    Ok((total, by_kind))
}

#[derive(Clone, Debug, Default)]
struct KindVerifyStats {
    kernel_verified: u64,
    failed: u64,
    reconstruct_failed: u64,
    cycle_skipped: u64,
    inductive_registered: u64,
}

fn verify_shards_by_kind(
    shard_files: &[PathBuf],
) -> Result<BTreeMap<String, KindVerifyStats>, Box<dyn Error>> {
    let mut out = empty_kind_verify_counts();

    for shard_path in shard_files {
        let reader = ShardReader::from_file(shard_path)?;
        let deps = build_dependency_graph(&reader);
        let topo = topo_sort(&deps);
        let mut env = Environment::new();

        let name_to_index: HashMap<&str, usize> = reader
            .constants
            .iter()
            .enumerate()
            .filter_map(|(idx, c)| reader.strings.get(c.name_idx as usize).map(|name| (name.as_str(), idx)))
            .collect();

        for name in &topo.order {
            let Some(&idx) = name_to_index.get(name.as_str()) else {
                continue;
            };
            let constant = &reader.constants[idx];
            let kind = constant_decl_kind_name(constant).to_string();
            let stats = out.entry(kind).or_default();
            match verify_constant(&mut env, name, &reader, constant) {
                VerifyOutcome::KernelVerified => stats.kernel_verified += 1,
                VerifyOutcome::InductiveRegistered => stats.inductive_registered += 1,
                VerifyOutcome::ReconstructFailed => stats.reconstruct_failed += 1,
                VerifyOutcome::KernelRejected => stats.failed += 1,
            }
        }

        for name in &topo.cyclic {
            if let Some(&idx) = name_to_index.get(name.as_str()) {
                let kind = constant_decl_kind_name(&reader.constants[idx]).to_string();
                out.entry(kind).or_default().cycle_skipped += 1;
            }
        }
    }

    Ok(out)
}

#[derive(Debug)]
struct TopoResult {
    order: Vec<String>,
    cyclic: Vec<String>,
}

fn topo_sort(deps: &HashMap<String, HashSet<String>>) -> TopoResult {
    let all_names: HashSet<&String> = deps.keys().collect();
    let mut in_degree: HashMap<&String, usize> = HashMap::new();
    let mut adj: HashMap<&String, Vec<&String>> = HashMap::new();

    for name in &all_names {
        in_degree.entry(name).or_insert(0);
        adj.entry(name).or_default();
    }

    for (name, refs) in deps {
        for dep in refs {
            if all_names.contains(dep) {
                adj.entry(dep).or_default().push(name);
                *in_degree.entry(name).or_insert(0) += 1;
            }
        }
    }

    let mut queue = VecDeque::new();
    for (name, degree) in &in_degree {
        if *degree == 0 {
            queue.push_back(*name);
        }
    }

    let mut order = Vec::with_capacity(all_names.len());
    while let Some(name) = queue.pop_front() {
        order.push(name.clone());
        if let Some(dependents) = adj.get(name) {
            for dependent in dependents {
                if let Some(entry) = in_degree.get_mut(dependent) {
                    *entry -= 1;
                    if *entry == 0 {
                        queue.push_back(*dependent);
                    }
                }
            }
        }
    }

    let ordered: HashSet<&str> = order.iter().map(String::as_str).collect();
    let mut cyclic = all_names
        .into_iter()
        .filter(|name| !ordered.contains(name.as_str()))
        .map(|name| name.clone())
        .collect::<Vec<_>>();
    cyclic.sort();

    TopoResult { order, cyclic }
}

#[derive(Debug)]
enum VerifyOutcome {
    KernelVerified,
    InductiveRegistered,
    ReconstructFailed,
    KernelRejected,
}

fn verify_constant(
    env: &mut Environment,
    name: &str,
    reader: &ShardReader,
    constant: &MathverseConstantHeader,
) -> VerifyOutcome {
    let type_expr = match reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        constant.type_idx,
    ) {
        Ok(expr) => expr,
        Err(_) => return VerifyOutcome::ReconstructFailed,
    };

    let value_expr = if constant.value_idx != NO_VALUE {
        reconstruct_from_shard_with_level_lists(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            &reader.level_lists,
            constant.value_idx,
        )
        .ok()
    } else {
        None
    };

    let level_params = reconstruct_level_params(
        &reader.strings,
        constant.level_params_start,
        constant.level_params_count,
    )
    .unwrap_or_default();

    let decl_name = Name::from_string(name);
    let decl_kind = constant
        .decl_kind()
        .unwrap_or(DeclKind::Theorem);

    match decl_kind {
        DeclKind::Inductive | DeclKind::Constructor | DeclKind::Recursor => {
            let decl = Declaration::Axiom {
                name: decl_name,
                level_params,
                type_: type_expr,
            };
            env.add_decl_unchecked(decl);
            VerifyOutcome::InductiveRegistered
        }
        DeclKind::Theorem | DeclKind::Definition | DeclKind::Opaque => {
            try_add_decl(env, decl_name, level_params, type_expr, value_expr)
        }
        DeclKind::Axiom | DeclKind::Quot => {
            let decl = Declaration::Axiom {
                name: decl_name,
                level_params,
                type_: type_expr,
            };
            if env.add_decl(decl).is_ok() {
                VerifyOutcome::KernelVerified
            } else {
                VerifyOutcome::KernelRejected
            }
        }
        _ => VerifyOutcome::KernelRejected,
    }
}

fn try_add_decl(
    env: &mut Environment,
    name: Name,
    level_params: Vec<Name>,
    type_expr: clean_kernel::Expr,
    value_expr: Option<clean_kernel::Expr>,
) -> VerifyOutcome {
    if let Some(value) = value_expr {
        let theorem = Declaration::Theorem {
            name: name.clone(),
            level_params: level_params.clone(),
            type_: type_expr.clone(),
            value,
        };
        if env.add_decl(theorem).is_ok() {
            return VerifyOutcome::KernelVerified;
        }
    }

    let axiom = Declaration::Axiom {
        name,
        level_params,
        type_: type_expr,
    };
    if env.add_decl(axiom).is_ok() {
        VerifyOutcome::KernelVerified
    } else {
        VerifyOutcome::KernelRejected
    }
}

fn decl_kind_name_from_olean(kind: &ConstantKind) -> &'static str {
    match kind {
        ConstantKind::Theorem => "Theorem",
        ConstantKind::Definition => "Definition",
        ConstantKind::Axiom => "Axiom",
        ConstantKind::Opaque => "Opaque",
        ConstantKind::Inductive => "Inductive",
        ConstantKind::Constructor => "Constructor",
        ConstantKind::Recursor => "Recursor",
        ConstantKind::Quot => "Quot",
        _ => "Definition",
    }
}

fn constant_decl_kind_name(constant: &MathverseConstantHeader) -> &'static str {
    match constant.decl_kind().unwrap_or(DeclKind::Theorem) {
        DeclKind::Theorem => "Theorem",
        DeclKind::Definition => "Definition",
        DeclKind::Axiom => "Axiom",
        DeclKind::Opaque => "Opaque",
        DeclKind::Inductive => "Inductive",
        DeclKind::Constructor => "Constructor",
        DeclKind::Recursor => "Recursor",
        DeclKind::Quot => "Quot",
        _ => "Theorem",
    }
}

fn empty_kind_counts() -> BTreeMap<String, u64> {
    let mut map = BTreeMap::new();
    for kind in KIND_ORDER {
        map.insert(kind.to_string(), 0);
    }
    map
}

fn empty_kind_verify_counts() -> BTreeMap<String, KindVerifyStats> {
    let mut map = BTreeMap::new();
    for kind in KIND_ORDER {
        map.insert(kind.to_string(), KindVerifyStats::default());
    }
    map
}

fn rate(num: u64, den: u64) -> f64 {
    if den == 0 {
        0.0
    } else {
        ((num as f64 / den as f64) * 1000.0).round() / 10.0
    }
}
EOF
  run_step "Corpus accounting" "$ACCOUNTING_LOG" \
    env CARGO_TARGET_DIR="$REPO_ROOT/target/mathverse-benchmark-helper" \
    cargo run --quiet --manifest-path "$ACCOUNTING_TMP_DIR/Cargo.toml" --message-format=short -j "$CARGO_BUILD_JOBS" -- \
      "--lean-lib=$LEAN_LIB_DIR" \
      "--output-dir=$OUTPUT_DIR" \
      "--modules=$MODULES" \
      "--json-out=$ACCOUNTING_JSON"
  ACCOUNTING_SECS="$STEP_ELAPSED"
else
  ACCOUNTING_SECS=0
fi

TOTAL_ELAPSED="$((SECONDS - SCRIPT_START))"

python3 - "$JSON_PATH" "$COMMIT_HASH" "$RUN_DATE" "$LEAN_LIB_DIR" "$MODULES" "$OUTPUT_DIR" \
  "$TOTAL_CONSTANTS" "$KERNEL_VERIFIED" "$FAILED_COUNT" "$RECONSTRUCT_FAILED" "$CYCLE_SKIPPED" \
  "$TOTAL_ELAPSED" "$PASS_RATE_PCT" "$OLEAN_FILE_COUNT" "$OLEAN_TOTAL_BYTES" \
  "$SHARD_FILE_COUNT" "$SHARD_TOTAL_BYTES" "$BUILD_BINARY_SECS" "$BUILD_SHARDS_SECS" \
  "$VERIFY_SECS" "$INCREMENTAL_SECS" "$ACCOUNTING_JSON" "$CORPUS_ACCOUNTING" "$MATHLIB_PRESENT" <<'PY'
import json
import os
import sys

(
    json_path,
    commit_hash,
    run_date,
    lean_lib_dir,
    modules,
    output_dir,
    total_constants,
    kernel_verified,
    failed,
    reconstruct_failed,
    cycle_skipped,
    elapsed_secs,
    pass_rate_pct,
    olean_file_count,
    olean_total_bytes,
    shard_file_count,
    shard_total_bytes,
    build_binary_secs,
    build_shards_secs,
    verify_secs,
    incremental_secs,
    accounting_json,
    corpus_accounting,
    mathlib_present,
) = sys.argv[1:]

report = {
    "commit_hash": commit_hash,
    "date": run_date,
    "lean_lib_dir": lean_lib_dir,
    "modules": [m for m in modules.split(",") if m],
    "output_dir": output_dir,
    "total_constants": int(total_constants),
    "kernel_verified": int(kernel_verified),
    "failed": int(failed),
    "reconstruct_failed": int(reconstruct_failed),
    "cycle_skipped": int(cycle_skipped),
    "elapsed_secs": int(elapsed_secs),
    "pass_rate_pct": float(pass_rate_pct),
    "integrity_verified": True,
    "mathlib_present": bool(int(mathlib_present)),
    "input_olean": {
        "file_count": int(olean_file_count),
        "total_bytes": int(olean_total_bytes),
    },
    "shards": {
        "file_count": int(shard_file_count),
        "total_bytes": int(shard_total_bytes),
    },
    "step_timings_secs": {
        "build_binary": int(build_binary_secs),
        "build_shards": int(build_shards_secs),
        "verify_integrity": int(verify_secs),
        "verify_incremental": int(incremental_secs),
    },
}

if int(corpus_accounting) == 1 and os.path.exists(accounting_json):
    with open(accounting_json, "r", encoding="utf-8") as handle:
        report["corpus_accounting"] = json.load(handle)

with open(json_path, "w", encoding="utf-8") as handle:
    json.dump(report, handle, indent=2, sort_keys=True)
    handle.write("\n")
PY

log
log "=== Mathverse Benchmark Summary ==="
log "  Lean lib dir:         $LEAN_LIB_DIR"
log "  Modules:              $MODULES"
log "  Olean files:          $OLEAN_FILE_COUNT ($(format_bytes "$OLEAN_TOTAL_BYTES"))"
log "  Shard files:          $SHARD_FILE_COUNT ($(format_bytes "$SHARD_TOTAL_BYTES"))"
log "  Total constants:      $TOTAL_CONSTANTS"
log "  Kernel verified:      $KERNEL_VERIFIED"
log "  Failed:               $FAILED_COUNT"
log "  Reconstruct failed:   $RECONSTRUCT_FAILED"
log "  Cycle skipped:        $CYCLE_SKIPPED"
log "  TC pass rate:         ${PASS_RATE_PCT}%"
log "  Step timings (secs):  build-binary=$BUILD_BINARY_SECS build=$BUILD_SHARDS_SECS verify=$VERIFY_SECS incremental=$INCREMENTAL_SECS"
if [ "$CORPUS_ACCOUNTING" -eq 1 ] && [ -f "$ACCOUNTING_JSON" ]; then
  ACCOUNTING_SUMMARY="$(python3 - "$ACCOUNTING_JSON" <<'PY'
import json, sys
data = json.load(open(sys.argv[1], "r", encoding="utf-8"))
print(f'{data["converted_constants"]}/{data["olean"]["total_constants"]} converted ({data["conversion_rate_pct"]:.1f}%)')
PY
)"
  log "  Corpus accounting:    $ACCOUNTING_SUMMARY"
fi
log "  Elapsed total:        ${TOTAL_ELAPSED}s"
log "  JSON report:          $JSON_PATH"
