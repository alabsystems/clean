#!/bin/sh
# Mathlib CLOSURE COVERAGE: make Mathlib theorems BROADLY citable at
# `TrustGate::Strict`, not just a lucky subset — and prove the improvement on a
# fixed, deterministically-derived sample measured BEFORE and AFTER.
#
#   scripts/mathlib_closure_coverage.sh
#
# Companion to scripts/mathlib_via_mathverse.sh. That script proves ONE Mathlib
# theorem can be cited and that the `KernelVerified` byte is honest. This script
# answers the next question: what FRACTION of the shard's kernel-verified
# theorems can actually be cited, and what is blocking the rest.
#
# THE DIAGNOSIS THIS SCRIPT ENCODES.
#
# A one-module shard (`Mathlib/Logic/Basic`) holds 365 constants, but a Mathlib
# theorem's transitive closure reaches thousands of constants in OTHER modules.
# Anything not in the shard and not resident in the prelude kills the citation
# with `Unknown constant: X` — raised by the kernel's own `add_decl`, fail-closed
# and honest. That is a COVERAGE gap, not a trust or gate failure.
#
# The fix is therefore to STAMP MORE REAL MODULES, never to widen a gate. The
# blocking constants were resolved to their owning modules by scanning 11,044
# `.olean` files; every one lives in Lean 4 core `Init.*` or `Batteries.Logic`.
# No Mathlib module is missing. So this script stamps:
#
#   A. all of `Init/`      (Lean 4 core — the simp/grind normal-form lemmas that
#                           every Mathlib proof term is built from)
#   B. `Batteries/Logic`   (owns `congr_fun`, `congr_arg`, `eqRec_heq_iff_heq`)
#   C. `Mathlib/Logic/Basic` (the target module; also the BEFORE baseline)
#
# and unions them into one shard dir. `LibraryLoader::load_library` merges
# `base_shards` across dirs, so separately-stamped dirs combine with no
# re-stamping.
#
# WHAT IS DELIBERATELY *NOT* DONE — every one of these looks like success in the
# probe output and is a soundness regression:
#
#   * stamping inductives/constructors/recursors `KernelVerified`. They are
#     VALUE-LESS: nothing kernel-checks them in the stamp lane, so any such stamp
#     would be fabricated. They stay `axiom_accepted`.
#   * `MATHVERSE_PRELOAD_OLEAN`. The `.olean` loader registers via
#     `extend_*_unchecked` (no positivity check, no universe check, eliminators
#     verbatim) and records `DeclarationVerification::Unchecked`. Material loaded
#     that way must never be admitted into a Strict closure. Check 4 asserts the
#     gate now refuses it.
#   * a `kernel-verified.json` sidecar in the shard dir. It is applied verbatim
#     with no re-check. Check 6 asserts none is present.
#   * widening `accepts_dependency` / `TrustGate::Strict`. Check 3 asserts the
#     source still reads KernelVerified-only.
#
# HOW VALUE-LESS DECLARATIONS ARE ADMITTED, since they can never be stamped.
# Not by a kind exemption — there is none. A dependency already RESIDENT in the
# environment is never ADDED by the loader and so is never gated. Residency is
# earned only through the kernel's own checked paths: `Environment::with_prelude`
# and `replay_inductive_family_checked` (rebuild on a scratch clone, install via
# checked `add_inductive`, byte-match against the shard, commit only on success).
# Check 4 asserts residency is tested by the RECORDED kernel verdict
# (`DeclarationVerification::FullKernelCheck`), not by mere name presence.
#
# Cost: ~14 min stamping (peak ~17 GB RSS during the Init run, ~300 MB on disk)
# plus ~4 min of censuses. Set MLCC_REUSE=1 to reuse existing stamp output.
# P6 slice 1a: blocked until the reference producer (slice 1b); see scripts/lib/p6_blocked.sh.
# shellcheck source=scripts/lib/p6_blocked.sh
. "$(cd "$(dirname "$0")" && pwd)/lib/p6_blocked.sh" && p6_blocked "scripts/mathlib_closure_coverage.sh"

set -eu

# --------------------------------------------------------------------------
# Configuration (override via environment)
# --------------------------------------------------------------------------
REPO="${CLEAN_REPO:-$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)}"
MLLIB="${MATHLIB_LIB:-$HOME/mathlib4/.lake/build/lib/lean}"
MLPKGS="${MATHLIB_PACKAGES:-$HOME/mathlib4/.lake/packages}"
TARGET_OLEAN="${TARGET_OLEAN:-$MLLIB/Mathlib/Logic/Basic.olean}"
WORK="${MLCC_WORK:-/tmp/mathlib-closure-coverage}"
SAMPLE_N="${MLCC_SAMPLE:-60}"
SAMPLE_SEED="${MLCC_SEED:-1337}"
REUSE="${MLCC_REUSE:-0}"

# Two theorems named in the report, pinned. `eq_or_ne` closed BEFORE and must
# still close (no regression). `not_iff_not` failed BEFORE on
# `Unknown constant: iff_true_intro` (Init/Core) and must close AFTER.
MUST_CLOSE_BEFORE="${MLCC_CONTROL:-eq_or_ne}"
MUST_CLOSE_AFTER="${MLCC_TARGET:-not_iff_not}"

BEFORE_DIR="$WORK/before"     # C alone — the one-module baseline
INIT_DIR="$WORK/init"         # A
BAT_DIR="$WORK/batteries"     # B
AFTER_DIR="$WORK/after"       # A ∪ B ∪ C
EV="$WORK/evidence"           # manifests, logs, censuses — NEVER beside the shards

FAIL=0
say()  { printf '%s\n' "$*"; }
ok()   { say "PASS  $*"; }
bad()  { say "FAIL  $*"; FAIL=1; }
die()  { say "FAIL  $*"; say ""; say "SOME CHECKS FAILED (see above)"; exit 1; }

say "== Mathlib closure coverage =="
say "      repo      $REPO"
say "      mathlib   $MLLIB"
say "      target    $TARGET_OLEAN"
say "      sample    $SAMPLE_N names, seed $SAMPLE_SEED (deterministic)"
say "      work      $WORK"
say ""

# --------------------------------------------------------------------------
# 1. preflight
# --------------------------------------------------------------------------
say "== 1. preflight: corpus, toolchain, binaries =="
[ -d "$MLLIB" ]        || die "Mathlib build lib not found: $MLLIB (set MATHLIB_LIB)"
[ -f "$TARGET_OLEAN" ] || die "target olean not found: $TARGET_OLEAN (set TARGET_OLEAN)"

TCLIB="${LEAN_TOOLCHAIN_LIB:-}"
if [ -z "$TCLIB" ]; then
  TCNAME=$(tr -d ' \n' < "$HOME/mathlib4/lean-toolchain" 2>/dev/null || true)
  TCDIR=$(printf '%s' "$TCNAME" | sed 's|/|--|; s|:|---|')
  if [ -n "$TCDIR" ] && [ -d "$HOME/.elan/toolchains/$TCDIR/lib/lean" ]; then
    TCLIB="$HOME/.elan/toolchains/$TCDIR/lib/lean"
  else
    TCLIB=$(ls -d "$HOME"/.elan/toolchains/*/lib/lean 2>/dev/null | head -1 || true)
  fi
fi
[ -n "$TCLIB" ] && [ -d "$TCLIB" ] || die "Lean toolchain lib/lean not found (set LEAN_TOOLCHAIN_LIB)"
[ -d "$TCLIB/Init" ] || die "$TCLIB/Init not found — cannot stamp Lean core"

BATLIB="${BATTERIES_LIB:-$MLPKGS/batteries/.lake/build/lib/lean}"
[ -f "$BATLIB/Batteries/Logic.olean" ] || die "Batteries/Logic.olean not found under $BATLIB (set BATTERIES_LIB)"

PKGPATH=""
for d in "$MLPKGS"/*/.lake/build/lib/lean; do
  [ -d "$d" ] && PKGPATH="$PKGPATH:$d"
done
LEAN_PATH="$MLLIB:$TCLIB$PKGPATH"
export LEAN_PATH
# Logic/Basic's transitive olean closure is ~3,500 modules; the default cap is
# 1,500 and the loader is FAIL-CLOSED, so without this the run aborts.
CLEAN_MAX_CLOSURE_MODULES="${CLEAN_MAX_CLOSURE_MODULES:-9000}"
export CLEAN_MAX_CLOSURE_MODULES

CLEAN_BIN="$REPO/target/release/clean"
PROBE_BIN="$REPO/target/release/examples/mathverse_mathlib_citation"
mkdir -p "$WORK" "$EV"
for spec in "clean:-p clean --bin clean" \
            "examples/mathverse_mathlib_citation:-p clean-cli --example mathverse_mathlib_citation"; do
  what=${spec%%:*}; args=${spec#*:}
  if [ ! -x "$REPO/target/release/$what" ]; then
    say "      building $what (missing) ..."
    # shellcheck disable=SC2086
    (cd "$REPO" && cargo build --offline --release $args) >"$EV/build.log" 2>&1 \
      || die "cargo build $args failed — see $EV/build.log"
  fi
done
python3 -c 'import zstandard' 2>/dev/null \
  || die "python3 zstandard module required for the independent byte decode"
ok "inputs present; LEAN_PATH set; CLEAN_MAX_CLOSURE_MODULES=$CLEAN_MAX_CLOSURE_MODULES"

# --------------------------------------------------------------------------
# helper: kv_names.py — INDEPENDENT raw-byte decoder, no Clean code involved.
# Layout: shard.rs (256-byte header, zstd string table, 12-byte levels,
# 16-byte exprs, 64-byte constant headers); types.rs::to_bytes puts
# import_confidence at byte 13 and decl_kind at byte 15.
# --------------------------------------------------------------------------
cat > "$EV/kv_names.py" <<'PYEOF'
import io, struct, sys, zstandard

def kv_theorem_names(path):
    raw = open(path, "rb").read()
    (magic, _v, _f, sc, sdl, lc, ec, cc) = struct.unpack_from("<8I", raw, 0)
    if magic != 0x4F4D4547:
        sys.exit("bad magic %#x in %s" % (magic, path))
    off = 256 + sdl + lc * 12 + ec * 16
    buf = io.BytesIO(zstandard.ZstdDecompressor().decompressobj()
                     .decompress(raw[256:256 + sdl]))
    names = []
    for _ in range(sc):
        n = buf.read(4)
        if len(n) < 4:
            break
        names.append(buf.read(struct.unpack("<I", n)[0]).decode("utf-8", "replace"))
    out, kv = [], 0
    for i in range(cc):
        o = off + i * 64
        (ni,) = struct.unpack_from("<I", raw, o)
        if raw[o + 13] == 0:
            kv += 1
            if raw[o + 15] == 0 and ni < len(names):   # decl_kind == Theorem
                out.append(names[ni])
    return out, kv

if __name__ == "__main__":
    names, kv = kv_theorem_names(sys.argv[1])
    if "--kv-count" in sys.argv:
        print(kv)
    else:
        for n in names:
            print(n)
PYEOF

# --------------------------------------------------------------------------
# helper: mergedir.py — union shard dirs by concatenating base_shards.
# --------------------------------------------------------------------------
cat > "$EV/mergedir.py" <<'PYEOF'
import json, pathlib, shutil, sys
out = pathlib.Path(sys.argv[1]); out.mkdir(parents=True, exist_ok=True)
shards, seen = [], set()
for src in sys.argv[2:]:
    s = pathlib.Path(src)
    m = json.loads((s / "manifest.json").read_text())
    for e in m["base_shards"] + m.get("delta_shards", []):
        base = pathlib.Path(e["path"]).name
        tgt, i = base, 0
        while tgt in seen:
            i += 1
            tgt = "%s_%d.mathverse" % (pathlib.Path(base).stem, i)
        seen.add(tgt)
        shutil.copyfile(s / e["path"], out / tgt)
        e = dict(e); e["path"] = tgt
        shards.append(e)
json.dump({"version": 1, "base_shards": shards, "delta_shards": [],
           "total_constants": sum(s["constant_count"] for s in shards),
           "total_exprs": sum(s["expr_count"] for s in shards)},
          open(out / "manifest.json", "w"), indent=2)
print("      merged %d shards / %d constants -> %s"
      % (len(shards), sum(s["constant_count"] for s in shards), out))
PYEOF

# --------------------------------------------------------------------------
# helper: census.py — probe every name in the sample, bucket the failures.
# --------------------------------------------------------------------------
cat > "$EV/census.py" <<'PYEOF'
import collections, json, os, subprocess, sys
probe, shard_dir, names_file, out_json = sys.argv[1:5]
names = [n for n in open(names_file).read().splitlines() if n]
res = {}
for n in names:
    env = {**os.environ, "MATHVERSE_BY_NAME": "1", "MATHVERSE_PROBE_NAME": n,
           "MATHVERSE_SHARD_DIR": shard_dir}
    p = subprocess.run([probe], capture_output=True, text=True, env=env)
    out = p.stderr + p.stdout
    if "GOAL CLOSED" in out:
        res[n] = ["CLOSED", ""]
        continue
    det = "OTHER"
    for line in out.splitlines():
        if "Unknown constant:" in line:
            det = "COVERAGE:" + line.split("Unknown constant:")[-1].strip()[:60]; break
        if "resident in the environment without a full kernel check" in line:
            det = "UNCHECKED_RESIDENT"; break
        if "stub substitution" in line:
            det = "STUB_SUBSTITUTION"; break
        if "below Strict" in line:
            det = "BELOW_STRICT"; break
        if "rigid universe parameter" in line:
            det = "RIGID_UNIV"; break
        if "TypeMismatch" in line or "does not unify" in line:
            det = "TYPE_MISMATCH"; break
    res[n] = ["FAIL", det]
json.dump(res, open(out_json, "w"), indent=1)
c = collections.Counter(v[0] for v in res.values())
b = collections.Counter(v[1].split(":")[0] for v in res.values() if v[0] == "FAIL")
print("CLOSED=%d TOTAL=%d PCT=%.1f" % (c["CLOSED"], len(names),
                                       100.0 * c["CLOSED"] / max(1, len(names))))
print("BUCKETS=%s" % json.dumps(dict(b)))
PYEOF

# --------------------------------------------------------------------------
# 2. the stamp lane's own soundness floor still holds
# --------------------------------------------------------------------------
say ""
say "== 2. stamp-lane soundness floor (unit test) =="
if (cd "$REPO" && cargo test --offline --release -p clean-mathverse --lib \
      test_ws5_real_olean_stamps_kernel_verified_on_disk -- --nocapture) \
      >"$EV/floor_test.log" 2>&1; then
  if grep -q "^test result: ok\. 1 passed" "$EV/floor_test.log"; then
    ok "$(grep '^test result:' "$EV/floor_test.log" | tail -1)"
  else
    bad "test ran but no terminating 'test result: ok. 1 passed' line — PARTIAL"
  fi
else
  bad "test_ws5_real_olean_stamps_kernel_verified_on_disk FAILED (see $EV/floor_test.log)"
fi

# --------------------------------------------------------------------------
# 3. no gate was weakened
# --------------------------------------------------------------------------
say ""
say "== 3. TrustGate::Strict is unmodified (admits KernelVerified ONLY) =="
GATE="$REPO/crates/clean-elab/src/tactic/mathverse_use.rs"
if grep -q 'Self::Strict | Self::RelaxedFoundational => {' "$GATE" \
   && grep -q 'confidence == ImportConfidence::KernelVerified' "$GATE"; then
  ok "TrustGate::accepts(Strict) == (confidence == KernelVerified)"
else
  bad "TrustGate::accepts no longer reads as KernelVerified-only — REVIEW BEFORE TRUSTING ANY RESULT"
fi
if grep -q 'Self::Strict | Self::Relaxed => false,' "$GATE"; then
  ok "accepts_dependency has no kind-based exemption under Strict"
else
  bad "accepts_dependency gained a Strict exemption — REVIEW"
fi

# --------------------------------------------------------------------------
# 4. residency is KERNEL-CHECKED residency, not name presence
# --------------------------------------------------------------------------
say ""
say "== 4. residency is tested by the recorded kernel verdict =="
# Value-less declarations enter a Strict closure ONLY by being resident, so the
# residency test IS a trust boundary. Name presence is not evidence of a kernel
# check: `.olean` import registers through `extend_*_unchecked` and records
# `DeclarationVerification::Unchecked`.
if grep -q 'env.declaration_verification(&dep_kernel_name)' "$GATE" \
   && grep -q 'DeclarationVerification::FullKernelCheck' "$GATE"; then
  ok "already_resident := declaration_verification(dep) == FullKernelCheck"
else
  bad "residency is back to bare name presence — unchecked .olean material would be admitted"
fi
if grep -q 'resident in the environment without a full kernel check' "$GATE"; then
  ok "a name-resident dependency without a full kernel check is refused under Strict"
else
  bad "no shadowed-by-unchecked refusal — an unchecked resident could stand in for a verified decl"
fi
if grep -q 'stub substitution' "$GATE"; then
  ok "resident Inductive/Constructor/Recursor must be backed by the structured kernel value"
else
  bad "no kind-agreement check — a prelude axiom stub could stand in for a real structure"
fi

# --------------------------------------------------------------------------
# 5. stamp: Clean's kernel re-checks each constant's shard-stored VALUE
# --------------------------------------------------------------------------
say ""
say "== 5. stamp-verified (3 invocations; kernel re-checks every value) =="

# $1 label  $2 stamp json  $3 "1" to also require axiom_fallback == 0
check_stamp_json() {
  python3 - "$1" "$2" "${3:-0}" <<'PYEOF'
import json, sys
label, d, strict_fb = sys.argv[1], json.load(open(sys.argv[2])), sys.argv[3] == "1"
c = d.get("closure", {})
print("      %-22s total=%s kernel_verified=%s axiom_accepted=%s axiom_fallback=%s failed=%s"
      % (label, d.get("total"), d.get("kernel_verified"), d.get("axiom_accepted"),
         d.get("axiom_fallback"), d.get("failed")))
print("      %-22s closure %s modules / %s constants; phase_a=%.1fs phase_b=%.1fs"
      % ("", c.get("modules_loaded"), c.get("closure_constants"),
         d.get("phase_a_secs", 0.0), d.get("phase_b_secs", 0.0)))
bad = []
if d.get("ok") is not True:                 bad.append("ok is not true")
# THE floor: had the heuristic converter minted even one KernelVerified, the run
# aborts before stamping. 0 is mandatory everywhere.
if d.get("heuristic_kernel_verified") != 0: bad.append("heuristic_kernel_verified != 0")
if d.get("failed") != 0:                    bad.append("failed != 0")
if not d.get("stored_kernel_verified"):     bad.append("stored_kernel_verified == 0")
if d.get("stored_kernel_verified") != d.get("kernel_verified"):
    bad.append("stored_kernel_verified != kernel_verified (stamp did not reach the bytes)")

# axiom_fallback is a COVERAGE datum, not a trust breach — and the distinction is
# worth stating precisely, because asserting it to zero here is wrong.
#
# A fallback is recorded when a value-bearing row cannot be proof-checked: either
# the shard carries no value (opacity artifacts — `opaque` gadgets, meta
# `register_option`/`partial def` rows whose values the olean->shard converter
# deliberately elides) or the kernel REJECTED the value. Both are stamped
# `Axiomatized`, never `KernelVerified`. So a fallback can only ever REDUCE what
# `TrustGate::Strict` admits; it can never smuggle anything in. Requiring 0 is
# the right bar for the Mathlib TARGET module (the parent script asserts it) but
# not for all of Lean core `Init/`, which genuinely has some. Report it loudly,
# fail only where the bar applies.
fb = d.get("axiom_fallback", 0)
if fb:
    print("      %-22s axiom_fallback=%d of %s — stamped Axiomatized, NEVER KernelVerified "
          "(can only narrow what Strict admits, never widen it)"
          % ("", fb, d.get("total")))
    if strict_fb:
        bad.append("axiom_fallback != 0 (required 0 for this target)")
if bad:
    print("FAIL  %s: %s" % (label, "; ".join(bad))); sys.exit(1)
sys.exit(0)
PYEOF
}

# $1 label  $2 out-dir  $3 closure-root  $4 strict-fallback(0|1)  $5.. inputs
run_stamp() {
  label="$1"; outdir="$2"; croot="$3"; strict_fb="$4"; shift 4
  if [ "$REUSE" = "1" ] && [ -f "$outdir/manifest.json" ] && [ -f "$EV/$label.json" ]; then
    say "      $label: reusing $outdir (MLCC_REUSE=1)"
    check_stamp_json "$label" "$EV/$label.json" "$strict_fb" || FAIL=1
    return 0
  fi
  rm -rf "$outdir"; mkdir -p "$outdir"
  START=$(date +%s)
  set +e
  "$CLEAN_BIN" mathverse stamp-verified "$@" \
      --out-dir "$outdir" \
      --manifest "$EV/$label-kernel-verified.json" \
      --closure-root "$croot" \
      --parallel --json >"$EV/$label.json" 2>"$EV/$label.err"
  RC=$?
  set -e
  END=$(date +%s)
  say "      $label: rc=$RC after $((END - START))s"
  if [ "$RC" != 0 ]; then
    tail -20 "$EV/$label.err" | sed 's/^/        /'
    die "stamp-verified ($label) failed"
  fi
  check_stamp_json "$label" "$EV/$label.json" "$strict_fb" || FAIL=1
}

# NOTE: --closure-root must be the root the TARGET olean lives under. Pointing
# it elsewhere fails with "module name is empty or contains empty
# '.'-separated components", which is why Batteries needs its own invocation.
#
# axiom_fallback is required to be 0 only for the Mathlib TARGET module, where
# the parent script already holds that bar. Lean core `Init/` genuinely has some
# (opacity artifacts and a handful of kernel-rejected values); they are stamped
# Axiomatized and can only narrow what Strict admits, never widen it.
run_stamp init      "$INIT_DIR"   "$TCLIB"  0 "$TCLIB/Init"
run_stamp batteries "$BAT_DIR"    "$BATLIB" 1 "$BATLIB/Batteries/Logic.olean"
run_stamp basic     "$BEFORE_DIR" "$MLLIB"  1 "$TARGET_OLEAN"
[ "$FAIL" = 0 ] || die "a stamp run did not meet the soundness floor"
ok "3 stamp runs: failed=0, heuristic_kernel_verified=0, stamp reached the bytes on each"

say ""
say "      union the three shard dirs (LibraryLoader merges base_shards):"
rm -rf "$AFTER_DIR"
python3 "$EV/mergedir.py" "$AFTER_DIR" "$INIT_DIR" "$BAT_DIR" "$BEFORE_DIR"

# --------------------------------------------------------------------------
# 6. no sidecar can be doing the work
# --------------------------------------------------------------------------
say ""
say "== 6. no kernel-verified.json sidecar in either shard dir =="
SIDE=0
for d in "$BEFORE_DIR" "$AFTER_DIR"; do
  if ls "$d"/*kernel-verified*.json >/dev/null 2>&1; then
    bad "sidecar present in $d — it would mint KernelVerified with no re-check"
    SIDE=1
  fi
done
[ "$SIDE" = 0 ] && ok "no sidecar in $BEFORE_DIR or $AFTER_DIR; confidence comes from shard bytes"

# --------------------------------------------------------------------------
# 7. independent raw-byte census + the fixed sample
# --------------------------------------------------------------------------
say ""
say "== 7. independent raw-byte decode; derive the FIXED sample =="
BASIC_SHARD=$(find "$BEFORE_DIR" -name '*.mathverse' | head -1)
[ -n "$BASIC_SHARD" ] || die "no .mathverse in $BEFORE_DIR"
python3 "$EV/kv_names.py" "$BASIC_SHARD" > "$EV/kv_theorems.txt"
POP=$(wc -l < "$EV/kv_theorems.txt" | tr -d ' ')
BEFORE_KV=$(python3 "$EV/kv_names.py" "$BASIC_SHARD" --kv-count)
AFTER_KV=0
for s in "$AFTER_DIR"/*.mathverse; do
  AFTER_KV=$((AFTER_KV + $(python3 "$EV/kv_names.py" "$s" --kv-count)))
done
say "      baseline shard: $BEFORE_KV KernelVerified constants, $POP of them Theorem"
say "      merged shard:   $AFTER_KV KernelVerified constants across $(ls "$AFTER_DIR"/*.mathverse | wc -l | tr -d ' ') shards"
[ "$POP" -gt 0 ] || die "baseline shard has no KernelVerified theorems"

# THE SAMPLE. Derived from the BASELINE population only, so BEFORE and AFTER are
# measured on exactly the same names — a rate computed across two different
# samples is meaningless.
python3 - "$EV/kv_theorems.txt" "$SAMPLE_N" "$SAMPLE_SEED" \
         "$MUST_CLOSE_BEFORE" "$MUST_CLOSE_AFTER" > "$EV/sample.txt" <<'PYEOF'
import random, sys
pop = sorted(set(l for l in open(sys.argv[1]).read().splitlines() if l))
n, seed = int(sys.argv[2]), int(sys.argv[3])
pins = [p for p in sys.argv[4:] if p in pop]
sample = random.Random(seed).sample(pop, min(n, len(pop)))
for p in pins:                       # pinned controls always measured
    if p not in sample:
        sample.append(p)
for s in sample:
    print(s)
PYEOF
SAMP=$(wc -l < "$EV/sample.txt" | tr -d ' ')
ok "fixed sample: $SAMP names, random.Random($SAMPLE_SEED).sample(sorted(pop), $SAMPLE_N) + pinned controls"

# --------------------------------------------------------------------------
# 8. BEFORE / AFTER citability on the SAME sample
# --------------------------------------------------------------------------
say ""
say "== 8. citability BEFORE (baseline one-module shard) =="
python3 "$EV/census.py" "$PROBE_BIN" "$BEFORE_DIR" "$EV/sample.txt" "$EV/before.json" \
  > "$EV/before.txt" 2>&1 || die "before census failed (see $EV/before.txt)"
sed 's/^/      /' "$EV/before.txt"
B_CLOSED=$(sed -n 's/^CLOSED=\([0-9]*\) .*/\1/p' "$EV/before.txt")

say ""
say "== 8b. citability AFTER (merged shard: Init + Batteries.Logic + Logic.Basic) =="
python3 "$EV/census.py" "$PROBE_BIN" "$AFTER_DIR" "$EV/sample.txt" "$EV/after.json" \
  > "$EV/after.txt" 2>&1 || die "after census failed (see $EV/after.txt)"
sed 's/^/      /' "$EV/after.txt"
A_CLOSED=$(sed -n 's/^CLOSED=\([0-9]*\) .*/\1/p' "$EV/after.txt")

if [ "$A_CLOSED" -gt "$B_CLOSED" ]; then
  ok "citability rose $B_CLOSED -> $A_CLOSED of $SAMP on the SAME sample"
else
  bad "citability did not improve ($B_CLOSED -> $A_CLOSED of $SAMP)"
fi
# The whole point: the coverage bucket must be gone. Anything left is a
# different defect (unification / universe levels), not a closure gap.
A_COV=$(python3 -c "
import json,sys
d=json.load(open(sys.argv[1]))
print(sum(1 for v in d.values() if v[1].startswith('COVERAGE')))" "$EV/after.json")
if [ "$A_COV" = "0" ]; then
  ok "coverage failures after: 0 (no closure member is declared outside the shard)"
else
  bad "coverage failures after: $A_COV — more modules still need stamping"
fi
# A trust refusal would mean the shard is not uniformly kernel-verified.
A_TRUST=$(python3 -c "
import json,sys
d=json.load(open(sys.argv[1]))
print(sum(1 for v in d.values() if v[1] in ('BELOW_STRICT','UNCHECKED_RESIDENT','STUB_SUBSTITUTION')))" "$EV/after.json")
say "      trust-side refusals after: $A_TRUST (fail-closed; not a coverage gap)"

# --------------------------------------------------------------------------
# 9. the two pinned probes, verbatim
# --------------------------------------------------------------------------
say ""
say "== 9. pinned probes =="
probe_line() {
  set +e
  MATHVERSE_BY_NAME=1 MATHVERSE_SHARD_DIR="$2" MATHVERSE_PROBE_NAME="$1" \
    "$PROBE_BIN" >"$EV/probe-$1.log" 2>&1
  prc=$?
  set -e
  line=$(grep -m1 'GOAL CLOSED\|citation: detail:' "$EV/probe-$1.log" || true)
  say "      [$1] rc=$prc"
  say "      $line"
  printf '%s' "$line" | grep -q 'GOAL CLOSED'
}

if probe_line "$MUST_CLOSE_BEFORE" "$AFTER_DIR"; then
  ok "control \`$MUST_CLOSE_BEFORE\` still closes (no regression)"
else
  bad "control \`$MUST_CLOSE_BEFORE\` no longer closes — REGRESSION"
fi
if probe_line "$MUST_CLOSE_AFTER" "$AFTER_DIR"; then
  ok "target \`$MUST_CLOSE_AFTER\` now closes (it failed on the baseline shard)"
else
  bad "target \`$MUST_CLOSE_AFTER\` still does not close"
fi

# --------------------------------------------------------------------------
say ""
say "== summary =="
say "      before shard   $BEFORE_DIR   ($BEFORE_KV KernelVerified)"
say "      after  shard   $AFTER_DIR   ($AFTER_KV KernelVerified)"
say "      evidence       $EV"
say "      citability     $B_CLOSED -> $A_CLOSED of $SAMP (same fixed sample)"
say "      coverage fails $A_COV after"
say ""
if [ "$FAIL" = 0 ]; then
  say "ALL CHECKS PASSED"
  say "Mathlib theorems are broadly citable at TrustGate::Strict; the residual is"
  say "not a closure gap."
else
  say "SOME CHECKS FAILED (see above)"
fi
exit "$FAIL"
