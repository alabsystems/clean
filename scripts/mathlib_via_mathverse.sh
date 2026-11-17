#!/bin/sh
# Mathlib via Mathverse: build a `.mathverse` shard whose constants are GENUINELY
# `KernelVerified` by Clean's own kernel, then close a Clean goal by citing one
# of them under `TrustGate::Strict`.
#
#   scripts/mathlib_via_mathverse.sh
#
# This is the Mathlib counterpart of scripts/isabelle/verify_grand.sh and it
# targets the same bar: a `.mathverse` SHARD (not the `.olean` import path)
# carrying real `KernelVerified` content, cited at `TrustGate::Strict`.
#
# WHY EACH CHECK EXISTS. "GOAL CLOSED" is worthless on its own — the gate admits
# a constant purely on one byte (`import_confidence == 0`). Three separate
# mechanisms can put that byte there WITHOUT the kernel ever running:
#
#   * `lean4/env_import.rs::confidence_for` mints KernelVerified from
#     "kind is Theorem/Definition AND a value is present". No kernel.
#   * a hand-written `kernel-verified.json` sidecar next to the shards is
#     applied verbatim by `load_built_library` -> `apply_kernel_verified_manifest`.
#   * editing the byte in the file.
#
# So this script does not merely run the probe. It establishes, with a NEGATIVE
# CONTROL and an INDEPENDENT RAW-BYTE DECODE performed outside all Clean code,
# that the `KernelVerified` bytes in the shard were absent before the kernel ran
# and present after, that no sidecar is in play, and that the byte cannot be
# casually forged. Every check prints PASS/FAIL; any FAIL exits non-zero.
#
# SOUNDNESS INVARIANT UNDER TEST: `KernelVerified` means, and only means, that
# Clean's kernel type-checked the declaration's VALUE. Nothing here weakens
# `TrustGate::Strict`, any trust policy, or any test — check 3 asserts that.
#
# Cost: ~4 minutes wall, ~2.6 GB peak RSS, ~1 MB of artifacts.
# P6 slice 1a: blocked until the reference producer (slice 1b); see scripts/lib/p6_blocked.sh.
# shellcheck source=scripts/lib/p6_blocked.sh
. "$(cd "$(dirname "$0")" && pwd)/lib/p6_blocked.sh" && p6_blocked "scripts/mathlib_via_mathverse.sh"

set -eu

# --------------------------------------------------------------------------
# Configuration (override via environment)
# --------------------------------------------------------------------------
REPO="${CLEAN_REPO:-$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)}"
MLLIB="${MATHLIB_LIB:-$HOME/mathlib4/.lake/build/lib/lean}"
MLPKGS="${MATHLIB_PACKAGES:-$HOME/mathlib4/.lake/packages}"
TARGET_OLEAN="${TARGET_OLEAN:-$MLLIB/Mathlib/Logic/Basic.olean}"
# `eq_or_ne` is Mathlib/Logic/Basic.lean:222 —
#   theorem eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x ≠ y := em <| x = y
# a real, hand-written, universe-polymorphic Mathlib theorem. It is PINNED
# because the probe's default pick (first KernelVerified theorem in index
# order) lands on `not_iff_not`, whose closure reaches `iff_true_intro` —
# declared in Init/Core.olean, i.e. outside this one-module shard. That is a
# coverage gap, not a trust or gate failure; see check 9's FAIL guidance.
PROBE_NAME="${MATHVERSE_PROBE_NAME:-eq_or_ne}"
WORK="${MLMV_WORK:-/tmp/mathlib-via-mathverse}"
OUT="$WORK/shard"        # the shard dir the probe reads. NO sidecar lives here.
EV="$WORK/evidence"      # JSON summary + kernel-verified.json, deliberately elsewhere
NEG="$WORK/negative"     # heuristic-only conversion of the SAME olean
TAMPER="$WORK/tamper"    # forged-KV copy, must be rejected

FAIL=0
say()  { printf '%s\n' "$*"; }
ok()   { say "PASS  $*"; }
bad()  { say "FAIL  $*"; FAIL=1; }
die()  { say "FAIL  $*"; say ""; say "SOME CHECKS FAILED (see above)"; exit 1; }

say "== Mathlib via Mathverse =="
say "      repo        $REPO"
say "      mathlib lib $MLLIB"
say "      target      $TARGET_OLEAN"
say "      probe       $PROBE_NAME"
say "      work        $WORK"
say ""

# --------------------------------------------------------------------------
# 1. preflight — inputs and binaries
# --------------------------------------------------------------------------
say "== 1. preflight: corpus, toolchain, binaries =="
[ -d "$MLLIB" ]        || die "Mathlib build lib not found: $MLLIB (set MATHLIB_LIB)"
[ -f "$TARGET_OLEAN" ] || die "target olean not found: $TARGET_OLEAN (set TARGET_OLEAN)"

# Toolchain lib/lean — needed on LEAN_PATH so the closure can resolve Init/Std.
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

PKGPATH=""
for d in "$MLPKGS"/*/.lake/build/lib/lean; do
  [ -d "$d" ] && PKGPATH="$PKGPATH:$d"
done
LEAN_PATH="$MLLIB:$TCLIB$PKGPATH"
export LEAN_PATH
# Logic/Basic's transitive olean closure is ~3,500 modules; the default cap is
# 1,500 (closure_load.rs:101) and the loader is FAIL-CLOSED, so without this the
# stamp run aborts rather than silently truncating the closure.
CLEAN_MAX_CLOSURE_MODULES="${CLEAN_MAX_CLOSURE_MODULES:-9000}"
export CLEAN_MAX_CLOSURE_MODULES

CLEAN_BIN="$REPO/target/release/clean"
CONV_BIN="$REPO/target/release/mathverse_convert"
PROBE_BIN="$REPO/target/release/examples/mathverse_mathlib_citation"
for spec in "clean:-p clean --bin clean" \
            "mathverse_convert:-p clean-mathverse --bin mathverse_convert" \
            "examples/mathverse_mathlib_citation:-p clean-cli --example mathverse_mathlib_citation"; do
  what=${spec%%:*}; args=${spec#*:}
  if [ ! -x "$REPO/target/release/$what" ]; then
    say "      building $what (missing) ..."
    # shellcheck disable=SC2086
    (cd "$REPO" && cargo build --offline --release $args) >"$WORK.build.log" 2>&1 \
      || die "cargo build $args failed — see $WORK.build.log"
  fi
done
ok "inputs present; LEAN_PATH set; CLEAN_MAX_CLOSURE_MODULES=$CLEAN_MAX_CLOSURE_MODULES"
say "      $(ls -l "$TARGET_OLEAN" | awk '{print $5" bytes  "$NF}')"

rm -rf "$WORK"; mkdir -p "$OUT" "$EV" "$NEG" "$TAMPER"

# --------------------------------------------------------------------------
# census.py — INDEPENDENT raw-byte decoder. No Clean code involved.
# Layout: shard.rs:7-48 (256-byte header, zstd string table, 12-byte levels,
# 16-byte exprs, 64-byte constant headers) and types.rs::to_bytes
# (byte 12 source_system, 13 import_confidence, 15 decl_kind).
# --------------------------------------------------------------------------
cat > "$WORK/census.py" <<'PYEOF'
import collections, io, struct, sys

CONF = {0: "KernelVerified", 1: "Translated", 2: "Axiomatized", 3: "Unverified",
        4: "Reconstructed", 5: "SurfaceNamesOnly", 6: "SourceVerified",
        7: "KernelCheckedConditional"}
KIND = {0: "Theorem", 1: "Definition", 2: "Axiom", 3: "Inductive",
        4: "Constructor", 5: "Recursor", 6: "Quot", 7: "Opaque"}
SYS  = {0: "Lean4", 6: "Isabelle"}

path = sys.argv[1]
args = sys.argv[2:]
raw = open(path, "rb").read()
(magic, ver, flags, string_count, string_data_len, level_count,
 expr_count, const_count, bloom, prov_len, sorted_len, ll_count) = \
    struct.unpack_from("<12I", raw, 0)
if magic != 0x4F4D4547:
    sys.exit("bad magic %#x" % magic)

str_off = 256
lvl_off = str_off + string_data_len
exp_off = lvl_off + level_count * 12
hdr_off = exp_off + expr_count * 16

# Names: string table is zstd-compressed [len:u32, utf8]*
names = []
try:
    import zstandard
    blob = zstandard.ZstdDecompressor().decompressobj().decompress(
        raw[str_off:str_off + string_data_len])
    buf = io.BytesIO(blob)
    for _ in range(string_count):
        n = buf.read(4)
        if len(n) < 4:
            break
        ln = struct.unpack("<I", n)[0]
        names.append(buf.read(ln).decode("utf-8", "replace"))
except Exception as exc:                                   # noqa: BLE001
    names = []
    if "--name" in args:
        sys.exit("string table decode failed (%s); cannot resolve --name" % exc)

conf = collections.Counter(); kind = collections.Counter(); srcs = collections.Counter()
kv_theorem = 0
by_name = {}
for i in range(const_count):
    o = hdr_off + i * 64
    name_idx, type_idx, value_idx = struct.unpack_from("<3I", raw, o)
    s, c, _dom, k = raw[o + 12], raw[o + 13], raw[o + 14], raw[o + 15]
    conf[c] += 1; kind[k] += 1; srcs[s] += 1
    if c == 0 and k == 0:
        kv_theorem += 1
    if names and name_idx < len(names):
        by_name[names[name_idx]] = (c, k, value_idx, i)

if "--kv-count" in args:
    print(conf.get(0, 0)); sys.exit(0)

if "--name" in args:
    want = args[args.index("--name") + 1]
    if want not in by_name:
        sys.exit("constant `%s` is NOT in this shard" % want)
    c, k, value_idx, idx = by_name[want]
    print("      `%s`  idx=%d  import_confidence=%d(%s)  decl_kind=%d(%s)  has_value=%s"
          % (want, idx, c, CONF.get(c, c), k, KIND.get(k, k), value_idx != 0xFFFFFFFF))
    problems = []
    if c != 0:
        problems.append("import_confidence is %s, not KernelVerified" % CONF.get(c, c))
    if k != 0:
        problems.append("decl_kind is %s, not Theorem" % KIND.get(k, k))
    if value_idx == 0xFFFFFFFF:
        problems.append("no value stored")
    if problems:
        sys.exit("; ".join(problems))
    sys.exit(0)

print("      file=%s bytes=%d version=%d constants=%d exprs=%d levels=%d level_lists=%d"
      % (path.rsplit("/", 1)[-1], len(raw), ver, const_count, expr_count,
         level_count, ll_count))
print("      import_confidence: %s"
      % {CONF.get(k, k): v for k, v in sorted(conf.items())})
print("      decl_kind:         %s"
      % {KIND.get(k, k): v for k, v in sorted(kind.items())})
print("      source_system:     %s"
      % {SYS.get(k, k): v for k, v in sorted(srcs.items())})
print("      KernelVerified AND Theorem = %d" % kv_theorem)
print("KVCOUNT=%d" % conf.get(0, 0))
print("NONLEAN4=%d" % sum(v for k, v in srcs.items() if k != 0))
PYEOF

# --------------------------------------------------------------------------
# 2. the stamp lane's own soundness floor still holds
# --------------------------------------------------------------------------
say ""
say "== 2. stamp-lane soundness floor (unit test) =="
# Asserts the full shape on a real Lean-core olean: heuristic conversion mints
# ZERO KernelVerified, stored KV is 0 before verification, and only after
# `verify_corpus_incremental` does the on-disk stamp appear.
if (cd "$REPO" && cargo test --offline --release -p clean-mathverse --lib \
      test_ws5_real_olean_stamps_kernel_verified_on_disk -- --nocapture) \
      >"$EV/floor_test.log" 2>&1; then
  if grep -q "^test result: ok\. 1 passed" "$EV/floor_test.log"; then
    ok "$(grep '^test result:' "$EV/floor_test.log" | tail -1)"
    say "      $(grep 'Minimal.olean corpus:' "$EV/floor_test.log" | tail -1)"
  else
    bad "test ran but no terminating 'test result: ok. 1 passed' line — treating as PARTIAL"
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
  ok "TrustGate::accepts(Strict) == (confidence == KernelVerified)  [$GATE]"
else
  bad "TrustGate::accepts no longer reads as KernelVerified-only — REVIEW BEFORE TRUSTING ANY RESULT"
fi
DIRTY=$(cd "$REPO" && git status --porcelain -- crates/ | grep -v '^?? ' || true)
if [ -z "$DIRTY" ]; then
  ok "no uncommitted modifications under crates/ (git status --porcelain clean)"
else
  bad "crates/ has uncommitted modifications — the result is not attributable to committed code:"
  printf '%s\n' "$DIRTY" | sed 's/^/        /'
fi

# --------------------------------------------------------------------------
# 4. NEGATIVE CONTROL — the heuristic import lane mints ZERO KernelVerified
# --------------------------------------------------------------------------
say ""
say "== 4. negative control: same olean, heuristic lane, NO kernel =="
# `mathverse_convert mathlib` passes verified_names = None, so confidence comes
# only from `confidence_for_constant` (SourceVerified / Axiomatized / Unverified).
# If this ever reports KernelVerified > 0, the whole result is void.
NEGSHARD=""
mkdir -p "$NEG/in/Mathlib/Logic" "$NEG/out" "$NEG/empty_tc" "$NEG/empty_pkg"
cp "$TARGET_OLEAN" "$NEG/in/Mathlib/Logic/"
# Empty --toolchain/--packages-root isolate the conversion to the ONE target
# olean, so the count below is about exactly the file check 5 stamps.
if "$CONV_BIN" mathlib --mathlib-root "$NEG/in" --toolchain "$NEG/empty_tc" \
     --packages-root "$NEG/empty_pkg" --output-dir "$NEG/out" \
     >"$EV/negative.log" 2>&1; then
  NEGSHARD=$(find "$NEG/out" -name '*.mathverse' | head -1)
  [ -n "$NEGSHARD" ] || bad "heuristic conversion produced no shard (see $EV/negative.log)"
else
  bad "mathverse_convert mathlib failed (see $EV/negative.log)"
fi

if [ -n "$NEGSHARD" ]; then
  python3 "$WORK/census.py" "$NEGSHARD" | grep -v '^KVCOUNT=\|^NONLEAN4='
  NEGKV=$(python3 "$WORK/census.py" "$NEGSHARD" --kv-count)
  if [ "$NEGKV" = "0" ]; then
    ok "heuristic-only shard has 0 KernelVerified — KV is NOT minted at import time"
  else
    bad "heuristic-only shard already has $NEGKV KernelVerified — SOUNDNESS FLOOR BREACH; result void"
  fi
  # And the probe refuses to even try against it.
  cp "$NEGSHARD" "$NEG/probe_dir_shard.mathverse" 2>/dev/null || true
fi

# --------------------------------------------------------------------------
# 5. mint KernelVerified: kernel re-checks each constant's shard-stored VALUE
# --------------------------------------------------------------------------
say ""
say "== 5. stamp-verified: Clean's kernel re-checks the shard's own values =="
say "      (phase A loads the ~3.5k-module olean closure; expect ~3.5 min)"
START=$(date +%s)
set +e
"$CLEAN_BIN" mathverse stamp-verified "$TARGET_OLEAN" \
    --out-dir "$OUT" \
    --manifest "$EV/kernel-verified.json" \
    --closure-root "$MLLIB" \
    --parallel --json >"$EV/stamp.json" 2>"$EV/stamp.err"
RC=$?
set -e
END=$(date +%s)
say "      stamp-verified exited rc=$RC after $((END - START))s"
if [ "$RC" != 0 ]; then
  say "      ---- stamp.err (tail) ----"
  tail -20 "$EV/stamp.err" | sed 's/^/        /'
  die "stamp-verified failed"
fi

python3 - "$EV/stamp.json" <<'PYEOF' || FAIL=1
import json, sys
d = json.load(open(sys.argv[1]))
c = d.get("closure", {})
print("      total=%s kernel_verified=%s axiom_accepted=%s axiom_fallback=%s failed=%s"
      % (d.get("total"), d.get("kernel_verified"), d.get("axiom_accepted"),
         d.get("axiom_fallback"), d.get("failed")))
print("      heuristic_kernel_verified=%s constants_stamped=%s stored_kernel_verified=%s"
      % (d.get("heuristic_kernel_verified"), d.get("constants_stamped"),
         d.get("stored_kernel_verified")))
print("      closure: %s modules / %s constants   phase_a=%.1fs phase_b=%.3fs"
      % (c.get("modules_loaded"), c.get("closure_constants"),
         d.get("phase_a_secs", 0.0), d.get("phase_b_secs", 0.0)))
bad = []
if d.get("ok") is not True:                      bad.append("ok is not true")
# THE floor: if the heuristic converter had minted even one KernelVerified, the
# run aborts before stamping (stamp_verified_dispatch.rs:838). 0 is mandatory.
if d.get("heuristic_kernel_verified") != 0:      bad.append("heuristic_kernel_verified != 0")
if d.get("failed") != 0:                         bad.append("failed != 0")
if d.get("axiom_fallback") != 0:                 bad.append("axiom_fallback != 0")
if not d.get("stored_kernel_verified"):          bad.append("stored_kernel_verified == 0")
if d.get("stored_kernel_verified") != d.get("kernel_verified"):
    bad.append("stored_kernel_verified != kernel_verified (stamp did not reach the bytes)")
if bad:
    print("FAIL  " + "; ".join(bad)); sys.exit(1)
print("PASS  %s constants kernel-verified and stamped into the shard bytes; "
      "heuristic minted 0" % d.get("stored_kernel_verified"))
PYEOF
STORED_KV=$(python3 -c "import json,sys;print(json.load(open(sys.argv[1]))['stored_kernel_verified'])" "$EV/stamp.json")

# --------------------------------------------------------------------------
# 6. no sidecar can be doing the work
# --------------------------------------------------------------------------
say ""
say "== 6. no kernel-verified.json sidecar in the shard dir =="
# `load_built_library` applies any kernel-verified.json sitting beside the
# shards (build_library.rs:322 -> library.rs:363) with NO re-check. Keeping the
# sidecar in the evidence dir means the probe can only be reading confidence
# out of the shard BYTES.
say "      $OUT contains: $(ls "$OUT" | tr '\n' ' ')"
if [ -e "$OUT/kernel-verified.json" ]; then
  bad "a kernel-verified.json sidecar is present in $OUT — it could mint KV with no re-check"
else
  ok "no sidecar in $OUT; confidence must come from the shard bytes"
fi

# --------------------------------------------------------------------------
# 7. INDEPENDENT raw-byte census (no Clean code involved)
# --------------------------------------------------------------------------
say ""
say "== 7. independent raw-byte census of the stamped shard =="
SHARD=$(find "$OUT" -name '*.mathverse' | head -1)
[ -n "$SHARD" ] || die "no .mathverse produced in $OUT"
python3 "$WORK/census.py" "$SHARD" >"$EV/census.txt" 2>&1 || bad "census.py failed"
grep -v '^KVCOUNT=\|^NONLEAN4=' "$EV/census.txt" || true
BYTE_KV=$(sed -n 's/^KVCOUNT=//p' "$EV/census.txt")
NONLEAN=$(sed -n 's/^NONLEAN4=//p' "$EV/census.txt")
if [ "$BYTE_KV" = "$STORED_KV" ]; then
  ok "raw bytes carry $BYTE_KV KernelVerified, matching the run's stored_kernel_verified"
else
  bad "raw-byte KernelVerified=$BYTE_KV != stored_kernel_verified=$STORED_KV"
fi
if [ "$NONLEAN" = "0" ]; then
  ok "every constant is source_system=Lean4 (dep-graph keying is uniform)"
else
  bad "$NONLEAN constants are not source_system=Lean4 — build_deps would drop edges"
fi

say ""
say "== 7b. the probe constant, decoded from the bytes =="
if python3 "$WORK/census.py" "$SHARD" --name "$PROBE_NAME" >"$EV/probe_hdr.txt" 2>&1; then
  cat "$EV/probe_hdr.txt"
  ok "\`$PROBE_NAME\` is KernelVerified + Theorem + has a value, in the shard bytes"
else
  cat "$EV/probe_hdr.txt" | sed 's/^/        /'
  bad "\`$PROBE_NAME\` does not satisfy KernelVerified+Theorem+value in the shard bytes"
fi

# --------------------------------------------------------------------------
# 8. the KernelVerified byte cannot be casually forged
# --------------------------------------------------------------------------
say ""
say "== 8. tamper check: forging KernelVerified into a shard is rejected =="
# INTEGRITY, not authenticity: the footer is a blake3 checksum, not a signature.
# This shows the naive attack (flip confidence bytes in an unstamped shard) is
# caught on the LOAD path, not merely by an explicit verify_integrity call.
if [ -n "${NEGSHARD:-}" ]; then
  cp "$NEGSHARD" "$TAMPER/forged.mathverse"
  cp "$OUT/manifest.json" "$TAMPER/manifest.json" 2>/dev/null || true
  python3 - "$TAMPER/forged.mathverse" <<'PYEOF'
import struct, sys
p = sys.argv[1]
b = bytearray(open(p, "rb").read())
(_m, _v, _f, _sc, sdl, lc, ec, cc) = struct.unpack_from("<8I", b, 0)
off = 256 + sdl + lc * 12 + ec * 16
n = 0
for i in range(cc):
    o = off + i * 64
    if b[o + 13] != 0:
        b[o + 13] = 0          # forge ImportConfidence::KernelVerified
        n += 1
open(p, "wb").write(bytes(b))
print("      forged %d confidence bytes to KernelVerified (footer NOT recomputed)" % n)
PYEOF
  python3 - "$TAMPER" "$TAMPER/forged.mathverse" <<'PYEOF'
import json, os, struct, sys
d, p = sys.argv[1], sys.argv[2]
h = struct.unpack_from("<12I", open(p, "rb").read(64), 0)
json.dump({"version": 1,
           "base_shards": [{"path": os.path.basename(p),
                            "content_hash": "local-probe-not-verified",
                            "constant_count": h[7], "expr_count": h[6],
                            "source": "lean4"}],
           "delta_shards": [], "total_constants": h[7], "total_exprs": h[6]},
          open(os.path.join(d, "manifest.json"), "w"), indent=2)
PYEOF
  set +e
  # The probe ABORTS on the rejected load (that IS the pass condition), and the
  # reaping shell announces "Abort trap: 6" on its own stderr. Reap it in a
  # separate `sh -c` whose stderr is discarded, so the expected rejection does
  # not print like a script error.
  sh -c 'MATHVERSE_SHARD_DIR="$1" "$2" >"$3" 2>&1' _ \
      "$TAMPER" "$PROBE_BIN" "$EV/tamper.log" 2>/dev/null
  TRC=$?
  set -e
  if [ "$TRC" != 0 ] && grep -q "ChecksumMismatch" "$EV/tamper.log"; then
    ok "forged shard REJECTED on the load path (ChecksumMismatch), rc=$TRC"
    grep -o 'ChecksumMismatch { expected: "[0-9a-f]\{8\}[^"]*", got: "[0-9a-f]\{8\}[^"]*" }' \
      "$EV/tamper.log" | head -1 | sed 's/^/        /' || true
  elif [ "$TRC" != 0 ]; then
    ok "forged shard rejected (rc=$TRC), though not via ChecksumMismatch:"
    tail -3 "$EV/tamper.log" | sed 's/^/        /'
  else
    bad "forged shard LOADED AND CLOSED A GOAL — the confidence byte is forgeable"
  fi
else
  bad "no negative-control shard to tamper with; check 4 must have failed"
fi

# --------------------------------------------------------------------------
# 9. THE PAYOFF — cite the Mathlib theorem at TrustGate::Strict
# --------------------------------------------------------------------------
say ""
say "== 9. payoff: a Mathlib theorem cited from a Clean proof at TrustGate::Strict =="
set +e
MATHVERSE_SHARD_DIR="$OUT" MATHVERSE_PROBE_NAME="$PROBE_NAME" \
  "$PROBE_BIN" >"$EV/citation.log" 2>&1
PRC=$?
set -e
sed 's/^/      /' "$EV/citation.log"
if [ "$PRC" = 0 ] && grep -q "GOAL CLOSED by kernel-verified library content via" "$EV/citation.log"; then
  ok "$(grep -m1 'GOAL CLOSED' "$EV/citation.log")"
elif grep -q "Unknown constant:" "$EV/citation.log"; then
  bad "COVERAGE gap, not a trust failure: a closure member is declared in a module"
  say "      outside this shard. Remedy: add that module's .olean to the SAME"
  say "      stamp-verified invocation (marginal cost ~0.03s/module; phase A does"
  say "      not amortize across separate invocations). Do NOT use"
  say "      MATHVERSE_PRELOAD_OLEAN — the olean loader registers UNCHECKED, which"
  say "      would void the claim."
else
  bad "citation probe did not close the goal (rc=$PRC)"
fi

# --------------------------------------------------------------------------
# 10. OPTIONAL — is the payoff a one-off? (MLMV_SWEEP=1, adds ~2 min)
# --------------------------------------------------------------------------
if [ "${MLMV_SWEEP:-0}" = "1" ]; then
  say ""
  say "== 10. sweep: every KernelVerified THEOREM in the shard, through Strict =="
  python3 - "$SHARD" >"$EV/kv_theorems.txt" <<'PYEOF'
import io, struct, sys, zstandard
raw = open(sys.argv[1], "rb").read()
(_m, _v, _f, sc, sdl, lc, ec, cc) = struct.unpack_from("<8I", raw, 0)
off = 256 + sdl + lc * 12 + ec * 16
buf = io.BytesIO(zstandard.ZstdDecompressor().decompressobj()
                 .decompress(raw[256:256 + sdl]))
names = []
for _ in range(sc):
    n = buf.read(4)
    if len(n) < 4:
        break
    names.append(buf.read(struct.unpack("<I", n)[0]).decode("utf-8", "replace"))
for i in range(cc):
    o = off + i * 64
    (ni,) = struct.unpack_from("<I", raw, o)
    if raw[o + 13] == 0 and raw[o + 15] == 0:      # KernelVerified AND Theorem
        print(names[ni])
PYEOF
  : > "$EV/sweep_closed.txt"; : > "$EV/sweep_notclosed.txt"
  while IFS= read -r n; do
    set +e
    out=$(MATHVERSE_SHARD_DIR="$OUT" MATHVERSE_PROBE_NAME="$n" "$PROBE_BIN" 2>&1)
    rc=$?
    set -e
    if [ "$rc" = 0 ] && printf '%s' "$out" | grep -q "GOAL CLOSED"; then
      printf '%s\n' "$n" >> "$EV/sweep_closed.txt"
    else
      why=$(printf '%s' "$out" | grep -oE "Unknown constant: [^ \"]+|UnknownConst|does not unify|not a theorem declaration" | head -1)
      printf '%s\t%s\n' "$n" "${why:-other}" >> "$EV/sweep_notclosed.txt"
    fi
  done < "$EV/kv_theorems.txt"
  NCLOSED=$(wc -l < "$EV/sweep_closed.txt" | tr -d ' ')
  NTOTAL=$(wc -l < "$EV/kv_theorems.txt" | tr -d ' ')
  say "      $NCLOSED / $NTOTAL KernelVerified theorems close the goal at Strict"
  say "      non-closing reasons (all COVERAGE or SEARCH, none trust/gate):"
  # `cut -f2`, not sed — BSD sed does not interpret \t in a bracket expression,
  # so a sed-based field strip silently leaves the constant name attached and
  # the histogram degenerates into one row per constant.
  cut -f2 "$EV/sweep_notclosed.txt" \
    | sed 's/Unknown constant: .*/coverage: a closure member is declared outside this shard/;
           s/^UnknownConst$/coverage: a closure member is declared outside this shard/;
           s/^does not unify$/search: premise selection ranked a different lemma (exact TypeMismatch)/;
           s/^not a theorem declaration$/search: premise selection returned a Definition, not a Theorem/' \
    | sort | uniq -c | sort -rn | sed 's/^/        /'
  if [ "$NCLOSED" -ge 2 ]; then
    ok "$NCLOSED distinct Mathlib theorems cite at Strict — not a single-constant artifact"
  else
    bad "only $NCLOSED constant(s) close; the result may be a one-off"
  fi
  # A trust/gate refusal would read "below Strict" WITHOUT the candidate-kind
  # clause. That must never appear: it would mean a closure member was admitted
  # or refused on confidence, i.e. the shard is not uniformly kernel-verified.
  if grep -q "below Strict" "$EV/sweep_notclosed.txt" 2>/dev/null; then
    bad "a constant was refused on TRUST (below Strict) — the shard is not uniformly KernelVerified"
  else
    ok "zero refusals on trust: no closure member was rejected for confidence"
  fi
fi

# --------------------------------------------------------------------------
say ""
say "== summary =="
say "      shard          $SHARD"
say "      evidence       $EV"
say "      KernelVerified $BYTE_KV Mathlib constants (independently decoded from shard bytes)"
say "      probe          $PROBE_NAME"
say ""
if [ "$FAIL" = 0 ]; then
  say "ALL CHECKS PASSED"
  say "A Clean proof can cite Mathlib via mathverse at TrustGate::Strict."
else
  say "SOME CHECKS FAILED (see above)"
fi
exit "$FAIL"
