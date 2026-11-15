#!/bin/zsh
# build_mir_sysroot.sh <seal-dir> <out-sysroot> [<work-dir>]
#
# Crystal D3 (decision memo 2026-09-23 §5 D3, §12, §19): build a RESIDENT MIR-encoded sysroot
# for ONE sealed Trust driver, prove it, and write a content manifest. "The MIR sysroot" is the
# sha256 of <out-sysroot>/MIR_SYSROOT_MANIFEST.json, never a directory name.
#
# A sysroot is bound to the compiler that built it, so the seal is the only positional input that
# selects the compiler; everything else is pinned and REFUSED on disagreement:
#   - the seal's own SHA256 file must match its rustc-main and librustc_driver dylib;
#   - the base sysroot is the seal's compile sysroot (`$SEAL/SYSROOT`), and the seal's `tc` must
#     pass exactly that `--sysroot`;
#   - the library source is the base sysroot's `lib/rustlib/src/rust`, a git tree whose `library/`
#     tree id must equal LIB_TREE_PIN and carry no uncommitted change;
#   - cargo is recorded by path, version and sha256 (CARGO overrides the path).
#
# THE RECIPE, and why each part is load-bearing (measured 2026-09-21/22, backlog row 3):
#   - `-Zbuild-std=std,core,alloc,panic_abort,panic_unwind` with `profile.release.panic="unwind"`:
#     std is always compiled at panic=unwind (a panic=abort crate may link an unwind std, never the
#     reverse), and build scripts always compile at unwind, so both panic halves must be present.
#     cargo adds proc_macro (and its rustc_literal_escaper) when std is requested.
#   - `panic_abort` itself at `-Cpanic=abort` (`-Zprofile-rustflags` + a package override): the
#     library workspace's own `[profile.*.package.panic_abort] rustflags` never reaches a
#     build-std unit, so without the override panic_abort is compiled at unwind and NO panic=abort
#     binary can link ("the crate `panic_abort` does not have the panic strategy `abort`").
#     MEASURED 2026-09-25: the lane's prebuilt control sysroot-v13 (laneREG bs-REG.sh, the same
#     cargo build-std route without the override) has exactly that defect; every lane dump is
#     `--lib`, so nothing linked a panic=abort binary against it and nobody saw it.
#   - `-Zalways-encode-mir` in the TARGET rustflags: std's non-generic, non-inline bodies get
#     encoded MIR, which is the whole point.
#   - `-Zhost-config -Ztarget-applies-to-host` plus `target-applies-to-host=false` and an explicit
#     `host.rustflags`: with `--target`, the RUSTFLAGS env var reaches target units only, so host
#     units (std's build scripts) need their own `-Ztrust-verify=off` or the verifier fails them.
#   - The crates are INSTALLED RESIDENT in a copy of the base sysroot. `-Zbuild-std` alone cannot
#     be used for a dump: rustc spells non-resident std as `__trust_crate@<hash>::`, which is
#     `sysroot_authenticated_def_path_str`'s anti-impersonation SECURITY STAMP. Never strip it.
#   - The build-std user crate is a DEPENDENCY-FREE probe. The old recipe built std beside
#     clean-kernel, whose deps dir then held two builds of hashbrown/cfg_if/libc/memchr and had to
#     be disambiguated by iterating on E0460. With no user dependency there is exactly one build of
#     each crate; a second candidate is REFUSED rather than guessed.
#
# PROOF (all must hold, else exit 1 and the sysroot is left for inspection but NOT manifested):
#   S1 a binary compiles and runs at panic=unwind; S2 the same at panic=abort;
#   S3 a proc-macro crate compiles and is used by a binary that runs (proc_macro/std coherence);
#   S4 MIR really is encoded: a sidecar probe rooted at a local fn calling `std::process::id` (a
#      non-generic, non-inline std fn) finds it NOT walkable on the base sysroot (control) and a
#      block-equal MEMBER on the new one;
#   S5 `seal_driver.sh sysrootcheck` accepts the pair.
#
# OUTPUTS: <out-sysroot>/ (the sysroot, with a `tc` wrapper = the seal's own wrapper with only its
# `--sysroot` changed), <out-sysroot>/MIR_SYSROOT_MANIFEST.json (IDENTITY: every installed file's
# sha256, the driver, the base, the library tree, the recipe; no timestamps, no work paths), and
# <out-sysroot>/BUILD.json (the run: times, smoke outputs; not identity). The work dir (build-std
# target dir, probes) is DELETED on success (KEEP_WORK=1 keeps it).
#
# Heavy: run it under the gate, e.g.
#   scripts/heavy_gate.sh run 13 mirsysroot -- zsh build_mir_sysroot.sh <seal> <out> <work>
# (the recorded analogue, build-std WITH clean-kernel at fuel 64, peaked 8.36 GB in 3m42s).
set -euo pipefail
export PATH=/usr/bin:/bin:/usr/sbin:/sbin
HOST=aarch64-apple-darwin
SEAL_IN=${1:?usage: build_mir_sysroot.sh <seal-dir> <out-sysroot> [<work-dir>]}
OUT_IN=${2:?usage: build_mir_sysroot.sh <seal-dir> <out-sysroot> [<work-dir>]}
SEAL=${SEAL_IN:A}
OUT=${OUT_IN:A}
WORK=${3:-$OUT.work}
WORK=${WORK:A}
SELF=${0:A}
CARGO=${CARGO:-$HOME/trust/build/$HOST/stage2/bin/cargo}
PY=/usr/bin/python3
LIB_TREE_PIN=${LIB_TREE_PIN:-4e89e4dee0b59012907a3988539491a0a8142baf}
# library/Cargo.toml patches memchr to ../crates/trust-memchr, so that tree is library source too.
MEMCHR_TREE_PIN=${MEMCHR_TREE_PIN:-$(git -C $HOME/trust/scratchpad/laneREG/wt rev-parse HEAD:crates/trust-memchr 2>/dev/null || echo unset)}
BUILD_STD="std,core,alloc,panic_abort,panic_unwind"
STD_RUSTFLAGS="-Ztrust-verify=off -Cdebuginfo=0 -Zalways-encode-mir"
HOST_RUSTFLAGS='["-Ztrust-verify=off"]'
T0=$(date +%s)

refuse() { echo "REFUSED: $*" >&2; exit 2; }
fail() { echo "FAILED: $*" >&2; exit 1; }
sha() { shasum -a 256 "$1" | cut -d' ' -f1; }

# ---- pinned inputs --------------------------------------------------------------------------
[[ -e $OUT ]] && refuse "$OUT exists (never overwritten; remove it by hand first)"
[[ -e $WORK ]] && refuse "$WORK exists"
[[ -x $SEAL/tc && -f $SEAL/rustc-main && -f $SEAL/SHA256 && -f $SEAL/SYSROOT ]] || refuse "$SEAL is not a sealed driver"
DYLIB=( $SEAL/librustc_driver_*.dylib(N) )
(( ${#DYLIB} == 1 )) || refuse "$SEAL must hold exactly one librustc_driver_*.dylib"
( cd / && shasum -a 256 -c "$SEAL/SHA256" >/dev/null ) || refuse "$SEAL/SHA256 does not match the sealed files"
BASE=$(head -1 "$SEAL/SYSROOT")
[[ -d $BASE/lib/rustlib/$HOST/lib ]] || refuse "base sysroot $BASE has no $HOST lib dir"
(( $(grep -c -- "--sysroot \"$BASE\"" "$SEAL/tc") == 1 )) || refuse "$SEAL/tc does not pass --sysroot \"$BASE\" exactly once"
LIBSRC=$BASE/lib/rustlib/src/rust
LIBSRC=${LIBSRC:A}
[[ -d $LIBSRC/library ]] || refuse "no library source at $LIBSRC"
LIB_TREE=$(git -C "$LIBSRC" rev-parse HEAD:library)
LIB_HEAD=$(git -C "$LIBSRC" rev-parse HEAD)
[[ $LIB_TREE == $LIB_TREE_PIN ]] || refuse "library tree $LIB_TREE != pin $LIB_TREE_PIN ($LIBSRC)"
[[ -z $(git -C "$LIBSRC" status --porcelain -- library crates/trust-memchr) ]] || refuse "library source $LIBSRC/{library,crates/trust-memchr} has uncommitted changes"
MEMCHR_TREE=$(git -C "$LIBSRC" rev-parse HEAD:crates/trust-memchr)
[[ $MEMCHR_TREE == $MEMCHR_TREE_PIN ]] || refuse "crates/trust-memchr tree $MEMCHR_TREE != pin $MEMCHR_TREE_PIN"
[[ -x $CARGO ]] || refuse "no cargo at $CARGO"
DYLD_STAGE1=$(sed -n 's/^DYLD_LIBRARY_PATH="\([^$]*\)\${.*/\1/p' "$SEAL/tc" | head -1)
[[ -n $DYLD_STAGE1 && -d $DYLD_STAGE1 ]] || refuse "cannot read the seal's DYLD_LIBRARY_PATH from $SEAL/tc"
echo "=== build_mir_sysroot seal=$SEAL out=$OUT work=$WORK"
echo "    base=$BASE libsrc=$LIBSRC head=$LIB_HEAD library_tree=$LIB_TREE"
echo "    cargo=$CARGO $("$CARGO" --version)"

mkdir -p "$WORK/probe/src"
# ---- build std with the seal ----------------------------------------------------------------
cat > "$WORK/probe/Cargo.toml" <<'EOF'
[package]
name = "crystal_mir_sysroot_probe"
version = "0.0.0"
edition = "2021"
publish = false

[dependencies]

[workspace]
EOF
print -r -- 'fn main() { println!("ok"); }' > "$WORK/probe/src/main.rs"
cd "$WORK/probe"
echo "=== build-std $(date -u +%FT%TZ)"
env -u CARGO_ENCODED_RUSTFLAGS -u CARGO_BUILD_RUSTFLAGS -u RUSTC_WRAPPER \
  CARGO_TARGET_DIR="$WORK/target" RUSTC="$SEAL/tc" RUSTC_BOOTSTRAP=1 RUSTFLAGS="$STD_RUSTFLAGS" \
  "$CARGO" -Zbuild-std="$BUILD_STD" -Zhost-config -Ztarget-applies-to-host -Zprofile-rustflags \
    --config 'target-applies-to-host=false' --config "host.rustflags=$HOST_RUSTFLAGS" \
    --config 'profile.release.panic="unwind"' \
    --config 'profile.release.package.panic_abort.rustflags=["-Cpanic=abort"]' \
    build --release --target $HOST -v > "$WORK/build-std.log" 2>&1 \
  || { tail -30 "$WORK/build-std.log"; fail "build-std (log $WORK/build-std.log)"; }
T1=$(date +%s)
echo "=== build-std done in $((T1-T0)) s"
DEPS=$WORK/target/$HOST/release/deps
PA_LINE=$(grep -E 'Running .*--crate-name panic_abort ' "$WORK/build-std.log" | tail -1)
[[ $PA_LINE == *'-Cpanic=abort'* ]] || fail "panic_abort was not compiled with -Cpanic=abort"
PU_LINE=$(grep -E 'Running .*--crate-name std ' "$WORK/build-std.log" | tail -1)
[[ $PU_LINE != *'-Cpanic=abort'* && $PU_LINE != *'panic=abort'* ]] || fail "std was compiled at panic=abort"
[[ $PU_LINE == *'-Zalways-encode-mir'* ]] || fail "std was compiled without -Zalways-encode-mir"

# ---- install resident ----------------------------------------------------------------------
cp -R "$BASE" "$OUT"
NEWLIB=$OUT/lib/rustlib/$HOST/lib
BASE_STEMS=( ${(f)"$(ls $BASE/lib/rustlib/$HOST/lib/*.rlib | sed 's#.*/lib##; s#-[0-9a-f]\{16\}\.rlib$##' | sort -u)"} )
NEW_STEMS=( ${(f)"$(ls $DEPS/*.rlib | sed 's#.*/lib##; s#-[0-9a-f]\{16\}\.rlib$##' | grep -v '^crystal_mir_sysroot_probe$' | sort -u)"} )
for st in "${BASE_STEMS[@]}"; do
  (( ${NEW_STEMS[(Ie)$st]} )) || fail "base crate $st was not rebuilt; a stale crate from another compiler would stay resident"
done
rm -f "$NEWLIB"/*.rlib "$NEWLIB"/*.rmeta
for st in "${NEW_STEMS[@]}"; do
  cands=( $DEPS/lib${st}-*.rlib(N) )
  (( ${#cands} == 1 )) || fail "crate $st has ${#cands} builds in $DEPS (a dependency-free probe must give one)"
  cp "${cands[1]}" "$NEWLIB/"
  m=${cands[1]%.rlib}.rmeta; [[ -f $m ]] && cp "$m" "$NEWLIB/"
done
echo "=== installed ${#NEW_STEMS} crates (base had ${#BASE_STEMS}); new stems: ${NEW_STEMS:|BASE_STEMS}"
sed "s#--sysroot \"$BASE\"#--sysroot \"$OUT\"#" "$SEAL/tc" > "$OUT/tc"
chmod +x "$OUT/tc"
(( $(grep -c -- "--sysroot \"$OUT\"" "$OUT/tc") == 1 )) || fail "tc wrapper rewrite"
diff <(sed "s#--sysroot \"$OUT\"#--sysroot \"$BASE\"#" "$OUT/tc") "$SEAL/tc" >/dev/null || fail "tc differs from the seal's beyond --sysroot"

# ---- proof ----------------------------------------------------------------------------------
P=$WORK/smoke; mkdir -p "$P"
cd "$P"
print -r -- 'fn main(){println!("ok");}' > s.rs
RUSTC_BOOTSTRAP=1 "$OUT/tc" --edition 2021 -O -Ztrust-verify=off -o s_unwind s.rs > s1.log 2>&1 || { cat s1.log; fail S1; }
S1=$(./s_unwind); [[ $S1 == ok ]] || fail "S1 printed '$S1'"
RUSTC_BOOTSTRAP=1 "$OUT/tc" --edition 2021 -O -Cpanic=abort -Ztrust-verify=off -o s_abort s.rs > s2.log 2>&1 || { cat s2.log; fail S2; }
S2=$(./s_abort); [[ $S2 == ok ]] || fail "S2 printed '$S2'"
cat > pm.rs <<'EOF'
extern crate proc_macro;
use proc_macro::TokenStream;
#[proc_macro]
pub fn ok_pm(_i: TokenStream) -> TokenStream { "\"ok-pm\"".parse().unwrap() }
EOF
print -r -- 'fn main(){println!("{}", pm::ok_pm!());}' > usepm.rs
RUSTC_BOOTSTRAP=1 "$OUT/tc" --edition 2021 --crate-type proc-macro --crate-name pm -Ztrust-verify=off -o libpm.dylib pm.rs > s3a.log 2>&1 || { cat s3a.log; fail S3a; }
RUSTC_BOOTSTRAP=1 "$OUT/tc" --edition 2021 -Ztrust-verify=off --extern pm=libpm.dylib -o usepm usepm.rs > s3b.log 2>&1 || { cat s3b.log; fail S3b; }
S3=$(./usepm); [[ $S3 == ok-pm ]] || fail "S3 printed '$S3'"
# An rlib, like every lane dump: the base sysroot cannot link a panic=abort binary (see above).
print -r -- 'pub fn crystal_probe() -> bool { std::process::id() > 0 }' > mirprobe.rs
for side in base mir; do
  tcx=$SEAL/tc; [[ $side == mir ]] && tcx=$OUT/tc
  mkdir -p "dump-$side"
  RUSTC_BOOTSTRAP=1 TRUST_CALLEE_SIDECAR_FUEL=4096 "$tcx" --edition 2021 --crate-name mirprobe --crate-type rlib \
    -O -Cpanic=abort -Ztrust-verify=off -Ztrust-ir-lower=on -Ztrust-ir-callee-sidecar=local:crystal_probe \
    -Ztrust-dump=ir:"$P/dump-$side" -o "libmirprobe-$side.rlib" mirprobe.rs > "s4-$side.log" 2>&1 \
    || { tail -20 "s4-$side.log"; fail "S4 $side compile"; }
done
S4=$("$PY" - "$P/dump-base" "$P/dump-mir" <<'EOF'
import glob, json, sys
def load(d):
    ms = glob.glob(d + "/callees/*.callees.manifest.json")
    assert len(ms) == 1, (d, ms)
    return json.load(open(ms[0]))
def is_id(name):
    return name == "std::process::id" or name.startswith("std::process::id::<")
base, mir = load(sys.argv[1]), load(sys.argv[2])
b_mem = [m for m in base["members"] if is_id(m["name"])]
b_esc = [e for e in base["escaping"] if "std::process::id" in e and "mir" in e.lower()]
m_mem = [m for m in mir["members"] if is_id(m["name"])]
ok = (not b_mem) and len(b_esc) >= 1 and len(m_mem) == 1 and m_mem[0]["mir_blocks"] == m_mem[0]["extracted_blocks"] > 0
print(json.dumps({"ok": ok, "base_member": len(b_mem), "base_escaping": b_esc[:2],
                  "mir_member": [{k: m[k] for k in ("name", "mir_blocks", "extracted_blocks", "mir_digest")} for m in m_mem],
                  "base_members": len(base["members"]), "mir_members": len(mir["members"])}, sort_keys=True))
EOF
)
echo "S4 $S4"
[[ $S4 == *'"ok": true'* ]] || fail "S4: std::process::id is not a member on the new sysroot, or is one on the base"
S5=$(TRUST_REPO_ROOT=$HOME/trust $HOME/trust/scripts/seal_driver.sh sysrootcheck "$SEAL" --sysroot "$OUT" 2>&1 | tail -1)
[[ $S5 == *OK* ]] || fail "S5 sysrootcheck: $S5"
echo "S1=$S1 S2=$S2 S3=$S3 S5=$S5"

# ---- manifest -------------------------------------------------------------------------------
VV=$("$SEAL/tc" -vV 2>/dev/null | tr '\n' '|')
"$PY" - "$OUT" "$SEAL" "$BASE" "$LIBSRC" "$LIB_HEAD" "$LIB_TREE:$MEMCHR_TREE" "$CARGO" "$("$CARGO" --version)" \
  "$SELF" "$BUILD_STD" "$STD_RUSTFLAGS" "$HOST_RUSTFLAGS" "$HOST" "$DYLD_STAGE1" "$VV" <<'EOF'
import hashlib, json, os, sys
(out, seal, base, libsrc, lib_head, lib_tree, cargo, cargo_ver, script, build_std, std_rf, host_rf,
 host, dyld, vv) = sys.argv[1:]
def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()
def tree(root):
    res = {}
    for dp, dn, fn in os.walk(root):
        dn.sort()
        for f in sorted(fn):
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, root)
            res[rel] = ("symlink:" + os.readlink(p)) if os.path.islink(p) else sha(p)
    return res
def first(p):
    try:
        return open(p).readline().strip()
    except OSError:
        return None
libdir = os.path.join("lib", "rustlib", host, "lib")
installed = {k: v for k, v in tree(out).items() if k.startswith(libdir + os.sep)}
dylib = [f for f in os.listdir(seal) if f.startswith("librustc_driver_") and f.endswith(".dylib")][0]
man = {
    "schema": "crystal-mir-sysroot-manifest/1",
    "meaning": "a RESIDENT sysroot whose std crates carry encoded MIR for every body (-Zalways-encode-mir), "
               "built by exactly this driver from exactly this library tree; identity is this file's sha256",
    "driver": {
        "seal_dir": seal,
        "REV": first(os.path.join(seal, "REV")), "TREE": first(os.path.join(seal, "TREE")),
        "SRC_ROOT": first(os.path.join(seal, "SRC_ROOT")),
        "SHARED_ROOT_REV": first(os.path.join(seal, "SHARED_ROOT_REV")),
        "rustc_main_sha256": sha(os.path.join(seal, "rustc-main")),
        "librustc_driver": dylib, "librustc_driver_sha256": sha(os.path.join(seal, dylib)),
        "seal_tc_sha256": sha(os.path.join(seal, "tc")),
        "dyld_stage1_libstd": {f: sha(os.path.join(dyld, f)) for f in sorted(os.listdir(dyld)) if f.startswith("libstd-") and f.endswith(".dylib")},
        "rustc_vV": vv,
    },
    "base_sysroot": {"path": base, "lib": {k: v for k, v in tree(base).items() if k.startswith(libdir + os.sep)}},
    "library_source": {"path": libsrc, "head": lib_head, "library_tree": lib_tree.split(":")[0],
                       "crates_trust_memchr_tree": lib_tree.split(":")[1], "uncommitted_under_either": 0},
    "recipe": {
        "script_sha256": sha(script), "cargo": {"path": cargo, "version": cargo_ver, "sha256": sha(cargo)},
        "build_std": build_std, "target": host, "target_rustflags": std_rf, "host_rustflags": host_rf,
        "profile_release_panic": "unwind", "panic_abort_rustflags": ["-Cpanic=abort"],
        "user_crate": "dependency-free probe (crystal_mir_sysroot_probe)",
    },
    "installed": installed,
    # The wrapper names its own sysroot, so it is hashed with that path replaced by @OUT@: the
    # manifest is then identical wherever the sysroot is installed (measured: a rebuild to another
    # path reproduces all 44 installed files byte for byte).
    "tc_template_sha256": hashlib.sha256(open(os.path.join(out, "tc")).read().replace(out, "@OUT@").encode()).hexdigest(),
}
with open(os.path.join(out, "MIR_SYSROOT_MANIFEST.json"), "w") as f:
    json.dump(man, f, indent=1, sort_keys=True)
    f.write("\n")
print("installed files", len(installed))
EOF
T2=$(date +%s)
DIGEST=$(sha "$OUT/MIR_SYSROOT_MANIFEST.json")
"$PY" - "$OUT/BUILD.json" "$T0" "$T1" "$T2" "$WORK" "$S1" "$S2" "$S3" "$S4" "$S5" "$DIGEST" <<'EOF'
import json, sys
out, t0, t1, t2, work, s1, s2, s3, s4, s5, digest = sys.argv[1:]
json.dump({"schema": "crystal-mir-sysroot-build/1", "manifest_sha256": digest,
           "build_std_wall_s": int(t1) - int(t0), "total_wall_s": int(t2) - int(t0), "work_dir": work,
           "smoke": {"S1_bin_unwind": s1, "S2_bin_abort": s2, "S3_proc_macro": s3,
                     "S4_mir_encoded": json.loads(s4), "S5_sysrootcheck": s5}},
          open(out, "w"), indent=1, sort_keys=True)
EOF
cp "$WORK/build-std.log" "$OUT/build-std.log"
if [[ ${KEEP_WORK:-0} != 1 ]]; then rm -rf "${WORK:?}"; fi
echo "MIR_SYSROOT_MANIFEST sha256=$DIGEST"
echo "BUILD_MIR_SYSROOT_DONE $OUT $(date -u +%FT%TZ)"
