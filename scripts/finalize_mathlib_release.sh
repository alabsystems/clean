#!/usr/bin/env bash
# Finalize the Mathlib kernel-verification into a single shard set +
# release manifest, and print the aggregate trust distribution.
#
# Run AFTER scripts/rebuild_mathlib_kv.sh completes (all chunks done).
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
KV="${KV:-$REPO_ROOT/data/mathverse-library/mathlib-kv}"
REL="${1:-$REPO_ROOT/data/mathverse-library/mathlib-release}"
VERSION="${2:-1.3.0}"
MV_SHARD="${MV_SHARD:-$REPO_ROOT/target/release/mathverse_shard}"

echo "=== Finalizing Mathlib kernel-verified release v$VERSION ==="
mkdir -p "$REL/shards"

# 1. Gather all stamped shards into one dir, prefixing by chunk to avoid stem
#    collisions (stamp-verified dedups stems only within a single invocation).
total_shards=0
for d in "$KV"/shards_*; do
  [ -d "$d" ] || continue
  cn=$(basename "$d")          # shards_01
  for s in "$d"/*.mathverse; do
    [ -f "$s" ] || continue
    cp "$s" "$REL/shards/${cn}__$(basename "$s")"
    total_shards=$((total_shards+1))
  done
done
echo "Collected $total_shards stamped shards into $REL/shards"

# 2. Aggregate kernel-verified counts from the per-chunk JSON summaries.
python3 - "$KV" "$REL" "$VERSION" <<'PY'
import json,sys,glob,re,os
kv,rel,version=sys.argv[1],sys.argv[2],sys.argv[3]
agg=dict(version=version,oleans_converted=0,total=0,kernel_verified=0,
         axiom_accepted=0,axiom_fallback=0,failed=0,stored_kernel_verified=0,chunks=0)
for log in sorted(glob.glob(os.path.join(kv,'chunk_*.log'))):
    t=open(log).read(); m=re.search(r'\{.*\}',t,re.S)
    if not m: continue
    try: d=json.loads(m.group(0))
    except Exception: continue
    agg['chunks']+=1
    for k in ('oleans_converted','total','kernel_verified','axiom_accepted',
              'axiom_fallback','failed','stored_kernel_verified'):
        agg[k]+=d.get(k,0)
tot=agg['total'] or 1
agg['kernel_verified_pct']=round(100*agg['kernel_verified']/tot,2)
open(os.path.join(rel,'AGGREGATE.json'),'w').write(json.dumps(agg,indent=2))
print(json.dumps(agg,indent=2))
print(f"\nGENUINE kernel-verified: {agg['kernel_verified']} / {agg['total']} "
      f"({agg['kernel_verified_pct']}%) across {agg['chunks']} chunks")
PY

# 3. Integrity-verify the collected shards (blake3) if the tool is present.
if [ -x "$MV_SHARD" ]; then
  echo "=== shard integrity (blake3) ==="
  "$MV_SHARD" verify "$REL/shards" 2>&1 | tail -5 || true
fi

echo "=== DONE. Release shards: $REL/shards ; aggregate: $REL/AGGREGATE.json ==="
