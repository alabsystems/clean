#!/usr/bin/env python3
"""Independent replay of a shard plan's partition proof.

    scripts/verify_shard_partition.py data/suite_plans/clean-verify__lib.json \
        target/verify-runner-pinned/target/debug/deps/clean_verify-<hash>

Deliberately shares NO code with verify_runner.py. It reads the committed plan,
re-derives each shard's argv from the stored fields, asks the TEST BINARY itself
which tests that argv selects, and checks coverage and disjointness with its own
set arithmetic. `shards plan` proving its own cut is a program checking its own
homework; this is a second opinion from a different program, and it also
re-derives the `all_names_sha256` so a plan cannot be silently re-pointed at a
different binary.

If this disagrees with the plan's stored proof, the stored proof is not
evidence. Exit 0 only when every check passes.
"""
import hashlib, json, re, subprocess, sys
from collections import Counter

if len(sys.argv) != 3:
    raise SystemExit(__doc__)
plan = json.load(open(sys.argv[1]))
binary = sys.argv[2]

def list_tests(args):
    out = subprocess.run([binary, "--list"] + args, capture_output=True, text=True, timeout=900)
    if out.returncode != 0:
        raise SystemExit(f"--list failed: {out.stderr[-2000:]}")
    return [m.group(1) for m in (re.match(r"^(\S+): test$", l) for l in out.stdout.splitlines()) if m]

declared = list_tests([])
print(f"declared by the binary            : {len(declared)}")
print(f"declared_total in the plan        : {plan['partition_proof']['declared_total']}")

seen = Counter()
owner = {}
per_shard = []
for shard in plan["shards"]:
    args = (["--exact"] if shard.get("mode") == "exact" else []) + list(shard["filters"])
    for s in shard.get("skip", []):
        args += ["--skip", s]
    got = list_tests(args)
    per_shard.append((shard["key"], shard["test_count"], len(got), shard.get("kind")))
    for n in got:
        seen[n] += 1
        owner.setdefault(n, []).append(shard["key"])

union = set(seen)
dup = [n for n, c in seen.items() if c > 1]
dropped = sorted(set(declared) - union)
alien = sorted(union - set(declared))
total = sum(seen.values())
mismatch = [(k, p, o) for k, p, o, _ in per_shard if p != o]

print()
print(f"{'shard':<20}{'planned':>9}{'observed':>10}  kind")
for k, p, o, kind in sorted(per_shard, key=lambda r: -r[2]):
    print(f"{k:<20}{p:>9}{o:>10}  {kind}")
print()
print(f"sum of per-shard counts           : {total}")
print(f"union size                        : {len(union)}")
print(f"dropped (declared, in no shard)   : {len(dropped)}  {dropped[:5]}")
print(f"duplicated (in >1 shard)          : {len(dup)}  {dup[:5]}")
print(f"alien (in a shard, not declared)  : {len(alien)}  {alien[:5]}")
print(f"shards whose observed != planned  : {len(mismatch)}  {mismatch[:5]}")
print(f"sha256 of sorted declared names   : {hashlib.sha256(chr(10).join(sorted(declared)).encode()).hexdigest()}")
print(f"same, as stored in the plan       : {plan['partition_proof']['all_names_sha256']}")
ok = (not dropped and not dup and not alien and not mismatch
      and total == len(declared) == len(union) == plan['partition_proof']['declared_total'])
print()
print("INDEPENDENT PARTITION PROOF:", "VERIFIED" if ok else "FAILED")
sys.exit(0 if ok else 1)
