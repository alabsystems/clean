# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Audit the default prelude's arithmetic against Lean 4.8.0, verdict by verdict.

Every probe is `theorem pN : <op at an edge operand> = <value> := by decide` (and `:= rfl`),
with the value Lean 4.8.0 computes and wrong values beside it (v+1, and for Int division the
T/E/F-rounding alternatives). Lean 4.8.0's kernel and `clean check` judge each one; the
summary counts the rows where they disagree. Results: reports/2026-10-27-prelude-arith-lean-audit/.

usage: python3 scripts/prelude_arith_lean_audit.py <outdir> <clean-binary> [filter-prefix]
"""
import itertools, json, os, re, subprocess, sys

OUT = sys.argv[1]
CLEAN = sys.argv[2]
FILT = sys.argv[3] if len(sys.argv) > 3 else ""
LEAN8 = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.8.0/bin/lean")
LEAN30 = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean")
os.makedirs(OUT, exist_ok=True)

cases = []  # (family, op, expr, rtype)
ALTS = {}  # case index -> extra wrong values to claim


def add(fam, op, expr, rtype, alts=()):
    cases.append((fam, op, expr, rtype, tuple(str(a) for a in alts)))


def tdm(a, b):
    if b == 0:
        return 0, a
    q = abs(a) // abs(b)
    q = q if (a >= 0) == (b >= 0) else -q
    return q, a - b * q


def edm(a, b):
    if b == 0:
        return 0, a
    r = a % abs(b)
    return (a - r) // b, r


def fdm(a, b):
    if b == 0:
        return 0, a
    return a // b, a - b * (a // b)


def divalts(a, b, which):
    vs = [f(a, b)[which] for f in (tdm, edm, fdm)]
    return sorted(set(vs))


def lit(v, ty):
    if v < 0:
        return f"(-{-v} : {ty})"
    return f"({v} : {ty})"


# ---- Nat ----
NV = [0, 1, 2, 7, 255, 256, 2**64 - 1, 2**64]
for op, sym in [("add", "+"), ("sub", "-"), ("mul", "*"), ("div", "/"), ("mod", "%"),
                ("land", "&&&"), ("lor", "|||"), ("xor", "^^^")]:
    for a, b in itertools.product(NV, NV):
        add("Nat", op, f"{lit(a,'Nat')} {sym} {lit(b,'Nat')}", "Nat")
for a, b in itertools.product(NV, [0, 1, 3, 8, 63, 64, 65]):
    add("Nat", "shiftLeft", f"{lit(a,'Nat')} <<< {lit(b,'Nat')}", "Nat")
    add("Nat", "shiftRight", f"{lit(a,'Nat')} >>> {lit(b,'Nat')}", "Nat")
for a, b in itertools.product([0, 1, 2, 3, 10], [0, 1, 2, 7, 64]):
    add("Nat", "pow", f"{lit(a,'Nat')} ^ {lit(b,'Nat')}", "Nat")
for a, b in itertools.product([0, 1, 6, 12, 2**64], [0, 1, 4, 18]):
    add("Nat", "gcd", f"Nat.gcd {lit(a,'Nat')} {lit(b,'Nat')}", "Nat")
    add("Nat", "lcm", f"Nat.lcm {lit(a,'Nat')} {lit(b,'Nat')}", "Nat")
for a in [0, 1, 2, 3, 255, 256, 2**64]:
    add("Nat", "log2", f"Nat.log2 {lit(a,'Nat')}", "Nat")
    add("Nat", "pred", f"Nat.pred {lit(a,'Nat')}", "Nat")
for a, b in itertools.product([0, 1, 7, 2**64], [0, 1, 7, 2**64]):
    add("Nat", "beq", f"Nat.beq {lit(a,'Nat')} {lit(b,'Nat')}", "Bool")
    add("Nat", "ble", f"Nat.ble {lit(a,'Nat')} {lit(b,'Nat')}", "Bool")
    add("Nat", "blt", f"Nat.blt {lit(a,'Nat')} {lit(b,'Nat')}", "Bool")
    add("Nat", "min", f"min {lit(a,'Nat')} {lit(b,'Nat')}", "Nat")
    add("Nat", "max", f"max {lit(a,'Nat')} {lit(b,'Nat')}", "Nat")

# ---- Int ----
IV = [0, 1, -1, 2, -2, 7, -7, 256, -256]
IVBIG = [2**63, -(2**63), 2**64, -(2**64), 2**127, -(2**127) - 1]
WH = {"div(/)": 0, "mod(%)": 1, "Int.div": 0, "Int.mod": 1, "Int.ediv": 0, "Int.emod": 1,
      "Int.fdiv": 0, "Int.fmod": 1}
for op, sym in [("add", "+"), ("sub", "-"), ("mul", "*"), ("div(/)", "/"), ("mod(%)", "%")]:
    for a, b in itertools.product(IV, IV):
        add("Int", op, f"{lit(a,'Int')} {sym} {lit(b,'Int')}", "Int",
            divalts(a, b, WH[op]) if op in WH else ())
    for a, b in itertools.product(IVBIG, [1, -1, 7, -7, 0]):
        add("Int", op, f"{lit(a,'Int')} {sym} {lit(b,'Int')}", "Int",
            divalts(a, b, WH[op]) if op in WH else ())
for fn in ["Int.div", "Int.mod", "Int.ediv", "Int.emod", "Int.fdiv", "Int.fmod"]:
    for a, b in itertools.product(IV, IV):
        add("Int", fn, f"{fn} {lit(a,'Int')} {lit(b,'Int')}", "Int", divalts(a, b, WH[fn]))
    for a, b in itertools.product(IVBIG, [7, -7, 0, -1]):
        add("Int", fn, f"{fn} {lit(a,'Int')} {lit(b,'Int')}", "Int", divalts(a, b, WH[fn]))
for a in IV + IVBIG:
    add("Int", "neg", f"-{lit(a,'Int')}", "Int")
    add("Int", "natAbs", f"Int.natAbs {lit(a,'Int')}", "Nat")
    add("Int", "toNat", f"Int.toNat {lit(a,'Int')}", "Nat")
    add("Int", "sign", f"Int.sign {lit(a,'Int')}", "Int")
for a, b in itertools.product([0, 1, -1, 7, -7, 2**64, -(2**64)], [0, 1, -1, 7, -7]):
    add("Int", "lt", f"decide ({lit(a,'Int')} < {lit(b,'Int')})", "Bool")
    add("Int", "le", f"decide ({lit(a,'Int')} ≤ {lit(b,'Int')})", "Bool")
    add("Int", "beq", f"({lit(a,'Int')} == {lit(b,'Int')})", "Bool")
    add("Int", "min", f"min {lit(a,'Int')} {lit(b,'Int')}", "Int")
    add("Int", "max", f"max {lit(a,'Int')} {lit(b,'Int')}", "Int")
for a, b in itertools.product([0, 1, -1, 2, -2, -3], [0, 1, 2, 3]):
    add("Int", "pow", f"{lit(a,'Int')} ^ {lit(b,'Nat')}", "Int")
for a, b in itertools.product([0, 1, -1, 7, -7, -256], [0, 1, 3, 64]):
    add("Int", "shiftRight", f"{lit(a,'Int')} >>> {lit(b,'Nat')}", "Int")
for a in [0, 5, -5]:
    add("Int", "subNatNat", f"Int.subNatNat {lit(abs(a),'Nat')} 7", "Int")
    add("Int", "negSucc", f"Int.negSucc {lit(abs(a),'Nat')}", "Int")

# ---- Fin ----
for n in [1, 5, 256]:
    fv = sorted({0, 1, min(3, n - 1), n - 1})
    ty = f"Fin {n}"
    for op, sym in [("add", "+"), ("sub", "-"), ("mul", "*"), ("div", "/"), ("mod", "%")]:
        for a, b in itertools.product(fv, fv):
            add("Fin", op, f"{lit(a,ty)} {sym} {lit(b,ty)}", ty)
    for a in [0, 1, n, n + 2, 1000]:
        add("Fin", "ofNat-lit", f"{lit(a,ty)}", ty)
    for a in fv:
        add("Fin", "val", f"Fin.val {lit(a,ty)}", "Nat")
        add("Fin", "neg", f"-{lit(a,ty)}", ty)

# ---- UIntN ----
for w, ty in [(8, "UInt8"), (16, "UInt16"), (32, "UInt32"), (64, "UInt64")]:
    m = 2**w
    uv = [0, 1, 2, 7, m // 2, m - 1]
    for op, sym in [("add", "+"), ("sub", "-"), ("mul", "*"), ("div", "/"), ("mod", "%"),
                    ("land", "&&&"), ("lor", "|||"), ("xor", "^^^")]:
        for a, b in itertools.product(uv, uv):
            add(ty, op, f"{lit(a,ty)} {sym} {lit(b,ty)}", ty)
    for a, b in itertools.product([1, m - 1, 7], [0, 1, w - 1, w, w + 1, 2 * w + 3]):
        add(ty, "shiftLeft", f"{lit(a,ty)} <<< {lit(b,ty)}", ty)
        add(ty, "shiftRight", f"{lit(a,ty)} >>> {lit(b,ty)}", ty)
    for a in [0, 1, m - 1, m, m + 5, 3 * m + 1]:
        add(ty, "ofNat-lit", f"{lit(a,ty)}", ty)
    for a in [0, 1, m - 1]:
        add(ty, "complement", f"~~~{lit(a,ty)}", ty)
        add(ty, "toNat", f"UInt{w}.toNat {lit(a,ty)}", "Nat")
    for a, b in itertools.product([0, 1, m - 1], [0, 1, m - 1]):
        add(ty, "lt", f"decide ({lit(a,ty)} < {lit(b,ty)})", "Bool")
        add(ty, "le", f"decide ({lit(a,ty)} ≤ {lit(b,ty)})", "Bool")
        add(ty, "beq", f"({lit(a,ty)} == {lit(b,ty)})", "Bool")

# ---- USize (platform-dependent; Lean's kernel cannot decide most of it) ----
for a, b in itertools.product([0, 1, 7], [0, 1, 7]):
    for op, sym in [("add", "+"), ("sub", "-"), ("mul", "*"), ("div", "/"), ("mod", "%")]:
        add("USize", op, f"{lit(a,'USize')} {sym} {lit(b,'USize')}", "USize")

# ---- BitVec ----
for w in [1, 8, 64]:
    m = 2**w
    bv = sorted({0, 1, min(7, m - 1), m // 2, m - 1})
    ty = f"BitVec {w}"
    def b(v):
        return f"(BitVec.ofNat {w} {v})"
    for op, sym in [("add", "+"), ("sub", "-"), ("mul", "*"), ("udiv", "/"), ("umod", "%"),
                    ("and", "&&&"), ("or", "|||"), ("xor", "^^^")]:
        for x, y in itertools.product(bv, bv):
            add("BitVec", op, f"{b(x)} {sym} {b(y)}", ty)
    for fn in ["BitVec.sdiv", "BitVec.srem", "BitVec.smod"]:
        for x, y in itertools.product(bv, bv):
            add("BitVec", fn.split(".")[1], f"{fn} {b(x)} {b(y)}", ty)
    for x, s in itertools.product(bv, [0, 1, w - 1, w, w + 1]):
        add("BitVec", "shiftLeft", f"{b(x)} <<< ({s} : Nat)", ty)
        add("BitVec", "ushiftRight", f"{b(x)} >>> ({s} : Nat)", ty)
        add("BitVec", "sshiftRight", f"BitVec.sshiftRight {b(x)} {s}", ty)
    for x in bv + [m, m + 3]:
        add("BitVec", "ofNat", f"{b(x)}", ty)
    for x in bv:
        add("BitVec", "neg", f"-{b(x)}", ty)
        add("BitVec", "not", f"~~~{b(x)}", ty)
        add("BitVec", "toNat", f"BitVec.toNat {b(x)}", "Nat")
        add("BitVec", "toInt", f"BitVec.toInt {b(x)}", "Int")
    for i in [0, 1, -1, -(m // 2), m, -m - 1]:
        add("BitVec", "ofInt", f"BitVec.ofInt {w} {lit(i,'Int')}", ty)
    for x, y in itertools.product(bv, bv):
        add("BitVec", "ult", f"BitVec.ult {b(x)} {b(y)}", "Bool")
        add("BitVec", "slt", f"BitVec.slt {b(x)} {b(y)}", "Bool")
        add("BitVec", "ule", f"BitVec.ule {b(x)} {b(y)}", "Bool")
        add("BitVec", "sle", f"BitVec.sle {b(x)} {b(y)}", "Bool")

if FILT:
    cases = [c for c in cases if c[0].startswith(FILT)]
ALTS = {i: list(c[4]) for i, c in enumerate(cases) if c[4]}
cases = [c[:4] for c in cases]


def eval_expr(expr, rtype):
    if rtype in ("Nat", "Int", "Bool"):
        return f"({expr} : {rtype})"
    if rtype.startswith("Fin"):
        return f"(({expr} : {rtype})).val"
    if rtype.startswith("UInt") or rtype == "USize":
        return f"(({expr} : {rtype})).toNat"
    if rtype.startswith("BitVec"):
        return f"(({expr} : {rtype})).toNat"
    raise ValueError(rtype)


# 1. Values from Lean 4.8.0's compiled evaluator, cross-checked by its kernel below.
with open(f"{OUT}/eval.lean", "w") as f:
    for i, (_, _, e, r) in enumerate(cases):
        f.write(f"#eval IO.println s!\"@V{i}@ {{{eval_expr(e, r)}}}\"\n")
res = subprocess.run([LEAN8, f"{OUT}/eval.lean"], capture_output=True, text=True)
valmap = {}
for l in res.stdout.splitlines():
    m = re.match(r"@V(\d+)@ (\S+)$", l.strip())
    if m:
        valmap[int(m.group(1))] = m.group(2)
missing = [i for i in range(len(cases)) if i not in valmap]
if missing:
    print("lean-eval-missing", len(missing), [cases[i][2] for i in missing[:5]])
vals = [valmap.get(i) for i in range(len(cases))]

def vlit(v, rtype):
    if rtype == "Bool":
        return v
    if rtype in ("Nat", "Int"):
        return lit(int(v), rtype)
    if rtype.startswith("BitVec"):
        w = rtype.split()[1]
        return f"(BitVec.ofNat {w} {v})"
    return lit(int(v), rtype)


def wrong(v, rtype):
    if rtype == "Bool":
        return "false" if v == "true" else "true"
    n = int(v)
    if rtype.startswith("Fin"):
        mod = int(rtype.split()[1])
        if mod == 1:
            return None
        return str((n + 1) % mod)
    if rtype.startswith("UInt"):
        mod = 2 ** int(rtype[4:])
        return str((n + 1) % mod)
    if rtype.startswith("BitVec"):
        mod = 2 ** int(rtype.split()[1])
        return str((n + 1) % mod)
    return str(n + 1)


probes = []  # (name, family, op, expr, claim, truth, tactic)
for i, (fam, op, e, r) in enumerate(cases):
    v = vals[i]
    if v is None:
        continue
    for tac in ["decide", "rfl"]:
        probes.append((f"p{i}_{tac}_t", fam, op, e, vlit(v, r), True, tac, r))
        w = wrong(v, r)
        if w is not None:
            probes.append((f"p{i}_{tac}_f", fam, op, e, vlit(w, r), False, tac, r))
        for j, alt in enumerate(a for a in ALTS.get(i, []) if a != v and a != w):
            probes.append((f"p{i}_{tac}_a{j}", fam, op, e, vlit(alt, r), False, tac, r))

with open(f"{OUT}/probes.lean", "w") as f:
    for (n, fam, op, e, claim, truth, tac, r) in probes:
        proof = "by decide" if tac == "decide" else "rfl"
        f.write(f"theorem {n} : ({e} : {r}) = {claim} := {proof}\n")


def lean_fails(lean, path):
    res = subprocess.run([lean, path], capture_output=True, text=True)
    bad = set()
    for line in res.stdout.splitlines():
        m = re.match(r".*?:(\d+):\d+: error", line)
        if m:
            bad.add(int(m.group(1)))
    return bad


import resource
def run_clean(path, timeout):
    import time
    p = subprocess.Popen([CLEAN, "check", "--json", path], stdout=subprocess.PIPE,
                         stderr=subprocess.DEVNULL, text=True)
    t0 = time.time()
    out = []
    import threading
    th = threading.Thread(target=lambda: out.append(p.stdout.read()))
    th.start()
    while p.poll() is None:
        time.sleep(0.3)
        try:
            rss = int(subprocess.run(["ps", "-o", "rss=", "-p", str(p.pid)], capture_output=True,
                                     text=True).stdout.strip() or 0)
        except ValueError:
            rss = 0
        if rss > int(os.environ.get("PROBE_MAX_KB", str(6 * 1024 * 1024))) or time.time() - t0 > timeout:
            p.kill()
            p.wait()
            th.join()
            return "killed:rss" if rss > 0 and time.time() - t0 <= timeout else "killed:time"
    th.join()
    try:
        return json.loads(out[0])
    except Exception:
        return None

groups = {}
for idx, p in enumerate(probes):
    groups.setdefault((p[1], p[2], p[6], p[5]), []).append(idx)
lean_ok_set, clean_ok_set, timeouts = set(), set(), []
clean_err = {}
os.makedirs(f"{OUT}/chunks", exist_ok=True)
for gi, (key, idxs) in enumerate(sorted(groups.items())):
    path = f"{OUT}/chunks/c{gi}.lean"
    with open(path, "w") as f:
        for i in idxs:
            n, fam, op, e, claim, truth, tac, r = probes[i]
            proof = "by decide" if tac == "decide" else "rfl"
            f.write(f"theorem {n} : ({e} : {r}) = {claim} := {proof}\n")
    bad = lean_fails(LEAN8, path)
    for ln, i in enumerate(idxs, start=1):
        if ln not in bad:
            lean_ok_set.add(probes[i][0])
    rep = run_clean(path, int(os.environ.get("PROBE_TIMEOUT", "180")))
    if not isinstance(rep, dict):
        timeouts.append(key)
        print("CLEAN-ABORT", rep, key, "-> one at a time", flush=True)
        for i in idxs:
            n, fam, op, e, claim, truth, tac, r = probes[i]
            proof = "by decide" if tac == "decide" else "rfl"
            p1 = f"{OUT}/chunks/one.lean"
            with open(p1, "w") as f:
                f.write(f"theorem {n} : ({e} : {r}) = {claim} := {proof}\n")
            rep1 = run_clean(p1, int(os.environ.get("PROBE_ONE_TIMEOUT", "15")))
            if not isinstance(rep1, dict):
                clean_err[n] = f"ABORT {rep1}"
                continue
            errs = rep1.get("errors", [])
            if errs:
                clean_err[n] = errs[0].split(":", 1)[-1][:300]
            elif n in {d["name"] for d in rep1["timing"]["per_declaration"]}:
                clean_ok_set.add(n)
        continue
    cbad = set()
    for err in rep.get("errors", []):
        nm = err.split(":", 1)[0].strip()
        cbad.add(nm)
        clean_err[nm] = err.split(":", 1)[1][:300] if ":" in err else err[:300]
    seen = {d["name"] for d in rep["timing"]["per_declaration"]}
    for i in idxs:
        n = probes[i][0]
        if n in seen and n not in cbad:
            clean_ok_set.add(n)
    print("done", key, len(idxs), flush=True)
rep = {}
rows = []
for ln, (n, fam, op, e, claim, truth, tac, r) in enumerate(probes, start=1):
    lean_ok = n in lean_ok_set
    clean_ok = n in clean_ok_set
    rows.append(dict(name=n, family=fam, op=op, expr=e, claim=claim, truth=truth, tactic=tac,
                     lean=lean_ok, clean=clean_ok, clean_err=clean_err.get(n)))
with open(f"{OUT}/rows.json", "w") as f:
    json.dump(dict(timeouts=[list(k) for k in timeouts],
                   rows=rows), f, indent=0)

# Lean must agree with the truth on every row (sanity: the probe is well-formed).
lean_wrong = [r for r in rows if r["lean"] and not r["truth"]]
unsound = [r for r in rows if r["clean"] and not r["lean"]]
incomplete = [r for r in rows if r["lean"] and not r["clean"]]
print(f"probes={len(rows)} lean_accepts_false={len(lean_wrong)} "
      f"clean_unsound={len(unsound)} clean_incomplete={len(incomplete)}")
summ = {}
for r in rows:
    k = (r["family"], r["op"], r["tactic"])
    s = summ.setdefault(k, [0, 0, 0, 0, 0])  # n, agree, unsound, clean-refutes-true, incomplete
    s[0] += 1
    if r["clean"] == r["lean"]:
        s[1] += 1
    elif r["clean"]:
        s[2] += 1
    elif r["truth"] and r["clean_err"] and "proved that the proposition" in r["clean_err"]:
        s[3] += 1
    else:
        s[4] += 1
with open(f"{OUT}/summary.tsv", "w") as f:
    f.write("family\top\ttactic\tprobes\tagree\tclean_accepts_lean_refutes\tclean_decide_refutes_true\tclean_stuck_on_true\n")
    for k in sorted(summ):
        f.write("\t".join(map(str, list(k) + summ[k])) + "\n")
for r in unsound[:60]:
    print("UNSOUND", r["name"], r["expr"], "=", r["claim"])
