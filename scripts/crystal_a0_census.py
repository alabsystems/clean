#!/usr/bin/env python3
"""The A0-eligibility census: every body's distance from A0 6-of-6, at one HEAD.

    scripts/crystal_a0_census.py <dump_O3> <O3.flip.txt> <O0.flip.txt> <out.json> [KEY=VALUE ...]

WHY THIS EXISTS.  A0's six criteria (bridge design 6.0 row A0: lowered,
spliced, zero unsupported, DerivedAgreed, bodyful reachable closure, flip event
observed) were only ever evaluated per hand-picked target.  The one whole-crate
number close to it -- "52 call bodies with a bodyful closure" -- predates every
marker wave, and "how many bodies are A0-complete" had never been computed at
any HEAD.  This script computes it mechanically from one sealed-driver
whole-crate compile: the coverage JSON (criteria 1-4), the emitted trust-ir
text's call graph (criterion 5, the same body-prefix walk
`crystal_frontier_census.py` verifies before using), and the flip log
(criterion 6, plus the A6 event-lineage == coverage-row-lineage check).

WHAT IT DOES NOT MEASURE.  A6's fail-closed perturbation criterion is
per-body-class (switch-map reaches switch-carrying bodies, mc-plan call-plan
bodies, ...) and is not census-able from one compile; the negative control is
crate-wide, not per-body.  So this census brackets A0 exactly and A6 only in
its digest half.  A row here is *eligibility*, not a chain: links 3-5 (the
Clean-side semantics, the refinement theorem, the kernel check) exist per
chain, not per row.

Provenance KEY=VALUE pairs are recorded verbatim, same contract as
`crystal_frontier_census.py`.

SYMBOLS (M2, 2026-09-27). A `fn` header's name is read by the shared reader
`scripts/crystal_trust_ir_symbols.py`: trust-ir WS4.3 prints a non-bare name
QUOTED (`rustcc fn @"clean_kernel::..."`), the reader decodes it, refuses what
the printer cannot write, and holds the module to one grammar -- so the name the
census compares with a coverage `def_path` is the name, never its spelling.
`--pinned-inputs` prints the first-party modules this script runs besides itself.
"""

import collections
import json
import os
import re
import sys

if os.path.dirname(os.path.abspath(__file__)) not in sys.path:
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# The ONE reader of trust-ir's definition-site symbols (quoted since WS4.3).
import crystal_trust_ir_symbols as tir_symbols  # noqa: E402

# Read by check_gate_registry.py (PINNED_INPUTS_MARKER): `--pinned-inputs` prints the
# first-party modules this script executes besides itself (derived from its imports).
ANSWERS_PINNED_INPUTS = True
CALL = re.compile(r"call @func\.(\d+)")
# The edge set is UNDER-approximated by CALL alone, and the census is the walk's
# only witness (workflow wf_1c3df27b, 2026-08-27). Two more edge forms exist:
#   * `fndef<func.N>` -- a function VALUE. If it can be reached it can be called,
#     so it is an edge for a closure that claims to bound reachable callees.
#     Measured: 8 sites in the recorded dump, all in reduce_float_* entries whose
#     bodyful already reads False via an ordinary edge -- so widening reproduces
#     today's totals EXACTLY (189 six-of-six / 339 one-short); a moved total
#     would mean the hole was already load-bearing.
#   * `call_indirect` -- NO static target. A body containing one has a closure
#     that is not statically known, so bodyful is False, FAIL-CLOSED (0 in the
#     recorded dump; the arm exists so the first one cannot pass silently).
FNDEF = re.compile(r"fndef<func\.(\d+)>")
INDIRECT = re.compile(r"\bcall_indirect\b")
ASSIGN = re.compile(r"^\s+%\d+ = ([a-z_]+)")
BARE = re.compile(r"^\s+([a-z_]+)")
BLOCK = re.compile(r"^bb\d+")
DID = re.compile(r"did=DefId\(0:(\d+) ~")
LINEAGE = re.compile(r"lineage=(sha256:[0-9a-f]+)")

CRITERIA = (
    "lowered",
    "spliced",
    "zero_unsupported",
    "derived_agreed",
    "bodyful_reachable_closure",
    "flip_event_O3",
)


def parse_ir(path):
    funcs, cur = [], None
    syms = tir_symbols.ModuleSymbols(tir_symbols.RUSTCC_PREFIX)
    for ln_no, ln in enumerate(open(path, encoding="utf-8", errors="replace"), 1):
        s = ln.rstrip("\n")
        try:
            fh = syms.fn_header(s, f"line {ln_no}")
        except tir_symbols.SymbolRefusal as exc:
            raise SystemExit(f"trust-ir text {path} line {ln_no}: {exc}")
        if fh is not None:
            cur = {"name": fh[0], "n": 0, "callees": set()}
            funcs.append(cur)
            continue
        if cur is None:
            continue
        if s.startswith("}"):
            cur = None
            continue
        body = s.strip()
        if body and not body.startswith(";") and not BLOCK.match(body):
            if ASSIGN.match(s) or BARE.match(s):
                cur["n"] += 1
        for c in CALL.finditer(s):
            cur["callees"].add(int(c.group(1)))
        for c in FNDEF.finditer(s):
            cur["callees"].add(int(c.group(1)))
        if INDIRECT.search(s):
            cur["indirect"] = True
    return funcs


KNOWN_TEXT_TAG = "!trust_definition::"


def norm_text_name(raw):
    """A text ordinal's name reduced to the form the coverage artifact records.

    Dumps taken with the 2026-09 driver tag a const-init definition as
    `!trust_definition::<path>::{const-init}::<hex>` where the coverage artifact
    records plain `<path>`. The older normalisation stripped only a BARE
    `::{const-init}` at end, so every such dump was refused outright at index
    fact 1 -- measured 2026-09-15 on dump-sidecar-O3: 358 of 3915 names, first
    refusal `coverage func_id 510 is crystal_tag_pin::_, text ordinal is
    !trust_definition::crystal_tag_pin::_::{const-init}::1134321d...`. The
    CONTROL dump taken with the unpatched driver at the same clean rev carries
    the identical prefixes, so this is a producer-naming generation, not
    anything the sidecar introduced.

    Deliberately narrow. Exactly ONE tag is stripped, and the hash is only
    removed as part of the `{const|static}-init` form. An unknown `!tag::` is
    left in place so it still fails the comparison rather than being normalised
    into agreement -- the whole value of this check is that it refuses.
    """
    if not raw.startswith(KNOWN_TEXT_TAG):
        # Untagged name: the historical normalisation, unchanged. A bare
        # `::{const-init}` suffix is still stripped; nothing else is touched.
        return re.sub(r"::\{(?:const|static)-init\}$", "", raw)
    raw = raw[len(KNOWN_TEXT_TAG):]
    # Tagged names carry a 32-hex definition hash, either after a
    # `{const|static}-init` marker or directly on the path. Both are stripped
    # HERE ONLY -- i.e. only for a name that carried the recognised tag, and
    # only for exactly 32 hex characters. An untagged name ending in hex, or a
    # tagged one whose hash is a different width, still reaches the comparison.
    raw = re.sub(r"::\{(?:const|static)-init\}(?:::[0-9a-f]{32})?$", "", raw)
    return re.sub(r"::[0-9a-f]{32}$", "", raw)


def verify_prefix(funcs, cov):
    """The same two index facts crystal_frontier_census.py fails closed on."""
    n = sum(1 for f in funcs if f["n"] > 0)
    for i, f in enumerate(funcs):
        if (f["n"] > 0) != (i < n):
            raise SystemExit(f"index fact 1 violated at entry {i} ({f['name']})")
    if n != cov["totals"]["spliced"]:
        raise SystemExit(
            f"index fact 1 violated: {n} text bodies vs {cov['totals']['spliced']} spliced"
        )
    for b in cov["bodies"]:
        fid = b["func_id"]
        if fid is None:
            continue
        if not isinstance(fid, int) or isinstance(fid, bool) or fid < 0:
            # audit r5: a NEGATIVE func_id sailed through both `fid < n` and
            # `fid >= n` via Python negative indexing and scored a declaration
            # bodyful downstream. Audit r6: non-integer shapes (1.0, "1",
            # True) crashed with a raw TypeError instead of refusing -- both
            # are one refusal now, and the selftest asserts THIS message so a
            # deleted guard cannot hide behind a sibling refusal.
            raise SystemExit(f"index fact 1 violated: invalid func_id {fid!r} "
                             f"(negative or non-integer)")
        name = norm_text_name(funcs[fid]["name"]) if fid < n else ""
        if fid >= n or name != b["def_path"]:
            raise SystemExit(
                f"index fact 1 violated: coverage func_id {fid} is {b['def_path']}, "
                f"text ordinal is {funcs[fid]['name'] if fid < len(funcs) else '<oor>'}"
            )
    ids = [c for f in funcs for c in f["callees"]]
    if ids and max(ids) >= len(funcs):
        raise SystemExit(f"index fact 2 violated: callee id {max(ids)} out of range")
    bad = [c for c in ids if not isinstance(c, int) or isinstance(c, bool) or c < 0]
    if bad:
        raise SystemExit(f"index fact 2 violated: invalid callee id {bad[0]!r} "
                         f"(negative or non-integer)")
    if not any(c < n for c in ids):
        raise SystemExit("index fact 2 violated: no call resolves inside the body prefix")
    return n


def parse_flips(path):
    cod, ctfe = {}, {}
    for ln in open(path, encoding="utf-8", errors="replace"):
        if "trust-ir-flip:" not in ln:
            continue
        m = DID.search(ln)
        if not m:
            continue
        di = int(m.group(1))
        lm = LINEAGE.search(ln)
        lin = lm.group(1) if lm else None
        if "CTFE compiled from trust" in ln:
            ctfe[di] = lin
        elif "compiled from trust" in ln:
            cod[di] = lin
    return cod, ctfe


# Rust COMMENT spans only. Deliberately narrower than the full non-code
# blanking in scripts/check_add_decl_ratchet.py: the clause-(b) registration
# convention CARRIES the spec source inside string literals
# (`const SRC_..: &str = "def <name> ..."`), so blanking strings would erase
# the genuine form along with the fakes. Comments are the prose channel the
# audit-r2 exploit came through (`// Author:` minted a phantom theorem);
# strings are a deliberate act of the file's author.
def _blank_comments(src):
    """Blank Rust comments to spaces, preserving newlines (line numbers
    survive); string literals are KEPT and SHIELD their contents.

    Audit r3 M3 (workflow wf_e15af3e7): the regex this replaces
    (`/\\*.*?\\*/|//[^\\n]*`) had two lexing defects, both demonstrated:
    Rust block comments NEST, and the non-greedy match stopped at the FIRST
    `*/`, so the tail of a nested comment survived blanking as "code" -- a
    def-form inside a rustc-confirmed pure comment registered a phantom
    theorem (the exact channel the r2 M-1 repair claimed closed); and a
    comment OPENER inside a string literal started a bogus comment that
    erased genuine registrations downstream (fail-closed, but still wrong).
    A regex cannot count nesting; this is the small honest scanner instead:
    normal / line-comment / block-comment(depth) / string (with escapes) /
    raw string (with #-fences) / char, comments blanked, everything else
    byte-preserved.
    """
    out = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        two = src[i:i + 2]
        if two == "//":
            j = i
            while j < n and src[j] != "\n":
                j += 1
            out.append(" " * (j - i))
            i = j
        elif two == "/*":
            depth = 1
            j = i + 2
            while j < n and depth:
                t = src[j:j + 2]
                if t == "/*":
                    depth += 1
                    j += 2
                elif t == "*/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            out.append("".join("\n" if ch == "\n" else " " for ch in src[i:j]))
            i = j
        elif c == '"' or (c == "r" and src[i + 1:i + 2] in ('"', "#")) or (
            src[i:i + 2] in ('b"', "br")
        ):
            # string / raw string / byte variants: find the raw fence if any
            j = i
            if src[j] == "b":
                j += 1
            raw = src[j:j + 1] == "r"
            if raw:
                j += 1
                fence = 0
                while src[j:j + 1] == "#":
                    fence += 1
                    j += 1
                if src[j:j + 1] != '"':
                    # not actually a raw string (e.g. the identifier `r`):
                    # emit one byte and continue scanning normally
                    out.append(c)
                    i += 1
                    continue
                j += 1
                end = '"' + "#" * fence
                k = src.find(end, j)
                j = (k + len(end)) if k != -1 else n
            else:
                if src[j:j + 1] != '"':
                    out.append(c)
                    i += 1
                    continue
                j += 1
                while j < n:
                    if src[j] == "\\":
                        j += 2
                    elif src[j] == '"':
                        j += 1
                        break
                    else:
                        j += 1
            out.append(src[i:j])
            i = j
        elif c == "'":
            # char literal (or lifetime): consume conservatively -- a lifetime
            # like 'a has no closing quote within 3 bytes and is emitted as-is
            if src[i + 1:i + 2] == "\\" and src[i + 3:i + 4] == "'":
                out.append(src[i:i + 4])
                i += 4
            elif src[i + 2:i + 3] == "'":
                out.append(src[i:i + 3])
                i += 3
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def clause_b_theorem_registered(theorem, where, repo_root="."):
    """Is `theorem` actually registered as a spec declaration at `where`?

    Audit r1 M1 (workflow wf_4d1a618b): the validator accepted a bare
    `{"clause": "b"}` with no theorem at all -- fail-OPEN on exactly the clause
    that claims a kernel-checked proof. A clause-(b) claim must be checkable
    against the SOURCE: the named file must exist and register the named
    theorem. This is a registration-existence check, not a proof check -- the
    proof is the kernel's job; this only refuses a theorem NAME that nothing
    registers.

    Audit r2 M-1 (workflow wf_0a50b8bb): the first cut matched RAW text and
    its third disjunct was a bare `{theorem}:` substring, so any prose token
    followed by a colon registered a phantom (demonstrated: the SPDX
    `// Author:` line). Comments are BLANKED before matching, and only the
    `def <name>` registration form counts -- which the genuine convention
    carries in the spec-source string literal (`SRC_* = "def <name> ..."`).
    Honest width (audit r5): strings are kept, so ANY string literal in ANY
    .rs file under crates/ registers -- including test-fixture Lean snippets
    -- not only the SRC_* convention. This check is registration-existence,
    never proof; the kernel checks the proof, and the committed-table arm
    pins the real entries against real spec files. The rationale-string `<name>:` disjunct
    is dropped: it was satisfiable by prose, which is the hole, not a
    convention worth keeping.
    """
    import os
    # Audit r4 M1 (workflow wf_4769693f): `where` was unconstrained beyond
    # existence, and comment-blanking is Rust-syntax-only -- so a NON-Rust
    # file whose PROSE quotes `def <name>` registered a phantom (demonstrated
    # live against two archived .md docs). A registration is a claim about
    # Rust spec SOURCE: anything that is not a `.rs` file under `crates/` is
    # refused before it is read (normpath first, so `crates/../docs/x.rs`
    # cannot smuggle past the prefix).
    norm = os.path.normpath(where).replace(os.sep, "/")
    if not (norm.startswith("crates/") and norm.endswith(".rs")):
        return False
    path = os.path.join(repo_root, norm)
    if not os.path.isfile(path):
        return False
    # audit r5: the prefix check above is string-only and open() follows
    # symlinks, so crates/spec/link.rs -> ../../outside.md read the outside
    # file. The RESOLVED path must still be a .rs under the repo's crates/.
    real = os.path.realpath(path)
    crates_root = os.path.realpath(os.path.join(repo_root, "crates"))
    if not (real.startswith(crates_root + os.sep) and real.endswith(".rs")):
        return False
    src = open(path, encoding="utf-8", errors="replace").read()
    code = _blank_comments(src)
    # Word boundary on the LEFT of `def` and on the theorem name (audit r3
    # minor: without it, `redef phantom(` and a name that PREFIXES a real
    # theorem both matched). `re.escape` because theorem names carry `::`.
    import re as _re
    return bool(_re.search(
        r"(?<![A-Za-z0-9_])def " + _re.escape(theorem) + r"[ (]", code))


# The callee-sidecar manifest schemas `sidecar_derived_ids` reads, keyed on the manifest's
# own `schema` field. v3 (trust callee_sidecar.rs, 2026-09-24) adds a `bb` on every call
# row, a `mir_digest` on every member and the top-level `fuel` / `fuel_exhausted`; this
# census reads none of them, but a manifest that CLAIMS v3 without them well formed does not
# vouch for itself and derives nothing -- as does a schema this file does not know.
SIDECAR_MANIFEST_SCHEMAS = (
    "trust-ir-callee-sidecar-v1",
    "trust-ir-callee-sidecar-v2",
    "trust-ir-callee-sidecar-v3",
)
_SIDECAR_MIR_DIGEST = re.compile(r"^sha256:[0-9a-f]{64}$")


def sidecar_v3_defect(man):
    """Why a manifest that claims v3 does NOT carry its v3 fields well formed, or None when
    it does: an int `fuel` >= 1, a bool `fuel_exhausted` (never true beside `closed: true`),
    a non-zero `sha256:<64 hex>` `mir_digest` per member, and per call row an int `bb`
    strictly increasing and below the member's `mir_blocks` (one call per MIR block, rows in
    block order). `type(x) is int` and not isinstance, because a JSON `true` is a Python
    bool, which IS an int. Every reason is driven by its own selftest arm (`v3-*`), the
    same arming the other `sidecar_derived_ids` refusals have."""
    if type(man.get("fuel")) is not int or man["fuel"] < 1:
        return "fuel"
    if type(man.get("fuel_exhausted")) is not bool:
        return "fuel_exhausted"
    if man["fuel_exhausted"] and man.get("closed") is True:
        return "closed with fuel exhausted"
    members = man.get("members")
    if not isinstance(members, list):
        return "members"
    for k, mem in enumerate(members):
        if not isinstance(mem, dict) or not isinstance(mem.get("calls"), list):
            return f"member {k} shape"
        digest = mem.get("mir_digest")
        if not (isinstance(digest, str) and _SIDECAR_MIR_DIGEST.match(digest)
                and digest != "sha256:" + "0" * 64):
            return f"member {k} mir_digest"
        n_blocks = mem.get("mir_blocks")
        if type(n_blocks) is not int:
            return f"member {k} mir_blocks"
        prev = -1
        for j, call in enumerate(mem["calls"]):
            bb = call.get("bb") if isinstance(call, dict) else None
            if not (type(bb) is int and prev < bb < n_blocks):
                return f"member {k} call {j} bb"
            prev = bb
    return None


def sidecar_derived_ids(dump_dir, crate_name):
    """Crate-module func_ids whose body the CALLEE SIDECAR derives, or None.

    The crate module carries a foreign callee as a bodyless DECLARATION, so a
    body past the instruction-bearing prefix scores the closure cell FALSE.
    That is correct about the MODULE and, since 2026-09-09, no longer the whole
    artifact: the producer's callee sidecar resolves such a callee to a
    monomorphized instance, takes `tcx.instance_mir`, and publishes a real
    instruction-bearing body beside the module, with a manifest joining each
    crate DECLARATION id to the member that carries it.

    Returns None when there is no manifest, or when the bundle does not vouch
    for itself -- `closed` must be true and `lowering` must be "ok", and only a
    root whose `outcome` is "resolved" contributes. A bundle that escapes, or
    that reports any other lowering state, derives nothing here. Nor does a
    manifest whose `schema` is not in SIDECAR_MANIFEST_SCHEMAS, or that claims
    v3 without its v3 fields well formed (`sidecar_v3_defect`).
    """
    mpath = os.path.join(dump_dir, "callees", f"{crate_name}.callees.manifest.json")
    if not os.path.isfile(mpath):
        return None
    try:
        man = json.load(open(mpath, encoding="utf-8"))
    except (OSError, ValueError):
        return None
    if not isinstance(man, dict) or man.get("schema") not in SIDECAR_MANIFEST_SCHEMAS:
        return None
    if man["schema"] == "trust-ir-callee-sidecar-v3" and sidecar_v3_defect(man) is not None:
        return None
    if man.get("closed") is not True or man.get("lowering") != "ok":
        return None
    out = set()
    for r in man.get("roots", []):
        if r.get("outcome") != "resolved":
            continue
        for i in r.get("crate_decl_func_ids", []) or []:
            if isinstance(i, int) and not isinstance(i, bool) and i >= 0:
                out.add(i)
    return out or None


def closure_walk(funcs, nb, fid, derived=None):
    """Transitive-closure walk for one body: (ok, closure_size, escapes, indirect).

    Module-level so the selftest can reach it (audit r4 M2, workflow
    wf_4769693f): the previous walk was nested inside main, arm 6 tested its
    own fixture's flag and never called this code, and a mutant with BOTH
    indirect refusals deleted stayed selftest-green. The refusals live here
    now and the selftest drives them in both polarities.
    """
    seen, stack, ok = set(), list(funcs[fid]["callees"]), True
    escapes, indirect = set(), bool(funcs[fid].get("indirect"))
    if indirect:
        ok = False  # an indirect call's target is statically unknown: fail closed
    while stack:
        c = stack.pop()
        if c in seen:
            continue
        seen.add(c)
        if c >= nb:
            # Past the module's instruction-bearing prefix. Bodyless THERE --
            # but the sidecar may carry the body, and `derived` is the manifest
            # join. It is passed only by the SECOND cell; the strict cell calls
            # this with derived=None and is unchanged.
            if derived is not None and c in derived:
                continue
            ok = False
            escapes.add(c)
            continue
        if funcs[c].get("indirect"):
            ok = False
            indirect = True
        stack.extend(funcs[c]["callees"])
    return ok, len(seen), frozenset(escapes), indirect


def target_for(discharge_table, def_path):
    """The discharge-table entry for a body, or None.

    AUDIT r10 M10-2 (sibling): `discharged()` carried its own
    `if discharge_table is None: return False` inside main, where no arm could
    reach it -- the same unreachable-guard shape audit r4 found in the closure
    walk. A None table now yields a None TARGET, which `check_discharge`
    already refuses through a guard that IS armed and IS a mutation row, so
    there is one fewer unarmed refusal rather than one more.
    """
    if discharge_table is None:
        return None
    return discharge_table.get("targets", {}).get(def_path)


def check_discharge(def_path, escapes, indirect, tgt, repo_root="."):
    """Core of the A0-SEMANTIC cell -- module-level so the selftest can reach it.

    escapes: the walk's escaping callee ids for this body. indirect: any
    indirect call in the closure. tgt: this def_path's discharge-table entry or
    None. True/False is the verdict; SystemExit is a REFUSAL (malformed or
    wider-than-reality table).

    FAIL-CLOSED ON BOTH CLAUSES (audit r1 M1 repair): clause (a) must name
    model+residual; clause (b) must name a `theorem` that is listed in the
    target's `clause_b_theorems` AND whose named source file registers it.
    Before this repair a bare `{"clause": "b"}` passed -- the one shape that
    claims a proof was the one shape nothing checked.
    """
    if indirect:
        return False
    if tgt is None:
        return False
    # v2 (audit r2 pre-emption): escapes are NAMES. Numeric func_ids renumber
    # with every module change -- the v1 id-keyed table was correctly refused
    # by this very gate on the first fresh dump (expect: 6516 -> 6547). The
    # caller maps its escaping ids to trust-ir names before calling.
    entries = set(tgt.get("escaping_callees", {}))
    extra = entries - set(escapes)
    if extra:
        raise SystemExit(
            f"discharge table for {def_path} names callee(s) {sorted(extra)} that the "
            f"walk does not find (walk escapes: {sorted(escapes)}) -- a table wider than "
            f"reality is refused, not ignored")
    listed = {t.get("theorem"): t for t in tgt.get("clause_b_theorems", [])}
    for e in sorted(escapes):
        ent = tgt.get("escaping_callees", {}).get(e)
        if ent is None:
            return False
        if ent.get("clause") not in ("a", "b"):
            raise SystemExit(f"discharge entry {def_path}/{e} has no valid clause")
        if ent["clause"] == "a" and not (
            str(ent.get("model") or "").strip() and str(ent.get("residual") or "").strip()
        ):
            raise SystemExit(
                f"discharge entry {def_path}/{e} is clause (a) but names no model+residual "
                f"-- an unnamed residual is a silence, which clause (a) exists to forbid")
        if ent["clause"] == "b":
            th = ent.get("theorem")
            if not th:
                raise SystemExit(
                    f"discharge entry {def_path}/{e} is clause (b) but names NO theorem -- "
                    f"an unreachability claim with no proof named is the fail-open hole "
                    f"audit r1 M1 closed; refused")
            row = listed.get(th)
            if row is None:
                raise SystemExit(
                    f"discharge entry {def_path}/{e} names theorem {th!r} that the target's "
                    f"clause_b_theorems does not list -- refused")
            _wparts = (row.get("where") or "").split()
            where = _wparts[0] if _wparts else ""
            if not where or not clause_b_theorem_registered(th, where, repo_root):
                raise SystemExit(
                    f"clause_b theorem {th!r} is not registered at {where!r} -- a theorem "
                    f"name nothing registers proves nothing; refused")
    return True


def selftest():
    """Every refusal must be reachable, demonstrated on EVERY invocation.

    Trust (2026-08-27, workflow wf_1c3df27b): the gate-registry row for this
    file claimed it "asserts no invariant and refuses nothing" while
    `verify_prefix` carries seven `SystemExit`s -- including the partition
    assertion the whole bodyful criterion rests on. A criterion this file
    computes must not be movable through a row nobody has seen refuse, so the
    refusals run as arms here, at the top of main, every time -- the
    `selftest-inline` convention (`scripts/check_lowering_adequacy.py`).
    """
    def fn(name, n, callees=(), indirect=False):
        f = {"name": name, "n": n, "callees": set(callees)}
        if indirect:
            f["indirect"] = True
        return f

    def refuses(tag, funcs, cov, needle=None):
        # needle: the refusal MESSAGE this arm pins. Without it an arm is
        # satisfied by ANY SystemExit, so deleting the pinned guard can be
        # masked by a sibling refusal -- audit r6 M1 found one such arm and
        # the arm-mutation gate's dry run found three more (partition,
        # callee-oor via vacuous-edges, clause-b-bare via unlisted).
        try:
            verify_prefix(funcs, cov)
        except SystemExit as e:
            if needle is None or needle in str(e):
                return True
            print(f"  [RED] selftest arm {tag}: refused by the WRONG guard: {e}")
            return False
        except Exception as e:  # audit r7: a crash is not a refusal
            print(f"  [RED] selftest arm {tag}: CRASHED instead of refusing: {e!r}")
            return False
        print(f"  [RED] selftest arm {tag}: refusal did NOT fire")
        return False

    good = [fn("a", 2, [1]), fn("b", 1), fn("c", 0)]
    cov = {"totals": {"spliced": 2},
           "bodies": [{"func_id": 0, "def_path": "a"}, {"func_id": 1, "def_path": "b"}]}
    ok = True
    # arm 1: a body AFTER a declaration breaks the partition
    ok &= refuses("partition", [fn("a", 2, [1]), fn("c", 0), fn("b", 1)], cov,
                  needle="violated at entry")
    # arm 2: text-body count != coverage spliced total
    ok &= refuses("spliced-total", good, {"totals": {"spliced": 3}, "bodies": []},
                  needle="text bodies vs")
    # arm 3: coverage func_id names a different function than the text ordinal
    ok &= refuses("name-mismatch", good,
                  {"totals": {"spliced": 2},
                   "bodies": [{"func_id": 0, "def_path": "WRONG"}]},
                  needle="text ordinal is")
    # arm 4: a callee id out of range
    ok &= refuses("callee-oor", [fn("a", 2, [9]), fn("b", 1), fn("c", 0)], cov,
                  needle="out of range")
    # arm 4b (audit r5; REWRITTEN audit r6 M1): a NEGATIVE coverage func_id
    # refuses BY ITS OWN GUARD. The r5 fixture used def_path "a", which
    # funcs[-1] wraps to "c" -- so with the guard DELETED the name-mismatch
    # refusal fired instead and refuses() accepted any SystemExit: the arm
    # was vacuous against deletion of the guard it existed to pin. def_path
    # "c" makes the wrapped lookup MATCH, and the message is asserted, so
    # only the negative-fid refusal can pass this arm.
    def refuses_saying(tag, needle, funcs_, cov_):
        try:
            verify_prefix(funcs_, cov_)
        except SystemExit as e:
            if needle in str(e):
                return True
            print(f"  [RED] selftest arm {tag}: refused, but by the WRONG guard: {e}")
            return False
        except Exception as e:  # audit r7: a crash is not a refusal
            print(f"  [RED] selftest arm {tag}: CRASHED instead of refusing: {e!r}")
            return False
        print(f"  [RED] selftest arm {tag}: refusal did NOT fire")
        return False
    ok &= refuses_saying("negative-fid", "invalid func_id", good,
                         {"totals": {"spliced": 2},
                          "bodies": [{"func_id": -1, "def_path": "c"}]})
    # arm 4c (audit r6): a NEGATIVE callee id refuses by its own guard --
    # this refusal previously had no arm at all (deletion stayed green)
    ok &= refuses_saying("negative-callee", "invalid callee id",
                         [fn("a", 2, [-1]), fn("b", 1), fn("c", 0)], cov)
    # arm 5: NO call resolves inside the prefix (vacuous edge set)
    ok &= refuses("vacuous-edges", [fn("a", 2, [2]), fn("b", 1), fn("c", 0)], cov,
                  needle="no call resolves")
    # the happy path must still pass
    try:
        if verify_prefix(good, cov) != 2:
            print("  [RED] selftest: happy path returned wrong prefix")
            ok = False
    except SystemExit:
        print("  [RED] selftest: happy path REFUSED")
        ok = False
    # arm 6 (2026-08-27 widening; REWRITTEN audit r4 M2): an indirect call
    # fails the closure CLOSED -- driven through the REAL walk (closure_walk),
    # which the old arm never called: it tested its own fixture's flag, so a
    # mutant with both indirect refusals deleted stayed green. Both
    # polarities, plus a clean control.
    _okc, _, _, _ind = closure_walk(
        [fn("a", 2, [1], indirect=True), fn("b", 1), fn("c", 0)], 2, 0)
    if _okc or not _ind:
        print("  [RED] selftest arm indirect-entry: walk passed an indirect body")
        ok = False
    # arm 6b: a CALLEE's indirect flag deep in the closure must propagate
    _okc, _, _, _ind = closure_walk(
        [fn("a", 2, [1]), fn("b", 1, indirect=True), fn("c", 0)], 2, 0)
    if _okc or not _ind:
        print("  [RED] selftest arm indirect-callee: walk passed / did not propagate")
        ok = False
    # arms parse-ir-* (audit r8 M4): parse_ir is the SOLE producer of the
    # `indirect` flag and of the fndef call edges the refusals above consume,
    # and every other arm hand-builds `funcs` -- so deleting either producer
    # line left both gates green while the real census scored an
    # indirect-calling body 6-of-6 instead of 5-of-6 (demonstrated). Drive the
    # producer itself over a two-function inline dump.
    import os as _pos, tempfile as _ptf
    with _ptf.TemporaryDirectory() as _pd:
        _dump = _pos.path.join(_pd, "m.trust-ir.txt")
        with open(_dump, "w", encoding="utf-8") as _f:
            _f.write("rustcc fn @a(functy.0) {\n"
                     "  %0 = call @func.1()\n"
                     "  %1 = fndef<func.2>\n"
                     "  %2 = call_indirect %1\n"
                     "}\n"
                     "rustcc fn @b(functy.1) {\n"
                     "  %0 = const 1\n"
                     "}\n")
        _pf = parse_ir(_dump)
        if len(_pf) != 2 or _pf[0]["name"] != "a":
            print(f"  [RED] selftest arm parse-ir-shape: parsed {len(_pf)} functions")
            ok = False
        elif not _pf[0].get("indirect"):
            print("  [RED] selftest arm parse-ir-indirect: a call_indirect line "
                  "did NOT set the indirect flag -- the walk's fail-closed "
                  "refusal has no input")
            ok = False
        elif 2 not in _pf[0]["callees"]:
            print("  [RED] selftest arm parse-ir-fndef: an fndef<func.N> line "
                  "did NOT add callee N -- escaping-callee edges go missing")
            ok = False
        elif 1 not in _pf[0]["callees"]:
            print("  [RED] selftest arm parse-ir-call: a call @func.N line did "
                  "NOT add callee N")
            ok = False
        elif _pf[1].get("indirect"):
            print("  [RED] selftest arm parse-ir-control: a body with no "
                  "call_indirect was flagged indirect")
            ok = False
        # arms parse-ir-quoted / -mixed / -escape (M2, 2026-09-27): trust-ir
        # WS4.3 prints a non-bare name QUOTED. The same module so printed must
        # parse to the same DECODED names (the `fn @(.*)` regex this replaced
        # kept the quotes, so every name missed its coverage `def_path`), and
        # what the printer cannot write is a refusal, not a parse.
        _legacy = ("rustcc fn @k::a<'_>(functy.0) {\n  %0 = call @func.1()\n}\n"
                   "rustcc fn @<k::S as k::T>::b(functy.1) {\n  %0 = const 1\n}\n")
        _quoted = tir_symbols.respell_ws43(_legacy)
        _qd = _pos.path.join(_pd, "q.trust-ir.txt")
        with open(_qd, "w", encoding="utf-8") as _f:
            _f.write(_quoted)
        _ld = _pos.path.join(_pd, "l.trust-ir.txt")
        with open(_ld, "w", encoding="utf-8") as _f:
            _f.write(_legacy)
        _qn = [f["name"] for f in parse_ir(_qd)]
        if '@"k::a<\'_>"' not in _quoted or _qn != [f["name"] for f in parse_ir(_ld)] \
                or _qn != ["k::a<'_>", "<k::S as k::T>::b"]:
            print(f"  [RED] selftest arm parse-ir-quoted: a WS4.3 quoted module "
                  f"parsed to {_qn}, not its decoded names")
            ok = False
        for _tag, _text, _needle in (
                ("parse-ir-mixed", _quoted.replace('@"<k::S as k::T>::b"', "@<k::S as k::T>::b"),
                 "mixes a QUOTED"),
                ("parse-ir-escape", _quoted.replace('"k::a<\'_>"', '"k::a\\q"'),
                 "is not one the trust-ir printer emits")):
            with open(_qd, "w", encoding="utf-8") as _f:
                _f.write(_text)
            try:
                parse_ir(_qd)
            except SystemExit as _e:
                if _needle not in str(_e):
                    print(f"  [RED] selftest arm {_tag}: refused by the WRONG guard: {_e}")
                    ok = False
            except Exception as _e:  # noqa: BLE001 -- a crash is not a refusal
                print(f"  [RED] selftest arm {_tag}: CRASHED instead of refusing: {_e!r}")
                ok = False
            else:
                print(f"  [RED] selftest arm {_tag}: refusal did NOT fire")
                ok = False
    # arm 6c (control): a clean closure passes, no indirect, and an escaping
    # callee is REPORTED (the escape set feeds check_discharge)
    _okc, _, _esc, _ind = closure_walk(good, 2, 0)
    if not _okc or _ind or _esc:
        print("  [RED] selftest arm indirect-control: clean closure misjudged")
        ok = False
    _okc, _, _esc, _ind = closure_walk([fn("a", 2, [2]), fn("b", 1), fn("c", 0)], 2, 0)
    if _okc or _ind or _esc != frozenset({2}):
        print("  [RED] selftest arm escape-report: escaping callee not reported")
        ok = False
    # arms 7-11 (2026-08-27 R2 adoption): the discharge core, fail-closed both ways
    ENT = {"clause": "a", "model": "m", "residual": "r"}
    def refuses_d(tag, *a, needle=None):
        # needle: same sibling-masking defense as refuses() -- audit r6
        try:
            check_discharge(*a)
        except SystemExit as e:
            if needle is None or needle in str(e):
                return True
            print(f"  [RED] selftest arm {tag}: refused by the WRONG guard: {e}")
            return False
        except Exception as e:  # audit r7: a crash is not a refusal
            print(f"  [RED] selftest arm {tag}: CRASHED instead of refusing: {e!r}")
            return False
        print(f"  [RED] selftest arm {tag}: refusal did NOT fire")
        return False
    if check_discharge("t", {"callee_x"}, False, {"escaping_callees": {"callee_x": ENT}}) is not True:
        print("  [RED] arm discharge-covered: entry present but verdict False"); ok = False
    if check_discharge("t", {"callee_x"}, False, {"escaping_callees": {}}) is not False:
        print("  [RED] arm discharge-missing: escaping callee with no entry passed"); ok = False
    # arm discharge-no-target (audit r10 M10-2): a body with escaping callees
    # and NO discharge-table entry AT ALL must be False. This guard governs
    # every body in the crate except the single table target, and NOTHING
    # armed it: flipping `if tgt is None: return False` to `return True` left
    # 32/32 arms and CENSUS_ARMS=ok green while the census minted
    # a0_complete_semantic 202 -> 604 and semantic_only_bodies 1 -> 403.
    if check_discharge("t", {"callee_x"}, False, None) is not False:
        print("  [RED] arm discharge-no-target: a body with escaping callees and "
              "no discharge entry scored semantic-complete"); ok = False
    # arm discharge-no-table (audit r10): the census run WITHOUT a discharge
    # table must score an escaping body False, not True -- otherwise omitting
    # the `discharge=` argument silently emits a semantic total computed
    # against no table at all.
    if target_for(None, "t") is not None or target_for({}, "t") is not None:
        print("  [RED] arm discharge-no-table: an absent/empty discharge table "
              "produced a target"); ok = False
    if check_discharge("t", {"callee_x"}, False, target_for(None, "t")) is not False:
        print("  [RED] arm discharge-no-table: an escaping body passed with no "
              "discharge table at all"); ok = False
    if check_discharge("t", {"callee_x"}, True, {"escaping_callees": {"callee_x": ENT}}) is not False:
        print("  [RED] arm discharge-indirect: indirect call passed the semantic cell"); ok = False
    # arm invalid-clause (audit r7 M3): a clause outside {a, b} must refuse
    # BY ITS OWN GUARD -- this refusal was in neither the arm set nor the
    # mutation table, and deleting it let clause "z" fall through BOTH
    # branches and return True: a verdict-flipping mint
    ok &= refuses_d("invalid-clause", "t", {"callee_x"}, False,
                    {"escaping_callees": {"callee_x": {"clause": "z"}}},
                    needle="has no valid clause")
    ok &= refuses_d("wider-than-reality", "t", {"callee_x"}, False, {"escaping_callees": {"callee_x": ENT, "callee_phantom": ENT}},
                    needle="walk does not find")
    ok &= refuses_d("clause-a-unnamed-residual", "t", {"callee_x"}, False,
                    {"escaping_callees": {"callee_x": {"clause": "a", "model": "m"}}},
                    needle="unnamed residual is a silence")
    # arms 12-14 (audit r1 M1): clause (b) is fail-closed too
    ok &= refuses_d("clause-b-bare", "t", {"callee_x"}, False,
                    {"escaping_callees": {"callee_x": {"clause": "b"}}},
                    needle="names NO theorem")
    ok &= refuses_d("clause-b-unlisted-theorem", "t", {"callee_x"}, False,
                    {"escaping_callees": {"callee_x": {"clause": "b", "theorem": "phantom_thm"}},
                     "clause_b_theorems": []},
                    needle="does not list")
    ok &= refuses_d("clause-b-unregistered-theorem", "t", {"callee_x"}, False,
                    {"escaping_callees": {"callee_x": {"clause": "b", "theorem": "phantom_thm"}},
                     "clause_b_theorems": [{"theorem": "phantom_thm",
                                            "where": "does/not/exist.rs"}]},
                    needle="proves nothing")
    # arm 15 (audit r2 M-1): a file that merely MENTIONS the theorem -- in a
    # comment, colon-suffixed, even a commented-out def-form -- must NOT count
    # as registration. This arm kills both demonstrated mutants at once: the
    # existence-only mutant (the file exists) and the raw-text mutant (the
    # mention is right there in the bytes).
    import os as _os, tempfile as _tf
    with _tf.TemporaryDirectory() as _d:
        # fixtures live under crates/spec/ because registration now REFUSES
        # any `where` outside crates/ or not ending .rs (audit r4 M1) -- the
        # arms below must exercise the blanking logic, not the path refusal
        _os.makedirs(_os.path.join(_d, "crates", "spec"))
        _mention = _os.path.join(_d, "crates", "spec", "mention_only.rs")
        with open(_mention, "w", encoding="utf-8") as _f:
            _f.write("// phantom_thm: prose mention only\n"
                     "/* def phantom_thm (x : Nat) : X -- commented out */\n"
                     # audit r3 M3: Rust block comments NEST -- the regex this
                     # arm used to pass stopped at the FIRST */ and the tail
                     # of a nested comment counted as code. Both demonstrated
                     # nested shapes are pinned here.
                     "/* outer /* inner */ def phantom_thm (y : Nat) : X */\n"
                     "/* a /* b /* c */ */ def phantom_thm (z : Nat) : X */\n"
                     # audit r3 minor: a name-with-colon or redef prose in a
                     # STRING is not a registration either (word boundary).
                     "const P: &str = \"cannot redef phantom_thm(x)\";\n")
        if clause_b_theorem_registered("phantom_thm", "crates/spec/mention_only.rs", _d):
            print("  [RED] arm clause-b-mention-only: a comment-only mention registered")
            ok = False
        # arm 16 (positive control): the GENUINE convention -- the def-form
        # carried in a spec-source string literal -- must keep registering, so
        # an over-blanking regression cannot silently disable clause (b).
        _real = _os.path.join(_d, "crates", "spec", "real_form.rs")
        with open(_real, "w", encoding="utf-8") as _f:
            # audit r3 minor (string shielding): a comment OPENER inside an
            # EARLIER string must not start a bogus comment that erases the
            # genuine registration after it -- the old regex did exactly that.
            _f.write('const URL: &str = "https://example.com/x";\n'
                     'const SRC: &str = "def real_thm (n : Nat) : X := y";\n')
        if not clause_b_theorem_registered("real_thm", "crates/spec/real_form.rs", _d):
            print("  [RED] arm clause-b-string-form-registers: the genuine "
                  "string-literal def-form was refused")
            ok = False
        # a PREFIX of a registered name is not that name (word boundary right)
        if clause_b_theorem_registered("real_th", "crates/spec/real_form.rs", _d):
            print("  [RED] arm clause-b-prefix-name: a prefix of a registered "
                  "theorem name counted as registered")
            ok = False
        # arm md-prose (audit r4 M1): the SAME def-form bytes that register in
        # a .rs file must NOT register from a non-Rust file -- comment-blanking
        # is Rust-syntax-only, so in prose every byte is "code" and two
        # archived .md docs demonstrably minted phantoms before this refusal.
        _md = _os.path.join(_d, "crates", "spec", "prose.md")
        with open(_md, "w", encoding="utf-8") as _f:
            _f.write("The obligation is discharged by\n"
                     "def md_phantom (x : Nat) : X := y\n")
        if clause_b_theorem_registered("md_phantom", "crates/spec/prose.md", _d):
            print("  [RED] arm clause-b-md-prose: a .md file registered a theorem")
            ok = False
        # arm outside-crates (audit r4 M1): a genuine .rs def-form OUTSIDE
        # crates/ is refused -- spec source lives under crates/, and an
        # unconstrained root was the width of the phantom channel
        _os.makedirs(_os.path.join(_d, "docs"))
        _out = _os.path.join(_d, "docs", "outside.rs")
        with open(_out, "w", encoding="utf-8") as _f:
            _f.write('const SRC: &str = "def outside_thm (n : Nat) : X := y";\n')
        if clause_b_theorem_registered("outside_thm", "docs/outside.rs", _d):
            print("  [RED] arm clause-b-outside-crates: a file outside crates/ "
                  "registered a theorem")
            ok = False
        if clause_b_theorem_registered("outside_thm", "crates/../docs/outside.rs", _d):
            print("  [RED] arm clause-b-normpath-smuggle: crates/../ smuggled past "
                  "the path constraint")
            ok = False
        # arm symlink (audit r5): a symlink under crates/ resolving OUTSIDE
        # crates/ must refuse -- the prefix check is string-only and open()
        # follows links, so this was the residual traversal channel
        _lnk = _os.path.join(_d, "crates", "spec", "link.rs")
        try:
            _os.symlink(_os.path.join(_d, "docs", "outside.rs"), _lnk)
            if clause_b_theorem_registered("outside_thm", "crates/spec/link.rs", _d):
                print("  [RED] arm clause-b-symlink: a symlink out of crates/ registered")
                ok = False
        except OSError:
            pass  # filesystems without symlink support skip this arm's body
    # ...and the REAL committed table's clause-b theorem must verify against source
    # --- the sidecar join: a bundle that does not vouch for itself derives NOTHING.
    # Four arms, because `sidecar_derived_ids` is the only thing standing between
    # a manifest and the artifact-pair closure cell, and the whole value of that
    # cell is that an UNCLOSED or partially-lowered bundle cannot buy a body.
    import json as _sj, os as _so, tempfile as _st
    _base = {
        "schema": "trust-ir-callee-sidecar-v1",
        "closed": True,
        "lowering": "ok",
        "roots": [{"outcome": "resolved", "crate_decl_func_ids": [4938]}],
    }

    def _sidecar_arm(name, mutate, want):
        with _st.TemporaryDirectory() as _d:
            _so.makedirs(_so.path.join(_d, "callees"))
            man = _sj.loads(_sj.dumps(_base))
            mutate(man)
            with open(_so.path.join(_d, "callees", "k.callees.manifest.json"), "w") as fh:
                _sj.dump(man, fh)
            got = sidecar_derived_ids(_d, "k")
        if got != want:
            print(f"  [RED] arm sidecar-{name}: derived {got!r}, expected {want!r}")
        return got == want

    def _v3(m):
        # A well-formed v3 manifest over the same root (trust callee_sidecar.rs, 2026-09-24).
        m.update(schema="trust-ir-callee-sidecar-v3", fuel=64, fuel_exhausted=False,
                 members=[{"sidecar_func_id": 0, "mir_blocks": 3,
                           "mir_digest": "sha256:" + "ab" * 32,
                           "calls": [{"bb": 1, "class": "member"}]}])

    def _v3_then(f):
        return lambda m: (_v3(m), f(m))

    for _n, _mut, _want in (
        ("baseline", lambda m: None, {4938}),
        ("not-closed", lambda m: m.update(closed=False), None),
        ("lowering-not-ok", lambda m: m.update(lowering="partial"), None),
        ("root-unresolved", lambda m: m["roots"][0].update(outcome="declined"), None),
        # Manifest v3: read, and a manifest CLAIMING v3 without its fields derives nothing.
        ("v3", _v3, {4938}),
        ("v3-call-without-bb", _v3_then(lambda m: m["members"][0]["calls"][0].pop("bb")), None),
        ("v3-member-without-mir-digest", _v3_then(lambda m: m["members"][0].pop("mir_digest")), None),
        ("unknown-schema", lambda m: m.update(schema="trust-ir-callee-sidecar-v4"), None),
    ):
        if not _sidecar_arm(_n, _mut, _want):
            ok = False
    # ...each v3 defect is named by ITS OWN reason, so a deleted condition cannot hide
    # behind a sibling that happens to refuse the same mutant (the r6 sibling-masking
    # lesson); the two `sidecar-v3-*` arms above carry the refusal through
    # `sidecar_derived_ids` itself. `_base` is `closed: true`, which the exhausted arm uses.
    for _n, _mut, _want in (
        ("v3-well-formed", lambda m: None, None),
        ("v3-fuel", lambda m: m.pop("fuel"), "fuel"),
        ("v3-fuel-zero", lambda m: m.update(fuel=0), "fuel"),
        ("v3-fuel-exhausted-an-int", lambda m: m.update(fuel_exhausted=1), "fuel_exhausted"),
        ("v3-closed-and-exhausted", lambda m: m.update(fuel_exhausted=True),
         "closed with fuel exhausted"),
        ("v3-members", lambda m: m.update(members={}), "members"),
        ("v3-member-shape", lambda m: m["members"][0].pop("calls"), "member 0 shape"),
        ("v3-mir-digest", lambda m: m["members"][0].pop("mir_digest"), "member 0 mir_digest"),
        ("v3-zero-digest", lambda m: m["members"][0].update(mir_digest="sha256:" + "0" * 64),
         "member 0 mir_digest"),
        ("v3-mir-blocks", lambda m: m["members"][0].pop("mir_blocks"), "member 0 mir_blocks"),
        ("v3-bb-missing", lambda m: m["members"][0]["calls"][0].pop("bb"), "member 0 call 0 bb"),
        ("v3-bb-past-blocks", lambda m: m["members"][0]["calls"][0].update(bb=3),
         "member 0 call 0 bb"),
        ("v3-bb-a-bool", lambda m: m["members"][0]["calls"][0].update(bb=True),
         "member 0 call 0 bb"),
    ):
        _m = _sj.loads(_sj.dumps(_base))
        _v3(_m)
        _mut(_m)
        _got = sidecar_v3_defect(_m)
        if _got != _want:
            print(f"  [RED] arm sidecar-{_n}: defect {_got!r}, expected {_want!r}")
            ok = False
    # ...and a dump with NO manifest derives nothing, which is what keeps every
    # pre-sidecar artifact reading exactly as it did before.
    with _st.TemporaryDirectory() as _d:
        if sidecar_derived_ids(_d, "k") is not None:
            print("  [RED] arm sidecar-no-manifest: a dump without a manifest derived ids")
            ok = False

    import json as _json
    try:
        _t = _json.load(open("data/crystal_a0_discharge.json"))
        for _name, _tg in _t["targets"].items():
            for _row in _tg.get("clause_b_theorems", []):
                _wp = (_row.get("where") or "").split()
                _w = _wp[0] if _wp else ""
                if not clause_b_theorem_registered(_row["theorem"], _w):
                    print(f"  [RED] committed clause_b theorem {_row['theorem']} not "
                          f"registered at {_w}")
                    ok = False
    except FileNotFoundError:
        pass  # bare-clone selftest contexts without the table stay green
    if not ok:
        raise SystemExit("crystal_a0_census selftest: arms misbehave -- refusing to census")


def main(argv):
    # `--selftest` runs the refusal arms alone and exits; without it they STILL
    # run first (selftest-inline convention) -- the flag exists so the
    # demonstration is invocable by name and the registry badge matches the file.
    if len(argv) > 1 and argv[1] == "--pinned-inputs":
        from pathlib import Path  # noqa: PLC0415 -- this flag's only use
        print("\n".join(tir_symbols.first_party_imports(Path(__file__))))
        return
    if len(argv) > 1 and argv[1] == "--selftest":
        selftest()
        print("crystal_a0_census selftest: 59/59 arms behave")
        return
    selftest()
    if len(argv) < 5:
        raise SystemExit(__doc__)
    d3, f3, f0, out = argv[1:5]
    provenance = {}
    for kv in argv[5:]:
        if "=" not in kv:
            raise SystemExit(f"provenance argument {kv!r} is not KEY=VALUE")
        k, v = kv.split("=", 1)
        provenance[k] = v
    discharge_table = None
    if "discharge" in provenance:
        discharge_table = json.load(open(provenance["discharge"], encoding="utf-8"))
    cov = json.load(open(d3 + "/clean_kernel.coverage.json", encoding="utf-8"))
    funcs = parse_ir(d3 + "/clean_kernel.trust-ir.txt")
    # The callee sidecar's manifest, if this dump carries one. None on every
    # dump that does not, which is what keeps the second cell equal to the
    # strict one on older artifacts.
    derived_ids = sidecar_derived_ids(d3, "clean_kernel")
    nb = verify_prefix(funcs, cov)
    cod3, ctfe3 = parse_flips(f3)
    cod0, ctfe0 = parse_flips(f0)

    closures = {}

    closures_sc = {}

    def bodyful(fid):
        # audit r4 M2: the walk itself is module-level (closure_walk) so the
        # selftest exercises the SAME code the census runs, not a copy.
        if fid not in closures:
            closures[fid] = closure_walk(funcs, nb, fid)
        return closures[fid]

    def bodyful_sc(fid):
        """`bodyful`, with the sidecar manifest's derived ids admitted."""
        if fid not in closures_sc:
            closures_sc[fid] = closure_walk(funcs, nb, fid, derived=derived_ids)
        return closures_sc[fid]

    def discharged(fid, def_path):
        """The A0-SEMANTIC cell (owner ruling 2026-08-27, workflow wf_1c3df27b R2).

        True iff the syntactic walk holds OUTRIGHT, or every escaping callee
        carries a clause in data/crystal_a0_discharge.json for this def_path.
        FAIL-CLOSED both directions: an escaping callee with no entry is False,
        and a table entry naming a callee the walk does not find is a REFUSAL
        (a table wider than reality is how residuals hide). An indirect call is
        False regardless -- no table entry can name an unknown target.
        """
        ok, _, escapes, indirect = bodyful(fid)
        if ok:
            return True
        tgt = target_for(discharge_table, def_path)
        escape_names = {funcs[e]["name"] for e in escapes}
        return check_discharge(def_path, escape_names, indirect, tgt, repo_root=".")

    rows = []
    for b in cov["bodies"]:
        dm = b["differentials"].get("derived_mir", {})
        fid = b["func_id"]
        md = dm.get("markers_detail", "")
        crit = {
            "lowered": bool(b.get("lowered")),
            "spliced": bool(b.get("spliced")),
            "zero_unsupported": b.get("unsupported") == [],
            "derived_agreed": dm.get("verdict") == "agreed",
            "bodyful_reachable_closure": (fid is not None and fid < nb and bodyful(fid)[0]),

            "flip_event_O3": b["def_index"] in cod3,
        }
        # The SEMANTIC cell (owner ruling 2026-08-27) is computed and reported
        # BESIDE the six historical criteria, never inside their sum: the
        # historical 6-of-6 total must stay derivable from the same six cells it
        # always was, and the semantic total is its own named number.
        semantic = fid is not None and fid < nb and discharged(fid, b["def_path"])
        # The SAME walk as the strict closure cell, with the callee sidecar's
        # derived bodies admitted. Its own named number, NOT a seventh cell:
        # `score = sum(crit.values())` below is why -- adding it to `crit`
        # inflates the score and silently redefines 6-of-6, which I did and the
        # run caught (44 -> 40 closure-blocked with the strict cell untouched).
        # Same discipline as `bodyful_or_discharged_closure` above it.
        sidecar_closed = fid is not None and fid < nb and bodyful_sc(fid)[0]
        score = sum(crit.values())
        ev_lin = cod3.get(b["def_index"])
        rows.append(
            {
                "def_path": b["def_path"],
                "def_index": b["def_index"],
                "score": score,
                "crit": crit,
                "bodyful_or_discharged_closure": semantic,
                "bodyful_or_sidecar_closure": sidecar_closed,
                "markers_exact": bool(dm.get("markers_exact")),
                "markers_vacuous": md.startswith("0 marker line(s)"),
                "flip_O0": b["def_index"] in cod0,
                "ctfe_O3": b["def_index"] in ctfe3,
                "a6_event_lineage_equal": (ev_lin is not None and ev_lin == b.get("lineage")),
            }
        )

    complete = [r for r in rows if r["score"] == 6]
    one_short = [r for r in rows if r["score"] == 5]
    missing = collections.Counter(
        next(c for c in CRITERIA if not r["crit"][c]) for r in one_short
    )
    dist = collections.Counter(r["score"] for r in rows)

    result = {
        "schema": "clean.crystal.a0_census/1",
        "provenance": provenance,
        "inputs": {"dump_O3": d3, "flip_O3": f3, "flip_O0": f0},
        "criteria": list(CRITERIA),
        "totals": {
            "bodies": cov["totals"]["bodies"],
            "score_distribution": {str(k): v for k, v in sorted(dist.items())},
            "a0_complete_6_of_6": len(complete),
            "a0_complete_with_nonvacuous_markers": sum(
                1 for r in complete if r["markers_exact"] and not r["markers_vacuous"]
            ),
            "ctfe_flip_O3_bodies": sum(1 for r in rows if r["ctfe_O3"]),
            "a0_one_short_5_of_6": len(one_short),
            "one_short_missing_criterion": dict(missing.most_common()),
            "a0_complete_semantic": sum(
                1
                for r in rows
                if r["score"] - r["crit"]["bodyful_reachable_closure"]
                + r["bodyful_or_discharged_closure"]
                == 6
            ),
            # Same shape, over the ARTIFACT-PAIR reading of the closure cell.
            # Built by SUBTRACTING the strict cell and adding the sidecar one,
            # so it can never move the six-cell score it is derived from.
            "a0_complete_with_sidecar": sum(
                1
                for r in rows
                if r["score"] - r["crit"]["bodyful_reachable_closure"]
                + r["bodyful_or_sidecar_closure"]
                == 6
            ),
            "closure_closed_only_by_sidecar": sum(
                1
                for r in rows
                if r["bodyful_or_sidecar_closure"]
                and not r["crit"]["bodyful_reachable_closure"]
            ),
        },
        # The bodies whose closure the MODULE leaves open and the PAIR closes.
        # Named for the same reason semantic_only_bodies is: a total alone
        # cannot establish WHICH body, and "the designated target is among
        # them" must be record, not prose.
        "closure_closed_only_by_sidecar_bodies": sorted(
            r["def_path"]
            for r in rows
            if r["bodyful_or_sidecar_closure"]
            and not r["crit"]["bodyful_reachable_closure"]
        ),
        # audit r2 minor 2 (wf_0a50b8bb): the semantic total alone cannot
        # establish WHICH bodies are semantic-only complete -- the landed-tip
        # record carried "+1" with no name, so "the +1 is is_zero BY NAME" was
        # prose, not record. The list is the difference the total is built
        # from, emitted so the record proves it.
        "semantic_only_bodies": sorted(
            r["def_path"]
            for r in rows
            if r["score"] - r["crit"]["bodyful_reachable_closure"]
            + r["bodyful_or_discharged_closure"]
            == 6
            and r["score"] != 6
        ),
        "a0_complete_bodies": sorted(
            (
                {
                    "def_path": r["def_path"],
                    "def_index": r["def_index"],
                    "markers_exact": r["markers_exact"],
                    "markers_vacuous": r["markers_vacuous"],
                    "flip_O0": r["flip_O0"],
                    "a6_event_lineage_equal": r["a6_event_lineage_equal"],
                }
                for r in complete
            ),
            key=lambda x: x["def_index"],
        ),
        "one_short_missing_flip_only_sample": sorted(
            r["def_path"] for r in one_short if not r["crit"]["flip_event_O3"]
        )[:40],
        "one_short_missing_closure_bodies": sorted(
            r["def_path"] for r in one_short if not r["crit"]["bodyful_reachable_closure"]
        ),
    }
    json.dump(result, open(out, "w", encoding="utf-8"), indent=1)

    print(f"bodies: {cov['totals']['bodies']}   score distribution: {dict(sorted(dist.items()))}")
    nv = [r for r in complete if r["markers_exact"] and not r["markers_vacuous"]]
    print(f"A0 6-of-6 COMPLETE: {len(complete)}  (with NON-VACUOUS markers_exact: {len(nv)})")
    print("  non-vacuous 6-of-6 bodies:")
    for r in sorted(nv, key=lambda x: x["def_index"]):
        print(f"    {r['def_path']}  di={r['def_index']}")
    print(f"A0 5-of-6, by missing criterion: {dict(missing.most_common())}")
    print(f"wrote {out}")


if __name__ == "__main__":
    main(sys.argv)
