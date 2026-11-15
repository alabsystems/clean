#!/usr/bin/env python3
"""Crystal links 0 and 1, CRATE-WIDE (decision memo 2026-09-23 §7; §11 stale items 1 and 2).

LINK 0. "Every codegen'd instance extracts (mir_blocks == extracted_blocks), refusals are
classified, and the result is reported as a fraction."  The DENOMINATOR is not the sidecar's
own member list (that would make the fraction circular): it is rustc's monomorphization
partition, printed by `-Zprint-mono-items` in the SAME compile as the sidecar dump
(`MONO_ITEM fn <instance> @@ <cgu>[<linkage>]`, one line per codegen'd item,
rustc_monomorphize/src/partitioning.rs; statics and global_asm are counted apart). Every
codegen'd FUNCTION instance is joined BY NAME to the sidecar manifest and gets exactly one class:

  extracted                  the unique image of exactly one member, whose mir_blocks equals its
                             extracted_blocks -- the only class the fraction counts
  extracted-fingerprint-dup  every candidate member is the same printed instance, differing only
                             in the producer's `::<__trust_args@hex>` suffix (one codegen instance
                             walked under two identities); NOT counted
  extracted-ambiguous        any other key shared by several members or several codegen'd items;
                             NOT counted
  refused:<class>            joined to an instance-level `escaping` row (intrinsic, virtual,
                             foreign, mir-unavailable, fuel, mono-failed, extraction-panicked,
                             block-drift), or to `panic_terminals` / `foreign_terminals` / an
                             `intrinsic-terminal` call row
  not-reached:<class>        the walk never visited it. By shape: drop-glue (a MIR `Drop` terminator
                             is not a call; `extract_member` walks Call/TailCall only), drop-impl,
                             vtable-dispatch-target (named in a virtual row, which RECORDS its
                             dispatch set and never enqueues it), trait-method, closure, shim-<k>,
                             item. The shape is not a proof of which collector edge reached it.
A member with mir_blocks != extracted_blocks is RED whatever joins it (the producer refuses such a
body in `apply_call_name_overrides`, so its presence is a producer defect), and an `escaping` row
whose reason matches no known class is RED (UNCLASSIFIED): a refusal nobody can name is not a
classified refusal.

THE NAME JOIN. The sidecar names an instance with trust_mir_extract::exact_def_path_str_with_args
(def paths, crate-qualified, `with_no_visible_paths`, lifetimes as '_, a `::<__trust_args@hex>`
suffix when the crate graph has a duplicate crate name, a `__trust_crate@hex::` prefix on an
ambiguous crate, `#nsNx` namespace tags, `#shim:<Kind>` for shims); rustc prints a mono item with
the default printer (VISIBLE paths such as std::vec::Vec for alloc::vec::Vec, no local-crate
prefix, named lifetimes, ` - shim(..)` suffixes). Level 1 removes the spelling noise (trust
suffixes/prefixes/tags, lifetimes, the local crate prefix); level 2 also strips every lower-case
path segment followed by a type/trait/item segment (the module prefix, where visible and def paths
differ). A join is taken at a level only when exactly ONE codegen'd item and exactly ONE member
carry the key there, and level 2 sees only what level 1 left, so a namesake is never borrowed.

LINK 0, MONO-ROOTED (seal-ph3 onward, `-Ztrust-ir-callee-sidecar=census:mono:`). The walk above is
rooted at local bodies and follows calls, so it never visits drop glue, `Drop` impls or
vtable-only methods. A `mono:` run roots the walk at every function instance rustc codegens
(`<mono item>` root rows, `collect_and_partition_mono_items`), so each one gets an outcome by its
EXACT sidecar name: extracted (block-equal member), refused:<class> (escaping row), terminal, or
UNACCOUNTED (RED). The denominator is still the independent `-Zprint-mono-items` list, and the two
are cross-checked: the root count must equal the MONO_ITEM count (else NOT-MET), and every
MONO_ITEM line is name-joined onto a root (reported). `census:` means members carry extraction
outcomes only and no bundle is lowered; link 0 and link 1 need nothing else. Give it as
`link0manifest=` beside the `census:local:` F/2F pair that carries link 1.

LINK 1. "The closure over ALL roots of each crate is fuel-invariant: doubling the fuel adds no
member." Manifests of one crate at fuel F and 2F, both v3, `fuel_exhausted` false at BOTH, member
NAME sets equal (not counts), root rows equal, every member's mir_digest equal. ALL ROOTS is
MEASURED, not read off the filter: with `coverage=<crate>.coverage.json` (the crate module's own
body list, which is exactly the ledger set `-Ztrust-ir-callee-sidecar=local:<s>` filters with
`def_path.contains(s)`), every piece's local-root rows must be exactly the bodies its substring
selects, and every body must be selected by some piece.

ROOT PIECES. A crate too large for one run is measured as pieces `local:<substring>` (from seal-ph3
on, `local:<a>|<b>|..` selects a body containing ANY alternative; `filter_selects` mirrors that),
given as '+'-joined manifest lists. The walk's successor set of an instance depends on the instance alone
(`extract_member`; the crate-wide scan adds no member), so link 0 is judged on the union of the
pieces' members, and link 1 piece by piece. A member two pieces disagree on is RED.

Exit 0: every requested verdict MET. Exit 1: a verdict NOT-MET or RED. Exit 2: REFUSED -- an
input is missing, malformed, not schema v3, or not the measurement it claims to be (fuel not
doubled, no 2F manifest); never green. Summary line `LINK01=<MET|NOT-MET|RED|REFUSED>`.
TRUSTED, not checked: that a case's mono list and manifest come from one compile (the dump
wrapper writes both from one cargo invocation).

Usage:
  crystal_link01_census.py --case crate=<c>,manifest=<M_F>[+<M_F piece>...],mono=<mono_F.txt>[+...]
      [,coverage=<crate>.coverage.json][,manifest2f=<M_2F>[+...]][,mono2f=<mono_2F.txt>]
      [,link0manifest=<census:mono: manifest>[+...]]   (then mono= is THAT compile's list)
      [,k=<label of the configuration K, e.g. O3c16>]  (echoed per case: one case per K)
      ... [--json OUT] [--details OUT.tsv]
  crystal_link01_census.py --self-test
Python >= 3.9, standard library only.
"""
from __future__ import annotations

import argparse
import collections
import json
import re
import sys
import tempfile
from pathlib import Path

SCHEMA = "trust-ir-callee-sidecar-v3"
REPORT_SCHEMA = "clean.crystal.link01_census/v1"
ALL_ROOTS_FILTER = "local:"

EXIT_OK, EXIT_FAIL, EXIT_REFUSED = 0, 1, 2


class Refused(Exception):
    """An input is not the measurement it claims to be. Exit 2, never green."""


# --------------------------------------------------------------------------------------------
# Name normalization
# --------------------------------------------------------------------------------------------
TRUST_ARGS = re.compile(r"::<__trust_args@[0-9a-f]+>")
TRUST_CRATE = re.compile(r"__trust_crate@[0-9a-f]+::")
NS_TAG = re.compile(r"#ns\d+[a-z]+")
LIFETIME = re.compile(r"'\{[^}]*\}|'[A-Za-z_][A-Za-z0-9_]*")
# A module segment: a lower-case identifier followed by `::` and then a path segment that is an
# identifier or an inherent-impl segment. A fn name followed by `::{closure#N}` or `::<args>` is
# NOT stripped (the lookahead refuses `{` and a non-impl `<`).
MODULE_SEGMENT = re.compile(r"\b[a-z_][A-Za-z0-9_]*::(?=[A-Za-z_]|<impl )")
SIDECAR_SHIM = re.compile(r"#shim:([A-Za-z]+)(?::(?:true|false))?$")
MONO_SUFFIX = re.compile(r"^(?P<path>.*?) - (?P<suffix>(?:dropshim|shim)(?:\(.*\))?|intrinsic|virtual#\d+)$")

# sidecar `#shim:<ShimKind head>` -> coarse class; the mono printer's suffix -> the same classes.
SIDECAR_SHIM_CLASS = {
    "VTable": "VTable", "Reify": "Reify", "ThreadLocal": "ThreadLocal",
    "ClosureOnce": "Once", "ConstructCoroutineInClosure": "Once",
    "DropGlue": "DropGlue", "AsyncDropGlueCtor": "DropGlue",
    "FnPtr": "Ty", "Clone": "Ty", "FnPtrAddr": "Ty", "AsyncDropGlue": "Ty",
    "FutureDropPoll": "FutureDropPoll",
}


def mono_shim_class(suffix: str | None, path: str) -> str | None:
    if suffix is None:
        return None
    if suffix == "intrinsic":
        return "Intrinsic"
    if suffix.startswith("virtual#"):
        return "Virtual"
    if suffix == "shim(vtable)":
        return "VTable"
    if suffix.startswith("shim(reify"):
        return "Reify"
    if suffix == "shim(tls)":
        return "ThreadLocal"
    if suffix == "shim":
        return "Once"
    if suffix.startswith("dropshim("):
        return "FutureDropPoll"
    if suffix == "shim(None)" or suffix.startswith("shim(Some("):
        return "DropGlue"
    return "Ty"


def split_sidecar_name(name: str) -> tuple[str, str | None]:
    m = SIDECAR_SHIM.search(name)
    if not m:
        return name, None
    return name[: m.start()], SIDECAR_SHIM_CLASS.get(m.group(1), m.group(1))


def norm1(path: str, local_crate: str) -> str:
    s = TRUST_ARGS.sub("", path)
    s = TRUST_CRATE.sub("", s)
    s = NS_TAG.sub("", s)
    s = LIFETIME.sub("'_", s)
    if local_crate:
        s = re.sub(r"(?<![A-Za-z0-9_])" + re.escape(local_crate) + r"::", "", s)
    return s


def norm2(path: str, local_crate: str) -> str:
    s = norm1(path, local_crate)
    prev = None
    while prev != s:
        prev = s
        s = MODULE_SEGMENT.sub("", s)
    return s


# --------------------------------------------------------------------------------------------
# Inputs
# --------------------------------------------------------------------------------------------
def parse_mono(text: str, source: str) -> dict:
    fns: list[dict] = []
    other = collections.Counter()
    for lineno, line in enumerate(text.splitlines(), 1):
        if not line.startswith("MONO_ITEM "):
            continue
        body = line[len("MONO_ITEM "):]
        if " @@" not in body:
            raise Refused(f"{source}:{lineno}: MONO_ITEM line without ' @@' partition field")
        item, placement = body.rsplit(" @@", 1)
        if item.startswith("fn "):
            inst = item[3:]
            m = MONO_SUFFIX.match(inst)
            path, suffix = (m.group("path"), m.group("suffix")) if m else (inst, None)
            fns.append({"instance": inst, "path": path, "shim": mono_shim_class(suffix, path),
                        "placement": placement.strip()})
        else:
            other[item.split(" ", 1)[0]] += 1
    if not fns:
        raise Refused(f"{source}: no `MONO_ITEM fn` line -- not a -Zprint-mono-items output")
    return {"fns": fns, "other": dict(other)}


def load_manifest(path: str) -> dict:
    try:
        text = Path(path).read_text()
    except OSError as exc:
        raise Refused(f"{path}: unreadable: {exc}")
    try:
        m = json.loads(text)
    except json.JSONDecodeError as exc:
        raise Refused(f"{path}: not JSON ({exc})")
    if not isinstance(m, dict) or m.get("schema") != SCHEMA:
        raise Refused(f"{path}: schema {m.get('schema') if isinstance(m, dict) else None!r}, "
                      f"need {SCHEMA} (fuel/fuel_exhausted are v3 fields)")
    for key, typ in (("crate", str), ("filter", str), ("fuel", int), ("fuel_exhausted", bool),
                     ("members", list), ("roots", list), ("escaping", list),
                     ("panic_terminals", list), ("foreign_terminals", list)):
        if not isinstance(m.get(key), typ) or (typ is int and isinstance(m.get(key), bool)):
            raise Refused(f"{path}: `{key}` missing or not {typ.__name__}")
    for i, x in enumerate(m["members"]):
        if not isinstance(x, dict) or not isinstance(x.get("name"), str) \
                or not isinstance(x.get("mir_blocks"), int) \
                or not isinstance(x.get("extracted_blocks"), int) \
                or not isinstance(x.get("calls"), list):
            raise Refused(f"{path}: member row {i} malformed")
    return m


# --------------------------------------------------------------------------------------------
# Escaping rows: which INSTANCE each names and why (callee_sidecar.rs `run`, every `escaping.push`)
# --------------------------------------------------------------------------------------------
INSTANCE_REFUSALS = [
    ("intrinsic", re.compile(r"^(?P<n>.*): bodyless instance kind Intrinsic$")),
    ("virtual", re.compile(r"^(?P<n>.*): bodyless instance kind Virtual(?:;.*| \(.*)?$", re.S)),
    ("foreign", re.compile(r"^(?P<n>.*): foreign item \(no Rust body on this target\)(?:; foreign callback: .*)?$", re.S)),
    ("mir-unavailable", re.compile(r"^(?P<n>.*): MIR unavailable$")),
    ("fuel", re.compile(r"^(?P<n>.*): member fuel \(\d+\) exhausted$")),
    ("block-drift", re.compile(r"^(?P<n>.*): MIR/extracted block-count drift while renaming direct calls: MIR=\d+ extracted=\d+$")),
    ("mono-failed", re.compile(r"^(?P<n>.*): MIR monomorphization failed: .*$", re.S)),
    ("extraction-panicked", re.compile(r"^(?P<n>.*): extraction panicked$")),
]
# Rows about an EDGE of a member that WAS extracted -- they refuse no instance.
EDGE_ROWS = [
    ("edge:indirect", re.compile(r"^(?P<n>.*): indirect call \(non-const func operand of type .*$", re.S)),
    ("edge:unresolved", re.compile(r"^(?P<n>.*): call .*: instance resolution (?:ambiguous|error).*$", re.S)),
]


def classify_escaping(row: str) -> tuple[str, str | None]:
    for cls, rx in INSTANCE_REFUSALS:
        m = rx.match(row)
        if m:
            return cls, m.group("n")
    for cls, rx in EDGE_ROWS:
        m = rx.match(row)
        if m:
            return cls, m.group("n")
    return "UNCLASSIFIED", None


def split_top_level(s: str) -> list[str]:
    out, depth, cur = [], 0, []
    pairs = {"<": ">", "(": ")", "[": "]", "{": "}"}
    closers = set(pairs.values())
    i = 0
    while i < len(s):
        c = s[i]
        if c == "-" and i + 1 < len(s) and s[i + 1] == ">":  # `->` is not a closer
            cur.append("->")
            i += 2
            continue
        if c in pairs:
            depth += 1
        elif c in closers:
            depth -= 1
        if c == "," and depth == 0:
            out.append("".join(cur).strip())
            cur = []
        else:
            cur.append(c)
        i += 1
    if "".join(cur).strip():
        out.append("".join(cur).strip())
    return out


VTABLE_ENUM = re.compile(r"vtable enumeration \d+ \[")


def vtable_targets(row: str) -> list[str]:
    """The dispatch-set names a virtual row RECORDS (never enqueues)."""
    m = VTABLE_ENUM.search(row)
    if not m:
        return []
    start, depth = m.end(), 1
    i = start
    while i < len(row) and depth:
        if row[i] == "[":
            depth += 1
        elif row[i] == "]":
            depth -= 1
        i += 1
    return split_top_level(row[start: i - 1])


# --------------------------------------------------------------------------------------------
# Link 0
# --------------------------------------------------------------------------------------------
def _index(names_with_payload, local_crate):
    """[(name, payload)] -> {level: {(key, shimclass): [payload]}}"""
    idx = {1: collections.defaultdict(list), 2: collections.defaultdict(list)}
    for name, payload in names_with_payload:
        path, shim = split_sidecar_name(name)
        idx[1][(norm1(path, local_crate), shim)].append(payload)
        idx[2][(norm2(path, local_crate), shim)].append(payload)
    return idx


def _lookup(idx, path, shim, local_crate):
    for level, fn in ((1, norm1), (2, norm2)):
        hit = idx[level].get((fn(path, local_crate), shim))
        if hit:
            return level, hit
    return None, []


def _escaping_index(manifest: dict) -> tuple[dict, list[str], collections.Counter, list[str]]:
    """name -> instance-level refusal class; UNCLASSIFIED rows; counts by class; vtable targets."""
    by_name: dict[str, str] = {}
    unclassified: list[str] = []
    classes = collections.Counter()
    vtable_names: list[str] = []
    for row in manifest["escaping"]:
        if not isinstance(row, str):
            raise Refused("an `escaping` row is not a string")
        cls, name = classify_escaping(row)
        classes[cls] += 1
        if cls == "UNCLASSIFIED":
            unclassified.append(row)
        elif not cls.startswith("edge:"):
            by_name.setdefault(name, cls)
        if cls == "virtual":
            vtable_names.extend(vtable_targets(row))
    return by_name, unclassified, classes, vtable_names


def _intrinsic_terminals(manifest: dict) -> set:
    out = set()
    for x in manifest["members"]:
        for c in x["calls"]:
            cls = c.get("class", "") if isinstance(c, dict) else ""
            if cls.startswith("intrinsic-terminal: "):
                out.add(cls[len("intrinsic-terminal: "):])
    return out


def link0_mono(manifest: dict, mono: dict) -> dict:
    """LINK 0 over a `mono:` manifest (seal-ph3 onward): the walk is ROOTED at every function
    instance rustc codegens (`<mono item>` root rows, `collect_and_partition_mono_items`), so each
    codegen'd instance has an outcome by its exact sidecar name. The denominator stays the
    independent `-Zprint-mono-items` list of the same compile, and the two sets are cross-checked:
    by count, and by the name join of every MONO_ITEM line onto a root."""
    local = manifest["crate"]
    red: list[str] = []
    drift = [x["name"] for x in manifest["members"] if x["mir_blocks"] != x["extracted_blocks"]]
    for n in drift:
        red.append(f"member {n} has mir_blocks != extracted_blocks")
    members = {x["name"]: x for x in manifest["members"]}
    esc, unclassified, esc_classes, _ = _escaping_index(manifest)
    for row in unclassified:
        red.append(f"UNCLASSIFIED escaping row: {row[:200]}")
    panic, foreign = set(manifest["panic_terminals"]), set(manifest["foreign_terminals"])
    intrinsic = _intrinsic_terminals(manifest)
    mroots = [r for r in manifest["roots"] if r.get("caller") == "<mono item>"]
    names = [r.get("resolved") for r in mroots]
    if any(not isinstance(n, str) for n in names):
        raise Refused("a `<mono item>` root row has no resolved instance name")
    if len(set(names)) != len(names):
        red.append(f"{len(names) - len(set(names))} `<mono item>` roots name one instance twice")
    classes = collections.Counter()
    samples = collections.defaultdict(list)
    details: list[tuple[str, str]] = []
    for n in names:
        if n in members:
            m = members[n]
            cls = "extracted" if m["mir_blocks"] == m["extracted_blocks"] else "RED:block-drift"
        elif n in esc:
            cls = "refused:" + esc[n]
        elif n in panic:
            cls = "terminal:panic"
        elif n in foreign:
            cls = "terminal:foreign"
        elif n in intrinsic:
            cls = "refused:intrinsic"
        else:
            cls = "UNACCOUNTED"
        classes[cls] += 1
        details.append((cls, n))
        if len(samples[cls]) < 8:
            samples[cls].append(n[:300])
    if classes.get("UNACCOUNTED"):
        red.append(f"{classes['UNACCOUNTED']} codegen'd instance(s) rooted with no member, no escaping row "
                   f"and no terminal: an outcome the manifest does not account for")
    if any(k.startswith("RED:") for k in classes):
        red.append("a codegen'd instance's member has block counts that differ")
    total = len(mono["fns"])
    # The independent cross-check: every MONO_ITEM line must name ONE root. Joined through the same
    # two-level name join as the reach census, over the roots' exact sidecar names.
    root_idx = _index([(n, n) for n in names], local)
    joined = collections.Counter()
    unjoined: list[str] = []
    for item in mono["fns"]:
        level, hit = _lookup(root_idx, item["path"], item["shim"], local)
        if hit and len(set(hit)) == 1:
            joined[hit[0]] += 1
        else:
            unjoined.append(item["instance"])
    cover: list[str] = []
    if len(mroots) != total:
        cover.append(f"{len(mroots)} `<mono item>` roots against {total} `MONO_ITEM fn` lines of the same compile")
    extracted = classes.get("extracted", 0)
    verdict = "RED" if red else ("MET" if extracted == total and not cover else "NOT-MET")
    return {
        "mode": "mono",
        "verdict": verdict,
        "codegen_fn_instances": total,
        "codegen_other_items": mono["other"],
        "mono_roots": len(mroots),
        "extracted": extracted,
        "fraction": round(extracted / total, 6) if total else 0.0,
        "fraction_text": f"{extracted}/{total}",
        "extracted_incl_ambiguous": extracted,
        "classes": dict(sorted(classes.items())),
        "mono_list_joined_to_one_root": sum(1 for c in joined.values() if c == 1),
        "mono_list_unjoined": len(unjoined),
        "mono_list_unjoined_samples": [u[:300] for u in unjoined[:8]],
        "roots_joined_by_two_mono_lines": sum(1 for c in joined.values() if c > 1),
        "members": len(members),
        "members_joined": extracted,
        "members_joined_more_than_once": 0,
        "members_block_drift": drift,
        "escaping_rows_by_class": dict(sorted(esc_classes.items())),
        "unclassified_escaping": unclassified[:20],
        "red": red,
        "root_cover_reasons": cover,
        "samples": {k: v for k, v in sorted(samples.items()) if k != "extracted"},
        "_details": details,
    }


def link0(manifest: dict, mono: dict) -> dict:
    if manifest.get("mode") == "mono":
        return link0_mono(manifest, mono)
    local = manifest["crate"]
    red: list[str] = []
    drift = [x["name"] for x in manifest["members"] if x["mir_blocks"] != x["extracted_blocks"]]
    for n in drift:
        red.append(f"member {n} has mir_blocks != extracted_blocks")
    member_idx = _index([(x["name"], x) for x in manifest["members"]], local)

    refusal_rows = []
    unclassified = []
    vtable_names = []
    esc_classes = collections.Counter()
    for row in manifest["escaping"]:
        if not isinstance(row, str):
            raise Refused("an `escaping` row is not a string")
        cls, name = classify_escaping(row)
        esc_classes[cls] += 1
        if cls == "UNCLASSIFIED":
            unclassified.append(row)
        elif not cls.startswith("edge:"):
            refusal_rows.append((name, cls))
        if cls == "virtual":
            vtable_names.extend(vtable_targets(row))
    for row in unclassified:
        red.append(f"UNCLASSIFIED escaping row: {row[:200]}")
    refusal_idx = _index(refusal_rows, local)
    terminal_rows = [(n, "terminal:panic") for n in manifest["panic_terminals"]]
    terminal_rows += [(n, "terminal:foreign") for n in manifest["foreign_terminals"]]
    intrinsic_terminals = set()
    for x in manifest["members"]:
        for c in x["calls"]:
            cls = c.get("class", "") if isinstance(c, dict) else ""
            if cls.startswith("intrinsic-terminal: "):
                intrinsic_terminals.add(cls[len("intrinsic-terminal: "):])
    terminal_rows += [(n, "refused:intrinsic") for n in sorted(intrinsic_terminals)]
    terminal_idx = _index(terminal_rows, local)
    vtable_idx = _index([(n, n) for n in vtable_names], local)

    classes = collections.Counter()
    joined_level = collections.Counter()
    ambiguous_keys = 0
    samples = collections.defaultdict(list)
    details: list[tuple[str, str]] = []
    per_member_hits = collections.Counter()
    # BIDIRECTIONAL uniqueness. A join is taken at a level only when exactly ONE codegen'd item and
    # exactly ONE member carry the key there: level-2 stripping can map two distinct instances (two
    # types named `Error` in different modules) to one key, and a codegen'd instance the walk never
    # reached must not borrow the member of its namesake. Level 2 sees only what level 1 left.
    keys = [((norm1(it["path"], local), it["shim"]), (norm2(it["path"], local), it["shim"])) for it in mono["fns"]]
    mono_c1 = collections.Counter(k1 for k1, _ in keys)
    joined1 = {}
    for i, (k1, _) in enumerate(keys):
        hit = member_idx[1].get(k1, [])
        if len(hit) == 1 and mono_c1[k1] == 1:
            joined1[i] = hit[0]
    taken = {id(m) for m in joined1.values()}
    mono_c2 = collections.Counter(k2 for i, (_, k2) in enumerate(keys) if i not in joined1)
    for i, item in enumerate(mono["fns"]):
        path, shim = item["path"], item["shim"]
        k1, k2 = keys[i]
        if i in joined1:
            level, hit = 1, [joined1[i]]
        else:
            hit1 = member_idx[1].get(k1, [])
            hit2 = [m for m in member_idx[2].get(k2, []) if id(m) not in taken]
            if hit1:
                level, hit = 1, hit1 + [None]  # ambiguous at level 1
            elif len(hit2) == 1 and mono_c2[k2] == 1:
                level, hit = 2, hit2
            elif hit2:
                level, hit = 2, hit2 + [None]  # ambiguous at level 2
            else:
                level, hit = None, []
        if hit:
            if len(hit) == 1:
                m = hit[0]
                per_member_hits[m["name"]] += 1
                cls = "extracted" if m["mir_blocks"] == m["extracted_blocks"] else "RED:block-drift"
                joined_level[level] += 1
            else:
                ambiguous_keys += 1
                real = [m for m in hit if m is not None]
                ok = all(m["mir_blocks"] == m["extracted_blocks"] for m in real)
                # The FINGERPRINT-DUPLICATE case: every candidate is the same printed instance and
                # differs only in the producer's `::<__trust_args@hex>` suffix (convert.rs
                # `disambiguate_generic_call_path`), with this codegen'd item alone on the key. The
                # walk reached one codegen instance under two identities. Reported apart and NOT
                # counted as extracted: a later content join needs a unique image.
                same_print = len({TRUST_ARGS.sub("", m["name"]) for m in real}) == 1
                single_item = (mono_c1[k1] == 1) if level == 1 else (mono_c2[k2] == 1)
                if not ok:
                    cls = "RED:block-drift"
                elif len(real) > 1 and same_print and single_item:
                    cls = "extracted-fingerprint-dup"
                else:
                    cls = "extracted-ambiguous"
        else:
            _, rhit = _lookup(refusal_idx, path, shim, local)
            _, thit = _lookup(terminal_idx, path, shim, local)
            _, vhit = _lookup(vtable_idx, path, shim, local)
            if rhit:
                cls = "refused:" + sorted(set(rhit))[0]
            elif thit:
                cls = sorted(set(thit))[0]
            elif vhit:
                cls = "not-reached:vtable-dispatch-target"
            elif shim == "DropGlue":
                cls = "not-reached:drop-glue"
            elif shim is not None:
                cls = "not-reached:shim-" + shim
            elif re.search(r" as (?:[A-Za-z_][A-Za-z0-9_]*::)*Drop>::drop$", path):
                cls = "not-reached:drop-impl"
            elif (path.startswith("<") and " as " in path) or re.search(r"<impl .* for .*>::[A-Za-z_][A-Za-z0-9_]*(?:::<.*>)?$", path):
                # a trait method: the collector reaches these through vtables (an unsizing coercion
                # puts every entry of the vtable in the partition) as well as through calls
                cls = "not-reached:trait-method"
            elif re.search(r"::\{closure#\d+\}$", path):
                cls = "not-reached:closure"
            else:
                cls = "not-reached:item"
        classes[cls] += 1
        details.append((cls, item["instance"]))
        if len(samples[cls]) < 8:
            samples[cls].append(item["instance"][:300])
    total = len(mono["fns"])
    extracted = classes.get("extracted", 0)
    multi = {n: c for n, c in per_member_hits.items() if c > 1}
    if any(k.startswith("RED:") for k in classes):
        red.append("a codegen'd instance joined a member whose block counts differ")
    verdict = "RED" if red else ("MET" if extracted == total else "NOT-MET")
    return {
        "verdict": verdict,
        "codegen_fn_instances": total,
        "codegen_other_items": mono["other"],
        "extracted": extracted,
        "fraction": round(extracted / total, 6) if total else 0.0,
        "fraction_text": f"{extracted}/{total}",
        "extracted_incl_ambiguous": extracted + classes.get("extracted-ambiguous", 0) + classes.get("extracted-fingerprint-dup", 0),
        "classes": dict(sorted(classes.items())),
        "joined_by_level": {str(k): v for k, v in sorted(joined_level.items())},
        "ambiguous_keys": ambiguous_keys,
        "members": len(manifest["members"]),
        "members_joined": len(per_member_hits),
        "members_joined_more_than_once": len(multi),
        "members_block_drift": drift,
        "escaping_rows_by_class": dict(sorted(esc_classes.items())),
        "unclassified_escaping": unclassified[:20],
        "red": red,
        "samples": {k: v for k, v in sorted(samples.items()) if k != "extracted"},
        "_details": details,
    }


# --------------------------------------------------------------------------------------------
# Root partitions: a crate too large for one sidecar run is measured as PIECES, each with filter
# `local:<substring>`. The walk's successor set of an instance is a function of the instance alone
# (callee_sidecar.rs `extract_member`; the crate-wide scan adds no member), so the closure over a
# union of roots is the union of the pieces' closures, and link 0 is judged on that union.
# --------------------------------------------------------------------------------------------
def merge_manifests(ms: list[dict]) -> tuple[dict, list[str]]:
    red: list[str] = []
    crates = {m["crate"] for m in ms}
    if len(crates) != 1:
        raise Refused(f"pieces name different crates: {sorted(crates)}")
    members: dict[str, dict] = {}
    for m in ms:
        for x in m["members"]:
            prev = members.get(x["name"])
            if prev is None:
                members[x["name"]] = x
            elif (prev["mir_blocks"], prev["extracted_blocks"], prev.get("mir_digest")) != \
                    (x["mir_blocks"], x["extracted_blocks"], x.get("mir_digest")):
                red.append(f"member {x['name'][:200]} differs between pieces (blocks or mir_digest)")
    def union(key):
        seen, out = set(), []
        for m in ms:
            for v in m[key]:
                if v not in seen:
                    seen.add(v)
                    out.append(v)
        return out
    roots, seen_roots = [], set()
    for m in ms:
        for r in m["roots"]:
            key = json.dumps(r, sort_keys=True)
            if key not in seen_roots:
                seen_roots.add(key)
                roots.append(r)
    modes = {parse_filter(m["filter"])[1] for m in ms}
    if len(modes) != 1:
        raise Refused(f"pieces mix root modes {sorted(modes)}")
    merged = {"crate": ms[0]["crate"], "filter": "+".join(m["filter"] for m in ms), "mode": modes.pop(),
              "roots": roots,
              "members": list(members.values()), "escaping": union("escaping"),
              "panic_terminals": union("panic_terminals"), "foreign_terminals": union("foreign_terminals"),
              "fuel_exhausted": any(m["fuel_exhausted"] for m in ms)}
    return merged, red


def load_coverage(path: str) -> list[str]:
    try:
        c = json.loads(Path(path).read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise Refused(f"{path}: unreadable coverage: {exc}")
    bodies = c.get("bodies") if isinstance(c, dict) else None
    if not isinstance(bodies, list) or not all(isinstance(b, dict) and isinstance(b.get("def_path"), str) for b in bodies):
        raise Refused(f"{path}: no `bodies` list of def_path rows")
    return [b["def_path"] for b in bodies]


def parse_filter(spelling: str) -> tuple[bool, str, str]:
    """(census, mode, pieces) of a sidecar filter, mirroring callee_sidecar.rs
    `parse_sidecar_filter`: the grammar is `[census:][mono:|local:]<pieces>`. mode is "mono",
    "local", or "edges" (neither prefix: the roots are the selected bodies' foreign callee edges)."""
    census = spelling.startswith("census:")
    rest = spelling[len("census:"):] if census else spelling
    for mode in ("mono", "local"):
        if rest.startswith(mode + ":"):
            return census, mode, rest[len(mode) + 1:]
    return census, "edges", rest


def filter_selects(pieces: str, name: str) -> bool:
    """The sidecar's selection by `<pieces>` (callee_sidecar.rs `filter_alternatives`): an EMPTY
    string is the one alternative "" and selects everything; otherwise the `|`-separated,
    non-empty alternatives, and a name is selected when it contains ANY of them. A filter
    without `|` is the plain substring test, so every earlier filter keeps its meaning (and a
    filter made only of `|` selects nothing)."""
    if pieces == "":
        return True
    return any(a in name for a in pieces.split("|") if a)


def roots_cover(pieces: list[dict], bodies: list[str] | None) -> list[str]:
    """ALL roots, measured: the local-root rows of the pieces against the crate module's own body
    list (coverage.json of the same compile), which is exactly the ledger set the filter reads."""
    reasons: list[str] = []
    subs = []
    for m in pieces:
        _, mode, sub = parse_filter(m["filter"])
        if mode != "local":
            reasons.append(f"filter {m['filter']!r} is not a `local:` filter, so its roots are not the crate's bodies")
            return reasons
        subs.append(sub)
    if bodies is None:
        if len(pieces) != 1 or subs[0] != "":
            reasons.append("pieces with a substring filter need coverage= to prove they cover ALL roots")
        return reasons
    for m, sub in zip(pieces, subs):
        want = collections.Counter(b for b in bodies if filter_selects(sub, b))
        got = collections.Counter(r.get("callee_def_path") for r in m["roots"] if r.get("caller") == "<local root>")
        if want != got:
            miss, extra = want - got, got - want
            reasons.append(f"piece {m['filter']!r}: local roots are not the coverage bodies its filter selects "
                           f"({sum(miss.values())} missing, e.g. {next(iter(miss), '')!s:.120}; {sum(extra.values())} extra)")
    unmatched = [b for b in bodies if not any(filter_selects(sub, b) for sub in subs)]
    if unmatched:
        reasons.append(f"{len(unmatched)} crate body/bodies matched by no piece's filter (not ALL roots), e.g. {unmatched[0][:160]}")
    return reasons


# --------------------------------------------------------------------------------------------
# Link 1
# --------------------------------------------------------------------------------------------
def link1_piece(m1: dict, m2: dict) -> dict:
    reasons: list[str] = []
    if m1["crate"] != m2["crate"]:
        raise Refused(f"link 1 compares two crates: {m1['crate']} vs {m2['crate']}")
    if m2["fuel"] != 2 * m1["fuel"]:
        raise Refused(f"link 1 needs fuel F and 2F; got {m1['fuel']} and {m2['fuel']}")
    if m1["filter"] != m2["filter"]:
        raise Refused(f"link 1 compares two filters: {m1['filter']!r} vs {m2['filter']!r}")
    for tag, m in (("F", m1), ("2F", m2)):
        if m["fuel_exhausted"]:
            reasons.append(f"fuel_exhausted is true at {tag} (fuel {m['fuel']}, filter {m['filter']!r})")
    n1 = [x["name"] for x in m1["members"]]
    n2 = [x["name"] for x in m2["members"]]
    s1, s2 = set(n1), set(n2)
    if len(s1) != len(n1) or len(s2) != len(n2):
        reasons.append("a manifest names one member twice")
    added = sorted(s2 - s1)
    lost = sorted(s1 - s2)
    if added:
        reasons.append(f"{len(added)} member(s) at 2F not at F, e.g. {added[0][:200]}")
    if lost:
        reasons.append(f"{len(lost)} member(s) at F not at 2F, e.g. {lost[0][:200]}")
    d1 = {x["name"]: x.get("mir_digest") for x in m1["members"]}
    d2 = {x["name"]: x.get("mir_digest") for x in m2["members"]}
    digest_diff = sorted(n for n in s1 & s2 if d1[n] != d2[n])
    if digest_diff:
        reasons.append(f"{len(digest_diff)} member(s) with a different mir_digest at 2F, e.g. {digest_diff[0][:200]}")
    r1 = [json.dumps(r, sort_keys=True) for r in m1["roots"]]
    r2 = [json.dumps(r, sort_keys=True) for r in m2["roots"]]
    if r1 != r2:
        reasons.append(f"root rows differ ({len(r1)} vs {len(r2)})")
    outcomes = collections.Counter()
    for r in m1["roots"]:
        o = str(r.get("outcome", ""))
        outcomes[o.split(":")[0] if o.startswith(("refused", "subsumed")) else o] += 1
    return {
        "filter": m1["filter"],
        "verdict": "NOT-MET" if reasons else "MET",
        "fuel": [m1["fuel"], m2["fuel"]],
        "fuel_exhausted": [m1["fuel_exhausted"], m2["fuel_exhausted"]],
        "members": [len(n1), len(n2)],
        "added_at_2f": added[:20],
        "lost_at_2f": lost[:20],
        "digest_mismatches": len(digest_diff),
        "roots": len(m1["roots"]),
        "local_roots": sum(1 for r in m1["roots"] if r.get("caller") == "<local root>"),
        "root_outcomes": dict(sorted(outcomes.items())),
        "reasons": reasons,
    }


def link1(p1: list[dict], p2: list[dict], bodies: list[str] | None) -> dict:
    if len(p1) != len(p2):
        raise Refused(f"link 1 needs one 2F manifest per F piece; got {len(p1)} and {len(p2)}")
    pieces = [link1_piece(a, b) for a, b in zip(p1, p2)]
    reasons = [r for pc in pieces for r in pc["reasons"]]
    reasons += roots_cover(p1, bodies)
    union1 = {x["name"] for m in p1 for x in m["members"]}
    union2 = {x["name"] for m in p2 for x in m["members"]}
    return {
        "verdict": "NOT-MET" if reasons else "MET",
        "pieces": pieces,
        "fuel": [p1[0]["fuel"], p2[0]["fuel"]],
        "fuel_exhausted": [any(m["fuel_exhausted"] for m in p1), any(m["fuel_exhausted"] for m in p2)],
        "members": [len(union1), len(union2)],
        "added_at_2f": sorted(union2 - union1)[:20],
        "lost_at_2f": sorted(union1 - union2)[:20],
        "digest_mismatches": sum(pc["digest_mismatches"] for pc in pieces),
        "roots": sum(pc["roots"] for pc in pieces),
        "local_roots": sum(pc["local_roots"] for pc in pieces),
        "coverage_bodies": None if bodies is None else len(bodies),
        "root_outcomes": dict(sum((collections.Counter(pc["root_outcomes"]) for pc in pieces), collections.Counter())),
        "reasons": reasons,
    }


# --------------------------------------------------------------------------------------------
# Driver
# --------------------------------------------------------------------------------------------
CASE_KEYS = {"crate", "manifest", "mono", "manifest2f", "mono2f", "coverage", "link0manifest", "k"}


def parse_case(spec: str) -> dict:
    case = {}
    for part in spec.split(","):
        if "=" not in part:
            raise Refused(f"--case {spec!r}: `{part}` is not key=value")
        k, v = part.split("=", 1)
        case[k.strip()] = v.strip()
    unknown = set(case) - CASE_KEYS
    if unknown or "mono" not in case or not ({"manifest", "link0manifest"} & set(case)):
        raise Refused(f"--case {spec!r}: needs crate=, mono=, and manifest= and/or link0manifest= (optional "
                      f"manifest2f=, mono2f=, coverage=; manifest lists may be '+'-joined root pieces); "
                      f"unknown {sorted(unknown)}")
    if "manifest2f" in case and "manifest" not in case:
        raise Refused(f"--case {spec!r}: manifest2f= needs its F side, manifest=")
    return case


def _read_mono(path: str) -> dict:
    try:
        return parse_mono(Path(path).read_text(), path)
    except OSError as exc:
        raise Refused(f"{path}: unreadable: {exc}")


def run_case(case: dict) -> dict:
    """link 0 reads `link0manifest` (a `census:mono:` run, seal-ph3 on) when given, else `manifest`;
    link 1 reads `manifest` (F) against `manifest2f` (2F)."""
    p1 = [load_manifest(p) for p in case["manifest"].split("+")] if "manifest" in case else []
    l0 = [load_manifest(p) for p in case["link0manifest"].split("+")] if "link0manifest" in case else p1
    merged0, merge_red = merge_manifests(l0)
    if case.get("crate") and case["crate"].replace("-", "_") != merged0["crate"]:
        raise Refused(f"case crate {case['crate']} but the manifest is for {merged0['crate']}")
    if p1 and p1[0]["crate"] != merged0["crate"]:
        raise Refused(f"link 0 and link 1 manifests name different crates")
    monos = [_read_mono(p) for p in case["mono"].split("+")]
    mono = monos[0]
    bodies = load_coverage(case["coverage"]) if "coverage" in case else None
    head = p1[0] if p1 else l0[0]
    out = {"crate": merged0["crate"], "k": case.get("k", ""),
           "filter": "+".join(m["filter"] for m in p1) if p1 else "",
           "link0_filter": merged0["filter"], "pieces": len(p1),
           "fuel": head["fuel"], "fuel_exhausted": any(m["fuel_exhausted"] for m in (p1 or l0)),
           "link0_fuel": l0[0]["fuel"], "link0_fuel_exhausted": merged0["fuel_exhausted"],
           "lowering": [str(m.get("lowering", ""))[:300] for m in (p1 or l0)],
           "closed": [m.get("closed") for m in (p1 or l0)],
           "closed_modulo_foreign": [m.get("closed_modulo_foreign") for m in (p1 or l0)],
           "inputs": dict(case)}
    out["link0"] = link0(merged0, mono)
    out["link0"]["red"].extend(merge_red)
    for other in monos[1:]:
        if sorted(x["instance"] for x in other["fns"]) != sorted(x["instance"] for x in mono["fns"]):
            out["link0"]["red"].append("the pieces' compiles codegen different instance sets")
    if out["link0"]["red"]:
        out["link0"]["verdict"] = "RED"
    if merged0["mode"] != "mono":
        cover = roots_cover(l0, bodies)
        out["link0"]["root_cover_reasons"] = cover
    else:
        cover = out["link0"]["root_cover_reasons"]
    if merged0["fuel_exhausted"]:
        cover.append("the link-0 walk exhausted its fuel: an instance may be unvisited for that reason alone")
    if cover and out["link0"]["verdict"] == "MET":
        out["link0"]["verdict"] = "NOT-MET"
    if "manifest2f" in case:
        p2 = [load_manifest(p) for p in case["manifest2f"].split("+")]
        out["link1"] = link1(p1, p2, bodies)
        if "mono2f" in case:
            mono2 = _read_mono(case["mono2f"].split("+")[0])
            a = sorted(x["instance"] for x in mono["fns"])
            b = sorted(x["instance"] for x in mono2["fns"])
            out["link1"]["codegen_set_equal_at_2f"] = a == b
            if a != b:
                out["link1"]["verdict"] = "NOT-MET"
                out["link1"]["reasons"].append("the codegen'd instance set differs between the F and 2F compiles")
    else:
        out["link1"] = {"verdict": "NOT-MEASURED", "reasons": ["no manifest2f given"]}
    return out


def overall(cases: list[dict]) -> str:
    vs = []
    for c in cases:
        vs += [c["link0"]["verdict"], c["link1"]["verdict"]]
    if "RED" in vs:
        return "RED"
    if "NOT-MEASURED" in vs:
        return "REFUSED"
    if "NOT-MET" in vs:
        return "NOT-MET"
    return "MET"


def render(cases: list[dict]) -> str:
    lines = []
    for c in cases:
        l0, l1 = c["link0"], c["link1"]
        lines.append(f"== {c['crate']}{' [K ' + c['k'] + ']' if c['k'] else ''} (link-1 filter {c['filter']!r}, fuel {c['fuel']}, exhausted {c['fuel_exhausted']}; "
                     f"link-0 filter {c['link0_filter']!r}, fuel {c['link0_fuel']}, exhausted {c['link0_fuel_exhausted']})")
        if l0.get("mode") == "mono":
            lines.append(f"   link0 roots: {l0['mono_roots']} `<mono item>` roots vs {l0['codegen_fn_instances']} MONO_ITEM fn lines; "
                         f"{l0['mono_list_joined_to_one_root']} lines join exactly one root, {l0['mono_list_unjoined']} do not")
        lines.append(f"   link0 {l0['verdict']}: extracted {l0['fraction_text']} = {100 * l0['fraction']:.2f}% of codegen'd fn instances "
                     f"(+{l0['extracted_incl_ambiguous'] - l0['extracted']} ambiguous); members {l0['members']}, "
                     f"joined {l0['members_joined']}; other mono items {l0['codegen_other_items']}")
        for k, v in l0["classes"].items():
            lines.append(f"      {v:7d}  {k}")
        lines.append(f"      escaping rows by class: {l0['escaping_rows_by_class']}")
        for r in l0["red"][:10]:
            lines.append(f"      RED: {r}")
        for r in l0.get("root_cover_reasons", []):
            lines.append(f"      roots: {r}")
        if l1["verdict"] == "NOT-MEASURED":
            lines.append("   link1 NOT-MEASURED (no 2F manifest)")
        else:
            lines.append(f"   link1 {l1['verdict']}: fuel {l1['fuel'][0]}/{l1['fuel'][1]}, exhausted {l1['fuel_exhausted']}, "
                         f"members {l1['members'][0]}/{l1['members'][1]}, added {len(l1['added_at_2f'])}, lost {len(l1['lost_at_2f'])}, "
                         f"digest mismatches {l1['digest_mismatches']}, roots {l1['roots']} ({l1['local_roots']} local, "
                         f"coverage bodies {l1['coverage_bodies']}) {l1['root_outcomes']}")
            if len(l1["pieces"]) > 1:
                for pc in l1["pieces"]:
                    lines.append(f"      piece {pc['filter']!r}: {pc['verdict']} members {pc['members'][0]}/{pc['members'][1]} "
                                 f"exhausted {pc['fuel_exhausted']} local roots {pc['local_roots']}")
            for r in l1["reasons"]:
                lines.append(f"      reason: {r}")
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--case", action="append", default=[])
    ap.add_argument("--json")
    ap.add_argument("--details", help="write every codegen'd instance with its class, one TSV row each")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args(argv)
    if a.self_test:
        return self_test()
    if not a.case:
        ap.error("give at least one --case, or --self-test")
    try:
        cases = [run_case(parse_case(s)) for s in a.case]
    except Refused as exc:
        print(f"REFUSED: {exc}", file=sys.stderr)
        print("LINK01=REFUSED")
        return EXIT_REFUSED
    print(render(cases))
    verdict = overall(cases)
    for c in cases:
        print(f"LINK01 crate={c['crate']}{' k=' + c['k'] if c['k'] else ''} link0={c['link0']['verdict']} "
              f"extracted={c['link0']['fraction_text']} link1={c['link1']['verdict']}")
    print(f"LINK01={verdict}")
    if a.details:
        with open(a.details, "w") as fh:
            for c in cases:
                for cls, inst in c["link0"]["_details"]:
                    fh.write(f"{c['crate']}\t{cls}\t{inst}\n")
    for c in cases:
        c["link0"].pop("_details", None)
    if a.json:
        Path(a.json).write_text(json.dumps({"schema": REPORT_SCHEMA, "verdict": verdict, "cases": cases},
                                           indent=1, sort_keys=False) + "\n")
    return {"MET": EXIT_OK, "REFUSED": EXIT_REFUSED}.get(verdict, EXIT_FAIL)


# --------------------------------------------------------------------------------------------
# Self-test: synthetic inputs, and mutation arms that must go red
# --------------------------------------------------------------------------------------------
def _member(i, name, blocks, calls=(), digest=None):
    return {"sidecar_func_id": i, "name": name, "instance_kind": "Shim" if "#shim:" in name else "Item",
            "def_path": name, "mir_blocks": blocks, "extracted_blocks": blocks,
            "mir_digest": digest or f"sha256:{i:064x}", "calls": list(calls)}


def _synthetic(fuel=64):
    members = [
        _member(0, "kcrate::tc::infer::<impl kcrate::tc::TypeChecker<'_>>::infer_type::<__trust_args@00aa>", 6,
                [{"bb": 0, "site": "x", "resolved": "alloc::vec::Vec::<kcrate::Expr>::push", "class": "member"},
                 {"bb": 1, "site": "y", "resolved": "core::intrinsics::cold_path", "class": "intrinsic-terminal: core::intrinsics::cold_path",
                  "evidence": "native-op:fence"}]),
        _member(1, "alloc::vec::Vec::<kcrate::Expr>::push", 2),
        _member(2, "__trust_crate@c82c5f8d9d3d6b59::hashbrown::raw::RawTableInner::new_uninitialized::<alloc::alloc::Global>::<__trust_args@0e3c>", 20),
        _member(3, "kcrate::tc::infer::<impl kcrate::tc::TypeChecker<'_>>::infer_type::{closure#0}", 3),
        _member(4, "<for<'_> fn(&'_ str) -> alloc::string::String {kcrate::f} as core::ops::function::FnOnce<(&str,)>>::call_once#shim:FnPtr", 2),
        _member(5, "<kcrate::S as core::ops::drop::Drop>::drop", 1),
    ]
    return {
        "schema": SCHEMA, "crate": "kcrate", "filter": ALL_ROOTS_FILTER, "producer": {},
        "closed": False, "closed_meaning": "", "closed_modulo_foreign": False, "closed_modulo_foreign_meaning": "",
        "lowering": "ok", "fuel": fuel, "fuel_exhausted": False, "dispatch_scan": None,
        "roots": [{"caller": "<local root>", "callee_def_path": "tc::infer::<impl tc::TypeChecker<'env>>::infer_type",
                   "crate_decl_func_ids": [0], "resolved": members[0]["name"], "sidecar_func_id": 0, "outcome": "resolved"}],
        "members": members,
        "panic_terminals": ["core::panicking::panic"],
        "foreign_terminals": ["alloc::alloc::{extern#0}::__rust_alloc"],
        "escaping": [
            "core::fmt::num::<impl core::fmt::Display for u32>::fmt: MIR unavailable",
            "<dyn kcrate::T as kcrate::T>::go: bodyless instance kind Virtual; vtable enumeration 1 "
            "[<kcrate::Q as kcrate::T>::go] (slot 3 of the vtables of 1 concrete type(s))",
            "kcrate::fptr: indirect call (non-const func operand of type fn(u32) -> u32); enumerated targets 0 []",
        ],
        "artifacts": None,
    }


def _synthetic_mono(fuel=64):
    """A `census:mono:` manifest: every codegen'd instance is a `<mono item>` root."""
    m = _synthetic(fuel)
    m["filter"] = "census:mono:"
    m["lowering"] = "census: extraction outcomes only; the bundle is not lowered"
    m["closed"] = False
    m["members"].append(_member(6, "core::ptr::drop_glue::<kcrate::S>#shim:DropGlue", 3))
    m["roots"] = [{"caller": "<mono item>", "callee_def_path": x["name"], "crate_decl_func_ids": [],
                   "resolved": x["name"], "sidecar_func_id": x["sidecar_func_id"], "outcome": "resolved"}
                  for x in m["members"]]
    return m


MONO_DROP = "MONO_ITEM fn std::ptr::drop_glue::<S> - shim(Some(S)) @@ k[Internal]"

MONO_BASE = [
    "MONO_ITEM fn tc::infer::<impl tc::TypeChecker<'env>>::infer_type @@ kcrate.x-cgu.0[External]",
    "MONO_ITEM fn std::vec::Vec::<Expr>::push @@ kcrate.x-cgu.0[Internal]",
    "MONO_ITEM fn hashbrown::raw::RawTableInner::new_uninitialized::<std::alloc::Global> @@ kcrate.x-cgu.0[Internal]",
    "MONO_ITEM fn tc::infer::<impl tc::TypeChecker<'env>>::infer_type::{closure#0} @@ kcrate.x-cgu.0[Internal]",
    "MONO_ITEM fn <for<'a> fn(&'a str) -> std::string::String {f} as std::ops::FnOnce<(&str,)>>::call_once - shim(for<'a> fn(&'a str) -> std::string::String {f}) @@ kcrate.x-cgu.0[Internal]",
    "MONO_ITEM fn <S as std::ops::Drop>::drop @@ kcrate.x-cgu.0[External]",
    "MONO_ITEM static TABLE @@ kcrate.x-cgu.0[External]",
]


def self_test() -> int:
    failures: list[str] = []
    arms = 0
    tmp = Path(tempfile.mkdtemp(prefix="link01-selftest-"))

    def write(name, obj):
        p = tmp / name
        p.write_text(obj if isinstance(obj, str) else json.dumps(obj))
        return str(p)

    COVER = {"bodies": [{"def_path": "tc::infer::<impl tc::TypeChecker<'env>>::infer_type"}]}

    def run(label, m1, m2, mono_lines, expect_exit, expect_in=(), mono2_lines=None, verdicts=None,
            coverage=COVER):
        nonlocal arms
        arms += 1
        m1s = m1 if isinstance(m1, list) else [m1]
        a = "+".join(write(f"{arms}-f{i}.json", m) for i, m in enumerate(m1s))
        mono = write(f"{arms}-mono.txt", "\n".join(mono_lines) + "\n")
        spec = f"crate=kcrate,manifest={a},mono={mono}"
        if coverage is not None:
            spec += f",coverage={write(f'{arms}-coverage.json', coverage)}"
        if m2 is not None:
            m2s = m2 if isinstance(m2, list) else [m2]
            spec += ",manifest2f=" + "+".join(write(f"{arms}-2f{i}.json", m) for i, m in enumerate(m2s))
        if mono2_lines is not None:
            spec += f",mono2f={write(f'{arms}-mono2.txt', chr(10).join(mono2_lines) + chr(10))}"
        rep = tmp / f"{arms}-report.json"
        import contextlib
        import io
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
            rc = main(["--case", spec, "--json", str(rep)])
        out = buf.getvalue()
        ok = rc == expect_exit and all(s in out for s in expect_in)
        if ok and verdicts is not None and rep.exists():
            c = json.loads(rep.read_text())["cases"][0]
            got = (c["link0"]["verdict"], c["link1"]["verdict"])
            ok = got == verdicts
            out += f"\n(verdicts {got})"
        if not ok:
            failures.append(f"arm {arms} {label}: exit {rc} (want {expect_exit}), want {list(expect_in)} in:\n{out[-2500:]}")

    base = _synthetic(64)
    base2 = _synthetic(128)
    # 1. baseline: every codegen'd fn instance extracts; F and 2F equal. Joins exercised: local-crate
    #    prefix, __trust_args suffix, __trust_crate prefix, visible (std::) vs def (alloc::) paths,
    #    named vs canonical lifetimes, a shim suffix, a closure, a Drop impl root. Statics excluded.
    run("baseline MET", base, base2, MONO_BASE, EXIT_OK,
        ["extracted 6/6", "LINK01=MET", "{'static': 1}"], verdicts=("MET", "MET"))
    # 2. a member dropped at 2F -> link1 NOT-MET (by name).
    m2 = _synthetic(128)
    del m2["members"][1]
    run("member dropped at 2F", base, m2, MONO_BASE, EXIT_FAIL,
        ["1 member(s) at F not at 2F", "LINK01=NOT-MET"], verdicts=("MET", "NOT-MET"))
    # 3. a member ADDED at 2F -> NOT-MET.
    m2 = _synthetic(128)
    m2["members"].append(_member(9, "kcrate::late", 1))
    run("member added at 2F", base, m2, MONO_BASE, EXIT_FAIL, ["1 member(s) at 2F not at F"], verdicts=("MET", "NOT-MET"))
    # 4. a member RENAMED at 2F: counts equal, name sets differ -> NOT-MET (names, never counts).
    m2 = _synthetic(128)
    m2["members"][5]["name"] = "<kcrate::S2 as core::ops::drop::Drop>::drop"
    run("member renamed at 2F, equal counts", base, m2, MONO_BASE, EXIT_FAIL,
        ["member(s) at 2F not at F", "members 6/6"], verdicts=("MET", "NOT-MET"))
    # 5. a block-count mismatch -> link0 RED (even for a member the join reaches).
    m1 = _synthetic(64)
    m1["members"][1]["extracted_blocks"] = 3
    run("block-count mismatch", m1, base2, MONO_BASE, EXIT_FAIL,
        ["has mir_blocks != extracted_blocks", "RED:block-drift", "LINK01=RED"], verdicts=("RED", "MET"))
    # 6. fuel_exhausted true at F -> link1 NOT-MET.
    m1 = _synthetic(64)
    m1["fuel_exhausted"] = True
    run("fuel_exhausted at F", m1, base2, MONO_BASE, EXIT_FAIL,
        ["fuel_exhausted is true at F", "the link-0 walk exhausted its fuel"], verdicts=("NOT-MET", "NOT-MET"))
    # 7. fuel_exhausted true at 2F -> link1 NOT-MET.
    m2 = _synthetic(128)
    m2["fuel_exhausted"] = True
    run("fuel_exhausted at 2F", base, m2, MONO_BASE, EXIT_FAIL, ["fuel_exhausted is true at 2F"], verdicts=("MET", "NOT-MET"))
    # 8. a refusal left unclassified -> RED.
    m1 = _synthetic(64)
    m1["escaping"].append("kcrate::odd: refused for a reason nobody has named")
    run("unclassified refusal", m1, base2, MONO_BASE, EXIT_FAIL,
        ["UNCLASSIFIED escaping row", "LINK01=RED"], verdicts=("RED", "MET"))
    # 9. a codegen'd instance the walk never reached -> NOT-MET, classified, fraction < 1.
    run("unreached item", base, base2, MONO_BASE + ["MONO_ITEM fn helper_nobody_calls @@ k[Internal]"], EXIT_FAIL,
        ["extracted 6/7", "not-reached:item"], verdicts=("NOT-MET", "MET"))
    # 10. drop glue, a drop impl, a vtable dispatch target, a MIR-unavailable refusal, a panic
    #     terminal, a promoted intrinsic, and a vtable shim are each classified.
    extra = [
        "MONO_ITEM fn std::ptr::drop_glue::<S> - shim(Some(S)) @@ k[Internal]",
        "MONO_ITEM fn <std::vec::Vec<u8> as std::ops::Drop>::drop @@ k[Internal]",
        "MONO_ITEM fn <Q as T>::go @@ k[Internal]",
        "MONO_ITEM fn core::fmt::num::imp::<impl std::fmt::Display for u32>::fmt @@ k[Internal]",
        "MONO_ITEM fn core::panicking::panic @@ k[Internal]",
        "MONO_ITEM fn std::intrinsics::cold_path @@ k[Internal]",
        "MONO_ITEM fn <S as T>::go - shim(vtable) @@ k[Internal]",
    ]
    run("classes", base, base2, MONO_BASE + extra, EXIT_FAIL,
        ["not-reached:drop-glue", "not-reached:drop-impl", "not-reached:vtable-dispatch-target",
         "refused:mir-unavailable", "terminal:panic", "refused:intrinsic", "not-reached:shim-VTable", "extracted 6/13"],
        verdicts=("NOT-MET", "MET"))
    # 11. an ambiguous join is never counted as extracted.
    m1 = _synthetic(64)
    m1["members"].append(_member(7, "alloc::other::vec::Vec::<kcrate::Expr>::push", 2))
    m2 = _synthetic(128)
    m2["members"].append(_member(7, "alloc::other::vec::Vec::<kcrate::Expr>::push", 2))
    run("ambiguous join", m1, m2, MONO_BASE, EXIT_FAIL, ["extracted-ambiguous", "extracted 5/6"], verdicts=("NOT-MET", "MET"))
    # 12. fuel not doubled -> REFUSED (not the measurement asked for).
    m2 = _synthetic(96)
    run("fuel not doubled", base, m2, MONO_BASE, EXIT_REFUSED, ["needs fuel F and 2F", "LINK01=REFUSED"])
    # 13. a substring filter that leaves a crate body out -> both links NOT-MET (measured against the
    #     crate module's own body list, never read off the filter's spelling).
    m1 = _synthetic(64)
    m1["filter"] = "local:infer_type"
    m2 = _synthetic(128)
    m2["filter"] = "local:infer_type"
    cover2 = {"bodies": COVER["bodies"] + [{"def_path": "env::register_prelude"}]}
    run("not all roots", m1, m2, MONO_BASE, EXIT_FAIL, ["matched by no piece's filter (not ALL roots)"],
        verdicts=("NOT-MET", "NOT-MET"), coverage=cover2)
    # 14. a v2 manifest (no fuel fields) -> REFUSED.
    m1 = _synthetic(64)
    m1["schema"] = "trust-ir-callee-sidecar-v2"
    del m1["fuel"], m1["fuel_exhausted"]
    run("schema v2", m1, base2, MONO_BASE, EXIT_REFUSED, ["need trust-ir-callee-sidecar-v3"])
    # 15. truncated manifest JSON -> REFUSED.
    run("truncated manifest", json.dumps(base)[:-40], base2, MONO_BASE, EXIT_REFUSED, ["not JSON"])
    # 16. no mono items -> REFUSED (the denominator is missing, never 0/0 = green).
    run("empty mono list", base, base2, ["some unrelated line"], EXIT_REFUSED, ["no `MONO_ITEM fn` line"])
    # 17. a mir_digest that moved at 2F -> NOT-MET (the extraction is not deterministic).
    m2 = _synthetic(128)
    m2["members"][2]["mir_digest"] = "sha256:" + "f" * 64
    run("digest moved at 2F", base, m2, MONO_BASE, EXIT_FAIL, ["different mir_digest"], verdicts=("MET", "NOT-MET"))
    # 18. the codegen'd set differs between the two compiles -> link1 NOT-MET.
    run("codegen set moved", base, base2, MONO_BASE, EXIT_FAIL, ["codegen'd instance set differs"],
        mono2_lines=MONO_BASE[:-2], verdicts=("MET", "NOT-MET"))
    # 19. no 2F manifest -> link1 NOT-MEASURED, overall REFUSED (never green).
    run("no 2F manifest", base, None, MONO_BASE, EXIT_REFUSED, ["link1 NOT-MEASURED"])
    # 20. a mono line with no partition field -> REFUSED.
    run("malformed mono line", base, base2, MONO_BASE + ["MONO_ITEM fn broken"], EXIT_REFUSED, ["without ' @@'"])
    # 21. root rows changed at 2F -> NOT-MET.
    m2 = _synthetic(128)
    m2["roots"][0]["outcome"] = "refused: local root still requires monomorphization"
    run("roots moved at 2F", base, m2, MONO_BASE, EXIT_FAIL, ["root rows differ"], verdicts=("MET", "NOT-MET"))
    # 22. `local:` whose root rows miss a body the crate module has -> NOT-MET (the ledger is not all).
    run("local: roots miss a coverage body", base, base2, MONO_BASE, EXIT_FAIL,
        ["local roots are not the coverage bodies its filter selects"], verdicts=("NOT-MET", "NOT-MET"),
        coverage=cover2)
    # 23. two PIECES covering every body: link 0 on the union, link 1 per piece -> MET.
    def piece(fuel, sub, keep, root_path):
        m = _synthetic(fuel)
        m["filter"] = "local:" + sub
        m["members"] = [x for x in m["members"] if x["sidecar_func_id"] in keep]
        m["roots"] = [{"caller": "<local root>", "callee_def_path": root_path, "crate_decl_func_ids": [],
                       "resolved": None, "sidecar_func_id": None, "outcome": "resolved"}]
        return m
    rp_a, rp_b = COVER["bodies"][0]["def_path"], "env::register_prelude"
    pa, pb = piece(64, "tc::", {0, 1, 2, 3}, rp_a), piece(64, "env::", {1, 4, 5}, rp_b)
    pa2, pb2 = piece(128, "tc::", {0, 1, 2, 3}, rp_a), piece(128, "env::", {1, 4, 5}, rp_b)
    run("pieces MET", [pa, pb], [pa2, pb2], MONO_BASE, EXIT_OK, ["extracted 6/6", "piece 'local:env::'"],
        verdicts=("MET", "MET"), coverage=cover2)
    # 23b. `|`-alternation pieces (seal-ph3): `local:tc::|nothing::` and `local:|env::|` (empty
    #      alternatives dropped) cover the two bodies; a third body neither selects is caught.
    pa_alt = piece(64, "tc::|nothing::", {0, 1, 2, 3}, rp_a)
    pb_alt = piece(64, "|env::|", {1, 4, 5}, rp_b)
    pa2_alt = piece(128, "tc::|nothing::", {0, 1, 2, 3}, rp_a)
    pb2_alt = piece(128, "|env::|", {1, 4, 5}, rp_b)
    run("alternation pieces MET", [pa_alt, pb_alt], [pa2_alt, pb2_alt], MONO_BASE, EXIT_OK, ["extracted 6/6"],
        verdicts=("MET", "MET"), coverage=cover2)
    cover3 = {"bodies": cover2["bodies"] + [{"def_path": "cert::check"}]}
    run("alternation pieces leave a body out", [pa_alt, pb_alt], [pa2_alt, pb2_alt], MONO_BASE, EXIT_FAIL,
        ["1 crate body/bodies matched by no piece's filter"], verdicts=("NOT-MET", "NOT-MET"), coverage=cover3)
    # 24. pieces that disagree on a shared member's digest -> link0 RED.
    pb_bad = piece(64, "env::", {1, 4, 5}, rp_b)
    pb_bad["members"][0]["mir_digest"] = "sha256:" + "e" * 64
    run("pieces disagree on a shared member", [pa, pb_bad], [pa2, pb2], MONO_BASE, EXIT_FAIL,
        ["differs between pieces"], coverage=cover2)
    # 25. pieces without coverage= cannot claim ALL roots -> NOT-MET.
    run("pieces without coverage", [pa, pb], [pa2, pb2], MONO_BASE, EXIT_FAIL,
        ["need coverage= to prove they cover ALL roots"], verdicts=("NOT-MET", "NOT-MET"), coverage=None)
    # 26. one piece exhausted at 2F -> link1 NOT-MET although the other is clean.
    pb2x = piece(128, "env::", {1, 4, 5}, rp_b)
    pb2x["fuel_exhausted"] = True
    run("one piece exhausted", [pa, pb], [pa2, pb2x], MONO_BASE, EXIT_FAIL,
        ["fuel_exhausted is true at 2F (fuel 128, filter 'local:env::')"], verdicts=("MET", "NOT-MET"), coverage=cover2)
    # 27. a namesake is never borrowed: `b::Error::new` normalizes (level 2) onto the member that is
    #     `a::Error::new`'s unique level-1 image, so it is NOT extracted; and two codegen'd items on
    #     one level-2 key with one member are both ambiguous.
    m1 = _synthetic(64)
    m1["members"].append(_member(8, "kcrate::a::Error::new", 1))
    m2 = _synthetic(128)
    m2["members"].append(_member(8, "kcrate::a::Error::new", 1))
    run("namesake not borrowed", m1, m2, MONO_BASE + ["MONO_ITEM fn a::Error::new @@ k[External]",
                                                     "MONO_ITEM fn b::Error::new @@ k[External]"],
        EXIT_FAIL, ["extracted 7/8", "not-reached:item"], verdicts=("NOT-MET", "MET"))
    m1 = _synthetic(64)
    m1["members"].append(_member(8, "alloc::x::Thing::go", 1))
    m2 = _synthetic(128)
    m2["members"].append(_member(8, "alloc::x::Thing::go", 1))
    run("two items on one level-2 key", m1, m2, MONO_BASE + ["MONO_ITEM fn std::x::Thing::go @@ k[Internal]",
                                                            "MONO_ITEM fn core::y::Thing::go @@ k[Internal]"],
        EXIT_FAIL, ["extracted 6/8", "extracted-ambiguous"], verdicts=("NOT-MET", "MET"))
    # 27b. two codegen'd items that PRINT identically (a closure of a generic parent instantiated
    #      twice renders its closure type without its args) and one member: neither is extracted,
    #      because a member cannot be the image of two items.
    m1 = _synthetic(64)
    m1["members"].append(_member(8, "kcrate::x::f::{closure#0}", 1))
    m2 = _synthetic(128)
    m2["members"].append(_member(8, "kcrate::x::f::{closure#0}", 1))
    run("two items print alike, one member", m1, m2,
        MONO_BASE + ["MONO_ITEM fn x::f::{closure#0} @@ k[Internal]", "MONO_ITEM fn x::f::{closure#0} @@ k[Internal]"],
        EXIT_FAIL, ["extracted 6/8", "extracted-ambiguous"], verdicts=("NOT-MET", "MET"))
    # 28. one codegen'd instance walked under two `__trust_args` identities is its own class,
    #     never counted as extracted.
    m1 = _synthetic(64)
    m1["members"].append(_member(8, "alloc::x::Thing::go::<__trust_args@aa01>", 1))
    m1["members"].append(_member(9, "alloc::x::Thing::go::<__trust_args@bb02>", 1))
    m2 = _synthetic(128)
    m2["members"] += [dict(x) for x in m1["members"][-2:]]
    run("fingerprint duplicate", m1, m2, MONO_BASE + ["MONO_ITEM fn std::x::Thing::go @@ k[Internal]"],
        EXIT_FAIL, ["extracted 6/7", "extracted-fingerprint-dup"], verdicts=("NOT-MET", "MET"))
    # MONO-ROOTED LINK 0 (seal-ph3 `census:mono:`), with link 1 from `census:local:` at F and 2F.
    def run_mono(label, l0, mono_lines, expect_exit, expect_in=(), verdicts=None, f=None, f2=None):
        nonlocal arms
        arms += 1
        spec = f"crate=kcrate,link0manifest={write(f'{arms}-l0.json', l0)},mono={write(f'{arms}-mono.txt', chr(10).join(mono_lines) + chr(10))}"
        spec += f",coverage={write(f'{arms}-coverage.json', COVER)}"
        if f is not None:
            spec += f",manifest={write(f'{arms}-f.json', f)}"
        if f2 is not None:
            spec += f",manifest2f={write(f'{arms}-2f.json', f2)}"
        rep = tmp / f"{arms}-report.json"
        import contextlib
        import io
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
            rc = main(["--case", spec, "--json", str(rep)])
        out = buf.getvalue()
        ok = rc == expect_exit and all(x in out for x in expect_in)
        if ok and verdicts is not None and rep.exists():
            c = json.loads(rep.read_text())["cases"][0]
            ok = (c["link0"]["verdict"], c["link1"]["verdict"]) == verdicts
            out += f"\n(verdicts {(c['link0']['verdict'], c['link1']['verdict'])})"
        if not ok:
            failures.append(f"arm {arms} {label}: exit {rc} (want {expect_exit}), want {list(expect_in)} in:\n{out[-2500:]}")

    cl1, cl2 = _synthetic(64), _synthetic(128)
    cl1["filter"] = cl2["filter"] = "census:local:"
    mono7 = MONO_BASE + [MONO_DROP]
    # M0. the configuration label is echoed per case (one case per K).
    arms += 1
    import contextlib
    import io
    _buf = io.StringIO()
    _spec = (f"crate=kcrate,k=O0c16,link0manifest={write('k-l0.json', _synthetic_mono())},"
             f"mono={write('k-mono.txt', chr(10).join(MONO_BASE + [MONO_DROP]) + chr(10))}")
    with contextlib.redirect_stdout(_buf), contextlib.redirect_stderr(_buf):
        _rc = main(["--case", _spec])
    if "LINK01 crate=kcrate k=O0c16 link0=MET" not in _buf.getvalue() or "[K O0c16]" not in _buf.getvalue():
        failures.append(f"arm {arms} K label not echoed:\n{_buf.getvalue()[-800:]}")
    # M1. every codegen'd instance -- drop glue included -- is a root and extracts: link 0 MET, and
    #     the census:local: pair gives link 1 MET.
    run_mono("mono all extract", _synthetic_mono(), mono7, EXIT_OK,
             ["extracted 7/7", "7 `<mono item>` roots vs 7 MONO_ITEM fn lines", "LINK01=MET"],
             verdicts=("MET", "MET"), f=cl1, f2=cl2)
    # M2. a rooted instance refused by kind is classified, not extracted.
    mm = _synthetic_mono()
    mm["members"] = [x for x in mm["members"] if x["sidecar_func_id"] != 1]
    mm["escaping"].append("alloc::vec::Vec::<kcrate::Expr>::push: MIR unavailable")
    run_mono("mono refused root", mm, mono7, EXIT_REFUSED, ["refused:mir-unavailable", "extracted 6/7"],
             verdicts=("NOT-MET", "NOT-MEASURED"))
    # M3. a root with no member, no escaping row and no terminal is UNACCOUNTED -> RED.
    mm = _synthetic_mono()
    mm["members"] = [x for x in mm["members"] if x["sidecar_func_id"] != 1]
    run_mono("mono unaccounted root", mm, mono7, EXIT_FAIL, ["UNACCOUNTED", "LINK01=RED"])
    # M4. rustc codegens an instance the sidecar did not root -> NOT-MET (count cross-check).
    run_mono("mono root missing", _synthetic_mono(), mono7 + ["MONO_ITEM fn extra_fn @@ k[Internal]"], EXIT_REFUSED,
             ["7 `<mono item>` roots against 8 `MONO_ITEM fn` lines"], verdicts=("NOT-MET", "NOT-MEASURED"))
    # M5. one instance rooted twice -> RED.
    mm = _synthetic_mono()
    mm["roots"].append(dict(mm["roots"][0], sidecar_func_id=99))
    run_mono("mono duplicate root", mm, mono7, EXIT_FAIL, ["name one instance twice"])
    # M6. a rooted member whose block counts differ -> RED.
    mm = _synthetic_mono()
    mm["members"][6]["extracted_blocks"] = 2
    run_mono("mono block drift", mm, mono7, EXIT_FAIL, ["RED:block-drift", "LINK01=RED"])
    # M7. link 1 compares census:local: F and 2F; a census:local: F against a local: 2F is not one
    #     measurement -> REFUSED.
    cl2b = _synthetic(128)
    run_mono("census filter mismatch", _synthetic_mono(), mono7, EXIT_REFUSED, ["compares two filters"], f=cl1, f2=cl2b)
    # M8. a census:mono: run cannot stand in for link 1 (its roots are not the crate's bodies).
    mm1, mm2 = _synthetic_mono(64), _synthetic_mono(128)
    run_mono("mono manifests offered for link 1", _synthetic_mono(), mono7, EXIT_FAIL,
             ["is not a `local:` filter"], verdicts=("MET", "NOT-MET"), f=mm1, f2=mm2)
    # 28b. the normalizers themselves: a module prefix is stripped, a closure's parent fn is not.
    arms += 1
    if norm2("alloc::vec::Vec::<u8>::push", "k") != norm2("std::vec::Vec::<u8>::push", "k") \
            or norm2("a::f::{closure#0}", "k") == norm2("a::g::{closure#0}", "k") \
            or norm2("k::m::gen::<u32>", "k") != "gen::<u32>":
        failures.append(f"arm {arms} normalizer: module stripping wrong")
    # 29. an escaping row whose name contains ': ' (a closure span) is still attributed whole.
    arms += 1
    cls, name = classify_escaping("f::<{closure@src/a.rs:1:2: 3:4}>: MIR unavailable")
    if (cls, name) != ("mir-unavailable", "f::<{closure@src/a.rs:1:2: 3:4}>"):
        failures.append(f"arm {arms} escaping attribution: got {(cls, name)}")

    for f in failures:
        print(f"SELF-TEST FAIL {f}", file=sys.stderr)
    status = "FAIL" if failures else "OK"
    print(f"crystal_link01_census self-test {status}: arms={arms} failed={len(failures)}")
    return EXIT_FAIL if failures else EXIT_OK


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
