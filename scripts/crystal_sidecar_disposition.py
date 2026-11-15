#!/usr/bin/env python3
"""What does the DERIVED callee bundle itself say about every edge that escapes it?

    scripts/crystal_sidecar_disposition.py <dump_dir> <out.json> [--census=<lowering_census.json>]
        [--record=<partial_bundle.json>] [--expect=absent=N,call_indirect=N,dropped=N] [KEY=VALUE ...]
    scripts/crystal_sidecar_disposition.py --self-test | --pinned-inputs

WHY THIS EXISTS.  Link 3 of the infer_type goal ("the escaping edges close") is red
because the sidecar publishes `closed` from a WALK over a leaf model, while the
lowered trust-ir module it holds already states the real per-site disposition:
every call whose body is not in the bundle is lowered as a typed obligation
reading `[trust-absent-callee-assumption] call to absent callee `NAME` (...)`,
every call with no static target is a `call_indirect` instruction, and every
member the retry could not lower is simply not a function of the module.  The
open ledger of link 3 is therefore DERIVABLE from the module plus its manifest,
without a walk and without a compiler rebuild.  This script is the first step of
that design: prove the instrument on the EXISTING artifact.

WHAT IT ANSWERS.  Over `<dump>/callees/<crate>.callees.trust-ir.txt` and the
manifest beside it:

    (a) how many absent-callee obligation rows there are, grouped by callee;
    (b) how many `call_indirect` instructions the module carries, and where;
    (c) which manifest members are DROPPED -- named by the manifest but bodyless
        in the module -- and how many;
    (d) what each absent callee IS: a dropped member, a primitive/intrinsic, a
        shim, a no-MIR body, an extern symbol, a virtual (dyn) call, or an
        indirect call through a fn pointer that the bridge spelled as an absent
        callee named by its pointer TYPE;
    (e) the identity  absent_rows == sum over classes.

The classification authority is the manifest's own `escaping` reasons and member
set; name SHAPE is a recorded cross-check, never the authority, except for the
fn-pointer class where the shape is confirmed against the enclosing function's
own manifest `indirect call` row.

WHAT THE VERDICT MEANS.  `disposition: derived` says the module's every escaping
site is enumerated, parsed and placed in exactly one named class, and that the
counts reconcile with the manifest (members = lowered + dropped; manifest
indirect rows in lowered members = call_indirect + fn-pointer absent rows).

WHAT IT DOES NOT MEAN.  It does NOT say the closure is closed -- it is not, and
this is the ledger of exactly how open it is.  It does NOT say any class is
dischargeable.  It does NOT attribute a dropped member to one of the lowering
census's refusal families: that census is aggregate-only and names no member,
so the per-member `family` here is `unattributed` and `family_hint` is derived
from the member's OWN escaping calls (an atomic intrinsic present or not) and
is labelled a hint.  And it says nothing about whether any lowered body is
correct: that is links 4-5, per chain, elsewhere.

FAIL-CLOSED.  The script refuses (exit 1, `disposition: refused`, and no zero
minted) rather than emit a number when: the text header is not the format it
was written against; an `fn @` header, an `obligation` row, or an
absent-callee description does not parse against the exact grammar recorded
in this file; a manifest `escaping` row carries a reason it does not know; the
module's function order is not the manifest's lowered order (which is what
makes `function N` resolvable); an obligation names a function index the
module does not have; any absent callee lands in `unknown`; any
reconciliation identity fails; a `--record` pin (sha256 of text, binary,
manifest; member counts) or a `--census` count disagrees; or an `--expect`
figure disagrees.  Usage errors exit 2.

Provenance KEY=VALUE pairs are recorded verbatim, the same contract
`crystal_sidecar_closure.py` and `crystal_a0_census.py` use.

MANIFEST SCHEMAS.  v1, v2 and v3 are read, keyed on the manifest's own `schema`
field (`read_manifest_schema`).  v2 and v3 carry `foreign_terminals`, which is
then REQUIRED; v3 (trust callee_sidecar.rs, 2026-09-24) adds a `bb` on every
call row, a `mir_digest` on every member and the top-level `fuel` /
`fuel_exhausted`, and a manifest that claims v3 without them, or with one
malformed, refuses.  This instrument validates the v3 fields and reads none of
them.  `--self-test` drives that function in both polarities.
"""

import collections
import hashlib
import json
import re
import sys
from pathlib import Path

if str(Path(__file__).resolve().parent) not in sys.path:
    sys.path.insert(0, str(Path(__file__).resolve().parent))
# The ONE reader of trust-ir's definition-site symbols (M2, 2026-09-27): trust-ir WS4.3 prints a
# non-bare name QUOTED; the reader decodes it, refuses what the printer cannot write, and holds
# the module to one grammar, so a function is joined to its manifest member by its NAME.
import crystal_trust_ir_symbols as tir_symbols  # noqa: E402

# Read by check_gate_registry.py (PINNED_INPUTS_MARKER): `--pinned-inputs` prints the first-party
# modules this script executes besides itself (derived from its imports).
ANSWERS_PINNED_INPUTS = True

HEADER = "; TrustIr text format v1"
MODULE = re.compile(r'^module "(?P<name>[^"]*)"$')
BLOCK = re.compile(r"^bb\d+(\(.*\))?:$")
OBLIGATION = re.compile(
    r'^obligation (?P<id>\d+) (?P<kind>\S+) (?P<status>\S+) '
    r'"(?P<desc>(?:[^"\\]|\\.)*)" function (?P<func>\d+) formula "(?P<schema>[^"]*)" '
)
ABSENT_PREFIX = "[trust-absent-callee-assumption] call to absent callee `"
ABSENT = re.compile(
    r"^\[trust-absent-callee-assumption\] call to absent callee `(?P<callee>[^`]*)` "
    r"\((?P<why>body not in the lowered bundle|dynamic dispatch on receiver `[^`]*`: [^)]*)\) may panic$"
)
INDIRECT = re.compile(r"\bcall_indirect\b")
ESCAPING = re.compile(
    r"^(?P<name>.*?): (?:(?:non-Item|bodyless) instance kind (?P<kind>Intrinsic|Shim|Virtual)"
    r"|(?P<nomir>MIR unavailable)"
    # v2: a FOREIGN item -- declared in an `extern` block, proved by `tcx.is_foreign_item`
    # rather than read off the name. This is the reason `{extern#` used to be inferred from
    # below, and inferring it was a standing violation of this file's own rule that a name
    # shape is a cross-check and never the authority.
    r"|(?P<foreign>foreign item \(no Rust body on this target\))"
    # The indirect row gained a trailing `; enumerated targets N [..]` clause in the
    # 2026-09-21 producer. It is INFORMATION on the same verdict, so the pattern is opened
    # at the tail rather than pinned to the old spelling.
    r"|(?P<indirect>indirect call \(non-const func operand of type .*))$",
    re.S,
)
# Two producer spellings of the same refusal: `non-Item instance kind X` (the
# 2026-09-16 producer, which refused every non-Item kind by name) and `bodyless
# instance kind X` (2026-09-20, after shims are admitted and only Intrinsic and
# Virtual -- the kinds `instance_mir` has no body for -- are refused).
INTRINSIC_TERMINAL_CLASS = "intrinsic-terminal: "
INDIRECT_CALL_CLASS = "escaping: indirect call ("
FNPTR_TYPE = re.compile(r"^(for<[^>]*> )?fn\(")

CLASSES = (
    "dropped-member",
    "primitive",
    "shim",
    "no-mir",
    "extern",
    "virtual",
    "indirect-fnptr",
    "unknown",
)


MANIFEST_V1 = "trust-ir-callee-sidecar-v1"
MANIFEST_V2 = "trust-ir-callee-sidecar-v2"
MANIFEST_V3 = "trust-ir-callee-sidecar-v3"
MANIFEST_SCHEMAS = (MANIFEST_V1, MANIFEST_V2, MANIFEST_V3)
# `ProofDigest`'s display form; the all-zero digest is Trust's "no digest" value (and the
# placeholder its own layout fixture carries), so it is refused as a member's digest.
MIR_DIGEST = re.compile(r"^sha256:[0-9a-f]{64}$")
ZERO_MIR_DIGEST = "sha256:" + "0" * 64


class Refuse(Exception):
    """A fail-closed condition: the input is not what this instrument was written against."""


def check_v3_fields(manifest):
    """Refuse a manifest that claims v3 without its v3 fields, well formed.  `type(x) is
    int`, not isinstance: a JSON `true` is a Python bool, which IS an int.  A member's calls
    are one per MIR block in block order, so their `bb`s strictly increase and each is below
    the member's `mir_blocks`."""
    if type(manifest.get("fuel")) is not int or manifest["fuel"] < 1:
        raise Refuse("v3 manifest has no well-typed `fuel` (the member cap in effect)")
    if type(manifest.get("fuel_exhausted")) is not bool:
        raise Refuse("v3 manifest has no well-typed `fuel_exhausted`")
    if manifest["fuel_exhausted"] and manifest.get("closed") is True:
        raise Refuse("v3 manifest says `closed` with its member fuel exhausted: contradictory")
    members = manifest.get("members")
    if not isinstance(members, list):
        raise Refuse("v3 manifest `members` is not a list")
    for k, member in enumerate(members):
        if not isinstance(member, dict) or not isinstance(member.get("calls"), list):
            raise Refuse(f"v3 manifest member #{k} is not an object with a `calls` list")
        digest = member.get("mir_digest")
        if not (isinstance(digest, str) and MIR_DIGEST.match(digest) and digest != ZERO_MIR_DIGEST):
            raise Refuse(f"v3 manifest member #{k} has no well-formed `mir_digest` "
                         f"(sha256:<64 hex>, non-zero): {digest!r}")
        n_blocks = member.get("mir_blocks")
        if type(n_blocks) is not int:
            raise Refuse(f"v3 manifest member #{k} has no `mir_blocks` to bound its call bbs")
        prev = -1
        for j, call in enumerate(member["calls"]):
            bb = call.get("bb") if isinstance(call, dict) else None
            if not (type(bb) is int and prev < bb < n_blocks):
                raise Refuse(f"v3 manifest member #{k} call {j} has no `bb` in ({prev}, {n_blocks}): {bb!r}")
            prev = bb


def read_manifest_schema(manifest):
    """Validate the manifest's schema-keyed fields; return its FOREIGN terminal set, or None
    under v1.

    v2 records the FOREIGN boundary as a producer fact (`tcx.is_foreign_item`); v3 keeps
    it.  v1 cannot, and the difference is not cosmetic: under v1 an absent
    `foreign_terminals` is indistinguishable from "this closure has no foreign boundary",
    which is the wrong reading to make silently.  So `foreign` is None under v1 ONLY and the
    `extern` class falls back to the name shape WITH that caveat recorded in its
    cross-check note; a v3 manifest never takes that fallback."""
    schema = manifest.get("schema")
    if schema not in MANIFEST_SCHEMAS:
        raise Refuse(f"manifest schema is {schema!r}, not one of {', '.join(MANIFEST_SCHEMAS)}")
    foreign = None
    if schema != MANIFEST_V1:
        ft = manifest.get("foreign_terminals")
        if not isinstance(ft, list) or any(not isinstance(x, str) for x in ft):
            raise Refuse(f"{schema} manifest has no well-formed `foreign_terminals` list")
        foreign = frozenset(ft)
    if schema == MANIFEST_V3:
        check_v3_fields(manifest)
    return foreign


def sha256_of(path):
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_module(text):
    """Return (module_name, functions, obligations, call_indirect_sites).

    `functions` is a list of {name, functy, instruction_bearing} in text order --
    the dense numbering `function N` on an obligation row addresses.  Every `fn @`
    row must close with a bare `}`; a row that does not parse refuses.
    """
    lines = text.split("\n")
    if not lines or lines[0] != HEADER:
        raise Refuse(f"text header is {lines[0][:60]!r}, not {HEADER!r}")
    module_name = None
    functions, obligations, indirect = [], [], []
    cur = None
    syms = tir_symbols.ModuleSymbols(tir_symbols.RUSTCC_PREFIX)
    for lineno, line in enumerate(lines, 1):
        if line.startswith("fn @") or line.startswith("rustcc fn @"):
            if cur is not None:
                raise Refuse(f"line {lineno}: fn header inside an unclosed fn block")
            try:
                fh = syms.fn_header(line, f"line {lineno}")
            except tir_symbols.SymbolRefusal as exc:
                raise Refuse(f"line {lineno}: fn header does not parse: {exc}") from exc
            if fh is None:
                raise Refuse(f"line {lineno}: fn header does not parse: {line[:120]!r}")
            functions.append({"name": fh[0], "functy": fh[1], "instruction_bearing": False})
            cur = len(functions) - 1
            continue
        if cur is not None:
            if line == "}":
                cur = None
                continue
            stripped = line.strip()
            if INDIRECT.search(stripped) and not stripped.startswith(";"):
                indirect.append({"line": lineno, "function": cur, "in": functions[cur]["name"],
                                 "text": stripped})
            if stripped and not stripped.startswith(";") and not BLOCK.match(stripped):
                functions[cur]["instruction_bearing"] = True
            continue
        if line.startswith("obligation "):
            matched = OBLIGATION.match(line)
            if not matched:
                raise Refuse(f"line {lineno}: obligation row does not parse: {line[:160]!r}")
            obligations.append({"line": lineno, "id": int(matched.group("id")), "kind": matched.group("kind"),
                                "status": matched.group("status"), "desc": matched.group("desc"),
                                "function": int(matched.group("func"))})
            continue
        if module_name is None:
            matched = MODULE.match(line)
            if matched:
                module_name = matched.group("name")
    if cur is not None:
        raise Refuse("text ends inside an unclosed fn block")
    if module_name is None:
        raise Refuse("no `module \"...\"` row in the text")
    if not functions:
        raise Refuse("no fn rows in the text")
    if not obligations:
        raise Refuse("no obligation rows in the text")
    return module_name, functions, obligations, indirect


def absent_rows(obligations, functions):
    """Every `[trust-absent-callee-assumption]` obligation, parsed to (callee, why, function)."""
    rows = []
    for ob in obligations:
        desc = ob["desc"]
        if not desc.startswith("[trust-absent-callee-assumption]"):
            continue
        matched = ABSENT.match(desc)
        if not matched:
            raise Refuse(f"obligation {ob['id']}: absent-callee description does not parse: {desc[:200]!r}")
        if ob["function"] >= len(functions):
            raise Refuse(f"obligation {ob['id']} names function {ob['function']}; the module has {len(functions)}")
        why = matched.group("why")
        rows.append({"id": ob["id"], "callee": matched.group("callee"),
                     "shape": "dynamic-dispatch" if why.startswith("dynamic dispatch") else "body-absent",
                     "function": ob["function"]})
    return rows


def parse_escaping(manifest):
    """Manifest `escaping` rows -> {callee_name: reason-kind} and {caller_name: n_indirect_rows}.

    For the `indirect call` reason the row's name is the CALLER (the site has no
    callee), so those go to a separate map.  A reason this file does not know refuses.
    """
    by_callee, indirect_callers = {}, collections.Counter()
    for row in manifest.get("escaping", []):
        if not isinstance(row, str):
            raise Refuse(f"escaping row is not a string: {row!r}"[:200])
        matched = ESCAPING.match(row)
        if not matched:
            raise Refuse(f"escaping row carries a reason this instrument does not know: {row[:200]!r}")
        if matched.group("indirect"):
            indirect_callers[matched.group("name")] += 1
            continue
        kind = matched.group("kind") or ("foreign" if matched.group("foreign") else "MIR unavailable")
        name = matched.group("name")
        if name in by_callee and by_callee[name] != kind:
            raise Refuse(f"escaping callee {name[:100]!r} carries two reasons: {by_callee[name]} / {kind}")
        by_callee[name] = kind
    return by_callee, indirect_callers


def classify(callee, row_function, functions, dropped, escaping, members_by_name,
             terminals=frozenset(), foreign=None):
    """One absent callee -> (class, cross-check note).  Authority order is deliberate:
    the member set first (a dropped member IS in the manifest by name), then the
    manifest's own escaping reason, then the fn-pointer shape confirmed against the
    enclosing function's manifest row.  Anything else is `unknown`."""
    if callee in dropped:
        return "dropped-member", None
    # A RECORDED TERMINAL is a callee the bundle deliberately does not carry a
    # body for, because something else supplies its semantics -- the producer
    # earns that class per callee and records it, and the reason it is checked
    # HERE rather than trusted is that a terminal is exactly the shape a wrong
    # promotion would hide in. An intrinsic terminal must still be named
    # `core::intrinsics::*`; anything else carrying the class is reported.
    if callee in terminals:
        if callee.startswith("core::intrinsics::"):
            return "primitive", None
        return "primitive", "recorded a TERMINAL but not named core::intrinsics::*"
    reason = escaping.get(callee)
    if reason == "Intrinsic":
        return "primitive", None if callee.startswith("core::intrinsics::") else "name is not core::intrinsics::*"
    if reason == "Shim":
        return "shim", None
    if reason == "Virtual":
        return "virtual", None if callee.startswith("<dyn ") else "name is not <dyn ...>"
    # A PROMOTED FOREIGN TERMINAL (manifest v2 `foreign_terminals`). The authority is the
    # producer's `tcx.is_foreign_item` query; the `{extern#` name shape is the cross-check,
    # reported when the two disagree rather than silently preferred either way.
    if foreign is not None and callee in foreign:
        return "extern", None if "{extern#" in callee else "recorded FOREIGN but the name carries no {extern#} segment"
    if reason == "foreign":
        return "extern", None if "{extern#" in callee else "escaping-as-foreign but the name carries no {extern#} segment"
    if reason == "MIR unavailable":
        if foreign is not None:
            # v2 producer: a foreign item can no longer reach this arm, so a `{extern#`
            # name here is a cross-check FAILURE, not a classification shortcut. Under v1
            # the shape was all there was, and that is recorded in the verdict.
            return "no-mir", "name carries {extern#} but the v2 producer did not record it foreign" if "{extern#" in callee else None
        if "{extern#" in callee:
            return "extern", "v1 manifest: class inferred from the NAME SHAPE, not from a producer query"
        return "no-mir", None
    if FNPTR_TYPE.match(callee):
        caller = functions[row_function]["name"]
        member = members_by_name.get(caller)
        has_indirect = member is not None and any(
            c.get("class", "").startswith(INDIRECT_CALL_CLASS) for c in member.get("calls", []))
        if has_indirect:
            return "indirect-fnptr", None
        return "unknown", "fn-pointer-shaped callee but the enclosing function has no manifest indirect-call row"
    return "unknown", "not a member, not an escaping callee, not fn-pointer-shaped"


def family_hint(member):
    """Aggregate-only census => per-member family is UNKNOWN; this is the one hint the
    manifest can give: does the member's own escaping call list contain an atomic
    intrinsic (the census's family A)?  Labelled a hint everywhere it is printed."""
    for call in member.get("calls", []):
        if call.get("class", "").startswith("escaping") and "core::intrinsics::atomic_" in call.get("resolved", ""):
            return "A:atomic-intrinsic-in-own-calls"
    return None


def parse_kv(argv):
    opts, provenance = {}, {}
    for arg in argv:
        if arg.startswith("--"):
            key, _, value = arg[2:].partition("=")
            if key not in ("census", "record", "expect") or not value:
                raise SystemExit(f"unknown or empty option {arg!r}")
            opts[key] = value
        elif "=" in arg:
            key, value = arg.split("=", 1)
            provenance[key] = value
        else:
            raise SystemExit(f"argument {arg!r} is neither --option=value nor KEY=VALUE")
    return opts, provenance


def parse_expect(spec):
    expect = {}
    for item in spec.split(","):
        key, _, value = item.partition("=")
        if key not in ("absent", "call_indirect", "dropped") or not value.isdigit():
            raise SystemExit(f"--expect item {item!r} is not absent=N|call_indirect=N|dropped=N")
        expect[key] = int(value)
    return expect


def run(dump, out, opts, provenance):
    crate_text = next(iter(sorted(dump.glob("*.trust-ir.txt"))), None)
    if crate_text is None:
        raise Refuse(f"no <crate>.trust-ir.txt in {dump}")
    crate_name = crate_text.name[: -len(".trust-ir.txt")]
    callees = dump / "callees"
    text_path = callees / f"{crate_name}.callees.trust-ir.txt"
    bin_path = callees / f"{crate_name}.callees.trust-ir.bin"
    manifest_path = callees / f"{crate_name}.callees.manifest.json"
    for path in (text_path, bin_path, manifest_path):
        if not path.exists():
            raise Refuse(f"sidecar artifact missing: {path}")

    module_name, functions, obligations, indirect_sites = parse_module(text_path.read_text(encoding="utf-8"))
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    foreign = read_manifest_schema(manifest)
    members = manifest.get("members", [])
    names = [m.get("name") for m in members]
    if len(set(names)) != len(names) or any(n is None for n in names):
        raise Refuse("manifest member names are not unique / not all present")
    members_by_name = {m["name"]: m for m in members}

    bodyful = {f["name"] for f in functions if f["instruction_bearing"]}
    bodyless_in_text = [f["name"] for f in functions if not f["instruction_bearing"]]
    not_members = [f["name"] for f in functions if f["name"] not in members_by_name]
    if not_members:
        raise Refuse(f"{len(not_members)} module function(s) are not manifest members, e.g. {not_members[0][:120]!r}")
    lowered_in_manifest_order = [n for n in names if n in {f["name"] for f in functions}]
    if lowered_in_manifest_order != [f["name"] for f in functions]:
        raise Refuse("module function order is not the manifest's lowered order; `function N` is not resolvable")
    dropped = [m for m in members if m["name"] not in bodyful]
    dropped_names = {m["name"] for m in dropped}
    if len(members) != len(bodyful) + len(dropped):
        raise Refuse("members != bodyful + dropped (a name is both?)")

    escaping, indirect_callers = parse_escaping(manifest)
    # THE INTRINSIC-TERMINAL SET, derived from the members' own call rows rather
    # than from a flat list: the producer awards the class PER CALL SITE (edge
    # class `intrinsic-terminal: <callee>`), having earned it from that site's
    # member lowering, so per-site is the granularity at which it is true.
    terminals = frozenset(
        c["class"][len(INTRINSIC_TERMINAL_CLASS):].strip()
        for m in manifest.get("members", [])
        for c in m.get("calls", [])
        if isinstance(c.get("class"), str) and c["class"].startswith(INTRINSIC_TERMINAL_CLASS)
    )
    rows = absent_rows(obligations, functions)

    per_callee = collections.OrderedDict()
    for row in rows:
        cls, note = classify(row["callee"], row["function"], functions, dropped_names, escaping,
                             members_by_name, terminals, foreign)
        entry = per_callee.setdefault(row["callee"], {"rows": 0, "class": cls, "shapes": collections.Counter(),
                                                      "callers": set(), "notes": set()})
        if entry["class"] != cls:
            raise Refuse(f"callee {row['callee'][:100]!r} classified two ways: {entry['class']} / {cls}")
        entry["rows"] += 1
        entry["shapes"][row["shape"]] += 1
        entry["callers"].add(functions[row["function"]]["name"])
        if note:
            entry["notes"].add(note)

    by_class = collections.Counter()
    distinct_by_class = collections.Counter()
    for entry in per_callee.values():
        by_class[entry["class"]] += entry["rows"]
        distinct_by_class[entry["class"]] += 1
    identity_sum = sum(by_class[c] for c in CLASSES)
    if identity_sum != len(rows):
        raise Refuse(f"identity failed: {len(rows)} absent rows != {identity_sum} summed over classes")
    unknown = [(n, e) for n, e in per_callee.items() if e["class"] == "unknown"]
    dynamic_not_virtual = [n for n, e in per_callee.items()
                           if e["shapes"]["dynamic-dispatch"] and e["class"] != "virtual"]
    if dynamic_not_virtual:
        raise Refuse(f"{len(dynamic_not_virtual)} dynamic-dispatch callee(s) are not classed virtual")

    # Indirect reconciliation: manifest indirect rows split by member disposition, versus what the module carries.
    indirect_rows_lowered = sum(n for caller, n in indirect_callers.items() if caller in bodyful)
    indirect_rows_dropped = sum(n for caller, n in indirect_callers.items() if caller in dropped_names)
    if indirect_rows_lowered + indirect_rows_dropped != sum(indirect_callers.values()):
        raise Refuse("an indirect-call escaping row names a caller that is neither lowered nor dropped")
    fnptr_rows = by_class["indirect-fnptr"]
    indirect_identity = indirect_rows_lowered == len(indirect_sites) + fnptr_rows
    if not indirect_identity:
        raise Refuse(f"indirect identity failed: {indirect_rows_lowered} manifest indirect rows in lowered members "
                     f"!= {len(indirect_sites)} call_indirect + {fnptr_rows} fn-pointer absent rows")

    # Dropped-member ledger.
    dropped_named = [m for m in dropped if m["name"] in per_callee]
    hints = collections.Counter(family_hint(m) or "none" for m in dropped)
    named_hints = collections.Counter(family_hint(m) or "none" for m in dropped_named)
    roots_outcomes = collections.Counter(r.get("outcome") for r in manifest.get("roots", []))

    shas = {"text": sha256_of(text_path), "binary": sha256_of(bin_path), "manifest": sha256_of(manifest_path)}
    checks = []

    def check(name, ok, detail):
        checks.append({"check": name, "ok": bool(ok), "detail": detail})
        if not ok:
            raise Refuse(f"{name}: {detail}")

    record_path = opts.get("record")
    if record_path:
        record = json.loads(Path(record_path).read_text(encoding="utf-8"))
        check("record.module_text_sha256", record.get("module_text_sha256") == shas["text"], record.get("module_text_sha256"))
        check("record.module_bin_sha256", record.get("module_bin_sha256") == shas["binary"], record.get("module_bin_sha256"))
        check("record.manifest_sha256", record.get("manifest_sha256") == shas["manifest"], record.get("manifest_sha256"))
        check("record.members", record.get("members_walked") == len(members), record.get("members_walked"))
        check("record.members_lowered", record.get("members_lowered") == len(bodyful), record.get("members_lowered"))
        check("record.members_dropped", record.get("members_dropped") == len(dropped), record.get("members_dropped"))
        check("record.module.functions", record.get("module", {}).get("functions") == len(functions),
              record.get("module", {}).get("functions"))
        check("record.module.obligations", record.get("module", {}).get("obligations") == len(obligations),
              record.get("module", {}).get("obligations"))
    census_path = opts.get("census")
    census_note = None
    if census_path:
        census = json.loads(Path(census_path).read_text(encoding="utf-8"))
        check("census.members", census.get("members") == len(members), census.get("members"))
        check("census.solo_ok", census.get("solo_ok") == len(bodyful), census.get("solo_ok"))
        check("census.solo_failed", census.get("solo_failed") == len(dropped), census.get("solo_failed"))
        census_note = {
            "manifest_sha256_in_census": census.get("manifest_sha256"),
            "matches_this_manifest": census.get("manifest_sha256") == shas["manifest"],
            "note": ("the census was measured against an earlier manifest (its own trust_rev differs); "
                     "its counts are pinned above, its sha is reported, not enforced"),
            "families": [{"id": f.get("id"), "name": f.get("name"), "members": f.get("members")}
                         for f in census.get("families", [])],
            "per_member_family_named": False,
        }
    expect = parse_expect(opts["expect"]) if "expect" in opts else {}
    actual = {"absent": len(rows), "call_indirect": len(indirect_sites), "dropped": len(dropped)}
    for key, value in expect.items():
        check(f"expect.{key}", actual[key] == value, f"expected {value}, measured {actual[key]}")
    check("no unknown absent callee", not unknown,
          f"{len(unknown)} unknown: " + "; ".join(f"{n[:80]} ({sorted(e['notes'])})" for n, e in unknown[:5]))

    top = sorted(per_callee.items(), key=lambda kv: (-kv[1]["rows"], kv[0]))
    report = {
        "schema": "crystal-sidecar-disposition-v1",
        "disposition": "derived",
        "module": {"name": module_name, "text": str(text_path), "binary": str(bin_path),
                   "manifest": str(manifest_path), "sha256": shas,
                   "functions": len(functions), "instruction_bearing": len(bodyful),
                   "bodyless_declarations_in_text": len(bodyless_in_text), "obligations": len(obligations)},
        "absent_callee_rows": len(rows),
        "absent_callee_row_shapes": dict(collections.Counter(r["shape"] for r in rows)),
        "distinct_absent_callees": len(per_callee),
        "rows_by_class": {c: by_class[c] for c in CLASSES},
        "distinct_callees_by_class": {c: distinct_by_class[c] for c in CLASSES},
        "identity": {"absent_rows": len(rows), "sum_over_classes": identity_sum, "holds": True},
        "call_indirect": {"count": len(indirect_sites), "sites": indirect_sites},
        "indirect_reconciliation": {
            "manifest_indirect_rows": sum(indirect_callers.values()),
            "in_lowered_members": indirect_rows_lowered,
            "in_dropped_members": indirect_rows_dropped,
            "call_indirect_instructions": len(indirect_sites),
            "fnptr_absent_rows": fnptr_rows,
            "identity_lowered_eq_call_indirect_plus_fnptr": indirect_identity,
        },
        "dropped_members": {
            "count": len(dropped),
            "derivation": "manifest members whose name is not an instruction-bearing `fn @` block of the module "
                          "(the module carries NO bodyless declarations for them; they are absent outright)",
            "named_by_an_absent_row": len(dropped_named),
            "not_named_by_any_absent_row": len(dropped) - len(dropped_named),
            "family": "unattributed: the lowering census is aggregate-only and names no member",
            "family_hint_all": dict(hints),
            "family_hint_named": dict(named_hints),
            "names": sorted(dropped_names),
        },
        "manifest": {"closed": manifest.get("closed"), "lowering": manifest.get("lowering"),
                     "members": len(members), "escaping_rows": len(manifest.get("escaping", [])),
                     "escaping_by_reason": dict(collections.Counter(escaping.values())),
                     "panic_terminals": len(manifest.get("panic_terminals", [])),
                     "roots_outcomes": dict(roots_outcomes)},
        "census": census_note,
        "top_absent_callees": [
            {"rows": e["rows"], "class": e["class"], "callers": len(e["callers"]),
             "family_hint": family_hint(members_by_name[n]) if e["class"] == "dropped-member" else None,
             "callee": n}
            for n, e in top[:25]
        ],
        "absent_callees": [
            {"callee": n, "rows": e["rows"], "class": e["class"], "shapes": dict(e["shapes"]),
             "callers": len(e["callers"]),
             "family_hint": family_hint(members_by_name[n]) if e["class"] == "dropped-member" else None,
             "notes": sorted(e["notes"])}
            for n, e in top
        ],
        "checks": checks,
        "meaning": (
            "Every escaping site the lowered module carries is enumerated and placed in exactly one class, "
            "and the counts reconcile with the manifest. This is the OPEN ledger link 3 should be derived from: "
            "it says how open the closure is, not that any edge closes, not that any class is dischargeable, "
            "and not which refusal family a dropped member belongs to (the census is aggregate-only)."
        ),
        "provenance": provenance,
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n")

    print(f"module {module_name}: {len(functions)} functions ({len(bodyful)} instruction-bearing, "
          f"{len(bodyless_in_text)} bodyless declarations), {len(obligations)} obligations")
    print(f"  absent-callee rows {len(rows)} ({report['absent_callee_row_shapes']}) over "
          f"{len(per_callee)} distinct callees")
    for cls in CLASSES:
        print(f"    {cls:16s} rows {by_class[cls]:5d}  distinct {distinct_by_class[cls]:4d}")
    print(f"  identity: {len(rows)} == {identity_sum}  HOLDS")
    print(f"  call_indirect {len(indirect_sites)}; manifest indirect rows {sum(indirect_callers.values())} = "
          f"{indirect_rows_lowered} in lowered ({len(indirect_sites)} call_indirect + {fnptr_rows} fn-pointer "
          f"absent rows) + {indirect_rows_dropped} in dropped")
    print(f"  dropped members {len(dropped)} of {len(members)} ({len(dropped_named)} named by an absent row); "
          f"family hint {dict(hints)} -- HINT, census is aggregate-only")
    print("  top absent callees:")
    for row in report["top_absent_callees"][:15]:
        print(f"    {row['rows']:5d} {row['class']:16s} {row['callee'][:100]}")
    for row in checks:
        print(f"  check {row['check']}: {'ok' if row['ok'] else 'FAIL'} ({row['detail']})")
    print(f"DISPOSITION: derived (closure is OPEN at {len(rows)} sites + {len(indirect_sites)} indirect)")
    print(f"wrote {out}")
    return 0


def self_test():
    """Drive `read_manifest_schema` -- the function `run` reads every manifest through -- in
    both polarities: each schema is read, v3 gives the SAME foreign set as its v2 twin (never
    the v1 name-shape fallback), and a v3 manifest missing or malforming a v3 field, or any
    unknown schema, refuses with its own message."""
    call = {"bb": 2, "site": "s", "resolved": "r", "class": "member"}
    v2 = {"schema": MANIFEST_V2, "closed": False, "foreign_terminals": ["libc::{extern#0}::f"],
          "members": [{"sidecar_func_id": 0, "name": "m", "mir_blocks": 4, "calls": [dict(call)]}]}

    def v3(mutate=None):
        m = json.loads(json.dumps(v2))
        m.update(schema=MANIFEST_V3, fuel=64, fuel_exhausted=False)
        m["members"][0]["mir_digest"] = "sha256:" + "ab" * 32
        if mutate:
            mutate(m)
        return m

    def v1():
        m = json.loads(json.dumps(v2))
        m["schema"] = MANIFEST_V1
        del m["foreign_terminals"]
        return m

    arms = []

    def reads(tag, manifest, want):
        try:
            got = read_manifest_schema(manifest)
        except Refuse as refusal:
            arms.append((tag, False, f"refused: {refusal}"))
            return
        arms.append((tag, got == want, f"read {got!r}, expected {want!r}"))

    def refuses(tag, manifest, needle):
        try:
            got = read_manifest_schema(manifest)
        except Refuse as refusal:
            arms.append((tag, needle in str(refusal), f"refused by the WRONG guard: {refusal}"))
            return
        arms.append((tag, False, f"read {got!r} instead of refusing"))

    ft = frozenset(["libc::{extern#0}::f"])
    reads("v1-reads-without-foreign", v1(), None)
    reads("v2-reads-foreign", json.loads(json.dumps(v2)), ft)
    reads("v3-reads-as-its-v2-twin", v3(), ft)
    refuses("v3-call-without-bb", v3(lambda m: m["members"][0]["calls"][0].pop("bb")), "`bb`")
    refuses("v3-bb-past-mir_blocks", v3(lambda m: m["members"][0]["calls"][0].update(bb=4)), "`bb`")
    refuses("v3-bb-a-bool", v3(lambda m: m["members"][0]["calls"][0].update(bb=True)), "`bb`")
    refuses("v3-member-without-mir_digest", v3(lambda m: m["members"][0].pop("mir_digest")), "`mir_digest`")
    refuses("v3-zero-mir_digest",
            v3(lambda m: m["members"][0].update(mir_digest=ZERO_MIR_DIGEST)), "`mir_digest`")
    refuses("v3-without-fuel", v3(lambda m: m.pop("fuel")), "`fuel`")
    refuses("v3-closed-with-fuel-exhausted",
            v3(lambda m: m.update(closed=True, fuel_exhausted=True)), "fuel exhausted")
    refuses("v3-without-foreign_terminals", v3(lambda m: m.pop("foreign_terminals")), "`foreign_terminals`")
    refuses("unknown-schema", v3(lambda m: m.update(schema="trust-ir-callee-sidecar-v4")), "schema")

    # M2 (2026-09-27): `parse_module` -- the function `run` reads every module through -- reads a
    # module however trust-ir printed its symbols. A WS4.3 module (non-bare names QUOTED) parses to
    # the SAME names as its legacy twin (the `fn @(.*)` regex this replaced kept the quotes, so no
    # function joined its manifest member by name), and what no printer writes is REFUSED.
    legacy = ("; TrustIr text format v1\nmodule \"k::callees\"\n"
              "fn @k::a<'_>(functy.0) {\nbb0:\n    %0 = call @func.1()\n    ret\n}\n"
              "rustcc fn @<k::S as k::T>::b(functy.1) {\n}\n"
              'obligation 0 x open "d" function 0 formula "s" \n')
    quoted = tir_symbols.respell_ws43(legacy)

    def parses(tag, text, want):
        try:
            got = [(f["name"], f["functy"], f["instruction_bearing"]) for f in parse_module(text)[1]]
        except Refuse as refusal:
            arms.append((tag, False, f"refused: {refusal}"))
            return
        arms.append((tag, got == want, f"parsed {got!r}, expected {want!r}"))

    def refuses_text(tag, text, needle):
        try:
            got = parse_module(text)
        except Refuse as refusal:
            arms.append((tag, needle in str(refusal), f"refused by the WRONG guard: {refusal}"))
            return
        arms.append((tag, False, f"parsed {got!r} instead of refusing"))

    names = [("k::a<'_>", 0, True), ("<k::S as k::T>::b", 1, False)]
    parses("legacy-module-parses", legacy, names)
    parses("ws43-quoted-module-parses-to-the-same-names",
           quoted if '@"k::a<\'_>"' in quoted else legacy + "not respelled", names)
    refuses_text("mixed-quoted-and-raw-refused",
                 quoted.replace('@"<k::S as k::T>::b"', "@<k::S as k::T>::b"), "mixes a QUOTED")
    refuses_text("bad-escape-refused", quoted.replace('"k::a<\'_>"', '"k::a\\q"'),
                 "is not one the trust-ir printer emits")
    bad = [(tag, why) for tag, ok, why in arms if not ok]
    for tag, why in bad:
        print(f"  [RED] self-test arm {tag}: {why}")
    print(f"crystal_sidecar_disposition self-test: {len(arms) - len(bad)}/{len(arms)} arms behave")
    return 0 if not bad else 1


def main(argv):
    if len(argv) == 2 and argv[1] in ("--self-test", "--selftest"):
        return self_test()
    if len(argv) == 2 and argv[1] == "--pinned-inputs":
        print("\n".join(tir_symbols.first_party_imports(Path(__file__))))
        return 0
    if len(argv) < 3:
        print(__doc__.strip().splitlines()[2].strip())
        print(__doc__.strip().splitlines()[3].strip())
        return 2
    dump, out = Path(argv[1]), Path(argv[2])
    opts, provenance = parse_kv(argv[3:])
    try:
        return run(dump, out, opts, provenance)
    except Refuse as refusal:
        print(f"REFUSED: {refusal}")
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps({"schema": "crystal-sidecar-disposition-v1", "disposition": "refused",
                                   "reason": str(refusal), "provenance": provenance}, indent=2) + "\n")
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
