#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Per-FUNCTION object burn-in for the Trust flip: a gained drop is never explainable.

WHY THIS EXISTS
---------------
The Trust flip replaces rustc's MIR for some bodies with MIR derived from
trust-ir. Its safety evidence was a comparator that could not see OWNERSHIP: a
flipped `TypeChecker::infer_type` passed a `TypeError` BY COPY where built MIR
MOVES it, then dropped the bitwise copy after handing the value to
`from_residual` -- a DOUBLE DROP. Every check passed. Crate totals and the
symbol set were unchanged (the extra call is a new RELOCATION inside an
EXISTING function), so only a comparison per function could see it: in the
flipped arm `infer_type` carries one more `bl core::ptr::drop_glue::<TypeError>`
than the control. This script is that comparison, made fail-closed.

WHAT IT DOES
------------
    crystal_object_burnin.py CONTROL ARM [--explained FILE.json] [--json OUT.json]
                             [--cache-dir DIR] [--show-diff] [--no-demangle]
    crystal_object_burnin.py --selftest

CONTROL and ARM are each an `.rlib`/`ar` archive, one object file, or a
directory of object files. Object members are chosen by MAGIC, never by name.
Each object is disassembled with `objdump -d -r --no-show-raw-insn
--show-all-symbols` (cached by the object's content sha256 plus the objdump
identity when --cache-dir is given), and the text is PARSED: a function is the
text between two `<sym>:` headers. Nothing is grep-counted.

VERDICT (exit 0 pass, 1 fail, 2 refused -- every non-zero is a failure)
  * 1 if any function present on both sides gains a reference -- per symbol,
    the count strictly increases -- to a DROP symbol (DROP_NEEDLES below), or
    a function present only in the arm references one at all. That is the
    double-drop / use-after-free signature and an --explained entry does NOT
    suppress it. A reference through a machine-outlined body or a pure
    tail-call thunk counts as the caller's own (see THUNKS).
    The needles are matched as substrings of the MANGLED name, which works for
    both Rust schemes because v0 (`_R`) and legacy (`_ZN`) mangling embed every
    identifier verbatim as `<len><ident>`. They are `drop_glue` /
    `drop_in_place` (the glue), `drop_slow` (an inlined `Arc`/`Rc` decrement
    calls `Arc::<T>::drop_slow`: the O3 control of 2026-09-23 has 390 call
    sites of `Arc<Expr>::drop_slow` alone, so a double drop of an `Expr`
    reaches no glue symbol), `4Drop4drop` / `Drop$GT$4drop` (a direct
    `<T as Drop>::drop`, v0 and legacy: 311 sites at O3, 1,105 at O0) and
    `dealloc` (`__rust_dealloc`, `alloc::alloc::dealloc`,
    `Allocator::deallocate`: 315 `deallocate` sites at O0).
  * 1 if a function differs, or exists on one side only, and is not named in
    --explained (a JSON object: function name -> non-empty reason).
  * 1 if an --explained entry names a function that does NOT differ: a stale
    explanation is a pre-signed excuse for the next, different change.
  * 2 if an input cannot be read, has no object member, has no member with
    an executable section, objdump fails, a code-bearing member parses to
    zero functions, an object is not `mach-o arm64` (the only format the
    normalisation was measured on), or a BRANCH relocation names a
    layout-local label instead of a symbol (its callee could not be named, so
    a drop there could not be seen; none exist in the 2026-09-23 artifacts).
    An empty comparison is not a pass. A member whose own
    section table holds no instructions (an rlib's `lib.rmeta` is a Mach-O
    object) is skipped and listed -- decided by section flags, never by name.

ALIASES AND THUNKS
  * `--show-all-symbols`: without it llvm-objdump prints ONE name per address,
    and the O3 control has 7,730 text symbols at 7,483 addresses (`nm`), so
    247 names -- merged-function aliases, and the real name of the function
    printed as `ltmp0` -- were never compared. Headers at one address with no
    body between them now all receive the body that follows, so a function
    the arm merges into a dropping sibling is compared under its own name.
  * THUNKS: a call to an `_OUTLINED_FUNCTION_*` body or to a function whose
    whole body is ONE instruction (a merge-functions tail call is one `b`; 32
    such bodies in the O3 control) adds that body's drop references to
    the caller's count (transitively), so a drop the machine outliner or
    merge-functions moves out of line is still the caller's gained drop.

NORMALISATION (the prototype's, plus what the real artifacts measured it needs)
  * `l_anon.<hash>.` -> `l_anon.H.`; `adrp` page operands -> PAGE; absolute
    `0x... <` addresses dropped; a branch target in the function itself is
    written relative to `.` (a relocated instruction's placeholder operand
    always lands there too, so the relocation line alone names its target).
  * layout-local labels -- `l_anon.H.<n>`, `lCPI<n>_<m>`, `ltmp<n>`,
    `__MergedGlobals[.n]` -- are renamed per function by first appearance.
    Measured 2026-09-23 on the O3 cu=1 control/cite pair, one class at a
    time: the prototype (which kept every index) reports 1,118 differing
    functions and renaming `lCPI` ALONE brings it to 20 -- `lCPI<n>` is
    numbered by the function's ordinal, and the arm lacks one function, so
    every later function renumbers. Renaming `l_anon`/`ltmp`/`__MergedGlobals`
    changes nothing on that pair; they are renamed because their indices are
    module-sequential in the same way (reasoning, not a measurement).
  * `ARM64_RELOC_ADDEND` is folded into the relocation it qualifies: kept
    (`sym+0x50`) against a global symbol, reduced to `+A` against a
    layout-local label, where the offset is layout.
  * `<name>.llvm.<digits>` -> `<name>.llvm.P`, on function names and on every
    operand. ThinLTO (cargo's default at codegen-units > 1 and opt-level > 0)
    promotes a local symbol another unit references and suffixes it with the
    DEFINING module's hash, so an arm that moves that module renames the callee
    while every call site stays put: measured on the cu=16 clean-kernel pair of
    2026-09-24, all 15 "gained" drops inside the codegen units whose members
    were identical on both sides were such renames. The `.llvm.` marker is kept,
    so a promoted copy is still distinct from the external symbol.
  * a PROMOTED anonymous constant, `_anon.<module hash>.<n>` (the global twin of
    `l_anon`, carrying the defining module's hash and index), is renamed like
    `l_anon`: 276 of the 283 non-drop differences left in those same identical
    units after the suffix rule were such renames.
  * `_OUTLINED_FUNCTION_<n>` (machine-outliner bodies) are named by the digest
    of their normalised body, both as entries and as call targets, so a
    renumbering pairs up and a changed outlined body is still seen.

KNOWN LIMITS (stated, not hidden)
  * The renaming of layout-local labels makes the comparison blind to a
    function that switches WHICH anonymous constant / constant-pool entry it
    references while its code is otherwise identical. Data sections (string
    constants, vtables, jump tables) are not compared at all.
  * A renamed function is only-in-each; if the new name references any drop
    symbol that is an unexplainable drop finding, so a rename that keeps its
    drops can only be passed by changing this gate, never by --explained.
  * A drop fully inlined past every needle -- e.g. a user `Drop::drop` body
    inlined into the caller that neither deallocates nor calls glue -- is not
    seen, and a drop reached through an ordinary (non-thunk) helper counts
    against the helper, not the caller.
  * Multiple copies of one name (codegen-units > 1) are paired as a multiset
    (see `drop_gain`); an arm copy with no partner is held to the control's
    largest count, so a NEW copy that drops no more than the most-dropping
    control copy passes. Codegen-units > 1 is not judgeable in practice: the
    cu=16 pair ckt-link-O3-dt2ctl / -dt2cite (2026-09-23) reports 5,889
    differing functions and 2,246 with gained drop references, because the
    partitioner moves inlining between units. Burn in at codegen-units=1.
  * The normalisation was measured on Mach-O arm64 (llvm-objdump) only; any
    other format is refused rather than trusted. ELF, for one, may relocate a
    call against a SECTION symbol (`.text+0x40`), which would name no callee.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import difflib
import hashlib
import io
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import time
import zlib
from dataclasses import dataclass
from pathlib import Path

SCHEMA = "clean.crystal-object-burnin/v1"
EXIT_PASS = 0
EXIT_FAIL = 1
EXIT_REFUSED = 2
OBJDUMP_ARGS = ("-d", "-r", "--no-show-raw-insn", "--show-all-symbols")
DROP_NEEDLES = ("drop_glue", "drop_in_place", "drop_slow", "4Drop4drop", "Drop$GT$4drop",
                "dealloc")
BRANCH_RELOCS = ("ARM64_RELOC_BRANCH26", "X86_64_RELOC_BRANCH")
MEASURED_FORMAT = "mach-o arm64"
OBJECT_MAGICS = (b"\xcf\xfa\xed\xfe", b"\xce\xfa\xed\xfe", b"\xfe\xed\xfa\xcf",
                 b"\xfe\xed\xfa\xce", b"\x7fELF")

HEADER = re.compile(r"^([0-9a-f]+) <(.+)>:$")
SECTION = re.compile(r"^Disassembly of section (.+):$")
FILE_FORMAT = re.compile(r":\s+file format (.+)$")
RELOC = re.compile(r"^([0-9a-f]+):\s+((?:ARM64|X86_64)_RELOC_[A-Z0-9_]+|R_[A-Z0-9_]+)\s*(.*)$")
INSN = re.compile(r"^([0-9a-f]+):\s*(.*)$")
WS = re.compile(r"\s+")
ANON_HASH = re.compile(r"(?<![A-Za-z0-9_])(l?_anon)\.[0-9a-f]+\.")
ADRP_TARGET = re.compile(r"0x[0-9a-f]+ <.*>$")
ABS_ADDR = re.compile(r"\b0x[0-9a-f]+ <")
SYMREF = re.compile(r"<[^<>]*>")
LOCAL = re.compile(r"\b(l_anon\.H\.|_anon\.H\.|lCPI|ltmp|__MergedGlobals)(\d+_\d+|\d+|\.\d+)?\b")
OUTLINED = re.compile(r"\b_OUTLINED_FUNCTION_\d+\b")
LLVM_PROMO = re.compile(r"\.llvm\.\d+\b")


class Refused(Exception):
    """An input the gate cannot judge. Exit 2: an unread input is never a pass."""


@dataclass
class Fn:
    name: str
    obj: str
    start: int
    nlines: int
    digest: str
    drops: dict       # drop-needle symbol -> reference count (through thunks)
    blob: bytes       # zlib("addr\tnormalised line\n" ...), for --show-diff / drop sites
    callees: tuple = ()   # relocation targets, for thunk attribution (parse-local)
    thunk: bool = False   # the whole body is ONE instruction (a tail-call thunk)


# ── parsing ──────────────────────────────────────────────────────────────────

def is_drop_symbol(sym: str) -> bool:
    return any(n in sym for n in DROP_NEEDLES)


def _rename_locals(lines: list) -> list:
    """Layout-local labels renamed per function, per class, by first appearance."""
    seen: dict = {}

    def sub(m: re.Match) -> str:
        key = m.group(0)
        if key not in seen:
            seen[key] = sum(1 for k in seen if k.startswith(m.group(1)))
        return f"{m.group(1)}#{seen[key]}"
    return [(a, LOCAL.sub(sub, t)) for a, t in lines]


def _finish(name: str, obj: str, start: int, lines: list) -> Fn:
    lines = _rename_locals(lines)
    drops: dict = {}
    callees, insns = [], []
    for _, t in lines:
        sym = t.split(" ", 2)[2] if t.startswith("R ") and t.count(" ") >= 2 else ""
        if sym and not t.startswith("R ARM64_RELOC_ADDEND"):
            callees.append(sym.split("+", 1)[0])
        if not t.startswith("R "):
            insns.append(t)
        if not sym:
            m = SYMREF.search(t)
            sym = m.group(0)[1:-1] if m else ""
        if sym and is_drop_symbol(sym):
            sym = sym.split("+", 1)[0]
            drops[sym] = drops.get(sym, 0) + 1
    body = "\n".join(t for _, t in lines)
    blob = zlib.compress("".join(f"{a:x}\t{t}\n" for a, t in lines).encode(), 1)
    return Fn(name, obj, start, len(lines), hashlib.sha256(body.encode()).hexdigest(),
              drops, blob, tuple(callees), len(insns) == 1)


def _through_thunks(fns: list) -> None:
    """Add to each function the drop references of the outlined bodies and
    pure tail-call thunks it references, transitively (cycles cut)."""
    transparent = {f.name: f for f in fns if f.thunk or f.name.startswith("_OUTLINED_FUNCTION_")}
    if not transparent:
        return
    memo: dict = {}

    def eff(f: Fn) -> dict:
        if id(f) in memo:
            return memo[id(f)]
        memo[id(f)] = dict(f.drops)                       # a cycle sees direct refs only
        out = dict(f.drops)
        for c in f.callees:
            g = transparent.get(c)
            if g is not None and g is not f:
                for s, n in eff(g).items():
                    out[s] = out.get(s, 0) + n
        memo[id(f)] = out
        return out
    effective = [eff(f) for f in fns]                     # all computed from DIRECT counts
    for f, d in zip(fns, effective):
        f.drops = d


def _resolve_outlined(pending: list, obj: str) -> list:
    """Name every `_OUTLINED_FUNCTION_<n>` by the digest of its own body."""
    bodies = {n: ls for n, _, ls in pending if OUTLINED.fullmatch(n)}
    digest = {n: hashlib.sha256("\n".join(t for _, t in _rename_locals(ls)).encode())
              .hexdigest()[:16] for n, ls in bodies.items()}

    def sub(m: re.Match) -> str:
        return f"_OUTLINED_FUNCTION_{digest[m.group(0)]}" if m.group(0) in digest \
            else "_OUTLINED_FUNCTION_?"
    out = []
    for name, start, ls in pending:
        name = sub(OUTLINED.fullmatch(name)) if OUTLINED.fullmatch(name) else name
        out.append(_finish(name, obj, start, [(a, OUTLINED.sub(sub, t)) for a, t in ls]))
    return out


def parse_objdump(stream, obj: str) -> tuple:
    """Parse `objdump -d -r --no-show-raw-insn --show-all-symbols` text into Fn records.

    Returns (functions, fmt). A function is the text between two `<sym>:`
    headers; a section header or a file header also closes it. Consecutive
    headers at ONE address with no body between them are aliases
    (`--show-all-symbols`): every one of them receives the body that follows.
    """
    done: list = []      # finished Fn records
    pending: list = []   # (name, start, [(addr, text)]) awaiting outlined-body digests
    st = {"name": None, "start": 0, "lines": [], "addend": None, "aliases": []}
    fmt = section = ""
    own: list = []       # (`<name+`, `<name>`) for every name of the current body

    def close() -> None:
        if st["name"] is not None:
            if st["addend"] is not None:
                a, v = st["addend"]
                st["lines"].append((a, f"R ARM64_RELOC_ADDEND {v}"))
            for nm in st["aliases"] + [st["name"]]:
                fn = (nm, st["start"], st["lines"])
                if OUTLINED.fullmatch(nm) or any("_OUTLINED_FUNCTION_" in t for _, t in fn[2]):
                    pending.append(fn)    # named by an outlined body's digest at the end
                else:
                    done.append(_finish(fn[0], obj, fn[1], fn[2]))
        st.update(name=None, lines=[], addend=None, aliases=[])

    for raw in stream:
        line = raw.rstrip("\n")
        if not line:
            continue
        c0 = line[0]
        if c0 not in " \t":
            m = HEADER.match(line)
            if m:
                start, name = int(m.group(1), 16), LLVM_PROMO.sub(".llvm.P", m.group(2))
                if (st["name"] is not None and not st["lines"] and st["addend"] is None
                        and st["start"] == start):
                    st["aliases"].append(st["name"])      # same address, no body yet
                else:
                    close()
                    own = []
                own.append((f"<{name}+", f"<{name}>"))
                if section not in ("", "__TEXT,__text", ".text"):
                    name = f"{section}::{name}"
                st.update(name=name, start=start, lines=[])
                continue
            m = SECTION.match(line)
            if m:
                close()
                section = m.group(1)
                continue
            m = FILE_FORMAT.search(line)
            if m:
                close()
                fmt = m.group(1).strip()
                continue
        if st["name"] is None:
            continue
        s = LLVM_PROMO.sub(".llvm.P", line.strip())
        lines = st["lines"]
        m = RELOC.match(s) if "R_" in s or "_RELOC_" in s else None
        if m:
            addr, rtype, sym = int(m.group(1), 16), m.group(2), m.group(3).strip()
            pend = st["addend"]
            if rtype.endswith("_ADDEND"):
                if pend is not None:
                    lines.append((pend[0], f"R ARM64_RELOC_ADDEND {pend[1]}"))
                st["addend"] = (addr, sym)
                continue
            sym = ANON_HASH.sub(r"\1.H.", sym)
            if rtype in BRANCH_RELOCS and LOCAL.fullmatch(sym):
                raise Refused(f"{obj}: {rtype} at 0x{addr:x} in {st['name']} names the "
                              f"layout-local label {sym!r}, not its callee -- a drop there "
                              f"could not be seen")
            if pend is not None and pend[0] == addr:
                sym = f"{sym}+A" if LOCAL.fullmatch(sym) else f"{sym}+{pend[1]}"
                st["addend"] = None
            lines.append((addr, f"R {rtype} {sym}"))
            continue
        if st["addend"] is not None:
            a, v = st["addend"]
            lines.append((a, f"R ARM64_RELOC_ADDEND {v}"))
            st["addend"] = None
        m = INSN.match(s)
        if not m:
            lines.append((-1, "X " + WS.sub(" ", s)))
            continue
        ins = WS.sub(" ", m.group(2).strip())
        if ins.startswith("adrp "):
            ins = ADRP_TARGET.sub("PAGE", ins)
        elif "0x" in ins:
            ins = ABS_ADDR.sub("<", ins)
        if "<" in ins:
            for own_plus, own_close in own:
                ins = ins.replace(own_plus, "<.+").replace(own_close, "<.>")
        lines.append((int(m.group(1), 16), ins))
    close()
    fns = done + _resolve_outlined(pending, obj)
    _through_thunks(fns)
    return fns, fmt


# ── inputs ───────────────────────────────────────────────────────────────────

def ar_members(data: bytes):
    """(name, bytes) for every member of a BSD or GNU `ar` archive."""
    if not data.startswith(b"!<arch>\n"):
        raise Refused("not an ar archive")
    pos, longnames = 8, b""
    while pos + 60 <= len(data):
        hdr = data[pos:pos + 60]
        if hdr[58:60] != b"`\n":
            raise Refused(f"corrupt ar member header at byte {pos}")
        name = hdr[:16].decode("ascii", "replace").rstrip()
        size = int(hdr[48:58].decode("ascii").strip())
        body = data[pos + 60:pos + 60 + size]
        pos += 60 + size + (size & 1)
        if name.startswith("#1/"):
            n = int(name[3:])
            name, body = body[:n].rstrip(b"\0").decode("utf-8", "replace"), body[n:]
        elif name == "//":
            longnames = body
            continue
        elif name in ("/", "/SYM64/"):
            continue
        elif name.startswith("/") and name[1:].isdigit():
            off = int(name[1:])
            name = longnames[off:].split(b"\n", 1)[0].rstrip(b"/").decode("utf-8", "replace")
        else:
            name = name.rstrip("/")
        yield name, body


def collect_objects(spec: Path) -> list:
    """[(label, bytes)] for every object file CONTROL/ARM names, chosen by magic."""
    if spec.is_dir():
        found = [(p.name, p.read_bytes()) for p in sorted(spec.iterdir()) if p.is_file()]
    elif spec.is_file():
        data = spec.read_bytes()
        if data.startswith(b"!<arch>\n"):
            found = [(f"{spec.name}({n})", b) for n, b in ar_members(data)]
        else:
            found = [(spec.name, data)]
    else:
        raise Refused(f"{spec} does not exist")
    if any(b.startswith(b"BC\xc0\xde") for _, b in found):
        raise Refused(f"{spec} holds LLVM bitcode members; objdump cannot disassemble them")
    objs = [(n, b) for n, b in found if b[:4] in OBJECT_MAGICS]
    if not objs:
        raise Refused(f"{spec} contains no object file (Mach-O/ELF magic)")
    return objs


def code_bytes(data: bytes) -> int | None:
    """Bytes of executable sections, read from the object's OWN section flags.

    An rlib's `lib.rmeta` is itself a Mach-O object (Rust wraps metadata in
    one) with no code, so "parsed to zero functions" is its normal state. It is
    skipped because its section table says it holds no instructions -- never
    because of its name. None = a format this reader does not model, which is
    then treated as code-bearing, so zero functions there still refuses.
    """
    try:
        if data[:4] == b"\xcf\xfa\xed\xfe":                      # Mach-O 64, little-endian
            ncmds = struct.unpack_from("<I", data, 16)[0]
            off, total = 32, 0
            for _ in range(ncmds):
                cmd, size = struct.unpack_from("<II", data, off)
                if cmd == 0x19:                                  # LC_SEGMENT_64
                    nsects = struct.unpack_from("<I", data, off + 64)[0]
                    for k in range(nsects):
                        sec = off + 72 + 80 * k
                        sz = struct.unpack_from("<Q", data, sec + 40)[0]
                        flags = struct.unpack_from("<I", data, sec + 64)[0]
                        if flags & 0x80000400:                   # PURE_ | SOME_INSTRUCTIONS
                            total += sz
                off += size
            return total
        if data[:4] == b"\x7fELF" and data[4] == 2 and data[5] == 1:   # ELF64, little-endian
            shoff = struct.unpack_from("<Q", data, 0x28)[0]
            shentsize, shnum = struct.unpack_from("<HH", data, 0x3A)
            return sum(struct.unpack_from("<Q", data, shoff + i * shentsize + 32)[0]
                       for i in range(shnum)
                       if struct.unpack_from("<Q", data, shoff + i * shentsize + 8)[0] & 0x4)
    except struct.error as exc:
        raise Refused(f"truncated object header: {exc}") from exc
    return None


def check_format(label: str, fmt: str) -> None:
    """Refuse any object format the normalisation was not measured on."""
    if fmt != MEASURED_FORMAT:
        raise Refused(f"{label} is {fmt or 'of no stated format'!r}; the normalisation "
                      f"was measured on {MEASURED_FORMAT!r} only")


def objdump_tool(path: str) -> dict:
    exe = shutil.which(path)
    if not exe:
        raise Refused(f"objdump not found: {path}")
    ver = subprocess.run([exe, "--version"], capture_output=True, text=True, check=False)
    ident = f"{os.path.realpath(exe)}\n{ver.stdout}\n{' '.join(OBJDUMP_ARGS)}"
    return {"path": exe, "version": (ver.stdout.strip().splitlines() or ["?"])[0].strip(),
            "key": hashlib.sha256(ident.encode()).hexdigest()[:16]}


def disassemble(sha: str, data: bytes, tool: dict, cache: Path | None, work: Path) -> dict:
    """objdump text for one object, by content sha256; called once per DISTINCT object."""
    out_dir = cache if cache is not None else work
    out = out_dir / f"{sha}-{tool['key']}.objdump.txt"
    hit = cache is not None and out.is_file()
    if not hit:
        obj = work / f"{sha}.o"
        obj.write_bytes(data)
        tmp = out_dir / f".{sha}.{os.getpid()}.{time.monotonic_ns()}.partial"
        with open(tmp, "wb") as fh:
            rc = subprocess.run([tool["path"], *OBJDUMP_ARGS, str(obj)], stdout=fh,
                                stderr=subprocess.PIPE, check=False)
        if rc.returncode != 0:
            tmp.unlink(missing_ok=True)
            raise Refused(f"objdump exited {rc.returncode} on object sha256:{sha}: "
                          f"{rc.stderr.decode(errors='replace').strip()[-300:]}")
        os.replace(tmp, out)
        obj.unlink(missing_ok=True)
    return {"text": str(out), "cache": "hit" if hit else ("stored" if cache else "none")}


def _parse_file(path: str, label: str) -> tuple:
    """Worker entry: plain tuples cross the process boundary, never Fn instances."""
    with open(path, encoding="utf-8", errors="replace") as fh:
        fns, fmt = parse_objdump(fh, label)
    return [(f.name, f.obj, f.start, f.nlines, f.digest, f.drops, f.blob) for f in fns], fmt


def load_side(fns_by_obj: list) -> dict:
    side: dict = {}
    for fns in fns_by_obj:
        for f in fns:
            side.setdefault(f.name, []).append(f)
    return side


# ── comparison ───────────────────────────────────────────────────────────────

def drop_gain(ctl: list, arm: list) -> dict:
    """symbol -> (control count, arm count) for a copy that gained references.

    Copies of one name (codegen-units > 1) are paired as a MULTISET: digest-
    identical copies cancel first, then the rest pair per symbol by rank,
    largest with largest. An arm copy left with no partner is held to the
    control's largest count, so a monomorphisation duplicated into another
    codegen unit is not a gained drop. This is strictly stronger than the max
    over copies it replaced, which let one copy's 0 -> 1 gain hide behind a
    sibling copy that already referenced the symbol twice.
    """
    rest_c, rest_a = list(ctl), []
    for f in arm:
        hit = next((i for i, g in enumerate(rest_c) if g.digest == f.digest), None)
        if hit is None:
            rest_a.append(f)
        else:
            del rest_c[hit]
    out = {}
    for s in sorted({s for f in ctl + arm for s in f.drops}):
        top = max(f.drops.get(s, 0) for f in ctl)
        cs = sorted((f.drops.get(s, 0) for f in rest_c), reverse=True)
        for i, a in enumerate(sorted((f.drops.get(s, 0) for f in rest_a), reverse=True)):
            c = cs[i] if i < len(cs) else top
            if a > c:
                out[s] = (c, a)
                break
    return out


def _lines(f: Fn) -> list:
    rows = zlib.decompress(f.blob).decode().splitlines()
    return [(int(r.split("\t", 1)[0], 16), r.split("\t", 1)[1]) for r in rows]


def added_drop_sites(ctl: Fn, arm: Fn, gained) -> list:
    """Arm-side references to a GAINED symbol in inserted/replaced runs of the
    aligned diff. Evidence for a reader; the verdict is the count, not this."""
    a, b = _lines(ctl), _lines(arm)
    sm = difflib.SequenceMatcher(None, [t for _, t in a], [t for _, t in b], autojunk=False)
    out = []
    for tag, _, _, j1, j2 in sm.get_opcodes():
        if tag in ("insert", "replace"):
            out += [f"0x{addr:x}  {t}" for addr, t in b[j1:j2]
                    if any(t.endswith(f" {g}") or f" {g}+" in t for g in gained)]
    return out


def compare(ctl: dict, arm: dict, explained: dict) -> dict:
    common = sorted(ctl.keys() & arm.keys())
    only_c = sorted(ctl.keys() - arm.keys())
    only_a = sorted(arm.keys() - ctl.keys())
    differing, drops, unexplained, ignored = [], [], [], []
    for name in common:
        if {f.digest for f in ctl[name]} == {f.digest for f in arm[name]}:
            continue
        gain = drop_gain(ctl[name], arm[name])
        row = {"name": name, "control_lines": ctl[name][0].nlines,
               "arm_lines": arm[name][0].nlines, "arm_start": f"0x{arm[name][0].start:x}",
               "explained": explained.get(name)}
        differing.append(row)
        if gain:
            c = max(ctl[name], key=lambda f: sum(f.drops.values()))
            a = max(arm[name], key=lambda f: sum(f.drops.values()))
            drops.append({"name": name, "gained": {s: {"control": v[0], "arm": v[1]}
                                                   for s, v in gain.items()},
                          "added_sites": added_drop_sites(c, a, gain)})
            if name in explained:
                ignored.append(name)
        if name not in explained:
            unexplained.append(name)
    unexplained += [n for n in only_c + only_a if n not in explained]
    touched = {r["name"] for r in differing} | set(only_c) | set(only_a)
    stale = sorted(n for n in explained if n not in touched)
    lonely = {n: {s: max(f.drops.get(s, 0) for f in arm[n])
                  for s in sorted({s for f in arm[n] for s in f.drops})}
              for n in only_a if any(f.drops for f in arm[n])}
    # a function the control does not have gains every drop it references: a
    # new helper (or a rename) is exactly where an out-of-line drop can go
    for n, refs in lonely.items():
        drops.append({"name": n, "only_in_arm": True,
                      "gained": {s: {"control": 0, "arm": c} for s, c in refs.items()},
                      "added_sites": [f"0x{a:x}  {t}" for a, t in _lines(arm[n][0])
                                      if any(t.endswith(f" {s}") or f" {s}+" in t
                                             for s in refs)]})
        if n in explained:
            ignored.append(n)
    fail = bool(drops or unexplained or stale)
    return {"functions": {"control": len(ctl), "arm": len(arm)}, "common": len(common),
            "differing": differing, "only_in_control": only_c, "only_in_arm": only_a,
            "drop_findings": drops, "explanation_ignored_for_drop": ignored,
            "only_in_arm_drop_refs": lonely, "unexplained": sorted(set(unexplained)),
            "stale_explanations": stale, "verdict": "fail" if fail else "pass",
            "exit_code": EXIT_FAIL if fail else EXIT_PASS}


def load_explained(path: Path | None) -> dict:
    if path is None:
        return {}
    try:
        doc = json.loads(path.read_text())
    except (OSError, ValueError) as exc:
        raise Refused(f"--explained {path}: {exc}") from exc
    if not isinstance(doc, dict) or not all(
            isinstance(k, str) and isinstance(v, str) and v.strip() for k, v in doc.items()):
        raise Refused(f"--explained {path} must be a JSON object: function name -> "
                      f"non-empty reason string")
    return doc


# ── reporting ────────────────────────────────────────────────────────────────

def demangle(names: list, fmt: str) -> dict:
    tool = shutil.which("llvm-cxxfilt") or shutil.which("c++filt")
    if not tool or not names:
        return {}
    args = [tool, "-_"] if "mach-o" in fmt else [tool]
    try:
        r = subprocess.run(args, input="\n".join(names) + "\n", capture_output=True,
                           text=True, timeout=60, check=False)
    except (OSError, subprocess.SubprocessError):
        return {}
    got = r.stdout.splitlines()
    if r.returncode != 0 or len(got) != len(names):
        return {}
    return {n: d for n, d in zip(names, got) if d != n}


def print_report(rep: dict, dm: dict, ctl: dict, arm: dict, show_diff: bool) -> None:
    def label(n: str) -> str:
        return f"{n}\n        = {dm[n]}" if n in dm else n
    fc = rep["functions"]
    print(f"  functions: control {fc['control']}  arm {fc['arm']}  common {rep['common']}")
    print(f"  differing {len(rep['differing'])}  only-in-control {len(rep['only_in_control'])}"
          f"  only-in-arm {len(rep['only_in_arm'])}")
    print(f"  drop/dealloc references GAINED in {len(rep['drop_findings'])} function(s), "
          f"common or only-in-arm  [never explainable]")
    for d in rep["drop_findings"]:
        print(f"DROP  {'(only in arm) ' if d.get('only_in_arm') else ''}{label(d['name'])}")
        for s, v in d["gained"].items():
            print(f"      +{v['arm'] - v['control']} {s}  (control {v['control']} -> "
                  f"arm {v['arm']})")
        for site in d["added_sites"][:6]:
            print(f"      added at {site}")
        if len(d["added_sites"]) > 6:
            print(f"      ... {len(d['added_sites']) - 6} more added site(s) in the --json report")
    for r in rep["differing"]:
        why = f"explained: {r['explained']}" if r["explained"] else "UNEXPLAINED"
        print(f"DIFF  {r['name']}  lines {r['control_lines']} -> {r['arm_lines']}  [{why}]")
        if show_diff:
            a = [t for _, t in _lines(ctl[r["name"]][0])]
            b = [t for _, t in _lines(arm[r["name"]][0])]
            for ln in list(difflib.unified_diff(a, b, lineterm="", n=2))[2:202]:
                print(f"      {ln}")
    for side, key in (("CONTROL", "only_in_control"), ("ARM", "only_in_arm")):
        for n in rep[key]:
            tag = "explained" if n not in rep["unexplained"] else "UNEXPLAINED"
            print(f"ONLY-{side}  {n}  [{tag}]")
    for n, refs in rep["only_in_arm_drop_refs"].items():
        print(f"      only-in-arm {n} references {', '.join(f'{s} x{c}' for s, c in refs.items())}")
    for n in rep["explanation_ignored_for_drop"]:
        print(f"IGNORED-EXPLANATION  {n}  (a gained drop is never explainable)")
    for n in rep["stale_explanations"]:
        print(f"STALE-EXPLANATION  {n}  (does not differ; delete the entry)")
    print(f"VERDICT={rep['verdict']} exit={rep['exit_code']} "
          f"drop_gained={len(rep['drop_findings'])} unexplained={len(rep['unexplained'])} "
          f"stale_explanations={len(rep['stale_explanations'])}")


def run(args) -> int:
    t0 = time.time()
    tool = objdump_tool(args.objdump)
    explained = load_explained(args.explained)
    cache = Path(args.cache_dir) if args.cache_dir else None
    if cache is not None:
        cache.mkdir(parents=True, exist_ok=True)
    inputs = {"control": collect_objects(Path(args.control)),
              "arm": collect_objects(Path(args.arm))}
    print(f"CRYSTAL_OBJECT_BURNIN control={args.control} arm={args.arm}")
    print(f"  objdump: {tool['version']} ({tool['path']}) args: {' '.join(OBJDUMP_ARGS)}")
    members, blobs = [], {}
    objects: dict = {"control": [], "arm": []}
    for side, objs in inputs.items():
        for label, data in objs:
            sha, code = hashlib.sha256(data).hexdigest(), code_bytes(data)
            if code == 0:
                objects[side].append({"label": label, "sha256": sha, "bytes": len(data),
                                      "code_bytes": 0, "functions": 0,
                                      "skipped": "no executable section"})
                print(f"  {side}: {label}  sha256:{sha}  no executable section -- skipped")
                continue
            members.append((side, label, sha, len(data), code))
            blobs[sha] = data
        if not any(m[0] == side for m in members):
            raise Refused(f"{side} has no object with an executable section")
    inputs = None
    shas = sorted(blobs)
    with tempfile.TemporaryDirectory(prefix="crystal-object-burnin-") as tmp:
        work = Path(tmp)
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(4, len(shas))) as ex:
            dis = dict(zip(shas, ex.map(
                lambda h: disassemble(h, blobs[h], tool, cache, work), shas)))
        blobs = None
        with concurrent.futures.ProcessPoolExecutor(max_workers=min(4, len(shas))) as ex:
            parsed = dict(zip(shas, ex.map(_parse_file, [dis[h]["text"] for h in shas],
                                           [f"sha256:{h[:16]}" for h in shas])))
    by_side: dict = {"control": [], "arm": []}
    fmts = set()
    for side, label, sha, size, code in members:
        rows, fmt = parsed[sha]
        if not rows:
            raise Refused(f"{label} parsed to ZERO functions -- an empty comparison is "
                          f"not a pass")
        check_format(label, fmt)
        fmts.add(fmt)
        by_side[side].append([Fn(n, label, st, nl, dg, dr, bl)
                              for n, _, st, nl, dg, dr, bl in rows])
        objects[side].append({"label": label, "sha256": sha, "bytes": size,
                              "code_bytes": code, "functions": len(rows), "format": fmt,
                              "cache": dis[sha]["cache"]})
        print(f"  {side}: {label}  sha256:{sha}  {len(rows)} functions  "
              f"[{fmt}; objdump cache {dis[sha]['cache']}]")
    ctl, arm = load_side(by_side["control"]), load_side(by_side["arm"])
    rep = compare(ctl, arm, explained)
    names = sorted({d["name"] for d in rep["drop_findings"]}
                   | {r["name"] for r in rep["differing"]} | set(rep["only_in_control"])
                   | set(rep["only_in_arm"])
                   | {s for d in rep["drop_findings"] for s in d["gained"]})
    dm = {} if args.no_demangle else demangle(names, " ".join(sorted(fmts)))
    print_report(rep, dm, ctl, arm, args.show_diff)
    print(f"  elapsed {time.time() - t0:.1f}s")
    if args.json:
        script = Path(__file__).resolve()
        doc = {"schema": SCHEMA, "script": "scripts/crystal_object_burnin.py",
               "script_sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
               "control": str(args.control), "arm": str(args.arm),
               "explained_file": str(args.explained) if args.explained else None,
               "objdump": {k: v for k, v in tool.items() if k != "key"} | {
                   "args": list(OBJDUMP_ARGS)},
               "objects": objects, "demangled": dm, **rep}
        Path(args.json).write_text(json.dumps(doc, indent=1, sort_keys=False) + "\n")
    return rep["exit_code"]


# ── self-test ────────────────────────────────────────────────────────────────

_CTL = """\
/tmp/x/a.o:\tfile format mach-o arm64

Disassembly of section __TEXT,__text:

0000000000000000 <ltmp0>:
       0:      \tstp\tx29, x30, [sp, #-0x10]!
       4:      \tadrp\tx0, 0x0 <ltmp0>
\t\t0000000000000004:  ARM64_RELOC_PAGE21\tl_anon.00112233445566778899aabbccddeeff.7
       8:      \tadd\tx0, x0, #0x0
\t\t0000000000000008:  ARM64_RELOC_PAGEOFF12\tl_anon.00112233445566778899aabbccddeeff.7
       c:      \tbl\t0xc <ltmp0+0xc>
\t\t000000000000000c:  ARM64_RELOC_BRANCH26\t__RNvCs1ab_4demo6helper
      10:      \tadrp\tx1, 0x0 <ltmp0>
\t\t0000000000000010:  ARM64_RELOC_PAGE21\tlCPI5_0
      11:      \tldr\tq0, [x1]
\t\t0000000000000011:  ARM64_RELOC_PAGEOFF12\tlCPI5_0
      12:      \tadrp\tx2, 0x0 <ltmp0>
\t\t0000000000000012:  ARM64_RELOC_ADDEND\t0x10
\t\t0000000000000012:  ARM64_RELOC_PAGE21\tltmp3
      13:      \tldp\tx29, x30, [sp], #0x10
      14:      \tret

0000000000000018 <__RNvMNtCs1ab_4demo5inferNtB2_11TypeChecker10infer_type>:
      18:      \tsub\tsp, sp, #0x40
      1c:      \tcmn\tx8, #0x1
      20:      \tb.eq\t0x30 <__RNvMNtCs1ab_4demo5inferNtB2_11TypeChecker10infer_type+0x18>
      24:      \tadrp\tx9, 0x0 <ltmp0>
\t\t0000000000000024:  ARM64_RELOC_ADDEND\t0x50
\t\t0000000000000024:  ARM64_RELOC_PAGE21\t__RNvCs1ab_4demo8REGISTRY
      28:      \tbl\t0x28 <__RNvMNtCs1ab_4demo5inferNtB2_11TypeChecker10infer_type+0x10>
\t\t0000000000000028:  ARM64_RELOC_BRANCH26\t__RNvCs1ab_4demo13from_residual
      2c:      \tadd\tsp, sp, #0x40
      30:      \tret
"""
_DROP = ("      2a:      \tmov\tx0, sp\n      2b:      \tbl\t0x2b <__RNvMNtCs1ab_4demo5inferNtB2_"
         "11TypeChecker10infer_type+0x13>\n\t\t000000000000002b:  ARM64_RELOC_BRANCH26\t"
         "{sym}\n")
_GLUE = "__RINvNtCs9xy_4core3ptr9drop_glueNtCs1ab_4demo9TypeErrorE"
_INFER = "__RNvMNtCs1ab_4demo5inferNtB2_11TypeChecker10infer_type"
_NEW_FN = "\n0000000000000040 <__RNvCs1ab_4demo7new_one>:\n      40:      \tret\n"
_OUT = """
0000000000000060 <_OUTLINED_FUNCTION_0>:
      60:      \tmov\tx0, x19
      64:      \tret

0000000000000068 <__RNvCs1ab_4demo6caller>:
      68:      \tbl\t0x68 <__RNvCs1ab_4demo6caller>
\t\t0000000000000068:  ARM64_RELOC_BRANCH26\t_OUTLINED_FUNCTION_0
      6c:      \tret
"""
# review 2026-09-23: shapes the first arms did not reach. Measured against the
# pre-review script (sha256 1206bbea...): the nine new FAIL-expected arms from
# drop_slow through the alias arm each exited 0 there, and the BRANCH26 against
# `ltmp0` was not refused.
_ARC_SLOW = "__RNvMsd_NtCsdP_5alloc4syncINtB5_3ArcNtNtCs1ab_4demo4expr4ExprE9drop_slowB9_"
_DROP_IMPL = "__RNvXs0_NtCs1ab_4demo4certNtB5_9ProofCertNtNtNtCs9xy_4core3ops4drop4Drop4drop"
_DROP_IMPL_LEGACY = ("__ZN60_$LT$demo..ProofCert$u20$as$u20$core..ops..drop..Drop$GT$4drop"
                     "17h00aa11bb22cc33ddE")
_DEALLOCATE = "__RNvXs_NtCs6h_5alloc5allocNtB4_6GlobalNtNtCs9xy_4core5alloc9Allocator10deallocate"
_THUNKS = f"""
0000000000000080 <_OUTLINED_FUNCTION_0>:
      80:      \tmov\tx0, x19
      84:      \tb\t0x84 <_OUTLINED_FUNCTION_0>
\t\t0000000000000084:  ARM64_RELOC_BRANCH26\t{_GLUE}

0000000000000088 <__RNvCs1ab_4demo7discard>:
      88:      \tb\t0x88 <__RNvCs1ab_4demo7discard>
\t\t0000000000000088:  ARM64_RELOC_BRANCH26\t{_GLUE}

000000000000008a <__RNvCs1ab_4demo8discard2>:
      8a:      \tb\t0x8a <__RNvCs1ab_4demo8discard2>
\t\t000000000000008a:  ARM64_RELOC_BRANCH26\t__RNvCs1ab_4demo7discard

000000000000008c <__RNvCs1ab_4demo5other>:
      8c:      \tbl\t0x8c <__RNvCs1ab_4demo5other>
\t\t000000000000008c:  ARM64_RELOC_BRANCH26\t_OUTLINED_FUNCTION_0
      90:      \tbl\t0x90 <__RNvCs1ab_4demo5other+0x4>
\t\t0000000000000090:  ARM64_RELOC_BRANCH26\t__RNvCs1ab_4demo7discard
      94:      \tret
"""
_HELPER = f"""
00000000000000a0 <__RNvCs1ab_4demo10new_helper>:
      a0:      \tmov\tx0, x19
      a4:      \tbl\t0xa4 <__RNvCs1ab_4demo10new_helper+0x4>
\t\t00000000000000a4:  ARM64_RELOC_BRANCH26\t{_GLUE}
      a8:      \tret
"""
_SIBLING = _HELPER.replace("10new_helper", "7sibling")
_WITHOUT_INFER = _CTL.split(f"\n0000000000000018 <{_INFER}>:")[0] + "\n"
# merge-functions made infer_type an ALIAS of a sibling that drops: two headers, one body
_ALIASED = _WITHOUT_INFER + f"\n00000000000000a0 <{_INFER}>:" + _SIBLING
_HDR = f"\n0000000000000018 <{_INFER}>:"
_EMPTY = "\n0000000000000016 <__RNvCs1ab_4demo5empty>:"
_LTMP_CALL = ("      2b:      \tbl\t0x2b <" + _INFER + "+0x13>\n"
              "\t\t000000000000002b:  ARM64_RELOC_ADDEND\t0x88\n"
              "\t\t000000000000002b:  ARM64_RELOC_BRANCH26\tltmp0\n")


def _after_residual(text: str, extra: str) -> str:
    anchor = "ARM64_RELOC_BRANCH26\t__RNvCs1ab_4demo13from_residual\n"
    assert anchor in text
    return text.replace(anchor, anchor + extra)


def _texts_compare(ctl: list, arm: list, explained: dict) -> dict:
    def side(texts):
        fns = []
        for i, t in enumerate(texts):
            parsed, _ = parse_objdump(io.StringIO(t), f"obj{i}")
            if not parsed:
                raise Refused(f"obj{i} parsed to ZERO functions")
            fns.append(parsed)
        return load_side(fns)
    return compare(side(ctl), side(arm), explained)


def selftest() -> int:
    # every layout artefact at once: anon hash AND index, constant-pool index,
    # a layout-local addend, and an adrp page operand naming another symbol
    moved = (_CTL.replace("00112233445566778899aabbccddeeff.7", "ffeeddccbbaa99887766554433221100.9")
             .replace("lCPI5_0", "lCPI4_0").replace("ADDEND\t0x10", "ADDEND\t0x20")
             .replace("adrp\tx0, 0x0 <ltmp0>", "adrp\tx0, 0x4000 <__RNvCs1ab_4demo3foo+0x24>"))
    for probe in ("ffeeddcc", "lCPI4_0", "ADDEND\t0x20", "0x4000 <"):
        assert probe in moved, probe  # a no-op substitution would make the arm vacuous
    wider = _CTL.replace("sub\tsp, sp, #0x40", "sub\tsp, sp, #0x50")
    arms = [
        # (name, control texts, arm texts, explained, expected exit, extra predicate)
        ("identical inputs pass", [_CTL], [_CTL], {}, EXIT_PASS, None),
        ("renumbered anon label + moved adrp page pass (normalisation)",
         [_CTL], [moved], {}, EXIT_PASS, None),
        ("added drop_glue relocation FAILS and names infer_type",
         [_CTL], [_after_residual(_CTL, _DROP.format(sym=_GLUE))], {}, EXIT_FAIL,
         lambda r: [d["name"] for d in r["drop_findings"]] == [_INFER]
         and r["drop_findings"][0]["gained"] == {_GLUE: {"control": 0, "arm": 1}}
         and any(_GLUE in s for s in r["drop_findings"][0]["added_sites"])),
        # ThinLTO promotes a local symbol referenced from another codegen unit as
        # `<name>.llvm.<module hash>`; the hash is the DEFINING module's, so an arm whose
        # partitioning moved that module renames the callee without changing a single
        # call (measured on the cu=16 clean-kernel pair, 2026-09-24: 2 calls to
        # `drop_glue<Level>.llvm.5746...` became 2 to `drop_glue<Level>.llvm.1364...`)
        ("a ThinLTO promotion-suffix rename of a drop callee passes (normalisation)",
         [_after_residual(_CTL, _DROP.format(sym=_GLUE + ".llvm.5746798428916379799"))],
         [_after_residual(_CTL, _DROP.format(sym=_GLUE + ".llvm.13649391023793296500"))],
         {}, EXIT_PASS, lambda r: not r["drop_findings"] and not r["differing"]),
        ("a GAINED call to a promoted drop callee still FAILS",
         [_CTL], [_after_residual(_CTL, _DROP.format(sym=_GLUE + ".llvm.13649391023793296500"))],
         {_INFER: "x"}, EXIT_FAIL,
         lambda r: r["drop_findings"][0]["gained"] == {_GLUE + ".llvm.P": {"control": 0, "arm": 1}}),
        ("an explanation does NOT suppress a gained drop",
         [_CTL], [_after_residual(_CTL, _DROP.format(sym=_GLUE))], {_INFER: "reviewed"},
         EXIT_FAIL, lambda r: r["explanation_ignored_for_drop"] == [_INFER]),
        ("added __rust_dealloc call FAILS",
         [_CTL], [_after_residual(_CTL, _DROP.format(
             sym="__RNvCskZ_7___rustc14___rust_dealloc"))], {}, EXIT_FAIL,
         lambda r: len(r["drop_findings"]) == 1),
        ("added legacy-mangled drop_in_place FAILS",
         [_CTL], [_after_residual(_CTL, _DROP.format(
             sym="__ZN4core3ptr42drop_in_place$LT$demo..TypeError$GT$17h00aa11bb22cc33ddE"))],
         {}, EXIT_FAIL, lambda r: len(r["drop_findings"]) == 1),
        ("explained non-drop difference passes",
         [_CTL], [wider], {_INFER: "frame grew; reviewed"}, EXIT_PASS,
         lambda r: len(r["differing"]) == 1 and not r["unexplained"]),
        ("unexplained non-drop difference FAILS",
         [_CTL], [wider], {}, EXIT_FAIL, lambda r: r["unexplained"] == [_INFER]),
        ("global ADDEND change is a difference",
         [_CTL], [_CTL.replace("ADDEND\t0x50", "ADDEND\t0x58")], {}, EXIT_FAIL,
         lambda r: r["unexplained"] == [_INFER]),
        ("only-in-arm function unexplained FAILS", [_CTL], [_CTL + _NEW_FN], {}, EXIT_FAIL,
         lambda r: r["only_in_arm"] == ["__RNvCs1ab_4demo7new_one"]),
        ("only-in-arm function explained passes", [_CTL], [_CTL + _NEW_FN],
         {"__RNvCs1ab_4demo7new_one": "new helper"}, EXIT_PASS, None),
        ("stale explanation FAILS", [_CTL], [_CTL], {_INFER: "old"}, EXIT_FAIL,
         lambda r: r["stale_explanations"] == [_INFER]),
        ("a duplicated identical copy in another object passes", [_CTL], [_CTL, _CTL], {},
         EXIT_PASS, None),
        ("a renumbered machine-outlined body passes",
         [_CTL + _OUT], [_CTL + _OUT.replace("_OUTLINED_FUNCTION_0", "_OUTLINED_FUNCTION_3")],
         {}, EXIT_PASS, None),
        ("a changed machine-outlined body FAILS at its caller",
         [_CTL + _OUT], [_CTL + _OUT.replace("mov\tx0, x19", "mov\tx0, x20")], {}, EXIT_FAIL,
         lambda r: "__RNvCs1ab_4demo6caller" in r["unexplained"]
         and len(r["only_in_arm"]) == 1 and len(r["only_in_control"]) == 1),
        # a body that ALREADY drops once, duplicated into a second codegen unit
        # whose copy differs in its frame only: the unpaired new copy is held to
        # the control's largest count, 1 -> 1, so no drop was gained; a SUM over
        # copies would read 1 -> 2 and cry wolf
        ("a differing duplicate with the same drop count is not a gained drop",
         [_after_residual(_CTL, _DROP.format(sym=_GLUE))],
         [_after_residual(_CTL, _DROP.format(sym=_GLUE)),
          _after_residual(wider, _DROP.format(sym=_GLUE))],
         {_INFER: "frame grew in a second codegen unit"}, EXIT_PASS,
         lambda r: not r["drop_findings"] and len(r["differing"]) == 1),
        # ── review 2026-09-23: each of these PASSED, explained, before the review
        ("a gained Arc::<T>::drop_slow call (an inlined Arc drop) FAILS even explained",
         [_CTL], [_after_residual(_CTL, _DROP.format(sym=_ARC_SLOW))], {_INFER: "x"},
         EXIT_FAIL, lambda r: [d["name"] for d in r["drop_findings"]] == [_INFER]),
        ("a gained <T as Drop>::drop call FAILS even explained, v0 and legacy",
         [_CTL, _CTL], [_after_residual(_CTL, _DROP.format(sym=_DROP_IMPL)),
                        _after_residual(_CTL, _DROP.format(sym=_DROP_IMPL_LEGACY))],
         {_INFER: "x"}, EXIT_FAIL,
         lambda r: set(r["drop_findings"][0]["gained"]) == {_DROP_IMPL, _DROP_IMPL_LEGACY}),
        ("a gained Allocator::deallocate call (the O0 shape) FAILS even explained",
         [_CTL], [_after_residual(_CTL, _DROP.format(sym=_DEALLOCATE))], {_INFER: "x"},
         EXIT_FAIL, lambda r: len(r["drop_findings"]) == 1),
        ("a call into an UNCHANGED outlined body that drops FAILS at the caller",
         [_CTL + _THUNKS],
         [_after_residual(_CTL, _DROP.format(sym="_OUTLINED_FUNCTION_0")) + _THUNKS],
         {_INFER: "x"}, EXIT_FAIL,
         lambda r: [d["name"] for d in r["drop_findings"]] == [_INFER]
         and r["drop_findings"][0]["gained"] == {_GLUE: {"control": 0, "arm": 1}}),
        ("a call into an UNCHANGED pure tail-call thunk to drop glue FAILS at the caller",
         [_CTL + _THUNKS],
         [_after_residual(_CTL, _DROP.format(sym="__RNvCs1ab_4demo7discard")) + _THUNKS],
         {_INFER: "x"}, EXIT_FAIL,
         lambda r: [d["name"] for d in r["drop_findings"]] == [_INFER]),
        ("a call into a CHAIN of two thunks ending in drop glue FAILS at the caller",
         [_CTL + _THUNKS],
         [_after_residual(_CTL, _DROP.format(sym="__RNvCs1ab_4demo8discard2")) + _THUNKS],
         {_INFER: "x"}, EXIT_FAIL,
         lambda r: [d["name"] for d in r["drop_findings"]] == [_INFER]
         and r["drop_findings"][0]["gained"] == {_GLUE: {"control": 0, "arm": 1}}),
        ("a NEW only-in-arm function that drops FAILS even with both halves explained",
         [_CTL],
         [_after_residual(_CTL, _DROP.format(sym="__RNvCs1ab_4demo10new_helper")) + _HELPER],
         {_INFER: "calls a new helper", "__RNvCs1ab_4demo10new_helper": "new"}, EXIT_FAIL,
         lambda r: [(d["name"], d.get("only_in_arm")) for d in r["drop_findings"]]
         == [("__RNvCs1ab_4demo10new_helper", True)]),
        ("one copy's 0 -> 1 gain is not masked by a sibling copy that drops twice",
         [_after_residual(_CTL, _DROP.format(sym=_GLUE) + _DROP.format(sym=_GLUE)), _CTL],
         [_after_residual(_CTL, _DROP.format(sym=_GLUE) + _DROP.format(sym=_GLUE)),
          _after_residual(wider, _DROP.format(sym=_GLUE))],
         {_INFER: "x"}, EXIT_FAIL,
         lambda r: r["drop_findings"][0]["gained"] == {_GLUE: {"control": 0, "arm": 1}}),
        ("identical copies cancel first: a new copy is held to the largest control copy",
         [_CTL, _after_residual(_CTL, _DROP.format(sym=_GLUE) + _DROP.format(sym=_GLUE))],
         [_CTL, _after_residual(_CTL, _DROP.format(sym=_GLUE) + _DROP.format(sym=_GLUE)),
          _after_residual(wider, _DROP.format(sym=_GLUE))],
         {_INFER: "a third codegen unit"}, EXIT_PASS, lambda r: not r["drop_findings"]),
        ("a function merged as an ALIAS of a dropping sibling FAILS under its own name",
         [_CTL + _SIBLING], [_ALIASED], {_INFER: "merged"}, EXIT_FAIL,
         lambda r: [d["name"] for d in r["drop_findings"]] == [_INFER]),
        ("the same alias group on both sides passes, every name compared",
         [_ALIASED], [_ALIASED], {}, EXIT_PASS,
         lambda r: r["common"] == 3),
        ("a bodiless header at a DIFFERENT address does not inherit the next body",
         [_CTL.replace(_HDR, _EMPTY + _HDR)],
         [_after_residual(_CTL, _DROP.format(sym=_GLUE)).replace(_HDR, _EMPTY + _HDR)],
         {_INFER: "x"}, EXIT_FAIL,
         lambda r: [d["name"] for d in r["drop_findings"]] == [_INFER] and r["common"] == 3),
        ("a drop_glue BRANCH26 behind an ARM64_RELOC_ADDEND line FAILS",
         [_CTL], [_after_residual(_CTL, _DROP.format(sym=_GLUE).replace(
             "\t\t000000000000002b:  ARM64_RELOC_BRANCH26",
             "\t\t000000000000002b:  ARM64_RELOC_ADDEND\t0x10\n"
             "\t\t000000000000002b:  ARM64_RELOC_BRANCH26"))], {_INFER: "x"}, EXIT_FAIL,
         lambda r: r["drop_findings"][0]["gained"] == {_GLUE: {"control": 0, "arm": 1}}),
        ("a drop gained in a function whose header name holds '<' FAILS",
         [_CTL.replace(_INFER, _INFER + "<u8>")],
         [_after_residual(_CTL, _DROP.format(sym=_GLUE)).replace(_INFER, _INFER + "<u8>")],
         {_INFER + "<u8>": "x"}, EXIT_FAIL,
         lambda r: [d["name"] for d in r["drop_findings"]] == [_INFER + "<u8>"]),
    ]
    failed = []
    for name, c, a, ex, want, pred in arms:
        try:
            rep = _texts_compare(c, a, ex)
            ok = rep["exit_code"] == want and (pred is None or pred(rep))
        except Exception as exc:  # noqa: BLE001 -- an arm that raises is a failed arm
            ok, rep = False, {"exception": repr(exc)}
        if not ok:
            failed.append(f"{name}: got {rep.get('exit_code', rep)}")
    # refusals: empty text, a call whose callee is a layout-local label, and the
    # ar reader choosing members by magic
    try:
        _texts_compare(["garbage\n"], [_CTL], {})
        failed.append("empty parse was not refused")
    except Refused:
        pass
    try:
        _texts_compare([_CTL], [_after_residual(_CTL, _LTMP_CALL)], {_INFER: "x"})
        failed.append("a BRANCH26 against a layout-local label was not refused")
    except Refused:
        pass
    obj = b"\xcf\xfa\xed\xfe" + b"\0" * 12
    rmeta = b"rust metadata!"
    ar = b"!<arch>\n"
    for n, body in (("#1/12", b"a-cgu.0.o\0\0\0" + obj), ("lib.rmeta/", rmeta)):
        ar += n.ljust(16).encode() + b"0".ljust(12) + b"0".ljust(6) + b"0".ljust(6) \
            + b"644".ljust(8) + str(len(body)).ljust(10).encode() + b"`\n" + body \
            + (b"\n" if len(body) & 1 else b"")
    with tempfile.TemporaryDirectory() as tmp:
        p = Path(tmp) / "libx.rlib"
        p.write_bytes(ar)
        got = collect_objects(p)
        if [(n, b) for n, b in got] != [("libx.rlib(a-cgu.0.o)", obj)]:
            failed.append(f"ar reader chose {[n for n, _ in got]}")
    # code_bytes: a metadata-only Mach-O is code-free, a __text-bearing one is not
    def macho(flags: int, size: int) -> bytes:
        sect = (b"__text".ljust(16, b"\0") + b"__TEXT".ljust(16, b"\0")
                + struct.pack("<QQIIIIIIII", 0, size, 0, 0, 0, 0, flags, 0, 0, 0))
        seg = struct.pack("<II16sQQQQiiII", 0x19, 72 + len(sect), b"", 0, 0, 0, 0, 7, 7, 1, 0)
        return struct.pack("<IiiIIIII", 0xFEEDFACF, 0, 0, 1, 1, len(seg + sect), 0, 0) \
            + seg + sect
    if (code_bytes(macho(0x80000400, 0x40)), code_bytes(macho(0, 0x40))) != (0x40, 0):
        failed.append("code_bytes misread section flags")
    # the format guard, and objdump asked for EVERY name at an address
    for fmt in ("elf64-littleaarch64", "mach-o 64-bit x86-64", ""):
        try:
            check_format("x.o", fmt)
            failed.append(f"format {fmt!r} was not refused")
        except Refused:
            pass
    check_format("x.o", MEASURED_FORMAT)
    if "--show-all-symbols" not in OBJDUMP_ARGS:
        failed.append("objdump would print one name per address: aliases go uncompared")
    total = len(arms) + 6
    print(f"CRYSTAL_OBJECT_BURNIN_SELFTEST arms={total} passed={total - len(failed)}")
    for f in failed:
        print(f"  FAILED ARM: {f}")
    return EXIT_FAIL if failed else EXIT_PASS


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("control", nargs="?", help=".rlib/ar archive, object file, or dir of objects")
    ap.add_argument("arm", nargs="?", help="same, for the arm under test")
    ap.add_argument("--explained", type=Path, help="JSON object: function name -> reason")
    ap.add_argument("--json", help="write a machine-readable report here")
    ap.add_argument("--cache-dir", help="cache objdump text by object content sha256")
    ap.add_argument("--objdump", default=os.environ.get("OBJDUMP", "objdump"))
    ap.add_argument("--show-diff", action="store_true", help="print normalised diffs")
    ap.add_argument("--no-demangle", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    if not args.control or not args.arm:
        ap.error("CONTROL and ARM are required (or --selftest)")
    try:
        return run(args)
    except (Refused, OSError) as exc:
        print(f"CRYSTAL_OBJECT_BURNIN refused: {exc}")
        print(f"VERDICT=refused exit={EXIT_REFUSED}")
        return EXIT_REFUSED


if __name__ == "__main__":
    sys.exit(main())
