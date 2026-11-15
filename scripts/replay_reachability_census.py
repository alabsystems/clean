#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Compare the linker's reachability of the dependency-closed replay with the
source census in crates/clean-olean/src/recheck_closed/by_name_census_tests.rs.

Inputs:
  1. demangled symbols of `examples/replay_reachability_probe` (a binary that
     calls only `recheck_closed`, unoptimised, dead code stripped), one per
     line, `rustc_demangle` alternate form;
  2. the census dump written by the test under CLEAN_BY_NAME_CENSUS_DUMP
     (`reached<TAB>kind<TAB>owner<TAB>name<TAB>file`, every item it found).

Every kernel function or static the LINKER keeps whose source item the census
found must be one the census REACHED; otherwise the census under-approximates
and its verdict is vacuous for what it missed. Exit 1 and list them if any is
missing. Linker items with no source item at all (`#[derive]` output, std
blanket impls monomorphised at a kernel type, closures, enum-variant
constructors) are counted separately: they are generated from a definition and
hold no string literal of their own.
"""
import re
import sys
from collections import defaultdict

IDENT = r"[A-Za-z_][A-Za-z0-9_]*"


def parse_path(s, i):
    """Parse `seg(::seg)*` starting at i, skipping `<...>` after a segment.
    Returns (segments, end index)."""
    segs = []
    while True:
        m = re.compile(IDENT).match(s, i)
        if not m:
            break
        segs.append(m.group(0))
        i = m.end()
        if s.startswith("<", i):
            depth = 0
            while i < len(s):
                if s[i] == "<":
                    depth += 1
                elif s[i] == ">":
                    depth -= 1
                    if depth == 0:
                        i += 1
                        break
                i += 1
        if s.startswith("::", i) and re.compile(IDENT).match(s, i + 2):
            i += 2
            continue
        break
    return segs, i


def skip_to_close(s, i):
    """i is just after a '<'; return index just after its matching '>'."""
    depth = 1
    while i < len(s) and depth:
        if s[i] == "<":
            depth += 1
        elif s[i] == ">":
            depth -= 1
        i += 1
    return i


def items_of(sym):
    """Yield ('method', owner, name) / ('trait-method', trait, name) /
    ('free', modpath, name) / ('static', modpath, NAME) for every kernel item
    a symbol names (including inside generic arguments)."""
    for m in re.finditer(r"clean_kernel::", sym):
        start = m.start()
        segs, end = parse_path(sym, m.end())
        if not segs:
            continue
        if start > 0 and sym[start - 1] == "<":
            # <clean_kernel::path::Type [as Trait]>::method
            close = skip_to_close(sym, start)
            inner = sym[start:close - 1]
            after = re.compile(r"::(" + IDENT + ")").match(sym, close)
            if not after:
                continue
            owner = segs[-1]
            # The owner's path: a type declared inside a fn body (`fn f() {
            # struct S; impl T for S {…} }`) has that fn as its last module
            # segment, and is part of that fn's body.
            yield ("method", owner, after.group(1), "::".join(segs[:-1]))
            t = re.search(r" as ((?:" + IDENT + r"::)*)(" + IDENT + r")", inner)
            if t and t.group(1).startswith("clean_kernel::"):
                yield ("trait-method", t.group(2), after.group(1))
            continue
        last = segs[-1]
        if re.fullmatch(r"[A-Z][A-Z0-9_]+", last):
            yield ("static", "::".join(segs[:-1]), last)
        elif last[0].islower():
            yield ("free", "::".join(segs[:-1]), last)


def main():
    syms = [l.rstrip("\n") for l in open(sys.argv[1]) if "clean_kernel" in l]
    rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[2]) if l.strip()]
    # (owner, name) -> reached?  and  name -> [(file, reached)] for free fns.
    methods = defaultdict(bool)
    free = defaultdict(list)
    statics = defaultdict(list)
    traits_of_name = defaultdict(set)
    for reached, kind, owner, name, file in rows:
        r = reached == "1"
        if kind == "fn" and owner != "-":
            methods[(owner, name)] |= r
            traits_of_name[name].add(owner)
        elif kind == "fn":
            free[name].append((file, r))
        elif kind == "static":
            statics[name].append((file, r))

    modules = set()
    for row in rows:
        f = row[4]
        stem = f[:-len("/mod.rs")] if f.endswith("/mod.rs") else f[:-len(".rs")]
        modules.add(stem)
        # every ancestor directory is a module too
        parts = stem.split("/")
        for k in range(1, len(parts)):
            modules.add("/".join(parts[:k]))

    def in_module(file, path):
        cands = set()
        for k in range(len(path), 0, -1):
            p = "/".join(path[:k])
            cands.update({p + ".rs", p + "/mod.rs"})
        return file in cands or (not path and file == "lib.rs")

    missing, no_source, seen = [], set(), set()
    for sym in syms:
        for item in items_of(sym):
            if item in seen:
                continue
            seen.add(item)
            kind, a, b = item[:3]
            if kind == "trait-method":
                continue
            if kind == "method" and re.fullmatch(r"[A-Z][A-Z0-9_]+", a):
                kind, a, b = "static", "", a
            if kind == "method":
                if (a, b) in methods:
                    if not methods[(a, b)]:
                        missing.append(item)
                    continue
                # Not defined on the type itself: a kernel trait's default
                # body, named in the same symbol as `<Type as Trait>::m`.
                defaults = [it2[1] for it2 in items_of(sym)
                            if it2[0] == "trait-method" and it2[2] == b and (it2[1], b) in methods]
                if defaults:
                    if not any(methods[(t, b)] for t in defaults):
                        missing.append(item)
                    continue
                # A type local to a fn body: the owner path's last segment
                # is that fn, not a module file.
                owner_path = item[3].split("::") if item[3] else []
                if owner_path and "/".join(owner_path) not in modules:
                    fn = owner_path[-1]
                    parent_hits = [r for _, r in free.get(fn, [])] + [
                        r for (_, m), r in methods.items() if m == fn]
                    if parent_hits:
                        if not any(parent_hits):
                            missing.append(item)
                        continue
                no_source.add(item)
            elif kind == "free":
                path = a.split("::")
                hits = [r for f, r in free.get(b, []) if in_module(f, path)]
                if hits:
                    if not any(hits):
                        missing.append(item)
                    continue
                # A fn nested inside another fn: its parent is the path's
                # last segment, and the parent's body is scanned whole.
                parent = path[-1] if path else ""
                parent_hits = [r for f, r in free.get(parent, []) if in_module(f, path[:-1])]
                if parent_hits:
                    if not any(parent_hits):
                        missing.append(item)
                    continue
                # A `#[path]` module maps to a file its module path does not
                # name: fall back to every free fn of that name.
                if b in free:
                    if not any(r for _, r in free[b]):
                        missing.append(item)
                    continue
                no_source.add(item)
            elif kind == "static":
                hits = [r for f, r in statics.get(b, [])]
                if hits:
                    if not any(hits):
                        missing.append(item)
                    continue
                # A static declared inside a fn body is part of that body.
                parent = a.split("::")[-1] if a else ""
                parent_hits = [r for f, r in free.get(parent, [])]
                if parent_hits:
                    if not any(parent_hits):
                        missing.append(item)
                    continue
                no_source.add(item)
    print(f"linker kernel items: {len(seen)}")
    print(f"census rows: {len(rows)}; reached: {sum(1 for r in rows if r[0] == '1')}")
    print(f"linker items with no source item (derives, std blanket impls, closures, "
          f"enum constructors): {len(no_source)}")
    print(f"linker items whose source item the census did NOT reach: {len(missing)}")
    for m in sorted(missing):
        print("  MISSING", *m)
    if "-v" in sys.argv:
        for m in sorted(no_source):
            print("  NOSOURCE", *m)
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
