#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The explicit-prefix spelling of a generated EvalIR proof source.

Since 1b6b65dc83 the committed EvalIR proof sources name some heads with an
explicit `@` (`@Eq T a b`, `@IROption.some T x`, `@Nat.rec motive z s`), so the
ordinary elaborator receives every argument, implicit ones included, in its own
slot. The generators that own those sources (gen_lzb_activation,
gen_lzd_activation, gen_lzd_sctr, gen_slot_lemmas) build their terms without the
prefix, and that `@`-free text is what their self-tests pin: digests of terms a
kernel accepted. `respell` is the one step between the two. It inserts `@` in
front of each occurrence of a declared head and changes nothing else, so the
printed text with every `@` removed is the generator's own term byte for byte,
and each generator's `--check` holds the committed source to the printed text
byte for byte.

This is untrusted source spelling, as gen_it_sctr's private printer is: the
EvalIR initializer still elaborates and kernel-checks every printed declaration.
Which heads take the prefix is the committed source's choice. A generator
declares the set, and a const whose committed source keeps a head bare names it
in that generator's exception table, so the printer decides nothing. It judges
no arity either: `@Nat.rec motive z s` is a partial application the sources
carry.

Loaded by the generators with importlib, as gen_lzd_sctr loads
gen_lzd_activation. `python3 scripts/explicit_prefix.py --self-test` runs the
arms below on their own; every generator's `--self-test` runs them too.
"""
from __future__ import annotations

import re
import sys

NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*")


def respell(source: str, heads) -> str:
    """`source` with `@` before every occurrence of a name in `heads`.

    An occurrence is the whole dotted name: not preceded by a name character or
    a dot (so `Other.Eq` is not `Eq`) and not followed by one (so `Eq.trans` and
    `EqX` are not `Eq`). Refuses non-ASCII source, source that already carries a
    prefix, and a head that is not a constant name.
    """
    if not source.isascii():
        raise ValueError("explicit-prefix printer: the source is not ASCII")
    if "@" in source:
        raise ValueError(
            "explicit-prefix printer: the source already carries an explicit prefix; "
            "a generator builds the @-free term and this step adds every prefix"
        )
    names = sorted(set(heads), key=len, reverse=True)
    for head in names:
        if not NAME.fullmatch(head):
            raise ValueError(f"explicit-prefix printer: {head!r} is not a constant name")
    if not names:
        return source
    pattern = re.compile(
        r"(?<![A-Za-z0-9_.])(?:" + "|".join(re.escape(h) for h in names) + r")(?![A-Za-z0-9_.])"
    )
    printed = pattern.sub(lambda m: "@" + m.group(0), source)
    if printed.replace("@", "") != source:
        raise ValueError("explicit-prefix printer: the printed text is not the source plus prefixes")
    return printed


def self_test() -> list[str]:
    """Refusals, empty when every arm holds."""
    failures = []
    arms = [
        ("a foreign head that ends in a declared name",
         "def a : Type := Other.Eq Nat x y", {"Eq"}, "def a : Type := Other.Eq Nat x y"),
        ("a longer name that starts with a declared one",
         "def b : Type := Eq.trans h1 h2 (EqX y)", {"Eq"}, "def b : Type := Eq.trans h1 h2 (EqX y)"),
        ("nested applications of two heads",
         "def c : Type := Eq Nat (IRList.nil Nat) (IRList.nil Nat)", {"Eq", "IRList.nil"},
         "def c : Type := @Eq Nat (@IRList.nil Nat) (@IRList.nil Nat)"),
        ("a dotted head and its prefix name, each where it occurs",
         "def d : Eq T a b := Eq.trans T a b b h (Eq.refl T b)", {"Eq", "Eq.trans"},
         "def d : @Eq T a b := @Eq.trans T a b b h (Eq.refl T b)"),
        ("a partial application keeps its arguments",
         "def e := Nat.rec motive z s", {"Nat.rec"}, "def e := @Nat.rec motive z s"),
        ("no heads, no change", "def f := Eq T a b", set(), "def f := Eq T a b"),
    ]
    for label, source, heads, want in arms:
        try:
            got = respell(source, heads)
        except ValueError as exc:
            failures.append(f"explicit-prefix arm '{label}' refused: {exc}")
            continue
        if got != want:
            failures.append(f"explicit-prefix arm '{label}': printed {got!r}, wanted {want!r}")
    for label, source, heads in [
        ("source already prefixed", "def g := @Eq T a b", {"Eq"}),
        ("non-ASCII source", "def h := Eq T a β", {"Eq"}),
        ("a head that is not a name", "def i := Eq T a b", {"Eq trans"}),
    ]:
        try:
            respell(source, heads)
        except ValueError:
            continue
        failures.append(f"explicit-prefix printer accepted {label}")
    return failures


if __name__ == "__main__":
    if sys.argv[1:] != ["--self-test"]:
        print("usage: explicit_prefix.py --self-test", file=sys.stderr)
        sys.exit(2)
    problems = self_test()
    for line in problems:
        print(line)
    print("explicit_prefix --self-test: " + ("OK" if not problems else "FAILED"))
    sys.exit(1 if problems else 0)
