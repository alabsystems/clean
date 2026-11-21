#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Quote trust-cg e-graph rule files as `EqsatRule.Rule` literals (PKG-U2).

UNTRUSTED. This script is a convenience that writes the three generated modules
and the lemma table of this fixture family; nothing relies on it being right. trust-cg builds the
same literal in Rust from its checker's parsed rule and asks the kernel to
accept a lemma of this family for it, so a literal written wrongly here is a
kernel refusal there, never a proved rule.

It reads rule text in the five-clause grammar of trust-cg
`docs/eqsat-tier-e.md` section 5.1 and prints one `def NAME : EqsatRule.Rule`
per rule:

* variables are the rule's left-side variables, indexed by rank in the order
  of their names' bytes (the checker's `BTreeMap<String, VarInfo>`, which is
  the order a derivation's substitution uses);
* a variable is a constant variable when every left-side occurrence is
  `(const ?v)`; its sort is the sort of its position;
* `?v` is `Pat.var`, `(const ?v)` is `Pat.cvar`, as written (the checker's
  `Pat::Var` and `Pat::ConstVar`); `(const INT)` is `Pat.lit neg mag` with
  `-0` normalised to `lit false 0`; `(eval OP ?a ...)` is OP over `Pat.cvar`s.

Regenerate the modules from a trust-cg checkout (run from this directory):

    R=origin/main:crates/trust-cg-eqsat
    git -C ~/trust-cg show $R/rules/integer_identities.rules > /tmp/integer_identities.rules
    python3 gen_rule_defs.py --module EqsatIntRuleDefs --namespace Defs \\
        --source "trust-cg crates/trust-cg-eqsat/rules/integer_identities.rules" \\
        /tmp/integer_identities.rules > EqsatIntRuleDefs.lean

    mkdir -p /tmp/wrong_rules
    for f in missing_side_condition one_way_reversed panic_only_sdiv_neg_one \\
             panic_only_udiv_self wrong_boolean_constant wrong_constant wrong_fold \\
             wrong_operand_order wrong_select_arm wrong_width; do
        git -C ~/trust-cg show $R/tests/wrong_rules/$f.rules > /tmp/wrong_rules/$f.rules
    done
    python3 gen_rule_defs.py --module EqsatIntWrongRuleDefs --namespace WrongDefs \\
        --name-from-file --allow-partial-ops \\
        --source "trust-cg crates/trust-cg-eqsat/tests/wrong_rules/" \\
        /tmp/wrong_rules/*.rules > EqsatIntWrongRuleDefs.lean

    git -C ~/trust-cg show $R/rules/tier_s_integer.rules > /tmp/tier_s_integer.rules
    python3 gen_rule_defs.py --module EqsatTierSRuleDefs --namespace TierSDefs \\
        --source "trust-cg crates/trust-cg-eqsat/rules/tier_s_integer.rules" \\
        /tmp/tier_s_integer.rules > EqsatTierSRuleDefs.lean

`--check FILE` compares the output with FILE instead of printing it (add it to
any command above to verify a committed module against the rule text).
`--table` prints one `def-name direction kind domain` row per rule instead.
`--lemmas` prints the family's `LEMMAS` file instead: one
`rule scope kind lemma` row per rule and scope of the rule's domain, naming the
lemma that scope needs (README, "Lemma names and the record term").
`--also NAMESPACE SOURCE FILE` adds a further rule file to the table, with the
namespace its literals are generated in; its rows follow the first file's:

    python3 gen_rule_defs.py --module EqsatIntRuleDefs --namespace Defs \\
        --source "trust-cg crates/trust-cg-eqsat/rules/integer_identities.rules" \\
        --also TierSDefs "trust-cg crates/trust-cg-eqsat/rules/tier_s_integer.rules" \\
            /tmp/tier_s_integer.rules \\
        --lemmas /tmp/integer_identities.rules > LEMMAS

The table is keyed by rule name, in one lemma namespace, whatever the rule
file (trust-cg's registry reads it so). A rule name two rule files have gets
one row, and the script refuses it unless the files give that name one
literal, one kind and one domain: the row's lemma is stated on the first
file's literal, and it is then a proof of the later file's statement too.
Each rule file of a table is given once, under a namespace and a file name of
its own: a namespace given twice, and a file whose name or whose bytes are
those of another file of the table, are refused.

`python3 gen_rule_defs.py --self-test` runs the reader's own controls (what it
accepts and refuses beside the checker's tokenizer) and the command line's
(a table and a module written from two rule files in a temporary directory,
`--check` on each, and the command lines it refuses), and exits non-zero on a
difference.

Rule text is read as UTF-8, as the checker reads a `&str`: any character may
stand inside a `;` comment, and a character outside `0x21..0x7E` and the
checker's white space is refused outside one (section 5.1). Bytes that are
not UTF-8 are refused; they cannot reach the checker either.

Every index and literal is written `(nat_lit n)`: a raw `Nat` literal with no
`OfNat` instance, which is the term trust-cg's generator builds, so the two
literals are the same term and not merely definitionally equal.
"""

import argparse
import contextlib
import hashlib
import io
import os
import re
import sys
import tempfile

TYPES = ["i8", "i16", "i32", "i64", "i128", "isize",
         "u8", "u16", "u32", "u64", "u128", "usize", "bool"]
INT_TYPES = TYPES[:-1]

BIN = {"add": "add", "sub": "sub", "mul": "mul", "and": "and", "or": "or", "xor": "xor",
       "rotl": "rotl", "rotr": "rotr"}
BOOL_BIN = {"band": "bAnd", "bor": "bOr", "bxor": "bXor"}
# Not total: a rule file that names one is refused by the engine and the
# checker. `--allow-partial-ops` quotes them for the control set only.
PARTIAL_BIN = {"udiv": "udiv", "sdiv": "sdiv", "urem": "urem", "srem": "srem",
               "shl": "shl", "lshr": "lshr", "ashr": "ashr"}
UN = ["neg", "not", "ctpop", "ctlz", "cttz", "bswap", "bitreverse"]
PRED = ["eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge"]

MAX_DEPTH = 64

NAME = re.compile(r"[a-z][a-z0-9_]*\Z")
# A Lean namespace component, for `--namespace` and `--also`.
NAMESPACE = re.compile(r"[A-Z][A-Za-z0-9]*\Z")
INT = re.compile(r"-?[0-9]+\Z")


class Refused(Exception):
    pass


def tokenize(text):
    out = []
    i = 0
    while i < len(text):
        c = text[i]
        if c in " \t\r\n\x0c":
            i += 1
        elif c == ";":
            while i < len(text) and text[i] != "\n":
                i += 1
        elif c in "()":
            out.append(c)
            i += 1
        elif 0x21 <= ord(c) <= 0x7E:
            j = i
            while j < len(text) and 0x21 <= ord(text[j]) <= 0x7E and text[j] not in "();":
                j += 1
            out.append(text[i:j])
            i = j
        else:
            raise Refused(f"character U+{ord(c):04X} outside a comment")
    return out


def parse_forms(tokens):
    stack = [[]]
    for tok in tokens:
        if tok == "(":
            if len(stack) > MAX_DEPTH:
                raise Refused(f"nesting deeper than {MAX_DEPTH} lists is refused")
            stack.append([])
        elif tok == ")":
            if len(stack) < 2:
                raise Refused("unbalanced ')'")
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(tok)
    if len(stack) != 1:
        raise Refused("unbalanced '('")
    return stack[0]


def parse_int(tok):
    """(neg, mag) as the checker's `Int::parse` reads an INT."""
    neg = tok.startswith("-")
    mag = int(tok[1:] if neg else tok)
    if mag >= 1 << 128 or (neg and mag > 1 << 127):
        raise Refused(f"INT {tok} outside [-2^127, 2^128 - 1]")
    return (neg and mag != 0, mag)


def canonical(form):
    """Section 5.2 canonical text."""
    if isinstance(form, str):
        if INT.match(form):
            neg, mag = parse_int(form)
            return f"-{mag}" if neg else str(mag)
        return form
    return "(" + " ".join(canonical(f) for f in form) + ")"


def var_of(tok):
    if isinstance(tok, str) and tok.startswith("?") and NAME.match(tok[1:]):
        return tok[1:]
    return None


class Reader:
    def __init__(self, allow_partial):
        self.allow_partial = allow_partial

    def op(self, name):
        """(kind, SemR constructor, operand sorts, result sort)."""
        if name == "select":
            return ("sel", None, ["bool", "t", "t"], "t")
        if name.startswith("icmp.") and name[5:] in PRED:
            return ("cmp", name[5:], ["t", "t"], "bool")
        if name in BIN:
            return ("bin", BIN[name], ["t", "t"], "t")
        if name in BOOL_BIN:
            return ("bin", BOOL_BIN[name], ["bool", "bool"], "bool")
        if name in UN:
            return ("un", name, ["t"], "t")
        if name in PARTIAL_BIN:
            if not self.allow_partial:
                raise Refused(f"operator {name} is not total and is refused")
            return ("bin", PARTIAL_BIN[name], ["t", "t"], "t")
        raise Refused(f"unknown operator {name}")

    def pat(self, form, rhs):
        """A pattern tree: ('var', v) ('cvar', v) ('lit', neg, mag) ('tt',)
        ('ff',) ('op', opinfo, [args]) ('eval', opinfo, [vars])."""
        if isinstance(form, str):
            if form == "true":
                return ("tt",)
            if form == "false":
                return ("ff",)
            v = var_of(form)
            if v is None:
                raise Refused(f"{form} is not a pattern")
            return ("var", v)
        if not form or not isinstance(form[0], str):
            raise Refused("a pattern list must start with an operator atom")
        head, args = form[0], form[1:]
        if head == "const":
            if len(args) != 1 or not isinstance(args[0], str):
                raise Refused("(const ...) takes exactly one INT or ?var")
            v = var_of(args[0])
            if v is not None:
                return ("cvar", v)
            if INT.match(args[0]):
                neg, mag = parse_int(args[0])
                return ("lit", neg, mag)
            raise Refused(f"(const {args[0]}) is neither INT nor ?var")
        if head == "eval":
            if not rhs:
                raise Refused("eval appears only in the rhs")
            if not args or not isinstance(args[0], str):
                raise Refused("(eval OP ?var...) needs an OP")
            info = self.op(args[0])
            if info[0] == "sel":
                raise Refused("(eval select ...) is refused")
            vs = [var_of(a) for a in args[1:]]
            if len(vs) != len(info[2]) or any(v is None for v in vs):
                raise Refused(f"(eval {args[0]} ...) takes {len(info[2])} constant variables")
            return ("eval", info, vs)
        info = self.op(head)
        if len(args) != len(info[2]):
            raise Refused(f"{head} takes {len(info[2])} operands, found {len(args)}")
        return ("op", info, [self.pat(a, rhs) for a in args])


def assign(sorts, v, sort):
    if sorts.setdefault(v, sort) != sort:
        raise Refused(f"?{v} has two sorts")


def check_sorts(pat, expected, sorts, kinds):
    """Assign variable sorts; `kinds` (lhs only) records (const, term) uses."""
    tag = pat[0]
    if tag in ("var", "cvar"):
        assign(sorts, pat[1], expected)
        if kinds is not None:
            k = kinds.setdefault(pat[1], [False, False])
            k[0 if tag == "cvar" else 1] = True
    elif tag == "lit":
        if expected != "t":
            raise Refused("(const INT) stands at a bool position")
    elif tag in ("tt", "ff"):
        if expected != "bool":
            raise Refused("true/false stand at a T position")
    elif tag == "op":
        _, _, operand_sorts, result = pat[1]
        if result != expected:
            raise Refused("an operator stands at a position of the other sort")
        for a, s in zip(pat[2], operand_sorts):
            check_sorts(a, s, sorts, kinds)
    else:
        _, _, operand_sorts, result = pat[1]
        if result != expected:
            raise Refused("an eval stands at a position of the other sort")
        for v, s in zip(pat[2], operand_sorts):
            assign(sorts, v, s)


def check_rhs_vars(pat, vars_):
    tag = pat[0]
    if tag == "var":
        if pat[1] not in vars_:
            raise Refused(f"rhs variable ?{pat[1]} does not occur in the lhs")
    elif tag == "cvar":
        if pat[1] not in vars_ or not vars_[pat[1]][1]:
            raise Refused(f"(const ?{pat[1]}) in the rhs is not a constant variable")
    elif tag == "op":
        for a in pat[2]:
            check_rhs_vars(a, vars_)
    elif tag == "eval":
        for v in pat[2]:
            if v not in vars_ or not vars_[v][1]:
                raise Refused(f"eval argument ?{v} is not a constant variable of the lhs")


def ops_of(pat):
    """Every operator of a pattern, as (name for messages, admitted at bool)."""
    out = []
    if pat[0] in ("op", "eval"):
        kind, ctor = pat[1][0], pat[1][1]
        at_bool = (kind == "sel"
                   or (kind == "bin" and ctor in ("and", "or", "xor", "bAnd", "bOr", "bXor"))
                   or (kind == "cmp" and ctor in ("eq", "ne")))
        out.append((ctor or "select", at_bool))
        if pat[0] == "op":
            for a in pat[2]:
                out += ops_of(a)
    return out


def uses_eval(pat):
    if pat[0] == "eval":
        return True
    return pat[0] == "op" and any(uses_eval(a) for a in pat[2])


def uses_lit(pat):
    if pat[0] == "lit":
        return True
    return pat[0] == "op" and any(uses_lit(a) for a in pat[2])


def clause(form, keyword):
    if isinstance(form, list) and form and form[0] == keyword:
        return form[1:]
    raise Refused(f"expected the ({keyword} ...) clause")


def read_rule(form, reader):
    if not isinstance(form, list) or len(form) != 7 or form[0] != "rule":
        raise Refused("a rule is (rule NAME) with exactly the five clauses")
    name = form[1]
    if not isinstance(name, str) or not NAME.match(name):
        raise Refused(f"rule name {name!r} is not [a-z][a-z0-9_]*")
    try:
        direction = clause(form[2], "direction")
        if direction not in (["equiv"], ["refines"]):
            raise Refused("direction must be equiv or refines")
        domain = clause(form[3], "domain")
        if not domain or any(t not in TYPES for t in domain) or len(set(domain)) != len(domain):
            raise Refused("the domain is a non-empty list of distinct TYPEs")
        lhs_forms = clause(form[4], "lhs")
        rhs_forms = clause(form[5], "rhs")
        if len(lhs_forms) != 1 or len(rhs_forms) != 1:
            raise Refused("lhs and rhs take exactly one pattern")
        lhs = reader.pat(lhs_forms[0], False)
        rhs = reader.pat(rhs_forms[0], True)
        if lhs[0] != "op":
            raise Refused("the lhs root must be an OP node")
        lhs_sort = lhs[1][3]
        sorts, kinds = {}, {}
        check_sorts(lhs, lhs_sort, sorts, kinds)
        vars_ = {}
        for v, (has_const, has_term) in kinds.items():
            if has_const and has_term:
                raise Refused(f"?{v} is both a constant variable and a term variable")
            vars_[v] = (sorts[v], has_const)
        check_sorts(rhs, lhs_sort, sorts, None)
        check_rhs_vars(rhs, vars_)
        conds = []
        for c in clause(form[6], "where"):
            if not isinstance(c, list) or not c:
                raise Refused("a COND must be a list")
            v = var_of(c[1]) if len(c) > 1 else None
            if v is None or vars_.get(v) != ("t", True):
                raise Refused("a where variable must be a constant variable of sort T")
            if c[0] in ("eq", "ne") and len(c) == 3 and isinstance(c[2], str) and INT.match(c[2]):
                conds.append((c[0], v) + parse_int(c[2]))
            elif c[0] in ("pow2", "zero_mod_width") and len(c) == 2:
                conds.append((c[0], v))
            else:
                raise Refused("malformed COND")
        if "bool" in domain and (conds or uses_lit(lhs) or uses_lit(rhs)):
            raise Refused("a rule with bool in its domain has no (const INT) and no where")
        if "bool" in domain:
            for op, at_bool in ops_of(lhs) + ops_of(rhs):
                if not at_bool:
                    raise Refused(f"operator {op} is not admitted at domain type bool")
    except Refused as e:
        raise Refused(f"rule {name}: {e}") from None
    order = sorted(vars_, key=lambda v: v.encode("ascii"))
    return {
        "name": name,
        "direction": direction[0],
        "domain": domain,
        "lhs": lhs,
        "rhs": rhs,
        "conds": conds,
        "vars": [(v,) + vars_[v] for v in order],
        "rank": {v: i for i, v in enumerate(order)},
        "canonical": canonical(form),
        # `fold`: the rhs is `(eval ...)` itself, so the quoted sides are equal.
        "kind": "fold" if rhs[0] == "eval" else ("eval" if uses_eval(rhs) else "plain"),
    }


def lean_bool(b):
    return "true" if b else "false"


def lean_nat(n):
    """A raw `Nat` literal (no `OfNat` instance), the term trust-cg builds."""
    return f"(nat_lit {n})"


def lean_pat(pat, rank):
    tag = pat[0]
    if tag == "var":
        return f"(Pat.var {lean_nat(rank[pat[1]])})"
    if tag == "cvar":
        return f"(Pat.cvar {lean_nat(rank[pat[1]])})"
    if tag == "lit":
        return f"(Pat.lit {lean_bool(pat[1])} {lean_nat(pat[2])})"
    if tag == "tt":
        return "Pat.tt"
    if tag == "ff":
        return "Pat.ff"
    kind, ctor = pat[1][0], pat[1][1]
    if tag == "eval":
        args = [f"(Pat.cvar {lean_nat(rank[v])})" for v in pat[2]]
    else:
        args = [lean_pat(a, rank) for a in pat[2]]
    if kind == "bin":
        return f"(Pat.bin BinOp.{ctor} {' '.join(args)})"
    if kind == "un":
        return f"(Pat.un UnOp.{ctor} {' '.join(args)})"
    if kind == "cmp":
        return f"(Pat.cmp ICmpOp.{ctor} {' '.join(args)})"
    return f"(Pat.sel {' '.join(args)})"


def lean_sorts(vars_):
    out = "Sorts.nil"
    for _, sort, const in reversed(vars_):
        out = f"(Sorts.cons Srt.{sort} {lean_bool(const)} {out})"
    return out


def lean_conds(conds, rank):
    out = "Conds.nil"
    for c in reversed(conds):
        if c[0] in ("eq", "ne"):
            one = f"(Cond.{c[0]} {lean_nat(rank[c[1]])} {lean_bool(c[2])} {lean_nat(c[3])})"
        elif c[0] == "pow2":
            one = f"(Cond.pow2 {lean_nat(rank[c[1]])})"
        else:
            one = f"(Cond.zeroModWidth {lean_nat(rank[c[1]])})"
        out = f"(Conds.cons {one} {out})"
    return out


def lean_literal(rule):
    """The lines of the `Rule` literal: what the rule's statement is about."""
    return [
        f"  Rule.mk Dir.{rule['direction']}",
        f"    {lean_sorts(rule['vars'])}",
        f"    {lean_pat(rule['lhs'], rule['rank'])}",
        f"    {lean_pat(rule['rhs'], rule['rank'])}",
        f"    {lean_conds(rule['conds'], rule['rank'])}",
    ]


def lean_def(rule, def_name, origin):
    variables = ", ".join(
        f"{v} = {i} ({sort}{', const' if const else ''})"
        for i, (v, sort, const) in enumerate(rule["vars"])
    ) or "none"
    lines = [f"/-- `{rule['canonical']}`"]
    if origin:
        lines.append(f"    From `{origin}`.")
    lines += [
        f"    Variables: {variables}. -/",
        f"def {def_name} : Rule :=",
    ]
    return "\n".join(lines + lean_literal(rule))


def lemma_rows(def_name, kind, domain):
    """The `rule scope kind lemma` rows of one rule: a row per scope of its
    domain. A rule whose domain has all twelve integer types has one lemma for
    them (`int`); otherwise one per integer type. `bool` is a scope of its
    own. A `fold` rule gets no lemma (`-`)."""
    ints = [t for t in INT_TYPES if t in domain]
    scopes = []
    if ints == INT_TYPES:
        scopes.append(("int", f"EqsatInt.{def_name}"))
    else:
        scopes += [(t, f"EqsatInt.{def_name}_{t}") for t in ints]
    if "bool" in domain:
        scopes.append(("bool", f"EqsatInt.{def_name}_bool" if ints else f"EqsatInt.{def_name}"))
    return [(def_name, scope, kind, "-" if kind == "fold" else lemma) for scope, lemma in scopes]


def merged_lemma_rows(sets):
    """The rows of a table over several rule files, given as
    `(namespace, [(def_name, rule)])` in table order: every row of the first
    file, then, for each later file, the rows of the rules no earlier file
    has. A rule name an earlier file has gets no second row, and is refused
    unless both files give it one literal and the same rows (so one kind and
    one domain): the earlier row's lemma is stated on the earlier file's
    literal, and two literals that are one term have one statement."""
    rows, first = [], {}
    for namespace, entries in sets:
        for def_name, rule in entries:
            own = lemma_rows(def_name, rule["kind"], rule["domain"])
            if def_name not in first:
                first[def_name] = (namespace, lean_literal(rule), own)
                rows += own
                continue
            earlier, literal, earlier_rows = first[def_name]
            if lean_literal(rule) != literal:
                raise Refused(f"{namespace}.{def_name} is not the literal of "
                              f"{earlier}.{def_name}: one rule name, two statements")
            if own != earlier_rows:
                raise Refused(f"{namespace}.{def_name} and {earlier}.{def_name} are one literal "
                              "with two kinds or two domains: one rule name, two sets of rows")
    return rows


def lemmas_file(rows, source, inputs, also=()):
    """The text of `LEMMAS`. Refuses two rows that name one lemma (a rule
    `x_bool` beside the bool instance of a rule `x`). `also` lists each
    further rule file of the table as `(namespace, source, inputs)`."""
    named = [row[3] for row in rows if row[3] != "-"]
    twice = sorted({name for name in named if named.count(name) > 1})
    if twice:
        raise Refused(f"two rows name one lemma: {' '.join(twice)}")
    header = [
        "# The lemmas of a rule set of the eqsat_rules family (PKG-U2; README.md, \"The rule",
        "# set and its lemma groups\"). GENERATED by `gen_rule_defs.py --lemmas` in this",
        "# directory; do not edit. The script's header says how to regenerate.",
        "#",
        f"# Read from {source}",
        "# (SHA-256):",
    ]
    header += [f"#   {name}  {digest}" for name, digest in inputs]
    for namespace, also_source, also_inputs in also:
        header += [
            f"# and from {also_source}",
            f"# (SHA-256), its literals in namespace {namespace}:",
        ]
        header += [f"#   {name}  {digest}" for name, digest in also_inputs]
    if also:
        header += [
            "# A later rule file's rows follow the first's, and the lemma of such a row",
            "# is stated on that file's literal (`Sound <its namespace>.<rule> ...`). A",
            "# rule name an earlier file has gets no second row: the generator refuses it",
            "# unless both files give it one literal, one kind and one domain, so the",
            "# earlier row's lemma, stated on the earlier file's literal, is a proof of",
            "# the later file's statement too (the gate asserts the entry accepts it).",
        ]
    header += [
        "#",
        "# One `rule scope kind lemma` row per rule and scope of the rule's domain.",
        "# scope: `int` (the domain has all twelve integer types and the lemma is",
        "#   `∀ t, Sound Defs.<rule> (.int t)`), one integer type, or `bool`.",
        "# kind: `plain`; `eval` (the right side uses `(eval ...)` under an operator, so",
        "#   the lemma carries the named premise checker-ground-eval); `fold` (the right",
        "#   side is `(eval ...)`: no lemma, written `-`, and the disposition is",
        "#   Unsupported(\"fold-evaluator\")). trust-cg reads the kind from its own parsed",
        "#   rule, never from this column.",
        "# lemma: the theorem of namespace EqsatInt the gate",
        "#   (crates/clean-olean/tests/eqsat_rules.rs) requires with exactly the row's",
        "#   statement, unless the gate's TIMED_OUT names the row; the gate refuses a",
        "#   `Sound` theorem of the lemma modules that no row names.",
    ]
    return "\n".join(header + [" ".join(row) for row in rows]) + "\n"


def read_rules(raw, reader):
    """The rules of one rule file's bytes, or `Refused`."""
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as e:
        raise Refused(f"not UTF-8: {e}") from None
    return [read_rule(form, reader) for form in parse_forms(tokenize(text))]


def self_test():
    """Controls on what the reader accepts, beside the checker's tokenizer
    (trust-cg `registry.rs` `tokenize`): each case is accepted or refused as
    the checker does, and an accepted case gives the literal named."""
    rule = ("(rule add_zero (direction equiv) (domain u8) "
            "(lhs (add ?x (const 0))) (rhs ?x) (where))\n")
    reader = Reader(False)
    plain = [lean_def(r, r["name"], None) for r in read_rules(rule.encode(), reader)]
    failures = []

    def accepted(what, raw):
        try:
            got = [lean_def(r, r["name"], None) for r in read_rules(raw, reader)]
        except Refused as e:
            failures.append(f"{what}: refused ({e}), the checker accepts it")
            return
        if got != plain:
            failures.append(f"{what}: a different literal")

    def refused(what, raw, allow_partial=False):
        try:
            read_rules(raw, Reader(allow_partial))
        except Refused:
            return
        failures.append(f"{what}: accepted, the checker refuses it")

    if len(plain) != 1 or "Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 0))" \
            not in plain[0]:
        failures.append("control: add_zero is not quoted as expected")
    accepted("a non-ASCII comment line",
             "; caf\u00e9 \u2014 a comment the checker admits\n".encode() + rule.encode())
    accepted("a non-ASCII trailing comment",
             rule.rstrip("\n").encode() + " ; \u03bb\u2192\n".encode())
    accepted("a non-ASCII comment that ends the file with no newline",
             rule.encode() + "; \u00e9".encode())
    accepted("form feed and carriage return as white space",
             rule.replace(" (domain", "\x0c\r(domain").encode())
    refused("a non-ASCII character outside a comment",
            rule.replace("add_zero", "add_z\u00e9ro").encode())
    refused("a no-break space outside a comment", rule.replace(" (lhs", "\u00a0(lhs").encode())
    refused("a control character outside a comment", rule.replace(" (lhs", "\x0b(lhs").encode())
    refused("bytes that are not UTF-8 in a comment", b"; \xff\xfe\n" + rule.encode())
    refused("bytes that are not UTF-8 outside a comment", rule.encode() + b"\xc3")
    refused("a non-total operator", rule.replace("(add ?x (const 0))", "(udiv ?x (const 1))").encode())
    refused("an unbalanced form", rule.rstrip("\n")[:-1].encode())
    # The lemma rows of a domain (`--lemmas`).
    for what, got, want in [
        ("all twelve integer types",
         lemma_rows("r", "plain", INT_TYPES),
         [("r", "int", "plain", "EqsatInt.r")]),
        ("integer types and bool",
         lemma_rows("r", "eval", TYPES),
         [("r", "int", "eval", "EqsatInt.r"), ("r", "bool", "eval", "EqsatInt.r_bool")]),
        ("bool only",
         lemma_rows("r", "plain", ["bool"]),
         [("r", "bool", "plain", "EqsatInt.r")]),
        ("two integer types",
         lemma_rows("r", "plain", ["u8", "i8"]),
         [("r", "i8", "plain", "EqsatInt.r_i8"), ("r", "u8", "plain", "EqsatInt.r_u8")]),
        ("a fold rule",
         lemma_rows("fold_r", "fold", TYPES),
         [("fold_r", "int", "fold", "-"), ("fold_r", "bool", "fold", "-")]),
    ]:
        if got != want:
            failures.append(f"lemma rows of {what}: {got}")
    try:
        lemmas_file(lemma_rows("r", "plain", TYPES) + lemma_rows("r_bool", "plain", INT_TYPES),
                    "a control", [])
        failures.append("lemma rows: one lemma named by two rows was accepted")
    except Refused:
        pass
    # A table over two rule files (`--also`): a rule only the later file has
    # follows the first file's rows, a rule name both have is one row, and the
    # header records both files. A shared name with another literal, another
    # kind or another domain is refused.
    def one(text):
        return [(r["name"], r) for r in read_rules(text.encode(), reader)]

    comm = ("(rule add_comm (direction equiv) (domain u8) "
            "(lhs (add ?x ?y)) (rhs (add ?y ?x)) (where))\n")
    try:
        merged = merged_lemma_rows([("Defs", one(rule)), ("Later", one(comm + rule))])
        want = [("add_zero", "u8", "plain", "EqsatInt.add_zero_u8"),
                ("add_comm", "u8", "plain", "EqsatInt.add_comm_u8")]
        if merged != want:
            failures.append(f"a table over two rule files: {merged}")
        text = lemmas_file(merged, "the first file", [("a.rules", "0" * 64)],
                           [("Later", "the later file", [("b.rules", "1" * 64)])])
        for line in ["# Read from the first file", "#   a.rules  " + "0" * 64,
                     "# and from the later file",
                     "# (SHA-256), its literals in namespace Later:", "#   b.rules  " + "1" * 64,
                     "add_zero u8 plain EqsatInt.add_zero_u8",
                     "add_comm u8 plain EqsatInt.add_comm_u8"]:
            if line not in text.split("\n"):
                failures.append(f"a table over two rule files lacks the line {line!r}")
        if "# and from" in lemmas_file(merged, "the first file", [("a.rules", "0" * 64)]):
            failures.append("a table over one rule file names a second")
    except Refused as e:
        failures.append(f"a table over two rule files: refused ({e})")
    mul_mul = ("(rule r (direction equiv) (domain u8) (lhs (mul (mul ?x (const ?a)) (const ?b))) "
               "(rhs (mul ?x {})) (where))\n")
    for what, earlier, later in [
        ("another literal", rule, rule.replace("(const 0)", "(const 1)")),
        ("another direction", rule, rule.replace("equiv", "refines")),
        ("another domain", rule, rule.replace("(domain u8)", "(domain u8 u16)")),
        ("another kind (eval against the same operator on constants)",
         mul_mul.format("(eval mul ?a ?b)"), mul_mul.format("(mul (const ?a) (const ?b))")),
    ]:
        try:
            merged_lemma_rows([("Defs", one(earlier)), ("Later", one(later))])
            failures.append(f"a rule name in two files with {what}: accepted")
        except Refused:
            pass
    failures += command_line_failures(rule, comm)
    if failures:
        sys.exit("gen_rule_defs.py --self-test: " + "; ".join(failures))
    print("gen_rule_defs.py --self-test: ok (4 accepted, 7 refused, 1 literal control, "
          "5 lemma-row controls, 1 refused lemma table, 1 table over two rule files, "
          "4 refused shared rule names, 4 accepted command lines over two rule files, "
          "9 refused command lines)")


def run_main(argv):
    """`main` on `argv`, its output captured: `(exit, stdout)`, where `exit` is
    `None` for a return and otherwise what `sys.exit` was given."""
    out = io.StringIO()
    try:
        with contextlib.redirect_stdout(out):
            main(argv)
    except SystemExit as e:
        return (0 if e.code is None else e.code), out.getvalue()
    return None, out.getvalue()


def command_line_failures(rule, comm):
    """The self-test's controls on the command line itself (`main` and
    `read_set`, which the controls on in-script rule text do not reach): a
    table and a module written from two rule files in a temporary directory,
    `--check` on each, and the command lines that are refused. `rule` is the
    text of one rule and `comm` of another."""
    failures = []
    with tempfile.TemporaryDirectory() as tmp:
        def write(name, text):
            path = os.path.join(tmp, name)
            with open(path, "wb") as f:
                f.write(text.encode("utf-8"))
            return path

        def sha(path):
            with open(path, "rb") as f:
                return hashlib.sha256(f.read()).hexdigest()

        first = write("first.rules", rule)
        later = write("later.rules", comm + rule)
        table = ["--module", "M", "--namespace", "Defs", "--source", "the first file",
                 "--also", "Later", "the later file", later, "--lemmas", first]
        module = ["--module", "M", "--namespace", "Later", "--source", "the later file", later]

        # Accepted: the table over both files, with each file's own digest in
        # the header; the later file's module; and `--check` on each.
        status, text = run_main(table)
        if status is not None:
            failures.append(f"the command line of a table over two rule files: {status}")
        for line in ["# Read from the first file", f"#   first.rules  {sha(first)}",
                     "# and from the later file",
                     "# (SHA-256), its literals in namespace Later:",
                     f"#   later.rules  {sha(later)}",
                     "add_zero u8 plain EqsatInt.add_zero_u8",
                     "add_comm u8 plain EqsatInt.add_comm_u8"]:
            if line not in text.split("\n"):
                failures.append(f"the command line's table lacks the line {line!r}")
        if text.count(" plain ") != 2:
            failures.append("the command line's table has a row per file for a shared rule name")
        committed = write("LEMMAS", text)
        if run_main(table + ["--check", committed]) != (None, ""):
            failures.append("--check refuses the table the same command line wrote")
        status, lean = run_main(module)
        if status is not None:
            failures.append(f"the command line of the later file's module: {status}")
        for line in ["namespace EqsatRule.Later", "def add_comm : Rule :=",
                     "def add_zero : Rule :=", f"     later.rules  {sha(later)}",
                     "end EqsatRule.Later"]:
            if line not in lean.split("\n"):
                failures.append(f"the command line's module lacks the line {line!r}")
        generated = write("M.lean", lean)
        if run_main(module + ["--check", generated]) != (None, ""):
            failures.append("--check refuses the module the same command line wrote")

        # Refused, each for its own reason and with nothing printed.
        def refused(what, argv, needle):
            status, printed = run_main(argv)
            if status is None or status == 0:
                failures.append(f"{what}: accepted")
            elif needle not in str(status):
                failures.append(f"{what}: refused for another reason ({status})")
            elif printed:
                failures.append(f"{what}: refused, and printed output")

        stale = "is not what the rule text generates"
        refused("--check of a table with one row edited",
                table + ["--check", write("LEMMAS.edited", text.replace("add_comm_u8", "x"))],
                stale)
        refused("--check of a table against one rule file only",
                ["--module", "M", "--namespace", "Defs", "--source", "the first file",
                 "--lemmas", first, "--check", committed], stale)
        refused("--check of a module with one literal edited",
                module + ["--check", write("M.edited", lean.replace("Pat.var", "Pat.cvar", 1))],
                stale)
        base = ["--module", "M", "--namespace", "Defs", "--source", "the first file"]
        refused("--also under the first file's namespace",
                base + ["--also", "Defs", "the later file", later, "--lemmas", first],
                "namespace Defs is given twice")
        other = write("other.rules", comm)
        refused("two --also under one namespace",
                base + ["--also", "Later", "the later file", later,
                        "--also", "Later", "another file", other, "--lemmas", first],
                "namespace Later is given twice")
        refused("--also of the first file itself",
                base + ["--also", "Later", "the later file", first, "--lemmas", first],
                "a rule file is given once")
        refused("--also of a file with the bytes of an earlier one",
                base + ["--also", "Later", "the later file", later,
                        "--also", "Other", "a copy", write("copy.rules", comm + rule),
                        "--lemmas", first],
                "has the bytes of later.rules")
        refused("--also without --lemmas",
                base + ["--also", "Later", "the later file", later, first], "needs --lemmas")
        refused("a shared rule name with another literal, on the command line",
                base + ["--also", "Later", "the later file",
                        write("edited.rules", comm + rule.replace("(const 0)", "(const 1)")),
                        "--lemmas", first],
                "Later.add_zero is not the literal of Defs.add_zero")
    return failures


def read_set(paths, reader, name_from_file):
    """One rule set: `(inputs, entries)`, each file's `(name, SHA-256)` and each
    rule as `(def_name, rule, origin)` in the order read. A refused file and a
    definition name used twice are `Refused`, with the file's path."""
    inputs, entries, seen = [], [], set()
    for path in paths:
        with open(path, "rb") as f:
            raw = f.read()
        inputs.append((os.path.basename(path), hashlib.sha256(raw).hexdigest()))
        try:
            rules = read_rules(raw, reader)
        except Refused as e:
            raise Refused(f"{path}: {e}") from None
        stem = os.path.splitext(os.path.basename(path))[0]
        if name_from_file and len(rules) != 1:
            raise Refused(f"{path}: --name-from-file needs exactly one rule per file")
        for rule in rules:
            def_name = stem if name_from_file else rule["name"]
            if not NAME.match(def_name) or def_name in seen:
                raise Refused(f"{path}: {def_name!r} is not a fresh [a-z][a-z0-9_]* name")
            seen.add(def_name)
            entries.append((def_name, rule, os.path.basename(path) if name_from_file else None))
    return inputs, entries


def repeated_rule_file(sets):
    """Among the rule files of a table, given as `(namespace, inputs)` in table
    order: the first file whose name or whose bytes an earlier file has, as a
    message, or `None`. One rule file read twice would give a table whose
    every later row is a shared rule name, and two files of one name cannot
    both be recorded in the table's header."""
    seen = []
    for namespace, inputs in sets:
        for name, digest in inputs:
            for earlier, earlier_name, earlier_digest in seen:
                if name == earlier_name:
                    return (f"{namespace}: {name} is the name of a rule file of {earlier} "
                            "too: a rule file is given once")
                if digest == earlier_digest:
                    return (f"{namespace}: {name} has the bytes of {earlier_name} of "
                            f"{earlier}: a rule file is given once")
            seen.append((namespace, name, digest))
    return None


def main(argv=None):
    """The command line. `argv` is `sys.argv[1:]` when not given (the
    self-test gives its own)."""
    if argv is None:
        argv = sys.argv[1:]
    if argv == ["--self-test"]:
        self_test()
        return
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("files", nargs="+", help="rule files, in the order to emit")
    ap.add_argument("--module", required=True, help="the Lean module being written (its file stem)")
    ap.add_argument("--namespace", required=True, help="namespace under EqsatRule")
    ap.add_argument("--source", required=True, help="where the rule text lives, for the header")
    ap.add_argument("--name-from-file", action="store_true",
                    help="name each def after its file's stem (one rule per file)")
    ap.add_argument("--allow-partial-ops", action="store_true",
                    help="quote udiv sdiv urem srem shl lshr ashr (control set only)")
    ap.add_argument("--check", metavar="FILE", help="compare with FILE instead of printing")
    ap.add_argument("--table", action="store_true",
                    help="print `def-name direction kind domain` rows instead of Lean "
                         "(kind: plain, eval = the rhs uses (eval ...) under an operator, "
                         "fold = the rhs is (eval ...))")
    ap.add_argument("--lemmas", action="store_true",
                    help="print the family's LEMMAS file instead of Lean: one "
                         "`rule scope kind lemma` row per rule and scope of its domain")
    ap.add_argument("--also", nargs=3, action="append", default=[],
                    metavar=("NAMESPACE", "SOURCE", "FILE"),
                    help="with --lemmas: a further rule file of the table, the namespace "
                         "its literals are generated in and where its text lives")
    args = ap.parse_args(argv)
    namespaces = [args.namespace] + [namespace for namespace, _, _ in args.also]
    for value in namespaces:
        if not NAMESPACE.match(value):
            sys.exit(f"namespace {value!r} is not a namespace component [A-Z][A-Za-z0-9]*")
    for value in namespaces:
        if namespaces.count(value) > 1:
            sys.exit(f"--also: namespace {value} is given twice: the literals of each rule "
                     "file have a namespace of their own")
    if args.also and not args.lemmas:
        sys.exit("--also adds a rule file to the lemma table: it needs --lemmas")
    if args.also and (args.name_from_file or args.allow_partial_ops):
        sys.exit("--also is for rule files of the engine: not with --name-from-file or "
                 "--allow-partial-ops")

    reader = Reader(args.allow_partial_ops)
    try:
        inputs, entries = read_set(args.files, reader, args.name_from_file)
        also = [(namespace, source) + read_set([path], reader, False)
                for namespace, source, path in args.also]
    except Refused as e:
        sys.exit(str(e))
    if args.also:
        repeated = repeated_rule_file(
            [(args.namespace, inputs)]
            + [(namespace, also_inputs) for namespace, _, also_inputs, _ in also])
        if repeated:
            sys.exit(f"--also: {repeated}")
    defs = [lean_def(rule, def_name, origin) for def_name, rule, origin in entries]

    if args.table:
        sys.stdout.write("".join(
            "\t".join([def_name, rule["direction"], rule["kind"], " ".join(rule["domain"])]) + "\n"
            for def_name, rule, _ in entries))
        return
    if args.lemmas:
        try:
            sets = [(args.namespace, [(def_name, rule) for def_name, rule, _ in entries])]
            sets += [(namespace, [(def_name, rule) for def_name, rule, _ in also_entries])
                     for namespace, _, _, also_entries in also]
            out = lemmas_file(merged_lemma_rows(sets), args.source, inputs,
                              [(namespace, source, also_inputs)
                               for namespace, source, also_inputs, _ in also])
        except Refused as e:
            sys.exit(f"--lemmas: {e}")
        if args.check:
            with open(args.check, encoding="utf-8") as f:
                if f.read() != out:
                    sys.exit(f"{args.check} is not what the rule text generates; regenerate it")
            return
        sys.stdout.write(out)
        return

    header = [
        "/- Copyright 2026 Andrew Yates. Apache-2.0.",
        "   GENERATED by `gen_rule_defs.py` in this directory; do not edit. The",
        "   script's header says how to regenerate.",
        "",
        f"   {len(defs)} rule statement(s) of",
        f"   {args.source},",
        "   each quoted as an `EqsatRule.Rule` literal (the comment above a literal",
        "   is the rule's section 5.2 canonical text). These literals are data, not",
        "   claims: a lemma about one is in another module, and trust-cg rebuilds",
        "   each literal from its own parsed rule before the kernel is asked anything.",
        "",
        "   Rule text read (SHA-256):",
    ]
    header += [f"     {name}  {digest}" for name, digest in inputs]
    header += [
        "-/",
        "import EqsatRule",
        "",
        f"namespace EqsatRule.{args.namespace}",
        "open SemR",
        "",
    ]
    out = "\n".join(header) + "\n" + "\n\n".join(defs) + f"\n\nend EqsatRule.{args.namespace}\n"
    if args.check:
        with open(args.check, encoding="utf-8") as f:
            if f.read() != out:
                sys.exit(f"{args.check} is not what the rule text generates; regenerate it")
        return
    sys.stdout.write(out)


if __name__ == "__main__":
    main()
