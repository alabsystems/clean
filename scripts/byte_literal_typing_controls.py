#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Prepare and validate independent Lean controls for the byte/literal model.

This utility runs no compiler. The caller must use heavy_gate for Lean replay,
check its exit status, and retain source/tool/log identities. These controls
qualify model terms, not production Rust execution. Source scans reuse the
comment/string-blanking Lean scanner (source_scan: blank_noncode_lean).
Negative logs may contain post-failure sorryAx axiom reports from Lean's error
recovery; these are diagnostics, never successful proof evidence. Authored
admissions and every positive-log admission are refused.
"""

import argparse
from pathlib import Path
import re
import sys

from lean_suite_conformance import blank_noncode_lean


ROOTS = (
    "ir_byte_literal_infers_v1", "ir_byte_literal_typing_v1",
    "ir_byte_literal_infers_sound_v1",
    "ir_byte_literal_nat_infers_input_v1", "ir_byte_literal_string_infers_input_v1",
    "ir_byte_literal_nat_typing_input_v1", "ir_byte_literal_string_typing_input_v1",
)
CONTROLS = tuple(f"replay_byte_literal_{kind}_none_is_empty_v1" for kind in ("infers", "typing"))
ADMISSION = re.compile(r"\b(?:sorry|sorryAx|admit|admitted)\b", re.I)
RESOURCE = re.compile(
    r"maximum recursion|maxrecdepth|maxheartbeats|heartbeat|out of memory|"
    r"timeout|timed out|time limit|stack overflow|fuel exhausted|budget exceeded|"
    r"\bpanic\b|segmentation fault|\bkilled\b", re.I,
)
ERROR = re.compile(r"^(.+):(\d+):(\d+): error: (.*)$", re.M)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def declaration(code, root):
    """Only the exporter's exact two-line, explicit-term layout is supported."""
    name = re.escape("CleanVerify." + root)
    starts = list(re.finditer(rf"^(?:noncomputable )?def {name}\b", code, re.M))
    require(len(starts) == 1, f"{root}: expected exactly one definition")
    match = re.search(rf"^noncomputable def {name} : (?P<type>[^\n]+) :=\n"
                      r"  (?P<body>[^\n]+)\n", code, re.M)
    require(match is not None, f"{root}: unsupported generated declaration layout")
    return match


def control_appendix():
    text = "\n-- Independent refusal controls: failure implies Empty, never acceptance.\n"
    for judgment, root in zip(("infers", "typing"), CONTROLS):
        text += (
            f"noncomputable def CleanVerify.{root} : "
            "(tenv : CleanVerify.KDeclEnv) -> (G : CleanVerify.ListType CleanVerify.KExpr) -> "
            "(input : CleanVerify.KExpr) -> "
            f"(h : CleanVerify.ir_byte_literal_{judgment}_v1 tenv G input "
            "(@CleanVerify.IROption.none CleanVerify.KExpr)) -> CleanVerify.Empty :=\n"
            "  fun tenv G input h => h\n"
            f"#print axioms CleanVerify.{root}\n\n"
        )
    return text


def validate_source(source):
    code = blank_noncode_lean(source)
    require(not ADMISSION.search(code), "source contains an authored admission")
    controls_present = [bool(re.search(rf"\b{root}\b", code)) for root in CONTROLS]
    require(all(controls_present) or not any(controls_present), "partial Empty controls")
    roots = ROOTS + (CONTROLS if all(controls_present) else ())
    for root in roots:
        declaration(code, root)
        audit = rf"^#print axioms CleanVerify\.{re.escape(root)}\s*$"
        require(len(re.findall(audit, code, re.M)) == 1, f"{root}: expected exactly one axiom audit")
    if all(controls_present):
        require(source.endswith(control_appendix()), "Empty controls differ from identity appendix")
    return code, roots


def mutate(source, kind, mode):
    require(kind in ("nat", "string") and mode in ("subject", "nominal"), "unknown control kind or mode")
    code, _ = validate_source(source)
    judgment = "infers" if mode == "subject" else "typing"
    root = f"ir_byte_literal_{kind}_{judgment}_input_v1"
    match = declaration(code, root)
    head = source[match.start("type"):match.end("type")]
    goal = f"(@CleanVerify.ir_byte_literal_{judgment}_v1 x_0 x_1 (@CleanVerify.literal_{kind} x_2) "
    require(head.count(goal) == 1, f"{root}: exact generated conclusion not found")
    before, conclusion = head.split(goal)
    if mode == "subject":
        other = "string" if kind == "nat" else "nat"
        changed = goal.replace(f"literal_{kind} x_2", f"literal_{other} x_2") + conclusion
    else:
        token = "@CleanVerify.IRTy.fatstr_"
        require(conclusion.count(token) == 1, f"{root}: exact observer nominal not found")
        changed = goal + conclusion.replace(token, "@CleanVerify.IRTy.containerlen_")
    # Offsets refer to the geometry-preserving scanner: telescope, body and
    # every other byte in the generated export remain exactly unchanged.
    return source[:match.start("type")] + before + changed + source[match.end("type"):]


def prepare(source_path, outdir):
    source = source_path.read_text(encoding="utf-8")
    _, roots = validate_source(source)
    require(not any(root in roots for root in CONTROLS), "source already has Empty controls")
    outputs = {"PositiveControls.lean": source + control_appendix()}
    for kind in ("nat", "string"):
        outputs[f"WrongSubject-{kind}.lean"] = mutate(source, kind, "subject")
        outputs[f"WrongNominal-{kind}.lean"] = mutate(source, kind, "nominal")
    require(all(not (outdir / name).exists() for name in outputs), "output already exists; refusing overwrite")
    outdir.mkdir(parents=True, exist_ok=True)
    for name, text in outputs.items():
        with (outdir / name).open("x", encoding="utf-8", newline="") as stream:
            stream.write(text)
    print(f"Prepared {len(outputs)} controls in {outdir}")


def check_positive(source, log, exit_code):
    require(exit_code == 0, "positive Lean replay must exit 0")
    _, roots = validate_source(source)
    require(not re.search(r"\berror\s*:", log, re.I), "positive replay reported an error")
    require(not RESOURCE.search(log), "positive replay reported a resource failure")
    require(not ADMISSION.search(log), "positive replay reported an admission")
    for root in roots:
        line = f"'CleanVerify.{root}' does not depend on any axioms"
        reports = re.findall(rf"^'CleanVerify\.{re.escape(root)}'.*$", log, re.M)
        require(reports == [line], f"{root}: missing, duplicate or nonempty axiom closure")


def check_mutant(source_path, log, exit_code, root, original_path):
    require(exit_code == 1, "mutant must exit 1, not accept or die abnormally")
    require(root in ROOTS[3:], "mutant root must be an input inference/typing law")
    _, _, _, kind, judgment, _, _ = root.split("_")
    mode = "subject" if judgment == "infers" else "nominal"
    source = source_path.read_text(encoding="utf-8")
    expected = mutate(original_path.read_text(encoding="utf-8"), kind, mode)
    require(source == expected, "mutant differs from the exact regenerated type-only control")
    code, _ = validate_source(source)
    match = declaration(code, root)
    line = code.count("\n", 0, match.start()) + 1
    require(not RESOURCE.search(log), "mutant replay reported a resource failure")
    errors = list(ERROR.finditer(log))
    require(bool(errors), "mutant has no positioned Lean error")
    first = errors[0]
    require(not re.search(r"\berror\s*:", log[:first.start()], re.I),
            "an earlier unpositioned error precedes the target refusal")
    require(Path(first[1]).resolve() == source_path.resolve(), "first error names a different source")
    require(int(first[2]) in (line, line + 1), "first error is not at the target declaration/body")
    require(re.fullmatch(r"Type mismatch\s*", first[4], re.I) is not None,
            "first error is not a semantic Type mismatch")
    require(not ADMISSION.search(log[:first.start()]), "admission precedes semantic refusal")
    # Lean recovers from a failed declaration by assigning sorryAx and may
    # print its closure later. This diagnostic recovery is not proof evidence.
    # Refuse all other admissions, including source-authored ones above.
    after = re.sub(r"^'CleanVerify\.[\w.]+?' depends on axioms: \[sorryAx\]\s*$",
                   "", log[first.start():], flags=re.M)
    require(not ADMISSION.search(after), "mutant has an admission beyond diagnostic recovery")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    prep = commands.add_parser("prepare", help="write four type-only mutants and two Empty controls")
    prep.add_argument("source", type=Path)
    prep.add_argument("outdir", type=Path)
    positive = commands.add_parser("check-positive", help="require all roots and empty replay axiom audits")
    positive.add_argument("source", type=Path)
    positive.add_argument("log", type=Path)
    positive.add_argument("--exit-code", type=int, required=True)
    negative = commands.add_parser("check-mutant", help="require semantic refusal at the unchanged proof")
    negative.add_argument("source", type=Path)
    negative.add_argument("log", type=Path)
    negative.add_argument("--exit-code", type=int, required=True)
    negative.add_argument("--root", choices=ROOTS[3:], required=True)
    negative.add_argument("--original", type=Path, required=True,
                          help="pristine export: every byte except the prescribed type mutation must match")
    args = parser.parse_args(argv)
    try:
        if args.command == "prepare":
            prepare(args.source, args.outdir)
        elif args.command == "check-positive":
            check_positive(args.source.read_text(encoding="utf-8"), args.log.read_text(encoding="utf-8"), args.exit_code)
            print("PASS: required roots have independent empty axiom closures")
        else:
            check_mutant(args.source, args.log.read_text(encoding="utf-8"), args.exit_code, args.root, args.original)
            print(f"PASS: semantic mutant refusal at {args.root}")
    except (OSError, ValueError) as error:
        print(f"REFUSED: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
