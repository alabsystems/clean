#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Run the patched-kernel control (unit P3 of the kernel self-proof plan).

    scripts/heavy_gate.sh run 16 p3-patched-kernel-control -- \\
        python3 scripts/patched_kernel_control.py [--write-record] [--packages a,b] \\
            [--work-dir DIR] [--keep] [--from-worktree]

The question: if `clean-kernel` were wrong about one planted proof of `False`
(the closed term `Nat.zero` at type `False`), which places that mint an
accepted row would still mint one? Each host crate's
`tests/patched_kernel_control.rs` drives its sites on that pair and compares
what it sees with its pins (`crates/clean-kernel/tests/support/
patched_kernel_control.rs` states the contract).

This script never edits the repository's sources. It copies the tree, less
`reports/`, into a scratch directory (`git archive` of HEAD, or the working
tree with `--from-worktree`), and there it runs three legs:

  unmodified  each host test on the kernel as committed: every site refuses;
  mutant      `TypeChecker::check_type` patched to accept exactly the planted
              pair, with CLEAN_P3_KERNEL_UNDER_TEST naming the mutant: a site
              that mints is a pinned gap, a refusal names who stopped it;
  undeclared  the mutant again, clean-kernel's test only, WITHOUT the variable:
              it must fail with `P3 WRONG ACCEPT`, so the ordinary test is
              shown to catch this mutant.

The scratch tree AND its target directory are deleted on exit, failure
included, unless `--keep`; the repository's own `infer.rs` is hashed before and
after and must not move. The target directory must not exist when the run
starts and is never shared: cargo names a workspace member's artifacts by its
path relative to the workspace root, not by the checkout it lives in, so a
target directory shared with another checkout would serve that checkout's next
build the mutant `clean-kernel` (2026-11-13: it did, and that checkout's
ordinary test failed with `P3 WRONG ACCEPT`; `docs/DECISIONS.md`).
With `--write-record` (HEAD mode on a clean tree only) the measurement is
written to RECORD; the host tests' `committed_record_matches_the_pins` keep that
file and the pins in step.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = "reports/self-proof-p3-2026-11-12/patched_kernel_control.json"
PACKAGES = ("clean-kernel", "clean-olean", "clean-mathverse")
TEST = "patched_kernel_control"
MODE_ENV = "CLEAN_P3_KERNEL_UNDER_TEST"
MUTANT_ID = "check-type-nat-zero-false"
WRONG_ACCEPT = "P3 WRONG ACCEPT"
CENSUS = "data/authority_sites.json"

MUTATION_FILE = "crates/clean-kernel/src/tc/infer.rs"
ANCHOR = "        if self.is_le(&inferred, expected) {\n"
REPLACEMENT = (
    "        if self.is_le(&inferred, expected)\n"
    "            || (*e == Expr::const_str(\"Nat.zero\") && *expected == Expr::const_str(\"False\"))\n"
    "        {\n"
)

# Every mint P1's census (CENSUS) says rests on clean-kernel, keyed by
# `file#symbol`, with the probe that drives it. `exercised` means the probe
# calls this function, or calls the function that calls it on the planted
# declaration; `entry` means only the kernel entry the site calls is measured,
# by the named probe, and the site itself is not driven. A census site missing
# here stops the run: a new mint must be classified before a record is minted.
EXERCISED = "exercised"
ENTRY = "entry only"
COVERAGE: dict[str, tuple[str, str, str]] = {
    # ---- Clean ----
    "crates/clean-auto/src/proved_gate.rs#kernel_recheck_proved_grade": (ENTRY, "kernel.check_type", "the API builds its own term from an ay certificate, so the planted pair cannot be supplied"),
    "crates/clean-compiler/src/emit_trust_ir_tv.rs#attempt_certify": (ENTRY, "kernel.add_decl", "the claim is built by the translation-validation producer from a trust-ir function"),
    "crates/clean-mathverse/src/cli/parallel_verify_replay.rs#check_value_bearing": (ENTRY, "kernel.check_decl_readonly_strict", "`stamp-verified --parallel` needs an .olean closure converted to shards; its kernel call is check_decl_readonly_with_heartbeat"),
    "crates/clean-mathverse/src/coq/shard.rs#write_constant_checked": (ENTRY, "kernel.add_decl", "needs a Coq dump"),
    "crates/clean-mathverse/src/coq/shard.rs#write_inductive_checked": (ENTRY, "kernel.add_decl", "needs a Coq dump; an inductive, not a theorem"),
    "crates/clean-mathverse/src/graduate/intake.rs#carry_definition": (ENTRY, "kernel.add_decl", "a carried definition, not a theorem"),
    "crates/clean-mathverse/src/graduate/intake.rs#carry_opaque": (ENTRY, "kernel.add_decl", "a carried opaque, not a theorem"),
    "crates/clean-mathverse/src/graduate/intake.rs#carry_theorem": (ENTRY, "kernel.add_decl", "graduation fixtures (request, baseline) are not built; it calls Environment::add_decl"),
    "crates/clean-mathverse/src/graduate/intake.rs#evaluate_candidate": (EXERCISED, "mathverse.trust_sign.attest", "its verdict is graduate::recheck::recheck_and_classify, the function attest calls"),
    "crates/clean-mathverse/src/hol/isabelle_pure_verify/batch.rs#try_bridge_discharge": (ENTRY, "kernel.add_decl", "needs Isabelle dumps"),
    "crates/clean-mathverse/src/hol/isabelle_pure_verify/batch.rs#verify_one_with_translations": (ENTRY, "kernel.add_decl", "needs Isabelle dumps"),
    "crates/clean-mathverse/src/hol/isabelle_pure_verify/emit_defs.rs#emit_synthesized_def_consts": (ENTRY, "kernel.check_decl_readonly_strict", "needs Isabelle dumps; its kernel call is check_decl_readonly_strict"),
    "crates/clean-mathverse/src/hol/isabelle_verified.rs#import_verified_hol_proofs": (ENTRY, "kernel.add_decl", "needs Isabelle dumps"),
    "crates/clean-mathverse/src/lean4/mathlib_kernel_verify.rs#verify_mathlib_lemmas_kernel": (ENTRY, "kernel.check_type", "needs a Mathlib lemma table"),
    "crates/clean-mathverse/src/lean4/shard_verify.rs#verify_shard_into_env": (ENTRY, "kernel.add_decl", "a second shard engine; the probed one is verify/incremental"),
    "crates/clean-mathverse/src/library.rs#MathverseLibrary::submit_proven": (ENTRY, "reference.add_checked", "admits the submission through ReferenceKernel::add_checked over an empty Environment::default(), where neither `False` nor `Nat.zero` is resident"),
    "crates/clean-mathverse/src/nnverify_ieee754_shard.rs#verify_nnverify_ieee754_shard": (ENTRY, "kernel.check_type", "fixed NN-verification shard"),
    "crates/clean-mathverse/src/shard_verify/constant_verify.rs#verify_single_constant": (ENTRY, "kernel.add_decl", "starts from Environment::new()"),
    "crates/clean-mathverse/src/trust_sign/reauditor.rs#reaudit_one": (EXERCISED, "mathverse.trust_sign.attest", "reaudit_one's verdict is attest's"),
    "crates/clean-mathverse/src/verify/foreign/mod.rs#verify_single_constant": (ENTRY, "kernel.add_decl", "foreign-system shards not built"),
    "crates/clean-mathverse/src/verify/incremental/mod.rs#accept_unsafe_definition_type_only": (ENTRY, "kernel.add_decl", "the unsafe-definition branch; the planted theorem does not take it"),
    "crates/clean-mathverse/src/verify/incremental/mod.rs#reconstruct_and_replay_one": (EXERCISED, "mathverse.development_manifest", "on the shard engine's path for every constant"),
    "crates/clean-mathverse/src/verify/incremental/mod.rs#retry_motive_universe_bump_ladder": (ENTRY, "kernel.add_decl", "a retry branch the planted theorem does not take"),
    "crates/clean-mathverse/src/verify/incremental/mod.rs#retry_speculative_motive_universe": (ENTRY, "kernel.add_decl", "a retry branch the planted theorem does not take"),
    "crates/clean-mathverse/src/verify/incremental/mod.rs#try_accept_seeded_duplicate": (ENTRY, "kernel.check_type", "the duplicate-name branch; the planted theorem is not a duplicate"),
    "crates/clean-mathverse/src/verify/incremental/mod.rs#try_add_constant": (EXERCISED, "mathverse.development_manifest", "on the shard engine's path for every constant"),
    "crates/clean-mathverse/src/verify/incremental/mod.rs#try_add_decl": (EXERCISED, "mathverse.development_manifest", "the add_decl that mints AddConstResult::KernelVerified"),
    "crates/clean-mathverse/src/verify/sharded.rs#verify_module": (EXERCISED, "mathverse.lean4.kernel_verify_const", "its per-constant verdict is kernel_verify_const_with_heartbeat"),
    "crates/clean-server/src/handlers/swarm.rs#recheck_and_classify_session": (ENTRY, "kernel.add_decl", "a clean-server session is not opened; it calls Environment::add_decl on the session overlay"),
    # ---- Trust, at the census's pinned commit (never built here) ----
    "crates/trust-cert-meter/src/lib.rs#grade": (ENTRY, "kernel.check_type", "Trust is not built by this control"),
    "crates/trust-certify/src/calculus_row.rs#certify_calculus_row": (ENTRY, "reference.check_closed_term", "Trust is not built; the row's goal shape is fixed"),
    "crates/trust-certify/src/reference_mint.rs#IslandReference::check_judgment": (ENTRY, "reference.check_closed_term", "Trust is not built; the call it makes is the probed one"),
    "crates/trust-certify/src/reference_mint.rs#check_closed_in": (ENTRY, "reference.check_closed_term", "Trust is not built; the call it makes is the probed one"),
    "crates/trust-certify/src/reference_mint.rs#check_island_judgment_in": (ENTRY, "reference.check_closed_term", "Trust is not built; the call it makes is the probed one"),
    "crates/trust-certify/src/reference_mint.rs#check_refutation": (ENTRY, "reference.check_closed_term", "Trust is not built; the call it makes is the probed one"),
    "crates/trust-certify/src/reference_mint.rs#check_registered_with": (ENTRY, "reference.add_checked", "Trust is not built; the call it makes is the probed one"),
    "crates/trust-cg-bridge/src/compiler_input_capture/semr_scalar/program.rs#CanonicalScalarProgramEnvironment::check": (ENTRY, "reference.check_closed_term", "Trust is not built; fixed goal shape"),
    "crates/trust-cg-bridge/src/frame_step_evidence.rs#FrameTheoremEnvironment::prove_entry_step": (ENTRY, "reference.check_closed_term", "Trust is not built; fixed goal shape"),
    "crates/trust-cg-bridge/src/frame_step_evidence.rs#FrameTheoremEnvironment::replay_entry_step": (ENTRY, "reference.check_closed_term", "Trust is not built; fixed goal shape"),
    "crates/trust-cg-bridge/src/frame_step_evidence/caller.rs#CallerFrameEnvironment::prove_conditional_frame": (ENTRY, "reference.check_closed_term", "Trust is not built; fixed goal shape"),
    "crates/trust-cg-bridge/src/frame_step_evidence/caller.rs#CallerFrameEnvironment::replay_conditional_frame": (ENTRY, "reference.check_closed_term", "Trust is not built; fixed goal shape"),
    "crates/trust-cg-bridge/src/frame_step_evidence/caller/callee.rs#CalleeFrameEnvironment::prove_separate_callee": (ENTRY, "reference.check_closed_term", "Trust is not built; fixed goal shape"),
    "crates/trust-cg-bridge/src/frame_step_evidence/caller/callee.rs#CalleeFrameEnvironment::replay_separate_callee": (ENTRY, "reference.check_closed_term", "Trust is not built; fixed goal shape"),
    "crates/trust-clean/src/certification/pipeline.rs#CertificationPipeline::certify": (ENTRY, "kernel.check_type", "Trust is not built by this control"),
    "crates/trust-clean/src/certification/pipeline.rs#CertificationPipeline::certify_from_solver_proof": (ENTRY, "kernel.check_type", "Trust is not built by this control"),
    "crates/trust-clean/src/olean_replay.rs#replay_closed_declarations": (ENTRY, "kernel.add_decl", "Trust is not built by this control"),
    "crates/trust-clean/src/whole_program.rs#certify_function_in_graph": (ENTRY, "kernel.add_decl", "Trust is not built by this control"),
    "crates/trust-router/src/ay_certify.rs#certify_lia_two_bound_incomplete_control": (ENTRY, "kernel.check_type", "Trust is not built by this control"),
    "crates/trust-router/src/ay_certify.rs#certify_lia_two_bound_unsat": (ENTRY, "kernel.check_type", "Trust is not built by this control"),
    "crates/trust-spec-temporal/src/lib.rs#recheck_bound_clean_kernel": (ENTRY, "kernel.check_type", "Trust is not built by this control"),
    "crates/trust-spec-temporal/src/lib.rs#recheck_bound_clean_kernel_finite": (ENTRY, "kernel.check_type", "Trust is not built by this control"),
}


def fail(message: str) -> None:
    print(f"patched_kernel_control: {message}", file=sys.stderr)
    raise SystemExit(1)


def git(*args: str) -> str:
    return subprocess.run(["git", "-C", str(ROOT), *args], check=True, capture_output=True, text=True).stdout


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def resolve_targo() -> str:
    out = subprocess.run([str(ROOT / "scripts/rust_frontend.sh"), "--targo"], capture_output=True)
    if out.returncode != 0 or not os.fsdecode(out.stdout).strip():
        fail(f"cannot resolve targo through scripts/rust_frontend.sh: {os.fsdecode(out.stderr).strip()}")
    return os.fsdecode(out.stdout).removesuffix("\n")


# The tracked `reports/` (8 GB on 2026-11-16, 95% of the tree) is evidence no
# leg reads: the legs build and run three integration tests, and the one file
# under `reports/` they name (RECORD) is read only by the record test, which
# the legs do not run. Copying it filled the shared volume (2026-11-17), so the
# scratch tree omits it; a leg that did read it would fail on the missing file.
EXCLUDED_PREFIX = b"reports/"


def copy_tree(dest: Path, from_worktree: bool) -> None:
    """The tracked tree minus `reports/` into `dest`, every file stamped NOW
    (`tar -m`): a scratch build directory kept across runs then always sees the
    copy as newer than whatever it built last, a mutant build included."""
    dest.mkdir(parents=True)
    if from_worktree:
        listed = subprocess.run(
            ["git", "-C", str(ROOT), "ls-files", "-z", "-c", "-o", "--exclude-standard"],
            check=True, capture_output=True,
        ).stdout.split(b"\0")
        names = b"\0".join(n for n in listed if n and not n.startswith(EXCLUDED_PREFIX)
                           and (ROOT / os.fsdecode(n)).is_file()) + b"\0"
        pack = subprocess.Popen(["tar", "-c", "--null", "-T", "-", "-f", "-"], cwd=ROOT, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        assert pack.stdin is not None
        pack.stdin.write(names)
        pack.stdin.close()
    else:
        pack = subprocess.Popen(["git", "-C", str(ROOT), "archive", "--format=tar", "HEAD", "--", ".",
                                 f":(exclude){EXCLUDED_PREFIX.decode()}"], stdout=subprocess.PIPE)
    unpack = subprocess.run(["tar", "-x", "-m", "-f", "-", "-C", str(dest)], stdin=pack.stdout)
    if pack.wait() != 0 or unpack.returncode != 0:
        fail("copying the tree into the scratch directory failed")
    (dest.parent / ".metadata_never_index").touch()


def mutate(tree: Path) -> dict[str, str]:
    path = tree / MUTATION_FILE
    text = path.read_text()
    if text.count(ANCHOR) != 1:
        fail(f"the mutation anchor occurs {text.count(ANCHOR)} times in {MUTATION_FILE}, not once")
    original = sha256(path)
    path.write_text(text.replace(ANCHOR, REPLACEMENT))
    return {"original_sha256": original, "mutant_sha256": sha256(path)}


def run_leg(leg: str, package: str, tree: Path, target: Path, logs: Path, targo: str, declare: bool) -> dict:
    command = [targo, "--unverified", "test", "--locked", "-p", package, "--test", TEST, "--", "--exact", TEST, "--nocapture"]
    env = {k: v for k, v in os.environ.items() if k != MODE_ENV}
    env["CARGO_TARGET_DIR"] = str(target)
    if declare:
        env[MODE_ENV] = MUTANT_ID
    log = logs / f"{leg}-{package}.log"
    print(f"patched_kernel_control: {leg} leg, {package} (log {log})", flush=True)
    with log.open("w") as out:
        status = subprocess.run(command, cwd=tree, env=env, stdout=out, stderr=subprocess.STDOUT).returncode
    text = log.read_text(errors="replace")
    rows, sites = [], {}
    for line in text.splitlines():
        cells = line.split("\t")
        if cells[0] == "P3_ROW" and len(cells) == 7 and cells[1] == package:
            rows.append({"site": cells[3], "verdict": cells[4], "by": cells[5], "detail": cells[6]})
        elif cells[0] == "P3_SITE" and len(cells) == 4 and cells[1] == package:
            sites[cells[2]] = cells[3]
    shown = ["targo", *command[1:]]
    if declare:
        shown = [f"{MODE_ENV}={MUTANT_ID}", *shown]
    return {"leg": leg, "package": package, "command": " ".join(shown), "exit_status": status,
            "wrong_accept_reported": WRONG_ACCEPT in text, "rows": rows, "sites": sites, "log": text}


def census_coverage() -> list[dict]:
    census = json.loads((ROOT / CENSUS).read_text())
    seen, out = set(), []
    for side in ("clean", "trust"):
        for site in census[side]["sites"]:
            checker = site.get("checker")
            if site.get("class") != "mint" or not isinstance(checker, dict) or checker.get("kind") != "clean-kernel":
                continue
            key = f"{site['file']}#{site['symbol']}"
            if key in seen:
                continue
            seen.add(key)
            if key not in COVERAGE:
                fail(f"census site {side}:{key} rests on clean-kernel and has no row in COVERAGE; classify it")
            how, probe, note = COVERAGE[key]
            out.append({"census": side, "site": key, "checker": f"clean-kernel/{checker.get('entry')}/{checker.get('theory')}",
                        "coverage": how, "probe": probe, "note": note})
    stale = sorted(set(COVERAGE) - seen)
    if stale:
        fail(f"COVERAGE names sites the census no longer lists as clean-kernel mints: {stale}")
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--packages", default=",".join(PACKAGES))
    parser.add_argument("--work-dir", type=Path, help="scratch root (default: a new temporary directory)")
    parser.add_argument("--keep", action="store_true",
                        help="keep the scratch tree and its target directory (which then holds a mutant clean-kernel)")
    parser.add_argument("--from-worktree", action="store_true", help="copy the working tree, not HEAD")
    parser.add_argument("--write-record", action="store_true", help=f"write {RECORD}")
    args = parser.parse_args()
    packages = [p for p in args.packages.split(",") if p]
    if unknown := sorted(set(packages) - set(PACKAGES)):
        fail(f"unknown packages {unknown}")
    if not os.environ.get("HEAVY_GATE_HELD"):
        fail("run me under scripts/heavy_gate.sh run <gb> p3-patched-kernel-control -- python3 scripts/patched_kernel_control.py ...")
    if args.write_record:
        if args.from_worktree:
            fail("--write-record measures a commit: drop --from-worktree")
        dirty = [line for line in git("status", "--porcelain", "--untracked-files=no").splitlines() if not line.endswith(RECORD)]
        if dirty:
            fail(f"--write-record needs a clean tracked tree; dirty: {dirty}")
    coverage = census_coverage()
    head = git("rev-parse", "HEAD").strip()
    real_infer = sha256(ROOT / MUTATION_FILE)
    targo = resolve_targo()
    work = args.work_dir.resolve() if args.work_dir else Path(tempfile.mkdtemp(prefix="p3-patched-kernel-"))
    tree, target, logs = work / "tree", work / "target", work / "logs"
    for owned in (tree, target):
        if owned.exists():
            fail(f"{owned} exists; this run builds a mutant kernel and must own a fresh tree and target directory")
    logs.mkdir(parents=True, exist_ok=True)
    legs: list[dict] = []
    try:
        copy_tree(tree, args.from_worktree)
        for package in packages:
            legs.append(run_leg("unmodified", package, tree, target, logs, targo, declare=False))
        mutation = mutate(tree)
        for package in packages:
            legs.append(run_leg("mutant", package, tree, target, logs, targo, declare=True))
        if "clean-kernel" in packages:
            legs.append(run_leg("undeclared", "clean-kernel", tree, target, logs, targo, declare=False))
    finally:
        if args.keep:
            print(f"patched_kernel_control: KEPT {tree} and {target}; the target holds a mutant clean-kernel: "
                  "never point another build at it", file=sys.stderr)
        else:
            for owned in (tree, target):
                if owned.exists():
                    shutil.rmtree(owned)
    if sha256(ROOT / MUTATION_FILE) != real_infer:
        fail(f"{MUTATION_FILE} in the repository changed during the run")

    problems = []
    for leg in legs:
        expected_ok = leg["leg"] != "undeclared"
        if expected_ok and leg["exit_status"] != 0:
            problems.append(f"{leg['leg']} {leg['package']}: exit {leg['exit_status']}")
        if not expected_ok and (leg["exit_status"] == 0 or not leg["wrong_accept_reported"]):
            problems.append(f"undeclared clean-kernel: exit {leg['exit_status']}, `{WRONG_ACCEPT}` reported: {leg['wrong_accept_reported']}")
    sites = []
    for package in packages:
        clean = next(l for l in legs if l["leg"] == "unmodified" and l["package"] == package)
        mutant = next(l for l in legs if l["leg"] == "mutant" and l["package"] == package)
        if [r["site"] for r in clean["rows"]] != [r["site"] for r in mutant["rows"]] or not clean["rows"]:
            problems.append(f"{package}: the legs observed different site lists")
            continue
        for before, after in zip(clean["rows"], mutant["rows"]):
            sites.append({
                "package": package, "site": before["site"], "mints": mutant["sites"].get(before["site"], ""),
                "unmodified": {"verdict": before["verdict"], "by": before["by"], "detail": before["detail"]},
                "mutant": {"verdict": after["verdict"], "stopped_by": after["by"], "detail": after["detail"]},
            })
    for leg in legs:
        print(f"patched_kernel_control: {leg['leg']:10} {leg['package']:16} exit {leg['exit_status']}")
    for row in sites:
        print(f"  {row['package']:16} {row['site']:42} mutant {row['mutant']['verdict']:8} by {row['mutant']['stopped_by']}")
    if problems:
        for problem in problems:
            print(f"patched_kernel_control: FAILED: {problem}", file=sys.stderr)
        print(f"patched_kernel_control: logs in {logs}", file=sys.stderr)
        return 1

    gaps = [r for r in sites if r["mutant"]["verdict"] == "minted"]
    independent = [r for r in sites if r["mutant"]["verdict"] == "refused" and r["mutant"]["stopped_by"] in ("clean-ck0", "lean-kernel")]
    record = {
        "schema": "clean.patched_kernel_control.v1",
        "unit": "P3, docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md",
        "minted_by": "scripts/patched_kernel_control.py --write-record",
        "generated_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "measured_commit": head,
        "tree": "git archive of measured_commit without reports/, built in a scratch directory with targo --unverified (no proof claim)",
        "toolchain": subprocess.run([targo, "--unverified", "--version"], capture_output=True, text=True).stdout.strip(),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "mutation": {"id": MUTANT_ID, "file": MUTATION_FILE, "anchor": ANCHOR, "replacement": REPLACEMENT, **mutation,
                     "scratch_tree_and_target_deleted": not args.keep, "repository_file_unchanged": True},
        "legs": [{k: leg[k] for k in ("leg", "package", "command", "exit_status", "wrong_accept_reported")} for leg in legs],
        "summary": {
            "sites": len(sites),
            "minted_under_mutant": len(gaps),
            "stopped_by_an_independent_member": len(independent),
            "stopped_by_the_same_kernel_elsewhere": len(sites) - len(gaps) - len(independent),
            "reading": "Every site that minted under the mutant is a pinned gap: nothing but clean-kernel stands behind it. "
                       "P3's done-when (no accepted row) can hold only after the authority flip (plan rung 2).",
        },
        "sites": sites,
        "census_coverage": coverage,
    }
    if args.write_record:
        path = ROOT / RECORD
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(record, indent=1, ensure_ascii=False) + "\n")
        print(f"patched_kernel_control: wrote {RECORD}")
    print(f"patched_kernel_control: {len(sites)} sites, {len(gaps)} minted under the mutant, "
          f"{len(independent)} stopped by an independent member")
    return 0


if __name__ == "__main__":
    sys.exit(main())
