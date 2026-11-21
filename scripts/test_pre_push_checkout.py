#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""scripts/githooks/pre-push judges the PUSHED COMMIT, in a clean checkout of it,
by the PUSHER's hook.

Verifier r8b (2026-09-25): the hook ran every leg over the WORKING TREE, so a
pushed commit carrying a failing test passed whenever the tree held an
uncommitted fix, or when the pushed ref was not HEAD. The hook's outer role now
checks each pushed commit out, pristine, and runs its legs there
(`CLEAN_PUSH_CHECKOUT`); see the header of scripts/githooks/pre-push.

Verifier r9 recheck (2026-09-25): for one revision the outer role ran the
PUSHED COMMIT's own hook in that checkout, so a commit whose hook said `exit 0`
pushed with no leg run -- R10 included. The outer role now runs ITSELF there
(arm 10), and runs its own copy of check_gate_registry.py's R10 over the commit
first (arm 11).

Each arm builds a small git repository whose committed
`scripts/check_hook_coverage.py` -- the first thing the hook's inner role runs
-- is a STUB standing in for the pushed commit's legs: it prints where it ran
and what it saw (`STUB verdict: BAD` when a file named BAD is in its tree) and
exits 1, so nothing after it runs. The REAL hook is run as git would run it
(cwd in the working tree, `<remote> <url>` as arguments, ref lines on stdin).

Usage: python3 scripts/test_pre_push_checkout.py   (exit 0 iff every arm holds)
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HOOK = ROOT / "scripts/githooks/pre-push"
ZERO = "0" * 40
PEER = ("peer", "https://example.invalid/peer.git")

STUB = """#!/usr/bin/env python3
import os, subprocess, sys
head = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
ranges = os.environ.get("CLEAN_PUSH_RANGES", "").strip()
print(f"STUB ran in {os.path.realpath(os.getcwd())} at {head} "
      f"checkout={os.environ.get('CLEAN_PUSH_CHECKOUT', '')} ranges=[{ranges}]")
print(f"STUB EV3 head={head} published=[{os.environ.get('CLEAN_EV3_PUBLISHED_MAIN', '<unset>')}]")
print("STUB verdict: BAD is in the pushed tree" if os.path.exists("BAD") else "STUB verdict: clean")
print("STUB corpus: " + (open("theories/Required.lean").read().strip()
      if os.path.exists("theories/Required.lean") else "ABSENT"))
sys.exit(1)
"""
EMPTY_REGISTRY = '{"rows": []}\n'

_GIT_LOCATION = ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
                 "GIT_OBJECT_DIRECTORY", "GIT_PREFIX")


def _env() -> dict[str, str]:
    env = {k: v for k, v in os.environ.items()
           if k not in _GIT_LOCATION and k not in (
               "CLEAN_PUSH_CHECKOUT", "CLEAN_PUSH_RANGES", "CLEAN_EV3_PUBLISHED_MAIN",
               "CLEAN_EV3_SOURCE_ROOT")}
    env.update(GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t",
               GIT_COMMITTER_EMAIL="t@t")
    return env


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", *args], cwd=repo, env=_env(), capture_output=True,
                          text=True, check=True).stdout.strip()


def commit(repo: Path, msg: str) -> str:
    git(repo, "add", "-A")
    git(repo, "commit", "-qm", msg)
    return git(repo, "rev-parse", "HEAD")


def hook(repo: Path, stdin: str, extra_env: dict[str, str] | None = None, *,
         destination: tuple[str, str] = PEER) -> tuple[int, str]:
    env = _env()
    env.update(extra_env or {})
    proc = subprocess.run(["bash", str(HOOK), *destination],
                          cwd=repo, env=env, input=stdin, capture_output=True, text=True,
                          timeout=120)
    return proc.returncode, proc.stdout + proc.stderr


def build(tmp: Path) -> tuple[Path, str, str]:
    """A repo with GOOD (clean) and BAD (carries a file BAD) commits."""
    repo = tmp / "repo"
    (repo / "scripts").mkdir(parents=True)
    (repo / "data").mkdir()
    git(repo, "init", "-q", "-b", "main")
    (repo / "scripts/check_hook_coverage.py").write_text(STUB)
    (repo / "data/gate_registry.json").write_text(EMPTY_REGISTRY)
    (repo / "theories").mkdir()
    (repo / "theories/Required.lean").write_text("complete tracked corpus\n")
    (repo / "README").write_text("x\n")
    good = commit(repo, "good")
    (repo / "BAD").write_text("a failing pushed commit\n")
    bad = commit(repo, "bad")
    return repo, good, bad


def line(sha: str, ref: str = "refs/heads/main") -> str:
    return f"{ref} {sha} {ref} {ZERO}\n"


def arms(tmp: Path) -> list[str]:
    problems = []

    def require(name: str, ok: bool, out: str) -> None:
        print(f"  [{'ok' if ok else 'FAIL'}] {name}")
        if not ok:
            problems.append(f"{name}:\n{out}")

    # 1. The measured shape: the pushed commit fails, the working tree holds an
    #    uncommitted fix (BAD deleted). The pushed commit must be judged.
    repo, good, bad = build(tmp / "a1")
    (repo / "BAD").unlink()
    rc, out = hook(repo, line(bad))
    require("1 a failing pushed commit is RED although the working tree holds the fix",
            rc != 0 and f"at {bad}" in out and "verdict: BAD is in the pushed tree" in out, out)
    # 2. The converse control: a clean pushed commit is judged clean although
    #    the working tree carries the failure (an untracked BAD).
    git(repo, "checkout", "-q", good)
    (repo / "BAD").write_text("junk in the working tree\n")
    rc, out = hook(repo, line(good))
    require("2 a clean pushed commit is judged clean although the working tree carries BAD",
            f"at {good} checkout={good}" in out and "STUB verdict: clean" in out
            and "verdict: BAD" not in out, out)
    # 3. The pushed ref is not HEAD: the checkout is of the pushed sha.
    rc, out = hook(repo, line(bad, "refs/heads/other"))
    require("3 a pushed ref that is not HEAD is judged at its own commit",
            rc != 0 and f"at {bad}" in out and "verdict: BAD" in out, out)
    # 4. Two refs, two commits: each gated, each fed only its own ref line.
    rc, out = hook(repo, line(good) + line(bad, "refs/heads/other"))
    require("4 two pushed commits are each gated with their own refs",
            rc != 0 and f"at {good}" in out and f"at {bad}" in out
            and f"at {good} checkout={good} ranges=[{ZERO} {good}]" in out, out)
    # 5. A deletion-only push gates nothing.
    rc, out = hook(repo, f"(delete) {ZERO} refs/heads/gone {bad}\n")
    require("5 a deletion-only push is let through without a checkout",
            rc == 0 and "STUB ran" not in out, out)
    # 6. The inner role refuses a tree that is not a pristine checkout of its sha:
    #    here HEAD is `good` but an untracked BAD is present.
    rc, out = hook(repo, line(good), {"CLEAN_PUSH_CHECKOUT": good})
    require("6 CLEAN_PUSH_CHECKOUT set by hand over a dirty tree is a refusal",
            rc != 0 and "not a" in out and "STUB ran" not in out, out)
    # 7. ...and over a tree at another commit.
    (repo / "BAD").unlink()
    rc, out = hook(repo, line(bad), {"CLEAN_PUSH_CHECKOUT": bad})
    require("7 CLEAN_PUSH_CHECKOUT naming a commit HEAD is not is a refusal",
            rc != 0 and "STUB ran" not in out, out)
    # 8. Something else already at the checkout path is refused and left alone.
    repo8, good8, _ = build(tmp / "a8")
    squatter = repo8.parent / f".{repo8.name}.pre-push"
    squatter.mkdir()
    (squatter / "keep").write_text("not ours\n")
    rc, out = hook(repo8, line(good8))
    require("8 a directory at the checkout path that is not our worktree is refused, untouched",
            rc != 0 and (squatter / "keep").read_text() == "not ours\n"
            and "STUB ran" not in out, out)
    # 9. Run by hand with no refs: the commit HEAD names is gated, not the tree.
    rc, out = hook(repo, "")
    require("9 run by hand, the hook gates HEAD's commit",
            f"at {good}" in out and "STUB verdict: clean" in out, out)
    # 10. Verifier r9 recheck: the pushed commit's OWN hook says `exit 0`. It is
    #     not run -- the pusher's hook runs its legs over the commit anyway.
    (repo / "scripts/githooks").mkdir(parents=True)
    (repo / "scripts/githooks/pre-push").write_text(
        "#!/usr/bin/env bash\necho 'C: this commit skips its own legs'; exit 0\n")
    (repo / "BAD").write_text("a failing pushed commit\n")
    neutered = commit(repo, "a failing commit whose own hook exits 0")
    git(repo, "checkout", "-q", good)
    rc, out = hook(repo, line(neutered, "refs/heads/other"))
    require("10 a pushed commit whose own hook says `exit 0` is still judged by the pusher's",
            rc != 0 and f"at {neutered}" in out and "verdict: BAD" in out
            and "skips its own legs" not in out, out)
    # 11. ...and a pinned gate script the commit edits without re-pinning, with
    #     its own registry check neutered, is refused by the PUSHER's R10.
    repo11, good11, _ = build(tmp / "a11")
    git(repo11, "checkout", "-q", good11)
    gate = repo11 / "scripts/check_x.py"
    gate.write_text("import sys\nsys.exit(1)\n")
    (repo11 / "data/gate_registry.json").write_text(json.dumps({"rows": [{
        "id": "check_x", "path": "scripts/check_x.py",
        "demonstrated": {"script_sha256": hashlib.sha256(gate.read_bytes()).hexdigest()}}]}))
    commit(repo11, "a pinned gate")
    gate.write_text("import sys\nsys.exit(0)  # gutted, pin not moved\n")
    (repo11 / "scripts/check_gate_registry.py").write_text("raise SystemExit(0)\n")
    (repo11 / "scripts/githooks").mkdir(parents=True)
    (repo11 / "scripts/githooks/pre-push").write_text("#!/usr/bin/env bash\nexit 0\n")
    gutted = commit(repo11, "gut the gate, the registry check and the hook")
    git(repo11, "checkout", "-q", good11)
    rc, out = hook(repo11, line(gutted, "refs/heads/other"))
    require("11 an unpinned gate edit is refused by the pusher's R10 though the commit "
            "neutered its own registry check",
            rc != 0 and "R10 PUSHED: check_x is pinned at" in out, out)
    # 12. One push at a time per repository: while another push holds the
    #     checkout's lock the hook WAITS. The lock is flock(2), which the kernel
    #     drops with its holder; the `mkdir` lock it replaced took over a dead
    #     holder's lock by `rm -rf` + `mkdir`, and two pushes racing on one dead
    #     holder could both proceed in one checkout.
    holder = os.open(repo / ".git" / "clean-pre-push.flock", os.O_RDWR | os.O_CREAT, 0o644)
    fcntl.flock(holder, fcntl.LOCK_EX)
    proc = subprocess.Popen(["bash", str(HOOK), *PEER],
                            cwd=repo, env=_env(), stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    assert proc.stdin is not None
    proc.stdin.write(line(good))
    proc.stdin.close()
    time.sleep(3)
    waited = proc.poll() is None
    os.close(holder)
    assert proc.stdout is not None
    out = proc.stdout.read()
    proc.wait(timeout=120)
    require("12 a push waits while another push holds the pre-push checkout",
            waited and f"at {good}" in out, out)
    # 13. A new linked checkout inherits sparsity from its source. The real
    # outer hook must restore tracked inputs before either checker runs.
    repo13, good13, bad13 = build(tmp / "a13")
    git(repo13, "checkout", "-q", good13)
    git(repo13, "sparse-checkout", "init", "--cone")
    git(repo13, "sparse-checkout", "set", "scripts", "data")
    assert not (repo13 / "theories/Required.lean").exists()
    source_status = git(repo13, "status", "--porcelain")
    rc, out = hook(repo13, line(good13))
    require("13 a sparse source creates a complete checkout of the pushed SHA",
            rc != 0 and f"at {good13}" in out
            and "STUB corpus: complete tracked corpus" in out
            and git(repo13, "config", "--bool", "core.sparseCheckout") == "true"
            and not (repo13 / "theories/Required.lean").exists()
            and git(repo13, "status", "--porcelain") == source_status, out)
    # 14. Force-checkout and clean alone leave a reused sparse index sparse.
    checkout13 = repo13.parent / f".{repo13.name}.pre-push"
    git(checkout13, "sparse-checkout", "init", "--cone")
    git(checkout13, "sparse-checkout", "set", "scripts", "data")
    assert not (checkout13 / "theories/Required.lean").exists()
    rc, out = hook(repo13, line(bad13))
    require("14 reuse rehydrates the exact other pushed SHA before its checker",
            rc != 0 and f"at {bad13}" in out and "verdict: BAD" in out
            and "STUB corpus: complete tracked corpus" in out
            and git(checkout13, "config", "--bool", "core.sparseCheckout") == "false"
            and not git(checkout13, "status", "--porcelain", "--ignored"), out)
    # 15. Pristine status alone does not prove a directly invoked inner tree
    # contains its tracked inputs.
    rc, out = hook(repo13, line(good13), {"CLEAN_PUSH_CHECKOUT": good13})
    require("15 direct inner invocation refuses a pristine sparse tree",
            rc != 0 and "not a full tracked tree" in out and "STUB ran" not in out, out)
    # 16. A real command failure must stop before R10 or a checker. This wrapper
    # changes only this isolated fixture's Git hydration command.
    wrapper = tmp / "git-control"
    wrapper.mkdir()
    real_git = shutil.which("git")
    assert real_git
    fake_git = wrapper / "git"
    fake_git.write_text("#!/usr/bin/env python3\nimport os, sys\n"
                        "if sys.argv[-2:] == ['sparse-checkout', 'disable']:\n"
                        " print('CONTROL hydration refused'); sys.exit(78)\n"
                        f"os.execv({real_git!r}, [{real_git!r}, *sys.argv[1:]])\n")
    fake_git.chmod(0o755)
    rc, out = hook(repo13, line(good13), {"PATH": str(wrapper) + os.pathsep + os.environ["PATH"]})
    require("16 hydration failure refuses before R10 and before any checker",
            rc != 0 and "CONTROL hydration refused" in out
            and "could not restore the full tracked tree" in out
            and "GATE_REGISTRY_PUSHED" not in out and "STUB ran" not in out, out)
    # 17. Hydration belongs inside the same lock as checkout and all its reads.
    git(checkout13, "sparse-checkout", "init", "--cone")
    git(checkout13, "sparse-checkout", "set", "scripts", "data")
    common13 = Path(git(repo13, "rev-parse", "--git-common-dir"))
    if not common13.is_absolute():
        common13 = repo13 / common13
    holder = os.open(common13 / "clean-pre-push.flock", os.O_RDWR | os.O_CREAT, 0o644)
    fcntl.flock(holder, fcntl.LOCK_EX)
    proc = subprocess.Popen(["bash", str(HOOK), *PEER],
                            cwd=repo13, env=_env(), stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    assert proc.stdin
    proc.stdin.write(line(good13))
    proc.stdin.close()
    time.sleep(3)
    waited = proc.poll() is None and not (checkout13 / "theories/Required.lean").exists()
    os.close(holder)
    assert proc.stdout
    out = proc.stdout.read()
    proc.wait(timeout=120)
    require("17 hydration waits for the repository lock",
            waited and f"at {good13}" in out and "STUB corpus: complete tracked corpus" in out, out)
    # 18. Manually skipped entries can hide a missing tracked input even with
    # sparse mode disabled; the inner role must not accept that either.
    repo18, good18, _ = build(tmp / "a18")
    git(repo18, "checkout", "-q", good18)
    git(repo18, "update-index", "--skip-worktree", "theories/Required.lean")
    (repo18 / "theories/Required.lean").unlink()
    assert not git(repo18, "status", "--porcelain")
    rc, out = hook(repo18, line(good18), {"CLEAN_PUSH_CHECKOUT": good18})
    require("18 direct inner invocation refuses skipped tracked entries",
            rc != 0 and "not a full tracked tree" in out and "STUB ran" not in out, out)

    # The stub reports the parent selected by the real hook in the pristine
    # checkout of each pushed tip. The fixture uses only Git's local config and
    # the supplied ref tuples.
    ev3, published, candidate = build(tmp / "a19")
    fetch_url = "https://example.invalid/origin-fetch.git"
    push_url = "ssh://example.invalid/origin-push.git"
    second_push_url = "ssh://example.invalid/origin-mirror.git"
    git(ev3, "remote", "add", "origin", fetch_url)
    for url in (push_url, second_push_url):
        git(ev3, "config", "--add", "remote.origin.pushurl", url)
    git(ev3, "update-ref", "refs/remotes/origin/main", candidate)
    inherited = {"CLEAN_EV3_PUBLISHED_MAIN": candidate}
    main_update = f"refs/heads/feature {candidate} refs/heads/main {published}\n"

    def observation(head: str, prior: str = "") -> str:
        return f"STUB EV3 head={head} published=[{prior}]"

    rc, out = hook(ev3, line(published, "refs/heads/topic") + main_update,
                   inherited, destination=("origin", push_url))
    require("19 only the origin main tip inherits its advertised parent across mixed tips",
            rc != 0 and out.count("STUB EV3") == 2
            and observation(published) in out and observation(candidate, published) in out, out)

    rc, out = hook(ev3, main_update + line(candidate, "refs/heads/topic"), inherited,
                   destination=(second_push_url, second_push_url))
    require("20 a second configured push URL binds one origin main update when both refs share a tip",
            rc != 0 and out.count("STUB EV3") == 1
            and observation(candidate, published) in out, out)

    for name, refs, destination in (
        ("21 an origin branch push clears inherited EV3 context",
         line(candidate, "refs/heads/topic"), ("origin", push_url)),
        ("22 another remote's main push clears inherited EV3 context", line(candidate), PEER),
        ("23 a manual invocation clears inherited EV3 context", "", ("origin", push_url)),
    ):
        rc, out = hook(ev3, refs, inherited, destination=destination)
        require(name, rc != 0 and out.count("STUB EV3") == 1
                and observation(candidate) in out, out)

    rc, out = hook(ev3, main_update, destination=("origin", fetch_url))
    require("24 origin main refuses a destination outside the configured push URLs",
            rc == 1 and "cannot match the origin/main destination" in out
            and "gating " not in out and "STUB ran" not in out, out)

    def require_origin_refusal(name: str, ref_inputs: tuple[str, ...]) -> None:
        results = [hook(ev3, refs, destination=("origin", push_url)) for refs in ref_inputs]
        require(name, all(rc == 1 and "EV3 requires one origin/main update" in out
                          and "gating " not in out and "STUB ran" not in out
                          for rc, out in results),
                "\n".join(out for _, out in results))

    require_origin_refusal("25 origin main refuses malformed or trailing ref fields", (
        f"refs/heads/feature {candidate} refs/heads/main malformed\n",
        f"refs/heads/feature malformed refs/heads/main {published}\n",
        main_update.rstrip("\n") + " unexpected\n",
    ))
    require_origin_refusal("26 origin main refuses duplicate update rows", (main_update * 2,))
    require_origin_refusal("27 origin main refuses both creation and deletion tuples", (
        line(candidate),
        f"(delete) {ZERO} refs/heads/main {published}\n",
    ))

    # The reused inner checkout gets this push URL only from the original
    # worktree. The same raw row must still govern its advertised parent.
    checkout19 = ev3.parent / f".{ev3.name}.pre-push"
    worktree_push_url = "ssh://example.invalid/worktree-origin.git"
    git(ev3, "config", "extensions.worktreeConfig", "true")
    git(ev3, "config", "--worktree", "--add", "remote.origin.pushurl", worktree_push_url)
    inner = {"CLEAN_PUSH_CHECKOUT": candidate, "CLEAN_EV3_SOURCE_ROOT": str(ev3)}
    worktree_destination = ("origin", worktree_push_url)
    forged_rc, forged_out = hook(checkout19, main_update, {**inner, **inherited},
                                 destination=worktree_destination)
    rc, out = hook(checkout19, main_update, {**inner, "CLEAN_EV3_PUBLISHED_MAIN": published},
                   destination=worktree_destination)
    require("28 direct inner rejects a forged parent and accepts the corresponding raw row context",
            forged_rc == 1 and "origin/main row differs from the checked-out push context" in forged_out
            and "STUB ran" not in forged_out and rc == 1 and observation(candidate, published) in out,
            forged_out + out)

    rc, out = hook(ev3, main_update, destination=("origin", push_url + "\nunconfigured"))
    require("29 a newline in the destination cannot match one configured URL",
            rc == 1 and "cannot match the origin/main destination" in out
            and "gating " not in out and "STUB ran" not in out, out)
    return problems


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="pre-push-checkout-") as td:
        problems = arms(Path(td).resolve())
    print(f"PRE_PUSH_CHECKOUT_SELFTEST arms=29 failed={len(problems)}")
    for p in problems:
        print(p, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
