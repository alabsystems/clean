#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Re-derive the committed artifacts a moved input left stale, in the order they read each other.

WHY (2026-10-15). A trust-ir pin bump moves the root `Cargo.lock` and
`scripts/crystal_a2_project/Cargo.{toml,lock}`, and each move left a hook leg red until
somebody ran the command its message names, one after another:

  vendor-manifest-check       data/vendor_manifest.json pins cargo_lock_sha256
  gate-registry               R7: check_lint_coverage pins the projector's manifest and lock
                              as DERIVED inputs, so its 72 arms must replay (`--repin`)
  verdict-set-check           ... and that re-pin moves data/gate_registry.json, an input
  verdict-io-contracts-check  pin of data/verdict_set.json, whose digest the IO contracts
  spine-assumption-ledger-check  pin, whose digest the ledger pins, whose digest (with the
  spine-scoreboard-ratchet    two verdict artifacts') the scoreboard pins -- minted LAST

bb04555f8 and d95127f28 each walked that by hand. This walks it: every NODE below in
dependency order (a node reads only nodes above it), and a stale node is re-derived the way
its own leg documents before the next node is judged, so staleness flows down the chain
exactly once. `scripts/bump-trust-ir-pin.sh` runs it as its last phase, inside its
transaction; it is also what to run after a hand `--repin`.

NOTHING HERE DECIDES A VERDICT. A node's check is the hook leg's own command; its
re-derivation is its generator's documented mint. Every generator that guards a ratchet
refuses to mint past it (verdict_set's lane (c) line ratchet, the scoreboard's directions);
such a refusal stops the walk with exit 1, and the move needs its dated rebase by a person.
The gate registry's node re-pins only rows whose DERIVED input set moved (`inputs`, R7),
each through `check_gate_registry.py --repin`, which moves a pin only over a demonstration
it replayed green in the same process. That replay is the cost -- check_lint_coverage's
arms, about an hour on a loaded box -- and it is the guarantee R7 exists for: a gate that
RUNS the projector is re-shown to fail whenever what it runs can change. A row whose own
SCRIPT alone moved is not re-pinned here: that is an edit to a gate, demonstrated by its
author. When the script and the derived inputs both moved, the `--repin` the input drift
starts moves the script pin too -- over the same green in-process replay, so R7 holds.

Usage:
  python3 scripts/rederive_chain.py            re-derive every stale node, then re-check all
  python3 scripts/rederive_chain.py --check    read-only: every node's check; exit 1 if any is red
  python3 scripts/rederive_chain.py --outputs  the tracked files a re-derivation may write
  --offline   stage the vendor manifest from cargo's local registry cache only (no download)

Exit codes: 0 every node fresh (after re-deriving what was stale), 1 a node is red or a
re-derivation refused, 2 usage.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = "scripts/check_gate_registry.py"


class Refused(RuntimeError):
    """A re-derivation that did not happen, with the reason."""


@dataclass
class Context:
    root: Path
    python: str = sys.executable
    offline: bool = False
    log: list[str] = field(default_factory=list)

    def run(self, argv: tuple[str, ...], stream: bool = False) -> tuple[int, str]:
        """`argv` (a repo script and its flags) under this interpreter, in the tree.
        `stream` echoes the output as it comes (a replay runs for an hour)."""
        # Unbuffered, or a streamed replay's progress arrives in one block at its end.
        env = {**os.environ, "PYTHONUNBUFFERED": "1"} if stream else None
        try:
            proc = subprocess.Popen([self.python, *argv], cwd=self.root, text=True, env=env,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        except OSError as exc:
            return 127, f"could not run {argv[0]}: {exc}"
        lines = []
        assert proc.stdout is not None
        for line in proc.stdout:
            lines.append(line)
            if stream:
                print(f"    {line}", end="", flush=True)
        return proc.wait(), "".join(lines)


def _tail(out: str, n: int = 3) -> str:
    lines = [ln.strip() for ln in out.strip().splitlines() if ln.strip()]
    return " | ".join(lines[-n:]) or "(no output)"


@dataclass(frozen=True)
class Node:
    """A committed artifact derived from committed inputs: its check, its mint."""
    name: str
    outputs: tuple[str, ...]
    check: tuple[str, ...]
    mint: tuple[tuple[str, ...], ...] = ()

    def stale(self, ctx: Context) -> str:
        """Why this node must be re-derived ("" when it is fresh)."""
        rc, out = ctx.run(self.check)
        return "" if rc == 0 else f"`{' '.join(self.check)}` exits {rc}: {_tail(out)}"

    def verify(self, ctx: Context) -> str:
        """Why this node's leg is red ("" when its check passes)."""
        return self.stale(ctx)

    def rederive(self, ctx: Context) -> None:
        self._mint(ctx, self.mint)

    def _mint(self, ctx: Context, argvs, stream: bool = False) -> None:
        for argv in argvs:
            rc, out = ctx.run(argv, stream=stream)
            ctx.log.append(f"{self.name}: {' '.join(argv)} -> {rc}")
            if rc != 0:
                raise Refused(f"{self.name}: `{' '.join(argv)}` exited {rc}: {_tail(out, 6)}")


@dataclass(frozen=True)
class VendorManifest(Node):
    """Staged from Cargo.lock's crates.io rows (`--stage-third-party`), then minted from the
    staged tree: the pair the vendor-manifest-check leg names. The staging directory lives
    under the tree's gitignored `target/` and is removed on the way out."""

    def rederive(self, ctx: Context) -> None:
        stage = ctx.root / "target" / f"rederive-vendor-{os.getpid()}"
        rel = stage.relative_to(ctx.root).as_posix()
        shutil.rmtree(stage, ignore_errors=True)
        try:
            self._mint(ctx, (
                (*self.check[:1], "--stage-third-party", rel,
                 *(() if ctx.offline else ("--download",))),
                (*self.check[:1], rel),
            ))
        finally:
            shutil.rmtree(stage, ignore_errors=True)


def _registry():
    """check_gate_registry, imported from THIS tree: its R7 reading of a derived input set
    (`_derived_inputs`, `_inputs_drift`) is the one this node acts on, never a copy."""
    scripts = str(Path(__file__).resolve().parent)
    if scripts not in sys.path:
        sys.path.insert(0, scripts)
    import check_gate_registry  # noqa: E402
    return check_gate_registry


@dataclass(frozen=True)
class GateRegistry(Node):
    """Stale when a row's pinned DERIVED input set has moved (R7 `inputs`); re-derived by
    `--repin <row>`, a green replay of that row's arms, one row at a time. Verified by the
    whole registry check (GATE_REGISTRY=ok), which also covers every other rule."""
    repin: tuple[str, ...] = (REGISTRY, "--repin")

    def drifted(self, ctx: Context) -> list[tuple[str, str]]:
        reg = _registry()
        drifted = []
        for row in reg.load_registry(ctx.root)["rows"]:
            pinned = (row.get("demonstrated") or {}).get("inputs")
            if not isinstance(pinned, dict):
                continue
            derived, why = reg._derived_inputs(ctx.root, reg._subject(row))
            if derived is None:
                raise Refused(f"{self.name}: {row['id']} cannot re-derive its pinned inputs: {why}")
            moved = reg._inputs_drift(pinned, derived)
            if moved:
                drifted.append((row["id"], moved))
        return drifted

    def stale(self, ctx: Context) -> str:
        return "; ".join(f"{rid} ({moved})" for rid, moved in self.drifted(ctx))

    def verify(self, ctx: Context) -> str:
        return Node.stale(self, ctx)

    def rederive(self, ctx: Context) -> None:
        for rid, moved in self.drifted(ctx):
            print(f"  {self.name}: re-pinning {rid} over a replay of its recorded arms "
                  f"({moved})", flush=True)
            self._mint(ctx, ((*self.repin, rid),), stream=True)


# The chain, in dependency order: each node reads only the nodes above it. The scoreboard
# reads the ledger and both verdict artifacts (its STALE INPUT message: "re-minted LAST of
# the derived chain"), and the status page renders the scoreboard.
NODES: tuple[Node, ...] = (
    VendorManifest("vendor-manifest", ("data/vendor_manifest.json",),
                   ("scripts/gen_vendor_manifest.py", "--check")),
    GateRegistry("gate-registry", ("data/gate_registry.json",), (REGISTRY,)),
    Node("verdict-set", ("data/verdict_set.json",),
         ("scripts/verdict_set.py", "--check"), (("scripts/verdict_set.py",),)),
    Node("verdict-io-contracts", ("data/verdict_io_contracts.json",),
         ("scripts/verdict_io_contracts.py", "--check"), (("scripts/verdict_io_contracts.py",),)),
    Node("spine-assumption-ledger", ("data/spine_assumption_ledger.json",),
         ("scripts/spine_assumption_ledger.py", "--check"),
         (("scripts/spine_assumption_ledger.py",),)),
    Node("spine-scoreboard", ("data/spine_scoreboard.json",),
         ("scripts/spine_scoreboard.py", "--ratchet"), (("scripts/spine_scoreboard.py", "--refresh"),)),
    Node("one-trust-status", ("docs/STATUS_ONE_TRUST.md",),
         ("scripts/one_trust_status.py", "--check"), (("scripts/one_trust_status.py",),)),
)


def check(ctx: Context, nodes: tuple[Node, ...] = NODES) -> int:
    """Read-only: every node's leg check. 0 when all pass."""
    red = 0
    for node in nodes:
        try:
            why = node.verify(ctx)
        except Refused as exc:
            why = str(exc)
        print(f"  [{'RED' if why else 'ok'}] {node.name}" + (f": {why}" if why else ""))
        red += bool(why)
    print(f"REDERIVE_CHECK={'fail' if red else 'ok'} nodes={len(nodes)} red={red}")
    return 1 if red else 0


def rederive(ctx: Context, nodes: tuple[Node, ...] = NODES) -> int:
    """Re-derive each stale node in order, then require every node's check to pass."""
    redone: list[str] = []
    try:
        for node in nodes:
            why = node.stale(ctx)
            if not why:
                print(f"  [fresh] {node.name}", flush=True)
                continue
            print(f"  [stale] {node.name}: {why}", flush=True)
            node.rederive(ctx)
            still = node.stale(ctx)
            if still:
                raise Refused(f"{node.name} is still stale after its re-derivation: {still}")
            redone.append(node.name)
            print(f"  [re-derived] {node.name}", flush=True)
    except Refused as exc:
        print(f"  [REFUSED] {exc}", file=sys.stderr)
        print(f"REDERIVE=fail re-derived={','.join(redone) or 'none'} -- the walk stopped; "
              f"the nodes below the refusal were not judged", file=sys.stderr)
        return 1
    red = [(node.name, why) for node in nodes if (why := node.verify(ctx))]
    for name, why in red:
        print(f"  [RED] {name}: {why}", file=sys.stderr)
    print(f"REDERIVE={'fail' if red else 'ok'} nodes={len(nodes)} "
          f"re-derived={','.join(redone) or 'none'}" + (f" red={len(red)}" if red else ""))
    return 1 if red else 0


def main(argv: list[str]) -> int:
    known = {"--check", "--outputs", "--offline"}
    if any(a not in known for a in argv) or ("--check" in argv and "--outputs" in argv):
        print(f"usage: rederive_chain.py [--check | --outputs] [--offline] (got {argv})",
              file=sys.stderr)
        return 2
    if "--outputs" in argv:
        print("\n".join(out for node in NODES for out in node.outputs))
        return 0
    ctx = Context(ROOT, offline="--offline" in argv)
    return check(ctx) if "--check" in argv else rederive(ctx)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
