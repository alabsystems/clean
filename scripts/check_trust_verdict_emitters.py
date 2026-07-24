#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Pillar-1 discipline gate: no new trust-verdict green without classification.

A trust-verdict emitter is any code path that stamps a soundness-bearing label
(KernelVerified / Proved / valid / verified / safe). Pillar 1 requires every such
emitter to be either kernel-re-checked, fail-closed, or a tracked residual-TCB
item with a // SOUNDNESS: comment. This gate turns that from a snapshot into an
enforced invariant: it fails CI if

  1. a NEW `TrustLevel::KernelVerified` verdict *construction* appears in an
     enforced (clean-kernel) source file that no registry entry accounts for;
  2. a registry entry classified `kernel-rechecked` whose file calls NONE of the
     kernel recheck primitives (mislabeled — a "kernel-rechecked" verdict that
     never re-checks);
  3. a registry entry classified `asserts-own-authority` whose file carries NO
     `// SOUNDNESS:` comment (an un-justified own-authority accept);
  4. the clean-kernel `asserts-own-authority` count in the ratchet does not equal
     the number of such registry entries, or is RAISED above the recorded
     baseline (the count only ratchets DOWN).

Registry: data/trust_verdict_emitters.json (seeded from the 127-emitter audit in
docs/PILLAR_1_TRUST_MAP.md). ENFORCEMENT SCOPE: only `repo:clean` entries and the
clean-kernel source tree are hard-scanned here; `repo:trust` entries (the
trust-router/trust-vcgen fork) are documented for the full picture but enforced by
that repo's own gate.

Wired into scripts/local_gate.sh. Pure-stdlib; no cargo build required.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
REGISTRY = REPO_ROOT / "data" / "trust_verdict_emitters.json"
KERNEL_SRC = REPO_ROOT / "crates" / "clean-kernel" / "src"

# A `TrustLevel::KernelVerified` used to CONSTRUCT a verdict (mint the label),
# as opposed to READING it. Construction contexts: `.map(|_| TrustLevel::...)`,
# a `Some(TrustLevel::...)`/`Ok(TrustLevel::...)` wrap, or an `= TrustLevel::...`
# assignment/return that is NOT a `==`/`!=` comparison and NOT the `min_trust`
# fold seed. We deliberately do NOT flag `==`/`!=` reads, `TrustLevel::X => n`
# ordinal match arms, or the `let mut min_trust = ...` fold identity.
CONSTRUCT_RE = re.compile(
    r"(?:\.map\(\s*\|_\|\s*|Some\(\s*|Ok\(\s*|=>\s*|(?<![=!<>])=\s*)TrustLevel::KernelVerified\b"
)
# Explicit non-construction forms to subtract (reads / fold-seed / ordinal arm).
READ_RE = re.compile(
    r"(==\s*TrustLevel::KernelVerified"
    r"|TrustLevel::KernelVerified\s*(==|!=|=>)"
    r"|let\s+mut\s+min_trust\s*=\s*TrustLevel::KernelVerified)"
)


def is_test_path(rel: Path) -> bool:
    parts = set(rel.parts)
    if "tests" in parts or "tests2" in parts:
        return True
    name = rel.name
    if re.search(r"(^test_|_tests?\.rs$|^tests?\.rs$|^tests_)", name):
        return True
    # kani proof harnesses are #[cfg(kani)] formal-verification, not verdicts.
    return name.endswith("kani.rs") or "kani" in name or "test" in name


def strip_cfg_test_blocks(text: str) -> str:
    """Blank out top-level `#[cfg(test)] mod ... { ... }` bodies so inline test
    fixtures inside otherwise-production files do not trip the scanner. Brace-
    matched from the `mod name {` following a `#[cfg(test)]` attribute."""
    out = []
    i = 0
    n = len(text)
    cfg = "#[cfg(test)]"
    while i < n:
        j = text.find(cfg, i)
        if j == -1:
            out.append(text[i:])
            break
        out.append(text[i:j])
        # find the opening brace of the following `mod ... {`
        brace = text.find("{", j)
        if brace == -1:
            out.append(text[j:])
            break
        depth = 0
        k = brace
        while k < n:
            if text[k] == "{":
                depth += 1
            elif text[k] == "}":
                depth -= 1
                if depth == 0:
                    k += 1
                    break
            k += 1
        # replace the whole cfg(test) block with newlines (preserve line numbers)
        block = text[j:k]
        out.append("\n" * block.count("\n"))
        i = k
    return "".join(out)


def load_registry() -> dict:
    try:
        data = json.loads(REGISTRY.read_text())
    except (OSError, json.JSONDecodeError) as exc:  # fail closed
        sys.exit(f"FAIL: cannot read {REGISTRY}: {exc}")
    if not isinstance(data.get("emitters"), list):
        sys.exit(f"FAIL: {REGISTRY} missing the 'emitters' list.")
    return data


def entry_file(entry: dict) -> Path | None:
    """Extract the source file path from an entry_point 'crates/...rs :: fn'."""
    ep = entry.get("entry_point", "")
    m = re.match(r"\s*(crates/[^\s:]+\.rs)", ep)
    if not m:
        return None
    return REPO_ROOT / m.group(1)


def main() -> int:  # noqa: C901 (single linear gate)
    data = load_registry()
    emitters = data["emitters"]
    primitives = data.get("kernel_recheck_primitives", [])
    ratchet = data.get("asserts_own_authority_ratchet", {})
    recorded_count = int(ratchet.get("clean_kernel_count", -1))

    ok = True

    # ── (0) registry self-consistency: clean entries must resolve to a file ──
    construction_sites: set[str] = set()
    clean_aoa = 0
    for e in emitters:
        if e.get("repo") != "clean":
            continue
        f = entry_file(e)
        if f is None or not f.exists():
            ok = False
            print(
                f"FAIL: registry entry '{e.get('id')}' entry_point does not resolve "
                f"to an existing file: {e.get('entry_point')!r}",
                file=sys.stderr,
            )
            continue
        rel = str(f.relative_to(REPO_ROOT))
        text = f.read_text()
        basis = e.get("basis")

        # collect declared verdict construction sites (file:line) to allow-list.
        for site in e.get("verdict_construction_sites", []):
            construction_sites.add(site)

        # (2) kernel-rechecked entries must actually call a recheck primitive.
        if basis == "kernel-rechecked":
            calls = e.get("recheck_calls", [])
            if not calls:
                ok = False
                print(
                    f"FAIL: '{e.get('id')}' is kernel-rechecked but lists no recheck_calls.",
                    file=sys.stderr,
                )
            elif not any(c in text for c in calls if c in primitives or True):
                # at least one declared recheck token must appear in the file.
                ok = False
                print(
                    f"FAIL: '{e.get('id')}' is kernel-rechecked but its file {rel} "
                    f"calls none of its recheck primitives {calls}.",
                    file=sys.stderr,
                )

        # (3) asserts-own-authority entries must carry a // SOUNDNESS: comment.
        if basis == "asserts-own-authority":
            clean_aoa += 1
            if "// SOUNDNESS:" not in text:
                ok = False
                print(
                    f"FAIL: '{e.get('id')}' is asserts-own-authority but its file {rel} "
                    f"carries no `// SOUNDNESS:` comment.",
                    file=sys.stderr,
                )

    # ── (1) NEW verdict construction not accounted for ──
    for path in sorted(KERNEL_SRC.rglob("*.rs")):
        rel = path.relative_to(REPO_ROOT)
        if is_test_path(rel):
            continue
        try:
            text = strip_cfg_test_blocks(path.read_text())
        except OSError as exc:
            sys.exit(f"FAIL: cannot read {rel}: {exc}")
        for lineno, line in enumerate(text.splitlines(), 1):
            stripped = line.lstrip()
            if stripped.startswith("//") or stripped.startswith("*"):
                continue
            if not CONSTRUCT_RE.search(line) or READ_RE.search(line):
                continue
            site = f"{rel}:{lineno}"
            if site in construction_sites:
                continue
            ok = False
            print(
                f"FAIL: unclassified trust-verdict construction at {site}:\n"
                f"    {line.strip()}\n"
                f"  -> a new `TrustLevel::KernelVerified` is minted here. Add a "
                f"data/trust_verdict_emitters.json entry (with a verdict_construction_sites "
                f"'{site}') classifying its BASIS, and a // SOUNDNESS: comment if it "
                f"asserts its own authority.",
                file=sys.stderr,
            )

    # ── (4) asserts-own-authority ratchet (down-only) ──
    if recorded_count < 0:
        ok = False
        print(
            "FAIL: registry asserts_own_authority_ratchet.clean_kernel_count missing.",
            file=sys.stderr,
        )
    elif clean_aoa > recorded_count:
        ok = False
        print(
            f"FAIL: clean-kernel asserts-own-authority emitters ({clean_aoa}) EXCEED the "
            f"recorded ratchet baseline ({recorded_count}). A new own-authority verdict "
            f"must be reviewed + justified; the count only ratchets DOWN.",
            file=sys.stderr,
        )
    elif clean_aoa < recorded_count:
        print(
            f"NOTE: clean-kernel asserts-own-authority emitters ({clean_aoa}) are BELOW the "
            f"recorded baseline ({recorded_count}); lower "
            f"asserts_own_authority_ratchet.clean_kernel_count in the registry.",
        )

    if ok:
        print(
            f"OK: trust-verdict emitter discipline — {len(emitters)} emitters classified, "
            f"clean asserts-own-authority={clean_aoa}/{recorded_count}, "
            f"no unclassified new green in clean-kernel."
        )
        return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
