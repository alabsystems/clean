#!/usr/bin/env python3
"""Self-test for the STALE-PRODUCER advisory in `scripts/trust_verify_ratchet.sh`.

The advisory answers one question the soundness gate could not: *does the
compiler build this run measured actually contain the landed fix for the
obligation class it just certified?*  Measured 2026-08-25, that distinction was
worth a whole lane — the shared stage1 `9f07573349` (2026-08-23 16:05 -0700)
contains the divzero fix `18a0083876` and PREDATES the shift fix `c67021cd0d`
(2026-08-23 20:28 -0700) by four hours, so `sentinel_div_by_zero_must_not_prove`
was correctly FAILED in the same run in which
`sentinel_shift_overflow_must_not_prove` was CERTIFIED.  Read without the
ancestry, that looks like a brand-new unsoundness in a different solver.

THE ONE PROPERTY THAT MUST NEVER SLIP: the advisory is *advisory*.  It prints,
it returns 0, and the certification still exits 2.  A diagnostic that could
swallow a soundness verdict would be strictly worse than no diagnostic, so the
structural arms below pin that it contains no exit path and is reachable only
from the certification arm.
"""

from __future__ import annotations

import re
import subprocess
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
RATCHET = REPO / "scripts" / "trust_verify_ratchet.sh"

ADVISORY_START = "# ------------------------------------------------------- STALE-PRODUCER ADVISORY"
ADVISORY_END = "run_soundness() {"


def ratchet_text() -> str:
    return RATCHET.read_text(encoding="utf-8")


def advisory_fragment() -> str:
    """The advisory block on its own, sourceable without running the gate."""
    text = ratchet_text()
    start = text.index(ADVISORY_START)
    end = text.index(ADVISORY_END, start)
    return text[start:end]


def function_body(name: str) -> str:
    frag = advisory_fragment()
    start = frag.index(f"{name}() {{")
    end = frag.index("\n}\n", start)
    return frag[start:end]


class ProducerFixAdvisoryTests(unittest.TestCase):
    def test_pins_are_full_commit_shas_with_a_subject(self) -> None:
        frag = advisory_fragment()
        start = frag.index("KNOWN_PRODUCER_FIXES=(")
        block = frag[start : frag.index("\n)\n", start)]
        rows = re.findall(r'^\s*"([^"]+)"\s*$', block, re.MULTILINE)
        self.assertGreaterEqual(len(rows), 4, "the landed vcgen fixes must stay pinned")
        for row in rows:
            sha, _, subject = row.partition("|")
            self.assertRegex(sha, r"^[0-9a-f]{40}$", f"pin {sha!r} is not a full sha")
            self.assertTrue(subject.strip(), f"pin {sha} carries no subject")

    def test_advisory_body_contains_no_exit_path(self) -> None:
        body = function_body("report_producer_fix_ancestry")
        for forbidden in ("exit ", "fail ", "fail_code ", "set -e"):
            self.assertNotIn(
                forbidden,
                body,
                "the advisory must never be able to change the gate's verdict",
            )

    def test_advisory_is_reached_only_from_the_certification_arm(self) -> None:
        text = ratchet_text()
        calls = [
            line
            for line in text.splitlines()
            if "report_producer_fix_ancestry" in line and "()" not in line
        ]
        self.assertEqual(len(calls), 1, f"expected exactly one call site, got {calls}")
        call_at = text.index(calls[0])
        arm_at = text.rindex("      2)\n", 0, call_at)
        verdict_at = text.index("fail_code 2", call_at)
        self.assertLess(arm_at, call_at, "the call must sit inside the `2)` arm")
        self.assertLess(call_at, verdict_at, "the advisory must print before the verdict")

    def _run_advisory(self, repo: Path, producer: str, pins: list[str]) -> tuple[int, str]:
        array = "KNOWN_PRODUCER_FIXES=(\n" + "\n".join(f'  "{p}"' for p in pins) + "\n)\n"
        script = "\n".join(
            [
                "set -uo pipefail",
                advisory_fragment(),
                array,
                f'STAGE1="{repo}/build/host/stage1/bin"',
                f'REPO="{repo}"',
                f'TRUSTC_ID="{producer}"',
                "report_producer_fix_ancestry",
                "echo \"RC=$?\"",
            ]
        )
        with tempfile.NamedTemporaryFile("w", suffix=".sh", delete=False) as handle:
            handle.write(script)
            path = handle.name
        proc = subprocess.run(
            ["bash", path], text=True, capture_output=True, check=False, cwd=str(REPO)
        )
        return proc.returncode, proc.stdout + proc.stderr

    def test_verdicts_are_contains_absent_and_unknown(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "trust"
            (root / "build" / "host" / "stage1" / "bin").mkdir(parents=True)
            git = ["git", "-C", str(root)]
            subprocess.run(git + ["init", "-q"], check=True)
            subprocess.run(git + ["config", "user.email", "t@example.invalid"], check=True)
            subprocess.run(git + ["config", "user.name", "t"], check=True)
            (root / "a").write_text("a", encoding="utf-8")
            subprocess.run(git + ["add", "a"], check=True)
            subprocess.run(git + ["commit", "-qm", "base"], check=True)
            base = subprocess.run(
                git + ["rev-parse", "HEAD"], text=True, capture_output=True, check=True
            ).stdout.strip()
            (root / "b").write_text("b", encoding="utf-8")
            subprocess.run(git + ["add", "b"], check=True)
            subprocess.run(git + ["commit", "-qm", "producer"], check=True)
            producer = subprocess.run(
                git + ["rev-parse", "HEAD"], text=True, capture_output=True, check=True
            ).stdout.strip()
            subprocess.run(git + ["checkout", "-q", "-b", "side", base], check=True)
            (root / "c").write_text("c", encoding="utf-8")
            subprocess.run(git + ["add", "c"], check=True)
            subprocess.run(git + ["commit", "-qm", "later-fix"], check=True)
            later = subprocess.run(
                git + ["rev-parse", "HEAD"], text=True, capture_output=True, check=True
            ).stdout.strip()

            missing = "0" * 40
            rc, out = self._run_advisory(
                root,
                producer,
                [f"{base}|landed before", f"{later}|not in this build", f"{missing}|absent object"],
            )
            self.assertEqual(rc, 0, out)
            self.assertIn("RC=0", out)
            self.assertRegex(out, rf"{base}\s+contains")
            self.assertRegex(out, rf"{later}\s+ABSENT")
            self.assertRegex(out, rf"{missing}\s+UNKNOWN")
            self.assertIn("PREDATES", out)

    def test_no_local_checkout_reports_unknown_rather_than_not_stale(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "nowhere"
            (root / "build" / "host" / "stage1" / "bin").mkdir(parents=True)
            rc, out = self._run_advisory(root, "f" * 40, [f"{'e' * 40}|some fix"])
            self.assertEqual(rc, 0, out)
            self.assertIn("UNKNOWN", out)
            self.assertNotIn("contains", out)


if __name__ == "__main__":
    unittest.main()
