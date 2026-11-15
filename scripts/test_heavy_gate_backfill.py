#!/usr/bin/env python3
# Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
"""Check memory admission against completion subsets and real FIFO waiters."""

import itertools
import os
from pathlib import Path
import random
import signal
import subprocess
import tempfile
import time
import unittest

GATE = Path(__file__).with_name("heavy_gate.sh")


def oracle_room(budget, head, weights):
    # Enumerate future remaining holders, independently of the implementation's
    # dynamic program. A younger job must preserve EVERY feasible head state.
    feasible = [budget - head - sum(subset)
                for count in range(len(weights) + 1)
                for subset in itertools.combinations(weights, count)
                if sum(subset) + head <= budget]
    return min(feasible, default=0)


class BackfillTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="clean-gate-backfill-")
        self.root = Path(self.temp.name)
        self.tokens = self.root / "tokens"
        self.tokens.mkdir()
        self.queue = self.root / "queue"
        self.queue.mkdir()
        self.children = []
        self.env = dict(os.environ, HEAVY_GATE_DIR=str(self.root),
                        HEAVY_GATE_PHYS_GB="64", HEAVY_GATE_BUDGET_GB="48",
                        HEAVY_GATE_OWNER_PID=str(os.getpid()))

    def tearDown(self):
        for process in self.children:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGTERM)
            try:
                process.communicate(timeout=3)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.communicate()
        self.temp.cleanup()

    def seed(self, weights):
        for token in self.tokens.iterdir():
            token.unlink()
        for index, weight in enumerate(weights):
            (self.tokens / f"holder-{index}").write_text(
                f"{os.getpid()} {weight} existing 2026-11-10T00:00:00Z\n")

    def room(self, budget, head, weights, faulty_reader=False):
        self.seed(weights)
        # Exercise the production helper verbatim. The independent oracle
        # above has no dynamic programming or dependence on its implementation.
        source = GATE.read_text()
        start = source.index("_backfill_room() {\n")
        end = source.index("\n}\n", start) + 3
        command = ('set -uo pipefail\n' + source[start:end]
                   + '\nBUDGET=$1; TOKENS=$2; _backfill_room "$3"')
        if faulty_reader:
            command = ('awk() { case "$1" in NR==1*) return 2;; esac; '
                       'command awk "$@"; }\n' + command)
        result = subprocess.run(["/bin/bash", "-c", command, "backfill",
                                 str(budget), str(self.tokens), str(head)],
                                text=True, capture_output=True, check=True)
        return int(result.stdout)

    def acquire(self, weight, label):
        process = subprocess.Popen(["/bin/bash", str(GATE), "acquire", str(weight), label],
                                   env=self.env, text=True, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, start_new_session=True)
        self.children.append(process)
        return process

    def wait_ticket(self, label):
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            for ticket in self.queue.iterdir():
                try:
                    if f" {label} " in ticket.read_text():
                        return ticket
                except FileNotFoundError:
                    pass
            time.sleep(0.02)
        self.fail(f"no queue ticket for {label}")

    def admitted(self, process):
        out, err = process.communicate(timeout=15)
        self.assertEqual(process.returncode, 0, err)
        token = Path(out.strip())
        self.assertTrue(token.is_file(), (out, err))
        return token

    def test_large_holder_leaves_safe_capacity_for_small_backfill(self):
        self.assertEqual(self.room(48, 34, [34]), 14)
        self.assertEqual(self.room(48, 34, [34, 2]), 12)
        self.assertEqual(self.room(48, 34, [34, 2, 12]), 0)

    def test_a_smaller_remaining_holder_limits_backfill(self):
        self.assertEqual(self.room(48, 34, [11, 16]), 3)
        self.assertEqual(self.room(48, 34, [11, 16, 2]), 1)
        self.assertEqual(self.room(48, 34, [10, 10, 10]), 4)

    def test_empty_full_and_oversized_head(self):
        for budget, head, weights in [(48, 34, []), (48, 48, [34]),
                                      (4, 4, [2]), (48, 49, [34])]:
            self.assertEqual(self.room(budget, head, weights),
                             oracle_room(budget, head, weights))

    def test_all_completion_subsets_match_independent_oracle(self):
        rng = random.Random(20261110)
        for _ in range(60):
            budget = rng.randint(1, 96)
            head = rng.randint(1, budget)
            remaining = budget
            weights = []
            for _ in range(rng.randint(0, 6)):
                if remaining == 0:
                    break
                weight = rng.randint(1, remaining)
                weights.append(weight)
                remaining -= weight
            with self.subTest(budget=budget, head=head, weights=weights):
                self.assertEqual(self.room(budget, head, weights),
                                 oracle_room(budget, head, weights))

    def test_release_after_snapshot_cannot_invalidate_the_bound(self):
        for weights in ([34], [11, 16], [10, 10, 10], [34, 2, 12]):
            room = self.room(48, 34, weights)
            for count in range(len(weights) + 1):
                for remaining in itertools.combinations(weights, count):
                    if sum(remaining) + 34 <= 48:
                        self.assertLessEqual(sum(remaining) + 34 + room, 48)

    def test_token_read_failure_does_not_turn_into_available_capacity(self):
        with self.assertRaises(subprocess.CalledProcessError) as error:
            self.room(48, 34, [11, 16], faulty_reader=True)
        self.assertEqual(error.exception.returncode, 3)

    def test_public_admission_backfills_without_spending_head_capacity(self):
        self.seed([34])
        head = self.acquire(34, "oldest")
        self.wait_ticket("oldest")
        time.sleep(1.1)  # Queue epoch ordering across platforms and PID rollover.
        young = self.acquire(2, "young")
        token = self.admitted(young)
        self.assertIsNone(head.poll())
        self.assertEqual(sum(int(p.read_text().split()[1])
                             for p in self.tokens.iterdir()), 36)
        (self.tokens / "holder-0").unlink()
        head_token = self.admitted(head)
        self.assertTrue(token.exists())
        self.assertTrue(head_token.exists())
        self.assertEqual(sum(int(p.read_text().split()[1])
                             for p in self.tokens.iterdir()), 36)

    def test_public_admission_preserves_first_feasible_head_completion(self):
        self.seed([11, 16])
        head = self.acquire(34, "oldest")
        self.wait_ticket("oldest")
        time.sleep(1.1)
        young = self.acquire(4, "young")
        self.wait_ticket("young")
        # Releasing 16 makes the head fit beside the remaining 11. The young
        # job would fit by itself but would postpone that exact opportunity.
        (self.tokens / "holder-1").unlink()
        head_token = self.admitted(head)
        self.assertIsNone(young.poll())
        self.assertEqual(sum(int(p.read_text().split()[1])
                             for p in self.tokens.iterdir()), 45)
        head_token.unlink()
        self.admitted(young)

    def test_public_admission_still_refuses_to_exceed_current_budget(self):
        self.seed([48])
        waiter = self.acquire(1, "waiter")
        self.wait_ticket("waiter")
        time.sleep(0.5)
        self.assertIsNone(waiter.poll())
        self.assertEqual(len(list(self.tokens.iterdir())), 1)
        (self.tokens / "holder-0").unlink()
        self.admitted(waiter)


if __name__ == "__main__":
    unittest.main()
