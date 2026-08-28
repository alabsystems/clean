#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Suite wrapper so check_script_selftests.sh runs spine_set.py --self-test.

The real arms (closure computation, family tagging, dyn-edge exclusion,
fail-closed on missing dump fields, provenance required) live in
scripts/spine_set.py; this wrapper gives them a caller in the scripts/test_*
suite — a self-test nothing runs is rot (see check_script_selftests.sh).
"""

import subprocess
import sys
from pathlib import Path


def main() -> int:
    script = Path(__file__).resolve().parent / "spine_set.py"
    proc = subprocess.run(
        [sys.executable, str(script), "--self-test"],
        capture_output=True,
        text=True,
        check=False,
    )
    sys.stdout.write(proc.stdout)
    sys.stderr.write(proc.stderr)
    if proc.returncode != 0:
        return proc.returncode
    if "all green" not in proc.stdout:
        print("test_spine_set: rc=0 but no 'all green' summary line", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
