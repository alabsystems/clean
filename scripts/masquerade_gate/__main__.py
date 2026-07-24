# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Entry point for `python3 -m scripts.masquerade_gate`."""
from __future__ import annotations

import sys

from scripts.masquerade_gate.cli import main

if __name__ == "__main__":
    sys.exit(main())
