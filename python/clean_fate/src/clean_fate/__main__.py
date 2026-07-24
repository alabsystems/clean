# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""
CLI entry point for clean-fate.

Usage:
    python -m clean_fate verify <file.lean>
    python -m clean_fate verify <file.lean> --timeout 60
    python -m clean_fate verify <file.lean> --endpoint http://localhost:8000
    python -m clean_fate status
"""

import argparse
import sys
from pathlib import Path

from clean_fate import cleanVerifier, __version__


def main() -> int:
    parser = argparse.ArgumentParser(
        prog="clean-fate",
        description="clean verification client for FATE-Eval integration",
    )
    parser.add_argument(
        "--version", action="version", version=f"clean-fate {__version__}"
    )
    parser.add_argument(
        "--endpoint",
        default="http://localhost:8000",
        help="clean-server endpoint (default: http://localhost:8000)",
    )

    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # verify command
    verify_parser = subparsers.add_parser("verify", help="Verify a Lean file")
    verify_parser.add_argument("file", type=Path, help="Lean file to verify")
    verify_parser.add_argument(
        "--timeout", type=int, default=30, help="Timeout in seconds (default: 30)"
    )

    # status command
    subparsers.add_parser("status", help="Check clean-server status")

    args = parser.parse_args()

    if args.command is None:
        parser.print_help()
        return 0

    verifier = cleanVerifier(endpoint=args.endpoint)

    if args.command == "verify":
        if not args.file.exists():
            print(f"Error: File not found: {args.file}", file=sys.stderr)
            return 1

        try:
            code = args.file.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as e:
            print(f"Error reading file: {e}", file=sys.stderr)
            return 1

        result = verifier.verify(code, timeout=args.timeout)

        if result.complete:
            print(f"PASS: {args.file}")
            print(f"  Time: {result.verify_time:.3f}s")
            return 0
        print(f"FAIL: {args.file}")
        if result.is_timeout:
            print(f"  Timeout after {args.timeout}s")
        for msg in result.sorted_messages.errors:
            print(f"  Error: {msg.message}")
        return 1

    if args.command == "status":
        try:
            # Simple health check - verify empty file (minimal valid Lean code)
            result = verifier.verify("-- clean-fate health check", timeout=5)
            print(f"clean-server at {args.endpoint}: OK")
            print(f"  Response time: {result.verify_time:.3f}s")
            return 0
        except Exception as e:
            print(f"clean-server at {args.endpoint}: ERROR")
            print(f"  {e}")
            return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
