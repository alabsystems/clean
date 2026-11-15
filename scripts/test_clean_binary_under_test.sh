#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Suite entry for `scripts/lib/clean_binary_under_test.sh`.
#
# The library carries its own mutation arms; this file is the CALLER that makes
# them run. `scripts/check_script_selftests.sh` discovers suites by globbing
# `scripts/test_*`, so a self-test living under `scripts/lib/` is invisible to
# it -- which would make the arms exactly the thing that script's own header
# warns about, "self-tests, zero callers". This is four lines so that they are
# not.
#
# Run directly:  bash scripts/test_clean_binary_under_test.sh
set -uo pipefail
cd "$(cd "$(dirname "$0")/.." && pwd)" || exit 1

# shellcheck source=scripts/lib/clean_binary_under_test.sh
. scripts/lib/clean_binary_under_test.sh

_clean_binary_under_test_selftest
exit $?
