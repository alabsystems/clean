#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# Compatibility shim for stale hooks that source .githooks/hook_common.sh.

set -euo pipefail

hook_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git rev-parse --show-toplevel 2>/dev/null || true)"
hook_common_target=""
elif [[ -f "$hook_dir/lib/hook_common.sh" ]]; then
    hook_common_target="$hook_dir/lib/hook_common.sh"
else
    printf 'ERROR: Cannot find canonical hook_common.sh for .githooks shim\n' >&2
    if (return 0 2>/dev/null); then
        return 1
    fi
    exit 1
fi

# shellcheck disable=SC1091
source "$hook_common_target"
