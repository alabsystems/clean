#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: clean
# Licensed under the Apache License, Version 2.0

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

exec bash "$REPO_ROOT/scripts/lean4_compat/verify_corpus.sh" "$@"
