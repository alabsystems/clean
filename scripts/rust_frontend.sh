#!/usr/bin/env bash
# Resolve the cargo-frontend subcommand binary for the TOOLCHAIN THAT IS PINNED,
# then exec the requested gate with it. Nothing here relaxes a check: the same
# `fmt --all --check` / `clippy ... -D warnings` runs, under whatever name the
# pinned toolchain ships it as.
#
# WHY THIS EXISTS. On 2026-08-18, `rust-toolchain.toml` moved from
# `channel = "stable"` to `channel = "trust"`. That file's own header lists, as
# explicitly UNKNOWN at the time, "whether the installed stage2 ships the
# components this repo's gates need: rustfmt (trustfmt) for
# `cargo fmt --all --check`, clippy (tippy) for the workspace `-D warnings`
# gate". Measured here on 2026-08-20, at fa691b5a9, the answer is: it ships
# them, under RENAMED binaries, and the stock spelling therefore cannot run.
#
#   $ cargo fmt --all --check
#   error: 'cargo-fmt' is not installed for the custom toolchain 'trust'.
#   $ cargo clippy --version
#   error: 'cargo-clippy' is not installed for the custom toolchain 'trust'.
#
# The stage2 bin holds `targo-fmt` and `targo-tippy` instead -- cargo resolves
# `cargo <sub>` by looking for a `cargo-<sub>` sibling, so the rename alone
# breaks both gates. Two further traps, both measured:
#
#   * `targo fmt` through the rustup shim (~/.cargo/bin/targo) is REFUSED:
#     "OS-reported Targo executable ... is not a plain regular file; protected
#     Targo frontends cannot be symlinks or reparse points".
#   * `targo fmt` through the rustup toolchain dir is ALSO refused:
#     "protected Trust toolchain directory `~/.rustup/toolchains/trust/bin`
#     traverses a symlink or non-canonical path". The linked toolchain is a
#     symlink into trust's build tree, so every path through rustup is
#     non-canonical by construction.
#
# `rustc --print sysroot` reports the resolved, canonical stage2 directory, and
# the frontend invoked from there authenticates. That is what this resolves.
#
# Usage:  scripts/rust_frontend.sh fmt --all --check
#         scripts/rust_frontend.sh clippy --locked --workspace --all-targets -- -D warnings
set -euo pipefail

if [ "$#" -lt 1 ]; then
  echo "usage: rust_frontend.sh <fmt|clippy> [args...]" >&2
  exit 2
fi

sub="$1"; shift

case "$sub" in
  fmt)    candidates=("fmt") ;;
  clippy) candidates=("clippy" "tippy") ;;
  *)      candidates=("$sub") ;;
esac

sysroot="$(rustc --print sysroot)"
# Canonicalise: a symlinked sysroot is what the Trust frontends refuse.
if command -v python3 >/dev/null 2>&1; then
  sysroot="$(python3 -c 'import os,sys;print(os.path.realpath(sys.argv[1]))' "$sysroot")"
fi
bindir="$sysroot/bin"

# Try, in order: the stock `cargo <sub>`, then every (driver, subcommand) pair
# the pinned sysroot actually ships. The stock spelling comes FIRST so that on
# an ordinary upstream toolchain this script is a no-op passthrough.
for name in "${candidates[@]}"; do
  if [ -x "$bindir/cargo-$name" ]; then
    exec cargo "$name" "$@"
  fi
done

for driver in targo cargo; do
  [ -x "$bindir/$driver" ] || continue
  for name in "${candidates[@]}"; do
    if [ -x "$bindir/$driver-$name" ]; then
      exec "$bindir/$driver" "$name" "$@"
    fi
  done
done

echo "rust_frontend.sh: no frontend for '$sub' in $bindir" >&2
echo "  looked for: cargo-<n> and <targo|cargo>-<n> with n in: ${candidates[*]}" >&2
exit 127
