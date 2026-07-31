#!/usr/bin/env bash
# Package / verify the `cargo vendor` source tree as a release artifact.
#
# Mirrors the .mathverse shard release convention (crates/clean-mathverse/
# src/release.rs: tar.zst archive + checksum manifest + re-extract-and-verify),
# but for the vendored third-party source tree. The vendor/ tree is LARGE
# (~583 MB) and GITIGNORED — it is NEVER committed. Instead it is published as a
# GitHub release asset `vendor-sources-v<VERSION>.tar.zst` alongside a sha256
# sidecar, exactly like `mathverse-library-v*.tar.zst`.
#
# Subcommands:
#   package [VERSION] [OUT_DIR]   tar.zst the vendor/ tree + write .sha256 sidecar
#   verify  <ARCHIVE>             re-extract to a temp dir and re-checksum every
#                                 crate's source against data/vendor_manifest.json
#
# The archive lives in RELEASES, not git. Publish with, e.g.:
#   gh release upload vendor-sources-v<VERSION> \
#     dist/vendor-sources-v<VERSION>.tar.zst \
#     dist/vendor-sources-v<VERSION>.tar.zst.sha256

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

MANIFEST="data/vendor_manifest.json"

sha256_of() {
  # Portable sha256 (macOS `shasum -a 256`, Linux `sha256sum`).
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

cmd_package() {
  local version="${1:-$(date -u +%Y.%m.%d)}"
  local out_dir="${2:-dist}"

  if [[ ! -d vendor ]]; then
    echo "error: vendor/ not found — fetch a compatible external-source artifact" >&2
    echo "       (raw cargo vendor is forbidden while it would copy internal AY/NY)" >&2
    exit 1
  fi
  if [[ ! -f "${MANIFEST}" ]]; then
    echo "error: ${MANIFEST} missing — run: python3 scripts/gen_vendor_manifest.py" >&2
    exit 1
  fi

  # Recompute provenance before archiving. This rejects internal AY/NY sources,
  # extra/missing crates, checksum drift, and a manifest bound to another
  # Cargo.lock. Never package a tree merely because vendor/ happens to exist.
  VENDOR_PACKAGE_TMP="$(mktemp)"
  trap 'rm -f "${VENDOR_PACKAGE_TMP:-}" vendor/.vendor_manifest.json' EXIT
  python3 scripts/gen_vendor_manifest.py vendor "${VENDOR_PACKAGE_TMP}"
  python3 - "${MANIFEST}" "${VENDOR_PACKAGE_TMP}" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as handle:
    expected = json.load(handle)
with open(sys.argv[2], encoding="utf-8") as handle:
    actual = json.load(handle)

for field in ("cargo_lock_sha256", "summary", "crates"):
    if expected.get(field) != actual.get(field):
        print(
            f"error: vendor provenance field {field!r} is stale or mismatched; "
            "refresh only through a third-party-only staging flow",
            file=sys.stderr,
        )
        raise SystemExit(1)
PY

  mkdir -p "${out_dir}"
  local archive="${out_dir}/vendor-sources-v${version}.tar.zst"

  # Ship the provenance manifest INSIDE the archive so a downloaded tree carries
  # its own tamper-evidence record (parallels the mathverse-manifest.json shipped
  # in the shard archive).
  cp "${MANIFEST}" vendor/.vendor_manifest.json

  echo "+ archiving vendor/ (+manifest) -> ${archive}" >&2
  if tar --zstd -cf "${archive}" vendor 2>/dev/null; then
    :
  else
    # Fallback: tar | zstd (matches release.rs's two-path strategy).
    tar -cf - vendor | zstd -q -o "${archive}"
  fi
  rm -f vendor/.vendor_manifest.json

  local sum
  sum="$(sha256_of "${archive}")"
  echo "${sum}  $(basename "${archive}")" > "${archive}.sha256"

  local asize
  asize="$(du -h "${archive}" | awk '{print $1}')"
  echo "packaged: ${archive} (${asize})"
  echo "sha256:   ${sum}"
  echo "sidecar:  ${archive}.sha256"
  echo
  echo "NOT committed to git. Publish as a release asset, e.g.:"
  echo "  gh release upload vendor-sources-v${version} ${archive} ${archive}.sha256"
}

cmd_verify() {
  local archive="${1:?usage: package_vendor.sh verify <archive.tar.zst>}"
  if [[ ! -f "${archive}" ]]; then
    echo "error: archive not found: ${archive}" >&2
    exit 1
  fi

  # 1) Verify the archive's own sha256 sidecar if present.
  if [[ -f "${archive}.sha256" ]]; then
    local want got
    want="$(awk '{print $1}' "${archive}.sha256")"
    got="$(sha256_of "${archive}")"
    if [[ "${want}" != "${got}" ]]; then
      echo "FAIL: archive sha256 mismatch (want ${want}, got ${got})" >&2
      exit 1
    fi
    echo "ok: archive sha256 matches sidecar (${got})"
  else
    echo "warn: no ${archive}.sha256 sidecar — skipping archive-level checksum" >&2
  fi

  # 2) Re-extract to a temp dir and re-checksum every vendored crate against the
  #    manifest (the tamper-evidence step). We regenerate a manifest FROM the
  #    extracted tree and diff its per-crate checksums against the committed
  #    data/vendor_manifest.json.
  # Script-global (not `local`) so the EXIT trap can safely expand it under
  # `set -u` even after this function returns.
  VENDOR_VERIFY_TMP="$(mktemp -d)"
  local tmp="${VENDOR_VERIFY_TMP}"
  trap 'rm -rf "${VENDOR_VERIFY_TMP:-}"' EXIT
  echo "+ extracting to ${tmp}" >&2
  if tar --zstd -xf "${archive}" -C "${tmp}" 2>/dev/null; then
    :
  else
    zstd -d --stdout "${archive}" | tar -xf - -C "${tmp}"
  fi

  # Manifest may live inside the archive (.vendor_manifest.json) or be the
  # committed repo copy; prefer the committed copy as the source of truth.
  local reference="${MANIFEST}"
  [[ -f "${reference}" ]] || reference="${tmp}/vendor/.vendor_manifest.json"

  python3 scripts/gen_vendor_manifest.py "${tmp}/vendor" "${tmp}/regenerated_manifest.json"

  python3 - "${reference}" "${tmp}/regenerated_manifest.json" <<'PY'
import json, sys
ref = {(c["name"], c["version"]): c["checksum"]
       for c in json.load(open(sys.argv[1]))["crates"]}
got = {(c["name"], c["version"]): c["checksum"]
       for c in json.load(open(sys.argv[2]))["crates"]}
mismatch = [k for k in ref if k in got and ref[k] != got[k]]
missing  = [k for k in ref if k not in got]
extra    = [k for k in got if k not in ref]
if mismatch or missing or extra:
    for k in mismatch: print(f"MISMATCH {k}: {ref[k]} != {got[k]}")
    for k in missing:  print(f"MISSING  {k} (in manifest, not in extracted tree)")
    for k in extra:    print(f"EXTRA    {k} (in extracted tree, not in manifest)")
    print(f"FAIL: {len(mismatch)} mismatch, {len(missing)} missing, {len(extra)} extra")
    sys.exit(1)
print(f"ok: all {len(ref)} vendored crates re-checksum against the manifest")
PY
  echo "verify OK: ${archive}"
}

usage() {
  echo "usage: $0 {package [VERSION] [OUT_DIR] | verify <archive.tar.zst>}" >&2
  exit 2
}

case "${1:-}" in
  package) shift; cmd_package "$@" ;;
  verify)  shift; cmd_verify  "$@" ;;
  *) usage ;;
esac
