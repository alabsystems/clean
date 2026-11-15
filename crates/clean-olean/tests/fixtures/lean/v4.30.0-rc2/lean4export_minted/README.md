# lean4export-minted exports (pinned Lean v4.30.0-rc2)

Exports written by lean4export itself, not by Clean, so that Clean's export
writer (`clean_export_write`, self-proof unit Q1) can be compared with what
pinned Lean's own exporter writes for the same declarations.

- `prelude_roots.ndjson.gz`: lean4export, built at commit
  `12581a6b680d8478175596338eb2d53383a323e3` (tag `v4.30.0-rc2`) for pinned
  Lean v4.30.0-rc2 by `scripts/lean_export_mint.sh`, run over `Init.Prelude`
  with `--export-mdata` and ten `--decl` roots (the sidecar lists them), then
  compressed with `gzip -9 -n`. The sidecar
  `prelude_roots.ndjson.sidecar.json` is the mint script's own record: the
  command, the exporter commit and the sha256 of its binary, the toolchain and
  its githash, and the sha256 of the uncompressed export.

Read by `crates/clean-olean/tests/ndjson_export_lean4export_differential.rs`,
which checks the decompressed bytes against the sidecar's sha256 before using
them. To mint again:

```sh
scripts/lean_export_mint.sh --toolchain v4.30.0-rc2 --module Init.Prelude \
  --export-mdata --decl Nat.add --decl List.map --decl String.utf8ByteSize \
  --decl Array.push --decl Quot.lift --decl Lean.Syntax \
  --decl of_decide_eq_true --decl sorryAx --decl Lean.Macro.MethodsRefPointed \
  --decl Lean.Name.hash --out prelude_roots.ndjson
gzip -9 -n prelude_roots.ndjson
```

lean4export is Apache-2.0 (Lean FRO); its source is not vendored here.
