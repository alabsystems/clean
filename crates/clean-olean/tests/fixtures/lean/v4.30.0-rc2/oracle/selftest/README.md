# `oracle/selftest` — the dumper's own probe family

Not a fixture for any `clean-olean` parity test: this family exists so the
oracle (`../DumpOlean.lean`) and the compile helper
(`clean_olean::test_support::compiled_fixture_dir`) have an
end-to-end regression that exercises every shape the real families use —
a `prelude` single-component twin (`Sib`), a hierarchical twin (`Sub/part`),
an ordinary module importing both (`Probe`: inductive, definition by `match`,
theorem, class + priority-731 instance, `@[simp]` theorem, `export` alias,
opaque, axiom, `let`, string literal) and a `module`-header source (`ModProbe`:
`public`/`private`/plain defs) that yields the `.olean.server`/`.olean.private`
companions.

## Recipe

Toolchain: `leanprover/lean4:v4.30.0-rc2`, `lean --version` =
`Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit
3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)`.

From this directory, with `LEAN_PATH=$PWD` and
`L=~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`, in `ORDER`
order:

```sh
$L --root . -o Sib.olean Sib.lean
$L --root . -o Sub/part.olean Sub/part.lean
$L --root . -o Probe.olean Probe.lean
$L --root . -o ModProbe.olean ModProbe.lean     # also writes ModProbe.olean.server, .private, .ir
```

`compiled_fixture_dir("oracle/selftest")` performs exactly these steps in a
content-addressed copy under `<target>/clean-olean-lean-fixtures/`.

## Assertions the family satisfies (measured 2026-09-15, all four compiles exit 0)

Through `DumpOlean.lean`:

* `Probe.olean`: 49 constants = 49 `const_names`, 31 extension entries,
  `is_module=false`; kinds definition 33, theorem 7, constructor 3, recursor 2,
  inductive 2, axiom 1, opaque 1; four import rows `Init`, `Init` (meta),
  `Sib`, `Sub.part`, each `import_all=false, is_exported=true`.
* Decoded extension rows in `Probe.olean`: `Lean.aliasExtension` 1
  (`target.dot` → `Probe.Exports.target.dot`), `Lean.classExtension` 1
  (`Probe.Cls`), `Lean.Meta.instanceExtension` 2 (`Unary._sizeOf_inst` at
  1000, `Probe.instCls` at 731), `Lean.Meta.simpExtension` 4 theorems
  (`Unary.zero.sizeOf_spec`, `Unary.succ.sizeOf_spec`, `Unary.succ.injEq`,
  `Probe.lem`).
* `ModProbe.olean{,.server,.private}`: constants 1 / 1 / 3 — `ModProbe.visible`
  is an axiom stub in the base and server parts and a valued definition only in
  `.private`, beside `_private.ModProbe.0.ModProbe.hidden` and
  `_private.ModProbe.0.ModProbe.internal`; entries 10 / 11 / 13.
* Env mode `--env Probe --search-path <dir>`: 49 rows, instances
  `Unary._sizeOf_inst` and `Probe.instCls`, class `Probe.Cls`, every constant
  present.

The Rust regression
(`test_selftest_family_compiles_and_the_oracle_reads_it_in_both_modes`) asserts
only relations, not these counts — the counts are recorded here so a drift on
a toolchain bump is visible, not so anything trusts them.
