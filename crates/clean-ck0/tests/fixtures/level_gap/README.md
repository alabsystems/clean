# Pinned-Lean verdicts on the level-gap declarations

`lean_kernel_verdicts_v4.30.0-rc2.txt` holds pinned Lean v4.30.0-rc2's kernel
verdict on each declaration that `../../level_as_written/residue.rs` and R174's
universe-check tests in `../../level_geq_and_nested_size.rs` pin
(`docs/DECISIONS.md` R174, R177). `LevelGapKernelVerdicts.lean` hands each one to
`Environment.addDeclCore` with `doCheck := true`, over `Init.Prelude`, with
its levels built from the raw constructors, so the kernel alone decides.
`level_as_written/residue.rs` (part of the `level_as_written` test target)
reads the table with `include_str!` and requires each
row's verdict to be the one its pin states.

## Regenerate

Under aterm a bare `lean` is Clean; put the pinned toolchain first on `PATH`:

```sh
PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin:$PATH" \
  lean --run LevelGapKernelVerdicts.lean > lean_kernel_verdicts_v4.30.0-rc2.txt
```

## Measured 2026-10-28

`lean --run` (v4.30.0-rc2): rc 0, 35 rows, 11 ACCEPT and 24 REJECT; sha256
`fcfc1a19272d37f4058dc2ecd52bf507c2daf9895bf1994236cc9e4e679af804`. The first 11 rows (R174) are byte-identical to the 11-row table of
that date, and the first 25 to the 25-row table. Rows 12-15 are R177's
instantiation residue and its controls. Rows 16-25 are R177's third form, an
`imax` that reduces to a `max`, under a written `succ`, and rows 26-35 the
same `imax` with no `succ` written, where the kernel adds it typing `Sort l`
as `Sort (succ l)`; each set with its controls.

Do not measure a theorem through `addDecl` under `try`/`catch`: under
v4.30.0-rc2 its kernel error was logged after `addDecl` returned, and the
`catch` never saw it.
