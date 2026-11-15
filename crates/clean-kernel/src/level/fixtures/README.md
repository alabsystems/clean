# Pinned-Lean universe-level verdicts

`lean_kernel_verdicts_v4.30.0-rc2.tsv` holds, for 2,009 pairs of semantically
equal universe levels, whether pinned Lean v4.30.0-rc2's kernel accepts the two
as definitionally equal. `level/lean_kernel_tests.rs` reads it with
`include_str!` and requires the Lean kernel theory to agree on every row in both
directions (DECISIONS R150).

| file | what |
|---|---|
| `gen_level_pairs.py` | deterministic pair generator; ground truth is evaluation only (`u, v, w` in `0..3`), no port of either kernel's level algebra |
| `KernelLevelVerdicts.lean` | asks pinned Lean's kernel: per pair, `def t.{u,v,w} : Sort a → Sort b := fun x => x` through `Environment.addDeclCore` with `doCheck := true` |
| `lean_kernel_verdicts_v4.30.0-rc2.tsv` | header `# lean 4.30.0-rc2`, then `a<TAB>b<TAB>ACCEPT\|REJECT` |

Rows: every structurally distinct ordered pair of equal raw levels to depth 2
over `0, 1, u, v, u+1, v+1` (520); a seeded sample (`SEED = 20261017`) of 1,480
depth-3 pairs; the named shapes t1, t2, t3, t3b, t4, t6, t7, t8, t9 of
`reports/level-normalizer-probe-2026-10-17/` (t5 and t10 are constructions, not
pairs: `tc/level_profile_tests.rs` pins them). Encoding: `Z`, `S(x)`, `M(a,b)`,
`I(a,b)`, `P(name)`, all nodes raw.

## Regenerate

Under aterm a bare `lean` is Clean; put the pinned toolchain first on `PATH`:

```sh
python3 gen_level_pairs.py pairs.tsv
PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin:$PATH" \
  lean --run KernelLevelVerdicts.lean pairs.tsv > lean_kernel_verdicts_v4.30.0-rc2.tsv
```

## Measured 2026-10-19

- `gen_level_pairs.py`: depth-2 520, depth-3 sample 1,480, named 9, total 2,009;
  two runs byte-identical.
- `lean --run` (v4.30.0-rc2): rc 0, 5.4 s; 1,355 ACCEPT, 654 REJECT; sha256
  `f45349f4eeb03e8548034fa4bb6d353e3019cf34a81fef2ea284540c46cc25e4`.
- The same pairs through v4.33.1 (`addDeclCore` takes its extra argument there)
  give identical verdicts on every row: `level.cpp` differs between them only by
  the added `normalizes_to_zero`, which `is_equivalent` does not use.
