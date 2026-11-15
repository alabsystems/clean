# Lean-built artifacts for `tests/module_trust.rs`

Written by `lean` v4.30.0-rc2 (the repository-pinned toolchain), module-trust
round 29 (`reports/2026-09-24-module-trust.md` section 12):

| File | Source | How |
|---|---|---|
| `honest/D.olean` | `honest/D.lean` | `lean -o D.olean D.lean` |
| `other/Z.olean` | `other/Z.lean` | `lean -o Z.olean Z.lean` |
| `parts/D.olean{,.server,.private}` | `parts/D.lean` | `lean -o D.olean D.lean` (a `module`: the three parts are written together) |
| `parts_disagree/D.olean{,.server,.private}` | `parts/D.lean` | `parts/` with the `D.olean.private` constant array reduced to its `D.v` record renamed `D.e` (`xpart.py` of round 30's battery): the public part says `D.e := 1`, the private part `D.e := 0` |
| `twice/D.olean` | `honest/D.lean` | `honest/D.olean` with its `D.v` record renamed `D.w` in the constant array and the constant-name array (`ntamper.py N2r` of the round's battery): `D.w` declared twice, `:= 1` then `:= 0` |

`lean` refuses `import Z` + `import D` ("environment already contains 'D.v'
from Z") and `import D` over `twice/D.olean`. Over `parts_disagree/` it
reads the private part: `D.e = 0 := rfl` checks and `D.e = 1 := rfl` does not.
Round 29's `twice/` and the round-30 rows are in
`reports/2026-09-24-module-trust.md` sections 12 and 13.
