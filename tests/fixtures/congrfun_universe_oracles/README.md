# congrFun over one `Sort _` carrier: Lean oracle fixture

`declarations.lean` and `declaration-results.json` are copied byte for byte
from `reports/implicit-positional-arguments-2026-11-06/congrfun-universe-oracles/`,
which stays as the dated history of the run. The results record pinned Lean
4.30.0-rc2, 4.35.0 and 4.36.0-rc2 accepting the source (exit 0, matching
`source_sha256`). `test_level_occurs_congr_fun_over_one_sort_hole_preserves_polymorphism`
(`crates/clean-elab/src/tests_pkg4_level_occurs.rs`) reads both files and
checks that the digest still matches, so the fixture cannot drift from the
runs that justify it.
