# `deep_recursion` — self tail calls compiled as loops

**Unit:** X4's gap `head-loop-is-not-a-loop` of
`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`.
**Test:** `crates/clean/tests/deep_recursion.rs`.
**Evidence:** `reports/x4-head-loop-2026-11-15/`.

Each program is real Lean that pinned Lean v4.30.0-rc2 compiles. The test
builds each with `clean run --keep-temp` at optimisation levels 0, 1 and 2, on
the C lane and (with `trust-ir-backend` and `CLEAN_TRUST_CG_BIN`) on the
trust-cg lane, and runs the kept executable by itself on a 512 KiB main-thread
stack (`ulimit -s 512`). A loop program must print `expected/<name>.stdout`
and exit 0 there; a pinned overflow must die of a signal after printing a
prefix of it.

| Program | Kind | What it pins |
|---|---|---|
| `head_loop_10m` | loop | c27's head loop (structural on the counter, function-typed motive) at 10⁷ steps |
| `tail_k0_10m` | loop | a self tail call whose recursive function takes only the counter (`k = 0`) |
| `mutual_acc_1m` | loop | c36's shape: a structural mutual block of two-argument members calling across members in tail position, 10⁶ steps; Clean's selector function makes the cycle a loop (Lean has no mutual tail calls: its binary aborts on an 8 MiB stack) |
| `swap_loop` | loop | a back edge passing its parameters permuted (parallel assignment) |
| `poly_loop_10m` | loop | a polymorphic loop whose back edge passes an erased type argument |
| `wf_loop_1m` | loop | `termination_by` (well-founded) recursion with a tail call, 10⁶ steps |
| `io_twice` | loop | an action IH used twice runs twice |
| `two_use_ih` | loop | a pure IH used twice is computed once (2⁶⁰ calls otherwise) |
| `for_unit_state` | loop | `for` loops in `IO` with `PUnit` state: an object passed to an erased parameter by the loop's continuation (a regression X4's direct IH calls exposed) |
| `non_tail_deep_1m` | overflow | NEGATIVE CONTROL: `deep n + 1` is not a tail call and must overflow the small stack |
| `io_loop_10m` | overflow | gap `io-loop-through-bind-continuation`: the recursive call sits in `IO.bind`'s continuation lambda, not in `go`'s tail; Lean's binary exits 0 |
| `mutual_even_odd_10m` | overflow | gap `mutual-value-pack-not-a-loop`: the elaborator packs this one-argument block into one function returning the pair of results (`isEven.isOdd.pack`), a non-tail recursion; Lean's binary aborts on an 8 MiB stack too |

## Expected bytes

Minted with
`scripts/heavy_gate.sh run 1 x4-lean-build -- python3 reports/x4-head-loop-2026-11-15/mint_deep_expected.py <scratch>`,
which runs `scripts/native_exec_battery_expected.py --fixture
tests/fixtures/deep_recursion` (`lean --run`) and, for the three programs on
which Lean's interpreter overflows its own stack (`mutual_acc_1m`,
`mutual_even_odd_10m`, `non_tail_deep_1m`), takes pinned Lean's compiled
binary's bytes instead (`lean -c`, `leanc`, run at Lean's default main thread,
exit 0). On an 8 MiB main thread (`LEAN_MAIN_USE_THREAD=0`, `ulimit -s 8176`)
pinned Lean's binaries of those three abort with `Stack overflow detected.
Aborting.` (exit 134); the X4 report records each.
