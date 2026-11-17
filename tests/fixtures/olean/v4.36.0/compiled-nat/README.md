# Lean 4.36 imported Nat runtime

The official Lean 4.36.0 compiler supplies the comparison for this fixture.
[Lean 4.36.0 release](https://github.com/leanprover/lean4/releases/tag/v4.36.0)

`CapturedNat.lean` imports the existing [module-ir producer](../module-ir),
checks a theorem by `rfl`, and evaluates the same expression. With the
original artifact set, Lean prints `41`. With the two replacement IR parts,
it prints `42`, and the same theorem still passes. The base, server, and
private `.olean` files are byte-identical in both cases. The existing
`App.lean` run prints the same respective values and exits with status 17
in each world.

To reproduce the replacement parts, copy `../module-ir/lakefile.toml` and
`../module-ir/lean-toolchain` into a fresh directory. Copy
`replacement/StableFixture/Defs.lean` there at `StableFixture/Defs.lean`
and run the official SDK's `lake build StableFixture.Defs:c`. The source
changes only the value of the producer's private `offset` from 1 to 2.
The replacement companions are under `.lake/build/lib/lean/StableFixture`.

For the comparison, put the five original parts in a directory containing
`StableFixture/` and use that directory as the sole `LEAN_PATH` entry.
Run `lean CapturedNat.lean` and `lean --run App.lean`, using
`../module-ir/App.lean` for the latter. Repeat with
`replacement/StableFixture/Defs.ir.sig` and
`replacement/StableFixture/Defs.ir` copied over the original companions.
