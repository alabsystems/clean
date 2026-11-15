# Closure-cache fixture pair (Lean v4.30.0-rc2)

Two modules for `crates/clean-mathverse/src/cli/graduate_closure_cache_tests.rs`:

- `Init.lean` — a `prelude` LEAF: it imports nothing (inductive `Leaf`, def `Leaf.same`).
- `Target.lean` — `prelude` + `import Init`, where `Init` is the leaf beside it (def `targetVal`).

So the closure of `Target` is `{Target, Init}` and it is acyclic. The previous layout copied
`v4.13.0/custom/Minimal.olean` into both slots; Minimal imports `Init`, so that `Init`
imported itself, which the typed import graph refuses as a dependency cycle.

Regenerate with the pinned toolchain, pointing `LEAN_PATH` at this directory ONLY so that
`import Init` resolves to the leaf and never to Lean's own `Init`:

```sh
L=~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean
LEAN_PATH=$PWD $L -o Init.olean Init.lean
LEAN_PATH=$PWD $L -o Target.olean Target.lean
```
