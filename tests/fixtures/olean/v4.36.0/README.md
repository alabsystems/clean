# Lean 4.36.0 fixtures

These fixtures were produced by the official macOS arm64 distribution of
[Lean v4.36.0](https://github.com/leanprover/lean4/releases/tag/v4.36.0),
commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. The
[provenance manifest](fixture-provenance.json) records the verified release
archive digest, Lean and Lake binary identities, and the size and SHA-256 of
each input, output and artifact. The matching
[Mathlib revision](https://github.com/leanprover-community/mathlib4/tree/fc4f59e577feb1a4956671bc04ac18aaaf8cd842)
is pinned for subsequent project checks.

Run these commands with the official distribution's `bin` first on `PATH` and
no other Lean toolchain or library override. Work in a copy of this directory.

```sh
cd matcher-metadata
lean --root . -o MatcherParity.olean MatcherParity.lean
LEAN_PATH="$PWD" lean Inspect.lean
cd ../plain
lean --root . -o StablePlain.olean StablePlain.lean
cd ../module-ir
lake build StableFixture.Defs:c -v
export LEAN_PATH="$PWD/.lake/build/lib/lean"
lean App.lean
lean --run App.lean
lean MetaUse.lean
```

`Inspect.lean` prints the five JSON records stored as an array in
`matcher-metadata/oracle.json`. `StablePlain` uses an ordinary prelude import
and exercises theorem and definition decoding. The Lake package uses postponed
compilation and produces the three `.olean` parts, `.ir.sig` and `.ir` in
`.lake/build/lib/lean/StableFixture`. `App.lean` checks an imported theorem and
its program prints `41` followed by a newline and exits `17`.
`MetaUse.lean` checks a proof using an imported elaborator and prints `74`
followed by a newline.

A second run in a fresh directory reproduced all seven binary parts byte
for byte and agreed on the five matcher records, both proofs, stdout and
the program exit status. This directory supplies upstream reference results
for Clean's compatibility tests.
