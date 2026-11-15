# Lean 4.8 matcher metadata fixture

`MatcherParity.olean` is the unchanged output of Lean 4.8.0 for the adjacent
source. `Inspect.lean` reads the actual match compiler extension through Lean.
The fixture imports `Init.Prelude` from that exact installed toolchain.

The three recorded matchers are `choose.match_1`, `chooseEq.match_1`, and
`chooseTwo.match_1`. Their parameter counts are zero, discriminant counts are
1/1/2, alternative argument counts are `[1,1,1]` / `[1,1,1]` /
`[1,1,1,1]`, and elimination universe positions are all `some 0`. The named
case stores `some h`; all other discriminant names are absent. The ordinary
function named `ordinary.match_1` is not registered as a matcher.

Lean 4.8 unboxes the one-field `DiscrInfo`: its array element is the
`Option Name` itself. The decoder tests pin both `none` and `some h`.

Generation: `lean --root . -o MatcherParity.olean MatcherParity.lean`, then
`LEAN_PATH=. lean Inspect.lean`. Native commands, producer identity and the
original output are retained under `NOV10-CLEAN-SIMP-MATCHERS/oracle04` in the
external qualification archive. These artifacts do not certify the reader
or any whole compiler.

- source SHA256: `b4dbce1de5079b8d1d843124460f3ff4f07b40d0339098879b32b5e6cf7723fe`
- olean SHA256: `a7700d2121999ec7c10e805c78ba9442adbb4db5426b915bb6120e716ef15b86`
- inspector SHA256: `84e16147a631d7188b92aa9febc80f454beb483c076019df294d8e8187f1351b`
