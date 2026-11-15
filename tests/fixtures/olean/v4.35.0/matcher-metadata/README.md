# Lean v4.35.0 matcher metadata fixture

The adjacent source was compiled by the official Lean v4.35.0 executable.
`Inspect.lean` reads the actual match compiler extension; its five JSON rows are
retained in `oracle.json`. Four definitions are registered as matchers; the
ordinary function named `ordinary.match_1` is absent from the registry.

These bytes measure the six-field matcher representation, alternative field and
unit-thunk counts, named discriminant equations, and nonempty overlap maps.
The overlap map has rows `1 → [0]` and `2 → [0, 1]`. It is stored as a bounded
hash map whose values are size-annotated binary tree sets.

Actual generation used `lean --root . -o MatcherParity.olean MatcherParity.lean`,
then `LEAN_PATH=. lean Inspect.lean`. The immutable external archive is
`/tmp/clean-root-latest-matcher-native-oracles-completed-archive`, index SHA256
`6606590a61588ce179c2078487700e7d8b065d92c99d64a98a3af621ccc23e82`.
All six commands across both official profiles exited zero. All 36,118 declared
toolchain input files matched before and after execution. Two earlier failed
inspection drafts are retained separately and provide no successful metadata
claim. This fixture is producer evidence; Clean reader and proof behavior still
require their own executed checks.

- MatcherParity.lean SHA256: `e716da41e22b93f751aa9e26c93e1e5c3a8311866fffaebc5426e5741d8b2ec3`
- MatcherParity.olean SHA256: `a259115242badbf11079939389a9ad53b36fb6d4de3f702eff7e85142e762abd`
- Inspect.lean SHA256: `34a997b6be8a3dac3f70501ed15455bccf73a1d36ecf822d493fe7b30e06d30a`
- oracle.json SHA256: `9b2a097b7d3db6d800116259018f1f98da2fcb0871a6d9107305c7c1497075e8`
