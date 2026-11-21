# Native Nat comparison

The official Lean 4.36.0 SDK at commit
`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9` produced `stdout`. Replay the two
sources in order with the release's `lean --run`.

```sh
lean --run NatVectors.lean
lean --run NatCarrierBoundary.lean
```

`c_wide_nat.c` exercises the matching C runtime operations and word
representations. It also checks copying, reference consumption, and the
separate bounded `u128` reader. Run `NatVectors.lean` with
`pow-exponent-cutoff` or `pow-aliased-oversized` to replay the two
`Nat.pow` panics. Each must produce empty stdout, the exact runtime message
on stderr and exit status 1. Two power-of-two vectors compare more than
four million bits through both scalar and heap input carriers. The last
cases cross the constructor
header's inline storage limit with a 33-limb Nat.

From `crates/clean-runtime`, the same comparison runs directly through the
host C compiler.

```sh
cc -std=c11 -O2 -I include src/clean_runtime.c tests/c_wide_nat.c -o /tmp/clean-wide-nat
/tmp/clean-wide-nat | cmp - tests/wide_nat_oracle/stdout
```
