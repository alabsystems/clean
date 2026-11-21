# Lean 4.36 proof-only module export

The official Lean 4.36.0 arm64 Darwin SDK at
`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9` produced all five `Seal`
artifacts. The public and server constant arrays carry axiom records for
the three public signatures. The private array carries the real axiom
`Seal.gap` and the three theorem bodies, including `Seal.hidden`.
The public axiom-collection extension preserves the dependencies of the
weakened theorem rows. This distinguishes a public theorem with an
axiom-free proof from one that relies on `Seal.gap`.

Rebuild in a scratch copy of this directory with the SDK's executable
in `LEAN436`. All five artifacts reproduced byte for byte.

```sh
LEAN_PATH=. "$LEAN436" -o Seal.olean Seal.lean
LEAN_PATH=. "$LEAN436" Consumer.lean
LEAN_PATH=. "$LEAN436" Private.lean
LEAN_PATH=. "$LEAN436" Hidden.lean
```

`Consumer.lean` exits 0 and prints

```text
'Seal.exportedProof' does not depend on any axioms
'Seal.usesGap' depends on axioms: [gap]
```

`Private.lean` exits 0 and prints `Seal.hidden : True`. `Hidden.lean`
exits 1 and prints

```text
Hidden.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `Seal.hidden`
```

All five artifacts were present during each run. Each run had empty stderr.

| Artifact | SHA-256 |
| --- | --- |
| `Seal.olean` | `111e5d3080b3b0bff94572ed50b92fd4ab36e4645c6093cdc28343d3cf6e0032` |
| `Seal.olean.server` | `a8bea1a7e47f58bdce2e6be72dae73966e43d1a64ed1efe3a1b430db35ea96f5` |
| `Seal.olean.private` | `350b2a9181288692a66564114bff63f235e1101f3d56a0539b018b7bfd44da05` |
| `Seal.ir.sig` | `f833777c9ba24ed8cd7f873ad79bcf3870d05176aa54e0a1f26078ed66e0fe12` |
| `Seal.ir` | `073dbd86959997d11f6af177773ed54fd8535f00705a7d037493274933e675a7` |
