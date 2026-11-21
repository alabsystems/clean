# Lean 4.36 compile-time Nat functions

The official Lean 4.36.0 SDK produced these three declaration parts with
`lean -o MetaMark.olean MetaMark.lean`. The marked and ordinary definitions
both have Nat signatures. The base file includes compiled code for the
marked definition and an opaque IR entry for the ordinary definition.

A source file beginning with `module` and `import MetaMark` prints `20`
for `#eval markedNat 7`. The same import refuses `#eval ordinaryNat 7`
on phase visibility. Both observations use the three included artifacts
with neither separate IR companion present.
