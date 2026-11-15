These are the unchanged native IR bundles captured by the complete development
Trust 9794 toolchain while checking `trust-intbound` at parent source c133258d3c.
The original qualified helper inventory is retained under
`NOV3-TRUST-ON-TRUST-HELPERS/after/trust-intbound/verifier-inputs`.

- `clamp_width.json`: SHA-256 `1ba90d0a8a711e52ed4a7a15012c72216c0961a397285b3e4f9538486645514b`
- `clamp_to_max.json`: SHA-256 `e563693d5143327c2b77d2a7985958e5987cc778614d931a899f0b921f1ad838`

Both keep all seven original proof-obligation records and every instruction,
including range assumptions and the allocation/store/load path. The test uses
the canonical native bundle and binary readers plus the reference interpreter.
SemR's existing binary decoder binds the exact preserved serialized modules
to the quoted program theorems. The new proofs use SemR's independent `Step`
and `Exec` relations and existing integer byte-memory laws.

The native program statements are universal over valid U32/U64 inputs. The
comparison and arm-swap rules also cover U8/U16 in the shared same-width unsigned
fragment. Wrong comparison, swapped arms and wrong selected bound are separate
mutants of the retained modules; they are not replacement source captures.

No theorem here certifies Rust-to-IR lowering, source-query reconstruction,
compiler publication authority, or arbitrary memory aliasing. Those remain
separate boundaries. Proof-label metadata does not grant authority, and the
native bundle's existing solver result is not used as a theorem.

The `.tirb` files are the exact v41 serialization retained from the original
qualification attempt, including all seven proof rows. `wire-manifest.json`
records their SHA-256 identities. The current binary reader must decode each
one to the original typed module or its explicitly named test mutation; a
new writer cannot silently replace the proof question. Replaying the saved
proof also binds its decoded and returned claims to these supplied bytes in
the current canonical SemR context.

The literal builder balances its append tree without changing any bytes.
The shared replay checks complete `List Nat` equality before proof reuse, then
requires exact request-byte identity. A metadata-only mutation keeps the native
function and its execution unchanged but must still be refused as a different
input. Semantic decoder equality alone is not byte identity.

`SemRClampTransfer.lean` checks a concrete execution witness for each of the six
mutants, proves that its original universal claim implies the corresponding
wrong result, and refutes that claim. Transfer controls compare those checked
consequences and require a type mismatch; a timeout cannot satisfy a control.
The full original proof closure remains mandatory. This fixture uses a finite
8,000,000-heartbeat per-declaration allowance; the global 2,000,000 default is
unchanged and does not accept these full-wire equality proofs.
