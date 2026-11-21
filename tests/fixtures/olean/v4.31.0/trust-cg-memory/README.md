# Lean v4.31 Trust-CG memory qualification input

These two modules were produced by the official Lean v4.31.0 executable at
`68218e876d2a38b1985b8590fff244a83c321783`. They provide a concrete positive
fixture for qualifying Clean's future v4.31 support. They do not register a
world or establish independent Clean verification.

`MachineMemory431.lean` contains literal Trust-CG `MachState`, register and
memory definitions, plus its existing byte-address/frame lemmas. The source
book binds those excerpts to Trust-CG commit
`7e54ef60ec47938565d15db3831cca1da095f4b4`. It uses the original `BitVec 64`
addresses and `writeMem`, rather than a Nat-address model. Its additional
theorems cover the address increments, the copied divisor after X0 changes,
the two eight-byte stores, preservation of protected text bytes, and an actual
overlap that changes a byte.

`MachineFetch431.lean` uses the same commit's literal `readMem_congr_bytes`
lemma to prove that the original four-byte instruction read is preserved
after the pair store when those four addresses avoid its sixteen write
addresses. This fixture copies definitions; it does not import or qualify the
whole `Trust.A64.Machine` module. Concrete instruction decoding/execution,
object/relocation binding and full function correctness remain separate.

Both producer compilations exited zero. `Inspect.lean` and the fetch module's
axiom reports cover all eleven selected theorems; their reported closures
contain only `propext` and `Quot.sound`. The three false controls each exited
one because the claimed proposition is false, and wrote no `.olean`.

The installed Clean executable recorded in [the oracle](oracle.json) parsed
the memory and fetch files with 30/30 and 5/5 declarations, without recovery,
under its unchanged v4.30rc2 grammar. Its
explicit v4.31 verification command still refused with exit two. Parse-only
success and the producer's results do not close that verification gap. The
world registry, Oracle, native-fold authority and import policies are unchanged.

The producer came from GitHub asset `448155813`,
`lean-4.31.0-darwin_aarch64.tar.zst`, 543754552 bytes, SHA-256
`264105500c8abdf37b68ffe03390a783ed259807807222698da8dd92d6ce0a27`.
The whole 15193-entry distribution input book matched before and after all
producer commands, including file contents, modes, timestamps and symlinks.
The raw `PRODUCER-INPUTS-BEFORE.json` and `PRODUCER-INPUTS-AFTER.json` books
have identical SHA-256 `8e7ae34dee9ebb1b95d6498cc65f5adcc8b0a263974b384b39791088543c0a2f`.
`oracle.json` records the executed roster and artifact hashes. Raw producer and
inspection logs remain separate evidence; the committed fixture uses portable
filenames and content digests.

Reproduce with that exact authenticated producer, from this directory:

```sh
fixture_lean=/absolute/path/to/lean-4.31.0-darwin_aarch64/bin/lean
"$fixture_lean" -j1 -M2048 -T10000000 --root . -o MachineMemory431.olean MachineMemory431.lean
LEAN_PATH=. "$fixture_lean" -j1 -M2048 -T10000000 --root . -o MachineFetch431.olean MachineFetch431.lean
LEAN_PATH=. "$fixture_lean" -j1 -M2048 -T10000000 --root . Inspect.lean
LEAN_PATH=. "$fixture_lean" -j1 -M2048 -T10000000 --root . -o FalseNext.olean FalseNext.lean
LEAN_PATH=. "$fixture_lean" -j1 -M2048 -T10000000 --root . -o FalseOverlap.olean FalseOverlap.lean
LEAN_PATH=. "$fixture_lean" -j1 -M2048 -T10000000 --root . -o FalseFetch.olean FalseFetch.lean
```

The last three commands must fail. Do not substitute these producer results
for bounded independent Clean checks after the measured world is qualified.
