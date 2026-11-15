# Current canonical scalar intake (owned dependent source fixture)

## Current selected source

The nine IR-owned source copies select canonical IR
`bd313b4fbfae2c2826bade463e23224f1df9a61a`, together with its unchanged
`U64ScalarProfile`. `SemR.lean` SHA-256 is
`0ea0e29f2b0d70a158f0ac54725d5175b9be81f4fc5b0a4d0839e9b968ee180d`.
The canonical decoder/model includes the wire-70 blob/tensor additions; no
Clean-owned program interpretation is substituted for it.

The initialized unsigned Select/copy/equality/return laws are the exact
supplemental canonical source published in IR
`1edad551f5df3fef3f21123101a0f10431e38797` (`SemRUnsignedSelect.lean`, SHA-256
`0dc1b27bed50e1643964e92e28bb07851e6900fc5ceceb16cfcf87585f3d95e7`). They
must be compiled against this selected model, rather than reusing an artifact
from an earlier model. The shared Boolean/scalar WP and typed claim fixtures
consume that same semantics and keep the original program and question bytes.

`SOURCE_REVISION` and the source-object regression identify this source intake.
The distinct Cargo consumer-edge check still requires the actual compiled
SemR witness to match; source qualification cannot waive a mismatching edge.
Earlier proof runs retain their original model/input identities. Producer
qualification does not establish a fresh independent Clean CIC replay, source
refinement or production proof authority.

## Historical design and qualification record

The following descriptions and counts refer to their recorded earlier cuts; they
do not replace the current source selection above or qualify this new decoder.

This source family explicitly selects published IR `b7c5c90124b248c94b676d56e4e74bbb7734be6e`.
The root Cargo pins are deliberately unchanged pending canonical R3/G3 adoption.
The declared-source-object check can qualify this fixture; the separate actual
consumer-edge pin check must still refuse a mismatching old pin. No test or gate
waives that distinction.

Eleven modules are now in ORDER: nine byte-exact canonical IR copies plus the
existing SemRCheck and new U64AdditionConsumer byte-subject claims. The latter
only lifts canonical decode/run/no-body-violation; it introduces no source model.
The exact262-byte compiler module is wire38. A separately produced full canonical
278-byte v63 encoding decodes identically. Scalar v63 support still refuses
MakeClosure instructions/nonempty closure tables; future and malformed encodings
remain refused. The old blanket v63-refusal negative is replaced by the actual
unsupported-instruction negative, with its population retained.

`semr_u64_addition::canonical_scalar_full_recheck_and_subject_refusals` imports
untrusted upstream .oleans, then rechecks the COMPLETE dependency closure of all
kernel declarations in the new scalar+audit+consumer modules from EMPTY through
Clean's pinned ReferenceKernel, not the upstream Lean kernel. The exact returned
and NoBad predicates use canonical SemR and its existing relational theorem.
Wrong term, bytes, literal and return claims use that SAME full checked entry.
This is canonical IR mathematics, not TCX/THIR/source faithfulness, a physical
Rust ABI/ISA theorem, SourceNoUB, a body license or a new grade.

## Preserved earlier model/evidence documentation

# `semr` — RM4: SemR, trust-ir level R's one semantics

Proven-core plan RM4 (Trust `docs/plans/2026-10-15-proven-core.md` §5 milestone 5;
increment 6 of the KR0 plan's §9). Seven module sources the pinned `lean -o` compiles
(`ORDER`), so Lean's kernel checks them first; `crates/clean-olean/tests/semr_reference.rs`
then admits their cone through `ReferenceKernel` and audits the closures.

| Module | What it declares |
|---|---|
| `SemR.lean` | trust-ir `lean/semr/SemR.lean`, byte for byte (SHA-256 pinned on both sides): level R's syntax for the scalar/control-flow fragment, the binary decoder (wire v38–v62), the operator layer on `w`-bit residues (no `Int` division), the executable step (`execNode` dispatching to one step function per instruction, `stepCore`, `run`), the small-step relation `Step` (one rule per instruction and outcome, stated without the executable; its frame-open check `Opened`, signature check `SigChecks` and block-parameter binding `ParamsBind` are its own rules) and the run relation `Exec` over it, and `step_sound`, `step_complete`, `step_det`, `run_sound`, `run_complete`, `exec_det` |
| `MiniRust.lean` | trust-ir `lean/semr/MiniRust.lean`, byte for byte: the `trust_sem` family's `SpecrPrelude.lean` and `MiniRustSlice.lean` (Trust's specr translator output) in a `noncomputable section` (`semr_minirust_copy_is_the_trust_sem_slice`) |
| `SemRMiniRust.lean` (imports `SemR`, `MiniRust`) | trust-ir `lean/semr/SemRMiniRust.lean`, byte for byte: for every integer type and every residue, SemR's operators are MiniRust's generated `MRf.Machine.eval_bin_op`/`eval_un_op` on any machine and fuel — `intBin_minirust` (add, sub, mul, udiv, sdiv, urem, srem, and, or, xor — the bitwise three at the operand's own signedness, `bitwise_resid` — shl, lshr, ashr: value for value, UB for UB), `intUn_minirust` (neg, not), `ctpop_minirust` (MiniRust's `CountOnes`, its count typed `u32`), `icmp_minirust` (all ten comparisons), `ovf_minirust` (the checked trio, value and flag); the value level on well-typed integer operands (`evalBinop_minirust`, `evalUnop_minirust`, `evalIcmp_minirust`, `evalOverflow_minirust`), `ICmp` on `Bool`s (`icmp_bool_minirust`, the equalities and unsigned orders), and `isize`/`usize` at MiniRust's x86_64 8-byte pointer (`mr_ptr_size`, `mr_usize`) |
| `SemRMemory.lean` (imports `SemRMiniRust`) | trust-ir's exact normal-memory proof layer: byte reads/writes, uninitialized bytes, target-aware integer images and load-after-store with explicit 32/64 premises; liveness/bounds facts; the separately scoped 64-bit MiniRust representation and access correspondence |
| `ClosureConstruction.lean` | Exact quoted closure construction contracts: actual captures, nominal signatures, memory preservation, malformed-input refusals and the v63 MakeClosure instruction refusal |
| `MetadataCheck.lean` | Exact parser controls for scalar catalogs, non-authoritative proof metadata, malformed tags/lengths/options, and refused typed bindings |
| `SemRCheck.lean` (imports `SemRMemory`, `ClosureConstruction` and `MetadataCheck`) | The original `subBlob`, runs, corruptions, operator instances and five false statements/refutations; target-width footprints/images, zero-sized u64 count/index, allocation-address boundaries and a 32-bit load/store instance, with false 32-bit footprint/image/allocation claims for the native forgery controls |

The merge of main's RM4c/R211 work retains its real memory blob and runs,
MiniRust decode/alignment/dead-slot instances and all six memory forgery
controls alongside the target-width controls. VF5 and VF7 now import this
single SemR source; the duplicate `vf5_f1/SemR.lean` is removed as on main.
The nine copied source modules now match published IR
`4d74bf705138e2603e4f3eb5455f6aac8a72773f`, including its storage-only geometry, wire64/65 decoder boundaries,
`ClosureConstruction.lean` contracts and metadata parser controls. The existing memory and target-width
proof layers keep their exact source bytes. Current source and independent
proof checks are required to qualify this intake; historical reports keep their original
input identities.

Rules SemR keeps: no `native_decide`, `partial`, `sorry`, `axiom`, `opaque`, `implemented_by`,
`extern` or `unsafe`. Two layers hold them (Clean R164):

* `semr_theorems_are_admitted_through_the_entry_with_closure_in_ax0` (`--release`) audits EVERY
  kernel declaration all seven modules make (their `.olean`s' own constant lists): each is
  admitted through the entry, is neither an axiom nor opaque, and has a closure ⊆ Ax0 whose
  cone reaches no `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat` or `Lean.trustCompiler`.
  The compiler's `_unsafe_rec` twins and its non-kernel names (`_boxed`, `_closed_N`, …) are
  counted and set aside. The negative control is the `semr_forged` family.
* `semr_fixture_is_trust_irs_semr_byte_for_byte` scans all seven sources with comments removed
  and string and character literals KEPT (fail closed), lexing literals so that none can open a
  comment or a string; this covers what the kernel cannot see (`implemented_by`, `extern`).

`semr_fixture_is_the_pinned_trust_irs_semr` compares all nine copied source files,
including `SemRMemory.lean`, with trust-ir's `lean/semr/` files at the revision Clean's
`Cargo.lock` resolves for clean-olean's test-only `trust-ir-semr` witness.
It selects that actual consumer edge, not the first Trust-IR package row, so
the production compiler cohort can retain its qualified predecessor revision.

`SOURCE_REVISION` records the published source revision
`4d74bf705138e2603e4f3eb5455f6aac8a72773f`. The witness, nine exact copied
source files and their digests move together. `ClosureConstruction.lean` is the
fifth copied source: its capture-preservation, nominal-signature and failure
contracts join the reference entry's complete declaration audit and exact Ax0
census. `SemRCheck` imports that proof module. The v63 MakeClosure instruction refusal is itself
one of the checked theorem roots; a proof of that refusal must not prove its
opposite. The executable decoder recognizes versions 38–65 with explicit unsupported-constructor refusals. Quoted
construction grants no wire admission, subset or machine-code proof credit.

The source-object test compares every copy with the immutable Git revision,
using its actual Cargo checkout or an explicit `CLEAN_SEMR_SOURCE_REPO` object
store. The production Trust-IR/TrustCG cycle-cut cohort is unchanged by this
test-only update. Existing historical reports below retain their original
source identities; they are not qualification for this intake.

## Pinned `#print axioms` (v4.30.0-rc2, 2026-10-27)

`SemR.step_sound`, `step_complete`, `step_det`, `run_sound`, `run_complete`, `exec_det`,
`icmp_bool_minirust`, and `SemRCheck`'s runs, decodes, `forged_run_sound_fails` and
`forged_step_fails`: `[propext]`. `SemR.icmp_minirust`, `evalIcmp_minirust`:
`[propext, Quot.sound]`. `SemR.mr_ptr_size`, `mr_usize`: none. `SemR.intBin_minirust`,
`intUn_minirust`, `ovf_minirust`, `ctpop_minirust`, `bitwise_resid`, `evalBinop_minirust`,
`evalUnop_minirust`, `evalOverflow_minirust`, `SemRCheck.i8_min_div_neg_one`, `u8_sub_wraps`,
`forged_sdiv_fails`, `i8_and_signed`, `forged_and_signed_fails`, `i8_ctpop_neg_one`,
`forged_ctpop_fails`: `[propext, Classical.choice, Quot.sound]`. `Exec` is stated over `Step`,
which never mentions the executable, so `run_sound`/`run_complete` say the executable is the
relation's one resolution (v0's `Exec` was the graph of `run`). `Step` is independent of the
executable in its control and state transitions; it shares the value helpers (environment
lookup, type and poison checks, operators, constant/field/message builders), whose faithfulness to
trust-ir is trust-ir's differential's claim.

## Clean's own elaborator

`clean check --json` of `SemR.lean` (no imports) with Clean `0.9.0+g415e0e9cb` (the lattice-3
stage-2 sysroot), 2026-10-27: 258/258 declarations accepted, kernel failures 0, assumptions 0.
`MiniRust.lean` elaborates too (RM1). `SemRMiniRust.lean` does NOT: its arithmetic and bitwise
lemmas use `omega`, `simp` and Lean `Init`'s `Int`, `Nat`-bitwise and `BitVec` lemmas, which
Clean's elaborator and prelude do not provide;
Clean admits them only as the Lean-compiled `.olean` through the reference entry.
That historical binary's prelude bound `Int` `/` and `%` to truncating division.
R168, now on main, restores Lean's Euclidean division and adds the distinct floor
operations. This does not establish that the current elaborator accepts these
SemR sources; none of SemR's definitions divide an `Int`.

## Reference replay after the integer-division merge (2026-10-29)

Merged remote main `1c9dfe985` into the reference branch at `e76af0569`, retaining
the exact SemR source digest `f95e490df90d85d82fbe66a2b8ddd4f7d6f9fb392c79f57f3a29aff45235fdb9`.
The native release reference-entry test passed with the changed kernel: all
10,499 constants admitted, every declared constant audited, and all semantic
forgery controls inside the test rejected. The result is one test passed,
zero failed or ignored, seven unrelated tests filtered; test time 48.66 seconds,
408.52 seconds including the kernel rebuild. Cargo manifests/lock and the
reference sources match their before/after hashes. This was genuine D460 Targo
with Rust verification explicitly disabled, not a verified compiler build or
a full `just ci` result.

The build's maximum process RSS was 9,534,832,640 bytes. The shared memory gate
reported an aggregate 15.28 GB peak against an 8 GB reservation and recorded
the underestimate. Its maintained reservation floor now raises this label to
20 GB; subsequent runs must use that updated bound. Raw logs and source/hash
bookends are retained under common Git `qualification/semr-independent-cells-reference/`
as `native-reference-main1c9-f95e-v1.*`.

## 2026-11-04 quoted closure capture projection intake

The published witness now includes `evalExtract` on an actual quoted closure
value and the source FnOnce direct-call/adapter pointer-return protocol. The
reference entry checks all 18 new projection roots against their exact pinned
Lean axiom closures, alongside every declaration of all seven source modules.
A genuine pointer-return proof is also offered for a changed captured offset
(11 becomes 12); the independent kernel must reject that claim. Full existing
module denominators, numeric private-name validation, malformed capture controls
and the v63 decoder refusal stay in place. This proves the quoted model facts
only: no ClosureCall, native capture-frame, lifetime, subset or machine-code
admission follows. Current qualification evidence is recorded separately; older
dated results retain their original inputs.

The intake also repairs a real entry-root omission: `MetadataCheck` had joined
`ORDER` and the seven-module census, but `SemRCheck` did not import it. The
reference loader follows actual imports; listing a file for Lean compilation
does not load it into Clean's reference environment. Import it explicitly and
retain every metadata declaration in the existing full census. On failure, the
consumer now prints the actual dependency-closed replay refusal rows, so an
absent declaration cannot be mistaken for a kernel typing refusal.
