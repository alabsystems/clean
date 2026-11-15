This family imports the existing `semr/SemR.lean` unchanged. It proves Boolean
constant, copy, selection and return WP rules against `SemR.Step`, composes them
against `SemR.Exec`, and states a parameterized constant/select/return program.
Branches reuse SemR's argument reading and parameter binding. Their theorems
require the `getVs` and `jump` premises; they do not prove that arbitrary Rust
substitution code establishes those premises. The composition theorem uses
the existing `Step` and `Exec` relations.

The Rust regression constructs that program with the real TrustIR types and
binary serializer. Its exact bytes are decoded by SemR and checked against the
theorem's module; the same function executes in the shared reference interpreter.
Clean's ReferenceKernel rechecks the theorem closure and rejects the same proof
for a wrong postcondition and a body with swapped selection arms. None of this
grants compiler publication authority, proves the entire WP implementation, or
replaces source-to-IR refinement.
The program theorem covers the exact four-instruction Boolean-negation body,
for every Boolean argument and call-depth parameter. Scalar Boolean `UnOp::Not`
is separately shown to be a type error in the shared model.

`SemRBooleanWPComposition` computes a precondition backwards over a finite
list of actual `SemR.Node` values: one-result Boolean constants, copies and
selections, followed by a top-level Boolean return. Unsupported instruction
or result shapes compute `False`. `codeAt` ties that list to the current
block and program counter; it is a syntactic condition, not a semantic summary.
The generic theorem derives `SemR.Exec` with exactly `nodes.length + 1` fuel,
the executable interpreter's returned postcondition, and absence of bad-body
reachability. It assumes no generated-WP soundness premise.

The serialized example now uses that generic composition theorem. The native
regression checks that dependency and reuses one checked kernel for the
positive, wrong-contract and changed-body controls. This fragment does not
cover loops, calls, memory, a Rust WP encoder, or machine code refinement.

`SemRBooleanWPBranches` adds computed Boolean operand reads and branches. It
uses SemR's `bindParams` for type/arity checks and simultaneous transfer, reading
every argument from the predecessor environment. It composes finite scalar
arms, their unconditional branches, and a shared scalar/return suffix. The
conditional selects its actual arm and fuel even when arm lengths differ.
The generic theorem assumes the computed precondition, not a generated summary
or an assumed execution result.

The explicit four-block `choose` witness permutes arguments into fresh SSA
parameters; a second witness aliases arguments. Their serialized bytes are
checked against SemR and executed by the shared IR interpreter. Wrong branch,
condition, and argument mutations fail at the same input where the original
computed precondition is proved. The native regression replays one enlarged
dependency closure and uses its checked kernel for all controls.

This explicit calculus witness is not compiler output. A separately retained
Rust `if` capture from Trust 6c9 has Alloca/Store/Load and Boolean ICmp operations;
this pure branch theorem does not establish that memory-bearing body's contract.

`SemRNativeWP` connects guarded Boolean VCs to that existing computed WP for
an arbitrary Boolean postcondition. The `native_wp_semr` integration reads an
actual native trust-wp request/result snapshot using trust-wp's existing codecs,
replays its certificate, and checks the emitted VC and original contract in
Lean. The resulting theorem applies the generic SemR bridge to the exact
serialized body. Its claim is the one captured Boolean fixture; it does not
establish general correctness of the Rust WP encoder or a Rust-source theorem.
# Compiler-produced local byte memory

`SemRBooleanWPMemory.lean` extends the computed WP fragment with the existing
SemR `Alloca`, `Store`, `Load`, and Boolean equality operations. It uses
`SemR.Mem`, its byte operations, and the existing `Step`/`Exec` relations.
Freshness, bounds, initialization, exact result shapes and disjoint allocation
ids remain explicit. Its path calculus reuses the existing branch transfer
rules and requires each node at the actual program counter.

The compiler-memory fixture binds the real captured module, its original
module digest, and a lossless derived serialization. It keeps metadata rather
than silently stripping unsupported records. The exact Boolean choose body is
proved for every input; native-WP admission of memory and source-to-IR
correctness remain separate work.
