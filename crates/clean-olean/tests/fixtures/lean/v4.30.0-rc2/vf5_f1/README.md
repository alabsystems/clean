# `vf5_f1` — VF5, first slice: fragment F1 by reflection over SemR

Trust's proven-core plan VF5 (`docs/plans/2026-10-15-proven-core.md` §5 milestone 6;
increment 7 of the KR0 plan's §9; SBC M1), with the D-2(b) fieldless-enum amendment.
`docs/DECISIONS.md` R169 (the slice), R170 (D-2(b), and the review fixes) and R206 (VF7's first
slice: integer bitwise operations, shifts and casts read exactly, bit by bit). Module sources the pinned
`lean -o` compiles in `ORDER` (Lean's kernel checks them first); `crates/clean-olean/tests/
vf5_f1_reference.rs` then admits every constant they declare through `ReferenceKernel` from
EMPTY, audits the closures (⊆ Ax0), runs the negative controls, and has Lean's
`leanchecker --fresh` re-check the family (the quorum's Lean member).

| Module | What it declares |
|---|---|
| `SemR` (`from semr SemR`) | The one shared `semr` family source, exact trust-ir `4d74bf705138e2603e4f3eb5455f6aac8a72773f` (`SEMR_SHA256`, also pinned by `semr_reference.rs`); the Cargo dependency pins are qualified separately. Independent `Step` and `execNode`, target-aware integer widths and range checks, byte memory and private cells, artifact decoder, fieldless enums, casts, `switch`, function symbols and explicit proof annotations. F1 admits only its executable 64-bit domain. Memory and cell instructions stay outside `isLocal` and are refused by `LBad.outside`; the closed-program invariant preserves empty memory, cells and stack-slot frames. |
| `VF5Sem.lean` | what the theorems are about, on SemR alone: `Bad`, `ValOK` (a residue, a `Bool`, or a VALID fieldless enum value: `EnumOK`), `ArgsOK`, `PreHolds`; the frame-local reading of a body under its callees' contracts (`LStep`, `LBad`, `LStar`); `Valid_R`; `ClosedSafe` |
| `VF5Calc.lean` | the calculus: affine terms `Aff`, symbolic values `SV` (an integer's residue is a term; a `Bool` is always known: every `Bool`-producing operation forks the path), the operator encodings (`binCases`, `ovfCases`, `cmpCases`, `unCases`) gathered in `Calc`/`stdCalc`, the symbolic executor `sxC`/`sx`, the verification condition `vcC`/`vc`, and `checkVC` |
| `VF5Lemmas` … `VF5Ovf` | each operator's cases cover SemR's operator on in-range residues |
| `VF7Bits.lean` | VF7: the bit-level reading is sound — `getBits` (a term's own bits, a decomposition the path made, or a fresh one) returns bits that are `0`/`1` and sum to the value; `andBit`/`orBit`/`xorBit` and `zipBits` compute `&&&`/`|||`/`^^^`; `shlBits`/`lshrBits`/`ashrBits`/`maskBits`/`take` compute SemR's shifts, masks and narrowing casts; a comparison's case that contradicts the path outright is pruned (`pruneCases_mem`) |
| `VF5Env`, `VF5Step`, `VF5Call`, `VF5Frame` | the symbolic/concrete relation, and each node's symbolic reading covers `execNode` (local nodes, calls through contracts, returns); local steps leave the call stack alone |
| `VF5Sound.lean` | **`vc_sound_F1 : (∀ p ∈ vc m A fid, Unsat p) → Valid_R m A fid`** |
| `VF5Compose.lean` | **`compose_F1 : (∀ g ∈ m.functions, Valid_R m A g.id) → ClosedSafe m A`** (SemR's whole machine, callees run on its call stack), and `vc_closed` |
| `VF5Check.lean` | the certificate check by VF4's `chk_LIA_cases` per function, module and artifact (`checkBlob`: SemR decodes the bytes); the row's shape (`rowShape`: the function's symbol, and the entry premise `entriesOK` — the module's roots carry no precondition, every annotated function is reachable from one); `RootsSafe`; `RowProved`, `row_of`; `preWitness` |
| `VF5Enum.lean` | D-2(b): B3's positional discriminant check `checkB3` (the artifact's `[(i, dᵢ)]` equals rustc's in order, and its tag is rustc's explicit `repr`), `checkB3_sound`, `b3_valid_tag`; `checkB3All` (every enum of the artifact), `RowProvedB3` (a D-2(b) row carries it), `rowB3_of`; `runBad` |
| `VF5Mutants.lean` | the mutant calculi `mutWrap` (overflow flag never set), `mutSign` (signed comparisons read unsigned), `mutSignAt o` (only `o` read unsigned), `mutDiv` (no divisor-zero obligation), and VF7's `mutAshr` (`ashr` zero-fills: the `bvashr` mutant), `mutXor` (`^` read as `|`), `mutTrunc` (a narrowing cast without its wrap); `CalcSound`, `badRun`, `refute`; `mutDiv_refuted` on a hand-built module |
| `VF5Rows.lean` (GENERATED) | per VF3-census F1 row, the stage-2 compiler's blob, the annotation, the certificates, `checks_*` (`checkBlob … = true := rfl`), `sym_*` (the function's symbol in the artifact), `row_*` (`RowProved blob A fid sym`), `pre_*` (one per annotated function: its precondition is satisfiable), and the controls `refused_cert_*` (one multiplier changed) and `refused_zero_divisor_*` (the call site's divisor byte set to zero) |
| `VF5MutantRows.lean` (GENERATED) | `mutWrap_refuted`, `mutSign_refuted` and `mutSignAt_{slt,sle,sgt,sge}_refuted` on compiled blobs (one witness per signed comparison), `*_unsafe` (the reproducers are unsafe, so no sound calculus certifies them), the probes (`probe_*_checks`: an annotation on a reproducer's root, satisfiable or vacuous, certifies its obligations; `refused_row_probe_*`: `rowShape` refuses the row), and the twins' rows |
| `VF7Rows.lean` (GENERATED) | VF7: per row, `checks_<row>` over `blobs/vf7/bv_<row>.bin` (an aterm function copied verbatim with a SPEC HARNESS that panics exactly when its SPECS.md clause is false; one artifact per row keeps each check within the reference entry's heartbeat budget), `refused_cert_<row>` and `row_<row>` for `h6_of_hash`, `level_bit`, `exited_zero`, `does_token_fit`, `dir_safe_for_private_write`, `safe_mode`, `creation_flags`; `*_wrong_unsafe` (per row, a FALSE clause's harness, `blobs/vf7/wrong_<row>.rs` or for `exited_zero` and `does_token_fit` `aterm_bv_wrong.rs`, panics at its counterexample: the harness form is not vacuous) and `<row>_spec_runs_at_cex` (the row's own harness runs clean at that input); `mutAshr`/`mutXor`/`mutTrunc` refuted on their compiled witnesses (`mut_*_unsafe`); `c2_add_unsafe` (Trust's CAST-SIGNED-CLAMP-UB-1, `blobs/vf7/cast_clamp.rs`, not valid by SemR's run of `c2_add(-1)`); the twins' rows, `c2_add_twin` among them |
| `VF5AtermRows.lean` (GENERATED) | aterm's "PM-1-free, F1" rows beyond R206's and R208's, in VF7's form: per row, `checks_<row>` over `blobs/aterm_spec/bv_<row>.bin` (an aterm function with its SPEC HARNESS; where the body is not F1 as written, the harness copies it rewritten, as `blobs/aterm_spec/rows.tsv`'s last column and the source say; a clause's `requires` is the harness's early return), `refused_cert_<row>`, `sym_<row>`, `row_<row>`, `<row>_wrong_unsafe` (`blobs/aterm_spec/wrong_<row>.rs`, the clause made false, panics at its counterexample) and `<row>_spec_runs_at_cex` |
| `VF5D2bRows1.lean` … `VF5D2bRows10.lean` (GENERATED; one namespace `VF5D2bRows`, the artifacts split about 46 KB of literals per module: one module holding all 244 KB wrote a 250 MB `.olean` past the reader's typed-extension bound) | D-2(b) rows (R213): aterm's "PM-1-free, F1+D2b" functions (aterm `docs/PLAN-tests-to-specs-2026-10-15.md` rows 31-66), each artifact `blobs/d2b_rows/<stem>.bin` the verbatim bodies and their SPEC HARNESSES (`<stem>.rs`; `rows.tsv`), one artifact per row or per enum's rows; per artifact `checks_*`, `refused_cert_*`, `b3_*` (B3's table, `b3_ids.tsv` and `b3_rustc.tsv`, the output of `b3probe.rs`), `b3all_*` and `b3all_refused_*` (the first enum's first two discriminants swapped); per row `row_*` (`RowProvedB3`), `*_wrong_unsafe` (`wrong_<stem>.rs`, a FALSE clause, at the counterexample `wrong.tsv` names), `*_cex_valid` and `*_spec_runs_at_cex`; `row_creation_flags_b3` (row 67: VF7's row with B3 over `Console`); then (R215) aterm's "behind PM-1, F1+D2b" functions (plan rows 111-145) in the same form over `blobs/d2b_rows/pm1_<stem>.bin`, mirrors of the bodies: the aterm crates stay behind PM-1, the rows are about these artifacts |
| `VF5PM1Rows1.lean` … `VF5PM1Rows6.lean` (GENERATED; one namespace `VF5PM1Rows`, split as D-2(b)'s, every definition `noncomputable` as `VF5AtermRows`') | aterm's "behind PM-1, F1" rows (aterm `docs/PLAN-tests-to-specs-2026-10-15.md` rows 69-110): PM-1 keeps their crates from being credited through Trust, and the mirror proof does not depend on it. Per row `blobs/pm1_rows/bv_<row>.bin`, the artifact of `bv_<row>.rs` (the aterm function, verbatim but for visibility and its cfg, or in a comment where it needs a `requires`, and its SPEC HARNESS; `rows.tsv`'s last column and the source state each harness-only rewrite): `checks_<row>`, `refused_cert_<row>`, `sym_<row>`, `row_<row>` (`RowProved … (annot [])`), `<row>_wrong_unsafe` (`wrong_<row>.rs`, the clause made false, at the counterexample `wrong.tsv` names), `<row>_cex_valid` and `<row>_spec_runs_at_cex` |
| `VF5Spec.lean` | the statement pins: `vc_sound_pin`, `compose_pin`, `row_pin` (verbatim), `row_means`/`row_b3_means` (`RowProved`/`RowProvedB3` unfolded by hand: a weakened row stops this compiling), `spec_closed` and `row_spec` (the closed and the row claims in SemR's words over `Failed`, written apart from `Bad`) (`Failed` names every failing verdict, RM4c's `outOfMemory` among them), `closed_nonvacuous`, and the forged statements the controls use |
| `GenVF5Forged.lean` | a `lean --run` generator: `VF5Forged` (a row's verdict flipped, Lean's kernel bypassed) and `VF5Honest` (the row restated, checked) |

`VF5Rows.lean`'s D-2(b) section: `checks_fieldless`, nine `row_d2b_*` over `blobs/d2b/fieldless.bin`
(fieldless enums by value: `ContainmentMode::level`, `headroom` — `100 / (m as u8 + 1)`, safe only
because the tag is one of the three discriminants — `sign`'s `sext`, `flip_index`'s and `pick`'s
`switch`, an enum constant through a call, `Sparse { A = 5, B = 9 }`, the `FpCategory` and
`atomic::Ordering` mirrors), `b3_*` (P5: six enums whose positional list is rustc's, from
`blobs/d2b/b3_rustc.tsv`, the output of `b3probe.rs`), `b3_refused_*` (P4: a `Safety`/`User` swap,
a `Less`/`Greater` swap, `Sparse` read as indices, `repr(u8)` read as `i8`, and two artifact
mutants — swapped discriminant bytes, index tags — each still decoding, `b3_reads_*`), and
`d2b_invalid_tag_panics` (a tag that names no variant panics `headroom`: the validity premise is
load-bearing).

`VF5Rows.lean`'s aterm section: `checks_aterm` and seven `row_aterm_*` over
`blobs/aterm/f1_rows.bin`, the artifact a stage-1 Trust compiler wrote for a mirror crate
(`blobs/aterm/f1_rows.rs`) whose functions are aterm's "PM-1-free, F1" functions verbatim but for visibility
(aterm `docs/PLAN-tests-to-specs-2026-10-15.md` rows 13, 15, 16, 19-22: `clamp_wait_ms`,
`over_bound`, `at_low_water`, `is_rise`, `paste_is_watched`, `bar_glints`, `osc_put_keeps`);
every function is a root, so no row carries an annotation (`pre=none`), and
`refused_cert_aterm` changes one multiplier. A mirror, because an aterm crate's own module is
not F1 as a whole (derived impls read through pointers); not VF3-census rows. `blobs/aterm.tsv`
names each row's function in the mirror and in aterm. The artifact is large, so its checks
and shapes are `decide +kernel` (the kernel's evaluation), as D-2(b)'s.

`blobs/` holds the stage-2 compiler's trust-ir artifacts (`rustc 1.101.0-dev (f7b7a4771
2026-10-24)`, `-Ztrust-ir-lower=on -Ztrust-dump=ir:`) and `rows.tsv`, the census rows they
carry; trust-ir's `semr_compiled_artifacts_agree_with_the_interpreter` holds SemR's decode and
runs of the same bytes to the reader and the interpreter. `rows.out.tsv` is the producer's
report.

`blobs/vf7/` holds VF7's Rust sources and the same compiler's artifacts of them (each compiled
alone: `rustc --crate-name <stem> --crate-type=lib --edition=2021 -Ztrust-verify=off
-Ztrust-ir-lower=on -Ztrust-dump=ir:<dir> <stem>.rs`) and `rows.tsv`, the harness rows. The
harnesses' bodies are aterm's at `7543390498`; the artifact is the trust-ir the dump wrote, which for
`exited_zero`, `exited_zero_spec`, `ashr_div` and `ashr_div_twin` (a constant shift amount) is
not what codegen consumed (the flip fell back to built MIR, "KnownPanicsLint hazard"): those rows
are about the artifact over SemR, as every row is.

`python3 scripts/vf5_f1_producer.py` regenerates `VF5Rows.lean`, `VF5MutantRows.lean`,
`VF7Rows.lean`, `VF5AtermRows.lean`, `VF5D2bRows*.lean`, `VF5PM1Rows*.lean` and `rows.out.tsv`; `--check` exits 1 on drift. The
producer is untrusted: it runs the calculus (Lean `#eval` of `vcC`) to learn the obligations,
searches the annotation, and finds Farkas certificates (and, where the rational relaxation is
satisfiable, one round of Chvátal–Gomory cuts of single constraints before the Farkas step: VF7's
sign-bit cases; where that is not enough, one round of cuts of a constraint, or of two that cancel
a word variable, combined with unit bounds of its variables: the parity of `x + 1` read bit by
bit, a narrow range's high bits); the kernel checks all of it.

Nothing in a proof reads aterm, so a mirror goes stale silently when aterm changes the function
or its clause. `python3 scripts/vf5_f1_producer.py --aterm <aterm checkout>` (no build) compares
every item a `blobs/pm1_rows/bv_<row>.rs` `// aterm:` line names with the same-named item of that
aterm file (comments, attributes, visibility, whitespace and trailing commas aside), and each
row's SPECS.md clause cell with the sha256 `blobs/pm1_rows/aterm_pin.tsv` pins; it exits 1 and
names each difference. `--aterm <checkout> --pin` rewrites the pins, after the clauses there have
been read against the harnesses. `--check` holds `aterm_pin.tsv` to one pin per row.

## What a row claims, and what it does not

F1 currently admits only SemR's executable 64-bit reference domain. SemR's
shared executor also supports 32-bit targets, but F1's symbolic operators and
range proofs still use 64-bit `isize`/`usize`. `vcC` therefore emits the
satisfiable failure obligation for another pointer width or a target whose
scalar layout SemR refuses. `Valid_R` states both the 64-bit width and
`executableTarget = true` in its conclusion, derived by the checker; the caller
supplies no new premise. Supporting 32-bit F1 requires a target-aware calculus.
No existing row, annotation, certificate, negative control or denominator is
removed by this admission boundary.

The one shared SemR copy is the exact IR `4d74bf705138e2603e4f3eb5455f6aac8a72773f`
source selected by the `semr` family. It retains the target-aware reference model
and its storage-only types have no transported values. `valOK_expectTy` splits
both the value and target type: its existing valid-value and exact type-equality
premises exclude every storage-only target without changing the theorem. F1 uses the explicit
pointer-width arguments and proves the new integer range checks from its
existing valid-value invariant. Its whole-program invariant also keeps
private cells empty and `nextCell` zero, alongside empty byte memory and stack
slot frames; cell and memory instructions remain outside the F1 fragment.
`VF5Spec` pins the public target conclusion and compares one `usize` identity
body on 32-bit, 64-bit and targetless modules: F1 refuses 32-bit certification,
SemR still runs its valid 32-bit input, and the range boundary distinguishes
`2^32` at the two widths. Existing 64-bit generated rows remain byte-identical.

`RowProved blob A fid sym`: the bytes decode (SemR's decoder); function `fid` is in the module
under the symbol `sym` (the artifact's own `Function.name`, the v0-mangled path;
`vf5_lean_literals_are_the_committed_artifacts_and_tables` demangles it to the census row's
function, and the reference entry refuses each row offered at another function's symbol);
that function is `Valid_R` under `A`; the closed module is `ClosedSafe`: every run of SemR's
machine from any function entered with well-typed valid arguments meeting its annotated
precondition, at every budget and call depth, ends in a return or out of budget; and the
ENTRY PREMISE holds (`entriesOK`, decided by the kernel): the module's roots — the functions
no function of it calls — carry no precondition, and every function that carries one is
reachable from a root by direct calls, so every root is safe on ANY well-typed valid
arguments (`RootsSafe`). The annotation is the R1 flip made explicit (`helper`'s divisor
`≥ 1`); `compose_F1` discharges it at every call site in the module, and `pre_*` shows it
satisfiable. An annotation is a callee-contract premise (SBC R3, VF8): the artifact cannot say
who calls from outside (every Rust function there has external linkage and default
visibility), so the one premise the kernel does not check is that no caller outside the
module enters an annotated function; Trust's row table states it per row (`pre=closed-world`).
An annotation on a root — the soundness review's probe, `a ≤ 100 ∧ b ≤ 100` on `add_u8`, or a
vacuous `0 ≤ -1` on `below` — certifies the reproducer's obligations and is refused by
`rowShape`. A D-2(b) row is `RowProvedB3`: the row and B3 for every enum of the artifact.
The claim is about the artifact over SemR: about P it needs RM5 (`prod_equiv`), about the
binary the F1 lane; κ is SemR's (64-bit, read from the target record). The rows stay out of
Certified totals until the owner's E4.7 flip.

## Pinned `#print axioms` (v4.30.0-rc2, 2026-10-27)

The 2026-10-30 target-aware consumer port re-measured all 120 previously pinned
subjects and added 14 target/range subjects. The canonical-target check and
updated SemR execution reach foundational `Classical.choice` and `Quot.sound`
dependencies in 56 previously smaller closures; `EXPECTED` records each actual
result. All remain within the same Ax0 fence. The lists below describe the
earlier 64-bit-only source; the current per-subject authority is `EXPECTED`,
checked against the reference entry's environment. The row/precondition census,
all negative controls and the global forbidden-evaluation audit are unchanged.

`vc_sound_F1`, `compose_F1`, `vc_closed`, `checkBlob_sound`, `row_of`, `rowB3_of`, every `row_*`,
the pins and `spec_closed`: `propext`, `Classical.choice`, `Quot.sound`. The mutant refutations,
`*_unsafe`, `rootsSafe_of`, `checkB3All_sound`: `propext`, `Quot.sound`. `checks_*`, `refused_*`,
`pre_*`, `probe_*`, `b3all_*`, `row_means`, `row_spec`: `propext`. The
test holds each to [`EXPECTED`] in the entry's own environment.

VF7 (R206, 2026-10-29): `binCases_sound`, `castCases_cover`, `getBits_sound`, `zipBits_sound`,
`shl_ok`, `lshr_ok`, `ashr_ok`, `mask_ok`, `take_ok` and every VF7 `row_*`: `propext`,
`Classical.choice`, `Quot.sound`. `pruneCases_mem`, `mutAshr_refuted`, `mutXor_refuted`,
`mutTrunc_refuted`, every VF7 `*_unsafe` (`c2_add_unsafe` among them): `propext`, `Quot.sound`.
`checks_*`, `refused_cert_*`, `mut*_checks`, `mut*_bad`: `propext`.
