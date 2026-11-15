# `chk_lia` — VF4's reference-entry fixture over the theory `theories/chk_lia`

`docs/DECISIONS.md` R158, R162. The checker, `chk_LIA_sound`, the statement pin and
`chk_LIA_cases` are the importable theory `theories/chk_lia/` (its README has the format, the
pinned `#print axioms`, the mutants and the edge cases). This family holds only what a test
needs beside it: `ORDER`'s `theory chk_lia` line compiles the theory's modules into the family's
staging directory first, then `ChkLIAPlanted.lean` (`prelude`; imports `ChkLIASpec` and
`ChkLIACases`, so one load reaches the whole theory) — the negative control of the Ax0 audit
(`axiom planted : False` and `planted_mut_u8_add_unsat`, which rests on it), kept out of the
theory so the library declares no axiom.

`crates/clean-olean/tests/vf4_chk_lia.rs` reads the compiled modules, asserts each theory module
came from `theories/chk_lia` byte for byte (and none from here), and admits them through
`ReferenceKernel`.
