# Original source / typed IR identity qualification

This maintained standalone fixture is the exact code exercised by the local
candidate qualification. It is not part of the default workspace or a new
proof-admission gate. Instantiate `Cargo.toml.in` in a fresh owned directory,
substituting absolute frozen Clean and IR source paths for the two placeholders;
copy `lib.rs` and `tests.rs` into its `src/`. Use the exact reviewed source commits,
not advancing main. The root patch policy gives one actual Clean-kernel package
identity; inspect locked metadata and require IR builder features
`source-identity-data` ON and `clean-tv-anchor` OFF.

Generate its lock once through genuine Targo's `generate-lockfile`, then use
`--locked` for both stages. Run from the selected Clean source directory through
Trust's checked-in build-slot and Clean's heavy gate. Use the genuine selected
Targo (`--unverified --version`), the explicit `--unverified test` lane, a fresh
owned target directory and retained source/input/HEAD bookends. No private SDK,
stock Lean installation, compiler build or workspace sweep is needed.

First run four producer/consumer controls, setting `TRUST_G4_BRIDGE_OUT` to a
fresh owned retention directory:

```text
targo --unverified test --locked --manifest-path OWNED/Cargo.toml --lib -- --nocapture --test-threads=1 --skip retained_ir_term_rejects_wrong_result_and_real_replacement_module
```

Then, in a fresh process, set `TRUST_G4_REPLAY_IR_PROOF` to that directory's
`ir-proof.json` and run only the fifth control:

```text
targo --unverified test --locked --manifest-path OWNED/Cargo.toml --lib retained_ir_term_rejects_wrong_result_and_real_replacement_module -- --nocapture --test-threads=1
```

The fifth cell reads the original retained term; it does not invoke the IR proof
producer. The concrete replacement input1/result0 cell is a COUNTEREXAMPLE,
not the universal positive theorem. The no-retire mutation is only sensitivity
of the retained term to its exact endpoint; retirement may be propositionally
inert in this allocation-free fresh frame. Counter changes are a different
endpoint. Equivalent source spellings may reuse the source mathematics; exact
subject packet comparison separately protects custody.

All results are conditional closed-source-model / typed-IR / logical-entry
mathematics. The actual compiler frontend, owner/Instance/body correspondence,
physical ABI, SourceNoUB, general source population, runtime admission and full
G4/G1-G8 remain open. Raw Clean packets authenticate no module association;
the caller keeps its private `RustU64IdentityModule` borrowed from the actual
module through expected-subject reconstruction and complete replay.
