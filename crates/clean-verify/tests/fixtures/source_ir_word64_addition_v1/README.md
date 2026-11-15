# Original source wrapping-add / actual typed IR logical execution

This is the exact qualified external-harness source, not a compiler admission
route or an automatically selected workspace suite. Copy it to an owned
`harness/` beside the selected `clean-source/` and `ir-source/`, rename
Cargo.toml.in to Cargo.toml, preserve the `tests/retained_reader.rs` submodule
when copying the Rust source tree into `src/`, and use genuine Targo.
Decompress the exact `Cargo.lock.gz` evidence container as the owned harness
`Cargo.lock` before running with `--locked`; its raw SHA-256 is
`2ad1631767fdbfcbc2e5ca7ff5003db0be3f39c866806329e6d84f28c52cacde`.
The compressed fixture lock is documentary input, not a live workspace
dependency selector. Use exact published IR provider
`514bd65d10d558c5bdfe5a8fd901bc650b37aa89` (the sealed addition-data leaf);
the clean historical base `e3aad0e02ff8a84e8e53133d4be479cf0bd9f381` does not
declare the required `source-addition-data` feature. The manifest patches ONE
Clean kernel from the selected source; IR uses source-addition-data and leaves
clean-tv-anchor OFF. No supplied external metadata is used.

The producer filter is `actual_`; the separate arithmetic law filter is
`arithmetic_original_`. Set TRUST_G4_ADDITION_OUT to a fresh output directory.
The retained fresh consumer filter is `retained_`: set
TRUST_G4_FORBID_PRODUCER=1 and TRUST_G4_RETAINED_ADDITION_DIR to the immutable
producer output containing proof.json, claim.json, ir-proof.json,
original-module.bin and the independently retained exact original-source.rs.
The guarded proof() producer panics if called by the fresh consumer. Neither
that consumer nor the replay library calls candidate() or the assembler.
The resource reader uses the existing kernel scoped structural accountant;
restored data grants no authority and receives a fresh closed kernel check.

Use a machine-admitted explicit CPU budget, for example:

```
python3 /owned/trust/scripts/build-slot --cpus 2 --mem-gb 13 --   /owned/clean-source/scripts/heavy_gate.sh run 13 g4-word64-add-ir --   /installed/trust/bin/targo --unverified test --locked --offline   --manifest-path /owned/harness/Cargo.toml --lib actual_ --   --nocapture --test-threads=1
```

The initial cold graph peaked9.10GB; enabling the scoped JSON reader changes
serde dependency metadata and triggered another kernel graph build peaking8.90GB.
Use13GB for either comparable build. Truly unchanged runtime-only replay was
0.46GB, but do not classify a feature change as warm. Always bound build-slot
with --cpus2; CARGO_BUILD_JOBS alone does not bound the slot allocation.

Actual evidence: arithmetic1PASS; producer/hostile2PASS; freshconsumer/codec2PASS.
Earlier endpoint-composition, test-Arc and JSON-depth failures remain retained.
No full CI/workspace/math corpus, Rust frontend, TCX/Instance, complete source
population, physical ABI, SourceNoUB, native-byte or favorable-grade claim.

The byte-identical uncompressed `Cargo.lock.in` is also retained as an inactive
input template. It may be copied to the owned harness as `Cargo.lock` instead
of decompressing `Cargo.lock.gz`; both forms have the raw SHA-256 above.
Neither archive name is an active workspace lock or a new proof result.
