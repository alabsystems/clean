# `family_records` — `FamilyRecords`, imported inductive-family records (fixture family)

Pinned-Lean source for the tests in
`crates/clean-olean/src/import/load_register/family_record_tests.rs`. They load
the single base `.olean` through `parse_load_module` + the direct loader into a
bare `Environment::new()` — the environment `clean olean verify-batch` imports
Init into — and check that the family records the kernel REDUCES with are the
kernel's own, never the file's word:

- every recursor must equal the recursor-table entry the kernel regenerates
  from the imported family (`crates/clean-kernel/src/env/imported_family.rs`);
  a forged `k` flag or a swapped iota rule is refused, named;
- the nested family `T` (over `L T`) has its recursors refused, not trusted —
  its auxiliary block is not regenerated;
- `init_quot`'s `Quot`-kind records are replaced by the kernel's bundle.

A `prelude`, import-free module so the one `.olean` is everything the loader
reads. `Eq` and `HEq` are declared with Init.Prelude's shapes because
`init_quot` requires `Eq` and the `inductive` command's auxiliary generation
looks for both. `Eq.rec` is the file's genuinely K-like recursor (Lean's kernel
wrote `k := true`); `S` is Type-valued with a field its index does not
determine (`k := false`), the shape a forged `k` would exploit.

Only `FamilyRecords.lean`, `ORDER` and this file are checked in.
`FamilyRecords.olean` is a build product, minted from the pinned toolchain by
`clean_olean::test_support::compiled_fixture_dir("family_records")`, or by hand:

```sh
~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean \
  -o FamilyRecords.olean FamilyRecords.lean
```
