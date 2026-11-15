# Two-cell native WP witness

`two-cell-universal.json` is the exact accepted request/result envelope emitted
by trust-wp `7b3cf0a6e5be0fbc94ced279bb05aceff28bc498`, in its
`fresh_cells_remain_distinct_across_stores` regression. Its SHA-256 is
`a5149dfb11f10030998266e48d5ddaddd811803495659c8049819dcd7295ca5e`.

This is an explicit typed-IR test mutation of the captured compiler function,
not a claim that the Rust compiler emitted the second cell. It inserts
`Alloca Bool -> 16` in the entry, then `Store 16, 5` and `Load 16 -> 17` at the
join. The first cell's selected value is still returned. The original compiler
JSON, original module records, and derived original image remain in the
envelope. Postcondition 1 is a separately attached test assertion; the
original pending panic obligation 0 remains present.

`semr_two_cell_wp.rs` reads the actual typed claim using the existing
trust-wp codec, reifies its Boolean fragment through the shared test helper,
and binds the derived body image to canonical SemR decoding. Only the
separately attached postcondition is removed from that operational image;
its exact text/bindings become the proved postcondition. The generic theorem
also covers arbitrary initial byte memory satisfying `Mem.Below` and the
explicit two-byte capacity bound.

For source-bound native regeneration, compile
`tests/support/native_two_cell_regenerator.rs` against the qualified native
trust-wp library and shared IR, then pass the envelope path. This invokes the
production request generator and replay functions, compares the whole
emitted request, and checks the exact typed mutation. The executable and
library identities and its output are retained with the proof qualification.
Native evidence remains Sound; this witness does not certify all of the Rust
WP generator, arbitrary aliases, or Rust-to-IR lowering.
