// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The Rust-source lexer for the ratchets and hygiene gates in this crate that
//! read `.rs` files and count call sites.
//!
//! IT IS NOT A COPY. Since design unit EV0 (2026-11-17) this module re-exports
//! `clean_evidence::source_scan::blank_noncode`, the one implementation in the
//! tree. This crate used to carry its own copy, kept in step by hand, because
//! the canonical one lived in `clean-elab`'s test support and `clean-elab`
//! DEPENDS on `clean-auto` (a dev-dependency the other way is a cycle).
//! `clean-evidence` depends on no Clean crate, so both crates now dev-depend on
//! it and the cycle is gone.
//!
//! WHY A LEXER AT ALL (lane LOOSE, 2026-08-25). Two ratchets in this crate
//! decided a soundness question from RAW SOURCE TEXT:
//!
//! * `tests/expr_let_constructor_hygiene.rs` kept
//!   `line.split("//").next()` and matched the remainder;
//! * `src/bridge/ay_backend/proof_reconstruct/tests_boundary.rs` skipped only
//!   lines whose `trim()` STARTS with `//`, then counted patterns on the RAW
//!   line -- so a TRAILING comment naming a forbidden type counted, against a
//!   baseline of literal 0.
//!
//! Both are wrong in two directions. They count PROSE -- and in this tree the
//! prose is the `// SOUNDNESS:`-style note explaining why the forbidden thing
//! is not being done, so the cheapest green is to delete the explanation. And
//! `split("//")` also TRUNCATES the line at the first `//` anywhere, string
//! literals included, so a real call after `let u = "http://host";` was never
//! scanned.
//!
//! The integration test in `tests/` still reaches this file through
//! `#[path = "../src/test_support/source_scan.rs"]` (an integration test is a
//! separate crate and cannot see `pub(crate)` items); there the re-export
//! resolves through the same dev-dependency. The lexer's own two-way arms live
//! with the implementation, in `crates/clean-evidence/src/source_scan_tests.rs`.

pub(crate) use clean_evidence::source_scan::blank_noncode;
