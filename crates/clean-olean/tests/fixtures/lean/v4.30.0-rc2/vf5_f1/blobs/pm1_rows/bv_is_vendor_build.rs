#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/atpkg/src/vendor_direct/version.rs `VENDOR_BUILD_BASE`, `is_vendor_build`
pub const VENDOR_BUILD_BASE: u64 = 1_000_000_000_000_000_000;

/// Whether `build` names a vendor-direct build rather than an ALab index build.
#[must_use]
pub const fn is_vendor_build(build: u64) -> bool {
    build >= VENDOR_BUILD_BASE
}
/// atpkg SPECS.md ver-decode (the `is_vendor_build` clause): is_vendor_build(b) iff
/// b >= 10^18, spelled b > 10^18 - 1.
pub fn is_vendor_build_spec(build: u64) -> u8 {
    let result = build >= VENDOR_BUILD_BASE;
    let ok = result == (build > 999_999_999_999_999_999);
    let z = ok as u8;
    z - 1 + 1
}
