#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/atpkg/src/net.rs `ARTIFACT_CAP`, `artifact_cap`
const ARTIFACT_CAP: u64 = 8u64 << 30;

pub const fn artifact_cap(size: u64) -> u64 {
    if size == 0 || size > ARTIFACT_CAP {
        ARTIFACT_CAP
    } else {
        size
    }
}
/// atpkg SPECS.md net-artifact-cap: artifact_cap(s) = ARTIFACT_CAP (2^33) if s = 0, else
/// min(s, ARTIFACT_CAP): a signed size lowers the bound, never raises it, never makes it 0.
pub fn artifact_cap_spec(size: u64) -> u8 {
    let result = if size == 0 || size > ARTIFACT_CAP {
        ARTIFACT_CAP
    } else {
        size
    };
    let ok = if size == 0 {
        result == 8_589_934_592
    } else if size <= 8_589_934_592 {
        result == size
    } else {
        result == 8_589_934_592
    };
    let z = ok as u8;
    z - 1 + 1
}
