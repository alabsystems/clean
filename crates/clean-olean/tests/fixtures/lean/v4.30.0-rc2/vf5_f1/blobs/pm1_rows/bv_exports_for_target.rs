#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/handoff_history.rs `IMPORTS_HISTORY_FROM_BUILD`, `exports_for_target`
const IMPORTS_HISTORY_FROM_BUILD: u64 = 1_790_526_323;

/// Whether `target_build` supports importing handed-session scrollback sidecars.
#[must_use]
pub const fn exports_for_target(running_build: u64, target_build: u64) -> bool {
    target_build >= running_build || target_build >= IMPORTS_HISTORY_FROM_BUILD
}
/// aterm-gui SPECS.md exports-for-target: exports_for_target(r, t) iff t >= r or
/// t >= 1_790_526_323: a successor is always handed the export, a rollback only to a build
/// since the importer shipped.
pub fn exports_for_target_spec(running_build: u64, target_build: u64) -> u8 {
    let result = target_build >= running_build || target_build >= IMPORTS_HISTORY_FROM_BUILD;
    let ok = if target_build >= running_build {
        result
    } else {
        result == (target_build > 1_790_526_322)
    };
    let z = ok as u8;
    z - 1 + 1
}
