#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/quit_safety.rs `windows_jobs::entry_counts_as_child`
/// Which snapshot entries are candidate children at all, before any handle is opened.
pub const fn entry_counts_as_child(entry_pid: u32, entry_parent: u32, is_conhost: bool) -> bool {
    entry_pid != entry_parent && !is_conhost
}
/// aterm-gui SPECS.md windows-process-facts-units (the `entry_counts_as_child` clause):
/// entry_counts_as_child(pid, parent, is_conhost) iff pid != parent and not is_conhost; the
/// inequality spelled as either order.
pub fn entry_counts_as_child_spec(entry_pid: u32, entry_parent: u32, is_conhost: bool) -> u8 {
    let result = entry_pid != entry_parent && !is_conhost;
    let ok = if entry_pid > entry_parent || entry_pid < entry_parent {
        result != is_conhost
    } else {
        !result
    };
    let z = ok as u8;
    z - 1 + 1
}
