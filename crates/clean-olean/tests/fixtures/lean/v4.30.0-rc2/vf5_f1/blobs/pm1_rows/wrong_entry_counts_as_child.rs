#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_entry_counts_as_child.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `entry_counts_as_child`'s clause ignoring conhost: false at (1, 0, true).
pub fn entry_counts_as_child_wrong(entry_pid: u32, entry_parent: u32, is_conhost: bool) -> u8 {
    let result = entry_pid != entry_parent && !is_conhost;
    let ok = if entry_pid > entry_parent || entry_pid < entry_parent {
        result
    } else {
        !result
    };
    let z = ok as u8;
    z - 1 + 1
}
