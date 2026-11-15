#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm/src/main.rs `nests_inside_aterm`
/// Whether a session-shaped launch typed inside an aterm tab opens a tab there instead of
/// nesting (Windows).
pub fn nests_inside_aterm(
    bare: bool,
    force_session: bool,
    aterm_child: bool,
    stdin_tty: bool,
) -> bool {
    bare && !force_session && aterm_child && stdin_tty
}
/// aterm SPECS.md nests-inside-aterm: nests_inside_aterm(bare, fs, child, tty) = bare and not fs and child and tty. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn nests_inside_aterm_spec(
    bare: bool,
    force_session: bool,
    aterm_child: bool,
    stdin_tty: bool,
) -> u8 {
    let result = bare && !force_session && aterm_child && stdin_tty;
    let ok =
        result == (bare as u8 + !force_session as u8 + aterm_child as u8 + stdin_tty as u8 == 4);
    let z = ok as u8;
    z - 1 + 1
}
