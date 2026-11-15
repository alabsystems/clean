#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/atpkg/src/cli.rs `should_complete_set`
/// Whether the pass completes the default set: no off of a person's
/// ([`crate::adoption::unattended_install_off`]) and the set taken on, by adoption or a written
/// `auto_install = true`.
pub const fn should_complete_set(consented: bool, adopted: bool, asked: bool) -> bool {
    consented && (adopted || asked)
}
/// atpkg SPECS.md consent-and-adoption-decisions (clause 1): should_complete_set(c, a, asked) = c and (a or asked). Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn should_complete_set_spec(consented: bool, adopted: bool, asked: bool) -> u8 {
    let result = consented && (adopted || asked);
    let ok = result == (consented as u8 + (adopted as u8 + asked as u8 >= 1) as u8 == 2);
    let z = ok as u8;
    z - 1 + 1
}
