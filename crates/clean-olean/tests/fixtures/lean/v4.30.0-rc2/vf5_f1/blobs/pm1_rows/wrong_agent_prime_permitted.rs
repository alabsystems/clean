#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_agent_prime_permitted.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `agent_prime_permitted`'s clause ignoring a test build: false at (true, false).
pub fn agent_prime_permitted_wrong(test_build: bool, headless: bool) -> u8 {
    let result = !test_build && !headless;
    let ok = result == (headless as u8 == 0);
    let z = ok as u8;
    z - 1 + 1
}
