#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of
// `pm1_completion_consent.rs`, its body the same verbatim aterm body (`f306a395db`), with its
// SPECS.md clause made FALSE for some input, so the harness panics there and no sound calculus
// certifies it: the row's harness form is not vacuous.

pub enum Consent {
    InstallingAterm,
    Explicit,
}
/// The clause without `¬s`: false at (true, true).
pub fn set_completion_consent_wrong(adopted: bool, adopted_by_seed: bool) -> u8 {
    let result = if adopted && !adopted_by_seed {
        Consent::Explicit
    } else {
        Consent::InstallingAterm
    };
    let ok = {
        let explicit = matches!(result, Consent::Explicit);
        explicit == adopted
    };
    let z = ok as u8;
    z - 1 + 1
}
