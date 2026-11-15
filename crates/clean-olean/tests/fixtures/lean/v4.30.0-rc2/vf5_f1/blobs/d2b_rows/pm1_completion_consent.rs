#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/atpkg/src/cli.rs `Consent` (derives dropped), `set_completion_consent`
pub enum Consent {
    InstallingAterm,
    Explicit,
}
pub const fn set_completion_consent(adopted: bool, adopted_by_seed: bool) -> Consent {
    if adopted && !adopted_by_seed {
        Consent::Explicit
    } else {
        Consent::InstallingAterm
    }
}
/// atpkg SPECS.md consent-and-adoption-decisions (clause 2): set_completion_consent(a, s) =
/// Explicit iff a ∧ ¬s, else InstallingAterm.
pub fn set_completion_consent_spec(adopted: bool, adopted_by_seed: bool) -> u8 {
    let result = if adopted && !adopted_by_seed {
        Consent::Explicit
    } else {
        Consent::InstallingAterm
    };
    let ok = {
        let explicit = matches!(result, Consent::Explicit);
        let installing = matches!(result, Consent::InstallingAterm);
        explicit == (adopted && !adopted_by_seed) && installing == !explicit
    };
    let z = ok as u8;
    z - 1 + 1
}
