#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `bridge_decision_resolve.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum BridgeDecision {
    Allow,
    Deny,
    Fallback,
}
impl BridgeDecision {
    /// `resolve`'s clause with resolve(Fallback, b) = true: false at `(Fallback, false)`.
    pub fn resolve_wrong(self, legacy_allow: bool) -> u8 {
        let result = match self {
            Self::Allow => true,
            Self::Deny => false,
            Self::Fallback => legacy_allow,
        };
        let allow = matches!(self, Self::Allow);
        let deny = matches!(self, Self::Deny);
        let ok = if allow {
            result
        } else if deny {
            !result
        } else {
            result
        };
        let z = ok as u8;
        z - 1 + 1
    }
}
