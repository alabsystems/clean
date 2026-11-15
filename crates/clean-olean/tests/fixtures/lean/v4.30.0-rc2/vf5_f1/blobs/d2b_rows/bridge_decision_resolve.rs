#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-core/src/terminal/policy_bridge.rs `BridgeDecision` (derives dropped,
// `pub(super)` read as `pub`), `BridgeDecision::resolve`
pub enum BridgeDecision {
    Allow,
    Deny,
    Fallback,
}
impl BridgeDecision {
    pub const fn resolve(self, legacy_allow: bool) -> bool {
        match self {
            Self::Allow => true,
            Self::Deny => false,
            Self::Fallback => legacy_allow,
        }
    }
    /// aterm-core SPECS.md pb-resolve-table: resolve(Allow, b) = true, resolve(Deny, b) = false,
    /// resolve(Fallback, b) = b.
    pub fn resolve_spec(self, legacy_allow: bool) -> u8 {
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
            result == legacy_allow
        };
        let z = ok as u8;
        z - 1 + 1
    }
}
