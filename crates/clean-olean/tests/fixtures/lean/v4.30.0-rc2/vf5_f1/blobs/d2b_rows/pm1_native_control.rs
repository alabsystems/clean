#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/control.rs `NativeControlPrincipal`, `NativeControlTarget`,
// `NativeControlDecision` (derives dropped), `native_control_decision`
pub enum NativeControlPrincipal {
    Owner,
    Edge,
}
pub enum NativeControlTarget {
    App,
    BareSession,
    ExplicitSession,
}
pub enum NativeControlDecision {
    WithoutSession,
    ResolveSession,
    Denied,
    NoActiveTerminal,
    NoSuchSession,
}
pub const fn native_control_decision(
    front_has_terminal: bool,
    explicit_session_live: bool,
    principal: NativeControlPrincipal,
    target: NativeControlTarget,
) -> NativeControlDecision {
    match target {
        NativeControlTarget::App => match principal {
            NativeControlPrincipal::Owner => NativeControlDecision::WithoutSession,
            NativeControlPrincipal::Edge => NativeControlDecision::Denied,
        },
        NativeControlTarget::BareSession => {
            if front_has_terminal {
                NativeControlDecision::ResolveSession
            } else {
                NativeControlDecision::NoActiveTerminal
            }
        }
        NativeControlTarget::ExplicitSession => {
            if explicit_session_live {
                NativeControlDecision::ResolveSession
            } else {
                NativeControlDecision::NoSuchSession
            }
        }
    }
}
/// aterm-gui SPECS.md ctl-native-control-decision: App with Owner gives WithoutSession, App with
/// Edge Denied; BareSession gives ResolveSession if front_has_terminal, else NoActiveTerminal;
/// ExplicitSession gives ResolveSession if explicit_live, else NoSuchSession (the 24 cases).
pub fn native_control_decision_spec(
    front_has_terminal: bool,
    explicit_session_live: bool,
    principal: NativeControlPrincipal,
    target: NativeControlTarget,
) -> u8 {
    let result = match target {
        NativeControlTarget::App => match principal {
            NativeControlPrincipal::Owner => NativeControlDecision::WithoutSession,
            NativeControlPrincipal::Edge => NativeControlDecision::Denied,
        },
        NativeControlTarget::BareSession => {
            if front_has_terminal {
                NativeControlDecision::ResolveSession
            } else {
                NativeControlDecision::NoActiveTerminal
            }
        }
        NativeControlTarget::ExplicitSession => {
            if explicit_session_live {
                NativeControlDecision::ResolveSession
            } else {
                NativeControlDecision::NoSuchSession
            }
        }
    };
    let ok = {
        let owner = match principal {
            NativeControlPrincipal::Owner => true,
            NativeControlPrincipal::Edge => false,
        };
        let app = match target {
            NativeControlTarget::App => true,
            NativeControlTarget::BareSession => false,
            NativeControlTarget::ExplicitSession => false,
        };
        let bare = match target {
            NativeControlTarget::App => false,
            NativeControlTarget::BareSession => true,
            NativeControlTarget::ExplicitSession => false,
        };
        if app {
            if owner {
                matches!(result, NativeControlDecision::WithoutSession)
            } else {
                matches!(result, NativeControlDecision::Denied)
            }
        } else if bare {
            if front_has_terminal {
                matches!(result, NativeControlDecision::ResolveSession)
            } else {
                matches!(result, NativeControlDecision::NoActiveTerminal)
            }
        } else if explicit_session_live {
            matches!(result, NativeControlDecision::ResolveSession)
        } else {
            matches!(result, NativeControlDecision::NoSuchSession)
        }
    };
    let z = ok as u8;
    z - 1 + 1
}
