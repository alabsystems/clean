#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_native_control.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

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
/// The clause with a bare session and no terminal giving NoSuchSession: false at (false, false,
/// Owner, BareSession).
pub fn native_control_decision_wrong(
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
                matches!(result, NativeControlDecision::NoSuchSession)
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
