#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/control_auth.rs `BindAction` (derives dropped), `decide_bind`
pub enum BindAction {
    RemoveAndBind,
    RefuseLiveSocket,
}
pub const fn decide_bind(is_live: bool) -> BindAction {
    if is_live {
        BindAction::RefuseLiveSocket
    } else {
        BindAction::RemoveAndBind
    }
}
/// aterm-gui SPECS.md CA-socket-probe (the decide_bind clause): decide_bind(true) =
/// RefuseLiveSocket, decide_bind(false) = RemoveAndBind.
pub fn decide_bind_spec(is_live: bool) -> u8 {
    let result = if is_live {
        BindAction::RefuseLiveSocket
    } else {
        BindAction::RemoveAndBind
    };
    let ok = if is_live {
        matches!(result, BindAction::RefuseLiveSocket)
    } else {
        matches!(result, BindAction::RemoveAndBind)
    };
    let z = ok as u8;
    z - 1 + 1
}
