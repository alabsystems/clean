#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_decide_bind.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum BindAction {
    RemoveAndBind,
    RefuseLiveSocket,
}
/// The clause refusing a dead socket too: false at `false`.
pub fn decide_bind_wrong(is_live: bool) -> u8 {
    let result = if is_live {
        BindAction::RefuseLiveSocket
    } else {
        BindAction::RemoveAndBind
    };
    let ok = if is_live {
        matches!(result, BindAction::RefuseLiveSocket)
    } else {
        matches!(result, BindAction::RefuseLiveSocket)
    };
    let z = ok as u8;
    z - 1 + 1
}
