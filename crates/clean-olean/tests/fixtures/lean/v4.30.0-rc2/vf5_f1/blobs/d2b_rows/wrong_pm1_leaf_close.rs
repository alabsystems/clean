#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_leaf_close.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum LeafCloseRecordKind {
    ClosedView,
    ClosedTab,
}
/// The clause with `k < 1`: false at 1.
pub fn leaf_close_record_kind_wrong(leaves_before_close: usize) -> u8 {
    let result = if leaves_before_close <= 1 {
        LeafCloseRecordKind::ClosedTab
    } else {
        LeafCloseRecordKind::ClosedView
    };
    let ok = matches!(result, LeafCloseRecordKind::ClosedTab) == (leaves_before_close < 1);
    let z = ok as u8;
    z - 1 + 1
}
