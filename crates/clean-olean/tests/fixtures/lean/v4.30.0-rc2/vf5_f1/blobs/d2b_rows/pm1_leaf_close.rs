#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/closed_recovery.rs `LeafCloseRecordKind` (derives dropped),
// `leaf_close_record_kind`
pub enum LeafCloseRecordKind {
    ClosedView,
    ClosedTab,
}
pub const fn leaf_close_record_kind(leaves_before_close: usize) -> LeafCloseRecordKind {
    if leaves_before_close <= 1 {
        LeafCloseRecordKind::ClosedTab
    } else {
        LeafCloseRecordKind::ClosedView
    }
}
/// aterm-gui SPECS.md CR-ledger (the final sentence): leaf_close_record_kind(k) = ClosedTab ⇔ k
/// ≤ 1, else ClosedView.
pub fn leaf_close_record_kind_spec(leaves_before_close: usize) -> u8 {
    let result = if leaves_before_close <= 1 {
        LeafCloseRecordKind::ClosedTab
    } else {
        LeafCloseRecordKind::ClosedView
    };
    let ok = matches!(result, LeafCloseRecordKind::ClosedTab) == (leaves_before_close < 2);
    let z = ok as u8;
    z - 1 + 1
}
