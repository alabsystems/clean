#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_row_state.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum RowState {
    Published,
    Staged,
    Blocked,
    Absent,
    Skipped,
}
/// The clause with buildability outranking the latch: false at (false, false, true, true).
pub fn row_state_wrong(published: bool, staged: bool, latched: bool, buildable: bool) -> u8 {
    let result = if published {
        RowState::Published
    } else if staged {
        RowState::Staged
    } else if latched {
        RowState::Blocked
    } else if buildable {
        RowState::Absent
    } else {
        RowState::Skipped
    };
    let ok = if published {
        matches!(result, RowState::Published)
    } else if staged {
        matches!(result, RowState::Staged)
    } else if buildable {
        matches!(result, RowState::Absent)
    } else if latched {
        matches!(result, RowState::Blocked)
    } else {
        matches!(result, RowState::Skipped)
    };
    let z = ok as u8;
    z - 1 + 1
}
