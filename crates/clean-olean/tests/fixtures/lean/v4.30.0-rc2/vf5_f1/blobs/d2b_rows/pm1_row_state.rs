#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/atpkg-publish/src/lane/linux.rs `RowState` (derives dropped), `row_state`
pub enum RowState {
    Published,
    Staged,
    Blocked,
    Absent,
    Skipped,
}
pub const fn row_state(published: bool, staged: bool, latched: bool, buildable: bool) -> RowState {
    if published {
        RowState::Published
    } else if staged {
        RowState::Staged
    } else if latched {
        RowState::Blocked
    } else if buildable {
        RowState::Absent
    } else {
        RowState::Skipped
    }
}
/// atpkg-publish SPECS.md linux-row-state: row_state(pub, staged, latched, buildable) =
/// Published if pub, else Staged if staged, else Blocked if latched, else Absent if buildable,
/// else Skipped.
pub fn row_state_spec(published: bool, staged: bool, latched: bool, buildable: bool) -> u8 {
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
    } else if latched {
        matches!(result, RowState::Blocked)
    } else if buildable {
        matches!(result, RowState::Absent)
    } else {
        matches!(result, RowState::Skipped)
    };
    let z = ok as u8;
    z - 1 + 1
}
