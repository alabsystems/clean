// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The two facts the board reads from Git: a record's committed baseline and
//! the date of its last commit. Both are optional: outside a Git checkout the
//! board shows no age and `check` skips the direction comparison, saying so.

use std::path::Path;
use std::process::Command;

fn git(root: &Path, args: &[&str]) -> Option<Vec<u8>> {
    let mut command = Command::new("git");
    command
        .current_dir(root)
        .args(args)
        .env("GIT_OPTIONAL_LOCKS", "0");
    for variable in ["GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE"] {
        command.env_remove(variable);
    }
    let output = command.output().ok()?;
    output.status.success().then_some(output.stdout)
}

/// True when `root` is itself the top of a Git work tree. A temporary test
/// directory nested in some other checkout is not.
fn is_top_level(root: &Path) -> bool {
    git(root, &["rev-parse", "--show-prefix"]).is_some_and(|prefix| prefix == b"\n")
}

/// The bytes of `path` as committed at HEAD.
pub(super) fn committed_bytes(root: &Path, path: &str) -> Option<Vec<u8>> {
    if !is_top_level(root) {
        return None;
    }
    git(root, &["show", &format!("HEAD:{path}")])
}

/// `YYYY-MM-DD` of the last commit that touched `path`.
pub(super) fn last_commit_date(root: &Path, path: &str) -> Option<String> {
    if !is_top_level(root) {
        return None;
    }
    let output = git(root, &["log", "-1", "--format=%cs", "--", path])?;
    let date = String::from_utf8(output).ok()?.trim().to_owned();
    (!date.is_empty()).then_some(date)
}
