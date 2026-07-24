// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Relocate captured `.jsonl` proof files after each OK build.
//!
//! The capture hook writes files (heap-baked, at `at_end`, BEFORE any heap
//! save) into `from_dir`; after a segment builds OK the driver moves every name
//! matching the collect glob into the durable `to_dir` — matching the launch
//! scripts' `collect()` shell function.

use std::path::Path;

use regex::Regex;

use super::error::CaptureChainError;

/// Compile a simple filename glob (`*` = any run, `?` = one char; all other
/// characters literal) into an anchored [`Regex`].
#[must_use]
pub fn glob_to_regex(glob: &str) -> Regex {
    let mut pattern = String::with_capacity(glob.len() + 4);
    pattern.push('^');
    for ch in glob.chars() {
        match ch {
            '*' => pattern.push_str(".*"),
            '?' => pattern.push('.'),
            other => pattern.push_str(&regex::escape(&other.to_string())),
        }
    }
    pattern.push('$');
    // The pattern is well-formed by construction (every metachar is escaped).
    Regex::new(&pattern).unwrap_or_else(|_| Regex::new("^$").expect("literal empty regex compiles"))
}

/// Whether `name` matches `glob`.
#[must_use]
pub fn glob_matches(glob: &str, name: &str) -> bool {
    glob_to_regex(glob).is_match(name)
}

/// Move every file in `from_dir` whose name matches `glob` into `to_dir`,
/// returning the number moved. `to_dir` is created if missing. A missing
/// `from_dir` yields 0 (the hook simply produced nothing this segment).
///
/// # Errors
/// [`CaptureChainError::CreateDir`] if `to_dir` cannot be created;
/// [`CaptureChainError::Collect`] on a read/move failure.
pub fn collect_captures(
    from_dir: &Path,
    to_dir: &Path,
    glob: &str,
) -> Result<usize, CaptureChainError> {
    if !from_dir.exists() {
        return Ok(0);
    }
    std::fs::create_dir_all(to_dir).map_err(|source| CaptureChainError::CreateDir {
        path: to_dir.to_path_buf(),
        source,
    })?;
    let re = glob_to_regex(glob);
    let listing = std::fs::read_dir(from_dir).map_err(|source| CaptureChainError::Collect {
        path: from_dir.to_path_buf(),
        source,
    })?;
    let mut moved = 0usize;
    for entry in listing {
        let entry = entry.map_err(|source| CaptureChainError::Collect {
            path: from_dir.to_path_buf(),
            source,
        })?;
        let path = entry.path();
        if !path.is_file() {
            continue;
        }
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if !re.is_match(name) {
            continue;
        }
        let dest = to_dir.join(name);
        move_file(&path, &dest)?;
        moved += 1;
    }
    Ok(moved)
}

/// Move a file, falling back to copy+remove when `rename` fails across devices
/// (EXDEV: `from_dir` and `to_dir` on different mounts).
fn move_file(src: &Path, dest: &Path) -> Result<(), CaptureChainError> {
    if std::fs::rename(src, dest).is_ok() {
        return Ok(());
    }
    std::fs::copy(src, dest).map_err(|source| CaptureChainError::Collect {
        path: src.to_path_buf(),
        source,
    })?;
    std::fs::remove_file(src).map_err(|source| CaptureChainError::Collect {
        path: src.to_path_buf(),
        source,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_glob_matches_star_and_literal_dot() {
        assert!(glob_matches(
            "HOL-Library.*.jsonl",
            "HOL-Library.Interval.jsonl"
        ));
        assert!(glob_matches(
            "HOL-Library.*.jsonl",
            "HOL-Library.Float.jsonl"
        ));
        assert!(!glob_matches(
            "HOL-Library.*.jsonl",
            "HOL-Analysis.Inner.jsonl"
        ));
        // The literal dot must not match arbitrary characters.
        assert!(!glob_matches("a.b", "axb"));
        assert!(glob_matches("a.b", "a.b"));
    }

    #[test]
    fn test_glob_matches_question_mark() {
        assert!(glob_matches("f?o.jsonl", "foo.jsonl"));
        assert!(!glob_matches("f?o.jsonl", "fooo.jsonl"));
    }

    #[test]
    fn test_collect_moves_matching_files_only() {
        let base = std::env::temp_dir().join(format!("cc_collect_{}", std::process::id()));
        let from = base.join("from");
        let to = base.join("to");
        std::fs::create_dir_all(&from).expect("mk from");
        for name in [
            "HOL-Library.Interval.jsonl",
            "HOL-Library.Float.jsonl",
            "notes.txt",
        ] {
            std::fs::write(from.join(name), b"x").expect("write file");
        }
        let moved = collect_captures(&from, &to, "HOL-Library.*.jsonl").expect("collect succeeds");
        assert_eq!(moved, 2, "only the two matching jsonl files move");
        assert!(to.join("HOL-Library.Interval.jsonl").exists());
        assert!(to.join("HOL-Library.Float.jsonl").exists());
        assert!(
            from.join("notes.txt").exists(),
            "non-matching file stays in from_dir"
        );
        assert!(
            !from.join("HOL-Library.Float.jsonl").exists(),
            "matched files are moved (not copied)"
        );
        let _ = std::fs::remove_dir_all(&base);
    }

    #[test]
    fn test_collect_missing_from_dir_is_zero() {
        let missing = std::env::temp_dir().join("cc_collect_missing_xyz_none");
        let to = std::env::temp_dir().join("cc_collect_to_xyz_none");
        assert_eq!(
            collect_captures(&missing, &to, "*.jsonl").expect("missing from_dir yields 0"),
            0
        );
    }
}
