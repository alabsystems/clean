// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which Lean command line the front door speaks, and how it names itself
//! (decisions R75 and R76 in `docs/DECISIONS.md`).
//!
//! The releases Clean models differ in their command line (Lean 4.30.0-rc2
//! adds `-E`, `-V`, `--src-deps`, `--setup` and a file-taking `--run`), their
//! usage-error streams, their `-D` error texts, their `--json` objects and the
//! `sorry` warning's quotes. The dialect is chosen the way `elan` chooses the
//! `lean` it runs, from the working directory: `CLEAN_LEAN_VERSION` if set,
//! else the nearest `lean-toolchain` above the working directory, else Clean's
//! own pin. A `lean-toolchain` that reads exactly `clean`, the name
//! `clean lake new` and `clean lake init` write
//! ([`clean_lake::DEFAULT_CLEAN_TOOLCHAIN`]), is a Clean project and gets
//! Clean's own pin too, as an absent file does. Any other toolchain Clean does not
//! model is refused by name rather than answered in a dialect the caller did
//! not ask for.
//!
//! Identity is Clean's, never Lean's: `--version` prints Clean's build version
//! and names the Lean release it models, `-V` prints Clean's version, and `-g`
//! prints the commit Clean was built from (or refuses when the build has no git
//! provenance). No Lean commit hash is ever printed.

use std::path::{Path, PathBuf};

/// A Lean release whose command line `clean lean` reproduces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LeanDialect {
    /// Lean 4.8.0: trust-ir's toolchain, and the release Clean's elaborator,
    /// `-D` option table and `#guard_msgs` model.
    V4_8_0,
    /// Lean 4.30.0-rc2: Clean's own `lean-toolchain` pin.
    V4_30_0Rc2,
    /// Lean 4.36.0: stable source checking with its exact installed library.
    V4_36_0,
}

/// The environment variable that chooses the dialect explicitly.
pub(crate) const VERSION_ENV: &str = "CLEAN_LEAN_VERSION";

/// Clean's own pin (`lean-toolchain` at the repository root; a test keeps the
/// two equal).
pub(crate) const PINNED: LeanDialect = LeanDialect::V4_30_0Rc2;

impl LeanDialect {
    /// The release's version string.
    pub(crate) fn version(self) -> &'static str {
        match self {
            Self::V4_8_0 => "4.8.0",
            Self::V4_30_0Rc2 => "4.30.0-rc2",
            Self::V4_36_0 => "4.36.0",
        }
    }

    /// The source semantics paired with this command-line dialect.
    pub(crate) fn world(self) -> clean_kernel::LeanWorld {
        match self {
            Self::V4_8_0 => clean_kernel::LeanWorld::Lean408,
            Self::V4_30_0Rc2 => clean_kernel::LeanWorld::Lean430Rc2,
            Self::V4_36_0 => clean_kernel::LeanWorld::Lean436,
        }
    }

    /// Whether the release has the command-line additions of 4.30
    /// (`-E`, `-V`, `--src-deps`, `--setup`, `--run <file>`).
    pub(crate) fn is_modern(self) -> bool {
        self != Self::V4_8_0
    }

    /// A measured source world requires an exact library before checking.
    pub(crate) fn explicit_source_world(self) -> Option<clean_kernel::LeanWorld> {
        match self {
            Self::V4_36_0 => Some(clean_kernel::LeanWorld::Lean436),
            Self::V4_8_0 | Self::V4_30_0Rc2 => None,
        }
    }

    /// Parse a version as `CLEAN_LEAN_VERSION` or a `lean-toolchain` spells
    /// it: `4.8.0`, `v4.8.0` or `leanprover/lean4:v4.8.0`.
    pub(crate) fn parse(spelling: &str) -> Option<Self> {
        let trimmed = spelling.trim();
        let bare = trimmed.strip_prefix("leanprover/lean4:").unwrap_or(trimmed);
        match bare.strip_prefix('v').unwrap_or(bare) {
            "4.8.0" => Some(Self::V4_8_0),
            "4.30.0-rc2" => Some(Self::V4_30_0Rc2),
            "4.36.0" => Some(Self::V4_36_0),
            _ => None,
        }
    }

    /// Lean's `--help` text after its first line, verbatim.
    pub(crate) fn help_body(self) -> &'static str {
        match self {
            Self::V4_8_0 => include_str!("help_v4_8_0.txt"),
            Self::V4_30_0Rc2 => include_str!("help_v4_30_0_rc2.txt"),
            Self::V4_36_0 => include_str!("help_v4_36_0.txt"),
        }
    }
}

/// Why no dialect could be chosen: the message `clean lean` prints before
/// exiting 1.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DialectRefusal(pub(crate) String);

/// Choose the dialect for a run started in `cwd`, given the value of
/// [`VERSION_ENV`].
pub(crate) fn select(cwd: &Path, env_value: Option<&str>) -> Result<LeanDialect, DialectRefusal> {
    let modelled = "4.8.0, 4.30.0-rc2 and 4.36.0";
    if let Some(value) = env_value {
        return LeanDialect::parse(value).ok_or_else(|| {
            DialectRefusal(format!(
                "clean: `lean`: {VERSION_ENV}={value} names a Lean release Clean's `lean` \
                 front door does not model; it models {modelled}"
            ))
        });
    }
    match nearest_toolchain_file(cwd) {
        None => Ok(PINNED),
        // A project Clean's own scaffold made: Clean's pin, as with no file.
        Some((_, content)) if is_clean_scaffold_toolchain(&content) => Ok(PINNED),
        Some((path, content)) => LeanDialect::parse(&content).ok_or_else(|| {
            DialectRefusal(format!(
                "clean: `lean`: {} names the toolchain `{}`, which Clean's `lean` front door \
                 does not model (it models Lean {modelled}); set {VERSION_ENV} to choose one",
                path.display(),
                content.trim()
            ))
        }),
    }
}

/// Whether a `lean-toolchain`'s text is the one `clean lake new` and
/// `clean lake init` write, surrounding whitespace aside: exactly that name,
/// never the legacy `clean:stable` or another spelling.
fn is_clean_scaffold_toolchain(content: &str) -> bool {
    content.trim() == clean_lake::DEFAULT_CLEAN_TOOLCHAIN.trim()
}

/// The nearest `lean-toolchain` at or above `cwd`, with its text.
fn nearest_toolchain_file(cwd: &Path) -> Option<(PathBuf, String)> {
    cwd.ancestors().find_map(|dir| {
        let candidate = dir.join("lean-toolchain");
        std::fs::read_to_string(&candidate)
            .ok()
            .map(|text| (candidate, text))
    })
}

/// Clean's build version (`<crate version>+g<sha>`, or the crate version with
/// a note when the build has no git provenance).
pub(crate) fn clean_version() -> &'static str {
    env!("CLEAN_BUILD_VERSION")
}

/// The commit Clean was built from, when the build knows it.
pub(crate) fn clean_git_sha() -> Option<&'static str> {
    let sha = env!("CLEAN_BUILD_GIT_SHA");
    (sha != "unknown").then_some(sha)
}

/// The first line of `--version` and of every help text: Lean's shape
/// (`Lean (version …, <target>, commit …, Release)`), naming Clean and the
/// Lean release it models.
pub(crate) fn version_line(dialect: LeanDialect) -> String {
    let profile = if cfg!(debug_assertions) {
        "Debug"
    } else {
        "Release"
    };
    format!(
        "Clean (version {}, {}-{}, `lean` front door for Lean {}, {profile})",
        clean_version(),
        std::env::consts::ARCH,
        std::env::consts::OS,
        dialect.version()
    )
}

/// What Clean's front door refuses, appended to `--help` so the help never
/// advertises a flag that would then be refused without warning.
pub(crate) fn refusal_note(dialect: LeanDialect) -> String {
    let mut note = String::from(
        "Clean's `lean` front door refuses (exit 1, naming what is unsupported): ",
    );
    if dialect != LeanDialect::V4_36_0 {
        note.push_str("--features, -o, ");
    }
    note.push_str(
        "\
-i, -c, -b, -t, -M, -T, -j, -s, -e, -C, --server, --worker, --plugin, --load-dynlib, --setup, ",
    );
    if !dialect.is_modern() {
        note.push_str("--deps-json, ");
    }
    if dialect != LeanDialect::V4_36_0 {
        note.push_str("--print-prefix, --print-libdir, ");
    }
    note.push_str("--profile, --stats.\n");
    if dialect == LeanDialect::V4_36_0 {
        note.push_str(
            "For Lean 4.36.0 it also refuses --incr-save, --incr-load, and --incr-header-save.\n\
             The -o option supports checked axiom and theorem modules in the Lean 4.36.0 dialect.\n",
        );
    }
    note
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dialect_parse_accepts_toolchain_spellings() {
        assert_eq!(
            LeanDialect::parse("leanprover/lean4:v4.8.0\n"),
            Some(LeanDialect::V4_8_0)
        );
        assert_eq!(
            LeanDialect::parse("v4.30.0-rc2"),
            Some(LeanDialect::V4_30_0Rc2)
        );
        assert_eq!(LeanDialect::parse("4.8.0"), Some(LeanDialect::V4_8_0));
        assert_eq!(
            LeanDialect::parse("leanprover/lean4:v4.36.0\n"),
            Some(LeanDialect::V4_36_0)
        );
        assert_eq!(LeanDialect::parse("leanprover/lean4:v4.9.0"), None);
        // A reader measurement or explicit `check` choice does not admit the
        // separate full `lean` front-door dialect.
        assert_eq!(LeanDialect::parse("leanprover/lean4:v4.36.0-rc2"), None);
        assert_eq!(LeanDialect::parse("../build/release/stage1"), None);
    }

    #[test]
    fn test_pinned_dialect_is_the_repository_lean_toolchain() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean-toolchain");
        let text = std::fs::read_to_string(&root).expect("repository lean-toolchain");
        assert_eq!(LeanDialect::parse(&text), Some(PINNED), "{text}");
    }

    #[test]
    fn test_select_refuses_an_unmodelled_toolchain_and_honours_the_override() {
        let dir = std::env::temp_dir().join(format!("clean-lean-dialect-{}", std::process::id()));
        let sub = dir.join("sub");
        std::fs::create_dir_all(&sub).expect("temp dir");
        std::fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.9.0\n").expect("toolchain");
        let refused = select(&sub, None).expect_err("4.9.0 is not modelled");
        assert!(
            refused.0.contains("leanprover/lean4:v4.9.0"),
            "{}",
            refused.0
        );
        assert_eq!(select(&sub, Some("4.8.0")), Ok(LeanDialect::V4_8_0));
        std::fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.8.0\n").expect("toolchain");
        assert_eq!(select(&sub, None), Ok(LeanDialect::V4_8_0));
        assert!(select(&sub, Some("4.9.0")).is_err());
        std::fs::remove_dir_all(&dir).expect("cleanup");
    }

    /// `clean lake new` and `clean lake init` write
    /// `clean_lake::DEFAULT_CLEAN_TOOLCHAIN`; before this, `select` refused it
    /// (`LeanDialect::parse("clean")` is `None`), so `clean lean` exited 1 in
    /// every project Clean scaffolded unless `CLEAN_LEAN_VERSION` was set.
    #[test]
    fn test_select_clean_scaffold_toolchain_selects_the_pin() {
        let dir = tempfile::tempdir().expect("tempdir");
        let sub = dir.path().join("sub");
        std::fs::create_dir_all(&sub).expect("sub dir");
        let toolchain = dir.path().join("lean-toolchain");
        std::fs::write(&toolchain, clean_lake::DEFAULT_CLEAN_TOOLCHAIN).expect("toolchain");
        assert_eq!(select(&sub, None), Ok(PINNED));
        assert_eq!(select(dir.path(), None), Ok(PINNED));
        // The override still wins, and still refuses what it does not model.
        assert_eq!(select(&sub, Some("4.8.0")), Ok(LeanDialect::V4_8_0));
        assert!(select(&sub, Some("clean")).is_err());
    }

    /// Only the scaffold's exact name selects the pin. The legacy
    /// `clean:stable` (scaffolds before R153) stays refused by name: under
    /// elan 4.2.1 it ran the default Lean toolchain, so it does not say which
    /// Lean the project's `lean` speaks.
    #[test]
    fn test_select_other_clean_like_toolchains_are_refused() {
        let dir = tempfile::tempdir().expect("tempdir");
        let toolchain = dir.path().join("lean-toolchain");
        for spelling in [
            "clean:stable\n",
            "Clean\n",
            "clean-nightly\n",
            "leanprover/lean4:clean\n",
            "clean/clean:stable\n",
            "clean clean\n",
        ] {
            std::fs::write(&toolchain, spelling).expect("toolchain");
            let refused = select(dir.path(), None).expect_err(spelling);
            let named = format!("names the toolchain `{}`", spelling.trim());
            assert!(refused.0.contains(&named), "{spelling:?}: {}", refused.0);
        }
    }

    /// Clean's pin is the oracle world `crates/clean-olean/lean_worlds.tsv`
    /// names, so a Clean project's `lean` speaks the release Clean reads
    /// `.olean` files of.
    #[test]
    fn test_pinned_dialect_is_the_oracle_world_of_lean_worlds() {
        let table = Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-olean/lean_worlds.tsv");
        let text = std::fs::read_to_string(&table).expect("lean_worlds.tsv");
        let oracle_toolchains: Vec<&str> = text
            .lines()
            .filter(|line| !line.starts_with('#') && !line.trim().is_empty())
            .filter_map(|line| {
                let columns: Vec<&str> = line.split('\t').collect();
                match (columns.get(1), columns.get(2)) {
                    (Some(&"oracle"), Some(toolchain)) => Some(*toolchain),
                    _ => None,
                }
            })
            .collect();
        let pinned = format!("leanprover/lean4:v{}", PINNED.version());
        assert_eq!(oracle_toolchains, [pinned.as_str()]);
    }
}
