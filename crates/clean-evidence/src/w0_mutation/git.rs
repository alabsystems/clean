// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Read the pinned mutation inputs from their committed Git tree.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use super::CheckError;

const CHECKER: &str = "theories/kcheck_labelled";

pub(super) struct Snapshot {
    root: PathBuf,
    tree: String,
    epoch: String,
}

impl Snapshot {
    pub(super) fn open(root: &Path, commit: &str, tree: &str) -> Result<Self, CheckError> {
        if !is_oid(commit) || !is_oid(tree) {
            return Err(CheckError::Invalid(
                "snapshot commit and tree must be full lowercase SHA-1 IDs".to_owned(),
            ));
        }
        let root = root
            .canonicalize()
            .map_err(|error| CheckError::Unavailable(format!("{}: {error}", root.display())))?;
        if git(
            &root,
            &["rev-parse", "--is-inside-work-tree", "--show-prefix"],
        )? != b"true\n\n"
        {
            return Err(CheckError::Unavailable(format!(
                "{} is not the root of a Git worktree",
                root.display()
            )));
        }
        require_object_type(&root, commit, "commit")?;
        let object = git(&root, &["cat-file", "commit", commit])?;
        let (actual_tree, epoch) = commit_identity(&object)?;
        if tree != actual_tree {
            return Err(CheckError::Invalid(format!(
                "snapshot commit {commit} has tree {actual_tree}, expected {tree}"
            )));
        }
        require_object_type(&root, tree, "tree")?;
        Ok(Self {
            root,
            tree: tree.to_owned(),
            epoch: epoch.to_owned(),
        })
    }

    pub(super) fn epoch(&self) -> &str {
        &self.epoch
    }

    pub(super) fn read(&self, rel: &str) -> Result<Vec<u8>, CheckError> {
        let listing = self.list_path(rel)?;
        let entry = TreeEntry::named(&listing, rel)?;
        if !entry.is_regular() {
            return Err(CheckError::Invalid(format!(
                "snapshot path {rel:?} must be a regular tracked file"
            )));
        }
        require_object_type(&self.root, entry.oid, "blob")?;
        git(&self.root, &["cat-file", "blob", entry.oid])
    }

    pub(super) fn checker_sources(&self) -> Result<BTreeSet<String>, CheckError> {
        let listing = self.list_path(CHECKER)?;
        let checker = TreeEntry::named(&listing, CHECKER)?;
        if checker.kind != "040000 tree" {
            return Err(CheckError::Invalid(format!(
                "snapshot path {CHECKER:?} must be a tracked directory"
            )));
        }
        require_object_type(&self.root, checker.oid, "tree")?;
        let listing = git(
            &self.root,
            &["ls-tree", "-r", "-z", "--full-tree", checker.oid],
        )?;
        let mut sources = BTreeSet::new();
        if listing.is_empty() {
            return Ok(sources);
        }
        for record in terminated_records(&listing)?.split(|byte| *byte == 0) {
            if let Some(entry) = TreeEntry::checker_source(record)? {
                sources.insert(format!("{CHECKER}/{}", entry.path));
            }
        }
        Ok(sources)
    }

    fn list_path(&self, rel: &str) -> Result<Vec<u8>, CheckError> {
        if !is_relative(rel) {
            return Err(CheckError::Invalid(format!(
                "invalid snapshot path {rel:?}"
            )));
        }
        git(
            &self.root,
            &["ls-tree", "-z", "--full-tree", &self.tree, "--", rel],
        )
    }
}

fn is_oid(value: &str) -> bool {
    value.len() == 40
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn is_relative(path: &str) -> bool {
    !path.contains(['\\', '\0']) && path.split('/').all(|part| !matches!(part, "" | "." | ".."))
}

fn commit_identity(object: &[u8]) -> Result<(&str, &str), CheckError> {
    let invalid = || CheckError::Invalid("invalid snapshot commit headers".to_owned());
    let mut headers = object.split(|byte| *byte == b'\n');
    let tree = headers
        .next()
        .and_then(|line| line.strip_prefix(b"tree "))
        .and_then(|tree| std::str::from_utf8(tree).ok())
        .filter(|tree| is_oid(tree))
        .ok_or_else(invalid)?;
    let epoch = headers
        .take_while(|line| !line.is_empty())
        .find_map(|line| line.strip_prefix(b"committer "))
        .and_then(|line| line.rsplitn(3, |byte| *byte == b' ').nth(1))
        .and_then(|epoch| std::str::from_utf8(epoch).ok())
        .filter(|epoch| !epoch.is_empty() && epoch.bytes().all(|byte| byte.is_ascii_digit()))
        .ok_or_else(invalid)?;
    Ok((tree, epoch))
}

fn terminated_records(listing: &[u8]) -> Result<&[u8], CheckError> {
    listing
        .strip_suffix(b"\0")
        .ok_or_else(|| CheckError::Invalid("unterminated Git tree listing".to_owned()))
}

struct TreeEntry<'a> {
    path: &'a str,
    oid: &'a str,
    kind: &'a str,
}

impl<'a> TreeEntry<'a> {
    /// Apply the declared inventory exclusions to raw Git names first. Git
    /// permits names the host filesystem cannot represent; excluded cache and
    /// symlink entries must not make an otherwise valid source scope fail.
    fn checker_source(record: &'a [u8]) -> Result<Option<Self>, CheckError> {
        let separator = record
            .iter()
            .position(|byte| *byte == b'\t')
            .ok_or_else(|| CheckError::Invalid("invalid Git tree entry".to_owned()))?;
        let metadata = &record[..separator];
        let path = &record[separator + 1..];
        if !(metadata.starts_with(b"100644 blob ") || metadata.starts_with(b"100755 blob "))
            || !path.ends_with(b".lean")
            || path
                .split(|byte| *byte == b'/')
                .any(|part| part == b".lake")
        {
            return Ok(None);
        }
        Self::parse(record).map(Some)
    }

    fn named(listing: &'a [u8], path: &str) -> Result<Self, CheckError> {
        let missing = || CheckError::Invalid(format!("snapshot is missing {path:?}"));
        if listing.is_empty() {
            return Err(missing());
        }
        let entry = Self::parse(terminated_records(listing)?)?;
        if entry.path != path {
            return Err(missing());
        }
        Ok(entry)
    }

    fn parse(record: &'a [u8]) -> Result<Self, CheckError> {
        let invalid = || CheckError::Invalid("invalid Git tree entry".to_owned());
        let record = std::str::from_utf8(record).map_err(|_| invalid())?;
        let (metadata, path) = record.split_once('\t').ok_or_else(invalid)?;
        let (kind, oid) = metadata.rsplit_once(' ').ok_or_else(invalid)?;
        if !is_oid(oid) || !is_relative(path) {
            return Err(invalid());
        }
        Ok(Self { path, oid, kind })
    }

    fn is_regular(&self) -> bool {
        matches!(self.kind, "100644 blob" | "100755 blob")
    }
}

fn require_object_type(root: &Path, oid: &str, kind: &str) -> Result<(), CheckError> {
    let actual = git(root, &["cat-file", "-t", oid])?;
    if actual.strip_suffix(b"\n") != Some(kind.as_bytes()) {
        return Err(CheckError::Invalid(format!(
            "snapshot object {oid} is not of type {kind}"
        )));
    }
    Ok(())
}

fn git(root: &Path, args: &[&str]) -> Result<Vec<u8>, CheckError> {
    crate::git::read(root, args).map_err(CheckError::Unavailable)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::io::Write;
    use std::process::{Command, Stdio};

    fn text(root: &Path, args: &[&str]) -> String {
        String::from_utf8(git(root, args).unwrap())
            .unwrap()
            .trim_end()
            .to_owned()
    }

    fn commit(root: &Path, message: &str) -> String {
        git(
            root,
            &[
                "-c",
                "user.name=W0",
                "-c",
                "user.email=w0@example.invalid",
                "commit",
                "--quiet",
                "-m",
                message,
            ],
        )
        .unwrap();
        text(root, &["rev-parse", "HEAD"])
    }

    fn raw_index_entry(root: &Path, mode: &str, oid: &str, path: &[u8]) {
        let mut entry = format!("{mode} {oid}\t").into_bytes();
        entry.extend_from_slice(path);
        entry.push(0);
        let mut command = Command::new("git");
        for (name, _) in std::env::vars_os() {
            if name
                .as_encoded_bytes()
                .get(..4)
                .is_some_and(|prefix| prefix.eq_ignore_ascii_case(b"GIT_"))
            {
                command.env_remove(name);
            }
        }
        let mut writer = command
            .current_dir(root)
            .args(["update-index", "--add", "-z", "--index-info"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("raw Git index writer");
        writer
            .stdin
            .take()
            .expect("index writer stdin")
            .write_all(&entry)
            .expect("write raw index entry");
        let output = writer.wait_with_output().expect("raw index result");
        assert!(output.status.success(), "{output:?}");
    }

    #[test]
    fn complete_checker_inventory_filters_excluded_raw_names_before_decoding() {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path();
        git(root, &["init", "--quiet", "--object-format=sha1"]).unwrap();
        git(root, &["config", "user.name", "W0"]).unwrap();
        git(root, &["config", "user.email", "w0@example.invalid"]).unwrap();
        git(root, &["config", "commit.gpgsign", "false"]).unwrap();
        fs::create_dir_all(root.join(CHECKER).join("nested")).unwrap();
        for path in ["A.lean", "nested/B.lean"] {
            fs::write(root.join(CHECKER).join(path), "checker").unwrap();
        }
        git(root, &["add", "--all"]).unwrap();
        let parent = commit(root, "complete checker scope");
        let blob = text(root, &["rev-parse", &format!("HEAD:{CHECKER}/A.lean")]);

        // APFS cannot materialize these names. Real Git index/tree objects
        // exercise the reader without making a filesystem-dependent skip.
        for (mode, path) in [
            ("100644", b"excluded-\xff.txt".as_slice()),
            ("100644", b".lake/excluded-\xff.lean".as_slice()),
            ("100644", b"nested/.lake/excluded-\xff.lean".as_slice()),
            ("120000", b"excluded-\xff.lean".as_slice()),
        ] {
            let mut relative = format!("{CHECKER}/").into_bytes();
            relative.extend_from_slice(path);
            raw_index_entry(root, mode, &blob, &relative);
        }
        let tree = text(root, &["write-tree"]);
        let source = text(
            root,
            &["commit-tree", &tree, "-p", &parent, "-m", "raw exclusions"],
        );
        let snapshot = Snapshot::open(root, &source, &tree).unwrap();
        let expected = BTreeSet::from([
            format!("{CHECKER}/A.lean"),
            format!("{CHECKER}/nested/B.lean"),
        ]);
        assert_eq!(snapshot.checker_sources().unwrap(), expected);

        // Reconstruct the entire immutable inventory even after a selected
        // source vanishes from the current checkout; do not trust survivors.
        fs::remove_file(root.join(CHECKER).join("nested/B.lean")).unwrap();
        assert_eq!(snapshot.checker_sources().unwrap(), expected);
        assert_eq!(
            snapshot.read(&format!("{CHECKER}/nested/B.lean")).unwrap(),
            b"checker"
        );

        let mut selected = format!("{CHECKER}/").into_bytes();
        selected.extend_from_slice(b"selected-\xff.lean");
        raw_index_entry(root, "100644", &blob, &selected);
        let invalid_tree = text(root, &["write-tree"]);
        let invalid = text(
            root,
            &[
                "commit-tree",
                &invalid_tree,
                "-p",
                &source,
                "-m",
                "selected raw name",
            ],
        );
        assert!(matches!(
            Snapshot::open(root, &invalid, &invalid_tree)
                .unwrap()
                .checker_sources(),
            Err(CheckError::Invalid(_))
        ));
    }

    #[test]
    fn reads_the_committed_tree_and_ignores_replacements() {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path();
        git(root, &["init", "--quiet", "--object-format=sha1"]).unwrap();
        let checker = root.join(CHECKER);
        fs::create_dir_all(checker.join(".lake")).unwrap();
        fs::write(checker.join("A.lean"), "checker").unwrap();
        fs::write(checker.join(".lake/Cache.lean"), "cache").unwrap();
        fs::write(root.join("input[1]"), "pinned").unwrap();
        git(root, &["add", "--force", "--all"]).unwrap();
        let oid = text(root, &["rev-parse", ":input[1]"]);
        let symlink = format!("120000,{oid},{CHECKER}/Link.lean");
        git(root, &["update-index", "--add", "--cacheinfo", &symlink]).unwrap();
        let pinned = commit(root, "pinned");
        let tree = text(root, &["rev-parse", "HEAD^{tree}"]);
        let epoch = text(root, &["show", "-s", "--format=%ct", &pinned]);

        fs::write(root.join("input[1]"), "different").unwrap();
        git(root, &["add", "--", "input[1]"]).unwrap();
        git(root, &["rm", "--quiet", "--cached", "-r", "--", CHECKER]).unwrap();
        let replacement = commit(root, "replacement");
        let replacement_tree = text(root, &["rev-parse", "HEAD^{tree}"]);
        git(root, &["replace", &pinned, &replacement]).unwrap();
        let replacement_blob = text(root, &["rev-parse", "HEAD:input[1]"]);
        git(root, &["replace", &oid, &replacement_blob]).unwrap();

        let snapshot = Snapshot::open(root, &pinned, &tree).unwrap();
        assert_eq!(snapshot.epoch(), epoch);
        assert_eq!(snapshot.read("input[1]").unwrap().as_slice(), b"pinned");
        assert_eq!(
            snapshot.checker_sources().unwrap(),
            BTreeSet::from([format!("{CHECKER}/A.lean")])
        );
        for path in [
            "input1",
            "./input[1]",
            "../input[1]",
            "theories//kcheck_labelled",
            CHECKER,
        ] {
            assert!(matches!(snapshot.read(path), Err(CheckError::Invalid(_))));
        }
        assert!(matches!(
            snapshot.read(&format!("{CHECKER}/Link.lean")),
            Err(CheckError::Invalid(_))
        ));
        assert!(matches!(
            Snapshot::open(&checker, &pinned, &tree),
            Err(CheckError::Unavailable(_))
        ));
        assert!(matches!(
            Snapshot::open(root, &pinned, &pinned),
            Err(CheckError::Invalid(_))
        ));
        assert!(matches!(
            Snapshot::open(root, &"0".repeat(40), &tree),
            Err(CheckError::Unavailable(_))
        ));
        assert!(matches!(
            Snapshot::open(root, &replacement, &replacement_tree)
                .unwrap()
                .checker_sources(),
            Err(CheckError::Invalid(_))
        ));
    }
}
