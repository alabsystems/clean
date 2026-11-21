// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Compare staged Python membership with a pinned published commit.

use std::{path::Path, str};

use super::super::{git, require_root, Inputs, InventoryError, REGISTRY};
use super::{Membership, BASELINE};

#[derive(Clone, Copy)]
enum Source {
    Index,
    Published,
}

impl Source {
    fn description(self) -> &'static str {
        match self {
            Self::Index => "staged",
            Self::Published => "published",
        }
    }
}

fn is_object_id(id: &str) -> bool {
    matches!(id.len(), 40 | 64)
        && id
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn read_git(root: &Path, args: &[&str]) -> Result<Vec<u8>, InventoryError> {
    git::read(root, args).map_err(InventoryError::Unavailable)
}

fn staged_listing(root: &Path) -> Result<Vec<u8>, InventoryError> {
    read_git(
        root,
        &[
            "ls-files", "--stage", "-z", "--", "scripts", REGISTRY, BASELINE,
        ],
    )
}

fn memberships(
    root: &Path,
    listing: &[u8],
    source: Source,
) -> Result<(Membership, Membership), InventoryError> {
    if listing.is_empty() {
        return Err(InventoryError::Unavailable(format!(
            "{} Python membership inputs are missing",
            source.description(),
        )));
    }
    let invalid_entry = || {
        InventoryError::Invalid(format!(
            "invalid {} Git entry in Python membership inputs",
            source.description(),
        ))
    };
    let records = listing.strip_suffix(b"\0").ok_or_else(invalid_entry)?;
    let mut paths = Vec::new();
    let mut registry_oid = None;
    let mut baseline_oid = None;
    for record in records.split(|byte| *byte == 0) {
        let tab = record
            .iter()
            .position(|byte| *byte == b'\t')
            .ok_or_else(invalid_entry)?;
        let (metadata, path) = record.split_at(tab);
        let path = &path[1..];
        let mut fields = str::from_utf8(metadata)
            .map_err(|_| invalid_entry())?
            .split(' ');
        let (Some(mode), Some(second), Some(third), None) =
            (fields.next(), fields.next(), fields.next(), fields.next())
        else {
            return Err(invalid_entry());
        };
        if matches!(source, Source::Index) && third != "0" {
            return Err(InventoryError::Invalid(
                "unmerged entry in staged Python membership inputs".to_owned(),
            ));
        }
        let slot = if path == REGISTRY.as_bytes() {
            &mut registry_oid
        } else if path == BASELINE.as_bytes() {
            &mut baseline_oid
        } else {
            paths.extend_from_slice(path);
            paths.push(0);
            continue;
        };
        let oid = match source {
            Source::Index => second,
            Source::Published if second == "blob" => third,
            Source::Published => return Err(invalid_entry()),
        };
        if !matches!(mode, "100644" | "100755") || !is_object_id(oid) || slot.replace(oid).is_some()
        {
            return Err(invalid_entry());
        }
    }
    let blob = |oid: Option<&str>, name| {
        let oid = oid.ok_or_else(|| {
            InventoryError::Unavailable(format!(
                "{} Python membership input {name} is missing",
                source.description(),
            ))
        })?;
        read_git(root, &["cat-file", "blob", oid])
    };
    let inputs = Inputs {
        names: paths,
        registry: blob(registry_oid, REGISTRY)?,
    };
    let baseline = Membership::from_baseline(&blob(baseline_oid, BASELINE)?)?;
    Ok((Membership::collect(&inputs)?, baseline))
}

pub fn check_publication(root: &Path, published: &str) -> Result<(), InventoryError> {
    require_root(root)?;
    if !is_object_id(published) {
        return Err(InventoryError::Invalid(
            "the published baseline must name a full lowercase Git commit ID".to_owned(),
        ));
    }
    if read_git(root, &["cat-file", "-t", published])? != b"commit\n" {
        return Err(InventoryError::Invalid(
            "the published baseline object is not a commit".to_owned(),
        ));
    }
    let head = read_git(root, &["rev-parse", "--verify", "HEAD"])?;
    let head_oid = str::from_utf8(&head)
        .ok()
        .and_then(|head| head.strip_suffix('\n'))
        .filter(|id| is_object_id(id))
        .ok_or_else(|| InventoryError::Unavailable("cannot pin candidate HEAD".to_owned()))?;
    if !read_git(root, &["rev-list", "-1", published, "--not", head_oid])?.is_empty() {
        return Err(InventoryError::Invalid(
            "the published baseline commit is not an ancestor of candidate HEAD".to_owned(),
        ));
    }
    let prior = read_git(
        root,
        &[
            "ls-tree",
            "-r",
            "-z",
            "--full-tree",
            published,
            "--",
            "scripts",
            REGISTRY,
            BASELINE,
        ],
    )?;
    let (published_live, published_baseline) = memberships(root, &prior, Source::Published)?;
    let index = staged_listing(root)?;
    let (live, baseline) = memberships(root, &index, Source::Index)?;
    if baseline != live {
        return Err(InventoryError::Invalid(
            "staged baseline does not match staged Python membership".to_owned(),
        ));
    }
    baseline.check(&published_baseline)?;
    baseline.check(&published_live)?;
    if index != staged_listing(root)? || head != read_git(root, &["rev-parse", "--verify", "HEAD"])?
    {
        return Err(InventoryError::Invalid(
            "candidate HEAD or index changed during Python membership check".to_owned(),
        ));
    }
    Ok(())
}
