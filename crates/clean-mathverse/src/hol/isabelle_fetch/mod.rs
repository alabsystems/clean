// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean mathverse isabelle-fetch`: download the public inputs of the
//! Isabelle import into a work folder and check each against the checksum
//! pinned in `data/isabelle_public_inputs.json`.
//!
//! The inputs are the two Isabelle distribution archives the import ran on
//! (Isabelle2025 and Isabelle2025-2, macOS) and the AFP checkout at the commit
//! it used. For each one:
//!
//! * an archive already in the work folder with the pinned size and sha256 is
//!   VERIFIED and left alone; otherwise `curl` downloads it to `<file>.part`,
//!   the part is size-checked and stream-hashed, and only a match is renamed
//!   into place (a mismatch deletes the part and fails);
//! * an AFP checkout already at the pinned commit with no modified tracked file
//!   is VERIFIED; an absent one is made with `git init` and a shallow fetch of
//!   exactly that commit into `<dir>.part`, checked with `git rev-parse HEAD`,
//!   and renamed into place; anything else in its place is REFUSED and left
//!   untouched.
//!
//! `--dry` hashes what is present and prints what a real run would fetch; it
//! starts no download and writes nothing. Every run ends with the manifest's
//! `not_fetched` list: what the import needs that is not public, and how to
//! get each back. The command fails if any requested input ends FAILED or
//! REFUSED.

mod error;
mod fetch;
mod manifest;

#[cfg(test)]
mod tests;

use std::io::Write;
use std::path::{Path, PathBuf};

pub(crate) use error::FetchError;
pub(crate) use fetch::SystemFetcher;
pub(crate) use manifest::PublicInputs;

use fetch::{check_file, staging_path, CheckoutState, Fetcher, FileCheck};
use manifest::{AfpPin, Distribution};

/// Whether a run may change the work folder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Mode {
    /// Download, check out and rename into place.
    Fetch,
    /// Check what is present; print the rest of the plan.
    Dry,
}

/// What to fetch and where.
#[derive(Debug, Clone)]
pub(crate) struct FetchOptions {
    /// The work folder (already `~`-expanded).
    pub(crate) work_dir: PathBuf,
    /// Input ids to limit the run to; empty means every input.
    pub(crate) only: Vec<String>,
    /// Fetch or dry run.
    pub(crate) mode: Mode,
}

/// How one input ended.
#[derive(Debug)]
pub(crate) enum Outcome {
    /// Already present and matching its pin; nothing was fetched.
    Verified,
    /// Fetched by this run and matching its pin.
    Fetched,
    /// Dry run: what a real run would do.
    Planned(String),
    /// Something else sits where the input belongs; it was left untouched.
    Refused(FetchError),
    /// The input could not be fetched or did not match its pin.
    Failed(FetchError),
}

impl Outcome {
    fn label(&self) -> &'static str {
        match self {
            Outcome::Verified => "VERIFIED",
            Outcome::Fetched => "FETCHED",
            Outcome::Planned(_) => "WOULD FETCH",
            Outcome::Refused(_) => "REFUSED",
            Outcome::Failed(_) => "FAILED",
        }
    }

    fn detail(&self) -> String {
        match self {
            Outcome::Verified => "already present with the pinned checksum".to_string(),
            Outcome::Fetched => "fetched and checked against the pin".to_string(),
            Outcome::Planned(plan) => plan.clone(),
            Outcome::Refused(e) | Outcome::Failed(e) => e.to_string(),
        }
    }

    fn is_verified(&self) -> bool {
        matches!(self, Outcome::Verified | Outcome::Fetched)
    }

    fn is_unverified(&self) -> bool {
        matches!(self, Outcome::Refused(_) | Outcome::Failed(_))
    }
}

/// One input's result.
#[derive(Debug)]
pub(crate) struct ItemReport {
    /// The input id.
    pub(crate) id: String,
    /// How it ended.
    pub(crate) outcome: Outcome,
}

/// Every requested input's result, in manifest order.
#[derive(Debug, Default)]
pub(crate) struct FetchReport {
    /// One entry per requested input.
    pub(crate) items: Vec<ItemReport>,
}

impl FetchReport {
    /// `Ok` when every requested input is VERIFIED, FETCHED or (dry run)
    /// planned.
    ///
    /// # Errors
    /// [`FetchError::Unverified`] naming every FAILED or REFUSED input.
    pub(crate) fn into_result(self) -> Result<(), FetchError> {
        let bad: Vec<&str> = self
            .items
            .iter()
            .filter(|item| item.outcome.is_unverified())
            .map(|item| item.id.as_str())
            .collect();
        if bad.is_empty() {
            return Ok(());
        }
        Err(FetchError::Unverified {
            count: bad.len(),
            ids: bad.join(", "),
        })
    }
}

/// Fetch and check every selected input of `inputs`, writing a per-input
/// report and the manifest's not-fetched list to `out`.
///
/// Per-input problems end up in the returned report (FAILED or REFUSED) and
/// never stop the other inputs; call [`FetchReport::into_result`] for the exit
/// status.
///
/// # Errors
/// [`FetchError::UnknownId`] if `--only` names an id the manifest lacks,
/// [`FetchError::CreateDir`] if the work folder cannot be created, and
/// [`FetchError::Output`] if `out` cannot be written.
pub(crate) fn run_fetch(
    inputs: &PublicInputs,
    opts: &FetchOptions,
    fetcher: &dyn Fetcher,
    out: &mut dyn Write,
) -> Result<FetchReport, FetchError> {
    let known = inputs.ids();
    if let Some(id) = opts.only.iter().find(|id| !known.contains(&id.as_str())) {
        return Err(FetchError::UnknownId {
            id: id.clone(),
            known: known.join(", "),
        });
    }
    let wanted = |id: &str| opts.only.is_empty() || opts.only.iter().any(|o| o == id);

    if opts.mode == Mode::Fetch {
        std::fs::create_dir_all(&opts.work_dir).map_err(|source| FetchError::CreateDir {
            path: opts.work_dir.clone(),
            source,
        })?;
    }
    let dry = if opts.mode == Mode::Dry {
        " (dry run: nothing is downloaded or written)"
    } else {
        ""
    };
    say(
        out,
        &format!(
            "isabelle-fetch: manifest {} (recorded {}), work folder {}{dry}",
            inputs.origin,
            inputs.recorded,
            opts.work_dir.display()
        ),
    )?;

    let mut report = FetchReport::default();
    for dist in inputs
        .distributions
        .iter()
        .filter(|d| wanted(d.id.as_str()))
    {
        let target = opts.work_dir.join(&dist.file);
        say(out, "")?;
        say(out, &format!("{}  {}", dist.id, target.display()))?;
        say(
            out,
            &format!(
                "  pin: {} bytes, sha256 {}, ISABELLE_ID {}",
                dist.bytes, dist.sha256, dist.isabelle_id
            ),
        )?;
        say(out, &format!("  url: {}", dist.url))?;
        say(out, &format!("  used by: {}", dist.used_by))?;
        let outcome = fetch_distribution(dist, &target, opts.mode, fetcher, out)?;
        finish_item(&mut report, out, &dist.id, outcome)?;
    }

    let afp = &inputs.afp;
    if wanted(afp.id.as_str()) {
        let target = opts.work_dir.join(&afp.dir);
        say(out, "")?;
        say(out, &format!("{}  {}", afp.id, target.display()))?;
        say(
            out,
            &format!(
                "  pin: {} at {} ({}), depth {}",
                afp.repo, afp.rev, afp.commit_date, afp.depth
            ),
        )?;
        say(out, &format!("  used by: {}", afp.used_by))?;
        let note = &afp.matching_release_not_used;
        say(
            out,
            &format!(
                "  not fetched: {} at {}. {}",
                note.repo, note.rev, note.note
            ),
        )?;
        let outcome = fetch_afp(afp, &target, opts.mode, fetcher, out)?;
        finish_item(&mut report, out, &afp.id, outcome)?;
    }

    let count = |f: fn(&Outcome) -> bool| report.items.iter().filter(|i| f(&i.outcome)).count();
    say(out, "")?;
    say(
        out,
        &format!(
            "isabelle-fetch: {} input(s): {} verified, {} planned, {} failed or refused",
            report.items.len(),
            count(Outcome::is_verified),
            count(|o| matches!(o, Outcome::Planned(_))),
            count(Outcome::is_unverified),
        ),
    )?;
    write_not_fetched(inputs, out)?;
    Ok(report)
}

fn finish_item(
    report: &mut FetchReport,
    out: &mut dyn Write,
    id: &str,
    outcome: Outcome,
) -> Result<(), FetchError> {
    say(out, &format!("  {}: {}", outcome.label(), outcome.detail()))?;
    report.items.push(ItemReport {
        id: id.to_string(),
        outcome,
    });
    Ok(())
}

fn write_not_fetched(inputs: &PublicInputs, out: &mut dyn Write) -> Result<(), FetchError> {
    say(out, "")?;
    say(
        out,
        &format!(
            "Not fetched by this command ({} item(s); docs/ISABELLE_REIMPORT_RUNBOOK.md has the procedures):",
            inputs.not_fetched.len()
        ),
    )?;
    for item in &inputs.not_fetched {
        say(out, &format!("- {}", item.what))?;
        say(out, &format!("  why: {}", item.why))?;
        say(out, &format!("  how to get it: {}", item.how_to_get_it))?;
    }
    Ok(())
}

fn say(out: &mut dyn Write, line: &str) -> Result<(), FetchError> {
    writeln!(out, "{line}")
        .and_then(|()| out.flush())
        .map_err(|source| FetchError::Output { source })
}

/// Check one archive; in a real run, download it when it is missing or
/// differs. Only a report write failure is an `Err`.
fn fetch_distribution(
    dist: &Distribution,
    target: &Path,
    mode: Mode,
    fetcher: &dyn Fetcher,
    out: &mut dyn Write,
) -> Result<Outcome, FetchError> {
    let why = match check_file(target, dist.bytes, &dist.sha256) {
        Ok(FileCheck::Match) => return Ok(Outcome::Verified),
        Ok(FileCheck::Missing) => "absent".to_string(),
        Ok(FileCheck::Differs(actual)) => format!("present but differs ({actual})"),
        Err(e @ FetchError::NotAFile { .. }) => return Ok(Outcome::Refused(e)),
        Err(e) => return Ok(Outcome::Failed(e)),
    };
    let part = staging_path(target);
    if mode == Mode::Dry {
        return Ok(Outcome::Planned(format!(
            "{why}; a real run downloads {} to {}, checks size and sha256, and renames it to {}",
            dist.url,
            part.display(),
            target.display()
        )));
    }
    say(out, &format!("  {why}; downloading to {}", part.display()))?;
    if let Err(e) = fetcher.download(&dist.url, &part) {
        remove_staged_file(&part, out)?;
        return Ok(Outcome::Failed(e));
    }
    let outcome = match check_file(&part, dist.bytes, &dist.sha256) {
        Ok(FileCheck::Match) => {
            return Ok(match std::fs::rename(&part, target) {
                Ok(()) => Outcome::Fetched,
                Err(source) => {
                    remove_staged_file(&part, out)?;
                    Outcome::Failed(FetchError::Io {
                        path: target.to_path_buf(),
                        source,
                    })
                }
            });
        }
        Ok(FileCheck::Missing) => Outcome::Failed(FetchError::Download {
            url: dist.url.clone(),
            status: "exit status 0".to_string(),
            detail: format!(
                "curl reported success but {} does not exist",
                part.display()
            ),
        }),
        Ok(FileCheck::Differs(actual)) => Outcome::Failed(FetchError::Mismatch {
            path: target.to_path_buf(),
            expected_bytes: dist.bytes,
            expected_sha256: dist.sha256.clone(),
            actual,
        }),
        Err(e) => Outcome::Failed(e),
    };
    remove_staged_file(&part, out)?;
    Ok(outcome)
}

/// Delete a staged download. A failure to delete is reported, not fatal.
fn remove_staged_file(part: &Path, out: &mut dyn Write) -> Result<(), FetchError> {
    match std::fs::remove_file(part) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => say(
            out,
            &format!(
                "  could not delete {}: {e}; delete it by hand",
                part.display()
            ),
        ),
    }
}

/// Delete a staging directory this command made. A failure to delete is
/// reported, not fatal.
fn remove_staged_dir(staging: &Path, out: &mut dyn Write) -> Result<(), FetchError> {
    match std::fs::remove_dir_all(staging) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => say(
            out,
            &format!(
                "  could not delete {}: {e}; delete it by hand",
                staging.display()
            ),
        ),
    }
}

/// Check the AFP checkout; in a real run, fetch it when it is absent. Only a
/// report write failure is an `Err`.
fn fetch_afp(
    afp: &AfpPin,
    target: &Path,
    mode: Mode,
    fetcher: &dyn Fetcher,
    out: &mut dyn Write,
) -> Result<Outcome, FetchError> {
    if std::fs::symlink_metadata(target).is_ok() {
        return Ok(judge_existing(afp, target, fetcher));
    }
    let staging = staging_path(target);
    if mode == Mode::Dry {
        return Ok(Outcome::Planned(format!(
            "absent; a real run makes {} with git init, fetches {} from {} at depth {}, \
             checks it out detached, confirms HEAD, and renames it to {}",
            staging.display(),
            afp.rev,
            afp.repo,
            afp.depth,
            target.display()
        )));
    }
    say(
        out,
        &format!(
            "  absent; fetching {} into {} (a leftover staging checkout there is replaced)",
            afp.rev,
            staging.display()
        ),
    )?;
    if let Ok(meta) = std::fs::symlink_metadata(&staging) {
        let cleared = if meta.is_dir() {
            std::fs::remove_dir_all(&staging)
        } else {
            std::fs::remove_file(&staging)
        };
        if let Err(source) = cleared {
            return Ok(Outcome::Failed(FetchError::Io {
                path: staging,
                source,
            }));
        }
    }
    if let Err(source) = std::fs::create_dir_all(&staging) {
        return Ok(Outcome::Failed(FetchError::CreateDir {
            path: staging,
            source,
        }));
    }
    if let Err(e) = fetcher.checkout_rev(&afp.repo, &afp.rev, afp.depth, &staging) {
        remove_staged_dir(&staging, out)?;
        return Ok(Outcome::Failed(e));
    }
    let outcome = match fetcher.inspect_checkout(&staging) {
        Ok(CheckoutState::At {
            head,
            tracked_changes: false,
        }) if head == afp.rev => {
            return Ok(match std::fs::rename(&staging, target) {
                Ok(()) => Outcome::Fetched,
                Err(source) => {
                    remove_staged_dir(&staging, out)?;
                    Outcome::Failed(FetchError::Io {
                        path: target.to_path_buf(),
                        source,
                    })
                }
            });
        }
        Ok(state) => Outcome::Failed(FetchError::AfpFetchedWrongRev {
            dir: staging.clone(),
            head: match state {
                CheckoutState::At {
                    head,
                    tracked_changes,
                } if tracked_changes => format!("{head} with modified tracked files"),
                CheckoutState::At { head, .. } => head,
                CheckoutState::NoHead => "no commit".to_string(),
                CheckoutState::NotACheckout => "no git checkout".to_string(),
            },
            rev: afp.rev.clone(),
        }),
        Err(e) => Outcome::Failed(e),
    };
    remove_staged_dir(&staging, out)?;
    Ok(outcome)
}

/// Judge an AFP directory that already exists. Never changes it.
fn judge_existing(afp: &AfpPin, target: &Path, fetcher: &dyn Fetcher) -> Outcome {
    let dir = target.to_path_buf();
    match fetcher.inspect_checkout(target) {
        Err(e) => Outcome::Failed(e),
        Ok(CheckoutState::NotACheckout) => Outcome::Refused(FetchError::AfpNotACheckout { dir }),
        Ok(CheckoutState::NoHead) => Outcome::Refused(FetchError::AfpNoHead { dir }),
        Ok(CheckoutState::At { head, .. }) if head != afp.rev => {
            Outcome::Refused(FetchError::AfpOtherRev {
                dir,
                head,
                rev: afp.rev.clone(),
            })
        }
        Ok(CheckoutState::At {
            tracked_changes: true,
            ..
        }) => Outcome::Refused(FetchError::AfpModified {
            dir,
            rev: afp.rev.clone(),
        }),
        Ok(CheckoutState::At { .. }) => Outcome::Verified,
    }
}
