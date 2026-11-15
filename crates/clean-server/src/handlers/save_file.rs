// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! How `saveEnvironment` writes its file: whole, or not at all.
//!
//! # Why
//!
//! A save wrote its file with `fs::write`, which truncates the file and then
//! writes it. Anything that stopped the write partway (the process killed, a
//! full disk, the file-size limit, an I/O error) left the file torn: neither
//! the environment it held nor the one being saved, and a `loadEnvironment` of
//! it fails. Two saves of one path (a retried save, and the first one still
//! writing past its timeout) wrote into the same file at once (R36's open
//! items).
//!
//! # What a save does now
//!
//! It writes a temporary file beside the target (in the same directory, so
//! the rename below never crosses a file system), created with the old file's
//! permissions, flushes it to the disk (`fsync`), and renames it over the
//! target, which replaces the target in one step; then it flushes the
//! directory, so the rename itself survives a crash. A reader of the path sees
//! the old file or the whole new one, never a part. A save that fails, or
//! that may not commit, removes its temporary file and leaves the target as it
//! was. Two saves of one path write two temporary files, and the later rename
//! wins.
//!
//! Whether a save may commit is decided once, by whichever comes first: the
//! save, as it is about to rename, or its request, as it stops waiting
//! ([`Commit`]). A request that stops waiting first answers the timeout error
//! and the save never renames; a save that comes first renames, and its
//! request waits for it and answers what became of the file. So the timeout
//! error always means the file is as it was, and a success always means it was
//! replaced, or created where nothing was (review of 2026-10-18: the save read
//! the deadline before it renamed, but the request's timer was its own, and a
//! save that read the deadline just before it passed renamed after its request
//! had answered the timeout error).
//!
//! Kept as before, deliberately: a path that names something other than a
//! regular file (a named pipe, a device), through any symbolic links, is
//! written in place, because renaming over it would replace it with a regular
//! file; nothing old can be torn there, and a request is never kept waiting
//! for a reader of a pipe, so a pipe may have been written to after its
//! request answered the timeout error. A path that can name no new file (one
//! that ends in a separator, `.` or `..`, or the empty path) goes to
//! `fs::write` too, which refuses it as before and writes nothing (renaming a
//! temporary file over it fails, but only after the whole temporary file is
//! written). A file the server may not write is refused, as `fs::write`'s open
//! refused it, although the rename would only need the directory.
//!
//! A symbolic link is followed, through every link it names in turn, to the
//! path the last one names ([`named_file`]): the file there is replaced, or
//! created when nothing is there, by the steps above, and the links stay
//! links. A link that names nothing was written through with `fs::write`
//! (`fs::canonicalize` answers only for a path that exists): before its
//! deadline was read and without the commit, so it answered the timeout error
//! and then created its file, and a write cut short left that file torn
//! (review of 2026-10-19).
//!
//! What changes: the saved file is a new file, so another hard link to the
//! old one keeps the old contents, and the file belongs to the server's user.
//! The directory must be writable (the temporary file is created there): a
//! save of a writable file in a directory the server may not write is refused,
//! where `fs::write` wrote the file in place. A crash between creating the
//! temporary file and the rename can leave the temporary file behind
//! (`.<name>.<pid>.<n>.saving`, beside the target, with the name cut to
//! [`NAME_PREFIX_BYTES`] so the temporary name stays short); the target is
//! intact. In a directory with the sticky bit (`/tmp`), a writable file that
//! belongs to another user was written in place, but only its owner may
//! rename over it, so such a save is refused now (analysis, review of
//! 2026-10-19; it needs a second user to run).

use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, AtomicU8, Ordering};

use super::work::deadline_passed_now;

/// Temporary files this process has named, so two saves never share one.
static TEMPORARIES: AtomicU64 = AtomicU64::new(0);

/// The most bytes of the target's name a temporary file's name repeats: the
/// rest of that name is at most 40 bytes (a dot, the process id, a counter,
/// `.saving`), so a target whose name is at the file system's limit (255
/// bytes) still gets a temporary file.
pub(crate) const NAME_PREFIX_BYTES: usize = 32;

/// Neither side has decided yet.
const UNDECIDED: u8 = 0;
/// The save has begun replacing the file.
const COMMITTED: u8 = 1;
/// The request stopped waiting first: the save never replaces the file.
const ABANDONED: u8 = 2;

/// Whether a save may replace its file, decided once by whichever comes
/// first: the save as it is about to rename ([`Commit::take`]), or its request
/// as it stops waiting ([`Commit::abandon`]). The module's notes say why.
#[derive(Debug, Default)]
pub(crate) struct Commit(AtomicU8);

impl Commit {
    /// The save's side, just before it renames: whether it may. `false` once
    /// the request has stopped waiting.
    fn take(&self) -> bool {
        self.0
            .compare_exchange(UNDECIDED, COMMITTED, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
    }

    /// The request's side, as it stops waiting (its timeout fired, or it was
    /// cancelled): whether the save will now never replace the file. `false`
    /// means the save has begun replacing it, and its answer says how that
    /// ended.
    pub(crate) fn abandon(&self) -> bool {
        match self
            .0
            .compare_exchange(UNDECIDED, ABANDONED, Ordering::AcqRel, Ordering::Acquire)
        {
            Ok(_) => true,
            Err(decided) => decided == ABANDONED,
        }
    }
}

/// Why a save wrote nothing to its path.
#[derive(Debug)]
pub(crate) enum SaveError {
    /// The request's deadline passed before the save committed; the path is
    /// as it was.
    Interrupted,
    /// The request stopped waiting before the save committed; the path is as
    /// it was.
    Abandoned,
    /// The file system refused a step; the path is as it was (for a regular
    /// file).
    Io(String),
}

impl std::fmt::Display for SaveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Interrupted => f.write_str("the save's deadline passed before it committed"),
            Self::Abandoned => {
                f.write_str("the save's request stopped waiting before it committed")
            }
            Self::Io(detail) => f.write_str(detail),
        }
    }
}

fn io(step: &str, path: &Path, error: &std::io::Error) -> SaveError {
    SaveError::Io(format!("{step} {}: {error}", path.display()))
}

/// Write `data` to `path` whole or not at all (the module's notes). For a
/// regular file, or a path where nothing is yet, it reads the deadline of the
/// work it runs in (`run_until`) before it starts and before it commits; past
/// it, it writes nothing and answers [`SaveError::Interrupted`], with the
/// deadline latched. It commits only if it takes `commit` before its request
/// abandons it ([`SaveError::Abandoned`] otherwise). A pipe or a device is
/// written in place, deadline or not, as before.
pub(crate) fn save_file(path: &Path, data: &[u8], commit: &Commit) -> Result<(), SaveError> {
    let target = named_file(path)?;
    if names_no_new_file(&target) {
        // `fs::write` refuses it, writing nothing: no file can be created
        // there, and a directory cannot be opened for writing.
        return write_in_place(path, data);
    }
    let old = match fs::metadata(&target) {
        // A pipe, a device: renaming over it would replace it with a file.
        Ok(meta) if !meta.is_file() => return write_in_place(path, data),
        Ok(meta) => Some(meta.permissions()),
        Err(_) => None,
    };
    if old.is_some() {
        // `fs::write` opened the file for writing, so a file the server may
        // not write was refused. A rename over it needs only the directory's
        // permission: ask the file's own, without truncating it.
        OpenOptions::new()
            .write(true)
            .open(&target)
            .map_err(|e| io("cannot write", &target, &e))?;
    }
    // Past its deadline, a save creates no file (its answer is dropped).
    if deadline_passed_now() {
        return Err(SaveError::Interrupted);
    }
    let (temporary, file) = create_temporary(&target, old.as_ref())?;
    if let Err(error) = fill_and_commit(file, &temporary, data, &target, commit) {
        let _ = fs::remove_file(&temporary);
        return Err(error);
    }
    sync_directory(&target);
    Ok(())
}

/// The most symbolic links a save follows from its path (macOS's limit;
/// Linux's is 40). A longer chain is refused. The count is of the links a
/// save follows itself, each the last name of the path it reaches; the system
/// also counts the links in the directories along the way, so near the limit
/// a chain it refuses may be followed here (review of 2026-10-19: one of 25
/// layouts, 32 links reached through `/var`, which is a link).
const MAX_LINKS: usize = 32;

/// The path of the file a save of `path` writes: `path`, or, when it is a
/// symbolic link, the path it names, followed through each link in turn,
/// whether or not anything is there yet. A link's relative contents are
/// relative to the link's directory, as when it is opened, and are joined to
/// that directory's real path (it exists: the link is in it), so the path
/// stays as short as the system's own reading of it. Joined to the directory
/// as written, each relative link of a chain lengthened the path, and a chain
/// the system follows was refused as `File name too long` (review of
/// 2026-10-19: 30 links, each in a directory with a 60-byte name, at the
/// 14th).
fn named_file(path: &Path) -> Result<PathBuf, SaveError> {
    let mut named = path.to_path_buf();
    let mut followed = 0;
    loop {
        match fs::symlink_metadata(&named) {
            Ok(meta) if meta.file_type().is_symlink() => {
                if followed == MAX_LINKS {
                    return Err(SaveError::Io(format!(
                        "cannot write {}: more than {MAX_LINKS} symbolic links to follow",
                        path.display()
                    )));
                }
                followed += 1;
                let next =
                    fs::read_link(&named).map_err(|e| io("cannot read the link", &named, &e))?;
                named = if next.is_relative() {
                    let directory = directory_of(&named);
                    // Should the real path not be found, the path as written
                    // names the same directory.
                    fs::canonicalize(directory)
                        .unwrap_or_else(|_| directory.to_path_buf())
                        .join(next)
                } else {
                    next
                };
            }
            _ => return Ok(named),
        }
    }
}

/// Whether `path` can name no new file: its last component, as written, is
/// empty (it ends in a separator, or it is the empty path), `.` or `..`.
fn names_no_new_file(path: &Path) -> bool {
    let written = path.as_os_str().to_string_lossy();
    let last = written.rsplit(std::path::is_separator).next().unwrap_or("");
    matches!(last, "" | "." | "..")
}

/// Write `data` to the temporary file, flush it, and rename it over `target`
/// unless the deadline has passed or the request has abandoned the save.
fn fill_and_commit(
    mut file: File,
    temporary: &Path,
    data: &[u8],
    target: &Path,
    commit: &Commit,
) -> Result<(), SaveError> {
    // A test may make the deadline pass while the save writes (`seam::expire`).
    #[cfg(test)]
    let expired = seam::reached(target, seam::Step::Created);
    #[cfg(not(test))]
    let expired = false;
    file.write_all(data)
        .map_err(|e| io("cannot write", temporary, &e))?;
    file.sync_all()
        .map_err(|e| io("cannot flush", temporary, &e))?;
    drop(file);
    // A save whose deadline passed while it wrote never commits: it answers
    // the timeout error, where the commit alone would let it rename (and its
    // request wait for that) whenever its request had not yet stopped waiting.
    if expired || deadline_passed_now() {
        return Err(SaveError::Interrupted);
    }
    #[cfg(test)]
    let _ = seam::reached(target, seam::Step::BeforeCommit);
    if !commit.take() {
        return Err(SaveError::Abandoned);
    }
    #[cfg(test)]
    let _ = seam::reached(target, seam::Step::Committing);
    fs::rename(temporary, target).map_err(|e| io("cannot rename over", target, &e))
}

fn write_in_place(path: &Path, data: &[u8]) -> Result<(), SaveError> {
    fs::write(path, data).map_err(|e| io("cannot write", path, &e))
}

/// A new file beside `target`, named for this process and a counter, created
/// only if nothing has that name (so it never opens someone else's file), with
/// the old file's permissions (`old`) from its creation on: the new contents
/// are never readable by anyone the old file's were not.
fn create_temporary(
    target: &Path,
    old: Option<&fs::Permissions>,
) -> Result<(PathBuf, File), SaveError> {
    let name = target
        .file_name()
        .ok_or_else(|| SaveError::Io(format!("{} names no file", target.display())))?;
    let name = name.to_string_lossy();
    let prefix = &name[..floor_char_boundary(&name, NAME_PREFIX_BYTES)];
    let directory = directory_of(target);
    loop {
        let n = TEMPORARIES.fetch_add(1, Ordering::Relaxed);
        let temporary = directory.join(format!(".{prefix}.{}.{n}.saving", std::process::id()));
        let mut options = OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        if let Some(old) = old {
            use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
            // Created no more readable than the old file (the umask can only
            // take bits away); its exact mode is set below.
            options.mode(old.mode() & 0o777);
        }
        match options.open(&temporary) {
            Ok(file) => {
                if let Some(old) = old {
                    if let Err(e) = file.set_permissions(old.clone()) {
                        let _ = fs::remove_file(&temporary);
                        return Err(io("cannot set the permissions of", &temporary, &e));
                    }
                }
                return Ok((temporary, file));
            }
            // Left by an earlier process with this one's id: take the next.
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
            // No such directory: refused as `fs::write` refused it.
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                return Err(io("cannot write", target, &e))
            }
            Err(e) => {
                return Err(SaveError::Io(format!(
                    "cannot create {} to replace {} with (a save writes a new file beside \
                     its target and renames it over the target, so the directory must be \
                     writable): {e}",
                    temporary.display(),
                    target.display()
                )))
            }
        }
    }
}

/// The largest index at most `at` that is a character boundary of `text`.
fn floor_char_boundary(text: &str, at: usize) -> usize {
    if at >= text.len() {
        return text.len();
    }
    (0..=at)
        .rev()
        .find(|&i| text.is_char_boundary(i))
        .unwrap_or(0)
}

fn directory_of(target: &Path) -> &Path {
    match target.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent,
        _ => Path::new("."),
    }
}

/// Flush `target`'s directory, so the rename survives a crash. Best effort:
/// the file is in place already, and some file systems refuse to flush a
/// directory.
fn sync_directory(target: &Path) {
    #[cfg(unix)]
    {
        let directory = directory_of(target);
        if let Err(error) = File::open(directory).and_then(|d| d.sync_all()) {
            tracing::warn!(
                directory = %directory.display(),
                %error,
                "a save could not flush its directory"
            );
        }
    }
    #[cfg(not(unix))]
    let _ = target;
}

/// Where a test pauses a save of one path, to order it against its request
/// (`handlers/tests/save_file.rs`), or makes its deadline pass.
#[cfg(test)]
pub(crate) mod seam {
    use std::path::{Path, PathBuf};
    use std::sync::{mpsc, Mutex, PoisonError};

    /// A step of a save of a regular file.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) enum Step {
        /// The temporary file exists, with nothing written to it.
        Created,
        /// The temporary file is whole and flushed, and the deadline had not
        /// passed; the save has not decided whether it commits.
        BeforeCommit,
        /// The save has taken its commit and is about to rename.
        Committing,
    }

    struct Pause {
        path: PathBuf,
        step: Step,
        reached: tokio::sync::oneshot::Sender<()>,
        /// `None`: the save goes on at once.
        release: Option<mpsc::Receiver<()>>,
        /// The save finds its deadline passed from this step on.
        expires: bool,
    }

    static PAUSES: Mutex<Vec<Pause>> = Mutex::new(Vec::new());

    fn add(
        path: &Path,
        step: Step,
        release: Option<mpsc::Receiver<()>>,
        expires: bool,
    ) -> tokio::sync::oneshot::Receiver<()> {
        let (reached, at) = tokio::sync::oneshot::channel();
        PAUSES
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(Pause {
                path: path.to_path_buf(),
                step,
                reached,
                release,
                expires,
            });
        at
    }

    /// Pause the next save of `path` at `step`: the first receiver answers
    /// when the save gets there, and the save goes on when the sender sends
    /// (or is dropped).
    pub(crate) fn pause(
        path: &Path,
        step: Step,
    ) -> (tokio::sync::oneshot::Receiver<()>, mpsc::Sender<()>) {
        let (go, release) = mpsc::channel();
        (add(path, step, Some(release), false), go)
    }

    /// The next save of `path` finds its deadline passed from `step` on, as
    /// if it had passed there; the receiver answers when the save got there.
    pub(crate) fn expire(path: &Path, step: Step) -> tokio::sync::oneshot::Receiver<()> {
        add(path, step, None, true)
    }

    /// Take back what [`pause`] or [`expire`] set for `path` at `step`:
    /// `true` when it was still waiting, so no save of `path` got there.
    pub(crate) fn withdraw(path: &Path, step: Step) -> bool {
        let mut pauses = PAUSES.lock().unwrap_or_else(PoisonError::into_inner);
        let before = pauses.len();
        pauses.retain(|pause| !(pause.path == path && pause.step == step));
        pauses.len() != before
    }

    /// A save of `path` got to `step`: wait there if a test asked it to.
    /// `true` when the test made its deadline pass here.
    pub(super) fn reached(path: &Path, step: Step) -> bool {
        let pause = {
            let mut pauses = PAUSES.lock().unwrap_or_else(PoisonError::into_inner);
            pauses
                .iter()
                .position(|pause| pause.path == path && pause.step == step)
                .map(|at| pauses.remove(at))
        };
        let Some(pause) = pause else {
            return false;
        };
        let _ = pause.reached.send(());
        if let Some(release) = pause.release {
            let _ = release.recv();
        }
        pause.expires
    }
}
