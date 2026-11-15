// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! File acquisition, not proof authority. All data comes from one opened
//! regular descriptor, bounded by its original length. An explicit caller may
//! additionally bound the complete graph; ordinary imports gain no fixed cap.

use crate::import::runtime::RuntimeExtractionLimits;
use crate::import::{deadline, ImportError};
use std::fs::{File, Metadata, OpenOptions};
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::time::SystemTime;

/// Explicit acquisition policy for one checked graph, including every present
/// base, server, private and IR part, even on a decoded-cache hit.
///
/// The byte fields reuse the runtime extractor's policy shape, but this reader
/// enforces them BEFORE allocation. These are capture limits, not bounds on
/// subsequent kernel work or import authority. No default policy is installed
/// on ordinary loaders. `max_modules` also bounds the initial root selectors;
/// `max_imports` counts every present base/server/private header row, including
/// cumulative duplicates, before row decoding or cache lookup. Companion
/// pointer-space assembly retains the parser's existing finite gap bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ModuleCaptureLimits {
    pub bytes: RuntimeExtractionLimits,
    pub max_modules: usize,
    pub max_imports: usize,
}

impl ModuleCaptureLimits {
    pub const fn new(
        max_part_bytes: usize,
        max_captured_bytes: usize,
        max_modules: usize,
        max_imports: usize,
    ) -> Self {
        Self {
            bytes: RuntimeExtractionLimits {
                max_part_bytes,
                max_captured_bytes,
            },
            max_modules,
            max_imports,
        }
    }
}

#[derive(Default)]
pub(in crate::import) struct CaptureBudget {
    limits: Option<ModuleCaptureLimits>,
    bytes: usize,
    modules: usize,
    imports: usize,
}

fn resource(reason: String) -> ImportError {
    ImportError::ResourceLimit {
        operation: "capturing the module graph".into(),
        reason,
    }
}

impl CaptureBudget {
    pub(in crate::import) fn new(limits: Option<ModuleCaptureLimits>) -> Self {
        Self {
            limits,
            ..Self::default()
        }
    }

    pub(in crate::import) fn check_roots(&self, count: usize) -> Result<(), ImportError> {
        if let Some(limits) = self.limits {
            if count > limits.max_modules {
                return Err(resource(format!(
                    "{count} root selectors exceed the {} module limit",
                    limits.max_modules
                )));
            }
        }
        Ok(())
    }

    pub(in crate::import) fn module(&mut self) -> Result<(), ImportError> {
        if let Some(limits) = self.limits {
            self.modules = self
                .modules
                .checked_add(1)
                .filter(|count| *count <= limits.max_modules)
                .ok_or_else(|| resource(format!("module limit {} exceeded", limits.max_modules)))?;
        }
        Ok(())
    }

    pub(in crate::import) fn imports(&mut self, count: usize) -> Result<(), ImportError> {
        if let Some(limits) = self.limits {
            self.imports = self
                .imports
                .checked_add(count)
                .filter(|count| *count <= limits.max_imports)
                .ok_or_else(|| {
                    resource(format!("import-row limit {} exceeded", limits.max_imports))
                })?;
        }
        Ok(())
    }

    fn admit_length(&self, length: usize) -> io::Result<()> {
        if let Some(limits) = self.limits {
            if length > limits.bytes.max_part_bytes {
                return Err(invalid(format!(
                    "part has {length} bytes, capture limit is {}",
                    limits.bytes.max_part_bytes
                )));
            }
            if self
                .bytes
                .checked_add(length)
                .is_none_or(|sum| sum > limits.bytes.max_captured_bytes)
            {
                return Err(invalid(format!(
                    "part of {length} bytes exceeds remaining graph capture budget ({} used, {} limit)",
                    self.bytes, limits.bytes.max_captured_bytes
                )));
            }
        }
        Ok(())
    }

    fn consume(&mut self, length: usize) -> io::Result<()> {
        self.admit_length(length)?;
        if self.limits.is_some() {
            self.bytes = self
                .bytes
                .checked_add(length)
                .ok_or_else(|| invalid("captured byte count overflow"))?;
        }
        Ok(())
    }
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn unreadable(path: &Path, source: io::Error) -> ImportError {
    ImportError::FileUnreadable {
        path: path.to_path_buf(),
        source,
    }
}

/// This is an instability check only. Content hashes, never timestamps, remain
/// the decoded-cache identity. The Unix descriptor identity includes ctime so
/// restoring an mtime does not hide an in-place rewrite during capture.
#[derive(PartialEq, Eq)]
struct Stamp {
    length: u64,
    modified: Option<SystemTime>,
    #[cfg(unix)]
    unix: (u64, u64, i64, i64, i64, i64),
}

impl Stamp {
    fn of(metadata: &Metadata) -> Self {
        #[cfg(unix)]
        use std::os::unix::fs::MetadataExt;
        Self {
            length: metadata.len(),
            modified: metadata.modified().ok(),
            #[cfg(unix)]
            unix: (
                metadata.dev(),
                metadata.ino(),
                metadata.mtime(),
                metadata.mtime_nsec(),
                metadata.ctime(),
                metadata.ctime_nsec(),
            ),
        }
    }
}

struct OpenedPart {
    file: File,
    path: PathBuf,
    initial: Stamp,
    length: usize,
}

impl OpenedPart {
    fn from_file(file: File, path: &Path, budget: &CaptureBudget) -> io::Result<Self> {
        let metadata = file.metadata()?;
        if !metadata.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "module capture requires an opened regular file",
            ));
        }
        let length = usize::try_from(metadata.len())
            .map_err(|_| invalid("module part length does not fit this process"))?;
        budget.admit_length(length)?;
        Ok(Self {
            file,
            path: path.to_path_buf(),
            initial: Stamp::of(&metadata),
            length,
        })
    }

    fn read(mut self, budget: &mut CaptureBudget) -> Result<Vec<u8>, ImportError> {
        deadline::check()?;
        let current = self
            .file
            .metadata()
            .map_err(|error| unreadable(&self.path, error))?;
        if Stamp::of(&current) != self.initial {
            return Err(unreadable(
                &self.path,
                invalid("module part changed before capture"),
            ));
        }
        let mut bytes = Vec::new();
        bytes.try_reserve_exact(self.length).map_err(|error| {
            unreadable(
                &self.path,
                io::Error::other(format!("module capture allocation failed: {error}")),
            )
        })?;
        let mut chunk = [0u8; 64 * 1024];
        while bytes.len() < self.length {
            deadline::check()?;
            let wanted = chunk.len().min(self.length - bytes.len());
            match self.file.read(&mut chunk[..wanted]) {
                Ok(0) => {
                    return Err(unreadable(
                        &self.path,
                        io::Error::new(
                            io::ErrorKind::UnexpectedEof,
                            "module part shrank during capture",
                        ),
                    ))
                }
                Ok(count) => bytes.extend_from_slice(&chunk[..count]),
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                Err(error) => return Err(unreadable(&self.path, error)),
            }
        }
        // One byte detects growth without growing the admitted allocation.
        let mut extra = [0];
        loop {
            deadline::check()?;
            match self.file.read(&mut extra) {
                Ok(0) => break,
                Ok(_) => {
                    return Err(unreadable(
                        &self.path,
                        invalid("module part grew during capture"),
                    ))
                }
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                Err(error) => return Err(unreadable(&self.path, error)),
            }
        }
        let after = self
            .file
            .metadata()
            .map_err(|error| unreadable(&self.path, error))?;
        if Stamp::of(&after) != self.initial {
            return Err(unreadable(
                &self.path,
                invalid("module part changed during capture"),
            ));
        }
        budget
            .consume(bytes.len())
            .map_err(|error| unreadable(&self.path, error))?;
        Ok(bytes)
    }
}

fn open(path: &Path) -> io::Result<File> {
    let mut options = OpenOptions::new();
    options.read(true);
    // A pathname can become a FIFO after its caller's pre-stat. Opening
    // nonblocking and checking the resulting descriptor closes that race.
    // Regular symlink aliases remain supported; their target must be regular.
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NONBLOCK);
    }
    options.open(path)
}

pub(super) fn required(path: &Path, budget: &mut CaptureBudget) -> Result<Vec<u8>, ImportError> {
    let file = open(path).map_err(|error| unreadable(path, error))?;
    OpenedPart::from_file(file, path, budget)
        .map_err(|error| unreadable(path, error))?
        .read(budget)
}

pub(super) fn optional(
    path: &Path,
    budget: &mut CaptureBudget,
) -> Result<Option<Vec<u8>>, ImportError> {
    match open(path) {
        Ok(file) => OpenedPart::from_file(file, path, budget)
            .map_err(|error| unreadable(path, error))?
            .read(budget)
            .map(Some),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            // Match the existing absence policy: a dangling symlink is present
            // but unreadable, not a missing optional companion.
            match std::fs::symlink_metadata(path) {
                Err(absent) if absent.kind() == io::ErrorKind::NotFound => Ok(None),
                _ => Err(unreadable(path, error)),
            }
        }
        Err(error) => Err(unreadable(path, error)),
    }
}

#[cfg(test)]
mod tests;
