// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

struct Table {
    strings: Vec<Vec<u8>>,
    version: u32,
    blank_debug_files: bool,
}
pub(super) struct Builder(Table);
pub(super) struct SealedPool(Table);

impl Builder {
    pub(super) fn new(blank_debug_files: bool) -> Self {
        Self(Table {
            strings: Vec::new(),
            version: BASE_FORMAT_VERSION,
            blank_debug_files,
        })
    }
    pub(super) fn raise_to(&mut self, version: u32) {
        self.0.version = self.0.version.max(version);
    }
    pub(super) fn debug_file<'p>(&self, path: &'p str) -> &'p str {
        self.0.debug_file(path)
    }
    pub(super) fn seal(self) -> SealedPool {
        SealedPool(self.0)
    }
    pub(super) fn retire<O: ExecutionObserver>(self, out: &mut Output<'_, '_, O>) {
        self.0.retire(out);
    }
    pub(super) fn intern<O: ExecutionObserver>(
        &mut self,
        text: &str,
        out: &mut Output<'_, '_, O>,
    ) -> R<u64> {
        if let Some(index) = self.0.find(text.as_bytes(), out)? {
            return Ok(index);
        }
        let index = u64::try_from(self.0.strings.len())
            .map_err(|_| ObservedValueError::CapacityOverflow)?;
        let mut owned = Vec::new();
        let result = (|| {
            for chunk in text.as_bytes().chunks(1024) {
                out.reserve(&mut owned, chunk.len())?;
                out.admit(chunk.len(), chunk.len())?;
                owned.extend_from_slice(chunk);
            }
            out.reserve(&mut self.0.strings, 1)?;
            out.admit(1, core::mem::size_of::<Vec<u8>>())?;
            self.0.strings.push(core::mem::take(&mut owned));
            Ok(index)
        })();
        out.finish_child(result, owned)
    }
}
impl SealedPool {
    pub(super) fn strings(&self) -> &[Vec<u8>] {
        &self.0.strings
    }
    pub(super) fn minimum_version(&self) -> u32 {
        self.0.version
    }
    pub(super) fn debug_file<'p>(&self, path: &'p str) -> &'p str {
        self.0.debug_file(path)
    }
    pub(super) fn id_of<O: ExecutionObserver>(
        &self,
        text: &str,
        out: &mut Output<'_, '_, O>,
    ) -> R<u64> {
        self.0
            .find(text.as_bytes(), out)?
            .ok_or(ObservedValueError::UnsupportedValue)
    }
    pub(super) fn retire<O: ExecutionObserver>(self, out: &mut Output<'_, '_, O>) {
        self.0.retire(out);
    }
}
impl Table {
    fn debug_file<'p>(&self, path: &'p str) -> &'p str {
        if self.blank_debug_files { "" } else { path }
    }
    fn find<O: ExecutionObserver>(
        &self,
        text: &[u8],
        out: &mut Output<'_, '_, O>,
    ) -> R<Option<u64>> {
        out.poll()?;
        for (index, known) in self.strings.iter().enumerate() {
            out.poll()?;
            if known.len() != text.len() {
                continue;
            }
            let mut equal = true;
            for (left, right) in known.chunks(1024).zip(text.chunks(1024)) {
                out.admit(
                    left.len()
                        .checked_add(right.len())
                        .ok_or(ObservedValueError::CapacityOverflow)?,
                    0,
                )?;
                if left != right {
                    equal = false;
                    break;
                }
            }
            if equal {
                return Ok(Some(
                    u64::try_from(index).map_err(|_| ObservedValueError::CapacityOverflow)?,
                ));
            }
        }
        Ok(None)
    }
    fn retire<O: ExecutionObserver>(mut self, out: &mut Output<'_, '_, O>) {
        while !self.strings.is_empty() {
            out.retirement_poll();
            if let Some(value) = self.strings.pop() {
                out.retire(value);
            }
        }
        out.retire(self.strings);
    }
}
