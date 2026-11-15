// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
}

impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn admit(&mut self, work: usize, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }

    pub(super) fn text(&mut self, mut a: &[u8], mut b: &[u8]) -> R<bool> {
        self.admit(1, 2 * size_of::<&[u8]>())?;
        if a.len() != b.len() {
            return Ok(false);
        }
        loop {
            self.admit(1, size_of::<usize>())?;
            if a.is_empty() {
                return Ok(true);
            }
            // Equality is byte identity; chunk endpoints need not be UTF8
            // boundaries. Both slices have equal length throughout this loop.
            let count = a.len().min(1024);
            self.admit(2 * count + 2, 2 * size_of::<&[u8]>())?;
            if a[..count] != b[..count] {
                return Ok(false);
            }
            a = &a[count..];
            b = &b[count..];
        }
    }

    pub(super) fn strings(&mut self, mut a: &[String], mut b: &[String]) -> R<bool> {
        self.admit(1, 2 * size_of::<&[String]>())?;
        if a.len() != b.len() {
            return Ok(false);
        }
        loop {
            self.admit(1, 2 * size_of::<Option<(&String, &[String])>>())?;
            let (Some((left, rest_a)), Some((right, rest_b))) = (a.split_first(), b.split_first())
            else {
                return Ok(true);
            };
            if !self.text(left.as_bytes(), right.as_bytes())? {
                return Ok(false);
            }
            a = rest_a;
            b = rest_b;
        }
    }
}
