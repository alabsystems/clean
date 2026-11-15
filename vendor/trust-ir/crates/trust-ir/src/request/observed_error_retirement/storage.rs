// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn record(&mut self, work: usize, copy_bytes: usize) {
        self.session.retirement_record(self.site, work, copy_bytes);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn finish(&mut self) -> R {
        self.poll();
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 0,
                copy_bytes: 0,
            })
            .map_err(Into::into)
    }
    // A Copy bound verifies every apparently fixed variant field, including
    // enums/digests/spans. Newly owning fields cannot silently drop here.
    pub(super) fn fixed<T: Copy>(&mut self, value: T) {
        self.record(1, size_of::<T>());
        let _ = value;
        self.poll();
    }
    pub(super) fn text(&mut self, text: String) {
        self.record(1, size_of::<String>());
        // String::drop never scans characters. Account for the complete
        // allocation separately, without adding possibly large lengths.
        self.record(1, text.capacity());
        drop(text);
        self.poll();
    }
    pub(super) fn copy_rows<T: Copy>(&mut self, mut rows: Vec<T>) {
        self.record(1, size_of::<Vec<T>>());
        loop {
            self.record(1, size_of::<Option<T>>());
            let Some(value) = rows.pop() else {
                break;
            };
            self.fixed(value);
        }
        // A valid Vec's allocated non-ZST image is <= isize::MAX. For a
        // ZST the multiplication is zero even when capacity is usize::MAX.
        self.record(1, rows.capacity().saturating_mul(size_of::<T>()));
        drop(rows);
        self.poll();
    }
    pub(super) fn bundle_rows(&mut self, mut rows: Vec<E>) {
        self.record(1, size_of::<Vec<E>>());
        loop {
            self.record(1, size_of::<Option<E>>());
            let Some(error) = rows.pop() else {
                break;
            };
            self.bundle(error);
        }
        self.record(1, rows.capacity().saturating_mul(size_of::<E>()));
        drop(rows);
        self.poll();
    }
    pub(super) fn languages(&mut self, mut values: BTreeSet<NativeSourceLanguage>) {
        self.record(1, size_of::<BTreeSet<NativeSourceLanguage>>());
        loop {
            self.tree_pop(values.len());
            self.record(1, size_of::<Option<NativeSourceLanguage>>());
            let Some(value) = values.pop_first() else {
                break;
            };
            self.fixed(value);
        }
        self.record(1, size_of::<BTreeSet<NativeSourceLanguage>>());
        // An empty allocated root may remain after all actual keys drain.
        drop(values);
        self.poll();
    }
    fn tree_pop(&mut self, len: usize) {
        // Pinned698 B=6: 11 keys,12 edges. pop_first does no key comparison;
        // bounded left descent/removal/merge/steal/root adjustment visits at
        // most floor(log2(len))+1 levels. Six complete node images per level
        // cover old/new child/sibling/parent and links, with alignment slack.
        self.record(4, 4 * size_of::<usize>());
        let mut remaining = len;
        let mut levels = 1;
        while remaining > 1 {
            self.record(3, 3 * size_of::<usize>());
            remaining /= 2;
            levels += 1;
        }
        let node = 11
            * (size_of::<NativeSourceLanguage>() + align_of::<NativeSourceLanguage>() - 1)
            + 12 * (size_of::<usize>() + align_of::<usize>() - 1)
            + size_of::<[usize; 8]>();
        for _ in 0..levels {
            self.record(6 * (11 + 12 + 8) + 4, 6 * node);
        }
        self.poll();
    }
}
