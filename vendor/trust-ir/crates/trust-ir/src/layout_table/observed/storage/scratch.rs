// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Consuming private scratch. No unconstrained nonempty Drop route exists.
//! Logical payload/tree work is visible to the original observer even after
//! refusal; physical std/allocator/deallocator latency remains outside this.

use super::*;

impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(in super::super) fn retire_text(&mut self, text: String) {
        self.session.retirement_step(
            self.site,
            text.len()
                .saturating_add(size_of::<String>())
                .saturating_add(1),
        );
        drop(text);
        self.session.retirement_poll(self.site);
    }

    pub(in super::super) fn retire_copy_vec<T: Copy>(&mut self, mut rows: Vec<T>) {
        loop {
            self.session
                .retirement_step(self.site, size_of::<Option<T>>().saturating_add(1));
            let Some(value) = rows.pop() else { break };
            self.retire_fixed(value);
        }
        self.session
            .retirement_step(self.site, size_of::<Vec<T>>().saturating_add(1));
        drop(rows);
        self.session.retirement_poll(self.site);
    }

    pub(in super::super) fn retire_rows<T: Copy>(&mut self, mut rows: Vec<Vec<T>>) {
        loop {
            self.session
                .retirement_step(self.site, size_of::<Option<Vec<T>>>().saturating_add(1));
            let Some(row) = rows.pop() else { break };
            self.retire_copy_vec(row);
        }
        self.session
            .retirement_step(self.site, size_of::<Vec<Vec<T>>>().saturating_add(1));
        drop(rows);
        self.session.retirement_poll(self.site);
    }

    // Pre-observe every actual pop, including the final empty probe. The
    // population bound also covers sealed std tree repair/entry moves; actual
    // storage was conservatively prepaid on each original insertion.
    pub(super) fn retire_tree_pop<K, V>(&mut self, count: usize) {
        self.session.retirement_step(
            self.site,
            count
                .saturating_add(size_of::<Option<(K, V)>>())
                .saturating_add(1),
        );
    }

    pub(in super::super) fn retire_copy_map<K: Copy + Ord, V: Copy>(
        &mut self,
        mut rows: BTreeMap<K, V>,
    ) {
        loop {
            self.retire_tree_pop::<K, V>(rows.len());
            let Some(value) = rows.pop_first() else { break };
            self.retire_fixed(value);
        }
        self.session
            .retirement_step(self.site, size_of::<BTreeMap<K, V>>().saturating_add(1));
        drop(rows);
        self.session.retirement_poll(self.site);
    }

    pub(in super::super) fn retire_set<K: Copy + Ord>(&mut self, mut rows: BTreeSet<K>) {
        loop {
            self.retire_tree_pop::<K, ()>(rows.len());
            let Some(value) = rows.pop_first() else { break };
            self.retire_fixed(value);
        }
        self.session
            .retirement_step(self.site, size_of::<BTreeSet<K>>().saturating_add(1));
        drop(rows);
        self.session.retirement_poll(self.site);
    }

    pub(in super::super) fn retire_fields(&mut self, mut fields: Vec<FieldOffsetShape>) {
        loop {
            self.session.retirement_step(
                self.site,
                size_of::<Option<FieldOffsetShape>>().saturating_add(1),
            );
            let Some(FieldOffsetShape {
                field,
                name,
                ty_shape,
                offset_bits,
            }) = fields.pop()
            else {
                break;
            };
            self.retire_text(name);
            self.retire_fixed((field, ty_shape, offset_bits));
        }
        self.session.retirement_step(
            self.site,
            size_of::<Vec<FieldOffsetShape>>().saturating_add(1),
        );
        drop(fields);
        self.session.retirement_poll(self.site);
    }
}
