// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Allocation-free `Name` comparison utilities shared by head_family and
//! expr_classifier.

use clean_kernel::name::{Name, NameInner};

#[inline]
pub(crate) fn name_eq_str(name: &Name, expected: &str) -> bool {
    let mut parts = expected.rsplit('.');
    let mut current = name.inner();

    loop {
        match current {
            NameInner::Anon => return parts.next().is_none(),
            NameInner::Str(prefix, component) => {
                let Some(part) = parts.next() else {
                    return false;
                };
                if part != component.as_ref() {
                    return false;
                }
                let prefix: &Name = prefix;
                current = prefix.inner();
            }
            NameInner::Num(prefix, value) => {
                let Some(part) = parts.next() else {
                    return false;
                };
                let Ok(part_value) = part.parse::<u64>() else {
                    return false;
                };
                if part_value != *value {
                    return false;
                }
                let prefix: &Name = prefix;
                current = prefix.inner();
            }
        }
    }
}

#[inline]
pub(crate) fn name_eq_any(name: &Name, expected: &[&str]) -> bool {
    expected
        .iter()
        .any(|candidate| name_eq_str(name, candidate))
}
