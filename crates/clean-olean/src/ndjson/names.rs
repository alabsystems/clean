// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! How the reader stores a name (decision R118).
//!
//! Clean's replay keys declarations by a name's display spelling and reads
//! the spelling back (`Name::from_string`, which splits on `.` and reads a
//! decimal component as a number). A Lean name whose string component has a
//! `.` inside it (`Std.«term_..._»`: fourteen ordinary `Init` notation
//! definitions) or reads as a number does not survive that. The reader stores
//! such a component escaped instead -- `ESCAPE` first, every `.` in it as
//! `ESCAPE` -- so the stored name reads back as itself, and keeps the name as
//! written to report it. Names are compared by structure in the kernel, so
//! the escape changes nothing it decides as long as two names never share a
//! stored form: the reader declines an export in which two do
//! (`NdjsonError::NameCollision`). No name Lean's kernel keys a rule on
//! (`Nat.add`, `Quot`, `Eq`, ...) has such a component, so none is stored
//! differently.

use std::borrow::Cow;

/// The escape character: U+2024 ONE DOT LEADER.
pub(crate) const ESCAPE: char = '\u{2024}';

/// A string component as the reader stores it: as written unless its display
/// spelling would not read back as one string component.
pub(crate) fn stored_component(text: &str) -> Cow<'_, str> {
    if !text.contains('.') && text.parse::<u64>().is_err() {
        return Cow::Borrowed(text);
    }
    let mut out = String::with_capacity(text.len() + 6);
    out.push(ESCAPE);
    out.extend(text.chars().map(|c| if c == '.' { ESCAPE } else { c }));
    Cow::Owned(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::name::Name;

    #[test]
    fn test_names_stored_components_read_back_as_themselves() {
        for text in [
            "term_..._",
            "a.b",
            "7",
            "+7",
            "007",
            "",
            ".",
            "plain",
            "x\u{2024}y",
        ] {
            let stored = stored_component(text);
            let name = Name::from_string("Std").str(&*stored);
            assert_eq!(Name::from_string(&name.to_string()), name, "{text:?}");
        }
    }

    #[test]
    fn test_names_plain_components_are_stored_as_written() {
        for text in ["add", "Nat", "_private", "rec_1", "term_+_"] {
            assert!(matches!(stored_component(text), Cow::Borrowed(_)), "{text}");
        }
        assert_eq!(stored_component("a.b"), "\u{2024}a\u{2024}b");
        assert_eq!(stored_component("12"), "\u{2024}12");
    }
}
