// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sublist fragment: the two list-order relations whose Isabelle definition
//! matches a Mathlib `List` relation exactly.
//!
//! Faithfulness (checked against Mathlib `List` defs):
//! * `Sublist.prefix xs ys` (`∃zs. ys = xs @ zs`) ≡ `xs <+: ys` (`List.IsPrefix`,
//!   `∃ t, xs ++ t = ys`).
//! * `Sublist.suffix xs ys` (`∃zs. ys = zs @ xs`) ≡ `xs <:+ ys` (`List.IsSuffix`,
//!   `∃ t, t ++ xs = ys`).
//!
//! The remaining `Sublist` constants (`sublist`/`list_emb`/`strict_*`) have
//! subtler or ambiguous Mathlib counterparts and are deliberately left declined
//! (unsupported over unfaithful).

use super::super::super::isabelle_pure::IsaTerm;
use super::super::types::{prec, LeanTerm, Unsupported};
use super::binary_infix;

/// Try to render `n` as a `Sublist` relation.
pub(super) fn try_translate(n: &str, args: &[&IsaTerm]) -> Option<Result<LeanTerm, Unsupported>> {
    let out = match n {
        "Sublist.prefix" => binary_infix(n, "<+:", prec::REL, args),
        "Sublist.suffix" => binary_infix(n, "<:+", prec::REL, args),
        _ => return None,
    };
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::super::super::super::isabelle_pure::{IsaTerm, IsaType};
    use super::super::super::render::render_top;
    use super::*;

    fn lv(n: &str) -> IsaTerm {
        IsaTerm::Var {
            n: n.into(),
            i: 0,
            t: IsaType::Type {
                n: "List.list".into(),
                a: vec![IsaType::TVar {
                    n: "'a".into(),
                    i: 0,
                }],
            },
        }
    }

    #[test]
    fn prefix_and_suffix_are_infix() {
        let out = try_translate("Sublist.prefix", &[&lv("xs"), &lv("ys")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "xs <+: ys");
        let out = try_translate("Sublist.suffix", &[&lv("xs"), &lv("ys")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "xs <:+ ys");
    }

    #[test]
    fn other_sublist_consts_declined() {
        assert!(try_translate("Sublist.sublist", &[&lv("xs"), &lv("ys")]).is_none());
    }
}
