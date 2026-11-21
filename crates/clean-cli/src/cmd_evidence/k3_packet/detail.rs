// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The detail grammar for accepted and outside rows of a version 1 KCheck transcript.

use super::tokens::TokenFlags;
use super::transcript::canonical_decimal;

pub(super) fn accepted_detail(text: &str) -> Option<(TokenFlags, &str)> {
    let (bound, fields) = text.strip_prefix("bound=")?.split_once(" iota=")?;
    let (iota, fields) = fields.split_once(" k=")?;
    let (k, lparams) = fields.split_once(" lparams=")?;

    let mut bound = bound.split(';');
    let base = bound.next()?;
    if !canonical_decimal(base) || !bound.all(parameter_offset) || !canonical_decimal(lparams) {
        return None;
    }

    Some((
        TokenFlags {
            iota: bit(iota)?,
            k: bit(k)?,
        },
        lparams,
    ))
}

fn parameter_offset(text: &str) -> bool {
    text.split_once('+').is_some_and(|(parameter, offset)| {
        canonical_decimal(parameter) && canonical_decimal(offset)
    })
}

fn bit(text: &str) -> Option<bool> {
    match text {
        "0" => Some(false),
        "1" => Some(true),
        _ => None,
    }
}

pub(super) fn outside_detail(text: &str) -> bool {
    matches!(
        text,
        "quotient"
            | "axiomDecl"
            | "unsafe"
            | "partial"
            | "literal"
            | "projection"
            | "freeVariable"
            | "inductiveBlock"
    ) || text
        .strip_prefix("cites:[")
        .and_then(|body| body.strip_suffix(']'))
        .is_some_and(|body| !body.contains('\n'))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepted_details_return_frame_flags_and_canonical_level_parameter_text() {
        for (detail, iota, k, level_params) in [
            ("bound=0 iota=0 k=0 lparams=0", false, false, "0"),
            ("bound=12;0+2;19+0 iota=1 k=0 lparams=2", true, false, "2"),
            ("bound=1;0+0 iota=0 k=1 lparams=1", false, true, "1"),
            (
                "bound=18446744073709551616;79+0 iota=1 k=1 lparams=18446744073709551616",
                true,
                true,
                "18446744073709551616",
            ),
        ] {
            assert_eq!(
                accepted_detail(detail),
                Some((TokenFlags { iota, k }, level_params)),
                "{detail}"
            );
        }
    }

    #[test]
    fn accepted_details_require_canonical_numbers_and_exact_separators() {
        for detail in [
            "bound= iota=0 k=0 lparams=0",
            "bound=01 iota=0 k=0 lparams=0",
            "bound=٠ iota=0 k=0 lparams=0",
            "bound=0; iota=0 k=0 lparams=0",
            "bound=0;01+0 iota=0 k=0 lparams=0",
            "bound=0;1+00 iota=0 k=0 lparams=0",
            "bound=0;1+ iota=0 k=0 lparams=0",
            "bound=0;1+0+2 iota=0 k=0 lparams=0",
            "bound=0  iota=0 k=0 lparams=0",
            "bound=0 k=0 iota=0 lparams=0",
            "bound=0 iota=2 k=0 lparams=0",
            "bound=0 iota=0 k=01 lparams=0",
            "bound=0 iota=0 k=0 lparams=00",
            "bound=0 iota=0 k=0 lparams=0\n",
        ] {
            assert_eq!(accepted_detail(detail), None, "{detail:?}");
        }
    }

    #[test]
    fn outside_details_require_a_fixed_reason_or_bracketed_citation() {
        for detail in [
            "quotient",
            "axiomDecl",
            "unsafe",
            "partial",
            "literal",
            "projection",
            "freeVariable",
            "inductiveBlock",
            "cites:[]",
            "cites:[s3:foo s2:π]",
            "cites:[[]\r]",
        ] {
            assert!(outside_detail(detail), "{detail}");
        }
        for detail in [
            "base",
            "quotient ",
            "AxiomDecl",
            "cites: []",
            "cites:[name",
            "cites:[name]tail",
            "cites:[name]\n",
            "cites:[one\ntwo]",
        ] {
            assert!(!outside_detail(detail), "{detail:?}");
        }
    }
}
