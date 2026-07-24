// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Q-pattern matching support for Qq quotations
//!
//! Part of #16: Qq quotation support for macro metaprogramming
//!
//! This module implements pattern matching for quoted expressions (`q(...)` patterns),
//! supporting both static matching at elaboration time (Phase 3) and runtime
//! pattern matching (Phase 4).
//!
//! Split into sub-modules for maintainability (#307):
//! - `extract`: Pattern variable extraction from surface AST
//! - `static_match`: Elaboration with metavariables and static matching
//! - `runtime`: Runtime matching and let-pattern desugaring

mod extract;
mod runtime;
mod static_match;

use clean_parser::{SurfaceExpr, SurfacePattern};

pub(in crate::infer) fn q_match_pattern_expr<'a>(
    pattern: &'a SurfacePattern,
    aliases: &mut Vec<&'a str>,
) -> Option<&'a SurfaceExpr> {
    match pattern {
        SurfacePattern::QPattern(expr) => Some(expr.as_ref()),
        SurfacePattern::As(name, inner) => {
            aliases.push(name.as_str());
            q_match_pattern_expr(inner, aliases)
        }
        _ => None,
    }
}
