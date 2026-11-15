// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Rejection rendering must not expand shared expression DAGs without a bound.
//! This changes diagnostic text only; judgments, dependencies and budgets are
//! checked before these messages are constructed and are never accepted here.
use std::fmt::{self, Write};

const MAX_DIAGNOSTIC_BYTES: usize = 4096;
const TRUNCATED: &str = " [diagnostic truncated]";
struct Diagnostic {
    text: String,
    truncated: bool,
}
impl Write for Diagnostic {
    fn write_str(&mut self, value: &str) -> fmt::Result {
        let available = MAX_DIAGNOSTIC_BYTES
            .saturating_sub(TRUNCATED.len())
            .saturating_sub(self.text.len());
        if value.len() <= available {
            self.text.push_str(value);
            return Ok(());
        }
        let mut boundary = available;
        while !value.is_char_boundary(boundary) {
            boundary -= 1;
        }
        self.text.push_str(&value[..boundary]);
        self.truncated = true;
        Err(fmt::Error)
    }
}
pub(super) fn bounded_diagnostic(arguments: fmt::Arguments<'_>) -> String {
    let mut diagnostic = Diagnostic {
        text: String::with_capacity(MAX_DIAGNOSTIC_BYTES),
        truncated: false,
    };
    // Propagate writer refusal through Debug instead of first allocating the
    // complete rendering and truncating afterward. Derived Debug short-circuits
    // its child traversal on this error, including repeated DAG subexpressions.
    if fmt::write(&mut diagnostic, arguments).is_err() {
        diagnostic.truncated = true;
    }
    if diagnostic.truncated {
        diagnostic.text.push_str(TRUNCATED);
    }
    diagnostic.text
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BinderInfo, Expr};
    #[test]
    fn audit_diagnostic_streaming_bound_stops_shared_dag_expansion() {
        let mut term = Expr::const_str("True");
        for _ in 0..64 {
            term = Expr::pi(BinderInfo::Default, term.clone(), term);
        }
        let diagnostic = bounded_diagnostic(format_args!("TypeMismatch expected={term:?}"));
        assert!(diagnostic.starts_with("TypeMismatch"));
        assert!(diagnostic.ends_with(TRUNCATED));
        assert!(diagnostic.len() <= MAX_DIAGNOSTIC_BYTES);
    }
    #[test]
    fn audit_diagnostic_preserves_short_messages_and_unicode_boundaries() {
        assert_eq!(
            bounded_diagnostic(format_args!("TypeMismatch {{ local: {} }}", 7)),
            "TypeMismatch { local: 7 }"
        );
        let text = "αβ🦀".repeat(4096);
        let diagnostic = bounded_diagnostic(format_args!("UnknownConst {text}"));
        assert!(diagnostic.starts_with("UnknownConst "));
        assert!(diagnostic.ends_with(TRUNCATED));
        assert!(diagnostic.len() <= MAX_DIAGNOSTIC_BYTES);
        assert!(std::str::from_utf8(diagnostic.as_bytes()).is_ok());
    }
}
