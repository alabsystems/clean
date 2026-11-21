// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definition headers recognized by the incumbent C++ inventory scanner.

use super::python_whitespace;
use regex::Regex;
use std::sync::LazyLock;

// The inventory's Python regexes use str.isalnum() plus `_` for `\w` and
// str.isspace() for `\s`. Rust regex's default word class also includes marks
// and join controls, so it would change some captured names and boundaries.
pub(super) const WORD: &str = r"\p{L}\p{N}_";
pub(super) const SPACE: &str = r"\p{White_Space}\x1C-\x1F";

static NAMESPACE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(&format!(
        r#"\A(?:(?:inline[{SPACE}]+)?namespace(?:\z|[^{WORD}])|extern[{SPACE}]*"[{SPACE}]*"\z)"#
    ))
    .expect("namespace and extern header pattern")
});

static CLASS: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(&format!(
        r"\A(?:template[{SPACE}]*<[^{{}}]*>[{SPACE}]*)?(?:class|struct|union)[{SPACE}]+([{WORD}]+)"
    ))
    .expect("class header pattern")
});

static FUNCTION: LazyLock<Regex> = LazyLock::new(|| {
    // The search is unanchored. Preserve the first match and the precedence
    // of the special operator spellings over ordinary identifier names.
    Regex::new(&format!(
        r"(?x)
        (
            (?:[A-Za-z_][{WORD}]*[{SPACE}]*::[{SPACE}]*)*
            (?:
                operator[{SPACE}]*
                    (?:\([{SPACE}]*\)|\[[{SPACE}]*\]|[^{SPACE}{WORD}(]+)
                | ~?[A-Za-z_][{WORD}]*
            )
        )
        [{SPACE}]*\("
    ))
    .expect("function header pattern")
});

#[derive(Debug, Eq, PartialEq)]
pub(super) enum Header<'a> {
    Namespace,
    Class(&'a str),
    Block,
    Function(String),
    Unnamed,
}

/// Skip successive access labels starting at a UTF-8 byte boundary. Leave
/// any whitespace before the first non-label for the caller's header span.
pub(super) fn skip_access(code: &str, mut at: usize) -> usize {
    loop {
        let tail = &code[at..];
        let text = tail.trim_start_matches(python_whitespace);
        let Some(rest) = ["public", "private", "protected"]
            .into_iter()
            .find_map(|keyword| text.strip_prefix(keyword))
            .and_then(|rest| rest.trim_start_matches(python_whitespace).strip_prefix(':'))
        else {
            return at;
        };
        at += tail.len() - rest.len();
    }
}

pub(super) fn classify(header: &str) -> Header<'_> {
    let text = header.trim_matches(python_whitespace);
    if NAMESPACE.is_match(text) {
        return Header::Namespace;
    }
    if !text.contains('(') {
        return CLASS
            .captures(text)
            .and_then(|capture| capture.get(1))
            .map_or(Header::Block, |name| Header::Class(name.as_str()));
    }
    if text.ends_with('=') {
        return Header::Block;
    }
    let Some(name) = FUNCTION.captures(text).and_then(|capture| capture.get(1)) else {
        return Header::Unnamed;
    };
    let name = name.as_str();
    if matches!(
        name,
        "if" | "for" | "while" | "switch" | "return" | "catch" | "sizeof"
    ) {
        return Header::Unnamed;
    }
    Header::Function(name.chars().filter(|&ch| !python_whitespace(ch)).collect())
}

#[cfg(test)]
mod tests {
    use super::{classify, skip_access, Header};

    #[test]
    fn access_labels_leave_the_header_whitespace_and_stop_at_nonlabels() {
        let code = "é\u{1c}public:\n private\u{2009}:protected:\n  T f()";
        assert_eq!(&code[skip_access(code, 'é'.len_utf8())..], "\n  T f()");
        assert_eq!(skip_access(" \tprivate_name: f()", 0), 0);
        assert_eq!(&"public::rest"[skip_access("public::rest", 0)..], ":rest");
    }

    #[test]
    fn namespace_and_masked_extern_precede_function_detection() {
        for text in [
            "inline\u{1c}namespace anon(x)",
            "namespace\u{345}hidden",
            "extern\"\"",
            "extern \u{1d}\"\u{1f}\"",
        ] {
            assert_eq!(classify(text), Header::Namespace, "{text:?}");
        }
        assert_eq!(classify("extern \"C\""), Header::Block);
        assert_eq!(
            classify("namespaceÉ(x)"),
            Header::Function("namespaceÉ".into())
        );
    }

    #[test]
    fn class_templates_and_non_function_blocks_follow_the_incumbent_order() {
        assert_eq!(
            classify("template<X> struct A> struct B"),
            Header::Class("B")
        );
        assert_eq!(
            classify("template <class T> struct Δ9 : Base"),
            Header::Class("Δ9")
        );
        assert_eq!(classify("struct Word\u{345}Suffix"), Header::Class("Word"));
        assert_eq!(classify("class C (stuff)"), Header::Function("C".into()));
        assert_eq!(classify("A a ="), Header::Block);
        assert_eq!(classify("auto lambda() ="), Header::Block);
    }

    #[test]
    fn functions_keep_the_first_match_and_normalize_qualified_operator_names() {
        for (header, name) in [
            ("typeof(x) f()", "typeof"),
            ("long C\u{1c}::\u{1d}~D (", "C::~D"),
            ("long Out :: operator ( \u{1f} ) (", "Out::operator()"),
            ("long Out :: operator [ ] (", "Out::operator[]"),
            ("long Out :: operator <= (", "Out::operator<="),
            ("long Out :: operator foo (", "foo"),
            ("long fΔ١(", "fΔ١"),
            ("long f\u{345}Suffix(", "Suffix"),
            ("long 9Foo(", "Foo"),
            ("long ΔFoo(", "Foo"),
            ("ns::if (p)", "ns::if"),
        ] {
            assert_eq!(
                classify(header),
                Header::Function(name.into()),
                "{header:?}"
            );
        }
        for header in ["if (p)", "sizeof (x) function(x)", "(x)"] {
            assert_eq!(classify(header), Header::Unnamed, "{header:?}");
        }
    }
}
