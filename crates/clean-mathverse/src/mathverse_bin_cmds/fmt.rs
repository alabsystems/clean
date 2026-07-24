// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Formatting and parsing helpers for the mathverse CLI.

use crate::shard_verify::source_system_name;

/// Display name for a source system byte.
pub(crate) fn source_system_display(id: u8) -> &'static str {
    source_system_name(id)
}

/// Display name for an import confidence level.
pub(crate) fn confidence_display(id: u8) -> &'static str {
    match id {
        0 => "KernelVerified",
        1 => "Translated",
        2 => "Axiomatized",
        3 => "Unverified",
        6 => "SourceVerified",
        _ => "Unknown",
    }
}

/// Display name for a content domain.
pub(crate) fn domain_display(id: u8) -> &'static str {
    match id {
        0 => "PureMath",
        1 => "Software",
        2 => "Complexity",
        3 => "NnVerification",
        4 => "Physics",
        5 => "Logic",
        6 => "Cryptography",
        _ => "Unknown",
    }
}

/// Parse a source system name to its numeric ID.
/// Case-insensitive partial matching on known system names.
pub(crate) fn parse_source_system(name: &str) -> Option<u8> {
    let lower = name.to_lowercase();
    // Check exact numeric values first.
    if let Ok(n) = lower.parse::<u8>() {
        return Some(n);
    }
    // Match known names (case-insensitive).
    let systems: &[(&str, u8)] = &[
        ("lean4", 0),
        ("coq", 1),
        ("agda", 2),
        ("idris2", 3),
        ("fstar", 4),
        ("cedille", 5),
        ("isabelle", 6),
        ("hollight", 7),
        ("hol4", 8),
        ("metamath", 9),
        ("mizar", 10),
        ("dafny", 11),
        ("why3", 12),
        ("nuprl", 13),
        ("pvs", 14),
        ("acl2", 15),
        ("liquidhaskell", 16),
        ("key", 17),
        ("framac", 18),
        ("spark", 19),
        ("gammacrown", 20),
        ("alphabetacrown", 21),
        ("z3", 22),
        ("cvc5", 23),
        ("vampire", 24),
        ("cadical", 25),
        ("tlc", 26),
        ("clean", 27),
        ("cleannative", 27),
        ("verus", 49),
        ("creusot", 50),
        ("kani", 51),
    ];
    for &(sys_name, id) in systems {
        if lower == sys_name {
            return Some(id);
        }
    }
    None
}

/// Parse a trust/confidence level name to its numeric ID.
/// Accepts: "kernel", "kernelverified", "sourceverified", "translated", "axiomatized", "unverified".
pub(crate) fn parse_trust_level(name: &str) -> Option<u8> {
    let lower = name.to_lowercase();
    match lower.as_str() {
        "kernel" | "kernelverified" | "kernel_verified" | "0" => Some(0),
        "translated" | "1" => Some(1),
        "axiomatized" | "2" => Some(2),
        "unverified" | "3" => Some(3),
        "source" | "sourceverified" | "source_verified" | "6" => Some(6),
        _ => None,
    }
}

/// Output format for CLI commands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OutputFormat {
    Table,
    Json,
    Csv,
    Tsv,
}

impl OutputFormat {
    /// Parse from a string argument. Returns `None` for unrecognized formats.
    pub(crate) fn parse(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "table" | "text" => Some(Self::Table),
            "json" => Some(Self::Json),
            "csv" => Some(Self::Csv),
            "tsv" => Some(Self::Tsv),
            _ => None,
        }
    }

    /// Returns `true` when this format is a delimited tabular format (CSV/TSV).
    pub(crate) fn is_delimited(self) -> bool {
        matches!(self, Self::Csv | Self::Tsv)
    }

    /// Delimiter byte for delimited formats. Returns `None` for non-delimited
    /// formats; callers inside this module unwrap via `expect` after checking
    /// `is_delimited()`.
    fn delimiter(self) -> Option<char> {
        match self {
            Self::Csv => Some(','),
            Self::Tsv => Some('\t'),
            Self::Table | Self::Json => None,
        }
    }
}

/// Escape a field value for CSV/TSV output.
///
/// CSV (RFC 4180): if the field contains a delimiter, double-quote, or newline,
/// wrap in double quotes and escape internal `"` as `""`.
///
/// TSV: tabs and newlines inside a field are replaced with a literal space
/// (tabs cannot be represented in a line-oriented TSV stream without ambiguity).
pub(crate) fn escape_field(value: &str, fmt: OutputFormat) -> String {
    match fmt {
        OutputFormat::Csv => {
            if value.contains(',')
                || value.contains('"')
                || value.contains('\n')
                || value.contains('\r')
            {
                let escaped = value.replace('"', "\"\"");
                format!("\"{escaped}\"")
            } else {
                value.to_string()
            }
        }
        OutputFormat::Tsv => {
            // Tabs and newlines inside TSV fields are ambiguous; replace with space.
            value.replace(['\t', '\n', '\r'], " ")
        }
        _ => value.to_string(),
    }
}

/// Format a single row of already-stringified fields as a delimited-format
/// string (no trailing newline). Exposed for unit testing; production code
/// should use `emit_delimited_row` which writes to stdout.
pub(crate) fn format_delimited_row(fields: &[&str], fmt: OutputFormat) -> String {
    debug_assert!(
        fmt.is_delimited(),
        "format_delimited_row requires CSV/TSV format"
    );
    let delim = fmt
        .delimiter()
        .expect("invariant: is_delimited() implies Some");
    let mut out = String::new();
    let mut first = true;
    for field in fields {
        if !first {
            out.push(delim);
        }
        out.push_str(&escape_field(field, fmt));
        first = false;
    }
    out
}

/// Emit a single row of already-stringified fields in the target delimited format.
/// Each field is escaped according to the format's rules.
pub(crate) fn emit_delimited_row(fields: &[&str], fmt: OutputFormat) {
    println!("{}", format_delimited_row(fields, fmt));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_table_and_text_aliases() {
        assert_eq!(OutputFormat::parse("table"), Some(OutputFormat::Table));
        assert_eq!(OutputFormat::parse("text"), Some(OutputFormat::Table));
        assert_eq!(OutputFormat::parse("TABLE"), Some(OutputFormat::Table));
    }

    #[test]
    fn parse_csv_tsv_json() {
        assert_eq!(OutputFormat::parse("csv"), Some(OutputFormat::Csv));
        assert_eq!(OutputFormat::parse("tsv"), Some(OutputFormat::Tsv));
        assert_eq!(OutputFormat::parse("json"), Some(OutputFormat::Json));
        assert_eq!(OutputFormat::parse("CSV"), Some(OutputFormat::Csv));
    }

    #[test]
    fn parse_unknown_format_returns_none() {
        assert_eq!(OutputFormat::parse("xml"), None);
        assert_eq!(OutputFormat::parse(""), None);
    }

    #[test]
    fn csv_escapes_comma_fields() {
        assert_eq!(escape_field("simple", OutputFormat::Csv), "simple");
        assert_eq!(escape_field("a,b", OutputFormat::Csv), "\"a,b\"");
    }

    #[test]
    fn csv_escapes_embedded_quotes() {
        assert_eq!(
            escape_field("he said \"hi\"", OutputFormat::Csv),
            "\"he said \"\"hi\"\"\""
        );
    }

    #[test]
    fn csv_escapes_newlines() {
        assert_eq!(
            escape_field("line1\nline2", OutputFormat::Csv),
            "\"line1\nline2\""
        );
    }

    #[test]
    fn tsv_replaces_tabs_with_spaces() {
        assert_eq!(escape_field("a\tb", OutputFormat::Tsv), "a b");
        assert_eq!(escape_field("a\nb", OutputFormat::Tsv), "a b");
    }

    #[test]
    fn tsv_leaves_commas_and_quotes_intact() {
        assert_eq!(escape_field("a,\"b\"", OutputFormat::Tsv), "a,\"b\"");
    }

    #[test]
    fn is_delimited_matrix() {
        assert!(OutputFormat::Csv.is_delimited());
        assert!(OutputFormat::Tsv.is_delimited());
        assert!(!OutputFormat::Table.is_delimited());
        assert!(!OutputFormat::Json.is_delimited());
    }

    // ---------------------------------------------------------------
    // Row-level tests per subcommand (CSV + TSV).
    //
    // These model the shape of each subcommand's output. They exercise
    // header emission, row emission, delimiter choice, and — critically —
    // the escaping behavior when a declaration name legitimately contains
    // characters that collide with the chosen delimiter.
    // ---------------------------------------------------------------

    // -------- search subcommand ------------------------------------

    #[test]
    fn search_csv_header_and_simple_row() {
        let header = format_delimited_row(
            &[
                "idx",
                "name",
                "source_system",
                "trust",
                "domain",
                "has_value",
                "axiom_count",
            ],
            OutputFormat::Csv,
        );
        assert_eq!(
            header,
            "idx,name,source_system,trust,domain,has_value,axiom_count"
        );
        let row = format_delimited_row(
            &[
                "7",
                "Nat.add",
                "Lean4",
                "KernelVerified",
                "PureMath",
                "true",
                "0",
            ],
            OutputFormat::Csv,
        );
        assert_eq!(row, "7,Nat.add,Lean4,KernelVerified,PureMath,true,0");
    }

    #[test]
    fn search_csv_escapes_name_with_comma() {
        // Synthetic: a declaration whose name contains a comma must be quoted.
        let row = format_delimited_row(
            &[
                "42",
                "Foo<a,b>",
                "Lean4",
                "KernelVerified",
                "PureMath",
                "true",
                "0",
            ],
            OutputFormat::Csv,
        );
        assert_eq!(row, "42,\"Foo<a,b>\",Lean4,KernelVerified,PureMath,true,0");
    }

    #[test]
    fn search_tsv_tab_delimited_row() {
        let row = format_delimited_row(
            &[
                "7",
                "Nat.add",
                "Lean4",
                "KernelVerified",
                "PureMath",
                "true",
                "0",
            ],
            OutputFormat::Tsv,
        );
        assert_eq!(row, "7\tNat.add\tLean4\tKernelVerified\tPureMath\ttrue\t0");
    }

    #[test]
    fn search_tsv_sanitizes_embedded_tab() {
        // Tabs inside a field must collapse to spaces so the row remains parseable.
        let row = format_delimited_row(
            &[
                "42",
                "weird\tname",
                "Lean4",
                "KernelVerified",
                "PureMath",
                "true",
                "0",
            ],
            OutputFormat::Tsv,
        );
        assert_eq!(
            row,
            "42\tweird name\tLean4\tKernelVerified\tPureMath\ttrue\t0"
        );
    }

    // -------- list subcommand --------------------------------------

    #[test]
    fn list_csv_has_four_column_schema() {
        let header = format_delimited_row(
            &["idx", "name", "source_system", "trust"],
            OutputFormat::Csv,
        );
        assert_eq!(header, "idx,name,source_system,trust");

        let row = format_delimited_row(
            &["3", "List.map", "Mathlib", "Translated"],
            OutputFormat::Csv,
        );
        assert_eq!(row, "3,List.map,Mathlib,Translated");
    }

    #[test]
    fn list_tsv_preserves_commas_in_name() {
        // TSV does NOT need to escape commas — they are valid field contents.
        let row = format_delimited_row(
            &["3", "Map<K,V>", "Mathlib", "Translated"],
            OutputFormat::Tsv,
        );
        assert_eq!(row, "3\tMap<K,V>\tMathlib\tTranslated");
    }

    // -------- stats subcommand (long format) -----------------------

    #[test]
    fn stats_csv_long_format_rows() {
        let header = format_delimited_row(&["category", "key", "count"], OutputFormat::Csv);
        assert_eq!(header, "category,key,count");

        let total =
            format_delimited_row(&["total", "total_constants", "1234567"], OutputFormat::Csv);
        assert_eq!(total, "total,total_constants,1234567");

        let domain = format_delimited_row(&["domain", "PureMath", "900000"], OutputFormat::Csv);
        assert_eq!(domain, "domain,PureMath,900000");
    }

    // -------- deps subcommand --------------------------------------

    #[test]
    fn deps_tsv_row_schema() {
        let header = format_delimited_row(
            &["root", "idx", "depth", "name", "source_system"],
            OutputFormat::Tsv,
        );
        assert_eq!(header, "root\tidx\tdepth\tname\tsource_system");

        let row = format_delimited_row(
            &["Nat.add", "42", "1", "Nat.succ", "Lean4"],
            OutputFormat::Tsv,
        );
        assert_eq!(row, "Nat.add\t42\t1\tNat.succ\tLean4");
    }

    // -------- diff subcommand --------------------------------------

    #[test]
    fn diff_csv_side_rows() {
        let header = format_delimited_row(&["side", "name"], OutputFormat::Csv);
        assert_eq!(header, "side,name");

        let only_a = format_delimited_row(&["a", "MyLemma"], OutputFormat::Csv);
        let only_b = format_delimited_row(&["b", "OtherLemma"], OutputFormat::Csv);
        assert_eq!(only_a, "a,MyLemma");
        assert_eq!(only_b, "b,OtherLemma");
    }

    // -------- inspect subcommand -----------------------------------

    #[test]
    fn inspect_csv_row_handles_empty_provenance_fields() {
        let header = format_delimited_row(
            &[
                "idx",
                "name",
                "source_system",
                "trust",
                "domain",
                "has_value",
                "trust_gated",
                "axiom_count",
                "original_name",
                "source_file",
                "source_line",
                "source_version",
                "module_path",
                "pipeline_version",
                "notes",
            ],
            OutputFormat::Csv,
        );
        assert!(header.starts_with("idx,name,source_system"));
        assert!(header.ends_with("notes"));

        let row = format_delimited_row(
            &[
                "1",
                "Eq.refl",
                "Lean4",
                "KernelVerified",
                "PureMath",
                "true",
                "false",
                "0",
                "Eq.refl",
                "",
                "",
                "",
                "",
                "",
                "",
            ],
            OutputFormat::Csv,
        );
        // Trailing empties preserve schema alignment.
        assert_eq!(
            row,
            "1,Eq.refl,Lean4,KernelVerified,PureMath,true,false,0,Eq.refl,,,,,,"
        );
    }

    // -------- sample subcommand ------------------------------------

    #[test]
    fn sample_csv_row_with_domain() {
        let row = format_delimited_row(
            &["99", "Ring.mul", "Mathlib", "Translated", "PureMath"],
            OutputFormat::Csv,
        );
        assert_eq!(row, "99,Ring.mul,Mathlib,Translated,PureMath");
    }

    // -------- crash-proof edge cases -------------------------------

    #[test]
    fn csv_empty_field_list_emits_empty_line() {
        let row = format_delimited_row(&[], OutputFormat::Csv);
        assert_eq!(row, "");
    }

    #[test]
    fn csv_single_field_no_delimiter() {
        let row = format_delimited_row(&["lonely"], OutputFormat::Csv);
        assert_eq!(row, "lonely");
    }
}
