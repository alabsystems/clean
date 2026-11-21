// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lexical projection of C3 theorem statements into W0.

use super::{read_json, Measurement, ReportProvenance, RouteScoreboard, SCOREBOARD};
use crate::EvidenceCheckError;
use clean_parser::lexer::{LexError, Lexer, Token, TokenKind};
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fs;
use std::path::Path;
use walkdir::WalkDir;

pub(super) const CHECKER_SOURCES: &str = "theories/kcheck_labelled";
pub(super) const CHECKER_SOURCE_FIGURE: &str = "selfproof.checker_soundness";
// Part of the exact W0 wire representation.
const READING: &str = "a theorem of type `KCheckSpec.C3Owes KCheck.checker` stated in source; it counts only when two kernels have re-checked it (plan section 4)";

#[derive(Deserialize)]
struct CheckerRoute {
    checker_soundness: CheckerSourceFigure,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct CheckerSourceFigure {
    headline_theorems_in_source: Vec<SourceTheorem>,
    reading: String,
    source: String,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct SourceTheorem {
    file: String,
    theorem: String,
}

impl CheckerSourceFigure {
    pub(super) fn theorem_count(&self) -> usize {
        self.headline_theorems_in_source.len()
    }
}

impl fmt::Display for CheckerSourceFigure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} C3 theorem statement(s) in source",
            self.theorem_count()
        )
    }
}

/// Take a Lean name with adjacent qualification dots, preserving its source spelling.
fn take_name<'src, 'tokens>(
    source: &'src str,
    tokens: &'tokens [Token],
) -> Option<(&'src str, usize, &'tokens [Token])> {
    let (first, mut rest) = tokens.split_first()?;
    if !matches!(first.kind, TokenKind::Ident(_)) || first.lean_keyword {
        return None;
    }
    let mut end = first.span.end;
    while let [dot, part, tail @ ..] = rest {
        if dot.kind != TokenKind::Dot
            || !matches!(part.kind, TokenKind::Ident(_))
            || dot.span.start != end
            || dot.span.end != part.span.start
        {
            break;
        }
        end = part.span.end;
        rest = tail;
    }
    Some((&source[first.span.start..end], end, rest))
}

fn headline_name<'src>(source: &'src str, theorem: &Token, tail: &[Token]) -> Option<&'src str> {
    if theorem.span.end == tail.first()?.span.start
        || source[..theorem.span.start]
            .chars()
            .next_back()
            .is_some_and(|ch| ch.is_alphanumeric() || ch == '_')
    {
        return None;
    }
    let (name, _, tail) = take_name(source, tail)?;
    if name
        .chars()
        .any(|ch| ch.is_whitespace() || matches!(ch, ':' | '(' | '{' | '['))
    {
        return None;
    }
    let [colon, tail @ ..] = tail else {
        return None;
    };
    if colon.kind != TokenKind::Colon {
        return None;
    }
    let (obligation, mut end, mut tail) = take_name(source, tail)?;
    if !matches!(obligation, "KCheckSpec.C3Owes" | "C3Owes") {
        return None;
    }
    if let [dot, brace, levels @ ..] = tail {
        if dot.kind == TokenKind::Dot
            && brace.kind == TokenKind::LBrace
            && dot.span.start == end
            && dot.span.end == brace.span.start
        {
            let close = levels
                .iter()
                .position(|token| token.kind == TokenKind::RBrace)?;
            end = levels[close].span.end;
            tail = &levels[close + 1..];
        }
    }
    if end == tail.first()?.span.start {
        return None;
    }
    let (checker, _, tail) = take_name(source, tail)?;
    if matches!(checker, "KCheck.checker" | "checker") && tail.first()?.kind == TokenKind::ColonEq {
        Some(name)
    } else {
        None
    }
}

fn headline_theorems<'src>(
    source: &'src str,
    file: &str,
) -> Result<Vec<&'src str>, EvidenceCheckError> {
    let tokens = Lexer::tokenize(source);
    let mut found = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        match &token.kind {
            // An unsupported notation glyph is an opaque token. It cannot
            // participate in a headline and does not hide later tokens.
            TokenKind::Error(LexError::UnexpectedChar(glyph))
                if !glyph.is_control() && !matches!(*glyph, '\'' | '"' | '`' | '«' | '»') => {}
            TokenKind::Error(error) => {
                return Err(EvidenceCheckError::Invalid(format!(
                    "{file}: Lean lexer refused source at line {} ({error:?})",
                    token.line
                )));
            }
            // Block quotation delimiters are balanced characterwise. A
            // delimiter inside a comment or literal may end the token early.
            TokenKind::SyntaxQuote(body)
                if body.starts_with(['(', '[', '{'])
                    && (body.contains(['"', '\'', '«', '»'])
                        || body.contains("/-")
                        || body.contains("--")) =>
            {
                return Err(EvidenceCheckError::Invalid(format!(
                    "{file}: ambiguous syntax quotation at line {}",
                    token.line
                )));
            }
            TokenKind::Ident(name) if name == "include" && !token.ident_escaped => {
                return Err(EvidenceCheckError::Invalid(format!(
                    "{file}: `include` can hide hypotheses from the stated type"
                )));
            }
            TokenKind::Theorem => {
                if let Some(name) = headline_name(source, token, &tokens[index + 1..]) {
                    found.push(name);
                }
            }
            _ => {}
        }
    }
    Ok(found)
}

pub(super) fn derive(root: &Path) -> Result<CheckerSourceFigure, EvidenceCheckError> {
    let source_root = root.join(CHECKER_SOURCES);
    let metadata = fs::symlink_metadata(&source_root).map_err(|error| {
        EvidenceCheckError::Unavailable(format!("{}: {error}", source_root.display()))
    })?;
    if !metadata.is_dir() {
        return Err(EvidenceCheckError::Invalid(format!(
            "{} is not a checker source directory",
            source_root.display()
        )));
    }
    let entries = WalkDir::new(&source_root)
        .follow_root_links(false)
        .into_iter()
        .filter_entry(|entry| entry.file_name() != ".lake");
    let mut paths = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|error| EvidenceCheckError::Unavailable(error.to_string()))?;
        if entry.file_name().as_encoded_bytes().ends_with(b".lean") {
            if !entry.file_type().is_file() {
                return Err(EvidenceCheckError::Invalid(format!(
                    "{} is not a regular Lean source file",
                    entry.path().display()
                )));
            }
            paths.push(entry.into_path());
        }
    }
    paths.sort_unstable_by(|left, right| left.components().cmp(right.components()));

    let mut theorems = Vec::new();
    for path in paths {
        let file = path
            .strip_prefix(root)
            .ok()
            .and_then(Path::to_str)
            .ok_or_else(|| {
                EvidenceCheckError::Invalid(format!(
                    "invalid checker source path {}",
                    path.display()
                ))
            })?
            .replace(std::path::MAIN_SEPARATOR, "/");
        let text = fs::read_to_string(&path).map_err(|error| {
            let reason = format!("{}: {error}", path.display());
            if error.kind() == std::io::ErrorKind::InvalidData {
                EvidenceCheckError::Invalid(reason)
            } else {
                EvidenceCheckError::Unavailable(reason)
            }
        })?;
        for theorem in headline_theorems(&text, &file)? {
            theorems.push(SourceTheorem {
                file: file.clone(),
                theorem: theorem.to_owned(),
            });
        }
    }
    Ok(CheckerSourceFigure {
        headline_theorems_in_source: theorems,
        reading: READING.to_owned(),
        source: CHECKER_SOURCES.to_owned(),
    })
}

pub(super) fn measure(root: &Path) -> Result<Measurement, EvidenceCheckError> {
    let derived = derive(root)?;
    let scoreboard: RouteScoreboard<CheckerRoute> = read_json(root, SCOREBOARD)?;
    let recorded = scoreboard.route.checker_soundness;
    if derived != recorded {
        return Err(EvidenceCheckError::Invalid(format!(
            "{SCOREBOARD} route.checker_soundness differs from {CHECKER_SOURCES}\nrecorded {recorded:?}\nderived  {derived:?}"
        )));
    }
    Ok(Measurement::CheckerSource(derived))
}

pub(super) fn read_provenance(root: &Path) -> Result<ReportProvenance, EvidenceCheckError> {
    let result = derive(root)?;
    let mut fields = vec![
        ("Source directory", Some(result.source)),
        (
            "Statement shape",
            Some("KCheckSpec.C3Owes KCheck.checker".to_owned()),
        ),
        (
            "Statements found",
            Some(result.headline_theorems_in_source.len().to_string()),
        ),
    ];
    for declaration in result.headline_theorems_in_source {
        fields.push((
            "Statement in source",
            Some(format!("{} ({})", declaration.theorem, declaration.file)),
        ));
    }
    Ok(ReportProvenance { fields, legs: None })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn matches_only_the_exact_statement_shape() {
        for (source, expected) in [
            ("theorem c3 : KCheckSpec.C3Owes KCheck.checker := by\n  exact proof\n", vec!["c3"]),
            ("theorem c3' : C3Owes.{u} checker := proof\n", vec!["c3'"]),
            ("private theorem A.c3 : KCheckSpec.C3Owes.{max u v} /- comment -/ checker := proof\n", vec!["A.c3"]),
            ("-- theorem fake : KCheckSpec.C3Owes KCheck.checker := proof\n", vec![]),
            ("-- theorem fake : C3Owes checker := proof\ntheorem real : KCheckSpec.C3Owes KCheck.checker := proof", vec!["real"]),
            ("/- outer /- theorem fake : C3Owes checker := proof -/ still comment -/\n", vec![]),
            (r#"def note := "theorem fake : C3Owes checker := proof""#, vec![]),
            ("def quote := `(command| theorem fake : C3Owes checker := proof)", vec![]),
            ("theorem step (h : C3Owes checker) : True := trivial", vec![]),
            ("theorem other : C3Owes v1Checker := proof", vec![]),
            ("theorem other : C3Owes checker.v1 := proof", vec![]),
            ("theorem refuted : C3Owes checker → False := proof", vec![]),
            ("theorem both : C3Owes checker ∧ True := proof", vec![]),
            ("def other := by simp [↓reduceIte]\ntheorem c3 : C3Owes checker := proof", vec!["c3"]),
            ("theorem other : C3Owes ↓ checker := proof", vec![]),
        ] {
            assert_eq!(headline_theorems(source, "test.lean").unwrap(), expected, "{source}");
        }
    }

    #[test]
    fn refuses_hidden_includes_and_malformed_quoted_text() {
        for (source, diagnostic) in [
            ("variable (h : False)\n  /- preceding comment -/ include h\ntheorem c : C3Owes checker := h.elim", "`include` can hide hypotheses"),
            ("set_option autoImplicit false in include h in theorem c : C3Owes checker := h.elim", "`include` can hide hypotheses"),
            (r#"def note := "bad\q theorem fake : C3Owes checker := proof""#, "Lean lexer refused source"),
            (
                "def quote := `(command| /- ) theorem fake : C3Owes checker := proof -/ #check True )",
                "ambiguous syntax quotation",
            ),
            (
                r#"def quote := `(command| #check ") theorem fake : C3Owes checker := proof \" inside" )"#,
                "ambiguous syntax quotation",
            ),
        ] {
            let error = headline_theorems(source, "test.lean").unwrap_err();
            assert!(error.to_string().contains(diagnostic), "{source}: {error}");
        }
    }

    fn write(root: &Path, name: &str, contents: &str) {
        let path = root.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    #[test]
    fn scan_preserves_path_and_source_order_and_prunes_build_cache() {
        let root = tempfile::tempdir().unwrap();
        write(
            root.path(),
            "theories/kcheck_labelled/a.lean",
            "theorem later : C3Owes checker := proof",
        );
        write(
            root.path(),
            "theories/kcheck_labelled/a/z.lean",
            "theorem first : C3Owes checker := proof\ntheorem second : C3Owes checker := proof",
        );
        write(
            root.path(),
            "theories/kcheck_labelled/.lake/Cached.lean",
            "include hidden\ntheorem cached : C3Owes checker := hidden",
        );
        write(
            root.path(),
            "theories/kcheck_labelled/.lean",
            "theorem dotfile : C3Owes checker := proof",
        );
        let report = derive(root.path()).unwrap();
        assert_eq!(
            report
                .headline_theorems_in_source
                .iter()
                .map(|row| row.theorem.as_str())
                .collect::<Vec<_>>(),
            ["dotfile", "first", "second", "later"]
        );
        assert_eq!(
            report.headline_theorems_in_source[1].file,
            "theories/kcheck_labelled/a/z.lean"
        );
    }

    #[test]
    fn compares_statement_paths_reading_and_source_with_w0() {
        let root = tempfile::tempdir().unwrap();
        let file = "theories/kcheck_labelled/Proof.lean";
        write(
            root.path(),
            file,
            "theorem headline : C3Owes checker := proof",
        );
        let board = json!({
            "schema": "clean.self_proof_scoreboard.v1",
            "route": {"checker_soundness": {
                "headline_theorems_in_source": [{"file": file, "theorem": "headline"}],
                "reading": READING,
                "source": CHECKER_SOURCES
            }}
        });
        write(root.path(), SCOREBOARD, &board.to_string());
        assert!(measure(root.path()).is_ok());
        for (field, changed) in [
            ("headline_theorems_in_source", json!([])),
            ("reading", json!("claims proof authority")),
            ("source", json!("theories/kcheck")),
        ] {
            let mut wrong = board.clone();
            wrong["route"]["checker_soundness"][field] = changed;
            write(root.path(), SCOREBOARD, &wrong.to_string());
            let Err(error) = measure(root.path()) else {
                panic!("accepted drift in {field}")
            };
            assert!(error
                .to_string()
                .contains("route.checker_soundness differs"));
        }
    }
}
