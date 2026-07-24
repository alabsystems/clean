// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LaTeX parser for arXiv papers. Extracts theorem environments, definitions,
//! proofs, macros, and metadata from raw LaTeX source.

use super::types::*;

/// Standard amsthm-like theorem environments.
const THEOREM_ENV_NAMES: &[&str] = &[
    "theorem",
    "lemma",
    "proposition",
    "corollary",
    "conjecture",
    "claim",
    "fact",
];

/// Standard definition-like environments.
const DEFINITION_ENV_NAMES: &[&str] = &[
    "definition",
    "notation",
    "convention",
    "example",
    "remark",
    "assumption",
    "axiom",
];

/// Theorem kind display names (lowercase) to TheoremKind mapping.
fn classify_theorem(name: &str) -> Option<TheoremKind> {
    let lower = name.to_lowercase();
    if lower.contains("theorem") {
        Some(TheoremKind::Theorem)
    } else if lower.contains("lemma") {
        Some(TheoremKind::Lemma)
    } else if lower.contains("proposition") {
        Some(TheoremKind::Proposition)
    } else if lower.contains("corollary") {
        Some(TheoremKind::Corollary)
    } else if lower.contains("conjecture") {
        Some(TheoremKind::Conjecture)
    } else if lower.contains("claim") {
        Some(TheoremKind::Claim)
    } else if lower.contains("fact") {
        Some(TheoremKind::Fact)
    } else {
        None
    }
}

fn classify_definition(name: &str) -> Option<DefinitionKind> {
    let lower = name.to_lowercase();
    if lower.contains("definition") {
        Some(DefinitionKind::Definition)
    } else if lower.contains("notation") {
        Some(DefinitionKind::Notation)
    } else if lower.contains("convention") {
        Some(DefinitionKind::Convention)
    } else if lower.contains("example") {
        Some(DefinitionKind::Example)
    } else if lower.contains("remark") {
        Some(DefinitionKind::Remark)
    } else if lower.contains("assumption") || lower.contains("hypothesis") {
        Some(DefinitionKind::Assumption)
    } else if lower.contains("axiom") {
        Some(DefinitionKind::Axiom)
    } else {
        None
    }
}

/// Find custom theorem-like environments from `\newtheorem` declarations.
pub(crate) fn find_custom_environments(latex: &str) -> Vec<(String, String)> {
    let mut envs = Vec::new();

    // \newtheorem{name}[counter]{Display Name}
    // \newtheorem{name}{Display Name}[parent]
    // \newtheorem*{name}{Display Name}
    for line in latex.lines() {
        let trimmed = line.trim();

        // Skip comments
        if trimmed.starts_with('%') {
            continue;
        }

        // Match \newtheorem variants
        if let Some(rest) = trimmed.strip_prefix("\\newtheorem") {
            let rest = rest.trim_start_matches('*');
            if let Some(env_name) = extract_brace_arg(rest) {
                // Get the display name (skip optional [counter] arg)
                let after_name = &rest[env_name.len() + 2..]; // skip {name}
                let after_opt = skip_optional_arg(after_name);
                if let Some(display) = extract_brace_arg(after_opt) {
                    let lower = display.to_lowercase();
                    if classify_theorem(&lower).is_some() {
                        envs.push((env_name.to_string(), "theorem".to_string()));
                    } else if classify_definition(&lower).is_some() {
                        envs.push((env_name.to_string(), "definition".to_string()));
                    }
                }
            }
        }

        // Match custom macros like \newvtheorem{name}{Display}
        if trimmed.contains("newv") || trimmed.contains("newcustom") {
            if let Some(start) = trimmed.find('{') {
                if let Some(env_name) = extract_brace_arg(&trimmed[start..]) {
                    let after = &trimmed[start + env_name.len() + 2..];
                    if let Some(display) = extract_brace_arg(after) {
                        let lower = display.to_lowercase();
                        if classify_theorem(&lower).is_some() {
                            envs.push((env_name.to_string(), "theorem".to_string()));
                        } else if classify_definition(&lower).is_some() {
                            envs.push((env_name.to_string(), "definition".to_string()));
                        }
                    }
                }
            }
        }
    }

    envs
}

/// Extract content between matching braces: `{content}` → `content`.
fn extract_brace_arg(s: &str) -> Option<&str> {
    let s = s.trim();
    if !s.starts_with('{') {
        return None;
    }
    let mut depth = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(&s[1..i]);
                }
            }
            _ => {}
        }
    }
    None
}

/// Skip an optional `[...]` argument, returning the remainder.
fn skip_optional_arg(s: &str) -> &str {
    let s = s.trim();
    if !s.starts_with('[') {
        return s;
    }
    if let Some(end) = s.find(']') {
        &s[end + 1..]
    } else {
        s
    }
}

/// Extract user-defined macros from preamble.
pub(crate) fn extract_macros(latex: &str) -> Vec<LatexMacro> {
    let mut macros = Vec::new();

    for line in latex.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('%') {
            continue;
        }

        for prefix in &["\\newcommand", "\\renewcommand", "\\DeclareMathOperator"] {
            if let Some(rest) = trimmed.strip_prefix(prefix) {
                let rest = rest.trim_start_matches('*');
                // Extract macro name: either {\\name} or \\name
                let rest = rest.trim();
                let (name, after) = if rest.starts_with('{') {
                    if let Some(inner) = extract_brace_arg(rest) {
                        let name = inner.trim_start_matches('\\');
                        (name, &rest[inner.len() + 2..])
                    } else {
                        continue;
                    }
                } else if let Some(after_backslash) = rest.strip_prefix('\\') {
                    // Find end of command name
                    let end = after_backslash
                        .find(|c: char| !c.is_alphanumeric() && c != '@')
                        .map(|i| i + 1)
                        .unwrap_or(rest.len());
                    (&rest[1..end], &rest[end..])
                } else {
                    continue;
                };

                // Optional [nargs]
                let (nargs, after) = if after.trim().starts_with('[') {
                    let after = after.trim();
                    if let Some(end) = after.find(']') {
                        let n = after[1..end].parse::<u8>().unwrap_or(0);
                        (n, &after[end + 1..])
                    } else {
                        (0, after)
                    }
                } else {
                    (0, after)
                };

                // Extract body
                if let Some(body) = extract_brace_arg(after.trim()) {
                    macros.push(LatexMacro {
                        name: name.to_string(),
                        nargs,
                        body: body.to_string(),
                    });
                }
            }
        }
    }

    macros
}

/// Extract all occurrences of a LaTeX environment from the document.
///
/// Returns `(content, ref_label, dependencies, byte_end_position)` for each.
pub(crate) fn extract_environments(
    latex: &str,
    env_name: &str,
) -> Vec<(String, String, Vec<String>, usize)> {
    let begin_tag = format!("\\begin{{{env_name}}}");
    let end_tag = format!("\\end{{{env_name}}}");
    let mut results = Vec::new();
    let mut pos = 0;

    while pos < latex.len() {
        let idx = match latex[pos..].find(&begin_tag) {
            Some(i) => pos + i,
            None => break,
        };
        let content_start = idx + begin_tag.len();

        // Handle nesting
        let mut depth = 1;
        let mut scan = content_start;
        loop {
            let next_begin = latex[scan..].find(&begin_tag).map(|i| scan + i);
            let next_end = latex[scan..].find(&end_tag).map(|i| scan + i);

            match (next_begin, next_end) {
                (_, None) => break,
                (Some(b), Some(e)) if b < e => {
                    depth += 1;
                    scan = b + begin_tag.len();
                }
                (_, Some(e)) => {
                    depth -= 1;
                    if depth == 0 {
                        let content = latex[content_start..e].trim().to_string();
                        let end_pos = e + end_tag.len();

                        let ref_label = extract_label(&content);
                        let deps = extract_refs(&content);

                        results.push((content, ref_label, deps, end_pos));
                        pos = end_pos;
                        break;
                    }
                    scan = e + end_tag.len();
                }
            }
        }

        if depth > 0 {
            // Unmatched begin — skip
            pos = content_start;
        }
    }

    results
}

/// Extract `\label{...}` from content.
fn extract_label(content: &str) -> String {
    if let Some(start) = content.find("\\label{") {
        let after = &content[start + 7..];
        if let Some(end) = after.find('}') {
            return after[..end].to_string();
        }
    }
    String::new()
}

/// Extract all `\ref{...}`, `\eqref{...}`, `\cref{...}` etc.
fn extract_refs(content: &str) -> Vec<String> {
    let mut refs = Vec::new();
    for prefix in &["\\ref{", "\\eqref{", "\\cref{", "\\Cref{", "\\autoref{"] {
        let mut pos = 0;
        while let Some(start) = content[pos..].find(prefix) {
            let abs_start = pos + start + prefix.len();
            if let Some(end) = content[abs_start..].find('}') {
                refs.push(content[abs_start..abs_start + end].to_string());
                pos = abs_start + end + 1;
            } else {
                break;
            }
        }
    }
    refs.sort();
    refs.dedup();
    refs
}

/// Extract the abstract.
pub(crate) fn extract_abstract(latex: &str) -> String {
    let envs = extract_environments(latex, "abstract");
    if let Some((content, _, _, _)) = envs.into_iter().next() {
        return content;
    }
    String::new()
}

/// Extract paper title from `\title{...}`.
pub(crate) fn extract_title(latex: &str) -> String {
    // Handle \title[short]{full}
    if let Some(start) = latex.find("\\title") {
        let rest = &latex[start + 6..];
        let rest = skip_optional_arg(rest);
        if let Some(title) = extract_brace_arg(rest.trim()) {
            return title.to_string();
        }
    }
    String::new()
}

/// Parse a complete LaTeX document into an `ArxivPaper`.
pub(crate) fn parse_latex(paper_id: &str, latex: &str) -> ArxivPaper {
    let title = extract_title(latex);
    let abstract_latex = extract_abstract(latex);
    let macros = extract_macros(latex);
    let custom_envs = find_custom_environments(latex);

    // Build environment lists
    let mut theorem_env_names: Vec<String> =
        THEOREM_ENV_NAMES.iter().map(|s| s.to_string()).collect();
    let mut definition_env_names: Vec<String> =
        DEFINITION_ENV_NAMES.iter().map(|s| s.to_string()).collect();

    for (name, kind) in &custom_envs {
        if kind == "theorem" && !theorem_env_names.contains(name) {
            theorem_env_names.push(name.clone());
        } else if kind == "definition" && !definition_env_names.contains(name) {
            definition_env_names.push(name.clone());
        }
    }

    // Extract all proof environments for matching
    let proof_envs = extract_environments(latex, "proof");

    // Extract definitions
    let mut definitions = Vec::new();
    let mut def_counter = 0u32;
    for env_name in &definition_env_names {
        for (content, ref_label, deps, _end) in extract_environments(latex, env_name) {
            def_counter += 1;
            let kind = classify_definition(env_name).unwrap_or(DefinitionKind::Definition);
            definitions.push(ArxivDefinition {
                label: format!("{} {def_counter}", capitalize(env_name)),
                kind,
                latex: content,
                ref_label,
                dependencies: deps,
            });
        }
    }

    // Extract theorems with proof matching
    let mut theorems = Vec::new();
    let mut thm_counter = 0u32;
    for env_name in &theorem_env_names {
        for (content, ref_label, deps, end) in extract_environments(latex, env_name) {
            thm_counter += 1;
            let kind = classify_theorem(env_name).unwrap_or(TheoremKind::Theorem);

            // Find proof within 500 chars after theorem ends
            let proof_latex = find_next_proof(latex, end, &proof_envs);

            theorems.push(ArxivTheorem {
                label: format!("{} {thm_counter}", capitalize(env_name)),
                kind,
                statement_latex: content,
                proof_latex,
                ref_label,
                dependencies: deps,
            });
        }
    }

    ArxivPaper {
        paper_id: paper_id.to_string(),
        title,
        authors: String::new(), // TODO: extract from \author{}
        categories: Vec::new(), // filled from metadata
        abstract_latex,
        macros,
        custom_environments: custom_envs,
        definitions,
        theorems,
        warnings: Vec::new(),
    }
}

/// Find the proof environment that follows within 500 chars of a theorem's end.
fn find_next_proof(
    latex: &str,
    theorem_end: usize,
    proof_envs: &[(String, String, Vec<String>, usize)],
) -> String {
    let begin_tag = "\\begin{proof}";
    // Check if there's a \begin{proof} within 500 chars
    let search = &latex[theorem_end..std::cmp::min(theorem_end + 500, latex.len())];
    if let Some(offset) = search.find(begin_tag) {
        let abs_pos = theorem_end + offset;
        // Find the matching proof_env entry
        for (content, _, _, end) in proof_envs {
            // Check if this proof starts at approximately the right place
            if *end > abs_pos && *end < abs_pos + 50000 {
                return content.clone();
            }
        }
    }
    String::new()
}

fn capitalize(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().to_string() + c.as_str(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_brace_arg() {
        assert_eq!(extract_brace_arg("{hello}"), Some("hello"));
        assert_eq!(extract_brace_arg("{a{b}c}"), Some("a{b}c"));
        assert_eq!(extract_brace_arg("nope"), None);
    }

    #[test]
    fn test_find_custom_environments() {
        let latex = r#"
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{myconj}{Conjecture}
\newtheorem{defn}{Definition}
"#;
        let envs = find_custom_environments(latex);
        assert!(envs.iter().any(|(n, k)| n == "myconj" && k == "theorem"));
        assert!(envs.iter().any(|(n, k)| n == "defn" && k == "definition"));
    }

    #[test]
    fn test_parse_simple_paper() {
        let latex = r#"
\documentclass{article}
\newtheorem{theorem}{Theorem}
\newtheorem{definition}{Definition}
\newcommand{\NN}{\mathbb{N}}
\begin{document}
\title{Test Paper}
\begin{abstract}
This is the abstract.
\end{abstract}
\begin{definition}\label{def:prime}
A natural number $p > 1$ is \emph{prime} if its only divisors are $1$ and $p$.
\end{definition}
\begin{theorem}\label{thm:inf}
There are infinitely many primes.
\end{theorem}
\begin{proof}
Suppose there are finitely many primes $p_1, \ldots, p_n$.
Consider $N = p_1 \cdots p_n + 1$. By Theorem~\ref{thm:inf}, contradiction.
\end{proof}
\end{document}
"#;
        let paper = parse_latex("test.0001", latex);
        assert_eq!(paper.title, "Test Paper");
        assert_eq!(paper.abstract_latex, "This is the abstract.");
        assert_eq!(paper.definitions.len(), 1);
        assert_eq!(paper.definitions[0].ref_label, "def:prime");
        assert_eq!(paper.theorems.len(), 1);
        assert_eq!(paper.theorems[0].ref_label, "thm:inf");
        assert!(!paper.theorems[0].proof_latex.is_empty());
        assert_eq!(paper.macros.len(), 1);
        assert_eq!(paper.macros[0].name, "NN");
    }
}
