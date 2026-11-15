// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Harvest rule instances from Carcara's own `test_cases!` rule tests.
//!
//! The rule test files are the richest source of well-formed instances for every rule Carcara
//! implements, including the deliberately wrong ones (`: false`). They are read at run time, so
//! regression tests added there automatically become battery seeds.

use std::fs;
use std::path::Path;

#[derive(Debug, Clone)]
pub struct Seed {
    pub file: String,
    pub test: String,
    pub group: String,
    pub defs: String,
    pub proof: String,
    pub expected: bool,
}

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Str(String),
    Ident(String),
    Punct(char),
}

fn lex(src: &str) -> Vec<Tok> {
    let b: Vec<char> = src.chars().collect();
    let mut i = 0;
    let mut out = Vec::new();
    while i < b.len() {
        let c = b[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '/' && i + 1 < b.len() && b[i + 1] == '/' {
            while i < b.len() && b[i] != '\n' {
                i += 1;
            }
        } else if c == 'r' && i + 1 < b.len() && (b[i + 1] == '#' || b[i + 1] == '"') {
            // Raw string r#"..."# (any number of hashes).
            let mut j = i + 1;
            let mut hashes = 0;
            while j < b.len() && b[j] == '#' {
                hashes += 1;
                j += 1;
            }
            if j >= b.len() || b[j] != '"' {
                out.push(Tok::Ident("r".into()));
                i += 1;
                continue;
            }
            j += 1;
            let start = j;
            loop {
                if j >= b.len() {
                    return out;
                }
                if b[j] == '"'
                    && b[j + 1..]
                        .iter()
                        .take(hashes)
                        .filter(|c| **c == '#')
                        .count()
                        == hashes
                {
                    break;
                }
                j += 1;
            }
            out.push(Tok::Str(b[start..j].iter().collect()));
            i = j + 1 + hashes;
        } else if c == '"' {
            let mut j = i + 1;
            let mut s = String::new();
            while j < b.len() && b[j] != '"' {
                if b[j] == '\\' && j + 1 < b.len() {
                    match b[j + 1] {
                        'n' => s.push('\n'),
                        't' => s.push('\t'),
                        '\\' => s.push('\\'),
                        '"' => s.push('"'),
                        '\n' => {
                            // Line continuation: skip the newline and leading whitespace.
                            j += 2;
                            while j < b.len() && b[j].is_whitespace() {
                                j += 1;
                            }
                            continue;
                        }
                        other => {
                            s.push('\\');
                            s.push(other);
                        }
                    }
                    j += 2;
                } else {
                    s.push(b[j]);
                    j += 1;
                }
            }
            out.push(Tok::Str(s));
            i = j + 1;
        } else if c.is_alphanumeric() || c == '_' {
            let start = i;
            while i < b.len() && (b[i].is_alphanumeric() || b[i] == '_') {
                i += 1;
            }
            out.push(Tok::Ident(b[start..i].iter().collect()));
        } else {
            out.push(Tok::Punct(c));
            i += 1;
        }
    }
    out
}

/// Extract every `test_cases! { definitions = "...", "group" { "proof": bool, ... } ... }`.
pub fn harvest_file(path: &Path) -> Vec<Seed> {
    let Ok(src) = fs::read_to_string(path) else {
        return Vec::new();
    };
    let file = path
        .file_name()
        .map(|f| f.to_string_lossy().to_string())
        .unwrap_or_default();
    let toks = lex(&src);
    let mut seeds = Vec::new();
    let mut current_test = String::new();
    let mut i = 0;
    while i < toks.len() {
        if toks[i] == Tok::Ident("fn".into()) {
            if let Some(Tok::Ident(name)) = toks.get(i + 1) {
                current_test = name.clone();
            }
        }
        if toks[i] == Tok::Ident("test_cases".into()) && toks.get(i + 1) == Some(&Tok::Punct('!')) {
            i += 2;
            // Expect `{ definitions = <str> ,`
            let mut j = i;
            while j < toks.len() && toks[j] != Tok::Ident("definitions".into()) {
                j += 1;
            }
            let defs = match toks.get(j + 2) {
                Some(Tok::Str(s)) => s.clone(),
                _ => {
                    i = j + 1;
                    continue;
                }
            };
            j += 3;
            if toks.get(j) == Some(&Tok::Punct(',')) {
                j += 1;
            }
            // Groups until the macro's closing brace.
            loop {
                match (toks.get(j), toks.get(j + 1)) {
                    (Some(Tok::Str(group)), Some(Tok::Punct('{'))) => {
                        let group = group.clone();
                        j += 2;
                        while let (
                            Some(Tok::Str(proof)),
                            Some(Tok::Punct(':')),
                            Some(Tok::Ident(b)),
                        ) = (toks.get(j), toks.get(j + 1), toks.get(j + 2))
                        {
                            seeds.push(Seed {
                                file: file.clone(),
                                test: current_test.clone(),
                                group: group.clone(),
                                defs: defs.clone(),
                                proof: proof.clone(),
                                expected: b == "true",
                            });
                            j += 3;
                            if toks.get(j) == Some(&Tok::Punct(',')) {
                                j += 1;
                            }
                        }
                        if toks.get(j) == Some(&Tok::Punct('}')) {
                            j += 1;
                        }
                    }
                    _ => break,
                }
            }
            i = j;
            continue;
        }
        i += 1;
    }
    seeds
}

pub fn harvest_dir(dir: &Path) -> Vec<Seed> {
    let mut entries: Vec<_> = fs::read_dir(dir)
        .map(|rd| rd.filter_map(Result::ok).map(|e| e.path()).collect())
        .unwrap_or_default();
    entries.sort();
    entries
        .iter()
        .filter(|p| p.extension().is_some_and(|e| e == "rs"))
        .flat_map(|p| harvest_file(p))
        .collect()
}
