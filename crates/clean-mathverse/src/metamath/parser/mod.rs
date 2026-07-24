// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metamath `.mm` file parser.
//!
//! Parses the full `.mm` format including:
//! - `$c` (constant), `$v` (variable) declarations
//! - `$a` (axiom), `$p` (provable) assertions
//! - `$f` (floating), `$e` (essential) hypotheses
//! - `${ ... $}` scope blocks
//! - `$( ... $)` comments (skipped)
//! - Normal and compressed proof formats
//!
//! Reference: <http://us.metamath.org/mpe/mmset.html>

use crate::error::{MathverseError, MathverseResult};

use super::types::{
    MmDatabase, MmExpression, MmProof, MmProofFormat, MmStatement, MmStatementKind,
};

// ════════════════════════════════════════════════════════════════════════════
// Public API
// ════════════════════════════════════════════════════════════════════════════

/// Parse a Metamath `.mm` file from its text content.
///
/// # Errors
///
/// Returns an error if the input contains malformed syntax (unclosed comments,
/// unexpected tokens, missing `$.` terminators, etc.).
pub fn parse_mm(input: &str) -> MathverseResult<MmDatabase> {
    let tokens = tokenize(input)?;
    parse_tokens(&tokens)
}

// ════════════════════════════════════════════════════════════════════════════
// Tokenizer
// ════════════════════════════════════════════════════════════════════════════

/// Tokenize input, stripping `$( ... $)` comments.
///
/// Metamath tokens are separated by whitespace. The only multi-character
/// tokens that need special handling are comment delimiters `$(` and `$)`.
pub(crate) fn tokenize(input: &str) -> MathverseResult<Vec<String>> {
    let raw_tokens: Vec<&str> = input.split_whitespace().collect();
    let mut result = Vec::new();
    let mut in_comment = false;
    let mut comment_depth: usize = 0;

    for token in raw_tokens {
        if in_comment {
            if token == "$)" {
                comment_depth -= 1;
                if comment_depth == 0 {
                    in_comment = false;
                }
            } else if token == "$(" {
                comment_depth += 1;
            }
            continue;
        }

        if token == "$(" {
            in_comment = true;
            comment_depth = 1;
            continue;
        }

        result.push(token.to_string());
    }

    if in_comment {
        return Err(MathverseError::ImportFailed {
            system: "Metamath".to_string(),
            reason: "unclosed comment: $( without matching $)".to_string(),
        });
    }

    Ok(result)
}

// ════════════════════════════════════════════════════════════════════════════
// Parser
// ════════════════════════════════════════════════════════════════════════════

/// Scope frame for `${ ... $}` blocks.
struct Scope {
    /// Variables declared in this scope.
    variables: Vec<String>,
    /// Hypothesis labels declared in this scope.
    hypotheses: Vec<String>,
}

/// Parse a token stream into an `MmDatabase`.
fn parse_tokens(tokens: &[String]) -> MathverseResult<MmDatabase> {
    let mut db = MmDatabase::default();
    let mut scopes: Vec<Scope> = vec![Scope {
        variables: Vec::new(),
        hypotheses: Vec::new(),
    }];
    let mut pos = 0;

    while pos < tokens.len() {
        let token = &tokens[pos];
        match token.as_str() {
            "$c" => {
                pos += 1;
                pos = parse_constant_decl(&tokens[pos..], &mut db)? + pos;
            }
            "$v" => {
                pos += 1;
                pos = parse_variable_decl(&tokens[pos..], &mut db, &mut scopes)? + pos;
            }
            "${" => {
                scopes.push(Scope {
                    variables: Vec::new(),
                    hypotheses: Vec::new(),
                });
                pos += 1;
            }
            "$}" => {
                if scopes.len() <= 1 {
                    return Err(mm_error("unexpected $} without matching ${"));
                }
                scopes.pop();
                pos += 1;
            }
            "$d" => {
                pos += 1;
                while pos < tokens.len() && tokens[pos] != "$." {
                    pos += 1;
                }
                pos += 1;
            }
            _ => {
                let advance = parse_labeled_stmt(token, &tokens[pos..], &mut db, &mut scopes)?;
                pos += advance;
            }
        }
    }
    Ok(db)
}

/// Parse a labeled statement: `<label> <keyword> <body> $.`
///
/// Returns the total number of tokens consumed (including the label).
fn parse_labeled_stmt(
    label_token: &str,
    tokens: &[String],
    db: &mut MmDatabase,
    scopes: &mut [Scope],
) -> MathverseResult<usize> {
    if tokens.len() < 2 {
        return Err(mm_error(&format!(
            "unexpected end of input after label '{label_token}'"
        )));
    }
    let label = label_token.to_string();
    let keyword = &tokens[1];
    let body = &tokens[2..];

    match keyword.as_str() {
        "$f" | "$e" => {
            let kind = if keyword == "$f" {
                MmStatementKind::FloatingHyp
            } else {
                MmStatementKind::EssentialHyp
            };
            let (stmt, advance) = parse_hypothesis(&label, kind, body, scopes)?;
            db.statements.push(stmt);
            if let Some(scope) = scopes.last_mut() {
                scope.hypotheses.push(label);
            }
            Ok(2 + advance)
        }
        "$a" => {
            let (stmt, advance) = parse_axiom(&label, body, scopes)?;
            db.statements.push(stmt);
            Ok(2 + advance)
        }
        "$p" => {
            let (stmt, advance) = parse_theorem(&label, body, scopes)?;
            db.statements.push(stmt);
            Ok(2 + advance)
        }
        _ => Err(mm_error(&format!(
            "unexpected keyword '{keyword}' after label '{label}'"
        ))),
    }
}

/// Construct a Metamath import error.
fn mm_error(reason: &str) -> MathverseError {
    MathverseError::ImportFailed {
        system: "Metamath".to_string(),
        reason: reason.to_string(),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Declaration parsers
// ════════════════════════════════════════════════════════════════════════════

/// Parse `$c tok1 tok2 ... $.` — returns tokens consumed (including `$.`).
fn parse_constant_decl(tokens: &[String], db: &mut MmDatabase) -> MathverseResult<usize> {
    for (i, tok) in tokens.iter().enumerate() {
        if tok == "$." {
            return Ok(i + 1);
        }
        db.constants.push(tok.clone());
    }
    Err(mm_error("unterminated $c declaration: missing $."))
}

/// Parse `$v var1 var2 ... $.` — returns tokens consumed (including `$.`).
fn parse_variable_decl(
    tokens: &[String],
    db: &mut MmDatabase,
    scopes: &mut [Scope],
) -> MathverseResult<usize> {
    for (i, tok) in tokens.iter().enumerate() {
        if tok == "$." {
            return Ok(i + 1);
        }
        db.variables.push(tok.clone());
        if let Some(scope) = scopes.last_mut() {
            scope.variables.push(tok.clone());
        }
    }
    Err(mm_error("unterminated $v declaration: missing $."))
}

/// Collect tokens until `$.`, returning expression tokens and advance count.
fn collect_until_terminator(tokens: &[String]) -> MathverseResult<(Vec<String>, usize)> {
    let mut result = Vec::new();
    for (i, tok) in tokens.iter().enumerate() {
        if tok == "$." {
            return Ok((result, i + 1));
        }
        result.push(tok.clone());
    }
    Err(mm_error("missing $. terminator"))
}

/// Parse a hypothesis (`$f` or `$e`): `<tokens...> $.`
fn parse_hypothesis(
    label: &str,
    kind: MmStatementKind,
    tokens: &[String],
    scopes: &[Scope],
) -> MathverseResult<(MmStatement, usize)> {
    let (expr_tokens, advance) = collect_until_terminator(tokens)
        .map_err(|_| mm_error(&format!("unterminated hypothesis '{label}': missing $.")))?;
    let stmt = MmStatement {
        label: label.to_string(),
        kind,
        expression: MmExpression {
            tokens: expr_tokens,
        },
        proof: None,
        hypotheses: collect_active_hypotheses(scopes),
    };
    Ok((stmt, advance))
}

/// Parse an axiom (`$a`): `<tokens...> $.`
fn parse_axiom(
    label: &str,
    tokens: &[String],
    scopes: &[Scope],
) -> MathverseResult<(MmStatement, usize)> {
    let (expr_tokens, advance) = collect_until_terminator(tokens)
        .map_err(|_| mm_error(&format!("unterminated axiom '{label}': missing $.")))?;
    let stmt = MmStatement {
        label: label.to_string(),
        kind: MmStatementKind::Axiom,
        expression: MmExpression {
            tokens: expr_tokens,
        },
        proof: None,
        hypotheses: collect_active_hypotheses(scopes),
    };
    Ok((stmt, advance))
}

/// Parse a theorem (`$p`): `<tokens...> $= <proof_tokens...> $.`
fn parse_theorem(
    label: &str,
    tokens: &[String],
    scopes: &[Scope],
) -> MathverseResult<(MmStatement, usize)> {
    // Split at $= marker
    let mut split_pos = None;
    for (i, tok) in tokens.iter().enumerate() {
        if tok == "$=" {
            split_pos = Some(i);
            break;
        }
        if tok == "$." {
            return Err(mm_error(&format!(
                "theorem '{label}' has $. before $= (missing proof)"
            )));
        }
    }
    let eq_pos =
        split_pos.ok_or_else(|| mm_error(&format!("theorem '{label}' missing $= proof marker")))?;

    let expr_tokens: Vec<String> = tokens[..eq_pos].to_vec();
    let proof_start = eq_pos + 1;
    let (proof, proof_advance) = parse_proof(&tokens[proof_start..])?;

    let stmt = MmStatement {
        label: label.to_string(),
        kind: MmStatementKind::Theorem,
        expression: MmExpression {
            tokens: expr_tokens,
        },
        proof: Some(proof),
        hypotheses: collect_active_hypotheses(scopes),
    };
    Ok((stmt, proof_start + proof_advance))
}

// ════════════════════════════════════════════════════════════════════════════
// Proof parsers
// ════════════════════════════════════════════════════════════════════════════

/// Parse proof tokens: normal or compressed format.
fn parse_proof(tokens: &[String]) -> MathverseResult<(MmProof, usize)> {
    if tokens.is_empty() {
        return Err(mm_error("empty proof section"));
    }
    if tokens[0] == "(" {
        parse_compressed_proof(tokens)
    } else {
        parse_normal_proof(tokens)
    }
}

/// Parse a normal proof: `label1 label2 ... $.`
fn parse_normal_proof(tokens: &[String]) -> MathverseResult<(MmProof, usize)> {
    let (steps, advance) =
        collect_until_terminator(tokens).map_err(|_| mm_error("unterminated proof: missing $."))?;
    Ok((
        MmProof {
            format: MmProofFormat::Normal,
            steps,
        },
        advance,
    ))
}

/// Parse a compressed proof: `( label1 ... ) ENCODED $.`
fn parse_compressed_proof(tokens: &[String]) -> MathverseResult<(MmProof, usize)> {
    let mut i = 1; // skip '('
    let mut labels = Vec::new();

    while i < tokens.len() {
        if tokens[i] == ")" {
            i += 1;
            break;
        }
        labels.push(tokens[i].clone());
        i += 1;
    }

    let mut encoded = String::new();
    while i < tokens.len() {
        if tokens[i] == "$." {
            let mut steps = labels;
            if !encoded.is_empty() {
                steps.push(encoded);
            }
            return Ok((
                MmProof {
                    format: MmProofFormat::Compressed,
                    steps,
                },
                i + 1,
            ));
        }
        encoded.push_str(&tokens[i]);
        i += 1;
    }
    Err(mm_error("unterminated compressed proof: missing $."))
}

/// Collect all active hypothesis labels from all scope frames.
fn collect_active_hypotheses(scopes: &[Scope]) -> Vec<String> {
    scopes
        .iter()
        .flat_map(|s| s.hypotheses.iter().cloned())
        .collect()
}

#[cfg(test)]
mod tests;
