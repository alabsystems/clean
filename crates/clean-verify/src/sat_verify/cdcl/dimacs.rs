// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DIMACS CNF parser.
//!
//! Parses the standard DIMACS CNF format used by SAT competition benchmarks
//! and most SAT solver interfaces. Format:
//!
//! ```text
//! c comment line
//! p cnf <num_vars> <num_clauses>
//! 1 -2 3 0
//! -1 2 0
//! ```

use super::{CdclError, CdclState, Clause};

/// Parse a DIMACS CNF string into a [`CdclState`].
pub fn parse_dimacs(input: &str) -> Result<CdclState, CdclError> {
    let mut num_vars = 0u32;
    let mut num_clauses = 0usize;
    let mut header_seen = false;
    let mut clauses: Vec<Clause> = Vec::new();
    let mut current_clause: Clause = Vec::new();

    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if line.starts_with("p cnf") || line.starts_with("p CNF") {
            if header_seen {
                return Err(CdclError::ParseError("duplicate header".to_string()));
            }
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() < 4 {
                return Err(CdclError::ParseError(format!("bad header: {line}")));
            }
            num_vars = parts[2]
                .parse()
                .map_err(|_| CdclError::ParseError(format!("bad num_vars: {}", parts[2])))?;
            num_clauses = parts[3]
                .parse()
                .map_err(|_| CdclError::ParseError(format!("bad num_clauses: {}", parts[3])))?;
            header_seen = true;
            continue;
        }
        if !header_seen {
            return Err(CdclError::ParseError("clause before header".to_string()));
        }
        for token in line.split_whitespace() {
            let lit: i32 = token
                .parse()
                .map_err(|_| CdclError::ParseError(format!("bad literal: {token}")))?;
            if lit == 0 {
                clauses.push(std::mem::take(&mut current_clause));
            } else {
                current_clause.push(lit);
            }
        }
    }
    // Handle unterminated clause (some generators omit trailing 0)
    if !current_clause.is_empty() {
        clauses.push(current_clause);
    }
    if !header_seen {
        return Err(CdclError::ParseError("no header found".to_string()));
    }
    if clauses.len() != num_clauses {
        return Err(CdclError::ParseError(format!(
            "expected {num_clauses} clauses, got {}",
            clauses.len()
        )));
    }
    Ok(CdclState::new(num_vars, clauses))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_dimacs_basic() {
        let input = "c test\np cnf 3 2\n1 -2 3 0\n-1 2 0\n";
        let state = parse_dimacs(input).expect("parse");
        assert_eq!(state.num_vars, 3);
        assert_eq!(state.clauses.len(), 2);
        assert_eq!(state.clauses[0], vec![1, -2, 3]);
        assert_eq!(state.clauses[1], vec![-1, 2]);
    }

    #[test]
    fn test_parse_dimacs_unit_clause() {
        let input = "p cnf 1 1\n1 0\n";
        let state = parse_dimacs(input).expect("parse");
        assert_eq!(state.clauses.len(), 1);
        assert_eq!(state.clauses[0], vec![1]);
    }

    #[test]
    fn test_parse_dimacs_empty_clauses() {
        let input = "p cnf 2 0\n";
        let state = parse_dimacs(input).expect("parse");
        assert_eq!(state.clauses.len(), 0);
    }

    #[test]
    fn test_parse_dimacs_no_header() {
        assert!(parse_dimacs("1 -2 0\n").is_err());
    }

    #[test]
    fn test_parse_dimacs_clause_count_mismatch() {
        let input = "p cnf 2 3\n1 -2 0\n";
        assert!(parse_dimacs(input).is_err());
    }

    #[test]
    fn test_parse_dimacs_comments_ignored() {
        let input = "c line 1\nc line 2\np cnf 2 1\nc mid\n1 -2 0\nc end\n";
        let state = parse_dimacs(input).expect("parse");
        assert_eq!(state.clauses.len(), 1);
    }

    #[test]
    fn test_parse_dimacs_multi_literal_per_line() {
        let input = "p cnf 4 1\n1 -2 3 -4 0\n";
        let state = parse_dimacs(input).expect("parse");
        assert_eq!(state.clauses[0], vec![1, -2, 3, -4]);
    }
}
