// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OPB format parser and writer for pseudo-Boolean constraints.
//!
//! The OPB format is the standard interchange format for the Pseudo-Boolean
//! Competition (PB-Comp) and pseudo-Boolean solvers. Each `.opb` file describes
//! a set of PB constraints and an optional optimization objective.
//!
//! ## Format
//!
//! ```text
//! * #variable= N #constraint= M
//! * optional comments
//! min: +1 x1 +2 x2 ;            (optional objective)
//! +1 x1 +2 ~x2 >= 3 ;           (constraint)
//! +1 x1 +1 x2 = 1 ;             (equality constraint)
//! ```
//!
//! ## References
//!
//! - PB Competition: <http://www.cril.univ-artois.fr/PB16/format.pdf>
//! - Eén & Sörensson, "Translating Pseudo-Boolean Constraints into SAT", JSAT 2006

use super::types::{PbConstraint, PbFormula, PbObjective};
use super::PbError;

/// Parse an OPB format string into a PB formula.
///
/// Accepts the standard PB competition format:
/// - Comment lines starting with `*`
/// - Objective line starting with `min:` or `max:` (optional)
/// - Constraint lines ending with `;`
/// - Operators: `>=` and `=`
pub(crate) fn parse_opb(input: &str) -> Result<PbFormula, PbError> {
    let mut num_vars: u32 = 0;
    let mut constraints: Vec<PbConstraint> = Vec::new();
    let mut objective: Option<PbObjective> = None;

    for line in input.lines() {
        let line = line.trim();

        // Skip empty lines.
        if line.is_empty() {
            continue;
        }

        // Comment lines.
        if line.starts_with('*') {
            // Parse header for variable/constraint counts.
            if let Some(nv) = extract_header_value(line, "#variable=") {
                num_vars = nv;
            }
            continue;
        }

        // Objective line.
        if line.starts_with("min:") || line.starts_with("max:") {
            let is_minimize = line.starts_with("min:");
            // Both "min:" and "max:" are 4 ASCII bytes; skip the prefix.
            let content = line[4..].trim().trim_end_matches(';').trim();
            let terms = parse_terms(content)?;
            // Update num_vars from objective terms.
            for &(_, lit) in &terms {
                num_vars = num_vars.max(lit.unsigned_abs());
            }
            objective = Some(if is_minimize {
                PbObjective::minimize(terms)
            } else {
                PbObjective::maximize(terms)
            });
            continue;
        }

        // Constraint line: must contain >= or = and end with ;
        if line.ends_with(';') {
            let line = line.trim_end_matches(';').trim();
            let parsed = parse_constraint_line(line)?;
            // Update num_vars from constraint terms.
            for constraint in &parsed {
                for &(_, lit) in &constraint.terms {
                    num_vars = num_vars.max(lit.unsigned_abs());
                }
            }
            constraints.extend(parsed);
        }
    }

    let mut formula = PbFormula::new(num_vars);
    for c in constraints {
        formula.add_constraint(c);
    }
    if let Some(obj) = objective {
        formula.set_objective(obj);
    }

    Ok(formula)
}

/// Write a PB formula in OPB format.
#[must_use]
pub(crate) fn write_opb(formula: &PbFormula) -> String {
    let mut out = String::new();

    // Header comment.
    out.push_str(&format!(
        "* #variable= {} #constraint= {}\n",
        formula.num_vars,
        formula.constraints.len()
    ));

    // Objective.
    if let Some(ref obj) = formula.objective {
        if obj.minimize {
            out.push_str("min: ");
        } else {
            out.push_str("max: ");
        }
        for &(coeff, lit) in &obj.terms {
            write_term(&mut out, coeff, lit);
        }
        out.push_str(";\n");
    }

    // Constraints.
    for constraint in &formula.constraints {
        for &(coeff, lit) in &constraint.terms {
            write_term(&mut out, coeff, lit);
        }
        out.push_str(&format!(">= {} ;\n", constraint.degree));
    }

    out
}

/// Format a single coefficient-literal term in OPB notation.
fn write_term(out: &mut String, coeff: i64, lit: i32) {
    let sign = if coeff >= 0 { "+" } else { "" };
    if lit > 0 {
        out.push_str(&format!("{sign}{coeff} x{lit} "));
    } else {
        out.push_str(&format!("{sign}{coeff} ~x{} ", -lit));
    }
}

/// Extract an integer value from a header comment line for a given key.
fn extract_header_value(line: &str, key: &str) -> Option<u32> {
    let idx = line.find(key)?;
    let after = &line[idx + key.len()..];
    let after = after.trim_start();
    // Read digits.
    let num_str: String = after.chars().take_while(|c| c.is_ascii_digit()).collect();
    num_str.parse().ok()
}

/// Parse a constraint line (without the trailing `;`).
///
/// Supports `>=` and `=` operators. An equality `LHS = k` is decomposed
/// into two constraints: `LHS >= k` and `-LHS >= -k`.
fn parse_constraint_line(line: &str) -> Result<Vec<PbConstraint>, PbError> {
    if let Some((lhs, rhs)) = line.split_once(">=") {
        let terms = parse_terms(lhs.trim())?;
        let degree = parse_degree(rhs.trim())?;
        Ok(vec![PbConstraint::new(terms, degree)])
    } else if let Some((lhs, rhs)) = line.split_once('=') {
        // Equality: LHS = k means LHS >= k AND -LHS >= -k
        // (equivalently, LHS >= k AND LHS <= k)
        // LHS <= k is: -LHS >= -k
        let terms = parse_terms(lhs.trim())?;
        let degree = parse_degree(rhs.trim())?;

        let negated_terms: Vec<(i64, i32)> = terms.iter().map(|&(c, l)| (-c, l)).collect();

        Ok(vec![
            PbConstraint::new(terms, degree),
            PbConstraint::new(negated_terms, -degree),
        ])
    } else {
        Err(PbError::ConversionError(format!(
            "constraint line missing operator (>= or =): {line}"
        )))
    }
}

/// Parse the RHS degree value.
fn parse_degree(s: &str) -> Result<i64, PbError> {
    s.trim()
        .parse::<i64>()
        .map_err(|e| PbError::ConversionError(format!("invalid degree '{s}': {e}")))
}

/// Parse a sequence of `[+/-]coeff literal` terms.
///
/// Literal format: `x<n>` for positive literal, `~x<n>` for negated literal.
fn parse_terms(s: &str) -> Result<Vec<(i64, i32)>, PbError> {
    let mut terms = Vec::new();
    let tokens: Vec<&str> = s.split_whitespace().collect();
    let mut i = 0;

    while i < tokens.len() {
        let token = tokens[i];

        // Parse coefficient (may have +/- prefix).
        let coeff: i64 = token
            .parse()
            .map_err(|e| PbError::ConversionError(format!("invalid coefficient '{token}': {e}")))?;

        i += 1;
        if i >= tokens.len() {
            return Err(PbError::ConversionError(
                "expected literal after coefficient".to_string(),
            ));
        }

        let lit_token = tokens[i];
        let lit = parse_literal(lit_token)?;
        terms.push((coeff, lit));

        i += 1;
    }

    Ok(terms)
}

/// Parse a literal token: `x<n>` -> positive, `~x<n>` -> negative.
fn parse_literal(s: &str) -> Result<i32, PbError> {
    if let Some(rest) = s.strip_prefix("~x") {
        let var: u32 = rest
            .parse()
            .map_err(|e| PbError::ConversionError(format!("invalid literal '{s}': {e}")))?;
        if var == 0 {
            return Err(PbError::LiteralOutOfBounds { literal: 0 });
        }
        Ok(-(var as i32))
    } else if let Some(rest) = s.strip_prefix('x') {
        let var: u32 = rest
            .parse()
            .map_err(|e| PbError::ConversionError(format!("invalid literal '{s}': {e}")))?;
        if var == 0 {
            return Err(PbError::LiteralOutOfBounds { literal: 0 });
        }
        Ok(var as i32)
    } else {
        Err(PbError::ConversionError(format!(
            "invalid literal format '{s}': expected x<n> or ~x<n>"
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_opb_basic() {
        let input = "\
* #variable= 3 #constraint= 2
+1 x1 +2 ~x2 >= 3 ;
+1 x1 +1 x2 +1 x3 >= 2 ;
";
        let formula = parse_opb(input).expect("should parse valid OPB");
        assert_eq!(formula.num_vars, 3);
        assert_eq!(formula.constraints.len(), 2);

        // First constraint: 1*x1 + 2*~x2 >= 3
        assert_eq!(formula.constraints[0].terms, vec![(1, 1), (2, -2)]);
        assert_eq!(formula.constraints[0].degree, 3);

        // Second constraint: 1*x1 + 1*x2 + 1*x3 >= 2
        assert_eq!(formula.constraints[1].degree, 2);
    }

    #[test]
    fn test_parse_opb_with_objective() {
        let input = "\
* #variable= 2 #constraint= 1
min: +1 x1 +2 x2 ;
+1 x1 +1 x2 >= 1 ;
";
        let formula = parse_opb(input).expect("should parse OPB with objective");
        assert!(formula.objective.is_some());
        let obj = formula.objective.as_ref().unwrap();
        assert!(obj.minimize);
        assert_eq!(obj.terms, vec![(1, 1), (2, 2)]);
    }

    #[test]
    fn test_parse_opb_equality_constraint() {
        let input = "\
* #variable= 2 #constraint= 1
+1 x1 +1 x2 = 1 ;
";
        let formula = parse_opb(input).expect("should parse equality constraint");
        // Equality becomes two constraints: >= and <=
        assert_eq!(formula.constraints.len(), 2);
        assert_eq!(formula.constraints[0].degree, 1); // x1 + x2 >= 1
        assert_eq!(formula.constraints[1].degree, -1); // -x1 - x2 >= -1
    }

    #[test]
    fn test_write_opb_basic() {
        let mut formula = PbFormula::new(3);
        formula.add_constraint(PbConstraint::new(vec![(1, 1), (2, -2)], 3));
        formula.add_constraint(PbConstraint::new(vec![(1, 1), (1, 2), (1, 3)], 2));

        let output = write_opb(&formula);
        assert!(output.contains("* #variable= 3 #constraint= 2"));
        assert!(output.contains("+1 x1 +2 ~x2 >= 3 ;"));
        assert!(output.contains("+1 x1 +1 x2 +1 x3 >= 2 ;"));
    }

    #[test]
    fn test_write_opb_with_objective() {
        let mut formula = PbFormula::new(2);
        formula.add_constraint(PbConstraint::new(vec![(1, 1), (1, 2)], 1));
        formula.set_objective(PbObjective::minimize(vec![(1, 1), (2, 2)]));

        let output = write_opb(&formula);
        assert!(output.contains("min: +1 x1 +2 x2 ;"));
    }

    #[test]
    fn test_opb_roundtrip() {
        let mut original = PbFormula::new(3);
        original.add_constraint(PbConstraint::new(vec![(1, 1), (2, 2), (3, 3)], 4));
        original.add_constraint(PbConstraint::new(vec![(1, -1), (1, 2)], 1));
        original.set_objective(PbObjective::minimize(vec![(1, 1), (1, 2)]));

        let opb_text = write_opb(&original);
        let parsed = parse_opb(&opb_text).expect("roundtrip should parse");

        assert_eq!(parsed.num_vars, original.num_vars);
        assert_eq!(parsed.constraints.len(), original.constraints.len());

        for (orig, parsed) in original.constraints.iter().zip(parsed.constraints.iter()) {
            assert_eq!(orig.terms, parsed.terms);
            assert_eq!(orig.degree, parsed.degree);
        }
    }

    #[test]
    fn test_parse_opb_comments_ignored() {
        let input = "\
* This is a comment
* #variable= 2 #constraint= 1
* Another comment
+1 x1 +1 x2 >= 1 ;
";
        let formula = parse_opb(input).expect("comments should be ignored");
        assert_eq!(formula.constraints.len(), 1);
    }

    #[test]
    fn test_parse_opb_negative_coefficients() {
        let input = "\
* #variable= 2 #constraint= 1
+3 x1 -2 x2 >= 1 ;
";
        let formula = parse_opb(input).expect("negative coefficients should parse");
        assert_eq!(formula.constraints[0].terms, vec![(3, 1), (-2, 2)]);
    }

    #[test]
    fn test_parse_opb_invalid_literal_rejected() {
        let input = "\
* #variable= 1 #constraint= 1
+1 y1 >= 1 ;
";
        let result = parse_opb(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_opb_empty_input() {
        let formula = parse_opb("").expect("empty input is valid");
        assert_eq!(formula.num_vars, 0);
        assert_eq!(formula.constraints.len(), 0);
    }

    #[test]
    fn test_write_opb_negative_coefficients() {
        let mut formula = PbFormula::new(2);
        formula.add_constraint(PbConstraint::new(vec![(3, 1), (-2, 2)], 1));

        let output = write_opb(&formula);
        assert!(output.contains("+3 x1 -2 x2 >= 1 ;"));
    }
}
