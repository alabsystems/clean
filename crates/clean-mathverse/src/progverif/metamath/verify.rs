// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metamath RPN proof verification engine.
//!
//! Implements the standard Metamath stack-based proof verification algorithm.
//! Parses a complete `.mm` file (handling `$v`, `$f`, `$e`, `$d`, `$a`, `$p`,
//! scoping), then replays each theorem's RPN proof to verify correctness.
//!
//! Reference: <https://us.metamath.org/downloads/metamath.pdf> §4.

use std::collections::{HashMap, HashSet};

use super::MetamathError;

/// Result of verifying all theorems in a Metamath database.
#[derive(Debug, Clone, Default)]
pub struct VerifyResult {
    /// Theorems whose proofs verified successfully (normal RPN proofs).
    pub verified: usize,
    /// Theorems whose proofs failed verification.
    pub failed: usize,
    /// Axioms (not verified, accepted by definition).
    pub axioms: usize,
    /// Theorems with compressed proofs (skipped, not yet implemented).
    pub compressed_skipped: usize,
    /// Labels of theorems that failed verification (first N).
    pub failed_labels: Vec<String>,
    /// Total proof steps processed.
    pub total_steps: usize,
    /// Labels of theorems whose RPN proof verified successfully — used to mark
    /// the corresponding shard constants as `SourceVerified` (checked by
    /// Metamath's own proof verifier) rather than merely `Translated`.
    pub verified_labels: HashSet<String>,
}

/// Verify all proofs in a Metamath database text and return the set of theorem
/// labels whose RPN proof checked successfully. Returns an empty set if the text
/// fails to parse. Used at import time to upgrade verified theorems' confidence.
#[must_use]
pub fn verified_labels(text: &str) -> HashSet<String> {
    parse_and_verify(text)
        .map(|r| r.verified_labels)
        .unwrap_or_default()
}

/// Internal representation of a label's information.
#[derive(Debug, Clone)]
pub(crate) enum LabelInfo {
    /// Floating hypothesis: `<label> $f <typecode> <variable> $.`
    FloatingHyp { typecode: String, variable: String },
    /// Essential hypothesis: `<label> $e <tokens...> $.`
    EssentialHyp { expression: Vec<String> },
    /// Axiom or theorem assertion.
    Assertion {
        expression: Vec<String>,
        /// Mandatory floating hypotheses in order (label, typecode, variable).
        mand_floats: Vec<(String, String, String)>,
        /// Mandatory essential hypotheses in order (label, expression).
        mand_essentials: Vec<(String, Vec<String>)>,
        /// This assertion's MANDATORY distinct-variable pairs — the `$d`
        /// constraints it imposes on callers, restricted to its own mandatory
        /// variables. When the assertion is applied in a proof, the variables
        /// substituted for each such pair must be provably distinct in the
        /// calling theorem's frame.
        disjoint_pairs: Vec<(String, String)>,
        /// The FULL set of distinct-variable pairs active in this statement's
        /// frame, INCLUDING dummy variables used only in the proof. Used as the
        /// caller's `$d` frame: every substituted variable pair arising from an
        /// applied assertion's mandatory `$d` must appear here.
        full_disjoint: Vec<(String, String)>,
        /// Proof steps (empty for axioms).
        proof_steps: Vec<String>,
    },
}

/// Parse a Metamath `.mm` file and verify all theorem proofs.
///
/// Returns a `VerifyResult` summarizing how many proofs pass/fail.
/// Parse errors are returned as `Err`.
pub fn parse_and_verify(text: &str) -> Result<VerifyResult, MetamathError> {
    let tokens = tokenize(text);
    let labels = build_label_table(&tokens)?;
    // The set of all variables — every token that has a floating hypothesis.
    // Used to identify which tokens inside a substitution are variables when
    // enforcing $d distinct-variable conditions.
    let variables: HashSet<String> = labels
        .values()
        .filter_map(|info| match info {
            LabelInfo::FloatingHyp { variable, .. } => Some(variable.clone()),
            _ => None,
        })
        .collect();
    verify_all_proofs(&labels, &variables)
}

/// Normalize a variable pair so $d lookups are order-independent.
fn norm_pair(a: &str, b: &str) -> (String, String) {
    if a <= b {
        (a.to_string(), b.to_string())
    } else {
        (b.to_string(), a.to_string())
    }
}

/// Tokenize Metamath text, stripping comments.
pub(crate) fn tokenize(text: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut in_comment = false;

    for word in text.split_whitespace() {
        if in_comment {
            if word.ends_with("$)") || word == "$)" {
                in_comment = false;
            }
            continue;
        }
        if word.starts_with("$(") || word == "$(" {
            in_comment = true;
            // Check if comment ends on same token: "$( ... $)"
            if word.ends_with("$)") {
                in_comment = false;
            }
            continue;
        }
        tokens.push(word.to_string());
    }
    tokens
}

/// Scope frame tracking active hypotheses during parsing.
#[derive(Clone, Default)]
struct ScopeFrame {
    /// Variables declared in this scope.
    variables: Vec<String>,
    /// Floating hypotheses in this scope: (label, typecode, variable).
    float_hyps: Vec<(String, String, String)>,
    /// Essential hypotheses in this scope: (label, expression).
    ess_hyps: Vec<(String, Vec<String>)>,
    /// Disjoint variable pairs in this scope.
    disjoint: Vec<(String, String)>,
}

/// Build the label table by parsing the full token stream.
pub(crate) fn build_label_table(
    tokens: &[String],
) -> Result<HashMap<String, LabelInfo>, MetamathError> {
    let mut labels: HashMap<String, LabelInfo> = HashMap::new();
    let mut scope_stack: Vec<ScopeFrame> = vec![ScopeFrame::default()];
    let mut constants: std::collections::HashSet<String> = std::collections::HashSet::new();

    let mut i = 0;
    while i < tokens.len() {
        let tok = &tokens[i];

        match tok.as_str() {
            "${" => {
                scope_stack.push(ScopeFrame::default());
                i += 1;
            }
            "$}" => {
                if scope_stack.len() <= 1 {
                    return Err(MetamathError::DatabaseError {
                        reason: "unmatched $}".to_string(),
                    });
                }
                scope_stack.pop();
                i += 1;
            }
            "$c" => {
                // Constant declaration: $c <tokens...> $.
                i += 1;
                while i < tokens.len() && tokens[i] != "$." {
                    constants.insert(tokens[i].clone());
                    i += 1;
                }
                i += 1; // skip $.
            }
            "$v" => {
                // Variable declaration: $v <tokens...> $.
                i += 1;
                // INVARIANT: scope_stack starts with one frame and `$}`
                // refuses to pop below 1, so `last_mut()` is always Some.
                let frame = scope_stack
                    .last_mut()
                    .expect("invariant: scope_stack non-empty");
                while i < tokens.len() && tokens[i] != "$." {
                    frame.variables.push(tokens[i].clone());
                    i += 1;
                }
                i += 1; // skip $.
            }
            "$d" => {
                // Disjoint variable condition: $d <var1> <var2> ... $.
                i += 1;
                let mut vars = Vec::new();
                while i < tokens.len() && tokens[i] != "$." {
                    vars.push(tokens[i].clone());
                    i += 1;
                }
                i += 1; // skip $.
                let frame = scope_stack
                    .last_mut()
                    .expect("invariant: scope_stack non-empty");
                for a in 0..vars.len() {
                    for b in (a + 1)..vars.len() {
                        frame.disjoint.push((vars[a].clone(), vars[b].clone()));
                    }
                }
            }
            _ => {
                // Could be a label. Check if next token is a keyword.
                if i + 1 < tokens.len() {
                    match tokens[i + 1].as_str() {
                        "$f" => {
                            // Floating hypothesis: <label> $f <typecode> <variable> $.
                            let label = tok.clone();
                            i += 2; // skip label and $f
                            let typecode = tokens.get(i).cloned().unwrap_or_default();
                            i += 1;
                            let variable = tokens.get(i).cloned().unwrap_or_default();
                            i += 1;
                            if i < tokens.len() && tokens[i] == "$." {
                                i += 1;
                            }
                            let frame = scope_stack
                                .last_mut()
                                .expect("invariant: scope_stack non-empty");
                            frame.float_hyps.push((
                                label.clone(),
                                typecode.clone(),
                                variable.clone(),
                            ));
                            labels.insert(label, LabelInfo::FloatingHyp { typecode, variable });
                        }
                        "$e" => {
                            // Essential hypothesis: <label> $e <tokens...> $.
                            let label = tok.clone();
                            i += 2; // skip label and $e
                            let mut expr = Vec::new();
                            while i < tokens.len() && tokens[i] != "$." {
                                expr.push(tokens[i].clone());
                                i += 1;
                            }
                            i += 1; // skip $.
                            let frame = scope_stack
                                .last_mut()
                                .expect("invariant: scope_stack non-empty");
                            frame.ess_hyps.push((label.clone(), expr.clone()));
                            labels.insert(label, LabelInfo::EssentialHyp { expression: expr });
                        }
                        "$a" => {
                            // Axiom: <label> $a <tokens...> $.
                            let label = tok.clone();
                            i += 2; // skip label and $a
                            let mut expr = Vec::new();
                            while i < tokens.len() && tokens[i] != "$." {
                                expr.push(tokens[i].clone());
                                i += 1;
                            }
                            i += 1; // skip $.
                            let (mf, me, dp, fd) =
                                collect_mandatory_frame(&scope_stack, &expr, &constants);
                            labels.insert(
                                label,
                                LabelInfo::Assertion {
                                    expression: expr,
                                    mand_floats: mf,
                                    mand_essentials: me,
                                    disjoint_pairs: dp,
                                    full_disjoint: fd,
                                    proof_steps: Vec::new(),
                                },
                            );
                        }
                        "$p" => {
                            // Theorem: <label> $p <tokens...> $= <proof...> $.
                            let label = tok.clone();
                            i += 2; // skip label and $p
                            let mut expr = Vec::new();
                            while i < tokens.len() && tokens[i] != "$=" && tokens[i] != "$." {
                                expr.push(tokens[i].clone());
                                i += 1;
                            }
                            if i < tokens.len() && tokens[i] == "$=" {
                                i += 1; // skip $=
                            }
                            let mut proof = Vec::new();
                            while i < tokens.len() && tokens[i] != "$." {
                                proof.push(tokens[i].clone());
                                i += 1;
                            }
                            i += 1; // skip $.
                            let (mf, me, dp, fd) =
                                collect_mandatory_frame(&scope_stack, &expr, &constants);
                            labels.insert(
                                label,
                                LabelInfo::Assertion {
                                    expression: expr,
                                    mand_floats: mf,
                                    mand_essentials: me,
                                    disjoint_pairs: dp,
                                    full_disjoint: fd,
                                    proof_steps: proof,
                                },
                            );
                        }
                        _ => {
                            i += 1; // unknown token, skip
                        }
                    }
                } else {
                    i += 1;
                }
            }
        }
    }

    Ok(labels)
}

/// Collect the mandatory frame for an assertion:
/// - Mandatory floating hypotheses: one per variable in expr or essential hyps
/// - Mandatory essential hypotheses: all $e in scope
/// - Disjoint variable pairs: all $d in scope
fn collect_mandatory_frame(
    scope_stack: &[ScopeFrame],
    expr: &[String],
    constants: &std::collections::HashSet<String>,
) -> (
    Vec<(String, String, String)>,
    Vec<(String, Vec<String>)>,
    Vec<(String, String)>,
    Vec<(String, String)>,
) {
    // Collect all essential hypotheses and disjoint conditions from all scopes.
    let mut all_essentials = Vec::new();
    let mut all_disjoint = Vec::new();
    let mut all_floats = Vec::new();

    for frame in scope_stack {
        all_floats.extend(frame.float_hyps.iter().cloned());
        all_essentials.extend(frame.ess_hyps.iter().cloned());
        all_disjoint.extend(frame.disjoint.iter().cloned());
    }

    // Find all variables used in the expression and essential hypotheses.
    let mut used_vars: std::collections::HashSet<String> = std::collections::HashSet::new();
    for token in expr {
        if !constants.contains(token) {
            used_vars.insert(token.clone());
        }
    }
    for (_, ess_expr) in &all_essentials {
        for token in ess_expr {
            if !constants.contains(token) {
                used_vars.insert(token.clone());
            }
        }
    }

    // Mandatory floating hypotheses: those whose variable is used.
    let mand_floats: Vec<_> = all_floats
        .into_iter()
        .filter(|(_, _, var)| used_vars.contains(var))
        .collect();

    // Mandatory disjoint pairs: those where both variables appear in the
    // statement/essentials. The FULL active set (`all_disjoint`) is also
    // returned so callers can use it as their $d frame, which must include
    // dummy-variable pairs used only inside proofs.
    let mand_disjoint: Vec<_> = all_disjoint
        .iter()
        .filter(|(a, b)| used_vars.contains(a) && used_vars.contains(b))
        .cloned()
        .collect();

    (mand_floats, all_essentials, mand_disjoint, all_disjoint)
}

/// Verify all theorem proofs in the label table.
fn verify_all_proofs(
    labels: &HashMap<String, LabelInfo>,
    variables: &HashSet<String>,
) -> Result<VerifyResult, MetamathError> {
    let mut result = VerifyResult::default();

    // Per-proof verification is independent of the order in which we iterate
    // theorems; each proof is checked against the whole label table plus the
    // theorem's own $d frame.
    for (label, info) in labels {
        match info {
            LabelInfo::Assertion { proof_steps, .. } if proof_steps.is_empty() => {
                result.axioms += 1;
            }
            LabelInfo::Assertion {
                expression,
                mand_floats,
                mand_essentials,
                full_disjoint,
                proof_steps,
                ..
            } => {
                result.total_steps += proof_steps.len();
                // The theorem's $d frame: every active distinct-variable pair,
                // normalized so membership tests are order-independent.
                let theorem_disjoints: HashSet<(String, String)> =
                    full_disjoint.iter().map(|(a, b)| norm_pair(a, b)).collect();
                match verify_single_proof(
                    label,
                    expression,
                    mand_floats,
                    mand_essentials,
                    proof_steps,
                    labels,
                    &theorem_disjoints,
                    variables,
                ) {
                    Ok(ProofOutcome::Verified) => {
                        result.verified += 1;
                        result.verified_labels.insert(label.clone());
                    }
                    Ok(ProofOutcome::CompressedSkipped) => {
                        result.compressed_skipped += 1;
                    }
                    Err(ref e) => {
                        result.failed += 1;
                        if result.failed_labels.len() < 20 {
                            result.failed_labels.push(format!("{}: {}", label, e));
                        }
                    }
                }
            }
            _ => {} // floating/essential hyps — not verified
        }
    }

    Ok(result)
}

/// Outcome of a single proof verification.
enum ProofOutcome {
    /// Proof verified successfully via RPN stack machine.
    Verified,
    /// Compressed proof format — skipped (not yet implemented).
    CompressedSkipped,
}

/// Execute a single RPN proof step: look up label, apply to stack.
fn execute_proof_step(
    step_label: &str,
    stack: &mut Vec<Vec<String>>,
    labels: &HashMap<String, LabelInfo>,
    theorem_label: &str,
    theorem_disjoints: &HashSet<(String, String)>,
    variables: &HashSet<String>,
) -> Result<(), MetamathError> {
    // A Metamath proof may only cite EARLIER statements; a step that names the
    // theorem being proved is circular and never valid.
    if step_label == theorem_label {
        return Err(MetamathError::ProofVerificationFailed {
            theorem: theorem_label.to_string(),
            reason: format!("circular proof: step references the theorem `{step_label}` itself"),
        });
    }

    let info = labels
        .get(step_label)
        .ok_or_else(|| MetamathError::UnknownLabel {
            theorem: theorem_label.to_string(),
            label: step_label.to_string(),
        })?;

    match info {
        LabelInfo::FloatingHyp { typecode, variable } => {
            stack.push(vec![typecode.clone(), variable.clone()]);
        }
        LabelInfo::EssentialHyp { expression } => {
            stack.push(expression.clone());
        }
        LabelInfo::Assertion {
            expression,
            mand_floats: ref_floats,
            mand_essentials: ref_essentials,
            disjoint_pairs: ref_disjoints,
            ..
        } => {
            let n_hyps = ref_floats.len() + ref_essentials.len();
            if stack.len() < n_hyps {
                return Err(MetamathError::ProofVerificationFailed {
                    theorem: theorem_label.to_string(),
                    reason: format!(
                        "stack underflow at label `{step_label}`: need {n_hyps}, have {}",
                        stack.len()
                    ),
                });
            }

            // Pop hypotheses from stack.
            let start = stack.len() - n_hyps;
            let popped: Vec<Vec<String>> = stack.drain(start..).collect();

            // Build substitution map from floating hypotheses.
            // Each float hyp has (label, typecode, variable). The popped entry
            // must start with the same typecode; the rest is the substitution.
            let mut subst: HashMap<String, Vec<String>> = HashMap::new();
            for (i, (_, typecode, variable)) in ref_floats.iter().enumerate() {
                if i < popped.len() {
                    let popped_expr = &popped[i];
                    // Verify typecode matches (first token of popped expression).
                    if popped_expr.first() != Some(typecode) {
                        return Err(MetamathError::ProofVerificationFailed {
                            theorem: theorem_label.to_string(),
                            reason: format!(
                                "typecode mismatch at `{step_label}` for variable `{variable}`: \
                                 expected `{typecode}`, got `{}`",
                                popped_expr.first().map_or("(empty)", String::as_str),
                            ),
                        });
                    }
                    subst.insert(variable.clone(), popped_expr[1..].to_vec());
                }
            }

            // Verify essential hypotheses match their substituted forms.
            let float_count = ref_floats.len();
            for (j, (_, ess_expr)) in ref_essentials.iter().enumerate() {
                let popped_idx = float_count + j;
                if popped_idx < popped.len() {
                    let expected = apply_subst(ess_expr, &subst);
                    if popped[popped_idx] != expected {
                        return Err(MetamathError::ProofVerificationFailed {
                            theorem: theorem_label.to_string(),
                            reason: format!(
                                "essential hypothesis mismatch at `{step_label}`: \
                                 got {:?}, expected {:?}",
                                &popped[popped_idx][..std::cmp::min(10, popped[popped_idx].len())],
                                &expected[..std::cmp::min(10, expected.len())],
                            ),
                        });
                    }
                }
            }

            // Enforce the applied assertion's mandatory $d conditions: for each
            // required distinct pair, the variables actually substituted in must
            // be pairwise distinct AND declared disjoint in the calling theorem.
            enforce_disjoints(
                step_label,
                theorem_label,
                ref_disjoints,
                &subst,
                theorem_disjoints,
                variables,
            )?;

            // Apply substitution to the assertion expression and push result.
            let result_expr = apply_subst(expression, &subst);
            stack.push(result_expr);
        }
    }
    Ok(())
}

/// Enforce an applied assertion's mandatory `$d` distinct-variable conditions.
///
/// For each distinct pair `(a, b)` the assertion requires, look at the variables
/// actually substituted for `a` and `b`. Every cross pair `(x, y)` with `x` from
/// `subst[a]` and `y` from `subst[b]` must be (1) two *different* variables and
/// (2) declared disjoint in the calling theorem's `$d` frame. A violation means
/// the proof illegally collapsed variables that must stay distinct.
fn enforce_disjoints(
    step_label: &str,
    theorem_label: &str,
    assertion_disjoints: &[(String, String)],
    subst: &HashMap<String, Vec<String>>,
    theorem_disjoints: &HashSet<(String, String)>,
    variables: &HashSet<String>,
) -> Result<(), MetamathError> {
    for (a, b) in assertion_disjoints {
        let (Some(sub_a), Some(sub_b)) = (subst.get(a), subst.get(b)) else {
            continue;
        };
        let vars_a: Vec<&String> = sub_a.iter().filter(|t| variables.contains(*t)).collect();
        let vars_b: Vec<&String> = sub_b.iter().filter(|t| variables.contains(*t)).collect();
        for x in &vars_a {
            for y in &vars_b {
                if x == y {
                    return Err(MetamathError::ProofVerificationFailed {
                        theorem: theorem_label.to_string(),
                        reason: format!(
                            "$d violation applying `{step_label}`: variable `{x}` substituted \
                             for both sides of distinct pair (`{a}`, `{b}`)"
                        ),
                    });
                }
                if !theorem_disjoints.contains(&norm_pair(x, y)) {
                    return Err(MetamathError::ProofVerificationFailed {
                        theorem: theorem_label.to_string(),
                        reason: format!(
                            "$d violation applying `{step_label}`: `{x}` and `{y}` (for distinct \
                             pair (`{a}`, `{b}`)) are not declared distinct in `{theorem_label}`"
                        ),
                    });
                }
            }
        }
    }
    Ok(())
}

/// Verify a single theorem's proof using the RPN stack machine.
///
/// Handles both normal (uncompressed) and compressed proof formats.
fn verify_single_proof(
    theorem_label: &str,
    expected_expr: &[String],
    mand_floats: &[(String, String, String)],
    mand_essentials: &[(String, Vec<String>)],
    proof_steps: &[String],
    labels: &HashMap<String, LabelInfo>,
    theorem_disjoints: &HashSet<(String, String)>,
    variables: &HashSet<String>,
) -> Result<ProofOutcome, MetamathError> {
    let mut stack: Vec<Vec<String>> = Vec::new();

    // Detect compressed proof format: ( label1 label2 ... ) ENCODED_STRING
    if !proof_steps.is_empty() && proof_steps[0] == "(" {
        return verify_compressed_proof(
            theorem_label,
            expected_expr,
            mand_floats,
            mand_essentials,
            proof_steps,
            labels,
            &mut stack,
            theorem_disjoints,
            variables,
        );
    }

    // Single-token compressed (rare)
    if proof_steps.len() == 1
        && proof_steps[0]
            .chars()
            .all(|c| c.is_ascii_uppercase() || c == 'Z' || c == '?')
    {
        return Ok(ProofOutcome::CompressedSkipped);
    }

    // Normal (uncompressed) proof
    for step_label in proof_steps {
        if step_label == "?" {
            return Ok(ProofOutcome::CompressedSkipped);
        }
        execute_proof_step(
            step_label,
            &mut stack,
            labels,
            theorem_label,
            theorem_disjoints,
            variables,
        )?;
    }

    check_final_stack(&stack, expected_expr, theorem_label)?;
    Ok(ProofOutcome::Verified)
}

/// Verify a compressed proof by interleaving decompression and RPN execution.
///
/// In compressed proofs, Z saves the current stack top for later back-reference.
/// Back-references push the saved stack entry directly (without re-executing).
/// Reference: Metamath book §4.4.3
fn verify_compressed_proof(
    theorem_label: &str,
    expected_expr: &[String],
    mand_floats: &[(String, String, String)],
    mand_essentials: &[(String, Vec<String>)],
    proof_steps: &[String],
    labels: &HashMap<String, LabelInfo>,
    stack: &mut Vec<Vec<String>>,
    theorem_disjoints: &HashSet<(String, String)>,
    variables: &HashSet<String>,
) -> Result<ProofOutcome, MetamathError> {
    // Find closing paren
    let close_idx =
        proof_steps
            .iter()
            .position(|t| t == ")")
            .ok_or_else(|| MetamathError::DatabaseError {
                reason: "compressed proof missing closing paren".to_string(),
            })?;

    // Build label lookup table: mandatory hyps + explicit labels from parens
    let mut label_table: Vec<String> = Vec::new();
    for (label, _, _) in mand_floats {
        label_table.push(label.clone());
    }
    for (label, _) in mand_essentials {
        label_table.push(label.clone());
    }
    for tok in &proof_steps[1..close_idx] {
        label_table.push(tok.clone());
    }

    // Concatenate encoded string tokens after closing paren
    let encoded: String = proof_steps[close_idx + 1..].concat();

    // Saved stack entries for Z/back-reference
    let mut saved: Vec<Vec<String>> = Vec::new();
    let mut current_num: usize = 0;
    let mut in_number = false;

    for ch in encoded.chars() {
        match ch {
            'A'..='T' => {
                let digit = (ch as u8 - b'A') as usize;
                let index = if in_number {
                    current_num * 20 + digit
                } else {
                    digit
                };
                in_number = false;
                current_num = 0;

                if index < label_table.len() {
                    // Execute the label as a proof step
                    execute_proof_step(
                        &label_table[index],
                        stack,
                        labels,
                        theorem_label,
                        theorem_disjoints,
                        variables,
                    )?;
                } else {
                    // Back-reference: push saved stack entry directly
                    let saved_idx = index - label_table.len();
                    if saved_idx < saved.len() {
                        stack.push(saved[saved_idx].clone());
                    } else {
                        return Err(MetamathError::DatabaseError {
                            reason: format!(
                                "compressed proof back-reference {} out of range (saved={})",
                                saved_idx,
                                saved.len()
                            ),
                        });
                    }
                }
            }
            'U'..='Y' => {
                let digit = (ch as u8 - b'U' + 1) as usize;
                current_num = if in_number {
                    current_num * 5 + digit
                } else {
                    digit
                };
                in_number = true;
            }
            'Z' => {
                // Save current stack top for later back-reference
                if let Some(top) = stack.last() {
                    saved.push(top.clone());
                }
            }
            '?' => {
                return Ok(ProofOutcome::CompressedSkipped);
            }
            _ => {} // whitespace or unknown — ignore
        }
    }

    check_final_stack(stack, expected_expr, theorem_label)?;
    Ok(ProofOutcome::Verified)
}

/// Apply a substitution map to an expression (token list).
pub(crate) fn apply_subst(expr: &[String], subst: &HashMap<String, Vec<String>>) -> Vec<String> {
    let mut result = Vec::new();
    for token in expr {
        if let Some(replacement) = subst.get(token) {
            result.extend(replacement.iter().cloned());
        } else {
            result.push(token.clone());
        }
    }
    result
}

/// Check that the stack has exactly one element matching the expected expression.
fn check_final_stack(
    stack: &[Vec<String>],
    expected_expr: &[String],
    theorem_label: &str,
) -> Result<(), MetamathError> {
    if stack.len() != 1 {
        return Err(MetamathError::ProofVerificationFailed {
            theorem: theorem_label.to_string(),
            reason: format!("proof leaves {} items on stack, expected 1", stack.len()),
        });
    }

    if stack[0] != expected_expr {
        return Err(MetamathError::ProofVerificationFailed {
            theorem: theorem_label.to_string(),
            reason: format!(
                "proof result doesn't match assertion.\n  Got:    {:?}\n  Expect: {:?}",
                &stack[0][..std::cmp::min(10, stack[0].len())],
                &expected_expr[..std::cmp::min(10, expected_expr.len())]
            ),
        });
    }

    Ok(())
}

#[cfg(test)]
#[path = "verify_tests.rs"]
mod tests;
