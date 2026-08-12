// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VeriPB proof format parser.
//!
//! Parses VeriPB text into `VeriPbProof` objects using the existing PB proof
//! kernel. The parser accepts both the simple constraint form emitted by the
//! current writer and a stack-based Polish notation for `p` lines.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use std::collections::BTreeSet;

use super::rules::{verify_rule, PbRule};
use super::types::{PbConstraint, PbFormula};
use super::veripb::{VeriPbProof, VeriPbStep};
use super::PbError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StackValue {
    Number(i64),
    Constraint(usize),
}

#[derive(Debug)]
struct ParserState {
    proof: VeriPbProof,
    derived: Vec<Option<PbConstraint>>,
    visible_ids: Vec<usize>,
    header_count: Option<usize>,
}

impl ParserState {
    fn new(formula: PbFormula) -> Self {
        Self {
            proof: VeriPbProof::new(formula),
            derived: Vec::new(),
            visible_ids: Vec::new(),
            header_count: None,
        }
    }

    fn formula(&self) -> &PbFormula {
        &self.proof.formula
    }

    fn finish(self) -> Result<VeriPbProof, PbError> {
        if let Some(count) = self.header_count {
            let actual = self.proof.formula.constraints.len();
            if count != actual {
                return Err(PbError::ConversionError(format!(
                    "formula header count mismatch: proof says {count}, formula has {actual} constraints"
                )));
            }
        }
        Ok(self.proof)
    }

    fn set_header_count(&mut self, count: usize) -> Result<(), PbError> {
        if let Some(existing) = self.header_count {
            if existing != count {
                return Err(PbError::ConversionError(format!(
                    "conflicting formula header counts: {existing} and {count}"
                )));
            }
            return Ok(());
        }
        self.header_count = Some(count);
        Ok(())
    }

    fn register_visible(&mut self, internal_id: usize) {
        self.visible_ids.push(internal_id);
    }

    fn visible_live_indices(&self) -> Vec<usize> {
        self.visible_ids
            .iter()
            .copied()
            .filter(|&idx| self.derived.get(idx).is_some_and(Option::is_some))
            .collect()
    }

    fn resolve_visible_reference(&self, one_based: usize) -> Result<usize, PbError> {
        let index = one_based.saturating_sub(1);
        let internal_id =
            self.visible_ids
                .get(index)
                .copied()
                .ok_or(PbError::IndexOutOfBounds {
                    index,
                    count: self.visible_ids.len(),
                })?;

        if self.derived.get(internal_id).is_some_and(Option::is_some) {
            Ok(internal_id)
        } else {
            Err(PbError::IndexOutOfBounds {
                index,
                count: self.visible_ids.len(),
            })
        }
    }

    fn add_polynomial_step(
        &mut self,
        result: PbConstraint,
        rule: PbRule,
    ) -> Result<usize, PbError> {
        let actual = derive_rule(&self.derived, self.formula(), &rule)?;
        if actual != result {
            return Err(PbError::ConversionError(
                "parsed `p` line does not match the derived constraint".to_string(),
            ));
        }

        self.proof
            .add_step(VeriPbStep::PolynomialAddition { result, rule });
        self.derived.push(Some(actual));
        Ok(self.derived.len() - 1)
    }

    fn add_computed_polynomial_step(&mut self, rule: PbRule) -> Result<usize, PbError> {
        let result = derive_rule(&self.derived, self.formula(), &rule)?;
        self.proof.add_step(VeriPbStep::PolynomialAddition {
            result: result.clone(),
            rule,
        });
        self.derived.push(Some(result));
        Ok(self.derived.len() - 1)
    }

    fn add_rup_step(&mut self, result: PbConstraint) -> usize {
        self.proof.add_step(VeriPbStep::ReverseUnitPropagation {
            result: result.clone(),
        });
        self.derived.push(Some(result));
        self.derived.len() - 1
    }

    fn add_red_step(&mut self, result: PbConstraint) -> usize {
        self.proof.add_step(VeriPbStep::RedundantAddition {
            result: result.clone(),
        });
        self.derived.push(Some(result));
        self.derived.len() - 1
    }

    fn add_delete_step(&mut self, internal_id: usize) -> Result<(), PbError> {
        if internal_id >= self.derived.len() || self.derived[internal_id].is_none() {
            return Err(PbError::IndexOutOfBounds {
                index: internal_id,
                count: self.derived.len(),
            });
        }

        self.proof.add_step(VeriPbStep::Delete { id: internal_id });
        self.derived[internal_id] = None;
        Ok(())
    }
}

/// Parse a VeriPB proof against an already-parsed PB formula.
pub(crate) fn parse_veripb(input: &str, formula: PbFormula) -> Result<VeriPbProof, PbError> {
    let mut state = ParserState::new(formula);
    let mut saw_end = false;

    for (line_idx, raw_line) in input.lines().enumerate() {
        let line_no = line_idx + 1;
        let line = raw_line.trim();

        if line.is_empty()
            || line.starts_with('*')
            || line.starts_with("pseudo-Boolean proof version")
        {
            continue;
        }

        if line == "end pseudo-Boolean proof" {
            saw_end = true;
            break;
        }

        if let Some(rest) = line.strip_prefix("f ") {
            let count = parse_single_usize(rest, line_no, "formula constraint count")?;
            state.set_header_count(count)?;
            continue;
        }

        if let Some(rest) = line.strip_prefix("p ") {
            parse_polynomial_line(rest, line_no, &mut state)?;
            continue;
        }

        if let Some(rest) = line.strip_prefix("rup ") {
            let constraint = parse_constraint(rest, state.formula().num_vars, line_no)?;
            let idx = state.add_rup_step(constraint);
            state.register_visible(idx);
            continue;
        }

        if let Some(rest) = line.strip_prefix("red ") {
            let constraint = parse_constraint(rest, state.formula().num_vars, line_no)?;
            let idx = state.add_red_step(constraint);
            state.register_visible(idx);
            continue;
        }

        if let Some(rest) = line
            .strip_prefix("del ")
            .or_else(|| line.strip_prefix("d "))
        {
            let internal_id = parse_delete_reference(rest, line_no, &state)?;
            state.add_delete_step(internal_id)?;
            continue;
        }

        if let Some(rest) = line.strip_prefix("u ") {
            let level = parse_single_u32(rest, line_no, "undo level")?;
            state.proof.add_step(VeriPbStep::Undo { level });
            continue;
        }

        if line == "c" {
            state.proof.add_step(VeriPbStep::Conclude);
            continue;
        }

        return Err(line_error(
            line_no,
            format!("unsupported VeriPB line '{line}'"),
        ));
    }

    if !saw_end {
        return Err(PbError::ConversionError(
            "missing 'end pseudo-Boolean proof' marker".to_string(),
        ));
    }

    state.finish()
}

fn parse_polynomial_line(
    body: &str,
    line_no: usize,
    state: &mut ParserState,
) -> Result<(), PbError> {
    let body = body.trim();
    if body.is_empty() {
        return Err(line_error(line_no, "empty `p` line".to_string()));
    }

    if body.contains(">=") {
        let result = parse_constraint(body, state.formula().num_vars, line_no)?;
        let rule = infer_rule_exact(&result, state)?;
        let idx = state.add_polynomial_step(result, rule)?;
        state.register_visible(idx);
        return Ok(());
    }

    parse_polish_expression(body, line_no, state)
}

fn parse_polish_expression(
    body: &str,
    line_no: usize,
    state: &mut ParserState,
) -> Result<(), PbError> {
    let body = body.trim_end_matches(';').trim();
    if body.is_empty() {
        return Err(line_error(line_no, "empty Polish expression".to_string()));
    }

    let mut stack: Vec<StackValue> = Vec::new();
    let mut generated_this_line: Vec<usize> = Vec::new();

    for token in body.split_whitespace() {
        match token {
            "+" => {
                let right = pop_stack(&mut stack, line_no, "`+`")?;
                let left = pop_stack(&mut stack, line_no, "`+`")?;
                let right_idx =
                    resolve_constraint_value(right, state, &mut generated_this_line, line_no)?;
                let left_idx =
                    resolve_constraint_value(left, state, &mut generated_this_line, line_no)?;
                let idx = state.add_computed_polynomial_step(PbRule::Addition {
                    left: left_idx,
                    right: right_idx,
                })?;
                generated_this_line.push(idx);
                stack.push(StackValue::Constraint(idx));
            }
            "*" => {
                let right = pop_stack(&mut stack, line_no, "`*`")?;
                let left = pop_stack(&mut stack, line_no, "`*`")?;
                let (constraint, scalar) = resolve_scalar_constraint_operands(
                    left,
                    right,
                    state,
                    &mut generated_this_line,
                    line_no,
                )?;
                let idx = state
                    .add_computed_polynomial_step(PbRule::Multiplication { constraint, scalar })?;
                generated_this_line.push(idx);
                stack.push(StackValue::Constraint(idx));
            }
            "d" => {
                let right = pop_stack(&mut stack, line_no, "`d`")?;
                let left = pop_stack(&mut stack, line_no, "`d`")?;
                let (constraint, divisor) = resolve_scalar_constraint_operands(
                    left,
                    right,
                    state,
                    &mut generated_this_line,
                    line_no,
                )?;
                let idx = state.add_computed_polynomial_step(PbRule::Division {
                    constraint,
                    divisor,
                })?;
                generated_this_line.push(idx);
                stack.push(StackValue::Constraint(idx));
            }
            "s" => {
                let value = pop_stack(&mut stack, line_no, "`s`")?;
                let source =
                    resolve_constraint_value(value, state, &mut generated_this_line, line_no)?;
                let idx = state.add_computed_polynomial_step(PbRule::Saturation(source))?;
                generated_this_line.push(idx);
                stack.push(StackValue::Constraint(idx));
            }
            "r" => {
                let value = pop_stack(&mut stack, line_no, "`r`")?;
                let source =
                    resolve_constraint_value(value, state, &mut generated_this_line, line_no)?;
                let idx = state.add_computed_polynomial_step(PbRule::Rounding(source))?;
                generated_this_line.push(idx);
                stack.push(StackValue::Constraint(idx));
            }
            _ if token.starts_with('#') => {
                let one_based = parse_derived_reference(token, line_no)?;
                let idx = state.resolve_visible_reference(one_based)?;
                stack.push(StackValue::Constraint(idx));
            }
            _ => {
                let number = token.parse::<i64>().map_err(|err| {
                    line_error(line_no, format!("invalid Polish token '{token}': {err}"))
                })?;
                stack.push(StackValue::Number(number));
            }
        }
    }

    let final_value = stack
        .pop()
        .ok_or_else(|| line_error(line_no, "missing final expression result".to_string()))?;
    if !stack.is_empty() {
        return Err(line_error(
            line_no,
            "Polish expression left extra values on the stack".to_string(),
        ));
    }

    let final_idx = match final_value {
        StackValue::Constraint(idx) if generated_this_line.contains(&idx) => idx,
        StackValue::Constraint(idx) => {
            let copy_idx = state.add_computed_polynomial_step(PbRule::Multiplication {
                constraint: idx,
                scalar: 1,
            })?;
            generated_this_line.push(copy_idx);
            copy_idx
        }
        StackValue::Number(number) => {
            let formula_idx =
                number_to_formula_index(number, state.formula().constraints.len(), line_no)?;
            let result = state
                .formula()
                .constraints
                .get(formula_idx)
                .cloned()
                .ok_or(PbError::IndexOutOfBounds {
                    index: formula_idx,
                    count: state.formula().constraints.len(),
                })?;
            let idx = state.add_polynomial_step(result, PbRule::Input(formula_idx))?;
            generated_this_line.push(idx);
            idx
        }
    };

    for internal_id in generated_this_line.iter().rev().copied() {
        if internal_id != final_idx {
            state.add_delete_step(internal_id)?;
        }
    }
    state.register_visible(final_idx);

    Ok(())
}

fn resolve_scalar_constraint_operands(
    left: StackValue,
    right: StackValue,
    state: &mut ParserState,
    generated_this_line: &mut Vec<usize>,
    line_no: usize,
) -> Result<(usize, i64), PbError> {
    let formula_len = state.formula().constraints.len();

    let left_scalar = matches!(left, StackValue::Number(_));
    let right_scalar = matches!(right, StackValue::Number(_));
    let left_constraint = is_constraint_like(left, formula_len);
    let right_constraint = is_constraint_like(right, formula_len);

    if left_scalar && right_constraint {
        let scalar = resolve_scalar_value(left, line_no)?;
        let constraint = resolve_constraint_value(right, state, generated_this_line, line_no)?;
        return Ok((constraint, scalar));
    }

    if right_scalar && left_constraint {
        let scalar = resolve_scalar_value(right, line_no)?;
        let constraint = resolve_constraint_value(left, state, generated_this_line, line_no)?;
        return Ok((constraint, scalar));
    }

    Err(line_error(
        line_no,
        "expected one scalar and one constraint operand".to_string(),
    ))
}

fn resolve_scalar_value(value: StackValue, line_no: usize) -> Result<i64, PbError> {
    match value {
        StackValue::Number(number) => Ok(number),
        StackValue::Constraint(_) => Err(line_error(
            line_no,
            "expected an integer scalar operand".to_string(),
        )),
    }
}

fn resolve_constraint_value(
    value: StackValue,
    state: &mut ParserState,
    generated_this_line: &mut Vec<usize>,
    line_no: usize,
) -> Result<usize, PbError> {
    match value {
        StackValue::Constraint(idx) => Ok(idx),
        StackValue::Number(number) => {
            let formula_idx =
                number_to_formula_index(number, state.formula().constraints.len(), line_no)?;
            let result = state
                .formula()
                .constraints
                .get(formula_idx)
                .cloned()
                .ok_or(PbError::IndexOutOfBounds {
                    index: formula_idx,
                    count: state.formula().constraints.len(),
                })?;
            let idx = state.add_polynomial_step(result, PbRule::Input(formula_idx))?;
            generated_this_line.push(idx);
            Ok(idx)
        }
    }
}

fn is_constraint_like(value: StackValue, formula_len: usize) -> bool {
    match value {
        StackValue::Constraint(_) => true,
        StackValue::Number(number) => usize::try_from(number)
            .ok()
            .is_some_and(|one_based| one_based != 0 && one_based <= formula_len),
    }
}

fn infer_rule_exact(target: &PbConstraint, state: &ParserState) -> Result<PbRule, PbError> {
    for (formula_idx, constraint) in state.formula().constraints.iter().enumerate() {
        if constraint == target {
            return Ok(PbRule::Input(formula_idx));
        }
    }

    let visible = state.visible_live_indices();
    let dense = dense_constraints(&state.derived);

    for &left in &visible {
        for &right in &visible {
            let rule = PbRule::Addition { left, right };
            if rule_derives_target(&rule, &dense, state.formula(), &state.derived, target) {
                return Ok(rule);
            }
        }
    }

    for &constraint in &visible {
        let source = state
            .derived
            .get(constraint)
            .and_then(Option::as_ref)
            .ok_or(PbError::IndexOutOfBounds {
                index: constraint,
                count: state.derived.len(),
            })?;

        if let Some(scalar) = infer_multiplication_scalar(source, target) {
            let rule = PbRule::Multiplication { constraint, scalar };
            if rule_derives_target(&rule, &dense, state.formula(), &state.derived, target) {
                return Ok(rule);
            }
        }

        if let Some(divisor) = infer_division_divisor(source, target) {
            let rule = PbRule::Division {
                constraint,
                divisor,
            };
            if rule_derives_target(&rule, &dense, state.formula(), &state.derived, target) {
                return Ok(rule);
            }
        }

        let saturation = PbRule::Saturation(constraint);
        if rule_derives_target(&saturation, &dense, state.formula(), &state.derived, target) {
            return Ok(saturation);
        }

        let rounding = PbRule::Rounding(constraint);
        if rule_derives_target(&rounding, &dense, state.formula(), &state.derived, target) {
            return Ok(rounding);
        }
    }

    for &left in &visible {
        for &right in &visible {
            let vars: BTreeSet<u32> = state
                .derived
                .get(left)
                .and_then(Option::as_ref)
                .into_iter()
                .flat_map(|constraint| constraint.terms.iter().map(|&(_, lit)| lit.unsigned_abs()))
                .chain(
                    state
                        .derived
                        .get(right)
                        .and_then(Option::as_ref)
                        .into_iter()
                        .flat_map(|constraint| {
                            constraint.terms.iter().map(|&(_, lit)| lit.unsigned_abs())
                        }),
                )
                .collect();

            for var in vars {
                let rule = PbRule::GeneralizedResolution { left, right, var };
                if rule_derives_target(&rule, &dense, state.formula(), &state.derived, target) {
                    return Ok(rule);
                }
            }
        }
    }

    Err(PbError::ConversionError(format!(
        "unable to infer a PB rule for constraint '{}'",
        format_constraint(target)
    )))
}

fn rule_derives_target(
    rule: &PbRule,
    dense: &[PbConstraint],
    formula: &PbFormula,
    derived: &[Option<PbConstraint>],
    target: &PbConstraint,
) -> bool {
    check_rule_references_live(rule, derived)
        .and_then(|()| verify_rule(dense, formula, rule))
        .is_ok_and(|constraint| &constraint == target)
}

fn infer_multiplication_scalar(source: &PbConstraint, target: &PbConstraint) -> Option<i64> {
    if source.terms.len() != target.terms.len() {
        return None;
    }

    let mut ratio: Option<i64> = None;
    for (&(src_coeff, src_lit), &(dst_coeff, dst_lit)) in source.terms.iter().zip(&target.terms) {
        if src_lit != dst_lit || src_coeff == 0 || dst_coeff % src_coeff != 0 {
            return None;
        }

        let candidate = dst_coeff / src_coeff;
        if candidate <= 0 {
            return None;
        }
        ratio = Some(unify_ratio(ratio, candidate)?);
    }

    if source.degree != 0 {
        if target.degree % source.degree != 0 {
            return None;
        }
        ratio = Some(unify_ratio(ratio, target.degree / source.degree)?);
    } else if target.degree != 0 {
        return None;
    }

    ratio.or(Some(1))
}

fn infer_division_divisor(source: &PbConstraint, target: &PbConstraint) -> Option<i64> {
    if source.terms.len() != target.terms.len() {
        return None;
    }

    let mut lower: i128 = 1;
    let mut upper: i128 = i128::MAX / 4;

    for (&(src_coeff, src_lit), &(dst_coeff, dst_lit)) in source.terms.iter().zip(&target.terms) {
        if src_lit != dst_lit {
            return None;
        }
        let (lo, hi) = division_interval(src_coeff, dst_coeff)?;
        lower = lower.max(lo);
        upper = upper.min(hi);
        if lower > upper {
            return None;
        }
    }

    let (lo, hi) = division_interval(source.degree, target.degree)?;
    lower = lower.max(lo);
    upper = upper.min(hi);
    if lower > upper || lower <= 0 || lower > i128::from(i64::MAX) {
        return None;
    }

    Some(lower as i64)
}

fn unify_ratio(current: Option<i64>, candidate: i64) -> Option<i64> {
    if candidate <= 0 {
        return None;
    }
    match current {
        Some(existing) if existing != candidate => None,
        _ => Some(candidate),
    }
}

fn division_interval(source: i64, target: i64) -> Option<(i128, i128)> {
    let source = i128::from(source);
    let target = i128::from(target);

    if source == 0 {
        return (target == 0).then_some((1, i128::MAX / 4));
    }

    if source > 0 {
        if target <= 0 {
            return None;
        }

        let lo = ceil_div_positive(source, target);
        let hi = if target == 1 {
            i128::MAX / 4
        } else {
            (source - 1) / (target - 1)
        };
        return (lo <= hi).then_some((lo, hi));
    }

    if target > 0 {
        return None;
    }

    let abs_source = -source;
    let abs_target = -target;
    if abs_target == 0 {
        return Some((abs_source + 1, i128::MAX / 4));
    }

    let lo = abs_source / (abs_target + 1) + 1;
    let hi = abs_source / abs_target;
    (lo <= hi).then_some((lo, hi))
}

fn ceil_div_positive(a: i128, b: i128) -> i128 {
    (a + b - 1) / b
}

fn dense_constraints(derived: &[Option<PbConstraint>]) -> Vec<PbConstraint> {
    derived
        .iter()
        .map(|opt| opt.clone().unwrap_or_else(|| PbConstraint::new(vec![], 0)))
        .collect()
}

fn derive_rule(
    derived: &[Option<PbConstraint>],
    formula: &PbFormula,
    rule: &PbRule,
) -> Result<PbConstraint, PbError> {
    check_rule_references_live(rule, derived)?;
    let dense = dense_constraints(derived);
    verify_rule(&dense, formula, rule)
}

fn check_rule_references_live(
    rule: &PbRule,
    derived: &[Option<PbConstraint>],
) -> Result<(), PbError> {
    let indices: Vec<usize> = match rule {
        PbRule::Input(_) => Vec::new(),
        PbRule::Addition { left, right } => vec![*left, *right],
        PbRule::Multiplication { constraint, .. } => vec![*constraint],
        PbRule::Division { constraint, .. } => vec![*constraint],
        PbRule::Saturation(idx) => vec![*idx],
        PbRule::Rounding(idx) => vec![*idx],
        PbRule::GeneralizedResolution { left, right, .. } => vec![*left, *right],
    };

    for index in indices {
        if index >= derived.len() || derived[index].is_none() {
            return Err(PbError::IndexOutOfBounds {
                index,
                count: derived.len(),
            });
        }
    }

    Ok(())
}

fn parse_delete_reference(
    text: &str,
    line_no: usize,
    state: &ParserState,
) -> Result<usize, PbError> {
    let token = single_token(text, line_no, "delete reference")?;
    if token.starts_with('#') {
        let visible = parse_derived_reference(token, line_no)?;
        return state.resolve_visible_reference(visible);
    }

    let global_id = token
        .parse::<usize>()
        .map_err(|err| line_error(line_no, format!("invalid delete id '{token}': {err}")))?;
    let formula_count = state.formula().constraints.len();

    if global_id == 0 || global_id <= formula_count {
        return Err(line_error(
            line_no,
            format!("deletion of formula constraint {global_id} is not supported"),
        ));
    }

    let visible = global_id - formula_count;
    state.resolve_visible_reference(visible)
}

fn parse_derived_reference(token: &str, line_no: usize) -> Result<usize, PbError> {
    let digits = token
        .strip_prefix('#')
        .ok_or_else(|| line_error(line_no, format!("invalid derived reference '{token}'")))?;
    let one_based = digits.parse::<usize>().map_err(|err| {
        line_error(
            line_no,
            format!("invalid derived reference '{token}': {err}"),
        )
    })?;
    if one_based == 0 {
        return Err(line_error(
            line_no,
            "derived references are 1-indexed".to_string(),
        ));
    }
    Ok(one_based)
}

fn number_to_formula_index(
    number: i64,
    formula_len: usize,
    line_no: usize,
) -> Result<usize, PbError> {
    let one_based = usize::try_from(number).map_err(|_| {
        line_error(
            line_no,
            format!("formula references must be positive, got {number}"),
        )
    })?;

    if one_based == 0 || one_based > formula_len {
        return Err(line_error(
            line_no,
            format!("formula reference {number} is out of range for {formula_len} constraints"),
        ));
    }

    Ok(one_based - 1)
}

fn parse_constraint(text: &str, num_vars: u32, line_no: usize) -> Result<PbConstraint, PbError> {
    let text = text.trim();
    let text = text
        .strip_suffix(';')
        .ok_or_else(|| line_error(line_no, "constraint must end with ';'".to_string()))?
        .trim();

    let (lhs, rhs) = text.split_once(">=").ok_or_else(|| {
        line_error(
            line_no,
            format!("constraint is missing a '>=' operator: '{text}'"),
        )
    })?;

    let terms = parse_terms(lhs.trim(), num_vars, line_no)?;
    let degree = rhs
        .trim()
        .parse::<i64>()
        .map_err(|err| line_error(line_no, format!("invalid degree '{}': {err}", rhs.trim())))?;

    Ok(PbConstraint::new(terms, degree))
}

fn parse_terms(text: &str, num_vars: u32, line_no: usize) -> Result<Vec<(i64, i32)>, PbError> {
    if text.is_empty() {
        return Ok(Vec::new());
    }

    let mut terms = Vec::new();
    let tokens: Vec<&str> = text.split_whitespace().collect();
    let mut index = 0;

    while index < tokens.len() {
        let coeff_token = tokens[index];
        let coeff = coeff_token.parse::<i64>().map_err(|err| {
            line_error(
                line_no,
                format!("invalid coefficient '{coeff_token}': {err}"),
            )
        })?;
        index += 1;

        let lit_token = tokens.get(index).ok_or_else(|| {
            line_error(
                line_no,
                format!("expected literal after coefficient '{coeff_token}'"),
            )
        })?;
        let literal = parse_literal(lit_token, num_vars, line_no)?;
        terms.push((coeff, literal));
        index += 1;
    }

    Ok(terms)
}

fn parse_literal(token: &str, num_vars: u32, line_no: usize) -> Result<i32, PbError> {
    let literal = if let Some(rest) = token.strip_prefix("~x") {
        let var = rest
            .parse::<u32>()
            .map_err(|err| line_error(line_no, format!("invalid literal '{token}': {err}")))?;
        -(var as i32)
    } else if let Some(rest) = token.strip_prefix('x') {
        let var = rest
            .parse::<u32>()
            .map_err(|err| line_error(line_no, format!("invalid literal '{token}': {err}")))?;
        var as i32
    } else {
        return Err(line_error(line_no, format!("invalid literal '{token}'")));
    };

    let var = literal.unsigned_abs();
    if var == 0 || var > num_vars {
        return Err(PbError::LiteralOutOfBounds { literal });
    }

    Ok(literal)
}

fn parse_single_usize(text: &str, line_no: usize, label: &str) -> Result<usize, PbError> {
    let token = single_token(text, line_no, label)?;
    token
        .parse::<usize>()
        .map_err(|err| line_error(line_no, format!("invalid {label} '{token}': {err}")))
}

fn parse_single_u32(text: &str, line_no: usize, label: &str) -> Result<u32, PbError> {
    let token = single_token(text, line_no, label)?;
    token
        .parse::<u32>()
        .map_err(|err| line_error(line_no, format!("invalid {label} '{token}': {err}")))
}

fn single_token<'a>(text: &'a str, line_no: usize, label: &str) -> Result<&'a str, PbError> {
    let mut parts = text.split_whitespace();
    let token = parts
        .next()
        .ok_or_else(|| line_error(line_no, format!("missing {label}")))?;
    if parts.next().is_some() {
        return Err(line_error(
            line_no,
            format!("expected a single {label}, got '{text}'"),
        ));
    }
    Ok(token)
}

fn pop_stack(stack: &mut Vec<StackValue>, line_no: usize, op: &str) -> Result<StackValue, PbError> {
    stack
        .pop()
        .ok_or_else(|| line_error(line_no, format!("stack underflow while evaluating {op}")))
}

fn format_constraint(constraint: &PbConstraint) -> String {
    let mut text = String::new();
    for &(coeff, lit) in &constraint.terms {
        if lit > 0 {
            text.push_str(&format!("{coeff} x{lit} "));
        } else {
            text.push_str(&format!("{coeff} ~x{} ", -lit));
        }
    }
    text.push_str(&format!(">= {} ;", constraint.degree));
    text
}

fn line_error(line_no: usize, message: String) -> PbError {
    if line_no == 0 {
        PbError::ConversionError(message)
    } else {
        PbError::ConversionError(format!("line {line_no}: {message}"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn contradiction_formula() -> PbFormula {
        let mut formula = PbFormula::new(1);
        formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
        formula.add_constraint(PbConstraint::new(vec![(1, -1)], 1));
        formula
    }

    #[test]
    fn test_parse_simple_complete_proof() {
        let text = r"
            * parsed from text
            pseudo-Boolean proof version 2.0
            f 2
            p 1
            p 2
            p #1 #2 +
            c
            end pseudo-Boolean proof
        ";

        let proof = parse_veripb(text, contradiction_formula()).expect("proof should parse");
        proof.verify().expect("parsed proof should verify");
    }

    #[test]
    fn test_parse_round_trip_generated_veripb() {
        let formula = contradiction_formula();
        let mut proof = VeriPbProof::new(formula.clone());
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, 1)], 1),
            rule: PbRule::Input(0),
        });
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(1, -1)], 1),
            rule: PbRule::Input(1),
        });
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![], 1),
            rule: PbRule::Addition { left: 0, right: 1 },
        });
        proof.add_step(VeriPbStep::Conclude);

        let parsed = parse_veripb(&proof.to_veripb_format(), formula).expect("round-trip parse");
        parsed.verify().expect("round-trip proof should verify");
    }

    #[test]
    fn test_parse_missing_end_marker_fails() {
        let err = parse_veripb(
            "pseudo-Boolean proof version 2.0\nf 0\nc\n",
            PbFormula::new(0),
        )
        .expect_err("missing end marker should fail");
        assert!(matches!(err, PbError::ConversionError(_)));
    }

    #[test]
    fn test_parse_invalid_constraint_reference_fails() {
        let err = parse_veripb(
            "pseudo-Boolean proof version 2.0\nf 2\np #1 1 +\nend pseudo-Boolean proof\n",
            contradiction_formula(),
        )
        .expect_err("invalid reference should fail");

        assert!(matches!(err, PbError::IndexOutOfBounds { .. }));
    }

    #[test]
    fn test_parse_malformed_line_fails() {
        let err = parse_veripb(
            "pseudo-Boolean proof version 2.0\nf 1\np 1 x1 >= ;\nend pseudo-Boolean proof\n",
            {
                let mut formula = PbFormula::new(1);
                formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
                formula
            },
        )
        .expect_err("malformed line should fail");

        assert!(matches!(err, PbError::ConversionError(_)));
    }

    #[test]
    fn test_parse_rup_and_delete_steps() {
        let text = r"
            pseudo-Boolean proof version 2.0
            f 2
            rup >= 1 ;
            d 3
            rup >= 1 ;
            c
            end pseudo-Boolean proof
        ";

        let proof = parse_veripb(text, contradiction_formula()).expect("proof should parse");
        assert!(matches!(
            proof.steps.first(),
            Some(VeriPbStep::ReverseUnitPropagation { .. })
        ));
        assert!(proof
            .steps
            .iter()
            .any(|step| matches!(step, VeriPbStep::Delete { .. })));
        proof.verify().expect("RUP proof should verify");
    }

    #[test]
    fn test_parse_red_step() {
        let text = r"
            pseudo-Boolean proof version 2.0
            f 2
            red >= 1 ;
            c
            end pseudo-Boolean proof
        ";

        let proof = parse_veripb(text, contradiction_formula()).expect("proof should parse");
        assert!(matches!(
            proof.steps.first(),
            Some(VeriPbStep::RedundantAddition { .. })
        ));
        proof.verify().expect("red proof should verify");
    }
}
