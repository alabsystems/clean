// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::cmp::Ordering;

use super::types::Monomial;

pub(super) fn cmp_monomials(lhs: &Monomial, rhs: &Monomial) -> Ordering {
    let lhs_degree: u32 = lhs.iter().map(|(_, exp)| *exp).sum();
    let rhs_degree: u32 = rhs.iter().map(|(_, exp)| *exp).sum();
    match lhs_degree.cmp(&rhs_degree) {
        Ordering::Equal => {}
        non_eq => return non_eq,
    }

    let mut lhs_idx = 0usize;
    let mut rhs_idx = 0usize;

    while lhs_idx < lhs.len() || rhs_idx < rhs.len() {
        let next_var = match (lhs.get(lhs_idx), rhs.get(rhs_idx)) {
            (Some((lhs_var, _)), Some((rhs_var, _))) => (*lhs_var).min(*rhs_var),
            (Some((lhs_var, _)), None) => *lhs_var,
            (None, Some((rhs_var, _))) => *rhs_var,
            (None, None) => unreachable!(),
        };

        let lhs_exp = if lhs.get(lhs_idx).map(|(var, _)| *var) == Some(next_var) {
            let exp = lhs[lhs_idx].1;
            lhs_idx += 1;
            exp
        } else {
            0
        };
        let rhs_exp = if rhs.get(rhs_idx).map(|(var, _)| *var) == Some(next_var) {
            let exp = rhs[rhs_idx].1;
            rhs_idx += 1;
            exp
        } else {
            0
        };

        match lhs_exp.cmp(&rhs_exp) {
            Ordering::Equal => {}
            non_eq => return non_eq,
        }
    }

    Ordering::Equal
}

pub(super) fn multiply_monomials(lhs: &Monomial, rhs: &Monomial) -> Monomial {
    let mut result = Vec::with_capacity(lhs.len() + rhs.len());
    let mut lhs_idx = 0usize;
    let mut rhs_idx = 0usize;

    while lhs_idx < lhs.len() && rhs_idx < rhs.len() {
        let (lhs_var, lhs_exp) = lhs[lhs_idx];
        let (rhs_var, rhs_exp) = rhs[rhs_idx];
        match lhs_var.cmp(&rhs_var) {
            Ordering::Less => {
                result.push((lhs_var, lhs_exp));
                lhs_idx += 1;
            }
            Ordering::Greater => {
                result.push((rhs_var, rhs_exp));
                rhs_idx += 1;
            }
            Ordering::Equal => {
                result.push((lhs_var, lhs_exp.saturating_add(rhs_exp)));
                lhs_idx += 1;
                rhs_idx += 1;
            }
        }
    }

    result.extend_from_slice(&lhs[lhs_idx..]);
    result.extend_from_slice(&rhs[rhs_idx..]);
    result
}

pub(super) fn lcm_monomials(lhs: &Monomial, rhs: &Monomial) -> Monomial {
    let mut result = Vec::with_capacity(lhs.len() + rhs.len());
    let mut lhs_idx = 0usize;
    let mut rhs_idx = 0usize;

    while lhs_idx < lhs.len() && rhs_idx < rhs.len() {
        let (lhs_var, lhs_exp) = lhs[lhs_idx];
        let (rhs_var, rhs_exp) = rhs[rhs_idx];
        match lhs_var.cmp(&rhs_var) {
            Ordering::Less => {
                result.push((lhs_var, lhs_exp));
                lhs_idx += 1;
            }
            Ordering::Greater => {
                result.push((rhs_var, rhs_exp));
                rhs_idx += 1;
            }
            Ordering::Equal => {
                result.push((lhs_var, lhs_exp.max(rhs_exp)));
                lhs_idx += 1;
                rhs_idx += 1;
            }
        }
    }

    result.extend_from_slice(&lhs[lhs_idx..]);
    result.extend_from_slice(&rhs[rhs_idx..]);
    result
}

pub(super) fn monomial_quotient(target: &Monomial, divisor: &Monomial) -> Option<Monomial> {
    let mut result = Vec::with_capacity(target.len());
    let mut target_idx = 0usize;
    let mut divisor_idx = 0usize;

    while divisor_idx < divisor.len() {
        let (divisor_var, divisor_exp) = divisor[divisor_idx];
        let (target_var, target_exp) = target.get(target_idx).copied()?;

        match target_var.cmp(&divisor_var) {
            Ordering::Less => {
                result.push((target_var, target_exp));
                target_idx += 1;
            }
            Ordering::Greater => return None,
            Ordering::Equal => {
                if target_exp < divisor_exp {
                    return None;
                }
                if target_exp > divisor_exp {
                    result.push((target_var, target_exp - divisor_exp));
                }
                target_idx += 1;
                divisor_idx += 1;
            }
        }
    }

    result.extend_from_slice(&target[target_idx..]);
    Some(result)
}
