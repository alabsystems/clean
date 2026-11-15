// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Fixed {
    Bool,
    Int,
    BitVec(u32),
}
#[derive(Clone, Copy)]
pub(super) enum Sort<'a> {
    Fixed(Fixed),
    Borrowed(&'a ClauseSort),
}
#[derive(Clone, Copy)]
pub(super) enum Pair<'a> {
    Sort(&'a ClauseSort, &'a ClauseSort),
    Ctors(
        &'a [(String, Vec<(String, ClauseSort)>)],
        &'a [(String, Vec<(String, ClauseSort)>)],
        usize,
    ),
    Fields(
        &'a [(String, ClauseSort)],
        &'a [(String, ClauseSort)],
        usize,
    ),
}
impl<'a> State<'a> {
    pub(super) fn equal_sort<O: ExecutionObserver>(
        &mut self,
        left: Sort<'a>,
        right: &'a ClauseSort,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(7, size_of::<bool>())?;
        if let Sort::Fixed(left) = left {
            return Ok(match (left, right) {
                (Fixed::Bool, ClauseSort::Bool) | (Fixed::Int, ClauseSort::Int) => true,
                (Fixed::BitVec(a), ClauseSort::BitVec(b)) => a == *b,
                _ => false,
            });
        }
        let Sort::Borrowed(left) = left else {
            return Err(ObservedValueError::InvalidRange);
        };
        let result = (|| {
            work.admit(1, 0)?;
            if self.equality.capacity() != 0 {
                return Err(ObservedValueError::InvalidRange);
            }
            work.admit(1, size_of::<Pair<'_>>())?;
            work.push(&mut self.equality, Pair::Sort(left, right))?;
            loop {
                work.admit(1, size_of::<Option<Pair<'_>>>())?;
                let Some(pair) = self.equality.pop() else {
                    return Ok(true);
                };
                work.admit(7, 3 * size_of::<Pair<'_>>())?;
                match pair {
                    Pair::Sort(a, b) => match (a, b) {
                        (ClauseSort::Bool, ClauseSort::Bool)
                        | (ClauseSort::Int, ClauseSort::Int)
                        | (ClauseSort::RoundingMode, ClauseSort::RoundingMode) => {}
                        (ClauseSort::BitVec(a), ClauseSort::BitVec(b)) => {
                            if a != b {
                                return Ok(false);
                            }
                        }
                        (
                            ClauseSort::Float { eb: a, sb: b },
                            ClauseSort::Float { eb: c, sb: d },
                        ) => {
                            if a != c || b != d {
                                return Ok(false);
                            }
                        }
                        (ClauseSort::Array(a, b), ClauseSort::Array(c, d)) => {
                            work.push(&mut self.equality, Pair::Sort(b, d))?;
                            work.push(&mut self.equality, Pair::Sort(a, c))?;
                        }
                        (
                            ClauseSort::Datatype {
                                name: a,
                                constructors: b,
                            },
                            ClauseSort::Datatype {
                                name: c,
                                constructors: d,
                            },
                        ) => {
                            if !work.equal(a, c)? || b.len() != d.len() {
                                return Ok(false);
                            }
                            work.push(&mut self.equality, Pair::Ctors(b, d, 0))?;
                        }
                        // Exhaustive variant census below guards future variants;
                        // different current tags are semantically unequal.
                        (
                            ClauseSort::Bool
                            | ClauseSort::Int
                            | ClauseSort::RoundingMode
                            | ClauseSort::BitVec(_)
                            | ClauseSort::Float { .. }
                            | ClauseSort::Array(..)
                            | ClauseSort::Datatype { .. },
                            _,
                        ) => return Ok(false),
                    },
                    Pair::Ctors(a, b, index) => {
                        if let Some((name, fields)) = work.at(a, index)? {
                            let (other, children) =
                                work.at(b, index)?.ok_or(ObservedValueError::InvalidRange)?;
                            if !work.equal(name, other)? || fields.len() != children.len() {
                                return Ok(false);
                            }
                            let mut next = index;
                            work.next(&mut next)?;
                            work.push(&mut self.equality, Pair::Ctors(a, b, next))?;
                            work.push(&mut self.equality, Pair::Fields(fields, children, 0))?;
                        }
                    }
                    Pair::Fields(a, b, index) => {
                        if let Some((name, sort)) = work.at(a, index)? {
                            let (other, child) =
                                work.at(b, index)?.ok_or(ObservedValueError::InvalidRange)?;
                            if !work.equal(name, other)? {
                                return Ok(false);
                            }
                            let mut next = index;
                            work.next(&mut next)?;
                            work.push(&mut self.equality, Pair::Fields(a, b, next))?;
                            work.push(&mut self.equality, Pair::Sort(sort, child))?;
                        }
                    }
                }
            }
        })();
        work.retire_fixed_vec(&mut self.equality);
        let answer = result.map_err(|error| work.terminal(error))?;
        work.admit(1, size_of::<bool>())?;
        Ok(answer)
    }
}
pub(super) fn effective<'a, O: ExecutionObserver>(
    variable: &'a SpecVar,
    work: &mut Work<'_, '_, O>,
) -> R<Option<Sort<'a>>> {
    work.admit(1, size_of::<Option<Sort<'_>>>())?;
    match &variable.sort {
        Some(sort) => Ok(Some(Sort::Borrowed(sort))),
        None => Ok(parse(&variable.ty, work)?.map(Sort::Fixed)),
    }
}
/// Exact accepted grammar of parse_spec_var_sort; discarded ordinary error
/// strings are not constructed. Mathematical range bounds stay unnarrowed.
pub(super) fn parse<O: ExecutionObserver>(
    text: &str,
    work: &mut Work<'_, '_, O>,
) -> R<Option<Fixed>> {
    if work.equal(text, "Bool")? {
        return Ok(Some(Fixed::Bool));
    }
    if work.equal(text, "Int")? {
        return Ok(Some(Fixed::Int));
    }
    work.admit(8, 2 * size_of::<&str>())?;
    if let Some(width) = text
        .strip_prefix("BitVec(")
        .and_then(|rest| rest.strip_suffix(')'))
    {
        let Some(digits) = decimal(width, false, work)? else {
            return Ok(None);
        };
        let mut value = 0u32;
        let mut index = 0;
        while let Some(byte) = work.at(digits.1.as_bytes(), index)? {
            work.admit(3, size_of::<Option<u32>>())?;
            let Some(next) = value
                .checked_mul(10)
                .and_then(|v| v.checked_add(u32::from(*byte - b'0')))
            else {
                return Ok(None);
            };
            value = next;
            work.next(&mut index)?;
        }
        return Ok((value > 0).then_some(Fixed::BitVec(value)));
    }
    let mut index = 0;
    while let Some(byte) = work.at(text.as_bytes(), index)? {
        work.admit(2, size_of::<usize>())?;
        let next = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        if *byte == b'.' && work.at(text.as_bytes(), next)? == Some(&b'.') {
            work.admit(2, 2 * size_of::<&str>())?;
            let lo = &text[..index];
            let hi = &text[next + 1..];
            let (Some(lo), Some(hi)) = (decimal(lo, true, work)?, decimal(hi, true, work)?) else {
                return Ok(None);
            };
            work.admit(4, 2 * size_of::<usize>())?;
            let le = match (lo, hi) {
                ((true, _), (false, _)) => true,
                ((false, _), (true, _)) => false,
                ((false, a), (false, b)) => {
                    if a.len() != b.len() {
                        a.len() < b.len()
                    } else {
                        work.compare(a, b)? != Ordering::Greater
                    }
                }
                ((true, a), (true, b)) => {
                    if a.len() != b.len() {
                        a.len() > b.len()
                    } else {
                        work.compare(b, a)? != Ordering::Greater
                    }
                }
            };
            return Ok(le.then_some(Fixed::Int));
        }
        work.next(&mut index)?;
    }
    Ok(None)
}
fn decimal<'a, O: ExecutionObserver>(
    text: &'a str,
    signed: bool,
    work: &mut Work<'_, '_, O>,
) -> R<Option<(bool, &'a str)>> {
    work.admit(3, size_of::<Option<(bool, &str)>>())?;
    let (negative, digits) = if signed {
        match text.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, text),
        }
    } else {
        (false, text)
    };
    if digits.is_empty() {
        return Ok(None);
    }
    let mut index = 0;
    while let Some(byte) = work.at(digits.as_bytes(), index)? {
        work.admit(1, 0)?;
        if !byte.is_ascii_digit() {
            return Ok(None);
        }
        work.next(&mut index)?;
    }
    work.admit(4, 0)?;
    if (digits.len() > 1 && digits.as_bytes()[0] == b'0') || (negative && digits == "0") {
        return Ok(None);
    }
    Ok(Some((negative, digits)))
}
