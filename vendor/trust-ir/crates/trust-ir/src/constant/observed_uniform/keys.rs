// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) enum Key<'a> {
    Int(i128),
    Leaf(&'a Constant),
    Composite {
        variant: Option<core::mem::Discriminant<Constant>>,
        payload: u64,
        labels: &'a [(String, Constant)],
        children: Vec<usize>,
    },
}
impl Key<'_> {
    pub(super) fn equal<O: ExecutionObserver>(
        &self,
        other: &Self,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(8, 2 * size_of::<bool>())?;
        match (self, other) {
            (Self::Int(a), Self::Int(b)) => Ok(a == b),
            (Self::Leaf(a), Self::Leaf(b)) => leaf_equal(a, b, work),
            (
                Self::Composite {
                    variant: a,
                    payload: ap,
                    labels: al,
                    children: ac,
                },
                Self::Composite {
                    variant: b,
                    payload: bp,
                    labels: bl,
                    children: bc,
                },
            ) => {
                if a != b || ap != bp || al.len() != bl.len() || ac.len() != bc.len() {
                    return Ok(false);
                }
                let mut at = 0;
                while let Some((a, _)) = work.at(al, at)? {
                    let (b, _) = work.at(bl, at)?.ok_or(ObservedValueError::InvalidRange)?;
                    if !work.bytes_equal(a.as_bytes(), b.as_bytes())? {
                        return Ok(false);
                    }
                    work.next(&mut at)?;
                }
                let mut at = 0;
                while let Some(a) = work.at(ac, at)? {
                    let b = work.at(bc, at)?.ok_or(ObservedValueError::InvalidRange)?;
                    work.admit(1, size_of::<bool>())?;
                    if a != b {
                        return Ok(false);
                    }
                    work.next(&mut at)?;
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }
}
fn leaf_equal<O: ExecutionObserver>(
    a: &Constant,
    b: &Constant,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(16, 2 * size_of::<u128>() + 2 * size_of::<usize>())?;
    Ok(match (a, b) {
        (Constant::U128(a), Constant::U128(b)) => a == b,
        (Constant::Bytes { data: a, utf8: au }, Constant::Bytes { data: b, utf8: bu }) => {
            au == bu && work.bytes_equal(a, b)?
        }
        (Constant::Float(a), Constant::Float(b)) => a.to_bits() == b.to_bits(),
        (Constant::Bool(a), Constant::Bool(b)) => a == b,
        (Constant::FnDef(a), Constant::FnDef(b)) => a == b,
        (
            Constant::SymbolAddr {
                symbol: a,
                addend: aa,
            },
            Constant::SymbolAddr {
                symbol: b,
                addend: ba,
            },
        ) => aa == ba && work.bytes_equal(a.as_bytes(), b.as_bytes())?,
        (Constant::PhantomData, Constant::PhantomData) => true,
        _ => false,
    })
}
