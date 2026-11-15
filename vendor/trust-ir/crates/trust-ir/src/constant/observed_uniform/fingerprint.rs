// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Fixed-width lookup accelerator, never equality or authentication authority.
use super::*;
use sha2::{Digest, Sha256};
fn bytes<O: ExecutionObserver>(source: &[u8], hash: &mut Sha256, work: &mut Work<'_, '_, O>) -> R {
    let mut at = 0;
    loop {
        work.admit(1, size_of::<usize>())?;
        if at == source.len() {
            return Ok(());
        }
        let end = at
            .checked_add((source.len() - at).min(1024))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        // Same bounded <=1024-byte SHA update constituent as existing observed
        // domain digest. This is a class accelerator, not a canonical digest.
        work.admit(end - at, end - at)?;
        hash.update(&source[at..end]);
        at = end;
    }
}
fn number<O: ExecutionObserver>(n: u128, hash: &mut Sha256, work: &mut Work<'_, '_, O>) -> R {
    work.admit(1, size_of::<[u8; 16]>())?;
    bytes(&n.to_be_bytes(), hash, work)
}
fn text<O: ExecutionObserver>(s: &str, hash: &mut Sha256, work: &mut Work<'_, '_, O>) -> R {
    number(s.len() as u128, hash, work)?;
    bytes(s.as_bytes(), hash, work)
}
fn variant(node: &Constant) -> u8 {
    match node {
        Constant::Int(_) => 0,
        Constant::U128(_) => 1,
        Constant::Bytes { .. } => 2,
        Constant::Float(_) => 3,
        Constant::Bool(_) => 4,
        Constant::Aggregate(_) => 5,
        Constant::Array(_) => 6,
        Constant::Splat { .. } => 7,
        Constant::Vector(_) => 8,
        Constant::Sequence(_) => 9,
        Constant::Set(_) => 10,
        Constant::Record(_) => 11,
        Constant::Closure { .. } => 12,
        Constant::FnDef(_) => 13,
        Constant::SymbolAddr { .. } => 14,
        Constant::PhantomData => 15,
        Constant::Uninit => 16,
        Constant::TensorBlob { .. } => 17,
        Constant::Ext(e) => e.unreachable(),
    }
}
pub(super) fn of<O: ExecutionObserver>(
    key: &Key<'_>,
    source: Option<&Constant>,
    work: &mut Work<'_, '_, O>,
) -> R<[u8; 32]> {
    work.admit(1, size_of::<Sha256>())?;
    let mut hash = Some(Sha256::new());
    let result = (|| {
        let h = hash.as_mut().ok_or(ObservedValueError::InvalidRange)?;
        work.admit(16, size_of::<usize>())?;
        match key {
            Key::Int(n) => {
                number(0, h, work)?;
                number(*n as u128, h, work)?;
            }
            Key::Leaf(node) => {
                number(1, h, work)?;
                number(u128::from(variant(node)), h, work)?;
                match node {
                    Constant::U128(n) => number(*n, h, work)?,
                    Constant::Bytes { data, utf8 } => {
                        number(u128::from(*utf8), h, work)?;
                        number(data.len() as u128, h, work)?;
                        bytes(data, h, work)?;
                    }
                    Constant::Float(n) => number(u128::from(n.to_bits()), h, work)?,
                    Constant::Bool(n) => number(u128::from(*n), h, work)?,
                    Constant::FnDef(id) => number(u128::from(id.index()), h, work)?,
                    Constant::SymbolAddr { symbol, addend } => {
                        text(symbol, h, work)?;
                        number(i128::from(*addend) as u128, h, work)?;
                    }
                    Constant::PhantomData => {}
                    Constant::TensorBlob { digest, dims } => {
                        bytes(&digest.0, h, work)?;
                        number(dims.len() as u128, h, work)?;
                        for dim in dims {
                            number(u128::from(*dim), h, work)?;
                        }
                    }
                    _ => return Err(ObservedValueError::InvalidRange),
                }
            }
            Key::Composite {
                variant: tag,
                payload,
                labels,
                children,
            } => {
                number(2, h, work)?;
                let tag = if tag.is_some() {
                    let node = source.ok_or(ObservedValueError::InvalidRange)?;
                    Some(variant(node))
                } else {
                    None
                };
                number(tag.map_or(0, |v| u128::from(v) + 1), h, work)?;
                number(u128::from(*payload), h, work)?;
                number(labels.len() as u128, h, work)?;
                let mut at = 0;
                while let Some((label, _)) = work.at(labels, at)? {
                    text(label, h, work)?;
                    work.next(&mut at)?;
                }
                number(children.len() as u128, h, work)?;
                let mut at = 0;
                while let Some(id) = work.at(children, at)? {
                    number(*id as u128, h, work)?;
                    work.next(&mut at)?;
                }
            }
        }
        work.admit(128, size_of::<[u8; 32]>())?;
        Ok(())
    })();
    match result {
        Ok(()) => {
            let h = hash.take().ok_or(ObservedValueError::InvalidRange)?;
            let out = h.finalize().into();
            work.retire(hash);
            work.admit(1, 0)?;
            Ok(out)
        }
        Err(error) => {
            work.retire(hash);
            Err(work.terminal(error))
        }
    }
}
