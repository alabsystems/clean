// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn resolve<'a, O: ExecutionObserver>(
    module: &'a Module,
    function: FuncId,
    place: &ClausePlace,
    work: &mut Work<'_, '_, O>,
) -> R<Result<&'a Ty, ObservedClauseTypingError<'a>>> {
    work.admit(
        1,
        size_of::<Option<&crate::Function>>() + 2 * size_of::<usize>(),
    )?;
    let mut found = None;
    let mut count = 0;
    let mut index = 0;
    while let Some(candidate) = work.at(&module.functions, index)? {
        work.admit(1, 2 * size_of::<u32>())?;
        if candidate.id.index() == function.index() {
            work.next(&mut count)?;
            work.admit(1, size_of::<Option<&crate::Function>>())?;
            found = Some(candidate);
        }
        work.next(&mut index)?;
    }
    work.admit(1, size_of::<ObservedClauseTypingError<'_>>())?;
    if count != 1 {
        return Ok(Err(ObservedClauseTypingError::FunctionUnresolved {
            function,
            matches: count,
        }));
    }
    let found = found.ok_or(ObservedValueError::InvalidRange)?;
    let Some(signature) = work.at(&module.func_types, found.ty.index() as usize)? else {
        return Ok(Err(ObservedClauseTypingError::SignatureUnresolved {
            function,
        }));
    };
    work.admit(11, 2 * size_of::<ObservedClauseTypingError<'_>>())?;
    Ok(match place {
        ClausePlace::Param { index } => param(signature, *index, work)?,
        ClausePlace::ResultSlot { index } => match work.at(&signature.returns, *index as usize)? {
            Some(ty) => Ok(ty),
            None => Err(ObservedClauseTypingError::ResultOutOfRange {
                index: *index,
                arity: signature.returns.len(),
            }),
        },
        ClausePlace::MutParamExit { index } => match param(signature, *index, work)? {
            Ok(Ty::RefMut(inner) | Ty::PtrMut(inner)) => Ok(inner.as_ref()),
            Ok(ty) => Err(ObservedClauseTypingError::MutParamExitNotMutable { index: *index, ty }),
            Err(e) => Err(e),
        },
        ClausePlace::ParamPointeeEntry { index } => match param(signature, *index, work)? {
            Ok(Ty::Ref(inner) | Ty::RefMut(inner)) => Ok(inner.as_ref()),
            Ok(ty) => {
                Err(ObservedClauseTypingError::ParamPointeeNotReference { index: *index, ty })
            }
            Err(e) => Err(e),
        },
        ClausePlace::World
        | ClausePlace::WorldPre
        | ClausePlace::WorldPost
        | ClausePlace::Unwind
        | ClausePlace::SpecVar { .. }
        | ClausePlace::SpecVarNext { .. } => {
            Err(ObservedClauseTypingError::PlaceHasNoIrType(*place))
        }
        ClausePlace::Value(_) => Err(ObservedClauseTypingError::ValuePlaceUnsupported(*place)),
    })
}
fn param<'a, O: ExecutionObserver>(
    signature: &'a crate::FuncTy,
    index: u32,
    work: &mut Work<'_, '_, O>,
) -> R<Result<&'a Ty, ObservedClauseTypingError<'a>>> {
    work.admit(1, size_of::<ObservedClauseTypingError<'_>>())?;
    Ok(match work.at(&signature.params, index as usize)? {
        Some(ty) => Ok(ty),
        None => Err(ObservedClauseTypingError::ParamOutOfRange {
            index,
            arity: signature.params.len(),
        }),
    })
}
