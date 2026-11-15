// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls; complete ordinary helper results are the oracle.
#![allow(
    clippy::map_clone,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::{InstructionSite, InterpretOptions};
use crate::value::{BlockId, FuncTyId, ValueId};
use crate::{FuncTy, Function};
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original typing stop");
        }
        self.work = self.work.checked_add(e.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(e.copy_bytes)
            .ok_or("copy overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(180))
}
fn fixture() -> Module {
    let mut m = Module::new("typing");
    m.func_types.push(FuncTy::unrecorded(
        vec![
            Ty::U8,
            Ty::RefMut(Box::new(Ty::I16)),
            Ty::PtrMut(Box::new(Ty::U32)),
            Ty::Ref(Box::new(Ty::Bool)),
        ],
        vec![Ty::U64],
        false,
    ));
    m.functions.push(Function::new(
        FuncId::new(7),
        "f",
        FuncTyId::new(0),
        BlockId::new(0),
    ));
    m
}
fn places() -> Vec<ClausePlace> {
    vec![
        ClausePlace::Param { index: 0 },
        ClausePlace::ResultSlot { index: 0 },
        ClausePlace::MutParamExit { index: 0 },
        ClausePlace::World,
        ClausePlace::Unwind,
        ClausePlace::Value(ValueId::new(u32::MAX)),
        ClausePlace::SpecVar { index: u32::MAX },
        ClausePlace::SpecVarNext { index: u32::MAX },
        ClausePlace::WorldPre,
        ClausePlace::WorldPost,
        ClausePlace::ParamPointeeEntry { index: 0 },
    ]
}
fn owned(error: ObservedClauseTypingError<'_>) -> ClauseTypingError {
    match error {
        ObservedClauseTypingError::FunctionUnresolved { function, matches } => {
            ClauseTypingError::FunctionUnresolved { function, matches }
        }
        ObservedClauseTypingError::SignatureUnresolved { function } => {
            ClauseTypingError::SignatureUnresolved { function }
        }
        ObservedClauseTypingError::ParamOutOfRange { index, arity } => {
            ClauseTypingError::ParamOutOfRange { index, arity }
        }
        ObservedClauseTypingError::ResultOutOfRange { index, arity } => {
            ClauseTypingError::ResultOutOfRange { index, arity }
        }
        ObservedClauseTypingError::MutParamExitNotMutable { index, ty } => {
            ClauseTypingError::MutParamExitNotMutable {
                index,
                ty: ty.clone(),
            }
        }
        ObservedClauseTypingError::ParamPointeeNotReference { index, ty } => {
            ClauseTypingError::ParamPointeeNotReference {
                index,
                ty: ty.clone(),
            }
        }
        ObservedClauseTypingError::PlaceHasNoIrType(place) => {
            ClauseTypingError::PlaceHasNoIrType(place)
        }
        ObservedClauseTypingError::ValuePlaceUnsupported(place) => {
            ClauseTypingError::ValuePlaceUnsupported(place)
        }
    }
}
fn run(m: &Module, id: FuncId, place: &ClausePlace) -> Observer {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let result = resolve_clause_place_borrowed_observed(m, id, place, &mut s, site()).unwrap();
    assert_eq!(
        result.map(Ty::clone).map_err(owned),
        resolve_clause_place(m, id, place)
    );
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    o
}
fn admit(sort: &ClauseSort, ty: &Ty, bits: Option<u32>) -> (bool, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let result = clause_sort_admits_observed(sort, ty, bits, &mut s, site()).unwrap();
    assert_eq!(result, clause_sort_admits(sort, ty, bits));
    assert!(s.first_refusal().is_none());
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (result, o)
}
fn types() -> Vec<Ty> {
    use crate::ty::{DialectTy, FatPtrKind, HandleTy, SetRepr};
    use crate::value::{ClosureTyId, EnumId, PredId, RecordId, StructId, TyId};
    vec![
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
        Ty::Char,
        Ty::Error,
        Ty::F16,
        Ty::F32,
        Ty::F64,
        Ty::Bool,
        Ty::Vector(Box::new(Ty::U32), 8),
        Ty::Ptr,
        Ty::FatPtr(FatPtrKind::Str),
        Ty::Unit,
        Ty::Never,
        Ty::Struct(StructId::new(3)),
        Ty::Array(TyId::new(7), 64),
        Ty::Tuple(vec![Ty::U32]),
        Ty::Enum(EnumId::new(8)),
        Ty::Func(FuncTyId::new(9)),
        Ty::Ref(Box::new(Ty::U8)),
        Ty::RefMut(Box::new(Ty::U16)),
        Ty::PtrConst(Box::new(Ty::U32)),
        Ty::PtrMut(Box::new(Ty::U64)),
        Ty::Rc(Box::new(Ty::I32)),
        Ty::Set(TyId::new(1), SetRepr::Boxed),
        Ty::Sequence(TyId::new(2)),
        Ty::Record(RecordId::new(3)),
        Ty::Closure(ClosureTyId::new(4)),
        Ty::Refine(TyId::new(5), PredId::new(6)),
        Ty::Dialect(Box::new(DialectTy::new("vector", "lanes", 1))),
        Ty::Handle(Box::new(HandleTy::new("Nat", "trust_bignum::Nat"))),
    ]
}
