// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::imports::ty_equivalence_across;
use crate::interpret::InterpretOptions;
use crate::pred::Space;
use crate::signature_abi::*;
use crate::ty::{
    ClosureTy, DialectTy, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, FatPtrKind, HandleTy,
    RecordDef, SetRepr, StructDef, StructRepr,
};
use crate::value::{ClosureTyId, EnumId, FuncId, FuncTyId, RecordId, StructId, UnivId};
use crate::{FuncTy, ProofDigest};
mod abi;
mod abi_fixtures;
mod fixtures;
mod nominal;
mod predicates;
mod stops;
mod types;
use fixtures::*;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    copy_cap: Option<usize>,
    cleanup_fails: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("first stop");
        }
        if self.cleanup_fails
            && event.phase == ExecutionPhase::ScratchRetirement
            && self.stop.is_some_and(|cut| self.events.len() > cut)
        {
            return Err("later cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("copy overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.copy_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(2317))
}
fn options() -> InterpretOptions {
    InterpretOptions {
        fuel: 0,
        ..InterpretOptions::default()
    }
}
fn check(a: &Module, ta: &Ty, b: &Module, tb: &Ty) -> TyEquivalence {
    let expected = ty_equivalence_across(a, ta, b, tb);
    let before = (a.clone(), ta.clone(), b.clone(), tb.clone());
    let mut observer = Observer::default();
    let result;
    {
        let mut session = ObservedSession::new(options(), &mut observer);
        result = ty_equivalence_across_observed(a, ta, b, tb, &mut session, site()).unwrap();
        assert_eq!(result, expected);
        assert_eq!(session.remaining_fuel(), 0);
        assert!(session.first_refusal().is_none());
        if let TyEquivalence::OriginConflict(conflict) = result {
            conflict.retire_observed(&mut session, site()).unwrap();
        }
        assert_eq!(
            ty_structurally_eq_across_observed(a, ta, b, tb, &mut session, site()).unwrap(),
            matches!(expected, TyEquivalence::Equal)
        );
    }
    assert_eq!((&before.0, &before.1, &before.2, &before.3), (a, ta, b, tb));
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    expected
}
fn equal(a: &Module, ta: &Ty, b: &Module, tb: &Ty) {
    assert_eq!(check(a, ta, b, tb), TyEquivalence::Equal);
}
fn unequal(a: &Module, ta: &Ty, b: &Module, tb: &Ty) {
    assert!(!matches!(check(a, ta, b, tb), TyEquivalence::Equal));
}
