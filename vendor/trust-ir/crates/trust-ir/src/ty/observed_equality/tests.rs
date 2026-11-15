// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::interpret::InterpretOptions;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    bytes: usize,
    work_limit: Option<usize>,
    byte_limit: Option<usize>,
    retirement: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        if self.retirement && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("bytes overflow")?;
        if self.work_limit.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_limit.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(crate::FuncId::new(71))
}
fn equal(left: &Ty, right: &Ty) -> bool {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let result = left
        .structural_eq_observed(right, &mut session, site())
        .unwrap();
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|e| e.site == site()));
    result
}
fn types() -> Vec<Ty> {
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
        Ty::Ptr,
        Ty::Unit,
        Ty::Never,
        Ty::Vector(Box::new(Ty::U8), 17),
        Ty::FatPtr(FatPtrKind::Slice(TyId::new(2))),
        Ty::FatPtr(FatPtrKind::Str),
        Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 9 }),
        Ty::FatPtr(FatPtrKind::ContainerLen),
        Ty::FatPtr(FatPtrKind::ContainerVtable),
        Ty::Struct(StructId::new(3)),
        Ty::Array(TyId::new(2), 17),
        Ty::Tuple(vec![Ty::I8, Ty::U64]),
        Ty::Enum(EnumId::new(3)),
        Ty::Func(FuncTyId::new(3)),
        Ty::Ref(Box::new(Ty::U64)),
        Ty::RefMut(Box::new(Ty::U64)),
        Ty::PtrConst(Box::new(Ty::U64)),
        Ty::PtrMut(Box::new(Ty::U64)),
        Ty::Rc(Box::new(Ty::U64)),
        Ty::Set(TyId::new(2), SetRepr::Bitset),
        Ty::Sequence(TyId::new(2)),
        Ty::Record(RecordId::new(3)),
        Ty::Closure(ClosureTyId::new(3)),
        Ty::Refine(TyId::new(2), PredId::new(3)),
        Ty::Dialect(Box::new(DialectTy::new("space", "name", 1))),
        Ty::Handle(Box::new(HandleTy::new("name", "runtime"))),
    ]
}
#[test]
fn every_current_level_r_type_payload_matches_derived_structural_equality() {
    let types = types();
    for a in &types {
        for b in &types {
            assert_eq!(equal(a, b), a == b, "{a:?} / {b:?}");
        }
    }
}
#[test]
fn wide_and_deep_inline_types_compare_actual_children_without_canonicalizing_keys() {
    let left = Ty::Tuple(vec![Ty::Ref(Box::new(Ty::Char)); 257]);
    let mut right = left.clone();
    assert!(equal(&left, &right));
    if let Ty::Tuple(fields) = &mut right {
        fields[256] = Ty::Ref(Box::new(Ty::U32));
    }
    assert!(!equal(&left, &right));
    let mut left = Ty::Bool;
    for _ in 0..257 {
        left = Ty::RefMut(Box::new(left));
    }
    assert!(equal(&left, &left.clone()));
    assert!(!equal(
        &Ty::Array(TyId::new(1), 1),
        &Ty::Array(TyId::new(1), 2)
    ));
    assert!(!equal(
        &Ty::Set(TyId::new(1), SetRepr::Bitset),
        &Ty::Set(TyId::new(1), SetRepr::Boxed)
    ));
}
#[test]
fn variable_nominal_identity_compares_strings_inside_bounded_actual_chunks() {
    let left = Ty::Handle(Box::new(HandleTy::new("x".repeat(4097), "runtime")));
    let right = left.clone();
    let mut observer = Observer {
        stop_at: Some(8),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        left.structural_eq_observed(&right, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
    let mut other = right;
    if let Ty::Handle(h) = &mut other {
        h.runtime.push('!');
    }
    assert!(!equal(&left, &other));
    let a = Ty::Dialect(Box::new(DialectTy::new("λ".repeat(2049), "name", 1)));
    let b = Ty::Dialect(Box::new(DialectTy::new("λ".repeat(2049), "name", 2)));
    assert!(!equal(&a, &b));
}
#[test]
fn every_actual_small_type_compare_boundary_and_retirement_can_refuse() {
    let ty = Ty::Tuple(vec![Ty::Ref(Box::new(Ty::I8)), Ty::Bool]);
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    ty.structural_eq_observed(&ty, &mut session, site())
        .unwrap();
    for stop in 1..=measured.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            ty.structural_eq_observed(&ty, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            ty.structural_eq_observed(&ty, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn equality_work_and_scratch_allowances_accumulate_without_renewing_fuel() {
    let ty = Ty::Tuple(vec![Ty::I8; 17]);
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    ty.structural_eq_observed(&ty, &mut session, site())
        .unwrap();
    for memory in [false, true] {
        let mut observer = if memory {
            Observer {
                byte_limit: Some(measured.bytes),
                ..Observer::default()
            }
        } else {
            Observer {
                work_limit: Some(measured.work),
                ..Observer::default()
            }
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(
            ty.structural_eq_observed(&ty, &mut session, site())
                .unwrap()
        );
        assert_eq!(
            ty.structural_eq_observed(&ty, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn equality_refuses_before_first_scratch_growth_and_even_false_result_needs_retirement() {
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut scratch: Vec<usize> = Vec::new();
    assert_eq!(
        work.reserve(&mut scratch),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(scratch.capacity(), 0);
    for other in [Ty::I8, Ty::U8] {
        let mut observer = Observer {
            retirement: true,
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            Ty::I8.structural_eq_observed(&other, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "retirement");
    }
}
