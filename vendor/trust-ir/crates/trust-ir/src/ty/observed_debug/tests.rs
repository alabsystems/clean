// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Raw ordinary Debug and observed primitive source-fee controls; all UNRUN.
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use std::{cell::Cell, rc::Rc};
mod abi_fixture;
mod registry;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    work: usize,
    bytes: usize,
    stop: Option<usize>,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original raw-debug stop");
        }
        self.work += e.work;
        self.bytes += e.copy_bytes;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(crate::FuncId::new(1551))
}
fn dispose<O: ExecutionObserver>(text: String, s: &mut ObservedSession<'_, O>) {
    s.retirement_step(site(), size_of::<String>() + 1);
    drop(text);
    s.retirement_poll(site());
}
fn observed(ty: &Ty) -> (String, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = ty.debug_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (out, o)
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
        Ty::Vector(Box::new(Ty::Bool), u32::MAX),
        Ty::Tensor(Box::new(Ty::I32), 2),
        Ty::Tensor(Box::new(Ty::Tensor(Box::new(Ty::U8), 0)), u32::MAX),
        Ty::Tuple(vec![]),
        Ty::Tuple(vec![Ty::Bool, Ty::I32]),
        Ty::Struct(StructId::new(7)),
        Ty::Enum(EnumId::new(8)),
        Ty::Func(FuncTyId::new(9)),
        Ty::Closure(ClosureTyId::new(10)),
        Ty::Record(RecordId::new(11)),
        Ty::Sequence(TyId::new(12)),
        Ty::Array(TyId::new(13), u64::MAX),
        Ty::Refine(TyId::new(14), PredId::new(15)),
        Ty::Set(TyId::new(16), SetRepr::Bitset),
        Ty::Set(TyId::new(17), SetRepr::Boxed),
        Ty::Ref(Box::new(Ty::Bool)),
        Ty::RefMut(Box::new(Ty::I32)),
        Ty::PtrConst(Box::new(Ty::I64)),
        Ty::PtrMut(Box::new(Ty::F64)),
        Ty::Rc(Box::new(Ty::Never)),
        Ty::Dialect(Box::new(DialectTy {
            namespace: "bad.name".into(),
            name: "中\n".into(),
            version: 0,
        })),
        Ty::handle("a'\n中", "rt\t"),
        Ty::FatPtr(FatPtrKind::Slice(TyId::new(18))),
        Ty::FatPtr(FatPtrKind::Str),
        Ty::FatPtr(FatPtrKind::TraitObject { trait_id: u32::MAX }),
        Ty::FatPtr(FatPtrKind::ContainerLen),
        Ty::FatPtr(FatPtrKind::ContainerVtable),
    ]
}
#[test]
fn every_inhabited_raw_type_variant_and_all_fixed_payloads_match_actual_derived_debug() {
    for ty in types() {
        assert_eq!(observed(&ty).0, format!("{ty:?}"));
    }
}
#[test]
fn complete_function_abi_all_five_modes_bindings_and_unvalidated_metadata_match_debug() {
    for mode in abi_fixture::modes() {
        let f = FuncTy {
            params: vec![Ty::Tuple(types())],
            returns: vec![Ty::Ptr],
            is_vararg: true,
            abi: Some(abi_fixture::abi(mode)),
        };
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = f.debug_observed(&mut s, site()).unwrap();
        assert_eq!(out, format!("{f:?}"));
        dispose(out, &mut s);
    }
    let f = FuncTy::unrecorded(vec![], vec![], false);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = f.debug_observed(&mut s, site()).unwrap();
    assert_eq!(out, format!("{f:?}"));
    dispose(out, &mut s);
    for convention in [
        crate::CallingConv::C,
        crate::CallingConv::Fast,
        crate::CallingConv::Cold,
        crate::CallingConv::Rust,
        crate::CallingConv::Swift,
        crate::CallingConv::CUnwind,
        crate::CallingConv::SysV64,
        crate::CallingConv::Win64,
        crate::CallingConv::Aapcs,
        crate::CallingConv::EfiApi,
        crate::CallingConv::VectorCall,
        crate::CallingConv::RustCold,
    ] {
        let mut abi = abi_fixture::abi(AbiPassMode::Ignore);
        abi.lowered_convention = convention;
        let f = FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
            abi: Some(abi),
        };
        assert_function(&f);
    }
    for capture in [
        AbiCapture::Any,
        AbiCapture::ReadOnly,
        AbiCapture::Address,
        AbiCapture::None,
    ] {
        for extension in [AbiExtension::None, AbiExtension::Sign, AbiExtension::Zero] {
            let attributes = AbiAttributes {
                capture,
                extension,
                ..AbiAttributes::default()
            };
            let scalar = AbiScalar {
                register: AbiRegister {
                    class: AbiRegisterClass::Integer,
                    bytes: 1,
                },
                source_offset: 0,
                source_bytes: 0,
                value_bits: 0,
                attributes,
            };
            let f = FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
                abi: Some(abi_fixture::abi(AbiPassMode::Direct(scalar))),
            };
            assert_function(&f);
        }
    }
}
#[test]
fn pinned_debug_unicode_property_quotes_combining_private_ignorable_and_unassigned_cases_match() {
    for text in [
        "'\"\\\n\t\r\0",
        "é",
        "\u{300}",
        "\u{e000}",
        "\u{85}",
        "\u{ad}",
        "\u{378}",
        "\u{200e}",
        "\u{e0100}",
        "\u{10ffff}",
    ] {
        let ty = Ty::handle(text, text);
        assert_eq!(observed(&ty).0, format!("{ty:?}"));
    }
}
#[test]
fn nested_inline_types_use_actual_observed_heap_tasks_and_match_ordinary_spelling() {
    let mut ty = Ty::Tuple(vec![Ty::Bool, Ty::handle("H", "rt")]);
    for _ in 0..192 {
        ty = Ty::Ref(Box::new(ty));
    }
    let expected = format!("{ty:?}");
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = ty.debug_observed(&mut s, site()).unwrap();
    assert_eq!(out, expected);
    dispose(out, &mut s);
    ty.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn every_actual_raw_debug_visit_growth_escape_retirement_and_publication_callback_refuses() {
    let ty = Ty::Tuple(vec![
        Ty::handle("é'", "rt"),
        Ty::Vector(Box::new(Ty::I32), 4),
    ]);
    let (_, baseline) = observed(&ty);
    for cut in 1..=baseline.events.len() {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            ty.debug_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original raw-debug stop");
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn exact_raw_debug_cumulative_work_copy_owner_caps_refuse_second_call_without_renewal() {
    let ty = Ty::Tuple(vec![Ty::Bool, Ty::Ptr]);
    let (_, baseline) = observed(&ty);
    for copy in [false, true] {
        let cap = baseline
            .events
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(cap)
        } else {
            o.work_cap = Some(cap)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = ty.debug_observed(&mut s, site()).unwrap();
        assert_eq!(
            ty.debug_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        dispose(out, &mut s);
    }
}
#[test]
fn zero_instruction_fuel_and_preexisting_stop_preserve_raw_debug_original_context() {
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let out = Ty::Bool.debug_observed(&mut s, site()).unwrap();
    assert_eq!(out, "Bool");
    assert_eq!(s.remaining_fuel(), 0);
    dispose(out, &mut s);
    drop(s);
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        Ty::Bool.debug_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(calls.get(), 1);
}
#[test]
fn complete_returned_raw_debug_string_stays_caller_owned_across_next_original_fee_refusal() {
    let ty = Ty::handle("é'", "rt");
    let (expected, baseline) = observed(&ty);
    let mut o = Observer {
        stop: Some(baseline.events.len() + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut held = Some(ty.debug_observed(&mut s, site()).unwrap());
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: size_of::<String>()
        })
        .is_err()
    );
    assert_eq!(held.as_ref(), Some(&expected));
    dispose(held.take().unwrap(), &mut s);
    assert!(held.is_none());
    assert_eq!(s.first_refusal().unwrap().cause, "original raw-debug stop");
}
#[test]
fn final_raw_debug_publication_refusal_cannot_return_partial_or_empty_success() {
    let ty = Ty::Tuple(types());
    let (_, baseline) = observed(&ty);
    assert_eq!(
        baseline.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    let mut o = Observer {
        stop: Some(baseline.events.len()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        ty.debug_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn actual_shared_ty_display_uses_pinned_complete_scalar_escape_visit_tariff() {
    let ty = Ty::handle("\u{300}\u{e000}\u{378}", "r");
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = ty.display_observed(&mut s, site()).unwrap();
    assert_eq!(out, format!("{ty}"));
    dispose(out, &mut s);
    drop(s);
    let classifications = o
        .events
        .iter()
        .filter(|e| e.work == 2928 && e.copy_bytes == size_of::<core::char::EscapeDebug>())
        .count();
    assert_eq!(classifications, 4);
}

fn assert_function(f: &FuncTy) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = f.debug_observed(&mut s, site()).unwrap();
    assert_eq!(out, format!("{f:?}"));
    dispose(out, &mut s);
}
#[test]
fn actual_fixed_task_array_is_refused_before_construction_or_heap_growth() {
    let ty = Ty::Ref(Box::new(Ty::Bool));
    let mut observer = Observer {
        stop: Some(2),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = State::default();
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    // This is the real type dispatch used by run(), not a parallel formatter.
    // It inspects the borrowed fixed Ty then prepays its three actual tasks.
    assert_eq!(
        state.ty(&ty, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.tasks.capacity(), 0);
    assert_eq!(state.output.capacity(), 0);
    work.retire(take(&mut state.tasks));
    work.retire(take(&mut state.output));
    drop(state);
    drop(work);
    let _ = ty.retire_observed(&mut session, site());
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original raw-debug stop"
    );
    drop(session);
    assert_eq!(
        observer.events[1],
        ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 3,
            copy_bytes: 3 * size_of::<Task<'_>>()
        }
    );
}
