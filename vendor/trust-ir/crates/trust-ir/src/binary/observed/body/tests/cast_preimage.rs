// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn error() -> String {
    "function #17 spells the producer-internal Ty::Error, which has no binary spelling, so the body has no identity to state".to_owned()
}
fn raw(in_return: bool, nested: bool) -> Module {
    let mut m = module();
    let ty = if nested {
        Ty::Tuple(vec![Ty::I8, Ty::Ref(Box::new(Ty::Error))])
    } else {
        Ty::Error
    };
    let attrs = ParamAttrs {
        pass: Some(PassMode::Cast {
            pieces: vec![Ty::U8, ty, Ty::I64],
        }),
        ..ParamAttrs::default()
    };
    if in_return {
        m.functions[0].attrs.ret = attrs;
    } else {
        m.functions[0].attrs.params = vec![ParamAttrs::default(), attrs, ParamAttrs::default()];
    }
    m
}
#[test]
fn ordinary_body_refuses_raw_cast_piece_error_for_params_return_and_all_inline_children() {
    for in_return in [false, true] {
        for nested in [false, true] {
            let m = raw(in_return, nested);
            assert_eq!(m.function_body_digest(f()), Err(error()));
            run(&m, f());
        }
    }
}
#[test]
fn valid_param_return_cast_preimages_remain_complete_wire_digest_inputs() {
    let mut m = module();
    let original = m.function_body_digest(f()).unwrap();
    m.functions[0].attrs.params.push(ParamAttrs {
        pass: Some(PassMode::Cast {
            pieces: vec![Ty::I64, Ty::U8],
        }),
        ..ParamAttrs::default()
    });
    let with_param = m.function_body_digest(f()).unwrap();
    assert_ne!(with_param, original);
    run(&m, f());
    m.functions[0].attrs.ret.pass = Some(PassMode::Cast {
        pieces: vec![Ty::Tuple(vec![Ty::I8, Ty::Ref(Box::new(Ty::I64))])],
    });
    assert_ne!(m.function_body_digest(f()).unwrap(), with_param);
    run(&m, f());
}
#[test]
fn complete_raw_cast_refusal_keeps_original_drop_before_type_before_inlining_order() {
    let mut m = raw(false, true);
    m.functions[0].scopes = Some(vec![inlining()]);
    assert_eq!(m.function_body_digest(f()), Err(error()));
    run(&m, f());
    let mut d = ambiguous();
    d.functions[0].attrs.ret.pass = m.functions[0].attrs.params[1].pass.clone();
    d.functions[0].scopes = Some(vec![inlining()]);
    let expected=Err("function #17 drops i64, which two or more drop-glue rows name, so the body has no identity to state".to_owned());
    assert_eq!(d.function_body_digest(f()), expected);
    run(&d, f());
}
#[test]
fn raw_cast_preflight_all_interior_cuts_and_exact_cumulative_one_short_withhold_the_reason() {
    let m = raw(true, true);
    let baseline = run(&m, f());
    for cut in 1..=baseline.split {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut o,
        );
        assert_eq!(
            call(&m, f(), &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().progress,
            baseline.events()[cut - 1]
        );
        assert_eq!(s.remaining_fuel(), 0);
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events()[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    for copies in [false, true] {
        let mut o = Observer::default();
        let charge = total(baseline.events(), copies);
        assert!(charge > 0);
        if copies {
            o.copy_cap = Some(charge - 1);
        } else {
            o.work_cap = Some(charge - 1);
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            call(&m, f(), &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
    }
}
