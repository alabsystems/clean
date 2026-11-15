// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

#[derive(Clone, Copy)]
enum Route {
    Whole(IdentityScheme),
    Checked,
    SourceBody,
}

fn run(route: Route, module: &Module, stop: Option<usize>) -> (R<ProofDigest>, Observer) {
    let mut observer = Observer {
        stop_at: stop,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let result = match route {
        Route::Whole(scheme) => observed_module_identity(module, scheme, &mut session, site()),
        Route::Checked => {
            observed_checked_module_identity(module, IdentityScheme::V3, &mut session, site())
        }
        Route::SourceBody => observed_source_function_identity(module, 0, &mut session, site()),
    };
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    if stop.is_some() {
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert_eq!(session.first_refusal().unwrap().progress.site, site());
    } else {
        assert!(session.first_refusal().is_none());
    }
    drop(session);
    (result, observer)
}

fn assert_held_error(route: Route, module: &Module) {
    let (held, baseline) = run(route, module, None);
    assert_eq!(held, Err(ObservedValueError::UnsupportedValue));
    let normal = baseline
        .events
        .iter()
        .rposition(|e| e.phase == ExecutionPhase::CanonicalSerialization)
        .unwrap();
    let suffix = normal + 1;
    assert!(!baseline.events[suffix..].is_empty());
    assert!(
        baseline.events[suffix..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    for cut in suffix + 1..=baseline.events.len() {
        let (actual, observed) = run(route, module, Some(cut));
        assert_eq!(
            actual, held,
            "a pool cleanup refusal cannot replace the type hole"
        );
        assert_eq!(&observed.events[..cut], &baseline.events[..cut]);
        assert!(
            observed.events[suffix..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn whole_and_checked_module_type_error_survives_every_late_pool_cleanup_cut() {
    let mut module = module();
    module.types.push(Ty::Tuple(vec![Ty::U8, Ty::Error]));
    for route in [
        Route::Whole(IdentityScheme::V2),
        Route::Whole(IdentityScheme::V3),
        Route::Checked,
    ] {
        assert_held_error(route, &module);
    }
    assert_eq!(
        module.types.last(),
        Some(&Ty::Tuple(vec![Ty::U8, Ty::Error]))
    );
}

#[test]
fn actual_source_body_projection_keeps_held_error_and_never_publishes_a_prefix() {
    let mut module = module();
    module.types.push(Ty::Tuple(vec![Ty::U8, Ty::Error]));
    assert_held_error(Route::SourceBody, &module);
    assert_eq!(module.functions.len(), 1);
    assert_eq!(module.functions[0].id, FuncId::new(17));
}
