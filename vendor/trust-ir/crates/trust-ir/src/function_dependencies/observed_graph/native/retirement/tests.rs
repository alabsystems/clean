// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::interpret::InterpretOptions;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            Err("original stop")
        } else {
            Ok(())
        }
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(73))
}
#[test]
fn deep_pending_node_is_retired_without_new_scratch_when_storage_admission_refuses() {
    let mut ty = Ty::Bool;
    for _ in 0..50_000 {
        ty = Ty::Ref(Box::new(ty));
    }
    let mut build = NativeBuild::new();
    let mut observer = Observer {
        stop_at: Some(1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        store_node(
            &mut build.graph,
            ReachNodeKind::Sink(DependencyRefusalKind::ImplicitDestructor(ty)),
            &mut session,
            site()
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(build.graph.nodes.is_empty());
    build.retire(&mut session, site());
    assert_eq!(session.first_refusal().unwrap().cause, "original stop");
    assert!(observer.events.len() > 50_000);
}
#[test]
fn deep_stored_node_retires_after_later_refusal_before_original_scope_returns() {
    let mut ty = Ty::Bool;
    for _ in 0..50_000 {
        ty = Ty::Tuple(vec![ty]);
    }
    let mut build = NativeBuild::new();
    let mut observer = Observer {
        stop_at: Some(3),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    store_node(
        &mut build.graph,
        ReachNodeKind::Sink(DependencyRefusalKind::ImplicitDestructor(ty)),
        &mut session,
        site(),
    )
    .unwrap();
    assert!(admit(&mut session, site(), 1, 0).is_err());
    build.retire(&mut session, site());
    assert_eq!(session.first_refusal().unwrap().cause, "original stop");
    assert!(observer.events.len() > 50_000);
}
