// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn only_actual_whole_image_writes_make_bulk_assertions_replayable() {
    for copy in [false, true] {
        let source = bulk_module(copy, 2);
        let error = Interpreter::with_module(&source)
            .execute_func(FuncId::new(0), [])
            .unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::Panic);
        assert_eq!(error.panic.as_ref().unwrap().kind, AssertKind::Unspecified);
        let trace = parity(&source, vec![]);
        assert!(
            trace
                .events
                .iter()
                .any(|event| event.phase == ExecutionPhase::SparseRun)
        );
        let partial = bulk_module(copy, 1);
        let error = Interpreter::with_module(&partial)
            .execute_func(FuncId::new(0), [])
            .unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert!(error.panic.is_none());
        parity(&partial, vec![]);
    }
}
