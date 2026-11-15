// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

mod tests {
    use super::*;
    #[cfg(not(debug_assertions))]
    use crate::{BinderInfo, Expr};

    fn snapshot() -> InferenceStats {
        inference_stats_snapshot().expect("diagnostic feature enabled")
    }

    #[test]
    fn exact_environment_opt_in_and_eight_lifetime_checkpoints() {
        assert!(early_enabled(Some("1")));
        for value in [
            None,
            Some(""),
            Some("0"),
            Some("true"),
            Some(" 1"),
            Some("1 "),
        ] {
            assert!(!early_enabled(value));
        }
        let kind = ExprKind::Sort(crate::Level::zero());
        let mut state = State::new(true);
        for (index, threshold) in CHECKPOINTS.iter().copied().enumerate() {
            state.lifetime_visits = threshold - 2;
            assert!(state.visit(&kind, 3, false).is_none());
            let (at, counts) = state.visit(&kind, 3, false).expect("fixed checkpoint");
            assert_eq!(at, threshold);
            assert_eq!(counts.fast_visits, 2);
            assert_eq!(state.next_checkpoint, index + 1);
            // The public reset has exactly this effect, not a new quota.
            state.counts = InferenceStats::default();
        }
        state.lifetime_visits = u64::MAX - 1;
        assert!(state.visit(&kind, 1, true).is_none());
        assert!(state.visit(&kind, 1, true).is_none());
        assert_eq!(state.next_checkpoint, 8);
        let mut silent = State::new(false);
        silent.lifetime_visits = CHECKPOINTS[0] - 1;
        assert!(silent.visit(&kind, 1, true).is_none());
    }

    #[test]
    fn kind_mode_depth_and_counter_overflow_are_scalar() {
        let mut state = State::new(false);
        state.visit(&ExprKind::Sort(crate::Level::zero()), 7, false);
        state.visit(&ExprKind::BVar(0), 3, true);
        assert_eq!(state.counts.fast_visits, 2);
        assert_eq!(state.counts.strict_visits, 1);
        assert_eq!(state.counts.infer_only_visits, 1);
        assert_eq!(state.counts.node_kinds[2], 1);
        assert_eq!(state.counts.node_kinds[0], 1);
        assert_eq!(state.counts.node_kinds.iter().sum::<u64>(), 2);
        assert_eq!(state.counts.max_frame_depth, 7);
        state.counts.fast_visits = u64::MAX;
        state.counts.node_kinds[0] = u64::MAX;
        state.visit(&ExprKind::BVar(0), 1, false);
        assert_eq!(state.counts.fast_visits, u64::MAX);
        assert_eq!(state.counts.node_kinds[0], u64::MAX);
        assert!(size_of::<State>() < 512);
    }

    #[test]
    fn aggregate_api_is_thread_local_and_reset_preserves_quota() {
        inference_stats_reset();
        record_arc(ArcEvent::Hit, 17);
        record_arc(ArcEvent::Admission, 2);
        record_memo_rotation(3);
        record_operation(Operation::OpenLam);
        assert_eq!(snapshot().arc_peak_entries, 17, "not the sum of checkers");
        let (visits, checkpoint) = STATE.with(|state| {
            let mut state = state.borrow_mut();
            state.lifetime_visits = 1234;
            state.next_checkpoint = 1;
            (state.lifetime_visits, state.next_checkpoint)
        });
        std::thread::spawn(|| {
            inference_stats_reset();
            assert_eq!(snapshot(), InferenceStats::default());
            record_arc(ArcEvent::Miss, 99);
            assert_eq!(snapshot().arc_misses, 1);
        })
        .join()
        .expect("independent thread");
        assert_eq!(snapshot().arc_hits, 1);
        assert_eq!(snapshot().arc_rotations, 1);
        assert_eq!(snapshot().arc_evicted_entries, 3);
        assert_eq!(snapshot().arc_misses, 0);
        assert!(inference_stats_report().contains("arc_peak_entries: 17"));
        for event in [
            ArcEvent::NoFrame,
            ArcEvent::InferenceError,
            ArcEvent::CapacityRefusal,
            ArcEvent::RecursiveFill,
        ] {
            record_arc(event, 0);
        }
        for operation in [
            Operation::OpenPi,
            Operation::OpenLet,
            Operation::AbstractLam,
            Operation::SubstLet,
            Operation::InstantiateApp,
        ] {
            record_operation(operation);
        }
        record_visit(&ExprKind::Sort(crate::Level::zero()), 1, false);
        assert_eq!(snapshot().arc_inference_errors, 1);
        assert_eq!(snapshot().arc_capacity_refusals, 1);
        assert_eq!(snapshot().arc_recursive_fills, 1);
        assert_eq!(snapshot().subst_let_calls, 1);
        assert_eq!(snapshot().fast_visits, 1);
        inference_stats_reset();
        assert_eq!(snapshot(), InferenceStats::default());
        STATE.with(|state| {
            let state = state.borrow();
            assert_eq!(
                (state.lifetime_visits, state.next_checkpoint),
                (visits + 1, checkpoint)
            );
        });
    }

    #[test]
    fn window_rotation_counters_saturate() {
        inference_stats_reset();
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            state.counts.arc_rotations = u64::MAX;
            state.counts.arc_evicted_entries = u64::MAX - 1;
        });
        record_memo_rotation(2);
        assert_eq!(snapshot().arc_rotations, u64::MAX);
        assert_eq!(snapshot().arc_evicted_entries, u64::MAX);
        inference_stats_reset();
    }

    #[test]
    fn checkpoint_output_is_bounded_and_io_error_is_diagnostic_only() {
        let mut bytes = Vec::new();
        let counts = InferenceStats {
            fast_visits: u64::MAX,
            ..InferenceStats::default()
        };
        write_checkpoint(&mut bytes, u64::MAX, &counts);
        assert!(bytes.len() < 4096);
        assert_eq!(bytes.iter().filter(|byte| **byte == b'\n').count(), 1);
        struct Broken;
        impl std::io::Write for Broken {
            fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
                Err(std::io::Error::new(
                    std::io::ErrorKind::BrokenPipe,
                    "diagnostic sink closed",
                ))
            }
            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
        write_checkpoint(&mut Broken, 1_000, &counts);
        assert_eq!(counts.fast_visits, u64::MAX);
    }

    #[cfg(not(debug_assertions))]
    struct MemoFrame<'tc, 'env>(&'tc crate::TypeChecker<'env>);

    #[cfg(not(debug_assertions))]
    impl<'tc, 'env> MemoFrame<'tc, 'env> {
        fn new(checker: &'tc crate::TypeChecker<'env>) -> Self {
            assert_eq!(checker.infer_memo_depth.replace(1), 0);
            assert!(checker.infer_arc_memo.borrow().is_empty());
            Self(checker)
        }
    }

    #[cfg(not(debug_assertions))]
    impl Drop for MemoFrame<'_, '_> {
        fn drop(&mut self) {
            self.0.infer_memo_depth.set(0);
            self.0.infer_arc_memo.borrow_mut().clear();
        }
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn actual_fast_arc_capacity_hits_errors_and_direct_bypass() {
        use crate::{Environment, TypeChecker, TypeError};
        use std::sync::Arc;
        let env = Environment::new();
        for capacity in [0, 1] {
            let mut checker = TypeChecker::new(&env);
            checker.set_max_cache_entries(capacity);
            let node = Arc::new(Expr::prop());
            inference_stats_reset();
            assert_eq!(
                checker.infer_type_fast_arc(&node).expect("direct"),
                Expr::type_()
            );
            assert_eq!(snapshot().arc_no_frame_bypasses, 1);
            assert_eq!(snapshot().arc_admissions, 0);
            let _frame = MemoFrame::new(&checker);
            inference_stats_reset();
            for _ in 0..2 {
                assert_eq!(
                    checker.infer_type_fast_arc(&node).expect("shared Sort"),
                    Expr::type_()
                );
            }
            let good = snapshot();
            assert_eq!(good.arc_admissions, capacity as u64);
            assert_eq!(good.arc_hits, capacity as u64);
            assert_eq!(good.arc_misses, 2 - capacity as u64);
            assert_eq!(
                good.arc_capacity_refusals,
                if capacity == 0 { 2 } else { 0 }
            );
            assert_eq!(good.arc_peak_entries, capacity);
            assert!(matches!(
                checker.infer_type_fast_arc(&Arc::new(Expr::bvar(0))),
                Err(TypeError::UnboundVariable(0))
            ));
            let bad = snapshot();
            assert_eq!(bad.arc_misses, good.arc_misses + 1);
            assert_eq!(bad.arc_inference_errors, 1);
            assert_eq!(bad.arc_admissions, good.arc_admissions);
            assert_eq!(bad.arc_capacity_refusals, good.arc_capacity_refusals);
            assert_eq!(bad.node_kinds[0], 1);
        }
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn actual_dependent_lam_let_and_pi_preserve_results() {
        use crate::{Environment, Name, TypeChecker};
        let env = Environment::new();
        let checker = TypeChecker::new(&env);
        let term = Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::lam(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::let_named(
                    Name::anon(),
                    Expr::bvar(1),
                    Expr::bvar(0),
                    Expr::bvar(0),
                    false,
                ),
            ),
        );
        let expected = Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        );
        inference_stats_reset();
        assert_eq!(
            checker.infer_type_full(&term).expect("dependent term"),
            expected
        );
        let stats = snapshot();
        assert_eq!(stats.open_lam_calls, 2);
        assert_eq!(stats.abstract_lam_calls, 2);
        assert_eq!(stats.open_let_calls, 1);
        assert_eq!(stats.subst_let_calls, 1);
        assert!(stats.strict_visits > 0);
        assert!(stats.max_frame_depth >= 3);
        assert_eq!(checker.ctx_len(), 0);
        assert_eq!(checker.infer_memo_depth.get(), 0);
        assert!(checker.infer_arc_memo.borrow().is_empty());
        inference_stats_reset();
        assert!(checker.infer_type_full(&expected).is_ok());
        assert_eq!(snapshot().open_pi_calls, 2);
        assert_eq!(checker.ctx_len(), 0);
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn actual_strict_mode_rejects_bad_let_after_infer_only_cache() {
        use crate::{Environment, Name, TypeChecker, TypeError};
        use std::sync::Arc;
        let env = Environment::new();
        let checker = TypeChecker::new(&env);
        let bad = Arc::new(Expr::app(
            Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
            Expr::prop(),
        ));
        let _frame = MemoFrame::new(&checker);
        inference_stats_reset();
        assert_eq!(
            checker.infer_type_fast_arc(&bad).expect("infer-only"),
            Expr::prop()
        );
        assert!(snapshot().infer_only_visits > 0);
        assert_eq!(snapshot().strict_visits, 0);
        let term = Expr::let_named_arc(
            Name::anon(),
            Arc::new(Expr::prop()),
            bad,
            Arc::new(Expr::bvar(0)),
            false,
        );
        assert!(matches!(
            checker.infer_type_full(&term),
            Err(TypeError::TypeMismatch { .. })
        ));
        assert!(snapshot().strict_visits > 0);
        assert_eq!(
            snapshot().open_let_calls,
            0,
            "the bad value fails before opening"
        );
        assert_eq!(snapshot().subst_let_calls, 0);
        assert_eq!(checker.ctx_len(), 0);
        assert!(checker.infer_only.get());
    }
}
