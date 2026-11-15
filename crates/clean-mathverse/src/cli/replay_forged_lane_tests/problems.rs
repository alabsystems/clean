// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Refusal bookkeeping shared by the battery's table-driven modules: every
//! module of a table is run before a test fails, so one failure names each
//! lane and module that did not refuse.

/// `None` when `result` refuses the run with `needle` in its reason; otherwise
/// what the lane did instead. Every module is run before a test fails, so a
/// failure names each lane and module that did not refuse.
pub(super) fn refusal_problem<T: std::fmt::Debug, E: std::fmt::Display>(
    lane: &str,
    module: &str,
    result: Result<T, E>,
    needle: &str,
) -> Option<String> {
    match result {
        Ok(ok) => Some(format!(
            "{lane} on {module} must refuse the run, got {ok:?}"
        )),
        Err(e) => {
            let message = e.to_string();
            (!message.contains(needle))
                .then(|| format!("{lane} on {module} refused without `{needle}`: {message}"))
        }
    }
}

pub(super) fn assert_no_problems(problems: &[String]) {
    assert!(
        problems.is_empty(),
        "{} problem(s):\n{}",
        problems.len(),
        problems.join("\n")
    );
}
