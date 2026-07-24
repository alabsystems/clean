// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused do-match q-pattern regressions for #796.

use super::*;

#[test]
fn test_elab_do_match_q_pattern_static_supported() {
    let env = Environment::with_prelude();
    let result = elab_with_env(
        &env,
        r#"
do { match q(Type) with | q($x) => return x | _ => return q(Prop) }
"#,
    );
    assert!(
        result.is_ok(),
        "static q-pattern do-match should elaborate, got {result:?}"
    );
}

#[test]
fn test_elab_do_match_q_pattern_runtime_fails_closed() {
    let env = Environment::with_prelude();
    let err = elab_with_env(
        &env,
        r#"
fun (e : Type) =>
  do { match e with | q($x) => return x | _ => return e }
"#,
    )
    .expect_err("runtime q-pattern do-match should fail closed for now");
    assert!(
        matches!(err, ElabError::NotImplemented(ref msg) if msg.contains("runtime q-pattern do-match")),
        "runtime q-pattern do-match should report a clear fail-closed error, got {err:?}"
    );
}
