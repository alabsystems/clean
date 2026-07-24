// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Environment, Name};

#[test]
fn with_prelude_includes_ite() {
    let env = Environment::with_prelude();
    assert!(
        env.get_const(&Name::from_string("ite")).is_some(),
        "with_prelude() must provide ite for elaborating if-expressions"
    );
}
