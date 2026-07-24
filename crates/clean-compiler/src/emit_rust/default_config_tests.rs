// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ir::IRBody;
use crate::ir_checker::IRError;
use clean_kernel::Name;

fn var(n: u32) -> VarId {
    VarId(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

#[test]
fn test_emit_rust_default_config_checks_ir() {
    let decl = IRDecl {
        name: name("invalid_default"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };

    let result = emit_rust(&[decl]);
    assert!(
        result.is_err(),
        "emit_rust should return Err for invalid IR"
    );
    assert!(
        matches!(result, Err(IRError::UndefinedVariable(_))),
        "expected UndefinedVariable error, got: {result:?}",
    );
}
