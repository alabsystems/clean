// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn function(id: u32, name: &str) -> Function {
    Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0))
}
pub(super) fn module() -> Module {
    let mut m = Module::new("");
    m.functions = vec![function(900, "raw 'λ\0尾\n"), function(17, "other")];
    m
}
pub(super) fn node(function: u32) -> BinaryProjectionError {
    BinaryProjectionError::ConstructAheadOfWireTag {
        construct: "raw construct",
        site: Some(WireNodeSite {
            function,
            block: u32::MAX,
            index: usize::MAX,
        }),
    }
}
pub(super) fn actual() -> NativeVerificationBundle {
    let mut b = crate::request::tests::native_bundle();
    b.module.completeness = Some(ModuleCompleteness::Complete);
    b.module.types.push(Ty::Error);
    b
}
