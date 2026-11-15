// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::{FuncTy, Ty};

#[test]
fn fresh_signature_constructor_preserves_exact_legacy_data() {
    for is_vararg in [false, true] {
        let actual = FuncTy::unrecorded(vec![Ty::Ptr, Ty::U64], vec![Ty::I64, Ty::Bool], is_vararg);
        assert_eq!(
            actual,
            FuncTy {
                params: vec![Ty::Ptr, Ty::U64],
                returns: vec![Ty::I64, Ty::Bool],
                is_vararg,
                abi: None,
            }
        );
    }
    let empty = FuncTy::unrecorded(vec![], vec![], false);
    assert!(empty.params.is_empty() && empty.returns.is_empty());
    assert!(!empty.is_vararg && empty.abi.is_none());
}

#[test]
fn fresh_signature_constructor_moves_owned_carriers_without_reallocation() {
    let params = vec![Ty::Ptr, Ty::U64, Ty::I64];
    let returns = vec![Ty::U64, Ty::Bool];
    let parameter_storage = params.as_ptr();
    let return_storage = returns.as_ptr();
    let actual = FuncTy::unrecorded(params, returns, true);
    assert_eq!(actual.params.as_ptr(), parameter_storage);
    assert_eq!(actual.returns.as_ptr(), return_storage);
    assert_eq!(actual.params, [Ty::Ptr, Ty::U64, Ty::I64]);
    assert_eq!(actual.returns, [Ty::U64, Ty::Bool]);
    assert!(actual.is_vararg && actual.abi.is_none());
}
