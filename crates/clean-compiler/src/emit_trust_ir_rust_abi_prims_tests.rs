// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The native carrier-primitive table (`crate::carrier_prims`): which names
//! are rows, at which signatures, and which are deliberately not.

use crate::carrier_prims::*;
use crate::ir::IRType;
use clean_kernel::Name;

fn prim(name: &str, nat: bool) -> Option<CarrierPrim> {
    carrier_prim(&Name::from_string(name), nat)
}

#[test]
fn every_width_has_its_arithmetic_and_comparisons() {
    for (carrier, width) in [
        ("UInt8", UIntWidth::W8),
        ("UInt16", UIntWidth::W16),
        ("UInt32", UIntWidth::W32),
        ("UInt64", UIntWidth::W64),
    ] {
        assert_eq!(
            prim(&format!("{carrier}.add"), false),
            Some(CarrierPrim::Bin(ScalarBin::Add, width))
        );
        assert_eq!(
            prim(&format!("{carrier}.decLe"), false),
            Some(CarrierPrim::Cmp(ScalarCmp::Ule, width))
        );
        // `div`/`mod` keep Lean's `x / 0 = 0`, which no plain machine
        // division has; they are not rows.
        assert_eq!(prim(&format!("{carrier}.div"), false), None);
        assert_eq!(prim(&format!("{carrier}.mod"), false), None);
    }
    // `USize` is host-width: never a row.
    assert_eq!(prim("USize.add", false), None);
}

#[test]
fn nat_rows_exist_only_at_the_pinned_handle() {
    for name in ["Nat.add", "Nat.sub", "Nat.decEq", "Nat.ble", "UInt64.toNat"] {
        assert!(prim(name, true).is_some(), "{name} at the handle");
        assert_eq!(prim(name, false), None, "{name} without the handle");
    }
    // Not exported by trust-bignum: never a row, so never a call.
    for name in ["Nat.mul", "Nat.div", "Nat.mod", "Nat.pow", "Nat.land"] {
        assert_eq!(prim(name, true), None, "{name}");
    }
}

#[test]
fn aliases_are_not_rows() {
    // These reach a row only through their kernel values
    // (`opt::resolve_carrier_prims`), never by name.
    for name in [
        "instDecidableUInt64Le",
        "instDecidableEqUInt32",
        "and",
        "or",
        "decide",
    ] {
        assert_eq!(prim(name, true), None, "{name}");
    }
}

#[test]
fn signatures_match_arity_and_result() {
    let decide = CarrierPrim::Decide;
    assert_eq!(decide.params(), vec![IRType::Erased, IRType::Bool]);
    assert_eq!(decide.ret(), IRType::Bool);
    let lt = CarrierPrim::Nat(NatOp::Lt);
    assert_eq!(lt.params(), vec![IRType::Object, IRType::Object]);
    assert_eq!(lt.ret(), IRType::Bool);
    let to_nat = CarrierPrim::Nat(NatOp::OfUInt(UIntWidth::W8));
    assert_eq!(to_nat.params(), vec![IRType::UInt8]);
    assert_eq!(to_nat.ret(), IRType::Object);
}

#[test]
fn carrier_primitive_rejects_escaped_display_collisions() {
    for text in [
        "UInt8.decLt",
        "UInt32.add",
        "Bool.and",
        "Decidable.decide",
        "Nat.blt",
    ] {
        let escaped = Name::anon().str(text);
        assert_ne!(escaped, Name::from_string(text));
        assert!(
            carrier_prim(&escaped, true).is_none(),
            "{text}: displayed text cannot select a primitive"
        );
    }
}
