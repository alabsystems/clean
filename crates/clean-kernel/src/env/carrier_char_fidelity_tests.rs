// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! P2 fidelity gate — the seeded `Char` carrier vs the genuine Lean v4.30 oracle
//! (`tests/fixtures/carrier_v4_30/oracle_decls.txt`).
//!
//! Ground truth (oracle):
//! ```text
//! structure Char where mk :: (val : UInt32) (valid : UInt32.isValidChar val)
//! Char.val : Char → UInt32          (projection i=0)
//! Char.valid : ∀ self, UInt32.isValidChar (Char.val self)   (projection i=1)
//! Char.ofNat : Nat → Char           (invalid code points → '\0')
//! ```
//! The behavioural half (`Char.ofNat` invalid-cp → 0, `Char.toNat`,
//! `Char.utf8Size`) is checked against `lean` #eval by the differential harness
//! (`carrier_differential_tests.rs`); this module pins the SHAPE.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;

/// Peel a Pi telescope: returns `[dom0, dom1, …, codomain]`.
// `while let … = cur.kind()` borrows `cur` for the whole body, so the tail
// re-assignment `cur = cod` cannot use the clippy-suggested `while let` form.
#[allow(clippy::while_let_loop)]
fn peel_pi(e: &Expr) -> Vec<Expr> {
    let mut out = Vec::new();
    let mut cur = e.clone();
    loop {
        let next = match cur.kind() {
            ExprKind::Pi(_, dom, cod) => {
                out.push(dom.as_ref().clone());
                cod.as_ref().clone()
            }
            _ => break,
        };
        cur = next;
    }
    out.push(cur);
    out
}
fn is_const(e: &Expr, n: &str) -> bool {
    matches!(e.kind(), ExprKind::Const(name, _) if name.to_string() == n)
}

#[test]
fn test_char_seed_shape_matches_v4_30_oracle() {
    let env = Environment::try_with_prelude().expect("native prelude");

    // Char : Type, single constructor Char.mk (ctor idx 0).
    let char_ty = env.get_const(&Name::from_string("Char")).expect("Char");
    assert!(
        matches!(char_ty.type_.kind(), ExprKind::Sort(_)),
        "Char : Sort"
    );
    let char_ind = env
        .get_inductive(&Name::from_string("Char"))
        .expect("Char inductive");
    assert_eq!(char_ind.constructor_names.len(), 1, "Char has 1 ctor");

    // Char.mk : (val : UInt32) → (valid : UInt32.isValidChar val) → Char.
    let mk = env
        .get_const(&Name::from_string("Char.mk"))
        .expect("Char.mk");
    let mk_parts = peel_pi(&mk.type_);
    assert_eq!(mk_parts.len(), 3, "Char.mk : UInt32 → _ → Char (2 fields)");
    assert!(is_const(&mk_parts[0], "UInt32"), "Char.mk field 0 : UInt32");
    assert!(
        is_const(mk_parts[1].get_app_fn(), "UInt32.isValidChar"),
        "Char.mk field 1 : UInt32.isValidChar _"
    );
    assert!(is_const(&mk_parts[2], "Char"), "Char.mk returns Char");

    // Char.val : Char → UInt32.
    let val = env
        .get_const(&Name::from_string("Char.val"))
        .expect("Char.val");
    let vp = peel_pi(&val.type_);
    assert_eq!(vp.len(), 2);
    assert!(
        is_const(&vp[0], "Char") && is_const(&vp[1], "UInt32"),
        "Char.val : Char → UInt32"
    );

    // Char.valid : (self : Char) → UInt32.isValidChar (Char.val self).
    let valid = env
        .get_const(&Name::from_string("Char.valid"))
        .expect("Char.valid");
    let vlp = peel_pi(&valid.type_);
    assert!(is_const(&vlp[0], "Char"), "Char.valid domain Char");
    let vlp_last = vlp[vlp.len() - 1].get_app_fn();
    assert!(
        is_const(vlp_last, "UInt32.isValidChar"),
        "Char.valid : … → UInt32.isValidChar _"
    );

    // Char.ofNat : Nat → Char ; Char.toNat : Char → Nat.
    let ofnat = env
        .get_const(&Name::from_string("Char.ofNat"))
        .expect("Char.ofNat");
    let op = peel_pi(&ofnat.type_);
    assert!(
        is_const(&op[0], "Nat") && is_const(&op[1], "Char"),
        "Char.ofNat : Nat → Char"
    );
    let tonat = env
        .get_const(&Name::from_string("Char.toNat"))
        .expect("Char.toNat");
    let tp = peel_pi(&tonat.type_);
    assert!(
        is_const(&tp[0], "Char") && is_const(&tp[1], "Nat"),
        "Char.toNat : Char → Nat"
    );

    // The isValidChar predicates + utf8Size are seeded.
    assert!(env
        .get_const(&Name::from_string("Nat.isValidChar"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("UInt32.isValidChar"))
        .is_some());
    assert!(env.get_const(&Name::from_string("Char.utf8Size")).is_some());

    // Structure fields, in order: [val, valid].
    let fields = env
        .get_structure_field_names(&Name::from_string("Char"))
        .expect("Char structure fields");
    assert_eq!(
        fields.iter().map(|n| n.to_string()).collect::<Vec<_>>(),
        vec!["val".to_string(), "valid".to_string()],
        "Char structure fields = [val, valid]"
    );
}
