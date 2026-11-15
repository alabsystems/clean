// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **M10 for `ir_lzc`: the interface, per body AND per global.**
//!
//! Split out of `crystal_a2_mint_lzc.rs` — read that file's header first for
//! what the chain is and what it does not claim. Two halves: the committed
//! triple projects under its pins, and each pin BITES one token off.
//!
//! The globals half is new in kind. `IRGlobal.mk : Nat → IRConst → IRGlobal`
//! carries an id and an initializer, so a global's NAME, its resolved array
//! TYPE and its LINKAGE have nowhere in the module to land; they are pinned in
//! the tag table's `globals` lane and compared by `project`. Its BYTES do have
//! somewhere to land, so they are not interface at all — a changed byte moves
//! the core digest instead of being refused, and the last check here is that
//! line drawn on the artifact rather than described.

use clean_verify::ir_mint;

use super::{canon, core_a, fixture, tags};

// ────────────────────────────────────────────────────────────────────────────
// M10 — the interface, per body and per global: accepted under the pins,
// refused one token off them.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m10_both_bodies_and_the_global_project_under_their_pins() {
    let p = ir_mint::project(&fixture(), &tags())
        .unwrap_or_else(|e| panic!("the committed fixtures must project: {e}"));
    let (masked, _) =
        ir_mint::mask_text_unwitnessed(&core_a()).expect("reader A's module must mask");
    assert_eq!(
        canon(&p.core),
        canon(&masked),
        "projecting under the pins must produce reader A's committed module, modulo the one \
         slot the emitted text cannot witness (the root's switch flag)"
    );
    assert_eq!(p.interfaces.len(), 2, "one interface per body");
    assert_eq!(p.interfaces[0].function_name, "level::Level::is_zero");
    assert_eq!(
        p.interfaces[1].function_name,
        "<level::LevelArc as std::ops::Deref>::deref"
    );
    let deref = &p.interfaces[1];
    assert_eq!(deref.functy, 22, "the deref's OWN signature index");
    assert_ne!(
        deref.functy, p.interfaces[0].functy,
        "…and it is not the root's"
    );
    assert_eq!(
        deref
            .params
            .iter()
            .map(|s| s.ty.as_str())
            .collect::<Vec<_>>(),
        ["ptr"],
        "one by-reference receiver"
    );
    assert!(
        deref.block_params.is_empty() && deref.aligns.is_empty(),
        "the deref is ONE block with no join, and it performs no load and no store — measured, \
         not assumed: the `expect` message is reached by `globaladdr`, never read"
    );
    // The observed function lanes. The root witnesses itself and the deref; the
    // deref witnesses itself and the TWO DECLARATIONS it calls — which is the
    // fact that makes this chain Phase A rather than a wider `ir_lz`.
    assert_eq!(p.bodies[0].funcs.len(), 2, "root: self plus the deref");
    assert_eq!(
        p.bodies[1].funcs.len(),
        3,
        "deref: self plus `as_deref` and `expect`, both DECLARATIONS"
    );
    assert_eq!(
        p.bodies[1].globals,
        vec![1135],
        "…and the one global it addresses"
    );
}

/// The pins BITE — on the body's header, on the fat-pointer kind, and on all
/// three fields of the global that `IRGlobal.mk` has no slot for.
#[test]
fn m10_the_interface_pins_bite() {
    let t = tags();
    for (from, to, slot) in [
        ("(functy.22)", "(functy.23)", "signature index"),
        (
            "fatptr<str>",
            "fatptr<slice ty.0>",
            "fat pointer kind `slice ty.0`",
        ),
        ("@global.1135", "@global.9999", "addresses `@global.9999`"),
        ("type ty.0 = u8", "type ty.0 = i8", "global type"),
        ("[ty.0 x 34]", "[ty.0 x 33]", "declares 33 element(s)"),
        ("global internal @", "global @", "global linkage"),
    ] {
        let mutated = fixture().replace(from, to);
        assert_ne!(mutated, fixture(), "the mutation must bite: {from}");
        let e = ir_mint::project(&mutated, &t)
            .map(|_| ())
            .err()
            .unwrap_or_else(|| panic!("`{from}` -> `{to}` must be REFUSED, never accepted"));
        assert!(
            format!("{e}").contains(slot),
            "`{from}` -> `{to}`: the refusal must name the drifted slot ({slot}): {e}"
        );
    }
    // The CONTENT of the global is NOT interface — it is in the module, so a
    // changed byte is not refused and MOVES THE CORE DIGEST instead. That is
    // the line this lane draws: what the module can hold is compared as the
    // module, what it cannot hold is pinned in the table.
    let bytes = fixture().replace("const u64 34", "const u64 33");
    assert_ne!(bytes, fixture(), "the mutation must bite");
    let moved = ir_mint::project(&bytes, &t).expect("a metadata length is CONTENT, not interface");
    assert_ne!(
        ir_mint::digest(&canon(&moved.core)),
        ir_mint::digest(ir_mint::IR_LZC_CORE),
        "…and content the module holds must move its digest rather than pass unnoticed"
    );
}
