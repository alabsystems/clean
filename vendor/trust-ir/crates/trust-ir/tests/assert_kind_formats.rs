// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Plan item P (faithful panics, wire v52): the FORMAT half of
// `Inst::Assert { cond, kind }`. The binary codec's tag 29 / tag 63 split is
// pinned in `src/binary.rs` (`assert_kind_*` tests) and the panic outcome in
// `src/interpret.rs` (`assert_panic_kind_tests`); this file pins what the other
// transports do with the kind:
//
//   * text: `assert %c` is `Unspecified`, `assert %c, KIND` every other kind
//     (`overflow OP`, `div_by_zero`, `rem_by_zero`, `bounds_check %i, %n`,
//     `misaligned_ptr %r, %f`, `null_ptr`); the parser reads each back, refuses
//     an unknown kind or op, and never accepts a spelled `unspecified`;
//   * JSON / MessagePack: serde SKIPS an `Unspecified` kind, so a kindless
//     assert keeps its historical bytes and an old document without `kind`
//     decodes as `Unspecified`;
//   * canonicalization renumbers a kind's operands with the rest of the body;
//   * the semantic diff sees the kind as identity.

#![cfg(all(
    feature = "binary",
    feature = "diff",
    feature = "fmt",
    feature = "parser",
    feature = "serde"
))]

use trust_ir::{
    AssertKind, AssertOverflowOp, Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode,
    Module, Ty, ValueId,
};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

/// Every kind, operands over the params `%a` / `%b` given.
fn kinds(a: ValueId, b: ValueId) -> Vec<AssertKind> {
    let mut kinds = vec![AssertKind::Unspecified];
    kinds.extend(AssertOverflowOp::ALL.map(AssertKind::Overflow));
    kinds.extend([
        AssertKind::DivByZero,
        AssertKind::RemByZero,
        AssertKind::BoundsCheck { index: a, len: b },
        AssertKind::MisalignedPtr {
            required: b,
            found: a,
        },
        AssertKind::NullPtr,
    ]);
    kinds
}

/// `check(c: bool, a: usize, b: usize)` with the params numbered `ids`, one
/// assert of `c` per kind in `kinds`, then return.
fn module(ids: [u32; 3], kinds: &[AssertKind]) -> Module {
    let mut m = Module::new("assert_kind_formats");
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Bool, Ty::Usize, Ty::Usize],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "check", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((v(ids[0]), Ty::Bool));
    b.params.push((v(ids[1]), Ty::Usize));
    b.params.push((v(ids[2]), Ty::Usize));
    for kind in kinds {
        b.body.push(InstrNode::new(Inst::Assert {
            cond: v(ids[0]),
            kind: *kind,
            site: None,
        }));
    }
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    m.functions.push(f);
    m
}

fn dense() -> Module {
    module([0, 1, 2], &kinds(v(1), v(2)))
}

#[test]
fn text_round_trips_every_kind_and_is_idempotent() {
    let m = dense();
    let text = trust_ir::format::canonical_checked(&m).expect("text carries every kind");
    for spelling in [
        "assert %0\n",
        "assert %0, overflow add",
        "assert %0, overflow neg",
        "assert %0, div_by_zero",
        "assert %0, rem_by_zero",
        "assert %0, bounds_check %1, %2",
        "assert %0, misaligned_ptr %2, %1",
        "assert %0, null_ptr",
    ] {
        assert!(text.contains(spelling), "missing `{spelling}`: {text}");
    }
    assert!(
        !text.contains("unspecified"),
        "the kindless spelling is the only spelling of Unspecified: {text}"
    );
    let parsed = trust_ir::parser::parse_module(&text).expect("the parser reads it back");
    assert_eq!(
        parsed.functions[0].blocks[0].body,
        m.functions[0].blocks[0].body
    );
    assert_eq!(trust_ir::format::canonical(&parsed), text, "idempotent");
    assert!(trust_ir::diff::diff(&m, &parsed).is_empty());
}

/// The negative twins of the text round trip: an unknown kind, an unknown
/// overflow op, a spelled `unspecified` and a bounds check missing its
/// second operand are all refused.
#[test]
fn the_parser_refuses_a_malformed_kind() {
    let text = trust_ir::format::canonical(&dense());
    for (from, to) in [
        ("assert %0, div_by_zero", "assert %0, div_by_one"),
        ("assert %0, overflow add", "assert %0, overflow pow"),
        ("assert %0, null_ptr", "assert %0, unspecified"),
        (
            "assert %0, bounds_check %1, %2",
            "assert %0, bounds_check %1",
        ),
    ] {
        let broken = text.replacen(from, to, 1);
        assert_ne!(broken, text, "`{from}` is in the text");
        assert!(
            trust_ir::parser::parse_module(&broken).is_err(),
            "`{to}` must not parse"
        );
    }
}

#[test]
fn json_and_msgpack_round_trip_every_kind() {
    let m = dense();
    let json = serde_json::to_string(&m).expect("json");
    let back: Module = serde_json::from_str(&json).expect("json decode");
    assert_eq!(back, m);
    let mp = rmp_serde::to_vec(&m).expect("msgpack");
    let back: Module = rmp_serde::from_slice(&mp).expect("msgpack decode");
    assert_eq!(back, m);
}

/// The READING half (plan item P, wire v52; kept by amendment P): a document
/// written without a `kind` — every older producer's `{"Assert":{"cond":N}}`
/// — still decodes, as `Unspecified` with no site, in JSON and in
/// positional MessagePack (a one-element array).
#[test]
fn serde_reads_kindless_documents_as_unspecified() {
    let old: Inst = serde_json::from_str(r#"{"Assert":{"cond":4}}"#).expect("old json");
    assert_eq!(
        old,
        Inst::Assert {
            cond: v(4),
            kind: AssertKind::Unspecified,
            site: None,
        }
    );
    // A pre-v54 MessagePack assert, `{"Assert": [7]}` with the kind skipped:
    // fixmap(1), fixstr "Assert", fixarray(1), positive fixint 7.
    let mut mp = vec![0x81, 0xa6];
    mp.extend_from_slice(b"Assert");
    mp.extend_from_slice(&[0x91, 0x07]);
    let back: Inst = rmp_serde::from_slice(&mp).expect("old msgpack decode");
    assert_eq!(
        back,
        Inst::Assert {
            cond: v(7),
            kind: AssertKind::Unspecified,
            site: None,
        }
    );
}

/// The EMITTING half, rewritten by amendment P (wire v54): serde now ALWAYS
/// emits `kind` (an `Unspecified` one included), because `site` became the
/// sole trailing skipped field positional MessagePack tolerates; an absent
/// site is skipped, so a siteless kinded assert keeps its v52 JSON.
#[test]
fn serde_always_emits_the_kind_and_skips_an_absent_site() {
    let unspecified = Inst::Assert {
        cond: v(0),
        kind: AssertKind::Unspecified,
        site: None,
    };
    assert_eq!(
        serde_json::to_value(&unspecified).expect("json"),
        serde_json::json!({ "Assert": { "cond": 0, "kind": "Unspecified" } })
    );
    let kinded = Inst::Assert {
        cond: v(0),
        kind: AssertKind::BoundsCheck {
            index: v(1),
            len: v(2),
        },
        site: None,
    };
    assert_eq!(
        serde_json::to_value(&kinded).expect("json"),
        serde_json::json!({ "Assert": { "cond": 0, "kind": { "BoundsCheck": { "index": 1, "len": 2 } } } })
    );
    // MessagePack: a two-element array now; it round-trips.
    let mp = rmp_serde::to_vec(&unspecified).expect("msgpack");
    let back: Inst = rmp_serde::from_slice(&mp).expect("msgpack decode");
    assert_eq!(back, unspecified);
}

/// Canonicalization renumbers a kind's operands WITH the body: params
/// numbered 10/20/30 become 0/1/2 everywhere, the bounds-check and
/// misaligned-pointer operands included (`mem2reg::rewrite_node`).
#[test]
fn canonicalization_renumbers_kind_operands() {
    let sparse = module([10, 20, 30], &kinds(v(20), v(30)));
    let text = trust_ir::format::canonical(&sparse);
    assert_eq!(text, trust_ir::format::canonical(&dense()));
    assert!(text.contains("assert %0, bounds_check %1, %2"), "{text}");
    // The binary codec's canonical projection agrees: the same bytes as the
    // dense module's, so the kind operands were mapped with their definitions
    // (`FunctionCanonicalPlan::map_value` in `write_assert_kind`).
    let canonical = |m: &Module| {
        let options = trust_ir::binary::ModuleBinaryOptions {
            body: trust_ir::binary::ModuleBinaryBody::Canonical,
            ..Default::default()
        };
        trust_ir::binary::ProjectedModuleBinaryPlan::try_new(m, options)
            .expect("a kinded module projects canonically")
            .to_vec()
            .expect("to_vec: test fixture")
    };
    assert_eq!(canonical(&sparse), canonical(&dense()));
    // Control: the RAW bodies differ (only the numbering does).
    assert_ne!(
        trust_ir::binary::serialize_module(&sparse).expect("serialize_module: test fixture"),
        trust_ir::binary::serialize_module(&dense()).expect("serialize_module: test fixture")
    );
}

/// The kind is identity to the semantic diff: two asserts of one condition
/// differing only in kind (or only in a kind operand) differ.
#[test]
fn diff_treats_the_kind_as_identity() {
    let base = module([0, 1, 2], &[AssertKind::DivByZero]);
    for other in [
        AssertKind::Unspecified,
        AssertKind::RemByZero,
        AssertKind::Overflow(AssertOverflowOp::Div),
    ] {
        assert!(
            !trust_ir::diff::diff(&base, &module([0, 1, 2], &[other])).is_empty(),
            "DivByZero vs {other:?}"
        );
    }
    let a = module(
        [0, 1, 2],
        &[AssertKind::BoundsCheck {
            index: v(1),
            len: v(2),
        }],
    );
    let swapped = module(
        [0, 1, 2],
        &[AssertKind::BoundsCheck {
            index: v(2),
            len: v(1),
        }],
    );
    assert!(!trust_ir::diff::diff(&a, &swapped).is_empty(), "operands");
    assert!(trust_ir::diff::diff(&a, &a.clone()).is_empty(), "same");
}

/// A kind's operands are ordinary SSA operands (dominance, use counting,
/// renaming all see them), visited after the condition.
#[test]
fn kind_operands_are_value_operands() {
    let inst = Inst::Assert {
        cond: v(7),
        kind: AssertKind::MisalignedPtr {
            required: v(8),
            found: v(9),
        },
        site: None,
    };
    let mut seen = Vec::new();
    inst.visit_value_operands(|id| seen.push(id));
    assert_eq!(seen, vec![v(7), v(8), v(9)]);
    assert!(inst.uses_value(v(9)));
    let mut seen = Vec::new();
    Inst::Assert {
        cond: v(7),
        kind: AssertKind::NullPtr,
        site: None,
    }
    .visit_value_operands(|id| seen.push(id));
    assert_eq!(seen, vec![v(7)]);
}

/// The lowering surface: every kind but `Unspecified` names the `core` lang
/// item a faithful lowering calls; `Unspecified` names none.
#[test]
fn every_kind_but_unspecified_names_its_rust_panic_entry_point() {
    for kind in kinds(v(1), v(2)) {
        match kind.rust_panic_lang_item() {
            None => assert_eq!(kind, AssertKind::Unspecified),
            Some(item) => assert!(
                item.starts_with("panic_"),
                "{kind:?} names `{item}`, not a panic entry point"
            ),
        }
    }
    assert_eq!(
        AssertKind::BoundsCheck {
            index: v(1),
            len: v(2)
        }
        .rust_panic_lang_item(),
        Some("panic_bounds_check")
    );
}
