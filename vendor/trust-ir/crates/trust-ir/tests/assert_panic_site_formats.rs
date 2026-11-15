// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Amendment P (wire v54, `docs/SPEC_RATIFICATIONS.md` §19.1): the FORMAT half
// of the panic site. The binary codec's tag 66 / 67 split is pinned in
// `src/binary.rs` (the `panic_site_*` / `*_panic_site*` tests) and the panic
// outcome in `src/interpret.rs` (`panic_site_tests`); this file pins what the
// other transports and the generic walkers do with a site:
//
//   * text: `, panic @func.E at @global.G | %V` after the kind clause, and
//     `assert_invoke %c[, KIND], panic .. to bbN(..) unwind bbM`;
//   * JSON / MessagePack: serde now ALWAYS emits `kind` and skips an absent
//     `site` (its sole trailing skipped field); documents written before the
//     site existed, kind skipped or not, still decode;
//   * a `Value` location is an SSA operand; the semantic diff sees the site
//     as identity; the dependency census reaches the entry and the location
//     global; `AssertInvoke`'s successors and unwind edge are visited.

#![cfg(all(
    feature = "binary",
    feature = "diff",
    feature = "fmt",
    feature = "parser",
    feature = "serde"
))]

use trust_ir::value::GlobalId;
use trust_ir::{
    AssertKind, Block, BlockId, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode,
    Linkage, Module, PanicLocation, PanicSite, Ty, ValueId,
};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn site(entry: u32, location: PanicLocation) -> PanicSite {
    PanicSite {
        entry: FuncId::new(entry),
        location,
    }
}

fn global(name: &str) -> Global {
    Global {
        name: name.to_string(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(7)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}

/// The sited spellings: Unspecified + static, bounds check + static,
/// overflow + run-time location.
fn sited(ids: [u32; 4]) -> Vec<Inst> {
    let [c, i, n, p] = ids.map(v);
    vec![
        Inst::Assert {
            cond: c,
            kind: AssertKind::Unspecified,
            site: Some(site(2, PanicLocation::Global(GlobalId::new(1)))),
        },
        Inst::Assert {
            cond: c,
            kind: AssertKind::BoundsCheck { index: i, len: n },
            site: Some(site(1, PanicLocation::Global(GlobalId::new(0)))),
        },
        Inst::Assert {
            cond: c,
            kind: AssertKind::Overflow(trust_ir::AssertOverflowOp::Add),
            site: Some(site(2, PanicLocation::Value(p))),
        },
    ]
}

/// `check(c: bool, i: usize, n: usize, p: ptr)` (params numbered `ids`):
/// the sited asserts, then `assert_invoke %c, div_by_zero, panic @func.2 at
/// @global.0 to bb1(%i) unwind bb2`; bb1 returns, bb2 is a cleanup pad.
/// Function 1 is `panic_bounds_check(usize, usize, ptr)`, function 2
/// `panic_loc(ptr)`; globals 0 and 1 are location records.
fn module(ids: [u32; 4]) -> Module {
    let mut m = Module::new("assert_panic_site_formats");
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Bool, Ty::Usize, Ty::Usize, Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let bounds_ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Usize, Ty::Usize, Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let loc_ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "check", ft, BlockId::new(0));
    let mut b0 = Block::new(BlockId::new(0));
    b0.params.push((v(ids[0]), Ty::Bool));
    b0.params.push((v(ids[1]), Ty::Usize));
    b0.params.push((v(ids[2]), Ty::Usize));
    b0.params.push((v(ids[3]), Ty::Ptr));
    for inst in sited(ids) {
        b0.body.push(InstrNode::new(inst));
    }
    b0.body.push(InstrNode::new(Inst::AssertInvoke {
        cond: v(ids[0]),
        kind: AssertKind::DivByZero,
        site: site(2, PanicLocation::Global(GlobalId::new(0))),
        normal_dest: BlockId::new(1),
        normal_args: vec![v(ids[1])],
        unwind_dest: BlockId::new(2),
    }));
    // Dense after the entry's parameters, as the text format numbers them.
    let next = ids[3];
    let mut b1 = Block::new(BlockId::new(1));
    b1.params.push((v(next + 1), Ty::Usize));
    b1.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    let mut b2 = Block::new(BlockId::new(2));
    b2.body.push(
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results([v(next + 2), v(next + 3)]),
    );
    b2.body
        .push(InstrNode::new(Inst::Resume { exn: v(next + 2) }));
    f.blocks.extend([b0, b1, b2]);
    m.functions.push(f);
    m.functions.push(Function::new(
        FuncId::new(1),
        "panic_bounds_check",
        bounds_ft,
        BlockId::new(0),
    ));
    m.functions.push(Function::new(
        FuncId::new(2),
        "panic_loc",
        loc_ft,
        BlockId::new(0),
    ));
    m.globals.push(global("loc0"));
    m.globals.push(global("loc1"));
    m
}

fn dense() -> Module {
    module([0, 1, 2, 3])
}

#[test]
fn text_round_trips_every_site_and_assert_invoke() {
    let m = dense();
    let text = trust_ir::format::canonical_checked(&m).expect("text carries every site");
    for spelling in [
        "assert %0, panic @func.2 at @global.1\n",
        "assert %0, bounds_check %1, %2, panic @func.1 at @global.0\n",
        "assert %0, overflow add, panic @func.2 at %3\n",
        "assert_invoke %0, div_by_zero, panic @func.2 at @global.0 to bb1(%1) unwind bb2",
    ] {
        assert!(text.contains(spelling), "missing `{spelling}`: {text}");
    }
    let parsed = trust_ir::parser::parse_module(&text).expect("the parser reads it back");
    assert_eq!(parsed.functions[0].blocks, m.functions[0].blocks);
    assert_eq!(trust_ir::format::canonical(&parsed), text, "idempotent");
    assert!(trust_ir::diff::diff(&m, &parsed).is_empty());
}

/// The negative twins: an `assert_invoke` without its panic clause, a site
/// without `at`, a site naming no function, and a clause after the site.
#[test]
fn the_parser_refuses_a_malformed_site() {
    let text = trust_ir::format::canonical(&dense());
    for (from, to) in [
        (
            "assert_invoke %0, div_by_zero, panic @func.2 at @global.0 to",
            "assert_invoke %0, div_by_zero to",
        ),
        (
            "assert %0, panic @func.2 at @global.1",
            "assert %0, panic @func.2 @global.1",
        ),
        (
            "assert %0, panic @func.2 at @global.1",
            "assert %0, panic @global.2 at @global.1",
        ),
        (
            "assert %0, bounds_check %1, %2, panic",
            "assert %0, bounds_check %1, %2, null_ptr, panic",
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
fn json_and_msgpack_round_trip_every_site_and_assert_invoke() {
    let m = dense();
    let json = serde_json::to_string(&m).expect("json");
    let back: Module = serde_json::from_str(&json).expect("json decode");
    assert_eq!(back, m);
    let mp = rmp_serde::to_vec(&m).expect("msgpack");
    let back: Module = rmp_serde::from_slice(&mp).expect("msgpack decode");
    assert_eq!(back, m);
}

/// Serde ALWAYS emits `kind` now and skips an absent site; the site is
/// `{"entry": E, "location": {"Global": G} | {"Value": V}}`. A document
/// written before the site existed — the v52 form with the kind skipped, or
/// with it present — still decodes, siteless.
#[test]
fn serde_always_emits_the_kind_and_reads_pre_site_documents() {
    let sited = Inst::Assert {
        cond: v(0),
        kind: AssertKind::Unspecified,
        site: Some(site(3, PanicLocation::Value(v(4)))),
    };
    assert_eq!(
        serde_json::to_value(&sited).expect("json"),
        serde_json::json!({ "Assert": { "cond": 0, "kind": "Unspecified",
            "site": { "entry": 3, "location": { "Value": 4 } } } })
    );
    let siteless = Inst::Assert {
        cond: v(0),
        kind: AssertKind::NullPtr,
        site: None,
    };
    assert_eq!(
        serde_json::to_value(&siteless).expect("json"),
        serde_json::json!({ "Assert": { "cond": 0, "kind": "NullPtr" } })
    );
    for old in [
        r#"{"Assert":{"cond":4}}"#,
        r#"{"Assert":{"cond":4,"kind":"Unspecified"}}"#,
    ] {
        let decoded: Inst = serde_json::from_str(old).expect("old json");
        assert_eq!(
            decoded,
            Inst::Assert {
                cond: v(4),
                kind: AssertKind::Unspecified,
                site: None,
            },
            "{old}"
        );
    }
    for inst in [sited, siteless] {
        let mp = rmp_serde::to_vec(&inst).expect("msgpack");
        assert_eq!(rmp_serde::from_slice::<Inst>(&mp).expect("decode"), inst);
    }
}

/// Every MessagePack golden written BEFORE the site existed still decodes:
/// the pinned pre-site copies of the assert-bearing conformance goldens
/// (`fixtures/compat/pre_panic_site_*`), whose asserts were written with the
/// kind skipped or present and no site. This guards the positional layout
/// (`site` is the sole trailing skipped field) and the variant table (an
/// `AssertInvoke` added anywhere in `Inst` never shifts a name-keyed
/// variant).
#[test]
fn pre_site_msgpack_goldens_still_decode() {
    let compat = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../trust-ir-conformance/tests/fixtures/compat");
    let mut decoded_asserts = 0usize;
    for name in [
        "pre_panic_site_assert_kind.msgpack",
        "pre_panic_site_inst_control.msgpack",
    ] {
        let bytes = std::fs::read(compat.join(name)).expect("pinned pre-site golden");
        let module: Module = rmp_serde::from_slice(&bytes).expect("a pre-site golden decodes");
        for node in module
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.body)
        {
            if let Inst::Assert { site, .. } = &node.inst {
                assert_eq!(*site, None, "{name}: a pre-site assert decodes siteless");
                decoded_asserts += 1;
            }
        }
    }
    assert!(decoded_asserts > 1, "the pinned goldens carry asserts");
    // The JSON twin of the kind golden decodes too.
    let json = std::fs::read_to_string(compat.join("pre_panic_site_assert_kind.json"))
        .expect("pinned pre-site json");
    let _: Module = serde_json::from_str(&json).expect("a pre-site JSON golden decodes");
}

/// A run-time location is an ordinary SSA operand, visited after the
/// condition and the kind's operands; `AssertInvoke` then visits its
/// normal-edge arguments. A static location is not a value.
#[test]
fn site_location_values_are_value_operands() {
    let inst = Inst::Assert {
        cond: v(7),
        kind: AssertKind::BoundsCheck {
            index: v(8),
            len: v(9),
        },
        site: Some(site(1, PanicLocation::Value(v(10)))),
    };
    let mut seen = Vec::new();
    inst.visit_value_operands(|id| seen.push(id));
    assert_eq!(seen, vec![v(7), v(8), v(9), v(10)]);
    assert!(inst.uses_value(v(10)));
    let invoke = Inst::AssertInvoke {
        cond: v(7),
        kind: AssertKind::Unspecified,
        site: site(1, PanicLocation::Value(v(10))),
        normal_dest: BlockId::new(1),
        normal_args: vec![v(11)],
        unwind_dest: BlockId::new(2),
    };
    let mut seen = Vec::new();
    invoke.visit_value_operands(|id| seen.push(id));
    assert_eq!(seen, vec![v(7), v(10), v(11)]);
    let mut seen = Vec::new();
    Inst::Assert {
        cond: v(7),
        kind: AssertKind::Unspecified,
        site: Some(site(1, PanicLocation::Global(GlobalId::new(0)))),
    }
    .visit_value_operands(|id| seen.push(id));
    assert_eq!(seen, vec![v(7)]);
    // Canonicalization renumbers the location with the body.
    let sparse = module([10, 20, 30, 40]);
    assert_eq!(
        trust_ir::format::canonical(&sparse),
        trust_ir::format::canonical(&dense())
    );
}

/// The site is identity to the semantic diff: retargeting the entry, moving
/// the location to another global, or dropping the site is a body change.
#[test]
fn diff_treats_the_site_as_identity() {
    let base = dense();
    let mut retargeted = base.clone();
    let mut moved = base.clone();
    let mut dropped = base.clone();
    if let Inst::Assert { site: Some(s), .. } = &mut retargeted.functions[0].blocks[0].body[0].inst
    {
        s.entry = FuncId::new(1);
    }
    if let Inst::Assert { site: Some(s), .. } = &mut moved.functions[0].blocks[0].body[0].inst {
        s.location = PanicLocation::Global(GlobalId::new(0));
    }
    if let Inst::Assert { site: s, .. } = &mut dropped.functions[0].blocks[0].body[0].inst {
        *s = None;
    }
    for (what, other) in [
        ("entry", retargeted),
        ("location", moved),
        ("dropped", dropped),
    ] {
        assert!(
            !trust_ir::diff::diff(&base, &other).is_empty(),
            "{what} must be a difference"
        );
    }
    assert!(trust_ir::diff::diff(&base, &base.clone()).is_empty());
}

/// The dependency census reaches a site's entry and its location global, so
/// neither is a dead declaration.
#[test]
fn function_dependencies_reach_the_entry_and_the_location_global() {
    use trust_ir::function_dependencies::{DependencyNode, inspect_function_dependencies};
    let m = dense();
    let census = inspect_function_dependencies(&m, FuncId::new(0));
    let reached = census.nodes();
    for node in [
        DependencyNode::Function(FuncId::new(1)),
        DependencyNode::Function(FuncId::new(2)),
        DependencyNode::Global(GlobalId::new(0)),
        DependencyNode::Global(GlobalId::new(1)),
    ] {
        assert!(
            reached.contains(&node),
            "{node:?} must be reached: {reached:?}"
        );
    }
}

/// `AssertInvoke` is a terminator whose successors are its normal and
/// unwind destinations, and its unwind destination is an unwind edge.
#[test]
fn assert_invoke_successors_and_unwind_edge_are_visited() {
    let m = dense();
    let f = &m.functions[0];
    let terminator = f.blocks[0].body.last().expect("a terminator");
    assert!(terminator.inst.is_terminator());
    assert!(terminator.inst.has_side_effects());
    assert!(terminator.inst.panic_site().is_some());
    // The dominator tree sees both edges: bb1 and bb2 are reachable.
    let dominators = trust_ir::analysis::DominatorTree::new(f);
    for block in [BlockId::new(1), BlockId::new(2)] {
        assert!(
            dominators.is_reachable(block),
            "bb{} reachable",
            block.index()
        );
    }
}
