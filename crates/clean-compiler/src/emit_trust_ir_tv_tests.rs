// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the backend translation-validation minter: the corpus decl is
//! kernel-certified end-to-end, a deliberate post-emit miscompile is REFUSED
//! (the whole point — a real wrong-code detector), and out-of-fragment decls
//! are silently skipped (no obligation, never a fake cert).
//!
//! NOTE: these tests assert the MINT side (obligation + certificate shape,
//! kernel accept/refuse). The independent CONSUMER-side acceptance — a minted
//! module validating `Certified` under `trust_ir_build::validate_module` —
//! lives in trust-ir's `clean-tv-anchor` test suite, which re-derives the
//! denotation in its own TCB and re-runs the kernel; the sibling trust-ir
//! checkout must carry that anchor before `certify_translation` is switched
//! on in a shipping pipeline (fail-closed direction either way: an older
//! validator REJECTS the unknown anchor rather than faith-accepting it).

use super::*;
use crate::emit_trust_ir::emit_trust_ir;
use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::{BinderInfo, Name as KName};
use trust_ir::inst::{BinOp, Inst};

/// The corpus IRDecl: `fn tv_demo(x: u32) -> u32 { (x + 7) * 3 }`, arithmetic
/// spelled as Applys to the fixed-width primitives (the native-BinOp path).
fn tv_demo_decl() -> IRDecl {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::UInt32,
        value: IRExpr::Lit(IRLiteral::UInt32(7)),
        rest: Box::new(IRBody::VDecl {
            var: VarId(2),
            ty: IRType::UInt32,
            value: IRExpr::Apply {
                fn_id: FnId(KName::from_string("UInt32.add")),
                args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(3),
                ty: IRType::UInt32,
                value: IRExpr::Lit(IRLiteral::UInt32(3)),
                rest: Box::new(IRBody::VDecl {
                    var: VarId(4),
                    ty: IRType::UInt32,
                    value: IRExpr::Apply {
                        fn_id: FnId(KName::from_string("UInt32.mul")),
                        args: vec![IRArg::Var(VarId(2)), IRArg::Var(VarId(3))],
                    },
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(4)))),
                }),
            }),
        }),
    };
    IRDecl {
        name: KName::from_string("tv_demo"),
        params: vec![(VarId(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body,
    }
}

/// The corpus decl's ORIGINAL kernel definition:
/// `fun (x : UInt32) => UInt32.mul (UInt32.add x (UInt32.ofNat 7)) (UInt32.ofNat 3)`.
fn tv_demo_original() -> Expr {
    let of_nat = |k: u64| Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(k));
    let add = Expr::apps(Expr::const_str("UInt32.add"), [Expr::bvar(0), of_nat(7)]);
    let mul = Expr::apps(Expr::const_str("UInt32.mul"), [add, of_nat(3)]);
    Expr::lam(BinderInfo::Default, Expr::const_str("UInt32"), mul)
}

/// E2E MINT: emit the corpus decl, certify it against its original kernel
/// definition, and check the attached obligation + certificate shape in full.
#[test]
fn test_mint_certifies_the_corpus_decl_end_to_end() {
    let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("corpus decl lowers");
    let originals = vec![("tv_demo".to_string(), tv_demo_original())];

    let report = certify_backend_translation(&mut module, &originals);
    assert_eq!(
        report.certified,
        vec!["tv_demo".to_string()],
        "the corpus decl must be kernel-certified, got: {report:?}"
    );
    assert!(
        report.refused.is_empty(),
        "no refusals expected: {report:?}"
    );

    // The obligation: TranslationValidation, Certified, function-scoped.
    let [obl] = module.proof_obligations.as_slice() else {
        panic!(
            "exactly one obligation expected, got {:?}",
            module.proof_obligations
        );
    };
    assert_eq!(obl.kind, ObligationKind::TranslationValidation);
    assert_eq!(obl.status, ProofStatus::Certified);
    assert_eq!(obl.function, Some(module.functions[0].id));

    // The certificate: CleanCic, lineage-bound, decodable payload, directive
    // citing the re-derivable theorem under the TV anchor, FOUNDATIONAL
    // (empty) allowed-axioms.
    let [cert] = module.proof_certificates.as_slice() else {
        panic!("exactly one certificate expected");
    };
    assert_eq!(cert.obligation, obl.id);
    let ProofEvidence::CleanCic {
        term,
        context,
        lineage,
        kernel_recheck: Some(directive),
    } = &cert.evidence
    else {
        panic!("evidence must be CleanCic with a kernel-recheck directive");
    };
    assert_eq!(*lineage, clean_cic_lineage_digest(obl), "lineage-bound");
    assert_eq!(directive.anchor, clean_reflect::CLEAN_BACKEND_TV_ANCHOR);
    assert_eq!(
        directive.theorems,
        vec!["CleanTV.tv_demo.denotes".to_string()]
    );
    assert!(directive.allowed_axioms.is_empty(), "FOUNDATIONAL floor");
    assert_eq!(directive.module, "CleanCompiler.BackendTV");
    // Payload decodes back to kernel Exprs (bincode-1 wire format).
    let _proof: Expr = bincode::deserialize(term).expect("term decodes to an Expr");
    let comparand: Expr = bincode::deserialize(context).expect("context decodes to an Expr");
    let rhs = clean_reflect::denote_source(
        &tv_demo_original(),
        32,
        &[],
        &clean_reflect::RecordVocab::empty(),
    )
    .expect("in-fragment");
    let expected_lambda = Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), rhs.body);
    assert_eq!(
        comparand, expected_lambda,
        "context carries the denoted comparand"
    );
}

/// THE DELIBERATE MISCOMPILE: patch the emitted body post-emit (Add -> Sub)
/// and the mint must REFUSE — the kernel finds `(x - 7) * 3` not
/// definitionally equal to the source's `(x + 7) * 3`. No obligation is
/// attached; the pipeline wiring turns this refusal into a hard error.
#[test]
fn test_mint_refuses_deliberate_miscompile_add_to_sub() {
    let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("corpus decl lowers");

    // Post-emit tamper: the Add BinOp becomes Sub (a genuine wrong-code bug).
    let body = &mut module.functions[0].blocks[0].body;
    let add_node = body
        .iter_mut()
        .find(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Add, .. }))
        .expect("fixture has the Add");
    let Inst::BinOp { op, .. } = &mut add_node.inst else {
        unreachable!()
    };
    *op = BinOp::Sub;

    let originals = vec![("tv_demo".to_string(), tv_demo_original())];
    let report = certify_backend_translation(&mut module, &originals);
    assert!(
        report.certified.is_empty(),
        "a miscompiled decl must NOT be certified: {report:?}"
    );
    assert!(
        report
            .refused
            .iter()
            .any(|(n, r)| n == "tv_demo" && r.contains("REFUSED")),
        "the kernel must REFUSE the miscompiled equation, got: {report:?}"
    );
    assert!(
        module.proof_obligations.is_empty() && module.proof_certificates.is_empty(),
        "a refusal must attach NO obligation and NO certificate"
    );
}

/// `helper(y) = y` and `caller(x) = helper(x) + 1`, emitted for real. The
/// caller's Call becomes a Fragment-3b pinned callee, so both live IN the
/// fragment; whether the caller certifies depends on the composition.
fn helper_caller_decls() -> (IRDecl, IRDecl) {
    let helper = IRDecl {
        name: KName::from_string("helper"),
        params: vec![(VarId(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let caller = IRDecl {
        name: KName::from_string("caller"),
        params: vec![(VarId(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        // v1 = helper(x); v2 = 1; v3 = UInt32.add(v1, v2); ret v3
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt32,
            value: IRExpr::Apply {
                fn_id: FnId(KName::from_string("helper")),
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::UInt32,
                value: IRExpr::Lit(IRLiteral::UInt32(1)),
                rest: Box::new(IRBody::VDecl {
                    var: VarId(3),
                    ty: IRType::UInt32,
                    value: IRExpr::Apply {
                        fn_id: FnId(KName::from_string("UInt32.add")),
                        args: vec![IRArg::Var(VarId(1)), IRArg::Var(VarId(2))],
                    },
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
                }),
            }),
        },
    };
    (helper, caller)
}

/// `fun (y : UInt32) => y` — helper's source.
fn helper_original() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        Expr::const_str("UInt32"),
        Expr::bvar(0),
    )
}

/// `fun (x : UInt32) => UInt32.add (helper x) (UInt32.ofNat 1)` — caller's source.
fn caller_original() -> Expr {
    let of_nat = |k: u64| Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(k));
    let hx = Expr::app(Expr::const_str("helper"), Expr::bvar(0));
    let add = Expr::apps(Expr::const_str("UInt32.add"), [hx, of_nat(1)]);
    Expr::lam(BinderInfo::Default, Expr::const_str("UInt32"), add)
}

/// E2E MINT (calls / Fragment-3b): helper and caller BOTH certify; the caller's
/// obligation carries the parametric CleanCic cert AND an `InheritedFromCallee`
/// cert grounding it at helper's own certified TV obligation.
#[test]
fn test_mint_certifies_caller_composing_callee() {
    let (helper, caller) = helper_caller_decls();
    let mut module = emit_trust_ir(&[helper, caller]).expect("lowers");
    let originals = vec![
        ("helper".to_string(), helper_original()),
        ("caller".to_string(), caller_original()),
    ];
    let report = certify_backend_translation(&mut module, &originals);
    assert!(
        report.certified.contains(&"helper".to_string())
            && report.certified.contains(&"caller".to_string()),
        "both helper and caller must certify, got: {report:?}"
    );
    assert!(
        report.refused.is_empty(),
        "no refusals expected: {report:?}"
    );

    // helper's and caller's obligations.
    let helper_fid = module
        .functions
        .iter()
        .find(|f| f.name == "helper")
        .unwrap()
        .id;
    let caller_fid = module
        .functions
        .iter()
        .find(|f| f.name == "caller")
        .unwrap()
        .id;
    let helper_obl = module
        .proof_obligations
        .iter()
        .find(|o| o.function == Some(helper_fid))
        .expect("helper TV obligation");
    let caller_obl = module
        .proof_obligations
        .iter()
        .find(|o| o.function == Some(caller_fid))
        .expect("caller TV obligation");

    // The caller carries BOTH a CleanCic (parametric) cert and an
    // InheritedFromCallee cert pointing at helper's obligation.
    let caller_certs: Vec<_> = module
        .proof_certificates
        .iter()
        .filter(|c| c.obligation == caller_obl.id)
        .collect();
    assert!(
        caller_certs
            .iter()
            .any(|c| matches!(c.evidence, ProofEvidence::CleanCic { .. })),
        "caller must carry a parametric CleanCic cert"
    );
    assert!(
        caller_certs.iter().any(|c| matches!(
            &c.evidence,
            ProofEvidence::InheritedFromCallee { callee, obligation }
                if *callee == helper_fid && *obligation == helper_obl.id
        )),
        "caller must inherit helper's TV obligation (compositional grounding), got: {caller_certs:?}"
    );
}

/// FAIL-CLOSED: a caller whose callee is NOT among the originals (so never
/// TV-certified) is SKIPPED — its compositional certificate cannot be grounded.
#[test]
fn test_mint_skips_caller_with_uncertified_callee() {
    let (helper, caller) = helper_caller_decls();
    let mut module = emit_trust_ir(&[helper, caller]).expect("lowers");
    // Only the caller is offered — helper is never certified.
    let originals = vec![("caller".to_string(), caller_original())];
    let report = certify_backend_translation(&mut module, &originals);
    assert!(
        report.certified.is_empty(),
        "caller cannot compose an uncertified callee"
    );
    assert!(
        report.refused.is_empty(),
        "an uncertified callee is a SKIP, not a refusal"
    );
    assert!(
        report
            .skipped
            .iter()
            .any(|(n, r)| n == "caller" && r.contains("callee")),
        "expected an auditable uncertified-callee skip, got: {report:?}"
    );
    assert!(module.proof_obligations.is_empty(), "no obligation on skip");
}

/// THE COMPOSITION MISCOMPILE DETECTOR: patch the caller's `+ 1` to `+ 2`
/// post-emit. The pinned symbol G_helper is identical on both sides, but
/// `(G_helper x) + 2` is not def-eq to the source's `(G_helper x) + 1` — the
/// kernel REFUSES the caller (helper still certifies).
#[test]
fn test_mint_refuses_miscompiled_caller_composition() {
    let (helper, caller) = helper_caller_decls();
    let mut module = emit_trust_ir(&[helper, caller]).expect("lowers");

    // Post-emit tamper: the caller's constant 1 becomes 2.
    let caller_fn = module
        .functions
        .iter_mut()
        .find(|f| f.name == "caller")
        .unwrap();
    let one = caller_fn
        .blocks
        .iter_mut()
        .flat_map(|b| b.body.iter_mut())
        .find(|n| {
            matches!(
                &n.inst,
                Inst::Const {
                    value: trust_ir::constant::Constant::Int(1),
                    ..
                }
            )
        })
        .expect("caller has the const 1");
    if let Inst::Const { value, .. } = &mut one.inst {
        *value = trust_ir::constant::Constant::Int(2);
    }

    let originals = vec![
        ("helper".to_string(), helper_original()),
        ("caller".to_string(), caller_original()),
    ];
    let report = certify_backend_translation(&mut module, &originals);
    assert!(
        report.certified.contains(&"helper".to_string()),
        "helper still certifies: {report:?}"
    );
    assert!(
        !report.certified.contains(&"caller".to_string()),
        "the miscompiled caller must NOT certify: {report:?}"
    );
    assert!(
        report
            .refused
            .iter()
            .any(|(n, r)| n == "caller" && r.contains("REFUSED")),
        "the kernel must REFUSE the miscompiled composition, got: {report:?}"
    );
}

/// Out-of-fragment on the SOURCE side (a `Nat.add` definition — bignum, not
/// the fixed-width fragment): skipped, never re-interpreted.
#[test]
fn test_mint_skips_out_of_fragment_source_definition() {
    let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("lowers");
    let nat_body = Expr::apps(
        Expr::const_str("Nat.add"),
        [Expr::bvar(0), Expr::nat_lit(7)],
    );
    let originals = vec![(
        "tv_demo".to_string(),
        Expr::lam(BinderInfo::Default, Expr::const_str("UInt32"), nat_body),
    )];
    let report = certify_backend_translation(&mut module, &originals);
    assert!(report.certified.is_empty());
    assert!(
        report
            .skipped
            .iter()
            .any(|(n, r)| n == "tv_demo" && r.contains("source side")),
        "expected an auditable source-side skip, got: {report:?}"
    );
    assert!(module.proof_obligations.is_empty(), "no obligation on skip");
}

/// A decl name with no emitted function is skipped with a reason (and the
/// module is untouched).
#[test]
fn test_mint_skips_unknown_function_name() {
    let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("lowers");
    let originals = vec![("no_such_fn".to_string(), tv_demo_original())];
    let report = certify_backend_translation(&mut module, &originals);
    assert!(report.certified.is_empty());
    assert!(
        report
            .skipped
            .iter()
            .any(|(n, r)| n == "no_such_fn" && r.contains("no emitted")),
        "expected a no-such-function skip, got: {report:?}"
    );
}

// --- Fragment-3a (control flow) end-to-end mint ----------------------------

/// A hand-built EMITTED trust-ir module in the Fragment-3a (`CondBr` diamond)
/// shape: `fn cf(x: u32) -> u32 { if x < 10 then x + 1 else x }`. Hand-built
/// because the current `emit_trust_ir` lowers a Bool `Case` to a `Switch`-on-tag
/// (with the comparison a runtime call), NOT the native `ICmp`+`CondBr` shape
/// the Fragment-3a recognizer targets — teaching the real emit path to produce
/// it is tracked as future work. The minter operates on any module, so it
/// certifies this canonical-branch module end-to-end.
fn cf_demo_emitted_module() -> Module {
    use trust_ir::constant::Constant;
    use trust_ir::inst::ICmpOp;
    use trust_ir::ty::Ty;
    use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
    use trust_ir::{Block, FuncTy, Function, InstrNode};

    let mut module = Module::new("cf_demo");
    module.func_types.push(FuncTy {
        params: vec![Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "cf", FuncTyId::new(0), BlockId::new(0));

    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::U32));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(10),
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ult,
            ty: Ty::U32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(InstrNode::new(Inst::CondBr {
        cond: ValueId::new(2),
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    }));

    let mut then_blk = Block::new(BlockId::new(1));
    then_blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(3)),
    );
    then_blk.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(3),
        })
        .with_result(ValueId::new(4)),
    );
    then_blk.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));

    let mut else_blk = Block::new(BlockId::new(2));
    else_blk.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));

    func.blocks.push(entry);
    func.blocks.push(then_blk);
    func.blocks.push(else_blk);
    module.add_function(func);
    module
}

/// `fun (x : UInt32) => cond (UInt32.blt x (UInt32.ofNat 10))
///                          (UInt32.add x (UInt32.ofNat 1)) x`.
fn cf_demo_original() -> Expr {
    let of_nat = |k: u64| Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(k));
    let cond = Expr::apps(Expr::const_str("UInt32.blt"), [Expr::bvar(0), of_nat(10)]);
    let then_e = Expr::apps(Expr::const_str("UInt32.add"), [Expr::bvar(0), of_nat(1)]);
    let ite = Expr::apps(
        Expr::const_str("cond"),
        [Expr::const_str("UInt32"), cond, then_e, Expr::bvar(0)],
    );
    Expr::lam(BinderInfo::Default, Expr::const_str("UInt32"), ite)
}

/// E2E MINT (control flow): the Fragment-3a `CondBr` module is kernel-certified
/// to denote its `if`-expression source.
#[test]
fn test_mint_certifies_control_flow_decl_end_to_end() {
    let mut module = cf_demo_emitted_module();
    let originals = vec![("cf".to_string(), cf_demo_original())];
    let report = certify_backend_translation(&mut module, &originals);
    assert_eq!(
        report.certified,
        vec!["cf".to_string()],
        "the control-flow decl must be kernel-certified, got: {report:?}"
    );
    assert!(
        report.refused.is_empty(),
        "no refusals expected: {report:?}"
    );
    let [obl] = module.proof_obligations.as_slice() else {
        panic!("exactly one obligation expected");
    };
    assert_eq!(obl.kind, ObligationKind::TranslationValidation);
    assert_eq!(obl.status, ProofStatus::Certified);
    assert_eq!(obl.function, Some(module.functions[0].id));
}

/// THE DELIBERATE MISCOMPILE (control flow): swap the branch arms post-emit and
/// the mint must REFUSE — `Bool.rec … x (x+1)` is not def-eq to the source's
/// `Bool.rec … (x+1) x` over the open scrutinee.
#[test]
fn test_mint_refuses_swapped_branch_arms() {
    let mut module = cf_demo_emitted_module();
    let Inst::CondBr {
        then_target,
        else_target,
        ..
    } = &mut module.functions[0].blocks[0].body[2].inst
    else {
        panic!("fixture layout: entry node 2 is the CondBr");
    };
    std::mem::swap(then_target, else_target);

    let originals = vec![("cf".to_string(), cf_demo_original())];
    let report = certify_backend_translation(&mut module, &originals);
    assert!(
        report.certified.is_empty(),
        "swapped arms must NOT certify: {report:?}"
    );
    assert!(
        report
            .refused
            .iter()
            .any(|(n, r)| n == "cf" && r.contains("REFUSED")),
        "the kernel must REFUSE the swapped-arm miscompile, got: {report:?}"
    );
    assert!(
        module.proof_obligations.is_empty() && module.proof_certificates.is_empty(),
        "a refusal must attach NO obligation and NO certificate"
    );
}

/// Obligation ids stay collision-free when the module already carries
/// obligations (e.g. from the default give-back pass).
#[test]
fn test_mint_allocates_fresh_obligation_ids() {
    use trust_ir::value::ProofId;
    let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("lowers");
    module.proof_obligations.push(ProofObligation {
        id: ProofId::new(7),
        kind: ObligationKind::MemorySafety,
        status: ProofStatus::Pending,
        description: "pre-existing".to_string(),
        formula: None,
        function: None,
        source: None,
    });
    let originals = vec![("tv_demo".to_string(), tv_demo_original())];
    let report = certify_backend_translation(&mut module, &originals);
    assert_eq!(report.certified.len(), 1);
    let tv_obl = module
        .proof_obligations
        .iter()
        .find(|o| o.kind == ObligationKind::TranslationValidation)
        .expect("TV obligation attached");
    assert_eq!(tv_obl.id.index(), 8, "fresh id after the existing max (7)");
}

// === Fragment-4 (closed-address computing heap) ==============================
//
// Corpus: ctor/projection over 2–4-field records mixed with arithmetic,
// hand-built in the alloc/store/load choreography the ctor lowering compiles
// to (hand-built for the same reason as `cf_demo_emitted_module` — the native
// emit path producing this exact shape is tracked as future work). Every
// corpus program mints a cert whose equation the kernel decides with an EMPTY
// axiom closure (the FOUNDATIONAL floor is asserted inside the minter).
//
// Injection corpus: miscompiled emissions, each REFUSED — by the kernel for
// value-visible bugs (wrong offset, swapped/aliased writes, load-before-store,
// dropped store, wrong projection), by the mint gate's structural balance
// check for Dealloc bugs, and by the fail-closed walker (an auditable SKIP,
// no cert ever minted) for out-of-fragment shapes.

use std::time::{Duration, Instant};

use clean_kernel::Expr as KExpr;
use trust_ir::constant::Constant;
use trust_ir::inst::{AllocOrigin, ICmpOp};
use trust_ir::ty::{FieldDef, StructDef, StructRepr, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, StructId, TyId, ValueId};
use trust_ir::{Block, FuncTy, Function, InstrNode, Module};

/// Test-side builder for straight-line heap-fragment modules: one function
/// `U32^n -> U32` with byte-offset (or word-scaled) GEPs over `StructDef`
/// records laid out `f0@0, f1@4, …`.
struct HeapFx {
    module: Module,
    body: Vec<InstrNode>,
    next: u32,
    nparams: usize,
}

impl HeapFx {
    fn new(nparams: usize) -> Self {
        let mut module = Module::new("heap_fx");
        module.func_types.push(FuncTy {
            params: vec![Ty::U32; nparams],
            returns: vec![Ty::U32],
            is_vararg: false,
        });
        HeapFx {
            module,
            body: Vec::new(),
            next: u32::try_from(nparams).unwrap(),
            nparams,
        }
    }

    /// A record `name { f0: U32 @0, f1: U32 @4, … }` in the module's struct
    /// table (size/align/offsets explicit — the layout the fold reads).
    fn add_record(&mut self, name: &str, nfields: usize) -> StructId {
        let id = StructId::new(u32::try_from(self.module.structs.len()).unwrap());
        let fields = (0..nfields)
            .map(|j| FieldDef {
                name: format!("f{j}"),
                ty: Ty::U32,
                offset: Some(4 * j as u64),
            })
            .collect();
        self.module.structs.push(StructDef {
            id,
            name: name.to_string(),
            fields,
            size: Some(4 * nfields as u64),
            align: Some(4),
            repr: StructRepr::Rust,
        });
        id
    }

    fn push(&mut self, inst: Inst) -> ValueId {
        let v = ValueId::new(self.next);
        self.next += 1;
        self.body.push(InstrNode::new(inst).with_result(v));
        v
    }

    fn param(&self, i: usize) -> ValueId {
        assert!(i < self.nparams);
        ValueId::new(u32::try_from(i).unwrap())
    }

    fn cu32(&mut self, k: i128) -> ValueId {
        self.push(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(k),
        })
    }

    fn cu64(&mut self, k: i128) -> ValueId {
        self.push(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(k),
        })
    }

    fn bin(&mut self, op: BinOp, a: ValueId, b: ValueId) -> ValueId {
        self.push(Inst::BinOp {
            op,
            ty: Ty::U32,
            lhs: a,
            rhs: b,
        })
    }

    fn alloc_ty(&mut self, ty: Ty) -> ValueId {
        self.push(Inst::HeapAlloc {
            ty,
            count: None,
            align: None,
            origin: AllocOrigin::CleanHeap,
        })
    }

    fn alloc(&mut self, sid: StructId) -> ValueId {
        self.alloc_ty(Ty::Struct(sid))
    }

    /// Byte-offset GEP over an `I8` pointee (the documented struct-field form).
    fn field_ptr(&mut self, base: ValueId, byte_off: u64) -> ValueId {
        let ix = self.cu64(i128::from(byte_off));
        self.push(Inst::GEP {
            pointee_ty: Ty::I8,
            base,
            indices: vec![ix],
            inbounds: true,
        })
    }

    /// Word-scaled GEP over a `U32` pointee (offset = index * 4).
    fn word_ptr(&mut self, base: ValueId, word_idx: u64) -> ValueId {
        let ix = self.cu64(i128::from(word_idx));
        self.push(Inst::GEP {
            pointee_ty: Ty::U32,
            base,
            indices: vec![ix],
            inbounds: true,
        })
    }

    fn store(&mut self, ptr: ValueId, v: ValueId) {
        self.body.push(InstrNode::new(Inst::Store {
            ty: Ty::U32,
            ptr,
            value: v,
            volatile: false,
            align: None,
        }));
    }

    fn load(&mut self, ptr: ValueId) -> ValueId {
        self.push(Inst::Load {
            ty: Ty::U32,
            ptr,
            volatile: false,
            align: None,
        })
    }

    fn dealloc(&mut self, ptr: ValueId) {
        self.body.push(InstrNode::new(Inst::Dealloc { ptr }));
    }

    fn finish(mut self, name: &str, ret: ValueId) -> Module {
        self.body
            .push(InstrNode::new(Inst::Return { values: vec![ret] }));
        let mut func = Function::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        for i in 0..self.nparams {
            block
                .params
                .push((ValueId::new(u32::try_from(i).unwrap()), Ty::U32));
        }
        block.body = self.body;
        func.blocks.push(block);
        self.module.add_function(func);
        self.module
    }
}

// --- source-side Expr helpers -------------------------------------------------

fn u32ty() -> KExpr {
    KExpr::const_str("UInt32")
}

fn of_nat(k: u64) -> KExpr {
    KExpr::app(KExpr::const_str("UInt32.ofNat"), KExpr::nat_lit(k))
}

fn uadd(a: KExpr, b: KExpr) -> KExpr {
    KExpr::apps(KExpr::const_str("UInt32.add"), [a, b])
}

fn umul(a: KExpr, b: KExpr) -> KExpr {
    KExpr::apps(KExpr::const_str("UInt32.mul"), [a, b])
}

/// `S.mk a…` — single-constructor aggregate introduction.
fn smk(s: &str, args: impl IntoIterator<Item = KExpr>) -> KExpr {
    KExpr::apps(KExpr::const_str(&format!("{s}.mk")), args)
}

/// `S.f<j> obj` — field projection (fields are named `f0, f1, …`).
fn sproj(s: &str, j: usize, obj: KExpr) -> KExpr {
    KExpr::app(KExpr::const_str(&format!("{s}.f{j}")), obj)
}

/// Wrap `body` in `n` `UInt32` binders (param `i` = `bvar(n - 1 - i)`).
fn lam_n(n: usize, body: KExpr) -> KExpr {
    (0..n).fold(body, |acc, _| KExpr::lam(BinderInfo::Default, u32ty(), acc))
}

// --- outcome assertions ---------------------------------------------------

#[track_caller]
fn mint(mut module: Module, name: &str, src: KExpr) -> (TvMintReport, Module) {
    let report = certify_backend_translation(&mut module, &[(name.to_string(), src)]);
    (report, module)
}

/// The program mints: kernel-certified obligation + CleanCic cert attached.
#[track_caller]
fn assert_certifies(module: Module, name: &str, src: KExpr) {
    let (report, module) = mint(module, name, src);
    assert_eq!(
        report.certified,
        vec![name.to_string()],
        "corpus program must certify, got: {report:?}"
    );
    assert!(
        report.refused.is_empty(),
        "no refusals expected: {report:?}"
    );
    let [obl] = module.proof_obligations.as_slice() else {
        panic!("exactly one obligation expected");
    };
    assert_eq!(obl.kind, ObligationKind::TranslationValidation);
    assert_eq!(obl.status, ProofStatus::Certified);
    assert!(
        module
            .proof_certificates
            .iter()
            .any(|c| matches!(c.evidence, ProofEvidence::CleanCic { .. })),
        "a CleanCic certificate must be attached"
    );
}

/// The KERNEL refuses the equation (value-visible miscompile): hard REFUSAL,
/// no obligation, no certificate.
#[track_caller]
fn assert_kernel_refuses(module: Module, name: &str, src: KExpr) {
    let (report, module) = mint(module, name, src);
    assert!(
        report.certified.is_empty(),
        "a miscompiled emission must NOT certify: {report:?}"
    );
    assert!(
        report
            .refused
            .iter()
            .any(|(n, r)| n == name && r.contains("REFUSED")),
        "the kernel must REFUSE the equation, got: {report:?}"
    );
    assert!(
        module.proof_obligations.is_empty() && module.proof_certificates.is_empty(),
        "a refusal must attach NO obligation and NO certificate"
    );
}

/// The MINT GATE refuses structurally (the Dealloc balance cases): hard
/// REFUSAL with the auditable balance reason.
#[track_caller]
fn assert_mint_gate_refuses(module: Module, name: &str, src: KExpr, why: &str) {
    let (report, module) = mint(module, name, src);
    assert!(report.certified.is_empty(), "must not certify: {report:?}");
    assert!(
        report
            .refused
            .iter()
            .any(|(n, r)| n == name && r.contains(why)),
        "the mint gate must refuse with `{why}`, got: {report:?}"
    );
    assert!(
        module.proof_obligations.is_empty() && module.proof_certificates.is_empty(),
        "a refusal must attach NO obligation and NO certificate"
    );
}

/// The fail-closed walker keeps the program OUTSIDE the fragment (an
/// auditable SKIP — refusing to mint; no cert is ever attached).
#[track_caller]
fn assert_walker_skips(module: Module, name: &str, src: KExpr, why: &str) {
    let (report, module) = mint(module, name, src);
    assert!(report.certified.is_empty(), "must not certify: {report:?}");
    assert!(
        report
            .skipped
            .iter()
            .any(|(n, r)| n == name && r.contains(why)),
        "expected an auditable fail-closed skip containing `{why}`, got: {report:?}"
    );
    assert!(
        module.proof_obligations.is_empty() && module.proof_certificates.is_empty(),
        "a skip must attach NO obligation and NO certificate"
    );
}

// --- the corpus (≥10 programs, each kernel-recheck green) ---------------------

/// `Pair.f0 (Pair.mk a b)` — alloc, two stores, load field 0.
#[test]
fn heap_certifies_pair_first() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    let a = b.param(0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    let bb = b.param(1);
    b.store(p1, bb);
    let r = b.load(p0);
    b.dealloc(p);
    let module = b.finish("pair_first", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_certifies(module, "pair_first", src);
}

/// `Pair.f1 (Pair.mk a b)` — load field 1.
#[test]
fn heap_certifies_pair_second() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    let a = b.param(0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    let bb = b.param(1);
    b.store(p1, bb);
    let r = b.load(p1);
    b.dealloc(p);
    let module = b.finish("pair_second", r);
    let src = lam_n(
        2,
        sproj("Pair", 1, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_certifies(module, "pair_second", src);
}

/// Arithmetic INTO the ctor and OVER the projections:
/// `Pair.f0 (Pair.mk (a+1) b) + Pair.f1 (Pair.mk (a+1) b)`.
#[test]
fn heap_certifies_pair_sum_with_arith() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let one = b.cu32(1);
    let a = b.param(0);
    let t = b.bin(BinOp::Add, a, one);
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, t);
    let p1 = b.field_ptr(p, 4);
    let bb = b.param(1);
    b.store(p1, bb);
    let l0 = b.load(p0);
    let l1 = b.load(p1);
    let s = b.bin(BinOp::Add, l0, l1);
    b.dealloc(p);
    let module = b.finish("pair_sum", s);
    let mk = || smk("Pair", [uadd(KExpr::bvar(1), of_nat(1)), KExpr::bvar(0)]);
    let src = lam_n(2, uadd(sproj("Pair", 0, mk()), sproj("Pair", 1, mk())));
    assert_certifies(module, "pair_sum", src);
}

/// A 3-field record with computed fields: `Triple.f1 (Triple.mk (a+b) (b*c) 5)
/// + Triple.f2 (…)`.
#[test]
fn heap_certifies_triple_mixed_arith() {
    let mut b = HeapFx::new(3);
    let tri = b.add_record("Triple", 3);
    let (a, bb, c) = (b.param(0), b.param(1), b.param(2));
    let f0 = b.bin(BinOp::Add, a, bb);
    let f1 = b.bin(BinOp::Mul, bb, c);
    let f2 = b.cu32(5);
    let p = b.alloc(tri);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, f0);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, f1);
    let p2 = b.field_ptr(p, 8);
    b.store(p2, f2);
    let l1 = b.load(p1);
    let l2 = b.load(p2);
    let s = b.bin(BinOp::Add, l1, l2);
    b.dealloc(p);
    let module = b.finish("triple_mix", s);
    // params: a = bvar 2, b = bvar 1, c = bvar 0
    let mk = || {
        smk(
            "Triple",
            [
                uadd(KExpr::bvar(2), KExpr::bvar(1)),
                umul(KExpr::bvar(1), KExpr::bvar(0)),
                of_nat(5),
            ],
        )
    };
    let src = lam_n(3, uadd(sproj("Triple", 1, mk()), sproj("Triple", 2, mk())));
    assert_certifies(module, "triple_mix", src);
}

/// A 4-field record, projecting the last field: `Quad.f3 (Quad.mk a b (a+b) (a*b))`.
#[test]
fn heap_certifies_quad_fourth_field() {
    let mut b = HeapFx::new(2);
    let quad = b.add_record("Quad", 4);
    let (a, bb) = (b.param(0), b.param(1));
    let f2 = b.bin(BinOp::Add, a, bb);
    let f3 = b.bin(BinOp::Mul, a, bb);
    let p = b.alloc(quad);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let p2 = b.field_ptr(p, 8);
    b.store(p2, f2);
    let p3 = b.field_ptr(p, 12);
    b.store(p3, f3);
    let r = b.load(p3);
    b.dealloc(p);
    let module = b.finish("quad_last", r);
    let mk = smk(
        "Quad",
        [
            KExpr::bvar(1),
            KExpr::bvar(0),
            uadd(KExpr::bvar(1), KExpr::bvar(0)),
            umul(KExpr::bvar(1), KExpr::bvar(0)),
        ],
    );
    let src = lam_n(2, sproj("Quad", 3, mk));
    assert_certifies(module, "quad_last", src);
}

/// TWO allocations at distinct model bases (0 and BLOCK):
/// `Pair.f0 (Pair.mk a b) + Pair.f1 (Pair.mk b a)`.
#[test]
fn heap_certifies_two_allocations() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let q = b.alloc(pair);
    let q0 = b.field_ptr(q, 0);
    b.store(q0, bb);
    let q1 = b.field_ptr(q, 4);
    b.store(q1, a);
    let l0 = b.load(p0);
    let l1 = b.load(q1);
    let s = b.bin(BinOp::Add, l0, l1);
    b.dealloc(p);
    b.dealloc(q);
    let module = b.finish("two_allocs", s);
    let src = lam_n(
        2,
        uadd(
            sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
            sproj("Pair", 1, smk("Pair", [KExpr::bvar(0), KExpr::bvar(1)])),
        ),
    );
    assert_certifies(module, "two_allocs", src);
}

/// Same-cell OVERWRITE (a two-deep tower on one address): last write wins,
/// exactly the semantics — `Pair.f0 (Pair.mk b a)` after storing `a` then `b`
/// at field 0.
#[test]
fn heap_certifies_same_cell_overwrite() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    b.store(p0, bb); // overwrite
    let p1 = b.field_ptr(p, 4);
    b.store(p1, a);
    let r = b.load(p0);
    b.dealloc(p);
    let module = b.finish("overwrite", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(0), KExpr::bvar(1)])),
    );
    assert_certifies(module, "overwrite", src);
}

/// The word-scaled GEP form (`pointee U32, index j` — offset j*4) folds to
/// the same cells as the byte-offset form.
#[test]
fn heap_certifies_scaled_word_gep() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.word_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.word_ptr(p, 1);
    b.store(p1, bb);
    let r = b.load(p1);
    b.dealloc(p);
    let module = b.finish("scaled_gep", r);
    let src = lam_n(
        2,
        sproj("Pair", 1, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_certifies(module, "scaled_gep", src);
}

/// Arithmetic ON a loaded value: `(Pair.f0 (Pair.mk a b)) * 3 + 7`.
#[test]
fn heap_certifies_arith_on_loaded_value() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let l = b.load(p0);
    let three = b.cu32(3);
    let m = b.bin(BinOp::Mul, l, three);
    let seven = b.cu32(7);
    let s = b.bin(BinOp::Add, m, seven);
    b.dealloc(p);
    let module = b.finish("arith_load", s);
    let proj = sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)]));
    let src = lam_n(2, uadd(umul(proj, of_nat(3)), of_nat(7)));
    assert_certifies(module, "arith_load", src);
}

/// Nested arithmetic INSIDE ctor fields: `Triple.f0 (Triple.mk ((a+b)*c) c a)`.
#[test]
fn heap_certifies_nested_field_exprs() {
    let mut b = HeapFx::new(3);
    let tri = b.add_record("Triple", 3);
    let (a, bb, c) = (b.param(0), b.param(1), b.param(2));
    let t1 = b.bin(BinOp::Add, a, bb);
    let t2 = b.bin(BinOp::Mul, t1, c);
    let p = b.alloc(tri);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, t2);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, c);
    let p2 = b.field_ptr(p, 8);
    b.store(p2, a);
    let r = b.load(p0);
    b.dealloc(p);
    let module = b.finish("nested_fields", r);
    let mk = smk(
        "Triple",
        [
            umul(uadd(KExpr::bvar(2), KExpr::bvar(1)), KExpr::bvar(0)),
            KExpr::bvar(0),
            KExpr::bvar(2),
        ],
    );
    let src = lam_n(3, sproj("Triple", 0, mk));
    assert_certifies(module, "nested_fields", src);
}

/// A load–store CHAIN through the heap (nested `hread` inside a stored
/// value): store a@f0, copy f0 into f1 via a load, read f1 — `Pair.f1
/// (Pair.mk a a)`.
#[test]
fn heap_certifies_load_store_chain() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let a = b.param(0);
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let v = b.load(p0);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, v);
    let w = b.load(p1);
    b.dealloc(p);
    let module = b.finish("chain", w);
    let src = lam_n(
        2,
        sproj("Pair", 1, smk("Pair", [KExpr::bvar(1), KExpr::bvar(1)])),
    );
    assert_certifies(module, "chain", src);
}

/// Heap use INSIDE one Fragment-3a arm (fresh per-arm heap):
/// `if a < 10 then Pair.f0 (Pair.mk (a+b) b) else b`.
#[test]
fn heap_certifies_heap_in_branch_arm() {
    let mut module = Module::new("arm_heap_fixture");
    module.structs.push(StructDef {
        id: StructId::new(0),
        name: "Pair".to_string(),
        fields: vec![
            FieldDef {
                name: "f0".to_string(),
                ty: Ty::U32,
                offset: Some(0),
            },
            FieldDef {
                name: "f1".to_string(),
                ty: Ty::U32,
                offset: Some(4),
            },
        ],
        size: Some(8),
        align: Some(4),
        repr: StructRepr::Rust,
    });
    module.func_types.push(FuncTy {
        params: vec![Ty::U32, Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
    });
    let mut func = Function::new(
        FuncId::new(0),
        "arm_heap",
        FuncTyId::new(0),
        BlockId::new(0),
    );

    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::U32));
    entry.params.push((ValueId::new(1), Ty::U32));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(10),
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ult,
            ty: Ty::U32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(2),
        })
        .with_result(ValueId::new(3)),
    );
    entry.body.push(InstrNode::new(Inst::CondBr {
        cond: ValueId::new(3),
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    }));

    // then arm: its OWN alloc/store/load/dealloc choreography.
    let mut then_blk = Block::new(BlockId::new(1));
    then_blk.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(4)),
    );
    then_blk.body.push(
        InstrNode::new(Inst::HeapAlloc {
            ty: Ty::Struct(StructId::new(0)),
            count: None,
            align: None,
            origin: AllocOrigin::CleanHeap,
        })
        .with_result(ValueId::new(5)),
    );
    then_blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(6)),
    );
    then_blk.body.push(
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I8,
            base: ValueId::new(5),
            indices: vec![ValueId::new(6)],
            inbounds: true,
        })
        .with_result(ValueId::new(7)),
    );
    then_blk.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U32,
        ptr: ValueId::new(7),
        value: ValueId::new(4),
        volatile: false,
        align: None,
    }));
    then_blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(4),
        })
        .with_result(ValueId::new(8)),
    );
    then_blk.body.push(
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I8,
            base: ValueId::new(5),
            indices: vec![ValueId::new(8)],
            inbounds: true,
        })
        .with_result(ValueId::new(9)),
    );
    then_blk.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U32,
        ptr: ValueId::new(9),
        value: ValueId::new(1),
        volatile: false,
        align: None,
    }));
    then_blk.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::U32,
            ptr: ValueId::new(7),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(10)),
    );
    then_blk.body.push(InstrNode::new(Inst::Dealloc {
        ptr: ValueId::new(5),
    }));
    then_blk.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(10)],
    }));

    let mut else_blk = Block::new(BlockId::new(2));
    else_blk.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));

    func.blocks.push(entry);
    func.blocks.push(then_blk);
    func.blocks.push(else_blk);
    module.add_function(func);

    let cond = KExpr::apps(KExpr::const_str("UInt32.blt"), [KExpr::bvar(1), of_nat(10)]);
    let then_e = sproj(
        "Pair",
        0,
        smk(
            "Pair",
            [uadd(KExpr::bvar(1), KExpr::bvar(0)), KExpr::bvar(0)],
        ),
    );
    let ite = KExpr::apps(
        KExpr::const_str("cond"),
        [u32ty(), cond, then_e, KExpr::bvar(0)],
    );
    let src = lam_n(2, ite);
    assert_certifies(module, "arm_heap", src);
}

/// An ARRAY allocation used as a scratch cell (constant index): the source is
/// plain arithmetic — the pure side never sees the heap.
#[test]
fn heap_certifies_array_scratch_cell() {
    let mut b = HeapFx::new(2);
    b.module.types.push(Ty::U32); // TyId(0) = U32
    let (a, bb) = (b.param(0), b.param(1));
    let t = b.bin(BinOp::Add, a, bb);
    let arr = b.alloc_ty(Ty::Array(TyId::new(0), 4));
    let cell = b.word_ptr(arr, 2);
    b.store(cell, t);
    let r = b.load(cell);
    b.dealloc(arr);
    let module = b.finish("arr_scratch", r);
    let src = lam_n(2, uadd(KExpr::bvar(1), KExpr::bvar(0)));
    assert_certifies(module, "arr_scratch", src);
}

// --- the injection corpus (each a miscompiled emission, each refused) ---------

/// Honest shape shared by the wrong-offset injections: `Triple.f1
/// (Triple.mk a b 5)` — return field 1 (= b). The injections mis-address the
/// f1 store WITHIN the record's cells, so the WALKER accepts and the KERNEL
/// refuses (the design note's wrong-offset case).
fn triple_f1_module(f1_store_offset: u64) -> Module {
    let mut b = HeapFx::new(2);
    let tri = b.add_record("Triple", 3);
    let (a, bb) = (b.param(0), b.param(1));
    let five = b.cu32(5);
    let p = b.alloc(tri);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, f1_store_offset); // honest: 4
    b.store(p1, bb);
    let p2 = b.field_ptr(p, 8);
    b.store(p2, five);
    let honest_p1 = b.field_ptr(p, 4);
    let r = b.load(honest_p1);
    b.dealloc(p);
    b.finish("triple_f1", r)
}

fn triple_f1_source() -> KExpr {
    lam_n(
        2,
        sproj(
            "Triple",
            1,
            smk("Triple", [KExpr::bvar(1), KExpr::bvar(0), of_nat(5)]),
        ),
    )
}

/// Sanity: the honest triple_f1 shape certifies (so the injections below
/// fail for the injected reason, not a fixture artifact).
#[test]
fn heap_injection_baseline_certifies() {
    assert_certifies(triple_f1_module(4), "triple_f1", triple_f1_source());
}

/// WRONG OFFSET (+1 word): the f1 store lands at 8 (field 2's cell). The
/// later load at 4 reduces past it to hempty's 0 — kernel REFUSES.
#[test]
fn heap_refuses_wrong_offset_store_plus_word() {
    assert_kernel_refuses(triple_f1_module(8), "triple_f1", triple_f1_source());
}

/// WRONG OFFSET (-1 word): the f1 store lands at 0, clobbering field 0; the
/// load at 4 reads hempty's 0 — kernel REFUSES.
#[test]
fn heap_refuses_wrong_offset_store_minus_word() {
    assert_kernel_refuses(triple_f1_module(0), "triple_f1", triple_f1_source());
}

/// FIELD SWAP: the two stores of `Pair.mk a b` are swapped (a@4, b@0); the
/// load of field 0 now reads b where the source projects a — kernel REFUSES.
#[test]
fn heap_refuses_field_swap_stores() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, a); // swapped: a into f1
    b.store(p0, bb); // swapped: b into f0
    let r = b.load(p0);
    b.dealloc(p);
    let module = b.finish("field_swap", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_kernel_refuses(module, "field_swap", src);
}

/// SWAPPED DEPENDENT STORES: two writes to the SAME cell in the wrong order —
/// the read normalizes to the earlier value; kernel REFUSES.
#[test]
fn heap_refuses_swapped_dependent_stores() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    // Honest order stores a then b (last write wins = b). Injected: b then a.
    b.store(p0, bb);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, a);
    let r = b.load(p0);
    b.dealloc(p);
    let module = b.finish("dep_stores", r);
    // Source: field 0 holds b (the honest final value).
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(0), KExpr::bvar(1)])),
    );
    assert_kernel_refuses(module, "dep_stores", src);
}

/// ALIASED DOUBLE-WRITE DIVERGENCE: a second pointer value (a GEP alias of
/// the same literal cell) writes after the first — a compiler that assumed
/// no-alias and kept the first value miscompiles; addresses are literals, so
/// the read normalizes to the aliased write's value and the kernel REFUSES
/// the no-alias assumption's equation.
#[test]
fn heap_refuses_aliased_double_write_divergence() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    let alias = b.field_ptr(p, 0); // distinct SSA value, same literal cell
    b.store(p0, a);
    b.store(alias, bb); // the aliased write
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let r = b.load(p0);
    b.dealloc(p);
    let module = b.finish("aliased", r);
    // The (wrong) no-alias source claims field 0 still holds a.
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_kernel_refuses(module, "aliased", src);
}

/// LOAD-BEFORE-STORE: the load is hoisted above the store — an uninitialized
/// read (UB in trust-ir semantics). The WALKER refuses it structurally
/// (never denoting it to hempty's 0) and the gate escalates to REFUSED.
#[test]
fn heap_refuses_load_before_store() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    let r = b.load(p0); // hoisted above the store
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    b.dealloc(p);
    let module = b.finish("hoisted_load", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_kernel_refuses(module, "hoisted_load", src);
}

/// DROPPED STORE: field 1's store is deleted; its load reads a never-written
/// cell — the WALKER refuses the uninitialized read structurally and the
/// gate escalates to REFUSED.
#[test]
fn heap_refuses_dropped_store() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let a = b.param(0);
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    // (the b -> f1 store is DROPPED)
    let p1 = b.field_ptr(p, 4);
    let r = b.load(p1);
    b.dealloc(p);
    let module = b.finish("dropped_store", r);
    let src = lam_n(
        2,
        sproj("Pair", 1, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_kernel_refuses(module, "dropped_store", src);
}

/// DROPPED STORE OF LITERAL 0 — the soundness hole the walker's written-cell
/// tracking closes: without it, the never-written cell denoted to hempty's 0
/// and the equation `0 = 0` CERTIFIED this miscompile. Must refuse.
#[test]
fn heap_refuses_dropped_store_of_literal_zero() {
    let mut b = HeapFx::new(1);
    let pair = b.add_record("Pair", 2);
    let bb = b.param(0);
    let p = b.alloc(pair);
    // (the `0 -> f0` store is DROPPED)
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let p0 = b.field_ptr(p, 0);
    let r = b.load(p0);
    b.dealloc(p);
    let module = b.finish("dropped_zero_store", r);
    // The source honestly claims field 0 holds the literal 0 the (dropped)
    // store would have written.
    let src = lam_n(
        1,
        sproj("Pair", 0, smk("Pair", [of_nat(0), KExpr::bvar(0)])),
    );
    assert_kernel_refuses(module, "dropped_zero_store", src);
}

/// WRONG FIELD PROJECTION: the emission loads field 0 where the source
/// projects field 1 (distinct field values) — kernel REFUSES.
#[test]
fn heap_refuses_wrong_field_projection() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let r = b.load(p0); // loads f0…
    b.dealloc(p);
    let module = b.finish("wrong_proj", r);
    // …but the source projects f1.
    let src = lam_n(
        2,
        sproj("Pair", 1, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_kernel_refuses(module, "wrong_proj", src);
}

/// DROPPED DEALLOC: the value equation cannot see a leak — the MINT GATE's
/// structural balance check refuses it.
#[test]
fn heap_refuses_dropped_dealloc() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let r = b.load(p0);
    // (the Dealloc is DROPPED)
    let module = b.finish("leak", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_mint_gate_refuses(module, "leak", src, "dropped Dealloc");
}

/// DOUBLED DEALLOC: likewise invisible to the value equation — the MINT
/// GATE's structural balance check refuses the double-free.
#[test]
fn heap_refuses_doubled_dealloc() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let r = b.load(p0);
    b.dealloc(p);
    b.dealloc(p); // DOUBLED
    let module = b.finish("double_free", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_mint_gate_refuses(module, "double_free", src, "doubled Dealloc");
}

/// Dealloc of a NON-BASE address (a field pointer): fails closed in the
/// walker — the program stays outside the fragment, no cert is minted.
#[test]
fn heap_refuses_dealloc_of_non_base_address() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let r = b.load(p0);
    b.dealloc(p1); // NON-BASE (not the allocation's own result value)
    let module = b.finish("bad_dealloc", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_walker_skips(
        module,
        "bad_dealloc",
        src,
        "not the allocation's own HeapAlloc result value",
    );
}

/// NON-CONSTANT GEP INDEX (a parameter): does not fold — fail-closed.
#[test]
fn heap_refuses_non_constant_gep_index() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let ptr = b.push(Inst::GEP {
        pointee_ty: Ty::I8,
        base: p,
        indices: vec![bb], // a RUNTIME index
        inbounds: true,
    });
    b.store(ptr, a);
    let r = b.load(ptr);
    b.dealloc(p);
    let module = b.finish("dyn_gep", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_walker_skips(module, "dyn_gep", src, "non-constant GEP index");
}

/// POINTER-TYPED PARAMETER: open-heap functions are out of M1 — fail-closed.
#[test]
fn heap_refuses_pointer_param() {
    let mut module = Module::new("ptr_param_fixture");
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::U32],
        is_vararg: false,
    });
    let mut func = Function::new(
        FuncId::new(0),
        "ptr_param",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Ptr));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    func.blocks.push(block);
    module.add_function(func);
    let src = KExpr::lam(BinderInfo::Default, u32ty(), of_nat(0));
    assert_walker_skips(module, "ptr_param", src, "parameter type");
}

/// LOAD OUTSIDE THE FOOTPRINT: offset 8 of an 8-byte record is no recorded
/// cell — fail-closed at mint (the design note's unrecorded-address rule).
#[test]
fn heap_refuses_load_outside_footprint() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let out = b.field_ptr(p, 8); // past the record
    let r = b.load(out);
    b.dealloc(p);
    let module = b.finish("oob_load", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_walker_skips(module, "oob_load", src, "not a recorded live cell");
}

/// LOAD AFTER DEALLOC (structural use-after-free): the cell is no longer
/// live — fail-closed at mint.
#[test]
fn heap_refuses_load_after_dealloc() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    b.dealloc(p);
    let r = b.load(p0); // use-after-free
    let module = b.finish("uaf_load", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_walker_skips(module, "uaf_load", src, "deallocated");
}

/// A FOREIGN ALLOCATION ORIGIN (RustHeap): the fragment models CleanHeap
/// Perceus cells only — fail-closed.
#[test]
fn heap_refuses_foreign_alloc_origin() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let a = b.param(0);
    let p = b.push(Inst::HeapAlloc {
        ty: Ty::Struct(pair),
        count: None,
        align: None,
        origin: AllocOrigin::RustHeap, // FOREIGN
    });
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let r = b.load(p0);
    b.dealloc(p);
    let module = b.finish("foreign_origin", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_walker_skips(module, "foreign_origin", src, "CleanHeap only");
}

/// A VOLATILE STORE is an observable access, not a pure cell write —
/// fail-closed.
#[test]
fn heap_refuses_volatile_store() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let a = b.param(0);
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U32,
        ptr: p0,
        value: a,
        volatile: true, // VOLATILE
        align: None,
    }));
    let r = b.load(p0);
    b.dealloc(p);
    let module = b.finish("volatile_store", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_walker_skips(module, "volatile_store", src, "volatile");
}

/// CROSS-ALLOCATION GEP (a pointer-identity game): a GEP from allocation A
/// folding into allocation B's block is NOT a recorded cell of its OWN
/// allocation — fail-closed at mint (honesty note 3).
#[test]
fn heap_refuses_cross_allocation_gep() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair); // base 0
    let q = b.alloc(pair); // base BLOCK = 16
    let q0 = b.field_ptr(q, 0);
    b.store(q0, bb);
    let smuggled = b.field_ptr(p, 16); // p + 16 == q's base, owner is p
    b.store(smuggled, a);
    let r = b.load(q0);
    b.dealloc(p);
    b.dealloc(q);
    let module = b.finish("cross_gep", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(0), KExpr::bvar(1)])),
    );
    assert_walker_skips(module, "cross_gep", src, "not a recorded live cell");
}

// --- the ledger measurement (Risk 2 discipline) --------------------------------

/// The LARGEST corpus program — a 10-field record with 20 stores (every field
/// written then overwritten) and 10 loads summed — and the kernel-recheck
/// wall-time measurement the CK1 ledger records (the note budgets well under
/// 2 s for ≤10-field/≤20-store bodies).
#[test]
fn heap_ledger_ten_fields_twenty_stores_recheck_time() {
    let mut b = HeapFx::new(2);
    let ten = b.add_record("Ten", 10);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(ten);
    // First batch: field i <- a + i.
    let mut ptrs = Vec::new();
    for i in 0..10u64 {
        let k = b.cu32(i128::from(i));
        let v = b.bin(BinOp::Add, a, k);
        let ptr = b.field_ptr(p, 4 * i);
        b.store(ptr, v);
        ptrs.push(ptr);
    }
    // Second batch (overwrites): field i <- b * (i + 1).
    for (i, ptr) in ptrs.iter().enumerate() {
        let k = b.cu32(i128::from(i as u64 + 1));
        let v = b.bin(BinOp::Mul, bb, k);
        b.store(*ptr, v);
    }
    // Sum the ten loads.
    let mut acc = b.load(ptrs[0]);
    for ptr in &ptrs[1..] {
        let l = b.load(*ptr);
        acc = b.bin(BinOp::Add, acc, l);
    }
    b.dealloc(p);
    let module = b.finish("ledger_ten", acc);

    // Source: fold add over the ten projections of the FINAL ctor value.
    let mk = || {
        smk(
            "Ten",
            (0..10u64).map(|i| umul(KExpr::bvar(0), of_nat(i + 1))),
        )
    };
    let mut src_body = sproj("Ten", 0, mk());
    for i in 1..10usize {
        src_body = uadd(src_body, sproj("Ten", i, mk()));
    }
    let src = lam_n(2, src_body);

    // Measure the recheck decomposed: prelude env build, heap vocabulary
    // install, and the actual kernel judgment (theorem add).
    let lhs = clean_reflect::denote_function(&module, &module.functions[0])
        .expect("ledger program is in-fragment");
    let vocab = clean_reflect::RecordVocab::from_module(&module);
    let rhs = clean_reflect::denote_source(&src, 32, &[], &vocab).expect("ledger source denotes");
    assert_eq!(lhs.arity, rhs.arity);

    let t0 = Instant::now();
    let mut env = Environment::try_with_prelude().expect("prelude");
    let t_env = t0.elapsed();
    for decl in heap_vocab_declarations() {
        env.add_decl(decl).expect("heap vocabulary installs");
    }
    let t1 = Instant::now();
    env.add_decl(clean_kernel::env::Declaration::Theorem {
        name: Name::from_string(&clean_reflect::tv_theorem_name("ledger_ten")),
        level_params: vec![],
        type_: clean_reflect::tv_statement(&[], lhs.arity, &lhs.body, &rhs.body),
        value: clean_reflect::tv_proof_term(&[], lhs.arity, &lhs.body),
    })
    .expect("the kernel decides the 10-field/20-store equation");
    let t_thm = t1.elapsed();
    eprintln!(
        "CK1-LEDGER heap TV recheck (ledger_ten, 10 fields / 20 stores / 10 loads): \
         kernel judgment {t_thm:?} (+ prelude env build {t_env:?}; total {:?})",
        t0.elapsed()
    );
    // Falsifier floor (generous for debug builds; the ledger number itself is
    // taken from a release run and recorded in the CK1 ledger).
    assert!(
        t_thm < Duration::from_secs(30),
        "kernel judgment took {t_thm:?} — the closed-address model has regressed"
    );

    // And the full mint path certifies it end-to-end.
    assert_certifies(module, "ledger_ten", src);
}

// ---------------------------------------------------------------------------
// PIPELINE WIRING (default-on): `compile_lcnf_to_trust_ir` with the DEFAULT
// config must mint the certificate for an in-fragment decl — the "certified
// by default where fragments allow" rung (2026-07-21 flip).
// ---------------------------------------------------------------------------

/// The default config certifies: `TrustIrConfig::certify_translation` is ON.
#[test]
fn test_certify_translation_is_default_on() {
    assert!(
        crate::emit_trust_ir::TrustIrConfig::default().certify_translation,
        "certified-by-default regressed: TrustIrConfig::default().certify_translation \
         must be true (see designs/2026-07-04-backend-tv-certificate.md, 2026-07-21 update)"
    );
}

/// E2E through the REAL pipeline entry point: a kernel definition whose
/// lowering lands in Fragment-2 (`certDemo : UInt32 -> UInt32 := fun x => x`
/// — a scalar-signature decl the boxing pass leaves scalar), taken through
/// `constant_to_decl` (the REAL frontend path) and
/// `compile_lcnf_to_trust_ir` with the DEFAULT config, comes out with a
/// `Certified` `TranslationValidation` obligation + `CleanCic` certificate —
/// no opt-in flag anywhere.
///
/// Why the identity and not arithmetic: pipeline-lowered fixed-width
/// arithmetic is currently BOXED (`Box` args + `Apply UInt32.add` at
/// `Object`; the `unboxing::unbox_decls` pass is not yet wired into
/// `compile_lcnf_decls`), so `uint_arith_binop`'s native-BinOp arm is only
/// reachable from IRDecl-level producers today. The scalar identity is the
/// smallest decl the REAL pipeline lowers into the fragment end-to-end.
#[test]
fn test_pipeline_mints_certificate_by_default() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    use crate::pass_manager::{compile_lcnf_to_trust_ir, PipelineConfig};
    use crate::to_lcnf::constant_to_decl;
    use clean_kernel::env::Declaration;
    use clean_kernel::Environment;

    let u32_ty = || KExpr::const_str("UInt32");

    // Kernel source of truth: certDemo : UInt32 -> UInt32 := fun x => x.
    let defn = KExpr::lam(BinderInfo::Default, u32_ty(), KExpr::bvar(0));
    let mut env = Environment::try_with_prelude().expect("prelude environment");
    env.add_decl(Declaration::Definition {
        name: KName::from_string("certDemo"),
        level_params: vec![],
        type_: KExpr::arrow(u32_ty(), u32_ty()),
        value: defn,
        is_reducible: true,
    })
    .expect("certDemo kernel-checks against the prelude");

    // The REAL frontend lowering, not a hand-built LCNF.
    let info = env
        .get_const(&KName::from_string("certDemo"))
        .expect("certDemo is in the environment");
    let decl = constant_to_decl(&env, info)
        .expect("certDemo lowers to LCNF")
        .expect("certDemo is computable");

    // DEFAULT config apart from ExternCalls (the handoff mode every shipping
    // consumer uses); certify_translation is NOT spelled — the default is on trial.
    let config = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module = compile_lcnf_to_trust_ir(
        std::slice::from_ref(&decl),
        &env,
        &PipelineConfig::default(),
        &config,
    )
    .expect("pipeline compiles + certifies certDemo");

    let func = module
        .functions
        .iter()
        .find(|f| f.name == "certDemo")
        .expect("certDemo was emitted");
    let obl = module
        .proof_obligations
        .iter()
        .find(|o| o.kind == ObligationKind::TranslationValidation)
        .unwrap_or_else(|| {
            panic!(
                "default-config pipeline must mint the TV obligation for the in-fragment \
                 decl; obligations: {:?}; functions: {:?}",
                module.proof_obligations,
                module.functions.iter().map(|f| &f.name).collect::<Vec<_>>()
            )
        });
    assert_eq!(obl.status, ProofStatus::Certified);
    assert_eq!(obl.function, Some(func.id));
    let cert = module
        .proof_certificates
        .iter()
        .find(|c| c.obligation == obl.id)
        .expect("the obligation carries its CleanCic certificate");
    assert!(
        matches!(cert.evidence, ProofEvidence::CleanCic { .. }),
        "evidence must be kernel-re-checkable CleanCic, got: {:?}",
        cert.prover
    );
}

// ---------------------------------------------------------------------------
// FRAGMENT-5 (boxed-scalar Nat vocabulary): a parameter-free boxed-`Nat`
// constant — `() -> Ptr` built from the runtime box vocabulary, e.g. the
// `UIntN.size` family — certifies against its `Nat` source literal, and a
// miscompiled constant is REFUSED (the Nat-fragment miscompile detector).
// ---------------------------------------------------------------------------

/// Build a `() -> Ptr` "boxed-Nat constant" module: `const u64 k;
/// %1 = call clean_box_uint64(%0); ret %1`, with a bodyless `clean_box_uint64`
/// runtime extern (the vocabulary primitive). Name it `demoNat`.
fn boxed_nat_const_module(k: i128) -> Module {
    use trust_ir::constant::Constant;
    let mut m = Module::new("f5_boxed_nat");
    // ft0 = (u64) -> ptr  (clean_box_uint64);  ft1 = () -> ptr  (demoNat)
    m.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::Ptr],
        is_vararg: false,
    });
    m.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::Ptr],
        is_vararg: false,
    });
    // Bodyless runtime extern (no blocks => External import).
    m.add_function(Function::new(
        FuncId::new(0),
        "clean_box_uint64",
        FuncTyId::new(0),
        BlockId::new(0),
    ));
    // demoNat body.
    let mut f = Function::new(FuncId::new(1), "demoNat", FuncTyId::new(1), BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(k),
        })
        .with_result(ValueId::new(0)),
    );
    b.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
    );
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    f.blocks.push(b);
    m.add_function(f);
    m
}

/// A boxed-Nat constant certifies against its `Nat` source literal (the
/// `UIntN.size` shape: `clean_box_uint64 256` denotes `256`, source `256`).
#[test]
fn test_fragment5_certifies_boxed_nat_constant() {
    let module = boxed_nat_const_module(256);
    let (report, module) = mint(module, "demoNat", KExpr::nat_lit(256));
    assert_eq!(
        report.certified,
        vec!["demoNat".to_string()],
        "boxed-Nat constant must certify, got: {report:?}"
    );
    assert!(report.refused.is_empty(), "no refusals: {report:?}");
    let obl = module
        .proof_obligations
        .iter()
        .find(|o| o.kind == ObligationKind::TranslationValidation)
        .expect("TV obligation attached");
    assert_eq!(obl.status, ProofStatus::Certified);
    let cert = module
        .proof_certificates
        .iter()
        .find(|c| c.obligation == obl.id)
        .expect("cert attached");
    assert!(matches!(cert.evidence, ProofEvidence::CleanCic { .. }));
}

/// A MISCOMPILED boxed-Nat constant (emitted `clean_box_uint64 255` vs source
/// `256`) is REFUSED — the Fragment-5 Nat miscompile detector fires. No
/// obligation attached.
#[test]
fn test_fragment5_refuses_miscompiled_boxed_nat_constant() {
    let module = boxed_nat_const_module(255);
    let (report, module) = mint(module, "demoNat", KExpr::nat_lit(256));
    assert!(
        report.certified.is_empty(),
        "a miscompiled constant must NOT certify: {report:?}"
    );
    assert!(
        report.refused.iter().any(|(n, _)| n == "demoNat"),
        "the kernel must REFUSE 255 != 256, got: {report:?}"
    );
    assert!(
        module.proof_obligations.is_empty() && module.proof_certificates.is_empty(),
        "a refusal attaches no obligation/cert"
    );
}

/// The bignum `Nat` arithmetic rows are faithful: `clean_nat_of_u64 2 *
/// clean_nat_of_u64 3` (via `l_Nat_mul`) denotes `Nat.mul 2 3`, and the source
/// `Nat.mul 2 3` certifies (no `u64` wrap shortcut — plain bignum).
#[test]
fn test_fragment5_certifies_nat_mul_constant() {
    use trust_ir::constant::Constant;
    let mut m = Module::new("f5_nat_mul");
    // ft0 = (u64)->ptr clean_nat_of_u64; ft1 = (ptr,ptr)->ptr l_Nat_mul;
    // ft2 = ()->ptr demoMul
    m.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::Ptr],
        is_vararg: false,
    });
    m.func_types.push(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr],
        returns: vec![Ty::Ptr],
        is_vararg: false,
    });
    m.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::Ptr],
        is_vararg: false,
    });
    m.add_function(Function::new(
        FuncId::new(0),
        "clean_nat_of_u64",
        FuncTyId::new(0),
        BlockId::new(0),
    ));
    m.add_function(Function::new(
        FuncId::new(1),
        "l_Nat_mul",
        FuncTyId::new(1),
        BlockId::new(0),
    ));
    let mut f = Function::new(FuncId::new(2), "demoMul", FuncTyId::new(2), BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    let mut push = |b: &mut Block, inst: Inst, r: u32| {
        b.body
            .push(InstrNode::new(inst).with_result(ValueId::new(r)));
    };
    push(
        &mut b,
        Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(2),
        },
        0,
    );
    push(
        &mut b,
        Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0)],
        },
        1,
    );
    push(
        &mut b,
        Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(3),
        },
        2,
    );
    push(
        &mut b,
        Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(2)],
        },
        3,
    );
    push(
        &mut b,
        Inst::Call {
            callee: FuncId::new(1),
            args: vec![ValueId::new(1), ValueId::new(3)],
        },
        4,
    );
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));
    f.blocks.push(b);
    m.add_function(f);

    // Source: Nat.mul 2 3 (bignum). Both sides denote Nat.mul 2 3.
    let src = KExpr::apps(
        KExpr::const_str("Nat.mul"),
        [KExpr::nat_lit(2), KExpr::nat_lit(3)],
    );
    let (report, _module) = mint(m, "demoMul", src);
    assert_eq!(
        report.certified,
        vec!["demoMul".to_string()],
        "bignum Nat.mul constant must certify, got: {report:?}"
    );
}
