// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the backend translation-validation minter: the corpus decl is
//! kernel-certified end-to-end, a deliberate post-emit miscompile is REFUSED
//! (the whole point — a real wrong-code detector), and out-of-fragment decls
//! are silently skipped (no obligation, never a fake cert).
//!
//! NOTE: most of these tests assert the MINT side (obligation + certificate
//! shape, kernel accept/refuse). The independent CONSUMER-side acceptance — a
//! minted module validating `Certified` under `trust_ir_build::validate_module`
//! — is re-derived in trust-ir's own TCB (its `clean-tv-anchor` suite
//! re-derives the denotation and re-runs the kernel), and is ALSO run here
//! against the trust-ir this workspace PINS for every Fragment-4 heap corpus
//! program (`assert_pinned_trust_ir_rechecks`: accepted as minted, refused
//! with its `Release` dropped) and by the WS6.6 child module for the
//! arithmetic shapes. Fail-closed direction either way: an older validator
//! REJECTS an unknown anchor or shape rather than faith-accepting it — which
//! is exactly how the pre-2026-09-29 pin refused every heap certificate
//! without any test here noticing.

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

#[test]
fn test_codegen_license_refuses_duplicate_function_ids() {
    let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("corpus decl lowers");
    let mut unproved = module.functions[0].clone();
    unproved.name = "unproved_other".to_string();
    for node in &mut unproved.blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut node.inst {
            if *op == BinOp::Add {
                *op = BinOp::Sub;
            }
        }
    }
    module.functions.push(unproved);
    let before = module.clone();
    let report =
        certify_backend_translation(&mut module, &[("tv_demo".to_string(), tv_demo_original())]);
    assert!(
        report.certified.is_empty(),
        "duplicate identity minted authority: {report:?}"
    );
    assert!(
        report
            .refused
            .iter()
            .any(|(_, reason)| reason.contains("duplicate function id")),
        "{report:?}"
    );
    assert_eq!(
        module, before,
        "identity refusal must leave every license and certificate unchanged"
    );
}

#[test]
fn test_codegen_license_refuses_duplicate_function_names() {
    let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("corpus decl lowers");
    let mut other = module.functions[0].clone();
    other.id = FuncId::new(other.id.index() + 1);
    module.functions.push(other);
    let before = module.clone();
    let report =
        certify_backend_translation(&mut module, &[("tv_demo".to_string(), tv_demo_original())]);
    assert!(
        report.certified.is_empty(),
        "ambiguous source binding minted authority: {report:?}"
    );
    assert!(
        report
            .refused
            .iter()
            .any(|(_, reason)| reason.contains("duplicate function name")),
        "{report:?}"
    );
    assert_eq!(
        module, before,
        "identity refusal must leave every license and certificate unchanged"
    );
}

#[test]
fn test_codegen_license_refuses_duplicate_source_names() {
    let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("corpus decl lowers");
    let before = module.clone();
    let report = certify_backend_translation(
        &mut module,
        &[
            ("tv_demo".to_string(), tv_demo_original()),
            ("tv_demo".to_string(), tv_demo_original()),
        ],
    );
    assert!(
        report.certified.is_empty(),
        "ambiguous originals minted authority: {report:?}"
    );
    assert!(
        report
            .refused
            .iter()
            .any(|(_, reason)| reason.contains("duplicate source name")),
        "{report:?}"
    );
    assert_eq!(
        module, before,
        "identity refusal must leave every license and certificate unchanged"
    );
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
    assert_eq!(
        obl.site, None,
        "whole-function TV must not claim an instruction site"
    );

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
    let rhs =
        denote_source(&tv_demo_original(), 32, &[], &RecordVocab::empty()).expect("in-fragment");
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
    // `external: None` is asserted, not wildcarded: the composition is
    // module-local (helper is in THIS module), and the v41 cross-crate form
    // would move the claim to an import this module does not have.
    assert!(
        caller_certs.iter().any(|c| matches!(
            &c.evidence,
            ProofEvidence::InheritedFromCallee {
                callee,
                obligation,
                external: None,
            } if *callee == helper_fid && *obligation == helper_obl.id
        )),
        "caller must inherit helper's TV obligation (compositional grounding, module-local), got: {caller_certs:?}"
    );
}

/// CODEGEN LICENSE (trust-ir binary v41): `Function::body_gate` is
/// `Gated { "clean-kernel-tv" }` on exactly the bodies this minter
/// kernel-certified and `Ungated` on every other emitted body, and the
/// consumer-side interlock `trust_ir_build::validate_module_for_codegen`
/// accepts an all-certified module while refusing a partially-certified one
/// with `UngatedBodyForCodegen` — never the grandfathered
/// `UnlicensedBodyForCodegen`, because this producer makes a claim on every
/// body. Every module here comes from the real emitter + the real minter.
#[test]
fn test_codegen_license_gated_iff_kernel_certified() {
    use trust_ir::BodyGate;
    use trust_ir_build::{validate_module_for_codegen, ValidationError};
    // The minted license, evidence included, re-derived from the module.
    let gated = |m: &Module, n: &str| {
        let f = m
            .functions
            .iter()
            .find(|f| f.name == n)
            .unwrap_or_else(|| panic!("no emitted function `{n}`"));
        let expected = kernel_tv_gate(m, f.id);
        assert!(
            expected.is_some(),
            "`{n}` has one Certified TV row and a digest"
        );
        expected
    };
    let by_name = |m: &Module, n: &str| {
        m.functions
            .iter()
            .find(|f| f.name == n)
            .cloned()
            .unwrap_or_else(|| panic!("no emitted function `{n}`"))
    };

    // (a) Fresh from the emitter, before any gate ran: both bodies carry the
    // AFFIRMATIVE `Ungated` claim, so the interlock refuses each by name —
    // and reports nothing as merely "unlicensed".
    let (helper, caller) = helper_caller_decls();
    let mut module = emit_trust_ir(&[helper, caller]).expect("lowers");
    for f in &module.functions {
        assert!(!f.is_declaration(), "`{}` has a body", f.name);
        assert_eq!(f.body_gate, Some(BodyGate::Ungated), "`{}`", f.name);
    }
    let refused: Vec<String> = validate_module_for_codegen(&module)
        .into_iter()
        .map(|e| match e {
            ValidationError::UngatedBodyForCodegen { name, .. } => name,
            other => panic!("only UngatedBodyForCodegen expected, got {other:?}"),
        })
        .collect();
    assert_eq!(refused, ["helper", "caller"]);

    // (b) Certify the helper ONLY: its body is licensed by the kernel
    // judgment, the caller's (never offered, never judged) stays `Ungated`,
    // and the interlock now refuses exactly the caller.
    let report =
        certify_backend_translation(&mut module, &[("helper".to_string(), helper_original())]);
    assert_eq!(report.certified, vec!["helper".to_string()], "{report:?}");
    assert_eq!(
        by_name(&module, "helper").body_gate,
        gated(&module, "helper")
    );
    assert_eq!(
        by_name(&module, "caller").body_gate,
        Some(BodyGate::Ungated)
    );
    let errors = validate_module_for_codegen(&module);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::UngatedBodyForCodegen { name, .. }] if name == "caller"
        ),
        "exactly the uncertified body must be refused, got: {errors:?}"
    );

    // (c) Every body certified (fresh emit, both originals): the interlock —
    // structural validation, the license, AND codegen lowerability — accepts
    // the module outright.
    let (helper, caller) = helper_caller_decls();
    let mut module = emit_trust_ir(&[helper, caller]).expect("lowers");
    let report = certify_backend_translation(
        &mut module,
        &[
            ("helper".to_string(), helper_original()),
            ("caller".to_string(), caller_original()),
        ],
    );
    assert_eq!(report.certified.len(), 2, "{report:?}");
    for f in &module.functions {
        assert_eq!(
            f.body_gate,
            gated(&module, &f.name),
            "`{}` was certified, so it is licensed",
            f.name
        );
    }
    let errors = validate_module_for_codegen(&module);
    assert!(
        errors.is_empty(),
        "all-certified module must pass: {errors:?}"
    );

    // The license is wire-carried: the v41 binary codec round-trips both the
    // `Gated` authority and the `Ungated` refusal without laundering either.
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
    let decoded = trust_ir::binary::deserialize_module(&bytes).expect("v41 blob decodes");
    assert_eq!(
        decoded, module,
        "binary round-trip changed the licensed module"
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
                    value: Constant::Int(1),
                    ..
                }
            )
        })
        .expect("caller has the const 1");
    if let Inst::Const { value, .. } = &mut one.inst {
        *value = Constant::Int(2);
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
        abi: None,
    });
    let mut func = Function::new(FuncId::new(0), "cf", FuncTyId::new(0), BlockId::new(0));
    func.producer = Some(Producer::Clean);

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
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
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
        site: None,
        spec: None,
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

fn existing_proof_obligation(id: u32) -> ProofObligation {
    ProofObligation {
        id: ProofId::new(id),
        kind: ObligationKind::MemorySafety,
        status: ProofStatus::Pending,
        description: "pre-existing allocation boundary".to_string(),
        formula: None,
        function: None,
        source: None,
        site: None,
        spec: None,
    }
}

#[test]
fn test_mint_proof_id_exhaustion_refuses_without_wrapping_or_mutation() {
    let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("lowers");
    module.proof_obligations.extend([
        existing_proof_obligation(0),
        existing_proof_obligation(u32::MAX),
    ]);
    let before = module.clone();
    let report =
        certify_backend_translation(&mut module, &[("tv_demo".to_string(), tv_demo_original())]);
    assert!(report.certified.is_empty(), "{report:?}");
    assert_eq!(report.refused.len(), 1, "{report:?}");
    assert!(report.refused[0].1.contains("id space is exhausted"));
    assert_eq!(module, before);
}

#[test]
fn test_mint_proof_id_last_value_is_usable_once() {
    let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("lowers");
    module
        .proof_obligations
        .push(existing_proof_obligation(u32::MAX - 1));
    let originals = [("tv_demo".to_string(), tv_demo_original())];
    let report = certify_backend_translation(&mut module, &originals);
    assert_eq!(report.certified, ["tv_demo"], "{report:?}");
    assert_eq!(
        module.proof_obligations.last().unwrap().id.index(),
        u32::MAX
    );
    assert_eq!(
        module.proof_certificates.last().unwrap().obligation.index(),
        u32::MAX
    );
    let before = module.clone();
    let report = certify_backend_translation(&mut module, &originals);
    assert!(report.certified.is_empty(), "{report:?}");
    assert_eq!(report.refused.len(), 1, "{report:?}");
    assert_eq!(module, before);
}

#[test]
fn test_mint_proof_id_duplicate_existing_obligation_refuses() {
    let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("lowers");
    module
        .proof_obligations
        .extend([existing_proof_obligation(7), existing_proof_obligation(7)]);
    let before = module.clone();
    let report =
        certify_backend_translation(&mut module, &[("tv_demo".to_string(), tv_demo_original())]);
    assert!(report.certified.is_empty(), "{report:?}");
    assert_eq!(report.refused.len(), 1, "{report:?}");
    assert!(report.refused[0]
        .1
        .contains("duplicate proof obligation id"));
    assert_eq!(module, before);
}

#[test]
fn test_mint_proof_id_orphan_certificate_cannot_bind_to_new_obligation() {
    let mut seed = emit_trust_ir(&[tv_demo_decl()]).expect("lowers");
    let originals = [("tv_demo".to_string(), tv_demo_original())];
    assert_eq!(
        certify_backend_translation(&mut seed, &originals)
            .certified
            .len(),
        1
    );
    let mut module = emit_trust_ir(&[tv_demo_decl()]).expect("lowers");
    module.proof_certificates = seed.proof_certificates;
    let before = module.clone();
    let report = certify_backend_translation(&mut module, &originals);
    assert!(report.certified.is_empty(), "{report:?}");
    assert_eq!(report.refused.len(), 1, "{report:?}");
    assert!(report.refused[0]
        .1
        .contains("certificate references unknown proof obligation"));
    assert_eq!(module, before);
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
// Every corpus cell is a reference-counted `CleanHeap` cell released by ONE
// `Release` of its own result value (trust-ir SPEC "A reference-counted cell
// is released by `Release`, never by `Dealloc`", ratified 2026-09-27). Until
// 2026-09-28 the corpus spelled that release `Dealloc`, which the SPEC now
// calls undefined behaviour; those bodies are refused by name
// (`heap_refuses_dealloc_freed_cell`), never re-meant.
//
// Injection corpus: miscompiled emissions, each REFUSED — by the kernel for
// value-visible bugs (wrong offset, swapped/aliased writes, load-before-store,
// dropped store, wrong projection), by the mint gate's structural balance
// check for Release bugs, by the walker's wrong-emission refusal for a
// `Dealloc`-freed cell, and by the fail-closed walker (an auditable SKIP, no
// cert ever minted) for out-of-fragment shapes.

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
            abi: None,
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
            origin: None,
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

    /// The cell's one release: `Release` of the allocation's own result value
    /// (count 1 in the fragment, so this `Release` frees it).
    fn release(&mut self, ptr: ValueId) {
        self.body.push(InstrNode::new(Inst::Release { ptr }));
    }

    fn finish(mut self, name: &str, ret: ValueId) -> Module {
        self.body
            .push(InstrNode::new(Inst::Return { values: vec![ret] }));
        let mut func = Function::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));
        // A fixture of Clean's emitter output: the minter certifies only
        // Clean-produced bodies (WS6.7(d)).
        func.producer = Some(Producer::Clean);
        let mut block = Block::new(BlockId::new(0));
        for i in 0..self.nparams {
            block
                .params
                .push((ValueId::new(u32::try_from(i).unwrap()), Ty::U32));
        }
        block.body = self.body;
        func.blocks.push(block);
        self.module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
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

/// The program mints: kernel-certified obligation + CleanCic cert attached —
/// and the trust-ir this workspace PINS re-checks that certificate
/// ([`assert_pinned_trust_ir_rechecks`]).
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
    assert_pinned_trust_ir_rechecks(&module, name);
}

/// CONSUMER SIDE, at the PINNED trust-ir: `trust_ir_build::validate_module`
/// re-derives the emitted denotation through its own `clean_backend_tv`
/// mirror, re-runs the kernel judgment and the alloc/release balance, and
/// must ACCEPT the Clean-minted heap certificate with no error at all. Its
/// tampered twin — the same minted module with every `Release` dropped after
/// minting — must be REFUSED by that balance, because the value equation
/// cannot see a release.
///
/// Why this lives here: until the 2026-09-29 pin move Clean pinned trust-ir
/// `c603897b`, which predates trust-ir `2a4e6eb8` (SPEC "A reference-counted
/// cell is released by `Release`, never by `Dealloc`"). The re-checker at that
/// pin still balanced `Dealloc` and REFUSED every `Release`-spelled heap
/// certificate Clean mints ("instruction Release ... is outside the TV
/// fragment"): fail-closed, but none of Clean's own heap certificates could
/// be re-checked at its own pin, and no Clean test noticed. Every heap corpus
/// program goes through this helper, so a pin that stops accepting them — or
/// one that stops refusing the twin — fails here.
#[track_caller]
fn assert_pinned_trust_ir_rechecks(minted: &Module, name: &str) {
    let errors = trust_ir_build::validate_module(minted);
    assert!(
        errors.is_empty(),
        "`{name}`: the pinned trust-ir must ACCEPT the Clean-minted certificate, got: {errors:?}"
    );

    let mut twin = minted.clone();
    let mut dropped = 0usize;
    for function in &mut twin.functions {
        let mut dropped_here = 0usize;
        for block in &mut function.blocks {
            let before = block.body.len();
            block
                .body
                .retain(|node| !matches!(node.inst, Inst::Release { .. }));
            dropped_here += before - block.body.len();
        }
        dropped += dropped_here;
        if dropped_here > 0 {
            // The edit rewrites the body, so the license's evidence (trust-ir
            // v61) now names the OLD body. Left in place it is refused as
            // `GatedEvidenceMismatch` — pinned separately below; dropped, as
            // every body-rewriting transform must, the re-check refusal is
            // the only one left to name.
            assert!(
                function.invalidate_gate_evidence(),
                "`{name}`: the minted license carried evidence"
            );
        }
    }
    assert!(
        dropped > 0,
        "`{name}`: the twin is vacuous — every heap corpus cell is released"
    );
    let errors = trust_ir_build::validate_module(&twin);
    assert!(
        pinned_recheck_refused(&twin, &errors, "has no Release (dropped Release"),
        "`{name}`: the pinned trust-ir must REFUSE the certificate once its Release is \
         dropped, got: {errors:?}"
    );
}

/// `true` iff `errors` is exactly the pinned `validate_module` REJECTING the
/// one certificate in `module` for the named reason (`because` occurs in it),
/// and nothing else. (Structural validation reports the failed re-check
/// alone; `validate_module_for_codegen` would add the `GatedWithoutEvidence`
/// row that `ws6_6::recheck_refused` pins.)
fn pinned_recheck_refused(
    module: &Module,
    errors: &[trust_ir_build::ValidationError],
    because: &str,
) -> bool {
    let [oid] = module
        .proof_obligations
        .iter()
        .map(|o| o.id.index())
        .collect::<Vec<_>>()[..]
    else {
        return false;
    };
    matches!(
        errors,
        [trust_ir_build::ValidationError::CertifiedCleanCicKernelRecheckFailed {
            obligation,
            reason,
        }] if *obligation == oid && reason.contains(because)
    )
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

/// The MINT GATE refuses structurally (the Release balance cases, and the
/// walker's wrong-emission refusal of a `Dealloc`-freed cell): hard REFUSAL
/// with the auditable reason.
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
    b.release(p);
    let module = b.finish("pair_first", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_certifies(module, "pair_first", src);
}

/// The PINNED trust-ir re-checks a Clean-minted heap certificate for real:
/// `pair_first`'s certificate is ACCEPTED as minted, and each post-mint
/// tamper of the certified body is REFUSED by `validate_module` for its own
/// reason — a retargeted `Load` (value-visible: the re-derived denotation
/// reads field 1, so the re-run kernel judgment fails), the `Release`
/// respelled `Dealloc` (UB on a reference-counted cell under trust-ir's SPEC),
/// and the `Release` dropped (a leak the value equation cannot see). The
/// last one is also what [`assert_pinned_trust_ir_rechecks`] runs on every
/// heap corpus program.
#[test]
fn heap_certificate_is_rechecked_by_the_pinned_trust_ir() {
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
    b.release(p);
    let module = b.finish("pair_first", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    let (report, minted) = mint(module, "pair_first", src);
    assert_eq!(
        report.certified,
        vec!["pair_first".to_string()],
        "{report:?}"
    );
    assert_eq!(
        trust_ir_build::validate_module(&minted),
        Vec::new(),
        "the pinned trust-ir must ACCEPT the certificate as minted"
    );
    assert_eq!(
        trust_ir_build::validate_module_for_codegen(&minted),
        Vec::new(),
        "and the pinned codegen validator accepts the licensed heap body"
    );

    // Each tamper rewrites exactly one node of the certified body, and drops
    // the license's evidence as every body rewrite must (trust-ir v61), so the
    // re-check's refusal is the one named; `stale_license` below pins what a
    // tamper that KEEPS the evidence gets.
    let tamper_keeping_evidence = |edit: &dyn Fn(&mut InstrNode) -> bool| {
        let mut twin = minted.clone();
        let edited = twin.functions[0].blocks[0]
            .body
            .iter_mut()
            .map(edit)
            .filter(|hit| *hit)
            .count();
        assert_eq!(edited, 1, "each tamper rewrites exactly one node");
        twin
    };
    let tamper = |edit: &dyn Fn(&mut InstrNode) -> bool| {
        let mut twin = tamper_keeping_evidence(edit);
        assert!(
            twin.functions[0].invalidate_gate_evidence(),
            "the minted license carried evidence"
        );
        twin
    };

    // (a) Value-visible: the final Load reads field 1 instead of field 0.
    let retargeted = tamper(&|node: &mut InstrNode| match &mut node.inst {
        Inst::Load { ptr, .. } if *ptr == p0 => {
            *ptr = p1;
            true
        }
        _ => false,
    });
    let errors = trust_ir_build::validate_module(&retargeted);
    assert!(
        pinned_recheck_refused(
            &retargeted,
            &errors,
            "kernel REJECTED the translation-validation equation for 'pair_first'"
        ),
        "a retargeted Load must fail the re-run kernel judgment: {errors:?}"
    );
    // The same tamper with the license left as minted: its evidence names
    // the judged body, so it is refused as well, by name.
    let stale_license = tamper_keeping_evidence(&|node: &mut InstrNode| match &mut node.inst {
        Inst::Load { ptr, .. } if *ptr == p0 => {
            *ptr = p1;
            true
        }
        _ => false,
    });
    let errors = trust_ir_build::validate_module(&stale_license);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            trust_ir_build::ValidationError::GatedEvidenceMismatch { function, detail }
                if *function == stale_license.functions[0].id.index()
                    && detail.contains("another body")
        )) && errors.iter().any(|e| matches!(
            e,
            trust_ir_build::ValidationError::CertifiedCleanCicKernelRecheckFailed { .. }
        )),
        "a tamper that keeps the license is refused by its evidence too: {errors:?}"
    );

    // (b) The release respelled `Dealloc`: UB on a `CleanHeap` cell.
    let dealloc = tamper(&|node: &mut InstrNode| match node.inst {
        Inst::Release { ptr } => {
            node.inst = Inst::Dealloc { ptr };
            true
        }
        _ => false,
    });
    let errors = trust_ir_build::validate_module(&dealloc);
    assert!(
        pinned_recheck_refused(&dealloc, &errors, "Dealloc"),
        "a Dealloc-freed cell must be refused by the pinned re-checker: {errors:?}"
    );
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
    b.release(p);
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
    b.release(p);
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
    b.release(p);
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
    b.release(p);
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
    b.release(p);
    b.release(q);
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
    b.release(p);
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
    b.release(p);
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
    b.release(p);
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
    b.release(p);
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
    b.release(p);
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
        origin: None,
    });
    module.func_types.push(FuncTy {
        params: vec![Ty::U32, Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut func = Function::new(
        FuncId::new(0),
        "arm_heap",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    func.producer = Some(Producer::Clean);

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

    // then arm: its OWN alloc/store/load/release choreography.
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
    then_blk.body.push(InstrNode::new(Inst::Release {
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
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

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
    b.release(arr);
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
    b.release(p);
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
    b.release(p);
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
    b.release(p);
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
    b.release(p);
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
    b.release(p);
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
    b.release(p);
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
    b.release(p);
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
    b.release(p);
    let module = b.finish("wrong_proj", r);
    // …but the source projects f1.
    let src = lam_n(
        2,
        sproj("Pair", 1, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_kernel_refuses(module, "wrong_proj", src);
}

/// DROPPED RELEASE: the value equation cannot see a leak — the MINT GATE's
/// structural balance check refuses it.
#[test]
fn heap_refuses_dropped_release() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let r = b.load(p0);
    // (the Release is DROPPED)
    let module = b.finish("leak", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_mint_gate_refuses(module, "leak", src, "has no Release (dropped Release");
}

/// DOUBLED RELEASE: likewise invisible to the value equation — the second
/// `Release` of a count-1 cell is the RC underflow (a double free), and the
/// MINT GATE's structural balance check refuses it.
#[test]
fn heap_refuses_doubled_release() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let r = b.load(p0);
    b.release(p);
    b.release(p); // DOUBLED
    let module = b.finish("double_free", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_mint_gate_refuses(
        module,
        "double_free",
        src,
        "has 2 Releases (doubled Release",
    );
}

/// A `Dealloc`-FREED CELL: the honest `Pair.f0 (Pair.mk a b)` shape, with the
/// cell freed by `Dealloc` — the spelling this corpus used until 2026-09-28.
/// A Fragment-4 cell is a reference-counted `CleanHeap` cell and trust-ir's
/// SPEC makes its `Dealloc` undefined behaviour, so the walker refuses it BY
/// NAME as a wrong emission and the minter REFUSES — a hard error, never the
/// SKIP that `Dealloc` falling into the walker's out-of-fragment refusal would
/// give. The balance gate refuses the same body on its own, behind the walker.
#[test]
fn heap_refuses_dealloc_freed_cell() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let r = b.load(p0);
    b.body.push(InstrNode::new(Inst::Dealloc { ptr: p })); // UB on a CleanHeap cell
    let module = b.finish("dealloc_freed", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );

    // Behind the walker: the balance gate names the Dealloc on its own.
    let reason = alloc_release_balance(&module.functions[0])
        .expect_err("the balance gate refuses a Dealloc of an allocation base");
    assert!(
        reason.contains("freed by Dealloc") && reason.contains("wrong emission"),
        "the balance gate must name the Dealloc, got: {reason}"
    );

    // The minter: the walker's named wrong emission, REFUSED.
    assert_mint_gate_refuses(
        module,
        "dealloc_freed",
        src,
        "Dealloc of a Fragment-4 CleanHeap cell is undefined behaviour",
    );
}

/// Release of a NON-BASE address (a field pointer): fails closed in the
/// walker — the program stays outside the fragment, no cert is minted. The
/// balance gate does not count it (it is not a `HeapAlloc` result), so the
/// walker's own-result check is what keeps it out.
#[test]
fn heap_refuses_release_of_non_base_address() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let r = b.load(p0);
    b.release(p1); // NON-BASE (not the allocation's own result value)
    let module = b.finish("bad_release", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_walker_skips(
        module,
        "bad_release",
        src,
        "Release pointer is not the allocation's own HeapAlloc result value",
    );
}

/// ALIASED SECOND RELEASE (a double free): after the balanced `Release` of
/// the allocation's own result value, a second `Release` spelled through the
/// field pointer is the RC underflow. The balance gate counts only a `Release`
/// of a `HeapAlloc` result, so it sees ONE release and passes; the walker's
/// own-result rule is what keeps this body from certifying.
#[test]
fn heap_refuses_aliased_second_release() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    let r = b.load(p0);
    b.release(p);
    b.release(p0); // the SAME cell again, through an interior pointer
    let module = b.finish("aliased_double_free", r);
    assert_eq!(
        alloc_release_balance(&module.functions[0]),
        Ok(()),
        "the balance gate cannot see an aliased Release — only the walker can"
    );
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_walker_skips(
        module,
        "aliased_double_free",
        src,
        "Release pointer is not the allocation's own HeapAlloc result value",
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
    b.release(p);
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
        abi: None,
    });
    let mut func = Function::new(
        FuncId::new(0),
        "ptr_param",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    func.producer = Some(Producer::Clean);
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
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
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
    b.release(p);
    let module = b.finish("oob_load", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_walker_skips(module, "oob_load", src, "not a recorded live cell");
}

/// LOAD AFTER RELEASE (structural use-after-free): the `Release` freed the
/// count-1 cell, so it is no longer live — fail-closed at mint.
#[test]
fn heap_refuses_load_after_release() {
    let mut b = HeapFx::new(2);
    let pair = b.add_record("Pair", 2);
    let (a, bb) = (b.param(0), b.param(1));
    let p = b.alloc(pair);
    let p0 = b.field_ptr(p, 0);
    b.store(p0, a);
    let p1 = b.field_ptr(p, 4);
    b.store(p1, bb);
    b.release(p);
    let r = b.load(p0); // use-after-free
    let module = b.finish("uaf_load", r);
    let src = lam_n(
        2,
        sproj("Pair", 0, smk("Pair", [KExpr::bvar(1), KExpr::bvar(0)])),
    );
    assert_walker_skips(
        module,
        "uaf_load",
        src,
        "Load touches a released allocation",
    );
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
    b.release(p);
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
    b.release(p);
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
    b.release(p);
    b.release(q);
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
    b.release(p);
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
    let lhs =
        denote_function(&module, &module.functions[0]).expect("ledger program is in-fragment");
    let vocab = RecordVocab::from_module(&module);
    let rhs = denote_source(&src, 32, &[], &vocab).expect("ledger source denotes");
    assert_eq!(lhs.arity, rhs.arity);

    let t0 = Instant::now();
    let mut env = Environment::try_with_prelude().expect("prelude");
    let t_env = t0.elapsed();
    for decl in clean_reflect::heap_vocab_declarations() {
        env.add_decl(decl).expect("heap vocabulary installs");
    }
    let t1 = Instant::now();
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(&tv_theorem_name("ledger_ten")),
        level_params: vec![],
        type_: tv_statement(&[], lhs.arity, &lhs.body, &rhs.body),
        value: tv_proof_term(&[], lhs.arity, &lhs.body),
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
// `UIntN.size` family — is DECIDED but NOT MINTED. The walker holds it to the
// ownership balance (trust-ir SPEC "A reference-counted cell is released by
// `Release`, never by `Dealloc`", clause 4) and the kernel judges its equation
// against the `Nat` source; either refusal is a REFUSED row (a hard compile
// error under `certify_translation`). When both accept, the decl is SKIPPED
// with `FRAGMENT5_NOT_MINTED`: trust-ir's `clean_backend_tv` refuses a `Ptr`
// return, so a certificate would take its whole module down.
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
        abi: None,
    });
    m.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::Ptr],
        is_vararg: false,
        abi: None,
    });
    // Bodyless runtime extern (no blocks => External import).
    m.try_add_function(Function::new(
        FuncId::new(0),
        "clean_box_uint64",
        FuncTyId::new(0),
        BlockId::new(0),
    ))
    .expect("Module::try_add_function: test fixture");
    // demoNat body.
    let mut f = Function::new(FuncId::new(1), "demoNat", FuncTyId::new(1), BlockId::new(0));
    f.producer = Some(Producer::Clean);
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
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

/// `demoNat` with a boxed temporary `%3 = clean_box_uint64 7` built before
/// the `Return`, followed by `releases` `Release`s of it.
fn boxed_nat_const_with_temporary(releases: usize) -> Module {
    let mut module = boxed_nat_const_module(256);
    let body = &mut module.functions[1].blocks[0].body;
    assert!(
        matches!(body[2].inst, Inst::Return { .. }),
        "fixture layout: node 2 of demoNat is the Return"
    );
    let ret = body.pop().expect("the Return");
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(2)),
    );
    body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(2)],
        })
        .with_result(ValueId::new(3)),
    );
    for _ in 0..releases {
        body.push(InstrNode::new(Inst::Release {
            ptr: ValueId::new(3),
        }));
    }
    body.push(ret);
    module
}

/// The decl was DECIDED and not minted: SKIPPED with exactly
/// [`FRAGMENT5_NOT_MINTED`] — which the minter only reaches after the
/// walker's ownership balance and the kernel both accepted it, since either
/// refusal is a REFUSED row — with no obligation, no certificate and no
/// license change. Returns the module for further checks.
#[track_caller]
fn assert_decided_not_minted(module: Module, name: &str, src: KExpr) -> Module {
    let licenses: Vec<_> = module
        .functions
        .iter()
        .map(|f| f.body_gate.clone())
        .collect();
    let (report, module) = mint(module, name, src);
    assert!(
        report.certified.is_empty() && report.refused.is_empty(),
        "a balanced, kernel-accepted Fragment-5 body is neither minted nor refused: {report:?}"
    );
    assert_eq!(
        report.skipped,
        vec![(name.to_string(), FRAGMENT5_NOT_MINTED.to_string())],
        "skipped with the not-minted reason"
    );
    assert!(
        module.proof_obligations.is_empty() && module.proof_certificates.is_empty(),
        "no obligation and no certificate is attached"
    );
    assert_eq!(
        module
            .functions
            .iter()
            .map(|f| f.body_gate.clone())
            .collect::<Vec<_>>(),
        licenses,
        "no license is stamped"
    );
    module
}

/// The walker refuses a Fragment-5 body that breaks the ownership balance,
/// and the minter REFUSES it (`walker REFUSED (structural)`, a hard compile
/// error), whose reason names `class`. Nothing is attached.
#[track_caller]
fn assert_f5_balance_refused(module: Module, name: &str, src: KExpr, class: &str) {
    let (report, module) = mint(module, name, src);
    assert!(report.certified.is_empty(), "must not certify: {report:?}");
    assert!(
        report.refused.iter().any(|(n, r)| n == name
            && r.contains("walker REFUSED (structural)")
            && r.contains("Fragment-5 ownership balance")
            && r.contains(class)),
        "the minter must refuse `{name}` naming `{class}`, got: {report:?}"
    );
    assert!(
        module.proof_obligations.is_empty() && module.proof_certificates.is_empty(),
        "a refusal attaches no obligation/cert"
    );
}

/// A boxed-Nat constant (the `UIntN.size` shape: `clean_box_uint64 256`,
/// source `256`) is DECIDED and not minted: the walker admits it with its
/// balance, the kernel accepts the equation, and nothing is attached. (That
/// the real modules carrying such a body then validate at the pinned
/// trust-ir is pinned over real emission below and in
/// `test_ws5_12_review_sub_closure_validates_with_its_ptr_helper_unminted`;
/// this hand-built fixture carries no target info, which `validate_module`
/// requires of a bodyless runtime import.)
#[test]
fn test_fragment5_boxed_nat_constant_is_kernel_checked_not_minted() {
    let module = boxed_nat_const_module(256);
    let d = denote_function(&module, &module.functions[1])
        .expect("the walker and its ownership balance admit demoNat");
    assert_eq!((d.arity, d.callees.len()), (0, 0));
    assert_decided_not_minted(module, "demoNat", KExpr::nat_lit(256));
}

/// A MISCOMPILED boxed-Nat constant (emitted `clean_box_uint64 255` vs source
/// `256`) is REFUSED by the KERNEL — the Fragment-5 miscompile detector still
/// fires, because the not-minted gate sits AFTER the judgment. No obligation
/// attached.
#[test]
fn test_fragment5_refuses_miscompiled_boxed_nat_constant() {
    let module = boxed_nat_const_module(255);
    let (report, module) = mint(module, "demoNat", KExpr::nat_lit(256));
    assert!(
        report.certified.is_empty() && report.skipped.is_empty(),
        "a miscompiled constant is neither certified nor skipped: {report:?}"
    );
    assert!(
        report
            .refused
            .iter()
            .any(|(n, r)| n == "demoNat" && r.contains("kernel REFUSED the translation equation")),
        "the kernel must REFUSE 255 != 256, got: {report:?}"
    );
    assert!(
        module.proof_obligations.is_empty() && module.proof_certificates.is_empty(),
        "a refusal attaches no obligation/cert"
    );
}

/// A Fragment-5 body that builds a boxed temporary and `Release`s it once —
/// the shape Clean's `dec` lowers to — is balanced: the walker admits it, the
/// Fragment-4 alloc/release gate neither counts nor refuses a `Release` of a
/// call result, and the decl is decided and not minted (never refused).
#[test]
fn test_fragment5_balanced_release_of_a_temporary_is_not_refused() {
    let module = boxed_nat_const_with_temporary(1);
    assert_eq!(
        alloc_release_balance(&module.functions[1]),
        Ok(()),
        "a Release of a call result is neither counted nor refused by the Fragment-4 gate"
    );
    denote_function(&module, &module.functions[1])
        .expect("one Release of the temporary is balanced");
    let module = assert_decided_not_minted(module, "demoNat", KExpr::nat_lit(256));
    assert!(
        module.functions[1].blocks[0]
            .body
            .iter()
            .any(|n| matches!(n.inst, Inst::Release { .. })),
        "the decided body carries the Release"
    );
}

/// MUTANT: the returned box is `Release`d before the `Return` — a use after
/// free the value equation cannot see (it still denotes 256). REFUSED by the
/// walker's balance, never skipped and never minted.
#[test]
fn test_fragment5_refuses_release_of_the_returned_box() {
    let mut module = boxed_nat_const_module(256);
    module.functions[1].blocks[0].body.insert(
        2,
        InstrNode::new(Inst::Release {
            ptr: ValueId::new(1),
        }),
    );
    assert_f5_balance_refused(
        module,
        "demoNat",
        KExpr::nat_lit(256),
        "after its last reference is gone",
    );
}

/// MUTANT: the temporary is `Release`d twice — a count underflow (double
/// free). REFUSED by the walker's balance.
#[test]
fn test_fragment5_refuses_a_double_release() {
    assert_f5_balance_refused(
        boxed_nat_const_with_temporary(2),
        "demoNat",
        KExpr::nat_lit(256),
        "after its last reference is gone",
    );
}

/// `demoMul = l_Nat_mul (clean_nat_of_u64 2) (clean_nat_of_u64 3)`: two
/// owned references, each consumed once by `l_Nat_mul` — balanced.
fn nat_mul_const_module() -> Module {
    use trust_ir::constant::Constant;
    let mut m = Module::new("f5_nat_mul");
    // ft0 = (u64)->ptr clean_nat_of_u64; ft1 = (ptr,ptr)->ptr l_Nat_mul;
    // ft2 = ()->ptr demoMul
    m.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::Ptr],
        is_vararg: false,
        abi: None,
    });
    m.func_types.push(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr],
        returns: vec![Ty::Ptr],
        is_vararg: false,
        abi: None,
    });
    m.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::Ptr],
        is_vararg: false,
        abi: None,
    });
    m.try_add_function(Function::new(
        FuncId::new(0),
        "clean_nat_of_u64",
        FuncTyId::new(0),
        BlockId::new(0),
    ))
    .expect("Module::try_add_function: test fixture");
    m.try_add_function(Function::new(
        FuncId::new(1),
        "l_Nat_mul",
        FuncTyId::new(1),
        BlockId::new(0),
    ))
    .expect("Module::try_add_function: test fixture");
    let mut f = Function::new(FuncId::new(2), "demoMul", FuncTyId::new(2), BlockId::new(0));
    f.producer = Some(Producer::Clean);
    let mut b = Block::new(BlockId::new(0));
    let push = |b: &mut Block, inst: Inst, r: u32| {
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
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

/// The bignum `Nat` arithmetic rows are faithful and decided: `clean_nat_of_u64
/// 2 * clean_nat_of_u64 3` (via `l_Nat_mul`) denotes `Nat.mul 2 3`, which the
/// kernel accepts against the source `Nat.mul 2 3` (no `u64` wrap shortcut —
/// plain bignum) and refuses against `Nat.mul 2 4`. Decided, not minted.
#[test]
fn test_fragment5_nat_mul_constant_is_kernel_checked_not_minted() {
    let nat_mul = |a: u64, b: u64| {
        KExpr::apps(
            KExpr::const_str("Nat.mul"),
            [KExpr::nat_lit(a), KExpr::nat_lit(b)],
        )
    };
    assert_decided_not_minted(nat_mul_const_module(), "demoMul", nat_mul(2, 3));
    let (report, _) = mint(nat_mul_const_module(), "demoMul", nat_mul(2, 4));
    assert!(
        report
            .refused
            .iter()
            .any(|(n, r)| n == "demoMul" && r.contains("kernel REFUSED the translation equation")),
        "the kernel must refuse 2 * 3 = 2 * 4: {report:?}"
    );
}

// --- Fragment-5 over REAL emission --------------------------------------------

/// `clean compile`'s `-O0`, `-O1` and `-O2` pipelines
/// (`cmd_compile::pipeline_config_from_opt_level`).
fn f5_levels() -> [(&'static str, crate::pass_manager::PipelineConfig); 3] {
    use crate::pass_manager::PipelineConfig;
    [
        ("-O0", crate::rc_repair::e2e_support::o0()),
        ("-O1", PipelineConfig::default()),
        (
            "-O2",
            PipelineConfig {
                opt: crate::opt::OptConfig::aggressive(),
                rc: crate::rc::RCConfig::aggressive(),
                boxing: crate::boxing::BoxingConfig::default(),
            },
        ),
    ]
}

/// The verified `ExternCalls` emission every shipping consumer uses, with
/// the kernel-TV mint on.
fn f5_config(module_name: &str) -> crate::emit_trust_ir::TrustIrConfig {
    crate::emit_trust_ir::TrustIrConfig {
        module_name: module_name.to_string(),
        use_clean_dialect: true,
        runtime_lowering: crate::emit_trust_ir::RuntimeLowering::ExternCalls,
        certify_translation: true,
        ..crate::emit_trust_ir::TrustIrConfig::default()
    }
}

/// The bodied function `name` of `module`, if its signature is Fragment-5's
/// `() -> Ptr`.
fn f5_body<'m>(module: &'m Module, name: &str) -> Option<&'m Function> {
    module
        .functions
        .iter()
        .find(|f| f.name == name && !f.blocks.is_empty())
        .filter(|f| is_f5_signature(module, f))
}

fn is_f5_signature(module: &Module, f: &Function) -> bool {
    module
        .func_types
        .get(f.ty.as_usize())
        .is_some_and(|ft| ft.params.is_empty() && ft.returns.as_slice() == [Ty::Ptr])
}

fn rc_ops(f: &Function) -> usize {
    f.blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| matches!(n.inst, Inst::Retain { .. } | Inst::Release { .. }))
        .count()
}

/// Ordinary user sources whose optimized emission is an RC-BEARING
/// Fragment-5 body — the class the prelude census below contains none of.
/// Measured shapes (2026-09-29): `nat_big; retain; mul(x, x)` (`f5K2`),
/// `UInt64.size(); retain; mul(h, h)` (`f5SizeLet`, `f5SizeMul`), `retain;
/// sub(x, x)` (`f5BigSub`, `f5Size8Sub`), `UInt64.size(); retain; add(h, h)`
/// after CSE (`f5SizeCse`), `retain; retain; mul(x, x); add(x, r)`
/// (`f5BigAddMul`).
const F5_RC_BEARING_SOURCES: &[(&str, &str)] = &[
    (
        "f5K2",
        "def f5K2 : Nat := let x := 18446744073709551616; x * x\n",
    ),
    (
        "f5SizeLet",
        "def f5SizeLet : Nat := let x := UInt64.size; x * x\n",
    ),
    (
        "f5SizeMul",
        "def f5SizeMul : Nat := UInt64.size * UInt64.size\n",
    ),
    (
        "f5BigSub",
        "def f5BigSub : Nat := let x := 18446744073709551616; x - x\n",
    ),
    (
        "f5Size8Sub",
        "def f5Size8Sub : Nat := let x := UInt8.size; x - x\n",
    ),
    (
        "f5SizeCse",
        "def f5SizeCse : Nat := let x := UInt64.size; let y := UInt64.size; x + y\n",
    ),
    (
        "f5BigAddMul",
        "def f5BigAddMul : Nat := let x := 18446744073709551616; x + x * x\n",
    ),
];

/// REAL PIPELINE GUARD for the RC-bearing Fragment-5 class. The ownership
/// balance decides bodies the kernel never judges (every root here is a
/// source-side skip), so a regression in the emitter or in the balance would
/// surface as a hard compile error in user builds — this test is what makes
/// "the balance refuses no real producer output" a test-rung claim. Over the
/// seven sources at `-O1` and `-O2`: the verified emit does not refuse; each
/// root's emitted body is a Fragment-5 body the walker ADMITS (balance
/// included) and carries at least one `Retain`; the root is not certified;
/// no `Ptr`-returning row is certified; and the pinned `validate_module`
/// accepts the module.
#[test]
fn test_fragment5_rc_bearing_user_bodies_are_balanced_and_unminted() {
    use crate::pass_manager::compile_lcnf_to_trust_ir_with_report;
    use crate::rc_repair::e2e_support::{closure_decls_of, elaborated_env_with};

    let mut rc_bearing = 0usize;
    for (root, source) in F5_RC_BEARING_SOURCES {
        let env = elaborated_env_with(source);
        for (level, pipeline) in f5_levels().into_iter().skip(1) {
            let decls = closure_decls_of(&env, &pipeline, &[root]);
            let (module, report) =
                compile_lcnf_to_trust_ir_with_report(&decls, &env, &pipeline, &f5_config("f5_rc"))
                    .unwrap_or_else(|e| {
                        panic!("{root} {level}: the verified emit must not refuse: {e}")
                    });
            let body = f5_body(&module, root)
                .unwrap_or_else(|| panic!("{root} {level}: the root emits a `() -> Ptr` body"));
            let retains = body
                .blocks
                .iter()
                .flat_map(|b| &b.body)
                .filter(|n| matches!(n.inst, Inst::Retain { .. }))
                .count();
            assert!(
                retains >= 1,
                "{root} {level}: the root body is RC-bearing (else this guard is vacuous)"
            );
            denote_function(&module, body).unwrap_or_else(|e| {
                panic!("{root} {level}: the walker and its balance must admit the body: {e}")
            });
            assert!(
                !report.certified.iter().any(|n| n == root),
                "{root} {level}: the root is not certified: {report:?}"
            );
            let ptr_certified: Vec<&String> = report
                .certified
                .iter()
                .filter(|n| f5_body(&module, n).is_some())
                .collect();
            assert!(
                ptr_certified.is_empty(),
                "{root} {level}: no Fragment-5 row is certified: {ptr_certified:?}"
            );
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{root} {level}: {errors:?}");
            let why = report
                .skipped
                .iter()
                .find(|(n, _)| n == root)
                .map_or("<no skip row>", |(_, r)| r.as_str());
            eprintln!("{root} {level}: {retains} Retain(s); root skipped: {why}");
            rc_bearing += 1;
        }
    }
    assert_eq!(
        rc_bearing,
        2 * F5_RC_BEARING_SOURCES.len(),
        "every source was measured at both optimizing levels"
    );
}

/// CENSUS over the prelude population (each computable prelude decl its own
/// `ExternCalls` module, the trust-cg census's per-decl shape) at `-O0`,
/// `-O1` and `-O2`: no module is refused by the mint, no Fragment-5 (`() ->
/// Ptr`) row is certified, the four `UInt{8,16,32,64}.size` rows — the only
/// Fragment-5 roots the kernel accepts, and until 2026-09-29 the only
/// Fragment-5 certificates minted (4 per level, each refused with its module
/// by the pinned `validate_module`) — are SKIPPED with
/// [`FRAGMENT5_NOT_MINTED`], the walker admits at least 300 Fragment-5 bodies
/// at `-O1` (measured 327), and `validate_module` accepts every module.
///
/// VACUOUS for the RC-bearing class: no prelude Fragment-5 body carries a
/// `Retain` or `Release` (measured `rc_bearing=0` at every level), which is
/// why `test_fragment5_rc_bearing_user_bodies_are_balanced_and_unminted`
/// exists.
#[test]
fn test_fragment5_prelude_population_is_balanced_and_unminted() {
    use crate::emit_trust_ir::TrustIrError;
    use crate::pass_manager::{compile_lcnf_to_trust_ir_with_report, PipelineError};
    use crate::to_lcnf::constant_to_decl;

    const SIZE_ROWS: [&str; 4] = ["UInt8.size", "UInt16.size", "UInt32.size", "UInt64.size"];
    let mut env = Environment::with_prelude();
    let _ = env.init_io_ops();
    let infos: Vec<clean_kernel::ConstantInfo> = env.constants().cloned().collect();
    let config = f5_config("f5_census");
    for (level, pipeline) in f5_levels() {
        let (mut modules, mut admitted, mut rc_bearing) = (0usize, 0usize, 0usize);
        let mut refused: Vec<String> = Vec::new();
        let mut ptr_certified: Vec<String> = Vec::new();
        let mut invalid: Vec<String> = Vec::new();
        let mut not_minted: BTreeSet<String> = BTreeSet::new();
        for info in &infos {
            let Ok(Some(decl)) = constant_to_decl(&env, info) else {
                continue;
            };
            let (module, report) = match compile_lcnf_to_trust_ir_with_report(
                std::slice::from_ref(&decl),
                &env,
                &pipeline,
                &config,
            ) {
                Ok(pair) => pair,
                Err(PipelineError::TrustIr(TrustIrError::TranslationRefused(rows))) => {
                    eprintln!("F5_MODULE\t{level}\t{}\tREFUSED\t{rows:?}", info.name);
                    refused.push(format!("{}: {rows:?}", info.name));
                    continue;
                }
                // Outside the census: a construct the emitter does not lower.
                Err(err) => {
                    eprintln!("F5_MODULE\t{level}\t{}\tOUTSIDE\t{err:?}", info.name);
                    continue;
                }
            };
            eprintln!("F5_MODULE\t{level}\t{}\tEMITTED", info.name);
            modules += 1;
            for f in module
                .functions
                .iter()
                .filter(|f| !f.blocks.is_empty() && is_f5_signature(&module, f))
            {
                let denotation = denote_function(&module, f);
                eprintln!(
                    "F5_ROW\t{level}\t{}\t{}\t{:?}",
                    info.name,
                    f.name,
                    denotation.as_ref().map(|_| ())
                );
                if denotation.is_ok() {
                    admitted += 1;
                    if rc_ops(f) > 0 {
                        rc_bearing += 1;
                    }
                }
            }
            ptr_certified.extend(
                report
                    .certified
                    .iter()
                    .filter(|n| f5_body(&module, n).is_some())
                    .cloned(),
            );
            not_minted.extend(
                report
                    .skipped
                    .iter()
                    .filter(|(_, r)| r == FRAGMENT5_NOT_MINTED)
                    .map(|(n, _)| n.clone()),
            );
            if !trust_ir_build::validate_module(&module).is_empty() {
                invalid.push(info.name.to_string());
            }
        }
        eprintln!(
            "{level}: modules={modules} admittedF5={admitted} rc_bearing={rc_bearing} \
             not_minted={not_minted:?} ptr_certified={} refused={} invalid={}",
            ptr_certified.len(),
            refused.len(),
            invalid.len()
        );
        assert!(
            modules > 500,
            "{level}: only {modules} prelude modules emitted"
        );
        assert!(
            refused.is_empty(),
            "{level}: the balance or the kernel refused real emission: {refused:?}"
        );
        assert!(
            ptr_certified.is_empty(),
            "{level}: a Fragment-5 row was minted: {ptr_certified:?}"
        );
        assert!(
            invalid.is_empty(),
            "{level}: validate_module refused {} module(s): {:?}",
            invalid.len(),
            &invalid[..invalid.len().min(10)]
        );
        for row in SIZE_ROWS {
            assert!(
                not_minted.contains(row),
                "{level}: `{row}` must be decided and not minted: {not_minted:?}"
            );
        }
        if level == "-O1" {
            assert!(
                admitted >= 300,
                "{level}: only {admitted} admitted Fragment-5 bodies (measured 327)"
            );
        }
    }
}

/// WS6.6 — the kernel-TV fragment widening (source-side `let`, the
/// pin-cycle mutation control, the shared golden fixture).
#[path = "emit_trust_ir_tv_ws6_6_tests.rs"]
mod ws6_6;

#[path = "emit_trust_ir_tv_ws6_7_tests.rs"]
mod ws6_7;
