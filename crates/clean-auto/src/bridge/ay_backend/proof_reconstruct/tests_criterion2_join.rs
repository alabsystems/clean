// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-repository fail-closed checks for the historical Criterion-2
//! overflow-carrier experiment.
//!
//! TrustCG intentionally exposes no production validator replay authority yet,
//! so an externally linked lowering must keep the ordinary checked-overflow
//! path.  Separately, the old C1 reflexivity formula can still be replayed by
//! the proof checker, but its axiomatic BV semantics prevent promotion to a
//! `CertifiedPayload`.  Together these checks prevent test-only synthetic
//! discharge from leaking across the Clean/TrustCG boundary.

use super::certified_proof::{certify_reconstruction, false_expr, NotCertified};
use super::theory_lemma_bv::reconstruct_bv_bitblast;
use super::{ReconstructionResult, ReconstructionStats};
use ay_proof::bv_blast_export::{
    export_bv_blast_proof, BvOp, OperandRef, SliceObligation, SLICE_WIDTH,
};
use clean_kernel::bitvec_slice;
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, CertificationIssue, Declaration, Environment, Expr, FVarId, LocalContext,
    TypeChecker,
};
use trust_ir::proof::ProofFormula;
use trust_ir::{
    Block, BlockId, FuncTy, Function, Inst, InstrNode, Module, OverflowOp, Ty, ValueId,
};

fn overflow_add_i32_module() -> Module {
    let a = ValueId::new(0);
    let b = ValueId::new(1);
    let sum = ValueId::new(2);
    let flag = ValueId::new(3);
    let entry = BlockId::new(0);

    let block = Block {
        id: entry,
        params: vec![(a, Ty::I32), (b, Ty::I32)],
        body: vec![
            InstrNode {
                inst: Inst::Overflow {
                    op: OverflowOp::AddOverflow,
                    ty: Ty::I32,
                    lhs: a,
                    rhs: b,
                },
                results: vec![sum, flag],
                // A public annotation is metadata, not replay authority.
                proofs: vec![trust_ir::proof::ProofAnnotation::NoOverflow],
                span: None,
                proof_context: None,
                scope: None,
            },
            InstrNode {
                inst: Inst::Return { values: vec![sum] },
                results: vec![],
                proofs: vec![],
                span: None,
                proof_context: None,
                scope: None,
            },
        ],
    };

    let mut module = Module::new("criterion2_fail_closed");
    let func_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(
        trust_ir::value::FuncId::new(0),
        "overflow_add_i32",
        func_ty,
        entry,
    );
    func.blocks = vec![block];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn external_trust_cg_lowering_does_not_enable_test_model_authority() {
    let module = overflow_add_i32_module();
    let func = module.functions.first().expect("one function");

    // The fixture is hand-built and carries no codegen license
    // (`body_gate: None`). Since trust-cg WS7.5 (decision gate DG-73) the
    // default policy REFUSES such a body, so the default entry must refuse it
    // by name -- a claim-less body is not lowered by default.
    match trust_cg_lower::translate_function(func, &module) {
        Err(trust_cg_lower::AdapterError::UnlicensedBody { function }) => {
            assert_eq!(function, "overflow_add_i32");
        }
        Err(other) => panic!("a claim-less body must be refused as UnlicensedBody, got {other:?}"),
        Ok(_) => panic!("the default codegen license must refuse a claim-less body (DG-73)"),
    }

    // What this test is about is the overflow path, not the license, so the
    // fixture is lowered under the stated test policy trust-cg documents for
    // hand-built fixtures: claim-less bodies permitted, nothing else changed.
    let permit_claim_less = trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit);
    let (lir_func, proof_ctx) =
        trust_cg_lower::translate_function_with_license(func, &module, &permit_claim_less)
            .expect("lowering succeeds under the stated claim-less test policy");

    let has_guard_overflow = lir_func
        .blocks
        .values()
        .flat_map(|bb| bb.instructions.iter())
        .any(|inst| {
            matches!(
                inst.opcode,
                trust_cg_lower::instructions::Opcode::GuardOverflow { .. }
            )
        });

    assert!(
        !has_guard_overflow,
        "production dependency builds must keep the checked-overflow path until \
         exact validator replay authority is wired"
    );
    assert!(
        proof_ctx.synthesized_discharged.is_empty(),
        "a public NoOverflow label must not synthesize discharged authority"
    );
}

fn slice_obligation_from_formula(formula: &ProofFormula) -> Result<SliceObligation, String> {
    if formula.schema != "smtlib2" {
        return Err(format!("unsupported schema: {}", formula.schema));
    }
    let expected_sort = format!("(_ BitVec {SLICE_WIDTH})");
    if formula.sort.as_deref() != Some(expected_sort.as_str()) {
        return Err(format!("unsupported sort: {:?}", formula.sort));
    }
    let smt = formula
        .smtlib
        .as_deref()
        .ok_or_else(|| "missing SMT-LIB formula".to_string())?;
    let op = if smt.contains("bvadd") {
        BvOp::Add
    } else if smt.contains("bvsub") {
        BvOp::Sub
    } else {
        return Err(format!("unsupported BV operation: {smt}"));
    };
    let obligation = SliceObligation {
        width: SLICE_WIDTH,
        op,
        lhs_args: [OperandRef::A, OperandRef::B],
        rhs_args: [OperandRef::A, OperandRef::B],
    };
    if obligation.render_smt() != smt {
        return Err("formula is outside the exact reflexivity fragment".to_string());
    }
    Ok(obligation)
}

fn slice_env() -> Environment {
    let mut env = Environment::new();
    env.init_bv_slice().expect("init_bv_slice");
    env.init_classical().expect("init_classical");
    let bv = Expr::const_str(bitvec_slice::names::BV);
    for n in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(n),
            level_params: vec![],
            type_: bv.clone(),
        })
        .expect("slice operand");
    }
    env
}

#[test]
fn historical_reflexivity_formula_checks_but_cannot_certify() {
    let env = slice_env();
    let formula = trust_cg_lower::ProofContext::overflow_carrier_reflexivity_formula(
        trust_cg_ir::OverflowOp::SignedAdd,
        SLICE_WIDTH as u16,
    );
    let obligation =
        slice_obligation_from_formula(&formula).expect("exact historical formula converts");
    let proof = export_bv_blast_proof(obligation).expect("reflexivity negation is UNSAT");
    let neg = FVarId::new(900);
    let rec = reconstruct_bv_bitblast(&proof, neg).expect("reconstruct reflexivity proof");

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        neg,
        Name::from_string("h_neg"),
        rec.negated_goal.clone(),
        BinderInfo::Default,
    );
    let result = ReconstructionResult {
        proof_term: Some(rec.proof_term),
        negated_goal_fvar: Some(neg),
        compound_witness_fvars: Vec::new(),
        derives_empty_clause: true,
        trust_subterm_count: 0,
        residual: crate::bridge::ay_backend::reconstruction_quality::ResidualTrustSummary::empty(),
        stats: ReconstructionStats::default(),
    };

    let tc = TypeChecker::with_context(&env, ctx.clone());
    tc.check_type(
        result.proof_term.as_ref().expect("reconstructed term"),
        &false_expr(),
    )
    .expect("the proof checker accepts the reconstructed tautology");

    let err = certify_reconstruction(&result, &env, &ctx)
        .expect_err("axiomatic BV semantics must block certification");
    assert!(matches!(
        err,
        NotCertified::AuthorityRejected { ref issues }
            if issues.iter().any(|issue| matches!(
                issue,
                CertificationIssue::NonFoundationalAxiom { name }
                    if name.to_string().starts_with("Clean.BV")
            ))
    ));
}
