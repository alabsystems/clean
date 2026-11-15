// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS5.12 — Clean `let` gets its kernel-TV companion (F-097, the `let` half).
//! A child of `emit_trust_ir::tests`, so the `trust-ir-backend-lib` gate leg
//! (`-- emit_trust_ir`) runs it.
//!
//! The proof program's Part A-Lean probe p03 (`def sqLet (a : UInt64) :
//! UInt64 := let t := a + 1; t * t`) measured three GAP rows at the trust
//! clean-origin island (`reports/2026-09-17-two-language-proof-program/parta/
//! out/*/features.txt`): `a.lean.let.emit` (verified emit refused: "clean-origin
//! evidence disagreement … the expected kernel-TV companion is missing"),
//! `a.lean.let.carried` (no `Producer::Clean` body carried, the def only a
//! body-less declaration) and `a.lean.let.exec` (the interpreter traps at
//! that declaration). Every one of them was the SOURCE denoter's missing
//! `let` rule, which WS6.6 supplies (`clean_reflect::denote_source` zeta).
//! This file ports each row as an in-repo test named after it, on the Clean
//! producer's own pipeline (`clean compile -O1`/`-O2`, verification ON, the
//! kernel-TV mint DEFAULT-ON), where the same rule is what decides them:
//!
//! * `gap_a_lean_let_emit_flips` — the verified emit no longer refuses: the
//!   p03 source lowers and mints with `sqLet` CERTIFIED (the clean-side
//!   analogue of the island's fatal companion-missing path is the
//!   `TranslationRefused` error, which does not fire);
//! * `gap_a_lean_let_carried_flips` — the module CARRIES the row: a
//!   `Certified` `TranslationValidation` obligation scoped to `sqLet`, a
//!   `CleanCic` certificate re-checkable through the `clean_backend_tv`
//!   anchor, the body licensed `Gated { clean-kernel-tv }`, and
//!   `validate_module` (the in-process kernel re-check) accepts it;
//! * `gap_a_lean_let_exec_flips` — the reference interpreter EXECUTES the
//!   carried body: `sqLet a = (a + 1)^2 mod 2^64` on and across the wrap.
//!
//! Plus the increment's negative twin through the same pipeline: a `let`
//! whose bound value is a non-wrapping op (`a / 2`) stays UNCERTIFIED and
//! UNLICENSED with its existing skip class — the skip names the op, never the
//! `let` — so the widening admits exactly the shape it claims.

use super::*;
use crate::pass_manager::{compile_lcnf_to_trust_ir_with_report, PipelineConfig};
use crate::rc_repair::e2e_support::{closure_decls_of, elaborated_env_with, o0};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::proof::{ObligationKind, ProofEvidence, ProofStatus};
use trust_ir::ty::Ty;

/// p03 verbatim (`parta-lean/probes/p03_let.lean`).
const P03_SOURCE: &str = "def sqLet (a : UInt64) : UInt64 := let t := a + 1; t * t\n";

/// The negative twin: the let-bound value is a NON-WRAPPING op the fragment
/// does not denote on either side.
const DIV_LET_SOURCE: &str = "def divLet (a : UInt64) : UInt64 := let t := a / 2; t * t\n";

/// `clean compile -O2`'s pipeline.
fn o2() -> PipelineConfig {
    PipelineConfig {
        opt: crate::opt::OptConfig::aggressive(),
        rc: crate::rc::RCConfig::aggressive(),
        boxing: crate::boxing::BoxingConfig::default(),
    }
}

/// The optimizing levels at which the emitted body is `add; mul; ret`.
fn optimizing() -> [(&'static str, PipelineConfig); 2] {
    [("-O1", PipelineConfig::default()), ("-O2", o2())]
}

/// Verification ON: the kernel-TV mint runs after finalize.
fn verified_config() -> TrustIrConfig {
    TrustIrConfig {
        module_name: "ws5_12".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        certify_translation: true,
        ..TrustIrConfig::default()
    }
}

/// `source`'s `root` closure, lowered and minted at `pipeline`.
fn minted(
    source: &str,
    root: &str,
    pipeline: &PipelineConfig,
) -> Result<(Module, crate::emit_trust_ir_tv::TvMintReport), crate::pass_manager::PipelineError> {
    let env = elaborated_env_with(source);
    let decls = closure_decls_of(&env, pipeline, &[root]);
    compile_lcnf_to_trust_ir_with_report(&decls, &env, pipeline, &verified_config())
}

fn function<'m>(module: &'m Module, name: &str) -> &'m trust_ir::Function {
    module
        .functions
        .iter()
        .find(|f| f.name == name && !f.blocks.is_empty())
        .unwrap_or_else(|| panic!("`{name}` is not defined in the module"))
}

/// Run `name` on one `U64` argument through the reference interpreter.
fn run_u64(module: &Module, name: &str, arg: u64) -> u128 {
    let f = function(module, name);
    let out = Interpreter::with_module(module)
        .execute_function(f, [InterpretValue::int(Ty::U64, i128::from(arg)).unwrap()])
        .unwrap_or_else(|e| panic!("interpreting `{name}`({arg}): {e}"));
    out.returns
        .first()
        .and_then(InterpretValue::as_int)
        .unwrap_or_else(|| panic!("`{name}` must return an integer"))
        .as_unsigned()
}

/// GAP row `a.lean.let.emit` → PASS: the verified emit is not refused, and
/// the mint's verdict on `sqLet` is CERTIFIED (no skip, no refusal) at both
/// optimizing levels. At `-O0` the dynamic class-method path is still an
/// EMITTED-side skip — a skip, never a refusal, so the emit still succeeds.
#[test]
fn gap_a_lean_let_emit_flips() {
    for (level, pipeline) in optimizing() {
        let (_, report) = minted(P03_SOURCE, "sqLet", &pipeline)
            .unwrap_or_else(|e| panic!("{level}: the verified emit must not refuse: {e}"));
        assert!(
            report.certified.iter().any(|n| n == "sqLet"),
            "{level}: sqLet must be kernel-certified: {report:?}"
        );
        assert!(
            !report.skipped.iter().any(|(n, _)| n == "sqLet"),
            "{level}: no skip row for sqLet: {report:?}"
        );
        assert!(report.refused.is_empty(), "{level}: {report:?}");
    }
    let (_, report) = minted(P03_SOURCE, "sqLet", &o0()).expect("-O0 emits");
    let reason = report
        .skipped
        .iter()
        .find(|(n, _)| n == "sqLet")
        .map(|(_, r)| r.as_str())
        .unwrap_or_else(|| panic!("-O0 keeps sqLet an emitted-side skip: {report:?}"));
    assert!(reason.starts_with("emitted side:"), "-O0: {reason}");
    assert!(
        !reason.contains("source construct let"),
        "-O0 must not blame the source `let` any more: {reason}"
    );
}

/// GAP row `a.lean.let.carried` → PASS: the module carries `sqLet` as a
/// defined body with its kernel-TV row — obligation, certificate, license —
/// and the in-process re-check (`validate_module`) accepts the whole module.
#[test]
fn gap_a_lean_let_carried_flips() {
    for (level, pipeline) in optimizing() {
        let (module, _) = minted(P03_SOURCE, "sqLet", &pipeline).expect("emits");
        let f = function(&module, "sqLet");
        assert!(f.body_gate.is_some(), "{level}");
        assert_eq!(
            f.body_gate,
            crate::emit_trust_ir_tv::kernel_tv_gate(&module, f.id),
            "{level}: the body is licensed by the kernel-TV authority, with evidence"
        );

        let rows: Vec<_> = module
            .proof_obligations
            .iter()
            .filter(|o| o.function == Some(f.id))
            .collect();
        assert_eq!(
            rows.len(),
            1,
            "{level}: exactly one obligation scoped to sqLet: {rows:?}"
        );
        let row = rows[0];
        assert_eq!(row.kind, ObligationKind::TranslationValidation, "{level}");
        assert_eq!(row.status, ProofStatus::Certified, "{level}");
        assert!(
            row.formula.is_some(),
            "{level}: the TV row states its claim (importable across a crate boundary)"
        );

        let certs: Vec<_> = module
            .proof_certificates
            .iter()
            .filter(|c| c.obligation == row.id)
            .collect();
        assert_eq!(
            certs.len(),
            1,
            "{level}: one certificate backs the row: {certs:?}"
        );
        match &certs[0].evidence {
            ProofEvidence::CleanCic { kernel_recheck, .. } => {
                let recheck = kernel_recheck
                    .as_ref()
                    .unwrap_or_else(|| panic!("{level}: the certificate names its re-check"));
                assert_eq!(
                    recheck.anchor,
                    clean_reflect::CLEAN_BACKEND_TV_ANCHOR,
                    "{level}"
                );
                assert_eq!(
                    recheck.theorems,
                    vec![clean_reflect::tv_theorem_name("sqLet")],
                    "{level}"
                );
            }
            other => panic!("{level}: the row must be backed by CleanCic evidence, got {other:?}"),
        }

        let errors = validate_module(&module);
        assert!(
            errors.is_empty(),
            "{level}: in-process kernel re-check: {errors:?}"
        );
    }
}

/// GAP row `a.lean.let.exec` → PASS: the carried body executes in the
/// reference interpreter with the kernel-certified meaning
/// `sqLet a = (a + 1)^2 mod 2^64` — below the wrap, across it, and at the
/// boundary where `a + 1` itself wraps to 0.
#[test]
fn gap_a_lean_let_exec_flips() {
    for (level, pipeline) in optimizing() {
        let (module, _) = minted(P03_SOURCE, "sqLet", &pipeline).expect("emits");
        for (a, want) in [
            (0u64, 1u128),
            (6, 49),
            (7, 64),
            (1u64 << 32, (1u128 << 33) + 1),
            (u64::MAX - 1, 1),
            (u64::MAX, 0),
        ] {
            assert_eq!(run_u64(&module, "sqLet", a), want, "{level}: sqLet({a})");
        }
    }
}

/// NEGATIVE TWIN: `let t := a / 2; t * t`. The bound value is a non-wrapping
/// op the fragment does not denote; the `let` rule must not launder it into a
/// certificate. The root stays UNCERTIFIED and UNLICENSED, the module still
/// emits and validates, and the skip names the op — never the `let`.
#[test]
fn test_ws5_12_let_bound_non_wrapping_op_stays_unlicensed() {
    for (level, pipeline) in optimizing() {
        let (module, report) = minted(DIV_LET_SOURCE, "divLet", &pipeline)
            .unwrap_or_else(|e| panic!("{level}: a skip is never a refusal: {e}"));
        assert!(
            !report.certified.iter().any(|n| n == "divLet"),
            "{level}: divLet must not certify: {report:?}"
        );
        let reason = report
            .skipped
            .iter()
            .find(|(n, _)| n == "divLet")
            .map(|(_, r)| r.as_str())
            .unwrap_or_else(|| panic!("{level}: divLet must be skipped: {report:?}"));
        assert!(
            !reason.contains("source construct let") && !reason.contains("let binding"),
            "{level}: the skip must not blame the `let`: {reason}"
        );
        assert!(
            reason.contains("div") || reason.contains("Div") || reason.contains("callee"),
            "{level}: the skip names the division (or the shim call it lowers to): {reason}"
        );
        let f = function(&module, "divLet");
        assert_eq!(f.body_gate, Some(BodyGate::Ungated), "{level}: unlicensed");
        assert!(
            !module
                .proof_obligations
                .iter()
                .any(|o| o.function == Some(f.id)),
            "{level}: no obligation is minted for a skipped root"
        );
        let errors = validate_module(&module);
        assert!(errors.is_empty(), "{level}: {errors:?}");
    }
}

// --- Review (adversarial) ---------------------------------------------------
//
// Shapes the increment did not write, each through the REAL elaborator and
// pipeline, so what the reflect-level fixtures assume about `ExprKind::Let`
// is measured here rather than hand-built: a `let` that SHADOWS the
// parameter, nested lets over two parameters, a dead out-of-fragment value
// the optimizer drops on the emitted side only, and the `have` spelling the
// roadmap's risk line names.

/// `let a := a + 1; a * a` — the inner `a` must win everywhere in the body.
const SHADOW_SOURCE: &str = "def sqShadow (a : UInt64) : UInt64 := let a := a + 1; a * a\n";

/// Nested lets over two parameters, the reflect-level `nested_let_source`
/// shape as the elaborator really builds it (over the add/mul closure; see
/// [`SUB_LET_SOURCE`] for why `-` is kept apart).
const NESTED_SOURCE: &str =
    "def nest (a b : UInt64) : UInt64 := let t := a + 1; let u := t * b; u + a\n";

/// The same nested shape with a SUBTRACTION. The decl closure of `-` at
/// `UInt64` carries a boxed-`Nat` `() -> Ptr` helper (`UInt64.size`,
/// measured). Until 2026-09-29 clean's Fragment-5 mint CERTIFIED that
/// helper, and the pinned trust-ir re-checker — which has no Fragment-5 and
/// refuses any `Ptr` return ("outside the TV fragment") — then failed the
/// WHOLE module, `subLet`'s own valid certificate included (measured
/// 2026-09-20). Fragment-5 is now decided but not minted
/// (`emit_trust_ir_tv::FRAGMENT5_NOT_MINTED`), so the module validates;
/// pinned below.
const SUB_LET_SOURCE: &str =
    "def subLet (a b : UInt64) : UInt64 := let t := a + 1; let u := t * b; u - a\n";

/// A DEAD out-of-fragment value: `-O1`/`-O2` drop the division from the
/// emitted body, so only the eager source-side rule can keep this honest.
const DEAD_DIV_SOURCE: &str = "def deadDiv (a : UInt64) : UInt64 := let t := a / 2; a + 1\n";

/// The roadmap's risk line: p03 spelled with `have`.
const HAVE_SOURCE: &str = "def sqHave (a : UInt64) : UInt64 := have t := a + 1; t * t\n";

/// Run `name` on `args` (all `U64`) through the reference interpreter.
fn run_u64s(module: &Module, name: &str, args: &[u64]) -> u128 {
    let f = function(module, name);
    let out = Interpreter::with_module(module)
        .execute_function(
            f,
            args.iter()
                .map(|&a| InterpretValue::int(Ty::U64, i128::from(a)).unwrap())
                .collect::<Vec<_>>(),
        )
        .unwrap_or_else(|e| panic!("interpreting `{name}`{args:?}: {e}"));
    out.returns
        .first()
        .and_then(InterpretValue::as_int)
        .unwrap_or_else(|| panic!("`{name}` must return an integer"))
        .as_unsigned()
}

/// `root` is CERTIFIED at `level`, the module validates, and the body is
/// licensed by the kernel-TV authority.
fn assert_certified(
    module: &Module,
    report: &crate::emit_trust_ir_tv::TvMintReport,
    root: &str,
    level: &str,
) {
    assert!(
        report.certified.iter().any(|n| n == root),
        "{level}: {root} must be kernel-certified: {report:?}"
    );
    assert!(report.refused.is_empty(), "{level}: {report:?}");
    let f = function(module, root);
    assert!(f.body_gate.is_some(), "{level}");
    assert_eq!(
        f.body_gate,
        crate::emit_trust_ir_tv::kernel_tv_gate(module, f.id),
        "{level}: {root} is licensed, with evidence"
    );
    let errors = validate_module(module);
    assert!(
        errors.is_empty(),
        "{level}: in-process kernel re-check: {errors:?}"
    );
}

#[test]
fn test_ws5_12_review_shadowing_let_certifies_with_the_inner_binding() {
    // A WRONG EMITTED MODULE here would compute with the outer `a` in one of
    // the two uses (`(a+1)*a` = 42 at 6) or both (`a*a` = 36); the kernel
    // equation and the interpreter must both see `(a+1)^2` = 49.
    for (level, pipeline) in optimizing() {
        let (module, report) = minted(SHADOW_SOURCE, "sqShadow", &pipeline)
            .unwrap_or_else(|e| panic!("{level}: the verified emit must not refuse: {e}"));
        assert_certified(&module, &report, "sqShadow", level);
        for (a, want) in [(0u64, 1u128), (6, 49), (u64::MAX, 0)] {
            assert_eq!(
                run_u64(&module, "sqShadow", a),
                want,
                "{level}: sqShadow({a})"
            );
        }
    }
}

#[test]
fn test_ws5_12_review_nested_lets_certify_on_the_real_elaborator() {
    for (level, pipeline) in optimizing() {
        let (module, report) = minted(NESTED_SOURCE, "nest", &pipeline)
            .unwrap_or_else(|e| panic!("{level}: the verified emit must not refuse: {e}"));
        assert_certified(&module, &report, "nest", level);
        // nest a b = ((a + 1) * b) + a  mod 2^64
        for (a, b, want) in [
            (0u64, 0u64, 0u128),
            (2, 3, 11),
            (5, 0, 5),
            (u64::MAX, 7, u128::from(u64::MAX)),
            (u64::MAX - 1, 1, u128::from(u64::MAX) - 2),
        ] {
            assert_eq!(
                run_u64s(&module, "nest", &[a, b]),
                want,
                "{level}: nest({a}, {b})"
            );
        }
    }
}

/// FIXED FINDING (review, 2026-09-20; fixed 2026-09-29): the `-` closure's
/// `Ptr`-returning helper (`UInt64.size`) used to be CERTIFIED by clean's
/// Fragment-5 mint, and the pinned trust-ir re-checker, which has no
/// Fragment-5, refused its certificate and with it the whole module —
/// `subLet`'s own certificate included. Fragment-5 is now decided but not
/// minted, so at `-O1` and `-O2`: `subLet` is certified and licensed
/// `Gated{clean-kernel-tv}`, and the interpreter executes it as
/// `((a + 1) * b) - a mod 2^64`; `UInt64.size` is skipped with
/// [`crate::emit_trust_ir_tv::FRAGMENT5_NOT_MINTED`], carries no obligation
/// and stays `Ungated`; and the pinned `validate_module` accepts the module.
///
/// What this does NOT restore: codegen. trust-cg refuses the module for
/// codegen on the `Ungated` helper body, so Fragment-5 coverage for codegen
/// is nil until trust-ir mirrors the fragment and Clean mints it again.
#[test]
fn test_ws5_12_review_sub_closure_validates_with_its_ptr_helper_unminted() {
    use crate::emit_trust_ir_tv::FRAGMENT5_NOT_MINTED;
    for (level, pipeline) in optimizing() {
        let (module, report) = minted(SUB_LET_SOURCE, "subLet", &pipeline)
            .unwrap_or_else(|e| panic!("{level}: the verified emit must not refuse: {e}"));
        assert!(
            report.certified.iter().any(|n| n == "subLet"),
            "{level}: subLet must be kernel-certified: {report:?}"
        );
        assert!(report.refused.is_empty(), "{level}: {report:?}");
        let f = function(&module, "subLet");
        assert!(f.body_gate.is_some(), "{level}");
        assert_eq!(
            f.body_gate,
            crate::emit_trust_ir_tv::kernel_tv_gate(&module, f.id),
            "{level}: subLet is licensed, with evidence"
        );
        for (a, b, want) in [
            (0u64, 0u64, 0u128),
            (2, 3, 7),
            (5, 0, u128::from(u64::MAX) - 4),
            (u64::MAX, 7, 1),
        ] {
            assert_eq!(
                run_u64s(&module, "subLet", &[a, b]),
                want,
                "{level}: subLet({a}, {b})"
            );
        }

        let helper = function(&module, "UInt64.size");
        assert_eq!(
            module
                .func_types
                .get(helper.ty.as_usize())
                .map(|ft| (ft.params.len(), ft.returns.clone())),
            Some((0, vec![Ty::Ptr])),
            "{level}: UInt64.size is the closure's Fragment-5 `() -> Ptr` helper"
        );
        assert!(
            report
                .skipped
                .iter()
                .any(|(n, r)| n == "UInt64.size" && r == FRAGMENT5_NOT_MINTED),
            "{level}: UInt64.size is decided and not minted: {report:?}"
        );
        assert!(
            !report.certified.iter().any(|n| n == "UInt64.size"),
            "{level}: {report:?}"
        );
        assert_eq!(
            helper.body_gate,
            Some(BodyGate::Ungated),
            "{level}: the unminted helper stays Ungated"
        );
        assert!(
            !module
                .proof_obligations
                .iter()
                .any(|o| o.function == Some(helper.id)),
            "{level}: no obligation is scoped to the helper"
        );

        let errors = validate_module(&module);
        assert!(errors.is_empty(), "{level}: {errors:?}");
    }
}

#[test]
fn test_ws5_12_review_dead_out_of_fragment_let_value_stays_unlicensed() {
    // The optimizer drops `a / 2` from the emitted body (nothing uses `t`),
    // so the emitted side is the in-fragment `add a 1; ret`. A lazy source
    // rule would then CERTIFY a body whose source contains an op the fragment
    // never denoted. The eager rule keeps it a skip naming the division.
    for (level, pipeline) in optimizing() {
        let (module, report) = minted(DEAD_DIV_SOURCE, "deadDiv", &pipeline)
            .unwrap_or_else(|e| panic!("{level}: a skip is never a refusal: {e}"));
        assert!(
            !report.certified.iter().any(|n| n == "deadDiv"),
            "{level}: deadDiv must not certify: {report:?}"
        );
        let reason = report
            .skipped
            .iter()
            .find(|(n, _)| n == "deadDiv")
            .map(|(_, r)| r.as_str())
            .unwrap_or_else(|| panic!("{level}: deadDiv must be skipped: {report:?}"));
        assert!(
            !reason.contains("let binding") && !reason.contains("source construct let"),
            "{level}: the skip must not blame the `let`: {reason}"
        );
        assert!(
            reason.contains("HDiv.hDiv") || reason.contains("div") || reason.contains("callee"),
            "{level}: the skip names the division: {reason}"
        );
        let f = function(&module, "deadDiv");
        assert_eq!(f.body_gate, Some(BodyGate::Ungated), "{level}: unlicensed");
        assert!(
            !module
                .proof_obligations
                .iter()
                .any(|o| o.function == Some(f.id)),
            "{level}: no obligation is minted for a skipped root"
        );
        let errors = validate_module(&module);
        assert!(errors.is_empty(), "{level}: {errors:?}");
    }
}

#[test]
fn test_ws5_12_review_have_spelling_is_measured_as_let() {
    // RISK LINE, MEASURED: Clean's distinct term-mode `SurfaceExpr::Have`
    // elaborates to `ExprKind::Let` — the SAME kernel
    // node p03's `let` becomes — so the zeta arm handles it BY MEASUREMENT,
    // not by assumption. Were the elaborator ever to build a `letFun`
    // application instead, the first assertion fails here, and the reflect
    // twin (`test_ws5_12_let_fun_spelling_is_refused_by_name`) pins that the
    // denoter would refuse it naming `letFun`, never certify it.
    let env = elaborated_env_with(HAVE_SOURCE);
    let value = env
        .get_const(&Name::from_string("sqHave"))
        .and_then(|ci| ci.value.clone())
        .expect("sqHave has a stored definition");
    let clean_kernel::ExprKind::Lam(_, _, body) = value.kind() else {
        panic!("sqHave binds its parameter: {value}");
    };
    assert!(
        matches!(body.kind(), clean_kernel::ExprKind::Let(..)),
        "term-mode `have` must elaborate to ExprKind::Let (measured), got {body}"
    );
    for (level, pipeline) in optimizing() {
        let (module, report) = minted(HAVE_SOURCE, "sqHave", &pipeline)
            .unwrap_or_else(|e| panic!("{level}: the verified emit must not refuse: {e}"));
        assert_certified(&module, &report, "sqHave", level);
        assert_eq!(run_u64(&module, "sqHave", 6), 49, "{level}");
    }
}
