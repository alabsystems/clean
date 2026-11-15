// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.7 — the TV minter co-evolves with trust-ir's license and certificate
//! binding (WS1.4 / WS1.5 / WS1.12a).
//!
//! A child of `emit_trust_ir_tv::tests`, so the `trust-ir-backend-lib` gate
//! leg (`-- emit_trust_ir`) runs it. Every module here comes from the real
//! emitter or a Clean-shaped fixture, is minted by the real minter, and is
//! judged by the PINNED trust-ir validator.
//!
//! What this file pins, by roadmap part:
//!
//! * **(b) bound mint.** `certify_backend_translation_bound` populates every
//!   `CertificateBinding` field; the pinned validator admits the result under
//!   every layer, including `with_bound_certificates(true)`. Negative twins:
//!   a stripped binding (`UnboundCertificate` under the bound policy), a
//!   mutated statement digest, and an environment digest of a DIFFERENT
//!   anchor — the pre-WS1.15 one without the signed carrier aliases, which is
//!   exactly the environment Clean minted against before this increment — are
//!   each refused by their named field. Binding is the shipping default, and a
//!   bound, evidenced module round-trips the binary codec at the pin.
//! * **(b) license evidence.** Every `Gated` body carries `GateEvidence
//!   { obligation, body_digest }` naming its TV row and its body; the pinned
//!   validator admits it under the gate-evidence policy. Negative twins: a body
//!   edited after the mint, and a license whose digest no longer names its
//!   body, are refused as `GatedEvidenceMismatch`; a license stripped of its
//!   evidence is refused as `UnevidencedGate` by the evidence policy.
//! * **The c04 A2 shape.** Retargeting a certified caller's `Call` from
//!   `plus` to `minus` is refused by trust-ir and by Clean's own pre-flight
//!   `validate_module_for_codegen` — the one-sided edit by WS1.4 on every
//!   certificate, the CONSISTENT edit (call and inheritance row together) by
//!   the binding's `callees` field on a bound one. The unbound control shows
//!   the residual the binding closes.
//! * **Transplant mutation control.** A minted certificate and license moved
//!   onto a sibling function with the SAME body and signature are refused by
//!   the obligation's function scope and by the license's body digest.
//! * **(c)** callee rows are one per called function, keyed by `FuncId`.
//! * **(d)** the minter refuses a body Clean did not produce.
//! * **(e)** `Gated` is minted only in the step that attaches its evidence.

// The parent scopes (`emit_trust_ir_tv` and its `tests`) already bring the
// emitter, the IR builders, the kernel names and the trust-ir proof types.
use super::*;
use trust_ir::proof::{clean_cic_lineage_is_v8, ProofDigestAlgorithm};
use trust_ir_build::{
    validate_module, validate_module_for_codegen, validate_module_with_config, ValidationConfig,
    ValidationError,
};

// ---- fixtures ------------------------------------------------------------------

/// `v2 = <first>(a, b); v3 = <second>(v2, a); ret v3` at `UInt64` — the
/// c04 program's leaves (`plus = a*b + a`, `minus = a*b - a`).
fn leaf_decl(name: &str, second: &str) -> IRDecl {
    IRDecl {
        name: KName::from_string(name),
        params: vec![(VarId(0), IRType::UInt64), (VarId(1), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: VarId(2),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: FnId(KName::from_string("UInt64.mul")),
                args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(3),
                ty: IRType::UInt64,
                value: IRExpr::Apply {
                    fn_id: FnId(KName::from_string(second)),
                    args: vec![IRArg::Var(VarId(2)), IRArg::Var(VarId(0))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
            }),
        },
    }
}

/// `v2 = <callee>(a, b); v3 = 7; v4 = UInt64.add(v2, v3); ret v4` — the c04
/// caller.
fn top_decl(callee: &str) -> IRDecl {
    IRDecl {
        name: KName::from_string("top"),
        params: vec![(VarId(0), IRType::UInt64), (VarId(1), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: VarId(2),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: FnId(KName::from_string(callee)),
                args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(3),
                ty: IRType::UInt64,
                value: IRExpr::Lit(IRLiteral::UInt64(7)),
                rest: Box::new(IRBody::VDecl {
                    var: VarId(4),
                    ty: IRType::UInt64,
                    value: IRExpr::Apply {
                        fn_id: FnId(KName::from_string("UInt64.add")),
                        args: vec![IRArg::Var(VarId(2)), IRArg::Var(VarId(3))],
                    },
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(4)))),
                }),
            }),
        },
    }
}

fn u64ty() -> Expr {
    Expr::const_str("UInt64")
}

fn u64_fn2_ty() -> Expr {
    Expr::arrow(u64ty(), Expr::arrow(u64ty(), u64ty()))
}

/// `fun (a b : UInt64) => body` (inside, `a` is `bvar 1` and `b` is `bvar 0`).
fn lam_ab(body: Expr) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        u64ty(),
        Expr::lam(BinderInfo::Default, u64ty(), body),
    )
}

/// `fun a b => UInt64.<second> (UInt64.mul a b) a`.
fn leaf_source(second: &str) -> Expr {
    let prod = Expr::apps(
        Expr::const_str("UInt64.mul"),
        [Expr::bvar(1), Expr::bvar(0)],
    );
    lam_ab(Expr::apps(Expr::const_str(second), [prod, Expr::bvar(1)]))
}

/// `fun a b => UInt64.add (<callee> a b) (UInt64.ofNat 7)`.
fn top_source(callee: &str) -> Expr {
    let call = Expr::apps(Expr::const_str(callee), [Expr::bvar(1), Expr::bvar(0)]);
    let seven = Expr::app(Expr::const_str("UInt64.ofNat"), Expr::nat_lit(7));
    lam_ab(Expr::apps(Expr::const_str("UInt64.add"), [call, seven]))
}

/// The c04 program as Clean emits it: `plus`, `minus`, a byte-identical twin
/// `plus2` of `plus`, and `top` calling `plus`. Returns the emitted module,
/// the originals the minter compares against, and the SOURCE environment
/// holding those definitions (the one closure digests are taken in).
fn c04_program() -> (Module, Vec<(String, Expr)>, Environment) {
    let module = emit_trust_ir(&[
        leaf_decl("plus", "UInt64.add"),
        leaf_decl("minus", "UInt64.sub"),
        leaf_decl("plus2", "UInt64.add"),
        top_decl("plus"),
    ])
    .expect("the c04 program lowers");
    let originals = vec![
        ("plus".to_string(), leaf_source("UInt64.add")),
        ("minus".to_string(), leaf_source("UInt64.sub")),
        ("plus2".to_string(), leaf_source("UInt64.add")),
        ("top".to_string(), top_source("plus")),
    ];
    let mut env = Environment::try_with_prelude().expect("prelude");
    for (name, value) in &originals {
        env.add_decl(Declaration::Definition {
            name: KName::from_string(name),
            level_params: vec![],
            type_: u64_fn2_ty(),
            value: value.clone(),
            is_reducible: false,
        })
        .unwrap_or_else(|e| panic!("source `{name}` is well-typed: {e:?}"));
    }
    (module, originals, env)
}

/// Each decl's source identity, by source name: its declaration and closure
/// digest, or the reason it cannot be stated.
type SourceIdentities = BTreeMap<String, Result<SourceDefinitionRef, String>>;

/// The bound mint over a TABLE of source identities (the pipeline asks the
/// same question on demand of its environment).
fn mint_bound(
    module: &mut Module,
    originals: &[(String, Expr)],
    sources: &SourceIdentities,
) -> TvMintReport {
    certify_backend_translation_bound(module, originals, &|name: &str| sources.get(name).cloned())
}

/// Each original's source identity in `env`: its declaration and closure
/// digest, exactly as the pipeline computes them.
fn sources_in(env: &Environment, originals: &[(String, Expr)]) -> SourceIdentities {
    originals
        .iter()
        .map(|(name, _)| {
            let bytes = env
                .closure_digest(&KName::from_string(name))
                .unwrap_or_else(|e| panic!("`{name}` has a closure digest: {e}"));
            (
                name.clone(),
                Ok(SourceDefinitionRef {
                    decl: name.clone(),
                    closure_digest: ProofDigest {
                        algorithm: ProofDigestAlgorithm::Sha256,
                        bytes,
                    },
                }),
            )
        })
        .collect()
}

/// The c04 program, minted BOUND (`bound = true`) or unbound.
fn minted_c04(bound: bool) -> Module {
    let (mut module, originals, env) = c04_program();
    let report = if bound {
        mint_bound(&mut module, &originals, &sources_in(&env, &originals))
    } else {
        certify_backend_translation(&mut module, &originals)
    };
    assert_eq!(
        report.certified.len(),
        originals.len(),
        "every c04 decl certifies (bound = {bound}): {report:?}"
    );
    module
}

fn fid(module: &Module, name: &str) -> FuncId {
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no emitted function `{name}`"))
        .id
}

/// The one TV obligation scoped to `name`.
fn tv_obligation(module: &Module, name: &str) -> ProofObligation {
    let f = fid(module, name);
    let rows: Vec<&ProofObligation> = module
        .proof_obligations
        .iter()
        .filter(|o| o.function == Some(f) && o.kind == ObligationKind::TranslationValidation)
        .collect();
    let [row] = rows.as_slice() else {
        panic!("exactly one TV obligation on `{name}`, got {rows:?}");
    };
    (*row).clone()
}

/// The `clean_backend_tv` binding of `name`'s TV certificate, mutably.
fn binding_mut<'m>(module: &'m mut Module, name: &str) -> &'m mut Option<Box<CertificateBinding>> {
    let oid = tv_obligation(module, name).id;
    module
        .proof_certificates
        .iter_mut()
        .find_map(|c| match &mut c.evidence {
            ProofEvidence::CleanCic {
                kernel_recheck: Some(recheck),
                ..
            } if c.obligation == oid => Some(&mut recheck.binding),
            _ => None,
        })
        .unwrap_or_else(|| panic!("`{name}` carries a CleanCic directive"))
}

/// Re-key `name`'s CleanCic lineage to the v8 form over its CURRENT binding —
/// what an adversary who edits a binding and re-mints the lineage would do.
/// The v8 lineage folds the binding bytes in, so without this an edited
/// binding is refused as a lineage mismatch before its fields are compared;
/// with it, the refusal must come from the named binding field.
fn rekey_v8(module: &mut Module, name: &str) {
    let obligation = tv_obligation(module, name);
    let resolver_view = module.clone();
    let resolve = module_symbol_resolver(&resolver_view);
    for cert in module
        .proof_certificates
        .iter_mut()
        .filter(|c| c.obligation == obligation.id)
    {
        if let ProofEvidence::CleanCic {
            lineage,
            kernel_recheck: Some(recheck),
            ..
        } = &mut cert.evidence
        {
            *lineage =
                clean_cic_lineage_digest_v8(&obligation, &resolve, recheck.binding.as_deref())
                    .expect("the obligation is keyed by symbol");
        }
    }
}

fn strict() -> ValidationConfig<'static> {
    ValidationConfig::pinned()
        .with_codegen(true)
        .with_bound_certificates(true)
        .with_gate_evidence(true)
}

/// The `GatedEvidenceMismatch` details the validator reports for `function`.
fn evidence_mismatches(errors: &[ValidationError], function: FuncId) -> Vec<String> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::GatedEvidenceMismatch {
                function: f,
                detail,
            } if *f == function.index() => Some(detail.clone()),
            _ => None,
        })
        .collect()
}

fn binding_refusals(errors: &[ValidationError], obligation: ProofId) -> Vec<String> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::CertificateBindingMismatch {
                obligation: o,
                field,
                ..
            } if *o == obligation.index() => Some(field.clone()),
            _ => None,
        })
        .collect()
}

/// Retarget `top`'s one `Call` to `to`; with `with_row`, also rewrite its
/// `InheritedFromCallee` row to `to`'s own TV obligation (the CONSISTENT
/// edit).
fn retarget_top(module: &mut Module, to: &str, with_row: bool) {
    let target = fid(module, to);
    let target_obligation = tv_obligation(module, to).id;
    let top = fid(module, "top");
    let top_obligation = tv_obligation(module, "top").id;
    let mut calls = 0;
    for func in module.functions.iter_mut().filter(|f| f.id == top) {
        for node in func.blocks.iter_mut().flat_map(|b| b.body.iter_mut()) {
            if let Inst::Call { callee, .. } = &mut node.inst {
                *callee = target;
                calls += 1;
            }
        }
    }
    assert_eq!(calls, 1, "exactly one Call retargeted");
    if with_row {
        let mut rows = 0;
        for cert in module
            .proof_certificates
            .iter_mut()
            .filter(|c| c.obligation == top_obligation)
        {
            if let ProofEvidence::InheritedFromCallee {
                callee, obligation, ..
            } = &mut cert.evidence
            {
                *callee = target;
                *obligation = target_obligation;
                rows += 1;
            }
        }
        assert_eq!(rows, 1, "exactly one inheritance row rewritten");
    }
}

fn top_is_refused_for_codegen(module: &Module) -> bool {
    let top = fid(module, "top").index();
    validate_module_for_codegen(module).iter().any(
        |e| matches!(e, ValidationError::GatedWithoutEvidence { function, .. } if *function == top),
    )
}

// ---- (b) the bound mint ------------------------------------------------------------

/// POSITIVE (roadmap WS6.7 Tests): Clean's bound mint passes WS1.4, WS1.5
/// and WS1.12's validator at the pin — the structural layer, the codegen
/// layer, and the codegen layer under the bound-certificate AND gate-evidence
/// policies — every binding field is the one the roadmap names, and every
/// license carries `GateEvidence` naming its TV row and its body digest.
#[test]
fn ws6_7_bound_mint_is_admitted_by_every_pinned_layer() {
    let (_, originals, env) = c04_program();
    let module = minted_c04(true);
    let anchor = tv_anchor_environment().expect("anchor");
    let anchor_digest = kernel_environment_digest(&anchor).expect("anchor digests");
    let resolve = module_symbol_resolver(&module);
    for (name, _) in &originals {
        let obligation = tv_obligation(&module, name);
        let cert = module
            .proof_certificates
            .iter()
            .find(|c| {
                c.obligation == obligation.id && c.evidence.clean_cic_kernel_recheck().is_some()
            })
            .expect("the CleanCic certificate");
        let binding = cert
            .evidence
            .clean_cic_kernel_recheck()
            .and_then(|r| r.binding.as_deref())
            .unwrap_or_else(|| panic!("`{name}` is bound"));
        assert_eq!(binding.environment_digest, anchor_digest, "`{name}`");
        assert_eq!(binding.origin_module, None, "`{name}` is minted here");
        let source = binding.source.as_ref().expect("source identity");
        assert_eq!(source.decl, *name);
        assert_eq!(
            source.closure_digest.bytes,
            env.closure_digest(&KName::from_string(name))
                .expect("digest"),
            "`{name}`: the closure digest of the source environment"
        );
        let callees: &[&str] = if name == "top" { &["plus"] } else { &[] };
        assert_eq!(binding.callees, callees, "`{name}`");
        assert!(
            clean_cic_lineage_is_v8(&obligation, &cert.evidence, &resolve),
            "`{name}`: a bound certificate carries the symbol-keyed v8 lineage"
        );
        let f = fid(&module, name);
        assert_eq!(
            module
                .functions
                .iter()
                .find(|g| g.id == f)
                .map(|g| &g.body_gate),
            Some(&Some(BodyGate::Gated {
                authority: CLEAN_KERNEL_TV_AUTHORITY.to_string(),
                evidence: Some(GateEvidence {
                    obligation: obligation.id,
                    body_digest: module.function_body_digest(f).expect("digest"),
                }),
            })),
            "`{name}` is licensed, citing its TV row and its body"
        );
    }
    assert_eq!(validate_module(&module), Vec::new());
    assert_eq!(validate_module_for_codegen(&module), Vec::new());
    assert_eq!(
        validate_module_with_config(&module, &strict()).into_errors(),
        Vec::new(),
        "the bound-certificate and gate-evidence policies admit every row"
    );
}

/// CONTROL: the unbound mint (the default) is admitted by the default lanes
/// exactly as before, and refused by the bound-certificate policy BY NAME —
/// one `UnboundCertificate` per certified row.
#[test]
fn ws6_7_unbound_mint_is_refused_only_by_the_bound_policy() {
    let module = minted_c04(false);
    assert_eq!(validate_module_for_codegen(&module), Vec::new());
    let errors = validate_module_with_config(&module, &strict()).into_errors();
    let unbound: BTreeSet<u32> = errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::UnboundCertificate { obligation } => Some(*obligation),
            _ => None,
        })
        .collect();
    let certified: BTreeSet<u32> = module
        .proof_obligations
        .iter()
        .filter(|o| o.status == ProofStatus::Certified)
        .map(|o| o.id.index())
        .collect();
    assert_eq!(unbound, certified, "{errors:?}");
}

/// POSITIVE, real source through the pipeline with the DEFAULT config: the
/// pipeline mints bound certificates whose `source` is the elaborated
/// environment's own closure digest, evidenced licenses, and the result passes
/// the bound and evidence policies. The closure's other bodies (instances,
/// boxed wrappers) are outside the fragment and stay `Ungated`, so the codegen
/// layer refuses exactly those and never `sqLet`.
#[test]
fn ws6_7_pipeline_mints_bound_certificates_from_real_source() {
    use crate::pass_manager::{compile_lcnf_to_trust_ir_with_report, PipelineConfig};
    use crate::rc_repair::e2e_support::{closure_decls_of, elaborated_env_with};
    let source = "def sqLet (a : UInt64) : UInt64 := let t := a + 1; t * t\n";
    let cfg = crate::emit_trust_ir::TrustIrConfig {
        module_name: "ws6_7".to_string(),
        runtime_lowering: crate::emit_trust_ir::RuntimeLowering::ExternCalls,
        certify_translation: true,
        ..crate::emit_trust_ir::TrustIrConfig::default()
    };
    assert!(cfg.bind_certificates, "binding is the shipping default");
    let env = elaborated_env_with(source);
    let pipeline = PipelineConfig::default();
    let decls = closure_decls_of(&env, &pipeline, &["sqLet"]);
    let (module, report) = compile_lcnf_to_trust_ir_with_report(&decls, &env, &pipeline, &cfg)
        .expect("sqLet lowers and mints");
    assert!(report.certified.iter().any(|n| n == "sqLet"), "{report:?}");
    let oid = tv_obligation(&module, "sqLet").id;
    let binding = module
        .proof_certificates
        .iter()
        .filter(|c| c.obligation == oid)
        .find_map(|c| c.evidence.clean_cic_kernel_recheck())
        .and_then(|r| r.binding.as_deref())
        .expect("the pipeline minted a bound certificate");
    let source = binding.source.as_ref().expect("source identity");
    assert_eq!(source.decl, "sqLet");
    assert_eq!(
        source.closure_digest.bytes,
        env.closure_digest(&KName::from_string("sqLet"))
            .expect("digest")
    );
    let sqlet = fid(&module, "sqLet");
    assert_eq!(
        module
            .functions
            .iter()
            .find(|f| f.id == sqlet)
            .map(|f| &f.body_gate),
        Some(&kernel_tv_gate(&module, sqlet)),
        "sqLet carries the evidenced license"
    );
    assert_eq!(
        validate_module_with_config(
            &module,
            &ValidationConfig::pinned()
                .with_bound_certificates(true)
                .with_gate_evidence(true)
        )
        .into_errors(),
        Vec::new(),
        "the bound and evidence policies admit the pipeline's mint"
    );
    let codegen = validate_module_with_config(&module, &strict()).into_errors();
    assert!(
        !codegen.is_empty(),
        "control: the closure has unminted bodies"
    );
    for error in &codegen {
        assert!(
            matches!(
                error,
                ValidationError::UngatedBodyForCodegen { function, .. } if *function != sqlet.index()
            ),
            "only the unminted closure bodies are refused for codegen: {codegen:?}"
        );
    }
}

/// The shipping default binds, and a bound, evidenced module HAS a binary
/// identity at this pin: the writer selects the certificate-binding version
/// (`CERTIFICATE_BINDING_FORMAT_VERSION`, v61), and the decoded module is the minted one, binding and evidence
/// included, still admitted by the strictest policy.
#[test]
fn ws6_7_bound_evidenced_module_round_trips_the_binary_codec() {
    assert!(crate::emit_trust_ir::TrustIrConfig::default().bind_certificates);
    let module = minted_c04(true);
    let bytes =
        crate::emit_trust_ir::serialize_module_bytes(&module).expect("a bound module serializes");
    assert_eq!(
        u32::from_le_bytes(bytes[8..12].try_into().expect("header")),
        trust_ir::binary::CERTIFICATE_BINDING_FORMAT_VERSION,
        "a binding and license evidence select the carrier's version"
    );
    let back = trust_ir::binary::deserialize_module(&bytes).expect("decodes");
    assert_eq!(back, module, "binding and evidence survive the codec");
    assert_eq!(
        validate_module_with_config(&back, &strict()).into_errors(),
        Vec::new()
    );
}

/// A bound mint needs every decl's source identity: a decl offered without
/// one is SKIPPED with the reason — no obligation, no certificate, no license
/// — never minted with a partial or absent binding.
#[test]
fn ws6_7_bound_mint_without_a_source_identity_skips() {
    let (mut module, originals, env) = c04_program();
    let mut sources = sources_in(&env, &originals);
    sources.remove("minus");
    let report = mint_bound(&mut module, &originals, &sources);
    let reason = report
        .skipped
        .iter()
        .find(|(n, _)| n == "minus")
        .map(|(_, r)| r.as_str())
        .unwrap_or_else(|| panic!("`minus` is skipped: {report:?}"));
    assert!(reason.contains("source-definition identity"), "{reason}");
    let minus = fid(&module, "minus");
    assert!(module
        .proof_obligations
        .iter()
        .all(|o| o.function != Some(minus)));
    assert_eq!(
        module
            .functions
            .iter()
            .find(|f| f.id == minus)
            .map(|f| &f.body_gate),
        Some(&Some(BodyGate::Ungated))
    );
    assert_eq!(report.certified.len(), 3, "{report:?}");
    assert_eq!(
        validate_module_for_codegen(&module).len(),
        1,
        "only `minus` is unlicensed"
    );
}

/// A source identity that cannot be STATED (the pipeline's `Err` from
/// `Environment::closure_digest`) skips the decl with that reason, never a
/// partial binding: no obligation, no certificate, no license.
#[test]
fn ws6_7_bound_mint_with_an_unstateable_source_identity_skips_with_its_reason() {
    let (mut module, originals, env) = c04_program();
    let mut sources = sources_in(&env, &originals);
    sources.insert(
        "minus".to_string(),
        Err(
            "synthetic: `minus` mentions `Missing.decl`, which this environment does not \
             declare"
                .to_string(),
        ),
    );
    let report = mint_bound(&mut module, &originals, &sources);
    let reason = report
        .skipped
        .iter()
        .find(|(n, _)| n == "minus")
        .map(|(_, r)| r.as_str())
        .unwrap_or_else(|| panic!("`minus` is skipped: {report:?}"));
    assert!(
        reason.contains("cannot be stated") && reason.contains("Missing.decl"),
        "the skip names the identity's own reason: {reason}"
    );
    let minus = fid(&module, "minus");
    assert!(module
        .proof_obligations
        .iter()
        .all(|o| o.function != Some(minus)));
    assert_eq!(
        module
            .functions
            .iter()
            .find(|f| f.id == minus)
            .map(|f| &f.body_gate),
        Some(&Some(BodyGate::Ungated))
    );
    assert_eq!(report.certified.len(), 3, "{report:?}");
}

/// A missing source identity never hides a MISCOMPILE: the bound mint judges
/// the equation BEFORE it skips an unbindable decl, so `plus` compared against
/// `minus`'s definition is REFUSED (the pipeline turns that into a hard
/// compile error), exactly as the unbound mint refuses it — not skipped.
#[test]
fn ws6_7_bound_mint_judges_before_it_skips_an_unbindable_decl() {
    for identity in [None, Some(Err("synthetic: no closure".to_string()))] {
        let (mut module, mut originals, env) = c04_program();
        let mut sources = sources_in(&env, &originals);
        for (name, value) in &mut originals {
            if name == "plus" {
                *value = leaf_source("UInt64.sub");
            }
        }
        match identity.clone() {
            None => {
                sources.remove("plus");
            }
            Some(err) => {
                sources.insert("plus".to_string(), err);
            }
        }
        let report = mint_bound(&mut module, &originals, &sources);
        assert!(
            report
                .refused
                .iter()
                .any(|(n, r)| n == "plus" && r.contains("kernel REFUSED")),
            "{identity:?}: the miscompile is refused by the kernel: {report:?}"
        );
        assert!(
            report.skipped.iter().all(|(n, _)| n != "plus"),
            "{identity:?}: never merely skipped: {report:?}"
        );
        let plus = fid(&module, "plus");
        assert!(module
            .proof_obligations
            .iter()
            .all(|o| o.function != Some(plus)));
    }
}

/// NEGATIVE TWIN (roadmap: strip one binding): the stripped certificate is
/// re-keyed to the lineage an UNBOUND mint would carry, so every default lane
/// still admits it — that is the residual — and the bound policy refuses it
/// by NAME, `UnboundCertificate`, on exactly that obligation.
#[test]
fn ws6_7_stripped_binding_is_refused_as_unbound() {
    let mut module = minted_c04(true);
    let top = tv_obligation(&module, "top");
    *binding_mut(&mut module, "top") = None;
    for cert in &mut module.proof_certificates {
        if let ProofEvidence::CleanCic { lineage, .. } = &mut cert.evidence {
            if cert.obligation == top.id {
                *lineage = clean_cic_lineage_digest(&top);
            }
        }
    }
    assert_eq!(validate_module_for_codegen(&module), Vec::new());
    let errors = validate_module_with_config(&module, &strict()).into_errors();
    assert!(
        errors.contains(&ValidationError::UnboundCertificate {
            obligation: top.id.index()
        }),
        "{errors:?}"
    );
}

/// NEGATIVE TWIN: a stripped binding whose lineage is left alone no longer
/// matches its own v8 lineage (which folds the binding in), so even the
/// default lanes refuse it — `CertifiedCleanCicLineageMismatch` on the row,
/// and the body's license with it.
#[test]
fn ws6_7_stripped_binding_breaks_its_v8_lineage() {
    let mut module = minted_c04(true);
    let top = tv_obligation(&module, "top").id.index();
    *binding_mut(&mut module, "top") = None;
    assert!(validate_module(&module)
        .contains(&ValidationError::CertifiedCleanCicLineageMismatch { obligation: top }));
    assert!(top_is_refused_for_codegen(&module));
}

/// NEGATIVE TWIN (roadmap: an environment digest from a different prelude):
/// the digest of the PRE-WS1.15 anchor — the prelude and heap vocabulary
/// without the signed carrier aliases, the environment Clean minted in before
/// this increment — is refused as `environment_digest`.
#[test]
fn ws6_7_environment_digest_of_another_anchor_is_refused() {
    let mut older = Environment::try_with_prelude().expect("prelude");
    for decl in clean_reflect::heap_vocab_declarations() {
        older.add_decl(decl).expect("heap vocabulary");
    }
    let older_digest = kernel_environment_digest(&older).expect("digests");
    let mut module = minted_c04(true);
    let top = tv_obligation(&module, "top").id;
    let binding = binding_mut(&mut module, "top").as_mut().expect("bound");
    assert_ne!(binding.environment_digest, older_digest, "control");
    binding.environment_digest = older_digest;
    rekey_v8(&mut module, "top");
    let errors = validate_module(&module);
    assert!(
        binding_refusals(&errors, top).contains(&"environment_digest".to_string()),
        "{errors:?}"
    );
}

/// NEGATIVE TWIN: one byte of the statement digest mutated is refused as
/// `statement_digest`.
#[test]
fn ws6_7_mutated_statement_digest_is_refused() {
    let mut module = minted_c04(true);
    let plus = tv_obligation(&module, "plus").id;
    binding_mut(&mut module, "plus")
        .as_mut()
        .expect("bound")
        .statement_digest
        .bytes[0] ^= 1;
    rekey_v8(&mut module, "plus");
    let errors = validate_module(&module);
    assert!(
        binding_refusals(&errors, plus).contains(&"statement_digest".to_string()),
        "{errors:?}"
    );
}

// The c04 A2 shape, license evidence, the transplant control and parts
// (c)-(e) live in a child module, so neither file outgrows the paragon
// file-size ratchet; it reuses the fixtures above through `super::*`.
#[path = "emit_trust_ir_tv_ws6_7_license_tests.rs"]
mod license;

#[path = "emit_trust_ir_tv_ws6_7_source_pipeline_tests.rs"]
mod source_pipeline;
