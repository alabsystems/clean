// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.6 — widen the kernel-TV fragment (Clean side), pin-cycle ordered.
//!
//! A child of `emit_trust_ir_tv::tests`, so the `trust-ir-backend-lib` gate
//! leg (`-- emit_trust_ir`) runs it.
//!
//! What this file pins:
//!
//! * **Source-side `let` (minted now).** `sqLet`'s `let t := a + 1; t * t`
//!   denotes by zeta substitution. The re-checker trust-ir pins never
//!   re-derives the comparand, so this widening needs no trust-ir change, and
//!   every certificate here must pass `validate_module_for_codegen` at the
//!   PINNED trust-ir. Negative twins (operator swap, wrong let value, a
//!   de Bruijn slip) are kernel REFUSALS; a let at a non-`UIntW` type is a
//!   fail-closed skip.
//! * **The pin-cycle mutation control.** A Clean-side denotation of a shape
//!   the pinned re-checker does not know (`sar`'s `ashr`, which WS1.15 keeps
//!   OUT of the fragment) is ACCEPTED by Clean's kernel — and the same
//!   certificate is REFUSED by the pinned `validate_module_for_codegen`. That
//!   is why the minter's emitted-side fragment must not widen before trust-ir
//!   mirrors it. Until trust-ir 7b9146ba this control was `mask`'s `and`/`or`;
//!   the pin move to 4f09dab8 brought WS1.15 S4, which mirrors them as
//!   `Nat.land`/`Nat.lor`, so the `mask` certificate now RE-CHECKS at the pin
//!   (pinned below as an independent positive). The real minter now admits
//!   exactly those mirrored And/Or denotations too.
//! * **The eager-division control.** `select(b == 0, 0, udiv a b)` executes
//!   the `udiv` at `b = 0` (UB under ub-numerics-policy §1). The minter skips
//!   it and a forged certificate for it is refused by the pinned trust-ir —
//!   since 4f09dab8 (WS1.15 S1/S4: ICmp anywhere, UDiv only by a provably
//!   nonzero divisor) AT the `udiv`, naming the divisor, rather than at the
//!   `icmp` the older pin did not know.
//! * **The shared golden fixture** (`tv_golden/statements.txt`): the exact
//!   module text, comparand bytes and kernel statement bytes of the
//!   in-fragment shapes, which the trust-ir mirror must reproduce byte for
//!   byte (the WS1.15 drift mitigation).

use super::*;
use clean_kernel::{ExprKind, Level};
use trust_ir_build::{validate_module, validate_module_for_codegen, ValidationError};

// ---- fixtures ---------------------------------------------------------------

/// `sqLet` at `U32`: `%1 = 1; %2 = add %0 %1; %3 = mul %2 %2; ret %3`.
/// `mul_op` is the operator of the last instruction (the injection point).
fn sqlet_module(mul_op: BinOp) -> Module {
    let mut b = HeapFx::new(1);
    let one = b.cu32(1);
    let t = b.bin(BinOp::Add, b.param(0), one);
    let r = b.bin(mul_op, t, t);
    b.finish("sqLet", r)
}

/// `fun a => let t : UInt32 := a + k; t * t` — inside the let body `bvar 0`
/// is `t` and `bvar 1` is `a`. `body_uses_param` spells the body `t * a`
/// instead (the de Bruijn twin).
fn sqlet_source(k: u64, body_uses_param: bool) -> KExpr {
    let value = uadd(KExpr::bvar(0), of_nat(k));
    let rhs = if body_uses_param {
        KExpr::bvar(1)
    } else {
        KExpr::bvar(0)
    };
    let body = umul(KExpr::bvar(0), rhs);
    lam_n(
        1,
        KExpr::let_named(Name::from_string("t"), u32ty(), value, body, false),
    )
}

/// `mask` at `U32`: `%2 = and %0 %1; %3 = 1; %4 = or %2 %3; ret %4`.
fn mask_module() -> Module {
    let mut b = HeapFx::new(2);
    let a = b.bin(BinOp::And, b.param(0), b.param(1));
    let one = b.cu32(1);
    let r = b.bin(BinOp::Or, a, one);
    b.finish("mask", r)
}

/// `mask`'s source: `fun a b => UInt32.lor (UInt32.land a b) 1`.
fn mask_source() -> KExpr {
    let land = KExpr::apps(
        KExpr::const_str("UInt32.land"),
        [KExpr::bvar(1), KExpr::bvar(0)],
    );
    lam_n(
        2,
        KExpr::apps(KExpr::const_str("UInt32.lor"), [land, of_nat(1)]),
    )
}

/// `sar` at `U32`: `%2 = ashr %0 %1; ret %2` — a shape WS1.15 keeps outside
/// the TV fragment on BOTH sides (trust-ir 4f09dab8 `denote_binop`: "SDiv/SRem/
/// AShr and float ops are excluded"; Clean's fragment excludes AShr).
fn sar_module() -> Module {
    let mut b = HeapFx::new(2);
    let r = b.bin(BinOp::AShr, b.param(0), b.param(1));
    b.finish("sar", r)
}

/// `sar`'s source (never denoted: the emitted side refuses first).
fn sar_source() -> KExpr {
    lam_n(
        2,
        KExpr::apps(
            KExpr::const_str("UInt32.shiftRight"),
            [KExpr::bvar(1), KExpr::bvar(0)],
        ),
    )
}

/// The eager-division shape the REVIEW fix forbids:
/// `%2 = 0; %3 = icmp eq %1 %2; %4 = udiv %0 %1; %5 = select %3 %2 %4; ret %5`.
fn eager_div_module() -> Module {
    let mut b = HeapFx::new(2);
    let zero = b.cu32(0);
    let is_zero = b.push(Inst::ICmp {
        op: ICmpOp::Eq,
        ty: Ty::U32,
        lhs: b.param(1),
        rhs: zero,
    });
    let q = b.bin(BinOp::UDiv, b.param(0), b.param(1));
    let r = b.push(Inst::Select {
        ty: Ty::U32,
        cond: is_zero,
        then_val: zero,
        else_val: q,
    });
    b.finish("quot", r)
}

/// `quot`'s source: `fun a b => UInt32.div a b` (Lean: `x / 0 = 0`).
fn quot_source() -> KExpr {
    lam_n(
        2,
        KExpr::apps(
            KExpr::const_str("UInt32.div"),
            [KExpr::bvar(1), KExpr::bvar(0)],
        ),
    )
}

fn nat2(f: &str, a: KExpr, b: KExpr) -> KExpr {
    KExpr::apps(KExpr::const_str(f), [a, b])
}

fn nat_lit(k: u64) -> KExpr {
    KExpr::nat_lit(k)
}

/// `name` carries the license the minter stamps: `Gated { clean-kernel-tv }`
/// whose evidence re-derives from the module as it stands.
fn is_gated(module: &Module, name: &str) -> bool {
    module.functions.iter().any(|f| {
        f.name == name && f.body_gate.is_some() && f.body_gate == kernel_tv_gate(module, f.id)
    })
}

/// Forge the certificate a WIDER Clean-side denotation WOULD mint for the
/// single function `name` of `module` — exactly the minter's payload
/// (`attempt_certify` steps 4–6) with `lhs`/`rhs` supplied by hand — after
/// asserting that Clean's own kernel ACCEPTS the equation (so Clean would
/// mint it), then license the body as the minter does.
fn forge_widened_certificate(module: &mut Module, name: &str, lhs: &KExpr, rhs: &KExpr) {
    let arity = 2;
    let width = 32;
    let thm = tv_theorem_name(name);
    let stmt = tv_statement(&[], arity, lhs, rhs);
    let proof = tv_proof_term(&[], arity, lhs);
    let mut env = Environment::try_with_prelude().expect("prelude");
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(&thm),
        level_params: vec![],
        type_: stmt,
        value: proof.clone(),
    })
    .expect("Clean's kernel accepts the widened equation — Clean WOULD mint it");
    let rhs_lambda = (0..arity).fold(rhs.clone(), |acc, _| {
        KExpr::lam(BinderInfo::Default, KExpr::const_str("Nat"), acc)
    });
    let func = module.functions.iter().find(|f| f.name == name).unwrap();
    let fid = func.id;
    let oid = ProofId::new(0);
    let obligation = ProofObligation {
        id: oid,
        kind: ObligationKind::TranslationValidation,
        status: ProofStatus::Certified,
        description: format!("forged widened TV for '{name}'"),
        formula: Some(clean_reflect::tv_statement_formula(name, 2, width)),
        function: Some(fid),
        source: None,
        site: None,
        spec: None,
    };
    let lineage = clean_cic_lineage_digest(&obligation);
    module.proof_certificates.push(ProofCertificate {
        obligation: oid,
        prover: "clean-backend-tv".to_string(),
        evidence: ProofEvidence::CleanCic {
            term: bincode::serialize(&proof).unwrap(),
            context: bincode::serialize(&rhs_lambda).unwrap(),
            lineage,
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: TV_MODULE.to_string(),
                theorems: vec![thm],
                anchor: clean_reflect::CLEAN_BACKEND_TV_ANCHOR.to_string(),
                allowed_axioms: vec![],
                binding: None,
            }),
        },
        assurance: None,
    });
    module.proof_obligations.push(obligation);
    // The forged license carries the evidence the minter would stamp, so the
    // ONLY defect left for the re-checker is the wider denotation.
    let gate =
        kernel_tv_gate(module, fid).expect("the forged row is the function's one Certified TV row");
    for f in module.functions.iter_mut().filter(|f| f.id == fid) {
        f.body_gate = Some(gate.clone());
    }
}

/// `true` iff `errors` is exactly the pinned re-checker REJECTING the forged
/// certificate of `name`, for the named reason (`because` must occur in it),
/// followed by the one license refusal that rejection entails.
///
/// Since trust-ir WS1.5 (3e250ddb, "bind the codegen license to evidence") a
/// `Gated{clean-kernel-tv}` body is licensed only by a certificate that was
/// kernel-replayed IN THIS PASS, so the forged body's failed recheck is
/// reported twice, each for its own reason: once as the recheck failure
/// itself, once as `GatedWithoutEvidence` on the forged function under the
/// `clean-kernel-tv` authority. Both rows are pinned, and nothing else may
/// appear.
fn recheck_refused(forged: &Module, name: &str, errors: &[ValidationError], because: &str) -> bool {
    let fid = forged
        .functions
        .iter()
        .find(|f| f.name == name)
        .expect("the forged function is in the module")
        .id;
    matches!(
        errors,
        [
            ValidationError::CertifiedCleanCicKernelRecheckFailed { reason, .. },
            ValidationError::GatedWithoutEvidence { function, authority, detail },
        ] if reason.contains(because)
            && *function == fid.index()
            && authority == CLEAN_KERNEL_TV_AUTHORITY
            && detail.contains("was not kernel-replayed in this validation pass")
    )
}

// ---- source-side let (minted now) --------------------------------------------

/// POSITIVE: `sqLet` certifies through the source-side `let`, its body is
/// licensed `Gated{clean-kernel-tv}`, and the PINNED trust-ir accepts the
/// module for codegen — the independent kernel re-check passes, so this
/// widening needed nothing from the pinned mirror.
#[test]
fn ws6_6_sqlet_let_certifies_and_pinned_trust_ir_rechecks_it() {
    let (report, module) = mint(sqlet_module(BinOp::Mul), "sqLet", sqlet_source(1, false));
    assert_eq!(report.certified, ["sqLet"], "{report:?}");
    assert!(is_gated(&module, "sqLet"), "a certified body is licensed");
    let errors = validate_module_for_codegen(&module);
    assert!(
        errors.is_empty(),
        "the pinned trust-ir must re-check the let certificate: {errors:?}"
    );
}

/// NEGATIVE TWIN (operator swap): the emitted body squares with `add`
/// instead of `mul`. The kernel REFUSES; the pipeline turns that refusal
/// into a hard compile error (`TrustIrError::TranslationRefused`).
#[test]
fn ws6_6_sqlet_refuses_add_for_mul() {
    assert_kernel_refuses(sqlet_module(BinOp::Add), "sqLet", sqlet_source(1, false));
}

/// NEGATIVE TWIN (wrong let value): the source binds `a + 2`, the emitted
/// body computes `a + 1`. A zeta step that dropped or confused the value
/// would certify this; the kernel REFUSES.
#[test]
fn ws6_6_sqlet_refuses_a_different_let_value() {
    assert_kernel_refuses(sqlet_module(BinOp::Mul), "sqLet", sqlet_source(2, false));
}

/// NEGATIVE TWIN (de Bruijn): the source body is `t * a`, not `t * t`. If
/// the let environment were indexed wrong (`bvar 0` read as the parameter,
/// or `bvar 1` as the let), the two would coincide; the kernel REFUSES.
#[test]
fn ws6_6_sqlet_refuses_a_let_body_that_reads_the_parameter() {
    assert_kernel_refuses(sqlet_module(BinOp::Mul), "sqLet", sqlet_source(1, true));
}

/// FAIL-CLOSED: a let at a type other than the fragment's `UIntW` is out of
/// fragment — an auditable SKIP naming the binding type, never a mint.
#[test]
fn ws6_6_let_at_a_non_uint_type_is_skipped() {
    let value = uadd(KExpr::bvar(0), of_nat(1));
    let body = umul(KExpr::bvar(0), KExpr::bvar(0));
    let src = lam_n(
        1,
        KExpr::let_named(
            Name::from_string("t"),
            KExpr::const_str("Nat"),
            value,
            body,
            false,
        ),
    );
    assert_walker_skips(
        sqlet_module(BinOp::Mul),
        "sqLet",
        src,
        "source let binding at type Nat",
    );
}

/// MUTATION CONTROL: an out-of-fragment let VALUE fails closed even when the
/// body never reads it (the value is denoted eagerly, never dropped).
#[test]
fn ws6_6_unused_out_of_fragment_let_value_is_skipped() {
    let value = KExpr::apps(KExpr::const_str("UInt32.div"), [KExpr::bvar(0), of_nat(3)]);
    // let t := a / 3; (a + 1) * (a + 1)   — `t` unused (bvar 1 = a).
    let a1 = uadd(KExpr::bvar(1), of_nat(1));
    let body = umul(a1.clone(), a1);
    let src = lam_n(
        1,
        KExpr::let_named(Name::from_string("t"), u32ty(), value, body, true),
    );
    assert_walker_skips(
        sqlet_module(BinOp::Mul),
        "sqLet",
        src,
        "source construct headed by `UInt32.div`",
    );
}

// ---- pin-cycle mutation control ------------------------------------------------

/// MUTATION CONTROL (the two denoters must agree): a Clean-side denotation
/// that accepts `sar` — `ashr` spelled the way WS1.15 S4 spells `LShr`,
/// `Nat.div a (Nat.pow 2 b)` — is accepted by Clean's own kernel, yet the
/// PINNED trust-ir re-checker, which keeps `BinOp::AShr` out of the fragment,
/// REFUSES the certificate by name, so `validate_module_for_codegen` refuses
/// the module.
///
/// Minting a shape before trust-ir mirrors it therefore does not buy a
/// license, it loses the build. The real minter skips `sar` (its emitted
/// fragment is inside the pinned mirror's), which is asserted first.
///
/// This control was `mask`'s `and`/`or` while trust-ir sat at 7b9146ba; the
/// move to 4f09dab8 brought WS1.15 S4, under which that certificate re-checks
/// (see the positive below), so the control moved to a shape S4 still refuses.
#[test]
fn ws6_6_widened_denote_fails_pinned_recheck() {
    let (report, module) = mint(sar_module(), "sar", sar_source());
    assert!(report.certified.is_empty(), "{report:?}");
    assert!(
        report
            .skipped
            .iter()
            .any(|(n, r)| n == "sar" && r.contains("BinOp AShr")),
        "the minter must skip `sar` at the pinned fragment: {report:?}"
    );
    assert!(
        !is_gated(&module, "sar"),
        "a skipped body is never licensed"
    );

    let (x0, x1) = (KExpr::bvar(1), KExpr::bvar(0));
    let widened = nat2("Nat.div", x0, nat2("Nat.pow", nat_lit(2), x1));
    let mut forged = sar_module();
    forge_widened_certificate(&mut forged, "sar", &widened, &widened);
    let errors = validate_module_for_codegen(&forged);
    assert!(
        recheck_refused(
            &forged,
            "sar",
            &errors,
            "BinOp AShr is outside the TV fragment"
        ),
        "the pinned re-checker must refuse the unmirrored shape, naming it: {errors:?}"
    );
}

/// The independent consumer supported S4 before the minter. Retain the
/// hand-built certificate control beside the real minter's certificate, so
/// producer availability and independent consumer semantics are both checked.
#[test]
fn ws6_6_mask_s4_certificate_rechecks_at_the_pinned_trust_ir() {
    let (report, module) = mint(mask_module(), "mask", mask_source());
    assert_eq!(report.certified, ["mask"], "{report:?}");
    assert!(
        report.refused.is_empty() && report.skipped.is_empty(),
        "{report:?}"
    );
    assert!(is_gated(&module, "mask"));
    assert!(validate_module_for_codegen(&module).is_empty());

    let (x0, x1) = (KExpr::bvar(1), KExpr::bvar(0));
    let widened = nat2("Nat.lor", nat2("Nat.land", x0, x1), nat_lit(1));
    let mut forged = mask_module();
    forge_widened_certificate(&mut forged, "mask", &widened, &widened);
    let errors = validate_module_for_codegen(&forged);
    assert!(
        errors.is_empty(),
        "the pinned re-checker (trust-ir 4f09dab8, WS1.15 S4) must accept the S4-spelled \
         `mask` certificate: {errors:?}"
    );
}

/// A wrong scalar equation must reach an actual type-mismatch judgment,
/// rather than pass a negative control through a fragment skip or budget error.
#[track_caller]
fn assert_scalar_equation_type_mismatch(module: Module, name: &str, source: KExpr) {
    let (report, module) = mint(module, name, source);
    assert!(
        report.certified.is_empty() && report.skipped.is_empty(),
        "{report:?}"
    );
    let [(refused_name, reason)] = report.refused.as_slice() else {
        panic!("one actual kernel refusal required: {report:?}");
    };
    assert_eq!(refused_name, name);
    assert!(
        reason.contains("TypeMismatch"),
        "expected an actual type mismatch, not a resource or availability refusal: {reason}"
    );
    assert!(module.proof_obligations.is_empty() && module.proof_certificates.is_empty());
    assert!(!is_gated(&module, name));
}

/// The real minter must use the same And/Or semantics the independent
/// pinned consumer already rechecks; a hand-authored comparand is insufficient.
#[test]
fn ws6_6_mask_real_minter_certifies_and_independent_consumer_rechecks() {
    let (report, module) = mint(mask_module(), "mask", mask_source());
    assert_eq!(report.certified, ["mask"], "{report:?}");
    assert!(
        report.refused.is_empty() && report.skipped.is_empty(),
        "{report:?}"
    );
    assert!(is_gated(&module, "mask"));
    assert!(validate_module_for_codegen(&module).is_empty());
}

#[test]
fn ws6_6_mask_real_minter_refuses_operator_substitution() {
    let mut module = mask_module();
    let Inst::BinOp { op, .. } = &mut module.functions[0].blocks[0].body[0].inst else {
        panic!("mask's first instruction is its And");
    };
    *op = BinOp::Or;
    assert_scalar_equation_type_mismatch(module, "mask", mask_source());
}

#[test]
fn ws6_6_mask_real_minter_refuses_literal_substitution() {
    let mut module = mask_module();
    let Inst::Const { value, .. } = &mut module.functions[0].blocks[0].body[1].inst else {
        panic!("mask's second instruction is its literal");
    };
    *value = Constant::Int(3);
    assert_scalar_equation_type_mismatch(module, "mask", mask_source());
}

// ---- eager division ---------------------------------------------------------------

/// `select(b == 0, 0, udiv a b)` is SKIPPED by the minter and a forged
/// certificate for it (Lean's `if b = 0 then 0 else a / b`, which Clean's
/// kernel accepts) is REFUSED by the pinned trust-ir. Lean's `x / 0 = 0`
/// must be a CondBr diamond with `DivNonZero` on the `udiv`, never an eager
/// `udiv` under a `select` (ub-numerics-policy §1). At trust-ir 4f09dab8 the
/// re-checker admits the `icmp` (WS1.15 S1) and refuses at the `udiv` itself,
/// "UDiv divisor %1 is not provably nonzero" — the policy's own reason; the
/// 7b9146ba pin refused one instruction earlier, at the `icmp` it lacked.
#[test]
fn ws6_6_eager_udiv_under_select_is_skipped_and_refused() {
    let (report, module) = mint(eager_div_module(), "quot", quot_source());
    assert!(report.certified.is_empty(), "{report:?}");
    assert!(
        report
            .skipped
            .iter()
            .any(|(n, r)| n == "quot" && r.contains("ICmp")),
        "the minter must skip the eager-division body: {report:?}"
    );
    assert!(!is_gated(&module, "quot"));

    let (a, b) = (KExpr::bvar(1), KExpr::bvar(0));
    let lean_div = {
        let motive = KExpr::lam(
            BinderInfo::Default,
            KExpr::const_str("Bool"),
            KExpr::const_str("Nat"),
        );
        KExpr::apps(
            KExpr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(Level::zero())],
            ),
            [
                motive,
                nat2("Nat.div", a, b.clone()),
                nat_lit(0),
                nat2("Nat.beq", b, nat_lit(0)),
            ],
        )
    };
    let mut forged = eager_div_module();
    forge_widened_certificate(&mut forged, "quot", &lean_div, &lean_div);
    let errors = validate_module_for_codegen(&forged);
    assert!(
        recheck_refused(&forged, "quot", &errors, "is not provably nonzero"),
        "the pinned re-checker must refuse the eager-division body: {errors:?}"
    );
}

// ---- shared golden fixture ------------------------------------------------------

/// The committed golden file shared with trust-ir's mirror (WS1.15).
const GOLDEN: &str = include_str!("../tests/fixtures/tv_golden/statements.txt");

fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    bytes.iter().fold(String::new(), |mut s, b| {
        let _ = write!(s, "{b:02x}");
        s
    })
}

/// One golden fixture: the function whose statement is recorded, its
/// module, and the originals the minter is given (a caller's callees too).
type GoldenFixture = (&'static str, Module, Vec<(String, KExpr)>);

/// The fixture corpus: every emitted shape the pinned re-checker knows
/// (Fragment-2 arithmetic, the Fragment-3a diamond, the Fragment-3b
/// composition), plus the source-side let. Hand-built modules, so an
/// unrelated emitter change cannot churn the golden.
fn golden_corpus() -> Vec<GoldenFixture> {
    let mut arith = HeapFx::new(2);
    let m = arith.bin(BinOp::Mul, arith.param(1), arith.param(0));
    let r = arith.bin(BinOp::Add, arith.param(0), m);
    let w32 = arith.finish("w32", r);
    let w32_src = lam_n(
        2,
        uadd(KExpr::bvar(1), umul(KExpr::bvar(0), KExpr::bvar(1))),
    );
    let (helper, caller) = helper_caller_decls();
    let composed = emit_trust_ir(&[helper, caller]).expect("lowers");
    let one = |n: &str, e: KExpr| vec![(n.to_string(), e)];
    vec![
        (
            "sqLet",
            sqlet_module(BinOp::Mul),
            one("sqLet", sqlet_source(1, false)),
        ),
        ("w32", w32, one("w32", w32_src)),
        (
            "cf",
            cf_demo_emitted_module(),
            one("cf", cf_demo_original()),
        ),
        (
            "caller",
            composed,
            vec![
                ("helper".to_string(), helper_original()),
                ("caller".to_string(), caller_original()),
            ],
        ),
    ]
}

/// Render one golden record: the module text, then the comparand and the
/// kernel statement exactly as the minter serializes them (bincode of the
/// kernel `Expr`). The trust-ir mirror must re-derive the same statement
/// bytes from the same module text and comparand.
fn golden_record((name, module, originals): GoldenFixture) -> String {
    let mut minted = module.clone();
    let report = certify_backend_translation(&mut minted, &originals);
    assert!(
        report.certified.iter().any(|n| n == name) && report.refused.is_empty(),
        "golden corpus must certify `{name}`: {report:?}"
    );
    let func = module.functions.iter().find(|f| f.name == name).unwrap();
    let lhs = denote_function(&module, func).expect("in fragment");
    let oid = minted
        .proof_obligations
        .iter()
        .find(|o| o.function == Some(func.id))
        .expect("the fixture's obligation")
        .id;
    let context = minted
        .proof_certificates
        .iter()
        .find_map(|c| match &c.evidence {
            ProofEvidence::CleanCic { context, .. } if c.obligation == oid => Some(context.clone()),
            _ => None,
        })
        .expect("a CleanCic certificate");
    let mut rhs: KExpr = bincode::deserialize(&context).expect("comparand decodes");
    for _ in 0..lhs.callees.len() + lhs.arity {
        let ExprKind::Lam(_, _, inner) = rhs.kind() else {
            panic!("comparand binder")
        };
        rhs = inner.as_ref().clone();
    }
    let arities: Vec<usize> = lhs.callees.iter().map(|(_, a)| *a).collect();
    let stmt = tv_statement(&arities, lhs.arity, &lhs.body, &rhs);
    format!(
        "=== {name}\n--- module\n{module}--- comparand\n{}\n--- statement\n{}\n",
        hex(&context),
        hex(&bincode::serialize(&stmt).unwrap())
    )
}

/// MUTATION CONTROL (drift): the committed golden statement bytes are
/// reproduced exactly. trust-ir commits the same file and asserts its mirror
/// re-derives the same statement bytes from the same module text and
/// comparand, so a vocabulary change on either side fails one of the two.
/// Regenerate deliberately with `CLEAN_TV_GOLDEN_WRITE=1`; that run writes the
/// file and then FAILS, so re-run without the variable to check the new bytes.
#[test]
fn ws6_6_shared_golden_statement_bytes() {
    let rendered: String = golden_corpus().into_iter().map(golden_record).collect();
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/tv_golden/statements.txt"
    );
    if std::env::var_os("CLEAN_TV_GOLDEN_WRITE").is_some() {
        std::fs::write(path, &rendered).expect("write golden");
        // GOLDEN is `include_str!`'d at compile time, so this run cannot check
        // the bytes it just wrote: fail loudly rather than report `ok` with
        // the drift assertion never having run.
        panic!(
            "CLEAN_TV_GOLDEN_WRITE: regenerated {path}; move trust-ir's copy in lockstep, \
             unset the variable and re-run so the drift check actually executes"
        );
    }
    assert!(
        rendered == GOLDEN,
        "TV golden drifted from {path}; if the vocabulary change is deliberate, \
         regenerate with CLEAN_TV_GOLDEN_WRITE=1 and move trust-ir's copy in lockstep"
    );
}

/// The golden records re-check at the PINNED trust-ir: each minted module is
/// accepted for codegen, so the shared file only ever holds statements the
/// mirror already re-derives.
#[test]
fn ws6_6_golden_corpus_is_accepted_by_the_pinned_mirror() {
    for (name, mut module, originals) in golden_corpus() {
        let report = certify_backend_translation(&mut module, &originals);
        assert_eq!(
            report.certified.len(),
            originals.len(),
            "`{name}`: {report:?}"
        );
        let errors = validate_module(&module);
        assert!(errors.is_empty(), "`{name}`: {errors:?}");
        let errors = validate_module_for_codegen(&module);
        assert!(errors.is_empty(), "`{name}` for codegen: {errors:?}");
    }
}

// ---- the real pipeline ------------------------------------------------------------

/// POSITIVE, real source: the proof program's `sqLet` (`p03_let`) through the
/// full pipeline at `-O1` and `-O2` is kernel-certified, licensed, and its
/// certificate passes the pinned trust-ir's structural validation (which
/// re-runs the kernel judgment). At `-O0` the emitted body still calls the
/// class-method shims, so it stays skipped on the EMITTED side — never on
/// the source `let` any more.
#[test]
fn ws6_6_sqlet_real_source_certifies_at_o1_o2() {
    use crate::pass_manager::{compile_lcnf_to_trust_ir_with_report, PipelineConfig};
    use crate::rc_repair::e2e_support::{closure_decls_of, elaborated_env_with, o0};
    let source = "def sqLet (a : UInt64) : UInt64 := let t := a + 1; t * t\n";
    let cfg = crate::emit_trust_ir::TrustIrConfig {
        module_name: "ws6_6".to_string(),
        use_clean_dialect: true,
        runtime_lowering: crate::emit_trust_ir::RuntimeLowering::ExternCalls,
        certify_translation: true,
        ..crate::emit_trust_ir::TrustIrConfig::default()
    };
    let o2 = PipelineConfig {
        opt: crate::opt::OptConfig::aggressive(),
        rc: crate::rc::RCConfig::aggressive(),
        boxing: crate::boxing::BoxingConfig::default(),
    };
    let env = elaborated_env_with(source);
    for (level, pipeline) in [("-O1", PipelineConfig::default()), ("-O2", o2)] {
        let decls = closure_decls_of(&env, &pipeline, &["sqLet"]);
        let (module, report) = compile_lcnf_to_trust_ir_with_report(&decls, &env, &pipeline, &cfg)
            .expect("sqLet lowers and mints");
        assert!(
            report.certified.iter().any(|n| n == "sqLet"),
            "{level}: {report:?}"
        );
        assert!(is_gated(&module, "sqLet"), "{level}: licensed");
        let errors = validate_module(&module);
        assert!(errors.is_empty(), "{level}: pinned re-check: {errors:?}");
    }
    let decls = closure_decls_of(&env, &o0(), &["sqLet"]);
    let (_, report) = compile_lcnf_to_trust_ir_with_report(&decls, &env, &o0(), &cfg)
        .expect("sqLet lowers at -O0");
    let reason = report
        .skipped
        .iter()
        .find(|(n, _)| n == "sqLet")
        .map(|(_, r)| r.as_str())
        .unwrap_or_else(|| panic!("-O0 skips sqLet: {report:?}"));
    assert!(reason.starts_with("emitted side:"), "-O0: {reason}");
}

// ---- review: adversarial let shapes --------------------------------------------

fn usub(a: KExpr, b: KExpr) -> KExpr {
    KExpr::apps(KExpr::const_str("UInt32.sub"), [a, b])
}

fn let_u32(name: &str, value: KExpr, body: KExpr) -> KExpr {
    KExpr::let_named(Name::from_string(name), u32ty(), value, body, false)
}

/// `%2 = sub %lhs %rhs; ret %2` over two `U32` parameters.
fn sub_module(swap: bool) -> Module {
    let mut b = HeapFx::new(2);
    let (x, y) = if swap {
        (b.param(1), b.param(0))
    } else {
        (b.param(0), b.param(1))
    };
    let r = b.bin(BinOp::Sub, x, y);
    b.finish("subLet", r)
}

/// `fun a b => let t := a; t - b` — inside the let `bvar 0` is `t`, `bvar 1`
/// is `b` and `bvar 2` is `a`. A denoter that forgot to shift a parameter
/// index past the enclosing let would read `bvar 1` as `a` (giving `a - a`);
/// at arity 1 that slip escapes the telescope and only skips, so it takes a
/// second, non-commutative parameter to turn it into a wrong certificate.
fn sub_let_source() -> KExpr {
    lam_n(
        2,
        let_u32("t", KExpr::bvar(1), usub(KExpr::bvar(0), KExpr::bvar(1))),
    )
}

/// REVIEW (de Bruijn at arity 2): the let-shifted parameter names `b`, and
/// the pinned trust-ir re-checks the certificate.
#[test]
fn ws6_6_review_let_shifts_parameter_indices_at_arity_two() {
    let (report, module) = mint(sub_module(false), "subLet", sub_let_source());
    assert_eq!(report.certified, ["subLet"], "{report:?}");
    let errors = validate_module_for_codegen(&module);
    assert!(errors.is_empty(), "pinned re-check: {errors:?}");
}

/// REVIEW twin: the emitted `sub b a` must be REFUSED against `let t := a;
/// t - b` — the case an unshifted parameter index would confuse.
#[test]
fn ws6_6_review_let_arity_two_refuses_swapped_operands() {
    assert_kernel_refuses(sub_module(true), "subLet", sub_let_source());
}

/// `%1 = 1; %2 = add %0 %1; %3 = mul %2 %2; %4 = sub %3 %2; ret %4`.
fn nested_let_module() -> Module {
    let mut b = HeapFx::new(1);
    let one = b.cu32(1);
    let s = b.bin(BinOp::Add, b.param(0), one);
    let t = b.bin(BinOp::Mul, s, s);
    let r = b.bin(BinOp::Sub, t, s);
    b.finish("nested", r)
}

/// `fun a => let s := a + 1; let t := s * s; <body>`, where inside `body`
/// `bvar 0` is `t`, `bvar 1` is `s` and `bvar 2` is `a`.
fn nested_let_source(body: KExpr) -> KExpr {
    let s_val = uadd(KExpr::bvar(0), of_nat(1));
    let t_val = umul(KExpr::bvar(0), KExpr::bvar(0));
    lam_n(1, let_u32("s", s_val, let_u32("t", t_val, body)))
}

/// REVIEW (nested lets): an inner let's value reads the OUTER let, and the
/// body reads both — `t - s` certifies and re-checks at the pinned trust-ir.
#[test]
fn ws6_6_review_nested_lets_certify() {
    let src = nested_let_source(usub(KExpr::bvar(0), KExpr::bvar(1)));
    let (report, module) = mint(nested_let_module(), "nested", src);
    assert_eq!(report.certified, ["nested"], "{report:?}");
    let errors = validate_module_for_codegen(&module);
    assert!(errors.is_empty(), "pinned re-check: {errors:?}");
}

/// REVIEW twin: the environment order is load-bearing — `s - t` (the two
/// lets read in reverse) must be REFUSED against the emitted `t - s`.
#[test]
fn ws6_6_review_nested_lets_refuse_reversed_environment() {
    let src = nested_let_source(usub(KExpr::bvar(1), KExpr::bvar(0)));
    assert_kernel_refuses(nested_let_module(), "nested", src);
}

/// `fun x => let t := x + 1; cond (UInt32.blt c 10) t x`, with the
/// comparison operand `c` supplied (inside the let `bvar 0` = `t`,
/// `bvar 1` = `x`).
fn cf_let_source(cmp_operand: KExpr) -> KExpr {
    let cond = KExpr::apps(KExpr::const_str("UInt32.blt"), [cmp_operand, of_nat(10)]);
    let ite = KExpr::apps(
        KExpr::const_str("cond"),
        [u32ty(), cond, KExpr::bvar(0), KExpr::bvar(1)],
    );
    lam_n(1, let_u32("t", uadd(KExpr::bvar(0), of_nat(1)), ite))
}

/// REVIEW (let reaches the comparison and the arms): the Fragment-3a
/// diamond `if x < 10 then x + 1 else x` certifies from a source that
/// hoists `x + 1` into a let above the conditional.
#[test]
fn ws6_6_review_let_above_a_conditional_certifies() {
    let (report, module) = mint(
        cf_demo_emitted_module(),
        "cf",
        cf_let_source(KExpr::bvar(1)),
    );
    assert_eq!(report.certified, ["cf"], "{report:?}");
    let errors = validate_module_for_codegen(&module);
    assert!(errors.is_empty(), "pinned re-check: {errors:?}");
}

/// REVIEW twin: the comparison reads the LET (`x + 1 < 10`) rather than the
/// parameter — a different condition, which the kernel must REFUSE.
#[test]
fn ws6_6_review_let_in_comparison_refuses_wrong_operand() {
    assert_kernel_refuses(
        cf_demo_emitted_module(),
        "cf",
        cf_let_source(KExpr::bvar(0)),
    );
}

/// REVIEW (fail-closed): a let at ANOTHER `UIntW` (a `UInt64` binding in the
/// `U32` fragment) is out of fragment — the value would be denoted mod 2^32
/// while the source computes it mod 2^64. A SKIP, never a mint.
#[test]
fn ws6_6_review_let_at_another_width_is_skipped() {
    let value = KExpr::apps(
        KExpr::const_str("UInt64.add"),
        [
            KExpr::bvar(0),
            KExpr::app(KExpr::const_str("UInt64.ofNat"), KExpr::nat_lit(1)),
        ],
    );
    let src = lam_n(
        1,
        KExpr::let_named(
            Name::from_string("t"),
            KExpr::const_str("UInt64"),
            value,
            umul(KExpr::bvar(1), KExpr::bvar(1)),
            false,
        ),
    );
    assert_walker_skips(
        sqlet_module(BinOp::Mul),
        "sqLet",
        src,
        "source let binding at type UInt64",
    );
}

/// A valid HAdd dictionary may store subtraction: a theorem about the wrong
/// source denotation would otherwise be accepted even by the independent IR
/// consumer. Its checked source must certify only the correctly emitted Sub.
#[test]
fn source_instance_field_real_minter_refuses_wrong_operation_and_certifies_actual_field() {
    let u = u32ty();
    let dictionary = KExpr::apps(
        KExpr::const_(Name::from_string("HAdd.mk"), vec![Level::zero(); 3]),
        [
            u.clone(),
            u.clone(),
            u.clone(),
            KExpr::const_str("UInt32.sub"),
        ],
    );
    let source = lam_n(
        2,
        KExpr::apps(
            KExpr::const_(Name::from_string("HAdd.hAdd"), vec![Level::zero(); 3]),
            [
                u.clone(),
                u.clone(),
                u.clone(),
                dictionary,
                KExpr::bvar(1),
                KExpr::bvar(0),
            ],
        ),
    );
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("customField"),
        level_params: vec![],
        type_: KExpr::arrow(u.clone(), KExpr::arrow(u.clone(), u)),
        value: source.clone(),
        is_reducible: true,
    })
    .expect("actual kernel checked source");
    let mut wrong = HeapFx::new(2);
    let result = wrong.bin(BinOp::Add, wrong.param(0), wrong.param(1));
    assert_scalar_equation_type_mismatch(
        wrong.finish("customField", result),
        "customField",
        source.clone(),
    );
    let mut honest = HeapFx::new(2);
    let result = honest.bin(BinOp::Sub, honest.param(0), honest.param(1));
    let (report, module) = mint(honest.finish("customField", result), "customField", source);
    assert_eq!(report.certified, ["customField"], "{report:?}");
    assert!(
        report.refused.is_empty() && report.skipped.is_empty(),
        "{report:?}"
    );
    assert!(is_gated(&module, "customField"));
    let errors = validate_module_for_codegen(&module);
    assert!(
        errors.is_empty(),
        "the independent consumer must accept the actual scalar certificate: {errors:?}"
    );
}

#[test]
fn source_instance_field_real_minter_refuses_index_instead_of_actual_literal() {
    let u = u32ty();
    let dictionary = KExpr::apps(
        KExpr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]),
        [u.clone(), KExpr::nat_lit(7), of_nat(8)],
    );
    let source = KExpr::apps(
        KExpr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [u.clone(), KExpr::nat_lit(7), dictionary],
    );
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("customLiteral"),
        level_params: vec![],
        type_: u,
        value: source.clone(),
        is_reducible: true,
    })
    .unwrap();
    let mut wrong = HeapFx::new(0);
    let seven = wrong.cu32(7);
    assert_scalar_equation_type_mismatch(
        wrong.finish("customLiteral", seven),
        "customLiteral",
        source.clone(),
    );
    let mut honest = HeapFx::new(0);
    let eight = honest.cu32(8);
    let (report, module) = mint(
        honest.finish("customLiteral", eight),
        "customLiteral",
        source,
    );
    assert_eq!(report.certified, ["customLiteral"], "{report:?}");
    assert!(
        report.refused.is_empty() && report.skipped.is_empty(),
        "{report:?}"
    );
    assert!(is_gated(&module, "customLiteral"));
    let errors = validate_module_for_codegen(&module);
    assert!(
        errors.is_empty(),
        "the independent consumer must accept the actual scalar certificate: {errors:?}"
    );
}

/// The outer source expression has only legacy names. Its checked named
/// dictionary hides a distinct escaped constant whose DISPLAY is UInt32.add
/// but whose actual body is UInt32.sub. A forged Add emission must get no TV.
#[test]
fn source_instance_hidden_name_cannot_mint_a_wrong_operation_license() {
    let mut env = Environment::with_prelude();
    let u = u32ty();
    let hidden = Name::anon().str("UInt32.add");
    env.add_decl(Declaration::Definition {
        name: hidden.clone(),
        level_params: vec![],
        type_: KExpr::arrow(u.clone(), KExpr::arrow(u.clone(), u.clone())),
        value: KExpr::const_str("UInt32.sub"),
        is_reducible: true,
    })
    .unwrap();
    let dictionary_name = Name::from_string("TVReview.hiddenDictionary");
    env.add_decl(Declaration::Definition {
        name: dictionary_name.clone(),
        level_params: vec![],
        type_: KExpr::apps(
            KExpr::const_(Name::from_string("HAdd"), vec![Level::zero(); 3]),
            [u.clone(), u.clone(), u.clone()],
        ),
        value: KExpr::apps(
            KExpr::const_(Name::from_string("HAdd.mk"), vec![Level::zero(); 3]),
            [
                u.clone(),
                u.clone(),
                u.clone(),
                KExpr::const_(hidden, vec![]),
            ],
        ),
        is_reducible: true,
    })
    .unwrap();
    let source = lam_n(
        2,
        KExpr::apps(
            KExpr::const_(Name::from_string("HAdd.hAdd"), vec![Level::zero(); 3]),
            [
                u.clone(),
                u.clone(),
                u.clone(),
                KExpr::const_(dictionary_name, vec![]),
                KExpr::bvar(1),
                KExpr::bvar(0),
            ],
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("hiddenInstance"),
        level_params: vec![],
        type_: KExpr::arrow(u.clone(), KExpr::arrow(u.clone(), u)),
        value: source.clone(),
        is_reducible: true,
    })
    .expect("the complete original source is a checked definition");
    assert!(crate::emit_trust_ir::names::legacy_source_identity_supported(&source));
    let mut wrong = HeapFx::new(2);
    let result = wrong.bin(BinOp::Add, wrong.param(0), wrong.param(1));
    let mut module = wrong.finish("hiddenInstance", result);
    let report = certify_backend_translation_in_environment(
        &mut module,
        &[("hiddenInstance".to_string(), source)],
        &env,
    );
    assert!(report.certified.is_empty(), "{report:?}");
    assert!(
        report
            .skipped
            .iter()
            .any(|(name, why)| name == "hiddenInstance" && why.contains("escaped typed names")),
        "{report:?}"
    );
    assert!(!is_gated(&module, "hiddenInstance"));
    assert!(module.proof_certificates.is_empty());
}
