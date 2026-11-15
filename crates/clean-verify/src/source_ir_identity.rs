// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Closed SOURCE-model / supplied reflected IR entry mathematics, not a compiler
//! certificate. Actual Rust frontend/THIR faithfulness, complete source custody,
//! physical entry ABI and SourceNoUB remain separate unproved premises.
//!
//! The caller independently derives `expected` from its actual module/source
//! custody. The packet cannot choose the expected subject. Raw subject data is
//! untrusted: only the reconstructed universal semantic proposition is proved.
use clean_kernel::expr::FVarId;
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker};
use clean_rust_sem::source_identity_kernel::{install_source_model, project_identity_source};

/// Untrusted mathematical subject; this does NOT authenticate module association.
/// The IR consumer must derive it from its private typed original-module witness.
/// These fields are DATA, not a token of
/// Rustc/TCX authority. A real compiler must supply its original checked owner,
/// Instance, body and reflection; this standalone API cannot authenticate TCX.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawIdentitySubject {
    pub original_source: String,
    pub original_function: String,
    pub original_instance: String,
    /// Full original module encoding, not a claimed digest or an effect census.
    pub module_bytes: Vec<u8>,
    pub ir_function_name: String,
    pub function_id: u32,
    pub function_type_id: u32,
    pub entry_block: u32,
    pub parameter_value: u32,
    pub return_value: u32,
    /// Exact common core_reflection image, including actual cc3 and all tables.
    pub reflected_context: Expr,
}

/// Producer-supplied untrusted transport. Replay compares the COMPLETE subject
/// with independently supplied expected data and checks the original proof term.
#[derive(Debug, Clone)]
pub struct IdentityPacket {
    pub subject: RawIdentitySubject,
    pub proof: Expr,
}

/// Retains checked mathematics about the supplied context only. Original-module
/// association must remain with the IR consumer's typed witness; hashing or raw
/// expected-data equality cannot establish it. No actual-module custody is minted.
/// Retains a checked mathematical connection only. No authority/grade/appender
/// conversion exists, and a logical Rust entry is not a physical ABI theorem.
#[derive(Debug)]
pub struct CheckedIdentityMathematics {
    subject: RawIdentitySubject,
    source_digest: String,
    module_digest: String,
    claim: Expr,
    proof: Expr,
}
impl CheckedIdentityMathematics {
    pub fn subject(&self) -> &RawIdentitySubject {
        &self.subject
    }
    pub fn source_digest(&self) -> &str {
        &self.source_digest
    }
    pub fn module_digest(&self) -> &str {
        &self.module_digest
    }
    pub fn claim(&self) -> &Expr {
        &self.claim
    }
    pub fn proof(&self) -> &Expr {
        &self.proof
    }
}
fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn f(id: u64) -> Expr {
    Expr::fvar(FVarId::new(id))
}
fn close(bs: &[(u64, Expr)], body: Expr, lambda: bool) -> Expr {
    bs.iter().rev().fold(body, |body, (id, ty)| {
        let body = body.abstract_fvar(FVarId::new(*id));
        if lambda {
            Expr::lam(BinderInfo::Default, ty.clone(), body)
        } else {
            Expr::pi(BinderInfo::Default, ty.clone(), body)
        }
    })
}
fn list(ty: &str, values: impl IntoIterator<Item = Expr>) -> Expr {
    let values: Vec<_> = values.into_iter().collect();
    values
        .into_iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, head| {
            app("IRList.cons", [c(ty), head, tail])
        })
}
fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}

/// Actual universal IR endpoint, independently reconstructed rather than read
/// from the proof. The arbitrary environment contributes its original slot0;
/// full64 input admission and genuine pre-memory validity are named premises.
/// They do not assume successful execution or its result. Providers are arbitrary
/// and unreachable in this closed leaf. Final retirement is retained exactly.
fn ir_parts(subject: &RawIdentitySubject) -> Result<(Vec<(u64, Expr)>, Expr, Expr), String> {
    if subject.reflected_context.has_fvar_quick() || subject.reflected_context.has_loose_bvars() {
        return Err("open reflected context".into());
    }
    let rho = f(0);
    let w = f(1);
    let mem = f(2);
    let host = f(3);
    let providers = f(4);
    let word = Expr::app(rho.clone(), Expr::nat_lit(0));
    let values = list("IRScalar", [app("IRScalar.int_", [word.clone()])]);
    let owner = app("ir_byte_fresh_owner_v1", [mem.clone()]);
    let init = app(
        "ir_rust_u64_init_v1",
        [
            w.clone(),
            subject.reflected_context.clone(),
            Expr::nat_lit(subject.function_id as u64),
            values.clone(),
            mem.clone(),
            host.clone(),
        ],
    );
    let actual = app(
        "ir_byte_run_v1",
        [
            w.clone(),
            subject.reflected_context.clone(),
            providers.clone(),
            Expr::nat_lit(1),
            init,
        ],
    );
    let world = app(
        "IRByteWorldV1.mk",
        [
            w.clone(),
            app("ir_byte_retire_v1", [owner.clone(), mem.clone()]),
            host.clone(),
            list("Nat", []),
            app("Nat.succ", [owner.clone()]),
        ],
    );
    let expected = app(
        "IRByteConfigV1.halted",
        [w.clone(), app("IROutcome.ret", [values]), world],
    );
    let memory_guard = app(
        "ir_byte_memory_owners_v1",
        [mem.clone(), list("Nat", []), owner],
    );
    let input_guard = app(
        "ir_nat_ltb",
        [word, app("ir_nat_pow2", [Expr::nat_lit(64)])],
    );
    let bs = [
        (0, Expr::arrow(c("Nat"), c("Nat"))),
        (1, Expr::type_()),
        (2, c("IRByteMemoryV1")),
        (3, w.clone()),
        (4, app("IRByteProvidersV1", [w.clone()])),
        (5, eq(c("Bool"), memory_guard, c("Bool.true"))),
        (6, eq(c("Bool"), input_guard, c("Bool.true"))),
    ];
    Ok((bs.to_vec(), actual, expected))
}

const MATCH: &str = "RustSourceIRV1.ScalarReturn";
const MATCHED: &str = "RustSourceIRV1.ScalarReturn.matched";

pub fn ir_claim(subject: &RawIdentitySubject) -> Result<Expr, String> {
    let (bs, actual, expected) = ir_parts(subject)?;
    Ok(close(
        &bs,
        eq(app("IRByteConfigV1", [f(1)]), actual, expected),
        false,
    ))
}
fn match_term(source: Expr, ir: Expr) -> Expr {
    app(
        MATCH,
        [
            f(1),
            f(2),
            f(3),
            Expr::app(f(0), Expr::nat_lit(0)),
            source,
            ir,
        ],
    )
}
fn source_parts(subject: &RawIdentitySubject) -> Result<(Expr, Expr, Expr), String> {
    let source = project_identity_source(&subject.original_source).map_err(|e| e.to_string())?;
    if source.function() != subject.original_function
        || subject.original_instance.is_empty()
        || subject.module_bytes.is_empty()
        || subject.ir_function_name.is_empty()
    {
        return Err("incomplete original source/IR mathematical input".into());
    }
    let ty = app("RustSem.SourceIdentityV1.Exit", [f(1)]);
    let actual = app(
        "RustSem.SourceIdentityV1.run",
        [
            f(1),
            source.body().reflect().map_err(|e| e.to_string())?,
            f(0),
            f(3),
        ],
    );
    let expected = app(
        "RustSem.SourceIdentityV1.Exit.returned",
        [
            f(1),
            Expr::app(f(0), Expr::nat_lit(0)),
            f(3),
            Expr::app(
                Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                c("Nat"),
            ),
        ],
    );
    Ok((ty, actual, expected))
}

/// One composed relation, with the same source environment, input, arbitrary
/// world and EXACT retired IR endpoint in its indices. This is not merely a
/// conjunction whose connection is left to a reader's interpretation.
pub fn claim(subject: &RawIdentitySubject) -> Result<Expr, String> {
    let (bs, ir, _) = ir_parts(subject)?;
    let (_, source, _) = source_parts(subject)?;
    Ok(close(&bs, match_term(source, ir), false))
}
fn eq_app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![Level::succ(Level::zero())]),
        args,
    )
}

/// Untrusted composition candidate: transport the existing independent source
/// adequacy theorem and actual IR entry/run proof into ONE scalar-return relation.
pub fn candidate(subject: &RawIdentitySubject, ir_proof: Expr) -> Result<Expr, String> {
    let source = project_identity_source(&subject.original_source).map_err(|e| e.to_string())?;
    let (bs, ir_actual, ir_expected) = ir_parts(subject)?;
    let (src_ty, src_actual, src_expected) = source_parts(subject)?;
    let h_source = Expr::apps(
        source.proof_candidate().map_err(|e| e.to_string())?,
        [f(0), f(1), f(3)],
    );
    let h_ir = Expr::apps(ir_proof, bs.iter().map(|(id, _)| f(*id)));
    let ir_ty = app("IRByteConfigV1", [f(1)]);
    let matched = app(
        MATCHED,
        [f(1), f(2), f(3), Expr::app(f(0), Expr::nat_lit(0))],
    );
    let ir_motive = close(
        &[(20, ir_ty.clone())],
        match_term(src_expected.clone(), f(20)),
        true,
    );
    let with_ir = eq_app(
        "Eq.subst",
        [
            ir_ty.clone(),
            ir_motive,
            ir_expected.clone(),
            ir_actual.clone(),
            eq_app("Eq.symm", [ir_ty, ir_actual.clone(), ir_expected, h_ir]),
            matched,
        ],
    );
    let src_motive = close(&[(21, src_ty.clone())], match_term(f(21), ir_actual), true);
    let proof = eq_app(
        "Eq.subst",
        [
            src_ty.clone(),
            src_motive,
            src_expected.clone(),
            src_actual.clone(),
            eq_app("Eq.symm", [src_ty, src_actual, src_expected, h_source]),
            with_ir,
        ],
    );
    Ok(close(&bs, proof, true))
}

pub(crate) fn install_relation(env: &mut Environment) -> Result<(), String> {
    use clean_kernel::{Constructor, InductiveDecl, InductiveType};
    let w = f(1);
    let mem = f(2);
    let host = f(3);
    let value = f(4);
    let source_ty = app("RustSem.SourceIdentityV1.Exit", [w.clone()]);
    let ir_ty = app("IRByteConfigV1", [w.clone()]);
    let base = [
        (1, Expr::type_()),
        (2, c("IRByteMemoryV1")),
        (3, w.clone()),
        (4, c("Nat")),
    ];
    let mut all = base.to_vec();
    all.push((5, source_ty));
    all.push((6, ir_ty));
    let ty = close(&all, Expr::sort(Level::zero()), false);
    let returned = app(
        "RustSem.SourceIdentityV1.Exit.returned",
        [
            w.clone(),
            value.clone(),
            host.clone(),
            Expr::app(
                Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                c("Nat"),
            ),
        ],
    );
    let owner = app("ir_byte_fresh_owner_v1", [mem.clone()]);
    let world = app(
        "IRByteWorldV1.mk",
        [
            w.clone(),
            app("ir_byte_retire_v1", [owner.clone(), mem.clone()]),
            host.clone(),
            list("Nat", []),
            app("Nat.succ", [owner]),
        ],
    );
    let halted = app(
        "IRByteConfigV1.halted",
        [
            w.clone(),
            app(
                "IROutcome.ret",
                [list("IRScalar", [app("IRScalar.int_", [value.clone()])])],
            ),
            world,
        ],
    );
    let ctor = close(
        &base,
        app(MATCH, [w, mem, host, value, returned, halted]),
        false,
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string(MATCH),
            type_: ty,
            constructors: vec![Constructor {
                name: Name::from_string(MATCHED),
                type_: ctor,
            }],
        }],
    })
    .map_err(|e| format!("source/IR relation: {e:?}"))
}

pub fn environment() -> Result<Environment, String> {
    let mut spec = crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
        .map_err(|e| e.to_string())?
        .into_rust_u64_logical_entry_v1()
        .map_err(|e| e.to_string())?;
    install_source_model(spec.env_mut()).map_err(|e| e.to_string())?;
    install_relation(spec.env_mut())?;
    Ok(spec.into_environment())
}

pub fn replay(
    expected: &RawIdentitySubject,
    packet: &IdentityPacket,
) -> Result<CheckedIdentityMathematics, String> {
    if expected != &packet.subject {
        return Err("original source/actual IR subject mismatch".into());
    }
    let claim = claim(expected)?;
    if packet.proof.has_fvar_quick() || packet.proof.has_loose_bvars() {
        return Err("open connection proof".into());
    }
    let env = environment()?;
    let mut checker = TypeChecker::new(&env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .map_err(|e| format!("claim: {e:?}"))?;
    checker
        .check_type(&packet.proof, &claim)
        .map_err(|e| format!("proof: {e:?}"))?;
    if checker.heartbeat_spent() || clean_kernel::tc::declaration_budget_exhausted() {
        return Err("resource stop is not a verdict".into());
    }
    let audit = env.audit_certification(&claim, &packet.proof);
    if !audit.is_certified() {
        return Err(format!("audit: {audit:?}"));
    }
    for name in audit.dependencies {
        for deps in [
            env.axiom_deps(&name),
            env.foundational_axiom_deps(&name),
            env.trust_marker_deps(&name),
        ] {
            if !deps.ok_or("missing dependency closure")?.is_empty() {
                return Err("axiom or marker in connection".into());
            }
        }
    }
    Ok(CheckedIdentityMathematics {
        subject: expected.clone(),
        source_digest: blake3::hash(expected.original_source.as_bytes())
            .to_hex()
            .to_string(),
        module_digest: blake3::hash(&expected.module_bytes).to_hex().to_string(),
        claim,
        proof: packet.proof.clone(),
    })
}
