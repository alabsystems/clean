// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Historical conditional SOURCE/ByteV1 mathematics. Original-IR scalar progress
//! now has a canonical SemR reader in `clean_olean::semr_scalar`; this interface
//! retains its original world/retirement statement and grants no conversion to
//! that distinct model or any compiler grade.
//! Closed SOURCE-model / supplied reflected IR entry mathematics, not a compiler
//! certificate. Actual Rust frontend/THIR faithfulness, complete source custody,
//! physical entry ABI and SourceNoUB remain separate unproved premises.
//!
//! The caller independently derives `expected` from its actual module/source
//! custody. The packet cannot choose the expected subject. Raw subject data is
//! untrusted: only the reconstructed universal semantic proposition is proved.
use clean_kernel::expr::FVarId;
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker};
use clean_rust_sem::source_word64_addition_kernel::{
    install_source_model, project_word64_addition_source,
};

/// Untrusted mathematical subject; this does NOT authenticate module association.
/// The IR consumer must derive it from its private typed original-module witness.
/// These fields are DATA, not a token of
/// Rustc/TCX authority. A real compiler must supply its original checked owner,
/// Instance, body and reflection; this standalone API cannot authenticate TCX.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawAdditionSubject {
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
    pub constant_value: u32,
    pub literal: u64,
    pub addition_value: u32,
    pub return_value: u32,
    /// Exact common core_reflection image, including actual cc3 and all tables.
    pub reflected_context: Expr,
}

/// Producer-supplied untrusted transport. Replay compares the COMPLETE subject
/// with independently supplied expected data and checks the original proof term.
#[derive(Debug, Clone)]
pub struct AdditionPacket {
    pub subject: RawAdditionSubject,
    pub proof: Expr,
}

/// Retains checked mathematics about the supplied context only. Original-module
/// association must remain with the IR consumer's typed witness; hashing or raw
/// expected-data equality cannot establish it. No actual-module custody is minted.
/// Retains a checked mathematical connection only. No authority/grade/appender
/// conversion exists, and a logical Rust entry is not a physical ABI theorem.
#[derive(Debug)]
pub struct CheckedAdditionMathematics {
    subject: RawAdditionSubject,
    source_digest: String,
    module_digest: String,
    claim: Expr,
    proof: Expr,
}
impl CheckedAdditionMathematics {
    pub fn subject(&self) -> &RawAdditionSubject {
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
fn ir_parts(subject: &RawAdditionSubject) -> Result<(Vec<(u64, Expr)>, Expr, Expr), String> {
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
            Expr::nat_lit(3),
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
    let output = word_add(Expr::app(rho.clone(), Expr::nat_lit(0)), subject.literal);
    let expected = app(
        "IRByteConfigV1.halted",
        [
            w.clone(),
            app(
                "IROutcome.ret",
                [list("IRScalar", [app("IRScalar.int_", [output])])],
            ),
            world,
        ],
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

pub fn ir_claim(subject: &RawAdditionSubject) -> Result<Expr, String> {
    let (bs, actual, expected) = ir_parts(subject)?;
    Ok(close(
        &bs,
        eq(app("IRByteConfigV1", [f(1)]), actual, expected),
        false,
    ))
}
fn word_add(word: Expr, literal: u64) -> Expr {
    app(
        "Nat.mod",
        [
            app("Nat.add", [word, Expr::nat_lit(literal)]),
            app("Nat.succ", [Expr::nat_lit(u64::MAX)]),
        ],
    )
}
fn match_term(subject: &RawAdditionSubject, source: Expr, ir: Expr) -> Expr {
    app(
        MATCH,
        [
            f(1),
            f(2),
            f(3),
            word_add(Expr::app(f(0), Expr::nat_lit(0)), subject.literal),
            source,
            ir,
        ],
    )
}

fn source_parts(subject: &RawAdditionSubject) -> Result<(Expr, Expr, Expr), String> {
    let source =
        project_word64_addition_source(&subject.original_source).map_err(|e| e.to_string())?;
    if source.function() != subject.original_function
        || source.literal() != subject.literal
        || subject.original_instance.is_empty()
        || subject.module_bytes.is_empty()
        || subject.ir_function_name.is_empty()
    {
        return Err("incomplete/mismatched original source/IR mathematical input".into());
    }
    let ty = app("RustSem.SourceIdentityV1.Exit", [f(1)]);
    let raw = app(
        "RustSem.SourceWord64AdditionV1.run",
        [f(1), source.body().reflect(), f(0), f(3)],
    );
    let actual = app("RustSourceWord64IRV1.observe", [f(1), raw]);
    let expected = app(
        "RustSem.SourceIdentityV1.Exit.returned",
        [
            f(1),
            word_add(Expr::app(f(0), Expr::nat_lit(0)), subject.literal),
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
pub fn claim(subject: &RawAdditionSubject) -> Result<Expr, String> {
    let (bs, ir, _) = ir_parts(subject)?;
    let (_, source, _) = source_parts(subject)?;
    Ok(close(&bs, match_term(subject, source, ir), false))
}
fn eq_app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![Level::succ(Level::zero())]),
        args,
    )
}

/// Untrusted composition candidate: transport the existing independent source
/// adequacy theorem and actual IR entry/run proof into ONE scalar-return relation.
pub fn candidate(subject: &RawAdditionSubject, ir_proof: Expr) -> Result<Expr, String> {
    let source =
        project_word64_addition_source(&subject.original_source).map_err(|e| e.to_string())?;
    let (bs, ir_actual, ir_expected) = ir_parts(subject)?;
    let (src_ty, src_actual, src_expected) = source_parts(subject)?;
    let source_equality = Expr::apps(source.proof_candidate(), [f(0), f(1), f(3)]);
    let raw_ty = app("RustSem.SourceWord64AdditionV1.Exit", [f(1)]);
    let raw_actual = app(
        "RustSem.SourceWord64AdditionV1.run",
        [f(1), source.body().reflect(), f(0), f(3)],
    );
    let raw_expected = app(
        "RustSem.SourceWord64AdditionV1.Exit.returned",
        [
            f(1),
            word_add(Expr::app(f(0), Expr::nat_lit(0)), subject.literal),
            f(3),
            Expr::app(
                Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                c("Nat"),
            ),
        ],
    );
    let h_source = app(
        "ir_eq_cong",
        [
            raw_ty,
            src_ty.clone(),
            app("RustSourceWord64IRV1.observe", [f(1)]),
            raw_actual,
            raw_expected,
            source_equality,
        ],
    );
    let h_ir = Expr::apps(ir_proof, bs.iter().map(|(id, _)| f(*id)));
    let ir_ty = app("IRByteConfigV1", [f(1)]);
    let matched = app(
        MATCHED,
        [
            f(1),
            f(2),
            f(3),
            word_add(Expr::app(f(0), Expr::nat_lit(0)), subject.literal),
        ],
    );
    let ir_motive = close(
        &[(20, ir_ty.clone())],
        match_term(subject, src_expected.clone(), f(20)),
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
    let src_motive = close(
        &[(21, src_ty.clone())],
        match_term(subject, f(21), ir_actual),
        true,
    );
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

pub fn environment() -> Result<Environment, String> {
    let mut spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
        .map_err(|e| e.to_string())?
        .into_rust_u64_logical_entry_v1()
        .map_err(|e| e.to_string())?;
    clean_rust_sem::source_identity_kernel::install_source_model(spec.env_mut())
        .map_err(|e| e.to_string())?;
    install_source_model(spec.env_mut()).map_err(|e| e.to_string())?;
    super::source_ir_identity::install_relation(spec.env_mut())?;
    for (name, source) in mathematics::LAWS {
        spec.add_recursive_def(
            source,
            "Checked original word64 source arithmetic/IR connection; no actual-module authority",
        )
        .map_err(|e| e.to_string())?;
        spec.verify_definition(name).map_err(|e| e.to_string())?;
    }
    Ok(spec.into_environment())
}
mod mathematics;

pub fn replay(
    expected: &RawAdditionSubject,
    packet: &AdditionPacket,
) -> Result<CheckedAdditionMathematics, String> {
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
    Ok(CheckedAdditionMathematics {
        subject: expected.clone(),
        source_digest: blake3::hash(expected.original_source.as_bytes())
            .to_hex()
            .to_string(),
        module_digest: blake3::hash(&expected.module_bytes).to_hex().to_string(),
        claim,
        proof: packet.proof.clone(),
    })
}
