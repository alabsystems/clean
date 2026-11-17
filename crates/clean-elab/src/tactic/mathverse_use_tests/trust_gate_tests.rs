// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::mathverse_use::{validate_dependency_loader_trust, TrustGate};
use super::*;
use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_mathverse::library::MathverseLibrary;
use clean_mathverse::premise_select::{MatchReason, PremiseCandidate};
use clean_mathverse::shard::{ShardReader, ShardWriter};
use clean_mathverse::trust::policy::TrustPolicy;
use clean_mathverse::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    TrustLevel, NO_VALUE,
};

fn build_guard_shard(constants: &[(&str, ImportConfidence, DeclKind, bool)]) -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort0 = writer.add_expr(FlatExpr::sort(l0));

    for &(name, confidence, decl_kind, has_value) in constants {
        let name_idx = writer.add_string(name);
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx: sort0,
            value_idx: if has_value { sort0 } else { NO_VALUE },
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: confidence as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
    }

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

fn premise_candidate(lib: &MathverseLibrary, idx: u32) -> PremiseCandidate {
    let header = *lib.get_constant(idx).unwrap();
    PremiseCandidate {
        name: lib.get_name(idx).unwrap().to_string(),
        constant_idx: idx,
        score: 1.0,
        source_system: SourceSystem::Lean4,
        trust_level: TrustLevel::KernelVerified,
        match_reason: MatchReason::TypeUnification,
        header,
    }
}

fn detail_from_result(result: Result<(), TacticError>) -> String {
    match result.expect_err("guard should fail closed") {
        TacticError::SearchExhausted { tactic, detail } => {
            assert_eq!(tactic, "mathverse_use");
            detail
        }
        other => panic!("expected SearchExhausted, got {other:?}"),
    }
}

/// Same, but tolerant of which tactic label the citation entry point stamps.
fn detail_from_apply_result(result: Result<(), TacticError>) -> String {
    match result.expect_err("citation should fail closed") {
        TacticError::SearchExhausted { detail, .. } => detail,
        other => panic!("expected SearchExhausted, got {other:?}"),
    }
}

/// A two-row shard: `Root.thm` (row 0) depending on `Dep` (row 1), where
/// `Dep`'s type and universe parameters are given explicitly. Everything is
/// `KernelVerified` so the confidence gate never fires and the resident-type
/// comparison is the only thing under test.
///
/// `build_dep_type` receives the writer and returns `Dep`'s `type_idx`.
fn build_resident_probe_shard(
    dep_name: &str,
    dep_kind: DeclKind,
    dep_level_params: &[&str],
    build_dep_type: impl FnOnce(&mut ShardWriter) -> u32,
    extra_rows: impl FnOnce(&mut ShardWriter),
) -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort0 = writer.add_expr(FlatExpr::sort(l0));

    let root_name = writer.add_string("Root.thm");
    writer.add_constant(MathverseConstantHeader {
        name_idx: root_name,
        type_idx: sort0,
        value_idx: sort0,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Theorem as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    let lp_start = writer.add_string_block(dep_level_params);
    let dep_type = build_dep_type(&mut writer);
    let dep_name_idx = writer.add_string(dep_name);
    let has_value = matches!(
        dep_kind,
        DeclKind::Theorem | DeclKind::Definition | DeclKind::Opaque
    );
    writer.add_constant(MathverseConstantHeader {
        name_idx: dep_name_idx,
        type_idx: dep_type,
        value_idx: if has_value { sort0 } else { NO_VALUE },
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: dep_kind as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: lp_start,
        level_params_count: u16::try_from(dep_level_params.len()).unwrap(),
        _pad2: [0u8; 26],
    });

    extra_rows(&mut writer);

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

fn probe_library(shard: &ShardReader) -> MathverseLibrary {
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(shard).unwrap();
    lib.add_dependency(0, 1);
    lib
}

/// Flatten a kernel `Level` into `writer`. Core variants only.
fn add_kernel_level(writer: &mut ShardWriter, level: &Level) -> u32 {
    match level {
        Level::Zero => writer.add_level(FlatLevel::zero()),
        Level::Succ(inner) => {
            let inner_idx = add_kernel_level(writer, inner);
            writer.add_level(FlatLevel::succ(inner_idx))
        }
        Level::Max(l, r) => {
            let li = add_kernel_level(writer, l);
            let ri = add_kernel_level(writer, r);
            writer.add_level(FlatLevel::max(li, ri))
        }
        Level::Param(name) => {
            let name_idx = writer.add_string(&name.to_string());
            writer.add_level(FlatLevel::param(name_idx))
        }
        // `FlatLevel` exposes no `imax` constructor; no test needs one.
        Level::IMax(..) => panic!("test helper cannot encode an imax level"),
    }
}

/// Flatten a kernel `Expr` into `writer`, returning its expression index.
///
/// Core variants only, and it PANICS on anything else rather than encoding
/// an approximation — a synthetic shard row that silently differs from the
/// expression the test meant would defeat the very check under test.
fn add_kernel_expr(writer: &mut ShardWriter, expr: &Expr) -> u32 {
    use clean_kernel::ExprKind;
    match expr.kind() {
        ExprKind::BVar(idx) => writer.add_expr(FlatExpr::bvar(*idx)),
        ExprKind::Sort(level) => {
            let level_idx = add_kernel_level(writer, level);
            writer.add_expr(FlatExpr::sort(level_idx))
        }
        ExprKind::Const(name, levels) => {
            let name_idx = writer.add_string(&name.to_string());
            let list_idx = if levels.is_empty() {
                u32::MAX
            } else {
                let indices: Vec<u32> = levels
                    .iter()
                    .map(|level| add_kernel_level(writer, level))
                    .collect();
                writer.add_level_list(&indices)
            };
            writer.add_expr(FlatExpr::const_ref(name_idx, list_idx))
        }
        ExprKind::App(func, arg) => {
            let fi = add_kernel_expr(writer, func);
            let ai = add_kernel_expr(writer, arg);
            writer.add_expr(FlatExpr::app(fi, ai))
        }
        ExprKind::Lam(bd, ty, body) => {
            let ti = add_kernel_expr(writer, ty);
            let bi = add_kernel_expr(writer, body);
            writer.add_expr(FlatExpr::lam(binder_info_u8(bd.info), ti, bi))
        }
        ExprKind::Pi(bd, ty, body) => {
            let ti = add_kernel_expr(writer, ty);
            let bi = add_kernel_expr(writer, body);
            writer.add_expr(FlatExpr::pi(binder_info_u8(bd.info), ti, bi))
        }
        other => panic!("test helper cannot encode {other:?}"),
    }
}

fn binder_info_u8(info: clean_kernel::BinderInfo) -> u8 {
    match info {
        clean_kernel::BinderInfo::Default => 0,
        clean_kernel::BinderInfo::Implicit => 1,
        clean_kernel::BinderInfo::StrictImplicit => 2,
        clean_kernel::BinderInfo::InstImplicit => 3,
    }
}

// ---------------------------------------------------------------------
// RelaxedFoundational trust gate (the USABILITY lever).
//
// Its foundational half admits a non-KV dependency by NAME and kind, and,
// since e20128880, only as the kernel's CANONICAL declaration in the live
// environment. A kernel-checked resident is admitted under every gate by
// the residency rule (after the kind and type-agreement checks), so on a
// foundational dependency the two gates agree on the verdict; they differ
// in the reason they give when the environment holds no canonical one.
// ---------------------------------------------------------------------

// -----------------------------------------------------------------------
// mathverse_apply <name> — cite BY NAME with argument synthesis.
//
// This is the capability `mathverse_use` cannot express: it is nullary
// SEARCH, applies whatever premise selection ranks first, and closes only
// when the candidate's WHOLE type unifies. These pin the by-name contract.
// -----------------------------------------------------------------------

/// An unknown name is a clear, actionable refusal — not a silent miss.
#[test]
fn test_mathverse_apply_unknown_name_reports_it() {
    let shard = build_guard_shard(&[(
        "Known.thm",
        ImportConfidence::KernelVerified,
        DeclKind::Theorem,
        true,
    )]);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    super::super::mathverse_use::set_mathverse_library(lib);

    let mut state = ProofState::new(Environment::new(), Expr::prop());
    let err = super::super::mathverse_use::mathverse_apply_named(
        &mut state,
        "Totally.Absent.lemma",
        TrustGate::Strict,
    )
    .expect_err("an unknown name must not silently succeed");
    match err {
        TacticError::SearchExhausted { tactic, detail } => {
            assert_eq!(tactic, "mathverse_apply");
            assert!(
                detail.contains("Totally.Absent.lemma"),
                "the refusal must name the constant asked for: {detail}"
            );
        }
        other => panic!("expected SearchExhausted, got {other:?}"),
    }
    super::super::mathverse_use::clear_mathverse_library();
}

// -----------------------------------------------------------------------
// TYPE SUBSTITUTION — the guard, and its permissiveness budget.
//
// `validate_dependency_loader_trust`'s residency discriminator used to
// branch on KIND only:
//
//     DeclKind::Inductive   => env.get_inductive(name).is_some(),
//     DeclKind::Constructor => env.get_constructor(name).is_some(),
//     DeclKind::Recursor    => env.get_recursor(name).is_some(),
//     _ => true,                     // Definition/Theorem/Opaque/Axiom
//
// so a resident sharing a name AND a kind with a shard row but differing in
// TYPE was admitted, and the citation reported success about the shard's
// declaration while resting on Clean's. The first two tests below exercise
// exactly that path and now assert a REJECTION; the rest pin the
// permissiveness that keeps the check from mass-rejecting legitimate
// dependencies.
// -----------------------------------------------------------------------

/// Add a shard row for a binder gadget whose VALUE is `fun a₁ … aₙ => a_k`.
/// `k == 1` is the genuine identity; anything else must not be erased.
fn add_gadget_row(writer: &mut ShardWriter, name: &str, arity: usize, returns: usize) {
    let l0 = writer.add_level(FlatLevel::zero());
    let sort0 = writer.add_expr(FlatExpr::sort(l0));
    // de Bruijn: the k-th binder from the outside is index `arity - k`.
    let mut body = writer.add_expr(FlatExpr::bvar(u32::try_from(arity - returns).unwrap()));
    for _ in 0..arity {
        body = writer.add_expr(FlatExpr::lam(0, sort0, body));
    }
    let name_idx = writer.add_string(name);
    writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx: sort0,
        value_idx: body,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Definition as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
}

/// End to end. Before the type-agreement check this citation CLOSED the goal
/// and reported success while a member of the closure it claimed was the
/// shard's was really Clean's own differently-typed declaration — never
/// replaced, because the loader only adds names it finds ABSENT. It must now
/// fail closed, and the resident must be left exactly as it was found.
#[test]
fn test_citation_refuses_to_rest_on_differently_typed_resident() {
    use clean_kernel::flat::FlatExpr;
    use clean_mathverse::shard::ShardWriter;

    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort0 = writer.add_expr(FlatExpr::sort(l0));
    let true_name = writer.add_string("True");
    let true_intro_name = writer.add_string("True.intro");
    let true_ref = writer.add_expr(FlatExpr::const_ref(true_name, u32::MAX));
    let true_intro_ref = writer.add_expr(FlatExpr::const_ref(true_intro_name, u32::MAX));

    // Row 0 — the cited theorem: `Exploit.thm : True := True.intro`.
    let thm_name = writer.add_string("Exploit.thm");
    writer.add_constant(MathverseConstantHeader {
        name_idx: thm_name,
        type_idx: true_ref,
        value_idx: true_intro_ref,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Theorem as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    // Row 1 — a closure member whose shard type is `Prop`.
    let victim_name = writer.add_string("Victim.def");
    writer.add_constant(MathverseConstantHeader {
        name_idx: victim_name,
        type_idx: sort0,
        value_idx: sort0,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Definition as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let shard = ShardReader::from_bytes(&buf).unwrap();

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    lib.add_dependency(0, 1);
    super::super::mathverse_use::set_mathverse_library(lib);

    // The session environment: a real prelude plus Clean's own `Victim.def`,
    // whose type is `Prop → Prop` where the shard row says `Prop`.
    let mut env = Environment::with_prelude();
    let prop = Expr::sort(Level::zero());
    let resident_type = Expr::pi(
        clean_kernel::BinderInfo::Default,
        prop.clone(),
        prop.clone(),
    );
    env.add_decl(clean_kernel::Declaration::Definition {
        name: clean_kernel::Name::from_string("Victim.def"),
        level_params: vec![],
        type_: resident_type.clone(),
        value: Expr::lam(clean_kernel::BinderInfo::Default, prop, Expr::bvar(0)),
        is_reducible: false,
    })
    .expect("resident registers");

    let goal = Expr::const_str("True");
    let mut state = ProofState::new(env, goal);
    let closed = super::super::mathverse_use::mathverse_apply_named(
        &mut state,
        "Exploit.thm",
        TrustGate::Strict,
    );
    let detail = detail_from_apply_result(closed);
    assert!(
        detail.contains("Victim.def") && detail.contains("type substitution"),
        "the citation must fail CLOSED and name the substituted closure member: {detail}"
    );
    assert!(
        !state.is_complete(),
        "the goal must NOT be discharged — that silent success is the bug"
    );

    // The session is left exactly as it was found.
    let resident_after = state
        .env
        .get_const(&clean_kernel::Name::from_string("Victim.def"))
        .expect("Victim.def is still resident")
        .clone();
    assert_eq!(
        resident_after.type_, resident_type,
        "a refused citation must not mutate the resident declaration"
    );
    super::super::mathverse_use::clear_mathverse_library();
}

/// With NO library installed the failure names that cause specifically,
/// rather than looking like "lemma not found".
#[test]
fn test_mathverse_apply_without_library_says_so() {
    super::super::mathverse_use::clear_mathverse_library();
    let mut state = ProofState::new(Environment::new(), Expr::prop());
    let err = super::super::mathverse_use::mathverse_apply_named(
        &mut state,
        "Any.name",
        TrustGate::Strict,
    )
    .expect_err("no library installed must fail");
    match err {
        TacticError::SearchExhausted { detail, .. } => assert!(
            detail.contains("no Mathverse Library loaded"),
            "must distinguish 'no library' from 'no such lemma': {detail}"
        ),
        other => panic!("expected SearchExhausted, got {other:?}"),
    }
}

mod dependency_replay;
mod foundational_rows;
mod policy;
mod resident_agreement;
