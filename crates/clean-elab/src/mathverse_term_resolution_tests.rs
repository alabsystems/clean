// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse library content used as a TERM, not through a tactic.
//!
//! The capability under test: after `import Mathverse.<Corpus>.<Name>`, the
//! named library constant is an ordinary resident declaration, so the
//! elaborator's UNMODIFIED name resolution finds it and it can appear in a term
//! — `:= probe_id_thm q hq` — instead of only as the argument of
//! `mathverse_apply`.
//!
//! Each test states the BEFORE (the same source, unarmed) and the AFTER (the
//! same source, after the import), so a regression that quietly stops loading
//! shows up as a passing BEFORE half and a failing AFTER half rather than as a
//! vague failure.
//!
//! What is deliberately pinned here:
//!
//! * residency is not a rubber stamp — an ill-typed use of an imported constant
//!   is still refused by the KERNEL (`test_..._negative_control`);
//! * a trust refusal is reported AS a trust refusal, never as
//!   `Unknown identifier` (`test_..._trust_refusal_is_not_unknown_ident`);
//! * both corpora are served from one library in one session
//!   (`test_..._isabelle_...`), which is the cross-system claim;
//! * ordinary imports are untouched (`test_..._does_not_intercept_...`).

#![cfg(feature = "mathverse-library")]

use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level, Name};
use clean_mathverse::library::MathverseLibrary;
use clean_mathverse::shard::{ShardReader, ShardWriter};
use clean_mathverse::trust::policy::TrustPolicy;
use clean_mathverse::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
};

use crate::tactic::mathverse_use::{clear_mathverse_library, set_mathverse_library};
use crate::{ElabError, ElabResult};

// ---------------------------------------------------------------------------
// Fixture: one library, three rows, two corpora
// ---------------------------------------------------------------------------

/// `∀ (p : Prop), p → p`
fn id_thm_type() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    )
}

/// `fun (p : Prop) (h : p) => h`
fn id_thm_value() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    )
}

fn add_level(writer: &mut ShardWriter, level: &Level) -> u32 {
    match level {
        Level::Zero => writer.add_level(FlatLevel::zero()),
        Level::Succ(inner) => {
            let inner_idx = add_level(writer, inner);
            writer.add_level(FlatLevel::succ(inner_idx))
        }
        other => panic!("fixture cannot encode level {other:?}"),
    }
}

fn binder_info_u8(info: BinderInfo) -> u8 {
    match info {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

fn add_expr(writer: &mut ShardWriter, expr: &Expr) -> u32 {
    match expr.kind() {
        ExprKind::BVar(idx) => writer.add_expr(FlatExpr::bvar(*idx)),
        ExprKind::Sort(level) => {
            let level_idx = add_level(writer, level);
            writer.add_expr(FlatExpr::sort(level_idx))
        }
        ExprKind::Const(name, levels) => {
            let name_idx = writer.add_string(&name.to_string());
            let list_idx = if levels.is_empty() {
                u32::MAX
            } else {
                let indices: Vec<u32> = levels.iter().map(|l| add_level(writer, l)).collect();
                writer.add_level_list(&indices)
            };
            writer.add_expr(FlatExpr::const_ref(name_idx, list_idx))
        }
        ExprKind::App(func, arg) => {
            let fi = add_expr(writer, func);
            let ai = add_expr(writer, arg);
            writer.add_expr(FlatExpr::app(fi, ai))
        }
        ExprKind::Lam(bd, ty, body) => {
            let ti = add_expr(writer, ty);
            let bi = add_expr(writer, body);
            writer.add_expr(FlatExpr::lam(binder_info_u8(bd.info), ti, bi))
        }
        ExprKind::Pi(bd, ty, body) => {
            let ti = add_expr(writer, ty);
            let bi = add_expr(writer, body);
            writer.add_expr(FlatExpr::pi(binder_info_u8(bd.info), ti, bi))
        }
        other => panic!("fixture cannot encode {other:?}"),
    }
}

/// Install a four-row library on this thread:
///
/// | name                     | corpus   | confidence     |
/// |--------------------------|----------|----------------|
/// | `probe_id_thm`           | Lean4    | KernelVerified |
/// | `probe_isa_id_thm`       | Isabelle | KernelVerified |
/// | `probe_untrusted_thm`    | Lean4    | Axiomatized    |
/// | `probe_source_only_thm`  | Lean4    | SourceVerified |
///
/// All four carry the same (genuinely kernel-checkable) statement `∀ (p :
/// Prop), p → p`, so the only thing that differs between the accepted and the
/// refused rows is TRUST — which is what the refusal tests need in order to
/// mean anything.
///
/// The library's own `TrustPolicy` is `permissive` on purpose: the policy must
/// not be what hides the untrusted row, or the test would be checking
/// visibility filtering instead of the `TrustGate`.
fn install_probe_library() {
    install_library_with_rows(&[
        (
            "probe_id_thm",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
        ),
        (
            "probe_isa_id_thm",
            SourceSystem::Isabelle,
            ImportConfidence::KernelVerified,
        ),
        (
            "probe_untrusted_thm",
            SourceSystem::Lean4,
            ImportConfidence::Axiomatized,
        ),
        (
            "probe_source_only_thm",
            SourceSystem::Lean4,
            ImportConfidence::SourceVerified,
        ),
    ]);
}

/// Install a one-shard library on this thread whose every row carries the same
/// kernel-checkable statement `∀ (p : Prop), p → p` and differs only in NAME,
/// SOURCE SYSTEM and IMPORT CONFIDENCE.
///
/// Shared with the lazy-resolution tests (`mathverse_lazy_tests`), which need
/// the same shape under different names. Keeping one builder means both suites
/// exercise the same encoder; a fixture that drifted would make one of them
/// prove nothing.
pub(crate) fn install_library_with_rows(rows: &[(&str, SourceSystem, ImportConfidence)]) {
    let mut writer = ShardWriter::new();
    let ty = id_thm_type();
    let val = id_thm_value();

    for (name, system, confidence) in rows {
        let type_idx = add_expr(&mut writer, &ty);
        let value_idx = add_expr(&mut writer, &val);
        let name_idx = writer.add_string(name);
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: *system as u8,
            import_confidence: *confidence as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Theorem as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
    }

    let mut buf = Vec::new();
    writer.write(&mut buf).expect("fixture shard writes");
    let shard = ShardReader::from_bytes(&buf).expect("fixture shard reads");
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).expect("fixture shard loads");
    set_mathverse_library(lib);
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn elab(env: &mut Environment, src: &str) -> Result<ElabResult, ElabError> {
    let decl = clean_parser::parse_decl_exact(src)
        .expect("fixture source parses as one complete declaration");
    crate::elaborate_decl_and_register(env, &decl)
}

/// The declaration under test: a library constant used as a TERM.
const USE_AS_TERM: &str = "theorem uses_lib (q : Prop) (hq : q) : q := probe_id_thm q hq";

// ---------------------------------------------------------------------------
// The deliverable
// ---------------------------------------------------------------------------

/// BEFORE the import the name does not resolve; AFTER it, the same source
/// elaborates and kernel-registers.
///
/// This is the whole point of the feature: `probe_id_thm` is used as an ordinary
/// term applied to two arguments, with no `mathverse_apply` anywhere, and it
/// reaches the kernel through `Environment::add_decl`.
#[test]
fn test_mathverse_import_makes_library_constant_usable_as_a_term() {
    install_probe_library();

    // BEFORE — unarmed. Verbatim, so a change in the message is visible.
    let mut env = Environment::with_prelude();
    let before = elab(&mut env, USE_AS_TERM).expect_err("unarmed elaboration must fail");
    let before_msg = before.to_string();
    assert!(
        before_msg.starts_with("Unknown identifier: probe_id_thm"),
        "unarmed use must fail as an unresolved name, got: {before_msg}"
    );

    // ARM — this is the line a user writes.
    let mut env = Environment::with_prelude();
    assert!(
        env.get_const(&Name::from_string("probe_id_thm")).is_none(),
        "precondition: the constant is not resident before the import"
    );
    let imported = elab(&mut env, "import Mathverse.Mathlib.probe_id_thm")
        .expect("the Strict gate must admit a KernelVerified library constant");
    assert!(matches!(imported, ElabResult::Skipped));
    assert!(
        env.get_const(&Name::from_string("probe_id_thm")).is_some(),
        "the import must leave the constant RESIDENT — that residency, not any \
         name-resolution hook, is what makes the term below elaborate"
    );

    // AFTER — same source, now a registered theorem.
    let after = elab(&mut env, USE_AS_TERM).expect("armed elaboration must succeed");
    match after {
        ElabResult::Theorem { ref name, .. } => {
            assert_eq!(name.to_string(), "uses_lib");
        }
        other => panic!("expected a registered theorem, got {other:?}"),
    }
    assert!(
        env.get_const(&Name::from_string("uses_lib")).is_some(),
        "the proof that cites library content must itself be registered"
    );

    clear_mathverse_library();
}

/// Residency is not a rubber stamp: an ILL-TYPED use of the imported constant
/// is still refused, by the kernel, after the import succeeded.
///
/// Without this, "it elaborated" would be evidence of nothing.
#[test]
fn test_mathverse_import_term_use_negative_control() {
    install_probe_library();
    let mut env = Environment::with_prelude();
    elab(&mut env, "import Mathverse.Mathlib.probe_id_thm").expect("import succeeds");

    // `probe_id_thm q hq : q`, but the goal is `r`.
    let err = elab(
        &mut env,
        "theorem bogus_use (q r : Prop) (hq : q) : r := probe_id_thm q hq",
    )
    .expect_err("an ill-typed use of an imported constant must still be rejected");
    let msg = err.to_string();
    assert!(
        msg.contains("mismatch") || msg.contains("Type"),
        "the refusal must be a TYPE failure, not a name failure: {msg}"
    );
    assert!(
        !msg.contains("Unknown identifier"),
        "the constant IS resident; the failure must not be a resolution miss: {msg}"
    );

    clear_mathverse_library();
}

/// A trust refusal must surface AS a trust refusal.
///
/// `probe_untrusted_thm` is present in the library and spelled correctly; the
/// only thing wrong with it is its confidence. Reporting that as
/// `Unknown identifier` would turn a soundness decision into a spelling
/// complaint and would hide the reason the citation was refused.
#[test]
fn test_mathverse_import_trust_refusal_is_not_unknown_ident() {
    install_probe_library();
    let mut env = Environment::with_prelude();

    let err = elab(&mut env, "import Mathverse.Mathlib.probe_untrusted_thm")
        .expect_err("Strict must refuse an Axiomatized constant");
    let msg = err.to_string();
    assert!(
        matches!(err, ElabError::MathverseImportFailed { .. }),
        "expected a Mathverse import failure, got {err:?}"
    );
    assert!(
        msg.contains("probe_untrusted_thm"),
        "the refusal must name the constant asked for: {msg}"
    );
    assert!(
        !msg.contains("Unknown identifier"),
        "a trust refusal must not be reported as an unknown identifier: {msg}"
    );
    // And nothing was installed.
    assert!(
        env.get_const(&Name::from_string("probe_untrusted_thm"))
            .is_none(),
        "a refused import must leave the environment untouched"
    );

    clear_mathverse_library();
}

/// Both corpora, one library, one session — the cross-system claim.
///
/// The Isabelle-sourced row is imported and then used as a term in exactly the
/// same way as the Lean4-sourced one, from the same `MathverseLibrary`.
#[test]
fn test_mathverse_import_isabelle_constant_usable_as_a_term() {
    install_probe_library();
    let mut env = Environment::with_prelude();

    elab(&mut env, "import Mathverse.Isabelle.probe_isa_id_thm")
        .expect("Strict must admit the KernelVerified Isabelle row");
    let out = elab(
        &mut env,
        "theorem uses_isabelle (q : Prop) (hq : q) : q := probe_isa_id_thm q hq",
    )
    .expect("an Isabelle-sourced constant must be usable as a term");
    assert!(matches!(out, ElabResult::Theorem { .. }));

    clear_mathverse_library();
}

/// Both systems imported into one session, then a proof that cites each.
///
/// One module per `import`, as Lean's grammar has it: the comma-separated list
/// this test once used left the parser in `5018d30761`, and the lenient
/// `parse_decl` then dropped the `, …` tail without a word, so the Isabelle name
/// was never imported. The exact parser refuses that spelling outright.
#[test]
fn test_mathverse_import_serves_mathlib_and_isabelle_in_one_session() {
    install_probe_library();
    let mut env = Environment::with_prelude();

    // A single-declaration fixture must consume all its input. The old comma
    // form silently imported only the first target through parse_decl's
    // intentionally prefix-only API; neither tail is a second import here.
    for source in [
        "import Mathverse.Mathlib.probe_id_thm, Mathverse.Isabelle.probe_isa_id_thm",
        "import Mathverse.Mathlib.probe_id_thm import Mathverse.Isabelle.probe_isa_id_thm",
    ] {
        match clean_parser::parse_decl_exact(source) {
            Err(clean_parser::ParseError::UnexpectedToken { message, .. }) => assert!(
                message.starts_with("trailing input after declaration"),
                "the single-declaration guard must name the unused tail: {message}"
            ),
            other => panic!("an import tail must not be silently accepted: {other:?}"),
        }
    }

    elab(&mut env, "import Mathverse.Mathlib.probe_id_thm")
        .expect("the first valid import must pass the Strict gate");
    assert!(env.get_const(&Name::from_string("probe_id_thm")).is_some());
    assert!(
        env.get_const(&Name::from_string("probe_isa_id_thm"))
            .is_none(),
        "the first import must not load an unrequested constant from another corpus"
    );
    elab(&mut env, "import Mathverse.Isabelle.probe_isa_id_thm")
        .expect("the second valid import must pass the same Strict gate");
    assert!(
        env.get_const(&Name::from_string("probe_id_thm")).is_some()
            && env
                .get_const(&Name::from_string("probe_isa_id_thm"))
                .is_some(),
        "both imports must leave their genuine declarations in the same environment"
    );

    elab(
        &mut env,
        "theorem uses_both (q : Prop) (hq : q) : q := probe_isa_id_thm q (probe_id_thm q hq)",
    )
    .expect("a single proof term may mix Mathlib and Isabelle content");

    clear_mathverse_library();
}

/// The corpus tag is checked, not decorative: asking Isabelle for a Lean4 row
/// is an error rather than a silent success.
#[test]
fn test_mathverse_import_corpus_tag_is_checked() {
    install_probe_library();
    let mut env = Environment::with_prelude();

    let err = elab(&mut env, "import Mathverse.Isabelle.probe_id_thm")
        .expect_err("`probe_id_thm` is Lean4-sourced; the Isabelle tag must not pass");
    let msg = err.to_string();
    assert!(
        msg.contains("Isabelle") && msg.contains("Lean4"),
        "the mismatch must name both the requested and the actual corpus: {msg}"
    );

    clear_mathverse_library();
}

/// A name that is genuinely absent is still reported as absent — the import
/// path does not invent a trust story for a typo.
#[test]
fn test_mathverse_import_absent_name_is_reported() {
    install_probe_library();
    let mut env = Environment::with_prelude();

    let err = elab(&mut env, "import Mathverse.Mathlib.totally_absent_lemma")
        .expect_err("an absent name must not silently succeed");
    let msg = err.to_string();
    assert!(
        msg.contains("totally_absent_lemma") && msg.contains("not in the installed"),
        "expected a clear absence report, got: {msg}"
    );

    clear_mathverse_library();
}

/// `import Mathverse` on its own installs the library and loads nothing. It is
/// still useful — it fails loudly here if the shards are unavailable, rather
/// than at the first citation.
#[test]
fn test_bare_mathverse_import_arms_without_loading() {
    install_probe_library();
    let mut env = Environment::with_prelude();

    elab(&mut env, "import Mathverse").expect("a bare arming import succeeds");
    assert!(
        env.get_const(&Name::from_string("probe_id_thm")).is_none(),
        "arming must not load constants nobody asked for"
    );

    clear_mathverse_library();
}

/// The default gate is `Strict`, and widening it is the USER's explicit act.
///
/// `probe_source_only_thm` is `SourceVerified` — refused by `Strict`, admitted
/// by `Relaxed`. The same import line therefore fails and then succeeds, with
/// the only difference being a `set_option` the user wrote. This pins both
/// halves: that the default really is the strong gate, and that the option is
/// actually read (a typo'd option name silently leaves `Strict` in force, which
/// is the safe direction).
#[test]
fn test_mathverse_import_trust_gate_defaults_to_strict_and_is_opt_in_widened() {
    install_probe_library();

    let mut env = Environment::with_prelude();
    let err = elab(&mut env, "import Mathverse.Mathlib.probe_source_only_thm")
        .expect_err("Strict must refuse a merely SourceVerified constant");
    assert!(matches!(err, ElabError::MathverseImportFailed { .. }));

    // `relaxed` is REFUSED FROM SOURCE — a contract correction, not a weakening.
    //
    // This test previously asserted that one `set_option` line admits a merely
    // SourceVerified constant. That is exactly the hole: `TrustGate::Relaxed`
    // skips the shadowed-by-unchecked rule, the KIND discriminator, and
    // `validate_resident_type_agreement`, and before the import surface existed
    // it had NO user-reachable surface anywhere. Demonstrated with the option
    // available: a deliberately type-substituted resident installed cleanly.
    // `relaxed-foundational` stays reachable — it keeps all three checks and
    // only widens which AXIOMS may appear in the closure.
    let mut env = Environment::with_prelude();
    elab(&mut env, "set_option mathverse.trust \"relaxed\"").expect("option is accepted");
    let err = elab(&mut env, "import Mathverse.Mathlib.probe_source_only_thm")
        .expect_err("`relaxed` must not be reachable from source");
    assert!(
        err.to_string().contains("not available from source"),
        "expected the relaxed-is-unavailable diagnostic, got: {err}"
    );

    // The STRONGER widening is still available and still admits nothing that
    // Strict's resident checks would refuse.
    let mut env = Environment::with_prelude();
    elab(
        &mut env,
        "set_option mathverse.trust \"relaxed-foundational\"",
    )
    .expect("option is accepted");
    elab(&mut env, "import Mathverse.Mathlib.probe_id_thm")
        .expect("relaxed-foundational must still admit a KernelVerified constant");

    // A bad value is a loud error, not a silent fallback to some other gate.
    let mut env = Environment::with_prelude();
    elab(&mut env, "set_option mathverse.trust \"bogus\"").expect("option is accepted");
    let err = elab(&mut env, "import Mathverse.Mathlib.probe_id_thm")
        .expect_err("an unknown trust gate must be rejected");
    assert!(
        err.to_string().contains("unknown trust gate"),
        "expected a trust-gate diagnostic, got: {err}"
    );

    clear_mathverse_library();
}

/// THE HAPPY PATH IS UNTOUCHED.
///
/// An ordinary import is dispatched exactly as before — the Mathverse arm is
/// gated on one string compare against the first path segment, and a file that
/// never says `Mathverse` never reaches it. Note this test does NOT install a
/// library: if the arm fired it would fail with `MathverseImportFailed`
/// ("no Mathverse Library is installed…"), which is precisely the signal we
/// want if the interception ever widens.
///
/// Ordinary imports are fail-closed (`ImportPolicy::FailClosed`): a module no
/// `.olean`, project source or declared Clean prelude supplies is refused with
/// `UnresolvedImport`. So the ordinary path's verdict is either success or
/// that loader's own refusal — never a Mathverse error.
#[test]
fn test_ordinary_import_does_not_intercept_or_require_a_library() {
    clear_mathverse_library();
    let mut env = Environment::with_prelude();

    // Whether `Init.Core` resolves depends on the host's `.olean` search
    // paths; either way the ORDINARY loader decides it.
    match elab(&mut env, "import Init.Core") {
        Ok(out) => assert!(matches!(out, ElabResult::Skipped)),
        Err(err) => {
            assert!(
                !matches!(err, ElabError::MathverseImportFailed { .. })
                    && !err.to_string().contains("Mathverse"),
                "an ordinary import must never reach the Mathverse arm: {err}"
            );
        }
    }

    // And a module whose name merely STARTS with the reserved word is ordinary:
    // it reaches the `.olean` loader, which refuses it by name.
    let err = elab(&mut env, "import MathverseFoo.Bar")
        .expect_err("a nonexistent ordinary module is refused fail-closed");
    match err {
        ElabError::UnresolvedImport { ref module, .. } => {
            assert_eq!(module, "MathverseFoo.Bar", "got: {err}");
        }
        other => panic!("prefix collision must take the ordinary import path, got {other:?}"),
    }
}
