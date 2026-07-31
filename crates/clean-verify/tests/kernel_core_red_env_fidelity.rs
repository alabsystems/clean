// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Front #1 Stage 2 FIDELITY GATE for `kernel_core_red_env`.
//!
//! The reflection generator (`red_env_reflect` bin) emits the foundation-core
//! reflection of the live `Specification::new()` kernel environment as
//! committed generated artifacts. These tests re-walk the SAME live kernel
//! environment and compare the regenerated reflection 1:1 against the
//! committed artifacts — rule-for-rule and field-for-field on the erased
//! image — so ANY drift between the kernel's actual `RecursorVal`s /
//! definition values and the registered `kernel_core_red_env` literal fails
//! loudly. Plus the interning injectivity test (trust edge 1) and the
//! one-rfl-at-scale probe (the Stage-4 feasibility preview).

use std::time::Instant;

use clean_kernel::{Expr, ExprKind, Name, RecursorArgOrder, TypeChecker};
use clean_verify::red_env_reflect::{
    fidelity_check, parse_interning_tsv, reflect_expr, reflect_foundation_core,
    COMMITTED_DEF_SCRIPT, COMMITTED_INTERNING_TSV, COMMITTED_SKIP_LEDGER, REFLECT_DEFS,
    REFLECT_INDUCTIVES,
};
use clean_verify::test_utils::run_with_stack;

/// THE FIDELITY GATE: regenerating the reflection from the live kernel env
/// must reproduce the committed def script, interning table, and skip
/// ledger byte-for-byte (the renderer is deterministic, so byte equality IS
/// rule-for-rule/field-for-field equality of the erased image).
#[test]
fn test_fidelity_gate_regenerated_reflection_matches_committed_artifacts() {
    run_with_stack(|| {
        // Exercise the generator's artifact-independent full-build path with a
        // harmless extra marker. Seeing the marker live proves this build
        // consumed the supplied in-memory script rather than the committed
        // `include_str!` payload; the reflection itself must remain identical.
        let injected_script =
            format!("def kcre_full_validation_probe : Nat := Nat.zero\n{COMMITTED_DEF_SCRIPT}");
        let spec =
            clean_verify::Specification::new_with_red_env_reflection_script(&injected_script)
                .expect("full spec should build from the fresh in-memory script");
        let injected = spec
            .env()
            .get_const(&Name::from_string("kcre_full_validation_probe"))
            .expect("full spec must consume the injected script");
        assert!(
            injected.value.is_some(),
            "injected validation marker must be a value-bearing definition"
        );
        let reflection = fidelity_check(
            spec.env(),
            COMMITTED_DEF_SCRIPT,
            COMMITTED_INTERNING_TSV,
            COMMITTED_SKIP_LEDGER,
        )
        .expect("regenerated reflection must match the committed generated artifacts (no drift)");
        assert!(
            !reflection.recs.is_empty() && !reflection.defs.is_empty(),
            "reflection must be non-empty (foundation core present)"
        );

        // Regeneration must not depend on loading the artifact it replaces.
        // The dedicated seed contains exactly the allowlisted source
        // declarations and must render byte-identically to the final full
        // environment.
        let seed = clean_verify::Specification::new_red_env_reflection_seed()
            .expect("artifact-independent reflection seed should build");
        let seeded = reflect_foundation_core(seed.env());
        assert_eq!(
            seeded
                .def_script()
                .expect("seed reflection should render safely"),
            reflection
                .def_script()
                .expect("full reflection should render safely"),
            "artifact-independent seed and full live environment must generate the same script"
        );
        assert_eq!(
            seeded.interning_tsv(),
            reflection.interning_tsv(),
            "seed and full environment must generate the same interning table"
        );
        assert_eq!(
            seeded
                .skip_ledger_md()
                .expect("seed ledger should render safely"),
            reflection
                .skip_ledger_md()
                .expect("full ledger should render safely"),
            "seed and full environment must generate the same coverage ledger"
        );
    });
}

/// Field-for-field walk DIRECTLY against the kernel's `RecursorVal`s (not via
/// the renderer): every reflected recursor mirrors its kernel counterpart's
/// metadata counts and per-rule (constructor name, num_fields, erased rhs).
#[test]
fn test_fidelity_gate_field_for_field_against_kernel_recursors() {
    run_with_stack(|| {
        let spec = clean_verify::Specification::new().expect("spec should build");
        let env = spec.env();
        let reflection = reflect_foundation_core(env);
        for rec in &reflection.recs {
            let rv = env
                .get_recursor(&Name::from_string(&rec.name))
                .unwrap_or_else(|| panic!("{} should be a kernel recursor", rec.name));
            assert_eq!(rec.num_params, rv.num_params, "{}: num_params", rec.name);
            assert_eq!(rec.num_motives, rv.num_motives, "{}: num_motives", rec.name);
            assert_eq!(rec.num_minors, rv.num_minors, "{}: num_minors", rec.name);
            assert_eq!(rec.num_indices, rv.num_indices, "{}: num_indices", rec.name);
            assert_eq!(
                rv.arg_order,
                RecursorArgOrder::MajorAfterMinors,
                "{}: only the MajorAfterMinors layout is reflected",
                rec.name
            );
            assert_eq!(
                rec.rules.len(),
                rv.rules.len(),
                "{}: rule count (one per constructor)",
                rec.name
            );
            for (refl_rule, kernel_rule) in rec.rules.iter().zip(rv.rules.iter()) {
                assert_eq!(
                    refl_rule.ctor,
                    kernel_rule.constructor_name.to_string(),
                    "{}: rule constructor name",
                    rec.name
                );
                assert_eq!(
                    refl_rule.num_fields, kernel_rule.num_fields,
                    "{}/{}: num_fields",
                    rec.name, refl_rule.ctor
                );
                let re_erased = reflect_expr(&kernel_rule.rhs).unwrap_or_else(|e| {
                    panic!(
                        "{}/{}: rhs must be representable: {e}",
                        rec.name, refl_rule.ctor
                    )
                });
                assert_eq!(
                    refl_rule.rhs, re_erased,
                    "{}/{}: erased rhs image",
                    rec.name, refl_rule.ctor
                );
            }
        }
        for def in &reflection.defs {
            let ci = env
                .get_const(&Name::from_string(&def.name))
                .unwrap_or_else(|| panic!("{} should be a kernel constant", def.name));
            let value = ci
                .value
                .as_ref()
                .unwrap_or_else(|| panic!("{} should have a kernel value", def.name));
            let re_erased = reflect_expr(value)
                .unwrap_or_else(|e| panic!("{}: value must be representable: {e}", def.name));
            assert_eq!(def.value, re_erased, "{}: erased value image", def.name);
        }
        // Every allowlisted item is either reflected or in the skip ledger
        // with a reason (coverage-with-skips: nothing silently dropped).
        for ind in REFLECT_INDUCTIVES {
            let rec_name = format!("{ind}.rec");
            let reflected = reflection.recs.iter().any(|r| r.name == rec_name);
            let skipped = reflection
                .skips
                .iter()
                .any(|s| s.item.starts_with(&rec_name) && !s.item.contains("K-extension"));
            assert!(
                reflected || skipped,
                "{rec_name}: must be reflected or skip-ledgered"
            );
        }
        for def in REFLECT_DEFS {
            let reflected = reflection.defs.iter().any(|d| &d.name == def);
            let skipped = reflection.skips.iter().any(|s| &s.item == def);
            assert!(
                reflected || skipped,
                "{def}: must be reflected or skip-ledgered"
            );
        }
    });
}

/// Trust edge 1: the interning table is INJECTIVE (distinct real names get
/// distinct tags, one tag per name) — this is what makes `name_eqb` over the
/// reflected env agree with real kernel name equality.
#[test]
fn test_interning_table_injective() {
    run_with_stack(|| {
        let spec = clean_verify::Specification::new().expect("spec should build");
        let reflection = reflect_foundation_core(spec.env());
        assert!(
            reflection.interning_injective(),
            "interning table must be injective"
        );
        // Reuse the same whole-table parser as semantic source consumers.
        let committed = parse_interning_tsv(COMMITTED_INTERNING_TSV)
            .expect("committed interning table must satisfy the full format");
        assert_eq!(
            committed.len(),
            reflection.interning.len(),
            "committed table row count matches regenerated interning"
        );
    });
}

/// `kernel_core_red_env` is registered as a VALUE-FUL definition (lowers to
/// `Declaration::Definition` — census-neutral, ratchet-clean), parallel to
/// `the_red_env` (which is NOT swapped in Stage 2).
#[test]
fn test_kernel_core_red_env_registered_census_neutral() {
    run_with_stack(|| {
        let spec = clean_verify::Specification::new().expect("spec should build");
        let def = spec
            .definitions()
            .get("kernel_core_red_env")
            .expect("kernel_core_red_env should be registered");
        assert!(!def.is_axiom, "kernel_core_red_env must not be an axiom");
        assert!(
            def.value_src.is_some(),
            "kernel_core_red_env must be value-ful"
        );
        let ci = spec
            .env()
            .get_const(&Name::from_string("kernel_core_red_env"))
            .expect("kernel_core_red_env should be a kernel constant");
        assert!(
            ci.value.is_some(),
            "kernel_core_red_env must lower to a value-ful kernel Definition (census-neutral)"
        );
        // The generated helper pool (kcre_nat_* / kcre_name_*) lowers to
        // value-ful kernel Definitions too (census-neutral).
        for helper in ["kcre_nat_0", "kcre_name_0"] {
            let hci = spec
                .env()
                .get_const(&Name::from_string(helper))
                .unwrap_or_else(|| panic!("{helper} should be a kernel constant"));
            assert!(hci.value.is_some(), "{helper} must be value-ful");
        }
        // the_red_env is registered and — post Front #1 Stage 3 — is the
        // value-level ALIAS of kernel_core_red_env.
        let tre = spec
            .definitions()
            .get("the_red_env")
            .expect("the_red_env must still be registered");
        assert!(
            tre.value_src
                .as_deref()
                .is_some_and(|v| v.contains("kernel_core_red_env")),
            "the_red_env must be the Stage-3 alias of kernel_core_red_env, got: {:?}",
            tre.value_src
        );
    });
}

/// THE ONE-RFL-AT-SCALE PROBE (Stage-4 feasibility preview): the kernel must
/// whnf-EVALUATE each Stage-1 closure checker fold over the full reflected
/// env down to a Bool CONSTRUCTOR (fold does not stick), and the cost is
/// measured. NOTE the honest expectation: the Stage-1 checkers test
/// `bvar_ceiling rhs = 0`, an ADD-based over-approximation that only
/// certifies bvar-FREE rhs/values; real kernel rule rhss are closed lambdas
/// WITH bvars, so the checker may evaluate to `Bool.false` even though the
/// closure interfaces hold. This test gates EVALUATION (the scaling
/// question); the computed verdicts + timings are printed for the report.
#[test]
fn test_one_rfl_probe_checker_folds_evaluate_over_reflected_env() {
    run_with_stack(|| {
        let spec = clean_verify::Specification::new().expect("spec should build");
        let tc = TypeChecker::new(spec.env());
        for (checker, proj) in [
            ("rec_env_closed_b", "red_rec"),
            ("rec_env_lift_closed_b", "red_rec"),
            ("def_env_closed_b", "red_def"),
            ("def_env_lift_closed_b", "red_def"),
        ] {
            let e = Expr::app(
                Expr::const_str(checker),
                Expr::app(
                    Expr::const_str(proj),
                    Expr::const_str("kernel_core_red_env"),
                ),
            );
            let t = Instant::now();
            let w = tc.whnf(&e);
            let dt = t.elapsed();
            let verdict = match w.kind() {
                ExprKind::Const(n, _) => n.to_string(),
                other => panic!(
                    "{checker} fold STUCK over kernel_core_red_env: whnf head {other:?} \
                     (expected a Bool constructor)"
                ),
            };
            assert!(
                verdict == "Bool.true" || verdict == "Bool.false",
                "{checker}: whnf must reach a Bool constructor, got {verdict}"
            );
            println!(
                "one-rfl probe: {checker} ({proj} kernel_core_red_env) = {verdict} in {:.3}s",
                dt.as_secs_f64()
            );
        }

        // Aggregate per-element cost (the TRUE-case fold cost the Bool.and
        // short-circuit hides): force the full per-element checker test
        // `nat_eqb (bvar_ceiling <term>) 0` for every reflected rule rhs and
        // def value. Every element must EVALUATE to a Bool constructor; the
        // total is the measured one-rfl budget for a Stage-4 depth-aware
        // checker at real-env scale.
        let reflection = reflect_foundation_core(spec.env());
        let mut elements = Vec::new();
        for rec in &reflection.recs {
            for rule in &rec.rules {
                elements.push((format!("{}/{}", rec.name, rule.ctor), &rule.rhs));
            }
        }
        for def in &reflection.defs {
            elements.push((def.name.clone(), &def.value));
        }
        assert!(
            !elements.is_empty(),
            "reflected env must contribute probe elements"
        );
        let mut total = std::time::Duration::ZERO;
        for (label, term) in &elements {
            let reflected_term = reflection
                .kexpr_term(term)
                .unwrap_or_else(|error| panic!("{label}: reflected term must render: {error}"));
            let e = Expr::apps(
                Expr::const_str("nat_eqb"),
                [
                    Expr::app(Expr::const_str("bvar_ceiling"), reflected_term),
                    Expr::const_str("kcre_nat_0"),
                ],
            );
            let t = Instant::now();
            let w = tc.whnf(&e);
            total += t.elapsed();
            match w.kind() {
                ExprKind::Const(n, _)
                    if n.to_string() == "Bool.true" || n.to_string() == "Bool.false" => {}
                other => panic!("element probe {label} STUCK: whnf head {other:?}"),
            }
        }
        println!(
            "one-rfl element probes: {} elements fully forced in {:.3}s total",
            elements.len(),
            total.as_secs_f64()
        );
    });
}
