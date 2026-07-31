// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Acceptance tests for job C1 — the `ImplInfer` skeleton.
//!
//! The full-spec build is expensive (minutes), so this is ONE test that makes
//! every C1 assertion against a single `Specification`. Splitting it into a test
//! per assertion would multiply the build, not the coverage.
//!
//! What the gate requires (execution plan, machine 4) and where it is checked:
//!
//! | gate | assertion |
//! |---|---|
//! | registered at a new late stage | `EXPECTED_NAMES` all present |
//! | builds | the spec constructs at all (any failure aborts registration) |
//! | census stays 11 | no new declaration is a kernel `ConstantKind::Axiom` |
//! | non-vacuity witness per rule | `WITNESSES`, all `DerivedProved`, empty `axiom_deps` |
//! | `λ(x:Prop).x` derivable | `implinfer_lam_identity_witness` present and axiom-free |
//! | coverage stated as a fraction | the four arm-ledger theorems present |

use clean_kernel::env::ConstantKind;
use clean_kernel::Name;

use crate::spec::types::ProofStatus;
use crate::test_utils::build_spec_with_stack;

/// Every declaration the C1 lane registers, by stage.
const EXPECTED_NAMES: &[&str] = &[
    // M2 — the operational syntax
    "BinderInfo",
    "Multiplicity",
    "BinderData",
    "ImplLit",
    "ImplExpr",
    "LocalDecl",
    "LCtx",
    "local_decl_id",
    "local_decl_type",
    "local_decl_value",
    "local_decl_bi",
    "lctx_lookup",
    "lctx_fresh",
    "impl_lift_bvar_at",
    "impl_lift_at",
    "impl_inst_bvar_geq",
    "impl_inst_bvar_at",
    "impl_instantiate_at",
    "impl_instantiate",
    "impl_open",
    "impl_abstract_bvar",
    "impl_abstract_at",
    "impl_abstract_fvar",
    "impl_subst_fvar",
    "ImplConstInfo",
    "impl_const_lps",
    "impl_const_type",
    "impl_const_unsafe",
    "impl_const_partial",
    "name_list_len",
    "level_list_len",
    "name_list_mem",
    "level_params_ok",
    "impl_levels_ok",
    "level_lookup",
    "level_subst",
    "impl_inst_levels_list",
    "impl_inst_levels",
    // M3 — the boundary, the relation, the refutation
    "ImplWhnfTo",
    "ImplIsLe",
    "impl_name_nat",
    "impl_name_string",
    "impl_lit_type",
    "ImplUnit",
    "ImplInfer",
    "ImplNotBVar",
    "impl_infer_bvar_rejects",
    "impl_infer_next_id_monotone",
    // M5 — the arm ledger and the mode gate
    "CleanModeM",
    "ReleaseArm",
    "mode_has_cubical_layer",
    "mode_is_set_theoretic",
    "mode_has_sprop",
    "arm_gate",
    "arm_is_extension",
    "arm_is_proj",
    "arm_modelled",
    "impl_expr_arm",
    "impl_infer_mode_gate_constructive",
    "impl_infer_mode_gate_cubical_opens",
    "impl_infer_arm_partition",
    "impl_infer_proj_is_the_only_exclusion",
    "impl_expr_arm_never_extension",
    "impl_expr_arm_never_proj",
];

/// One non-vacuity witness per `ImplInfer` rule. `lit` gets two (one per
/// literal kind) because the arm's result table has two entries.
const WITNESSES: &[&str] = &[
    "implinfer_sort_witness",
    "implinfer_fvar_witness",
    "implinfer_const_witness",
    "implinfer_app_witness",
    "implinfer_lam_identity_witness",
    "implinfer_pi_witness",
    "implinfer_let_witness",
    "implinfer_lit_nat_witness",
    "implinfer_lit_str_witness",
    "implinfer_mdata_witness",
];

/// The nine `ImplInfer` constructors — one per successful release dispatch arm.
/// `bvar` is deliberately ABSENT: its rule is the refutation.
const IMPL_INFER_CTORS: &[&str] = &[
    "ImplInfer.sort",
    "ImplInfer.fvar",
    "ImplInfer.const",
    "ImplInfer.app",
    "ImplInfer.lam",
    "ImplInfer.pi",
    "ImplInfer.let_",
    "ImplInfer.lit",
    "ImplInfer.mdata",
];

#[test]
fn test_impl_infer_skeleton_meets_c1_acceptance_gate() {
    let spec = build_spec_with_stack();
    let defs = spec.definitions();

    // ── gate: registered, and the spec still builds ─────────────────────────
    for name in EXPECTED_NAMES {
        assert!(
            defs.contains_key(*name) || spec.env().get_const(&Name::from_string(name)).is_some(),
            "C1 declaration `{name}` is missing from the built specification"
        );
    }

    // ── gate: census stays 11 — nothing here is a kernel axiom ──────────────
    // The ratchet keys on kernel ConstantKind::Axiom (value-absence), NOT on the
    // SpecDefinition is_axiom flag, because the two can diverge: a definition
    // with {is_axiom:false, value_src:None} still lowers to a genuine kernel
    // axiom. So this asserts against the kernel environment directly.
    let live_axioms: Vec<String> = spec
        .env()
        .constants()
        .filter(|c| c.kind == ConstantKind::Axiom)
        .map(|c| c.name.to_string())
        .collect();
    for name in EXPECTED_NAMES.iter().chain(WITNESSES.iter()) {
        assert!(
            !live_axioms.iter().any(|a| a == *name),
            "C1 declaration `{name}` lowered to a KERNEL AXIOM — the lane must be \
             census-neutral (standing rule 1: census stays at 11)"
        );
    }

    // ── gate: a non-vacuity witness per rule, each axiom-free ───────────────
    for name in WITNESSES {
        let def = defs
            .get(*name)
            .unwrap_or_else(|| panic!("non-vacuity witness `{name}` is missing"));
        assert!(
            !def.is_axiom,
            "witness `{name}` must be a proved definition, not an axiom"
        );
        assert!(
            def.value_src.is_some(),
            "witness `{name}` must carry a VALUE — a value-less definition lowers to a \
             kernel axiom and would be a masquerade, not a witness"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "witness `{name}` must be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "witness `{name}` must have an EMPTY axiom closure, found {:?}",
            def.axiom_deps
        );
    }

    // ── gate: the flagship — λ(x : Prop). x is derivable ────────────────────
    // The exact acceptance KernelInferAccepts cannot represent: B's Lam arm
    // recurses on the raw de Bruijn body in the same state, so its lam inversion
    // extracts KernelInferAccepts st (bvar 0) bt, which kernel_infer_bvar_empty
    // makes Empty. Here the binder is opened to FVar(0) and the fvar rule fires.
    let flagship = defs
        .get("implinfer_lam_identity_witness")
        .expect("the identity-lambda witness is C1's headline claim");
    let flagship_ty = flagship.type_src.as_str();
    for fragment in [
        "ImplExpr.lam",
        "ImplExpr.bvar Nat.zero",
        "ImplExpr.pi",
        "Nat.succ Nat.zero",
    ] {
        assert!(
            flagship_ty.contains(fragment),
            "the identity-lambda witness must state `{fragment}`; got: {flagship_ty}"
        );
    }
    let flagship_val = flagship
        .value_src
        .as_deref()
        .expect("the flagship witness must have a value");
    assert!(
        flagship_val.contains("ImplInfer.lam") && flagship_val.contains("ImplInfer.fvar"),
        "the identity-lambda derivation must go through the lam rule and infer its \
         OPENED body with the fvar rule (the whole point); got: {flagship_val}"
    );

    // ── the relation's shape: 9 rules, and NO bvar constructor ──────────────
    for ctor in IMPL_INFER_CTORS {
        assert!(
            spec.env().get_const(&Name::from_string(ctor)).is_some(),
            "ImplInfer constructor `{ctor}` is missing"
        );
    }
    assert!(
        spec.env()
            .get_const(&Name::from_string("ImplInfer.bvar"))
            .is_none(),
        "ImplInfer must NOT have a bvar constructor: the release BVar arm is \
         `Err(TypeError::UnboundVariable)` unconditionally (tc/infer.rs:350), so the \
         bvar case is the REFUTATION impl_infer_bvar_rejects, not a rule"
    );

    // ── the refutation is PROVED, not assumed ──────────────────────────────
    let refutation = defs
        .get("impl_infer_bvar_rejects")
        .expect("the bvar refutation is the 10th modelled arm");
    assert!(
        !refutation.is_axiom && refutation.value_src.is_some(),
        "the bvar refutation must be proved by a real term, not assumed"
    );
    assert!(
        refutation.axiom_deps.is_empty(),
        "the bvar refutation must have an empty axiom closure, found {:?}",
        refutation.axiom_deps
    );
    assert!(
        refutation.type_src.contains("ImplExpr.bvar i")
            && refutation.type_src.trim_end().ends_with("-> Empty"),
        "the refutation must state `... (ImplExpr.bvar i) T m -> Empty`; got: {}",
        refutation.type_src
    );

    // ── coverage as a fraction: the arm ledger is 24 arms wide ─────────────
    // The 24 dispatch arms are the ReleaseArm constructors; assert every one is
    // present so the ledger cannot silently shrink and round the fraction up.
    for arm in crate::spec::core_spec::impl_infer_mode_gate::release_arm_names() {
        let ctor = format!("ReleaseArm.{arm}");
        assert!(
            spec.env().get_const(&Name::from_string(&ctor)).is_some(),
            "release dispatch arm `{ctor}` is missing from the coverage ledger"
        );
    }
    assert_eq!(
        crate::spec::core_spec::impl_infer_mode_gate::release_arm_names().len(),
        24,
        "the release dispatcher has 24 arms (tc/infer.rs:349-683); the ledger must \
         enumerate exactly that many"
    );
}
