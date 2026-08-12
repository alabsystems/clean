// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Acceptance tests for job C4 — the `CtxRep` bridge.
//!
//! One test, one full-spec build (the build is minutes; splitting multiplies the
//! build, not the coverage).
//!
//! | gate | assertion |
//! |---|---|
//! | registered after the ImplInfer stages | `EXPECTED_NAMES` all present |
//! | census stays 11 | no declaration is a kernel `ConstantKind::Axiom` |
//! | every relation is inhabited | `WITNESSES` present, `DerivedProved`, empty `axiom_deps` |
//! | the bridge is not identity-on-syntax | `CtxRep` and `ExprRep` are real inductives with the expected constructors |
//! | coverage stated as a fraction | exactly the four bridged rules exist, and the five blocked ones do NOT |

use clean_kernel::env::ConstantKind;
use clean_kernel::Name;

use crate::spec::types::ProofStatus;
use crate::test_utils::build_spec_with_stack;

/// Every declaration the C4 lane registers.
const EXPECTED_NAMES: &[&str] = &[
    // the translation (ExprRep, realized as a function)
    "rho_index",
    "impl_lit_to_kexpr",
    "to_kexpr_at",
    "to_kexpr",
    "ExprRep",
    "expr_rep_to_eq",
    "expr_rep_of_eq",
    // the layer-2 variable-type view and the context relation
    "opt_var_type",
    "ctx_var_type",
    "opt_lift1",
    "CtxRep",
    // the lookup theorem and the layer-2 variable-rule introduction
    "opt_var_type_succ",
    "ctx_rep_lookup",
    "kernelinfers_var_of_var_type",
    // the bridge, rule by rule
    "impl_bridge_fvar",
    "impl_bridge_sort",
    "impl_bridge_mdata",
    "impl_bridge_const",
    // the closed-level fact
    "ctx_rep_nil_lookup_empty",
];

/// Non-vacuity witnesses: every relation and every bridge lemma fired on a
/// concrete instance.
const WITNESSES: &[&str] = &[
    "expr_rep_sort_witness",
    "ctx_rep_nil_witness",
    "ctx_rep_one_witness",
    "impl_bridge_fvar_witness",
    "impl_bridge_sort_witness",
    "impl_bridge_mdata_witness",
    "impl_bridge_const_witness",
];

/// The four `ImplInfer` rules this lane bridges — stated as a fraction of nine,
/// never rounded up.
const BRIDGED_RULES: &[&str] = &[
    "impl_bridge_sort",
    "impl_bridge_fvar",
    "impl_bridge_const",
    "impl_bridge_mdata",
];

/// The five rules that are NOT bridged. Asserting their ABSENCE is what keeps
/// the coverage fraction honest: a future edit that adds one of these names
/// without a proof, or that quietly renames a blocked rule into a bridged one,
/// fails here.
const BLOCKED_RULES: &[&str] = &[
    "impl_bridge_lam",
    "impl_bridge_pi",
    "impl_bridge_let",
    "impl_bridge_app",
    "impl_bridge_lit",
];

#[test]
fn test_ctx_rep_bridge_meets_c4_acceptance_gate() {
    let spec = build_spec_with_stack();
    let defs = spec.definitions();

    // ── gate: registered, and the spec still builds ─────────────────────────
    for name in EXPECTED_NAMES {
        assert!(
            defs.contains_key(*name) || spec.env().get_const(&Name::from_string(name)).is_some(),
            "C4 declaration `{name}` is missing from the built specification"
        );
    }

    // ── gate: census stays 11 — nothing here is a kernel axiom ──────────────
    let live_axioms: Vec<String> = spec
        .env()
        .constants()
        .filter(|c| c.kind == ConstantKind::Axiom)
        .map(|c| c.name.to_string())
        .collect();
    for name in EXPECTED_NAMES.iter().chain(WITNESSES.iter()) {
        assert!(
            !live_axioms.iter().any(|a| a == *name),
            "C4 declaration `{name}` lowered to a KERNEL AXIOM — the lane must be \
             census-neutral (standing rule: census stays at 11)"
        );
    }

    // ── gate: every relation and bridge lemma is inhabited, axiom-free ──────
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

    // ── the relations are real inductives with the expected shape ───────────
    for ctor in ["CtxRep.nil", "CtxRep.snoc", "ExprRep.mk"] {
        assert!(
            spec.env().get_const(&Name::from_string(ctor)).is_some(),
            "constructor `{ctor}` is missing"
        );
    }

    // ── the bridge is representation-sensitive, not identity-on-syntax ──────
    // CtxRep's snoc rule must extend BOTH the renaming and the local context
    // with the same fresh id — that is the whole reason a contextual variable
    // reaches the fvar rule instead of the raw-bvar arm impl_infer_bvar_rejects
    // refutes.
    let ctx_rep_lookup = defs
        .get("ctx_rep_lookup")
        .expect("ctx_rep_lookup is C4's substance");
    for fragment in ["lctx_lookup", "ctx_var_type", "rho_index", "to_kexpr"] {
        assert!(
            ctx_rep_lookup.type_src.contains(fragment),
            "ctx_rep_lookup must relate `{fragment}` across the two layers; got: {}",
            ctx_rep_lookup.type_src
        );
    }
    let fvar_bridge = defs
        .get("impl_bridge_fvar")
        .expect("the fvar bridge is the rule the two-layer split exists for");
    assert!(
        fvar_bridge.type_src.contains("CtxRep")
            && fvar_bridge.type_src.contains("ImplExpr.fvar")
            && fvar_bridge.type_src.contains("KernelInfers"),
        "the fvar bridge must consume CtxRep and an ImplExpr.fvar and produce a \
         KernelInfers derivation; got: {}",
        fvar_bridge.type_src
    );

    // ── coverage as a fraction: four of nine, and the other five are ABSENT ─
    for name in BRIDGED_RULES {
        let def = defs
            .get(*name)
            .unwrap_or_else(|| panic!("bridged rule `{name}` is missing"));
        assert!(
            def.value_src.is_some() && def.axiom_deps.is_empty(),
            "bridged rule `{name}` must be a valued, axiom-free proof"
        );
    }
    assert_eq!(
        BRIDGED_RULES.len(),
        4,
        "C4 bridges FOUR of ImplInfer's nine rules; the fraction is 4/9 and must not be \
         rounded up"
    );
    for name in BLOCKED_RULES {
        assert!(
            !defs.contains_key(*name),
            "`{name}` exists, but the module header records that rule as BLOCKED. Either the \
             blocker was cleared (update the header, the coverage fraction and this list) or a \
             name was minted without a proof"
        );
    }
}
