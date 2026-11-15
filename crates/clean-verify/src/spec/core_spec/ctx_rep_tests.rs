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
//! | coverage stated as a fraction | all nine bridge arms exist; both literal kinds have positive and wrong-type witnesses |

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
    "impl_bridge_app",
    "impl_bridge_lam",
    "impl_bridge_pi",
    "impl_bridge_let_core",
    "impl_bridge_let",
    // both literal kinds are genuinely bridged and their exact outputs checked
    "impl_bridge_lit",
    "LiteralReturn",
    "literal_infer_result",
    "literal_return_eq",
    "kernelinfers_literal_result",
    "kernelinfers_literal_nat_type",
    "kernelinfers_literal_string_type",
    "kernelinfers_nat_not_string",
    "kernelinfers_string_not_nat",
    // the closed-level fact
    "ctx_rep_nil_lookup_empty",
];

/// Non-vacuity witnesses: every relation and every bridge lemma fired on a
/// concrete instance.
///
/// `impl_bridge_app_witness` is deliberately NOT here: firing the app arm needs
/// proofs of its three `forall`-premises, which are M4's own theorems, so that
/// witness lives in `add_kinfers_bridge_arms` and is gated by
/// `impl_infer_sound_tests`. Every other arm fires in-stage.
const WITNESSES: &[&str] = &[
    "expr_rep_sort_witness",
    "ctx_rep_nil_witness",
    "ctx_rep_one_witness",
    "impl_bridge_fvar_witness",
    "impl_bridge_sort_witness",
    "impl_bridge_mdata_witness",
    "impl_bridge_const_witness",
    "impl_bridge_lam_witness",
    "impl_bridge_pi_witness",
    "impl_bridge_let_witness",
    "impl_bridge_lit_nat_witness",
    "impl_bridge_lit_string_witness",
];

/// Every `ImplInfer` rule now has a bridge arm, including both literal kinds.
const BRIDGED_RULES: &[&str] = &[
    "impl_bridge_sort",
    "impl_bridge_fvar",
    "impl_bridge_const",
    "impl_bridge_mdata",
    "impl_bridge_app",
    "impl_bridge_lam",
    "impl_bridge_pi",
    "impl_bridge_let",
    "impl_bridge_lit",
];

/// These old conclusions were true of the previous literal-free judgment.
/// They cannot remain registered after the supported judgment grows.
const RETIRED_LITERAL_REFUTATIONS: &[&str] = &[
    "kernelinfers_lit_rejects",
    "impl_bridge_lit_refuted",
    "impl_bridge_lit_unprovable",
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

    // Every operational-model rule has a representation bridge.
    for name in BRIDGED_RULES {
        let def = defs
            .get(*name)
            .unwrap_or_else(|| panic!("bridged rule `{name}` is missing"));
        assert!(
            def.value_src.is_some() && def.axiom_deps.is_empty(),
            "bridged rule `{name}` must be a valued, axiom-free proof"
        );
        assert!(
            def.type_src.contains("KernelInfers"),
            "bridged rule `{name}` must land in the KernelInfers codomain — that is the \
             codomain that PINS the returned type, which TypingCtxConv does not; got: {}",
            def.type_src
        );
    }
    assert_eq!(
        BRIDGED_RULES.len(),
        9,
        "all nine ImplInfer rules must have a real bridge"
    );

    // ── the three binder rules are representation-sensitive AT the binder ───
    // Each must translate its body under the EXTENDED renaming `cons Nat x rho`
    // and its layer-2 context extended by the translated domain. A rule that
    // used the un-extended renaming under the binder would be the cofinite-free
    // discipline silently dropped.
    for name in ["impl_bridge_lam", "impl_bridge_pi", "impl_bridge_let_core"] {
        let def = defs.get(name).unwrap_or_else(|| panic!("`{name}` missing"));
        assert!(
            def.type_src.contains("ListType.cons Nat x rho")
                && def.type_src.contains("impl_open b x"),
            "binder rule `{name}` must run its body IH at the EXTENDED renaming on the \
             OPENED body — that is the freshness discipline; got: {}",
            def.type_src
        );
    }
    // The lam and let_ arms abstract the body type back; pi does not, because a
    // Pi's result is a sort. Asserting the asymmetry keeps it from drifting.
    for name in ["impl_bridge_lam", "impl_bridge_let_core"] {
        let def = defs.get(name).unwrap_or_else(|| panic!("`{name}` missing"));
        assert!(
            def.type_src.contains("impl_abstract_fvar bt x"),
            "`{name}` must carry the abstract commutation for its body TYPE"
        );
    }
    assert!(
        !defs
            .get("impl_bridge_pi")
            .expect("impl_bridge_pi missing")
            .type_src
            .contains("impl_abstract_fvar"),
        "impl_bridge_pi must NOT carry an abstract commutation — a Pi's result is a sort, \
         so there is nothing to abstract back"
    );
    // The app arm matches KernelInfers.app premise for premise: both operational
    // premises are copied verbatim from ImplInfer.app, not restated in layer-2
    // form.
    let app_bridge = defs
        .get("impl_bridge_app")
        .expect("impl_bridge_app missing");
    assert!(
        app_bridge
            .type_src
            .contains("ImplWhnfTo F (ImplExpr.pi bd A B)")
            && app_bridge.type_src.contains("ImplIsLe A2 A"),
        "the app bridge must carry ImplInfer.app's operational premises VERBATIM and \
         convert them inside the proof; got: {}",
        app_bridge.type_src
    );

    for name in RETIRED_LITERAL_REFUTATIONS {
        assert!(
            !defs.contains_key(*name),
            "obsolete literal-free impossibility theorem {name} must be retired"
        );
    }
    for name in [
        "literal_decode_encode",
        "literal_kinds_distinct",
        "kernelinfers_literal_nat_type",
        "kernelinfers_literal_string_type",
        "kernelinfers_nat_not_string",
        "kernelinfers_string_not_nat",
    ] {
        let def = defs.get(name).unwrap_or_else(|| panic!("{name} missing"));
        assert!(def.value_src.is_some() && !def.is_axiom);
        assert!(
            crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
            "{name} must have no hidden axioms"
        );
    }
    let literal_bridge = defs.get("impl_bridge_lit").expect("literal bridge");
    assert!(
        !literal_bridge.type_src.contains("Empty"),
        "literal bridge must apply without an impossible premise"
    );
    for (name, expected_rule) in [
        ("impl_bridge_lit_nat_witness", "impl_bridge_lit"),
        ("impl_bridge_lit_string_witness", "impl_bridge_lit"),
    ] {
        let witness = defs.get(name).expect("literal witness");
        assert!(
            witness
                .value_src
                .as_ref()
                .is_some_and(|v| v.contains(expected_rule)),
            "{name} must consume the bridge theorem"
        );
    }
}
