// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Gate for the M4 increment.
//!
//! ONE test, one full-spec build, same discipline as the C1/C2/C4 gates.

use clean_kernel::env::ConstantKind;
use clean_kernel::Name;

use crate::spec::types::ProofStatus;
use crate::test_utils::build_spec_with_stack;

/// Everything this M4 increment registers.
const EXPECTED_NAMES: &[&str] = &[
    // the commutation spine
    "to_kexpr_at_lift",
    "to_kexpr_at_instantiate",
    // the two owed operational-boundary soundness theorems
    "impl_whnf_to_defeq",
    "impl_is_le_defeq",
    // and the sharper companion: layer-1 whnf is layer-2 WHNF, not just DefEq
    // of the endpoints — what a KernelInfers-codomain bridge needs, since
    // TypingCtxConv.conv is unrestricted and does not pin the returned type
    "impl_whnf_to_whnf_to",
    // and the first arm bridged into the STRONGER codomain: KernelInfers.app
    // carries whnf_to and DefEq as witnessed premises, which TypingCtxConv does not
    "impl_kinfers_app",
    // the ImplInfer rules the retarget discharges
    "impl_sound_app",
    "impl_sound_sort",
    "impl_sound_const",
    "impl_sound_mdata",
    "impl_sound_lam",
    "impl_sound_pi",
    "impl_sound_let",
    "to_kexpr_open",
    "to_kexpr_abstract",
    "impl_sound_lam_scoped",
    "impl_sound_pi_scoped",
    "sub_zero_lt_succ",
    "impl_lift_lc",
    "impl_subst_is_abstract_instantiate",
    "impl_sound_let_scoped",
    "ImplSoundGuard",
    "to_kexpr_weaken",
    "ctx_rep_snoc_fresh",
    "tconv_var_of_var_type",
    "TEnvRepC",
    "impl_infer_sound",
    "implscoped_witness",
    "impllc_witness",
    "implfreshlc_witness",
    "implwhnfto_witness",
    "implisle_witness",
    "implunit_witness",
    "impllit_witness",
    "multiplicity_witness",
    "tenvrepc_empty",
    "impl_sound_guard_witness",
    "impl_infer_sound_witness",
];

#[test]
fn test_impl_infer_sound_increment_is_proved_and_census_neutral() {
    let spec = build_spec_with_stack();
    let defs = spec.definitions();
    let env = spec.env();

    // ── registered, valued, PROVED ─────────────────────────────────────────
    for name in EXPECTED_NAMES {
        let def = defs
            .get(*name)
            .unwrap_or_else(|| panic!("M4 declaration `{name}` is missing"));
        assert!(
            !def.is_axiom && def.value_src.is_some(),
            "`{name}` must carry a real proof term — a value-less definition lowers to a \
             kernel axiom, which for a commutation lemma would be assuming the very thing \
             M4 exists to prove"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "`{name}` must be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "`{name}` must have an EMPTY axiom closure, found {:?}",
            def.axiom_deps
        );
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "`{name}` never reached the kernel environment"
        );
    }

    // ── census 11 ──────────────────────────────────────────────────────────
    // Keyed on the kernel environment, not the `is_axiom` flag: the two can
    // diverge, and a value-less definition lowers to a genuine axiom.
    let live_axioms: Vec<String> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Axiom)
        .map(|c| c.name.to_string())
        .collect();
    for name in EXPECTED_NAMES {
        assert!(
            !live_axioms.iter().any(|a| a == *name),
            "M4 declaration `{name}` lowered to a KERNEL AXIOM — standing rule 1 is that the \
             census stays at 11"
        );
    }

    // ── the lemma is GENERALISED, which is the whole point ─────────────────
    // The depth-0 instance is what M4 consumes, but it is not provable by
    // induction on its own: under a binder the cutoff moves to `succ k`. If
    // someone weakened this to the `Nat.zero` instance it would still be true,
    // still be proved, and be useless — so pin the quantifier.
    let lift = defs
        .get("to_kexpr_at_lift")
        .expect("the keystone must exist");
    assert!(
        lift.type_src.contains("(k : Nat)") && lift.type_src.contains("Nat.add k c"),
        "to_kexpr_at_lift must quantify over the CUTOFF k and state the depth as `k + c` — \
         the depth-0 instance alone cannot carry its own induction through a binder; got: {}",
        lift.type_src
    );
    assert!(
        lift.type_src.contains("impl_lift_at") && lift.type_src.contains("lift_at (to_kexpr_at"),
        "to_kexpr_at_lift must relate the LAYER-1 lift to the LAYER-2 lift — a statement \
         mentioning only one side is not a commutation lemma; got: {}",
        lift.type_src
    );

    // ── the substituted value is translated at depth ZERO ──────────────────
    // Not a detail. The hit case of the induction has to line up with
    // `to_kexpr_at_lift`, whose right-hand side is `lift_at (… rho 0) 0 c`. A
    // version stating the value at depth `d` double-counts the depth on every
    // free variable inside it and is FALSE, not merely harder — so if someone
    // "generalises" it that way this assertion is what catches it.
    let inst = defs
        .get("to_kexpr_at_instantiate")
        .expect("the substitution commutation lemma must exist");
    assert!(
        inst.type_src.contains("(to_kexpr_at a rho Nat.zero)"),
        "to_kexpr_at_instantiate must translate the substituted value at depth ZERO; got: {}",
        inst.type_src
    );
    assert!(
        inst.type_src.contains("(Nat.succ d)"),
        "the body must be translated ONE BINDER DEEPER than the substitution depth — that is \
         what makes this the lemma the `app` rule needs (ctx_rep.rs's coverage table spells \
         the required shape out); got: {}",
        inst.type_src
    );
    assert!(
        inst.type_src.contains("impl_instantiate_at")
            && inst.type_src.contains("instantiate_at (to_kexpr_at"),
        "to_kexpr_at_instantiate must relate the LAYER-1 instantiation to the LAYER-2 one; \
         got: {}",
        inst.type_src
    );

    // ── the arms land in TypingCtxConv, which is the WHOLE POINT of M4 ──────
    // C4 bridged into KernelInfers and stopped at four rules because
    // KernelInfers has no conversion rule. If someone retargeted these back to
    // KernelInfers the app arm could not exist at all, so pin the codomain.
    for name in ["impl_sound_app", "impl_sound_sort", "impl_sound_const"] {
        let arm = defs.get(name).unwrap_or_else(|| panic!("`{name}` missing"));
        assert!(
            arm.type_src.contains("TypingCtxConv") && !arm.type_src.contains("KernelInfers"),
            "`{name}` must land in TypingCtxConv, not KernelInfers — the retarget IS M4's \
             decision (unified-implinfer-relation.md §2); got: {}",
            arm.type_src
        );
    }

    // The app arm must consume BOTH operational boundaries. Without them it
    // would be a different, weaker lemma that assumed the whnf step away.
    let app = defs
        .get("impl_sound_app")
        .expect("the app arm is M4's headline");
    assert!(
        app.type_src.contains("ImplWhnfTo F (ImplExpr.pi bd A B)")
            && app.type_src.contains("ImplIsLe A2 A"),
        "impl_sound_app must take the deployed arm's OWN premises — whnf the function type to \
         a Pi, then is_le the argument (tc/infer.rs:438,474). A version without them would be \
         assuming the very steps the rule performs; got: {}",
        app.type_src
    );
    assert!(
        app.type_src.contains("impl_instantiate B a"),
        "impl_sound_app must conclude at the LAYER-1 instantiation — concluding at layer 2's \
         `instantiate` would leave the result equation undischarged; got: {}",
        app.type_src
    );
}
