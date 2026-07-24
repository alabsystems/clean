// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended block-wise CROWN + LayerNorm theorems (T20-T22, T60-T61).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("init_nn_verify_blockwise_crown_ext");
    env
}

#[test]
fn test_zonotope_output_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.LayerNorm.zonotope_output"))
            .is_some(),
        "NNVerify.LayerNorm.zonotope_output should be registered",
    );
}

#[test]
fn test_t20_zonotope_reset_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.LayerNorm.zonotope_reset"))
            .is_some(),
        "T20: NNVerify.LayerNorm.zonotope_reset should be registered",
    );
}

#[test]
fn test_t21_width_preserved_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.LayerNorm.zonotope_width_preserved"
        ))
        .is_some(),
        "T21: NNVerify.LayerNorm.zonotope_width_preserved should be registered",
    );
}

#[test]
fn test_t22_generators_reset_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.LayerNorm.zonotope_generators_reset"
        ))
        .is_some(),
        "T22: NNVerify.LayerNorm.zonotope_generators_reset should be registered",
    );
}

#[test]
fn test_generators_after_ln_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.LayerNorm.generators_after_ln"))
            .is_some(),
        "NNVerify.LayerNorm.generators_after_ln should be registered",
    );
}

#[test]
fn test_t60_blockwise_crown_sound_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.Block.blockwise_crown_sound"))
            .is_some(),
        "T60: NNVerify.Block.blockwise_crown_sound (honest restatement of the retired \
         false blockwise_crown_equiv axiom) should be registered",
    );
}

#[test]
fn test_t61_blockwise_complexity_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.Block.blockwise_complexity"))
            .is_some(),
        "T61: NNVerify.Block.blockwise_complexity should be registered",
    );
}

#[test]
fn test_crown_cost_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.Block.crown_cost"))
            .is_some(),
        "NNVerify.Block.crown_cost should be registered",
    );
}

#[test]
fn test_total_dim_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.Block.total_dim"))
            .is_some(),
        "NNVerify.Block.total_dim should be registered",
    );
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("first init");
    env.init_nn_verify_blockwise_crown_ext()
        .expect("second init should be idempotent");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.LayerNorm.zonotope_output",
        "NNVerify.LayerNorm.zonotope_reset",
        "NNVerify.LayerNorm.zonotope_width_preserved",
        "NNVerify.LayerNorm.zonotope_generators_reset",
        "NNVerify.LayerNorm.generators_after_ln",
        "NNVerify.Block.blockwise_crown_sound",
        "NNVerify.Block.blockwise_complexity",
        "NNVerify.Block.crown_cost",
        "NNVerify.Block.total_dim",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
        assert!(
            name.starts_with("NNVerify."),
            "all names must start with NNVerify. prefix: {}",
            name,
        );
    }
}

#[test]
fn test_t20_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.LayerNorm.zonotope_reset"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&thm).expect("infer zonotope_reset type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "T20 should have Pi type (universally quantified)",
    );
}

#[test]
fn test_t21_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.LayerNorm.zonotope_width_preserved"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer zonotope_width_preserved type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "T21 should have Pi type (universally quantified)",
    );
}

#[test]
fn test_t22_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.LayerNorm.zonotope_generators_reset"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer zonotope_generators_reset type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "T22 should have Pi type (universally quantified)",
    );
}

#[test]
fn test_t60_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.Block.blockwise_crown_sound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer blockwise_crown_sound type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "T60 should have Pi type (universally quantified)",
    );
}

#[test]
fn test_t61_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.Block.blockwise_complexity"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer blockwise_complexity type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "T61 should have Pi type (universally quantified)",
    );
}

#[test]
fn test_base_blockwise_still_accessible() {
    let env = make_env();
    // Verify that extending block-wise CROWN doesn't break base C006 theorems
    assert!(
        env.get_const(&Name::from_string("NNVerify.Block.compose"))
            .is_some(),
        "Base Block.compose should still be accessible",
    );
    assert!(
        env.get_const(&Name::from_string("NNVerify.Block.monolithic_crown"))
            .is_some(),
        "Base Block.monolithic_crown should still be accessible",
    );
}

// =============================================================================
// Constructive proof validation (#3309)
// =============================================================================

// 2026-04-19 masquerade demotion (#3494, #3495, #3509): T60, T22, T20,
// and T21 were demoted from Declaration::Theorem to Declaration::Axiom.
// UPDATE 2026-06-17: T60 (blockwise_crown_equiv) was a FALSE unconditional
// equality; it is RETIRED to the honest kernel-checked Theorem
// NNVerify.Block.blockwise_crown_sound (conditional on the per-block hypothesis),
// reusing the C006 Nat.rec proof. Domain axioms 6 -> 5.
// Their former proofs closed only because the carriers
// (`Block.compose`/`Block.monolithic_crown` reduce to `zero_ib`;
// `generators_after_ln` is `fun n _ => n`; `zonotope_output n k γ β ε z`
// reduces to `to_ibp n k z` which itself returns the zero interval)
// collapsed both sides of the equation/inequality to the same term. See
// reports/audit/2026-04-19-clean-native-shard-audit.md entries 5-10.
//
// #3590 Branch B (FAITHFUL MATRIX RESTATEMENT): T22 is no longer in that
// demoted-axiom set. `generators_after_ln` is now the reducible diagonal
// radius matrix `(n k) z -> NNMat n n` (consuming all k input columns via
// `Fin.sum k Rat.abs`), and `zonotope_generators_reset` /
// `zonotope_generators_offdiagonal` are kernel-checked Theorems that pin the
// matrix as `diag(radius_i)`. The axiom is retired (admitted 8 -> 7).
//
// #3509 Branch B (FAITHFUL LAYERNORM-TRANSFER RESTATEMENT): T20 is also no
// longer in the demoted-axiom set. `zonotope_output` is now the interval hull
// of the FAITHFUL `layernorm_zono` (the LN output affine transfer
// `x ↦ γ ⊙ x + β`, genuinely consuming γ and β), and `zonotope_reset` /
// `zonotope_reset_upper` are kernel-checked Theorems pinning the LN-output box
// per component: `(out).lower/upper i = (γ i·c_i + β_i) ∓ Σⱼ|γ i·G_ij|`. The
// OLD `zonotope_output = to_ibp z` equality is now FALSE (gain γ scales the
// radius, bias β shifts the center), so it is RESTATED, not proved. The axiom
// is retired (admitted 7 -> 6). T21 (zonotope_width_preserved) stays an honest
// Axiom — it is a Tranche B governance wall (FALSE-as-written under |γ_i|>1)
// per designs/2026-06-13-nnverify-5axiom-retirement-roadmap.md.

#[test]
fn test_t60_is_faithful_theorem_after_retirement() {
    // 2026-06-17 RETIREMENT: the false unconditional axiom
    // NNVerify.Block.blockwise_crown_equiv (compose = monolithic_crown for ALL cb —
    // FALSE: at k=succ compose applies `cb` while monolithic collapses to zero_ib) is
    // retired. T60 is now the honest, kernel-checked Theorem
    // NNVerify.Block.blockwise_crown_sound: the SAME equality gated on the per-block
    // hypothesis `forall i X, cb i X = mono_step .. i X`, proved by the reused C006
    // Nat.rec induction (empty domain-axiom closure, Constructive). A regression to a
    // body-less axiom would re-open the census slot this retirement closed (domain 6 -> 5).
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.Block.blockwise_crown_sound"))
        .expect("T60 blockwise_crown_sound should exist");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "T60 must be a faithful Declaration::Theorem after the blockwise_crown_equiv \
         retirement; got {:?}",
        ci.kind,
    );
    assert!(
        ci.value.is_some(),
        "T60 blockwise_crown_sound Theorem must carry its reused Nat.rec proof value"
    );
}

#[test]
fn test_t20_zonotope_reset_carries_proof_value_after_3509_branch_b() {
    // #3509 Branch B (FAITHFUL LAYERNORM-TRANSFER RESTATEMENT): the body-less
    // Axiom (Branch A) is RETIRED. T20 `NNVerify.LayerNorm.zonotope_reset` is
    // now a faithful Declaration::Theorem — the lower-bound per-component
    // equation
    //   `(zonotope_output n k γ β ε z).lower i
    //      = (γ i * z.center i + β i) − Σⱼ |γ i * z.generators i j|`
    // over the k/γ/β-consuming `zonotope_output := to_ibp ∘ layernorm_zono`
    // carrier — so it carries its kernel-checked `Eq.refl` proof value. A
    // regression to a body-less Axiom would re-open the admitted-axiom census
    // slot the retirement closed. See nn_verify_blockwise_crown_ext_t20.rs.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.LayerNorm.zonotope_reset"))
        .expect("T20 should exist");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "#3509 Branch B: T20 zonotope_reset must be a faithful \
         Declaration::Theorem (axiom retired by a γ/β-consuming carrier); got {:?}",
        ci.kind,
    );
    assert!(
        ci.value.is_some(),
        "#3509 Branch B: T20 zonotope_reset Theorem must carry its Eq.refl \
         proof value — the lower-bound per-component equation is genuinely \
         proved over the faithful LN-transfer carrier, not asserted"
    );

    // The upper-bound companion pins the box exactly; it must also be a Theorem.
    let ci_up = env
        .get_const(&Name::from_string(
            "NNVerify.LayerNorm.zonotope_reset_upper",
        ))
        .expect("T20 upper companion should exist");
    assert_eq!(
        ci_up.kind,
        ConstantKind::Theorem,
        "#3509 Branch B: zonotope_reset_upper must be a faithful Theorem; got {:?}",
        ci_up.kind,
    );
    assert!(
        ci_up.value.is_some(),
        "upper companion must carry its proof value"
    );
}

#[test]
fn test_t20_layernorm_zono_carrier_consumes_gamma_beta() {
    // #3509 Branch B structural demasquerade: the faithful `layernorm_zono`
    // carrier (the LN output affine transfer `x ↦ γ ⊙ x + β`) MUST genuinely
    // consume the gain γ and bias β. The retired masquerade body discarded
    // γ, β, ε (it was `to_ibp n k z`, collapsing the box to the input box).
    // The faithful body cites Rat.mul (the γ-scaling) and Rat.add (the β-shift)
    // over the projected center/generators, so it can no longer launder a
    // γ/β-discarding claim through `Eq.refl`.
    use crate::expr::{Expr, ExprKind};
    fn expr_mentions(e: &Expr, target: &str) -> bool {
        let t = Name::from_string(target);
        fn go(e: &Expr, t: &Name) -> bool {
            match e.kind() {
                ExprKind::Const(n, _) => n == t,
                ExprKind::App(f, a) => go(f, t) || go(a, t),
                ExprKind::Lam(_, ty, b) | ExprKind::Pi(_, ty, b) => go(ty, t) || go(b, t),
                ExprKind::Let(_, ty, v, b, _) => go(ty, t) || go(v, t) || go(b, t),
                ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => go(x, t),
                _ => false,
            }
        }
        go(e, &t)
    }

    let env = make_env();
    let ln = env
        .get_const(&Name::from_string("NNVerify.LayerNorm.layernorm_zono"))
        .expect("layernorm_zono carrier should be registered");
    assert_eq!(
        ln.kind,
        ConstantKind::Definition,
        "layernorm_zono must be a (reducible) Definition carrier"
    );
    let body = ln
        .value
        .as_ref()
        .expect("layernorm_zono should carry a Definition body");
    assert!(
        expr_mentions(body, "Rat.mul"),
        "layernorm_zono body MUST cite Rat.mul (the per-row gain scaling \
         γ i * ·), proving it is no longer the γ-discarding carrier."
    );
    assert!(
        expr_mentions(body, "Rat.add"),
        "layernorm_zono body MUST cite Rat.add (the bias shift + β i), proving \
         it genuinely consumes β."
    );
    assert!(
        expr_mentions(body, "NNVerify.Zonotope.mk"),
        "layernorm_zono body MUST build a Zonotope.mk (the transferred zonotope)."
    );

    // zonotope_output must now be the interval hull of the LN-transferred
    // zonotope (cites layernorm_zono), NOT the old `to_ibp n k z` alias.
    let out = env
        .get_const(&Name::from_string("NNVerify.LayerNorm.zonotope_output"))
        .expect("zonotope_output should be registered");
    let out_body = out
        .value
        .as_ref()
        .expect("zonotope_output should carry a Definition body");
    assert!(
        expr_mentions(out_body, "NNVerify.LayerNorm.layernorm_zono"),
        "zonotope_output body MUST cite layernorm_zono (it is \
         to_ibp ∘ layernorm_zono), proving γ/β flow through it — the retired \
         masquerade body was the γ/β/ε-discarding `to_ibp n k z`."
    );
}

#[test]
fn test_t20_proof_quality_after_3509_branch_b() {
    // #3509 Branch B: T20 is now a faithful Declaration::Theorem whose
    // transitive axiom closure is empty of domain-specific axioms (the Eq.refl
    // proof reuses only the axiom-free reducible carriers Rat.mul / Rat.add /
    // Rat.sub / Rat.abs / Fin.sum / Zonotope.mk / to_ibp), so `proof_quality`
    // honestly classifies it as `Constructive`. This is NOT the #3509
    // masquerade artefact: the classification now reflects a genuine
    // γ/β/k-consuming per-component equation, not a vacuous `Eq.refl` over an
    // argument-discarding `to_ibp n k z` alias (the RHS `Fin.sum k …` over
    // `γ i * G_ij` would FAIL to type-check against the retired carrier).
    use crate::env::axiom_audit::ProofQuality;
    let env = make_env();
    for name in [
        "NNVerify.LayerNorm.zonotope_reset",
        "NNVerify.LayerNorm.zonotope_reset_upper",
    ] {
        let quality = env
            .proof_quality(&Name::from_string(name))
            .unwrap_or_else(|| panic!("proof_quality should work for {name}"));
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "#3509 Branch B: {name} must classify as Constructive (faithful \
             Eq.refl proof, closure ⊆ FOUNDATIONAL_AXIOMS over γ/β/k-consuming \
             carriers). Got: {:?}",
            quality,
        );
    }
}

#[test]
fn test_t21_zonotope_width_preserved_is_constructive_theorem() {
    // #3509 Branch B (T21 half): T21 `zonotope_width_preserved` is RETIRED from
    // the body-less Declaration::Axiom (#3509 Branch A) to a kernel-checked
    // Declaration::Theorem of the GAIN-BOUND form
    //   (∀ i, |γ i| ≤ 1) → l1(width(zonotope_output …)) ≤ l1(width(to_ibp …)).
    // The prior axiom was FALSE-as-written (unconditional preservation fails
    // under |γ_i| > 1); under the gain bound it is TRUE and proven here over
    // the faithful `to_ibp ∘ layernorm_zono` carriers, driving the domain TCB
    // 5 → 4. See nn_verify_blockwise_crown_ext_t21.rs.
    use crate::env::axiom_audit::ProofQuality;
    let env = make_env();
    let name = Name::from_string("NNVerify.LayerNorm.zonotope_width_preserved");
    let ci = env.get_const(&name).expect("T21 should exist");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "#3509 Branch B: T21 must be a kernel-checked Declaration::Theorem after \
         the GAIN-BOUND retirement; got {:?}",
        ci.kind,
    );
    assert!(
        ci.value.is_some(),
        "#3509 Branch B: T21 Theorem must carry its Fin.sum_le proof value — the \
         gain-bound width inequality is genuinely proven, not asserted",
    );
    // Foundational-closure guard: the transitive axiom closure must be empty of
    // ALL domain-specific axioms (so `proof_quality` is Constructive) — and in
    // particular must NOT expose any distributivity axiom. (`Rat.left_distrib`
    // is a sound kernel-checked quotient Theorem in the live carrier, so it
    // never appears in `axiom_deps`; this asserts the empty-closure invariant.)
    let deps = env
        .axiom_deps(&name)
        .expect("registered, axiom_deps should return Some");
    let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        domain_deps.is_empty(),
        "#3509 Branch B: T21 must have an empty domain-axiom closure; got {:?}",
        domain_deps
    );
    assert!(
        !domain_deps.iter().any(|d| d == "Rat.left_distrib"),
        "T21 closure must not expose Rat.left_distrib as a domain axiom",
    );
    let quality = env
        .proof_quality(&name)
        .expect("proof_quality should be reported for T21");
    assert!(
        matches!(quality, ProofQuality::Constructive),
        "#3509 Branch B: T21 must classify as Constructive (closure ⊆ \
         FOUNDATIONAL_AXIOMS over the faithful gain-scaled carriers). Got: {:?}",
        quality,
    );
}

#[test]
fn test_ext_classification_after_demotion() {
    // After the #3509(B) + #3590(B) + #3648 + 2026-06-17(T60) demasquerade waves:
    //   Axioms: T21 (zonotope_width_preserved, #3509 — a TRANCHE B governance
    //           wall: FALSE-as-written under faithful LN gain, parked on the
    //           user). [T60 retired 2026-06-17 -> blockwise_crown_sound Theorem.]
    //   Theorems: the #3509 Branch B FAITHFUL T20 pair (zonotope_reset
    //             lower-bound per-component equation + zonotope_reset_upper)
    //             over to_ibp ∘ layernorm_zono, T61 (blockwise_complexity,
    //             #3648 Branch B — faithful constructive Nat.rec induction
    //             `Σ bd² ≤ (Σ bd)²`), plus the #3590 Branch B FAITHFUL T22 pair
    //             (zonotope_generators_reset diagonal-entry equation +
    //             zonotope_generators_offdiagonal).
    //   Definitions: the #3509 Branch B FAITHFUL carriers layernorm_zono
    //                (γ⊙·+β LN affine transfer) and zonotope_output
    //                (to_ibp ∘ layernorm_zono), the #3648 Branch B FAITHFUL
    //                crown_cost and total_dim, and the #3590 Branch B FAITHFUL
    //                generators_after_ln (reducible diagonal radius matrix
    //                `(n k) z -> NNMat n n`, consuming all k columns via
    //                `Fin.sum k Rat.abs`).
    let env = make_env();

    let definition_names = [
        // #3509 Branch B: the faithful LN-transfer carriers.
        "NNVerify.LayerNorm.layernorm_zono",
        "NNVerify.LayerNorm.zonotope_output",
        "NNVerify.Block.crown_cost",
        "NNVerify.Block.total_dim",
        // #3590 Branch B: the faithful diagonal radius matrix carrier.
        "NNVerify.LayerNorm.generators_after_ln",
    ];
    for name in &definition_names {
        let ci = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{} should exist", name));
        assert_eq!(
            ci.kind,
            ConstantKind::Definition,
            "{} should be a Definition",
            name,
        );
    }

    // Constructive Theorems remaining in this module: the #3509 Branch B
    // faithful T20 pair (the body-less axiom is retired), T61 (#3648 B), the
    // #3590 Branch B faithful T22 pair, T60 (blockwise_crown_sound), and — as of
    // the #3509 Branch B T21 retirement — T21 itself (zonotope_width_preserved,
    // the GAIN-BOUND theorem; domain 5 -> 4).
    let theorem_names = [
        "NNVerify.LayerNorm.zonotope_reset",
        "NNVerify.LayerNorm.zonotope_reset_upper",
        "NNVerify.Block.blockwise_complexity",
        "NNVerify.LayerNorm.zonotope_generators_reset",
        "NNVerify.LayerNorm.zonotope_generators_offdiagonal",
        // 2026-06-17: the false blockwise_crown_equiv axiom retired to this honest
        // kernel-checked conditional-equality Theorem (domain 6 -> 5).
        "NNVerify.Block.blockwise_crown_sound",
        // #3509 Branch B (T21 half): the false unconditional width-preservation
        // axiom retired to this kernel-checked GAIN-BOUND Theorem
        // (∀ i, |γ i| ≤ 1 ⟹ width(out) ≤ width(in); domain 5 -> 4).
        "NNVerify.LayerNorm.zonotope_width_preserved",
    ];
    for name in &theorem_names {
        let ci = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{} should exist", name));
        assert_eq!(
            ci.kind,
            ConstantKind::Theorem,
            "{} should be a faithful constructive Declaration::Theorem",
            name,
        );
    }

    // No demoted axioms remain in this module: T20, T21, T22, and T60 have all
    // had their false/masquerading axioms retired to faithful kernel-checked
    // Theorems (T21 -> the GAIN-BOUND theorem, #3509 Branch B; T60 ->
    // blockwise_crown_sound, 2026-06-17).
    let demoted_axiom_names: [&str; 0] = [];
    for name in &demoted_axiom_names {
        let ci = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{} should exist", name));
        assert_eq!(
            ci.kind,
            ConstantKind::Axiom,
            "{} should be a Declaration::Axiom after masquerade demotion",
            name,
        );
    }
}

#[test]
fn test_t22_carries_proof_value_after_3590_branch_b() {
    // #3590 Branch B: the body-less Axiom (Branch A) is RETIRED. T22
    // zonotope_generators_reset is now a faithful Declaration::Theorem — the
    // diagonal-entry equation `generators_after_ln n k z i i = Σ_j |G_ij|`
    // over the k-consuming diagonal radius-box carrier — so it carries its
    // kernel-checked Decidable.rec proof value. A regression to a body-less
    // Axiom would re-open the admitted-axiom census slot the retirement closed.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.LayerNorm.zonotope_generators_reset",
        ))
        .expect("T22 should exist");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "#3590 Branch B: T22 zonotope_generators_reset must be a faithful \
         Declaration::Theorem (axiom retired by a k-consuming carrier); got {:?}",
        ci.kind,
    );
    assert!(
        ci.value.is_some(),
        "#3590 Branch B: T22 zonotope_generators_reset Theorem must carry its \
         Decidable.rec proof value — the diagonal-entry equation is genuinely \
         proved, not asserted"
    );
}

// =============================================================================
// Proof quality validation using axiom_audit API (#3375)
// =============================================================================

#[test]
fn test_t22_proof_quality_after_3590_branch_b() {
    // #3590 Branch B: T22 is now a faithful Declaration::Theorem whose
    // transitive axiom closure is empty of domain-specific axioms (the
    // Decidable.rec split reuses only axiom-free Fin.sum / Rat.abs /
    // instDecidableEqFin), so `proof_quality` honestly classifies it as
    // `Constructive`. This is NOT the #3495 masquerade artefact: the
    // classification now reflects a genuine k-consuming diagonal-radius
    // equation, not a vacuous `Eq.refl Nat n` over an argument-discarding
    // carrier (which would FAIL to type-check the `Fin.sum k ...` RHS here).
    use crate::env::axiom_audit::ProofQuality;
    let env = make_env();
    let name = Name::from_string("NNVerify.LayerNorm.zonotope_generators_reset");
    let quality = env
        .proof_quality(&name)
        .expect("proof_quality should work for T22");
    assert!(
        matches!(quality, ProofQuality::Constructive),
        "#3590 Branch B: T22 must classify as Constructive (faithful \
         Decidable.rec proof, closure ⊆ FOUNDATIONAL_AXIOMS over k-consuming \
         carriers). Got: {:?}",
        quality,
    );
}

#[test]
fn test_t61_is_faithful_theorem_with_proof_value() {
    // #3648 Branch B (2026-06-11): T61 blockwise_complexity is now a faithful
    // constructive Declaration::Theorem. The prior Branch A Axiom (and the
    // even-earlier vacuous `Nat.le_refl Nat.zero` masquerade Theorem) are
    // retired: `crown_cost` / `total_dim` are now FAITHFUL reducible
    // Definitions (Nat.rec folds that consume k, bd, and the IH), so T61
    // states the genuine `Σ bd² ≤ (Σ bd)²` and is discharged by a real
    // Nat.rec induction. The proof would FAIL to type-check against the old
    // arg-discarding placeholders, so this is not a masquerade. See
    // nn_verify_blockwise_crown_ext_t61_proof.rs and the #3648 Site 4 triage.
    let env = make_env();
    let name = Name::from_string("NNVerify.Block.blockwise_complexity");
    let ci = env
        .get_const(&name)
        .expect("T61 blockwise_complexity should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "#3648 Branch B: T61 must be a constructive Declaration::Theorem; got {:?}",
        ci.kind,
    );
    assert!(
        ci.value.is_some(),
        "#3648 Branch B: T61 Theorem must carry its Nat.rec induction proof value",
    );
    let tm = env
        .trust_marker_deps(&name)
        .expect("trust_marker_deps should resolve for T61");
    assert!(
        tm.is_empty(),
        "#3648 Branch B: T61 proof must be sorry-free; got {tm:?}",
    );
}

#[test]
fn test_t61_proof_quality_after_3648_branch_b() {
    // #3648 Branch B: T61 is now a faithful constructive Theorem whose
    // transitive axiom closure ⊆ the constructive Nat-order / distributivity
    // lemma set (no domain-specific axiom, no sorry), so `proof_quality`
    // classifies it as `Constructive`. This is NOT the old MASQUERADE: the
    // classification now reflects a genuine Nat.rec induction over faithful
    // carriers, not a vacuous `Nat.le_refl 0` over arg-discarding placeholders.
    use crate::env::axiom_audit::ProofQuality;
    let env = make_env();
    let name = Name::from_string("NNVerify.Block.blockwise_complexity");
    let quality = env
        .proof_quality(&name)
        .expect("proof_quality should work for T61");
    assert!(
        matches!(quality, ProofQuality::Constructive),
        "#3648 Branch B: T61 must classify as Constructive (faithful Nat.rec \
         induction, closure ⊆ constructive Nat lemmas). Got: {:?}",
        quality,
    );
}

// =============================================================================
// MASQUERADE history (#3495 remediation → #3590 Branch A demotion)
//
// The `reports/audit/2026-04-19-clean-native-shard-audit.md` audit flagged
// T22 as trivial-by-construction: the original carrier was `fun n _ => n`
// (a first projection) and the proof closed with a single `Eq.refl`. The
// #3495 "remediation" rewrote the carrier body as
// `@Nat.rec.{1} (fun _ => Nat) n (fun _m _ih => n) k` and wrapped the
// theorem proof in a `Nat.rec` induction whose step branch still returned
// bare `Eq.refl Nat n` (the induction hypothesis `_ih` was ignored).
// R9's wave-7 audit re-flagged this as a compound M2+M3+M4 MASQUERADE
// (see the t22.rs module docstring). #3590 Branch A demotes T22 to
// Declaration::Axiom and flips generators_after_ln to Declaration::Opaque
// to close the δ-reduction loophole.
//
// The structural guard tests below live in
// `tests_nn_verify_blockwise_crown_ext_t22_demasquerade_3590.rs`.
// =============================================================================

#[test]
fn test_t22_kernel_round_trip_on_fresh_env_after_3590_branch_b() {
    // #3590 Branch B: the faithful Theorem (and its off-diagonal companion +
    // the diagonal radius-matrix carrier) must register cleanly on a fresh
    // Environment, with the kernel TYPE-CHECKING the Decidable.rec proof
    // term during `add_decl`. This exercises the full proof path.
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext().expect(
        "fresh init should succeed — the faithful T22 Theorem pair + the \
         reducible generators_after_ln matrix carrier must pass kernel \
         add_decl (the proofs are type-checked here)",
    );

    // Confirm the declaration exists after the fresh init.
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.LayerNorm.zonotope_generators_reset",
        ))
        .expect("T22 should be registered after init on a fresh env");

    // Confirm it is a faithful Theorem after #3590 Branch B (axiom retired).
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "#3590 Branch B: T22 must be a faithful Declaration::Theorem after \
         kernel-checked registration on a fresh env (axiom retired); got {:?}",
        ci.kind,
    );
    assert!(
        ci.value.is_some(),
        "#3590 Branch B: the kernel-checked Theorem must carry its proof value"
    );

    // Confirm the type signature type-checks via the kernel TypeChecker.
    let thm = Expr::const_(
        Name::from_string("NNVerify.LayerNorm.zonotope_generators_reset"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("kernel must infer T22 type from fresh env");
    // The Branch B diagonal-entry equation is
    // `forall (n k : Nat) (z : Zonotope n k) (i : Fin n),
    //    generators_after_ln n k z i i = Fin.sum k (fun j => Rat.abs (z.generators i j))`,
    // which has 4 Pi binders (n, k, z, i) — the carrier now genuinely
    // consumes a zonotope and an index, not just two Nats.
    let mut binder_count = 0;
    let mut cursor = ty.clone();
    while let ExprKind::Pi(_, _, body) = cursor.kind() {
        binder_count += 1;
        cursor = (**body).clone();
    }
    assert_eq!(
        binder_count, 4,
        "T22 Branch B diagonal-entry equation should have exactly 4 Pi \
         binders (n, k, z, i). Got {} binders.",
        binder_count,
    );
}
