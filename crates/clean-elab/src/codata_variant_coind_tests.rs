// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the VC-6 coinductive tier ([`crate::codata_variant_coind`]).

use clean_kernel::{Environment, Name};

/// Elaborate a source file into a fresh prelude env, returning the env.
fn elaborate(src: &str) -> Result<Environment, crate::ElabError> {
    let decls = clean_parser::parse_file(src).expect("fixture must parse");
    let mut env = Environment::with_prelude();
    for d in &decls {
        crate::elaborate_decl_and_register(&mut env, d)?;
    }
    Ok(env)
}

/// The four-position-shape codata, without the coinductive tier.
const ITR: &str = r"
codata ITr (E : Type) (R : Type) (Ans : E → Type) where
  | Ret : R → ITr E R Ans
  | Tau : ITr E R Ans → ITr E R Ans
  | Vis : (e : E) → (Ans e → ITr E R Ans) → ITr E R Ans
  | Br : ITr E R Ans → ITr E R Ans → ITr E R Ans
";

/// The same, asking for the coinductive tier.
fn itr_coind() -> String {
    format!("{ITR}deriving Coind\n")
}

/// `deriving Coind` is what turns the tier on — and nothing else does.
///
/// The negative half is the cost guarantee: a codata that does not ask must
/// not pay for `iM_coind` (the seed section alone is +31 declarations, and
/// coinductive discharges are the expensive part of checking).
#[test]
fn test_coind_tier_is_opt_in() {
    let plain = elaborate(ITR).expect("plain codata must elaborate");
    assert!(
        plain.get_const(&Name::from_string("ITr.ext")).is_none(),
        "the coinductive tier must NOT be emitted without `deriving Coind`"
    );
    assert!(
        plain
            .get_const(&Name::from_string("Codata.iM_coind"))
            .is_none(),
        "the coinduction seed section must not be injected without `deriving Coind`"
    );

    let with = elaborate(&itr_coind()).expect("`deriving Coind` must elaborate");
    assert!(
        with.get_const(&Name::from_string("ITr.ext")).is_some(),
        "`deriving Coind` must emit one-step extensionality"
    );
    assert!(
        with.get_const(&Name::from_string("Codata.iM_coind"))
            .is_some(),
        "`deriving Coind` must inject the coinduction seed section"
    );

    // What the tier costs, pinned rather than asserted in prose: the 31
    // seed-section constants plus the tier's own declarations. For this
    // four-constructor codata (one empty, one unit, one family, one 2-fold)
    // the eta half is 2 wrappers + 6 shared + 1/4/4/7 per constructor = 24,
    // and the case tower adds 9 (CasesP, sumCases, one cases_Cₖ each, one
    // hoisted inner for each 2-argument constructor, and `cases` itself).
    let seed_section = 31usize;
    let tier = with.num_constants() - plain.num_constants() - seed_section;
    assert_eq!(
        tier,
        24 + 9,
        "the coinductive tier for a 4-constructor codata is 33 declarations; \
         a change here means a template was added or dropped"
    );
}

/// Every constructor gets an eta law, and every position shape its
/// extractors — all four VC-1 shapes in one declaration.
#[test]
fn test_every_position_shape_gets_its_companions() {
    let env = elaborate(&itr_coind()).expect("fixture must elaborate");
    for n in [
        // shared tier
        "ITr.child",
        "ITr.cast",
        "ITr.ExtQ",
        "ITr.ExtQ_hhead",
        "ITr.ExtQ_of_eq",
        "ITr.ext_unwrap",
        "ITr.ch_cast_irrel",
        "ITr.ext",
        // eta, one per constructor — including `Ret`, whose children clause
        // is vacuous and whose eta law therefore has no extractor at all
        "ITr.Ret_eta",
        "ITr.Tau_eta",
        "ITr.Vis_eta",
        "ITr.Br_eta",
        // extractors: unit, dependent family, and the k-fold pair
        "ITr.TauChild",
        "ITr.VisChild",
        "ITr.BrChild0",
        "ITr.BrChild1",
        // computation pins
        "ITr.TauChild_compute",
        "ITr.VisChild_compute",
        "ITr.BrChild0_compute",
        "ITr.BrChild1_compute",
        // the N-ary case tower
        "ITr.CasesP",
        "ITr.sumCases",
        "ITr.cases",
        "ITr.cases_Ret",
        "ITr.cases_Tau",
        "ITr.cases_Vis",
        "ITr.cases_Br",
        // hoisted inner existentials, only for constructors with 2+ args
        "ITr.cases_Vis_inner1",
        "ITr.cases_Br_inner1",
    ] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "`deriving Coind` must emit {n}"
        );
    }
    assert!(
        env.get_const(&Name::from_string("ITr.RetChild")).is_none(),
        "a constructor with no recursive argument must get NO child extractor"
    );
    for n in ["ITr.cases_Ret_inner1", "ITr.cases_Tau_inner1"] {
        assert!(
            env.get_const(&Name::from_string(n)).is_none(),
            "a one-argument constructor needs no hoisted inner existential ({n})"
        );
    }
}

/// A constructor with several recursive arguments AND an indexed one is
/// refused BY NAME, not left to fail as a confusing kernel error.
///
/// This is the honest edge of the probed envelope: the k-fold branch template
/// is validated for Sums of bare children only. The refusal must also be
/// transactional — the definitional tier still works for such a codata, so
/// the user's recourse (drop `deriving Coind`) has to leave a clean env.
#[test]
fn test_mixed_kfold_is_refused_by_name() {
    let src = "
codata Bad (A : Type) where
  | Mix : Bad A → (A → Bad A) → Bad A
deriving Coind
";
    let err = elaborate(src).expect_err("mixed k-fold must be refused");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("deriving Coind") && msg.contains("INDEXED family"),
        "the refusal must name the shape it cannot build, got: {msg}"
    );
}

/// The whole fixture, including the laws that are NOT `rfl`.
///
/// `ITr.spin_unfolds` is the load-bearing line: `spin` is built by `corec`,
/// so `spin = Tau spin` cannot be checked by reduction. Stating it with `rfl`
/// is REJECTED (measured — a `Subtype.mk` mismatch on the approximation
/// tower), which is what makes this fixture evidence that eta does real
/// coinductive work rather than restating a definitional law.
#[test]
fn test_eta_fixture_checks() {
    let src = include_str!("../data/variant_codata/itree_eta.lean");
    let env = elaborate(src).expect("the eta fixture must check");
    for n in [
        "ITr.eta_on_Tau",
        "ITr.eta_on_Br",
        "ITr.eta_on_Ret",
        "ITr.eta_on_Vis",
        "ITr.spin_unfolds",
        "ITr.bspin_unfolds",
        "ITr.spin_eq_spin2",
        // the case tower, consumed: `casesOn` is hand-written on top of the
        // generated `CasesP`/`cases`, so it only typechecks if the generated
        // disjunction nests exactly as the generator claims
        "ITr.casesOn",
        "ITr.spin_is_some_constructor",
    ] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "fixture theorem {n} must register"
        );
    }
}

/// `spin = Tau spin` by `rfl` must be REJECTED.
///
/// The anti-vacuity control for the whole tier, as a test rather than a
/// comment: if this ever started passing, eta would have become a
/// definitional law and `iM_coind` would be doing nothing.
#[test]
fn test_eta_on_a_corecursive_value_is_not_rfl() {
    let src = format!(
        "{}
def ITr.spin (E : Type) (R : Type) (Ans : E → Type) : ITr E R Ans :=
  ITr.corec E R Ans PUnit.{{1}} (fun j s => ITr.step_Tau E R Ans PUnit.{{1}} j s) PUnit.unit

theorem ITr.spin_unfolds (E : Type) (R : Type) (Ans : E → Type) :
    ITr.spin E R Ans = ITr.Tau E R Ans (ITr.spin E R Ans) := rfl
",
        itr_coind()
    );
    assert!(
        elaborate(&src).is_err(),
        "`spin = Tau spin` must NOT be definitional — if it were, the eta law \
         would be vacuous"
    );
}

/// The two constructor shapes the ITr fixture cannot reach.
///
/// Every ITr constructor has at most one payload and at least one recursive
/// argument, so two corners the generator reasons about went unexercised: a
/// NULLARY constructor (whose `CasesP` disjunct is a bare equation with no
/// existential, and whose eta law has no extractor) and a TWO-payload one
/// (whose `Pₖ` is a `PProd`, so the `T.cases` leaf recovers payloads by
/// projection and hands the eta law `tag (PProd.mk p.1 p.2)` against a bound
/// `p` — which type-checks only because structure eta is definitional).
#[test]
fn test_corner_shapes_check() {
    let src = include_str!("../data/variant_codata/corner_shapes.lean");
    let env = elaborate(src).expect("the corner-shape fixture must check");
    for n in [
        "Two.nil_cases",
        "Two.pair_cases",
        "Two.pair_eta_used",
        // the nullary constructor gets an eta law but NO extractor
        "Two.Nil_eta",
        "Two.PairChild",
    ] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "corner-shape declaration {n} must register"
        );
    }
    assert!(
        env.get_const(&Name::from_string("Two.NilChild")).is_none(),
        "a nullary constructor must get no child extractor"
    );
    assert!(
        env.get_const(&Name::from_string("Two.cases_Nil_inner1"))
            .is_none(),
        "a nullary constructor needs no hoisted inner existential"
    );
}

/// A constructor may not take one of the case tower's names.
///
/// `cases` is the sharp one: it would collide with `T.cases` itself AND
/// generate `T.cases_cases`. The refusal belongs in VC-1's envelope check,
/// where the user sees it, not in the downstream duplicate detector.
#[test]
fn test_tower_names_are_reserved() {
    for bad in ["cases", "CasesP", "sumCases"] {
        let src = format!("codata Bad (A : Type) where\n  | {bad} : Bad A → Bad A\n");
        let err = elaborate(&src)
            .expect_err("a constructor taking a generated companion name must be refused");
        let msg = format!("{err:?}");
        assert!(
            msg.contains("collides with the generated companion"),
            "the refusal must name the collision for `{bad}`, got: {msg}"
        );
    }
}
