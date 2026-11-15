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

/// The shape VC-6 used to refuse now WORKS, and the refusal is gone.
///
/// The refusal claimed a constructor with several recursive arguments, one of
/// them an indexed family, could not have its tier built. That was written
/// from "no worked precedent", never measured. Measured, the shape is fine —
/// what actually broke was two unrelated generator bugs (§12), both of which
/// hit far more ordinary shapes. This test is the retired refusal's negative:
/// if anyone re-adds it, this fails.
#[test]
fn test_the_retired_kfold_refusal_stays_retired() {
    let src = "
codata Mx (A : Type) where
  | Mix : Mx A → (A → Mx A) → Mx A
deriving Coind
";
    let env = elaborate(src).expect("the k-fold indexed-family shape must be accepted");
    for n in [
        "Mx.Mix_eta",
        "Mx.MixChild0",
        "Mx.MixChild1",
        "Mx.MixChild0_compute",
        "Mx.MixChild1_compute",
        "Mx.CasesP",
        "Mx.cases",
    ] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "the full tier must be emitted for the once-refused shape ({n})"
        );
    }
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
///
/// It also covers the two `cases_tower` branches ITr cannot reach: a
/// SINGLE-constructor codata (no `Sum` exists, so no `sumCases` is emitted
/// and the head equation is `rfl` rather than a folded chain) and a
/// three-way codata whose LAST constructor carries payloads (ITr's `Br`
/// carries none, so the last-leaf projection path had only run at arity 0).
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
        // single-constructor codata: the no-`Sum` branch of the tower
        "Stream1.cases_used",
        "Stream1.eta_used",
        "Stream1.CasesP",
        // three constructors, the LAST carrying payloads
        "Tri.cases_used",
        "Tri.three_eta_used",
        // regression pins for the two generator bugs of 2026-08-29 (§12)
        "Sc.cases_used", // lone ctor, first argument recursive
        "Mx.cases_used", // ... at k-fold arity with an indexed family
        "Mx.eta_used",
        "Cp.cases_used", // payload AFTER a child
        "Iv.cases_used", // payload BETWEEN two children
        "Dv.cases_used", // family domain mentioning a payload (control)
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
    assert!(
        env.get_const(&Name::from_string("Stream1.sumCases"))
            .is_none(),
        "a single-constructor codata has no `Sum` to dispatch on, so the tower \
         must not emit `sumCases` for it"
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

/// Universe-polymorphic variant codata, with the full coinductive tier.
///
/// The anti-vacuity half is the instantiation at a TYPE-valued parameter
/// (`St.{1} Type`). Checking only at `Nat` would prove nothing: a fresh level
/// metavariable that silently solves to `0` yields a well-typed,
/// kernel-accepted, strictly WEAKER declaration — the same hazard that made
/// `elab_hole` pin every `_` to `Sort 1`. A monomorphic generator passes a
/// `Nat`-only test and fails this one.
#[test]
fn test_universe_polymorphic_fixture() {
    let src = include_str!("../data/variant_codata/universe_poly.lean");
    let env = elaborate(src).expect("the universe-polymorphic fixture must check");
    for n in [
        "St.shapeF",
        "St.posF",
        "St.head",
        "St.Cons",
        "St.corec",
        "St.ext",
        "St.Cons_eta",
        "St.ConsChild",
        "St.CasesP",
        "St.cases",
        // the consumers, which is what says the tier is usable at `.{u}`
        "bigNil",
        "big_cases",
        "cons_eta",
        "forever",
        "forever_unfolds",
        // the `T.{u}` self-reference spelling, and the two spellings mixed
        "sf_cases",
        "mixed_cases",
    ] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "universe-polymorphic declaration {n} must register"
        );
    }
}

/// Every generated declaration carries the declared universe parameter.
///
/// Without the `set_uparams` sweep the family would register as monomorphic
/// and every use site would silently pin `u := 0` — green tests, wrong
/// theorems.
#[test]
fn test_universe_param_is_stamped_on_generated_heads() {
    let src = "
codata Up.{u} (A : Type u) where
  | C : A → Up A → Up A
deriving Coind
";
    let env = elaborate(src).expect("`codata Up.{u}` must elaborate");
    for n in [
        "Up.shapeF",
        "Up.head",
        "Up.C",
        "Up.ext",
        "Up.C_eta",
        "Up.cases",
    ] {
        let c = env
            .get_const(&Name::from_string(n))
            .unwrap_or_else(|| panic!("{n} must register"));
        assert_eq!(
            c.level_params.len(),
            1,
            "{n} must carry the declared universe parameter, not be monomorphic"
        );
    }
}

/// A self-reference at a DIFFERENT universe is not the carrier.
///
/// `Bad.{0} A` inside `codata Bad.{u}` denotes another type entirely, so
/// accepting it would silently monomorphise the declaration. The negative
/// half of letting `T.{u} A` through: the widening must not become "any
/// universe instantiation of the right name".
#[test]
fn test_self_reference_at_a_different_universe_is_refused() {
    let src = "
codata Bad.{u} (A : Type u) where
  | C : Bad.{0} A → Bad A
";
    let err = elaborate(src).expect_err("a foreign-universe self-reference must be refused");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("occurs neither as"),
        "the refusal must name the occurrence problem, got: {msg}"
    );
}

/// The generated ITree carrier is definitionally equal to ITreeEco's.
///
/// VC-7's first obstacle: ITreeEco declared its own empty inductive `NoPos`
/// where the generator emits `PEmpty`, and two distinct inductives are never
/// definitionally equal. With ITreeEco moved to `PEmpty`, both the position
/// functor and the carrier agree by `rfl` — so the 716 declarations built on
/// that carrier would survive redefining it as the generated one.
#[test]
fn test_itree_carrier_is_defeq() {
    let src = include_str!("../data/variant_codata/itree_carrier_defeq.lean");
    let env = elaborate(src).expect("the carrier-defeq fixture must check");
    for n in ["pos_agrees", "carrier_agrees"] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "{n} must register — it is the evidence VC-7 rests on"
        );
    }
}
