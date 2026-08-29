// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for VARIANT codata GENERATION — bricks VC-3, VC-4 and VC-5 of
//! `designs/2026-08-28-variant-codata-surface.md`.
//!
//! Four kinds of evidence, in increasing strength:
//!
//! 1. the family elaborates and every generated law kernel-checks;
//! 2. what the generator emits is the SAME kernel term as the hand-written,
//!    independently kernel-checked `data/variant_codata/itree_target.lean`
//!    (binder names are not part of a de Bruijn `Expr`, so this is equality
//!    up to α, which is the strongest available comparison);
//! 3. the generated family PROVES constructor disjointness — the one
//!    property a degenerate `shapeF` could not fake;
//! 4. the generated CORECURSOR builds a value whose unfolding never
//!    terminates — the one property a `corec` that ignored its coalgebra and
//!    returned a finite value could not fake.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

const ITREE_SRC: &str = r"
codata ITr (E : Type) (R : Type) (Ans : E → Type) where
  | Ret : R → ITr E R Ans
  | Tau : ITr E R Ans → ITr E R Ans
  | Vis : (e : E) → (Ans e → ITr E R Ans) → ITr E R Ans
  | Br : ITr E R Ans → ITr E R Ans → ITr E R Ans
";

/// Elaborate every declaration in `src`, panicking with the failing index.
fn elab_all(src: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let decls = parse_file(src).expect("fixture must parse");
    for (i, decl) in decls.iter().enumerate() {
        elaborate_decl_and_register(&mut env, decl)
            .unwrap_or_else(|e| panic!("declaration {i} failed to elaborate: {e:?}"));
    }
    env
}

fn get<'e>(env: &'e Environment, name: &str) -> &'e clean_kernel::ConstantInfo {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} must be registered"))
}

/// The whole definitional tier lands, by name, and the carrier carries the
/// `codata` provenance mark the record lane also sets.
#[test]
fn test_variant_codata_generates_the_definitional_tier() {
    let env = elab_all(ITREE_SRC);
    for name in [
        "ITr",
        "ITr.shapeF",
        "ITr.posF",
        "ITr.tgtF",
        "ITr.mkStep",
        "ITr.head",
        "ITr.Ret",
        "ITr.Tau",
        "ITr.Vis",
        "ITr.Br",
        "ITr.head_Ret",
        "ITr.head_Tau",
        "ITr.head_Vis",
        "ITr.head_Br",
        "ITr.child_Tau",
        "ITr.child_Vis",
        "ITr.child_Br_0",
        "ITr.child_Br_1",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "the generator must register {name}"
        );
    }
    // `Ret` has no children, so it has no child law — the position type is
    // `PEmpty.{1}` and there is nothing to state.
    assert!(
        env.get_const(&Name::from_string("ITr.child_Ret")).is_none(),
        "a childless constructor must not get a child law"
    );
    assert!(
        env.is_codata_carrier(&Name::from_string("ITr")),
        "the carrier must carry the codata provenance mark"
    );
}

/// The generated declarations are the SAME kernel terms as the hand-written
/// target fixture, which was kernel-checked independently of this generator
/// (`codata_variant_tests::test_variant_lowering_target_kernel_checks`).
///
/// Binder names live outside `ExprKind::Lam`/`Pi` (`BinderData` holds only
/// `info` and `mult`), so `Expr` equality IS α-equivalence: this compares
/// the terms, not the spellings. Where the fixture and the generator name
/// things differently — the fixture's `l`/`r` for `Br`'s anonymous
/// arguments, its `child_Br_left`/`child_Br_right` for the per-position
/// laws — the comparison is unaffected except for the law NAMES, which are
/// mapped explicitly below.
#[test]
fn test_generated_family_matches_the_hand_written_target() {
    const TARGET: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/data/variant_codata/itree_target.lean"
    ));
    let hand = elab_all(TARGET);
    let generated = elab_all(ITREE_SRC);
    for (gen_name, hand_name) in [
        ("ITr.shapeF", "ITr.shapeF"),
        ("ITr.posF", "ITr.posF"),
        ("ITr.tgtF", "ITr.tgtF"),
        ("ITr", "ITr"),
        ("ITr.mkStep", "ITr.mkStep"),
        ("ITr.Ret", "ITr.Ret"),
        ("ITr.Tau", "ITr.Tau"),
        ("ITr.Vis", "ITr.Vis"),
        ("ITr.Br", "ITr.Br"),
        ("ITr.head", "ITr.head"),
        ("ITr.head_Ret", "ITr.head_Ret"),
        ("ITr.head_Tau", "ITr.head_Tau"),
        ("ITr.head_Vis", "ITr.head_Vis"),
        ("ITr.head_Br", "ITr.head_Br"),
        ("ITr.child_Tau", "ITr.child_Tau"),
        ("ITr.child_Vis", "ITr.child_Vis"),
        ("ITr.child_Br_0", "ITr.child_Br_left"),
        ("ITr.child_Br_1", "ITr.child_Br_right"),
        // the corecursor tier (VC-4): `Step` is the coalgebra's codomain in
        // the codata's own vocabulary, each `step_C` is the CONSTRUCTOR with
        // the carrier replaced by the state, `corec` is `Codata.ucorec` at
        // this container. All six are the hand-written terms exactly.
        ("ITr.Step", "ITr.Step"),
        ("ITr.step_Ret", "ITr.step_Ret"),
        ("ITr.step_Tau", "ITr.step_Tau"),
        ("ITr.step_Vis", "ITr.step_Vis"),
        ("ITr.step_Br", "ITr.step_Br"),
        ("ITr.corec", "ITr.corec"),
    ] {
        let g = get(&generated, gen_name);
        let h = get(&hand, hand_name);
        assert_eq!(
            g.type_, h.type_,
            "{gen_name} does not have the hand-written type of {hand_name}\n\
             generated: {:?}\nhand-written: {:?}",
            g.type_, h.type_
        );
        assert_eq!(
            g.value, h.value,
            "{gen_name} does not have the hand-written value of {hand_name}\n\
             generated: {:?}\nhand-written: {:?}",
            g.value, h.value
        );
    }
}

/// THE anti-vacuity check of VC-3 and VC-5: the generated family proves
/// `ITr.Cⱼ x = ITr.Cₖ y → False` for the WHOLE matrix — all 5·4/2 = 10 pairs
/// of the fixture's five constructors. A generator that mapped two
/// constructors to the same tag would still satisfy every `rfl` law it emits
/// and would fail only here; the fixture's `Tau`/`Delay` pair is deliberately
/// the same shape (`Pₖ` and `Qₖ` identical), so collapsing THEM produces no
/// type error anywhere else in the family.
///
/// The fixture's own theorems are CONSUMERS of the generated ones, in `Not`
/// form and symmetrised — evidence that the generated statements are usable,
/// not merely present.
#[test]
fn test_generated_family_proves_constructor_disjointness() {
    const DISJOINT: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/data/variant_codata/itree_disjointness.lean"
    ));
    let env = elab_all(DISJOINT);
    let ctors = ["Ret", "Tau", "Vis", "Br", "Delay"];
    let mut pairs = 0usize;
    for (j, cj) in ctors.iter().enumerate() {
        for ck in &ctors[j + 1..] {
            let name = format!("ITr.{cj}_ne_{ck}");
            let info = get(&env, &name);
            assert!(
                info.value.is_some(),
                "{name} must be a proved theorem, not an axiom"
            );
            pairs += 1;
            // The reverse spelling is NOT generated — one statement per
            // unordered pair, symmetrised by the caller with `Eq.symm`
            // (`ITr.br_not_ret` in the fixture).
            assert!(
                env.get_const(&Name::from_string(&format!("ITr.{ck}_ne_{cj}")))
                    .is_none(),
                "only the ordered pair is generated"
            );
        }
    }
    assert_eq!(pairs, 10, "n·(n−1)/2 for n = 5");
    for name in [
        "ITr.tau_not_delay",
        "ITr.tau_not_vis",
        "ITr.br_not_ret",
        "ITr.ret_eq_of_eq",
        "ITr.vis_event_inj",
    ] {
        assert!(
            get(&env, name).value.is_some(),
            "{name} consumes a generated companion and must be proved"
        );
    }
}

/// THE anti-vacuity check of VC-4: the generated corecursor builds a value
/// whose unfolding never terminates.
///
/// `ITr.head_spin` on its own is worthless — a `corec` that ignored its
/// coalgebra and returned the FINITE `ITr.Tau x` would satisfy it, since the
/// head of a `Tau` is the `Tau` tag whatever sits underneath. `ITr.child_spin`
/// is the law that separates them: the child of `spin` is `spin` itself, by
/// `rfl`. MEASURED: substituting a finite `ITr.Tau (ITr.Tau x)` keeps the head
/// law and breaks the child law.
#[test]
fn test_generated_corecursor_builds_an_infinite_value() {
    const COREC: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/data/variant_codata/itree_corec.lean"
    ));
    let env = elab_all(COREC);
    for name in [
        "ITr.spin",
        "ITr.head_spin",
        "ITr.child_spin",
        "ITr.child_spin_via_law",
        "ITr.visLoop",
        "ITr.head_visLoop",
        "ITr.child_visLoop",
        "ITr.Ret_ne_spin",
    ] {
        assert!(
            get(&env, name).value.is_some(),
            "{name} must be a proved theorem/definition"
        );
    }
}

/// The whole corecursor tier lands, by name, and the shape of the per-step
/// child laws follows the same rule as the constructor child laws: none for a
/// childless constructor, one unindexed law for a single child, one per
/// injection for several.
#[test]
fn test_variant_codata_generates_the_corecursor_tier() {
    let env = elab_all(ITREE_SRC);
    for name in [
        "ITr.Step",
        "ITr.step_Ret",
        "ITr.step_Tau",
        "ITr.step_Vis",
        "ITr.step_Br",
        "ITr.corec",
        "ITr.head_corec",
        "ITr.child_corec",
        "ITr.head_step_Ret",
        "ITr.head_step_Tau",
        "ITr.head_step_Vis",
        "ITr.head_step_Br",
        "ITr.child_step_Tau",
        "ITr.child_step_Vis",
        "ITr.child_step_Br_0",
        "ITr.child_step_Br_1",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "the generator must register {name}"
        );
    }
    assert!(
        env.get_const(&Name::from_string("ITr.child_step_Ret"))
            .is_none(),
        "a childless constructor's step builder has no child law"
    );
}

/// The VC-5 companions land, and only where they mean something: a
/// constructor with no payload gets no retraction and no injectivity, because
/// there is nothing to retract.
#[test]
fn test_variant_codata_generates_the_companions() {
    let env = elab_all(ITREE_SRC);
    for name in [
        "ITr.isRet",
        "ITr.isTau",
        "ITr.isVis",
        "ITr.isBr",
        "ITr.Ret_ne_Tau",
        "ITr.Ret_ne_Vis",
        "ITr.Ret_ne_Br",
        "ITr.Tau_ne_Vis",
        "ITr.Tau_ne_Br",
        "ITr.Vis_ne_Br",
        "ITr.out_Ret",
        "ITr.Ret_inj",
        "ITr.out_Vis",
        "ITr.Vis_inj",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "the generator must register {name}"
        );
    }
    for name in [
        "ITr.out_Tau",
        "ITr.Tau_inj",
        "ITr.out_Br",
        "ITr.Br_inj",
        // one payload means the packed `Pₖ` equation IS the payload
        // equation; no projected variants are minted
        "ITr.Ret_inj_0",
        "ITr.Vis_inj_0",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} must not be generated"
        );
    }
}

/// A one-constructor variant is the record encoding, so there is nothing to
/// discriminate: no classifier and no disjointness theorem is minted, and the
/// tag tower — which has no tag — is never built. Injectivity survives,
/// because a single constructor can still be injective.
#[test]
fn test_single_constructor_variant_skips_discrimination() {
    let env = elab_all("codata VBox (A : Type) where\n  | wrap : A → VBox A → VBox A\n");
    for name in ["VBox.out_wrap", "VBox.wrap_inj", "VBox.corec"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "the generator must register {name}"
        );
    }
    assert!(
        env.get_const(&Name::from_string("VBox.iswrap")).is_none(),
        "a one-constructor variant has nothing to classify"
    );
}

/// The two telescopes of an injectivity statement must be genuinely
/// DIFFERENT binders. This is the vacuity a naive generator falls into: both
/// sides of `T.wrap x = T.wrap y → x = y` would be written with the
/// constructor's own binder names, the second shadowing the first, and the
/// theorem would degrade to the true-but-useless `x = x` — still kernel-
/// checking, still registered, and silently worthless.
///
/// The check is a CONSUMER that supplies two distinct values: it only
/// elaborates if the generated statement really quantifies over both.
#[test]
fn test_generated_injectivity_binds_two_distinct_telescopes() {
    let env = elab_all(
        "codata VBox (A : Type) where\n  \
           | wrap : (r : A) → VBox A → VBox A\n  \
           | loop : VBox A → VBox A\n\
         theorem VBox.use (A : Type) (p : A) (q : A) (x : VBox A) (y : VBox A)\n    \
           (h : VBox.wrap A p x = VBox.wrap A q y) : p = q :=\n  \
           VBox.wrap_inj A p x q y h\n",
    );
    assert!(
        get(&env, "VBox.use").value.is_some(),
        "the generated injectivity must accept two distinct telescopes"
    );
}

/// A constructor may collide with a companion derived from ANOTHER
/// constructor's name — `| Ret | head_Ret` mints `T.head_Ret` twice. The
/// reserved-name list cannot see that (it only knows the FIXED companions),
/// so the generator checks its own output and refuses by name instead of
/// letting the kernel report a duplicate declaration.
#[test]
fn test_generated_name_collision_is_a_named_refusal() {
    let mut env = Environment::with_prelude();
    let decls = parse_file(
        "codata Clash (A : Type) where\n  | Ret : A → Clash A\n  \
         | head_Ret : Clash A → Clash A\n",
    )
    .expect("should parse");
    let err = elaborate_decl_and_register(&mut env, &decls[0])
        .expect_err("a generated-name collision must be refused");
    let text = format!("{err:?}");
    assert!(
        text.contains("two generated declarations would both be called")
            && text.contains("Clash.head_Ret"),
        "the refusal must name the colliding declaration; got {text}"
    );
    assert!(
        env.get_const(&Name::from_string("Clash")).is_none(),
        "nothing may register"
    );
}

/// The mixed shape end-to-end: a nullary constructor (`PEmpty.{1}`
/// positions), a two-payload constructor whose child domain projects out of
/// a `PProd` (`Ans s.2`), and a two-bare-child constructor (`Sum`
/// positions). This is the shape whose projection path is not the identity,
/// so it is the one that would break if `PProd` projection inside a
/// `Sum.rec` branch did not elaborate.
///
/// The load-bearing declaration is the last one: `Mix.posF` at `Two`'s tag
/// must be `Ans e` BY `rfl`. That is the projection, stated as an equation
/// the kernel checks — with `s.1` instead of `s.2` it would be `Ans n` and
/// not even typecheck (`n : Nat`, and `Ans : E → Type`), and with the
/// payload left free it would not elaborate at all.
#[test]
fn test_mixed_shape_generates_and_computes() {
    let src = r"
codata Mix (E : Type) (Ans : E → Type) where
  | Stop : Mix E Ans
  | Two : (n : Nat) → (e : E) → (Ans e → Mix E Ans) → Mix E Ans
  | Fork : Mix E Ans → Mix E Ans → Mix E Ans

theorem Mix.posTwo (E : Type) (Ans : E → Type) (n : Nat) (e : E) :
    Mix.posF E Ans PUnit.unit (Sum.inr (Sum.inl (PProd.mk n e))) = Ans e := rfl
";
    let env = elab_all(src);
    for name in [
        "Mix",
        "Mix.shapeF",
        "Mix.posF",
        "Mix.Stop",
        "Mix.Two",
        "Mix.Fork",
        "Mix.head_Stop",
        "Mix.head_Two",
        "Mix.head_Fork",
        "Mix.child_Two",
        "Mix.child_Fork_0",
        "Mix.child_Fork_1",
        "Mix.posTwo",
        // the corecursor tier over the same three shapes
        "Mix.step_Stop",
        "Mix.step_Two",
        "Mix.step_Fork",
        "Mix.corec",
        // the companions: three pairs (3·2/2), and `Two` is the only
        // constructor with a payload — a two-factor `PProd` one, so its
        // injectivity is ALSO projected apart
        "Mix.Stop_ne_Two",
        "Mix.Stop_ne_Fork",
        "Mix.Two_ne_Fork",
        "Mix.out_Two",
        "Mix.Two_inj",
        "Mix.Two_inj_0",
        "Mix.Two_inj_1",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "the generator must register {name}"
        );
    }
    // `Stop` has no children and `Two` has exactly one, so neither gets an
    // indexed family of child laws.
    assert!(
        env.get_const(&Name::from_string("Mix.child_Stop"))
            .is_none(),
        "a childless constructor must not get a child law"
    );
    assert!(
        env.get_const(&Name::from_string("Mix.child_Two_0"))
            .is_none(),
        "a one-child constructor gets `child_C`, not `child_C_0`"
    );
}

/// n = 1 reproduces the RECORD lane exactly (design §3). A record codata
/// with k observations and m recursive fields and the one-constructor
/// variant `| step : T₁ → … → T_k → C → … → C → C` must build the same
/// container: the same `PProd` label, the same `Sum`-of-units positions,
/// the same constant target family.
///
/// MEASURED, and the reason only the VALUES are compared below: a container
/// definition's TYPE names the ones before it (`posF`'s type mentions
/// `<C>.shapeF`, `tgtF`'s mentions both), so two differently-named families
/// can never have equal container types. The values of `shapeF`, `posF` and
/// `tgtF` mention no name from their own family, and those are equal.
#[test]
fn test_single_constructor_variant_reproduces_the_record_encoding() {
    let env = elab_all(
        "codata Pair (A : Type) (B : Type) where\n  \
           fst : A\n  snd : B\n  left : Pair A B\n  right : Pair A B\n\
         codata VPair (A : Type) (B : Type) where\n  \
           | step : A → B → VPair A B → VPair A B → VPair A B\n",
    );
    for (record, variant) in [
        ("Pair.shapeF", "VPair.shapeF"),
        ("Pair.posF", "VPair.posF"),
        ("Pair.tgtF", "VPair.tgtF"),
    ] {
        assert_eq!(
            get(&env, record).value,
            get(&env, variant).value,
            "{variant} must be the same container definition as {record}"
        );
    }
    // `shapeF` is the one whose type is also name-free, so it can be
    // compared whole — the label type `PProd A B` really is the same object
    // in both lanes, not merely a term that happens to reduce the same way.
    assert_eq!(
        get(&env, "Pair.shapeF").type_,
        get(&env, "VPair.shapeF").type_,
        "the shape functor must have the same type in both lanes"
    );
}

/// Transactional registration: a declaration that passes the whole envelope
/// but cannot elaborate (an unknown payload type) leaves the environment
/// byte-identical — no partial family, and not even the lazy `Codata.*`
/// seed the candidate clone pulled in.
#[test]
fn test_failed_generation_registers_nothing() {
    let mut env = Environment::with_prelude();
    // The per-declaration prologue (`init_pprod`, the B101 bridge) adds
    // constants for ANY declaration; take the baseline after it has run.
    let warmup = parse_file("def genWarmup : Nat := Nat.zero").expect("should parse");
    elaborate_decl_and_register(&mut env, &warmup[0]).expect("warmup must elaborate");
    let before = env.num_constants();

    let decls = parse_file(
        "codata Bad (A : Type) where\n  | Leaf : NoSuchTypeAnywhere → Bad A\n  \
         | Node : Bad A → Bad A\n",
    )
    .expect("should parse");
    let err = elaborate_decl_and_register(&mut env, &decls[0])
        .expect_err("an unresolvable payload type must fail");
    let text = format!("{err:?}");
    assert!(
        text.contains("env left untouched"),
        "the failure must be reported as the transactional one; got {text}"
    );
    assert_eq!(
        env.num_constants(),
        before,
        "a failed variant codata must leave the environment byte-identical"
    );
    assert_eq!(
        env.constants()
            .filter(|c| {
                let n = c.name.to_string();
                n.starts_with("Codata.") || n == "Bad" || n.starts_with("Bad.")
            })
            .count(),
        0,
        "neither a partial family nor the lazy Codata.* seed may survive"
    );
    assert!(
        !env.is_codata_carrier(&Name::from_string("Bad")),
        "a failed family must not leave the carrier provenance mark"
    );
}
