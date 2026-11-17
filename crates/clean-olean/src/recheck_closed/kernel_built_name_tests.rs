// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Attack battery, round 24: names the kernel BUILDS or STRIPS by name.
//!
//! Round 23 gated the names the type checker REDUCES by name. Two more kinds
//! of by-name reference survived it, both outside `tc/`:
//!
//! * **kernel-built types.** `init_quot` builds `Quot.lift`'s and
//!   `Quot.sound`'s types around the constant NAMED `Eq` and never checks
//!   them. The replay installed the quotient before admitting anything, so the
//!   cone's own `Eq` — admitted later, unchecked against that use — decided
//!   what the axiom `Quot.sound` says (verifier, round 23).
//! * **by-name stripping.** `add_inductive_core` generates every recursor with
//!   its binder domains passed through `consume_type_annotations`, which
//!   rewrites `optParam α d` / `autoParam α t` / `outParam α` /
//!   `semiOutParam α` to `α` by NAME — sound only when each of those names
//!   unfolds to `α`. No false accept was found through it (the kernel's
//!   subject-reduction check on generated ι-rules refuses the field-level
//!   forgery, test below), but it is a by-name meaning a cone could supply, so
//!   the four names are now gated like the rest.
//!
//! Each quotient attack proves a closed inhabitant of the empty `RC.False`,
//! and is shown to PASS when the relevant gate is absent (a table derived from the
//! forged environment binds whatever the cone declares, which is what "no
//! gate" amounts to; `Environment::init_quot` up front is what the replay did
//! before), so the fixture is live and the gate is what stops it.

use super::super::{recheck_closed, ClosedRecheckOptions, ClosedRecheckRefusal};
use super::ExtensionBindings;
use clean_kernel::env::{
    ConstantInfo, ConstantKind, Environment, Reducibility, TrustedEnvExt as _,
};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use std::collections::BTreeSet;

fn n(s: &str) -> Name {
    Name::interned(s)
}

fn konst(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn prop() -> Expr {
    Expr::sort(Level::zero())
}

fn sort_u() -> Expr {
    Expr::sort(Level::param(n("u")))
}

fn arrow(a: Expr, b: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, a, b)
}

fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}

fn targets(names: &[&str]) -> BTreeSet<Name> {
    names.iter().map(|s| n(s)).collect()
}

fn import_structurally(env: &mut Environment, info: ConstantInfo) {
    let rejected = env.extend_constants_structural(std::iter::once(info));
    assert!(
        rejected.is_empty(),
        "structural tier rejected the fixture: {rejected:?}"
    );
}

fn decl(name: &str, kind: ConstantKind, type_: Expr, value: Option<Expr>) -> ConstantInfo {
    ConstantInfo {
        name: n(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind,
    }
}

fn family(
    env: &mut Environment,
    levels: &[&str],
    params: u32,
    name: &str,
    ty: Expr,
    ctors: Vec<(&str, Expr)>,
) {
    env.add_inductive_core(InductiveDecl {
        level_params: levels.iter().map(|l| n(l)).collect(),
        num_params: params,
        types: vec![InductiveType {
            name: n(name),
            type_: ty,
            constructors: ctors
                .into_iter()
                .map(|(c, t)| Constructor {
                    name: n(c),
                    type_: t,
                })
                .collect(),
        }],
    })
    .unwrap_or_else(|e| panic!("{name} must be admissible: {e}"));
}

/// `RC.True`/`RC.True.intro` and the empty `RC.False`, and NO `Eq`.
fn rc_env() -> Environment {
    let mut env = Environment::default();
    family(
        &mut env,
        &[],
        0,
        "RC.True",
        prop(),
        vec![("RC.True.intro", konst("RC.True"))],
    );
    family(&mut env, &[], 0, "RC.False", prop(), vec![]);
    env
}

/// `{α : Sort u} → α → α → Prop`
fn eq_type() -> Expr {
    Expr::pi(
        BinderInfo::Implicit,
        sort_u(),
        arrow(Expr::bvar(0), arrow(Expr::bvar(1), prop())),
    )
}

/// Lean's `Eq`: two parameters, one index, `Eq.refl : ∀ {α} (a : α), Eq a a`.
fn add_honest_eq(env: &mut Environment) {
    let eq_u = Expr::const_(n("Eq"), vec![Level::param(n("u"))]);
    family(
        env,
        &["u"],
        2,
        "Eq",
        eq_type(),
        vec![(
            "Eq.refl",
            Expr::pi(
                BinderInfo::Implicit,
                sort_u(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(0),
                    app(eq_u, [Expr::bvar(1), Expr::bvar(0), Expr::bvar(0)]),
                ),
            ),
        )],
    );
}

/// `r := fun _ _ => RC.True` over `RC.True`.
fn trivial_relation() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        konst("RC.True"),
        Expr::lam(BinderInfo::Default, konst("RC.True"), konst("RC.True")),
    )
}

/// `@Quot.sound.{0} RC.True r intro intro intro`, whose kernel-built type is
/// `@Eq.{0} (Quot r) (Quot.mk r intro) (Quot.mk r intro)`.
fn quot_sound_witness() -> Expr {
    let i = konst("RC.True.intro");
    app(
        Expr::const_(n("Quot.sound"), vec![Level::zero()]),
        [
            konst("RC.True"),
            trivial_relation(),
            i.clone(),
            i.clone(),
            i,
        ],
    )
}

/// Round-23 attack, form 1: `Eq` as a DEFINITION, `Eq a b := RC.False`.
/// `V.bad : RC.False := quot_sound_witness()` then type-checks by δ.
fn forged_eq_definition_env() -> Environment {
    let mut env = rc_env();
    let value = Expr::lam(
        BinderInfo::Implicit,
        sort_u(),
        Expr::lam(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::lam(BinderInfo::Default, Expr::bvar(1), konst("RC.False")),
        ),
    );
    let mut eq = decl("Eq", ConstantKind::Definition, eq_type(), Some(value));
    eq.level_params = vec![n("u")];
    import_structurally(&mut env, eq);
    env.init_quot();
    import_structurally(
        &mut env,
        decl(
            "V.bad",
            ConstantKind::Theorem,
            konst("RC.False"),
            Some(quot_sound_witness()),
        ),
    );
    env
}

/// Round-23 attack, form 2: `Eq` an inductive with NO constructor; the
/// `Quot.sound` witness is eliminated into `RC.False` through `Eq.rec`.
fn forged_empty_eq_env() -> Environment {
    let mut env = rc_env();
    family(&mut env, &["u"], 3, "Eq", eq_type(), vec![]);
    env.init_quot();
    let r = trivial_relation();
    let i = konst("RC.True.intro");
    let quot_ty = app(
        Expr::const_(n("Quot"), vec![Level::zero()]),
        [konst("RC.True"), r.clone()],
    );
    let mk = app(
        Expr::const_(n("Quot.mk"), vec![Level::zero()]),
        [konst("RC.True"), r, i],
    );
    let rec = env.get_recursor(&n("Eq.rec")).expect("Eq.rec").clone();
    let levels: Vec<Level> = rec.level_params.iter().map(|_| Level::zero()).collect();
    let eq_app = app(
        Expr::const_(n("Eq"), vec![Level::zero()]),
        [quot_ty.clone(), mk.clone(), mk.clone()],
    );
    let motive = Expr::lam(BinderInfo::Default, eq_app, konst("RC.False"));
    let head = app(
        Expr::const_(n("Eq.rec"), levels),
        [quot_ty, mk.clone(), mk, motive],
    );
    // No constructor, so no minor premise: the major follows the motive
    // whatever the recursor's argument order.
    let proof = app(head, [quot_sound_witness()]);
    import_structurally(
        &mut env,
        decl(
            "V.bad",
            ConstantKind::Theorem,
            konst("RC.False"),
            Some(proof),
        ),
    );
    env
}

fn options_with(bindings: ExtensionBindings) -> ClosedRecheckOptions {
    ClosedRecheckOptions {
        extension_bindings: bindings,
        ..ClosedRecheckOptions::default()
    }
}

fn quotient_refusal(refusals: &[ClosedRecheckRefusal]) -> Option<&str> {
    refusals.iter().find_map(|r| match r {
        ClosedRecheckRefusal::QuotientPrecondition { detail, .. } => Some(detail.as_str()),
        _ => None,
    })
}

fn binding_refusal_for<'a>(
    refusals: &'a [ClosedRecheckRefusal],
    name: &str,
) -> Option<&'a ClosedRecheckRefusal> {
    refusals.iter().find(
        |r| matches!(r, ClosedRecheckRefusal::ExtensionBindingMismatch { name: got, .. } if got == name),
    )
}

/// What the replay did before round 24, for the liveness half of each test:
/// install the quotient up front, then admit the cone. Reproduced here by
/// replaying under a table that binds the forged `Eq` into an environment
/// that already carries the quotient.
fn pre_fix_replay_accepts(env: &Environment, target: &str) -> bool {
    let mut replay = Environment::default();
    replay.init_quot();
    // Admit, in dependency order, exactly what the fixture declares.
    for fam in ["RC.True", "RC.False"] {
        let ind = env.get_inductive(&n(fam)).expect("family");
        let ctors = ind
            .constructor_names
            .iter()
            .map(|c| Constructor {
                name: c.clone(),
                type_: env.get_constructor(c).unwrap().type_.clone(),
            })
            .collect();
        replay
            .add_inductive_core(InductiveDecl {
                level_params: vec![],
                num_params: 0,
                types: vec![InductiveType {
                    name: n(fam),
                    type_: ind.type_.clone(),
                    constructors: ctors,
                }],
            })
            .unwrap();
    }
    if let Some(eq) = env.get_inductive(&n("Eq")) {
        replay
            .add_inductive_core(InductiveDecl {
                level_params: eq.level_params.clone(),
                num_params: eq.num_params,
                types: vec![InductiveType {
                    name: n("Eq"),
                    type_: eq.type_.clone(),
                    constructors: vec![],
                }],
            })
            .unwrap();
    } else {
        let eq = env.get_const(&n("Eq")).unwrap();
        replay
            .add_decl(clean_kernel::env::Declaration::Definition {
                name: n("Eq"),
                level_params: eq.level_params.clone(),
                type_: eq.type_.clone(),
                value: eq.value.clone().unwrap(),
                is_reducible: false,
            })
            .unwrap();
    }
    let bad = env.get_const(&n(target)).unwrap();
    replay
        .add_decl(clean_kernel::env::Declaration::Theorem {
            name: n(target),
            level_params: vec![],
            type_: bad.type_.clone(),
            value: bad.value.clone().unwrap(),
        })
        .is_ok()
}

// ─────────────────────────────────────────────────────────────────────────────
// Quotient over a forged `Eq`.
// ─────────────────────────────────────────────────────────────────────────────

/// Both round-23 forms PASSED the default replay at 0a515b8a9 ("CONDITIONAL
/// on 1 admitted axiom(s): Quot.sound"). They are now refused under the
/// pinned table, and — with `Eq`'s binding taken out of the picture by a
/// table derived from the forged environment — still refused, by the
/// quotient's own precondition.
#[test]
fn a_forged_eq_does_not_give_quot_sound_a_false_statement() {
    for (label, env) in [
        ("definition", forged_eq_definition_env()),
        ("empty inductive", forged_empty_eq_env()),
    ] {
        assert!(
            pre_fix_replay_accepts(&env, "V.bad"),
            "{label}: with the quotient installed before Eq, V.bad : RC.False is admitted — \
             if this stops holding, the fixture no longer exercises the fix"
        );

        let pinned = recheck_closed(&env, &targets(&["V.bad"]), &ClosedRecheckOptions::default());
        assert!(
            !pinned.report.passed(),
            "{label}: {}",
            pinned.report.verdict_sentence()
        );
        assert!(pinned.replayed.get_const(&n("V.bad")).is_none(), "{label}");
        assert!(!pinned.report.quotient_primitives_installed, "{label}");

        let unbound = recheck_closed(
            &env,
            &targets(&["V.bad"]),
            &options_with(ExtensionBindings::derive_from(&env, "test: forged Eq")),
        );
        assert!(
            !unbound.report.passed(),
            "{label}: {}",
            unbound.report.verdict_sentence()
        );
        let detail = quotient_refusal(&unbound.report.refusals).unwrap_or_else(|| {
            panic!(
                "{label}: no quotient refusal: {:?}",
                unbound.report.refusals
            )
        });
        assert!(detail.contains("cannot be installed"), "{label}: {detail}");
        assert!(unbound.replayed.get_const(&n("V.bad")).is_none(), "{label}");
        assert!(
            unbound.replayed.get_const(&n("Quot.sound")).is_none(),
            "{label}"
        );
    }
}

/// An honest `Eq` still lets a cone rest on `Quot.sound`, which is installed
/// after it and counted as an axiom.
#[test]
fn an_honest_eq_still_admits_the_quotient() {
    let mut env = rc_env();
    add_honest_eq(&mut env);
    env.init_quot();
    let sound = env.get_const(&n("Quot.sound")).unwrap().clone();
    let mut uses = decl(
        "V.uses_sound",
        ConstantKind::Theorem,
        sound.type_.clone(),
        Some(Expr::const_(
            n("Quot.sound"),
            sound
                .level_params
                .iter()
                .cloned()
                .map(Level::param)
                .collect::<Vec<_>>(),
        )),
    );
    uses.level_params = sound.level_params.clone();
    import_structurally(&mut env, uses);
    let run = recheck_closed(
        &env,
        &targets(&["V.uses_sound"]),
        &options_with(ExtensionBindings::derive_from(&env, "test: honest Eq")),
    );
    assert!(run.report.passed(), "{:?}", run.report.refusals);
    assert!(run.report.quotient_primitives_installed);
    assert_eq!(run.report.axioms_admitted, vec!["Quot.sound".to_string()]);
    // The pinned table does not bind this hand-built `Eq` (it is not Lean's
    // bytes), so the default replay refuses it at `Eq`, before the quotient.
    let pinned = recheck_closed(
        &env,
        &targets(&["V.uses_sound"]),
        &ClosedRecheckOptions::default(),
    );
    assert!(
        binding_refusal_for(&pinned.report.refusals, "Eq").is_some(),
        "{:?}",
        pinned.report.refusals
    );
    assert!(!pinned.report.quotient_primitives_installed);
}

/// A cone may not supply a quotient primitive of its own: a family that
/// carries a quotient name is refused, and so is a replay that was told not
/// to provide the primitives.
#[test]
fn quotient_names_are_never_admitted_from_the_cone() {
    let mut env = rc_env();
    add_honest_eq(&mut env);
    // `inductive Quot : Prop | mk : Quot` — a family squatting on the names.
    family(
        &mut env,
        &[],
        0,
        "Quot",
        prop(),
        vec![("Quot.mk", konst("Quot"))],
    );
    import_structurally(
        &mut env,
        decl(
            "V.q",
            ConstantKind::Theorem,
            konst("Quot"),
            Some(konst("Quot.mk")),
        ),
    );
    let run = recheck_closed(
        &env,
        &targets(&["V.q"]),
        &options_with(ExtensionBindings::derive_from(&env, "test")),
    );
    let detail = quotient_refusal(&run.report.refusals).expect("quotient refusal");
    assert!(detail.contains("kernel-reserved quotient name"), "{detail}");
    assert!(run.replayed.get_const(&n("V.q")).is_none());

    let mut env = rc_env();
    add_honest_eq(&mut env);
    env.init_quot();
    let mk_ty = env.get_const(&n("Quot.mk")).unwrap().clone();
    let mut uses = decl(
        "V.mk",
        ConstantKind::Definition,
        mk_ty.type_.clone(),
        Some(Expr::const_(n("Quot.mk"), vec![Level::param(n("u"))])),
    );
    uses.level_params = vec![n("u")];
    import_structurally(&mut env, uses);
    let off = recheck_closed(
        &env,
        &targets(&["V.mk"]),
        &ClosedRecheckOptions {
            install_quotient_primitives: false,
            extension_bindings: ExtensionBindings::derive_from(&env, "test"),
            ..ClosedRecheckOptions::default()
        },
    );
    assert!(
        quotient_refusal(&off.report.refusals).is_some(),
        "{:?}",
        off.report.refusals
    );
    assert!(!off.report.quotient_primitives_installed);
}

// ─────────────────────────────────────────────────────────────────────────────
// By-name stripping of `outParam` / `optParam` / `autoParam` / `semiOutParam`.
// ─────────────────────────────────────────────────────────────────────────────

/// Forged `outParam.{u} (α : Sort u) : Sort u := α → α`.
fn forged_out_param() -> ConstantInfo {
    let value = Expr::lam(
        BinderInfo::Default,
        sort_u(),
        arrow(Expr::bvar(0), Expr::bvar(1)),
    );
    let mut out = decl(
        "outParam",
        ConstantKind::Definition,
        arrow(sort_u(), sort_u()),
        Some(value),
    );
    out.level_params = vec![n("u")];
    out.is_reducible = true;
    out.reducibility = Reducibility::Reducible;
    out
}

/// `Box : Prop`, `Box.mk : outParam RC.False → Box`, over the forged
/// `outParam`: `add_inductive_core` would generate `Box.rec` with the minor
/// premise over `(x : RC.False)` — `outParam` stripped BY NAME — while
/// `Box.mk` takes an `RC.False → RC.False`. Measured: the kernel's own
/// subject-reduction check on the generated ι-rule refuses the family, so this
/// FIELD-level forgery is not a false accept today. The by-name stripping is
/// nonetheless a by-name meaning, and the replay now gates it at its root.
#[test]
fn a_forged_out_param_field_is_refused_by_the_kernel_rule_check() {
    let mut env = rc_env();
    import_structurally(&mut env, forged_out_param());
    let field = app(
        Expr::const_(n("outParam"), vec![Level::zero()]),
        [konst("RC.False")],
    );
    let err = env
        .add_inductive_core(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: n("Box"),
                type_: prop(),
                constructors: vec![Constructor {
                    name: n("Box.mk"),
                    type_: arrow(field, konst("Box")),
                }],
            }],
        })
        .expect_err("the generated rule is ill-typed");
    assert!(
        err.to_string().contains("violates subject reduction"),
        "{err}"
    );
}

/// A cone that declares its own `outParam` (or any of the four annotation
/// names) is refused at that declaration under the pinned table, before any
/// family is generated over it; under a table derived from the cone itself
/// (no gate) the same cone passes.
#[test]
fn a_forged_type_annotation_is_refused_at_its_binding() {
    let mut env = rc_env();
    import_structurally(&mut env, forged_out_param());
    let use_ty = app(
        Expr::const_(n("outParam"), vec![Level::zero()]),
        [konst("RC.False")],
    );
    let id = Expr::lam(BinderInfo::Default, konst("RC.False"), Expr::bvar(0));
    import_structurally(
        &mut env,
        decl("V.uses", ConstantKind::Definition, use_ty, Some(id)),
    );

    let ungated = recheck_closed(
        &env,
        &targets(&["V.uses"]),
        &options_with(ExtensionBindings::derive_from(
            &env,
            "test: derived from the forged env",
        )),
    );
    assert!(ungated.report.passed(), "{:?}", ungated.report.refusals);

    let run = recheck_closed(
        &env,
        &targets(&["V.uses"]),
        &ClosedRecheckOptions::default(),
    );
    assert!(
        binding_refusal_for(&run.report.refusals, "outParam").is_some(),
        "{:?}",
        run.report.refusals
    );
    assert!(run.replayed.get_const(&n("outParam")).is_none());
    assert!(run.replayed.get_const(&n("V.uses")).is_none());
}
