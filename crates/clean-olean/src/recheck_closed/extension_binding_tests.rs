// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Attack battery: a name the kernel reduces BY NAME, given a forged meaning.
//!
//! The kernel evaluates some constants by their name alone — `Nat.add` on two
//! literals is computed with bignum arithmetic, never by unfolding the
//! declaration that carries that name. An imported cone that supplies its own
//! declaration for such a name therefore gets two meanings for one constant:
//! the forged one (by δ) and the built-in one (by name). Two meanings are
//! enough to prove `False`, and every constant in the proof is re-admitted by
//! `add_decl` without complaint, because each step IS well-typed under a
//! kernel that believes both.
//!
//! Every attack below proves a closed inhabitant of an empty inductive
//! (`RC.False`) and must be refused by the default dependency-closed replay.

use super::super::{recheck_closed, ClosedRecheckOptions, ClosedRecheckRefusal};
use super::{ExtensionBindings, EXTENSION_KEYS};
use clean_kernel::env::{
    ConstantInfo, ConstantKind, Environment, Reducibility, TrustedEnvExt as _,
};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType, RecursorArgOrder};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use std::collections::BTreeSet;

fn n(s: &str) -> Name {
    Name::interned(s)
}

fn konst(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn one() -> Level {
    Level::succ(Level::zero())
}

fn type0() -> Expr {
    Expr::sort(one())
}

fn prop() -> Expr {
    Expr::sort(Level::zero())
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

fn definition(name: &str, type_: Expr, value: Expr) -> ConstantInfo {
    decl(name, ConstantKind::Definition, type_, Some(value))
}

fn theorem(name: &str, type_: Expr, value: Expr) -> ConstantInfo {
    decl(name, ConstantKind::Theorem, type_, Some(value))
}

fn add_family(env: &mut Environment, name: &str, ty: Expr, ctors: Vec<(&str, Expr)>) {
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
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

/// `Eq.{u}`, `RC.True`/`RC.True.intro`, `RC.False` (no constructors), and —
/// through the same `add_inductive_core` path the import uses — `Nat` exactly
/// as Lean declares it and `Bool` exactly as Lean declares it.
///
/// `extra_nat_ctor` adds a third `Nat` constructor: a forged `Nat` family.
fn base_env(extra_nat_ctor: bool) -> Environment {
    let mut env = Environment::default();
    let u = Level::param(n("u"));
    let eq_u = Expr::const_(n("Eq"), vec![u.clone()]);
    env.add_inductive_core(InductiveDecl {
        level_params: vec![n("u")],
        num_params: 2,
        types: vec![InductiveType {
            name: n("Eq"),
            type_: Expr::pi(
                BinderInfo::Implicit,
                Expr::sort(u.clone()),
                arrow(Expr::bvar(0), arrow(Expr::bvar(1), prop())),
            ),
            constructors: vec![Constructor {
                name: n("Eq.refl"),
                type_: Expr::pi(
                    BinderInfo::Implicit,
                    Expr::sort(u),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(0),
                        app(eq_u, [Expr::bvar(1), Expr::bvar(0), Expr::bvar(0)]),
                    ),
                ),
            }],
        }],
    })
    .expect("Eq must be admissible");
    add_family(
        &mut env,
        "RC.True",
        prop(),
        vec![("RC.True.intro", konst("RC.True"))],
    );
    add_family(&mut env, "RC.False", prop(), vec![]);
    let mut nat_ctors = vec![
        ("Nat.zero", konst("Nat")),
        ("Nat.succ", arrow(konst("Nat"), konst("Nat"))),
    ];
    if extra_nat_ctor {
        nat_ctors.push(("Nat.forged", konst("Nat")));
    }
    add_family(&mut env, "Nat", type0(), nat_ctors);
    add_family(
        &mut env,
        "Bool",
        type0(),
        vec![("Bool.false", konst("Bool")), ("Bool.true", konst("Bool"))],
    );
    env
}

/// `rec.{levels} motive minors… major`, honouring the recursor's own order.
fn rec_app(env: &Environment, rec: &str, motive: Expr, minors: Vec<Expr>, major: Expr) -> Expr {
    let info = env.get_recursor(&n(rec)).expect("recursor exists");
    let levels: Vec<Level> = info.level_params.iter().map(|_| one()).collect();
    let head = app(Expr::const_(info.name.clone(), levels), [motive]);
    match info.arg_order {
        RecursorArgOrder::MajorAfterMinors => app(app(head, minors), [major]),
        RecursorArgOrder::MajorAfterMotive => app(app(head, [major]), minors),
    }
}

/// `@Eq.{1} α a b`.
fn eq_at(ty: Expr, a: Expr, b: Expr) -> Expr {
    app(Expr::const_(n("Eq"), vec![one()]), [ty, a, b])
}

fn refl_at(ty: Expr, a: Expr) -> Expr {
    app(Expr::const_(n("Eq.refl"), vec![one()]), [ty, a])
}

/// Transport along `h : a = b` in `ty`: from `minor : P a` to `P b`, where
/// `P x := motive_body[x]`. `Eq.rec`'s universe for the motive is `0` (the
/// motive lands in `Prop`) and the `Eq` universe is `1`.
fn transport(
    env: &Environment,
    ty: Expr,
    a: Expr,
    p: impl Fn(Expr) -> Expr,
    minor: Expr,
    b: Expr,
    h: Expr,
) -> Expr {
    let info = env.get_recursor(&n("Eq.rec")).expect("Eq.rec");
    let levels: Vec<Level> = info
        .level_params
        .iter()
        .map(|p| if *p == n("u") { one() } else { Level::zero() })
        .collect();
    let motive = Expr::lam(
        BinderInfo::Default,
        ty.clone(),
        Expr::lam(
            BinderInfo::Default,
            eq_at(ty.clone(), a.clone(), Expr::bvar(0)),
            p(Expr::bvar(1)),
        ),
    );
    let head = app(Expr::const_(n("Eq.rec"), levels), [ty, a, motive]);
    match info.arg_order {
        RecursorArgOrder::MajorAfterMinors => app(head, [minor, b, h]),
        RecursorArgOrder::MajorAfterMotive => app(head, [b, h, minor]),
    }
}

fn nat2() -> Expr {
    arrow(konst("Nat"), arrow(konst("Nat"), konst("Nat")))
}

/// Honest `Nat.add` by structural recursion on the second argument:
/// `fun a b => Nat.rec a (fun _ ih => Nat.succ ih) b`.
fn honest_nat_add(env: &Environment) -> Expr {
    let motive = Expr::lam(BinderInfo::Default, konst("Nat"), konst("Nat"));
    let step = Expr::lam(
        BinderInfo::Default,
        konst("Nat"),
        Expr::lam(
            BinderInfo::Default,
            konst("Nat"),
            Expr::app(konst("Nat.succ"), Expr::bvar(0)),
        ),
    );
    Expr::lam(
        BinderInfo::Default,
        konst("Nat"),
        Expr::lam(
            BinderInfo::Default,
            konst("Nat"),
            rec_app(
                env,
                "Nat.rec",
                motive,
                vec![Expr::bvar(1), step],
                Expr::bvar(0),
            ),
        ),
    )
}

/// Forged `Nat.add := fun a b => a`.
fn forged_nat_add() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        konst("Nat"),
        Expr::lam(BinderInfo::Default, konst("Nat"), Expr::bvar(1)),
    )
}

/// `P n := Nat.rec RC.True (fun k _ => Nat.rec RC.False (fun _ _ => RC.True) k) n`:
/// `P 0 = True`, `P 1 = False`, `P 2 = True`.
fn parity_motive(env: &Environment, x: Expr) -> Expr {
    let to_prop = Expr::lam(BinderInfo::Default, konst("Nat"), prop());
    let inner = |k: Expr| {
        rec_app(
            env,
            "Nat.rec",
            to_prop.clone(),
            vec![
                konst("RC.False"),
                Expr::lam(
                    BinderInfo::Default,
                    konst("Nat"),
                    Expr::lam(BinderInfo::Default, prop(), konst("RC.True")),
                ),
            ],
            k,
        )
    };
    rec_app(
        env,
        "Nat.rec",
        to_prop.clone(),
        vec![
            konst("RC.True"),
            Expr::lam(
                BinderInfo::Default,
                konst("Nat"),
                Expr::lam(BinderInfo::Default, prop(), inner(Expr::bvar(1))),
            ),
        ],
        x,
    )
}

/// The `Nat.add` attack. `V.T1 : ∀ a b, Nat.add a b = a` holds by unfolding
/// the forged definition; `V.bad : RC.False` transports `P (Nat.add 1 1)` —
/// which the kernel's by-name `Nat.add` evaluates to `P 2 = RC.True` — along
/// `V.T1 1 1` to `P 1 = RC.False`.
///
/// `helper` routes the forged meaning through a separate constant so that
/// `Nat.add`'s OWN bytes are exactly the honest ones: `Nat.add := fun a b =>
/// V.helper a b`, with `V.helper` forged.
fn nat_add_attack_env(helper: bool) -> Environment {
    let mut env = base_env(false);
    if helper {
        import_structurally(&mut env, definition("V.helper", nat2(), forged_nat_add()));
        let via_helper = Expr::lam(
            BinderInfo::Default,
            konst("Nat"),
            Expr::lam(
                BinderInfo::Default,
                konst("Nat"),
                app(konst("V.helper"), [Expr::bvar(1), Expr::bvar(0)]),
            ),
        );
        import_structurally(&mut env, definition("Nat.add", nat2(), via_helper));
    } else {
        import_structurally(&mut env, definition("Nat.add", nat2(), forged_nat_add()));
    }
    let add = |a: Expr, b: Expr| app(konst("Nat.add"), [a, b]);
    import_structurally(
        &mut env,
        theorem(
            "V.T1",
            Expr::pi(
                BinderInfo::Default,
                konst("Nat"),
                Expr::pi(
                    BinderInfo::Default,
                    konst("Nat"),
                    eq_at(
                        konst("Nat"),
                        add(Expr::bvar(1), Expr::bvar(0)),
                        Expr::bvar(1),
                    ),
                ),
            ),
            Expr::lam(
                BinderInfo::Default,
                konst("Nat"),
                Expr::lam(
                    BinderInfo::Default,
                    konst("Nat"),
                    refl_at(konst("Nat"), Expr::bvar(1)),
                ),
            ),
        ),
    );
    let lit = |k: u64| Expr::nat_lit(k);
    let a = add(lit(1), lit(1));
    let proof = transport(
        &env,
        konst("Nat"),
        a,
        |x| parity_motive(&env, x),
        konst("RC.True.intro"),
        lit(1),
        app(konst("V.T1"), [lit(1), lit(1)]),
    );
    import_structurally(&mut env, theorem("V.bad", konst("RC.False"), proof));
    env
}

/// An honest environment for the SAME names: the table a correct `Nat.add`
/// binds to. Used only to show the gate compares against a table that is not
/// derived from the environment under test.
fn honest_nat_env() -> Environment {
    let mut env = base_env(false);
    let add = honest_nat_add(&env);
    import_structurally(&mut env, definition("Nat.add", nat2(), add));
    // `V.two : Nat.add 1 1 = 2 := rfl` — true, and needs the by-name evaluation
    // or the honest δι unfolding to agree.
    import_structurally(
        &mut env,
        theorem(
            "V.two",
            eq_at(
                konst("Nat"),
                app(konst("Nat.add"), [Expr::nat_lit(1), Expr::nat_lit(1)]),
                Expr::nat_lit(2),
            ),
            refl_at(konst("Nat"), Expr::nat_lit(2)),
        ),
    );
    env
}

/// `text` up to its first `#[cfg(test)] mod <ident> {`, if any.
fn strip_inline_test_module(text: &str) -> &str {
    let mut from = 0;
    while let Some(at) = text[from..].find("#[cfg(test)]") {
        let start = from + at;
        let rest = text[start + "#[cfg(test)]".len()..].trim_start();
        if let Some(after_mod) = rest.strip_prefix("mod ") {
            let ident_end = after_mod
                .find(|c: char| !(c.is_alphanumeric() || c == '_'))
                .unwrap_or(after_mod.len());
            if after_mod[ident_end..].trim_start().starts_with('{') {
                return &text[..start];
            }
        }
        from = start + 1;
    }
    text
}

/// The first binding refusal for any of `names`. The attack cones below
/// declare `Nat` too, and which of `Nat` / `Nat.add` is refused first depends
/// on whether the table in force binds this fixture's `Nat` family; either is
/// the gate refusing the forged meaning at its root.
fn binding_refusal_among<'a>(
    refusals: &'a [ClosedRecheckRefusal],
    names: &[&str],
) -> Option<&'a ClosedRecheckRefusal> {
    names
        .iter()
        .find_map(|name| binding_refusal_for(refusals, name))
}

fn binding_refusal_for<'a>(
    refusals: &'a [ClosedRecheckRefusal],
    name: &str,
) -> Option<&'a ClosedRecheckRefusal> {
    refusals
        .iter()
        .find(|r| matches!(r, ClosedRecheckRefusal::ExtensionBindingMismatch { name: got, .. } if got == name))
}

// ─────────────────────────────────────────────────────────────────────────────
// Attacks through the DEFAULT options. Each of these PASSED before 2026-09-24.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn a_forged_nat_add_does_not_prove_false_through_the_default_replay() {
    let env = nat_add_attack_env(false);
    let run = recheck_closed(&env, &targets(&["V.bad"]), &ClosedRecheckOptions::default());
    assert!(
        !run.report.passed(),
        "a closed proof of RC.False from a forged `Nat.add` must be refused: {}",
        run.report.verdict_sentence()
    );
    assert!(
        run.replayed.get_const(&n("V.bad")).is_none(),
        "V.bad must not be admitted"
    );
    assert!(
        binding_refusal_among(&run.report.refusals, &["Nat", "Nat.add"]).is_some(),
        "the refusal must name the forged binding itself: {:?}",
        run.report.refusals
    );
}

#[test]
fn a_forged_dependency_behind_honest_nat_add_bytes_is_refused() {
    // `Nat.add`'s own bytes are honest-shaped; the forgery is one constant
    // deeper. A table keyed on the declaration's own bytes would miss it.
    let env = nat_add_attack_env(true);
    let run = recheck_closed(&env, &targets(&["V.bad"]), &ClosedRecheckOptions::default());
    assert!(!run.report.passed(), "{}", run.report.verdict_sentence());
    assert!(run.replayed.get_const(&n("V.bad")).is_none());
    assert!(binding_refusal_among(&run.report.refusals, &["Nat", "Nat.add"]).is_some());
}

/// The verifier's attack (round 22): `Bool.not := fun b => b` against the
/// native `Bool.not` reducer. The native-reducer table is Clean's own
/// accelerator set, keyed by name and never tied to a definition, and it is no
/// longer installed in the replay environment at all.
#[test]
fn a_forged_bool_not_does_not_prove_false_through_the_default_replay() {
    let mut env = base_env(false);
    import_structurally(
        &mut env,
        definition(
            "Bool.not",
            arrow(konst("Bool"), konst("Bool")),
            Expr::lam(BinderInfo::Default, konst("Bool"), Expr::bvar(0)),
        ),
    );
    let not = |e: Expr| Expr::app(konst("Bool.not"), e);
    import_structurally(
        &mut env,
        theorem(
            "V.T1",
            Expr::pi(
                BinderInfo::Default,
                konst("Bool"),
                eq_at(konst("Bool"), not(Expr::bvar(0)), Expr::bvar(0)),
            ),
            Expr::lam(
                BinderInfo::Default,
                konst("Bool"),
                refl_at(konst("Bool"), Expr::bvar(0)),
            ),
        ),
    );
    // P x := Bool.rec RC.True RC.False x   (false ↦ True, true ↦ False)
    let p = |x: Expr| {
        rec_app(
            &env,
            "Bool.rec",
            Expr::lam(BinderInfo::Default, konst("Bool"), prop()),
            vec![konst("RC.True"), konst("RC.False")],
            x,
        )
    };
    let proof = transport(
        &env,
        konst("Bool"),
        not(konst("Bool.true")),
        p,
        konst("RC.True.intro"),
        konst("Bool.true"),
        app(konst("V.T1"), [konst("Bool.true")]),
    );
    import_structurally(&mut env, theorem("V.bad", konst("RC.False"), proof));

    let run = recheck_closed(&env, &targets(&["V.bad"]), &ClosedRecheckOptions::default());
    assert!(!run.report.passed(), "{}", run.report.verdict_sentence());
    assert!(run.replayed.get_const(&n("V.bad")).is_none());
    assert!(
        run.replayed.get_native_reducer(&n("Bool.not")).is_none(),
        "the replay environment must carry no by-name native reducer"
    );
}

#[test]
fn a_forged_nat_family_is_refused_as_an_extension_binding() {
    // A third constructor: literals are still typed `Nat`, and the kernel
    // still treats every literal as `zero`/`succ`, so the family's shape is
    // part of what the by-name arithmetic assumes.
    let env = base_env(true);
    let mut env = env;
    import_structurally(
        &mut env,
        definition("V.uses_nat", konst("Nat"), konst("Nat.forged")),
    );
    let run = recheck_closed(
        &env,
        &targets(&["V.uses_nat"]),
        &ClosedRecheckOptions::default(),
    );
    assert!(!run.report.passed());
    assert!(
        binding_refusal_for(&run.report.refusals, "Nat").is_some(),
        "{:?}",
        run.report.refusals
    );
}

/// A cone resting on an axiom `: RC.False` is re-admitted (an axiom is an
/// assumption, not a derivation), so it PASSES — and the pass sentence must
/// then say, in the sentence itself, that it rests on that axiom.
#[test]
fn a_pass_over_an_axiom_names_the_axiom_in_its_verdict_sentence() {
    let mut env = base_env(false);
    import_structurally(
        &mut env,
        decl("V.ax", ConstantKind::Axiom, konst("RC.False"), None),
    );
    import_structurally(
        &mut env,
        theorem("V.uses_ax", konst("RC.False"), konst("V.ax")),
    );
    let run = recheck_closed(
        &env,
        &targets(&["V.uses_ax"]),
        &ClosedRecheckOptions::default(),
    );
    assert!(run.report.passed());
    assert_eq!(run.report.axioms_admitted, vec!["V.ax".to_string()]);
    let sentence = run.report.verdict_sentence();
    assert!(
        sentence.contains("V.ax"),
        "the sentence must name the axiom: {sentence}"
    );
    assert!(
        sentence.contains("CONDITIONAL"),
        "a pass over an axiom is conditional on it, and must say so: {sentence}"
    );
}

/// `Quot.sound` enters the replay through the kernel's own `init_quot`, not
/// `add_decl`, so it used to be missing from `axioms_admitted` even when the
/// cone rested on it. Lean's `#print axioms` lists it; so must the report.
#[test]
fn a_cone_through_quot_sound_lists_it_as_an_axiom() {
    use clean_kernel::env::TrustedEnvExt as _;
    let mut env = base_env(false);
    env.init_quot();
    let sound = env
        .get_const(&n("Quot.sound"))
        .expect("init_quot installs Quot.sound")
        .clone();
    let levels: Vec<Level> = sound
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let mut uses = definition(
        "V.uses_sound",
        sound.type_.clone(),
        Expr::const_(n("Quot.sound"), levels),
    );
    uses.kind = ConstantKind::Theorem;
    uses.level_params = sound.level_params.clone();
    import_structurally(&mut env, uses);
    // This fixture's hand-built `Eq` is not Lean's bytes, so the pinned table
    // refuses it (as it must: `Eq` is now gated); bind it to itself to test the
    // axiom accounting, which is what this test is about.
    let run = recheck_closed(
        &env,
        &targets(&["V.uses_sound"]),
        &ClosedRecheckOptions {
            extension_bindings: ExtensionBindings::derive_from(&env, "test: honest Eq"),
            ..ClosedRecheckOptions::default()
        },
    );
    assert!(run.report.passed(), "{:?}", run.report.refusals);
    assert!(
        run.report
            .axioms_admitted
            .contains(&"Quot.sound".to_string()),
        "{:?}",
        run.report.axioms_admitted
    );
    for primitive in ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] {
        assert!(!run.report.axioms_admitted.contains(&primitive.to_string()));
    }
    assert!(run.report.verdict_sentence().contains("Quot.sound"));
}

#[test]
fn a_pass_with_no_axioms_says_so() {
    let mut env = base_env(false);
    import_structurally(&mut env, definition("V.t", prop(), konst("RC.True")));
    let run = recheck_closed(&env, &targets(&["V.t"]), &ClosedRecheckOptions::default());
    assert!(run.report.passed(), "{:?}", run.report.refusals);
    assert!(run.report.verdict_sentence().contains("no axioms"));
}

// ─────────────────────────────────────────────────────────────────────────────
// The gate itself.
// ─────────────────────────────────────────────────────────────────────────────

/// The same true theorem is admitted under a table that binds this `Nat.add`,
/// and refused — fail-closed, naming the binding — under the pinned Lean table,
/// which this hand-built `Nat.add` is not.
#[test]
fn a_true_theorem_passes_only_under_a_table_that_binds_its_nat_add() {
    let env = honest_nat_env();
    let honest = ExtensionBindings::derive_from(&env, "test: honest Nat.add");
    let bound = recheck_closed(
        &env,
        &targets(&["V.two"]),
        &ClosedRecheckOptions {
            extension_bindings: honest,
            ..ClosedRecheckOptions::default()
        },
    );
    assert!(bound.report.passed(), "{:?}", bound.report.refusals);
    assert!(!bound.report.extension_bindings_pinned);

    let pinned = recheck_closed(&env, &targets(&["V.two"]), &ClosedRecheckOptions::default());
    assert!(pinned.report.extension_bindings_pinned);
    assert!(!pinned.report.passed());
    assert!(binding_refusal_among(&pinned.report.refusals, &["Nat", "Nat.add"]).is_some());
}

/// Under the honest table, the forged `Nat.add` — directly or through a helper
/// — is refused by name. Under a table derived from the FORGED environment
/// (which is what "no gate" amounts to) the proof of `RC.False` went through
/// before the kernel's native-fold authority existed (the pre-fix witness
/// that the attack is real). Since `env/native_fold_authority.rs` (merged
/// from clean main), `reduce_nat` folds `Nat.add` only for a constant whose
/// δ-closure digest is canonical, so the forged one is not folded and
/// `V.bad` is refused as a type mismatch even with no binding: the attack is
/// stopped twice, by the binding (name → fingerprint) and by the authority
/// (content), and this test pins both refusals.
#[test]
fn the_gate_is_what_stops_the_nat_add_attack() {
    let honest = ExtensionBindings::derive_from(&honest_nat_env(), "test: honest Nat.add");
    for helper in [false, true] {
        let env = nat_add_attack_env(helper);
        let gated = recheck_closed(
            &env,
            &targets(&["V.bad"]),
            &ClosedRecheckOptions {
                extension_bindings: honest.clone(),
                ..ClosedRecheckOptions::default()
            },
        );
        assert!(!gated.report.passed(), "helper={helper}");
        assert!(
            binding_refusal_for(&gated.report.refusals, "Nat.add").is_some(),
            "helper={helper}"
        );

        let vacuous = ExtensionBindings::derive_from(&env, "test: derived from the forged env");
        let ungated = recheck_closed(
            &env,
            &targets(&["V.bad"]),
            &ClosedRecheckOptions {
                extension_bindings: vacuous,
                ..ClosedRecheckOptions::default()
            },
        );
        assert!(
            !ungated.report.passed(),
            "helper={helper}: with no binding the native-fold authority must still refuse \
             the forged Nat.add's fold: {:?}",
            ungated.report.refusals
        );
        assert!(
            binding_refusal_for(&ungated.report.refusals, "Nat.add").is_none(),
            "helper={helper}: the derived table binds nothing, so the refusal is the \
             authority's, not the gate's: {:?}",
            ungated.report.refusals
        );
        assert!(ungated.replayed.get_const(&n("V.bad")).is_none());
    }
}

/// A table derived from the environment under test binds nothing; a PASS under
/// it must not promote a single trust-ledger origin.
#[test]
fn a_derived_table_never_promotes_an_origin() {
    let mut env = honest_nat_env();
    let derived = ExtensionBindings::derive_from(&env, "test: derived");
    let run = recheck_closed(
        &env,
        &targets(&["V.two"]),
        &ClosedRecheckOptions {
            extension_bindings: derived,
            ..ClosedRecheckOptions::default()
        },
    );
    assert!(run.report.passed());
    assert_eq!(
        super::super::promote_origins_after_closed_recheck(&mut env, &run),
        0
    );
}

/// Each reviewed world binds exactly the keys its closure declares (for the
/// import-mode world: the keys its `Init` adds on top of the prelude), every
/// row is an extension key, no world pins one key twice, and the pinned table
/// binds exactly the union of the worlds' names.
#[test]
fn the_pinned_table_names_every_extension_key_it_binds_and_nothing_else() {
    use super::super::extension_binding_pins::PINNED_WORLDS;
    let pinned = ExtensionBindings::pinned();
    assert!(pinned.is_pinned());
    let keys: BTreeSet<Name> = EXTENSION_KEYS
        .iter()
        .map(|k| Name::from_string(k.name))
        .collect();
    let world = |label: &str| {
        PINNED_WORLDS
            .iter()
            .find(|w| w.label == label)
            .unwrap_or_else(|| panic!("no pinned world {label}"))
    };
    let mut union: BTreeSet<Name> = BTreeSet::new();
    for w in PINNED_WORLDS {
        let names: BTreeSet<Name> = w.rows.iter().map(|(n, _)| Name::from_string(n)).collect();
        assert_eq!(names.len(), w.rows.len(), "{}: a key pinned twice", w.label);
        for (name, hex) in w.rows {
            assert!(
                keys.contains(&Name::from_string(name)),
                "{}: {name} is pinned but is not an extension key",
                w.label
            );
            assert!(
                hex.len() == 64 && hex.bytes().all(|b| b.is_ascii_hexdigit()),
                "{}: {name}'s row is not a fingerprint",
                w.label
            );
        }
        union.extend(names);
    }
    assert_eq!(
        pinned.bound_names().cloned().collect::<BTreeSet<_>>(),
        union
    );

    // Lean v4.8.0 declares 40 of the keys; `String.ofList` is not one of them.
    let v4_8 = world("lean-v4.8.0-core");
    assert_eq!(v4_8.rows.len(), 40);
    assert_eq!(v4_8.rows.len(), EXTENSION_KEYS.len() - 1);
    assert!(!v4_8.rows.iter().any(|(n, _)| *n == "String.ofList"));
    // Lean v4.30.0-rc2 declares every key, `String.ofList` included.
    let v4_30 = world("lean-v4.30.0-rc2-core");
    assert_eq!(v4_30.rows.len(), EXTENSION_KEYS.len());
    // Over the import-mode prelude, the keys the prelude itself declares are
    // the base's, never a row: 27 of the 41 come from v4.30's `Init`,
    // including the four bitwise operations no longer seeded as base axioms.
    let mixed = world("clean-import+lean-v4.30.0-rc2-core");
    assert_eq!(mixed.rows.len(), 27);
    let base = Environment::try_with_prelude_for_import().expect("import-mode prelude");
    for (name, _) in mixed.rows {
        assert!(
            !super::declares(&base, &Name::from_string(name)),
            "{name} is the import-mode prelude's own declaration; the gate takes it as given"
        );
    }
}

/// A key binds to ANY reviewed world's row and to nothing else: two honest
/// `Nat.add`s of different shape both bind under the union of their tables,
/// the forged one binds under neither, and the refusal names both rows.
#[test]
fn a_key_binds_to_any_world_row_and_to_nothing_else() {
    let honest = ExtensionBindings::derive_from(&honest_nat_env(), "test: rec-shaped Nat.add");
    let mut other = base_env(false);
    // `fun a b => Nat.rec a (fun _ => Nat.succ) b`: the step eta-reduced, a
    // different term for the same function.
    let motive = Expr::lam(BinderInfo::Default, konst("Nat"), konst("Nat"));
    let step = Expr::lam(BinderInfo::Default, konst("Nat"), konst("Nat.succ"));
    let add = Expr::lam(
        BinderInfo::Default,
        konst("Nat"),
        Expr::lam(
            BinderInfo::Default,
            konst("Nat"),
            rec_app(
                &other,
                "Nat.rec",
                motive,
                vec![Expr::bvar(1), step],
                Expr::bvar(0),
            ),
        ),
    );
    import_structurally(&mut other, definition("Nat.add", nat2(), add));
    let eta = ExtensionBindings::derive_from(&other, "test: eta-shaped Nat.add");
    let union = ExtensionBindings::union("test: both worlds", &[&honest, &eta]);
    assert!(!union.is_pinned());

    let fingerprint = |env: &Environment| {
        super::super::fingerprint::Fingerprinter::new(env).constant(&n("Nat.add"))
    };
    let (a, b) = (fingerprint(&honest_nat_env()), fingerprint(&other));
    assert_ne!(a, b, "the two honest shapes must be two different rows");
    for (label, found) in [("rec-shaped", a), ("eta-shaped", b)] {
        assert!(
            matches!(
                super::check_binding(&union, &n("Nat.add"), &found),
                super::BindingVerdict::Bound
            ),
            "{label} Nat.add must bind under the union"
        );
    }
    let forged = fingerprint(&nat_add_attack_env(false));
    match super::check_binding(&union, &n("Nat.add"), &forged) {
        super::BindingVerdict::Bound => panic!("a forged Nat.add bound under the union"),
        super::BindingVerdict::Mismatch { expected, .. } => {
            let expected = expected.expect("the union pins Nat.add");
            assert!(
                expected.contains("rec-shaped") && expected.contains("eta-shaped"),
                "the refusal must name every row it compared against: {expected}"
            );
        }
    }
    // Neither part alone binds the other part's row.
    assert!(matches!(
        super::check_binding(&honest, &n("Nat.add"), &b),
        super::BindingVerdict::Mismatch { .. }
    ));
    assert!(matches!(
        super::check_binding(&eta, &n("Nat.add"), &a),
        super::BindingVerdict::Mismatch { .. }
    ));
}

/// Every name a type-checker hook matches by name must be classified: either
/// it is gated here, or it is listed with the reason it cannot fire in the
/// replay environment. A new by-name hook in `tc/` fails this test until
/// someone decides which.
#[test]
fn every_by_name_hook_in_the_type_checker_is_gated_or_explained() {
    let tc = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-kernel/src/tc");
    let mut names: BTreeSet<String> = BTreeSet::new();
    let mut stack = vec![tc];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).expect("read tc dir") {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                if !path
                    .file_name()
                    .is_some_and(|f| f.to_string_lossy().contains("test"))
                {
                    stack.push(path);
                }
                continue;
            }
            let file = path
                .file_name()
                .map(|f| f.to_string_lossy().into_owned())
                .unwrap_or_default();
            if !file.ends_with(".rs") || file.contains("test") {
                continue;
            }
            let text = std::fs::read_to_string(&path).expect("read tc source");
            // Stop at the file's IN-LINE test module (`#[cfg(test)] mod x {`):
            // fixture names are not hooks. An out-of-line `mod x;` is skipped
            // by the file filter above instead.
            let text = strip_inline_test_module(&text);
            for piece in text.split("Name::from_string(\"").skip(1) {
                if let Some(end) = piece.find('"') {
                    names.insert(piece[..end].to_string());
                }
            }
        }
    }
    assert!(
        names.contains("Nat.add"),
        "the scan must see the Nat extension"
    );
    let gated: BTreeSet<&str> = EXTENSION_KEYS.iter().map(|k| k.name).collect();
    let explained: BTreeSet<&str> = super::INERT_IN_REPLAY.iter().map(|(n, _)| *n).collect();
    let unclassified: Vec<&String> = names
        .iter()
        .filter(|s| !gated.contains(s.as_str()) && !explained.contains(s.as_str()))
        .collect();
    assert!(
        unclassified.is_empty(),
        "by-name type-checker hooks that are neither gated nor explained: {unclassified:?}"
    );
}

/// The bundle re-derivation (`clean_kernel::cert::bundle_recheck`) refuses a
/// `.cleancert` declaration outside the canonical base under any name the
/// kernel reduces or builds by name. Its list lives in the kernel crate, which
/// cannot see this table; the by-name census over `tc/` keeps THIS table
/// exhaustive, so the two must name exactly the same constants.
#[test]
fn every_extension_key_is_a_kernel_by_name_constant() {
    let keys: BTreeSet<&str> = EXTENSION_KEYS.iter().map(|k| k.name).collect();
    let kernel: BTreeSet<&str> = clean_kernel::cert::KERNEL_BY_NAME_CONSTANTS
        .iter()
        .copied()
        .collect();
    assert_eq!(
        keys, kernel,
        "clean_kernel::cert::KERNEL_BY_NAME_CONSTANTS must list exactly the extension keys"
    );
}

/// The binding controls of the 2026-11-14 `MData` erasure.
#[path = "extension_binding_mdata_tests.rs"]
mod mdata;
