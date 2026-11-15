// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KR1 increment 3 (`docs/DECISIONS.md` R143): every closure through the
//! reference entry is ⊆ Ax0 plus the quotient formers.
//!
//! Ax0 is `{propext, Quot.sound, Classical.choice}` (Trust
//! `docs/plans/2026-10-15-proven-core.md` §2.0); `Quot`, `Quot.mk`,
//! `Quot.lift` and `Quot.ind` are part of the theory, not axioms. The entry
//! admits an axiom only when it is the kernel's canonical declaration of one
//! of those names (name AND statement), and refuses any check whose closure
//! reaches a base axiom that is not, with `ReferenceRefusal::OutsideAx0`.
//! Before R143 the entry refused only the tripwires, so a base `axiom bad :
//! False` (R107: "a base carrying a false axiom passes") let `theorem _ :
//! False := bad` through. Each refusal below has its control on the same
//! entry.

use clean_kernel::{
    canonical_foundation_declaration, BinderInfo, Declaration, Environment, Expr, Level, Name,
    ReferenceKernel, ReferenceRefusal,
};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}

fn theorem(n: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Theorem {
        name: name(n),
        level_params: vec![],
        type_,
        value,
    }
}

fn axiom(n: &str, type_: Expr) -> Declaration {
    Declaration::Axiom {
        name: name(n),
        level_params: vec![],
        type_,
    }
}

fn expect_outside(result: Result<clean_kernel::ReferenceAccepted, ReferenceRefusal>, want: &str) {
    match result {
        Err(ReferenceRefusal::OutsideAx0 { reached, .. }) => assert_eq!(reached, name(want)),
        other => panic!("expected OutsideAx0 reaching {want}, got {other:?}"),
    }
}

/// `axiom kr3_bad : False` in a `with_prelude` base, cited directly, through
/// a definition, and through a theorem's type: each refuses, naming it.
/// Control: `True.intro` over the same entry.
#[test]
fn test_a_false_base_axiom_is_not_reachable_through_the_entry() {
    let mut base = Environment::with_prelude();
    base.add_decl(axiom("kr3_bad", c("False")))
        .expect("the base admits a false axiom (its type is well formed)");
    base.add_decl(theorem("kr3_bad_wrapped", c("False"), c("kr3_bad")))
        .expect("and a theorem resting on it");
    let mut k = ReferenceKernel::new(base).expect("a base may HOLD the axiom");
    expect_outside(
        k.add_checked(theorem("kr3_false", c("False"), c("kr3_bad"))),
        "kr3_bad",
    );
    expect_outside(k.check_closed_term(&c("False"), &c("kr3_bad")), "kr3_bad");
    expect_outside(
        k.check_closed_term(&c("False"), &c("kr3_bad_wrapped")),
        "kr3_bad",
    );
    k.check_closed_term(&c("True"), &c("True.intro"))
        .expect("control: True.intro");
}

/// Declaring an axiom through the entry: anything but a canonical Ax0
/// declaration refuses — a fresh name, `propext` at a false statement, and
/// `Classical.choice` without its `Nonempty` premise. Control: the kernel's
/// canonical `Classical.choice` is admitted once `Nonempty` is (both through
/// the entry, over an empty base).
#[test]
fn test_only_canonical_ax0_axioms_are_admitted() {
    let mut k = ReferenceKernel::new(Environment::default()).expect("empty base");
    expect_outside(k.add_checked(axiom("kr3_fresh", Expr::prop())), "kr3_fresh");
    expect_outside(k.add_checked(axiom("propext", Expr::prop())), "propext");
    assert!(k.environment().get_const(&name("propext")).is_none());
    let nonempty = Environment::with_prelude()
        .inductive_decl_of(&name("Nonempty"))
        .expect("with_prelude has Nonempty");
    k.add_inductive_checked(nonempty).expect("Nonempty");
    let u = name("u");
    let sort_u = Expr::sort(Level::param(u.clone()));
    let spoof = Declaration::Axiom {
        name: name("Classical.choice"),
        level_params: vec![u],
        type_: Expr::pi(BinderInfo::Implicit, sort_u, Expr::bvar(0)),
    };
    expect_outside(k.add_checked(spoof), "Classical.choice");
    let choice = canonical_foundation_declaration(&name("Classical.choice"))
        .expect("Classical.choice is foundational");
    k.add_checked(choice)
        .expect("control: the canonical Classical.choice is admitted");
}

/// The foundational axioms themselves are reachable: a theorem that is
/// `@propext` at its own statement, and one citing `Classical.choice`, are
/// accepted over `with_prelude` (control for every refusal in this file).
#[test]
fn test_ax0_itself_is_reachable() {
    let mut k = ReferenceKernel::new(Environment::with_prelude()).expect("with_prelude");
    let propext = k
        .environment()
        .get_const(&name("propext"))
        .expect("propext")
        .clone();
    k.add_checked(theorem(
        "kr3_uses_propext",
        propext.type_.clone(),
        c("propext"),
    ))
    .expect("a closure of {propext} is inside Ax0");
    let choice = k
        .environment()
        .get_const(&name("Classical.choice"))
        .expect("Classical.choice")
        .clone();
    let ty = choice
        .type_
        .instantiate_level_params_direct(&choice.level_params, &[Level::succ(Level::zero())]);
    k.check_closed_term(
        &ty,
        &Expr::const_(name("Classical.choice"), vec![Level::succ(Level::zero())]),
    )
    .expect("a closure of {Classical.choice} is inside Ax0");
}

/// The non-foundational axioms the default prelude still declares after R143
/// (the `IO` family, `tryCatchThe`, `tryFinally`) are unreachable through the
/// entry, directly and through a definition built on them (`instMonadIO`).
#[test]
fn test_opted_in_non_foundational_axioms_are_refused() {
    let mut opted = Environment::with_prelude();
    for name_ in ["IO", "IO.pure", "tryFinally", "tryCatchThe", "instMonadIO"] {
        assert!(
            opted.get_const(&name(name_)).is_none(),
            "default excludes {name_}"
        );
    }
    opted
        .init_io_stub_theory()
        .expect("explicit IO stub theory");
    opted
        .init_control_stub_theory()
        .expect("explicit control stub theory");
    let k = ReferenceKernel::new(opted).expect("opted-in environment");
    let env = k.environment();
    // `IO.pure`'s own type cites the `IO` axiom, which the closure reaches
    // first (seeds are taken in name order).
    for (ax, reached) in [
        ("tryFinally", "tryFinally"),
        ("tryCatchThe", "tryCatchThe"),
        ("IO.pure", "IO"),
    ] {
        let Some(info) = env.get_const(&name(ax)) else {
            panic!("explicit stub theory declares {ax}");
        };
        let levels = vec![Level::succ(Level::zero()); info.level_params.len()];
        let ty = info
            .type_
            .instantiate_level_params_direct(&info.level_params, &levels);
        expect_outside(
            k.check_closed_term(&ty, &Expr::const_(name(ax), levels)),
            reached,
        );
    }
    // The explicit IO fragment declares its checked `instMonadIO` dictionary;
    // absence fails here instead of skipping the closure assertion.
    let Some(inst) = env.get_const(&name("instMonadIO")) else {
        panic!("explicit IO stub theory declares instMonadIO");
    };
    let r = k.check_closed_term(&inst.type_.clone(), &c("instMonadIO"));
    assert!(
        matches!(r, Err(ReferenceRefusal::OutsideAx0 { .. })),
        "instMonadIO rests on the IO axioms: {r:?}"
    );
}

/// Every theorem the default prelude holds has its closure ⊆ Ax0 plus the
/// quotient formers (`axiom_deps` lists what is outside, canonical
/// foundations excluded). Control: a theorem resting on a fresh axiom, added
/// to the same environment, is listed.
#[test]
fn test_every_prelude_theorem_closure_is_inside_ax0() {
    let mut env = Environment::with_prelude();
    let mut outside: Vec<String> = env
        .constants()
        .filter(|c| c.kind == clean_kernel::ConstantKind::Theorem)
        .filter_map(|c| {
            let deps = env.axiom_deps(&c.name)?;
            (!deps.is_empty()).then(|| format!("{}: {deps:?}", c.name))
        })
        .collect();
    outside.sort();
    assert!(outside.is_empty(), "theorems outside Ax0: {outside:#?}");
    env.add_decl(axiom("kr3_ax", c("True"))).expect("axiom");
    env.add_decl(theorem("kr3_on_ax", c("True"), c("kr3_ax")))
        .expect("theorem");
    let deps = env.axiom_deps(&name("kr3_on_ax")).expect("present");
    assert!(deps.contains(&name("kr3_ax")), "control: {deps:?}");
}

/// `∀ p : Prop, p`.
fn false_ty() -> Expr {
    Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0))
}

/// `def Nonempty.{u} : Sort u → Prop := fun _ => ∀ p : Prop, p → p`: a
/// constant NAMED like Lean's premise of `Classical.choice` that every type
/// satisfies.
fn forged_nonempty() -> Declaration {
    let u = name("u");
    let sort_u = Expr::sort(Level::param(u.clone()));
    Declaration::Definition {
        name: name("Nonempty"),
        level_params: vec![u],
        type_: Expr::pi(BinderInfo::Default, sort_u.clone(), Expr::prop()),
        value: Expr::lam(
            BinderInfo::Default,
            sort_u,
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
            ),
        ),
        is_reducible: false,
    }
}

/// `@Classical.choice.{0} (∀ p, p) (fun p h => h)`: a proof of `∀ p, p` once
/// `Nonempty α` means `∀ p : Prop, p → p`.
fn choice_at_false() -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(name("Classical.choice"), vec![Level::zero()]),
            false_ty(),
        ),
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        ),
    )
}

/// Review of R143 (P2): the canonical `Classical.choice` statement names
/// `Nonempty` by name, so over a forged `Nonempty` the canonical axiom proves
/// `∀ p : Prop, p`. Admitting it through the entry now also requires its
/// premise to be Lean's inductive `Nonempty` (`check_foundation_premises`),
/// so the axiom refuses as `OutsideAx0` and the false theorem cannot be
/// stated. Control: the same steps with Lean's `Nonempty` admit the axiom
/// (`test_only_canonical_ax0_axioms_are_admitted`), and here the forged
/// definition itself is admitted (it is a definition, not an assumption).
#[test]
fn test_canonical_choice_over_a_forged_nonempty_is_refused_through_the_entry() {
    let mut k = ReferenceKernel::new(Environment::default()).expect("empty base");
    k.add_checked(forged_nonempty())
        .expect("control: the forged definition is a definition");
    let choice = canonical_foundation_declaration(&name("Classical.choice"))
        .expect("Classical.choice is foundational");
    expect_outside(k.add_checked(choice), "Classical.choice");
    assert!(
        k.add_checked(theorem("kr3_p2_false", false_ty(), choice_at_false()))
            .is_err(),
        "nothing proves ∀ p, p"
    );
}

/// Review of R143 (P3): the same forged premise in `new`'s base. The base's
/// canonical `Classical.choice` is outside Ax0 because its `Nonempty` is not
/// Lean's, so the false closed term refuses as `OutsideAx0`. Control: over
/// `with_prelude` (Lean's `Nonempty`), a citation of `Classical.choice` is
/// accepted (`test_ax0_itself_is_reachable`).
#[test]
fn test_canonical_choice_over_a_forged_base_nonempty_is_outside_ax0() {
    let mut base = Environment::default();
    base.add_decl(forged_nonempty()).expect("forged Nonempty");
    base.add_decl(canonical_foundation_declaration(&name("Classical.choice")).expect("canonical"))
        .expect("the canonical axiom over it");
    let k = ReferenceKernel::new(base).expect("a base may hold it");
    expect_outside(
        k.check_closed_term(&false_ty(), &choice_at_false()),
        "Classical.choice",
    );
}

/// Review of R143 (P2/P3 for `propext`): the canonical `propext` over an
/// `Iff` that is not Lean's (`def Iff (a b : Prop) : Prop := True`, so
/// `propext` would equate any two propositions) is outside Ax0 in a base and
/// refused through the entry. Control: `with_prelude`'s `propext` is
/// reachable (`test_ax0_itself_is_reachable`).
#[test]
fn test_canonical_propext_over_a_forged_iff_is_outside_ax0() {
    let eq = Environment::with_prelude()
        .inductive_decl_of(&name("Eq"))
        .expect("with_prelude has Eq");
    let true_ind = Environment::with_prelude()
        .inductive_decl_of(&name("True"))
        .expect("with_prelude has True");
    let forged_iff = Declaration::Definition {
        name: name("Iff"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        ),
        value: Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(BinderInfo::Default, Expr::prop(), c("True")),
        ),
        is_reducible: false,
    };
    let propext = canonical_foundation_declaration(&name("propext")).expect("canonical");
    let mut base = Environment::default();
    base.add_inductive_core(eq.clone()).expect("Eq");
    base.add_inductive_core(true_ind.clone()).expect("True");
    base.add_decl(forged_iff.clone()).expect("forged Iff");
    base.add_decl(propext.clone())
        .expect("canonical propext over it");
    let k = ReferenceKernel::new(base).expect("a base may hold it");
    let ty = k
        .environment()
        .get_const(&name("propext"))
        .expect("propext")
        .type_
        .clone();
    expect_outside(k.check_closed_term(&ty, &c("propext")), "propext");

    let mut k = ReferenceKernel::new(Environment::default()).expect("empty base");
    k.add_inductive_checked(eq).expect("Eq");
    k.add_inductive_checked(true_ind).expect("True");
    k.add_checked(forged_iff).expect("a definition");
    expect_outside(k.add_checked(propext), "propext");
}

/// Review of R143 (A3): a base `axiom propext : ∀ p : Prop, p` is named like
/// Ax0 but is not its statement, so it is outside Ax0 and a theorem resting
/// on it refuses through the entry. Before the review no test planted a
/// foundational name at a wrong statement in a BASE; a mutant that compared
/// the base axiom's name only passed every test. The base holds Lean's `Eq`
/// and `Iff`, so the statement is the only thing wrong (the premise rule
/// alone would not refuse it). Control: `True.intro` over the same entry.
#[test]
fn test_a_base_axiom_named_propext_at_a_false_statement_is_outside_ax0() {
    let prelude = Environment::with_prelude();
    let mut base = Environment::default();
    for ind in ["Eq", "Iff", "True"] {
        base.add_inductive_core(
            prelude
                .inductive_decl_of(&name(ind))
                .unwrap_or_else(|| panic!("with_prelude has {ind}")),
        )
        .expect("Lean's inductive");
    }
    base.check_foundation_premises(&name("propext"))
        .expect("propext's premises are Lean's here");
    base.add_decl(axiom("propext", false_ty()))
        .expect("the base admits it (its type is well formed)");
    let mut k = ReferenceKernel::new(base).expect("a base may HOLD it");
    expect_outside(
        k.add_checked(theorem("kr3_a3_false", false_ty(), c("propext"))),
        "propext",
    );
    k.check_closed_term(&c("True"), &c("True.intro"))
        .expect("control: True.intro");
}

/// Review of R143 (P1): two base theorems that cite each other. Built with
/// public doors only: `axiom pa : ∀ p, p`, `theorem pb := pa`, then
/// `upgrade_axiom_to_checked_decl(theorem pa := pb)` (which checks `pb` with
/// `pb` resident). The base then holds no axiom and every record is stamped
/// `FullKernelCheck`; before the review the dependencies-first re-check
/// dropped the back edge and checked each with the other resident, so both
/// a declaration and a closed term proving `∀ p, p` were accepted. Now the
/// cycle refuses as `BaseRecheck`. Control: an acyclic base theorem on the
/// same entry is accepted.
#[test]
fn test_a_cycle_of_base_theorems_is_refused() {
    let mut base = Environment::default();
    base.add_decl(axiom("kr3_pa", false_ty()))
        .expect("axiom pa");
    base.add_decl(theorem("kr3_pb", false_ty(), c("kr3_pa")))
        .expect("theorem pb := pa");
    base.upgrade_axiom_to_checked_decl(theorem("kr3_pa", false_ty(), c("kr3_pb")))
        .expect("the upgrade checks pa := pb with pb resident");
    let id_ty = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let id = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    base.add_decl(theorem("kr3_acyclic", id_ty.clone(), id))
        .expect("an acyclic theorem");
    let mut k = ReferenceKernel::new(base).expect("no axiom left in the base");
    for r in [
        k.check_closed_term(&false_ty(), &c("kr3_pb")),
        k.check_closed_term(&false_ty(), &c("kr3_pa")),
    ] {
        assert!(
            matches!(&r, Err(ReferenceRefusal::BaseRecheck { reason, .. }) if reason.contains("cyclic")),
            "expected a cyclic BaseRecheck, got {r:?}"
        );
    }
    assert!(matches!(
        k.add_checked(theorem("kr3_p_false", false_ty(), c("kr3_pa"))),
        Err(ReferenceRefusal::BaseRecheck { .. })
    ));
    k.check_closed_term(&id_ty, &c("kr3_acyclic"))
        .expect("control: an acyclic base theorem");
}

/// Review of R143: `check_foundation_premises` pins `Nonempty`'s shape, not
/// only that it is an inductive. Two inductives named `Nonempty` admitted
/// through the entry: one whose constructor takes no value (so every
/// `Nonempty α` is inhabited and the canonical `Classical.choice` would
/// prove `∀ p : Prop, p`), and one of type `Sort u → Sort (max 1 u)` with
/// Lean's constructor. The canonical axiom refuses as `OutsideAx0` over
/// each. Control: over Lean's `Nonempty` it is admitted
/// (`test_only_canonical_ax0_axioms_are_admitted`).
#[test]
fn test_canonical_choice_over_a_misshapen_nonempty_inductive_is_refused() {
    use clean_kernel::{Constructor, InductiveDecl, InductiveType};
    let u = name("u");
    let sort_u = || Expr::sort(Level::param(u.clone()));
    let ne = || Expr::const_(name("Nonempty"), vec![Level::param(u.clone())]);
    let argless = InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: name("Nonempty"),
            type_: Expr::pi(BinderInfo::Default, sort_u(), Expr::prop()),
            constructors: vec![Constructor {
                name: name("Nonempty.intro"),
                type_: Expr::pi(
                    BinderInfo::Implicit,
                    sort_u(),
                    Expr::app(ne(), Expr::bvar(0)),
                ),
            }],
        }],
    };
    let big = InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: name("Nonempty"),
            type_: Expr::pi(
                BinderInfo::Default,
                sort_u(),
                Expr::sort(Level::max(
                    Level::succ(Level::zero()),
                    Level::param(u.clone()),
                )),
            ),
            constructors: vec![Constructor {
                name: name("Nonempty.intro"),
                type_: Expr::pi(
                    BinderInfo::Implicit,
                    sort_u(),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(0),
                        Expr::app(ne(), Expr::bvar(1)),
                    ),
                ),
            }],
        }],
    };
    for (what, decl) in [("no value", argless), ("not a Prop", big)] {
        let mut k = ReferenceKernel::new(Environment::default()).expect("empty base");
        k.add_inductive_checked(decl)
            .unwrap_or_else(|e| panic!("{what}: the inductive itself is admissible: {e:?}"));
        let choice = canonical_foundation_declaration(&name("Classical.choice"))
            .expect("Classical.choice is foundational");
        expect_outside(k.add_checked(choice), "Classical.choice");
    }
}
