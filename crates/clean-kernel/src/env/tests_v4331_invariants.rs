// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean v4.33.1's defensive kernel invariants at the environment boundary
//! (plan item `kernel-defensive-invariants-v4331`, decision R147): structure
//! eta on a recursor major (leanprover/lean4#14843), the checked annotation
//! strip of generated recursors (leanprover/lean4#15707), and the nested
//! occurrence whose parametric argument hides a wrong-structure projection
//! (leanprover/lean4#14576 / #14577).

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// leanprover/lean4#14843 (v4.33.1): `to_cnstr_when_structure`, which turns a
/// recursor's non-constructor major into `S.mk major.1 … major.n`, skips Prop
/// structures through `is_prop(e_type)`, and since #14807 that requires the
/// type's type to be a sort. Clean's copy (`try_eta_struct_core`) inlined the
/// old check, `whnf(infer(e_type)).is_prop()`, so a type whose type is stuck
/// (not a sort) was read as "not Prop" and eta-expanded. A well-typed term
/// never has such a type, so the test plants one: `EtaS`'s declared type is
/// replaced, after admission, by `(h : EtaP) → EtaG h` with `EtaG` an axiom.
/// The control is the same recursor application over the admitted type, which
/// must still reduce through structure eta.
#[test]
fn structure_eta_on_a_major_whose_type_is_not_sort_typed_stays_stuck() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_bool().expect("init_bool should succeed");
    let c = |n: &str| Expr::const_(Name::from_string(n), vec![]);
    let axiom = |env: &mut Environment, n: &str, ty: Expr| {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(n),
            level_params: vec![],
            type_: ty,
        })
        .unwrap_or_else(|e| panic!("env setup: axiom {n}: {e:?}"));
    };
    axiom(&mut env, "EtaP", Expr::prop());
    axiom(&mut env, "eta_h", c("EtaP"));
    axiom(&mut env, "EtaG", Expr::arrow(c("EtaP"), Expr::type_()));
    let s_name = Name::from_string("EtaS");
    let s_of = |h: Expr| Expr::app(c("EtaS"), h);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: s_name.clone(),
            type_: Expr::arrow(c("EtaP"), Expr::type_()),
            constructors: vec![Constructor {
                name: Name::from_string("EtaS.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    c("EtaP"),
                    Expr::arrow(c("Bool"), s_of(Expr::bvar(1))),
                ),
            }],
        }],
    })
    .expect("env setup: structure EtaS (h : EtaP) | mk (b : Bool)");
    axiom(&mut env, "eta_x", s_of(c("eta_h")));

    let bool_ty = c("Bool");
    let rec_app = Expr::apps(
        Expr::const_(
            Name::from_string("EtaS.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            c("eta_h"),
            Expr::lam(BinderInfo::Default, s_of(c("eta_h")), bool_ty.clone()),
            Expr::lam(BinderInfo::Default, bool_ty, Expr::bvar(0)),
            c("eta_x"),
        ],
    );
    let field = Expr::proj(s_name.clone(), 0, c("eta_x"));

    // Control: over the admitted `EtaS : EtaP → Type`, structure eta fires.
    assert_eq!(
        TypeChecker::new(&env).whnf(&rec_app),
        field,
        "control: EtaS.rec over a non-constructor major must reduce through eta"
    );

    // Subject: `EtaS h : EtaG h`, whose type is stuck, not a sort.
    env.constants.get_mut(&s_name).expect("EtaS constant").type_ = Expr::pi(
        BinderInfo::Default,
        c("EtaP"),
        Expr::app(c("EtaG"), Expr::bvar(0)),
    );
    let reduced = TypeChecker::new(&env).whnf(&rec_app);
    assert_eq!(
        reduced, rec_app,
        "structure eta must not fire when the major's type is not sort-typed"
    );
}

/// `SpB | f | t`, the field type the annotation tests wrap.
fn spb_env() -> Environment {
    let mut env = Environment::new();
    let spb = Expr::const_(Name::from_string("SpB"), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("SpB"),
            type_: Expr::type_(),
            constructors: ["SpB.f", "SpB.t"]
                .map(|n| Constructor {
                    name: Name::from_string(n),
                    type_: spb.clone(),
                })
                .to_vec(),
        }],
    })
    .expect("env setup: SpB");
    env
}

/// `optParam : (α : Type) → α → Type := value`, then `SpFlag | mk (b : optParam
/// SpB SpB.f)`: the admission result, and the `SpFlag.rec` minor premise's
/// field domain when admitted.
fn admit_flag_over_opt_param(value: Expr) -> (Result<(), EnvError>, Option<Expr>) {
    let mut env = spb_env();
    let spb = Expr::const_(Name::from_string("SpB"), vec![]);
    env.add_decl(Declaration::Definition {
        name: Name::from_string("optParam"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::type_()),
        ),
        value,
        is_reducible: true,
    })
    .expect("env setup: the optParam definition must kernel-check");
    let annotated = Expr::app(
        Expr::app(Expr::const_(Name::from_string("optParam"), vec![]), spb),
        Expr::const_(Name::from_string("SpB.f"), vec![]),
    );
    let flag = Name::from_string("SpFlag");
    let admitted = env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: flag.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("SpFlag.mk"),
                type_: Expr::pi(BinderInfo::Default, annotated, Expr::const_(flag, vec![])),
            }],
        }],
    });
    let field = env
        .get_const(&Name::from_string("SpFlag.rec"))
        .and_then(|rec| match rec.type_.kind() {
            ExprKind::Pi(_, _motive, rest) => match rest.kind() {
                ExprKind::Pi(_, minor, _) => match minor.kind() {
                    ExprKind::Pi(_, field, _) => Some(field.as_ref().clone()),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        });
    (admitted, field)
}

/// leanprover/lean4#15704 / #15707 (#15707 was closed unmerged upstream on
/// 2026-10-17; neither the pinned v4.30.0-rc2 nor v4.33.1 has it): recursor
/// generation strips `optParam α d` to `α` by NAME in every binder domain,
/// which is sound only if `optParam` unfolds to its first argument. Decision
/// R147 does NOT port the checked strip, because it is not a pure tightening:
/// Clean already REFUSES a family over a non-canonical `optParam`, here
/// `fun α _ => α → α`, through the
/// subject-reduction check of the generated ι-rule (the stripped minor takes
/// an `SpB` where the constructor supplies an `SpB → SpB`), and a checked
/// strip would turn that refusal into an admission. This pins the refusal, so
/// it fails loudly the day the strip changes. The control is the canonical
/// `fun α _ => α`, which is admitted with the field domain stripped to `SpB`.
#[test]
fn spoofed_opt_param_family_is_refused_by_the_rule_check() {
    let spb = Expr::const_(Name::from_string("SpB"), vec![]);
    let canonical = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let (admitted, field) = admit_flag_over_opt_param(canonical);
    admitted.unwrap_or_else(|e| panic!("control: SpFlag over the canonical optParam: {e:?}"));
    assert_eq!(
        field,
        Some(spb),
        "control: the canonical optParam is stripped from the minor's field domain"
    );

    let spoofed = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
        ),
    );
    let (admitted, field) = admit_flag_over_opt_param(spoofed);
    let error = format!(
        "{:?}",
        admitted.expect_err("a family over a non-canonical optParam must stay refused")
    );
    assert!(
        error.contains("violates subject reduction"),
        "the refusal must be the generated rule's subject-reduction check, got {error}"
    );
    assert_eq!(
        field, None,
        "a refused family must leave no recursor behind"
    );
}

/// leanprover/lean4#14576 (fixed by #14577): a nested occurrence `NL (E w) b`
/// drops its parametric argument `b` from the auxiliary declaration the kernel
/// generates, so upstream never type-checked it, and an ill-typed `b`, here
/// `NC.0 (NC.0 w)` with `w : NW` (a projection of structure `NC` out of an
/// `NW`), was admitted and later reduced through a foreign constructor to prove
/// `False`. Clean must refuse the declaration. The control declares the same
/// family with a well-typed parametric argument, so a refusal of nested
/// families in general fails the test.
#[test]
fn nested_occurrence_with_ill_typed_parametric_argument_is_refused() {
    let mut env = Environment::new();
    env.init_bool().expect("init_bool should succeed");
    let c = |n: &str| Expr::const_(Name::from_string(n), vec![]);
    let one = |name: &str, ty: Expr, ctor: &str, ctor_ty: Expr, num_params: u32| InductiveDecl {
        level_params: vec![],
        num_params,
        types: vec![InductiveType {
            name: Name::from_string(name),
            type_: ty,
            constructors: vec![Constructor {
                name: Name::from_string(ctor),
                type_: ctor_ty,
            }],
        }],
    };
    for decl in [
        // inductive NP : Prop | mk (b : Bool)
        one(
            "NP",
            Expr::prop(),
            "NP.mk",
            Expr::arrow(c("Bool"), c("NP")),
            0,
        ),
        // structure NC where b : Bool
        one(
            "NC",
            Expr::type_(),
            "NC.mk",
            Expr::arrow(c("Bool"), c("NC")),
            0,
        ),
        // inductive NW : Type | mk (p : NP)
        one(
            "NW",
            Expr::type_(),
            "NW.mk",
            Expr::arrow(c("NP"), c("NW")),
            0,
        ),
        // inductive NL (α : Type) (b : Bool) : Type | mk
        one(
            "NL",
            Expr::arrow(Expr::type_(), Expr::arrow(c("Bool"), Expr::type_())),
            "NL.mk",
            Expr::pi(
                BinderInfo::Default,
                Expr::type_(),
                Expr::pi(
                    BinderInfo::Default,
                    c("Bool"),
                    Expr::app(Expr::app(c("NL"), Expr::bvar(1)), Expr::bvar(0)),
                ),
            ),
            2,
        ),
    ] {
        env.add_inductive(decl)
            .unwrap_or_else(|e| panic!("env setup: {e:?}"));
    }
    // inductive E (w : NW) : Type | mk (l : NL (E w) b) : E w
    let family = |name: &str, b: Expr| {
        let e = |w: Expr| Expr::app(c(name), w);
        one(
            name,
            Expr::arrow(c("NW"), Expr::type_()),
            &format!("{name}.mk"),
            Expr::pi(
                BinderInfo::Default,
                c("NW"),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(Expr::app(c("NL"), e(Expr::bvar(0))), b),
                    e(Expr::bvar(1)),
                ),
            ),
            1,
        )
    };
    let mut control = env.clone();
    control
        .add_inductive(family("NEok", c("Bool.true")))
        .unwrap_or_else(|e| panic!("control: a nested family with a well-typed argument: {e:?}"));
    let wrong = Expr::proj(
        Name::from_string("NC"),
        0,
        Expr::proj(Name::from_string("NC"), 0, Expr::bvar(0)),
    );
    let error = env
        .add_inductive(family("NEbad", wrong))
        .expect_err("a nested occurrence's ill-typed parametric argument must be refused");
    assert!(
        env.get_inductive(&Name::from_string("NEbad")).is_none(),
        "a refused family must leave no inductive behind"
    );
    let error = format!("{error:?}");
    // The refusing layer, measured 2026-10-19 (decision R147): the nested
    // restore pass type-checks each restored user constructor type
    // (`check_decl_readonly_strict` in `inductive_nested_restore.rs`), the
    // analogue of #14577, and refuses `NEbad.mk`'s projection of `NC` out of an
    // `NW`. With that check disabled the generated recursor's type check still
    // refuses the family, at `NEbad.rec`, so there are two refusing layers; this
    // test names the first.
    assert!(
        error.contains("InvalidProjNotStruct") && error.contains(r#"["NEbad", "mk"]"#),
        "the refusal must be the constructor type's check of the parametric argument, got {error}"
    );
}
