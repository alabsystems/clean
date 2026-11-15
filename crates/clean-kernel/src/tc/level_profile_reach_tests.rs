// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe levels in each kernel theory on the paths other than constant
//! instantiation, level def-eq and the Π sort (DECISIONS R150): a projection's
//! constructor type, δ-unfolding, an ι-rule's right-hand side, the inductive
//! checks (mutual universe, field bound, the structural `is_zero` that skips
//! it), the recursor's elimination level and its K target. Every verdict
//! asserted under the Lean theories is pinned Lean v4.30.0-rc2's on the same
//! declaration, built from raw `Level` nodes and checked with `addDeclCore`
//! (`reports/level-lean-profile-2026-10-19/ReachVerdicts.lean`, its output in
//! `ReachVerdicts.txt`). `Extended` keeps Clean's own algebra, the scoped R2
//! exception.

use crate::env::{Declaration, EnvError, Environment, KernelTheory};
use crate::expr::{BinderInfo, Expr};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;

const LEAN_THEORIES: [KernelTheory; 2] = [KernelTheory::Lean, KernelTheory::LeanReference];

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn p(s: &str) -> Level {
    Level::param(n(s))
}

fn max(a: Level, b: Level) -> Level {
    Level::lean_max_core(a, b)
}

fn imax(a: Level, b: Level) -> Level {
    Level::lean_imax_core(a, b)
}

fn one() -> Level {
    Level::succ(Level::zero())
}

fn uv() -> Vec<Name> {
    vec![n("u"), n("v")]
}

fn uvw() -> Vec<Name> {
    vec![n("u"), n("v"), n("w")]
}

fn uvw_levels() -> Vec<Level> {
    vec![p("u"), p("v"), p("w")]
}

/// The stored level `max (max u v) w`.
fn field_level() -> Level {
    max(max(p("u"), p("v")), p("w"))
}

/// The instantiation `w := imax u v`.
fn inst3() -> Vec<Level> {
    vec![p("u"), p("v"), imax(p("u"), p("v"))]
}

/// What Clean's collapsing substitution builds from `field_level` at `inst3`.
fn collapsed() -> Level {
    max(p("u"), p("v"))
}

/// What Lean's `instantiate` builds (`mk_max` keeps both sides).
fn raw() -> Level {
    max(max(p("u"), p("v")), imax(p("u"), p("v")))
}

fn env_in(theory: KernelTheory) -> Environment {
    let mut env = Environment::for_lean_replay();
    env.set_kernel_theory(theory);
    env
}

fn pi(dom: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, dom, body)
}

fn lam(dom: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, dom, body)
}

fn def(name: &str, level_params: Vec<Name>, type_: Expr, value: Expr) -> Declaration {
    Declaration::Definition {
        name: n(name),
        level_params,
        type_,
        value,
        is_reducible: false,
    }
}

fn axiom(name: &str, level_params: Vec<Name>, type_: Expr) -> Declaration {
    Declaration::Axiom {
        name: n(name),
        level_params,
        type_,
    }
}

fn one_type(
    level_params: Vec<Name>,
    name: &str,
    type_: Expr,
    ctors: Vec<(&str, Expr)>,
) -> InductiveDecl {
    InductiveDecl {
        level_params,
        num_params: 0,
        types: vec![InductiveType {
            name: n(name),
            type_,
            constructors: ctors
                .into_iter()
                .map(|(ctor, type_)| Constructor {
                    name: n(ctor),
                    type_,
                })
                .collect(),
        }],
    }
}

/// `add` in a copy of `env`; a refusal's text for the assertions.
fn admits(
    env: &Environment,
    add: impl FnOnce(&mut Environment) -> Result<(), EnvError>,
) -> Result<(), String> {
    let mut env = env.clone();
    add(&mut env).map_err(|e| format!("{e:?}"))
}

fn assert_refused(what: &str, theory: KernelTheory, verdict: Result<(), String>, why: &str) {
    let err = verdict.expect_err(&format!(
        "{what}: pinned Lean refuses it; {theory:?} admitted it"
    ));
    assert!(
        err.contains(why),
        "{what} under {theory:?} is refused as {why}, got {err}"
    );
}

fn assert_admitted(what: &str, theory: KernelTheory, verdict: Result<(), String>) {
    verdict.unwrap_or_else(|e| panic!("{what}: pinned Lean admits it; {theory:?} refused: {e}"));
}

/// `structure S.{u,v,w} where a : Sort (max (max u v) w)`.
fn s_env(theory: KernelTheory) -> Environment {
    let mut env = env_in(theory);
    env.add_inductive(one_type(
        uvw(),
        "S",
        Expr::sort(Level::succ(field_level())),
        vec![(
            "S.mk",
            pi(
                Expr::sort(field_level()),
                Expr::const_(n("S"), uvw_levels()),
            ),
        )],
    ))
    .expect("pinned Lean admits S");
    env
}

/// `def name.{u,v} : S.{u,v,imax u v} → Sort l := fun s => s.1`.
fn proj_decl(name: &str, l: Level) -> Declaration {
    let s = Expr::const_(n("S"), inst3());
    def(
        name,
        uv(),
        pi(s.clone(), Expr::sort(l)),
        lam(s, Expr::proj(n("S"), 0, Expr::bvar(0))),
    )
}

/// `type_checker.cpp:241`: `infer_proj` instantiates the constructor's type
/// with `instantiate_type_lparams`, so `s.1 : Sort (max (max u v) (imax u v))`.
#[test]
fn lean_profile_projection_instantiates_like_lean() {
    for theory in LEAN_THEORIES {
        let env = s_env(theory);
        let collapsed_decl = proj_decl("proj_collapsed", collapsed());
        assert_refused(
            "proj_collapsed",
            theory,
            admits(&env, |e| e.add_decl(collapsed_decl)),
            "TypeMismatch",
        );
        let raw_decl = proj_decl("proj_raw", raw());
        assert_admitted("proj_raw", theory, admits(&env, |e| e.add_decl(raw_decl)));
    }
    let env = s_env(KernelTheory::Extended);
    for (name, l) in [("proj_collapsed", collapsed()), ("proj_raw", raw())] {
        let decl = proj_decl(name, l);
        admits(&env, |e| e.add_decl(decl)).expect("Extended keeps Clean's collapse and normaliser");
    }
}

/// `def D.{u,v,w} : Sort (succ (max (max u v) w)) := Sort (max (max u v) w)`.
fn d_env(theory: KernelTheory) -> Environment {
    let mut env = env_in(theory);
    env.add_decl(def(
        "D",
        uvw(),
        Expr::sort(Level::succ(field_level())),
        Expr::sort(field_level()),
    ))
    .expect("pinned Lean admits D");
    env
}

/// `def name.{u,v} : D.{u,v,imax u v} → Sort l := fun x => x`.
fn delta_decl(name: &str, l: Level) -> Declaration {
    let d = Expr::const_(n("D"), inst3());
    def(
        name,
        uv(),
        pi(d.clone(), Expr::sort(l)),
        lam(d, Expr::bvar(0)),
    )
}

/// `unfold_definition_core` instantiates the value with
/// `instantiate_value_lparams`: `D.{u,v,imax u v}` unfolds to
/// `Sort (max (max u v) (imax u v))`.
#[test]
fn lean_profile_delta_unfolds_like_lean() {
    for theory in LEAN_THEORIES {
        let env = d_env(theory);
        let collapsed_decl = delta_decl("delta_collapsed", collapsed());
        assert_refused(
            "delta_collapsed",
            theory,
            admits(&env, |e| e.add_decl(collapsed_decl)),
            "TypeMismatch",
        );
        let raw_decl = delta_decl("delta_raw", raw());
        assert_admitted("delta_raw", theory, admits(&env, |e| e.add_decl(raw_decl)));
    }
    let env = d_env(KernelTheory::Extended);
    for (name, l) in [("delta_collapsed", collapsed()), ("delta_raw", raw())] {
        let decl = delta_decl(name, l);
        admits(&env, |e| e.add_decl(decl)).expect("Extended keeps Clean's collapse and normaliser");
    }
}

/// `inductive W.{u,v,w} : Sort (succ (max (max u v) w)) | leaf | node : (Sort (max (max u v) w) → W) → W`,
/// and `Eqr`/`Eqr.refl` standing for `Eq`/`Eq.refl` (the kernel reads no
/// more of them than their types).
fn w_env(theory: KernelTheory) -> Environment {
    let mut env = env_in(theory);
    let w = Expr::const_(n("W"), uvw_levels());
    env.add_inductive(one_type(
        uvw(),
        "W",
        Expr::sort(Level::succ(field_level())),
        vec![
            ("W.leaf", w.clone()),
            ("W.node", pi(pi(Expr::sort(field_level()), w.clone()), w)),
        ],
    ))
    .expect("pinned Lean admits W");
    let a = Expr::sort(p("u"));
    // Eqr.{u} : (α : Sort u) → α → α → Prop
    env.add_decl(axiom(
        "Eqr",
        vec![n("u")],
        pi(
            a.clone(),
            pi(Expr::bvar(0), pi(Expr::bvar(1), Expr::sort(Level::zero()))),
        ),
    ))
    .expect("Eqr");
    // Eqr.refl.{u} : (α : Sort u) → (x : α) → Eqr α x x
    let eqr = Expr::const_(n("Eqr"), vec![p("u")]);
    env.add_decl(axiom(
        "Eqr.refl",
        vec![n("u")],
        pi(
            a,
            pi(
                Expr::bvar(0),
                Expr::apps(eqr, [Expr::bvar(1), Expr::bvar(0), Expr::bvar(0)]),
            ),
        ),
    ))
    .expect("Eqr.refl");
    env
}

/// `def name.{u,v} : ∀ (m : W.{u,v,imax u v} → Type) (lf : m W.leaf)
///   (nd : ∀ (g : Sort l → W), (∀ (x : Sort l), m (g x)) → m (W.node g)) (g : Sort l → W),
///   Eqr (m (W.node g)) (W.rec m lf nd (W.node g)) (nd g (fun (x : Sort l) => W.rec m lf nd (g x)))
/// := fun m lf nd g => Eqr.refl _ _`: the right side is the ι-reduct, so the
/// kernel compares the rule's instantiated binder with `Sort l`.
fn iota_decl(name: &str, l: Level) -> Declaration {
    let w = Expr::const_(n("W"), inst3());
    let leaf = Expr::const_(n("W.leaf"), inst3());
    let node = Expr::const_(n("W.node"), inst3());
    let mut rec_levels = vec![one()];
    rec_levels.extend(inst3());
    let rec = Expr::const_(n("W.rec"), rec_levels);
    let g_ty = pi(Expr::sort(l.clone()), w.clone());
    let m_ty = pi(w, Expr::sort(one()));
    let lf_ty = Expr::app(Expr::bvar(0), leaf);
    // under [m, lf, g, x]: m = 3, g = 1, x = 0
    let ih_ty = pi(
        Expr::sort(l.clone()),
        Expr::app(Expr::bvar(3), Expr::app(Expr::bvar(1), Expr::bvar(0))),
    );
    // under [m, lf, g, ih]: m = 3, g = 1
    let nd_ty = pi(
        g_ty.clone(),
        pi(
            ih_ty,
            Expr::app(Expr::bvar(3), Expr::app(node.clone(), Expr::bvar(1))),
        ),
    );
    // under [m, lf, nd, g]: m = 3, lf = 2, nd = 1, g = 0
    let node_g = Expr::app(node, Expr::bvar(0));
    let alpha = Expr::app(Expr::bvar(3), node_g.clone());
    let lhs = Expr::apps(
        rec.clone(),
        [Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), node_g],
    );
    // under [m, lf, nd, g, x]: m = 4, lf = 3, nd = 2, g = 1, x = 0
    let ih = lam(
        Expr::sort(l),
        Expr::apps(
            rec,
            [
                Expr::bvar(4),
                Expr::bvar(3),
                Expr::bvar(2),
                Expr::app(Expr::bvar(1), Expr::bvar(0)),
            ],
        ),
    );
    let rhs = Expr::apps(Expr::bvar(1), [Expr::bvar(0), ih]);
    let eq = Expr::const_(n("Eqr"), vec![one()]);
    let refl = Expr::const_(n("Eqr.refl"), vec![one()]);
    let type_body = Expr::apps(eq, [alpha.clone(), lhs.clone(), rhs]);
    let value_body = Expr::apps(refl, [alpha, lhs]);
    let binders = |body: Expr, mk: fn(Expr, Expr) -> Expr| {
        mk(
            m_ty.clone(),
            mk(lf_ty.clone(), mk(nd_ty.clone(), mk(g_ty.clone(), body))),
        )
    };
    def(name, uv(), binders(type_body, pi), binders(value_body, lam))
}

/// `inductive_reduce_rec` instantiates the rule's right-hand side with
/// `instantiate_lparams`, so the ι-reduct's binder is
/// `Sort (max (max u v) (imax u v))`. Only the raw spelling is well typed
/// (the binder of `g` must match `W.node`'s field), so the pin is the
/// honest one: a collapsing instantiation refuses it.
#[test]
fn lean_profile_iota_instantiates_like_lean() {
    for theory in LEAN_THEORIES {
        let decl = iota_decl("iota_raw", raw());
        assert_admitted(
            "iota_raw",
            theory,
            admits(&w_env(theory), |e| e.add_decl(decl)),
        );
    }
    let decl = iota_decl("iota_raw", raw());
    admits(&w_env(KernelTheory::Extended), |e| e.add_decl(decl)).expect("Extended admits iota_raw");
}

fn empty_type(name: &str, l: Level) -> InductiveType {
    InductiveType {
        name: n(name),
        type_: Expr::sort(l),
        constructors: vec![],
    }
}

fn mutual(a: &str, b: &str, la: Level, lb: Level) -> InductiveDecl {
    InductiveDecl {
        level_params: uv(),
        num_params: 0,
        types: vec![empty_type(a, la), empty_type(b, lb)],
    }
}

/// `inductive.cpp:250`: a mutual block's result levels must be
/// `is_equivalent`.
#[test]
fn lean_profile_mutual_universe_compares_like_lean() {
    for theory in LEAN_THEORIES {
        let env = env_in(theory);
        assert_refused(
            "mutual_raw_vs_collapsed",
            theory,
            admits(&env, |e| {
                e.add_inductive(mutual("MA1", "MB1", raw(), collapsed()))
            }),
            "different universe",
        );
        assert_admitted(
            "mutual_raw_vs_raw",
            theory,
            admits(&env, |e| {
                e.add_inductive(mutual("MA2", "MB2", raw(), raw()))
            }),
        );
        assert_admitted(
            "mutual_max_uv_vs_max_vu",
            theory,
            admits(&env, |e| {
                e.add_inductive(mutual("MA3", "MB3", collapsed(), max(p("v"), p("u"))))
            }),
        );
    }
    admits(&env_in(KernelTheory::Extended), |e| {
        e.add_inductive(mutual("MA1", "MB1", raw(), collapsed()))
    })
    .expect("Extended's is_geq both ways admits it");
}

/// `max v (imax u v)`, a level `mk_max`/`mk_imax` keep, so no instantiation
/// of it is sharing-dependent. Lean's `normalize` keeps both arguments;
/// Clean's drops `v`, which `imax u v` dominates.
fn av_level() -> Level {
    max(p("v"), imax(p("u"), p("v")))
}

/// `succ (imax u v)`: above [`av_level`] at every assignment. Lean's
/// `is_geq` must prove `succ (imax u v) ≥ v` and does not (different bases,
/// different offsets, `level.cpp:508-526`); Clean's compares it with the
/// normalised `imax u v` (`succ^n x ≥ x`).
fn fb_level() -> Level {
    Level::succ(imax(p("u"), p("v")))
}

/// `axiom Av.{u,v} : Sort (max v (imax u v))` and `axiom NatR : Type`.
fn field_env(theory: KernelTheory) -> Environment {
    let mut env = env_in(theory);
    env.add_decl(axiom("Av", uv(), Expr::sort(av_level())))
        .expect("Av");
    env.add_decl(axiom("NatR", vec![], Expr::sort(one())))
        .expect("NatR");
    env
}

/// `inductive name.{u,v} : Sort l | mk : Av.{u,v} → name.{u,v}`.
fn av_field(name: &str, l: Level) -> InductiveDecl {
    let av = Expr::const_(n("Av"), vec![p("u"), p("v")]);
    let mk = format!("{name}.mk");
    one_type(
        uv(),
        name,
        Expr::sort(l),
        vec![(
            mk.as_str(),
            pi(av, Expr::const_(n(name), vec![p("u"), p("v")])),
        )],
    )
}

/// `inductive name : Sort l | mk : NatR → name`.
fn nat_field(name: &str, l: Level) -> InductiveDecl {
    let mk = format!("{name}.mk");
    one_type(
        vec![],
        name,
        Expr::sort(l),
        vec![(
            mk.as_str(),
            pi(
                Expr::const_(n("NatR"), vec![]),
                Expr::const_(n(name), vec![]),
            ),
        )],
    )
}

/// `inductive.cpp:439`: every field's sort must be `is_geq` below the result
/// level. `Fb1 : Sort (succ (imax u v))` over a field of
/// `Sort (max v (imax u v))` holds at every assignment, and pinned Lean
/// refuses it; `Fb2` (`succ (max u v)`) and `Fb3` (the field's own level) it
/// admits.
#[test]
fn lean_profile_field_bound_is_lean_is_geq() {
    assert!(!Level::lean_is_geq(&fb_level(), &av_level()));
    assert!(Level::is_geq(&fb_level(), &av_level()));
    for theory in LEAN_THEORIES {
        let env = field_env(theory);
        assert_refused(
            "field_succ_imax_over_max_v_imax",
            theory,
            admits(&env, |e| e.add_inductive(av_field("Fb1", fb_level()))),
            "UniverseMismatch",
        );
        assert_admitted(
            "field_succ_max_over_max_v_imax",
            theory,
            admits(&env, |e| {
                e.add_inductive(av_field("Fb2", Level::succ(max(p("u"), p("v")))))
            }),
        );
        assert_admitted(
            "field_max_v_imax_over_itself",
            theory,
            admits(&env, |e| e.add_inductive(av_field("Fb3", av_level()))),
        );
    }
    admits(&field_env(KernelTheory::Extended), |e| {
        e.add_inductive(av_field("Fb1", fb_level()))
    })
    .expect("Extended's is_geq admits Fb1");
}

/// `inductive.cpp:439`: the bound is skipped only for a result level that IS
/// the `Zero` node; `Sort (max 0 0)` holding a `Type` field is refused.
#[test]
fn lean_profile_universe_bound_skips_only_structural_zero() {
    for theory in LEAN_THEORIES {
        let env = field_env(theory);
        assert_refused(
            "zero_max00_nat_field",
            theory,
            admits(&env, |e| {
                e.add_inductive(nat_field("Z1", max(Level::zero(), Level::zero())))
            }),
            "UniverseMismatch",
        );
        assert_admitted(
            "zero_prop_nat_field",
            theory,
            admits(&env, |e| e.add_inductive(nat_field("Z2", Level::zero()))),
        );
    }
    admits(&field_env(KernelTheory::Extended), |e| {
        e.add_inductive(nat_field("Z1", max(Level::zero(), Level::zero())))
    })
    .expect("Extended skips the bound for a level that is 0 everywhere");
}

/// `axiom A0 : Sort (max 0 0)`, `inductive P0 : Prop | mk : A0 → P0`, and
/// `inductive Q0 : Sort (max 0 0) | mk : Q0`.
fn elim_env(theory: KernelTheory) -> Environment {
    let mut env = env_in(theory);
    env.add_decl(axiom(
        "A0",
        vec![],
        Expr::sort(max(Level::zero(), Level::zero())),
    ))
    .expect("pinned Lean admits A0");
    env.add_inductive(one_type(
        vec![],
        "P0",
        Expr::sort(Level::zero()),
        vec![(
            "P0.mk",
            pi(Expr::const_(n("A0"), vec![]), Expr::const_(n("P0"), vec![])),
        )],
    ))
    .expect("pinned Lean admits P0");
    env.add_inductive(one_type(
        vec![],
        "Q0",
        Expr::sort(max(Level::zero(), Level::zero())),
        vec![("Q0.mk", Expr::const_(n("Q0"), vec![]))],
    ))
    .expect("pinned Lean admits Q0");
    env
}

/// `inductive.cpp:517` (a field whose sort is not structurally `0` and does
/// not occur in the result restricts elimination to `Prop`) and `:557` (K
/// needs a structural `0`): pinned Lean builds `P0.rec` with no universe
/// parameter and `Q0.rec` with `k = false`.
#[test]
fn lean_profile_recursor_reads_structural_zero() {
    for theory in LEAN_THEORIES {
        let env = elim_env(theory);
        let p0 = env.get_recursor(&n("P0.rec")).expect("P0.rec");
        assert!(
            p0.level_params.is_empty(),
            "P0.rec under {theory:?}: pinned Lean eliminates only into Prop, got {:?}",
            p0.level_params
        );
        let q0 = env.get_recursor(&n("Q0.rec")).expect("Q0.rec");
        assert!(
            !q0.is_k,
            "Q0.rec under {theory:?}: pinned Lean's k is false"
        );
    }
    let env = elim_env(KernelTheory::Extended);
    let p0 = env.get_recursor(&n("P0.rec")).expect("P0.rec");
    assert_eq!(
        p0.level_params.len(),
        1,
        "Extended reads the field as a Prop"
    );
    let q0 = env.get_recursor(&n("Q0.rec")).expect("Q0.rec");
    assert!(q0.is_k, "Extended reads Q0 as an inductive predicate");
}

/// KNOWN GAP (DECISIONS R150): `inductive Qu.{u} : Sort (imax u 0) | mk : Qu.{u}`.
/// The constructor's type instantiates `Sort (imax u 0)` by the identity, a
/// node `mk_imax` rebuilds to `0`, so Lean's `instantiate` keeps or rebuilds
/// it by object sharing; pinned Lean admits `Qu` under either reading. Clean
/// cannot see sharing and refuses it by name. This fails the day the hazard
/// learns to admit a sharing dependence on which Lean's verdict does not turn.
#[test]
fn lean_profile_refuses_sharing_dependence_lean_admits_either_way() {
    let qu = || {
        one_type(
            vec![n("u")],
            "Qu",
            Expr::sort(imax(p("u"), Level::zero())),
            vec![("Qu.mk", Expr::const_(n("Qu"), vec![p("u")]))],
        )
    };
    for theory in LEAN_THEORIES {
        let err = admits(&env_in(theory), |e| e.add_inductive(qu()))
            .expect_err("Clean refuses Qu (pinned Lean admits it)");
        assert!(err.contains("LevelSharingDependent"), "{theory:?}: {err}");
    }
    admits(&env_in(KernelTheory::Extended), |e| e.add_inductive(qu())).expect("Extended admits Qu");
}
