// RESOLVED BOUNDARY for the Coq TEMPLATE-POLYMORPHISM `prod` unlock.
//
// The companion test `coq_template_poly_prod_feasibility.rs` proves the kernel
// accepts the poly inductive TYPE `prod.{u,v} : Sort u → Sort v → Sort (max u v)`
// and that `prod.{0,0} P Q : Prop` (the `eqmx` unlock) while `prod.{1,1} A B :
// Sort 1` reproduces today's monomorphic type. That was necessary but not
// sufficient for a 0-regression roll-out, because the roll-out also depends on
// the auto-generated RECURSOR `prod.0.rec` — and this is where the plan HIT a
// hard kernel boundary that the feasibility test did not exercise.
//
// # The (former) boundary
//
// Clean's `elim_only_at_universe_zero` (crates/clean-kernel/src/env/elim_analysis.rs)
// classified the POLY `prod` as **Prop-only elimination**:
//
//   * its result sort `max u v` is not PROVABLY nonzero, so the `is_nonzero`
//     gate (elim_analysis.rs:57) does NOT grant unconditional large elimination
//     and the single-constructor subsingleton analysis runs;
//   * `pair`'s two non-parameter fields `a : A`, `b : B` have sorts `u`, `v`
//     (universe PARAMETERS — not syntactically zero, hence treated as "non-Prop"),
//     and they do NOT appear as return-type indices (`prod` has none), so the
//     analysis returned `true` → Prop-only.
//
// Consequently `prod.0.rec` was built with level params `[u, v]` (NO motive
// universe) and its motive was fixed to `… → Sort 0` (Prop) — STRICTER than
// Lean 4 (`PProd.rec.{w,u,v}`) and stricter than real Coq (whose `prod` in
// `Type` projects into `Type`).
//
// # The kernel rule that resolved it (Coq-lane PARAMETRIC SINGLETON ELIMINATION)
//
// `elim_only_at_universe_zero` now grants LARGE elimination, ON THE CUMULATIVE
// (Coq re-verification) LANE, to a single-constructor inductive whose result
// level `R` is not provably nonzero WHEN every constructor field's sort level is
// `≤ R` as a level expression (`Level::is_geq(R, field)` — `u ≤ max(u,v)`,
// `v ≤ max(u,v)`). Pointwise-sound at every instantiation `σ`: if `σ(R) ≥ 1` the
// type is a genuine `Type` (large elim unconditional); if `σ(R) = 0` then every
// field level (`≤ R`) is also `0`, so the type is a single-ctor all-`Prop`-field
// SUBSINGLETON (Coq's singleton-elimination class, identical to `And`). This is
// exactly Coq's rule for template-polymorphic `prod`/`sum`/`sigT`.
//
// So `prod.0.rec` now carries level params `[motive, u, v]` on the cumulative
// lane and a `prod` projection into a `Type`-valued motive (`fst`) kernel-checks
// — WITHOUT regressing `eqmx` (`prod.{0,0} P Q : Prop` still checks). The rule is
// Coq-lane gated: the Lean/olean lane keeps the Prop-only `[u, v]` recursor, so
// no `.olean` recursor expectation changes.
//
// This test is the durable, kernel-checked record of that resolution: the poly
// recursor's large elimination, the `fst`-into-`Type` acceptance, the retained
// `eqmx` gain, the Lean-lane control, and the negative controls that keep
// witness extraction and multi-constructor families Prop-only.

use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl, InductiveType, Level,
    Name,
};

const PROD: &str = "Coq.Init.Datatypes.prod.0";
const PAIR: &str = "Coq.Init.Datatypes.pair";
const REC: &str = "Coq.Init.Datatypes.prod.0.rec";

fn n(s: &str) -> Name {
    Name::from_string(s)
}

/// `prod.{u,v} : Sort u → Sort v → Sort (max u v)` with
/// `pair.{u,v} : (A : Sort u)(B : Sort v)(a : A)(b : B) → prod.{u,v} A B`.
fn poly_prod_decl() -> InductiveDecl {
    let (u, v) = (Name::from_string("u"), Name::from_string("v"));
    let (ul, vl) = (Level::param(u.clone()), Level::param(v.clone()));
    let (sort_u, sort_v) = (Expr::sort(ul.clone()), Expr::sort(vl.clone()));
    let sort_max = Expr::sort(Level::max(ul.clone(), vl.clone()));
    let prod = Name::from_string(PROD);
    let ind_ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(BinderInfo::Default, sort_v.clone(), sort_max),
    );
    let prod_ab = Expr::app(
        Expr::app(
            Expr::const_(prod.clone(), vec![ul.clone(), vl.clone()]),
            Expr::bvar(3),
        ),
        Expr::bvar(2),
    );
    let ctor_ty = Expr::pi(
        BinderInfo::Default,
        sort_u,
        Expr::pi(
            BinderInfo::Default,
            sort_v,
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), prod_ab),
            ),
        ),
    );
    InductiveDecl {
        level_params: vec![u, v],
        num_params: 2,
        types: vec![InductiveType {
            name: prod,
            type_: ind_ty,
            constructors: vec![Constructor {
                name: Name::from_string(PAIR),
                type_: ctor_ty,
            }],
        }],
    }
}

fn one() -> Level {
    Level::succ(Level::Zero)
}

fn prod_at(lvls: Vec<Level>, a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(Expr::const_(Name::from_string(PROD), lvls), a), b)
}

/// On the CUMULATIVE (Coq re-verification) lane the poly `prod` recursor is now
/// LARGE-eliminating: it carries THREE level params `[motive, u, v]` (the motive
/// universe prepended to the inductive's own `[u, v]`). This is the parametric
/// singleton elimination unlock — every `pair` field sort (`u`, `v`) is `≤` the
/// result `max u v`, so at `u = v = 0` the type is a subsingleton and large
/// elimination is sound, while for `u, v > 0` it is a genuine `Type`.
#[test]
fn poly_prod_recursor_large_eliminates_three_level_params_cumulative() {
    let mut env = Environment::with_prelude();
    env.set_cumulative(true); // the Coq re-verification lane
    env.add_inductive(poly_prod_decl())
        .expect("kernel accepts poly prod TYPE (feasibility)");
    let info = env
        .get_const(&Name::from_string(REC))
        .expect("prod.0.rec generated");
    assert_eq!(
        info.level_params.len(),
        3,
        "poly prod.0.rec must large-eliminate on the cumulative lane (level \
         params [motive,u,v]); a Prop-only recursor would have 2 ([u,v]). Got {:?}",
        info.level_params
    );
}

/// LEAN-LANE CONTROL: WITHOUT the environment cumulativity flag (the Lean/olean
/// re-verification lane), the parametric-singleton rule is a no-op, so the poly
/// `prod` recursor stays Prop-only with exactly the inductive's two level params
/// `[u, v]` and NO motive universe. Flipping this on the Lean lane would diverge
/// from `.olean` recursor expectations, which is why the rule is Coq-lane gated.
#[test]
fn poly_prod_recursor_is_prop_only_on_lean_lane() {
    let mut env = Environment::with_prelude();
    // No `set_cumulative(true)` — the Lean/olean lane.
    env.add_inductive(poly_prod_decl())
        .expect("kernel accepts poly prod TYPE on the Lean lane too");
    let info = env
        .get_const(&Name::from_string(REC))
        .expect("prod.0.rec generated");
    assert_eq!(
        info.level_params.len(),
        2,
        "on the Lean lane the poly prod.0.rec must stay Prop-only (level params \
         [u,v]); got {:?}",
        info.level_params
    );
}

/// Through the REAL `add_decl` path (full check, the corpus re-verification
/// path) on the cumulative lane: a `prod` projection into a `Type`-valued motive
/// (`fst`) is now ACCEPTED by the large-eliminating recursor, AND the `eqmx`
/// unlock `prod.{0,0} P Q : Prop` remains accepted. This is the 0-regression
/// resolution: `fst`/`snd`/`prod_rect`/`prod_rec` project into `Type` again,
/// while the genuine `eqmx` gain is retained.
#[test]
fn prod_projection_into_type_and_prop_prod_both_accepted_cumulative() {
    let mut env = Environment::with_prelude();
    env.set_cumulative(true);
    env.add_inductive(poly_prod_decl()).expect("add poly prod");

    // fst : Π (A B : Type)(p : prod.{1,1} A B). A
    //     := λ A B p. prod.rec.{1,1,1} A B (λ_:prod A B => A) (λ a b => a) p
    // de Bruijn under λA λB λp:  A = 2, B = 1, p = 0.
    let fst_ty = Expr::pi(
        BinderInfo::Default,
        Expr::sort(one()),
        Expr::pi(
            BinderInfo::Default,
            Expr::sort(one()),
            Expr::pi(
                BinderInfo::Default,
                prod_at(vec![one(), one()], Expr::bvar(1), Expr::bvar(0)),
                Expr::bvar(2),
            ),
        ),
    );
    let motive = Expr::lam(
        BinderInfo::Default,
        prod_at(vec![one(), one()], Expr::bvar(2), Expr::bvar(1)),
        Expr::bvar(3), // returns A (Type-valued) — needs a large-elim recursor
    );
    let minor = Expr::lam(
        BinderInfo::Default,
        Expr::bvar(2),                                                // a : A
        Expr::lam(BinderInfo::Default, Expr::bvar(2), Expr::bvar(1)), // b : B, return a
    );
    // The large-elim recursor carries THREE levels [motive, u, v]; the motive
    // returns A at Sort 1, so the instance is prod.rec.{1,1,1}.
    let rec_app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string(REC), vec![one(), one(), one()]),
                        Expr::bvar(2),
                    ),
                    Expr::bvar(1),
                ),
                motive,
            ),
            minor,
        ),
        Expr::bvar(0),
    );
    let fst_val = Expr::lam(
        BinderInfo::Default,
        Expr::sort(one()),
        Expr::lam(
            BinderInfo::Default,
            Expr::sort(one()),
            Expr::lam(
                BinderInfo::Default,
                prod_at(vec![one(), one()], Expr::bvar(1), Expr::bvar(0)),
                rec_app,
            ),
        ),
    );
    let fst_res = env.add_decl(Declaration::Definition {
        name: Name::from_string("fst_into_type"),
        level_params: vec![],
        type_: fst_ty,
        value: fst_val,
        is_reducible: false,
    });
    assert!(
        fst_res.is_ok(),
        "RESOLVED: prod projection into a Type motive must be ACCEPTED by the \
         large-eliminating poly-prod recursor on the cumulative lane (fst/snd/\
         prod_rect/prod_rec re-verify). Unexpectedly rejected: {fst_res:?}"
    );

    // eqmx unlock: E : Prop := prod.{0,0} P Q  (P Q : Prop).
    for name in ["P", "Q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::sort(Level::Zero),
        })
        .expect("seed Prop");
    }
    let eqmx_res = env.add_decl(Declaration::Definition {
        name: Name::from_string("eqmx_shape"),
        level_params: vec![],
        type_: Expr::sort(Level::Zero), // : Prop
        value: prod_at(
            vec![Level::Zero, Level::Zero],
            Expr::const_(Name::from_string("P"), vec![]),
            Expr::const_(Name::from_string("Q"), vec![]),
        ),
        is_reducible: false,
    });
    assert!(
        eqmx_res.is_ok(),
        "the eqmx unlock (prod.{{0,0}} P Q : Prop) must STILL be ACCEPTED: {eqmx_res:?}"
    );
}

/// NEGATIVE CONTROL (witness extraction stays disabled): a single-constructor
/// `Prop` inductive with a non-`Prop` field that is NOT a result index
/// (`exn.mk : (w : Nat) → exn`, `exn : Prop`) must stay Prop-only-eliminating
/// EVEN on the cumulative lane. Here the result `R = Prop (0)` but the field
/// `Nat` sits at level `1`, and `Level::is_geq(0, 1)` is false, so the
/// parametric singleton rule does NOT fire — it falls through to the [R1]
/// index analysis and keeps the recursor Prop-only (0 level params).
///
/// (This — a `Prop` result with a strictly-larger field via Prop's
/// impredicativity — is the only shape where a well-formed single-constructor
/// inductive can have a field level not `≤ R`: for a non-`Prop` result `R` the
/// inductive's universe constraint already forces `R ≥` every field level, so
/// the rule's premise holds automatically there.)
#[test]
fn witness_singleton_stays_prop_only_cumulative() {
    let mut env = Environment::with_prelude();
    env.set_cumulative(true);
    let exn = n("BoundaryExn");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: exn.clone(),
            type_: Expr::sort(Level::Zero), // : Prop
            constructors: vec![Constructor {
                name: n("BoundaryExn.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    Expr::const_(n("Nat"), vec![]),
                    Expr::const_(exn.clone(), vec![]),
                ),
            }],
        }],
    })
    .expect("witness singleton must replay on the cumulative lane");
    let info = env
        .get_const(&n("BoundaryExn.rec"))
        .expect("recursor generated");
    assert_eq!(
        info.level_params.len(),
        0,
        "a non-Prop non-index field keeps the singleton Prop-only — witness \
         extraction must NOT be enabled by the parametric singleton rule; got {:?}",
        info.level_params
    );
}

/// NEGATIVE CONTROL (multi-constructor stays Prop-only): a two-constructor
/// `Prop` inductive must stay Prop-only-eliminating on the cumulative lane. The
/// multi-constructor gate short-circuits BEFORE the parametric singleton rule
/// (which is single-constructor-only), so the recursor carries 0 level params.
#[test]
fn multi_ctor_prop_stays_prop_only_cumulative() {
    let mut env = Environment::with_prelude();
    env.set_cumulative(true);
    let or = n("BoundaryOr");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: or.clone(),
            type_: Expr::sort(Level::Zero), // : Prop
            constructors: vec![
                Constructor {
                    name: n("BoundaryOr.introl"),
                    type_: Expr::const_(or.clone(), vec![]),
                },
                Constructor {
                    name: n("BoundaryOr.intror"),
                    type_: Expr::const_(or.clone(), vec![]),
                },
            ],
        }],
    })
    .expect("multi-ctor Prop must replay on the cumulative lane");
    let info = env
        .get_const(&n("BoundaryOr.rec"))
        .expect("recursor generated");
    assert_eq!(
        info.level_params.len(),
        0,
        "a multi-constructor Prop inductive stays Prop-only (the parametric \
         singleton rule is single-constructor only); got {:?}",
        info.level_params
    );
}
