// Feasibility + boundary record for the Coq TEMPLATE-POLYMORPHISM-INTO-PROP
// unlock (`Coq.Init.Datatypes.prod`, the mxalgebra/`eqmx` cluster).
//
// # What this pins
//
// Coq's `prod` is TEMPLATE-polymorphic: `prod P Q` collapses to `Prop` when
// `P Q : Prop` (this is how `mathcomp.algebra.mxalgebra.eqmx :=
// λ …, Datatypes.prod P Q : … -> Prop` typechecks in Coq). The Clean Coq
// importer currently renders `prod` MONOMORPHICALLY at `Sort 1 → Sort 1 →
// Sort 1` (the synthetic `mathverse_template_collapse` output level floors to
// `Type 1`), so `prod P Q` infers `Sort 1` and REJECTS against a declared
// `Prop` codomain — `eqmx` (and the ~245 NOT-KV mathcomp constants that
// reference it) become value-less UNIVERSE_RECON stand-ins that conversion
// cannot δ-unfold through.
//
// The faithful fix is to import `prod` UNIVERSE-POLYMORPHICALLY as
// `prod.{u,v} : Sort u → Sort v → Sort (max u v)` so `prod.{0,0} P Q : Prop`.
// This test is the DURABLE, kernel-checked record that the kernel FULLY
// supports the required shape, and it brackets the current-vs-target behavior:
//
//   (before) monomorphic `prod : Sort 1 → Sort 1 → Sort 1`:
//            `prod P Q` (P Q : Prop) does NOT check at `Prop`  — the boundary.
//   (target) poly `prod.{u,v} : Sort u → Sort v → Sort (max u v)`:
//            `prod.{0,0} P Q : Prop`                            — the unlock;
//            `prod.{1,1} A B : Sort 1`  reproduces the OLD monomorphic type
//            EXACTLY (a currently-`KernelVerified` `prod` use re-checks
//            identically once its references carry the `{1,1}` instance).
//
// # Why the corpus-wide roll-out is staged (not landed in this test)
//
// `prod` is referenced corpus-wide (~167 k Ind/Construct references across 249
// files; ~6.7 k `Case`-on-`prod` recursor sites across 161 files, many inside
// currently-`KernelVerified` constants such as `fst`/`snd`/`prod_rect`/
// `prod_rec`/`prod_ind`).
//
// RESOLVED (see `coq_template_poly_prod_recursor_boundary.rs`): the poly `prod`
// recursor's elimination strength was the last blocker. `elim_only_at_universe_zero`
// classified the poly `prod` as Prop-ONLY (result `max u v` not provably nonzero;
// `pair`'s fields `a:A`,`b:B` at PARAMETER sorts `u`,`v`, not indices) → a
// two-level `[u, v]` recursor that cannot project into a `Type` motive, so
// `fst`/`snd`/`prod_rect`/`prod_rec` would have regressed. The soundness-sensitive
// KERNEL fix (Coq-lane PARAMETRIC SINGLETON ELIMINATION: single-ctor + every field
// sort `≤` the result level → large elim on the cumulative lane) now builds
// `prod.0.rec` with THREE level params `[motive, u, v]`, restoring `Type`-motive
// projection WITHOUT losing the `eqmx` (`prod.{0,0}`) gain — pointwise-sound at
// every instantiation (a `Type` when `R ≥ 1`, an all-`Prop`-field subsingleton
// when `R = 0`). This test still records the TYPE-level feasibility; the recursor
// resolution lives in the boundary test.

use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl, InductiveType, Level,
    Name, TypeChecker,
};

const PROD: &str = "Coq.Init.Datatypes.prod.0";
const PAIR: &str = "Coq.Init.Datatypes.pair";

/// `prod.{u,v} : Sort u → Sort v → Sort (max u v)`, ctor
/// `pair.{u,v} : (A : Sort u) → (B : Sort v) → A → B → prod.{u,v} A B`.
fn poly_prod_decl() -> InductiveDecl {
    let (u, v) = (Name::from_string("u"), Name::from_string("v"));
    let (ul, vl) = (Level::param(u.clone()), Level::param(v.clone()));
    let (sort_u, sort_v) = (Expr::sort(ul.clone()), Expr::sort(vl.clone()));
    let sort_max = Expr::sort(Level::max(ul.clone(), vl.clone()));
    let prod = Name::from_string(PROD);

    // prod : Sort u → Sort v → Sort (max u v)
    let ind_ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(BinderInfo::Default, sort_v.clone(), sort_max),
    );

    // pair : (A : Sort u) → (B : Sort v) → A → B → prod.{u,v} A B
    // de Bruijn (all four bound): A=3, B=2, a=1, b=0.
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
                Expr::bvar(1), // a : A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1), // b : B
                    prod_ab,
                ),
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

/// Monomorphic `prod : Sort 1 → Sort 1 → Sort 1` — the importer's CURRENT
/// (template-collapsed) rendering, used to pin the pre-fix boundary.
fn mono_prod_decl() -> InductiveDecl {
    let s1 = Expr::sort(Level::succ(Level::Zero));
    let prod = Name::from_string(PROD);
    let prod_ab = Expr::app(
        Expr::app(Expr::const_(prod.clone(), vec![]), Expr::bvar(3)),
        Expr::bvar(2),
    );
    let ctor_ty = Expr::pi(
        BinderInfo::Default,
        s1.clone(),
        Expr::pi(
            BinderInfo::Default,
            s1.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), prod_ab),
            ),
        ),
    );
    InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: prod,
            type_: Expr::pi(
                BinderInfo::Default,
                s1.clone(),
                Expr::pi(BinderInfo::Default, s1.clone(), s1),
            ),
            constructors: vec![Constructor {
                name: Name::from_string(PAIR),
                type_: ctor_ty,
            }],
        }],
    }
}

fn seed_operands(env: &mut Environment) {
    // P, Q : Prop  and  A, B : Sort 1 (Set/Type-valued types).
    for n in ["P", "Q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(n),
            level_params: vec![],
            type_: Expr::sort(Level::Zero),
        })
        .expect("seed Prop");
    }
    for n in ["A", "B"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(n),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::Zero)),
        })
        .expect("seed Type");
    }
}

fn cst(n: &str) -> Expr {
    Expr::const_(Name::from_string(n), vec![])
}

/// TARGET: the kernel accepts poly `prod` and `prod.{0,0} P Q : Prop`
/// (the `eqmx` unlock), while `prod.{1,1} A B : Sort 1` reproduces the old
/// monomorphic type. Negative control: `prod.{1,1} P Q` must NOT check at Prop.
#[test]
fn poly_prod_collapses_to_prop_and_reproduces_mono_at_one_one() {
    let mut env = Environment::with_prelude();
    env.add_inductive(poly_prod_decl())
        .expect("kernel must accept prod.{u,v} : Sort u -> Sort v -> Sort (max u v)");
    seed_operands(&mut env);
    let tc = TypeChecker::new(&env);

    // (unlock) prod.{0,0} P Q : Prop — exactly the eqmx codomain.
    let prod00 = Expr::const_(Name::from_string(PROD), vec![Level::Zero, Level::Zero]);
    let app00 = Expr::app(Expr::app(prod00, cst("P")), cst("Q"));
    assert_eq!(
        tc.infer_type(&app00).expect("prod.{0,0} P Q typechecks"),
        Expr::sort(Level::Zero),
        "prod.{{0,0}} P Q must infer Prop (Sort 0)"
    );
    tc.check_type(&app00, &Expr::sort(Level::Zero))
        .expect("prod.{0,0} P Q must check at Prop (the eqmx unlock)");

    // (mono reproduction) prod.{1,1} A B : Sort 1 — byte-identical to today's
    // monomorphic prod, so a currently-KV prod use re-checks unchanged.
    let one = Level::succ(Level::Zero);
    let prod11 = Expr::const_(Name::from_string(PROD), vec![one.clone(), one.clone()]);
    let app11 = Expr::app(Expr::app(prod11, cst("A")), cst("B"));
    assert_eq!(
        tc.infer_type(&app11).expect("prod.{1,1} A B typechecks"),
        Expr::sort(one.clone()),
        "prod.{{1,1}} A B must infer Sort 1 (the old monomorphic type)"
    );

    // (negative control) prod.{1,1} P Q must NOT check at Prop: P : Prop cannot
    // inhabit the Sort-1 argument binder, so a wrong instance is a loud reject.
    let prod11pq = Expr::const_(Name::from_string(PROD), vec![one.clone(), one]);
    let app11pq = Expr::app(Expr::app(prod11pq, cst("P")), cst("Q"));
    assert!(
        tc.check_type(&app11pq, &Expr::sort(Level::Zero)).is_err(),
        "negative control: prod.{{1,1}} P Q must REJECT at Prop"
    );
}

/// BOUNDARY (pre-fix): with the importer's CURRENT monomorphic
/// `prod : Sort 1 → Sort 1 → Sort 1`, `prod P Q` (P Q : Prop) does NOT check at
/// `Prop` — the exact rejection that makes `eqmx` a value-less stand-in today.
#[test]
fn mono_prod_rejects_prod_of_props_at_prop_the_current_boundary() {
    let mut env = Environment::with_prelude();
    env.add_inductive(mono_prod_decl())
        .expect("kernel accepts monomorphic prod");
    seed_operands(&mut env);
    let tc = TypeChecker::new(&env);

    // prod P Q (monomorphic, no level instance). By cumulativity P,Q : Prop lift
    // into the Sort-1 argument binders, so the application is well-typed — but at
    // the monomorphic result sort Sort 1, NOT Prop.
    let prod_pq = Expr::app(
        Expr::app(Expr::const_(Name::from_string(PROD), vec![]), cst("P")),
        cst("Q"),
    );
    assert_eq!(
        tc.infer_type(&prod_pq).expect("mono prod P Q typechecks"),
        Expr::sort(Level::succ(Level::Zero)),
        "monomorphic prod P Q infers Sort 1"
    );
    assert!(
        tc.check_type(&prod_pq, &Expr::sort(Level::Zero)).is_err(),
        "boundary: monomorphic prod P Q must REJECT against a Prop codomain \
         (this is why eqmx becomes a value-less UNIVERSE_RECON stand-in)"
    );
}
