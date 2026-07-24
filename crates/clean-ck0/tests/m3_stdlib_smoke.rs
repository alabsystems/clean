// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ck0 standard-library smoke test (the "root of trust for math" leg).
//!
//! This drives REAL Lean-shaped standard declarations through ck0's actual
//! M0–M3 machinery — `add_inductive` (+ derived recursors), `Term::validate`
//! (the chokepoint), and `infer`/`check` — and confirms ck0 admits + type-checks
//! real theorems. Unlike the M2/M3 fixtures, the goal here is end-to-end
//! realistic content: the standard Init inductives with their faithful Lean
//! signatures, and ~10 representative Init-shaped theorems whose *types* infer to
//! a `Sort` and whose *proof terms* `check` against those types.
//!
//! Each inductive is built through the validation chokepoint against a bootstrap
//! env that knows the relevant names, then admitted into a fresh `MinimalEnv`
//! exactly at the producer→kernel boundary. Negative controls confirm that
//! acceptance is meaningful: an ill-typed proof term (`Eq.refl` at the wrong
//! type, `And.intro` under-applied) is REJECTED by `check`.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, Budget, Constructor, Env, InductiveDecl, MinimalEnv, Name, RawExpr, RawLevel,
    Term,
};

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

// ---- RawExpr builders ----

fn r_sort(level: u32) -> RawExpr {
    let mut l = RawLevel::Zero;
    for _ in 0..level {
        l = RawLevel::Succ(Box::new(l));
    }
    RawExpr::Sort(l)
}
fn r_prop() -> RawExpr {
    RawExpr::Sort(RawLevel::Zero)
}
fn r_sort_param(i: u32) -> RawExpr {
    RawExpr::Sort(RawLevel::Param(i))
}
fn r_const(name: &str) -> RawExpr {
    RawExpr::Const(n(name), vec![])
}
fn r_const_p(name: &str, levels: Vec<RawLevel>) -> RawExpr {
    RawExpr::Const(n(name), levels)
}
fn r_app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}
fn r_apps(f: RawExpr, args: Vec<RawExpr>) -> RawExpr {
    args.into_iter().fold(f, r_app)
}
fn r_pi(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(dom), Box::new(codom))
}
fn r_pi_i(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Implicit, Box::new(dom), Box::new(codom))
}
fn r_lam(dom: RawExpr, body: RawExpr) -> RawExpr {
    RawExpr::Lam(BinderInfo::Default, Box::new(dom), Box::new(body))
}
fn r_bvar(i: u32) -> RawExpr {
    RawExpr::BVar(i)
}
fn lparam(i: u32) -> RawLevel {
    RawLevel::Param(i)
}
fn lsucc(l: RawLevel) -> RawLevel {
    RawLevel::Succ(Box::new(l))
}

fn boot(decls: &[(&str, u32)]) -> MinimalEnv {
    let mut env = MinimalEnv::new();
    for (nm, nlp) in decls {
        env = env.with_const(n(nm), *nlp);
    }
    env
}
fn vlvl(env: &dyn Env, raw: &RawExpr, level_arity: u32) -> Term {
    Term::validate(env, raw, 0, level_arity).expect("term validates")
}

// ===========================================================================
// The standard Init inductives, with their REAL Lean signatures.
// ===========================================================================

/// `Bool : Type` with `false : Bool`, `true : Bool`.
fn bool_decl() -> InductiveDecl {
    let b = boot(&[("Bool", 0), ("Bool.false", 0), ("Bool.true", 0)]);
    InductiveDecl {
        name: n("Bool"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_sort(1), 0),
        constructors: vec![
            Constructor {
                name: n("Bool.false"),
                type_: vlvl(&b, &r_const("Bool"), 0),
            },
            Constructor {
                name: n("Bool.true"),
                type_: vlvl(&b, &r_const("Bool"), 0),
            },
        ],
    }
}

/// `Nat : Type` with `zero : Nat`, `succ : Nat -> Nat`.
fn nat_decl() -> InductiveDecl {
    let b = boot(&[("Nat", 0), ("Nat.zero", 0), ("Nat.succ", 0)]);
    InductiveDecl {
        name: n("Nat"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_sort(1), 0),
        constructors: vec![
            Constructor {
                name: n("Nat.zero"),
                type_: vlvl(&b, &r_const("Nat"), 0),
            },
            Constructor {
                name: n("Nat.succ"),
                type_: vlvl(&b, &r_pi(r_const("Nat"), r_const("Nat")), 0),
            },
        ],
    }
}

/// `List.{u} (A : Type u) : Type u` with `nil : List A`, `cons : A -> List A ->
/// List A`. num_params = 1.
fn list_decl() -> InductiveDecl {
    let b = boot(&[("List", 1), ("List.nil", 1), ("List.cons", 1)]);
    let ty = vlvl(&b, &r_pi(r_sort_param(0), r_sort_param(0)), 1);
    let nil_ty = r_pi(
        r_sort_param(0),
        r_app(r_const_p("List", vec![lparam(0)]), r_bvar(0)),
    );
    let list_a = |db: u32| r_app(r_const_p("List", vec![lparam(0)]), r_bvar(db));
    let cons_ty = r_pi(r_sort_param(0), r_pi(r_bvar(0), r_pi(list_a(1), list_a(2))));
    InductiveDecl {
        name: n("List"),
        num_level_params: 1,
        num_params: 1,
        type_: ty,
        constructors: vec![
            Constructor {
                name: n("List.nil"),
                type_: vlvl(&b, &nil_ty, 1),
            },
            Constructor {
                name: n("List.cons"),
                type_: vlvl(&b, &cons_ty, 1),
            },
        ],
    }
}

/// `Eq.{u} {A : Sort u} (a : A) : A -> Prop` with `refl (a) : Eq a a`.
/// Built with num_params = 2 (A and a), matching the M2 fixture.
fn eq_decl() -> InductiveDecl {
    let b = boot(&[("Eq", 1), ("Eq.refl", 1)]);
    let ty = r_pi(r_sort_param(0), r_pi(r_bvar(0), r_pi(r_bvar(1), r_prop())));
    let refl_ty = r_pi(
        r_sort_param(0),
        r_pi(
            r_bvar(0),
            r_apps(
                r_const_p("Eq", vec![lparam(0)]),
                vec![r_bvar(1), r_bvar(0), r_bvar(0)],
            ),
        ),
    );
    InductiveDecl {
        name: n("Eq"),
        num_level_params: 1,
        num_params: 2,
        type_: vlvl(&b, &ty, 1),
        constructors: vec![Constructor {
            name: n("Eq.refl"),
            type_: vlvl(&b, &refl_ty, 1),
        }],
    }
}

/// `And (a b : Prop) : Prop` with `intro : a -> b -> And a b`. num_params = 2.
fn and_decl() -> InductiveDecl {
    let b = boot(&[("And", 0), ("And.intro", 0)]);
    let ty = vlvl(&b, &r_pi(r_prop(), r_pi(r_prop(), r_prop())), 0);
    let intro_ty = r_pi(
        r_prop(),
        r_pi(
            r_prop(),
            r_pi(
                r_bvar(1),
                r_pi(
                    r_bvar(1),
                    r_apps(r_const("And"), vec![r_bvar(3), r_bvar(2)]),
                ),
            ),
        ),
    );
    InductiveDecl {
        name: n("And"),
        num_level_params: 0,
        num_params: 2,
        type_: ty,
        constructors: vec![Constructor {
            name: n("And.intro"),
            type_: vlvl(&b, &intro_ty, 0),
        }],
    }
}

/// `Or (a b : Prop) : Prop` with `inl : a -> Or a b`, `inr : b -> Or a b`.
fn or_decl() -> InductiveDecl {
    let b = boot(&[("Or", 0), ("Or.inl", 0), ("Or.inr", 0)]);
    let ty = vlvl(&b, &r_pi(r_prop(), r_pi(r_prop(), r_prop())), 0);
    let inl_ty = r_pi(
        r_prop(),
        r_pi(
            r_prop(),
            r_pi(r_bvar(1), r_apps(r_const("Or"), vec![r_bvar(2), r_bvar(1)])),
        ),
    );
    let inr_ty = r_pi(
        r_prop(),
        r_pi(
            r_prop(),
            r_pi(r_bvar(0), r_apps(r_const("Or"), vec![r_bvar(2), r_bvar(1)])),
        ),
    );
    InductiveDecl {
        name: n("Or"),
        num_level_params: 0,
        num_params: 2,
        type_: ty,
        constructors: vec![
            Constructor {
                name: n("Or.inl"),
                type_: vlvl(&b, &inl_ty, 0),
            },
            Constructor {
                name: n("Or.inr"),
                type_: vlvl(&b, &inr_ty, 0),
            },
        ],
    }
}

/// `False : Prop` (no constructors).
fn false_decl() -> InductiveDecl {
    let b = boot(&[("False", 0)]);
    InductiveDecl {
        name: n("False"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_prop(), 0),
        constructors: vec![],
    }
}

/// `True : Prop` with `intro : True`.
fn true_decl() -> InductiveDecl {
    let b = boot(&[("True", 0), ("True.intro", 0)]);
    InductiveDecl {
        name: n("True"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_prop(), 0),
        constructors: vec![Constructor {
            name: n("True.intro"),
            type_: vlvl(&b, &r_const("True"), 0),
        }],
    }
}

/// `Prod.{u,v} (A : Type u) (B : Type v) : Type (max u v)` with
/// `mk : A -> B -> Prod A B`. num_params = 2, num_level_params = 2.
fn prod_decl() -> InductiveDecl {
    let b = boot(&[("Prod", 2), ("Prod.mk", 2)]);
    // Prod : Type u -> Type v -> Type (max u v)
    let ty = r_pi(
        r_sort_param(0),
        r_pi(
            r_sort_param(1),
            RawExpr::Sort(RawLevel::Max(Box::new(lparam(0)), Box::new(lparam(1)))),
        ),
    );
    // mk : (A : Type u) -> (B : Type v) -> A -> B -> Prod A B
    let mk_ty = r_pi(
        r_sort_param(0),
        r_pi(
            r_sort_param(1),
            r_pi(
                r_bvar(1), // A
                r_pi(
                    r_bvar(1), // B
                    r_apps(
                        r_const_p("Prod", vec![lparam(0), lparam(1)]),
                        vec![r_bvar(3), r_bvar(2)],
                    ),
                ),
            ),
        ),
    );
    InductiveDecl {
        name: n("Prod"),
        num_level_params: 2,
        num_params: 2,
        type_: vlvl(&b, &ty, 2),
        constructors: vec![Constructor {
            name: n("Prod.mk"),
            type_: vlvl(&b, &mk_ty, 2),
        }],
    }
}

// ---------------------------------------------------------------------------
// Admission harness: build a single env with the whole stdlib admitted.
// ---------------------------------------------------------------------------

/// Admit Bool, Nat, List, Eq, And, Or, False, True, Prod into one env. Returns
/// the env; panics with a clear message if any admission fails (the test
/// asserts each admits).
fn stdlib_env() -> MinimalEnv {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, bool_decl()).expect("Bool admits");
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    add_inductive(&mut env, list_decl()).expect("List admits");
    add_inductive(&mut env, eq_decl()).expect("Eq admits");
    add_inductive(&mut env, and_decl()).expect("And admits");
    add_inductive(&mut env, or_decl()).expect("Or admits");
    add_inductive(&mut env, false_decl()).expect("False admits");
    add_inductive(&mut env, true_decl()).expect("True admits");
    add_inductive(&mut env, prod_decl()).expect("Prod admits");
    env
}

/// A theorem's TYPE must infer to a `Sort`, and its PROOF term must `check`
/// against that type. Returns on success; panics with detail on failure.
fn admit_theorem(env: &MinimalEnv, ty_raw: &RawExpr, proof_raw: &RawExpr, level_arity: u32) {
    let ty = Term::validate(env, ty_raw, 0, level_arity).expect("theorem type validates");
    let mut budget = Budget::default_budget();
    // The type itself is a well-formed type (its type is a Sort).
    clean_ck0::infer_sort_in_context(env, &[], &ty, &mut budget)
        .expect("theorem type infers to a Sort");
    let proof = Term::validate(env, proof_raw, 0, level_arity).expect("proof term validates");
    clean_ck0::check(env, &proof, &ty, &mut budget).expect("proof checks against the theorem type");
}

// ===========================================================================
// Test 1: every standard inductive admits and its recursor kernel-checks.
// ===========================================================================

#[test]
fn test_stdlib_inductives_admit_and_recursors_kernel_check() {
    let env = stdlib_env();
    for ind in [
        "Bool", "Nat", "List", "Eq", "And", "Or", "False", "True", "Prod",
    ] {
        let rec_ty = env
            .recursor_type(&n(ind))
            .unwrap_or_else(|| panic!("{ind}.rec type stored"));
        let mut budget = Budget::default_budget();
        clean_ck0::infer_sort_in_context(&env, &[], &rec_ty, &mut budget)
            .unwrap_or_else(|e| panic!("{ind}.rec kernel-checks: {e:?}"));
    }
}

// ===========================================================================
// Test 2: representative Init theorems — TYPE infers, PROOF checks.
// ===========================================================================

// --- Eq.refl as a proof: `(refl : Eq Nat.zero Nat.zero)`. -------------------
#[test]
fn test_eq_refl_inhabitant_checks() {
    let env = stdlib_env();
    // type: Eq.{1} Nat Nat.zero Nat.zero
    let ty = r_apps(
        r_const_p("Eq", vec![lsucc(RawLevel::Zero)]),
        vec![r_const("Nat"), r_const("Nat.zero"), r_const("Nat.zero")],
    );
    // proof: Eq.refl.{1} Nat Nat.zero
    let proof = r_apps(
        r_const_p("Eq.refl", vec![lsucc(RawLevel::Zero)]),
        vec![r_const("Nat"), r_const("Nat.zero")],
    );
    admit_theorem(&env, &ty, &proof, 0);
}

// --- Eq.symm : {A} -> {a b : A} -> a = b -> b = a --------------------------
// proof = fun A a b h => Eq.rec (motive := fun x _ => x = a) (Eq.refl a) h
#[test]
fn test_eq_symm_checks() {
    let env = stdlib_env();
    // We work at a fixed universe param u (level_arity = 1), A : Sort u.
    let eq = |a: RawExpr, x: RawExpr, y: RawExpr| {
        r_apps(r_const_p("Eq", vec![lparam(0)]), vec![a, x, y])
    };
    // Theorem TYPE: {A : Sort u} -> {a b : A} -> Eq A a b -> Eq A b a
    let ty = r_pi_i(
        r_sort_param(0), // A           bvar3 inside body
        r_pi_i(
            r_bvar(0), // a : A         bvar2
            r_pi_i(
                r_bvar(1), // b : A     bvar1
                r_pi(
                    eq(r_bvar(2), r_bvar(1), r_bvar(0)), // a = b   (h : bvar0)
                    eq(r_bvar(3), r_bvar(1), r_bvar(2)), // b = a
                ),
            ),
        ),
    );
    // PROOF: fun (A) (a) (b) (h : Eq A a b) =>
    //   Eq.rec (motive := fun (x : A) (_ : Eq A a x) => Eq A x a) (Eq.refl A a) h
    // Eq.rec is large-elim: Elim level vector = [motive_level, ind_level].
    // motive lands in Prop (Eq .. : Prop) so motive_level = Sort 0? The motive's
    // result is `Sort u`-typed? Eq A x a : Prop, so motive : A -> Eq A a x ->
    // Prop, motive_level = 0 (Prop). ind_level = u (Param 0).
    let elim = RawExpr::Elim(n("Eq"), RawLevel::Zero, vec![lparam(0)]);
    // motive = fun (x : A) (heq : Eq A a x) => Eq A x a.
    // Inside fun A a b h, the de Bruijn for A=3, a=2, b=1, h=0 at the motive site;
    // but Eq.rec's motive binds x then heq, so within motive body:
    //   x = bvar1, heq = bvar0, and outer A=5, a=4, b=3, h=2.
    let motive = r_lam(
        r_bvar(3), // x : A   (A is bvar3 at this depth: A a b h)
        r_lam(
            eq(r_bvar(4), r_bvar(3), r_bvar(0)), // Eq A a x
            eq(r_bvar(5), r_bvar(1), r_bvar(4)), // Eq A x a
        ),
    );
    // refl a : Eq A a a  — the minor premise (motive a (refl a) reduces to Eq A a a)
    let refl_a = r_apps(
        r_const_p("Eq.refl", vec![lparam(0)]),
        vec![r_bvar(3), r_bvar(2)], // A, a
    );
    // Eq.rec takes: motive, then the single minor (for refl), then A, a (params),
    // then index b, then major h. Built recursor telescope:
    //   {motive} -> (minor : motive a (Eq.refl a)) -> ... but params/indices
    //   precede. We rely on the stored recursor type's arg order; construct the
    //   application as Elim motive minor <indices/major> per Lean Eq.rec:
    //   @Eq.rec.{u_motive u} A a motive (refl_minor) b h
    // Eq has num_params=2 (A,a), num_indices=1 (b). Lean order:
    //   Eq.rec : {A a} (motive : (x:A) -> a = x -> Sort) -> motive a rfl ->
    //            {b : A} -> (h : a = b) -> motive b h
    let body = r_apps(
        elim,
        vec![
            r_bvar(3), // A
            r_bvar(2), // a
            motive,    // motive
            refl_a,    // minor: motive a rfl
            r_bvar(1), // b (index)
            r_bvar(0), // h (major)
        ],
    );
    let proof = r_lam(
        r_sort_param(0), // A
        r_lam(
            r_bvar(0), // a : A
            r_lam(
                r_bvar(1),                                        // b : A
                r_lam(eq(r_bvar(2), r_bvar(1), r_bvar(0)), body), // h : Eq A a b
            ),
        ),
    );
    admit_theorem(&env, &ty, &proof, 1);
}

// --- Eq.trans : {A} {a b c : A} -> a = b -> b = c -> a = c -----------------
// proof = fun A a b c h1 h2 =>
//   Eq.rec (motive := fun x _ => Eq A a x) h1 h2     (recursing on h2 : b = c)
#[test]
fn test_eq_trans_checks() {
    let env = stdlib_env();
    let eq = |a: RawExpr, x: RawExpr, y: RawExpr| {
        r_apps(r_const_p("Eq", vec![lparam(0)]), vec![a, x, y])
    };
    // TYPE: {A:Sort u}{a b c:A} -> Eq A a b -> Eq A b c -> Eq A a c
    let ty = r_pi_i(
        r_sort_param(0), // A     (in body A=.. grows)
        r_pi_i(
            r_bvar(0), // a
            r_pi_i(
                r_bvar(1), // b
                r_pi_i(
                    r_bvar(2), // c
                    r_pi(
                        eq(r_bvar(3), r_bvar(2), r_bvar(1)), // a = b
                        r_pi(
                            eq(r_bvar(4), r_bvar(2), r_bvar(1)), // b = c
                            eq(r_bvar(5), r_bvar(4), r_bvar(2)), // a = c
                        ),
                    ),
                ),
            ),
        ),
    );
    // PROOF: depth in body [A,a,b,c,h1,h2]: A=5,a=4,b=3,c=2,h1=1,h2=0.
    // Eq.rec recurses on h2 : Eq A b c. Eq.rec params: A, b. motive over (x, b=x).
    //   motive = fun (x:A) (_:Eq A b x) => Eq A a x.
    //   inside motive body: x=bvar1, the eq-proof=bvar0; outer A=7,a=6,b=5,c=4,...
    let elim = RawExpr::Elim(n("Eq"), RawLevel::Zero, vec![lparam(0)]);
    let motive = r_lam(
        r_bvar(5), // x : A   (A is bvar5 at this depth)
        r_lam(
            eq(r_bvar(6), r_bvar(4), r_bvar(0)), // Eq A b x
            eq(r_bvar(7), r_bvar(6), r_bvar(1)), // Eq A a x
        ),
    );
    // minor : motive b (Eq.refl b) ≡ Eq A a b  := h1.
    let minor = r_bvar(1); // h1
                           // @Eq.rec A b motive minor c h2.
    let body = r_apps(
        elim,
        vec![
            r_bvar(5), // A
            r_bvar(3), // b   (Eq.rec's `a`-param is `b` here, the recursion base)
            motive,
            minor,
            r_bvar(2), // c (index)
            r_bvar(0), // h2 (major)
        ],
    );
    let proof = r_lam(
        r_sort_param(0),
        r_lam(
            r_bvar(0), // a
            r_lam(
                r_bvar(1), // b
                r_lam(
                    r_bvar(2), // c
                    r_lam(
                        eq(r_bvar(3), r_bvar(2), r_bvar(1)),              // h1 : a = b
                        r_lam(eq(r_bvar(4), r_bvar(2), r_bvar(1)), body), // h2 : b = c
                    ),
                ),
            ),
        ),
    );
    admit_theorem(&env, &ty, &proof, 1);
}

// --- And.intro / And.left / And.right --------------------------------------
#[test]
fn test_and_intro_and_projections_check() {
    let env = stdlib_env();
    // True.intro : True, so we can build And True True.
    // And.intro : (a b : Prop) -> a -> b -> And a b
    // Theorem: And True True, proof And.intro True True True.intro True.intro.
    let and_tt = r_apps(r_const("And"), vec![r_const("True"), r_const("True")]);
    let proof = r_apps(
        r_const("And.intro"),
        vec![
            r_const("True"),
            r_const("True"),
            r_const("True.intro"),
            r_const("True.intro"),
        ],
    );
    admit_theorem(&env, &and_tt, &proof, 0);

    // And.left : {a b : Prop} -> And a b -> a, via And.rec.
    //   fun a b h => And.rec (motive := fun _ => a) (fun (ha:a) (hb:b) => ha) h
    // And is a Prop, single ctor → recursor is Prop-only (small elim). Elim level
    // vector = [ind_levels...] = [] (And has 0 level params), motive into Prop.
    let and_left_ty = r_pi_i(
        r_prop(), // a   bvar2
        r_pi_i(
            r_prop(), // b  bvar1
            r_pi(
                r_apps(r_const("And"), vec![r_bvar(1), r_bvar(0)]), // And a b
                r_bvar(2),                                          // a
            ),
        ),
    );
    // small-elim: Elim head level vector is just the ind levels (none).
    let elim = RawExpr::Elim(n("And"), RawLevel::Zero, vec![]);
    // motive = fun (_ : And a b) => a.  At body depth (a b h): a=2,b=1,h=0.
    let motive = r_lam(
        r_apps(r_const("And"), vec![r_bvar(2), r_bvar(1)]), // And a b
        r_bvar(3),                                          // a
    );
    // minor = fun (ha : a) (hb : b) => ha.
    let minor = r_lam(
        r_bvar(2),                   // ha : a
        r_lam(r_bvar(2), r_bvar(1)), // hb : b => ha
    );
    // And.rec : {a b} (motive : And a b -> Sort) -> ((ha:a)(hb:b)->motive (intro..))
    //   -> (t : And a b) -> motive t.  Lean order: params a b, motive, minor, major.
    let body = r_apps(elim, vec![r_bvar(2), r_bvar(1), motive, minor, r_bvar(0)]);
    let proof = r_lam(
        r_prop(), // a
        r_lam(
            r_prop(), // b
            r_lam(
                r_apps(r_const("And"), vec![r_bvar(1), r_bvar(0)]), // And a b
                body,
            ),
        ),
    );
    admit_theorem(&env, &and_left_ty, &proof, 0);
}

// --- Or.inl as an inhabitant + Or.elim type checks --------------------------
#[test]
fn test_or_inl_inhabitant_and_elim_type_check() {
    let env = stdlib_env();
    // Or.inl True.intro : Or True False  (a=True, b=False, proof of a).
    let or_tf = r_apps(r_const("Or"), vec![r_const("True"), r_const("False")]);
    let proof = r_apps(
        r_const("Or.inl"),
        vec![r_const("True"), r_const("False"), r_const("True.intro")],
    );
    admit_theorem(&env, &or_tf, &proof, 0);

    // Or.elim : {a b c : Prop} -> Or a b -> (a -> c) -> (b -> c) -> c, via Or.rec.
    //   fun a b c h ha hb => Or.rec (motive := fun _ => c) ha hb h
    let or_ab = |x: u32, y: u32| r_apps(r_const("Or"), vec![r_bvar(x), r_bvar(y)]);
    let ty = r_pi_i(
        r_prop(), // a  (depth grows)
        r_pi_i(
            r_prop(), // b
            r_pi_i(
                r_prop(), // c
                r_pi(
                    or_ab(2, 1), // Or a b   (a=2,b=1,c=0)
                    r_pi(
                        r_pi(r_bvar(3), r_bvar(2)), // a -> c
                        r_pi(
                            r_pi(r_bvar(3), r_bvar(3)), // b -> c
                            r_bvar(3),                  // c
                        ),
                    ),
                ),
            ),
        ),
    );
    // proof: fun a b c (h:Or a b) (ha:a->c) (hb:b->c) =>
    //   Or.rec (motive := fun _ => c) ha hb h
    // depth in body: a=5,b=4,c=3,h=2,ha=1,hb=0.
    let elim = RawExpr::Elim(n("Or"), RawLevel::Zero, vec![]);
    let motive = r_lam(
        r_apps(r_const("Or"), vec![r_bvar(5), r_bvar(4)]), // Or a b
        r_bvar(4),                                         // c
    );
    // minor_inl : (ha : a) -> motive (inl ha) = c  := fun (ha:a) => (ha applied? no)
    //   the minor for inl takes the field (ha:a) and returns c: we use the
    //   supplied `ha : a -> c` applied to the field.
    let minor_inl = r_lam(r_bvar(5), r_app(r_bvar(2), r_bvar(0))); // (x:a) => ha x
    let minor_inr = r_lam(r_bvar(4), r_app(r_bvar(1), r_bvar(0))); // (x:b) => hb x
                                                                   // Or.rec : {a b} (motive) (minor_inl) (minor_inr) (major) -> motive major.
    let body = r_apps(
        elim,
        vec![
            r_bvar(5), // a
            r_bvar(4), // b
            motive,
            minor_inl,
            minor_inr,
            r_bvar(2), // h
        ],
    );
    let proof = r_lam(
        r_prop(),
        r_lam(
            r_prop(),
            r_lam(
                r_prop(),
                r_lam(
                    or_ab(2, 1),
                    r_lam(
                        r_pi(r_bvar(3), r_bvar(2)),
                        r_lam(r_pi(r_bvar(3), r_bvar(3)), body),
                    ),
                ),
            ),
        ),
    );
    admit_theorem(&env, &ty, &proof, 0);
}

// --- Nat.rec computation: a small recursion reduces ------------------------
#[test]
fn test_nat_rec_small_computation_checks() {
    let env = stdlib_env();
    // Define `one := Nat.succ Nat.zero`. Build `Nat.rec` summing-ish: identity
    // function on Nat via rec, applied to (succ zero), check it has type Nat and
    // is def-eq to succ zero.
    //   id := Nat.rec (motive := fun _ => Nat) Nat.zero (fun n ih => Nat.succ ih)
    let elim = RawExpr::Elim(n("Nat"), lsucc(RawLevel::Zero), vec![]);
    let motive = r_lam(r_const("Nat"), r_const("Nat"));
    let z = r_const("Nat.zero");
    let s = r_lam(
        r_const("Nat"),
        r_lam(r_const("Nat"), r_app(r_const("Nat.succ"), r_bvar(0))),
    );
    let one = r_app(r_const("Nat.succ"), r_const("Nat.zero"));
    let app = r_apps(elim, vec![motive, z, s, one.clone()]);
    let t = Term::validate_closed(&env, &app).expect("validates");
    let mut budget = Budget::default_budget();
    let inferred = clean_ck0::infer(&env, &t, &mut budget).expect("infers");
    // Type is Nat.
    let nat = Term::validate_closed(&env, &r_const("Nat")).expect("Nat");
    assert!(
        clean_ck0::is_def_eq(&env, &inferred, &nat, &mut budget).expect("def_eq"),
        "Nat.rec identity has type Nat"
    );
    // Value reduces (def-eq) to succ zero.
    let one_t = Term::validate_closed(&env, &one).expect("one");
    assert!(
        clean_ck0::is_def_eq(&env, &t, &one_t, &mut budget).expect("def_eq"),
        "Nat.rec id (succ zero) reduces to succ zero"
    );
}

// --- List.append associativity STATEMENT type-checks -----------------------
#[test]
fn test_list_append_assoc_statement_type_checks() {
    let env = stdlib_env();
    // We cannot define List.append by recursion as a top-level const here (no
    // def-by-recursion frontend), but we CAN admit `append` as a typed constant
    // and confirm the associativity STATEMENT type-checks to a Sort. That is the
    // deliverable's "the TYPE type-checks even if the proof is by the recursor".
    // append : {A : Type u} -> List A -> List A -> List A
    let list_a = |db: u32| r_app(r_const_p("List", vec![lparam(0)]), r_bvar(db));
    let append_ty_raw = r_pi_i(
        r_sort_param(0), // A
        r_pi(list_a(0), r_pi(list_a(1), list_a(2))),
    );
    let append_ty = Term::validate(&env, &append_ty_raw, 0, 1).expect("append type validates");
    let env = env.with_const_typed(n("List.append"), 1, append_ty);

    // Statement: {A} (xs ys zs : List A) ->
    //   Eq (List A) (append (append xs ys) zs) (append xs (append ys zs))
    let la = |db: u32| r_app(r_const_p("List", vec![lparam(0)]), r_bvar(db));
    // append takes the implicit {A} explicitly here (no implicit insertion in the
    // chokepoint): append A xs ys. A is bvar3 throughout the body [A,xs,ys,zs].
    let appnd = |x: RawExpr, y: RawExpr| {
        r_apps(
            r_const_p("List.append", vec![lparam(0)]),
            vec![r_bvar(3), x, y],
        )
    };
    // depth in body [A,xs,ys,zs]: A=3, xs=2, ys=1, zs=0.
    let lhs = appnd(
        appnd(r_bvar(2), r_bvar(1)), // append xs ys
        r_bvar(0),                   // zs
    );
    let rhs = appnd(r_bvar(2), appnd(r_bvar(1), r_bvar(0)));
    let stmt = r_pi_i(
        r_sort_param(0), // A
        r_pi(
            la(0), // xs : List A
            r_pi(
                la(1), // ys
                r_pi(
                    la(2), // zs
                    // List.{u} validates as `Sort u -> Sort u`, so `List A : Sort
                    // u` and Eq's universe param is u (Param 0), not u+1.
                    r_apps(r_const_p("Eq", vec![lparam(0)]), vec![la(3), lhs, rhs]),
                ),
            ),
        ),
    );
    let stmt_t = Term::validate(&env, &stmt, 0, 1).expect("assoc statement validates");
    let mut budget = Budget::default_budget();
    let sort = clean_ck0::infer_sort_in_context(&env, &[], &stmt_t, &mut budget)
        .expect("append-assoc statement is a well-formed Prop");
    assert!(sort.is_zero(), "append-assoc statement lives in Prop");
}

// --- Bool basics: Bool.rec on true/false reduces ---------------------------
#[test]
fn test_bool_rec_reduces_on_constructors() {
    let env = stdlib_env();
    // not := Bool.rec (motive := fun _ => Bool) Bool.true Bool.false
    //   not false ~> true, not true ~> false.
    let elim = RawExpr::Elim(n("Bool"), lsucc(RawLevel::Zero), vec![]);
    let motive = r_lam(r_const("Bool"), r_const("Bool"));
    // minors in ctor order [false, true]: false-case -> Bool.true, true-case -> Bool.false.
    let not_of = |arg: RawExpr| {
        r_apps(
            elim.clone(),
            vec![
                motive.clone(),
                r_const("Bool.true"),  // minor for Bool.false
                r_const("Bool.false"), // minor for Bool.true
                arg,
            ],
        )
    };
    let mut budget = Budget::default_budget();
    // not false ~> true
    let t1 = Term::validate_closed(&env, &not_of(r_const("Bool.false"))).expect("v");
    let w1 = clean_ck0::whnf(&env, &t1, &mut budget).expect("whnf");
    let tru = Term::validate_closed(&env, &r_const("Bool.true")).expect("true");
    assert_eq!(w1, tru, "not false ~> true");
    // not true ~> false
    let t2 = Term::validate_closed(&env, &not_of(r_const("Bool.true"))).expect("v");
    let w2 = clean_ck0::whnf(&env, &t2, &mut budget).expect("whnf");
    let fls = Term::validate_closed(&env, &r_const("Bool.false")).expect("false");
    assert_eq!(w2, fls, "not true ~> false");
}

// --- Prod.mk + Prod.fst (via Prod.rec) -------------------------------------
#[test]
fn test_prod_mk_and_fst_check() {
    let env = stdlib_env();
    // p := Prod.mk Nat Bool Nat.zero Bool.true : Prod Nat Bool
    let prod_nb = r_apps(
        r_const_p("Prod", vec![lsucc(RawLevel::Zero), lsucc(RawLevel::Zero)]),
        vec![r_const("Nat"), r_const("Bool")],
    );
    let p = r_apps(
        r_const_p(
            "Prod.mk",
            vec![lsucc(RawLevel::Zero), lsucc(RawLevel::Zero)],
        ),
        vec![
            r_const("Nat"),
            r_const("Bool"),
            r_const("Nat.zero"),
            r_const("Bool.true"),
        ],
    );
    admit_theorem(&env, &prod_nb, &p, 0);

    // fst p : Nat via Prod.rec (motive := fun _ => Nat) (fun a b => a) p, def-eq zero.
    // Prod.rec is large-elim: Elim levels = [motive_level, u, v] = [1, 1, 1].
    let elim = RawExpr::Elim(
        n("Prod"),
        lsucc(RawLevel::Zero),
        vec![lsucc(RawLevel::Zero), lsucc(RawLevel::Zero)],
    );
    let motive = r_lam(prod_nb.clone(), r_const("Nat")); // fun _ : Prod Nat Bool => Nat
    let minor = r_lam(
        r_const("Nat"),
        r_lam(r_const("Bool"), r_bvar(1)), // fun a b => a
    );
    // Prod.rec : {A B} (motive) (minor) (major) -> motive major. Params A,B.
    let fst_p = r_apps(
        elim,
        vec![r_const("Nat"), r_const("Bool"), motive, minor, p.clone()],
    );
    let t = Term::validate_closed(&env, &fst_p).expect("validates");
    let mut budget = Budget::default_budget();
    let inferred = clean_ck0::infer(&env, &t, &mut budget).expect("fst infers");
    let nat = Term::validate_closed(&env, &r_const("Nat")).expect("Nat");
    assert!(
        clean_ck0::is_def_eq(&env, &inferred, &nat, &mut budget).expect("def_eq"),
        "Prod.fst p : Nat"
    );
    let zero = Term::validate_closed(&env, &r_const("Nat.zero")).expect("zero");
    assert!(
        clean_ck0::is_def_eq(&env, &t, &zero, &mut budget).expect("def_eq"),
        "Prod.fst (mk zero true) reduces to zero"
    );
}

// --- congrArg type checks (statement) --------------------------------------
#[test]
fn test_congr_arg_statement_type_checks() {
    let env = stdlib_env();
    // congrArg : {A B : Type} (f : A -> B) {a b : A} -> Eq A a b -> Eq B (f a) (f b)
    // Just confirm the STATEMENT type-checks to Prop (universe-monomorphic at u=v=1).
    let eqa = |a: RawExpr, x: RawExpr, y: RawExpr| {
        r_apps(r_const_p("Eq", vec![lsucc(RawLevel::Zero)]), vec![a, x, y])
    };
    // {A B : Type 0} (f : A -> B) {a b : A} -> Eq A a b -> Eq B (f a) (f b)
    let ty = r_pi_i(
        r_sort(1), // A   bvar grows
        r_pi_i(
            r_sort(1), // B
            r_pi(
                r_pi(r_bvar(1), r_bvar(1)), // f : A -> B
                r_pi_i(
                    r_bvar(2), // a : A
                    r_pi_i(
                        r_bvar(3), // b : A
                        r_pi(
                            eqa(r_bvar(4), r_bvar(1), r_bvar(0)), // Eq A a b
                            eqa(
                                r_bvar(4),                   // B
                                r_app(r_bvar(3), r_bvar(2)), // f a
                                r_app(r_bvar(3), r_bvar(1)), // f b
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    let t = Term::validate_closed(&env, &ty).expect("congrArg type validates");
    let mut budget = Budget::default_budget();
    let sort = clean_ck0::infer_sort_in_context(&env, &[], &t, &mut budget)
        .expect("congrArg statement is a well-formed type");
    assert!(sort.is_zero(), "congrArg statement is a Prop");
}

// ===========================================================================
// Negative controls: acceptance is meaningful.
// ===========================================================================

#[test]
fn test_neg_eq_refl_at_wrong_type_rejected() {
    let env = stdlib_env();
    // CLAIM: Eq.refl Nat zero : Eq Nat zero (succ zero)  — FALSE.
    let bad_ty = r_apps(
        r_const_p("Eq", vec![lsucc(RawLevel::Zero)]),
        vec![
            r_const("Nat"),
            r_const("Nat.zero"),
            r_app(r_const("Nat.succ"), r_const("Nat.zero")),
        ],
    );
    let proof = r_apps(
        r_const_p("Eq.refl", vec![lsucc(RawLevel::Zero)]),
        vec![r_const("Nat"), r_const("Nat.zero")],
    );
    let ty = Term::validate_closed(&env, &bad_ty).expect("type validates");
    let p = Term::validate_closed(&env, &proof).expect("proof validates");
    let mut budget = Budget::default_budget();
    let r = clean_ck0::check(&env, &p, &ty, &mut budget);
    assert!(
        r.is_err(),
        "Eq.refl zero must NOT check against Eq zero (succ zero): {r:?}"
    );
}

#[test]
fn test_neg_and_intro_underapplied_rejected() {
    let env = stdlib_env();
    // And.intro True True True.intro : And True True  — MISSING the second proof.
    // Its inferred type is `True -> And True True`, NOT `And True True`.
    let claimed_ty = r_apps(r_const("And"), vec![r_const("True"), r_const("True")]);
    let underapplied = r_apps(
        r_const("And.intro"),
        vec![r_const("True"), r_const("True"), r_const("True.intro")],
    );
    let ty = Term::validate_closed(&env, &claimed_ty).expect("type validates");
    let p = Term::validate_closed(&env, &underapplied).expect("proof validates");
    let mut budget = Budget::default_budget();
    let r = clean_ck0::check(&env, &p, &ty, &mut budget);
    assert!(
        r.is_err(),
        "under-applied And.intro must NOT check against And True True: {r:?}"
    );
}

#[test]
fn test_neg_non_strictly_positive_inductive_rejected() {
    // A non-strictly-positive inductive (self to the LEFT of an arrow in a field)
    // must be rejected at admission, so the stdlib admissions are meaningful.
    //   Bad : Type  with  Bad.mk : (Bad -> Bad) -> Bad.
    let b = boot(&[("Bad", 0), ("Bad.mk", 0)]);
    let ty = vlvl(&b, &r_sort(1), 0);
    let mk_ty = vlvl(
        &b,
        &r_pi(r_pi(r_const("Bad"), r_const("Bad")), r_const("Bad")),
        0,
    );
    let decl = InductiveDecl {
        name: n("Bad"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Bad.mk"),
            type_: mk_ty,
        }],
    };
    let mut env = stdlib_env();
    let r = add_inductive(&mut env, decl);
    assert!(
        matches!(r, Err(clean_ck0::AdmitError::NonPositive { .. })),
        "non-strictly-positive inductive must be rejected: {r:?}"
    );
}

#[test]
fn test_neg_wrong_constructor_arg_rejected() {
    let env = stdlib_env();
    // Or.inl with a proof of the WRONG disjunct's type: Or.inl True False
    // applied to (Nat.zero : Nat) — Nat.zero is not a proof of `True`.
    let proof = r_apps(
        r_const("Or.inl"),
        vec![r_const("True"), r_const("False"), r_const("Nat.zero")],
    );
    // Even validating-then-inferring must fail (Nat.zero : Nat ≠ True).
    let p = Term::validate_closed(&env, &proof).expect("term validates structurally");
    let mut budget = Budget::default_budget();
    let r = clean_ck0::infer(&env, &p, &mut budget);
    assert!(
        r.is_err(),
        "Or.inl applied to a non-proof of `a` must fail to infer: {r:?}"
    );
}
