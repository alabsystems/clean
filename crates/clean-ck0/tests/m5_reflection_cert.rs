// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ck0 reflection certificate — the "software kingdom" re-check IN the minimal
//! kernel.
//!
//! This brings the SAT/codegen resolution-refutation reflection mechanism (proven
//! as C1 in the LEGACY `clean-kernel`, see
//! `crates/clean-kernel/src/resolution_check.rs`) into ck0 ITSELF. The compiler is
//! taken out of the TCB: a Resolution-DAG refutation of an UNSAT clause set is
//! re-checked by REFLECTION — a computational checker `checkRefutes : List Clause
//! -> List Step -> Bool` is built entirely as ck0 `Definition`s over ck0
//! inductives, ck0 type-checks those definitions, and ck0's own `is_def_eq`
//! reduces `checkRefutes <instance> <refutation>` to `Bool.true` by ι/δ
//! computation on the concrete clause data. This is the #24/#25 "Nat.add via
//! Nat.rec, then reduce 2+2" pattern scaled up to a full resolution checker.
//!
//! NOTHING here is new trusted kernel source: the checker lives only in this test,
//! as terms the kernel CHECKS and EVALUATES. The kernel's only jobs are (a) admit
//! the inductives + checker definitions (so they kernel-check) and (b) reduce
//! `checkRefutes` on concrete data.
//!
//! ENCODINGS
//! ---------
//!   * Lit = `Nat`, encoded `2*var + polarity` (even = positive literal of var
//!     `n/2`; odd = its negation). `litNeg` flips the low bit.
//!   * Clause = `List Nat` (a disjunction of literals).
//!   * Step = inductive `Step` with one ctor
//!     `Step.mk (resolvent : List Nat) (prem1 prem2 pivot : Nat)`; `pivot` is
//!     recorded as the POSITIVE literal of the pivot var.
//!   * Refutation = `List Step`; the clause DB grows as `db ++ [resolvent_i]`.
//!
//! THE SOUNDNESS-CRITICAL `resolve` (mirrors the #22 fix)
//! -----------------------------------------------------
//!   `resolve a b p = dropLit p a ++ dropLit (litNeg p) b`  — a SINGLE ORIENTED
//!   drop (drop the positive pivot from `a`, the negative pivot from `b`). The old
//!   double-polarity drop `(a ∪ b) \ {p, ¬p}` is UNSOUND (it derives ∅ from the
//!   SATISFIABLE set `{(p), (¬p ∨ p)}`). `checkStep` validates BOTH legal
//!   orientations against the oriented resolvent and additionally requires the
//!   resolvent be tautology-free.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, Budget, Constructor, Env, InductiveDecl, MinimalEnv, Name, RawExpr, RawLevel,
    Term, Transparency,
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
fn r_lam(dom: RawExpr, body: RawExpr) -> RawExpr {
    RawExpr::Lam(BinderInfo::Default, Box::new(dom), Box::new(body))
}
fn r_bvar(i: u32) -> RawExpr {
    RawExpr::BVar(i)
}
// The `Sort 0`/`Prop` level of the raw-level helper set (`lzero`/`lone`/`lparam`);
// the M5 fixtures currently only reach `lone`/`lparam`. Kept alongside its
// siblings so a Prop-universe reflection fixture needs no re-derivation
// — 2026-07-31.
#[allow(dead_code)]
fn lzero() -> RawLevel {
    RawLevel::Zero
}
fn lone() -> RawLevel {
    RawLevel::Succ(Box::new(RawLevel::Zero))
}
fn lparam(i: u32) -> RawLevel {
    RawLevel::Param(i)
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

// ---- ground types / data builders ----
fn nat() -> RawExpr {
    r_const("Nat")
}
fn bool_ty() -> RawExpr {
    r_const("Bool")
}
fn btrue() -> RawExpr {
    r_const("Bool.true")
}
fn bfalse() -> RawExpr {
    r_const("Bool.false")
}
fn nat_zero() -> RawExpr {
    r_const("Nat.zero")
}
fn nat_succ(x: RawExpr) -> RawExpr {
    r_app(r_const("Nat.succ"), x)
}
fn nat_lit(k: u32) -> RawExpr {
    let mut e = nat_zero();
    for _ in 0..k {
        e = nat_succ(e);
    }
    e
}
// All list element types here (Nat, List Nat, Step) live in `Type 0 = Sort 1`,
// so the `List` level parameter is `1` (NOT 0): `List.{1} Nat`, etc.
/// `List Nat`.
fn list_nat() -> RawExpr {
    r_app(r_const_p("List", vec![lone()]), nat())
}
/// `List (List Nat)`.
fn list_list_nat() -> RawExpr {
    r_app(r_const_p("List", vec![lone()]), list_nat())
}
/// `List Step`.
fn list_step() -> RawExpr {
    r_app(r_const_p("List", vec![lone()]), r_const("Step"))
}
/// `@List.nil.{1} A`.
fn nil(elem: RawExpr) -> RawExpr {
    r_app(r_const_p("List.nil", vec![lone()]), elem)
}
/// `@List.cons.{1} A h t`.
fn cons(elem: RawExpr, h: RawExpr, t: RawExpr) -> RawExpr {
    r_apps(r_const_p("List.cons", vec![lone()]), vec![elem, h, t])
}
/// `List.rec.{motive,1}` applied: motive (closed result type `ret`), nil case,
/// cons case, major. `elem` is the element type (in `Type 0`, so elem-level = 1).
fn list_rec(
    elem: RawExpr,
    ret: RawExpr,
    nil_case: RawExpr,
    cons_case: RawExpr,
    major: RawExpr,
) -> RawExpr {
    // List.rec : motive universe = Sort 1 (Bool/List/Nat results), elem universe 1.
    let elim = RawExpr::Elim(n("List"), lone(), vec![lone()]);
    let motive = r_lam(r_app(r_const_p("List", vec![lone()]), elem.clone()), ret);
    r_apps(elim, vec![elem, motive, nil_case, cons_case, major])
}
/// `Bool.rec.{1}` into a `Sort 1` result `ret`: false case, true case, scrut.
/// (ctor order is [false, true].)
fn bool_rec(ret: RawExpr, false_case: RawExpr, true_case: RawExpr, scrut: RawExpr) -> RawExpr {
    let elim = RawExpr::Elim(n("Bool"), lone(), vec![]);
    let motive = r_lam(bool_ty(), ret);
    r_apps(elim, vec![motive, false_case, true_case, scrut])
}

// ===========================================================================
// Base inductives: Bool, Nat, List, Or, False — plus the Step inductive.
// ===========================================================================

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

/// `Step : Type` with `Step.mk (resolvent : List Nat) (prem1 prem2 pivot : Nat)`.
fn step_decl() -> InductiveDecl {
    let b = boot(&[("Step", 0), ("Step.mk", 0), ("List", 1), ("Nat", 0)]);
    // mk : List Nat -> Nat -> Nat -> Nat -> Step
    let mk_ty = r_pi(
        list_nat(),
        r_pi(nat(), r_pi(nat(), r_pi(nat(), r_const("Step")))),
    );
    InductiveDecl {
        name: n("Step"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_sort(1), 0),
        constructors: vec![Constructor {
            name: n("Step.mk"),
            type_: vlvl(&b, &mk_ty, 0),
        }],
    }
}

// ===========================================================================
// The checker, built as transparent ck0 Definitions over the recursors.
// Each body is kernel-checked against its declared type before registration.
// ===========================================================================

/// Register a transparent definition after kernel-checking its body against its
/// declared (validated) type.
fn def(env: MinimalEnv, name: &str, ty_raw: &RawExpr, body_raw: &RawExpr) -> MinimalEnv {
    let ty = Term::validate_closed(&env, ty_raw)
        .unwrap_or_else(|e| panic!("{name}: type validates: {e:?}"));
    let body = Term::validate_closed(&env, body_raw)
        .unwrap_or_else(|e| panic!("{name}: body validates: {e:?}"));
    let mut budget = Budget::default_budget();
    clean_ck0::check(&env, &body, &ty, &mut budget)
        .unwrap_or_else(|e| panic!("{name}: body checks against its type: {e:?}"));
    env.with_def(n(name), 0, ty, body, Transparency::Transparent)
}

// ---- Nat.beq : Nat -> Nat -> Bool (structural, double Nat.rec) ----
// natBeq m n := Nat.rec (motive := fun _ => Nat -> Bool)
//   /-m=0-/   (fun n => Nat.rec (fun _ => Bool) Bool.true (fun _ _ => Bool.false) n)
//   /-m=S k-/ (fun k ih => Nat.rec (fun _ => Bool) Bool.false (fun n2 _ => ih n2) n)
//   m n
fn nat_beq_body() -> RawExpr {
    let nat_to_bool = r_pi(nat(), bool_ty());
    // is-zero test: Nat.rec (fun _ => Bool) true (fun _ _ => false) x
    let is_zero = |x: RawExpr| {
        let elim = RawExpr::Elim(n("Nat"), lone(), vec![]);
        let motive = r_lam(nat(), bool_ty());
        let succ_case = r_lam(nat(), r_lam(bool_ty(), bfalse()));
        r_apps(elim, vec![motive, btrue(), succ_case, x])
    };
    // outer Nat.rec on m, motive (fun _ => Nat -> Bool):
    let elim = RawExpr::Elim(n("Nat"), lone(), vec![]);
    let motive = r_lam(nat(), nat_to_bool.clone());
    // zero case: fun (n : Nat) => is_zero n
    let zero_case = r_lam(nat(), is_zero(r_bvar(0)));
    // succ case: fun (k : Nat) (ih : Nat -> Bool) (n : Nat) =>
    //   Nat.rec (fun _ => Bool) false (fun n2 _ => ih n2) n
    let succ_case = {
        let inner_elim = RawExpr::Elim(n("Nat"), lone(), vec![]);
        let inner_motive = r_lam(nat(), bool_ty());
        // inner succ: fun (n2 : Nat) (_ : Bool) => ih n2  ; ih is bvar 3 here
        let inner_succ = r_lam(nat(), r_lam(bool_ty(), r_app(r_bvar(3), r_bvar(1))));
        let inner = r_apps(
            inner_elim,
            vec![inner_motive, bfalse(), inner_succ, r_bvar(0)],
        );
        r_lam(nat(), r_lam(nat_to_bool.clone(), r_lam(nat(), inner)))
    };
    // natBeq := fun m n => (Nat.rec motive zero_case succ_case m) n
    r_lam(
        nat(),
        r_lam(
            nat(),
            r_app(
                r_apps(elim, vec![motive, zero_case, succ_case, r_bvar(1)]),
                r_bvar(0),
            ),
        ),
    )
}

// ---- Bool ops: and / or / not via Bool.rec ----
fn band(x: RawExpr, y: RawExpr) -> RawExpr {
    r_apps(r_const("band"), vec![x, y])
}
fn bor(x: RawExpr, y: RawExpr) -> RawExpr {
    r_apps(r_const("bor"), vec![x, y])
}
fn bnot(x: RawExpr) -> RawExpr {
    r_app(r_const("bnot"), x)
}

fn register_bool_ops(env: MinimalEnv) -> MinimalEnv {
    let bb = r_pi(bool_ty(), r_pi(bool_ty(), bool_ty()));
    // band x y := Bool.rec (fun _ => Bool) false y x
    let band_body = r_lam(
        bool_ty(),
        r_lam(
            bool_ty(),
            bool_rec(bool_ty(), bfalse(), r_bvar(0), r_bvar(1)),
        ),
    );
    let env = def(env, "band", &bb, &band_body);
    // bor x y := Bool.rec (fun _ => Bool) y true x
    let bor_body = r_lam(
        bool_ty(),
        r_lam(
            bool_ty(),
            bool_rec(bool_ty(), r_bvar(0), btrue(), r_bvar(1)),
        ),
    );
    let env = def(env, "bor", &bb, &bor_body);
    // bnot x := Bool.rec (fun _ => Bool) true false x
    let bnot_body = r_lam(bool_ty(), bool_rec(bool_ty(), btrue(), bfalse(), r_bvar(0)));
    def(env, "bnot", &r_pi(bool_ty(), bool_ty()), &bnot_body)
}

// ---- literal ops ----
fn register_lit_ops(env: MinimalEnv) -> MinimalEnv {
    // litBeq a b := Nat.beq a b
    let bb = r_pi(nat(), r_pi(nat(), bool_ty()));
    let litbeq_body = r_lam(
        nat(),
        r_lam(
            nat(),
            r_apps(r_const("Nat.beq"), vec![r_bvar(1), r_bvar(0)]),
        ),
    );
    let env = def(env, "litBeq", &bb, &litbeq_body);

    // litNeg l flips the low bit: 0<->1, 2<->3, ...
    //   g : Nat -> (Bool -> Nat),  g l false = litNeg l,  g l true = litNeg (succ l)
    //   g 0       = fun b => Bool.rec (fun _=>Nat) 1 0 b
    //   g (succ p)= fun b => Bool.rec (fun _=>Nat) (g p true) (succ (succ (g p false))) b
    //   litNeg l := g l false
    let nat_carrier = r_pi(bool_ty(), nat());
    let neg_body = {
        let elim = RawExpr::Elim(n("Nat"), lone(), vec![]);
        let motive = r_lam(nat(), nat_carrier.clone());
        // zero case: fun (b : Bool) => Bool.rec 1 0 b
        let zero_case = r_lam(
            bool_ty(),
            bool_rec(nat(), nat_lit(1), nat_lit(0), r_bvar(0)),
        );
        // succ case: fun (p : Nat) (ih : Bool -> Nat) (b : Bool) =>
        //   Bool.rec (motive:=fun _=>Nat) (ih true) (succ (succ (ih false))) b
        //   bvars: b=0, ih=1, p=2
        let succ_case = {
            let ih_true = r_app(r_bvar(1), btrue());
            let ss_ih_false = nat_succ(nat_succ(r_app(r_bvar(1), bfalse())));
            r_lam(
                nat(),
                r_lam(
                    nat_carrier.clone(),
                    r_lam(bool_ty(), bool_rec(nat(), ih_true, ss_ih_false, r_bvar(0))),
                ),
            )
        };
        // litNeg := fun (l : Nat) => (Nat.rec motive zero succ l) false
        r_lam(
            nat(),
            r_app(
                r_apps(elim, vec![motive, zero_case, succ_case, r_bvar(0)]),
                bfalse(),
            ),
        )
    };
    def(env, "litNeg", &r_pi(nat(), nat()), &neg_body)
}

// ---- clause (List Nat) ops ----
fn register_clause_ops(env: MinimalEnv) -> MinimalEnv {
    // clauseMem x c := List.rec false (fun h _ ih => bor (litBeq x h) ih) c
    let mem_ty = r_pi(nat(), r_pi(list_nat(), bool_ty()));
    let mem_body = {
        // cons case: fun (h : Nat) (t : List Nat) (ih : Bool) => bor (litBeq x h) ih
        //   bvars: ih=0, t=1, h=2, c=3, x=4
        let litbeq = r_apps(r_const("litBeq"), vec![r_bvar(4), r_bvar(2)]);
        let cc = r_lam(
            nat(),
            r_lam(list_nat(), r_lam(bool_ty(), bor(litbeq, r_bvar(0)))),
        );
        r_lam(
            nat(),
            r_lam(
                list_nat(),
                list_rec(nat(), bool_ty(), bfalse(), cc, r_bvar(0)),
            ),
        )
    };
    let env = def(env, "clauseMem", &mem_ty, &mem_body);

    // clauseSubset a b := List.rec true (fun h _ ih => band (clauseMem h b) ih) a
    let sub_ty = r_pi(list_nat(), r_pi(list_nat(), bool_ty()));
    let sub_body = {
        //   bvars inside the cons case: ih=0, t=1, h=2, b=3, a=4
        let mem = r_apps(r_const("clauseMem"), vec![r_bvar(2), r_bvar(3)]);
        let cc = r_lam(
            nat(),
            r_lam(list_nat(), r_lam(bool_ty(), band(mem, r_bvar(0)))),
        );
        r_lam(
            list_nat(),
            r_lam(
                list_nat(),
                list_rec(nat(), bool_ty(), btrue(), cc, r_bvar(1)),
            ),
        )
    };
    let env = def(env, "clauseSubset", &sub_ty, &sub_body);

    // clauseSeteq a b := band (clauseSubset a b) (clauseSubset b a)
    let seteq_body = r_lam(
        list_nat(),
        r_lam(
            list_nat(),
            band(
                r_apps(r_const("clauseSubset"), vec![r_bvar(1), r_bvar(0)]),
                r_apps(r_const("clauseSubset"), vec![r_bvar(0), r_bvar(1)]),
            ),
        ),
    );
    let env = def(env, "clauseSeteq", &sub_ty, &seteq_body);

    // dropLit x c := List.rec nil (fun h t ih => Bool.rec (cons h ih) ih (litBeq x h)) c
    //   keep h unless h == x.
    let drop_ty = r_pi(nat(), r_pi(list_nat(), list_nat()));
    let drop_body = {
        //   bvars: ih=0, t=1, h=2, c=3, x=4
        let h = r_bvar(2);
        let keep = cons(nat(), h.clone(), r_bvar(0));
        let litbeq = r_apps(r_const("litBeq"), vec![r_bvar(4), h]);
        // Bool.rec (false=>keep) (true=>drop ih) litbeq
        let body = bool_rec(list_nat(), keep, r_bvar(0), litbeq);
        let cc = r_lam(nat(), r_lam(list_nat(), r_lam(list_nat(), body)));
        r_lam(
            nat(),
            r_lam(
                list_nat(),
                list_rec(nat(), list_nat(), nil(nat()), cc, r_bvar(0)),
            ),
        )
    };
    let env = def(env, "dropLit", &drop_ty, &drop_body);

    // append a b := List.rec b (fun h _ ih => cons h ih) a
    let app_ty = r_pi(list_nat(), r_pi(list_nat(), list_nat()));
    let app_body = {
        //   bvars: ih=0, t=1, h=2, a=3, b=4
        let cc = r_lam(
            nat(),
            r_lam(
                list_nat(),
                r_lam(list_nat(), cons(nat(), r_bvar(2), r_bvar(0))),
            ),
        );
        r_lam(
            list_nat(),
            r_lam(
                list_nat(),
                list_rec(nat(), list_nat(), r_bvar(0), cc, r_bvar(1)),
            ),
        )
    };
    let env = def(env, "append", &app_ty, &app_body);

    // clauseTautFree c := List.rec true
    //   (fun h _ ih => band (bnot (clauseMem (litNeg h) c)) ih) c
    let taut_ty = r_pi(list_nat(), bool_ty());
    let taut_body = {
        //   bvars: ih=0, t=1, h=2, c=3
        let neg_h = r_app(r_const("litNeg"), r_bvar(2));
        let mem = r_apps(r_const("clauseMem"), vec![neg_h, r_bvar(3)]);
        let cc = r_lam(
            nat(),
            r_lam(list_nat(), r_lam(bool_ty(), band(bnot(mem), r_bvar(0)))),
        );
        r_lam(
            list_nat(),
            list_rec(nat(), bool_ty(), btrue(), cc, r_bvar(0)),
        )
    };
    def(env, "clauseTautFree", &taut_ty, &taut_body)
}

// ---- resolve (single oriented drop) ----
fn register_resolve(env: MinimalEnv) -> MinimalEnv {
    // resolve a b p := append (dropLit p a) (dropLit (litNeg p) b)
    let ty = r_pi(list_nat(), r_pi(list_nat(), r_pi(nat(), list_nat())));
    let body = {
        //   bvars: p=0, b=1, a=2
        let a1 = r_apps(r_const("dropLit"), vec![r_bvar(0), r_bvar(2)]);
        let neg_p = r_app(r_const("litNeg"), r_bvar(0));
        let b1 = r_apps(r_const("dropLit"), vec![neg_p, r_bvar(1)]);
        r_lam(
            list_nat(),
            r_lam(
                list_nat(),
                r_lam(nat(), r_apps(r_const("append"), vec![a1, b1])),
            ),
        )
    };
    def(env, "resolve", &ty, &body)
}

// ---- nth : List (List Nat) -> Nat -> List Nat ----
fn register_nth(env: MinimalEnv) -> MinimalEnv {
    // nth db i := (List.rec (motive := fun _ => Nat -> List Nat)
    //   (fun _ => nil)
    //   (fun h t ihf => fun i => Nat.rec (fun _ => List Nat) h (fun k _ => ihf k) i)
    //   db) i
    let nat_to_list = r_pi(nat(), list_nat());
    let ty = r_pi(list_list_nat(), nat_to_list.clone());
    let body = {
        let nil_case = r_lam(nat(), nil(nat()));
        // cons case: fun (h : List Nat) (t : List(List Nat)) (ihf : Nat -> List Nat) (i : Nat) => ...
        //   bvars under these four lambdas: i=0, ihf=1, t=2, h=3
        let cons_case = {
            let inner_elim = RawExpr::Elim(n("Nat"), lone(), vec![]);
            let inner_motive = r_lam(nat(), list_nat());
            // succ case: fun (k : Nat) (_ : List Nat) => ihf k ; ihf is bvar 3 here
            let inner_succ = r_lam(nat(), r_lam(list_nat(), r_app(r_bvar(3), r_bvar(1))));
            let inner = r_apps(
                inner_elim,
                vec![inner_motive, r_bvar(3), inner_succ, r_bvar(0)],
            );
            r_lam(
                list_nat(),
                r_lam(
                    list_list_nat(),
                    r_lam(nat_to_list.clone(), r_lam(nat(), inner)),
                ),
            )
        };
        // List.rec over db with element type `List Nat`, motive (fun _ => Nat -> List Nat).
        let elim = RawExpr::Elim(n("List"), lone(), vec![lone()]);
        let motive = r_lam(list_list_nat(), nat_to_list.clone());
        let folded = r_apps(
            elim,
            vec![list_nat(), motive, nil_case, cons_case, r_bvar(1)],
        );
        r_lam(list_list_nat(), r_lam(nat(), r_app(folded, r_bvar(0))))
    };
    def(env, "nth", &ty, &body)
}

// ---- Step accessors via Step.rec ----
fn register_step_accessors(env: MinimalEnv) -> MinimalEnv {
    // stepResolvent s := Step.rec (fun resolvent _ _ _ => resolvent) s
    let sr_ty = r_pi(r_const("Step"), list_nat());
    // mk_case binds resolvent, prem1, prem2, pivot (4 fields).
    let sr_body = {
        // bvars in mk_case: pivot=0, prem2=1, prem1=2, resolvent=3
        let mk_case = r_lam(
            list_nat(),
            r_lam(nat(), r_lam(nat(), r_lam(nat(), r_bvar(3)))),
        );
        let elim = RawExpr::Elim(n("Step"), lone(), vec![]);
        let motive = r_lam(r_const("Step"), list_nat());
        r_lam(
            r_const("Step"),
            r_apps(elim, vec![motive, mk_case, r_bvar(0)]),
        )
    };
    let env = def(env, "stepResolvent", &sr_ty, &sr_body);

    // listIsNil c := List.rec true (fun _ _ _ => false) c
    let lin_body = {
        let cc = r_lam(nat(), r_lam(list_nat(), r_lam(bool_ty(), bfalse())));
        r_lam(
            list_nat(),
            list_rec(nat(), bool_ty(), btrue(), cc, r_bvar(0)),
        )
    };
    let env = def(env, "listIsNil", &r_pi(list_nat(), bool_ty()), &lin_body);

    // stepResolventEmpty s := listIsNil (stepResolvent s)
    let sre_body = r_lam(
        r_const("Step"),
        r_app(
            r_const("listIsNil"),
            r_app(r_const("stepResolvent"), r_bvar(0)),
        ),
    );
    let env = def(
        env,
        "stepResolventEmpty",
        &r_pi(r_const("Step"), bool_ty()),
        &sre_body,
    );

    // snocStep db s := List.rec (cons (stepResolvent s) nil) (fun h _ ih => cons h ih) db
    let snoc_ty = r_pi(list_list_nat(), r_pi(r_const("Step"), list_list_nat()));
    let snoc_body = {
        //   bvars: db=1, s=0
        let resolvent = r_app(r_const("stepResolvent"), r_bvar(0));
        let base = cons(list_nat(), resolvent, nil(list_nat()));
        // cons case: fun (h : List Nat) (t : List(List Nat)) (ih : List(List Nat)) => cons h ih
        let cc = r_lam(
            list_nat(),
            r_lam(
                list_list_nat(),
                r_lam(list_list_nat(), cons(list_nat(), r_bvar(2), r_bvar(0))),
            ),
        );
        // List.rec over db (element type List Nat), motive (fun _ => List(List Nat)).
        let elim = RawExpr::Elim(n("List"), lone(), vec![lone()]);
        let motive = r_lam(list_list_nat(), list_list_nat());
        r_lam(
            list_list_nat(),
            r_lam(
                r_const("Step"),
                r_apps(elim, vec![list_nat(), motive, base, cc, r_bvar(1)]),
            ),
        )
    };
    let env = def(env, "snocStep", &snoc_ty, &snoc_body);

    // listStepIsCons l := List.rec false (fun _ _ _ => true) l
    let lsic_body = {
        let elim = RawExpr::Elim(n("List"), lone(), vec![lone()]);
        let motive = r_lam(list_step(), bool_ty());
        let cc = r_lam(
            r_const("Step"),
            r_lam(list_step(), r_lam(bool_ty(), btrue())),
        );
        r_lam(
            list_step(),
            r_apps(elim, vec![r_const("Step"), motive, bfalse(), cc, r_bvar(0)]),
        )
    };
    def(
        env,
        "listStepIsCons",
        &r_pi(list_step(), bool_ty()),
        &lsic_body,
    )
}

// ---- checkStep ----
fn register_check_step(env: MinimalEnv) -> MinimalEnv {
    // checkStep db s := Step.rec (fun resolvent prem1 prem2 pivot =>
    //   band
    //     (bor
    //        (band (band (mem pivot a) (mem (neg pivot) b))
    //              (seteq resolvent (resolve a b pivot)))      -- orientation A
    //        (band (band (mem (neg pivot) a) (mem pivot b))
    //              (seteq resolvent (resolve b a pivot))))     -- orientation B
    //     (clauseTautFree resolvent)
    //  ) s
    //  where a = nth db prem1, b = nth db prem2.
    let cs_ty = r_pi(list_list_nat(), r_pi(r_const("Step"), bool_ty()));
    let cs_body = {
        // mk_case bvars: pivot=0, prem2=1, prem1=2, resolvent=3, s=4, db=5
        let db = || r_bvar(5);
        let resolvent = r_bvar(3);
        let prem1 = r_bvar(2);
        let prem2 = r_bvar(1);
        let pivot = || r_bvar(0);
        let neg_pivot = || r_app(r_const("litNeg"), pivot());
        let a = || r_apps(r_const("nth"), vec![db(), prem1.clone()]);
        let b = || r_apps(r_const("nth"), vec![db(), prem2.clone()]);
        let mem = |x: RawExpr, c: RawExpr| r_apps(r_const("clauseMem"), vec![x, c]);
        let seteq = |x: RawExpr, y: RawExpr| r_apps(r_const("clauseSeteq"), vec![x, y]);
        let resolve = |x: RawExpr, y: RawExpr| r_apps(r_const("resolve"), vec![x, y, pivot()]);
        // orientation A: pivot in a, neg-pivot in b, resolvent == resolve a b
        let branch_a = band(
            band(mem(pivot(), a()), mem(neg_pivot(), b())),
            seteq(resolvent.clone(), resolve(a(), b())),
        );
        // orientation B: neg-pivot in a, pivot in b, resolvent == resolve b a
        let branch_b = band(
            band(mem(neg_pivot(), a()), mem(pivot(), b())),
            seteq(resolvent.clone(), resolve(b(), a())),
        );
        let taut_free = r_app(r_const("clauseTautFree"), resolvent);
        let body = band(bor(branch_a, branch_b), taut_free);
        let mk_case = r_lam(list_nat(), r_lam(nat(), r_lam(nat(), r_lam(nat(), body))));
        let elim = RawExpr::Elim(n("Step"), lone(), vec![]);
        let motive = r_lam(r_const("Step"), bool_ty());
        r_lam(
            list_list_nat(),
            r_lam(
                r_const("Step"),
                r_apps(elim, vec![motive, mk_case, r_bvar(0)]),
            ),
        )
    };
    def(env, "checkStep", &cs_ty, &cs_body)
}

// ---- checkRefutes ----
fn register_check_refutes(env: MinimalEnv) -> MinimalEnv {
    // go : List Step -> (List(List Nat) -> Bool)
    //   go nil       db := false
    //   go (s::rest) db := band (checkStep db s)
    //       (Bool.rec (stepResolventEmpty s)            -- rest = nil  => require empty
    //                 (ih (snocStep db s))              -- rest = cons => recurse
    //                 (listStepIsCons rest))
    // checkRefutes db0 steps := (List.rec (fun _ => false) cons_case steps) db0
    let cr_ty = r_pi(list_list_nat(), r_pi(list_step(), bool_ty()));
    let db_to_bool = r_pi(list_list_nat(), bool_ty());
    let body = {
        let nil_case = r_lam(list_list_nat(), bfalse());
        // cons case: fun (s : Step) (rest : List Step) (ih : List(List Nat)->Bool) (db : List(List Nat)) => ...
        //   bvars: db=0, ih=1, rest=2, s=3
        let cons_case = {
            let check_step = r_apps(r_const("checkStep"), vec![r_bvar(0), r_bvar(3)]);
            let step_empty = r_app(r_const("stepResolventEmpty"), r_bvar(3));
            let snoc = r_apps(r_const("snocStep"), vec![r_bvar(0), r_bvar(3)]);
            let go_rest = r_app(r_bvar(1), snoc);
            let is_cons = r_app(r_const("listStepIsCons"), r_bvar(2));
            // Bool.rec (false => step_empty) (true => go_rest) is_cons
            let tail = bool_rec(bool_ty(), step_empty, go_rest, is_cons);
            let inner = band(check_step, tail);
            r_lam(
                r_const("Step"),
                r_lam(
                    list_step(),
                    r_lam(db_to_bool.clone(), r_lam(list_list_nat(), inner)),
                ),
            )
        };
        // List.rec over steps, element type Step, motive (fun _ => List(List Nat) -> Bool).
        let elim = RawExpr::Elim(n("List"), lone(), vec![lone()]);
        let motive = r_lam(list_step(), db_to_bool.clone());
        let folded = r_apps(
            elim,
            vec![r_const("Step"), motive, nil_case, cons_case, r_bvar(0)],
        );
        // checkRefutes := fun (db0 : ...) (steps : List Step) => folded db0
        r_lam(
            list_list_nat(),
            r_lam(list_step(), r_app(folded, r_bvar(1))),
        )
    };
    def(env, "checkRefutes", &cr_ty, &body)
}

// ===========================================================================
// Full environment: stdlib inductives + Step + the whole checker.
// ===========================================================================
fn checker_env() -> MinimalEnv {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, bool_decl()).expect("Bool admits");
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    add_inductive(&mut env, list_decl()).expect("List admits");
    add_inductive(&mut env, or_decl()).expect("Or admits");
    add_inductive(&mut env, false_decl()).expect("False admits");
    add_inductive(&mut env, step_decl()).expect("Step admits");
    let env = def(
        env,
        "Nat.beq",
        &r_pi(nat(), r_pi(nat(), bool_ty())),
        &nat_beq_body(),
    );
    let env = register_bool_ops(env);
    let env = register_lit_ops(env);
    let env = register_clause_ops(env);
    let env = register_resolve(env);
    let env = register_nth(env);
    let env = register_step_accessors(env);
    let env = register_check_step(env);
    register_check_refutes(env)
}

// ===========================================================================
// Concrete data builders for a literal/clause/step in the kernel encoding.
// ===========================================================================
/// Literal `(var, neg)` -> Nat `2*var + neg`.
fn lit(var: u32, neg: bool) -> RawExpr {
    nat_lit(var * 2 + u32::from(neg))
}
/// Clause (list of (var,neg)) -> `List Nat`.
fn clause(lits: &[(u32, bool)]) -> RawExpr {
    let mut e = nil(nat());
    for &(v, neg) in lits.iter().rev() {
        e = cons(nat(), lit(v, neg), e);
    }
    e
}
/// Clause DB -> `List (List Nat)`.
fn clauses(cs: &[&[(u32, bool)]]) -> RawExpr {
    let mut e = nil(list_nat());
    for c in cs.iter().rev() {
        e = cons(list_nat(), clause(c), e);
    }
    e
}
/// One step `Step.mk resolvent prem1 prem2 pivotPosLit`.
fn step(resolvent: &[(u32, bool)], prem1: u32, prem2: u32, pivot_var: u32) -> RawExpr {
    r_apps(
        r_const("Step.mk"),
        vec![
            clause(resolvent),
            nat_lit(prem1),
            nat_lit(prem2),
            lit(pivot_var, false), // pivot recorded as POSITIVE literal of the var
        ],
    )
}
/// Refutation -> `List Step`.
fn refutation(steps: &[RawExpr]) -> RawExpr {
    let mut e = nil(r_const("Step"));
    for s in steps.iter().rev() {
        e = cons(r_const("Step"), s.clone(), e);
    }
    e
}
fn check_refutes(cs: RawExpr, pf: RawExpr) -> RawExpr {
    r_apps(r_const("checkRefutes"), vec![cs, pf])
}

// The canonical small UNSAT instance:  {(p), (¬p ∨ q), (¬q)}.
//   vars: p=0, q=1.  Encoding: p=0, ¬p=1, q=2, ¬q=3.
//   clauses[0] = (p)       = [0]
//   clauses[1] = (¬p ∨ q)  = [1,2]
//   clauses[2] = (¬q)      = [3]
// Refutation (2 steps to ∅):
//   step0: resolve clauses[0]=(p) with clauses[1]=(¬p∨q) on pivot p
//          => dropLit p [p] ++ dropLit ¬p [¬p,q] = [] ++ [q] = (q)   -> DB index 3
//   step1: resolve DB[3]=(q) with clauses[2]=(¬q) on pivot q
//          => dropLit q [q] ++ dropLit ¬q [¬q] = [] ++ [] = ∅        -> DB index 4
fn unsat_instance() -> RawExpr {
    clauses(&[&[(0, false)], &[(0, true), (1, false)], &[(1, true)]])
}
fn good_refutation() -> RawExpr {
    refutation(&[
        // (q) from prem 0 (p) and prem 1 (¬p∨q), pivot var p=0
        step(&[(1, false)], 0, 1, 0),
        // ∅ from prem 3 (the derived (q)) and prem 2 (¬q), pivot var q=1
        step(&[], 3, 2, 1),
    ])
}

// ===========================================================================
// Tests.
// ===========================================================================

fn is_bool_true(env: &MinimalEnv, term_raw: &RawExpr) -> bool {
    let t = Term::validate_closed(env, term_raw).expect("term validates");
    let mut budget = Budget::default_budget();
    // confirm it has type Bool first (the checker is total on this data).
    let ty = clean_ck0::infer(env, &t, &mut budget).expect("checkRefutes app infers");
    let bool_t = Term::validate_closed(env, &bool_ty()).expect("Bool");
    assert!(
        clean_ck0::is_def_eq(env, &ty, &bool_t, &mut budget).expect("def_eq ty"),
        "checkRefutes application has type Bool"
    );
    let tru = Term::validate_closed(env, &btrue()).expect("true");
    clean_ck0::is_def_eq(env, &t, &tru, &mut budget).expect("def_eq")
}

#[test]
fn test_checker_definitions_admit_and_kernel_check() {
    // Building the env runs `check` on every checker definition's body against its
    // declared type; if any failed, `def` panics. Also confirm Step.rec checks.
    let env = checker_env();
    let rec_ty = env.recursor_type(&n("Step")).expect("Step.rec type stored");
    let mut budget = Budget::default_budget();
    clean_ck0::infer_sort_in_context(&env, &[], &rec_ty, &mut budget)
        .expect("Step.rec kernel-checks");
}

#[test]
fn test_positive_reflected_recheck_reduces_to_true() {
    // THE HEADLINE: ck0 itself re-checks the resolution refutation by computation.
    let env = checker_env();
    let app = check_refutes(unsat_instance(), good_refutation());
    assert!(
        is_bool_true(&env, &app),
        "checkRefutes <UNSAT instance> <its refutation> must reduce to Bool.true in ck0"
    );
}

#[test]
fn test_negative_wrong_resolvent_reduces_to_false() {
    let env = checker_env();
    // Tamper step0's recorded resolvent: claim (p) instead of (q).
    let bad = refutation(&[
        step(&[(0, false)], 0, 1, 0), // WRONG: should be (q)=[2], claims (p)=[0]
        step(&[], 3, 2, 1),
    ]);
    let app = check_refutes(unsat_instance(), bad);
    assert!(
        !is_bool_true(&env, &app),
        "a wrong-resolvent refutation must NOT reduce to Bool.true"
    );
}

#[test]
fn test_negative_non_opposite_pivot_reduces_to_false() {
    let env = checker_env();
    // Use a pivot variable that does NOT occur with opposite polarities in the
    // premises: resolve clauses[0]=(p) and clauses[1]=(¬p∨q) but claim pivot var q.
    // Neither orientation's side condition (mem pivot a / mem neg-pivot b) holds.
    let bad = refutation(&[
        step(&[(1, false)], 0, 1, 1), // pivot var q=1, but q∉(p) and ¬q∉(¬p∨q)
        step(&[], 3, 2, 1),
    ]);
    let app = check_refutes(unsat_instance(), bad);
    assert!(
        !is_bool_true(&env, &app),
        "a non-opposite-pivot step must NOT reduce to Bool.true"
    );
}

#[test]
fn test_negative_nonempty_final_clause_reduces_to_false() {
    let env = checker_env();
    // A valid first step deriving (q), but the chain STOPS there: the final
    // recorded clause is (q), not ∅, so checkRefutes must reject.
    let bad = refutation(&[step(&[(1, false)], 0, 1, 0)]);
    let app = check_refutes(unsat_instance(), bad);
    assert!(
        !is_bool_true(&env, &app),
        "a refutation whose final clause is non-empty must NOT reduce to Bool.true"
    );
}

#[test]
fn test_negative_satisfiable_set_with_bogus_refutation_reduces_to_false() {
    let env = checker_env();
    // SATISFIABLE set {(p), (¬p ∨ p)} (true under p=⊤). The old double-polarity
    // resolve would derive ∅ from it; the correct single oriented resolve does NOT.
    //   clauses[0] = (p)      = [0]
    //   clauses[1] = (¬p ∨ p) = [1,0]
    // Bogus "refutation" claiming ∅ in one step on pivot p:
    //   resolve (p) (¬p∨p) p = dropLit p [p] ++ dropLit ¬p [¬p,p] = [] ++ [p] = (p) ≠ ∅
    let sat = clauses(&[&[(0, false)], &[(0, true), (0, false)]]);
    let bogus = refutation(&[step(&[], 0, 1, 0)]);
    let app = check_refutes(sat, bogus);
    assert!(
        !is_bool_true(&env, &app),
        "a satisfiable set with a bogus empty-clause refutation must NOT reduce to Bool.true \
         (the single oriented resolve is the #22 soundness fix)"
    );
}

#[test]
fn test_positive_components_reduce_as_expected() {
    // Spot-check the building blocks reduce correctly (so the positive result is
    // not a coincidence of two bugs cancelling).
    let env = checker_env();
    let mut budget = Budget::default_budget();
    let eq = |env: &MinimalEnv, budget: &mut Budget, a: &RawExpr, b: &RawExpr| -> bool {
        let ta = Term::validate_closed(env, a).expect("a validates");
        let tb = Term::validate_closed(env, b).expect("b validates");
        clean_ck0::is_def_eq(env, &ta, &tb, budget).expect("def_eq")
    };
    // litNeg p = ¬p, litNeg ¬p = p.
    assert!(
        eq(
            &env,
            &mut budget,
            &r_app(r_const("litNeg"), lit(0, false)),
            &lit(0, true)
        ),
        "litNeg p = ¬p"
    );
    assert!(
        eq(
            &env,
            &mut budget,
            &r_app(r_const("litNeg"), lit(0, true)),
            &lit(0, false)
        ),
        "litNeg ¬p = p"
    );
    // resolve (p) (¬p∨q) p = (q).
    let res = r_apps(
        r_const("resolve"),
        vec![
            clause(&[(0, false)]),
            clause(&[(0, true), (1, false)]),
            lit(0, false),
        ],
    );
    assert!(
        eq(&env, &mut budget, &res, &clause(&[(1, false)])),
        "resolve (p) (¬p∨q) p = (q)"
    );
    // Nat.beq 3 3 = true, Nat.beq 3 4 = false.
    assert!(
        eq(
            &env,
            &mut budget,
            &r_apps(r_const("Nat.beq"), vec![nat_lit(3), nat_lit(3)]),
            &btrue()
        ),
        "Nat.beq 3 3 = true"
    );
    assert!(
        eq(
            &env,
            &mut budget,
            &r_apps(r_const("Nat.beq"), vec![nat_lit(3), nat_lit(4)]),
            &bfalse()
        ),
        "Nat.beq 3 4 = false"
    );
}

// ===========================================================================
// SOUNDNESS BRIDGE.
//
// We STATE the soundness-bridge TYPE in ck0 (so the certificate STRUCTURE lives
// in the kernel) and PROVE the endpoint lemma `emptyClauseUnsat`. The full
// top-level bridge `checkRefutes cs pf = true -> Unsat cs` requires a fold
// induction over the refutation list and a single-step resolution metatheorem
// that are OUT of M0–M3 scope for a closed ck0 term; we do NOT fake it and do NOT
// register it as a Theorem/Axiom. See the honest status in the report.
//
//   Holds   : Nat -> Prop                          (literal-truth assignment, param)
//   clauseOr Holds c : Prop                        (right-folded Or of the literals)
//   Unsat cs := (Holds : Nat -> Prop) -> allTrue -> False  -- model: every clause
//                                                             holds => contradiction
//   emptyClauseUnsat : (Holds) -> clauseOr Holds nil -> False   PROVED (it is id,
//                                                  clauseOr Holds nil ≡ False).
// ===========================================================================

fn register_clause_or(env: MinimalEnv) -> MinimalEnv {
    // clauseOr Holds c := List.rec False (fun h _ ih => Or (Holds h) ih) c : Prop
    let holds_ty = r_pi(nat(), r_prop());
    let ty = r_pi(holds_ty.clone(), r_pi(list_nat(), r_prop()));
    let body = {
        //   bvars: ih=0, t=1, h=2, c=3, Holds=4
        let holds_h = r_app(r_bvar(4), r_bvar(2));
        let or = r_apps(r_const("Or"), vec![holds_h, r_bvar(0)]);
        let cc = r_lam(nat(), r_lam(list_nat(), r_lam(r_prop(), or)));
        // List.rec whose motive maps each list to a PROPOSITION (`Prop : Sort 1`):
        // the motive's codomain sort is `Sort 1`, so the Elim motive-level is 1.
        let elim = RawExpr::Elim(n("List"), lone(), vec![lone()]);
        let motive = r_lam(list_nat(), r_prop());
        r_lam(
            holds_ty.clone(),
            r_lam(
                list_nat(),
                r_apps(elim, vec![nat(), motive, r_const("False"), cc, r_bvar(0)]),
            ),
        )
    };
    def(env, "clauseOr", &ty, &body)
}

#[test]
fn test_soundness_clause_or_nil_is_false_and_empty_clause_unsat_proved() {
    let env = register_clause_or(checker_env());
    let mut budget = Budget::default_budget();

    // clauseOr Holds nil ≡ False, for a parameter Holds. We check the STATEMENT
    // type and prove emptyClauseUnsat as the identity.
    let holds_ty = r_pi(nat(), r_prop());

    // emptyClauseUnsat : (Holds : Nat -> Prop) -> clauseOr Holds nil -> False
    //                  := fun Holds h => h
    // (h : clauseOr Holds nil; since clauseOr Holds nil ι-reduces to False, the
    //  identity is a proof.)
    let ty = r_pi(
        holds_ty.clone(),
        r_pi(
            r_apps(r_const("clauseOr"), vec![r_bvar(0), nil(nat())]),
            r_const("False"),
        ),
    );
    let proof = r_lam(
        holds_ty.clone(),
        r_lam(
            r_apps(r_const("clauseOr"), vec![r_bvar(0), nil(nat())]),
            r_bvar(0),
        ),
    );
    let ty_t = Term::validate_closed(&env, &ty).expect("emptyClauseUnsat type validates");
    // It is a well-formed Prop.
    let sort = clean_ck0::infer_sort_in_context(&env, &[], &ty_t, &mut budget)
        .expect("emptyClauseUnsat type is a well-formed type");
    assert!(sort.is_zero(), "emptyClauseUnsat statement lives in Prop");
    // The proof CHECKS — this is a real (foundational) proof of the endpoint lemma.
    let proof_t = Term::validate_closed(&env, &proof).expect("proof validates");
    clean_ck0::check(&env, &proof_t, &ty_t, &mut budget)
        .expect("emptyClauseUnsat: identity proof checks (clauseOr Holds nil ≡ False)");
}

#[test]
fn test_soundness_bridge_type_is_well_formed_in_ck0() {
    // We STATE the full bridge TYPE so the certificate structure is in ck0, and
    // confirm it kernel-checks to Prop. We do NOT register a proof (honest gap).
    //
    //   Unsat cs := (Holds : Nat -> Prop) ->
    //               (allHold : <every clause of cs has clauseOr Holds true>) -> False
    // To keep the stated type self-contained and kernel-checkable, we use the
    // direct unfolded model on our concrete 3-clause instance:
    //   Unsat3 cs := (Holds) -> clauseOr Holds cs0 -> clauseOr Holds cs1
    //                         -> clauseOr Holds cs2 -> False
    // and state:
    //   bridge : checkRefutes cs pf = true -> Unsat3 cs0 cs1 cs2
    // We assert ONLY that this TYPE is a well-formed Prop in ck0 (the cert
    // structure), not that it is inhabited.
    let env = register_clause_or(checker_env());
    let mut budget = Budget::default_budget();

    // Eq : {A : Sort u} -> A -> A -> Prop  — admit just enough to state `= true`.
    let env = {
        let b = boot(&[("Eq", 1), ("Eq.refl", 1)]);
        let eq_ty = r_pi(r_sort_param(0), r_pi(r_bvar(0), r_pi(r_bvar(1), r_prop())));
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
        let eq_decl = InductiveDecl {
            name: n("Eq"),
            num_level_params: 1,
            num_params: 2,
            type_: vlvl(&b, &eq_ty, 1),
            constructors: vec![Constructor {
                name: n("Eq.refl"),
                type_: vlvl(&b, &refl_ty, 1),
            }],
        };
        let mut env = env;
        add_inductive(&mut env, eq_decl).expect("Eq admits");
        env
    };

    let holds_ty = r_pi(nat(), r_prop());
    let c0 = clause(&[(0, false)]);
    let c1 = clause(&[(0, true), (1, false)]);
    let c2 = clause(&[(1, true)]);
    // `Holds` is bound by the outermost pi; each nested arrow shifts its de Bruijn
    // index by one (c0 at depth 0, c1 at depth 1, c2 at depth 2).
    let clause_or =
        |holds_db: u32, c: RawExpr| r_apps(r_const("clauseOr"), vec![r_bvar(holds_db), c]);
    // Unsat3 := (Holds) -> clauseOr Holds c0 -> clauseOr Holds c1 -> clauseOr Holds c2 -> False
    let unsat3 = r_pi(
        holds_ty.clone(),
        r_pi(
            clause_or(0, c0.clone()),
            r_pi(
                clause_or(1, c1.clone()),
                r_pi(clause_or(2, c2.clone()), r_const("False")),
            ),
        ),
    );
    // checkRefutes cs pf = true   (Eq Bool (checkRefutes cs pf) Bool.true)
    let cr = check_refutes(unsat_instance(), good_refutation());
    let hyp = r_apps(r_const_p("Eq", vec![lone()]), vec![bool_ty(), cr, btrue()]);
    // bridge type: hyp -> Unsat3
    let bridge_ty = r_pi(hyp, unsat3);
    let bridge_t = Term::validate_closed(&env, &bridge_ty).expect("bridge type validates");
    let sort = clean_ck0::infer_sort_in_context(&env, &[], &bridge_t, &mut budget)
        .expect("soundness-bridge TYPE kernel-checks");
    assert!(sort.is_zero(), "soundness-bridge type lives in Prop");
}
