// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ck0 Farkas certificate — the "AI / LRA kingdom" re-check IN the minimal
//! kernel.
//!
//! This is the #28 reflection pattern (see `tests/m5_reflection_cert.rs`, which
//! re-checks a SOFTWARE resolution refutation by reflection) applied to the
//! AI/LRA kingdom: a FARKAS infeasibility certificate for a system of integer
//! linear constraints is re-checked by REFLECTION — a computational checker
//! `farkasChecks : Rows -> Bounds -> Mults -> Bool` is built entirely as ck0
//! `Definition`s over ck0 inductives, ck0 type-checks those definitions, and
//! ck0's own `is_def_eq` reduces `farkasChecks <system> <y>` to `Bool.true` by
//! ι/δ computation on the concrete certificate data.
//!
//! NOTHING here is new trusted kernel source: the checker lives only in this
//! test, as terms the kernel CHECKS and EVALUATES. The kernel's only jobs are
//! (a) admit the inductives + checker definitions (so they kernel-check) and
//! (b) reduce `farkasChecks` on concrete data.
//!
//! THE MECHANISM (Farkas' lemma)
//! -----------------------------
//! A system of linear constraints  Σ_j a_ij x_j ≤ b_i  (i = 1..m) is INFEASIBLE
//! if there exist nonneg multipliers y_i ≥ 0 with
//!     (1)  Σ_i y_i a_ij = 0   for every variable column j,        AND
//!     (2)  Σ_i y_i b_i  < 0.
//! Then  0 = Σ_j (Σ_i y_i a_ij) x_j = Σ_i y_i (Σ_j a_ij x_j) ≤ Σ_i y_i b_i < 0,
//! i.e. `0 ≤ (negative)` — a contradiction, so no assignment x exists.
//! The certificate is the multiplier vector y; the checker verifies (1), (2),
//! and y_i ≥ 0 by arithmetic.
//!
//! INT ENCODING
//! ------------
//! Coefficients are signed, so we build a signed-integer layer over ck0's `Nat`
//! as a difference pair `Int.mk (pos neg : Nat)` denoting `pos - neg` (no
//! normalization needed — every op is defined to respect the equivalence
//! `(p,n) ~ (p',n')  iff  p + n' = p' + n`):
//!   intAdd a b = mk (a.pos + b.pos)               (a.neg + b.neg)
//!   intMul a b = mk (a.pos*b.pos + a.neg*b.neg)   (a.pos*b.neg + a.neg*b.pos)
//!   intLe  a b = (a.pos + b.neg) ≤Nat (b.pos + a.neg)
//!   intLt  a b = (a.pos + b.neg) <Nat (b.pos + a.neg)
//! These are total, fail-closed, and COMPUTE (see `test_int_arithmetic_probes`).

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, Budget, Constructor, Env, InductiveDecl, MinimalEnv, Name, RawExpr, RawLevel,
    Term, Transparency,
};

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

// ---- RawExpr builders (mirrors m5_reflection_cert.rs) ----
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
fn int() -> RawExpr {
    r_const("Int")
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

// All list element types here (Int, List Int) live in `Type 0 = Sort 1`, so the
// `List` level parameter is `1`: `List.{1} Int`, `List.{1} (List Int)`, etc.
fn list_int() -> RawExpr {
    r_app(r_const_p("List", vec![lone()]), int())
}
fn list_list_int() -> RawExpr {
    r_app(r_const_p("List", vec![lone()]), list_int())
}
fn nil(elem: RawExpr) -> RawExpr {
    r_app(r_const_p("List.nil", vec![lone()]), elem)
}
fn cons(elem: RawExpr, h: RawExpr, t: RawExpr) -> RawExpr {
    r_apps(r_const_p("List.cons", vec![lone()]), vec![elem, h, t])
}
/// `List.rec.{motive,1}`: motive (closed result type `ret`), nil case, cons
/// case, major. `elem` is the element type (in `Type 0`, so elem-level = 1).
fn list_rec(
    elem: RawExpr,
    ret: RawExpr,
    nil_case: RawExpr,
    cons_case: RawExpr,
    major: RawExpr,
) -> RawExpr {
    let elim = RawExpr::Elim(n("List"), lone(), vec![lone()]);
    let motive = r_lam(r_app(r_const_p("List", vec![lone()]), elem.clone()), ret);
    r_apps(elim, vec![elem, motive, nil_case, cons_case, major])
}
/// `Bool.rec.{1}` into a `Sort 1` result `ret`: false case, true case, scrut.
fn bool_rec(ret: RawExpr, false_case: RawExpr, true_case: RawExpr, scrut: RawExpr) -> RawExpr {
    let elim = RawExpr::Elim(n("Bool"), lone(), vec![]);
    let motive = r_lam(bool_ty(), ret);
    r_apps(elim, vec![motive, false_case, true_case, scrut])
}

// ===========================================================================
// Base inductives: Bool, Nat, List, Int, False.
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
fn r_sort_param(i: u32) -> RawExpr {
    RawExpr::Sort(RawLevel::Param(i))
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

/// `Int : Type` with single ctor `Int.mk (pos neg : Nat)`, denoting `pos - neg`.
fn int_decl() -> InductiveDecl {
    let b = boot(&[("Int", 0), ("Int.mk", 0), ("Nat", 0)]);
    // mk : Nat -> Nat -> Int
    let mk_ty = r_pi(nat(), r_pi(nat(), int()));
    InductiveDecl {
        name: n("Int"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_sort(1), 0),
        constructors: vec![Constructor {
            name: n("Int.mk"),
            type_: vlvl(&b, &mk_ty, 0),
        }],
    }
}

// ===========================================================================
// The checker, built as transparent ck0 Definitions over the recursors.
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

// ---- Nat ops: add, mul, le, lt via Nat.rec / Bool.rec ----

/// natAdd m n := Nat.rec (motive := fun _ => Nat) m (fun _ ih => succ ih) n
/// (recurse on 2nd arg, Lean convention): add m 0 = m, add m (S k) = S(add m k).
fn nat_add_body() -> RawExpr {
    let elim = RawExpr::Elim(n("Nat"), lone(), vec![]);
    let motive = r_lam(nat(), nat());
    let base = r_bvar(1); // m
    let step = r_lam(nat(), r_lam(nat(), nat_succ(r_bvar(0)))); // λ k ih => succ ih
    r_lam(
        nat(),
        r_lam(nat(), r_apps(elim, vec![motive, base, step, r_bvar(0)])),
    )
}

/// natMul m n := Nat.rec (fun _ => Nat) 0 (fun _ ih => natAdd ih m) n
/// mul m 0 = 0, mul m (S k) = (mul m k) + m.
fn nat_mul_body() -> RawExpr {
    let elim = RawExpr::Elim(n("Nat"), lone(), vec![]);
    let motive = r_lam(nat(), nat());
    let base = nat_lit(0);
    // step: λ (k:Nat)(ih:Nat) => natAdd ih m  ; bvars: ih=0, k=1, n=2, m=3
    let step = r_lam(
        nat(),
        r_lam(nat(), r_apps(r_const("natAdd"), vec![r_bvar(0), r_bvar(3)])),
    );
    r_lam(
        nat(),
        r_lam(nat(), r_apps(elim, vec![motive, base, step, r_bvar(0)])),
    )
}

/// natLe m n : Bool — structural double Nat.rec.
///   le 0     _     = true
///   le (S _) 0     = false
///   le (S k) (S j) = le k j
/// natLe m n := (Nat.rec (motive:=fun _ => Nat -> Bool)
///   /-0-/   (fun _ => true)
///   /-S k-/ (fun k ih => fun n => Nat.rec (fun _=>Bool) false (fun j _ => ih j) n)
///   m) n
fn nat_le_body() -> RawExpr {
    let nat_to_bool = r_pi(nat(), bool_ty());
    let elim = RawExpr::Elim(n("Nat"), lone(), vec![]);
    let motive = r_lam(nat(), nat_to_bool.clone());
    // zero case: fun (_n : Nat) => true
    let zero_case = r_lam(nat(), btrue());
    // succ case: fun (k : Nat) (ih : Nat -> Bool) (n : Nat) =>
    //   Nat.rec (fun _ => Bool) false (fun j _ => ih j) n
    let succ_case = {
        let inner_elim = RawExpr::Elim(n("Nat"), lone(), vec![]);
        let inner_motive = r_lam(nat(), bool_ty());
        // inner succ: fun (j:Nat)(_:Bool) => ih j ; ih is bvar 3 here
        let inner_succ = r_lam(nat(), r_lam(bool_ty(), r_app(r_bvar(3), r_bvar(1))));
        let inner = r_apps(
            inner_elim,
            vec![inner_motive, bfalse(), inner_succ, r_bvar(0)],
        );
        r_lam(nat(), r_lam(nat_to_bool.clone(), r_lam(nat(), inner)))
    };
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

/// natLt m n := natLe (succ m) n.
fn nat_lt_body() -> RawExpr {
    r_lam(
        nat(),
        r_lam(
            nat(),
            r_apps(r_const("natLe"), vec![nat_succ(r_bvar(1)), r_bvar(0)]),
        ),
    )
}

fn register_nat_ops(env: MinimalEnv) -> MinimalEnv {
    let nn = r_pi(nat(), r_pi(nat(), nat()));
    let nb = r_pi(nat(), r_pi(nat(), bool_ty()));
    let env = def(env, "natAdd", &nn, &nat_add_body());
    let env = def(env, "natMul", &nn, &nat_mul_body());
    let env = def(env, "natLe", &nb, &nat_le_body());
    def(env, "natLt", &nb, &nat_lt_body())
}

// ---- Bool ops: and via Bool.rec ----
fn band(x: RawExpr, y: RawExpr) -> RawExpr {
    r_apps(r_const("band"), vec![x, y])
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
    def(env, "band", &bb, &band_body)
}

// ===========================================================================
// Int layer over Nat (difference pairs).
// ===========================================================================

fn na(x: RawExpr, y: RawExpr) -> RawExpr {
    r_apps(r_const("natAdd"), vec![x, y])
}
fn nm(x: RawExpr, y: RawExpr) -> RawExpr {
    r_apps(r_const("natMul"), vec![x, y])
}

fn register_int_ops(env: MinimalEnv) -> MinimalEnv {
    // intPos i := Int.rec (fun p n => p) i  ;  intNeg i := Int.rec (fun p n => n) i
    let int_to_nat = r_pi(int(), nat());
    let pos_body = {
        // mk_case binds pos, neg. bvars: neg=0, pos=1.
        let mk_case = r_lam(nat(), r_lam(nat(), r_bvar(1)));
        let elim = RawExpr::Elim(n("Int"), lone(), vec![]);
        let motive = r_lam(int(), nat());
        r_lam(int(), r_apps(elim, vec![motive, mk_case, r_bvar(0)]))
    };
    let env = def(env, "intPos", &int_to_nat, &pos_body);
    let neg_body = {
        let mk_case = r_lam(nat(), r_lam(nat(), r_bvar(0)));
        let elim = RawExpr::Elim(n("Int"), lone(), vec![]);
        let motive = r_lam(int(), nat());
        r_lam(int(), r_apps(elim, vec![motive, mk_case, r_bvar(0)]))
    };
    let env = def(env, "intNeg", &int_to_nat, &neg_body);

    let ii_i = r_pi(int(), r_pi(int(), int()));
    let ii_b = r_pi(int(), r_pi(int(), bool_ty()));
    let mk = |p: RawExpr, q: RawExpr| r_apps(r_const("Int.mk"), vec![p, q]);
    let pos = |x: RawExpr| r_app(r_const("intPos"), x);
    let neg = |x: RawExpr| r_app(r_const("intNeg"), x);

    // intAdd a b := mk (a.pos + b.pos) (a.neg + b.neg)   ; bvars: b=0, a=1
    let add_body = {
        let p = na(pos(r_bvar(1)), pos(r_bvar(0)));
        let q = na(neg(r_bvar(1)), neg(r_bvar(0)));
        r_lam(int(), r_lam(int(), mk(p, q)))
    };
    let env = def(env, "intAdd", &ii_i, &add_body);

    // intMul a b := mk (a.pos*b.pos + a.neg*b.neg) (a.pos*b.neg + a.neg*b.pos)
    let mul_body = {
        let ap = || pos(r_bvar(1));
        let an = || neg(r_bvar(1));
        let bp = || pos(r_bvar(0));
        let bn = || neg(r_bvar(0));
        let p = na(nm(ap(), bp()), nm(an(), bn()));
        let q = na(nm(ap(), bn()), nm(an(), bp()));
        r_lam(int(), r_lam(int(), mk(p, q)))
    };
    let env = def(env, "intMul", &ii_i, &mul_body);

    // intLe a b := natLe (a.pos + b.neg) (b.pos + a.neg)   (a-b ≤ 0 ⇔ a ≤ b)
    let le_body = {
        let lhs = na(pos(r_bvar(1)), neg(r_bvar(0)));
        let rhs = na(pos(r_bvar(0)), neg(r_bvar(1)));
        r_lam(
            int(),
            r_lam(int(), r_apps(r_const("natLe"), vec![lhs, rhs])),
        )
    };
    let env = def(env, "intLe", &ii_b, &le_body);

    // intLt a b := natLt (a.pos + b.neg) (b.pos + a.neg)
    let lt_body = {
        let lhs = na(pos(r_bvar(1)), neg(r_bvar(0)));
        let rhs = na(pos(r_bvar(0)), neg(r_bvar(1)));
        r_lam(
            int(),
            r_lam(int(), r_apps(r_const("natLt"), vec![lhs, rhs])),
        )
    };
    let env = def(env, "intLt", &ii_b, &lt_body);

    // intEqZero i := band (natLe i.pos i.neg) (natLe i.neg i.pos)
    //   (i = 0 ⇔ pos ≤ neg ∧ neg ≤ pos ⇔ pos = neg)
    let eqz_ty = r_pi(int(), bool_ty());
    let eqz_body = r_lam(
        int(),
        band(
            r_apps(r_const("natLe"), vec![pos(r_bvar(0)), neg(r_bvar(0))]),
            r_apps(r_const("natLe"), vec![neg(r_bvar(0)), pos(r_bvar(0))]),
        ),
    );
    let env = def(env, "intEqZero", &eqz_ty, &eqz_body);

    // intIsNeg i := intLt i 0   (i.e. i < 0)
    let isneg_body = r_lam(
        int(),
        r_apps(
            r_const("intLt"),
            vec![r_bvar(0), mk(nat_lit(0), nat_lit(0))],
        ),
    );
    let env = def(env, "intIsNeg", &eqz_ty, &isneg_body);

    // intIsNonneg i := natLe i.neg i.pos   (i.e. 0 ≤ i)
    let nonneg_body = r_lam(
        int(),
        r_apps(r_const("natLe"), vec![neg(r_bvar(0)), pos(r_bvar(0))]),
    );
    let env = def(env, "intIsNonneg", &eqz_ty, &nonneg_body);

    // intEq a b := band (intLe a b) (intLe b a)  — SEMANTIC equality (the
    // difference-pair rep is non-normalized, so structural `is_def_eq` on raw
    // `Int.mk` forms is NOT semantic equality; tests compare via `intEq`).
    let eq_body = r_lam(
        int(),
        r_lam(
            int(),
            band(
                r_apps(r_const("intLe"), vec![r_bvar(1), r_bvar(0)]),
                r_apps(r_const("intLe"), vec![r_bvar(0), r_bvar(1)]),
            ),
        ),
    );
    def(env, "intEq", &ii_b, &eq_body)
}

// ===========================================================================
// The Farkas checker.
//
// rows   : List (List Int)   — each row is the coefficient vector a_i*.
// bounds : List Int          — the bound b_i for each row.
// mults  : List Int          — the multiplier y_i for each row (nonneg).
//
// We require all three lists parallel (same length m). For the column
// combination, every row must have the same number of columns; we fold the
// scaled rows componentwise.
// ===========================================================================

fn register_int0(env: MinimalEnv) -> MinimalEnv {
    // int0 : Int := mk 0 0  (a named zero so we can build vectors of it)
    let body = r_apps(r_const("Int.mk"), vec![nat_lit(0), nat_lit(0)]);
    def(env, "int0", &int(), &body)
}

fn register_zip_combine(env: MinimalEnv) -> MinimalEnv {
    // intListAdd : List Int -> List Int -> List Int (componentwise; the shorter
    // list's tail is taken from the longer — but our data is rectangular so
    // lengths match). Defined by recursion on the first list:
    //   intListAdd nil ys := ys
    //   intListAdd (x::xs) ys := cons (intAdd x (head0 ys)) (intListAdd xs (tail ys))
    // To keep it a clean single List.rec we instead recurse with ys threaded.
    //
    //   go : List Int -> (List Int -> List Int)
    //   go nil       := fun ys => ys
    //   go (x::xs)   := fun ys => cons (intAdd x (headZ ys)) (ihf (tailZ ys))
    // intListAdd xs ys := (List.rec ... xs) ys
    let li = || list_int();
    let li_li = r_pi(list_int(), list_int());

    // headZ ys := List.rec int0 (fun h _ _ => h) ys
    let headz_ty = r_pi(list_int(), int());
    let headz_body = {
        // cons case: fun (h:Int)(t:List Int)(ih:Int) => h ; bvars: ih=0,t=1,h=2
        let cc = r_lam(int(), r_lam(list_int(), r_lam(int(), r_bvar(2))));
        r_lam(
            list_int(),
            list_rec(int(), int(), r_const("int0"), cc, r_bvar(0)),
        )
    };
    let env = def(env, "headZ", &headz_ty, &headz_body);

    // tailZ ys := List.rec nil (fun _ t _ => t) ys
    let tailz_ty = r_pi(list_int(), list_int());
    let tailz_body = {
        let cc = r_lam(int(), r_lam(list_int(), r_lam(list_int(), r_bvar(1))));
        r_lam(
            list_int(),
            list_rec(int(), list_int(), nil(int()), cc, r_bvar(0)),
        )
    };
    let env = def(env, "tailZ", &tailz_ty, &tailz_body);

    // intListAdd xs ys := (List.rec (motive := fun _ => List Int -> List Int)
    //   (fun ys => ys)
    //   (fun x xs ihf => fun ys =>
    //       cons (intAdd x (headZ ys)) (ihf (tailZ ys)))
    //   xs) ys
    let intlistadd_ty = r_pi(list_int(), r_pi(list_int(), list_int()));
    let intlistadd_body = {
        let nil_case = r_lam(list_int(), r_bvar(0)); // fun ys => ys
                                                     // cons case: fun (x:Int)(xs:List Int)(ihf:List Int->List Int)(ys:List Int) => ...
                                                     //   bvars: ys=0, ihf=1, xs=2, x=3
        let cons_case = {
            let x = r_bvar(3);
            let ihf = r_bvar(1);
            let ys = r_bvar(0);
            let head = r_apps(
                r_const("intAdd"),
                vec![x, r_app(r_const("headZ"), ys.clone())],
            );
            let rest = r_app(ihf, r_app(r_const("tailZ"), ys));
            let body = cons(int(), head, rest);
            r_lam(
                int(),
                r_lam(list_int(), r_lam(li_li.clone(), r_lam(list_int(), body))),
            )
        };
        let elim = RawExpr::Elim(n("List"), lone(), vec![lone()]);
        let motive = r_lam(list_int(), li_li.clone());
        let folded = r_apps(elim, vec![int(), motive, nil_case, cons_case, r_bvar(1)]);
        r_lam(list_int(), r_lam(list_int(), r_app(folded, r_bvar(0))))
    };
    let env = def(env, "intListAdd", &intlistadd_ty, &intlistadd_body);

    // intListScale : Int -> List Int -> List Int
    //   intListScale s xs := List.rec nil (fun h _ ih => cons (intMul s h) ih) xs
    let scale_ty = r_pi(int(), r_pi(list_int(), list_int()));
    let scale_body = {
        // cons case: fun (h:Int)(t:List Int)(ih:List Int) => cons (intMul s h) ih
        //   bvars: ih=0, t=1, h=2, xs=3, s=4
        let mul = r_apps(r_const("intMul"), vec![r_bvar(4), r_bvar(2)]);
        let cc = r_lam(
            int(),
            r_lam(list_int(), r_lam(list_int(), cons(int(), mul, r_bvar(0)))),
        );
        r_lam(
            int(),
            r_lam(list_int(), list_rec(int(), li(), nil(int()), cc, r_bvar(0))),
        )
    };
    def(env, "intListScale", &scale_ty, &scale_body)
}

fn register_all_eqzero(env: MinimalEnv) -> MinimalEnv {
    // allEqZero : List Int -> Bool := List.rec true (fun h _ ih => band (intEqZero h) ih)
    let ty = r_pi(list_int(), bool_ty());
    let body = {
        let eqz = r_app(r_const("intEqZero"), r_bvar(2));
        let cc = r_lam(
            int(),
            r_lam(list_int(), r_lam(bool_ty(), band(eqz, r_bvar(0)))),
        );
        r_lam(
            list_int(),
            list_rec(int(), bool_ty(), btrue(), cc, r_bvar(0)),
        )
    };
    def(env, "allEqZero", &ty, &body)
}

fn register_combine_columns(env: MinimalEnv) -> MinimalEnv {
    // combineColumns : List (List Int) -> List Int -> List Int
    //   given rows and mults (parallel), returns Σ_i y_i * row_i (componentwise).
    //   go : List(List Int) -> (List Int -> List Int)   -- threads mults
    //     go nil          := fun _ => nil
    //     go (row::rows)  := fun ms =>
    //        intListAdd (intListScale (headZ ms) row) (ihf (tailZ ms))
    //   combineColumns rows mults := (List.rec ... rows) mults
    let ms_to_li = r_pi(list_int(), list_int());
    let ty = r_pi(list_list_int(), r_pi(list_int(), list_int()));
    let body = {
        let nil_case = r_lam(list_int(), nil(int())); // fun _ => nil
                                                      // cons case: fun (row:List Int)(rows:List(List Int))(ihf:List Int->List Int)(ms:List Int)
                                                      //   bvars: ms=0, ihf=1, rows=2, row=3
        let cons_case = {
            let row = r_bvar(3);
            let ihf = r_bvar(1);
            let ms = r_bvar(0);
            let scaled = r_apps(
                r_const("intListScale"),
                vec![r_app(r_const("headZ"), ms.clone()), row],
            );
            let rest = r_app(ihf, r_app(r_const("tailZ"), ms));
            let body = r_apps(r_const("intListAdd"), vec![scaled, rest]);
            r_lam(
                list_int(),
                r_lam(
                    list_list_int(),
                    r_lam(ms_to_li.clone(), r_lam(list_int(), body)),
                ),
            )
        };
        let elim = RawExpr::Elim(n("List"), lone(), vec![lone()]);
        let motive = r_lam(list_list_int(), ms_to_li.clone());
        let folded = r_apps(
            elim,
            vec![list_int(), motive, nil_case, cons_case, r_bvar(1)],
        );
        r_lam(list_list_int(), r_lam(list_int(), r_app(folded, r_bvar(0))))
    };
    def(env, "combineColumns", &ty, &body)
}

fn register_dot(env: MinimalEnv) -> MinimalEnv {
    // intDot : List Int -> List Int -> Int  (Σ_i x_i y_i), recurse on first.
    //   go : List Int -> (List Int -> Int)
    //     go nil       := fun _  => int0
    //     go (x::xs)   := fun ys => intAdd (intMul x (headZ ys)) (ihf (tailZ ys))
    let ys_to_int = r_pi(list_int(), int());
    let ty = r_pi(list_int(), r_pi(list_int(), int()));
    let body = {
        let nil_case = r_lam(list_int(), r_const("int0"));
        // cons case: fun (x:Int)(xs:List Int)(ihf:List Int->Int)(ys:List Int)
        //   bvars: ys=0, ihf=1, xs=2, x=3
        let cons_case = {
            let x = r_bvar(3);
            let ihf = r_bvar(1);
            let ys = r_bvar(0);
            let prod = r_apps(
                r_const("intMul"),
                vec![x, r_app(r_const("headZ"), ys.clone())],
            );
            let rest = r_app(ihf, r_app(r_const("tailZ"), ys));
            let body = r_apps(r_const("intAdd"), vec![prod, rest]);
            r_lam(
                int(),
                r_lam(
                    list_int(),
                    r_lam(ys_to_int.clone(), r_lam(list_int(), body)),
                ),
            )
        };
        let elim = RawExpr::Elim(n("List"), lone(), vec![lone()]);
        let motive = r_lam(list_int(), ys_to_int.clone());
        let folded = r_apps(elim, vec![int(), motive, nil_case, cons_case, r_bvar(1)]);
        r_lam(list_int(), r_lam(list_int(), r_app(folded, r_bvar(0))))
    };
    def(env, "intDot", &ty, &body)
}

fn register_all_nonneg(env: MinimalEnv) -> MinimalEnv {
    // allNonneg : List Int -> Bool := List.rec true (fun h _ ih => band (intIsNonneg h) ih)
    let ty = r_pi(list_int(), bool_ty());
    let body = {
        let nn = r_app(r_const("intIsNonneg"), r_bvar(2));
        let cc = r_lam(
            int(),
            r_lam(list_int(), r_lam(bool_ty(), band(nn, r_bvar(0)))),
        );
        r_lam(
            list_int(),
            list_rec(int(), bool_ty(), btrue(), cc, r_bvar(0)),
        )
    };
    def(env, "allNonneg", &ty, &body)
}

fn register_farkas_checks(env: MinimalEnv) -> MinimalEnv {
    // farkasChecks rows bounds mults :=
    //   band (allNonneg mults)                              -- (y_i ≥ 0)
    //   (band (allEqZero (combineColumns rows mults))       -- (Σ y_i a_ij = 0)
    //         (intIsNeg (intDot mults bounds)))             -- (Σ y_i b_i < 0)
    let ty = r_pi(
        list_list_int(),
        r_pi(list_int(), r_pi(list_int(), bool_ty())),
    );
    let body = {
        // bvars: mults=0, bounds=1, rows=2
        let nonneg = r_app(r_const("allNonneg"), r_bvar(0));
        let combo = r_apps(r_const("combineColumns"), vec![r_bvar(2), r_bvar(0)]);
        let cols_zero = r_app(r_const("allEqZero"), combo);
        let dot = r_apps(r_const("intDot"), vec![r_bvar(0), r_bvar(1)]);
        let bound_neg = r_app(r_const("intIsNeg"), dot);
        let inner = band(cols_zero, bound_neg);
        let body = band(nonneg, inner);
        r_lam(list_list_int(), r_lam(list_int(), r_lam(list_int(), body)))
    };
    def(env, "farkasChecks", &ty, &body)
}

// ===========================================================================
// Full environment.
// ===========================================================================
fn checker_env() -> MinimalEnv {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, bool_decl()).expect("Bool admits");
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    add_inductive(&mut env, list_decl()).expect("List admits");
    add_inductive(&mut env, false_decl()).expect("False admits");
    add_inductive(&mut env, int_decl()).expect("Int admits");
    let env = register_nat_ops(env);
    let env = register_bool_ops(env);
    let env = register_int_ops(env);
    let env = register_int0(env);
    let env = register_zip_combine(env);
    let env = register_all_eqzero(env);
    let env = register_combine_columns(env);
    let env = register_dot(env);
    let env = register_all_nonneg(env);
    register_farkas_checks(env)
}

// ===========================================================================
// Concrete data builders.
// ===========================================================================
/// A signed integer literal `k` -> `Int.mk |k| 0` (k≥0) or `Int.mk 0 |k|` (k<0).
fn int_lit(k: i64) -> RawExpr {
    if k >= 0 {
        let m = u32::try_from(k).expect("small literal");
        r_apps(r_const("Int.mk"), vec![nat_lit(m), nat_lit(0)])
    } else {
        let m = u32::try_from(-k).expect("small literal");
        r_apps(r_const("Int.mk"), vec![nat_lit(0), nat_lit(m)])
    }
}
/// A row / vector of Int.
fn ints(xs: &[i64]) -> RawExpr {
    let mut e = nil(int());
    for &x in xs.iter().rev() {
        e = cons(int(), int_lit(x), e);
    }
    e
}
/// Rows = List (List Int).
fn rows(rs: &[&[i64]]) -> RawExpr {
    let mut e = nil(list_int());
    for r in rs.iter().rev() {
        e = cons(list_int(), ints(r), e);
    }
    e
}

fn farkas_checks(rows_e: RawExpr, bounds_e: RawExpr, mults_e: RawExpr) -> RawExpr {
    r_apps(r_const("farkasChecks"), vec![rows_e, bounds_e, mults_e])
}

// ---- helpers for reduction assertions ----
fn reduces_to(env: &MinimalEnv, term_raw: &RawExpr, target_raw: &RawExpr) -> bool {
    let t = Term::validate_closed(env, term_raw).expect("term validates");
    let target = Term::validate_closed(env, target_raw).expect("target validates");
    let mut budget = Budget::default_budget();
    clean_ck0::is_def_eq(env, &t, &target, &mut budget).expect("def_eq")
}
fn is_bool_true(env: &MinimalEnv, term_raw: &RawExpr) -> bool {
    let t = Term::validate_closed(env, term_raw).expect("term validates");
    let mut budget = Budget::default_budget();
    // confirm it has type Bool first.
    let ty = clean_ck0::infer(env, &t, &mut budget).expect("farkasChecks app infers");
    let bool_t = Term::validate_closed(env, &bool_ty()).expect("Bool");
    assert!(
        clean_ck0::is_def_eq(env, &ty, &bool_t, &mut budget).expect("def_eq ty"),
        "farkasChecks application has type Bool"
    );
    let tru = Term::validate_closed(env, &btrue()).expect("true");
    clean_ck0::is_def_eq(env, &t, &tru, &mut budget).expect("def_eq")
}

// ===========================================================================
// THE INFEASIBLE INSTANCE + CERT.
//
//   x ≤ -1   (row [1],  bound -1)      i.e.  x ≤ -1
//  -x ≤ -1   (row [-1], bound -1)      i.e.  x ≥ 1
// Multipliers y = (1, 1):
//   column sum: 1*1 + 1*(-1) = 0                         ✓ (1)
//   bound sum:  1*(-1) + 1*(-1) = -2 < 0                 ✓ (2)
//   y ≥ 0                                                ✓
// ===========================================================================
fn infeasible_rows() -> RawExpr {
    rows(&[&[1], &[-1]])
}
fn infeasible_bounds() -> RawExpr {
    ints(&[-1, -1])
}
fn good_mults() -> RawExpr {
    ints(&[1, 1])
}

// ===========================================================================
// Tests.
// ===========================================================================

#[test]
fn test_checker_definitions_admit_and_kernel_check() {
    // Building the env runs `check` on every checker definition's body against
    // its declared type; if any failed, `def` would panic. Also confirm Int.rec
    // kernel-checks.
    let env = checker_env();
    let rec_ty = env.recursor_type(&n("Int")).expect("Int.rec type stored");
    let mut budget = Budget::default_budget();
    clean_ck0::infer_sort_in_context(&env, &[], &rec_ty, &mut budget)
        .expect("Int.rec kernel-checks");
}

#[test]
fn test_int_arithmetic_probes() {
    // Probe that intAdd / intMul / intLt / intLe / intEqZero / intIsNeg COMPUTE
    // the right answer on concrete signed inputs (so the headline isn't a
    // coincidence of cancelling bugs).
    let env = checker_env();
    let z = |k: i64| int_lit(k);
    // The difference-pair rep is non-normalized: `intAdd 2 (-3) = mk 2 3`, which
    // DENOTES -1 but is not STRUCTURALLY `mk 0 1`. So Int-valued results are
    // probed by SEMANTIC equality (`intEq _ _ ≡ Bool.true`), not `reduces_to`.
    let int_eq_true = |env: &MinimalEnv, a: RawExpr, b: RawExpr| -> bool {
        reduces_to(env, &r_apps(r_const("intEq"), vec![a, b]), &btrue())
    };

    // intAdd 2 3 = 5 ;  intAdd 2 (-3) = -1
    assert!(
        int_eq_true(&env, r_apps(r_const("intAdd"), vec![z(2), z(3)]), z(5)),
        "intAdd 2 3 = 5"
    );
    assert!(
        int_eq_true(&env, r_apps(r_const("intAdd"), vec![z(2), z(-3)]), z(-1)),
        "intAdd 2 (-3) = -1"
    );
    // intMul 2 3 = 6 ;  intMul 2 (-3) = -6 ;  intMul (-2) (-3) = 6
    assert!(
        int_eq_true(&env, r_apps(r_const("intMul"), vec![z(2), z(3)]), z(6)),
        "intMul 2 3 = 6"
    );
    assert!(
        int_eq_true(&env, r_apps(r_const("intMul"), vec![z(2), z(-3)]), z(-6)),
        "intMul 2 (-3) = -6"
    );
    assert!(
        int_eq_true(&env, r_apps(r_const("intMul"), vec![z(-2), z(-3)]), z(6)),
        "intMul (-2)(-3) = 6"
    );
    // intLt: -1 < 1 true ; 1 < 1 false ; 2 < -3 false ; -3 < -2 true
    assert!(
        reduces_to(&env, &r_apps(r_const("intLt"), vec![z(-1), z(1)]), &btrue()),
        "intLt -1 1 = true"
    );
    assert!(
        reduces_to(&env, &r_apps(r_const("intLt"), vec![z(1), z(1)]), &bfalse()),
        "intLt 1 1 = false"
    );
    assert!(
        reduces_to(
            &env,
            &r_apps(r_const("intLt"), vec![z(2), z(-3)]),
            &bfalse()
        ),
        "intLt 2 -3 = false"
    );
    assert!(
        reduces_to(
            &env,
            &r_apps(r_const("intLt"), vec![z(-3), z(-2)]),
            &btrue()
        ),
        "intLt -3 -2 = true"
    );
    // intLe: 1 ≤ 1 true ; 2 ≤ 1 false
    assert!(
        reduces_to(&env, &r_apps(r_const("intLe"), vec![z(1), z(1)]), &btrue()),
        "intLe 1 1 = true"
    );
    assert!(
        reduces_to(&env, &r_apps(r_const("intLe"), vec![z(2), z(1)]), &bfalse()),
        "intLe 2 1 = false"
    );
    // intEqZero: (mk 3 3) = 0 true ; 1 = 0 false ; -2 = 0 false
    assert!(
        reduces_to(
            &env,
            &r_app(
                r_const("intEqZero"),
                r_apps(r_const("Int.mk"), vec![nat_lit(3), nat_lit(3)])
            ),
            &btrue()
        ),
        "intEqZero (3-3) = true"
    );
    assert!(
        reduces_to(&env, &r_app(r_const("intEqZero"), z(1)), &bfalse()),
        "intEqZero 1 = false"
    );
    // intIsNeg: -2 true ; 0 false ; 3 false
    assert!(
        reduces_to(&env, &r_app(r_const("intIsNeg"), z(-2)), &btrue()),
        "intIsNeg -2 = true"
    );
    assert!(
        reduces_to(&env, &r_app(r_const("intIsNeg"), z(0)), &bfalse()),
        "intIsNeg 0 = false"
    );
    assert!(
        reduces_to(&env, &r_app(r_const("intIsNeg"), z(3)), &bfalse()),
        "intIsNeg 3 = false"
    );
}

#[test]
fn test_farkas_subterms_reduce_as_expected() {
    // Spot-check the checker's building blocks on the infeasible instance.
    let env = checker_env();
    // combineColumns [[1],[-1]] [1,1] DENOTES [0] — probe via allEqZero (every
    // column entry is zero), since the rep is non-normalized.
    assert!(
        reduces_to(
            &env,
            &r_app(
                r_const("allEqZero"),
                r_apps(
                    r_const("combineColumns"),
                    vec![infeasible_rows(), good_mults()]
                )
            ),
            &btrue()
        ),
        "allEqZero (combineColumns rows y) = true (columns sum to 0)"
    );
    // allEqZero [0] = true
    assert!(
        reduces_to(&env, &r_app(r_const("allEqZero"), ints(&[0])), &btrue()),
        "allEqZero [0] = true"
    );
    // intDot [1,1] [-1,-1] DENOTES -2 — probe via intEq.
    assert!(
        reduces_to(
            &env,
            &r_apps(
                r_const("intEq"),
                vec![
                    r_apps(r_const("intDot"), vec![good_mults(), infeasible_bounds()]),
                    int_lit(-2)
                ]
            ),
            &btrue()
        ),
        "intDot y b = -2"
    );
    // allNonneg [1,1] = true
    assert!(
        reduces_to(&env, &r_app(r_const("allNonneg"), good_mults()), &btrue()),
        "allNonneg [1,1] = true"
    );
}

#[test]
fn test_positive_reflected_recheck_reduces_to_true() {
    // THE HEADLINE: ck0 itself re-checks the Farkas infeasibility cert by
    // computation. farkasChecks <infeasible system> <valid y> ≡ Bool.true.
    let env = checker_env();
    let app = farkas_checks(infeasible_rows(), infeasible_bounds(), good_mults());
    assert!(
        is_bool_true(&env, &app),
        "farkasChecks <infeasible system> <valid cert> must reduce to Bool.true in ck0"
    );
}

#[test]
fn test_negative_negative_multiplier_reduces_to_false() {
    let env = checker_env();
    // y = (-1, 1): column sum = -1*1 + 1*(-1) = -2 ≠ 0 AND y not ≥ 0.
    let bad = ints(&[-1, 1]);
    let app = farkas_checks(infeasible_rows(), infeasible_bounds(), bad);
    assert!(
        !is_bool_true(&env, &app),
        "a NEGATIVE multiplier must NOT reduce to Bool.true"
    );
}

#[test]
fn test_negative_nonzero_column_sum_reduces_to_false() {
    let env = checker_env();
    // y = (2, 1): nonneg ✓, but column sum = 2*1 + 1*(-1) = 1 ≠ 0.
    let bad = ints(&[2, 1]);
    let app = farkas_checks(infeasible_rows(), infeasible_bounds(), bad);
    assert!(
        !is_bool_true(&env, &app),
        "a cert whose column-sum ≠ 0 must NOT reduce to Bool.true"
    );
}

#[test]
fn test_negative_nonnegative_bound_sum_reduces_to_false() {
    let env = checker_env();
    // Same infeasible rows, but flip the bounds to b = (+1, +1): now Σ y_i b_i =
    // 1*1 + 1*1 = 2 ≥ 0 — no contradiction even though columns cancel.
    let good_cols_no_contradiction = ints(&[1, 1]);
    let app = farkas_checks(infeasible_rows(), good_cols_no_contradiction, good_mults());
    assert!(
        !is_bool_true(&env, &app),
        "a cert with Σ y_i b_i ≥ 0 must NOT reduce to Bool.true"
    );
}

#[test]
fn test_negative_feasible_system_with_bogus_cert_reduces_to_false() {
    let env = checker_env();
    // FEASIBLE system:  x ≤ 1  and  -x ≤ 1   (i.e. -1 ≤ x ≤ 1, satisfied by x=0).
    //   rows = [[1],[-1]],  bounds = [1,1].
    // Bogus cert y = (1,1): columns cancel to 0, but Σ y_i b_i = 1+1 = 2 ≥ 0, so
    // farkasChecks must reject (no real Farkas cert exists for a feasible system).
    let feasible_bounds = ints(&[1, 1]);
    let app = farkas_checks(infeasible_rows(), feasible_bounds, good_mults());
    assert!(
        !is_bool_true(&env, &app),
        "a FEASIBLE system with a bogus cert must NOT reduce to Bool.true"
    );
}

// ===========================================================================
// SOUNDNESS BRIDGE.
//
// We STATE the soundness-bridge TYPE in ck0 (so the certificate STRUCTURE lives
// in the kernel) and PROVE the load-bearing endpoint arithmetic contradiction
// for the concrete witness (analogous to #28's `emptyClauseUnsat`):
//
//   The cert reduces  Σ y_i b_i  to the concrete Int -2, and `intIsNeg (-2)`
//   reduces to Bool.true. The "0 ≤ -2 < 0" contradiction is realized as:
//   from a putative model, the column condition forces 0 = Σ y_i (a_i·x) = the
//   combined-bound value, but that value is < 0 — i.e. `leZeroNeg : intIsNeg d =
//   true -> intLe int0 d = true -> False` instantiated at d = -2 is INHABITED in
//   ck0 because `intLe int0 (-2)` ι-reduces to Bool.false, so its `= true`
//   hypothesis is `Bool.false = Bool.true`, refuted by `noConfusion`.
//
// The FULL top-level bridge (`farkasChecks rows bounds y = true -> Unsat rows
// bounds`) needs a fold-induction over the rows together with the LRA
// metatheorem that the column/bound conditions imply `0 = Σ y(a·x) ≤ Σ y b`;
// that induction is OUT of M0–M3 scope for a closed ck0 term. We STATE that
// TYPE (it kernel-checks to Prop) and do NOT fake or register its proof.
// ===========================================================================

fn nat_eq_decl() -> InductiveDecl {
    // Eq : {A : Sort u} -> A -> A -> Prop, ctor Eq.refl.
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
    InductiveDecl {
        name: n("Eq"),
        num_level_params: 1,
        num_params: 2,
        type_: vlvl(&b, &eq_ty, 1),
        constructors: vec![Constructor {
            name: n("Eq.refl"),
            type_: vlvl(&b, &refl_ty, 1),
        }],
    }
}

#[test]
fn test_soundness_endpoint_contradiction_is_proved() {
    // The PROVED load-bearing kernel: for the concrete witness, the combined
    // bound value d = Σ y_i b_i = -2 satisfies `intIsNeg d = true` while a model
    // would force `intLe int0 d = true` (0 ≤ d). We prove these are jointly
    // contradictory by realizing `intLe int0 (-2) = true` as `Bool.false =
    // Bool.true`, which `Eq`-elimination into `False` refutes.
    let mut env = checker_env();
    add_inductive(&mut env, nat_eq_decl()).expect("Eq admits");
    let mut budget = Budget::default_budget();

    // First: confirm the two facts COMPUTE as claimed on the concrete witness.
    let d = r_apps(r_const("intDot"), vec![good_mults(), infeasible_bounds()]); // = -2
    assert!(
        reduces_to(&env, &r_app(r_const("intIsNeg"), d.clone()), &btrue()),
        "intIsNeg (Σ y b) = true"
    );
    // intLe int0 (Σ y b) reduces to Bool.false (0 ≤ -2 is false) — this is the
    // arithmetic core of the 0 ≤ -2 < 0 contradiction.
    let le0d = r_apps(r_const("intLe"), vec![r_const("int0"), d.clone()]);
    assert!(
        reduces_to(&env, &le0d, &bfalse()),
        "intLe 0 (Σ y b) = false (0 ≤ -2 is FALSE)"
    );

    // Now PROVE the contradiction in ck0: the type
    //   contradiction : Eq Bool (intLe int0 (Σ y b)) Bool.true -> False
    // is INHABITED, because the hypothesis is def-eq to `Eq Bool Bool.false
    // Bool.true`, which is uninhabited. We build the proof via Eq.rec into a
    // discriminator motive `D : Bool -> Prop` with `D false = True'`,
    // `D true = False`, transporting `D Bool.true`'s would-be inhabitant.
    //
    //   D := fun b => Bool.rec (motive := fun _ => Prop) True' False b
    //   from h : Eq Bool (intLe int0 d) Bool.true, since (intLe int0 d) ≡ false,
    //   h : Eq Bool false true; Eq.rec D (trivial : D false = True') h : D true = False.
    // We register True'/trivial as a one-ctor inductive to source `D false`.

    // True' : Prop with ctor True'.intro.
    let env = {
        let b = boot(&[("True'", 0), ("True'.intro", 0)]);
        let decl = InductiveDecl {
            name: n("True'"),
            num_level_params: 0,
            num_params: 0,
            type_: vlvl(&b, &r_prop(), 0),
            constructors: vec![Constructor {
                name: n("True'.intro"),
                type_: vlvl(&b, &r_const("True'"), 0),
            }],
        };
        let mut e = env;
        add_inductive(&mut e, decl).expect("True' admits");
        e
    };

    // D := fun (b:Bool) => Bool.rec (fun _ => Prop) True' False b   : Bool -> Prop
    let disc = r_lam(
        bool_ty(),
        bool_rec(r_prop(), r_const("True'"), r_const("False"), r_bvar(0)),
    );

    // contradiction : Eq Bool (intLe int0 d) Bool.true -> False
    //   := fun h => Eq.rec (motive := fun (y:Bool)(_ : Eq Bool (intLe int0 d) y) => D y)
    //                       (True'.intro : D (intLe int0 d))   -- since (intLe int0 d) ≡ false, D _ ≡ True'
    //                       h
    // Eq.rec here is the standard motive form. We use the kernel's Eq recursor.
    let le_int0_d = le0d.clone();
    let contradiction_ty = r_pi(
        r_apps(
            r_const_p("Eq", vec![lone()]),
            vec![bool_ty(), le_int0_d.clone(), btrue()],
        ),
        r_const("False"),
    );

    // Eq.rec : {A}{a} (motive : (b:A) -> Eq A a b -> Prop) -> motive a (Eq.refl) ->
    //          {b} -> (h : Eq A a b) -> motive b h
    // Build via the kernel Elim node for Eq.
    let proof = {
        // motive: fun (y:Bool) (_ : Eq Bool (intLe int0 d) y) => D y
        let motive = r_lam(
            bool_ty(),
            r_lam(
                r_apps(
                    r_const_p("Eq", vec![lone()]),
                    vec![bool_ty(), le_int0_d.clone(), r_bvar(0)],
                ),
                r_app(disc.clone(), r_bvar(1)),
            ),
        );
        // minor (the refl case): D (intLe int0 d) — since that ≡ false, D _ ≡ True',
        // so True'.intro inhabits it.
        let minor = r_const("True'.intro");
        // Eq.rec elim: levels [motive-level=0 (Prop), A-level=1].
        let elim = RawExpr::Elim(n("Eq"), lzero(), vec![lone()]);
        // @Eq.rec A a motive minor b h  — params A,a then motive,minor, then index b, major h.
        // h is the bound hypothesis (bvar 0).
        let h = r_bvar(0);
        r_lam(
            r_apps(
                r_const_p("Eq", vec![lone()]),
                vec![bool_ty(), le_int0_d.clone(), btrue()],
            ),
            r_apps(
                elim,
                vec![
                    bool_ty(),         // A
                    le_int0_d.clone(), // a
                    motive,
                    minor,
                    btrue(), // index b = Bool.true
                    h,       // major
                ],
            ),
        )
    };

    let ty_t =
        Term::validate_closed(&env, &contradiction_ty).expect("contradiction type validates");
    let sort = clean_ck0::infer_sort_in_context(&env, &[], &ty_t, &mut budget)
        .expect("contradiction type is a well-formed Prop");
    assert!(sort.is_zero(), "contradiction statement lives in Prop");
    let proof_t = Term::validate_closed(&env, &proof).expect("proof validates");
    clean_ck0::check(&env, &proof_t, &ty_t, &mut budget).expect(
        "endpoint contradiction proof checks: (intLe int0 (Σ y b) = true) -> False is INHABITED",
    );
}

#[test]
fn test_soundness_bridge_type_is_well_formed_in_ck0() {
    // STATE the full bridge TYPE so the certificate structure is in ck0; confirm
    // it kernel-checks to Prop. We do NOT register a proof (honest gap).
    //
    //   Sat rows bounds := (x : List Int) -> rowsHold rows bounds x   (a model)
    //   Unsat rows bounds := Sat rows bounds -> False
    //   bridge : Eq Bool (farkasChecks rows bounds y) Bool.true -> Unsat rows bounds
    //
    // To keep the stated type self-contained and kernel-checkable we use the
    // direct unfolded 2-row model on the concrete instance:
    //   rowSat r b x := intLe (intDot r x) b = true   (the constraint  a_i·x ≤ b_i)
    //   Unsat2 := (x : List Int) -> Eq Bool (rowSat row0 b0 x) true
    //                            -> Eq Bool (rowSat row1 b1 x) true -> False
    //   bridge : Eq Bool (farkasChecks ...) true -> Unsat2
    let mut env = checker_env();
    add_inductive(&mut env, nat_eq_decl()).expect("Eq admits");
    let mut budget = Budget::default_budget();

    let eqb = |a: RawExpr, b: RawExpr| r_apps(r_const_p("Eq", vec![lone()]), vec![bool_ty(), a, b]);
    // rowLe r x b := intLe (intDot r x) b   (Bool)   — the i-th constraint holds.
    // We inline it. row0 = [1], b0 = -1 ; row1 = [-1], b1 = -1.
    let row0 = ints(&[1]);
    let row1 = ints(&[-1]);
    let b0 = int_lit(-1);
    let b1 = int_lit(-1);
    // x is the outermost bound var (List Int); inside nested arrows its de Bruijn
    // index shifts. Build:
    //   Unsat2 := (x:List Int) -> (Eq Bool (intLe (intDot row0 x) b0) true)
    //                          -> (Eq Bool (intLe (intDot row1 x) b1) true) -> False
    let constraint = |x_db: u32, row: RawExpr, b: RawExpr| {
        let dot = r_apps(r_const("intDot"), vec![row, r_bvar(x_db)]);
        let le = r_apps(r_const("intLe"), vec![dot, b]);
        eqb(le, btrue())
    };
    let unsat2 = r_pi(
        list_int(),
        r_pi(
            constraint(0, row0.clone(), b0.clone()),
            r_pi(constraint(1, row1.clone(), b1.clone()), r_const("False")),
        ),
    );
    // hyp : Eq Bool (farkasChecks rows bounds y) Bool.true
    let cr = farkas_checks(infeasible_rows(), infeasible_bounds(), good_mults());
    let hyp = eqb(cr, btrue());
    let bridge_ty = r_pi(hyp, unsat2);
    let bridge_t = Term::validate_closed(&env, &bridge_ty).expect("bridge type validates");
    let sort = clean_ck0::infer_sort_in_context(&env, &[], &bridge_t, &mut budget)
        .expect("soundness-bridge TYPE kernel-checks");
    assert!(sort.is_zero(), "soundness-bridge type lives in Prop");
}
