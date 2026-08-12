// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Paragon integration benchmark: the in-repo prover's solve rate over a
// curated set of REAL Mathlib-shaped goals built as kernel `Expr`s over SMALL
// real environments (kernel `Init`/prelude-level: `Nat`, `List`, `Eq`, the
// classical bootstrap, plus a handful of faithful axioms). This is a
// SOLVE-RATE measurement, NOT a graduation — no full-Mathlib closure is loaded.
//
// It exercises the substrate added this session:
//   * the generic structural-induction lane (`engine_induction*`),
//   * universe-polymorphic premise injection (`engine_detailed`),
//   * the per-goal engine router (`engine_router`),
//   * MePo premise selection (`premise/selector`),
// through the public `AutomationEngine` API (`auto_prove` /
// `auto_prove_with_premises`).
//
// SOUNDNESS (load-bearing): the prover is on the SEARCH side, not the TCB. A
// goal counts as SOLVED only when the returned proof term KERNEL-CHECKS —
// `infer_type` succeeds AND `is_def_eq(inferred, goal)` holds — never merely
// because `auto_prove` returned `Some`. A returned-but-bogus term is recorded
// as `BogusProof` and FAILS the test (a soundness regression), distinct from an
// honest `Unsolved` (`None`), which is a legitimate negative.
//
// NOTE: this file is also `include!`d by `bench-runner/src/main.rs` (a
// standalone trust-ir-free workspace) so the measurement can RUN inside a
// worktree, where the full-workspace lockfile collides. Keep the header as
// regular `//` comments (not `//!`) so the `include!` stays legal.

use std::collections::BTreeMap;
use std::time::Duration;

use clean_auto::premise::PremiseDatabase;
use clean_auto::{AutomationEngine, AutomationQuery};
use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Constructor, Environment, Expr, InductiveDecl, InductiveType, KernelClassInfo,
    Level, LocalContext, TypeChecker,
};

const TIMEOUT: Duration = Duration::from_secs(30);

/// Goal class — mirrors the improvement targets named in the session brief.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Class {
    /// `∀` over `Nat`/`List` needing structural induction.
    Inductive,
    /// Closable by applying a universe-poly lemma at the goal's level.
    UnivPolyPremise,
    /// Equational / congruence (closed-implication form).
    Equational,
    /// Ground arithmetic (router → SMT/reduction).
    Arithmetic,
    /// Goals stated under a local typeclass instance `[inst : C α]` whose proof
    /// needs a class LAW (`mul_one`, `mul_assoc`) the routed engines never see —
    /// closed by the instance-projection-as-premise lane
    /// (`try_instance_projection_premises`).
    Typeclass,
    /// HARD negatives — deep multi-step / instance synthesis, expected to fail.
    /// Currently unused (every curated goal now solves after `mul_comm` landed),
    /// but retained as the registration path for a future honest-negative goal.
    #[allow(dead_code)]
    HardNegative,
}

impl Class {
    fn tag(self) -> &'static str {
        match self {
            Class::Inductive => "inductive",
            Class::UnivPolyPremise => "univpoly_premise",
            Class::Equational => "equational",
            Class::Arithmetic => "arithmetic",
            Class::Typeclass => "typeclass",
            Class::HardNegative => "hard_negative",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    /// Returned a proof term that kernel-checks against the goal.
    Solved,
    /// Returned `None` (honest negative).
    Unsolved,
    /// Returned a term that FAILED the kernel re-check (term references a
    /// constant absent from this small env, or its type is not def-eq to the
    /// goal). Recorded distinctly — the kernel still rejects it, so this is a
    /// search-side / env-provisioning issue, never an unsound accepted proof.
    BogusProof,
    /// The prover aborted the process (e.g. stack overflow) instead of
    /// returning — a robustness gap, captured via per-goal subprocess isolation.
    Crashed,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl Outcome {
    fn token(self) -> &'static str {
        match self {
            Outcome::Solved => "Solved",
            Outcome::Unsolved => "Unsolved",
            Outcome::BogusProof => "BogusProof",
            Outcome::Crashed => "Crashed",
        }
    }

    fn from_token(s: &str) -> Option<Self> {
        match s {
            "Solved" => Some(Outcome::Solved),
            "Unsolved" => Some(Outcome::Unsolved),
            "BogusProof" => Some(Outcome::BogusProof),
            "Crashed" => Some(Outcome::Crashed),
            _ => None,
        }
    }
}

/// Kernel-check a returned proof against `goal`. A proof counts only when its
/// inferred type is def-eq to the goal under the kernel.
fn kernel_check(
    env: &Environment,
    goal: &Expr,
    result: Option<clean_auto::ProofResult>,
) -> Outcome {
    let Some(proof) = result else {
        return Outcome::Unsolved;
    };
    let inferred = match proof.infer_type(env) {
        Ok(ty) => ty,
        Err(e) => {
            eprintln!(
                "  DIAG infer_type failed: {e:?}\n    proof_term={:?}",
                proof.proof_term()
            );
            return Outcome::BogusProof;
        }
    };
    let tc = match proof.proof_context() {
        Some(ctx) => TypeChecker::with_context(env, ctx.clone()),
        None => TypeChecker::new(env),
    };
    if tc.is_def_eq(&inferred, goal) {
        Outcome::Solved
    } else {
        eprintln!("  DIAG is_def_eq failed\n    inferred={inferred:?}\n    goal={goal:?}\n    proof_term={:?}", proof.proof_term());
        Outcome::BogusProof
    }
}

// ─── shared expression builders ────────────────────────────────────────────

fn konst(s: &str) -> Expr {
    Expr::const_str(s)
}

fn lvl0() -> Level {
    Level::zero()
}

fn lvl1() -> Level {
    Level::succ(Level::zero())
}

fn nat() -> Expr {
    konst("Nat")
}

/// `@Eq.{lvl} ty lhs rhs`.
fn eq_at(lvl: Level, ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::const_str_levels("Eq", vec![lvl]), [ty, lhs, rhs])
}

/// `@Eq.{1} Nat lhs rhs`.
fn nat_eq(lhs: Expr, rhs: Expr) -> Expr {
    eq_at(lvl1(), nat(), lhs, rhs)
}

fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(konst("Nat.add"), [a, b])
}

fn nat_mul(a: Expr, b: Expr) -> Expr {
    Expr::apps(konst("Nat.mul"), [a, b])
}

/// `Nat` numeral `succ^n zero`.
fn nat_lit(n: u32) -> Expr {
    let mut e = konst("Nat.zero");
    for _ in 0..n {
        e = Expr::app(konst("Nat.succ"), e);
    }
    e
}

fn forall_nat(body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, nat(), body)
}

// ─── ENV 1: Nat + List + Eq (real inductives) ──────────────────────────────

fn nat_list_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    env.init_list().expect("init_list");
    env.init_classical().expect("init_classical");
    register_append(&mut env);
    env
}

/// `nat_list_env` + the standard `Nat` ordering API the arithmetic-equality
/// reconstruction emits: `Nat.le`/`Nat.le.refl`/`Nat.le.step` (`init_le`, via
/// `init_nat_top_level_ordering`) and `Nat.le_antisymm`. The latter is a real
/// Lean-core lemma, axiomatized here (faithful) so the lane's
/// `@Nat.le_antisymm a b (≤-proof) (≥-proof)` ground-equality term resolves and
/// KERNEL-CHECKS. (`a`, `b` are EXPLICIT to match the emitted application.)
fn nat_arith_env() -> Environment {
    let mut env = nat_list_env();
    env.init_nat_top_level_ordering()
        .expect("init_nat_top_level_ordering");
    // Nat.le_antisymm : (a b : Nat) → Nat.le a b → Nat.le b a → @Eq.{1} Nat a b
    let nat_le = |x: Expr, y: Expr| Expr::apps(konst("Nat.le"), [x, y]);
    let ty = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(
                BinderInfo::Default,
                nat_le(Expr::bvar(1), Expr::bvar(0)),
                Expr::pi(
                    BinderInfo::Default,
                    nat_le(Expr::bvar(1), Expr::bvar(2)),
                    nat_eq(Expr::bvar(3), Expr::bvar(2)),
                ),
            ),
        ),
    );
    axiom(&mut env, "Nat.le_antisymm", vec![], ty);
    env
}

/// `List Nat` (`List.{0} Nat`).
fn list_nat() -> Expr {
    Expr::apps(Expr::const_str_levels("List", vec![lvl0()]), [nat()])
}

fn nil_nat() -> Expr {
    Expr::apps(Expr::const_str_levels("List.nil", vec![lvl0()]), [nat()])
}

fn cons_nat(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("List.cons", vec![lvl0()]),
        [nat(), h, t],
    )
}

fn eq_list(l: Expr, r: Expr) -> Expr {
    eq_at(lvl1(), list_nat(), l, r)
}

fn append(a: Expr, b: Expr) -> Expr {
    Expr::apps(konst("List.append"), [a, b])
}

/// `List.append := fun xs ys => @List.rec.{1,0} Nat (fun _ => List Nat) ys
/// (fun h t ih => List.cons Nat h ih) xs` (recurses on first arg).
fn register_append(env: &mut Environment) {
    let list_nat = list_nat();
    let ty = Expr::pi(
        BinderInfo::Default,
        list_nat.clone(),
        Expr::pi(BinderInfo::Default, list_nat.clone(), list_nat.clone()),
    );
    let motive = Expr::lam(BinderInfo::Default, list_nat.clone(), list_nat.clone());
    let cons_body = cons_nat(Expr::bvar(2), Expr::bvar(0));
    let cons_case = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            list_nat.clone(),
            Expr::lam(BinderInfo::Default, list_nat.clone(), cons_body),
        ),
    );
    let body = Expr::apps(
        Expr::const_str_levels("List.rec", vec![lvl1(), lvl0()]),
        [nat(), motive, Expr::bvar(0), cons_case, Expr::bvar(1)],
    );
    let value = Expr::lam(
        BinderInfo::Default,
        list_nat.clone(),
        Expr::lam(BinderInfo::Default, list_nat, body),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("List.append"),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .expect("register List.append");
}

// ─── ENV 2: faithful Eq env (trans / congr as axioms) ───────────────────────

fn ty_a() -> Expr {
    konst("A")
}

fn eq_a(lhs: Expr, rhs: Expr) -> Expr {
    eq_at(lvl1(), ty_a(), lhs, rhs)
}

fn axiom(env: &mut Environment, n: &str, level_params: Vec<Name>, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(n),
        level_params,
        type_,
    })
    .unwrap_or_else(|e| panic!("faithful axiom `{n}` should type-check: {e:?}"));
}

/// `Eq`, `Eq.refl/symm/trans`, `congrArg`, `congr` with their genuine Lean
/// types, base type `A`, elements `e0..e10`/`a`/`b`/`c`/`d`, functions
/// `f`/`g`/`h`. (Spelled-out de Bruijn so reconstructed proofs kernel-check.)
fn faithful_eq_env() -> Environment {
    let mut env = Environment::new();
    let u = || Name::from_string("u");
    let v = || Name::from_string("v");
    let su = || Expr::sort(Level::param(u()));
    let sv = || Expr::sort(Level::param(v()));
    let pu = || Level::param(u());
    let pv = || Level::param(v());
    let b = Expr::bvar;
    let d = BinderInfo::Default;

    axiom(
        &mut env,
        "Eq",
        vec![u()],
        Expr::pi(d, su(), Expr::pi(d, b(0), Expr::pi(d, b(1), Expr::prop()))),
    );
    axiom(
        &mut env,
        "Eq.refl",
        vec![u()],
        Expr::pi(d, su(), Expr::pi(d, b(0), eq_at(pu(), b(1), b(0), b(0)))),
    );
    axiom(
        &mut env,
        "Eq.symm",
        vec![u()],
        Expr::pi(
            d,
            su(),
            Expr::pi(
                d,
                b(0),
                Expr::pi(
                    d,
                    b(1),
                    Expr::pi(
                        d,
                        eq_at(pu(), b(2), b(1), b(0)),
                        eq_at(pu(), b(3), b(1), b(2)),
                    ),
                ),
            ),
        ),
    );
    axiom(
        &mut env,
        "Eq.trans",
        vec![u()],
        Expr::pi(
            d,
            su(),
            Expr::pi(
                d,
                b(0),
                Expr::pi(
                    d,
                    b(1),
                    Expr::pi(
                        d,
                        b(2),
                        Expr::pi(
                            d,
                            eq_at(pu(), b(3), b(2), b(1)),
                            Expr::pi(
                                d,
                                eq_at(pu(), b(4), b(2), b(1)),
                                eq_at(pu(), b(5), b(4), b(2)),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    axiom(
        &mut env,
        "congrArg",
        vec![u(), v()],
        Expr::pi(
            d,
            su(),
            Expr::pi(
                d,
                sv(),
                Expr::pi(
                    d,
                    b(1),
                    Expr::pi(
                        d,
                        b(2),
                        Expr::pi(
                            d,
                            Expr::arrow(b(3), b(3)),
                            Expr::pi(
                                d,
                                eq_at(pu(), b(4), b(2), b(1)),
                                eq_at(pv(), b(4), Expr::app(b(1), b(3)), Expr::app(b(1), b(2))),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    let imax = Level::imax(pu(), pv());
    axiom(
        &mut env,
        "congr",
        vec![u(), v()],
        Expr::pi(
            d,
            su(),
            Expr::pi(
                d,
                sv(),
                Expr::pi(
                    d,
                    Expr::arrow(b(1), b(1)),
                    Expr::pi(
                        d,
                        Expr::arrow(b(2), b(2)),
                        Expr::pi(
                            d,
                            b(3),
                            Expr::pi(
                                d,
                                b(4),
                                Expr::pi(
                                    d,
                                    eq_at(imax, Expr::arrow(b(5), b(5)), b(3), b(2)),
                                    Expr::pi(
                                        d,
                                        eq_at(pu(), b(6), b(2), b(1)),
                                        eq_at(
                                            pv(),
                                            b(6),
                                            Expr::app(b(5), b(3)),
                                            Expr::app(b(4), b(2)),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );

    axiom(&mut env, "A", vec![], Expr::type_());
    for i in 0..=10 {
        axiom(&mut env, &format!("e{i}"), vec![], ty_a());
    }
    for elem in ["a", "b", "c", "d"] {
        axiom(&mut env, elem, vec![], ty_a());
    }
    for func in ["f", "g"] {
        axiom(&mut env, func, vec![], Expr::arrow(ty_a(), ty_a()));
    }
    axiom(
        &mut env,
        "h",
        vec![],
        Expr::arrow(ty_a(), Expr::arrow(ty_a(), ty_a())),
    );
    env
}

/// Fold closed antecedents into `H1 → … → Hn → consequent`.
fn implication(antecedents: &[Expr], consequent: Expr) -> Expr {
    antecedents.iter().rev().fold(consequent, |acc, ante| {
        Expr::pi(BinderInfo::Default, ante.clone(), acc)
    })
}

// ─── ENV 3: universe-polymorphic premise envs ───────────────────────────────

/// Env with `Eq`, poly carrier `B.{u} : Sort u`, elements `x.{u} y.{u} : B.{u}`,
/// poly lemma `L.{u} : @Eq.{u} B x y`. Returns env + premise DB containing `L`.
fn poly_env_and_db() -> (Environment, PremiseDatabase) {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    let u = || Level::param(Name::from_string("u"));
    let up = || Name::from_string("u");
    axiom(&mut env, "B", vec![up()], Expr::sort(u()));
    let b_u = || Expr::const_str_levels("B", vec![u()]);
    axiom(&mut env, "x", vec![up()], b_u());
    axiom(&mut env, "y", vec![up()], b_u());
    let x_u = Expr::const_str_levels("x", vec![u()]);
    let y_u = Expr::const_str_levels("y", vec![u()]);
    let l_type = eq_at(u(), b_u(), x_u, y_u);
    axiom(&mut env, "L", vec![up()], l_type.clone());
    let mut db = PremiseDatabase::new();
    db.add(Name::from_string("L"), l_type);
    (env, db)
}

/// `@Eq.{lvl} B.{lvl} x.{lvl} y.{lvl}` — the `u := lvl` instance of `L`'s type.
fn poly_goal_at(lvl: Level) -> Expr {
    eq_at(
        lvl.clone(),
        Expr::const_str_levels("B", vec![lvl.clone()]),
        Expr::const_str_levels("x", vec![lvl.clone()]),
        Expr::const_str_levels("y", vec![lvl]),
    )
}

/// Faithful `Eq`/`Eq.trans` env + chain lemmas `lemAB`/`lemBC`/`lemCD` as
/// monomorphic axioms (and DB mirror) so the injection lane can select+chain.
fn injection_env_and_db() -> (Environment, PremiseDatabase) {
    let mut env = Environment::new();
    let u = || Name::from_string("u");
    let su = || Expr::sort(Level::param(u()));
    let pu = || Level::param(u());
    let b = Expr::bvar;
    let d = BinderInfo::Default;
    axiom(
        &mut env,
        "Eq",
        vec![u()],
        Expr::pi(d, su(), Expr::pi(d, b(0), Expr::pi(d, b(1), Expr::prop()))),
    );
    axiom(
        &mut env,
        "Eq.trans",
        vec![u()],
        Expr::pi(
            d,
            su(),
            Expr::pi(
                d,
                b(0),
                Expr::pi(
                    d,
                    b(1),
                    Expr::pi(
                        d,
                        b(2),
                        Expr::pi(
                            d,
                            eq_at(pu(), b(3), b(2), b(1)),
                            Expr::pi(
                                d,
                                eq_at(pu(), b(4), b(2), b(1)),
                                eq_at(pu(), b(5), b(4), b(2)),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    axiom(&mut env, "A", vec![], Expr::type_());
    for elem in ["a", "b", "c", "d"] {
        axiom(&mut env, elem, vec![], ty_a());
    }
    axiom(&mut env, "lemAB", vec![], eq_a(konst("a"), konst("b")));
    axiom(&mut env, "lemBC", vec![], eq_a(konst("b"), konst("c")));
    axiom(&mut env, "lemCD", vec![], eq_a(konst("c"), konst("d")));
    let mut db = PremiseDatabase::new();
    db.add(Name::from_string("lemAB"), eq_a(konst("a"), konst("b")));
    db.add(Name::from_string("lemBC"), eq_a(konst("b"), konst("c")));
    db.add(Name::from_string("lemCD"), eq_a(konst("c"), konst("d")));
    (env, db)
}

// ─── ENV 4: typeclass instances (instance-projection lane) ──────────────────
//
// Real-Mathlib-shaped elementary typeclass algebra, built as kernel `Expr`s: a
// faithful binary `Monoid`-shaped class `Mon α` (DATA fields `mul`, `one`; Prop
// LAW `mul_one`) and, for the transitive parent-projection, a `Semigroup`-shaped
// grandparent `Sg α` (`mul` + `mul_assoc`) with a `Monoid`-shaped `MonExt α`
// that `extends Sg` (its sole field is the parent instance `toSg : Sg α`). Each
// goal is stated under a LOCAL instance `[inst : C M]`; its proof needs a class
// LAW that the routed engines never see (they treat `inst` as opaque), reachable
// only by projecting the instance with the kernel `Proj(C, i, inst)` primitive.

/// `@Eq.{1} M lhs rhs`.
fn eq_m(lhs: Expr, rhs: Expr) -> Expr {
    eq_at(lvl1(), konst("M"), lhs, rhs)
}

/// Base typeclass env: `Eq` (universe-poly), carrier `M : Type`, elements
/// `a`/`b`/`c : M`. The class ops (`mul`, `one`) are NOT globals here — they are
/// instance FIELDS, projected off the local instance, so a goal is unreachable
/// without the instance's law.
fn tc_base_env() -> Environment {
    let mut env = Environment::new();
    // Real `Eq` plus its congruence prelude (`Eq.refl`/`Eq.symm`/`Eq.trans`,
    // `congr`/`congrArg`/`congrFun`), exactly the machinery the `Nat`/`List` env
    // installs. The single-lemma projection closer (TC1–TC3) only needs `Eq`, but
    // the MULTI-STEP rewrite closer emits genuine `congrArg`/`congr`/`Eq.trans`
    // terms (a law rewritten into a sub-term, two laws chained), which the kernel
    // re-checks — so the env must carry the same `Eq` prelude real Mathlib does.
    env.init_eq().expect("init_eq");
    axiom(&mut env, "M", vec![], Expr::type_()); // M : Type (Sort 1)
    for elem in ["a", "b", "c"] {
        axiom(&mut env, elem, vec![], konst("M"));
    }
    env
}

/// Faithful `Monoid`-shaped class `Mon α`: DATA fields `mul : α → α → α` and
/// `one : α`, plus the Prop LAW `mul_one : ∀ (x:α), @Eq α (mul x one) x`. Fields
/// are indexed `mul=0`, `one=1`, `mul_one=2` (the projection order).
fn tc_add_mon(env: &mut Environment) {
    let d = BinderInfo::Default;
    let b = Expr::bvar;
    let ty = Expr::type_();
    // Mon : Type → Type
    let mon_ty = Expr::arrow(ty.clone(), ty.clone());
    // under [α]: mul : α → α → α   (α=b0; then b1; codomain α=b2)
    let mul_ty = Expr::pi(d, b(0), Expr::pi(d, b(1), b(2)));
    // under [α, mul]: one : α   (α is 1 up)
    let one_ty = b(1);
    // under [α, mul, one]: mul_one : ∀ (x:α), @Eq α (mul x one) x
    //   x-domain α = b2; inside [α,mul,one,x]: α=b3, mul=b2, one=b1, x=b0
    let mul_one_ty = Expr::pi(
        d,
        b(2),
        eq_at(lvl1(), b(3), Expr::apps(b(2), [b(0), b(1)]), b(0)),
    );
    // Mon.mk : {α:Type} → (mul) → (one) → (mul_one) → Mon α   (α=b3 in codomain)
    let mk_ty = Expr::pi(
        BinderInfo::Implicit,
        ty,
        Expr::pi(
            d,
            mul_ty,
            Expr::pi(
                d,
                one_ty,
                Expr::pi(d, mul_one_ty, Expr::app(konst("Mon"), b(3))),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("Mon"),
            type_: mon_ty,
            constructors: vec![Constructor {
                name: Name::from_string("Mon.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("Mon inductive registers");
    env.register_structure_fields(
        Name::from_string("Mon"),
        vec![
            Name::from_string("mul"),
            Name::from_string("one"),
            Name::from_string("mul_one"),
        ],
    )
    .expect("Mon fields register");
    env.register_class(KernelClassInfo {
        name: Name::from_string("Mon"),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
}

/// Richer `Monoid`-shaped class `Mon3 α` carrying THREE laws — DATA fields
/// `mul`(0), `one`(1); Prop LAWS `mul_one`(2) `∀x, mul x one = x`, `one_mul`(3)
/// `∀x, mul one x = x`, `mul_assoc`(4) `∀x y z, mul (mul x y) z = mul x (mul y
/// z)`. Used by the MULTI-LEMMA goal (TC6): closing a goal under a `[inst : Mon3
/// M]` that needs TWO of these laws CHAINED (`mul_one` on one subterm and
/// `one_mul` on another) is what the instance-projection REWRITE closer
/// (`try_project_law_rewrite`) composes.
fn tc_add_mon3(env: &mut Environment) {
    let d = BinderInfo::Default;
    let b = Expr::bvar;
    let ty = Expr::type_();
    let mon_ty = Expr::arrow(ty.clone(), ty.clone());
    // under [α]: mul : α → α → α
    let mul_ty = Expr::pi(d, b(0), Expr::pi(d, b(1), b(2)));
    // under [α, mul]: one : α
    let one_ty = b(1);
    // under [α, mul, one]: mul_one : ∀ (x:α), mul x one = x
    let mul_one_ty = Expr::pi(
        d,
        b(2),
        eq_at(lvl1(), b(3), Expr::apps(b(2), [b(0), b(1)]), b(0)),
    );
    // under [α, mul, one, mul_one]: one_mul : ∀ (x:α), mul one x = x
    //   inside [α,mul,one,mul_one,x]: α=b4, mul=b3, one=b2, x=b0
    let one_mul_ty = Expr::pi(
        d,
        b(3),
        eq_at(lvl1(), b(4), Expr::apps(b(3), [b(2), b(0)]), b(0)),
    );
    // under [α, mul, one, mul_one, one_mul]:
    //   mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
    //   inside [α,mul,one,mul_one,one_mul,x,y,z]: α=b7, mul=b6, x=b2, y=b1, z=b0
    let assoc_lhs = Expr::apps(b(6), [Expr::apps(b(6), [b(2), b(1)]), b(0)]);
    let assoc_rhs = Expr::apps(b(6), [b(2), Expr::apps(b(6), [b(1), b(0)])]);
    let mul_assoc_ty = Expr::pi(
        d,
        b(4),
        Expr::pi(
            d,
            b(5),
            Expr::pi(d, b(6), eq_at(lvl1(), b(7), assoc_lhs, assoc_rhs)),
        ),
    );
    // Mon3.mk : {α} → mul → one → mul_one → one_mul → mul_assoc → Mon3 α (α=b5)
    let mk_ty = Expr::pi(
        BinderInfo::Implicit,
        ty,
        Expr::pi(
            d,
            mul_ty,
            Expr::pi(
                d,
                one_ty,
                Expr::pi(
                    d,
                    mul_one_ty,
                    Expr::pi(
                        d,
                        one_mul_ty,
                        Expr::pi(d, mul_assoc_ty, Expr::app(konst("Mon3"), b(5))),
                    ),
                ),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("Mon3"),
            type_: mon_ty,
            constructors: vec![Constructor {
                name: Name::from_string("Mon3.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("Mon3 inductive registers");
    env.register_structure_fields(
        Name::from_string("Mon3"),
        vec![
            Name::from_string("mul"),
            Name::from_string("one"),
            Name::from_string("mul_one"),
            Name::from_string("one_mul"),
            Name::from_string("mul_assoc"),
        ],
    )
    .expect("Mon3 fields register");
    env.register_class(KernelClassInfo {
        name: Name::from_string("Mon3"),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
}

/// `Semigroup`-shaped GRANDPARENT class `Sg α`: DATA field `mul : α → α → α` and
/// the Prop LAW `mul_assoc : ∀ (x y z:α), @Eq α (mul (mul x y) z) (mul x (mul y
/// z))`. Fields `mul=0`, `mul_assoc=1`.
fn tc_add_sg(env: &mut Environment) {
    let d = BinderInfo::Default;
    let b = Expr::bvar;
    let ty = Expr::type_();
    let sg_ty = Expr::arrow(ty.clone(), ty.clone());
    // under [α]: mul : α → α → α
    let mul_ty = Expr::pi(d, b(0), Expr::pi(d, b(1), b(2)));
    // under [α, mul]: mul_assoc : ∀ x y z, @Eq α (mul (mul x y) z) (mul x (mul y z))
    //   x-dom α=b1; y-dom α=b2; z-dom α=b3;
    //   inside [α,mul,x,y,z]: α=b4, mul=b3, x=b2, y=b1, z=b0
    let assoc_lhs = Expr::apps(b(3), [Expr::apps(b(3), [b(2), b(1)]), b(0)]);
    let assoc_rhs = Expr::apps(b(3), [b(2), Expr::apps(b(3), [b(1), b(0)])]);
    let mul_assoc_ty = Expr::pi(
        d,
        b(1),
        Expr::pi(
            d,
            b(2),
            Expr::pi(d, b(3), eq_at(lvl1(), b(4), assoc_lhs, assoc_rhs)),
        ),
    );
    // Sg.mk : {α} → (mul) → (mul_assoc) → Sg α   (α=b2 in codomain)
    let mk_ty = Expr::pi(
        BinderInfo::Implicit,
        ty,
        Expr::pi(
            d,
            mul_ty,
            Expr::pi(d, mul_assoc_ty, Expr::app(konst("Sg"), b(2))),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("Sg"),
            type_: sg_ty,
            constructors: vec![Constructor {
                name: Name::from_string("Sg.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("Sg inductive registers");
    env.register_structure_fields(
        Name::from_string("Sg"),
        vec![Name::from_string("mul"), Name::from_string("mul_assoc")],
    )
    .expect("Sg fields register");
    env.register_class(KernelClassInfo {
        name: Name::from_string("Sg"),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
}

/// `Monoid`-shaped class `MonExt α` that `extends Sg`: its sole field is the
/// parent instance `toSg : Sg α` (field 0), a DATA-valued projection whose type
/// head `Sg` is itself a class. It has NO law of its own — `mul_assoc` lives on
/// the grandparent `Sg`, reachable only *through* `MonExt.toSg`.
fn tc_add_mon_ext(env: &mut Environment) {
    let d = BinderInfo::Default;
    let b = Expr::bvar;
    let ty = Expr::type_();
    let mon_ty = Expr::arrow(ty.clone(), ty.clone());
    // under [α]: toSg : Sg α   (α=b0)
    let to_sg_ty = Expr::app(konst("Sg"), b(0));
    // MonExt.mk : {α} → (toSg : Sg α) → MonExt α   (α=b1 in codomain)
    let mk_ty = Expr::pi(
        BinderInfo::Implicit,
        ty,
        Expr::pi(d, to_sg_ty, Expr::app(konst("MonExt"), b(1))),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("MonExt"),
            type_: mon_ty,
            constructors: vec![Constructor {
                name: Name::from_string("MonExt.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("MonExt inductive registers");
    env.register_structure_fields(Name::from_string("MonExt"), vec![Name::from_string("toSg")])
        .expect("MonExt fields register");
    env.register_class(KernelClassInfo {
        name: Name::from_string("MonExt"),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
}

/// Notation-wrapper structure `HMulU` (stand-in for `HMul`): a single binary
/// field `hMul : M → M → M`. Its projection `Proj(HMulU, 0, ·)` is the analog of
/// `HMul.hMul`; a goal written `@HMulU.hMul instHMul a one` whnf-reduces to
/// `inst.mul a one` — exactly the instance-notation chain the whnf pre-pass must
/// collapse. NOT a class (never scanned as an instance); only its projection is
/// used, in the goal.
fn tc_add_hmulu(env: &mut Environment) {
    let d = BinderInfo::Default;
    // HMulU.mk : (hMul : M → M → M) → HMulU
    let hmul_field_ty = Expr::pi(d, konst("M"), Expr::pi(d, konst("M"), konst("M")));
    let mk_ty = Expr::pi(d, hmul_field_ty, konst("HMulU"));
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("HMulU"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("HMulU.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("HMulU inductive registers");
    env.register_structure_fields(Name::from_string("HMulU"), vec![Name::from_string("hMul")])
        .expect("HMulU fields register");
}

/// `Proj(name, idx, e)`.
fn proj(name: &str, idx: u32, e: Expr) -> Expr {
    Expr::proj(Name::from_string(name), idx, e)
}

// ─── the benchmark ──────────────────────────────────────────────────────────

/// How a goal is dispatched to the engine.
enum Run {
    /// `auto_prove` (no premise database).
    Plain,
    /// `auto_prove_with_premises` with the given premise database.
    WithPremises(PremiseDatabase),
    /// `auto_prove_with_query` carrying a local context — the dispatch the
    /// typeclass class needs so the instance-projection lane can scan the
    /// in-context instance local `[inst : C α]`.
    WithQuery(LocalContext),
}

/// One curated benchmark goal: a small real env, the goal `Expr`, the dispatch
/// mode, the PINNED `expected` outcome (the regression baseline — see
/// `run_regression`), and whether running it is known to ABORT the process
/// (stack overflow / runaway search in the in-repo prover); those are exercised
/// only under subprocess isolation, never in-process under `cargo test`.
struct Spec {
    class: Class,
    label: String,
    env: Environment,
    goal: Expr,
    run: Run,
    /// The pinned baseline. A regression test FAILS when the live outcome
    /// diverges from this — a `Solved`→non-`Solved` drift is a capability
    /// REGRESSION; an `Unsolved`→`Solved` drift is a capability GAIN that must
    /// be acknowledged by re-pinning `expected` (and updating the docs note).
    expected: Outcome,
    aborts_in_process: bool,
}

impl Spec {
    /// Pin this goal as an honest negative the in-repo prover returns `None`
    /// for (NOT `#[ignore]`d — it runs every time, so a future capability gain
    /// trips the regression test). Currently unused (`mul_comm`, the last
    /// negative, now solves), retained as the honest-negative registration path.
    #[allow(dead_code)]
    fn expect_unsolved(mut self) -> Self {
        self.expected = Outcome::Unsolved;
        self
    }

    /// Pin this goal as one that ABORTS the in-repo prover in-process (stack
    /// overflow or runaway search). It is NOT run under `cargo test` (it would
    /// crash/hang the test process); the standalone subprocess runner measures
    /// it empirically. Still reported — not silently `#[ignore]`d.
    ///
    /// Currently unused — no curated goal aborts in-process since the IH-rewrite
    /// step landed — but retained as the registration path for any future
    /// aborting goal (`aborts_in_process` plumbing + subprocess runner stay live).
    #[allow(dead_code)]
    fn expect_crashed_out_of_process(mut self) -> Self {
        self.expected = Outcome::Crashed;
        self.aborts_in_process = true;
        self
    }
}

fn plain(class: Class, label: &str, env: Environment, goal: Expr) -> Spec {
    Spec {
        class,
        label: label.to_string(),
        env,
        goal,
        run: Run::Plain,
        expected: Outcome::Solved,
        aborts_in_process: false,
    }
}

fn prem(class: Class, label: &str, env: Environment, goal: Expr, db: PremiseDatabase) -> Spec {
    Spec {
        class,
        label: label.to_string(),
        env,
        goal,
        run: Run::WithPremises(db),
        expected: Outcome::Solved,
        aborts_in_process: false,
    }
}

/// A typeclass goal dispatched through `auto_prove_with_query` with `ctx` (which
/// holds the in-context instance local `[inst : C α]`). Defaults to pinned
/// `Solved`; a negative wall is registered with `.expect_unsolved()`.
fn tc_query(class: Class, label: &str, env: Environment, goal: Expr, ctx: LocalContext) -> Spec {
    Spec {
        class,
        label: label.to_string(),
        env,
        goal,
        run: Run::WithQuery(ctx),
        expected: Outcome::Solved,
        aborts_in_process: false,
    }
}

/// Build the full curated goal set (30 goals) spanning the goal classes the
/// session's improvements target — including the TYPECLASS class closed by the
/// instance-projection-as-premise lane.
fn build_specs() -> Vec<Spec> {
    let mut specs: Vec<Spec> = Vec::new();

    // ── (a) INDUCTIVE — ∀ over Nat / List ──────────────────────────────────
    let env = nat_list_env();
    specs.push(plain(
        Class::Inductive,
        "forall n, 0 + n = n",
        env.clone(),
        forall_nat(nat_eq(
            nat_add(konst("Nat.zero"), Expr::bvar(0)),
            Expr::bvar(0),
        )),
    ));
    specs.push(plain(
        Class::Inductive,
        "forall n, n + 0 = n",
        env.clone(),
        forall_nat(nat_eq(
            nat_add(Expr::bvar(0), konst("Nat.zero")),
            Expr::bvar(0),
        )),
    ));
    specs.push(plain(
        Class::Inductive,
        "forall l, l ++ [] = l",
        env.clone(),
        Expr::pi(
            BinderInfo::Default,
            list_nat(),
            eq_list(append(Expr::bvar(0), nil_nat()), Expr::bvar(0)),
        ),
    ));
    specs.push(plain(
        Class::Inductive,
        "forall l, [] ++ l = l",
        env,
        Expr::pi(
            BinderInfo::Default,
            list_nat(),
            eq_list(append(nil_nat(), Expr::bvar(0)), Expr::bvar(0)),
        ),
    ));

    // ── (b) UNIVERSE-POLY PREMISE — auto_prove_with_premises + DB ───────────
    // (`PremiseDatabase` is not `Clone`; rebuild the small env+db per spec.)
    let (penv, pdb) = poly_env_and_db();
    specs.push(prem(
        Class::UnivPolyPremise,
        "poly lemma L at level 1",
        penv,
        poly_goal_at(lvl1()),
        pdb,
    ));
    let (penv, pdb) = poly_env_and_db();
    specs.push(prem(
        Class::UnivPolyPremise,
        "poly lemma L at level 0",
        penv,
        poly_goal_at(lvl0()),
        pdb,
    ));
    let (ienv, idb) = injection_env_and_db();
    specs.push(prem(
        Class::UnivPolyPremise,
        "premise-inject a = c (2-lemma chain)",
        ienv,
        eq_a(konst("a"), konst("c")),
        idb,
    ));
    let (ienv, idb) = injection_env_and_db();
    specs.push(prem(
        Class::UnivPolyPremise,
        "premise-inject a = d (3-lemma chain)",
        ienv,
        eq_a(konst("a"), konst("d")),
        idb,
    ));

    // ── (c) EQUATIONAL / CONGRUENCE — closed-implication form ───────────────
    let env = faithful_eq_env();
    let app = |func: &str, arg: Expr| Expr::app(konst(func), arg);
    for k in [2u32, 3, 5, 10] {
        let antecedents: Vec<Expr> = (0..k)
            .map(|i| eq_a(konst(&format!("e{i}")), konst(&format!("e{}", i + 1))))
            .collect();
        let consequent = eq_a(konst("e0"), konst(&format!("e{k}")));
        specs.push(plain(
            Class::Equational,
            &format!("eq.trans chain k={k}"),
            env.clone(),
            implication(&antecedents, consequent),
        ));
    }
    specs.push(plain(
        Class::Equational,
        "congruence f a = f b",
        env.clone(),
        implication(
            &[eq_a(konst("a"), konst("b"))],
            eq_a(app("f", konst("a")), app("f", konst("b"))),
        ),
    ));
    specs.push(plain(
        Class::Equational,
        "congruence f (f a) = f (f b)",
        env.clone(),
        implication(
            &[eq_a(konst("a"), konst("b"))],
            eq_a(
                app("f", app("f", konst("a"))),
                app("f", app("f", konst("b"))),
            ),
        ),
    ));
    specs.push(plain(
        Class::Equational,
        "congruence g a = g b",
        env.clone(),
        implication(
            &[eq_a(konst("a"), konst("b"))],
            eq_a(app("g", konst("a")), app("g", konst("b"))),
        ),
    ));
    let h_a_c = Expr::app(Expr::app(konst("h"), konst("a")), konst("c"));
    let h_b_c = Expr::app(Expr::app(konst("h"), konst("b")), konst("c"));
    specs.push(plain(
        Class::Equational,
        "congruence h a c = h b c",
        env,
        implication(&[eq_a(konst("a"), konst("b"))], eq_a(h_a_c, h_b_c)),
    ));

    // ── (d) ARITHMETIC — router → SMT (ground; needs Nat ordering lemmas) ────
    let env = nat_arith_env();
    specs.push(plain(
        Class::Arithmetic,
        "1 + 1 = 2",
        env.clone(),
        nat_eq(nat_add(nat_lit(1), nat_lit(1)), nat_lit(2)),
    ));
    specs.push(plain(
        Class::Arithmetic,
        "2 + 3 = 5",
        env.clone(),
        nat_eq(nat_add(nat_lit(2), nat_lit(3)), nat_lit(5)),
    ));
    // The arith lane's `eval_small_nat` now folds `Nat.mul` (and nested
    // `add`-under-`mul`) on numerals, so these ground products reduce and the
    // `Nat.le_antisymm` ground-equality lane discharges them. The whole
    // `@Nat.le_antisymm (2*3) 6 (≤-proof) (≥-proof)` term KERNEL-CHECKS (the
    // kernel reduces `Nat.mul` on the succ-numerals to the literal). Pinned
    // `Solved`, run in-process.
    specs.push(plain(
        Class::Arithmetic,
        "2 * 3 = 6",
        env.clone(),
        nat_eq(nat_mul(nat_lit(2), nat_lit(3)), nat_lit(6)),
    ));
    specs.push(plain(
        Class::Arithmetic,
        "(2 + 3) * 2 = 10",
        env,
        nat_eq(
            nat_mul(nat_add(nat_lit(2), nat_lit(3)), nat_lit(2)),
            nat_lit(10),
        ),
    ));

    // ── (e) TYPECLASS — goals under a local instance, closed by projecting a
    //        class law off it with the kernel `Proj(C, i, inst)` primitive ─────
    //
    // Each proof term (the projection + the specialised law) is KERNEL-checked
    // by the shared `kernel_check` in the context the instance lives in, so a
    // wrong field index / level / specialisation is caught by the kernel and
    // recorded `BogusProof`, never counted as a solve.

    // TC1 — Monoid.mul_one (DIRECT single-lemma projection). Under `[inst : Mon
    // M]`, the lane SKIPS the data fields `mul`/`one`, projects only the Prop law
    // `mul_one = Proj(Mon,2,inst) : ∀ x, (inst.mul) x (inst.one) = x`, and the
    // direct `is_def_eq` closer specialises it to `a`. Proof `Proj(Mon,2,inst) a`
    // kernel-checks against `inst.mul a inst.one = a`. Pinned `Solved`.
    {
        let mut env = tc_base_env();
        tc_add_mon(&mut env);
        let mut ctx = LocalContext::new();
        let inst = ctx.push(
            Name::from_string("inst"),
            Expr::app(konst("Mon"), konst("M")),
            BinderInfo::InstImplicit,
        );
        let mul = proj("Mon", 0, Expr::fvar(inst));
        let one = proj("Mon", 1, Expr::fvar(inst));
        // goal: @Eq M (inst.mul a inst.one) a
        let goal = eq_m(Expr::apps(mul, [konst("a"), one]), konst("a"));
        specs.push(tc_query(
            Class::Typeclass,
            "Monoid.mul_one: inst.mul a inst.one = a",
            env,
            goal,
            ctx,
        ));
    }

    // TC2 — Semigroup.mul_assoc via TRANSITIVE parent-projection. Under `[inst :
    // MonExt M]` (a class that `extends Sg`), the needed law `mul_assoc` is NOT a
    // field of `MonExt`; it lives on the grandparent `Sg`, reachable only through
    // the parent-instance projection `MonExt.toSg`. The transitive scan projects
    // `toSg` (a data field whose type head `Sg` is a class), RECURSES, and
    // surfaces `Proj(Sg,1,Proj(MonExt,0,inst))` — the `mul_assoc` law — which the
    // direct closer specialises to `a b c` (a 3-binder telescope). Proof
    // kernel-checks against `(m (m a b) c) = (m a (m b c))`. Pinned `Solved`.
    {
        let mut env = tc_base_env();
        tc_add_sg(&mut env);
        tc_add_mon_ext(&mut env);
        let mut ctx = LocalContext::new();
        let inst = ctx.push(
            Name::from_string("inst"),
            Expr::app(konst("MonExt"), konst("M")),
            BinderInfo::InstImplicit,
        );
        let to_sg = proj("MonExt", 0, Expr::fvar(inst));
        let m = proj("Sg", 0, to_sg); // inst.toSg.mul
        let mul2 = |x: Expr, y: Expr| Expr::apps(m.clone(), [x, y]);
        // goal: @Eq M (m (m a b) c) (m a (m b c))
        let goal = eq_m(
            mul2(mul2(konst("a"), konst("b")), konst("c")),
            mul2(konst("a"), mul2(konst("b"), konst("c"))),
        );
        specs.push(tc_query(
            Class::Typeclass,
            "Semigroup.mul_assoc via MonExt.toSg (transitive)",
            env,
            goal,
            ctx,
        ));
    }

    // TC3 — Monoid.mul_one written with HMUL NOTATION (whnf pre-pass). The goal's
    // operator is the wrapper projection `Proj(HMulU,0,instHMul)` where `instHMul
    // = HMulU.mk (inst.mul)` — syntactically DIFFERENT from the projected law's
    // `Proj(Mon,0,inst)`, so the first-order matcher misses it head-on. Only after
    // the whnf pre-pass reduces `Proj(HMulU,0, HMulU.mk (inst.mul))` to `inst.mul`
    // does the goal become `inst.mul a inst.one = a`, which `Mon.mul_one` closes.
    // The proof kernel-checks against the ORIGINAL (un-normalized) goal — is_def_eq
    // bridges the notation, so normalization only widens matching. Pinned `Solved`.
    {
        let mut env = tc_base_env();
        tc_add_mon(&mut env);
        tc_add_hmulu(&mut env);
        let mut ctx = LocalContext::new();
        let inst = ctx.push(
            Name::from_string("inst"),
            Expr::app(konst("Mon"), konst("M")),
            BinderInfo::InstImplicit,
        );
        let inst_mul = proj("Mon", 0, Expr::fvar(inst));
        let inst_one = proj("Mon", 1, Expr::fvar(inst));
        // instHMul := HMulU.mk (inst.mul)
        let inst_hmul = Expr::app(konst("HMulU.mk"), inst_mul);
        // goal: @Eq M (@HMulU.hMul instHMul a inst.one) a
        let hmul_op = proj("HMulU", 0, inst_hmul);
        let goal = eq_m(Expr::apps(hmul_op, [konst("a"), inst_one]), konst("a"));
        specs.push(tc_query(
            Class::Typeclass,
            "Monoid.mul_one via HMul notation (whnf pre-pass)",
            env,
            goal,
            ctx,
        ));
    }

    // TC4 — HONEST NEGATIVE (the wall). `mul_comm` under `[inst : Mon M]` is
    // UNPROVABLE: a bare `Monoid` carries no commutativity law, so no projection
    // (nor any chain of them) inhabits `inst.mul a b = inst.mul b a`. The lane
    // finds no closing term and returns `None` → `Unsolved`. This records the
    // boundary: the projection lane surfaces the instance's OWN laws (and its
    // parents'), but never SYNTHESISES a law the class does not have — that needs
    // a stronger instance (`CommMonoid`) or genuine multi-lemma search. Pinned
    // `Unsolved` (runs every time; a future gain trips the regression pin).
    {
        let mut env = tc_base_env();
        tc_add_mon(&mut env);
        let mut ctx = LocalContext::new();
        let inst = ctx.push(
            Name::from_string("inst"),
            Expr::app(konst("Mon"), konst("M")),
            BinderInfo::InstImplicit,
        );
        let mul = proj("Mon", 0, Expr::fvar(inst));
        // goal: @Eq M (inst.mul a b) (inst.mul b a)  — no commutativity law exists
        let goal = eq_m(
            Expr::apps(mul.clone(), [konst("a"), konst("b")]),
            Expr::apps(mul, [konst("b"), konst("a")]),
        );
        specs.push(
            tc_query(
                Class::Typeclass,
                "Monoid.mul_comm (no commutativity law — honest wall)",
                env,
                goal,
                ctx,
            )
            .expect_unsolved(),
        );
    }

    // TC5 — MULTI-STEP REWRITE (single law UNDER A CONGRUENCE). NEWLY SOLVES via
    // the instance-projection REWRITE closer (`try_project_law_rewrite`). Under
    // `[inst : Mon M]`, `(a * 1) * b = a * b` needs `mul_one` rewritten at the
    // inner subterm `a * 1 → a` (leaving `a * b = a * b`). The DIRECT closer
    // (`try_project_law_defeq`) only first-order matches ONE law's conclusion
    // against the WHOLE goal, so it cannot rewrite a law into a proper SUBTERM;
    // the superposition/SMT fallback cannot fire either (the class op `mul =
    // Proj(Mon,0,inst)` is a non-keyable `Proj` head). The rewrite closer feeds
    // the projected `mul_one` to the induction lane's kernel-checked equational
    // rewriter (`prove_eq_rewrite`): it first-order matches `mul_one` at the sub-
    // position `a * 1`, rewrites it to `a` lifting the step through the spine with
    // `congr`/`congrArg`, and closes the residual `a*b = a*b` by reflexivity. The
    // whole `Eq.trans (congr …) (Eq.refl …)` term KERNEL-CHECKS against the goal.
    // Pinned `Solved`.
    {
        let mut env = tc_base_env();
        tc_add_mon(&mut env);
        let mut ctx = LocalContext::new();
        let inst = ctx.push(
            Name::from_string("inst"),
            Expr::app(konst("Mon"), konst("M")),
            BinderInfo::InstImplicit,
        );
        let mul = proj("Mon", 0, Expr::fvar(inst));
        let one = proj("Mon", 1, Expr::fvar(inst));
        let m = |x: Expr, y: Expr| Expr::apps(mul.clone(), [x, y]);
        // goal: @Eq M ((a * 1) * b) (a * b)  — needs mul_one under a congruence
        let goal = eq_m(m(m(konst("a"), one), konst("b")), m(konst("a"), konst("b")));
        specs.push(tc_query(
            Class::Typeclass,
            "Monoid mul_one under congruence: (a*1)*b = a*b (multi-step rewrite)",
            env,
            goal,
            ctx,
        ));
    }

    // TC6 — MULTI-LEMMA CHAIN (TWO distinct laws). NEWLY SOLVES via the
    // instance-projection REWRITE closer — the literal answer to "does the
    // machinery chain multiple class axioms?" is now YES. Under `[inst : Mon3 M]`
    // (three laws `mul_one`/`one_mul`/`mul_assoc`), `(a * 1) * (1 * b) = a * b`
    // needs `mul_one` on the LEFT subterm (`a * 1 → a`) AND `one_mul` on the RIGHT
    // (`1 * b → b`) — two DIFFERENT projected laws COMPOSED. `prove_eq_rewrite`
    // rewrites the leftmost applicable law (`mul_one` at `a * 1`, via `congr`),
    // stitches with `Eq.trans`, and RECURSES on the residual `a * (1 * b) = a * b`,
    // where `one_mul` rewrites `1 * b → b` (again via `congr`) leaving `a*b = a*b`
    // closed by reflexivity. The whole nested-`Eq.trans` term — two projected
    // class laws chained through congruence — KERNEL-CHECKS against the goal.
    // Pinned `Solved`.
    {
        let mut env = tc_base_env();
        tc_add_mon3(&mut env);
        let mut ctx = LocalContext::new();
        let inst = ctx.push(
            Name::from_string("inst"),
            Expr::app(konst("Mon3"), konst("M")),
            BinderInfo::InstImplicit,
        );
        let mul = proj("Mon3", 0, Expr::fvar(inst));
        let one = proj("Mon3", 1, Expr::fvar(inst));
        let m = |x: Expr, y: Expr| Expr::apps(mul.clone(), [x, y]);
        // goal: @Eq M ((a * 1) * (1 * b)) (a * b)  — needs mul_one AND one_mul
        let goal = eq_m(
            m(m(konst("a"), one.clone()), m(one, konst("b"))),
            m(konst("a"), konst("b")),
        );
        specs.push(tc_query(
            Class::Typeclass,
            "Monoid mul_one+one_mul chain: (a*1)*(1*b) = a*b (multi-lemma chain)",
            env,
            goal,
            ctx,
        ));
    }

    // ── (f) HARD NEGATIVES — deep multi-step, expected to fail honestly ─────
    let env = nat_list_env();
    let two_nat = |body: Expr| {
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(BinderInfo::Default, nat(), body),
        )
    };
    // add_comm: NEWLY SOLVES via AUXILIARY-LEMMA SYNTHESIS (`engine_induction_aux`).
    // `Nat.add` recurses on its SECOND argument, so both the base case (`0+m =
    // m+0`) and the step (`(succ n)+m = m+(succ n)`) bottom out at a stuck
    // `Nat.add 0 _` / `Nat.add (succ _) _` that congruence-with-IH cannot close.
    // The lane DETECTS each stuck `op (ctor _) _`, SYNTHESISES the bridging lemma
    // (`zero_add : 0+y = y` / `succ_add : succ x + y = succ (x+y)`), PROVES it by
    // its OWN induction, KERNEL-CHECKS it, and registers it as a rewrite fact:
    // `zero_add` closes the base case, `succ_add` + the IH-rewrite close the step.
    // The whole `@Nat.rec` term (with the kernel-checked aux-lemma terms inlined)
    // KERNEL-CHECKS. Pinned `Solved`, run in-process.
    specs.push(plain(
        Class::Inductive,
        "forall n m, n + m = m + n (add_comm)",
        env.clone(),
        two_nat(nat_eq(
            nat_add(Expr::bvar(1), Expr::bvar(0)),
            nat_add(Expr::bvar(0), Expr::bvar(1)),
        )),
    ));
    // add_assoc: NEWLY SOLVES via the IH-rewriting induction step
    // (`engine_induction_rewrite`). It does not close on its outermost variable
    // `n` (the base case `(0+m)+k = 0+(m+k)` would need `0+m = m`), but the lane's
    // induction-VARIABLE SELECTION reorders the THIRD variable `k` to the front
    // and inducts there: the base case `(n+m)+0 = n+(m+0)` is reflexivity, and the
    // step `(n+m)+(succ k) = n+(m+(succ k))` whnf-reduces to
    // `succ((n+m)+k) = succ(n+(m+k))`, whose `congrArg succ` residual is exactly
    // the specialised IH `ih n m`. The whole `@Nat.rec` term KERNEL-CHECKS (it
    // also no longer stack-overflows: the deterministic rewrite path replaced the
    // runaway engine search). Pinned `Solved`, run in-process.
    specs.push(plain(
        Class::Inductive,
        "forall n m k, (n+m)+k = n+(m+k) (add_assoc)",
        env.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(
                BinderInfo::Default,
                nat(),
                Expr::pi(
                    BinderInfo::Default,
                    nat(),
                    nat_eq(
                        nat_add(nat_add(Expr::bvar(2), Expr::bvar(1)), Expr::bvar(0)),
                        nat_add(Expr::bvar(2), nat_add(Expr::bvar(1), Expr::bvar(0))),
                    ),
                ),
            ),
        ),
    ));
    // mul_comm: NEWLY SOLVES via the EXTENDED aux-lemma synthesis + CHAINING
    // (`engine_induction_aux` + `engine_induction_match`). Inducting on `n`, the
    // base case `0*m = m*0` needs the left-ABSORBING bridge `0*y = 0` (the
    // synthesis now tries `op c₀ y = c₀` alongside the left-IDENTITY `op c₀ y = y`,
    // keeping whichever KERNEL-PROVES — identity is false for `*` and fails its own
    // induction). The step `(succ k)*m = m*(succ k)` needs the left-DISTRIBUTE
    // bridge `succ_mul : (succ x)*y = x*y + y` (a new unary candidate shape), whose
    // OWN inductive step rearranges the accumulator (`(x*j+j)+x = (x*j+x)+j`) — an
    // `add_right_comm` that is NOT a constructor-commute bridge, so it is CHAINED:
    // pre-proved by the lane, kernel-checked, and offered to `succ_mul`'s proof via
    // the sub-term rewriter (`prove_eq_rewrite` branch 6, first-order matching a
    // `∀`-fact at a sub-position + re-folding `Nat.add`'s recursor form). Every
    // synthesised lemma AND the final `@Nat.rec` term KERNEL-CHECK. Pinned
    // `Solved`, run in-process.
    specs.push(plain(
        Class::Inductive,
        "forall n m, n * m = m * n (mul_comm)",
        env.clone(),
        two_nat(nat_eq(
            nat_mul(Expr::bvar(1), Expr::bvar(0)),
            nat_mul(Expr::bvar(0), Expr::bvar(1)),
        )),
    ));
    // append_assoc: NEWLY SOLVES via the IH-rewriting induction step. Unlike
    // `Nat.add`, `List.append` recurses on its FIRST argument, so induction on the
    // OUTERMOST variable `l1` closes directly: the base case `([]++l2)++l3 =
    // []++(l2++l3)` is reflexivity, and the step `((h::t)++l2)++l3 =
    // (h::t)++(l2++l3)` whnf-reduces both sides to `h :: …`, whose `congrArg
    // (cons h)` residual is the specialised IH `ih l2 l3`. The whole `@List.rec`
    // term KERNEL-CHECKS (and the formerly-runaway engine search is gone: the
    // deterministic rewrite path is bounded by fuel + the soft deadline). Pinned
    // `Solved`, run in-process.
    specs.push(plain(
        Class::Inductive,
        "forall l1 l2 l3, append_assoc",
        env,
        Expr::pi(
            BinderInfo::Default,
            list_nat(),
            Expr::pi(
                BinderInfo::Default,
                list_nat(),
                Expr::pi(
                    BinderInfo::Default,
                    list_nat(),
                    eq_list(
                        append(append(Expr::bvar(2), Expr::bvar(1)), Expr::bvar(0)),
                        append(Expr::bvar(2), append(Expr::bvar(1), Expr::bvar(0))),
                    ),
                ),
            ),
        ),
    ));

    specs
}

/// Run one spec through the engine and KERNEL-CHECK any returned proof.
fn run_spec(spec: &Spec) -> Outcome {
    let engine = AutomationEngine::new();
    let result = match &spec.run {
        Run::Plain => engine.auto_prove(&spec.env, &spec.goal, TIMEOUT, None),
        Run::WithPremises(db) => {
            engine.auto_prove_with_premises(&spec.env, &spec.goal, Vec::new(), db, TIMEOUT, None)
        }
        Run::WithQuery(local_ctx) => {
            // The projection lane populates the returned `ProofResult`'s
            // `proof_context` with this same local ctx (carrying the instance
            // fvar), so the shared `kernel_check` re-checks the projection term
            // in the context the instance lives in.
            engine
                .auto_prove_with_query(
                    &spec.env,
                    AutomationQuery::new(&spec.goal, TIMEOUT).with_local_ctx(local_ctx),
                )
                .verified()
        }
    };
    kernel_check(&spec.env, &spec.goal, result)
}

/// Run `run_spec` on a 1 GiB scoped worker thread (search lanes recurse deeply;
/// the macOS main-thread default of 8 MiB is too small for the hard goals). A
/// scoped thread lets the worker borrow `spec` without cloning.
fn run_spec_big_stack(spec: &Spec) -> Outcome {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1usize << 30)
            .spawn_scoped(s, || run_spec(spec))
            .expect("spawn bench worker")
            .join()
            .expect("bench worker panicked")
    })
}

/// Subprocess entry: run a single spec by index and print its outcome token to
/// stdout (`OUTCOME <idx> <token>`). Diagnostics go to stderr. Always exits 0 on
/// a graceful outcome; a stack overflow aborts the process (caught by parent).
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn run_one(idx: usize) {
    let specs = build_specs();
    let spec = specs
        .get(idx)
        .unwrap_or_else(|| panic!("goal index {idx} out of range"));
    let outcome = run_spec_big_stack(spec);
    println!("OUTCOME {idx} {}", outcome.token());
}

/// Why a pinned `expected` and the live `actual` diverged — the message the
/// regression test prints so a future agent knows whether they GAINED or LOST a
/// capability.
fn regression_hint(expected: Outcome, actual: Outcome) -> &'static str {
    match (expected, actual) {
        (Outcome::Solved, Outcome::Unsolved) => {
            "CAPABILITY REGRESSION: the in-repo prover no longer closes this goal"
        }
        (Outcome::Solved, Outcome::BogusProof) => {
            "SOUNDNESS REGRESSION: returned a term the kernel now rejects"
        }
        (Outcome::Solved, Outcome::Crashed) => {
            "ROBUSTNESS REGRESSION: the prover now aborts on this goal"
        }
        (Outcome::Unsolved, Outcome::Solved) | (Outcome::Crashed, Outcome::Solved) => {
            "CAPABILITY GAIN: this goal now SOLVES — re-pin `expected` to Solved and update the docs note"
        }
        (Outcome::Unsolved, Outcome::BogusProof) | (Outcome::Crashed, Outcome::BogusProof) => {
            "the prover now returns a term that fails the kernel re-check"
        }
        _ => "the live outcome no longer matches the pinned baseline",
    }
}

/// The regression run used by the `#[test]`: run every NON-aborting spec on a
/// large-stack worker and compare its live outcome to the spec's pinned
/// `expected`. Aborting specs (`aborts_in_process`) are NOT executed here — they
/// would crash/hang `cargo test`; their pinned `expected` is `Crashed`, measured
/// for real by the standalone subprocess runner. Returns the report rows plus
/// the list of human-readable mismatch messages (empty == no drift).
fn run_regression() -> (Vec<(Class, String, Outcome)>, Vec<String>) {
    let mut rows = Vec::new();
    let mut mismatches = Vec::new();
    for spec in build_specs().iter() {
        let actual = if spec.aborts_in_process {
            // Documented frontier — not run in-process. Treated as matching its
            // pinned `Crashed` baseline (the subprocess runner verifies it).
            Outcome::Crashed
        } else {
            run_spec_big_stack(spec)
        };
        eprintln!(
            "RESULT class={} expected={:?} actual={actual:?} label={:?}",
            spec.class.tag(),
            spec.expected,
            spec.label
        );
        if actual != spec.expected {
            mismatches.push(format!(
                "[{}] {:?}: expected {:?}, got {:?} -- {}",
                spec.class.tag(),
                spec.label,
                spec.expected,
                actual,
                regression_hint(spec.expected, actual)
            ));
        }
        rows.push((spec.class, spec.label.clone(), actual));
    }
    (rows, mismatches)
}

/// Print the machine-readable report. Returns `(total, solved, bogus)`.
fn print_report(rows: &[(Class, String, Outcome)]) -> (usize, usize, usize) {
    let total = rows.len();
    let count = |want: Outcome| rows.iter().filter(|(_, _, o)| *o == want).count();
    let solved = count(Outcome::Solved);
    let unsolved = count(Outcome::Unsolved);
    let bogus = count(Outcome::BogusProof);
    let crashed = count(Outcome::Crashed);

    let mut by_class: BTreeMap<&'static str, (usize, usize)> = BTreeMap::new();
    for (class, _, outcome) in rows {
        let entry = by_class.entry(class.tag()).or_insert((0, 0));
        entry.1 += 1;
        if *outcome == Outcome::Solved {
            entry.0 += 1;
        }
    }

    eprintln!("==================== PARAGON INTEGRATION BENCH ====================");
    eprintln!(
        "SUMMARY total={total} solved_kernel_checked={solved} unsolved={unsolved} bogus={bogus} crashed={crashed}"
    );
    for (tag, (s, n)) in &by_class {
        eprintln!("BY_CLASS {tag} {s}/{n}");
    }
    eprintln!("NON-SOLVED (honest — what the in-repo prover still can NOT do):");
    for (class, label, outcome) in rows {
        match outcome {
            Outcome::Unsolved => eprintln!("  - [{}] {label}  (returned None)", class.tag()),
            Outcome::BogusProof => eprintln!("  - [{}] {label}  (returned a term the kernel rejects)", class.tag()),
            Outcome::Crashed => eprintln!(
                "  - [{}] {label}  (prover aborted: stack overflow or runaway search past wall limit)",
                class.tag()
            ),
            Outcome::Solved => {}
        }
    }
    eprintln!("===================================================================");
    (total, solved, bogus)
}

/// The curated benchmark as a `clean-cli` integration REGRESSION test.
///
/// Every goal carries a PINNED `expected` outcome. The test FAILS when any live
/// outcome diverges from its pin, so the in-repo prover's reach can neither
/// silently REGRESS (a pinned `Solved` that stops solving) nor silently GAIN a
/// capability (a pinned honest-negative that starts solving — which must be
/// acknowledged by re-pinning). It ALSO fails on any `BogusProof` (a returned
/// term that does not kernel-check — a search-side soundness regression).
///
/// The two goals that formerly aborted in-process (`add_assoc` stack overflow,
/// `append_assoc` runaway engine search) NOW SOLVE via the IH-rewriting
/// induction step (`engine_induction_rewrite`) and are pinned `Solved`, run
/// in-process. No goal is currently pinned `Crashed`, so every spec executes
/// here; the standalone subprocess runner in `bench-runner` remains as a
/// belt-and-braces measurement and would isolate any future re-introduced abort.
#[cfg(test)]
#[test]
fn paragon_integration_bench_regression() {
    let (rows, mismatches) = run_regression();
    let (total, solved, bogus) = print_report(&rows);
    assert_eq!(total, 30, "expected 30 curated goals, ran {total}");
    assert_eq!(
        bogus, 0,
        "{bogus} returned proof(s) failed the kernel re-check (search-side soundness regression)"
    );
    assert!(
        mismatches.is_empty(),
        "paragon regression bench: {} pinned outcome(s) changed:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
    // Belt-and-braces: the curated baseline is 29/30 kernel-checked solves. The
    // arithmetic + inductive lanes account for the first 24 (the IH-rewriting
    // induction step added `add_assoc` + `append_assoc`; auxiliary-lemma synthesis
    // added `add_comm`; the `Nat.mul` ground-reduction extension added `2 * 3 = 6`
    // and `(2 + 3) * 2 = 10`; the CHAINED aux-lemma synthesis added `mul_comm`).
    // The TYPECLASS class then adds 5 more via the instance-projection lane: 3 by
    // the DIRECT closer (`Monoid.mul_one` direct, `Semigroup.mul_assoc` through the
    // transitive parent-projection, and `Monoid.mul_one` written with HMul notation
    // closed by the whnf pre-pass) and 2 by the new REWRITE closer
    // (`try_project_law_rewrite`) — `(a*1)*b = a*b` (one projected law rewritten
    // under a congruence) and `(a*1)*(1*b) = a*b` (two projected laws CHAINED),
    // both via the induction lane's kernel-checked `prove_eq_rewrite`. The one
    // remaining typeclass goal is an honest wall: `Monoid.mul_comm` has NO
    // commutativity law to project (nor to rewrite with), so it stays `Unsolved`;
    // a future gain there would trip this pin.
    assert_eq!(
        solved, 29,
        "expected the pinned 29/30 kernel-checked solves, saw {solved}"
    );
}
