// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: USING an *imported* STRUCTURALLY-recursive function — the common
//! `.olean` case, distinct from B49/B53's well-founded recursion
//! (imported_structural_recursion scenario).
//!
//! ## What an imported structurally-recursive def actually is
//!
//! A real Lean `.olean` ships a structurally-recursive function (the everyday
//! case — `List.length`, `Nat.add`, a custom `MyList.sum`) NOT as a surface
//! `match`, but as a plain `Declaration::Definition` whose *body is already
//! lowered* to the inductive's eliminator `T.rec` (or `T.brecOn`), plus a set of
//! `f.eq_*` equation lemmas for `simp`/`rw`. There is **no** clean-side
//! structure/recursor metadata to reconstruct: the kernel sees only the imported
//! `T.rec` recursor and the definitional `T.casesOn` constant.
//!
//! For a custom
//!
//! ```text
//! inductive MyList : Type | nil | cons (head : Nat) (tail : MyList)
//! ```
//!
//! the kernel builds `MyList.rec.{u}` in the standard `MajorAfterMinors` layout
//!
//! ```text
//! @MyList.rec.{u}
//!   {motive : MyList → Sort u}
//!   (m_nil  : motive MyList.nil)                                   -- minor: nil
//!   (m_cons : (head : Nat) → (tail : MyList) → motive tail          -- minor: cons
//!               → motive (MyList.cons head tail))                   --   (carries the IH!)
//!   (t : MyList)                                                    -- major (last)
//!   : motive t
//! ```
//!
//! where the `cons` rule's `recursive_fields = [false, true]` — the `tail` field
//! is recursive, so the `m_cons` minor takes an extra *inductive hypothesis*
//! argument `motive tail`. An imported `sum` is then literally
//!
//! ```text
//! def MyList.sum (t : MyList) : Nat :=
//!   @MyList.rec.{1} (fun _ => Nat) Nat.zero (fun head tail ih => Nat.add head ih) t
//! ```
//!
//! ## Why this is a sharper probe than B49/B53 (well-founded recursion)
//!
//! WF recursion (`Acc.rec`) iota-fires *once* per `Acc.intro` peeled, and the
//! B49/B53 probes drove a single-step accessibility witness. STRUCTURAL recursion
//! over a recursive constructor fires iota **repeatedly**: `sum [1,2,3]` must
//! reduce `MyList.rec` on `cons 1 (cons 2 (cons 3 nil))`, binding the IH to the
//! recursor *re-applied to the tail* at every layer, until it bottoms out at
//! `nil`. A layout bug in how the imported recursor's `cons` minor / IH slot is
//! placed — or in how the recursor re-applies to the tail in the iota rule's RHS
//! — would surface as a *wrong multi-step sum* (e.g. 0, 5, or a stuck term)
//! rather than the genuinely-correct `6`. Distinct element values (`1,2,3`) make
//! a dropped / doubled / mis-summed layer observable; `1+2+3 = 6` is distinct
//! from `0` (collapsed), `5` (head dropped), and `3` (top echoed).
//!
//! ## The probes
//!
//! (a) **multi-step iota reduction**: the imported `sum` applied to a concrete
//!     constructor-built list reduces through `MyList.rec` to the correct sum
//!     (`sum [1,2,3] = 6`, `sum [10,20] = 30`, `length [1,2,3] = 3`).
//! (b) **a def USING the result**: `sumPlusOne [1,2,3] = 7` — composing the
//!     imported recursive function's result into further computation.
//! (c) **the equation lemma**: `rw [MyList.sum.eq_cons]` and
//!     `simp only [MyList.sum.eq_cons]` unfold a use of `sum (cons h t)` to
//!     `Nat.add h (sum t)` and the proof references the imported lemma. Unlike a
//!     WF equation lemma (which needs the propositional `fix_eq` and is NOT
//!     `rfl`-provable), a *structural* equation lemma IS reducible — `sum (cons h
//!     t)` iota-reduces to `Nat.add h (sum t)` — so it is a genuine, sorry-free,
//!     axiom-free `Eq.refl` theorem, exactly as a `.olean` ships it.
//!
//! ## Outcome
//!
//! This validated the import path: USING an imported structurally-recursive def
//! reduces correctly through multi-step iota over the imported `MyList.rec`, a
//! def consuming its result computes correctly, and `rw`/`simp` with its
//! structural equation lemma fires. NO clean-elab correctness bug was found — the
//! recursor-reduction machinery (validated for the single-step case in B29/B43)
//! generalises to the multi-step structural case. The tests LOCK the behavior in.
//! A NATIVE control (Clean's own `MyList` built in-process, `MyList.rec` a
//! registered recursor) runs alongside so any future regression is isolated to
//! the imported-eliminator handling and native behavior stays byte-for-byte
//! identical.

use clean_kernel::env::TrustedEnvExt;
use clean_kernel::env::{Declaration, DeclarationTrustSummary, Environment};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType, RecursorArgOrder};
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, TypeChecker};

use clean_elab::tactic::{rewrite, simp, Goal, ProofState, SimpConfig};
use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat() -> Expr {
    const_("Nat")
}

/// `Sort 1` — the universe `Nat : Type 0 = Sort 1` lives in.
fn lvl1() -> Level {
    Level::succ(Level::zero())
}

/// `Nat` literal `n` in the kernel's native literal representation (the form the
/// unifier normalizes arguments to), so a rewrite's resolved `from` side matches
/// the goal syntactically.
fn nat_lit(n: u32) -> Expr {
    Expr::nat_lit(u64::from(n))
}

/// `MyList.nil`.
fn nil() -> Expr {
    const_("MyList.nil")
}

/// `MyList.cons head tail`.
fn cons(head: Expr, tail: Expr) -> Expr {
    Expr::app(Expr::app(const_("MyList.cons"), head), tail)
}

/// A concrete list `[a, b, c, …]` built from `MyList.cons` / `MyList.nil`.
fn mk_list(elems: &[u32]) -> Expr {
    let mut e = nil();
    for &v in elems.iter().rev() {
        e = cons(nat_lit(v), e);
    }
    e
}

/// `@Eq Nat lhs rhs` (`Nat : Type`, so the `Eq` universe level is `1`).
fn nat_eq(lhs: Expr, rhs: Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![lvl1()]);
    Expr::app(Expr::app(Expr::app(eq, nat()), lhs), rhs)
}

/// Reduce `expr` to whnf and return its head `Const` name / literal repr.
fn whnf_head(env: &Environment, expr: &Expr) -> String {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.kind() {
        ExprKind::Lit(_) => format!("{:?}", reduced.kind()),
        _ => match reduced.get_app_fn().kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        },
    }
}

/// Kernel-check an assembled closed `proof` against `goal_ty` using the trusted
/// `TypeChecker` (full checking via `check_type`). The authoritative kernel
/// acceptance check.
fn kernel_check_proof(env: &Environment, goal_ty: &Expr, proof: &Expr) {
    let tc = TypeChecker::new(env);
    tc.check_type(proof, goal_ty)
        .unwrap_or_else(|e| panic!("assembled proof must kernel-check against the goal: {e:?}"));
}

/// `inductive MyList : Type | nil | cons (head : Nat) (tail : MyList)`.
///
/// A non-parameterised recursive inductive over `Nat` elements. The `cons`
/// constructor's `tail` field is recursive, so `MyList.rec`'s `cons` minor
/// carries an inductive hypothesis — the structural-recursion shape this file
/// probes.
fn mylist_decl() -> InductiveDecl {
    let mylist = const_("MyList");
    // MyList : Type
    let ind_ty = Expr::type_();
    // nil : MyList
    let nil_ty = mylist.clone();
    // cons : Nat -> MyList -> MyList
    let cons_ty = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(BinderInfo::Default, mylist.clone(), mylist),
    );

    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("MyList"),
            type_: ind_ty,
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyList.nil"),
                    type_: nil_ty,
                },
                Constructor {
                    name: Name::from_string("MyList.cons"),
                    type_: cons_ty,
                },
            ],
        }],
    }
}

/// A faithfully *imported* `MyList`: the kernel-built family, both constructors,
/// and the `MyList.rec` recursor copied verbatim into a fresh env. `MyList.rec`
/// stays a registered recursor (so the kernel can iota-reduce); there is no
/// clean-side structure metadata, exactly as a `.olean` member is shaped.
fn imported_mylist_env() -> Environment {
    let mut native = Environment::new();
    native.init_nat().expect("init_nat");
    native.init_eq().expect("init_eq");
    native
        .add_inductive(mylist_decl())
        .expect("MyList should declare");

    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");

    let iv = native
        .get_inductive(&Name::from_string("MyList"))
        .cloned()
        .expect("scratch env has MyList");
    env.register_inductive(iv);
    for ctor in ["MyList.nil", "MyList.cons"] {
        let c = native
            .get_constructor(&Name::from_string(ctor))
            .cloned()
            .unwrap_or_else(|| panic!("{ctor} constructor"));
        env.register_constructor(c);
    }
    // MyList.rec stays a recursor on import: copy its ConstantInfo + RecursorVal
    // so the kernel can iota-reduce and the elaborator can reference it.
    let rec_const = native
        .get_const(&Name::from_string("MyList.rec"))
        .cloned()
        .expect("MyList.rec const");
    env.extend_constants_unchecked(std::iter::once(rec_const));
    let rec_val = native
        .get_recursor(&Name::from_string("MyList.rec"))
        .cloned()
        .expect("MyList.rec recursor");
    env.register_recursor(rec_val);
    env
}

fn elaborate_decls_into(env: &mut Environment, source: &str) {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source should parse");
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .unwrap_or_else(|e| panic!("declaration {i} should elaborate and kernel-check: {e}"));
    }
}

/// The imported structurally-recursive functions, lowered *directly* to
/// `@MyList.rec.{1}` exactly as a `.olean` ships them (no surface `match`), and
/// elaborated through the clean-elab elaborator so the elaborator+kernel both
/// accept a body that references the imported recursor:
///
/// ```text
/// MyList.sum t    = @MyList.rec.{1} (fun _ => Nat) 0       (fun h t ih => Nat.add h ih) t
/// MyList.length t = @MyList.rec.{1} (fun _ => Nat) 0       (fun h t ih => Nat.succ ih)  t
/// ```
const STRUCTURAL_DEFS: &str = "\
def MyList.sum (t : MyList) : Nat :=\n  \
  @MyList.rec (fun _ => Nat) Nat.zero (fun head tail ih => Nat.add head ih) t\n\
def MyList.length (t : MyList) : Nat :=\n  \
  @MyList.rec (fun _ => Nat) Nat.zero (fun head tail ih => Nat.succ ih) t\n\
def sumPlusOne (t : MyList) : Nat := Nat.succ (MyList.sum t)\n";

/// Register the structural equation lemma
/// `MyList.sum.eq_cons : ∀ (h : Nat) (t : MyList), MyList.sum (MyList.cons h t) = Nat.add h (MyList.sum t)`
/// as a kernel `Declaration::Theorem`, exactly as a `.olean` ships an equation
/// lemma — a fully-formed declaration with a baked-in proof term.
///
/// The proof is `fun h t => @Eq.refl Nat (Nat.add h (MyList.sum t))`, which
/// kernel-checks at the stated `∀`-equation because `MyList.sum (MyList.cons h
/// t)` iota-reduces through the imported `MyList.rec` to `Nat.add h (MyList.sum
/// t)`. Crucially this is `rfl`-provable (structural recursion reduces), so the
/// lemma is genuinely sorry-free and axiom-free with no `add_decl_structural`.
fn register_sum_eq_cons(env: &mut Environment) {
    // ∀ (h : Nat) (t : MyList), MyList.sum (MyList.cons h t) = Nat.add h (MyList.sum t)
    // under [h, t]: h = BVar1, t = BVar0.
    let sum = const_("MyList.sum");
    let lhs = Expr::app(sum.clone(), cons(Expr::bvar(1), Expr::bvar(0)));
    let rhs = Expr::app(
        Expr::app(const_("Nat.add"), Expr::bvar(1)),
        Expr::app(sum.clone(), Expr::bvar(0)),
    );
    let eq_body = nat_eq(lhs, rhs);
    let ty = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(BinderInfo::Default, const_("MyList"), eq_body),
    );

    // proof: fun (h : Nat) (t : MyList) => @Eq.refl Nat (Nat.add h (MyList.sum t))
    let refl = Expr::const_(Name::from_string("Eq.refl"), vec![lvl1()]);
    let rhs_val = Expr::app(
        Expr::app(const_("Nat.add"), Expr::bvar(1)),
        Expr::app(sum, Expr::bvar(0)),
    );
    let refl_body = Expr::app(Expr::app(refl, nat()), rhs_val);
    let value = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, const_("MyList"), refl_body),
    );

    env.add_decl(Declaration::Theorem {
        name: Name::from_string("MyList.sum.eq_cons"),
        level_params: vec![],
        type_: ty,
        value,
    })
    .expect("structural equation lemma MyList.sum.eq_cons should kernel-check (rfl-provable)");
}

// ===========================================================================
// Precondition: the synthesized env is the genuine *import* configuration —
// MyList.rec is a registered recursor in the MajorAfterMinors layout whose
// `cons` rule carries a recursive field (the IH), and the structural defs are
// plain Definitions (NOT recursors) whose bodies recurse through MyList.rec.
// ===========================================================================

#[test]
fn test_imported_mylist_rec_has_recursive_cons_minor_and_defs_use_it() {
    let mut env = imported_mylist_env();

    let rec = env
        .get_recursor(&Name::from_string("MyList.rec"))
        .expect("MyList.rec must be a registered recursor on import");
    assert_eq!(rec.num_params, 0, "MyList has no parameters");
    assert_eq!(rec.num_indices, 0, "MyList has no indices");
    assert_eq!(rec.num_motives, 1, "MyList.rec: single motive");
    assert_eq!(rec.num_minors, 2, "MyList.rec: one minor per constructor");
    assert_eq!(
        rec.arg_order,
        RecursorArgOrder::MajorAfterMinors,
        "MyList.rec uses the standard MajorAfterMinors layout"
    );
    let cons_rule = rec
        .rules
        .iter()
        .find(|r| r.constructor_name == Name::from_string("MyList.cons"))
        .expect("MyList.rec has a cons rule");
    assert_eq!(
        cons_rule.recursive_fields,
        vec![false, true],
        "the cons rule's `tail` field is RECURSIVE (head is not) — its minor \
         carries an inductive hypothesis, the structural-recursion shape"
    );

    elaborate_decls_into(&mut env, STRUCTURAL_DEFS);

    // The imported recursive functions are plain Definitions, not recursors, and
    // their bodies recurse through the imported MyList.rec.
    for name in ["MyList.sum", "MyList.length"] {
        assert!(
            env.get_recursor(&Name::from_string(name)).is_none(),
            "{name} must be a definition, not a registered recursor"
        );
        let body = env
            .get_const(&Name::from_string(name))
            .and_then(|i| i.value.clone())
            .unwrap_or_else(|| panic!("{name} should have a definition body"));
        assert!(
            body.collect_constants()
                .contains(&Name::from_string("MyList.rec")),
            "{name}'s body must recurse through the imported MyList.rec, got: {:?}",
            body.collect_constants()
        );
    }
}

// ===========================================================================
// Control: the imported MyList.rec iota-reduces *by hand* over a multi-layer
// cons list to the correct value, isolating any later failure to the elaborator
// rather than the kernel's reduction of the imported recursor.
// ===========================================================================

#[test]
fn test_imported_mylist_rec_kernel_multistep_iota_is_correct() {
    let env = imported_mylist_env();
    let tc = TypeChecker::new(&env);

    // @MyList.rec.{1} (fun _ => Nat) Nat.zero (fun head tail ih => Nat.add head ih) [1,2,3]
    // = Nat.add 1 (Nat.add 2 (Nat.add 3 0)) = 6, via THREE iota steps + a nil base.
    let motive = Expr::lam(BinderInfo::Default, const_("MyList"), nat());
    // m_cons := fun (head : Nat) (tail : MyList) (ih : Nat) => Nat.add head ih
    //   under [head, tail, ih]: head = BVar2, ih = BVar0.
    let m_cons = {
        let body = Expr::app(Expr::app(const_("Nat.add"), Expr::bvar(2)), Expr::bvar(0));
        let lam_ih = Expr::lam(BinderInfo::Default, nat(), body);
        let lam_tail = Expr::lam(BinderInfo::Default, const_("MyList"), lam_ih);
        Expr::lam(BinderInfo::Default, nat(), lam_tail)
    };
    let rec = Expr::const_(Name::from_string("MyList.rec"), vec![lvl1()]);
    let mk_app = |major: Expr| {
        let app = Expr::app(rec.clone(), motive.clone());
        let app = Expr::app(app, const_("Nat.zero"));
        let app = Expr::app(app, m_cons.clone());
        Expr::app(app, major)
    };

    let sum123 = mk_app(mk_list(&[1, 2, 3]));
    assert!(
        tc.is_def_eq(&sum123, &nat_lit(6)),
        "imported MyList.rec over [1,2,3] must multi-step iota-reduce to 6; got head {}",
        whnf_head(&env, &sum123)
    );
    // Distinct wrong values a layout / IH bug would produce.
    assert!(
        !tc.is_def_eq(&sum123, &nat_lit(0)),
        "multi-step reduction must not collapse to 0 (a dropped recursion)"
    );
    assert!(
        !tc.is_def_eq(&sum123, &nat_lit(5)),
        "multi-step reduction must not drop the head (5 = 2+3)"
    );
    assert!(
        !tc.is_def_eq(&sum123, &nat_lit(3)),
        "multi-step reduction must not echo the top element (3)"
    );

    // The nil base case reduces to the zero minor.
    let sum_nil = mk_app(nil());
    assert!(
        tc.is_def_eq(&sum_nil, &nat_lit(0)),
        "imported MyList.rec over nil must reduce to the zero minor (0); got head {}",
        whnf_head(&env, &sum_nil)
    );
}

// ===========================================================================
// MAIN PROBE (a): the elaborated imported `MyList.sum` / `MyList.length`,
// applied to concrete constructor-built lists, reduce through multi-step iota
// over the imported MyList.rec to the genuinely-correct DISTINCT values.
// ===========================================================================

#[test]
fn test_imported_structural_sum_and_length_reduce_correctly() {
    let mut env = imported_mylist_env();
    elaborate_decls_into(&mut env, STRUCTURAL_DEFS);
    let tc = TypeChecker::new(&env);

    // sum [1,2,3] = 6 (NOT 0, 5, or 3).
    let sum123 = Expr::app(const_("MyList.sum"), mk_list(&[1, 2, 3]));
    assert!(
        tc.is_def_eq(&sum123, &nat_lit(6)),
        "MyList.sum [1,2,3] must reduce to 6 through the imported recursor; got head {}",
        whnf_head(&env, &sum123)
    );
    assert!(
        !tc.is_def_eq(&sum123, &nat_lit(0)),
        "sum must not collapse to 0"
    );
    assert!(
        !tc.is_def_eq(&sum123, &nat_lit(5)),
        "sum must not drop the head element (5 = 2+3)"
    );

    // A second, distinct witness: sum [10,20] = 30.
    let sum1020 = Expr::app(const_("MyList.sum"), mk_list(&[10, 20]));
    assert!(
        tc.is_def_eq(&sum1020, &nat_lit(30)),
        "MyList.sum [10,20] must reduce to 30; got head {}",
        whnf_head(&env, &sum1020)
    );

    // sum [] = 0 (the base case).
    let sum_empty = Expr::app(const_("MyList.sum"), mk_list(&[]));
    assert!(
        tc.is_def_eq(&sum_empty, &nat_lit(0)),
        "MyList.sum [] must reduce to 0; got head {}",
        whnf_head(&env, &sum_empty)
    );

    // length [1,2,3] = 3 — a *different* structural recursion over the same
    // imported recursor (counts layers rather than summing), so a shared-layout
    // bug would diverge from `sum` here.
    let len123 = Expr::app(const_("MyList.length"), mk_list(&[1, 2, 3]));
    assert!(
        tc.is_def_eq(&len123, &nat_lit(3)),
        "MyList.length [1,2,3] must reduce to 3; got head {}",
        whnf_head(&env, &len123)
    );
    assert!(
        !tc.is_def_eq(&len123, &nat_lit(6)),
        "length must count layers (3), not sum elements (6) — a swapped minor body \
         would surface here"
    );
}

// ===========================================================================
// MAIN PROBE (b): a def CONSUMING the imported recursive function's result.
// `sumPlusOne t := Nat.succ (MyList.sum t)` composes `sum`'s value into further
// computation; `sumPlusOne [1,2,3] = 7`.
// ===========================================================================

#[test]
fn test_def_using_imported_structural_result_computes() {
    let mut env = imported_mylist_env();
    elaborate_decls_into(&mut env, STRUCTURAL_DEFS);
    let tc = TypeChecker::new(&env);

    // sumPlusOne [1,2,3] = succ (sum [1,2,3]) = succ 6 = 7.
    let call = Expr::app(const_("sumPlusOne"), mk_list(&[1, 2, 3]));
    assert!(
        tc.is_def_eq(&call, &nat_lit(7)),
        "sumPlusOne [1,2,3] must consume sum's result (6) and compute 7; got head {}",
        whnf_head(&env, &call)
    );
    assert!(
        !tc.is_def_eq(&call, &nat_lit(6)),
        "sumPlusOne must add one (7), not echo sum (6)"
    );

    // A use inside a further-elaborated def that pattern-matches the result is a
    // legitimate downstream consumer; check via def-eq on a distinct witness too.
    let call2 = Expr::app(const_("sumPlusOne"), mk_list(&[10, 20]));
    assert!(
        tc.is_def_eq(&call2, &nat_lit(31)),
        "sumPlusOne [10,20] must compute succ 30 = 31; got head {}",
        whnf_head(&env, &call2)
    );
}

// ===========================================================================
// MAIN PROBE (c1): `rw [MyList.sum.eq_cons]` unfolds a USE of the imported
// structurally-recursive `sum` on a `cons` head. The structural equation lemma
// is `rfl`-provable (unlike a WF one), so it is a genuine sorry-free, axiom-free
// imported lemma; the rewrite must peel its ∀ binders, instantiate, and fire.
// ===========================================================================

#[test]
fn test_rw_imported_structural_eq_cons_unfolds_use() {
    let mut env = imported_mylist_env();
    elaborate_decls_into(&mut env, STRUCTURAL_DEFS);
    register_sum_eq_cons(&mut env);

    // The equation lemma is itself sorry-free and axiom-free.
    let trust = env
        .get_const(&Name::from_string("MyList.sum.eq_cons"))
        .expect("eq_cons registered")
        .trust_summary();
    assert!(
        trust.is_fully_verified(),
        "structural equation lemma must be sorry-free and axiom-free, got {trust:?}"
    );

    // Goal: MyList.sum (cons 1 (cons 2 nil)) = Nat.add 1 (MyList.sum (cons 2 nil)).
    let tail = cons(nat_lit(2), nil());
    let lhs_use = Expr::app(const_("MyList.sum"), cons(nat_lit(1), tail.clone()));
    let rhs_target = Expr::app(
        Expr::app(const_("Nat.add"), nat_lit(1)),
        Expr::app(const_("MyList.sum"), tail),
    );
    let goal_target = nat_eq(lhs_use, rhs_target);

    let mut state = ProofState::new(env, goal_target);
    let root_goal: Goal = state
        .goals()
        .front()
        .cloned()
        .expect("fresh proof state has exactly one goal");

    // rw [MyList.sum.eq_cons] rewrites sum (cons 1 …) -> Nat.add 1 (sum …) (forward).
    rewrite(&mut state, "MyList.sum.eq_cons", false)
        .expect("rw [MyList.sum.eq_cons] should resolve the imported ∀-equation and fire");

    // The remaining goal `Nat.add 1 (sum …) = Nat.add 1 (sum …)` closes by def-eq.
    let close = simp(&mut state, SimpConfig::new());
    assert!(
        close.is_ok() && state.goals().is_empty(),
        "after rw [eq_cons], the residual goal must close by def-eq; remaining goals: {}",
        state.goals().len()
    );

    let proof = state
        .closed_proof()
        .expect("a completed rw+close proof state must yield a closed proof term");
    kernel_check_proof(state.env(), &root_goal.target, &proof);

    // The rewrite genuinely fired iff the imported lemma appears in the proof.
    let constants = proof.collect_constants();
    assert!(
        constants.contains(&Name::from_string("MyList.sum.eq_cons")),
        "rw's proof must reference the imported equation lemma (proving the rewrite \
         fired, not a coincidental def-eq), references: {constants:?}"
    );
    let trust = DeclarationTrustSummary::from_expr(&proof);
    assert!(
        !trust.has_sorry(),
        "rw proof must be sorry-free, got {trust:?}"
    );
    assert_eq!(
        trust.trusted_axiom_count(),
        0,
        "rw proof must carry no trusted axioms, got {trust:?}"
    );
}

// ===========================================================================
// MAIN PROBE (c2): `simp only [MyList.sum.eq_cons]` CLOSES a use-goal soundly.
// For a *reducible* structural def, `sum (cons 1 nil)` whnf-reduces; simp's
// matcher discharges the (now definitionally-true) goal — a sound, kernel-checked
// proof. Locks the simp-matcher behavior over an imported structural use in.
// ===========================================================================

#[test]
fn test_simp_imported_structural_eq_cons_closes_use() {
    let mut env = imported_mylist_env();
    elaborate_decls_into(&mut env, STRUCTURAL_DEFS);
    register_sum_eq_cons(&mut env);

    // Goal: MyList.sum (cons 3 nil) = 3  (a use that reduces: 3 + sum nil = 3 + 0 = 3).
    let lhs_use = Expr::app(const_("MyList.sum"), cons(nat_lit(3), nil()));
    let goal_target = nat_eq(lhs_use, nat_lit(3));

    let mut state = ProofState::new(env, goal_target);
    let root_goal: Goal = state
        .goals()
        .front()
        .cloned()
        .expect("fresh proof state has one goal");

    let mut cfg = SimpConfig::new();
    cfg.only = true;
    cfg.extra_lemmas = vec!["MyList.sum.eq_cons".to_string()];
    let res = simp(&mut state, cfg);
    assert!(
        res.is_ok() && state.goals().is_empty(),
        "simp only [MyList.sum.eq_cons] must close `sum (cons 3 nil) = 3`; \
         remaining goals: {}",
        state.goals().len()
    );

    let proof = state
        .closed_proof()
        .expect("a completed simp proof state must yield a closed proof term");
    kernel_check_proof(state.env(), &root_goal.target, &proof);
    let trust = DeclarationTrustSummary::from_expr(&proof);
    assert!(
        !trust.has_sorry(),
        "simp proof must be sorry-free, got {trust:?}"
    );
    assert_eq!(
        trust.trusted_axiom_count(),
        0,
        "simp proof must carry no trusted axioms, got {trust:?}"
    );
}

// ===========================================================================
// Control: the NATIVE path — Clean's own `MyList` built in-process (MyList.rec a
// registered recursor) — lowers the SAME structural defs and reduces identically.
// Confirms the imported-recursor handling matches native behavior byte-for-byte.
// ===========================================================================

#[test]
fn test_native_mylist_structural_recursion_reduces_correctly() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    env.add_inductive(mylist_decl())
        .expect("MyList should declare");

    // Native MyList.rec IS a registered recursor with the same layout as the copy.
    let rec = env
        .get_recursor(&Name::from_string("MyList.rec"))
        .expect("native MyList.rec recursor");
    assert_eq!(rec.arg_order, RecursorArgOrder::MajorAfterMinors);
    assert_eq!(rec.num_minors, 2);

    elaborate_decls_into(&mut env, STRUCTURAL_DEFS);
    let tc = TypeChecker::new(&env);

    let sum123 = Expr::app(const_("MyList.sum"), mk_list(&[1, 2, 3]));
    assert!(
        tc.is_def_eq(&sum123, &nat_lit(6)),
        "native MyList.sum [1,2,3] must reduce to 6; got head {}",
        whnf_head(&env, &sum123)
    );
    assert!(
        !tc.is_def_eq(&sum123, &nat_lit(0)),
        "native sum must not collapse to 0"
    );

    let len123 = Expr::app(const_("MyList.length"), mk_list(&[1, 2, 3]));
    assert!(
        tc.is_def_eq(&len123, &nat_lit(3)),
        "native MyList.length [1,2,3] must reduce to 3; got head {}",
        whnf_head(&env, &len123)
    );

    let plus = Expr::app(const_("sumPlusOne"), mk_list(&[10, 20]));
    assert!(
        tc.is_def_eq(&plus, &nat_lit(31)),
        "native sumPlusOne [10,20] must compute 31; got head {}",
        whnf_head(&env, &plus)
    );
}
