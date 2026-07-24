// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: **index-discriminating motive** for a single-index GADT `match`
//! that legitimately omits an *index-impossible* constructor whose branch type
//! has **no closed inhabitant** (Track G general dependent elimination).
//!
//! ## The canonical gap
//!
//! ```text
//! inductive Vec (α : Type) : Nat → Type
//!   | nil  : Vec α Nat.zero
//!   | cons : {n : Nat} → α → Vec α n → Vec α (Nat.succ n)
//!
//! def Vec.head {α} {n} (v : Vec α (Nat.succ n)) : α :=
//!   match v with | Vec.cons x _ => x
//! ```
//!
//! Matching `Vec α (Nat.succ n)` against only `cons` leaves the `nil` branch
//! (index `Nat.zero`) required by the eliminator but **unreachable** — its index
//! `Nat.zero` clashes with the scrutinee's `Nat.succ n` (distinct `Nat`
//! constructors, so impossible *even with the free variable `n`*). Under a
//! constant motive the omitted `nil` minor would need to inhabit `α`, which has
//! no closed inhabitant — so it cannot be filled without a `sorry`.
//!
//! ## The sound discharge (this change)
//!
//! Build an **index-discriminating** motive
//! `fun (m : Nat) (_ : Vec α m) => @Nat.rec (fun _ => Type) PUnit.{1} (fun _ _ => α) m`
//! which returns `α` at the reachable `succ` head and `PUnit.{1}` at the
//! impossible `zero` head. The omitted `nil` minor is then `PUnit.unit.{1}` — a
//! trivially-inhabited, axiom-free, `sorry`-free term — while the reachable
//! `cons` minor keeps the real result type `α`. The kernel re-checks the whole
//! lowered `Vec.casesOn` application, so registration success is the soundness
//! gate; we additionally assert an **empty axiom-dependency closure** so no
//! `sorry` (or any fabricated axiom) can have crept in.

use clean_kernel::env::Environment;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Expr, Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `Vec : (α : Type) → Nat → Type` with
///   `nil  : (α) → Vec α Nat.zero`
///   `cons : (α) → {n : Nat} → α → Vec α n → Vec α (Nat.succ n)`
fn vec_decl() -> InductiveDecl {
    let vec_ty = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, c("Nat"), Expr::type_()),
    );
    // nil : (α : Type) → Vec α Nat.zero    (α = BVar0)
    let nil_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::app(Expr::app(c("Vec"), Expr::bvar(0)), c("Nat.zero")),
    );
    // cons : (α) → {n} → α → Vec α n → Vec α (succ n)
    //   binders α(3) n(2) x(1) tl(0)
    let cons_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Implicit,
            c("Nat"),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // x : α
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(Expr::app(c("Vec"), Expr::bvar(2)), Expr::bvar(1)), // tl : Vec α n
                    Expr::app(
                        Expr::app(c("Vec"), Expr::bvar(3)),
                        Expr::app(c("Nat.succ"), Expr::bvar(2)),
                    ), // Vec α (succ n)
                ),
            ),
        ),
    );
    InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("Vec"),
            type_: vec_ty,
            constructors: vec![
                Constructor {
                    name: Name::from_string("Vec.nil"),
                    type_: nil_ty,
                },
                Constructor {
                    name: Name::from_string("Vec.cons"),
                    type_: cons_ty,
                },
            ],
        }],
    }
}

fn vec_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.add_inductive(vec_decl()).expect("Vec declares");
    env
}

fn elaborate_into(env: &mut Environment, source: &str) {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source parses");
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .unwrap_or_else(|e| panic!("declaration {i} should elaborate and kernel-check: {e}"));
    }
}

fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source parses");
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// MAIN PROBE: Vec.head over `Vec α (succ n)` (a *non-variable* index) matching
// only `cons` elaborates, kernel-checks, lowers through the discriminating
// motive, and has an empty axiom-dependency closure (no sorry / fabricated
// axiom).
// ---------------------------------------------------------------------------

#[test]
fn vec_head_omitted_impossible_nil_kernel_checks_sorry_free() {
    let mut env = vec_env();

    elaborate_into(
        &mut env,
        "def Vec.head {α : Type} {n : Nat} (v : Vec α (Nat.succ n)) : α :=\n  \
         match v with\n  | Vec.cons x _ => x",
    );

    let info = env
        .get_const(&Name::from_string("Vec.head"))
        .expect("Vec.head registered");
    let body = info.value.as_ref().expect("Vec.head is a definition");
    let consts = body.collect_constants();

    // Lowered through Vec.casesOn (the eliminator) and the index-discriminating
    // motive's `Nat.rec` + `PUnit.unit` impossible minor.
    assert!(
        consts.contains(&Name::from_string("Vec.casesOn")),
        "Vec.head must lower through Vec.casesOn; got {consts:?}"
    );
    assert!(
        consts.contains(&Name::from_string("Nat.rec")),
        "the index-discriminating motive must use Nat.rec; got {consts:?}"
    );
    assert!(
        consts.contains(&Name::from_string("PUnit.unit")),
        "the omitted impossible nil minor must be PUnit.unit; got {consts:?}"
    );

    // SOUNDNESS 1 — infer_type: the kernel re-derives Vec.head's declared type.
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(body)
        .expect("Vec.head body must infer a type in the kernel");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "Vec.head body type must be def-eq to its declared type:\n  got {inferred:?}\n  exp {:?}",
        info.type_
    );

    // SOUNDNESS 2 — empty axiom_deps closure: no sorry / sorryAx / fabricated
    // axiom anywhere in the transitive dependency closure.
    let deps = env
        .axiom_deps(&Name::from_string("Vec.head"))
        .expect("Vec.head has an axiom_deps closure");
    assert!(
        deps.is_empty(),
        "Vec.head must be axiom-free (no sorry / fabricated axiom); got {deps:?}"
    );
}

// ---------------------------------------------------------------------------
// REDUCTION PROBE: Vec.head genuinely projects the head element — a wrong motive
// / a mis-placed minor would surface as a different observable result.
// ---------------------------------------------------------------------------

#[test]
fn vec_head_reduces_to_head_element() {
    let mut env = vec_env();
    elaborate_into(
        &mut env,
        "def Vec.head {α : Type} {n : Nat} (v : Vec α (Nat.succ n)) : α :=\n  \
         match v with\n  | Vec.cons x _ => x",
    );

    // v := @Vec.cons Nat 0 (Nat.succ Nat.zero) (@Vec.nil Nat)   :  Vec Nat 1
    // Vec.head Nat 0 v  ==>  Nat.succ Nat.zero (the head element, 1)
    let one = Expr::app(c("Nat.succ"), c("Nat.zero"));
    let nil_nat = Expr::app(c("Vec.nil"), c("Nat"));
    let cons = Expr::const_(Name::from_string("Vec.cons"), vec![]);
    // @Vec.cons Nat (n:=0) (x:=1) (tl:=nil)
    let v = Expr::apps(cons, [c("Nat"), c("Nat.zero"), one.clone(), nil_nat]);
    let head = Expr::const_(Name::from_string("Vec.head"), vec![]);
    let call = Expr::apps(head, [c("Nat"), c("Nat.zero"), v]);

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&call, &one),
        "Vec.head (cons 1 nil) must reduce to the head element 1; got {:?}",
        tc.whnf(&call)
    );
    assert!(
        !tc.is_def_eq(&call, &c("Nat.zero")),
        "the reachable cons branch must not collapse to a default"
    );
}

// ---------------------------------------------------------------------------
// POLY-α GROUND PROBE: the *other* gap that a constant-motive default could not
// fill — a ground impossible index whose branch type is a bare `α`.
// ---------------------------------------------------------------------------

#[test]
fn gadt_poly_result_ground_impossible_index_kernel_checks() {
    let mut env = Environment::with_prelude();
    // inductive Ty | a | b
    // inductive GVal (α) : Ty → Type | mkA : α → GVal α Ty.a | mkB : GVal α Ty.b
    elaborate_into(
        &mut env,
        "inductive Ty where\n  | a : Ty\n  | b : Ty\n\
         inductive GVal (α : Type) : Ty → Type where\n  \
         | mkA : α → GVal α Ty.a\n  | mkB : GVal α Ty.b\n\
         def GVal.getA {α : Type} (e : GVal α Ty.a) : α :=\n  \
         match e with\n  | GVal.mkA x => x",
    );

    let info = env
        .get_const(&Name::from_string("GVal.getA"))
        .expect("GVal.getA registered");
    let tc = TypeChecker::new(&env);
    let body = info.value.as_ref().expect("GVal.getA has a value");
    let inferred = tc.infer_type(body).expect("GVal.getA infers");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "GVal.getA body type must be def-eq to its declared type"
    );
    let deps = env
        .axiom_deps(&Name::from_string("GVal.getA"))
        .expect("axiom_deps closure");
    assert!(
        deps.is_empty(),
        "GVal.getA must be axiom-free; got {deps:?}"
    );
}

// ---------------------------------------------------------------------------
// SOUNDNESS GUARD: a *variable*-index match that omits a *reachable* constructor
// must STILL be rejected. The `nil` index `zero` and the variable scrutinee index
// `n` do NOT clash (no constructor-head conflict), so the impossibility check
// does not fire, the discriminating motive is not engaged, and the genuinely
// non-exhaustive match is rejected — never silently filled.
// ---------------------------------------------------------------------------

#[test]
fn variable_index_omitting_reachable_arm_is_still_rejected() {
    let mut env = vec_env();
    let result = try_elaborate_into(
        &mut env,
        "def Vec.bad {α : Type} {n : Nat} (v : Vec α n) : Nat :=\n  \
         match v with\n  | Vec.cons x _ => Nat.zero",
    );
    assert!(
        result.is_err(),
        "a variable-index match omitting a reachable constructor must be rejected"
    );
    assert!(
        env.get_const(&Name::from_string("Vec.bad")).is_none(),
        "Vec.bad must not be registered after a rejected elaboration"
    );
}

// ---------------------------------------------------------------------------
// EXHAUSTIVE CONTROL: writing BOTH arms at a variable index still elaborates and
// reduces on each constructor — the pre-existing indexed-family handling is
// unchanged by the discriminating-motive addition.
// ---------------------------------------------------------------------------

#[test]
fn variable_index_exhaustive_match_unchanged() {
    let mut env = vec_env();
    elaborate_into(
        &mut env,
        "def Vec.len {α : Type} {n : Nat} (v : Vec α n) : Nat :=\n  \
         match v with\n  | Vec.nil => Nat.zero\n  | Vec.cons _ _ => Nat.succ Nat.zero",
    );

    let tc = TypeChecker::new(&env);
    // Vec.len Nat 0 (nil)         => 0
    let nil_nat = Expr::app(c("Vec.nil"), c("Nat"));
    let len = Expr::const_(Name::from_string("Vec.len"), vec![]);
    let call_nil = Expr::apps(len.clone(), [c("Nat"), c("Nat.zero"), nil_nat.clone()]);
    assert!(
        tc.is_def_eq(&call_nil, &c("Nat.zero")),
        "Vec.len nil must reduce to 0"
    );
    // Vec.len Nat 1 (cons 1 nil)  => 1
    let one = Expr::app(c("Nat.succ"), c("Nat.zero"));
    let cons = Expr::const_(Name::from_string("Vec.cons"), vec![]);
    let v = Expr::apps(cons, [c("Nat"), c("Nat.zero"), one.clone(), nil_nat]);
    let call_cons = Expr::apps(len, [c("Nat"), one.clone(), v]);
    assert!(
        tc.is_def_eq(&call_cons, &one),
        "Vec.len (cons 1 nil) must reduce to 1"
    );
}

// ---------------------------------------------------------------------------
// SUB-GAP (2) — NON-VARIABLE INDEX, dependent return. `Vec.dup2` rebuilds a
// `Vec α (Nat.succ n)` from a match whose scrutinee index is the *non-variable*
// `Nat.succ n`. The motive must be index-refining (`fun (m)(_) => Vec α m`,
// recovered by abstracting the whole `Nat.succ n` index term), so the `cons` arm
// gets the refined `Vec α (Nat.succ k)` and `Vec.cons x tl` fits. Before the
// non-variable extension to `build_indexed_dependent_motive_body`, this bailed to
// the constant motive and the kernel rejected the `cons` arm.
// ---------------------------------------------------------------------------

#[test]
fn non_variable_index_dependent_return_rebuild_kernel_checks() {
    let mut env = vec_env();
    elaborate_into(
        &mut env,
        "def Vec.dup2 {α : Type} {n : Nat} (v : Vec α (Nat.succ n)) : Vec α (Nat.succ n) :=\n  \
         match v with\n  | Vec.nil => Vec.nil\n  | Vec.cons x tl => Vec.cons x tl",
    );

    let info = env
        .get_const(&Name::from_string("Vec.dup2"))
        .expect("Vec.dup2 registered");
    let tc = TypeChecker::new(&env);
    let body = info.value.as_ref().expect("Vec.dup2 value");
    let inferred = tc.infer_type(body).expect("Vec.dup2 infers");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "Vec.dup2 body type must be def-eq to its declared type"
    );
    let deps = env
        .axiom_deps(&Name::from_string("Vec.dup2"))
        .expect("axiom_deps closure");
    assert!(deps.is_empty(), "Vec.dup2 must be axiom-free; got {deps:?}");

    // Vec.dup2 Nat 0 (cons 1 nil) reduces back to cons 1 nil (a faithful rebuild).
    let one = Expr::app(c("Nat.succ"), c("Nat.zero"));
    let nil_nat = Expr::app(c("Vec.nil"), c("Nat"));
    let cons = Expr::const_(Name::from_string("Vec.cons"), vec![]);
    let v = Expr::apps(cons, [c("Nat"), c("Nat.zero"), one.clone(), nil_nat]);
    let dup2 = Expr::const_(Name::from_string("Vec.dup2"), vec![]);
    let call = Expr::apps(dup2, [c("Nat"), c("Nat.zero"), v.clone()]);
    assert!(
        tc.is_def_eq(&call, &v),
        "Vec.dup2 (cons 1 nil) must rebuild to the same cons 1 nil"
    );
}

// ---------------------------------------------------------------------------
// LEVEL-1 / Type-valued sanity: a non-indexed inductive match (no GADT) is
// completely unaffected — the discriminating motive only engages for a
// single-index family with an omitted impossible constructor.
// ---------------------------------------------------------------------------

#[test]
fn non_indexed_match_unaffected() {
    let mut env = Environment::with_prelude();
    elaborate_into(
        &mut env,
        "inductive Color where\n  | red : Color\n  | green : Color\n\
         def Color.toNat (c : Color) : Nat :=\n  \
         match c with\n  | Color.red => Nat.zero\n  | Color.green => Nat.succ Nat.zero",
    );
    let tc = TypeChecker::new(&env);
    let to_nat = Expr::const_(Name::from_string("Color.toNat"), vec![]);
    let call = Expr::app(to_nat, c("Color.red"));
    assert!(
        tc.is_def_eq(&call, &c("Nat.zero")),
        "Color.toNat red must reduce to 0"
    );
    // No PUnit.unit leaked into a fully-exhaustive non-indexed match.
    let body = env
        .get_const(&Name::from_string("Color.toNat"))
        .and_then(|i| i.value.clone())
        .expect("Color.toNat value");
    assert!(
        !body
            .collect_constants()
            .contains(&Name::from_string("PUnit.unit")),
        "an exhaustive non-indexed match must not engage the discriminating motive"
    );
}

// ---------------------------------------------------------------------------
// FILE-PIPELINE E2E (Track K) — the *entire* program is surface text: the `Vec`
// inductive is PARSED (`nil : Vec α 0` writes its impossible index as the numeric
// literal `0`, NOT the hand-built `Const("Nat.zero")`), and elaboration goes
// through the same `parse_file_with_tactics → preprocess → register-with-warning`
// chain that `clean check <file>` uses (cmd_core::check_file_body). Before the
// literal-aware no-confusion fix in `index_head_ctor`, `clean check` reported the
// `cons` minor landing in the `nil` slot (`1 passed, 1 failed`) while the
// hand-built-inductive unit test above passed — a false green. This test pins the
// surface-program path so the divergence cannot silently regress.
// ---------------------------------------------------------------------------

/// Drive the surface program through the exact `clean check` file pipeline:
/// tactic-aware file parse, per-decl `preprocess_decl_with_context`, then
/// `elaborate_decl_and_register_with_warning` (file_ctx is `None`, matching the
/// CLI's per-decl call).
fn elaborate_file_pipeline(env: &mut Environment, source: &str) {
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls = clean_parser::parse_file_with_tactics(source, &patterns).expect("file parses");
    let mut file_ctx = FileContext::new();
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        clean_elab::elaborate_decl_and_register_with_warning(env, &processed)
            .unwrap_or_else(|e| panic!("decl {i} must elaborate via the file pipeline: {e}"));
    }
}

#[test]
fn vec_head_surface_program_passes_file_pipeline_sorry_free() {
    let mut env = Environment::with_prelude();
    // The WHOLE program is surface text — the `Vec` inductive is parsed, so the
    // `nil` index is the numeric literal `0`, exactly as `clean check` sees it.
    elaborate_file_pipeline(
        &mut env,
        "inductive Vec (α : Type) : Nat → Type\n  \
         | nil : Vec α 0\n  \
         | cons : {n : Nat} → α → Vec α n → Vec α (Nat.succ n)\n\
         def Vec.head {α : Type} {n : Nat} (v : Vec α (Nat.succ n)) : α :=\n  \
         match v with\n  | Vec.cons x _ => x",
    );

    let info = env
        .get_const(&Name::from_string("Vec.head"))
        .expect("Vec.head registered via the file pipeline");
    let body = info.value.as_ref().expect("Vec.head is a definition");
    let consts = body.collect_constants();
    // Same discriminating-motive lowering as the hand-built path: Vec.casesOn +
    // the index inductive's Nat.rec + the PUnit.unit impossible minor.
    assert!(
        consts.contains(&Name::from_string("Vec.casesOn")),
        "Vec.head must lower through Vec.casesOn; got {consts:?}"
    );
    assert!(
        consts.contains(&Name::from_string("Nat.rec")),
        "the index-discriminating motive must use Nat.rec; got {consts:?}"
    );
    assert!(
        consts.contains(&Name::from_string("PUnit.unit")),
        "the omitted impossible nil minor must be PUnit.unit; got {consts:?}"
    );

    // SOUNDNESS 1 — infer_type: the kernel re-derives Vec.head's declared type
    // from the lowered term (the soundness gate for the file-pipeline path).
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(body)
        .expect("Vec.head body must infer a type in the kernel");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "Vec.head body type must be def-eq to its declared type:\n  got {inferred:?}\n  exp {:?}",
        info.type_
    );

    // SOUNDNESS 2 — empty axiom_deps closure: no sorry / sorryAx / fabricated
    // axiom anywhere in the transitive dependency closure.
    let deps = env
        .axiom_deps(&Name::from_string("Vec.head"))
        .expect("Vec.head has an axiom_deps closure");
    assert!(
        deps.is_empty(),
        "Vec.head must be axiom-free (no sorry / fabricated axiom); got {deps:?}"
    );

    // REDUCTION — the surface-elaborated Vec.head genuinely projects the head.
    // v := @Vec.cons Nat 0 1 (@Vec.nil Nat) : Vec Nat 1 ;  Vec.head … v ==> 1.
    let one = Expr::app(c("Nat.succ"), c("Nat.zero"));
    let nil_nat = Expr::app(c("Vec.nil"), c("Nat"));
    let cons = Expr::const_(Name::from_string("Vec.cons"), vec![]);
    let v = Expr::apps(cons, [c("Nat"), c("Nat.zero"), one.clone(), nil_nat]);
    let head = Expr::const_(Name::from_string("Vec.head"), vec![]);
    let call = Expr::apps(head, [c("Nat"), c("Nat.zero"), v]);
    assert!(
        tc.is_def_eq(&call, &one),
        "Vec.head (cons 1 nil) must reduce to the head element 1; got {:?}",
        tc.whnf(&call)
    );
}

#[test]
fn variable_index_surface_program_omitting_reachable_arm_still_rejected() {
    // Soundness guard at the file-pipeline level: a *variable*-index match that
    // omits a *reachable* constructor (no constructor-head clash between `nil`'s
    // `0` and the variable index `n`) must STILL be rejected — the literal-aware
    // head recovery must not over-fire and silently fill a genuine non-exhaustive
    // match.
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let src = "inductive Vec (α : Type) : Nat → Type\n  \
         | nil : Vec α 0\n  \
         | cons : {n : Nat} → α → Vec α n → Vec α (Nat.succ n)\n\
         def Vec.bad {α : Type} {n : Nat} (v : Vec α n) : Nat :=\n  \
         match v with\n  | Vec.cons x _ => Nat.zero";
    let decls = clean_parser::parse_file_with_tactics(src, &patterns).expect("file parses");
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut saw_err = false;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        if clean_elab::elaborate_decl_and_register_with_warning(&mut env, &processed).is_err() {
            saw_err = true;
        }
    }
    assert!(
        saw_err,
        "a variable-index match omitting a reachable constructor must be rejected by the file pipeline"
    );
    assert!(
        env.get_const(&Name::from_string("Vec.bad")).is_none(),
        "Vec.bad must not be registered after a rejected elaboration"
    );
}

// ---------------------------------------------------------------------------
// TRACK S — `Vec.tail` INDEX UNIFICATION. The dependent-elimination case where
// the return type mentions the matched constructor's *bound* index via the
// scrutinee index's PREDECESSOR:
//
//   def Vec.tail {α}{n} (v : Vec α (Nat.succ n)) : Vec α n :=
//     match v with | Vec.cons _ tl => tl
//
// The scrutinee index is `Nat.succ n`, but the return type is `Vec α n` — the
// index's predecessor, NOT the index term itself. The straightforward
// whole-index abstraction is a no-op (the term `Nat.succ n` does not occur in
// `Vec α n`), so a constant motive forces the `cons` minor to inhabit `Vec α n`,
// while the bound tail is `tl : Vec α n'` (cons-bound index) — unrelated without
// the `Nat.succ n' = Nat.succ n` equation.
//
// The sound discharge (this change): the index-refining motive
//   fun (m : Nat) (_ : Vec α m) => Vec α (Nat.pred m)
// reduces (iota) at the scrutinee index `Nat.succ n` to `Vec α n` (the declared
// return type) and at the `cons` constructor's refined index `Nat.succ n'` to
// `Vec α n'`, which `tl` inhabits. The kernel re-checks the whole lowered
// `Vec.casesOn` term, so the `Nat.pred ∘ Nat.succ` iota-reduction is the
// soundness gate; an empty axiom-dependency closure rules out any `sorry`.
// ---------------------------------------------------------------------------

#[test]
fn vec_tail_index_unification_kernel_checks_sorry_free() {
    let mut env = vec_env();
    elaborate_into(
        &mut env,
        "def Vec.tail {α : Type} {n : Nat} (v : Vec α (Nat.succ n)) : Vec α n :=\n  \
         match v with\n  | Vec.cons _ tl => tl",
    );

    let info = env
        .get_const(&Name::from_string("Vec.tail"))
        .expect("Vec.tail registered");
    let body = info.value.as_ref().expect("Vec.tail is a definition");
    let consts = body.collect_constants();
    // Lowered through Vec.casesOn with the index-refining motive that uses
    // Nat.pred to express the return type as a function of the matched index.
    assert!(
        consts.contains(&Name::from_string("Vec.casesOn")),
        "Vec.tail must lower through Vec.casesOn; got {consts:?}"
    );
    assert!(
        consts.contains(&Name::from_string("Nat.pred")),
        "the index-refining motive must use Nat.pred; got {consts:?}"
    );

    // SOUNDNESS 1 — infer_type: the kernel re-derives Vec.tail's declared type.
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(body)
        .expect("Vec.tail body must infer a type in the kernel");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "Vec.tail body type must be def-eq to its declared type:\n  got {inferred:?}\n  exp {:?}",
        info.type_
    );

    // SOUNDNESS 2 — empty axiom_deps closure: no sorry / sorryAx / fabricated
    // axiom anywhere in the transitive dependency closure.
    let deps = env
        .axiom_deps(&Name::from_string("Vec.tail"))
        .expect("Vec.tail has an axiom_deps closure");
    assert!(
        deps.is_empty(),
        "Vec.tail must be axiom-free (no sorry / fabricated axiom); got {deps:?}"
    );
}

#[test]
fn vec_tail_reduces_to_the_tail_vector() {
    let mut env = vec_env();
    elaborate_into(
        &mut env,
        "def Vec.tail {α : Type} {n : Nat} (v : Vec α (Nat.succ n)) : Vec α n :=\n  \
         match v with\n  | Vec.cons _ tl => tl",
    );

    let tc = TypeChecker::new(&env);
    // v := @Vec.cons Nat 0 1 (@Vec.nil Nat) : Vec Nat 1 ;
    // Vec.tail Nat 0 v  ==>  @Vec.nil Nat (the tail, length 0).
    let one = Expr::app(c("Nat.succ"), c("Nat.zero"));
    let nil_nat = Expr::app(c("Vec.nil"), c("Nat"));
    let cons = Expr::const_(Name::from_string("Vec.cons"), vec![]);
    let v = Expr::apps(
        cons,
        [c("Nat"), c("Nat.zero"), one.clone(), nil_nat.clone()],
    );
    let tail = Expr::const_(Name::from_string("Vec.tail"), vec![]);
    let call = Expr::apps(tail, [c("Nat"), c("Nat.zero"), v]);
    assert!(
        tc.is_def_eq(&call, &nil_nat),
        "Vec.tail (cons 1 nil) must reduce to nil; got {:?}",
        tc.whnf(&call)
    );
}

#[test]
fn vec_tail_surface_program_passes_file_pipeline_sorry_free() {
    let mut env = Environment::with_prelude();
    // WHOLE program is surface text — the `Vec` inductive is parsed (so `nil`'s
    // index is the numeric literal `0`), exactly as `clean check` sees it.
    elaborate_file_pipeline(
        &mut env,
        "inductive Vec (α : Type) : Nat → Type\n  \
         | nil : Vec α 0\n  \
         | cons : {n : Nat} → α → Vec α n → Vec α (Nat.succ n)\n\
         def Vec.tail {α : Type} {n : Nat} (v : Vec α (Nat.succ n)) : Vec α n :=\n  \
         match v with\n  | Vec.cons _ tl => tl",
    );

    let info = env
        .get_const(&Name::from_string("Vec.tail"))
        .expect("Vec.tail registered via the file pipeline");
    let body = info.value.as_ref().expect("Vec.tail is a definition");
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(body)
        .expect("Vec.tail body must infer a type in the kernel");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "Vec.tail body type must be def-eq to its declared type"
    );
    let deps = env
        .axiom_deps(&Name::from_string("Vec.tail"))
        .expect("Vec.tail has an axiom_deps closure");
    assert!(
        deps.is_empty(),
        "Vec.tail must be axiom-free (no sorry / fabricated axiom); got {deps:?}"
    );
}

#[test]
fn vec_tail_wrong_index_return_is_still_rejected() {
    // NEGATIVE: declaring the return type `Vec α (Nat.succ n)` while the body is
    // the *tail* `tl : Vec α n'` is genuinely ill-typed (`Nat.succ n' ≠ n'`), so
    // the index-refining motive must NOT paper over it — the kernel must reject.
    let mut env = vec_env();
    let result = try_elaborate_into(
        &mut env,
        "def Vec.badtail {α : Type} {n : Nat} (v : Vec α (Nat.succ n)) : Vec α (Nat.succ n) :=\n  \
         match v with\n  | Vec.cons _ tl => tl",
    );
    assert!(
        result.is_err(),
        "returning the tail at the wrong (successor) index must be rejected"
    );
    assert!(
        env.get_const(&Name::from_string("Vec.badtail")).is_none(),
        "Vec.badtail must not be registered after a rejected elaboration"
    );
}
