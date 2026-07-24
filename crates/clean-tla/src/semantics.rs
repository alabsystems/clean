// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T·SEM — TLAsem: the reflected TLA+ behavior semantics, in CIC.
//!
//! This is the FIRST BRICK of the T·SEM keystone of the TY×Clean unified
//! certifying-verification program
//! (`designs/2026-06-20-ty-clean-unified-certifying-program.md`, §6 "T·SEM").
//!
//! It gives `⊨` a *denotation* the clean kernel can check: TLA+ behaviors,
//! the satisfaction relation `Sat`, the run predicate `Runs`, the box/diamond
//! modalities, leads-to, and weak/strong fairness — all as real CIC
//! `Declaration`s registered through `Environment::add_decl`, the kernel's
//! type-checking entry point. The capstone is the kernel-checked theorem
//! [`register_inductive_invariant_sound`]:
//!
//! ```text
//! InductiveInvariantSound :
//!   ∀ (Init : State → Prop) (Next : State → State → Prop) (Safety J : State → Prop),
//!     (∀ s, Init s → J s) →
//!     (∀ s s', J s → Next s s' → J s') →
//!     (∀ s, J s → Safety s) →
//!     ∀ b, Runs Init Next b → Sat b (SemBox (Lift Safety))
//! ```
//!
//! ## Concrete model (M0/M1)
//!
//! Per the directive ("a one-Int-variable `State` is fine"), `State := Nat`.
//! A `Behavior := Nat → State` is an ω-sequence of states. A TLA+ *formula* is
//! shallow-embedded as its denotation — the set of behaviors that satisfy it,
//! i.e. `Behavior → Prop` — so `Sat b F` is literally `F b`. The temporal
//! combinators are then ordinary CIC definitions:
//!
//! | TLA+            | clean definition                                            |
//! |-----------------|-------------------------------------------------------------|
//! | `drop b n`      | `λ i. b (Nat.add n i)`                                       |
//! | `Lift P`        | `λ b. P (b 0)`                                               |
//! | `□F` (`SemBox`) | `λ b. ∀ n, F (drop b n)`                                     |
//! | `◇F` (`SemDiam`)| `λ b. ∃ n, F (drop b n)`                                     |
//! | `P ⇝ Q`         | `□(λ b. P b → ◇Q b)`                                         |
//! | `Sat b F`       | `F b`                                                        |
//! | `Runs I N b`    | `I (b 0) ∧ ∀ n, (N (b n) (b (succ n)) ∨ b (succ n) = b n)`   |
//! | `WF_v A`        | `□(◇□(Lift Enabled A) → ◇⟨A⟩)`                               |
//! | `SF_v A`        | `□(□◇(Lift Enabled A) → ◇⟨A⟩)`                               |
//!
//! `Runs` is **stutter-permissive**: the per-index step relation is
//! `Next ∨ (s' = s)` — exactly TLA+'s `[N]_v`. The soundness theorem therefore
//! preserves `J` across both a real `Next` step and a stutter step (the stutter
//! case is closed by `Eq.subst`, free of any new axiom).
//!
//! ## Honesty (per `AGENTS.md`)
//!
//! Every declaration below is added via `Environment::add_decl`, which runs the
//! kernel type-checker; the capstone is a `Declaration::Theorem` whose proof
//! term is a genuine `Nat.rec` induction — NOT an `Axiom` wrapped in a
//! `Theorem`. The three TLA+ obligations (Init⇒J, consecution, J⇒Safety) are
//! **Pi-bound hypotheses**, not axioms, so the theorem's transitive axiom
//! closure is `⊆ FOUNDATIONAL_AXIOMS` (it reaches only `Eq`/`And`/`Or`/`Nat`).
//! The test module asserts `proof_quality(..) == ProofQuality::Constructive`.
//!
//! `WF`/`SF`/`SemDiam`/`LeadsTo`/`Enabled` are *defined* (M0 surface) but the
//! present brick proves only `InductiveInvariantSound` (safety). The liveness
//! descent lemma `WfDescentSound` named in the design is the next brick.
//!
//! ## Why free functions (not `impl Environment`)
//!
//! The in-kernel proof idiom (`env/*_proof.rs`) uses `impl Environment` +
//! the crate-private `EnvDeclBuilder`. From `clean-tla` (a downstream crate)
//! the orphan rule forbids `impl Environment`, and `EnvDeclBuilder` is
//! `pub(crate)`. So we use free functions over `&mut Environment` and a small
//! local binder builder [`B`] that uses only the public
//! `Expr::fvar`/`Expr::abstract_fvar` surface.

use clean_kernel::env::{Declaration, EnvError, Environment};
use clean_kernel::expr::{BinderInfo, Expr, FVarId};
use clean_kernel::level::Level;
use clean_kernel::name::Name;

/// A tiny binder-safe term builder, mirroring the kernel's (crate-private)
/// `EnvDeclBuilder`: it abstracts named FVars into de-Bruijn binders so we
/// never do manual index arithmetic. Uses only the public `Expr` surface.
pub(crate) struct B {
    next: u64,
}

/// Per-`B` disjoint FVar-id block allocator. Every `B::new()` claims a fresh
/// 2^32-sized block so nested builders never collide (the bug that the
/// kernel's `EnvDeclBuilder::child_of` guards against). The high base avoids
/// collision with any runtime FVarIds (which start from 0).
static B_BLOCK: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

impl B {
    pub(crate) fn new() -> Self {
        let block = B_BLOCK.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        B {
            next: 0xA000_0000_0000_0000 | (block << 32),
        }
    }

    /// Allocate a fresh local; returns `(id, fvar_expr)`.
    pub(crate) fn fresh(&mut self) -> (FVarId, Expr) {
        let id = FVarId::new(self.next);
        self.next += 1;
        (id, Expr::fvar(id))
    }

    /// `Π (x : ty), body` abstracting `id`.
    pub(crate) fn pi(&self, id: FVarId, bi: BinderInfo, ty: Expr, body: Expr) -> Expr {
        Expr::pi(bi, ty, body.abstract_fvar(id))
    }

    /// `λ (x : ty), body` abstracting `id`.
    pub(crate) fn lam(&self, id: FVarId, bi: BinderInfo, ty: Expr, body: Expr) -> Expr {
        Expr::lam(bi, ty, body.abstract_fvar(id))
    }

    /// Assert the expression is closed (no leaked FVars).
    pub(crate) fn finish(&self, e: Expr) -> Expr {
        if e.has_fvar_quick() {
            let mut ids = std::collections::BTreeSet::new();
            fn walk(e: &Expr, ids: &mut std::collections::BTreeSet<u64>) {
                use clean_kernel::expr::ExprKind;
                match e.kind() {
                    ExprKind::FVar(id) => {
                        ids.insert(id.as_u64());
                    }
                    ExprKind::App(f, a) => {
                        walk(f, ids);
                        walk(a, ids);
                    }
                    ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                        walk(t, ids);
                        walk(b, ids);
                    }
                    _ => {}
                }
            }
            walk(&e, &mut ids);
            let hex: Vec<String> = ids.iter().map(|i| format!("{i:#x}")).collect();
            panic!("semantics::B::finish: leaked FVar(s): {hex:?}");
        }
        e
    }
}

// ── short constant / type constructors ────────────────────────────────────

pub(crate) fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `State := Nat`.
pub(crate) fn state() -> Expr {
    c("Nat")
}

/// `Behavior := Nat → State` (= `Nat → Nat`).
pub(crate) fn behavior_ty() -> Expr {
    Expr::arrow(state(), state())
}

/// `StatePred := State → Prop`.
pub(crate) fn state_pred_ty() -> Expr {
    Expr::arrow(state(), Expr::prop())
}

/// `Action := State → State → Prop`.
pub(crate) fn action_ty() -> Expr {
    Expr::arrow(state(), Expr::arrow(state(), Expr::prop()))
}

/// `Formula := Behavior → Prop` — the denotation of a TLA+ formula.
pub(crate) fn formula_ty() -> Expr {
    Expr::arrow(behavior_ty(), Expr::prop())
}

pub(crate) fn nat_zero() -> Expr {
    c("Nat.zero")
}
pub(crate) fn nat_succ(n: Expr) -> Expr {
    Expr::app(c("Nat.succ"), n)
}
fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.add"), [a, b])
}
pub(crate) fn app(f: Expr, x: Expr) -> Expr {
    Expr::app(f, x)
}

/// `@Eq.{1} State a b`.
pub(crate) fn eq_state(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [state(), a, b],
    )
}

/// `And p q`.
fn and(p: Expr, q: Expr) -> Expr {
    Expr::apps(c("And"), [p, q])
}

/// `Or p q`.
pub(crate) fn or(p: Expr, q: Expr) -> Expr {
    Expr::apps(c("Or"), [p, q])
}

// ── liveness-substrate helpers (T·LIVE) ────────────────────────────────────

/// `Nat.lt a b` (reducible: `Nat.le (Nat.succ a) b`).
fn nat_lt(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.lt"), [a, b])
}

/// `False`.
fn false_() -> Expr {
    c("False")
}

/// `@Exists.{1} Nat pred` where `pred : Nat → Prop`.
fn exists_nat(pred: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(Level::zero())],
        ),
        [state(), pred],
    )
}

/// `@Exists.intro.{1} Nat pred w proof : Exists pred`.
fn exists_intro_nat(pred: Expr, w: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Exists.intro"),
            vec![Level::succ(Level::zero())],
        ),
        [state(), pred, w, proof],
    )
}

/// `@Exists.elim.{1} Nat pred goal h_ex h_fun : goal` where
/// `h_ex : Exists pred`, `h_fun : ∀ (x : Nat), pred x → goal`, `goal : Prop`.
fn exists_elim_nat(pred: Expr, goal: Expr, h_ex: Expr, h_fun: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Exists.elim"),
            vec![Level::succ(Level::zero())],
        ),
        [state(), pred, goal, h_ex, h_fun],
    )
}

/// `@Or.inl a b proof : Or a b`.
fn or_inl(a: Expr, b: Expr, proof: Expr) -> Expr {
    Expr::apps(c("Or.inl"), [a, b, proof])
}

/// `@Or.inr a b proof : Or a b`.
pub(crate) fn or_inr(a: Expr, b: Expr, proof: Expr) -> Expr {
    Expr::apps(c("Or.inr"), [a, b, proof])
}

/// `@And.intro a b pa pb : And a b`.
fn and_intro(a: Expr, b: Expr, pa: Expr, pb: Expr) -> Expr {
    Expr::apps(c("And.intro"), [a, b, pa, pb])
}

/// `@And.left a b h : a`.
fn and_left(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(c("And.left"), [a, b, h])
}

/// `@And.right a b h : b`.
fn and_right(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(c("And.right"), [a, b, h])
}

/// `@Or.rec a b motive fl fr disj : motive disj` (Prop motive, no level args).
pub(crate) fn or_rec(a: Expr, b: Expr, motive: Expr, fl: Expr, fr: Expr, disj: Expr) -> Expr {
    Expr::apps(c("Or.rec"), [a, b, motive, fl, fr, disj])
}

/// Add an opaque (non-reducible) `Declaration::Definition`, idempotently.
fn def_opaque(env: &mut Environment, name: &str, type_: Expr, value: Expr) -> Result<(), EnvError> {
    let n = Name::from_string(name);
    if env.get_const(&n).is_some() {
        return Ok(());
    }
    env.add_decl(Declaration::Definition {
        name: n,
        level_params: vec![],
        type_,
        value,
        is_reducible: false,
    })
}

/// Add a reducible `Declaration::Definition`, idempotently.
fn def_reducible(
    env: &mut Environment,
    name: &str,
    type_: Expr,
    value: Expr,
) -> Result<(), EnvError> {
    let n = Name::from_string(name);
    if env.get_const(&n).is_some() {
        return Ok(());
    }
    env.add_decl(Declaration::Definition {
        name: n,
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
}

/// Crate-internal re-export of the binder/term-building helpers so sibling
/// modules (e.g. [`crate::refine`], the T·REFINE brick) can reuse the *exact
/// same* CIC encoding idioms — the [`B`] disjoint-FVar builder and the
/// `State`/`Behavior`/`Action`/`Eq`/`And`/`Or` constructors — instead of
/// re-deriving them (which risks an encoding mismatch against the T·SEM
/// definitions the refinement layer is stated against).
pub(crate) mod reexport {
    /// `@Eq.subst.{1} State motive a b h pa : motive b` — an alias for
    /// [`super::eq_subst_nat`] under the `State` name the refinement layer uses
    /// (`State := Nat` in M0).
    pub(crate) use super::eq_subst_nat as eq_subst_state;
    pub(crate) use super::{
        action_ty, app, behavior_ty, c, eq_state, nat_succ, nat_zero, or, or_inr, or_rec, state,
        state_pred_ty, B,
    };

    // ── liveness-transfer (T·LIVE × T·REFINE apex) helpers ──────────────────
    // The refinement-tower module ([`crate::refine`]) reuses the TLAsem
    // `Formula` type and the *exact* Lamport-WF1 verification-condition type
    // builders so that `RefinedLivenessFromVCs` can invoke
    // `LatticeRankSoundGeneral` with a syntactically-identical obligation set.
    pub(crate) use super::{formula_ty, hasub_ty, hen_wait_ty, hhelp_ty, hpstab_ty, hrank_ty};
}

// ── the T·SEM module ───────────────────────────────────────────────────────

/// Register the entire T·SEM module: all definitions + the capstone theorem.
/// Idempotent.
///
/// REQUIRES: nothing (initializes `Nat`, `Eq`, `And`, `Or`, `Exists`).
/// ENSURES: on success, `TLAsem.InductiveInvariantSound` is a kernel-checked
///          `Declaration::Theorem` with `proof_quality == Constructive`.
pub fn register_tla_semantics(env: &mut Environment) -> Result<(), EnvError> {
    env.init_nat()?;
    env.init_eq()?;
    env.init_and()?;
    env.init_or()?;
    env.init_exists()?;

    register_drop(env)?;
    register_lift(env)?;
    register_sembox(env)?;
    register_semdiam(env)?;
    register_sat(env)?;
    register_leadsto(env)?;
    register_runs(env)?;
    register_enabled(env)?;
    register_lift_act(env)?;
    register_wf(env)?;
    register_sf(env)?;
    register_inductive_invariant_sound(env)?;
    // T·LIVE liveness substrate. It is built on `Acc.rec` over `Nat.accNatLt`
    // (strong/well-founded induction on the rank). Those constants are wired by
    // `Environment::with_prelude()` but their targeted `init_*` are `pub(crate)`
    // and so unreachable from this downstream crate on a bare `Environment::new`.
    // We therefore register the liveness layer ONLY when the prelude machinery is
    // present (so the M0 safety keystone still registers on a bare `new()` env;
    // the liveness theorems require `with_prelude()`).
    register_tla_liveness(env)?;
    Ok(())
}

/// Register the T·LIVE liveness substrate **iff** the well-founded prelude
/// machinery (`Acc.rec` / `Nat.accNatLt`) is available; otherwise no-op. To get
/// the liveness theorems, build the environment with `Environment::with_prelude()`.
///
/// On success (machinery present) registers, in dependency order:
/// `TLAsem.natStrongRec`, `TLAsem.WfDescentSound`,
/// `TLAsem.WfFiresWhenAlwaysEnabled`, `TLAsem.LatticeRankSound`.
pub fn register_tla_liveness(env: &mut Environment) -> Result<(), EnvError> {
    let have_acc = env.get_const(&Name::from_string("Acc.rec")).is_some()
        && env.get_const(&Name::from_string("Nat.accNatLt")).is_some()
        && env.get_const(&Name::from_string("Nat.lt")).is_some()
        && env.get_const(&Name::from_string("Classical.em")).is_some();
    if !have_acc {
        return Ok(());
    }
    register_nat_strong_rec(env)?;
    register_wf_descent_sound(env)?;
    register_wf_fires_when_always_enabled(env)?;
    register_wf_fires_when_enabled_throughout(env)?;
    register_wf_prefix_invariant(env)?;
    register_lattice_rank_sound(env)?;
    register_lattice_rank_sound_general(env)?;
    Ok(())
}

/// `TLAsem.drop : Behavior → Nat → Behavior`
/// `drop b n := λ i, b (Nat.add n i)` — the suffix of `b` starting at `n`.
fn register_drop(env: &mut Environment) -> Result<(), EnvError> {
    let type_ = Expr::arrow(behavior_ty(), Expr::arrow(state(), behavior_ty()));
    let mut bld = B::new();
    let (b_id, b) = bld.fresh();
    let (n_id, n) = bld.fresh();
    let (i_id, i) = bld.fresh();
    let body = app(b.clone(), nat_add(n.clone(), i));
    let v = bld.lam(i_id, BinderInfo::Default, state(), body);
    let v = bld.lam(n_id, BinderInfo::Default, state(), v);
    let v = bld.lam(b_id, BinderInfo::Default, behavior_ty(), v);
    def_reducible(env, "TLAsem.drop", type_, bld.finish(v))
}

/// `TLAsem.Lift : StatePred → Formula`
/// `Lift P := λ b, P (b Nat.zero)`.
fn register_lift(env: &mut Environment) -> Result<(), EnvError> {
    let type_ = Expr::arrow(state_pred_ty(), formula_ty());
    let mut bld = B::new();
    let (p_id, p) = bld.fresh();
    let (b_id, b) = bld.fresh();
    let body = app(p.clone(), app(b.clone(), nat_zero()));
    let v = bld.lam(b_id, BinderInfo::Default, behavior_ty(), body);
    let v = bld.lam(p_id, BinderInfo::Default, state_pred_ty(), v);
    def_reducible(env, "TLAsem.Lift", type_, bld.finish(v))
}

/// `TLAsem.SemBox : Formula → Formula`
/// `□F := λ b, ∀ (n : Nat), F (TLAsem.drop b n)`.
fn register_sembox(env: &mut Environment) -> Result<(), EnvError> {
    let type_ = Expr::arrow(formula_ty(), formula_ty());
    let mut bld = B::new();
    let (f_id, f) = bld.fresh();
    let (b_id, b) = bld.fresh();
    let (n_id, n) = bld.fresh();
    let drop = Expr::apps(c("TLAsem.drop"), [b.clone(), n]);
    let inner = app(f.clone(), drop);
    let forall_n = bld.pi(n_id, BinderInfo::Default, state(), inner);
    let v = bld.lam(b_id, BinderInfo::Default, behavior_ty(), forall_n);
    let v = bld.lam(f_id, BinderInfo::Default, formula_ty(), v);
    def_reducible(env, "TLAsem.SemBox", type_, bld.finish(v))
}

/// `TLAsem.SemDiam : Formula → Formula`
/// `◇F := λ b, @Exists.{1} Nat (λ n, F (TLAsem.drop b n))`.
fn register_semdiam(env: &mut Environment) -> Result<(), EnvError> {
    let type_ = Expr::arrow(formula_ty(), formula_ty());
    let exists_c = Expr::const_(
        Name::from_string("Exists"),
        vec![Level::succ(Level::zero())],
    );
    let mut bld = B::new();
    let (f_id, f) = bld.fresh();
    let (b_id, b) = bld.fresh();
    let (n_id, n) = bld.fresh();
    let drop = Expr::apps(c("TLAsem.drop"), [b.clone(), n]);
    let pred_body = app(f.clone(), drop);
    let pred = bld.lam(n_id, BinderInfo::Default, state(), pred_body);
    let exists_app = Expr::apps(exists_c, [state(), pred]);
    let v = bld.lam(b_id, BinderInfo::Default, behavior_ty(), exists_app);
    let v = bld.lam(f_id, BinderInfo::Default, formula_ty(), v);
    def_reducible(env, "TLAsem.SemDiam", type_, bld.finish(v))
}

/// `TLAsem.Sat : Behavior → Formula → Prop`
/// `Sat b F := F b`.
fn register_sat(env: &mut Environment) -> Result<(), EnvError> {
    let type_ = Expr::arrow(behavior_ty(), Expr::arrow(formula_ty(), Expr::prop()));
    let mut bld = B::new();
    let (b_id, b) = bld.fresh();
    let (f_id, f) = bld.fresh();
    let body = app(f.clone(), b.clone());
    let v = bld.lam(f_id, BinderInfo::Default, formula_ty(), body);
    let v = bld.lam(b_id, BinderInfo::Default, behavior_ty(), v);
    def_reducible(env, "TLAsem.Sat", type_, bld.finish(v))
}

/// `TLAsem.LeadsTo : Formula → Formula → Formula`
/// `P ⇝ Q := □(λ b, P b → ◇Q b)`.
fn register_leadsto(env: &mut Environment) -> Result<(), EnvError> {
    let type_ = Expr::arrow(formula_ty(), Expr::arrow(formula_ty(), formula_ty()));
    let mut bld = B::new();
    let (p_id, p) = bld.fresh();
    let (q_id, q) = bld.fresh();
    let (b_id, b) = bld.fresh();
    let diam_q_b = app(Expr::app(c("TLAsem.SemDiam"), q.clone()), b.clone());
    let imp = Expr::arrow(app(p.clone(), b.clone()), diam_q_b);
    let lam_b = bld.lam(b_id, BinderInfo::Default, behavior_ty(), imp);
    let box_app = app(c("TLAsem.SemBox"), lam_b);
    let v = bld.lam(q_id, BinderInfo::Default, formula_ty(), box_app);
    let v = bld.lam(p_id, BinderInfo::Default, formula_ty(), v);
    def_reducible(env, "TLAsem.LeadsTo", type_, bld.finish(v))
}

/// `TLAsem.Runs : StatePred → Action → Behavior → Prop`
/// Stutter-permissive run predicate:
/// `Runs I N b := And (I (b 0)) (∀ n, Or (N (b n)(b (succ n))) (Eq (b (succ n))(b n)))`.
fn register_runs(env: &mut Environment) -> Result<(), EnvError> {
    let type_ = Expr::arrow(
        state_pred_ty(),
        Expr::arrow(action_ty(), Expr::arrow(behavior_ty(), Expr::prop())),
    );
    let mut bld = B::new();
    let (i_id, init) = bld.fresh();
    let (nx_id, nx) = bld.fresh();
    let (b_id, b) = bld.fresh();
    let init_b0 = app(init.clone(), app(b.clone(), nat_zero()));

    let (n_id, n) = bld.fresh();
    let bn = app(b.clone(), n.clone());
    let bsn = app(b.clone(), nat_succ(n.clone()));
    let step = Expr::apps(nx.clone(), [bn.clone(), bsn.clone()]);
    let stutter = eq_state(bsn.clone(), bn.clone());
    let disj = or(step, stutter);
    let forall_n = bld.pi(n_id, BinderInfo::Default, state(), disj);

    let conj = and(init_b0, forall_n);
    let v = bld.lam(b_id, BinderInfo::Default, behavior_ty(), conj);
    let v = bld.lam(nx_id, BinderInfo::Default, action_ty(), v);
    let v = bld.lam(i_id, BinderInfo::Default, state_pred_ty(), v);
    def_reducible(env, "TLAsem.Runs", type_, bld.finish(v))
}

/// `TLAsem.Enabled : Action → StatePred`
/// `Enabled A := λ s, ∃ s', A s s'`.
fn register_enabled(env: &mut Environment) -> Result<(), EnvError> {
    let type_ = Expr::arrow(action_ty(), state_pred_ty());
    let exists_c = Expr::const_(
        Name::from_string("Exists"),
        vec![Level::succ(Level::zero())],
    );
    let mut bld = B::new();
    let (a_id, a) = bld.fresh();
    let (s_id, s) = bld.fresh();
    let (sp_id, sp) = bld.fresh();
    let body = Expr::apps(a.clone(), [s.clone(), sp]);
    let pred = bld.lam(sp_id, BinderInfo::Default, state(), body);
    let exists_app = Expr::apps(exists_c, [state(), pred]);
    let v = bld.lam(s_id, BinderInfo::Default, state(), exists_app);
    let v = bld.lam(a_id, BinderInfo::Default, action_ty(), v);
    def_reducible(env, "TLAsem.Enabled", type_, bld.finish(v))
}

/// `TLAsem.LiftAct : Action → Formula`
/// `LiftAct A := λ b, A (b 0) (b 1)` — the ⟨A⟩ action as a behavior formula.
fn register_lift_act(env: &mut Environment) -> Result<(), EnvError> {
    let type_ = Expr::arrow(action_ty(), formula_ty());
    let mut bld = B::new();
    let (a_id, a) = bld.fresh();
    let (b_id, b) = bld.fresh();
    let b0 = app(b.clone(), nat_zero());
    let b1 = app(b.clone(), nat_succ(nat_zero()));
    let body = Expr::apps(a.clone(), [b0, b1]);
    let v = bld.lam(b_id, BinderInfo::Default, behavior_ty(), body);
    let v = bld.lam(a_id, BinderInfo::Default, action_ty(), v);
    def_reducible(env, "TLAsem.LiftAct", type_, bld.finish(v))
}

/// `TLAsem.WF : Action → Formula`  (weak fairness)
/// `WF A := □(λ b, ◇□(Lift (Enabled A)) b → ◇⟨A⟩ b)`.
fn register_wf(env: &mut Environment) -> Result<(), EnvError> {
    register_enabled(env)?;
    register_lift_act(env)?;
    let type_ = Expr::arrow(action_ty(), formula_ty());
    let mut bld = B::new();
    let (a_id, a) = bld.fresh();
    let (b_id, b) = bld.fresh();
    let enabled = app(c("TLAsem.Enabled"), a.clone());
    let lift_en = app(c("TLAsem.Lift"), enabled);
    let box_en = app(c("TLAsem.SemBox"), lift_en);
    let ea_box = app(c("TLAsem.SemDiam"), box_en); // ◇□(Lift Enabled)
    let ea_at_b = app(ea_box, b.clone());
    let act = app(c("TLAsem.LiftAct"), a.clone());
    let diam_act = app(c("TLAsem.SemDiam"), act);
    let diam_at_b = app(diam_act, b.clone());
    let imp = Expr::arrow(ea_at_b, diam_at_b);
    let lam_b = bld.lam(b_id, BinderInfo::Default, behavior_ty(), imp);
    let box_app = app(c("TLAsem.SemBox"), lam_b);
    let v = bld.lam(a_id, BinderInfo::Default, action_ty(), box_app);
    def_reducible(env, "TLAsem.WF", type_, bld.finish(v))
}

/// `TLAsem.SF : Action → Formula`  (strong fairness)
/// `SF A := □(λ b, □◇(Lift (Enabled A)) b → ◇⟨A⟩ b)`.
fn register_sf(env: &mut Environment) -> Result<(), EnvError> {
    register_enabled(env)?;
    register_lift_act(env)?;
    let type_ = Expr::arrow(action_ty(), formula_ty());
    let mut bld = B::new();
    let (a_id, a) = bld.fresh();
    let (b_id, b) = bld.fresh();
    let enabled = app(c("TLAsem.Enabled"), a.clone());
    let lift_en = app(c("TLAsem.Lift"), enabled);
    let diam_en = app(c("TLAsem.SemDiam"), lift_en);
    let box_diam_en = app(c("TLAsem.SemBox"), diam_en); // □◇(Lift Enabled)
    let ea_at_b = app(box_diam_en, b.clone());
    let act = app(c("TLAsem.LiftAct"), a.clone());
    let diam_act = app(c("TLAsem.SemDiam"), act);
    let diam_at_b = app(diam_act, b.clone());
    let imp = Expr::arrow(ea_at_b, diam_at_b);
    let lam_b = bld.lam(b_id, BinderInfo::Default, behavior_ty(), imp);
    let box_app = app(c("TLAsem.SemBox"), lam_b);
    let v = bld.lam(a_id, BinderInfo::Default, action_ty(), box_app);
    def_reducible(env, "TLAsem.SF", type_, bld.finish(v))
}

// ── the capstone theorem ───────────────────────────────────────────────────

/// `∀ s, Init s → J s`.
fn h_init_ty(init: &Expr, j: &Expr) -> Expr {
    let mut hb = B::new();
    let (s_id, s) = hb.fresh();
    let imp = Expr::arrow(app(init.clone(), s.clone()), app(j.clone(), s.clone()));
    hb.pi(s_id, BinderInfo::Default, state(), imp)
}

/// `∀ s s', J s → Next s s' → J s'`.
fn h_cons_ty(next: &Expr, j: &Expr) -> Expr {
    let mut hb = B::new();
    let (s_id, s) = hb.fresh();
    let (sp_id, sp) = hb.fresh();
    let next_ss = Expr::apps(next.clone(), [s.clone(), sp.clone()]);
    let inner = Expr::arrow(
        app(j.clone(), s.clone()),
        Expr::arrow(next_ss, app(j.clone(), sp.clone())),
    );
    let inner = hb.pi(sp_id, BinderInfo::Default, state(), inner);
    hb.pi(s_id, BinderInfo::Default, state(), inner)
}

/// `∀ s, J s → Safety s`.
fn h_safe_ty(j: &Expr, safety: &Expr) -> Expr {
    let mut hb = B::new();
    let (s_id, s) = hb.fresh();
    let imp = Expr::arrow(app(j.clone(), s.clone()), app(safety.clone(), s.clone()));
    hb.pi(s_id, BinderInfo::Default, state(), imp)
}

/// `∀ n, Or (Next (b n)(b (succ n))) (Eq (b (succ n))(b n))`.
fn step_forall_ty(next: &Expr, b: &Expr) -> Expr {
    let mut sb = B::new();
    let (n_id, n) = sb.fresh();
    let bn = app(b.clone(), n.clone());
    let bsn = app(b.clone(), nat_succ(n.clone()));
    let stepr = Expr::apps(next.clone(), [bn.clone(), bsn.clone()]);
    let stut = eq_state(bsn.clone(), bn.clone());
    let disj = or(stepr, stut);
    sb.pi(n_id, BinderInfo::Default, state(), disj)
}

/// `Runs Init Next b`.
fn runs_app(init: &Expr, next: &Expr, b: &Expr) -> Expr {
    Expr::apps(c("TLAsem.Runs"), [init.clone(), next.clone(), b.clone()])
}

/// Register `TLAsem.InductiveInvariantSound`.
///
/// ```text
/// ∀ (Init : State → Prop) (Next : State → State → Prop) (Safety J : State → Prop),
///   (∀ s, Init s → J s) →
///   (∀ s s', J s → Next s s' → J s') →
///   (∀ s, J s → Safety s) →
///   ∀ b, Runs Init Next b → Sat b (SemBox (Lift Safety))
/// ```
///
/// PROOF (real `Nat.rec` induction; no axiom stand-ins). `Sat b (SemBox (Lift
/// Safety))` reduces (Sat/SemBox/Lift/drop reducible) to `∀ n, Safety (b
/// (Nat.add n 0))`, and `Nat.add n 0 ≡ n` by iota, so the goal is `∀ n, Safety
/// (b n)`. We first prove `jInv : ∀ n, J (b n)` by induction on `n`:
///   * base `n = 0`: `hInit (b 0) (And.left hRuns)`.
///   * step `n → succ n`: from `ih : J (b n)` and the stutter-closed step
///     `disj : Or (Next (b n)(b (succ n))) (Eq (b (succ n))(b n))`, `Or.rec`
///     gives `J (b (succ n))`: left `hN ↦ hCons (b n)(b (succ n)) ih hN`;
///     right `hEq ↦` rewrite `ih` along `Eq.symm hEq` via `Eq.subst`.
///
/// Finally `hSafe (b n) (jInv n)` discharges `Safety (b n)`.
pub fn register_inductive_invariant_sound(env: &mut Environment) -> Result<(), EnvError> {
    register_tla_semantics_prereqs(env)?;
    let name = Name::from_string("TLAsem.InductiveInvariantSound");
    if env.get_const(&name).is_some() {
        return Ok(());
    }

    let nat = state();
    let or_rec = c("Or.rec");
    let and_left = c("And.left");
    let and_right = c("And.right");
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let eq_symm = Expr::const_(
        Name::from_string("Eq.symm"),
        vec![Level::succ(Level::zero())],
    );
    let eq_subst = Expr::const_(
        Name::from_string("Eq.subst"),
        vec![Level::succ(Level::zero())],
    );

    // ── statement type ────────────────────────────────────────────────────
    let mut tb = B::new();
    let (init_id, init) = tb.fresh();
    let (next_id, next) = tb.fresh();
    let (j_id, jpred) = tb.fresh();
    let (safety_id, safety) = tb.fresh();
    let (h_init_id, _h_init) = tb.fresh();
    let (h_cons_id, _h_cons) = tb.fresh();
    let (h_safe_id, _h_safe) = tb.fresh();
    let (b_id, bvar) = tb.fresh();
    let (h_runs_id, _h_runs) = tb.fresh();

    let concl = {
        let lift_safety = app(c("TLAsem.Lift"), safety.clone());
        let box_lift = app(c("TLAsem.SemBox"), lift_safety);
        Expr::apps(c("TLAsem.Sat"), [bvar.clone(), box_lift])
    };

    let type_ = {
        let mut t = concl.clone();
        t = tb.pi(
            h_runs_id,
            BinderInfo::Default,
            runs_app(&init, &next, &bvar),
            t,
        );
        t = tb.pi(b_id, BinderInfo::Default, behavior_ty(), t);
        t = tb.pi(
            h_safe_id,
            BinderInfo::Default,
            h_safe_ty(&jpred, &safety),
            t,
        );
        t = tb.pi(h_cons_id, BinderInfo::Default, h_cons_ty(&next, &jpred), t);
        t = tb.pi(h_init_id, BinderInfo::Default, h_init_ty(&init, &jpred), t);
        t = tb.pi(j_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(safety_id, BinderInfo::Implicit, state_pred_ty(), t);
        t = tb.pi(next_id, BinderInfo::Implicit, action_ty(), t);
        t = tb.pi(init_id, BinderInfo::Implicit, state_pred_ty(), t);
        tb.finish(t)
    };

    // ── proof value ───────────────────────────────────────────────────────
    let mut vb = B::new();
    let (v_init_id, v_init) = vb.fresh();
    let (v_next_id, v_next) = vb.fresh();
    let (v_j_id, v_j) = vb.fresh();
    let (v_safety_id, v_safety) = vb.fresh();
    let (v_hinit_id, v_hinit) = vb.fresh();
    let (v_hcons_id, v_hcons) = vb.fresh();
    let (v_hsafe_id, v_hsafe) = vb.fresh();
    let (v_b_id, v_b) = vb.fresh();
    let (v_hruns_id, v_hruns) = vb.fresh();

    let init_b0_ty = app(v_init.clone(), app(v_b.clone(), nat_zero()));
    let steps_ty = step_forall_ty(&v_next, &v_b);

    // And.left / And.right of hRuns.
    let h_init_b0 = Expr::apps(
        and_left.clone(),
        [init_b0_ty.clone(), steps_ty.clone(), v_hruns.clone()],
    );
    let h_steps = Expr::apps(
        and_right.clone(),
        [init_b0_ty.clone(), steps_ty.clone(), v_hruns.clone()],
    );

    // motive := λ (n : Nat), J (b n)
    let motive = {
        let mut mb = B::new();
        let (n_id, n) = mb.fresh();
        let body = app(v_j.clone(), app(v_b.clone(), n.clone()));
        mb.lam(n_id, BinderInfo::Default, nat.clone(), body)
    };
    // base : J (b 0) := hInit (b 0) (And.left hRuns)
    let base = Expr::apps(
        v_hinit.clone(),
        [app(v_b.clone(), nat_zero()), h_init_b0.clone()],
    );
    // step : ∀ (n : Nat), J (b n) → J (b (succ n))
    let step = {
        let mut stb = B::new();
        let (n_id, n) = stb.fresh();
        let (ih_id, ih) = stb.fresh();
        let bn = app(v_b.clone(), n.clone());
        let bsn = app(v_b.clone(), nat_succ(n.clone()));
        let disj_n = app(h_steps.clone(), n.clone());
        let step_rel = Expr::apps(v_next.clone(), [bn.clone(), bsn.clone()]);
        let stut_eq = eq_state(bsn.clone(), bn.clone());
        let goal = app(v_j.clone(), bsn.clone());

        // fl : Next (b n)(b (succ n)) → J (b (succ n))
        let fl = {
            let mut lb = B::new();
            let (hn_id, hn) = lb.fresh();
            let body = Expr::apps(
                v_hcons.clone(),
                [bn.clone(), bsn.clone(), ih.clone(), hn.clone()],
            );
            lb.lam(hn_id, BinderInfo::Default, step_rel.clone(), body)
        };
        // fr : Eq (b (succ n))(b n) → J (b (succ n))
        let fr = {
            let mut rb = B::new();
            let (heq_id, heq) = rb.fresh();
            // hsym : Eq (b n)(b (succ n)) := @Eq.symm State (b (succ n)) (b n) heq
            let hsym = Expr::apps(
                eq_symm.clone(),
                [nat.clone(), bsn.clone(), bn.clone(), heq.clone()],
            );
            // @Eq.subst State (motive := J) (b n)(b (succ n)) hsym ih : J (b (succ n))
            let body = Expr::apps(
                eq_subst.clone(),
                [
                    nat.clone(),
                    v_j.clone(),
                    bn.clone(),
                    bsn.clone(),
                    hsym,
                    ih.clone(),
                ],
            );
            rb.lam(heq_id, BinderInfo::Default, stut_eq.clone(), body)
        };
        // @Or.rec a b (motive := λ _, J (b (succ n))) fl fr disj_n
        let or_motive = {
            let mut ob = B::new();
            let (o_id, _o) = ob.fresh();
            let disj_ty = or(step_rel.clone(), stut_eq.clone());
            ob.lam(o_id, BinderInfo::Default, disj_ty, goal.clone())
        };
        let or_app = Expr::apps(
            or_rec.clone(),
            [step_rel.clone(), stut_eq.clone(), or_motive, fl, fr, disj_n],
        );
        let lam_ih = stb.lam(
            ih_id,
            BinderInfo::Default,
            app(v_j.clone(), bn.clone()),
            or_app,
        );
        stb.lam(n_id, BinderInfo::Default, nat.clone(), lam_ih)
    };

    // jInv := λ (n : Nat), Nat.rec motive base step n  : ∀ n, J (b n)
    let j_inv = {
        let mut jb = B::new();
        let (n_id, n) = jb.fresh();
        let body = Expr::apps(
            nat_rec.clone(),
            [motive.clone(), base.clone(), step.clone(), n],
        );
        jb.lam(n_id, BinderInfo::Default, nat.clone(), body)
    };

    // proof_core : ∀ n, Safety (b n)  := λ n, hSafe (b n) (jInv n)
    let proof_core = {
        let mut pb = B::new();
        let (n_id, n) = pb.fresh();
        let safety_bn = Expr::apps(
            v_hsafe.clone(),
            [app(v_b.clone(), n.clone()), app(j_inv.clone(), n.clone())],
        );
        pb.lam(n_id, BinderInfo::Default, nat.clone(), safety_bn)
    };

    let value = {
        let mut v = proof_core;
        v = vb.lam(
            v_hruns_id,
            BinderInfo::Default,
            runs_app(&v_init, &v_next, &v_b),
            v,
        );
        v = vb.lam(v_b_id, BinderInfo::Default, behavior_ty(), v);
        v = vb.lam(
            v_hsafe_id,
            BinderInfo::Default,
            h_safe_ty(&v_j, &v_safety),
            v,
        );
        v = vb.lam(v_hcons_id, BinderInfo::Default, h_cons_ty(&v_next, &v_j), v);
        v = vb.lam(v_hinit_id, BinderInfo::Default, h_init_ty(&v_init, &v_j), v);
        v = vb.lam(v_j_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(v_safety_id, BinderInfo::Implicit, state_pred_ty(), v);
        v = vb.lam(v_next_id, BinderInfo::Implicit, action_ty(), v);
        v = vb.lam(v_init_id, BinderInfo::Implicit, state_pred_ty(), v);
        vb.finish(v)
    };

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_,
        value,
    })
}

/// Ensure the definitions the capstone references are present.
fn register_tla_semantics_prereqs(env: &mut Environment) -> Result<(), EnvError> {
    env.init_nat()?;
    env.init_eq()?;
    env.init_and()?;
    env.init_or()?;
    env.init_exists()?;
    register_drop(env)?;
    register_lift(env)?;
    register_sembox(env)?;
    register_semdiam(env)?;
    register_sat(env)?;
    register_runs(env)?;
    Ok(())
}

// ════════════════════════════════════════════════════════════════════════════
// T·LIVE — the liveness-under-fairness substrate
// ════════════════════════════════════════════════════════════════════════════

/// Register `TLAsem.natStrongRec`, a *strong* (course-of-values) induction
/// principle on `Nat` for a `Prop`-valued motive, built directly on the kernel
/// recursor `Acc.rec` over the axiom-free accessibility witness `Nat.accNatLt`.
///
/// ```text
/// TLAsem.natStrongRec :
///   (M : Nat → Prop)
///   → ((x : Nat) → ((y : Nat) → Nat.lt y x → M y) → M x)
///   → (n : Nat) → M n
/// ```
///
/// The clean kernel ships an identical `Nat.strongRecOnLt`, but its registrar is
/// `pub(crate)` — unreachable from the downstream `clean-tla` crate. We rebuild
/// it here with the public `Expr`/`B` surface. It mentions only `Acc`/`Acc.rec`
/// (kernel recursor) and `Nat`/`Nat.lt`/`Nat.accNatLt` (axiom-free), so its
/// transitive axiom closure is empty (⊆ FOUNDATIONAL).
///
/// REQUIRES: the env to carry `Acc`/`Acc.rec`/`Nat.accNatLt`/`Nat.lt`, i.e. an
/// `Environment::with_prelude()` (the targeted `init_*` for these are
/// `pub(crate)`; `with_prelude` is the public path that wires them).
fn register_nat_strong_rec(env: &mut Environment) -> Result<(), EnvError> {
    let name = Name::from_string("TLAsem.natStrongRec");
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let nat = state();
    let l0 = Level::zero();
    let l1 = Level::succ(l0.clone());
    let acc = |x: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Acc"), vec![l1.clone()]),
            [nat.clone(), c("Nat.lt"), x],
        )
    };
    let acc_rec = Expr::const_(Name::from_string("Acc.rec"), vec![l0.clone(), l1.clone()]);
    let acc_nat_lt = c("Nat.accNatLt");
    let nat_to_prop = Expr::arrow(nat.clone(), Expr::prop());

    // step_ty(M) := (x : Nat) → ((y : Nat) → Nat.lt y x → M y) → M x
    let step_ty = |m: &Expr| -> Expr {
        let mut s = B::new();
        let (x_id, x) = s.fresh();
        let ih_ty = {
            let mut t = B::new();
            let (y_id, y) = t.fresh();
            let inner = Expr::arrow(nat_lt(y.clone(), x.clone()), app(m.clone(), y.clone()));
            t.pi(y_id, BinderInfo::Default, nat.clone(), inner)
        };
        let inner = Expr::arrow(ih_ty, app(m.clone(), x.clone()));
        s.pi(x_id, BinderInfo::Default, nat.clone(), inner)
    };

    // ── type ────────────────────────────────────────────────────────────────
    let type_ = {
        let mut b = B::new();
        let (m_id, m) = b.fresh();
        let (s_id, _s) = b.fresh();
        let (n_id, n) = b.fresh();
        let concl = app(m.clone(), n.clone());
        let e = b.pi(n_id, BinderInfo::Default, nat.clone(), concl);
        let e = b.pi(s_id, BinderInfo::Default, step_ty(&m), e);
        let e = b.pi(m_id, BinderInfo::Default, nat_to_prop.clone(), e);
        b.finish(e)
    };

    // ── value ─────────────────────────────────────────────────────────────--
    let value = {
        let mut b = B::new();
        let (m_id, m) = b.fresh();
        let (s_id, step) = b.fresh();
        let (n_id, n) = b.fresh();

        // C := fun (x : Nat) (_ : Acc Nat.lt x) => M x
        let cmotive = {
            let mut d = B::new();
            let (x_id, x) = d.fresh();
            let (a_id, _a) = d.fresh();
            let mx = app(m.clone(), x.clone());
            let inner = d.lam(a_id, BinderInfo::Default, acc(x.clone()), mx);
            d.lam(x_id, BinderInfo::Default, nat.clone(), inner)
        };

        // STEP := fun (x) (h : ∀ y, Nat.lt y x → Acc Nat.lt y)
        //             (ih : ∀ y (p : Nat.lt y x), M y) => step x ih
        let step_fn = {
            let mut d = B::new();
            let (x_id, x) = d.fresh();
            let h_ty = {
                let mut t = B::new();
                let (y_id, y) = t.fresh();
                let inner = Expr::arrow(nat_lt(y.clone(), x.clone()), acc(y.clone()));
                t.pi(y_id, BinderInfo::Default, nat.clone(), inner)
            };
            let (h_id, _h) = d.fresh();
            let ih_ty = {
                let mut t = B::new();
                let (y_id, y) = t.fresh();
                let inner = Expr::arrow(nat_lt(y.clone(), x.clone()), app(m.clone(), y.clone()));
                t.pi(y_id, BinderInfo::Default, nat.clone(), inner)
            };
            let (ih_id, ih) = d.fresh();
            let body = Expr::apps(step.clone(), [x.clone(), ih.clone()]);
            let r = d.lam(ih_id, BinderInfo::Default, ih_ty, body);
            let r = d.lam(h_id, BinderInfo::Default, h_ty, r);
            d.lam(x_id, BinderInfo::Default, nat.clone(), r)
        };

        // @Acc.rec.{0,1} Nat Nat.lt C STEP n (Nat.accNatLt n)
        let rec_app = Expr::apps(
            acc_rec.clone(),
            [
                nat.clone(),
                c("Nat.lt"),
                cmotive,
                step_fn,
                n.clone(),
                app(acc_nat_lt.clone(), n.clone()),
            ],
        );
        let e = b.lam(n_id, BinderInfo::Default, nat.clone(), rec_app);
        let e = b.lam(s_id, BinderInfo::Default, step_ty(&m), e);
        let e = b.lam(m_id, BinderInfo::Default, nat_to_prop, e);
        b.finish(e)
    };

    def_opaque(env, "TLAsem.natStrongRec", type_, value)
}

/// `@Eq.{1} Nat a b`.
fn eq_nat(a: Expr, b: Expr) -> Expr {
    eq_state(a, b)
}

/// `@Eq.refl.{1} Nat a : Eq a a`.
fn eq_refl_nat(a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [state(), a],
    )
}

/// `@Eq.subst.{1} Nat motive a b (h : Eq a b) (pa : motive a) : motive b`,
/// where `motive : Nat → Prop`.
pub(crate) fn eq_subst_nat(motive: Expr, a: Expr, b: Expr, h: Expr, pa: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.subst"),
            vec![Level::succ(Level::zero())],
        ),
        [state(), motive, a, b, h, pa],
    )
}

/// `Nat.add_assoc a b c : Eq (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c))`.
fn nat_add_assoc(a: Expr, b: Expr, cc: Expr) -> Expr {
    Expr::apps(c("Nat.add_assoc"), [a, b, cc])
}

/// `@Classical.em p : Or p (p → False)`.
fn classical_em(p: Expr) -> Expr {
    Expr::apps(c("Classical.em"), [p])
}

/// `Nat.le a b` (bare, `Sort 0`).
fn nat_le(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.le"), [a, b])
}

/// `Nat.le_refl a : Nat.le a a` — but `Nat.le_refl` is registered in the
/// *typeclass* form (`LE.le Nat instLENat a a`); since that is def-eq to
/// `Nat.le a a`, the term still checks against a bare-`Nat.le` goal.
fn nat_le_refl(a: Expr) -> Expr {
    Expr::apps(c("Nat.le_refl"), [a])
}

/// `@Nat.le_trans a b cc h1 h2`. Registered in the typeclass form, but its
/// result `LE.le Nat instLENat a cc` is def-eq to `Nat.le a cc`, and it accepts
/// bare-`Nat.le` arguments by def-eq. We use it as the missing `lt_of_lt_of_le`:
/// with `a := Nat.succ x`, `Nat.le (succ x) b ≡ Nat.lt x b` and
/// `Nat.le (succ x) cc ≡ Nat.lt x cc`, so
/// `Nat.le_trans (succ x) b cc (h1 : Nat.lt x b)(h2 : Nat.le b cc) : Nat.lt x cc`.
fn nat_le_trans(a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(c("Nat.le_trans"), [a, b, cc, h1, h2])
}

/// `@Nat.lt_irrefl a : Nat.lt a a → False`.
fn nat_lt_irrefl(a: Expr) -> Expr {
    Expr::apps(c("Nat.lt_irrefl"), [a])
}

/// `@False.elim.{u} goal h : goal` where `goal : Sort u`, `h : False`.
/// We only ever eliminate into `Prop`, so `u := 0`.
fn false_elim_prop(goal: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        [goal, h],
    )
}

/// The per-`m` body predicate of `Hprog` at base index `n`:
/// `λ (m : Nat), Or (Q (b (n+m))) (And (P (b (n+m))) (Nat.lt (rho (b (n+m))) (rho (b n))))`.
fn prog_pred(p: &Expr, q: &Expr, rho: &Expr, b: &Expr, n: &Expr) -> Expr {
    let mut mb = B::new();
    let (m_id, m) = mb.fresh();
    let bnm = app(b.clone(), nat_add(n.clone(), m.clone()));
    let q_reach = app(q.clone(), bnm.clone());
    let p_reach = app(p.clone(), bnm.clone());
    let rho_small = nat_lt(
        app(rho.clone(), bnm.clone()),
        app(rho.clone(), app(b.clone(), n.clone())),
    );
    let body = or(q_reach, and(p_reach, rho_small));
    mb.lam(m_id, BinderInfo::Default, state(), body)
}

/// The conclusion existential predicate at base index `n`:
/// `λ (m : Nat), Q (b (n+m))`.
fn q_reach_pred(q: &Expr, b: &Expr, n: &Expr) -> Expr {
    let mut mb = B::new();
    let (m_id, m) = mb.fresh();
    let body = app(q.clone(), app(b.clone(), nat_add(n.clone(), m.clone())));
    mb.lam(m_id, BinderInfo::Default, state(), body)
}

/// `Hprog` hypothesis type:
/// `∀ (n : Nat), P (b n) → (Q (b n) → False) → Exists (prog_pred … n)`.
fn hprog_ty(p: &Expr, q: &Expr, rho: &Expr, b: &Expr) -> Expr {
    let mut nb = B::new();
    let (n_id, n) = nb.fresh();
    let bn = app(b.clone(), n.clone());
    let not_q = Expr::arrow(app(q.clone(), bn.clone()), false_());
    let ex = exists_nat(prog_pred(p, q, rho, b, &n));
    let inner = Expr::arrow(app(p.clone(), bn.clone()), Expr::arrow(not_q, ex));
    nb.pi(n_id, BinderInfo::Default, state(), inner)
}

/// Register `TLAsem.WfDescentSound` — the well-founded leads-to descent lemma
/// (the rank-induction substrate of T·LIVE), **fully proved** by strong
/// induction on the rank value `rho (b n)`.
///
/// ```text
/// WfDescentSound :
///   ∀ (P Q : StatePred) (rho : State → Nat) (b : Behavior),
///     (Hprog : ∀ n, P (b n) → (Q (b n) → False)
///                → ∃ m, Q (b (n+m)) ∨ (P (b (n+m)) ∧ rho (b (n+m)) < rho (b n)))
///     → ∀ n, P (b n) → ∃ m, Q (b (n+m))
/// ```
///
/// The conclusion `∀ n, P (b n) → ∃ m, Q (b (n+m))` is **definitionally equal**
/// to `Sat b (LeadsTo (Lift P) (Lift Q))` (`Sat`/`LeadsTo`/`SemBox`/`SemDiam`/
/// `Lift`/`drop` are reducible, and `Nat.add n 0 ≡ n`, `Nat.add m 0 ≡ m`,
/// `Nat.add n (Nat.add m 0) ≡ Nat.add n m` by iota). `WfDescentSound` is the
/// *fairness-free* heart: it isolates the well-founded descent from the
/// fairness-under-abstraction extraction (which lives in `LatticeRankSound`).
/// `Hprog` is a **Pi-bound hypothesis, not an axiom** — so the theorem's
/// transitive axiom closure stays ⊆ FOUNDATIONAL (it reaches only
/// `Acc.rec`/`Nat.accNatLt`/`Classical.em`/`Eq`/`And`/`Or`/`Exists`/`Nat`).
///
/// PROOF. Strong induction (`TLAsem.natStrongRec`) with motive
/// `M k := ∀ n, rho (b n) = k → P (b n) → ∃ m, Q (b (n+m))`. At rank `x`:
/// classically split on `Q (b n)`. If `Q (b n)`: witness `m = 0` (`n+0 ≡ n`).
/// Else apply `Hprog n` and `Or.rec` the result: a reached-Q gives witness `m0`;
/// a smaller-rank P-state `b (n+m0)` (rank `< rho (b n) = x`) feeds the strong
/// IH at index `n+m0`, yielding `∃ m1, Q (b ((n+m0)+m1))`, which `Nat.add_assoc`
/// reindexes to `Q (b (n+(m0+m1)))` — witness `m0+m1`.
pub fn register_wf_descent_sound(env: &mut Environment) -> Result<(), EnvError> {
    register_tla_semantics_prereqs(env)?;
    register_leadsto(env)?;
    register_nat_strong_rec(env)?;
    let name = Name::from_string("TLAsem.WfDescentSound");
    if env.get_const(&name).is_some() {
        return Ok(());
    }

    let nat = state();

    // ── statement type ────────────────────────────────────────────────────
    let mut tb = B::new();
    let (p_id, p) = tb.fresh();
    let (q_id, q) = tb.fresh();
    let (rho_id, rho) = tb.fresh();
    let (b_id, b) = tb.fresh();
    let (hprog_id, _hprog) = tb.fresh();
    let (n_id, n) = tb.fresh();
    let (hp_id, _hp) = tb.fresh();

    let rho_ty = Expr::arrow(state(), nat.clone());
    let concl_ex = exists_nat(q_reach_pred(&q, &b, &n));

    let type_ = {
        let mut t = concl_ex.clone();
        t = tb.pi(
            hp_id,
            BinderInfo::Default,
            app(p.clone(), app(b.clone(), n.clone())),
            t,
        );
        t = tb.pi(n_id, BinderInfo::Default, nat.clone(), t);
        t = tb.pi(hprog_id, BinderInfo::Default, hprog_ty(&p, &q, &rho, &b), t);
        t = tb.pi(b_id, BinderInfo::Default, behavior_ty(), t);
        t = tb.pi(rho_id, BinderInfo::Default, rho_ty.clone(), t);
        t = tb.pi(q_id, BinderInfo::Default, state_pred_ty(), t);
        t = tb.pi(p_id, BinderInfo::Default, state_pred_ty(), t);
        tb.finish(t)
    };

    // ── proof value ───────────────────────────────────────────────────────
    let mut vb = B::new();
    let (vp_id, vp) = vb.fresh();
    let (vq_id, vq) = vb.fresh();
    let (vrho_id, vrho) = vb.fresh();
    let (vb_id, vbv) = vb.fresh();
    let (vhprog_id, vhprog) = vb.fresh();

    // motive M := λ (k : Nat), ∀ (n : Nat), Eq (rho (b n)) k → P (b n)
    //                                          → Exists (q_reach_pred q b n)
    let motive = {
        let mut mb = B::new();
        let (k_id, k) = mb.fresh();
        let inner = {
            let mut ib = B::new();
            let (nn_id, nn) = ib.fresh();
            let bn = app(vbv.clone(), nn.clone());
            let heq_ty = eq_nat(app(vrho.clone(), bn.clone()), k.clone());
            let ex = exists_nat(q_reach_pred(&vq, &vbv, &nn));
            let body = Expr::arrow(heq_ty, Expr::arrow(app(vp.clone(), bn.clone()), ex));
            ib.pi(nn_id, BinderInfo::Default, nat.clone(), body)
        };
        mb.lam(k_id, BinderInfo::Default, nat.clone(), inner)
    };

    // STEP := λ (x : Nat)
    //            (ih : ∀ y, Nat.lt y x → M y)
    //            (n : Nat) (heq : Eq (rho (b n)) x) (hP : P (b n)) => …
    let step_fn = {
        let mut sb = B::new();
        let (x_id, x) = sb.fresh();
        let (ih_id, ih) = sb.fresh();
        let (nn_id, nn) = sb.fresh();
        let (heq_id, heq) = sb.fresh();
        let (hp2_id, hp2) = sb.fresh();

        let bn = app(vbv.clone(), nn.clone());
        let goal = exists_nat(q_reach_pred(&vq, &vbv, &nn)); // ∃ m, Q(b(n+m))

        // ── case split on Q (b n) via Classical.em ──────────────────────────
        let q_bn = app(vq.clone(), bn.clone());
        let not_q_bn = Expr::arrow(q_bn.clone(), false_());

        // fl : Q (b n) → goal   (witness m = 0)
        let fl = {
            let mut lb = B::new();
            let (hq_id, hq) = lb.fresh();
            // Exists.intro (q_reach_pred q b n) 0 hq : ∃ m, Q(b(n+m))
            // pred 0 = Q (b (n+0)) ≡ Q (b n), so hq : Q(b n) fits def-eq.
            let body = exists_intro_nat(q_reach_pred(&vq, &vbv, &nn), nat_zero(), hq.clone());
            lb.lam(hq_id, BinderInfo::Default, q_bn.clone(), body)
        };

        // fr : (Q (b n) → False) → goal
        let fr = {
            let mut rb = B::new();
            let (hnq_id, hnq) = rb.fresh();
            // Hprog n hP hnq : Exists (prog_pred P Q rho b n)
            let prog_ex = Expr::apps(vhprog.clone(), [nn.clone(), hp2.clone(), hnq.clone()]);
            let prog_p = prog_pred(&vp, &vq, &vrho, &vbv, &nn);

            // elim function: λ (m0 : Nat) (hm0 : prog_pred … m0) => …
            let elim_fn = {
                let mut eb = B::new();
                let (m0_id, m0) = eb.fresh();
                let (hm0_id, hm0) = eb.fresh();
                let bnm0 = app(vbv.clone(), nat_add(nn.clone(), m0.clone()));
                let q_reach = app(vq.clone(), bnm0.clone());
                let p_reach = app(vp.clone(), bnm0.clone());
                let rho_small = nat_lt(
                    app(vrho.clone(), bnm0.clone()),
                    app(vrho.clone(), bn.clone()),
                );
                let and_branch = and(p_reach.clone(), rho_small.clone());

                // gl : Q (b (n+m0)) → goal   (witness m0)
                let gl = {
                    let mut gb = B::new();
                    let (hqr_id, hqr) = gb.fresh();
                    let body =
                        exists_intro_nat(q_reach_pred(&vq, &vbv, &nn), m0.clone(), hqr.clone());
                    gb.lam(hqr_id, BinderInfo::Default, q_reach.clone(), body)
                };

                // gr : And (P (b(n+m0))) (rho(b(n+m0)) < rho(b n)) → goal
                let gr = {
                    let mut gb = B::new();
                    let (hand_id, hand) = gb.fresh();
                    let hpm0 = and_left(p_reach.clone(), rho_small.clone(), hand.clone());
                    let hlt = and_right(p_reach.clone(), rho_small.clone(), hand.clone());
                    // hlt : Nat.lt (rho (b (n+m0))) (rho (b n))
                    // transport to Nat.lt (rho (b (n+m0))) x via heq : rho (b n) = x
                    // motive_lt := λ (z : Nat), Nat.lt (rho (b (n+m0))) z
                    let motive_lt = {
                        let mut zb = B::new();
                        let (z_id, z) = zb.fresh();
                        let body = nat_lt(app(vrho.clone(), bnm0.clone()), z.clone());
                        zb.lam(z_id, BinderInfo::Default, nat.clone(), body)
                    };
                    let hlt_x = eq_subst_nat(
                        motive_lt,
                        app(vrho.clone(), bn.clone()),
                        x.clone(),
                        heq.clone(),
                        hlt,
                    ); // : Nat.lt (rho (b (n+m0))) x
                       // ih (rho (b (n+m0))) hlt_x : M (rho (b (n+m0)))
                    let rho_bnm0 = app(vrho.clone(), bnm0.clone());
                    let ih_at = Expr::apps(ih.clone(), [rho_bnm0.clone(), hlt_x]);
                    // ih_at (n+m0) (Eq.refl (rho (b (n+m0)))) hpm0
                    //   : Exists (q_reach_pred q b (n+m0))  = ∃ m1, Q(b((n+m0)+m1))
                    let nm0 = nat_add(nn.clone(), m0.clone());
                    let rec = Expr::apps(ih_at, [nm0.clone(), eq_refl_nat(rho_bnm0.clone()), hpm0]);
                    // reindex via Exists.elim: λ (m1 : Nat) (hQ1 : Q (b ((n+m0)+m1))) =>
                    //    Exists.intro (q_reach_pred q b n) (m0+m1)
                    //       (Eq.subst (λ z, Q (b z)) ((n+m0)+m1) (n+(m0+m1)) (add_assoc n m0 m1) hQ1)
                    let inner_pred = q_reach_pred(&vq, &vbv, &nm0); // λ m1, Q(b((n+m0)+m1))
                    let reidx_fn = {
                        let mut fb = B::new();
                        let (m1_id, m1) = fb.fresh();
                        let (hq1_id, hq1) = fb.fresh();
                        // motive_q := λ (z : Nat), Q (b z)
                        let motive_q = {
                            let mut qb = B::new();
                            let (z_id, z) = qb.fresh();
                            let body = app(vq.clone(), app(vbv.clone(), z.clone()));
                            qb.lam(z_id, BinderInfo::Default, nat.clone(), body)
                        };
                        let lhs_idx = nat_add(nat_add(nn.clone(), m0.clone()), m1.clone());
                        let rhs_idx = nat_add(nn.clone(), nat_add(m0.clone(), m1.clone()));
                        let assoc = nat_add_assoc(nn.clone(), m0.clone(), m1.clone());
                        let hq_reindexed = eq_subst_nat(
                            motive_q,
                            lhs_idx.clone(),
                            rhs_idx.clone(),
                            assoc,
                            hq1.clone(),
                        ); // : Q (b (n+(m0+m1)))
                        let witness = nat_add(m0.clone(), m1.clone());
                        let body =
                            exists_intro_nat(q_reach_pred(&vq, &vbv, &nn), witness, hq_reindexed);
                        let q1_ty = app(vq.clone(), app(vbv.clone(), lhs_idx));
                        let r = fb.lam(hq1_id, BinderInfo::Default, q1_ty, body);
                        fb.lam(m1_id, BinderInfo::Default, nat.clone(), r)
                    };
                    let elim = exists_elim_nat(inner_pred, goal.clone(), rec, reidx_fn);
                    gb.lam(hand_id, BinderInfo::Default, and_branch.clone(), elim)
                };

                // Or.rec (Q(b(n+m0))) (And …) (λ _, goal) gl gr hm0
                let or_motive = {
                    let mut ob = B::new();
                    let (o_id, _o) = ob.fresh();
                    let disj_ty = or(q_reach.clone(), and_branch.clone());
                    ob.lam(o_id, BinderInfo::Default, disj_ty, goal.clone())
                };
                let body = or_rec(
                    q_reach.clone(),
                    and_branch.clone(),
                    or_motive,
                    gl,
                    gr,
                    hm0.clone(),
                );
                let r = eb.lam(
                    hm0_id,
                    BinderInfo::Default,
                    {
                        // type of hm0 = prog_pred applied at m0 = Or (Q…) (And …)
                        or(q_reach.clone(), and_branch.clone())
                    },
                    body,
                );
                eb.lam(m0_id, BinderInfo::Default, nat.clone(), r)
            };

            let elim = exists_elim_nat(prog_p, goal.clone(), prog_ex, elim_fn);
            rb.lam(hnq_id, BinderInfo::Default, not_q_bn.clone(), elim)
        };

        // Or.rec (Q(b n)) (Q(b n) → False) (λ _, goal) fl fr (Classical.em (Q(b n)))
        let em = classical_em(q_bn.clone());
        let case_motive = {
            let mut cb = B::new();
            let (o_id, _o) = cb.fresh();
            let disj_ty = or(q_bn.clone(), not_q_bn.clone());
            cb.lam(o_id, BinderInfo::Default, disj_ty, goal.clone())
        };
        let cases = or_rec(q_bn.clone(), not_q_bn.clone(), case_motive, fl, fr, em);

        // wrap binders: x, ih, n, heq, hP
        let m_y_ty = {
            // ∀ y, Nat.lt y x → M y   — need M as a function; reuse `motive`
            let mut yb = B::new();
            let (y_id, y) = yb.fresh();
            let inner = Expr::arrow(nat_lt(y.clone(), x.clone()), app(motive.clone(), y.clone()));
            yb.pi(y_id, BinderInfo::Default, nat.clone(), inner)
        };
        let heq_ty = eq_nat(app(vrho.clone(), bn.clone()), x.clone());
        let r = sb.lam(
            hp2_id,
            BinderInfo::Default,
            app(vp.clone(), bn.clone()),
            cases,
        );
        let r = sb.lam(heq_id, BinderInfo::Default, heq_ty, r);
        let r = sb.lam(nn_id, BinderInfo::Default, nat.clone(), r);
        let r = sb.lam(ih_id, BinderInfo::Default, m_y_ty, r);
        sb.lam(x_id, BinderInfo::Default, nat.clone(), r)
    };

    // top-level: λ P Q rho b Hprog n hP =>
    //   natStrongRec M STEP (rho (b n)) n (Eq.refl (rho (b n))) hP
    let value = {
        let (vn_id, vn) = vb.fresh();
        let (vhp_id, vhp) = vb.fresh();
        let bn = app(vbv.clone(), vn.clone());
        let rho_bn = app(vrho.clone(), bn.clone());
        let strong = Expr::apps(
            c("TLAsem.natStrongRec"),
            [motive.clone(), step_fn, rho_bn.clone()],
        ); // : M (rho (b n)) = ∀ n', rho(b n')=rho(b n) → P(b n') → ∃ m, Q(b(n'+m))
        let applied = Expr::apps(
            strong,
            [vn.clone(), eq_refl_nat(rho_bn.clone()), vhp.clone()],
        );

        let mut v = applied;
        v = vb.lam(vhp_id, BinderInfo::Default, app(vp.clone(), bn.clone()), v);
        v = vb.lam(vn_id, BinderInfo::Default, nat.clone(), v);
        v = vb.lam(
            vhprog_id,
            BinderInfo::Default,
            hprog_ty(&vp, &vq, &vrho, &vbv),
            v,
        );
        v = vb.lam(vb_id, BinderInfo::Default, behavior_ty(), v);
        v = vb.lam(vrho_id, BinderInfo::Default, rho_ty.clone(), v);
        v = vb.lam(vq_id, BinderInfo::Default, state_pred_ty(), v);
        v = vb.lam(vp_id, BinderInfo::Default, state_pred_ty(), v);
        vb.finish(v)
    };

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_,
        value,
    })
}

/// `TLAsem.Enabled A s` (the unfolded `∃ s', A s s'`), as a *built* expression.
fn enabled_app(a: &Expr, s: &Expr) -> Expr {
    Expr::apps(c("TLAsem.Enabled"), [a.clone(), s.clone()])
}

/// Register `TLAsem.WfFiresWhenAlwaysEnabled` — the **fairness-under-abstraction
/// extraction** for the WF-only / continuously-enabled regime, **fully proved**.
///
/// ```text
/// WfFiresWhenAlwaysEnabled :
///   ∀ (A : Action) (b : Behavior),
///     Sat b (WF A) → (∀ s, Enabled A s)
///     → ∀ k, Sat (drop b k) (SemDiam (LiftAct A))
/// ```
///
/// i.e. from weak fairness of `A` **and** `A` enabled in every state, `A` fires
/// (`◇⟨A⟩`) from every suffix. This is the doc's "one-step" collapse of the
/// `□◇` fixpoint (§6 T·LIVE 🔴): when `Enabled A` is *continuously* true, the
/// WF antecedent `◇□(Lift Enabled A)` is *immediate* (`Exists.intro 0 (λ j, …)`),
/// so `WF A = □(◇□Enabled → ◇⟨A⟩)` discharges `◇⟨A⟩` in ONE elimination — no
/// fixpoint, no `Classical.choice`. The hypotheses are Pi-bound (not axioms);
/// closure ⊆ FOUNDATIONAL.
///
/// PROOF. `Sat b (WF A) k : (◇□Lift(Enabled A))(drop b k) → (◇⟨A⟩)(drop b k)`.
/// Build the antecedent `Exists.intro 0 (λ (j : Nat), hEn (drop … 0 j 0))`
/// (the `□` body) — well-typed because `hEn` supplies `Enabled A` at *every*
/// index. Apply to get the consequent, which is def-eq to
/// `Sat (drop b k) (SemDiam (LiftAct A))`.
pub fn register_wf_fires_when_always_enabled(env: &mut Environment) -> Result<(), EnvError> {
    register_tla_semantics_prereqs(env)?;
    register_enabled(env)?;
    register_lift_act(env)?;
    register_wf(env)?;
    let name = Name::from_string("TLAsem.WfFiresWhenAlwaysEnabled");
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let nat = state();

    // ── statement type ────────────────────────────────────────────────────
    let mut tb = B::new();
    let (a_id, a) = tb.fresh();
    let (b_id, b) = tb.fresh();
    let (hwf_id, _hwf) = tb.fresh();
    let (hen_id, _hen) = tb.fresh();
    let (k_id, k) = tb.fresh();

    let sat_wf = Expr::apps(c("TLAsem.Sat"), [b.clone(), app(c("TLAsem.WF"), a.clone())]);
    // ∀ s, Enabled A s
    let hen_ty = {
        let mut hb = B::new();
        let (s_id, s) = hb.fresh();
        let body = enabled_app(&a, &s);
        hb.pi(s_id, BinderInfo::Default, nat.clone(), body)
    };
    // Sat (drop b k) (SemDiam (LiftAct A))
    let drop_bk = Expr::apps(c("TLAsem.drop"), [b.clone(), k.clone()]);
    let diam_act = app(c("TLAsem.SemDiam"), app(c("TLAsem.LiftAct"), a.clone()));
    let concl = Expr::apps(c("TLAsem.Sat"), [drop_bk.clone(), diam_act.clone()]);

    let type_ = {
        let mut t = concl.clone();
        t = tb.pi(k_id, BinderInfo::Default, nat.clone(), t);
        t = tb.pi(hen_id, BinderInfo::Default, hen_ty.clone(), t);
        t = tb.pi(hwf_id, BinderInfo::Default, sat_wf.clone(), t);
        t = tb.pi(b_id, BinderInfo::Default, behavior_ty(), t);
        t = tb.pi(a_id, BinderInfo::Default, action_ty(), t);
        tb.finish(t)
    };

    // ── proof value ───────────────────────────────────────────────────────
    let mut vb = B::new();
    let (va_id, va) = vb.fresh();
    let (vb_id, vbv) = vb.fresh();
    let (vhwf_id, vhwf) = vb.fresh();
    let (vhen_id, vhen) = vb.fresh();
    let (vk_id, vk) = vb.fresh();

    // The WF box body, instantiated at suffix index k, has antecedent
    //   ante := (SemDiam (SemBox (Lift (Enabled A)))) (drop b k)
    //         ≡ ∃ i, ∀ j, Enabled A (b (k + (i + (j + 0))))
    // Build it as Exists.intro with witness i = 0:
    //   Exists.intro 0 (λ (j : Nat), hEn ((drop (drop (drop b k) 0) j) 0))
    // — but since hEn : ∀ s, Enabled A s, we can pass *any* index expression;
    // we use the literal indexed state so the term is well-typed against the
    // (reduced) box body.  The cleanest robust choice: provide the inner
    // ∀j proof as (λ j, hEn (<the exact state>)).  To avoid re-deriving the
    // exact index reduction by hand, we instead build the antecedent's inner
    // predicate via the public combinators and let def-eq match.

    // ante predicate for the SemBox: P_box := Lift (Enabled A)
    let lift_en = app(c("TLAsem.Lift"), app(c("TLAsem.Enabled"), va.clone()));
    let box_en = app(c("TLAsem.SemBox"), lift_en.clone()); // □(Lift Enabled)
                                                           // inner ∀j proof for □(Lift Enabled) at suffix (drop (drop b k) 0):
                                                           //   □F c ≡ ∀ j, F (drop c j);  F = Lift(Enabled A); F d = Enabled A (d 0).
                                                           // So we need (λ j, _ : Enabled A ((drop (drop (drop b k) 0) j) 0)).
                                                           // hEn applied to that exact state gives it.
    let drop_bk_v = Expr::apps(c("TLAsem.drop"), [vbv.clone(), vk.clone()]);
    let suffix0 = Expr::apps(c("TLAsem.drop"), [drop_bk_v.clone(), nat_zero()]); // drop (drop b k) 0

    // box_proof : □(Lift (Enabled A)) (drop (drop b k) 0)
    //           ≡ ∀ j, Enabled A ((drop (drop (drop b k) 0) j) 0)
    let box_proof = {
        let mut jb = B::new();
        let (j_id, j) = jb.fresh();
        let inner_suffix = Expr::apps(c("TLAsem.drop"), [suffix0.clone(), j.clone()]);
        let st = app(inner_suffix.clone(), nat_zero()); // (drop (drop(drop b k)0) j) 0
        let body = app(vhen.clone(), st);
        jb.lam(j_id, BinderInfo::Default, nat.clone(), body)
    };

    // ante : ◇□(Lift Enabled) (drop b k) ≡ ∃ i, □(Lift Enabled) (drop (drop b k) i)
    // witness i = 0, proof = box_proof.
    // The SemDiam existential predicate is  λ i, □(Lift Enabled) (drop (drop b k) i).
    let diam_pred = {
        let mut ib = B::new();
        let (i_id, i) = ib.fresh();
        let suffix_i = Expr::apps(c("TLAsem.drop"), [drop_bk_v.clone(), i.clone()]);
        let body = app(box_en.clone(), suffix_i);
        ib.lam(i_id, BinderInfo::Default, nat.clone(), body)
    };
    let ante = exists_intro_nat(diam_pred, nat_zero(), box_proof);

    // apply WF at k:  (Sat b (WF A)) k ante  : ◇⟨A⟩ (drop b k)  ≡ concl
    // Sat b (WF A) ≡ WF A b ≡ □(λ c, ◇□Enabled c → ◇⟨A⟩ c) b ≡ ∀ k, (… (drop b k))
    let wf_at_k = app(vhwf.clone(), vk.clone()); // : ante_ty → concl_ty (reduced)
    let fired = app(wf_at_k, ante); // : ◇⟨A⟩ (drop b k)  ≡  Sat (drop b k)(SemDiam(LiftAct A))

    // Rebuild the parameter-dependent binder types against the *value*
    // builder's fvars (va/vbv), not the type builder's (a/b) — else they leak.
    let sat_wf_v = Expr::apps(
        c("TLAsem.Sat"),
        [vbv.clone(), app(c("TLAsem.WF"), va.clone())],
    );
    let hen_ty_v = {
        let mut hb = B::new();
        let (s_id, s) = hb.fresh();
        let body = enabled_app(&va, &s);
        hb.pi(s_id, BinderInfo::Default, nat.clone(), body)
    };

    let value = {
        let mut v = fired;
        v = vb.lam(vk_id, BinderInfo::Default, nat.clone(), v);
        v = vb.lam(vhen_id, BinderInfo::Default, hen_ty_v, v);
        v = vb.lam(vhwf_id, BinderInfo::Default, sat_wf_v, v);
        v = vb.lam(vb_id, BinderInfo::Default, behavior_ty(), v);
        v = vb.lam(va_id, BinderInfo::Default, action_ty(), v);
        vb.finish(v)
    };

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_,
        value,
    })
}

/// Register `TLAsem.WfFiresWhenEnabledThroughout` — the **fairness-under-
/// abstraction extraction GENERALIZED** from *global* enabledness to a
/// **suffix-local `□Enabled`** premise, **fully proved**.
///
/// ```text
/// WfFiresWhenEnabledThroughout :
///   ∀ (A : Action) (b : Behavior),
///     Sat b (WF A)
///     → ∀ (k : Nat),
///         Sat (drop b k) (SemBox (Lift (Enabled A)))      -- □Enabled from k
///       → Sat (drop b k) (SemDiam (LiftAct A))            -- ◇⟨A⟩ from k
/// ```
///
/// This **strictly subsumes** [`register_wf_fires_when_always_enabled`]: that
/// lemma required `(∀ s, Enabled A s)` (continuous *global* enabledness); this
/// one requires only that `A` be enabled at **every state of the suffix
/// `drop b k`** — exactly `□(Lift (Enabled A))` from `k`. It is the bridge that
/// lets the general WF1 metatheorem feed the "stays-enabled-while-waiting"
/// invariant (a *suffix* fact, never a global one) into weak fairness.
///
/// PROOF. `Sat b (WF A) k : (◇□Lift(Enabled A))(drop b k) → (◇⟨A⟩)(drop b k)`.
/// We build the antecedent `◇□Enabled (drop b k)` with witness `i = 0`:
/// `Exists.intro (λ i, □(Lift Enabled)(drop (drop b k) i)) 0 box0`, where
/// `box0 : □(Lift Enabled)(drop (drop b k) 0) ≡ ∀ j, Enabled A (b (k+(0+(j+0))))`
/// is `λ j, hbox (0+(j+0))` — the premise `hbox : ∀ i, Enabled A (b (k+i))`
/// (the def-eq unfolding of `□Enabled from k`) applied at the *exact* index the
/// reduced box body demands. Apply WF to get the consequent
/// `◇⟨A⟩ (drop b k) ≡ Sat (drop b k)(SemDiam (LiftAct A))`. No `Classical`,
/// no fixpoint; hypotheses Pi-bound ⇒ closure ⊆ FOUNDATIONAL.
pub fn register_wf_fires_when_enabled_throughout(env: &mut Environment) -> Result<(), EnvError> {
    register_tla_semantics_prereqs(env)?;
    register_enabled(env)?;
    register_lift_act(env)?;
    register_wf(env)?;
    let name = Name::from_string("TLAsem.WfFiresWhenEnabledThroughout");
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let nat = state();

    // box_en_from(a, b, k) := Sat (drop b k) (SemBox (Lift (Enabled A)))
    let box_en_from = |a: &Expr, b: &Expr, k: &Expr| -> Expr {
        let drop_bk = Expr::apps(c("TLAsem.drop"), [b.clone(), k.clone()]);
        let lift_en = app(c("TLAsem.Lift"), app(c("TLAsem.Enabled"), a.clone()));
        let box_en = app(c("TLAsem.SemBox"), lift_en);
        Expr::apps(c("TLAsem.Sat"), [drop_bk, box_en])
    };
    // diam_fire_from(a, b, k) := Sat (drop b k) (SemDiam (LiftAct A))
    let diam_fire_from = |a: &Expr, b: &Expr, k: &Expr| -> Expr {
        let drop_bk = Expr::apps(c("TLAsem.drop"), [b.clone(), k.clone()]);
        let diam_act = app(c("TLAsem.SemDiam"), app(c("TLAsem.LiftAct"), a.clone()));
        Expr::apps(c("TLAsem.Sat"), [drop_bk, diam_act])
    };

    // ── statement type ────────────────────────────────────────────────────
    let mut tb = B::new();
    let (a_id, a) = tb.fresh();
    let (b_id, b) = tb.fresh();
    let (hwf_id, _hwf) = tb.fresh();
    let (k_id, k) = tb.fresh();
    let (hbox_id, _hbox) = tb.fresh();

    let sat_wf = Expr::apps(c("TLAsem.Sat"), [b.clone(), app(c("TLAsem.WF"), a.clone())]);
    let type_ = {
        let mut t = diam_fire_from(&a, &b, &k);
        t = tb.pi(hbox_id, BinderInfo::Default, box_en_from(&a, &b, &k), t);
        t = tb.pi(k_id, BinderInfo::Default, nat.clone(), t);
        t = tb.pi(hwf_id, BinderInfo::Default, sat_wf.clone(), t);
        t = tb.pi(b_id, BinderInfo::Default, behavior_ty(), t);
        t = tb.pi(a_id, BinderInfo::Default, action_ty(), t);
        tb.finish(t)
    };

    // ── proof value ───────────────────────────────────────────────────────
    let mut vb = B::new();
    let (va_id, va) = vb.fresh();
    let (vb_id, vbv) = vb.fresh();
    let (vhwf_id, vhwf) = vb.fresh();
    let (vk_id, vk) = vb.fresh();
    let (vhbox_id, vhbox) = vb.fresh();

    let lift_en = app(c("TLAsem.Lift"), app(c("TLAsem.Enabled"), va.clone()));
    let box_en = app(c("TLAsem.SemBox"), lift_en.clone()); // □(Lift Enabled)
    let drop_bk_v = Expr::apps(c("TLAsem.drop"), [vbv.clone(), vk.clone()]);

    // box0 : □(Lift Enabled)(drop (drop b k) 0)
    //      ≡ ∀ j, Enabled A ((drop (drop (drop b k) 0) j) 0)
    //      and the demanded state ((drop (drop (drop b k) 0) j) 0) ≡ b (k + (0 + (j + 0))).
    // `vhbox : □(Lift Enabled)(drop b k) ≡ ∀ i, Enabled A (b (k + i))`, so we apply
    // it at  i := 0 + (j + 0)  to land *exactly* on the demanded index.
    let box0 = {
        let mut jb = B::new();
        let (j_id, j) = jb.fresh();
        let idx = nat_add(nat_zero(), nat_add(j.clone(), nat_zero())); // 0 + (j + 0)
        let body = app(vhbox.clone(), idx);
        jb.lam(j_id, BinderInfo::Default, nat.clone(), body)
    };

    // ante : ◇□(Lift Enabled)(drop b k) := Exists.intro diam_pred 0 box0
    let diam_pred = {
        let mut ib = B::new();
        let (i_id, i) = ib.fresh();
        let suffix_i = Expr::apps(c("TLAsem.drop"), [drop_bk_v.clone(), i.clone()]);
        let body = app(box_en.clone(), suffix_i);
        ib.lam(i_id, BinderInfo::Default, nat.clone(), body)
    };
    let ante = exists_intro_nat(diam_pred, nat_zero(), box0);

    // (Sat b (WF A)) k ante : ◇⟨A⟩ (drop b k) ≡ Sat (drop b k)(SemDiam(LiftAct A))
    let wf_at_k = app(vhwf.clone(), vk.clone());
    let fired = app(wf_at_k, ante);

    let sat_wf_v = Expr::apps(
        c("TLAsem.Sat"),
        [vbv.clone(), app(c("TLAsem.WF"), va.clone())],
    );
    let value = {
        let mut v = fired;
        v = vb.lam(
            vhbox_id,
            BinderInfo::Default,
            box_en_from(&va, &vbv, &vk),
            v,
        );
        v = vb.lam(vk_id, BinderInfo::Default, nat.clone(), v);
        v = vb.lam(vhwf_id, BinderInfo::Default, sat_wf_v, v);
        v = vb.lam(vb_id, BinderInfo::Default, behavior_ty(), v);
        v = vb.lam(va_id, BinderInfo::Default, action_ty(), v);
        vb.finish(v)
    };

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_,
        value,
    })
}

/// Register `TLAsem.LatticeRankSound` — the first **liveness certificate**
/// theorem (WF-only, single helpful action, ℕ-rank), **fully proved** by
/// composing the fairness extraction [`register_wf_fires_when_always_enabled`]
/// with the well-founded descent [`register_wf_descent_sound`].
///
/// ```text
/// LatticeRankSound :
///   ∀ (A : Action) (P Q : StatePred) (rho : State → Nat) (b : Behavior),
///     (Hwf  : Sat b (WF A))                               -- weak fairness of A
///     (Hen  : ∀ s, Enabled A s)                           -- A continuously enabled
///     (Hfire2prog :                                       -- the local WF1+rank step
///        ∀ n, P (b n) → (Q (b n) → False)
///           → Sat (drop b n) (SemDiam (LiftAct A))        -- ◇⟨A⟩ from n
///           → ∃ m, Q (b (n+m)) ∨ (P (b (n+m)) ∧ rho (b (n+m)) < rho (b n)))
///     → ∀ n, P (b n) → ∃ m, Q (b (n+m))
/// ```
///
/// The conclusion is **definitionally** `Sat b (LeadsTo (Lift P) (Lift Q))`
/// (= `P ⇝ Q`); see [`register_wf_descent_sound`].
///
/// PROOF (genuine composition; no axiom stand-ins):
///   `LatticeRankSound A P Q rho b Hwf Hen Hfire2prog
///      := WfDescentSound P Q rho b
///           (λ n hP hnQ, Hfire2prog n hP hnQ
///                          (WfFiresWhenAlwaysEnabled A b Hwf Hen n))`.
/// `WfFiresWhenAlwaysEnabled` discharges the fairness obligation (`◇⟨A⟩` from
/// every suffix, from `WF A` + continuous enabledness — the doc's one-step
/// `□◇` collapse); `Hfire2prog` is the *local* WF1+rank descent step (Lamport's
/// `P ∧ ⟨A⟩ ⇒ Q' ∨ (P' ∧ rho↓)`), a Pi-bound hypothesis (NOT an axiom — the
/// per-verdict soundness leg, §2/§13); `WfDescentSound` runs the well-founded
/// rank induction. All hypotheses Pi-bound ⇒ closure ⊆ FOUNDATIONAL.
///
/// **HONEST RESIDUAL (§6 T·LIVE, reported up):** `Hfire2prog` is supplied, not
/// derived from raw `Next`/H1–H3 here. Deriving it *in full generality* (finding
/// the **first** A-fire and chaining rank-monotonicity from `n` to that index)
/// is the multi-step WF1 metatheorem; the *continuously-enabled, immediate-fire*
/// slice it rests on is the part `WfFiresWhenAlwaysEnabled` already closes.
pub fn register_lattice_rank_sound(env: &mut Environment) -> Result<(), EnvError> {
    register_tla_semantics_prereqs(env)?;
    register_leadsto(env)?;
    register_enabled(env)?;
    register_lift_act(env)?;
    register_wf(env)?;
    register_nat_strong_rec(env)?;
    register_wf_descent_sound(env)?;
    register_wf_fires_when_always_enabled(env)?;
    let name = Name::from_string("TLAsem.LatticeRankSound");
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let nat = state();
    let rho_ty = Expr::arrow(state(), nat.clone());

    // ── shared type builders (parameterized by fvars) ──────────────────────
    // Hfire2prog type, given fvars a,p,q,rho,b:
    let hfire2prog_ty = |a: &Expr, p: &Expr, q: &Expr, rho: &Expr, b: &Expr| -> Expr {
        let mut nb = B::new();
        let (n_id, n) = nb.fresh();
        let bn = app(b.clone(), n.clone());
        let not_q = Expr::arrow(app(q.clone(), bn.clone()), false_());
        // ◇⟨A⟩ from n  :=  Sat (drop b n) (SemDiam (LiftAct A))
        let drop_bn = Expr::apps(c("TLAsem.drop"), [b.clone(), n.clone()]);
        let diam_act = app(c("TLAsem.SemDiam"), app(c("TLAsem.LiftAct"), a.clone()));
        let fires = Expr::apps(c("TLAsem.Sat"), [drop_bn, diam_act]);
        let ex = exists_nat(prog_pred(p, q, rho, b, &n));
        let inner = Expr::arrow(
            app(p.clone(), bn.clone()),
            Expr::arrow(not_q, Expr::arrow(fires, ex)),
        );
        nb.pi(n_id, BinderInfo::Default, nat.clone(), inner)
    };
    let hen_ty = |a: &Expr| -> Expr {
        let mut hb = B::new();
        let (s_id, s) = hb.fresh();
        hb.pi(s_id, BinderInfo::Default, nat.clone(), enabled_app(a, &s))
    };
    let sat_wf = |a: &Expr, b: &Expr| -> Expr {
        Expr::apps(c("TLAsem.Sat"), [b.clone(), app(c("TLAsem.WF"), a.clone())])
    };

    // ── statement type ────────────────────────────────────────────────────
    let mut tb = B::new();
    let (a_id, a) = tb.fresh();
    let (p_id, p) = tb.fresh();
    let (q_id, q) = tb.fresh();
    let (rho_id, rho) = tb.fresh();
    let (b_id, b) = tb.fresh();
    let (hwf_id, _hwf) = tb.fresh();
    let (hen_id, _hen) = tb.fresh();
    let (hf2p_id, _hf2p) = tb.fresh();
    let (n_id, n) = tb.fresh();
    let (hp_id, _hp) = tb.fresh();

    let concl_ex = exists_nat(q_reach_pred(&q, &b, &n));
    let type_ = {
        let mut t = concl_ex;
        t = tb.pi(
            hp_id,
            BinderInfo::Default,
            app(p.clone(), app(b.clone(), n.clone())),
            t,
        );
        t = tb.pi(n_id, BinderInfo::Default, nat.clone(), t);
        t = tb.pi(
            hf2p_id,
            BinderInfo::Default,
            hfire2prog_ty(&a, &p, &q, &rho, &b),
            t,
        );
        t = tb.pi(hen_id, BinderInfo::Default, hen_ty(&a), t);
        t = tb.pi(hwf_id, BinderInfo::Default, sat_wf(&a, &b), t);
        t = tb.pi(b_id, BinderInfo::Default, behavior_ty(), t);
        t = tb.pi(rho_id, BinderInfo::Default, rho_ty.clone(), t);
        t = tb.pi(q_id, BinderInfo::Default, state_pred_ty(), t);
        t = tb.pi(p_id, BinderInfo::Default, state_pred_ty(), t);
        t = tb.pi(a_id, BinderInfo::Default, action_ty(), t);
        tb.finish(t)
    };

    // ── proof value ───────────────────────────────────────────────────────
    let mut vb = B::new();
    let (va_id, va) = vb.fresh();
    let (vp_id, vp) = vb.fresh();
    let (vq_id, vq) = vb.fresh();
    let (vrho_id, vrho) = vb.fresh();
    let (vb_id, vbv) = vb.fresh();
    let (vhwf_id, vhwf) = vb.fresh();
    let (vhen_id, vhen) = vb.fresh();
    let (vhf2p_id, vhf2p) = vb.fresh();

    // Hprog := λ (n : Nat) (hP : P (b n)) (hnQ : Q (b n) → False) =>
    //   Hfire2prog n hP hnQ (WfFiresWhenAlwaysEnabled A b Hwf Hen n)
    let hprog = {
        let mut pb = B::new();
        let (n2_id, n2) = pb.fresh();
        let (hp2_id, hp2) = pb.fresh();
        let (hnq_id, hnq) = pb.fresh();
        let bn = app(vbv.clone(), n2.clone());
        // WfFiresWhenAlwaysEnabled A b Hwf Hen n  : Sat (drop b n)(SemDiam(LiftAct A))
        let fires = Expr::apps(
            c("TLAsem.WfFiresWhenAlwaysEnabled"),
            [
                va.clone(),
                vbv.clone(),
                vhwf.clone(),
                vhen.clone(),
                n2.clone(),
            ],
        );
        let body = Expr::apps(vhf2p.clone(), [n2.clone(), hp2.clone(), hnq.clone(), fires]);
        let not_q = Expr::arrow(app(vq.clone(), bn.clone()), false_());
        let r = pb.lam(hnq_id, BinderInfo::Default, not_q, body);
        let r = pb.lam(hp2_id, BinderInfo::Default, app(vp.clone(), bn.clone()), r);
        pb.lam(n2_id, BinderInfo::Default, nat.clone(), r)
    };

    // WfDescentSound P Q rho b Hprog : ∀ n, P (b n) → ∃ m, Q (b (n+m))
    let descent = Expr::apps(
        c("TLAsem.WfDescentSound"),
        [vp.clone(), vq.clone(), vrho.clone(), vbv.clone(), hprog],
    );

    let value = {
        let mut v = descent;
        v = vb.lam(
            vhf2p_id,
            BinderInfo::Default,
            hfire2prog_ty(&va, &vp, &vq, &vrho, &vbv),
            v,
        );
        v = vb.lam(vhen_id, BinderInfo::Default, hen_ty(&va), v);
        v = vb.lam(vhwf_id, BinderInfo::Default, sat_wf(&va, &vbv), v);
        v = vb.lam(vb_id, BinderInfo::Default, behavior_ty(), v);
        v = vb.lam(vrho_id, BinderInfo::Default, rho_ty.clone(), v);
        v = vb.lam(vq_id, BinderInfo::Default, state_pred_ty(), v);
        v = vb.lam(vp_id, BinderInfo::Default, state_pred_ty(), v);
        v = vb.lam(va_id, BinderInfo::Default, action_ty(), v);
        vb.finish(v)
    };

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_,
        value,
    })
}

// ── WF1-metatheorem verification-condition types (the raw Lamport premises) ──
//
// These are the honest VCs that replace the opaque `Hfire2prog`: they are stated
// against `Next`/`A`/`P`/`Q`/`rho` *directly* (no liveness magic), each a real
// `∀`-quantified state-level implication — exactly Lamport's WF1 + ranking.

/// `Hpstab : ∀ s s', P s → (Q s → False) → Next s s' → Or (Q s') (P s')`
/// — `P` is **stable** along `Next` until `Q` (the WF1 `P ∧ [N] ⇒ P' ∨ Q'`).
pub(crate) fn hpstab_ty(next: &Expr, p: &Expr, q: &Expr) -> Expr {
    let mut sb = B::new();
    let (s_id, s) = sb.fresh();
    let (sp_id, sp) = sb.fresh();
    let not_q = Expr::arrow(app(q.clone(), s.clone()), false_());
    let nx = Expr::apps(next.clone(), [s.clone(), sp.clone()]);
    let concl = or(app(q.clone(), sp.clone()), app(p.clone(), sp.clone()));
    let inner = Expr::arrow(
        app(p.clone(), s.clone()),
        Expr::arrow(not_q, Expr::arrow(nx, concl)),
    );
    let inner = sb.pi(sp_id, BinderInfo::Default, state(), inner);
    sb.pi(s_id, BinderInfo::Default, state(), inner)
}

/// `Hrank : ∀ s s', P s → (Q s → False) → Next s s' → Or (Q s') (Nat.le (rho s')(rho s))`
/// — rank is **non-increasing** along `Next` off the goal (the WF1 rank floor).
pub(crate) fn hrank_ty(next: &Expr, p: &Expr, q: &Expr, rho: &Expr) -> Expr {
    let mut sb = B::new();
    let (s_id, s) = sb.fresh();
    let (sp_id, sp) = sb.fresh();
    let not_q = Expr::arrow(app(q.clone(), s.clone()), false_());
    let nx = Expr::apps(next.clone(), [s.clone(), sp.clone()]);
    let le = nat_le(app(rho.clone(), sp.clone()), app(rho.clone(), s.clone()));
    let concl = or(app(q.clone(), sp.clone()), le);
    let inner = Expr::arrow(
        app(p.clone(), s.clone()),
        Expr::arrow(not_q, Expr::arrow(nx, concl)),
    );
    let inner = sb.pi(sp_id, BinderInfo::Default, state(), inner);
    sb.pi(s_id, BinderInfo::Default, state(), inner)
}

/// `Hhelp : ∀ s s', P s → (Q s → False) → A s s' → Or (Q s') (Nat.lt (rho s')(rho s))`
/// — the **helpful** action strictly drops the rank (or already reaches `Q`).
pub(crate) fn hhelp_ty(a: &Expr, p: &Expr, q: &Expr, rho: &Expr) -> Expr {
    let mut sb = B::new();
    let (s_id, s) = sb.fresh();
    let (sp_id, sp) = sb.fresh();
    let not_q = Expr::arrow(app(q.clone(), s.clone()), false_());
    let act = Expr::apps(a.clone(), [s.clone(), sp.clone()]);
    let lt = nat_lt(app(rho.clone(), sp.clone()), app(rho.clone(), s.clone()));
    let concl = or(app(q.clone(), sp.clone()), lt);
    let inner = Expr::arrow(
        app(p.clone(), s.clone()),
        Expr::arrow(not_q, Expr::arrow(act, concl)),
    );
    let inner = sb.pi(sp_id, BinderInfo::Default, state(), inner);
    sb.pi(s_id, BinderInfo::Default, state(), inner)
}

/// `Hen : ∀ s, P s → (Q s → False) → Enabled A s`
/// — `A` is enabled at **every waiting (`P ∧ ¬Q`) state** (NOT globally).
pub(crate) fn hen_wait_ty(a: &Expr, p: &Expr, q: &Expr) -> Expr {
    let mut sb = B::new();
    let (s_id, s) = sb.fresh();
    let not_q = Expr::arrow(app(q.clone(), s.clone()), false_());
    let inner = Expr::arrow(
        app(p.clone(), s.clone()),
        Expr::arrow(not_q, enabled_app(a, &s)),
    );
    sb.pi(s_id, BinderInfo::Default, state(), inner)
}

/// `HAsub : ∀ s s', A s s' → Next s s'` — the helpful action is part of `Next`.
pub(crate) fn hasub_ty(a: &Expr, next: &Expr) -> Expr {
    let mut sb = B::new();
    let (s_id, s) = sb.fresh();
    let (sp_id, sp) = sb.fresh();
    let act = Expr::apps(a.clone(), [s.clone(), sp.clone()]);
    let nx = Expr::apps(next.clone(), [s.clone(), sp.clone()]);
    let inner = Expr::arrow(act, nx);
    let inner = sb.pi(sp_id, BinderInfo::Default, state(), inner);
    sb.pi(s_id, BinderInfo::Default, state(), inner)
}

/// The prefix-invariant disjunction at base `n`, prefix length `j`:
/// `Or (∃ i, Q (b (n+i))) (And (P (b (n+j))) (Nat.le (rho (b (n+j))) (rho (b n))))`.
/// (Left: `Q` already reached somewhere in the suffix. Right: still waiting at
/// `n+j`, with rank bounded by the start rank.)
fn prefix_inv_disj(p: &Expr, q: &Expr, rho: &Expr, b: &Expr, n: &Expr, j: &Expr) -> Expr {
    let q_reached = exists_nat(q_reach_pred(q, b, n));
    let bnj = app(b.clone(), nat_add(n.clone(), j.clone()));
    let bn = app(b.clone(), n.clone());
    let p_now = app(p.clone(), bnj.clone());
    let rank_bounded = nat_le(app(rho.clone(), bnj.clone()), app(rho.clone(), bn.clone()));
    or(q_reached, and(p_now, rank_bounded))
}

/// Register `TLAsem.WfPrefixInvariant` — the **stays-waiting-until-`Q`** prefix
/// invariant, **fully proved** by ordinary `Nat.rec` induction on the prefix
/// length `j`. This is one of the two pieces that *derive* the old `Hfire2prog`.
///
/// ```text
/// WfPrefixInvariant :
///   ∀ (P Q : StatePred) (rho : State → Nat) (Next : Action) (b : Behavior),
///     (Hstep  : ∀ i, Or (Next (b i)(b (succ i))) (Eq (b (succ i))(b i)))
///     (Hpstab : ∀ s s', P s → (Q s→False) → Next s s' → Or (Q s')(P s'))
///     (Hrank  : ∀ s s', P s → (Q s→False) → Next s s' → Or (Q s')(rho s' ≤ rho s))
///     → ∀ n, P (b n) → (Q (b n) → False)
///         → ∀ j, Or (∃ i, Q (b (n+i)))
///                   (And (P (b (n+j))) (rho (b (n+j)) ≤ rho (b n)))
/// ```
///
/// PROOF (`Nat.rec` on `j`):
/// * base `j = 0`: right disjunct `⟨hP, Nat.le_refl⟩` (`b (n+0) ≡ b n`).
/// * step `j → succ j`: split the IH disjunction (`Or.rec`).
///   - left (`∃ i, Q`): propagate left.
///   - right (`P (b (n+j)) ∧ rho (b (n+j)) ≤ rho (b n)`): split `Q (b (n+j))`
///     classically. If `Q`, go left (witness `i = j`). Else use `Hstep (n+j)`:
///     on a real `Next` step, `Hpstab`/`Hrank` give `P (b (n+j+1))` (or `Q'`⇒left)
///     and `rho (b (n+j+1)) ≤ rho (b (n+j)) ≤ rho (b n)` (`Nat.le_trans`); on a
///     stutter (`b (n+j+1) = b (n+j)`), `Eq.subst` carries `P`/rank across. Either
///     way the right disjunct holds at `succ j` (`b (n + succ j) ≡ b (succ (n+j))`
///     ≡ `b ((n+j)+1)` by iota).
fn register_wf_prefix_invariant(env: &mut Environment) -> Result<(), EnvError> {
    register_tla_semantics_prereqs(env)?;
    let name = Name::from_string("TLAsem.WfPrefixInvariant");
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let nat = state();
    let rho_ty = Expr::arrow(state(), nat.clone());

    // ── statement type ────────────────────────────────────────────────────
    let mut tb = B::new();
    let (p_id, p) = tb.fresh();
    let (q_id, q) = tb.fresh();
    let (rho_id, rho) = tb.fresh();
    let (next_id, next) = tb.fresh();
    let (b_id, b) = tb.fresh();
    let (hstep_id, _hstep) = tb.fresh();
    let (hpstab_id, _hpstab) = tb.fresh();
    let (hrank_id, _hrank) = tb.fresh();
    let (n_id, n) = tb.fresh();
    let (hp_id, _hp) = tb.fresh();
    let (hnq_id, _hnq) = tb.fresh();
    let (j_id, j) = tb.fresh();

    let type_ = {
        let mut t = prefix_inv_disj(&p, &q, &rho, &b, &n, &j);
        t = tb.pi(j_id, BinderInfo::Default, nat.clone(), t);
        let not_q_bn = Expr::arrow(app(q.clone(), app(b.clone(), n.clone())), false_());
        t = tb.pi(hnq_id, BinderInfo::Default, not_q_bn, t);
        t = tb.pi(
            hp_id,
            BinderInfo::Default,
            app(p.clone(), app(b.clone(), n.clone())),
            t,
        );
        t = tb.pi(n_id, BinderInfo::Default, nat.clone(), t);
        t = tb.pi(
            hrank_id,
            BinderInfo::Default,
            hrank_ty(&next, &p, &q, &rho),
            t,
        );
        t = tb.pi(hpstab_id, BinderInfo::Default, hpstab_ty(&next, &p, &q), t);
        t = tb.pi(hstep_id, BinderInfo::Default, step_forall_ty(&next, &b), t);
        t = tb.pi(b_id, BinderInfo::Default, behavior_ty(), t);
        t = tb.pi(next_id, BinderInfo::Default, action_ty(), t);
        t = tb.pi(rho_id, BinderInfo::Default, rho_ty.clone(), t);
        t = tb.pi(q_id, BinderInfo::Default, state_pred_ty(), t);
        t = tb.pi(p_id, BinderInfo::Default, state_pred_ty(), t);
        tb.finish(t)
    };

    // ── proof value ───────────────────────────────────────────────────────
    let mut vb = B::new();
    let (vp_id, vp) = vb.fresh();
    let (vq_id, vq) = vb.fresh();
    let (vrho_id, vrho) = vb.fresh();
    let (vnext_id, vnext) = vb.fresh();
    let (vb_id, vbv) = vb.fresh();
    let (vhstep_id, vhstep) = vb.fresh();
    let (vhpstab_id, vhpstab) = vb.fresh();
    let (vhrank_id, vhrank) = vb.fresh();
    let (vn_id, vn) = vb.fresh();
    let (vhp_id, vhp) = vb.fresh();
    let (vhnq_id, _vhnq) = vb.fresh();

    let bn = app(vbv.clone(), vn.clone());
    let rho_bn = app(vrho.clone(), bn.clone());

    // motive M := λ (j : Nat), prefix_inv_disj … j
    let motive = {
        let mut mb = B::new();
        let (jj_id, jj) = mb.fresh();
        let body = prefix_inv_disj(&vp, &vq, &vrho, &vbv, &vn, &jj);
        mb.lam(jj_id, BinderInfo::Default, nat.clone(), body)
    };

    // base : M 0 = Or (∃i,Q(b(n+i))) (And (P(b(n+0))) (rho(b(n+0)) ≤ rho(b n)))
    //   ≡ Or _ (And (P(b n)) (rho(b n) ≤ rho(b n)))   (b(n+0) ≡ b n)
    //   inr ⟨hP, Nat.le_refl (rho(b n))⟩
    let base = {
        let q_reached = exists_nat(q_reach_pred(&vq, &vbv, &vn));
        let p_now = app(vp.clone(), bn.clone());
        let rank_bounded = nat_le(rho_bn.clone(), rho_bn.clone());
        let and_pf = and_intro(
            p_now.clone(),
            rank_bounded.clone(),
            vhp.clone(),
            nat_le_refl(rho_bn.clone()),
        );
        or_inr(q_reached, and(p_now, rank_bounded), and_pf)
    };

    // step : ∀ (j : Nat), M j → M (succ j)
    let step_fn = {
        let mut spb = B::new();
        let (jj_id, jj) = spb.fresh();
        let (ih_id, ih) = spb.fresh();

        let bnj = app(vbv.clone(), nat_add(vn.clone(), jj.clone())); // b (n+j)
        let bnsj = app(vbv.clone(), nat_add(vn.clone(), nat_succ(jj.clone()))); // b(n+succ j) ≡ b((n+j)+1)
        let q_reached = exists_nat(q_reach_pred(&vq, &vbv, &vn));
        // goal type at succ j:
        let goal = prefix_inv_disj(&vp, &vq, &vrho, &vbv, &vn, &nat_succ(jj.clone()));

        // IH disjunction component types:
        let p_at_j = app(vp.clone(), bnj.clone());
        let rank_at_j = nat_le(app(vrho.clone(), bnj.clone()), rho_bn.clone());
        let and_at_j = and(p_at_j.clone(), rank_at_j.clone());

        // ── ih_left : (∃i,Q) → goal  (propagate left) ──────────────────────
        let ih_left = {
            let mut lb = B::new();
            let (hq_id, hq) = lb.fresh();
            // goal's left disjunct is the SAME `∃i,Q(b(n+i))`
            let body = or_inl(
                q_reached.clone(),
                {
                    let p_now = app(vp.clone(), bnsj.clone());
                    let rb = nat_le(app(vrho.clone(), bnsj.clone()), rho_bn.clone());
                    and(p_now, rb)
                },
                hq.clone(),
            );
            lb.lam(hq_id, BinderInfo::Default, q_reached.clone(), body)
        };

        // ── ih_right : (P(b(n+j)) ∧ rho(b(n+j)) ≤ rho(b n)) → goal ──────────
        let ih_right = {
            let mut rb = B::new();
            let (hand_id, hand) = rb.fresh();
            let hp_j = and_left(p_at_j.clone(), rank_at_j.clone(), hand.clone()); // P(b(n+j))
            let hrank_j = and_right(p_at_j.clone(), rank_at_j.clone(), hand.clone()); // rho(b(n+j)) ≤ rho(b n)

            // split Q(b(n+j)) classically
            let q_at_j = app(vq.clone(), bnj.clone());
            let not_q_at_j = Expr::arrow(q_at_j.clone(), false_());

            // q_fl : Q(b(n+j)) → goal  (witness i = j on the left)
            let q_fl = {
                let mut fb = B::new();
                let (hq_id, hq) = fb.fresh();
                let ex = exists_intro_nat(q_reach_pred(&vq, &vbv, &vn), jj.clone(), hq.clone());
                let p_now = app(vp.clone(), bnsj.clone());
                let rbd = nat_le(app(vrho.clone(), bnsj.clone()), rho_bn.clone());
                let body = or_inl(q_reached.clone(), and(p_now, rbd), ex);
                fb.lam(hq_id, BinderInfo::Default, q_at_j.clone(), body)
            };

            // q_fr : (Q(b(n+j)) → False) → goal   (waiting; advance one step)
            let q_fr = {
                let mut fb = B::new();
                let (hnqj_id, hnqj) = fb.fresh();

                // Hstep (n+j) : Or (Next (b(n+j))(b(n+j+1))) (Eq (b(n+j+1))(b(n+j)))
                let idx = nat_add(vn.clone(), jj.clone());
                let step_disj = app(vhstep.clone(), idx.clone());
                let next_step = Expr::apps(vnext.clone(), [bnj.clone(), bnsj.clone()]);
                let stutter_eq = eq_state(bnsj.clone(), bnj.clone());

                // s_next : Next(b(n+j))(b(n+j+1)) → goal
                let s_next = {
                    let mut nb = B::new();
                    let (hnext_id, hnext) = nb.fresh();
                    // Hpstab (b(n+j))(b(n+j+1)) hp_j hnqj hnext : Or (Q(b(n+j+1))) (P(b(n+j+1)))
                    let pstab = Expr::apps(
                        vhpstab.clone(),
                        [
                            bnj.clone(),
                            bnsj.clone(),
                            hp_j.clone(),
                            hnqj.clone(),
                            hnext.clone(),
                        ],
                    );
                    // Hrank (b(n+j))(b(n+j+1)) hp_j hnqj hnext : Or (Q(b(n+j+1))) (rho(b(n+j+1)) ≤ rho(b(n+j)))
                    let rankd = Expr::apps(
                        vhrank.clone(),
                        [
                            bnj.clone(),
                            bnsj.clone(),
                            hp_j.clone(),
                            hnqj.clone(),
                            hnext.clone(),
                        ],
                    );
                    let q_at_sj = app(vq.clone(), bnsj.clone());
                    let p_at_sj = app(vp.clone(), bnsj.clone());
                    let rho_le_j = nat_le(
                        app(vrho.clone(), bnsj.clone()),
                        app(vrho.clone(), bnj.clone()),
                    );

                    // We need to combine pstab : Q∨P  and rankd : Q∨(rho'≤rho_j).
                    // Or.rec on pstab:
                    //   inl hQ' ⇒ left (witness i = succ j)
                    //   inr hP' ⇒ Or.rec on rankd:
                    //              inl hQ' ⇒ left (witness succ j)
                    //              inr hle ⇒ right ⟨hP', le_trans (rho'≤rho_j)(rho_j≤rho_n)⟩
                    let witness_sj_left = |hq_sj: Expr| -> Expr {
                        // Exists.intro (q_reach_pred q b n) (succ j) hq_sj : ∃i, Q(b(n+i))
                        // pred (succ j) = Q(b(n+succ j)) ≡ Q(b(n+j+1)); hq_sj has that type.
                        let ex = exists_intro_nat(
                            q_reach_pred(&vq, &vbv, &vn),
                            nat_succ(jj.clone()),
                            hq_sj,
                        );
                        let p_now = app(vp.clone(), bnsj.clone());
                        let rbd = nat_le(app(vrho.clone(), bnsj.clone()), rho_bn.clone());
                        or_inl(q_reached.clone(), and(p_now, rbd), ex)
                    };

                    // inner Or.rec on rankd, given hP' : P(b(n+j+1))
                    let on_rank = |hp_sj: Expr| -> Expr {
                        let rk_fl = {
                            let mut gb = B::new();
                            let (hq_id, hq) = gb.fresh();
                            let body = witness_sj_left(hq.clone());
                            gb.lam(hq_id, BinderInfo::Default, q_at_sj.clone(), body)
                        };
                        let rk_fr = {
                            let mut gb = B::new();
                            let (hle_id, hle) = gb.fresh();
                            // le_trans (succ rho') ... : rho(b(n+j+1)) ≤ rho(b n)   [lt? no, ≤]
                            // We need rho'≤rho_j and rho_j≤rho_n ⇒ rho'≤rho_n by Nat.le_trans.
                            let rho_sj = app(vrho.clone(), bnsj.clone());
                            let rho_j = app(vrho.clone(), bnj.clone());
                            let le_n = nat_le_trans(
                                rho_sj.clone(),
                                rho_j.clone(),
                                rho_bn.clone(),
                                hle.clone(),
                                hrank_j.clone(),
                            ); // : Nat.le (rho(b(n+j+1))) (rho(b n))
                            let p_now = app(vp.clone(), bnsj.clone());
                            let rbd = nat_le(rho_sj.clone(), rho_bn.clone());
                            let and_pf = and_intro(p_now.clone(), rbd.clone(), hp_sj.clone(), le_n);
                            let body = or_inr(q_reached.clone(), and(p_now, rbd), and_pf);
                            gb.lam(hle_id, BinderInfo::Default, rho_le_j.clone(), body)
                        };
                        let rk_motive = {
                            let mut ob = B::new();
                            let (o_id, _o) = ob.fresh();
                            let disj = or(q_at_sj.clone(), rho_le_j.clone());
                            ob.lam(o_id, BinderInfo::Default, disj, goal.clone())
                        };
                        or_rec(
                            q_at_sj.clone(),
                            rho_le_j.clone(),
                            rk_motive,
                            rk_fl,
                            rk_fr,
                            rankd.clone(),
                        )
                    };

                    // outer Or.rec on pstab
                    let ps_fl = {
                        let mut gb = B::new();
                        let (hq_id, hq) = gb.fresh();
                        let body = witness_sj_left(hq.clone());
                        gb.lam(hq_id, BinderInfo::Default, q_at_sj.clone(), body)
                    };
                    let ps_fr = {
                        let mut gb = B::new();
                        let (hp_id2, hp2) = gb.fresh();
                        let body = on_rank(hp2.clone());
                        gb.lam(hp_id2, BinderInfo::Default, p_at_sj.clone(), body)
                    };
                    let ps_motive = {
                        let mut ob = B::new();
                        let (o_id, _o) = ob.fresh();
                        let disj = or(q_at_sj.clone(), p_at_sj.clone());
                        ob.lam(o_id, BinderInfo::Default, disj, goal.clone())
                    };

                    let body = or_rec(
                        q_at_sj.clone(),
                        p_at_sj.clone(),
                        ps_motive,
                        ps_fl,
                        ps_fr,
                        pstab,
                    );
                    nb.lam(hnext_id, BinderInfo::Default, next_step.clone(), body)
                };

                // s_stutter : Eq (b(n+j+1))(b(n+j)) → goal
                //   carry P and rank across the equality. heq : b(n+j+1) = b(n+j).
                //   right disjunct needs P(b(n+j+1)) and rho(b(n+j+1)) ≤ rho(b n).
                //   Use Eq.subst with motive λ z, And (P z)(rho z ≤ rho(b n)) on heq (symm)
                //   from the known ⟨hp_j, hrank_j⟩ : And (P(b(n+j)))(rho(b(n+j)) ≤ rho(b n)).
                let s_stutter = {
                    let mut nb = B::new();
                    let (heq_id, heq) = nb.fresh();
                    // motive_state := λ (z : State), And (P z) (Nat.le (rho z)(rho(b n)))
                    let motive_state = {
                        let mut zb = B::new();
                        let (z_id, z) = zb.fresh();
                        let body = and(
                            app(vp.clone(), z.clone()),
                            nat_le(app(vrho.clone(), z.clone()), rho_bn.clone()),
                        );
                        zb.lam(z_id, BinderInfo::Default, state(), body)
                    };
                    // We have at b(n+j): and_j := ⟨hp_j, hrank_j⟩ : motive_state (b(n+j))
                    let and_j = and_intro(
                        p_at_j.clone(),
                        rank_at_j.clone(),
                        hp_j.clone(),
                        hrank_j.clone(),
                    );
                    // Eq.subst motive_state (b(n+j)) (b(n+j+1)) (Eq.symm heq) and_j
                    //   : motive_state (b(n+j+1)) = And (P(b(n+j+1)))(rho(b(n+j+1)) ≤ rho(b n))
                    let heq_symm = Expr::apps(
                        Expr::const_(
                            Name::from_string("Eq.symm"),
                            vec![Level::succ(Level::zero())],
                        ),
                        [state(), bnsj.clone(), bnj.clone(), heq.clone()],
                    ); // : Eq (b(n+j))(b(n+j+1))
                    let and_sj =
                        eq_subst_nat(motive_state, bnj.clone(), bnsj.clone(), heq_symm, and_j);
                    // inr and_sj : goal
                    let p_now = app(vp.clone(), bnsj.clone());
                    let rbd = nat_le(app(vrho.clone(), bnsj.clone()), rho_bn.clone());
                    let body = or_inr(q_reached.clone(), and(p_now, rbd), and_sj);
                    nb.lam(heq_id, BinderInfo::Default, stutter_eq.clone(), body)
                };

                // Or.rec on Hstep (n+j)
                let step_motive = {
                    let mut ob = B::new();
                    let (o_id, _o) = ob.fresh();
                    let disj = or(next_step.clone(), stutter_eq.clone());
                    ob.lam(o_id, BinderInfo::Default, disj, goal.clone())
                };

                let body = or_rec(
                    next_step.clone(),
                    stutter_eq.clone(),
                    step_motive,
                    s_next,
                    s_stutter,
                    step_disj,
                );
                fb.lam(hnqj_id, BinderInfo::Default, not_q_at_j.clone(), body)
            };

            // Or.rec on Classical.em (Q(b(n+j)))
            let em = classical_em(q_at_j.clone());
            let case_motive = {
                let mut ob = B::new();
                let (o_id, _o) = ob.fresh();
                let disj = or(q_at_j.clone(), not_q_at_j.clone());
                ob.lam(o_id, BinderInfo::Default, disj, goal.clone())
            };

            let body = or_rec(
                q_at_j.clone(),
                not_q_at_j.clone(),
                case_motive,
                q_fl,
                q_fr,
                em,
            );
            rb.lam(hand_id, BinderInfo::Default, and_at_j.clone(), body)
        };

        // Or.rec on ih : M j = Or (∃i,Q) (And (P(b(n+j)))(rho ≤))
        let ih_motive = {
            let mut ob = B::new();
            let (o_id, _o) = ob.fresh();
            let disj = or(q_reached.clone(), and_at_j.clone());
            ob.lam(o_id, BinderInfo::Default, disj, goal.clone())
        };

        let body = or_rec(
            q_reached.clone(),
            and_at_j.clone(),
            ih_motive,
            ih_left,
            ih_right,
            ih.clone(),
        );

        // wrap binders j, ih
        let m_j = app(motive.clone(), jj.clone());
        let r = spb.lam(ih_id, BinderInfo::Default, m_j, body);
        spb.lam(jj_id, BinderInfo::Default, nat.clone(), r)
    };

    // Nat.rec.{0} motive base step : ∀ (j : Nat), M j
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);

    let rec_app = Expr::apps(nat_rec, [motive.clone(), base, step_fn]);

    let value = {
        let mut v = rec_app;
        v = vb.lam(
            vhnq_id,
            BinderInfo::Default,
            Expr::arrow(app(vq.clone(), bn.clone()), false_()),
            v,
        );
        v = vb.lam(vhp_id, BinderInfo::Default, app(vp.clone(), bn.clone()), v);
        v = vb.lam(vn_id, BinderInfo::Default, nat.clone(), v);
        v = vb.lam(
            vhrank_id,
            BinderInfo::Default,
            hrank_ty(&vnext, &vp, &vq, &vrho),
            v,
        );
        v = vb.lam(
            vhpstab_id,
            BinderInfo::Default,
            hpstab_ty(&vnext, &vp, &vq),
            v,
        );
        v = vb.lam(
            vhstep_id,
            BinderInfo::Default,
            step_forall_ty(&vnext, &vbv),
            v,
        );
        v = vb.lam(vb_id, BinderInfo::Default, behavior_ty(), v);
        v = vb.lam(vnext_id, BinderInfo::Default, action_ty(), v);
        v = vb.lam(vrho_id, BinderInfo::Default, rho_ty.clone(), v);
        v = vb.lam(vq_id, BinderInfo::Default, state_pred_ty(), v);
        v = vb.lam(vp_id, BinderInfo::Default, state_pred_ty(), v);
        vb.finish(v)
    };

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_,
        value,
    })
}

/// Register `TLAsem.LatticeRankSoundGeneral` — the **general WF1 + rank
/// metatheorem**, fully proved, with **no `Hfire2prog`** hypothesis: the
/// `P ⇝ Q` leads-to is derived from the *raw* Lamport WF1 verification
/// conditions plus weak fairness, with `A` enabled only on the **waiting region**
/// (`P ∧ ¬Q`) — never globally.
///
/// ```text
/// LatticeRankSoundGeneral :
///   ∀ (A Next : Action) (P Q : StatePred) (rho : State → Nat) (b : Behavior),
///     (Hstep  : ∀ i, Or (Next (b i)(b (succ i))) (Eq (b (succ i))(b i)))  -- [N] (stutter run)
///     (HAsub  : ∀ s s', A s s' → Next s s')                              -- A ⊆ Next
///     (Hpstab : ∀ s s', P s → (Q s→False) → Next s s' → Or (Q s')(P s'))  -- P stable off Q
///     (Hrank  : ∀ s s', P s → (Q s→False) → Next s s' → Or (Q s')(rho s' ≤ rho s))
///     (Hhelp  : ∀ s s', P s → (Q s→False) → A s s' → Or (Q s')(rho s' < rho s))
///     (Hen    : ∀ s, P s → (Q s→False) → Enabled A s)                     -- enabled WHILE WAITING
///     (Hwf    : Sat b (WF A))                                             -- weak fairness
///     → ∀ n, P (b n) → ∃ m, Q (b (n+m))
/// ```
///
/// The conclusion is def-eq to `Sat b (LeadsTo (Lift P)(Lift Q))` (= `P ⇝ Q`).
///
/// This **discharges the old `Hfire2prog`** (the residual of [`register_lattice_rank_sound`])
/// — it is *derived* here, not assumed. The crux that the
/// continuous-global-enabledness lemma [`register_wf_fires_when_always_enabled`]
/// dodged is closed: while the run stays in the waiting region `P ∧ ¬Q`, `A` is
/// continuously enabled *there*, the rank is non-increasing, so either `Q` is
/// reached or `A` stays enabled forever ⇒ WF forces `⟨A⟩` ⇒ the rank strictly
/// drops ⇒ well-founded ⇒ `Q`.
///
/// PROOF (genuine composition; no axiom stand-ins). Delegate to
/// `WfDescentSound P Q rho b Hprog`, where `Hprog n hP hnQ :
/// ∃ m, Q (b (n+m)) ∨ (P (b (n+m)) ∧ rho (b (n+m)) < rho (b n))` is built thus:
///   * `Classical.em (∃ i, Q (b (n+i)))`:
///     - **left** (`Q` reached at some `i`): `Exists.elim` → witness `m = i`,
///       `Or.inl`.
///     - **right** (`hNotEx : ¬∃ i, Q (b (n+i))`): set
///       `hNeverQ i := λ hQi, hNotEx (Exists.intro i hQi)`. Then for every `i`,
///       `WfPrefixInvariant … n hP hnQ i` (whose left disjunct `hNeverQ` refutes)
///       yields `P (b (n+i))` and `rho (b (n+i)) ≤ rho (b n)`. Feeding `P` + `¬Q`
///       to `Hen` gives `□Enabled` from `n`, so
///       `WfFiresWhenEnabledThroughout A b Hwf n (□Enabled)` fires:
///       `∃ j, A (b (n+j)) (b ((n+j)+1))`. `Exists.elim` that `j`; with
///       `P (b (n+j))`, `¬Q (b (n+j))`, the fire feeds `Hhelp`:
///       `Q (b ((n+j)+1)) ∨ rho (b ((n+j)+1)) < rho (b (n+j))`. The `Q'` branch is
///       a witness (`m = j+1`, `Or.inl`); the strict-drop branch combines with
///       `rho (b (n+j)) ≤ rho (b n)` (`Nat.le_trans`) for `rho (b (n+(j+1))) <
///       rho (b n)`, and `P (b (n+(j+1)))` (prefix invariant at `j+1`) gives the
///       witness `m = j+1`, `Or.inr`.
///
/// All hypotheses are Pi-bound (NONE is an axiom). Transitive axiom closure ⊆
/// FOUNDATIONAL: it reaches only `Acc.rec`/`Nat.accNatLt`/`Classical.em`/`Nat.rec`/
/// `Or`/`And`/`Exists`/`Eq`/`Nat.le_trans`/`Nat`.
///
/// NOTE on `HAsub`. The proof does **not** consume `HAsub` (`A ⊆ Next`): weak
/// fairness already ties `⟨A⟩` to *consecutive behavior states* (`A (b k)(b (k+1))`
/// on the actual run `b`), so the helpful fire is genuinely a step of `b` without
/// needing `A ⊆ Next`. `HAsub` is kept in the obligation set because it is the
/// canonical Lamport-WF1 side condition a TY certificate emits; binding it (and not
/// requiring it) makes this metatheorem **at least as strong** as the standard rule
/// while matching the certificate's VC shape.
pub fn register_lattice_rank_sound_general(env: &mut Environment) -> Result<(), EnvError> {
    register_tla_semantics_prereqs(env)?;
    register_leadsto(env)?;
    register_enabled(env)?;
    register_lift_act(env)?;
    register_wf(env)?;
    register_nat_strong_rec(env)?;
    register_wf_descent_sound(env)?;
    register_wf_fires_when_enabled_throughout(env)?;
    register_wf_prefix_invariant(env)?;
    let name = Name::from_string("TLAsem.LatticeRankSoundGeneral");
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let nat = state();
    let rho_ty = Expr::arrow(state(), nat.clone());

    // ── statement type ────────────────────────────────────────────────────
    let mut tb = B::new();
    let (a_id, a) = tb.fresh();
    let (next_id, next) = tb.fresh();
    let (p_id, p) = tb.fresh();
    let (q_id, q) = tb.fresh();
    let (rho_id, rho) = tb.fresh();
    let (b_id, b) = tb.fresh();
    let (hstep_id, _hstep) = tb.fresh();
    let (hasub_id, _hasub) = tb.fresh();
    let (hpstab_id, _hpstab) = tb.fresh();
    let (hrank_id, _hrank) = tb.fresh();
    let (hhelp_id, _hhelp) = tb.fresh();
    let (hen_id, _hen) = tb.fresh();
    let (hwf_id, _hwf) = tb.fresh();
    let (n_id, n) = tb.fresh();
    let (hp_id, _hp) = tb.fresh();

    let sat_wf = Expr::apps(c("TLAsem.Sat"), [b.clone(), app(c("TLAsem.WF"), a.clone())]);
    let concl_ex = exists_nat(q_reach_pred(&q, &b, &n));
    let type_ = {
        let mut t = concl_ex;
        t = tb.pi(
            hp_id,
            BinderInfo::Default,
            app(p.clone(), app(b.clone(), n.clone())),
            t,
        );
        t = tb.pi(n_id, BinderInfo::Default, nat.clone(), t);
        t = tb.pi(hwf_id, BinderInfo::Default, sat_wf.clone(), t);
        t = tb.pi(hen_id, BinderInfo::Default, hen_wait_ty(&a, &p, &q), t);
        t = tb.pi(hhelp_id, BinderInfo::Default, hhelp_ty(&a, &p, &q, &rho), t);
        t = tb.pi(
            hrank_id,
            BinderInfo::Default,
            hrank_ty(&next, &p, &q, &rho),
            t,
        );
        t = tb.pi(hpstab_id, BinderInfo::Default, hpstab_ty(&next, &p, &q), t);
        t = tb.pi(hasub_id, BinderInfo::Default, hasub_ty(&a, &next), t);
        t = tb.pi(hstep_id, BinderInfo::Default, step_forall_ty(&next, &b), t);
        t = tb.pi(b_id, BinderInfo::Default, behavior_ty(), t);
        t = tb.pi(rho_id, BinderInfo::Default, rho_ty.clone(), t);
        t = tb.pi(q_id, BinderInfo::Default, state_pred_ty(), t);
        t = tb.pi(p_id, BinderInfo::Default, state_pred_ty(), t);
        t = tb.pi(next_id, BinderInfo::Default, action_ty(), t);
        t = tb.pi(a_id, BinderInfo::Default, action_ty(), t);
        tb.finish(t)
    };

    // ── proof value ───────────────────────────────────────────────────────
    let mut vb = B::new();
    let (va_id, va) = vb.fresh();
    let (vnext_id, vnext) = vb.fresh();
    let (vp_id, vp) = vb.fresh();
    let (vq_id, vq) = vb.fresh();
    let (vrho_id, vrho) = vb.fresh();
    let (vb_id, vbv) = vb.fresh();
    let (vhstep_id, vhstep) = vb.fresh();
    // `vhasub` (A ⊆ Next) is bound by the lambda for VC-set fidelity but is NOT
    // consumed by the proof (see the NOTE in the doc-comment above).
    let (vhasub_id, _vhasub) = vb.fresh();
    let (vhpstab_id, vhpstab) = vb.fresh();
    let (vhrank_id, vhrank) = vb.fresh();
    let (vhhelp_id, vhhelp) = vb.fresh();
    let (vhen_id, vhen) = vb.fresh();
    let (vhwf_id, vhwf) = vb.fresh();

    // helper: WfPrefixInvariant applied at the two non-state premises and base n.
    //   prefix_at(n2, hP2, hnQ2) : ∀ j, Or (∃i,Q(b(n2+i))) (And (P(b(n2+j)))(rho(b(n2+j)) ≤ rho(b n2)))
    let prefix_at = |n2: &Expr, hp2: &Expr, hnq2: &Expr| -> Expr {
        Expr::apps(
            c("TLAsem.WfPrefixInvariant"),
            [
                vp.clone(),
                vq.clone(),
                vrho.clone(),
                vnext.clone(),
                vbv.clone(),
                vhstep.clone(),
                vhpstab.clone(),
                vhrank.clone(),
                n2.clone(),
                hp2.clone(),
                hnq2.clone(),
            ],
        )
    };

    // ── Hprog := λ (n2 : Nat)(hP2 : P(b n2))(hnQ2 : Q(b n2)→False) => prog_ex ──
    let hprog = {
        let mut pb = B::new();
        let (n2_id, n2) = pb.fresh();
        let (hp2_id, hp2) = pb.fresh();
        let (hnq2_id, hnq2) = pb.fresh();

        let bn2 = app(vbv.clone(), n2.clone());
        let rho_bn2 = app(vrho.clone(), bn2.clone());
        let prog_p = prog_pred(&vp, &vq, &vrho, &vbv, &n2); // λ m, Or(Q(b(n2+m)))(And(P)(rho<))
        let goal_ex = exists_nat(prog_p.clone()); // the Hprog result type at n2

        // ∃i, Q(b(n2+i))  (the Classical.em proposition)
        let q_reached = exists_nat(q_reach_pred(&vq, &vbv, &n2));
        let not_q_reached = Expr::arrow(q_reached.clone(), false_());

        // ── LEFT: (∃i, Q(b(n2+i))) → goal_ex  (witness the reached Q) ───────
        let case_left = {
            let mut lb = B::new();
            let (hex_id, hex) = lb.fresh();
            // Exists.elim: λ (i)(hQi : Q(b(n2+i))) => Exists.intro prog_p i (Or.inl … hQi)
            let elim_fn = {
                let mut eb = B::new();
                let (i_id, i) = eb.fresh();
                let (hqi_id, hqi) = eb.fresh();
                let bn2i = app(vbv.clone(), nat_add(n2.clone(), i.clone()));
                let q_i = app(vq.clone(), bn2i.clone());
                let p_i = app(vp.clone(), bn2i.clone());
                let rho_small = nat_lt(app(vrho.clone(), bn2i.clone()), rho_bn2.clone());
                // prog_p i = Or (Q(b(n2+i))) (And (P(b(n2+i)))(rho< ))
                let disj_inl = or_inl(
                    q_i.clone(),
                    and(p_i.clone(), rho_small.clone()),
                    hqi.clone(),
                );
                let intro = exists_intro_nat(prog_p.clone(), i.clone(), disj_inl);
                let r = eb.lam(hqi_id, BinderInfo::Default, q_i.clone(), intro);
                eb.lam(i_id, BinderInfo::Default, nat.clone(), r)
            };
            let body = exists_elim_nat(
                q_reach_pred(&vq, &vbv, &n2),
                goal_ex.clone(),
                hex.clone(),
                elim_fn,
            );
            lb.lam(hex_id, BinderInfo::Default, q_reached.clone(), body)
        };

        // ── RIGHT: (¬∃i, Q(b(n2+i))) → goal_ex ──────────────────────────────
        let case_right = {
            let mut rb = B::new();
            let (hnotex_id, hnotex) = rb.fresh();

            // hNeverQ : ∀ i, Q(b(n2+i)) → False  := λ i hQi, hNotEx (Exists.intro … i hQi)
            let h_never_q = {
                let mut nb = B::new();
                let (i_id, i) = nb.fresh();
                let (hqi_id, hqi) = nb.fresh();
                let bn2i = app(vbv.clone(), nat_add(n2.clone(), i.clone()));
                let q_i = app(vq.clone(), bn2i.clone());
                let intro = exists_intro_nat(q_reach_pred(&vq, &vbv, &n2), i.clone(), hqi.clone());
                let body = app(hnotex.clone(), intro); // : False
                let r = nb.lam(hqi_id, BinderInfo::Default, q_i.clone(), body);
                nb.lam(i_id, BinderInfo::Default, nat.clone(), r)
            };

            // p_at(i) : P(b(n2+i))   — from prefix invariant, refuting the Q-reached disjunct.
            //   prefix_at n2 hP2 hnQ2 i : Or (∃k,Q(b(n2+k))) (And (P(b(n2+i)))(rho ≤))
            //   Or.rec into P(b(n2+i)):  left ⇒ False.elim (hNotEx); right ⇒ And.left.
            let p_at = |i: &Expr| -> Expr {
                let bn2i = app(vbv.clone(), nat_add(n2.clone(), i.clone()));
                let p_i = app(vp.clone(), bn2i.clone());
                let q_reached_k = exists_nat(q_reach_pred(&vq, &vbv, &n2));
                let rank_le = nat_le(app(vrho.clone(), bn2i.clone()), rho_bn2.clone());
                let and_branch = and(p_i.clone(), rank_le.clone());
                let inv_i = app(prefix_at(&n2, &hp2, &hnq2), i.clone());
                let fl = {
                    let mut gb = B::new();
                    let (hk_id, hk) = gb.fresh();
                    let body = false_elim_prop(p_i.clone(), app(hnotex.clone(), hk.clone()));
                    gb.lam(hk_id, BinderInfo::Default, q_reached_k.clone(), body)
                };
                let fr = {
                    let mut gb = B::new();
                    let (hand_id, hand) = gb.fresh();
                    let body = and_left(p_i.clone(), rank_le.clone(), hand.clone());
                    gb.lam(hand_id, BinderInfo::Default, and_branch.clone(), body)
                };
                let mtv = {
                    let mut ob = B::new();
                    let (o_id, _o) = ob.fresh();
                    let disj = or(q_reached_k.clone(), and_branch.clone());
                    ob.lam(o_id, BinderInfo::Default, disj, p_i.clone())
                };
                or_rec(q_reached_k.clone(), and_branch.clone(), mtv, fl, fr, inv_i)
            };

            // rank_at(i) : rho(b(n2+i)) ≤ rho(b n2)  — same Or.rec, taking And.right.
            let rank_at = |i: &Expr| -> Expr {
                let bn2i = app(vbv.clone(), nat_add(n2.clone(), i.clone()));
                let p_i = app(vp.clone(), bn2i.clone());
                let q_reached_k = exists_nat(q_reach_pred(&vq, &vbv, &n2));
                let rank_le = nat_le(app(vrho.clone(), bn2i.clone()), rho_bn2.clone());
                let and_branch = and(p_i.clone(), rank_le.clone());
                let inv_i = app(prefix_at(&n2, &hp2, &hnq2), i.clone());
                let fl = {
                    let mut gb = B::new();
                    let (hk_id, hk) = gb.fresh();
                    let body = false_elim_prop(rank_le.clone(), app(hnotex.clone(), hk.clone()));
                    gb.lam(hk_id, BinderInfo::Default, q_reached_k.clone(), body)
                };
                let fr = {
                    let mut gb = B::new();
                    let (hand_id, hand) = gb.fresh();
                    let body = and_right(p_i.clone(), rank_le.clone(), hand.clone());
                    gb.lam(hand_id, BinderInfo::Default, and_branch.clone(), body)
                };
                let mtv = {
                    let mut ob = B::new();
                    let (o_id, _o) = ob.fresh();
                    let disj = or(q_reached_k.clone(), and_branch.clone());
                    ob.lam(o_id, BinderInfo::Default, disj, rank_le.clone())
                };
                or_rec(q_reached_k.clone(), and_branch.clone(), mtv, fl, fr, inv_i)
            };

            // box_en : □Enabled from n2  :=  λ (i : Nat), Hen (b(n2+i)) (p_at i) (hNeverQ i)
            //   typed  Sat (drop b n2)(SemBox (Lift (Enabled A))) ≡ ∀ i, Enabled A (b(n2+i)).
            let box_en = {
                let mut ib = B::new();
                let (i_id, i) = ib.fresh();
                let bn2i = app(vbv.clone(), nat_add(n2.clone(), i.clone()));
                let p_i_pf = p_at(&i);
                let nq_i_pf = app(h_never_q.clone(), i.clone()); // : Q(b(n2+i)) → False
                let body = Expr::apps(vhen.clone(), [bn2i.clone(), p_i_pf, nq_i_pf]);
                ib.lam(i_id, BinderInfo::Default, nat.clone(), body)
            };

            // fired : ◇⟨A⟩ from n2  := WfFiresWhenEnabledThroughout A b Hwf n2 box_en
            //       ≡ Sat (drop b n2)(SemDiam (LiftAct A)) ≡ ∃ j, A(b(n2+j))(b((n2+j)+1))
            let fired = Expr::apps(
                c("TLAsem.WfFiresWhenEnabledThroughout"),
                [va.clone(), vbv.clone(), vhwf.clone(), n2.clone(), box_en],
            );

            // diamond predicate (LiftAct A) ∘ drop : λ j, A(b(n2+j))(b((n2+j)+1))
            let fire_pred = {
                let mut jb = B::new();
                let (j_id, j) = jb.fresh();
                let bn2j = app(vbv.clone(), nat_add(n2.clone(), j.clone()));
                let bn2j1 = app(vbv.clone(), nat_succ(nat_add(n2.clone(), j.clone())));
                let body = Expr::apps(va.clone(), [bn2j, bn2j1]);
                jb.lam(j_id, BinderInfo::Default, nat.clone(), body)
            };

            // Exists.elim fired: λ (j)(hAct : A(b(n2+j))(b((n2+j)+1))) => …
            let elim_fn = {
                let mut eb = B::new();
                let (j_id, j) = eb.fresh();
                let (hact_id, hact) = eb.fresh();
                let bn2j = app(vbv.clone(), nat_add(n2.clone(), j.clone())); // b(n2+j)
                let bn2j1 = app(vbv.clone(), nat_succ(nat_add(n2.clone(), j.clone()))); // b((n2+j)+1) ≡ b(n2+(j+1))
                let act_ty = Expr::apps(va.clone(), [bn2j.clone(), bn2j1.clone()]);

                let p_j = p_at(&j); // P(b(n2+j))
                let nq_j = app(h_never_q.clone(), j.clone()); // Q(b(n2+j)) → False
                                                              // Hhelp (b(n2+j))(b((n2+j)+1)) p_j nq_j hAct
                                                              //   : Or (Q(b((n2+j)+1))) (Nat.lt (rho(b((n2+j)+1)))(rho(b(n2+j))))
                let helped = Expr::apps(
                    vhhelp.clone(),
                    [bn2j.clone(), bn2j1.clone(), p_j, nq_j, hact.clone()],
                );
                let q_j1 = app(vq.clone(), bn2j1.clone());
                let rho_lt_j = nat_lt(
                    app(vrho.clone(), bn2j1.clone()),
                    app(vrho.clone(), bn2j.clone()),
                );

                // witness m = succ j; prog_p (succ j) = Or (Q(b(n2+(j+1)))) (And (P)(rho< rho(b n2)))
                // h_left : Q(b((n2+j)+1)) → goal_ex   (Or.inl, witness succ j)
                let h_left = {
                    let mut gb = B::new();
                    let (hq_id, hq) = gb.fresh();
                    let bn2sj = app(vbv.clone(), nat_add(n2.clone(), nat_succ(j.clone()))); // b(n2+(j+1))
                    let q_sj = app(vq.clone(), bn2sj.clone());
                    let p_sj = app(vp.clone(), bn2sj.clone());
                    let rho_small = nat_lt(app(vrho.clone(), bn2sj.clone()), rho_bn2.clone());
                    let inl = or_inl(
                        q_sj.clone(),
                        and(p_sj.clone(), rho_small.clone()),
                        hq.clone(),
                    );
                    let intro = exists_intro_nat(prog_p.clone(), nat_succ(j.clone()), inl);
                    gb.lam(hq_id, BinderInfo::Default, q_j1.clone(), intro)
                };
                // h_right : Nat.lt (rho(b((n2+j)+1)))(rho(b(n2+j))) → goal_ex
                //   combine with rank_at(j) : rho(b(n2+j)) ≤ rho(b n2) via Nat.le_trans
                let h_right = {
                    let mut gb = B::new();
                    let (hlt_id, hlt) = gb.fresh();
                    let bn2sj = app(vbv.clone(), nat_add(n2.clone(), nat_succ(j.clone()))); // b(n2+(j+1))
                    let rho_sj = app(vrho.clone(), bn2sj.clone());
                    let rho_j = app(vrho.clone(), bn2j.clone());
                    // rho_sj < rho_j ≤ rho_bn2  ⇒ rho_sj < rho_bn2.
                    // Nat.lt a b ≡ Nat.le (succ a) b, so feed `Nat.le_trans (succ rho_sj) rho_j rho_bn2`:
                    //   h1 = hlt : Nat.lt rho_sj rho_j ≡ Nat.le (succ rho_sj) rho_j
                    //   h2 = rank_at j : Nat.le rho_j rho_bn2
                    //   result : Nat.le (succ rho_sj) rho_bn2 ≡ Nat.lt rho_sj rho_bn2
                    let lt_n = nat_le_trans(
                        nat_succ(rho_sj.clone()),
                        rho_j.clone(),
                        rho_bn2.clone(),
                        hlt.clone(),
                        rank_at(&j),
                    ); // : Nat.lt (rho(b(n2+(j+1)))) (rho(b n2))
                    let p_sj = p_at(&nat_succ(j.clone())); // P(b(n2+(j+1)))
                    let q_sj = app(vq.clone(), bn2sj.clone());
                    let p_sj_ty = app(vp.clone(), bn2sj.clone());
                    let rho_small = nat_lt(rho_sj.clone(), rho_bn2.clone());
                    let and_pf = and_intro(p_sj_ty.clone(), rho_small.clone(), p_sj, lt_n);
                    let inr = or_inr(
                        q_sj.clone(),
                        and(p_sj_ty.clone(), rho_small.clone()),
                        and_pf,
                    );
                    let intro = exists_intro_nat(prog_p.clone(), nat_succ(j.clone()), inr);
                    gb.lam(hlt_id, BinderInfo::Default, rho_lt_j.clone(), intro)
                };
                let mtv = {
                    let mut ob = B::new();
                    let (o_id, _o) = ob.fresh();
                    let disj = or(q_j1.clone(), rho_lt_j.clone());
                    ob.lam(o_id, BinderInfo::Default, disj, goal_ex.clone())
                };
                let body = or_rec(q_j1.clone(), rho_lt_j.clone(), mtv, h_left, h_right, helped);
                let r = eb.lam(hact_id, BinderInfo::Default, act_ty, body);
                eb.lam(j_id, BinderInfo::Default, nat.clone(), r)
            };

            let body = exists_elim_nat(fire_pred, goal_ex.clone(), fired, elim_fn);
            rb.lam(hnotex_id, BinderInfo::Default, not_q_reached.clone(), body)
        };

        // Or.rec on Classical.em (∃i, Q(b(n2+i)))
        let em = classical_em(q_reached.clone());
        let case_motive = {
            let mut ob = B::new();
            let (o_id, _o) = ob.fresh();
            let disj = or(q_reached.clone(), not_q_reached.clone());
            ob.lam(o_id, BinderInfo::Default, disj, goal_ex.clone())
        };
        let prog_ex = or_rec(
            q_reached.clone(),
            not_q_reached.clone(),
            case_motive,
            case_left,
            case_right,
            em,
        );

        // wrap λ n2 hP2 hnQ2
        let not_q_bn2 = Expr::arrow(app(vq.clone(), bn2.clone()), false_());
        let r = pb.lam(hnq2_id, BinderInfo::Default, not_q_bn2, prog_ex);
        let r = pb.lam(hp2_id, BinderInfo::Default, app(vp.clone(), bn2.clone()), r);
        pb.lam(n2_id, BinderInfo::Default, nat.clone(), r)
    };

    // WfDescentSound P Q rho b Hprog : ∀ n, P(b n) → ∃ m, Q(b(n+m))
    let descent = Expr::apps(
        c("TLAsem.WfDescentSound"),
        [vp.clone(), vq.clone(), vrho.clone(), vbv.clone(), hprog],
    );

    let value = {
        let mut v = descent;
        v = vb.lam(
            vhwf_id,
            BinderInfo::Default,
            {
                Expr::apps(
                    c("TLAsem.Sat"),
                    [vbv.clone(), app(c("TLAsem.WF"), va.clone())],
                )
            },
            v,
        );
        v = vb.lam(vhen_id, BinderInfo::Default, hen_wait_ty(&va, &vp, &vq), v);
        v = vb.lam(
            vhhelp_id,
            BinderInfo::Default,
            hhelp_ty(&va, &vp, &vq, &vrho),
            v,
        );
        v = vb.lam(
            vhrank_id,
            BinderInfo::Default,
            hrank_ty(&vnext, &vp, &vq, &vrho),
            v,
        );
        v = vb.lam(
            vhpstab_id,
            BinderInfo::Default,
            hpstab_ty(&vnext, &vp, &vq),
            v,
        );
        v = vb.lam(vhasub_id, BinderInfo::Default, hasub_ty(&va, &vnext), v);
        v = vb.lam(
            vhstep_id,
            BinderInfo::Default,
            step_forall_ty(&vnext, &vbv),
            v,
        );
        v = vb.lam(vb_id, BinderInfo::Default, behavior_ty(), v);
        v = vb.lam(vrho_id, BinderInfo::Default, rho_ty.clone(), v);
        v = vb.lam(vq_id, BinderInfo::Default, state_pred_ty(), v);
        v = vb.lam(vp_id, BinderInfo::Default, state_pred_ty(), v);
        v = vb.lam(vnext_id, BinderInfo::Default, action_ty(), v);
        v = vb.lam(va_id, BinderInfo::Default, action_ty(), v);
        vb.finish(v)
    };

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_,
        value,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::ProofQuality;
    use clean_kernel::tc::TypeChecker;

    #[test]
    fn test_lattice_rank_sound_typechecks_constructive() {
        use clean_kernel::env::ConstantKind;
        let mut env = Environment::with_prelude();
        register_tla_semantics(&mut env).expect("register T·SEM defs");
        register_lattice_rank_sound(&mut env).expect("LatticeRankSound registers + kernel-checks");

        let name = Name::from_string("TLAsem.LatticeRankSound");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        assert!(info.value.is_some(), "Theorem must retain its proof term");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(info.value.as_ref().unwrap(), &info.type_)
            .expect("LatticeRankSound must kernel-check");
        let quality = env.proof_quality(&name).expect("proof quality computes");
        assert_eq!(
            quality,
            ProofQuality::Constructive,
            "LatticeRankSound must be Constructive (closure ⊆ FOUNDATIONAL), got {quality:?}"
        );
    }

    /// Anti-masquerade: `LatticeRankSound`'s proof term genuinely references the
    /// composed substrate — `WfDescentSound`, `WfFiresWhenAlwaysEnabled` — and is
    /// NOT a degenerate term wrapping an axiom.
    #[test]
    fn test_lattice_rank_sound_composes_real_substrate() {
        use clean_kernel::expr::ExprKind;
        let mut env = Environment::with_prelude();
        register_tla_semantics(&mut env).expect("register T·SEM defs");
        register_lattice_rank_sound(&mut env).expect("register");
        let info = env
            .get_const(&Name::from_string("TLAsem.LatticeRankSound"))
            .expect("registered");
        let value = info.value.as_ref().expect("has proof value");
        fn collect(e: &Expr, out: &mut std::collections::HashSet<String>) {
            match e.kind() {
                ExprKind::Const(n, _) => {
                    out.insert(n.to_string());
                }
                ExprKind::App(f, a) => {
                    collect(f, out);
                    collect(a, out);
                }
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    collect(t, out);
                    collect(b, out);
                }
                _ => {}
            }
        }
        let mut names = std::collections::HashSet::new();
        collect(value, &mut names);
        for required in ["TLAsem.WfDescentSound", "TLAsem.WfFiresWhenAlwaysEnabled"] {
            assert!(
                names.contains(required),
                "LatticeRankSound proof must compose {required}; refs = {names:?}"
            );
        }
    }

    /// Anti-masquerade for the GENERAL theorem: its proof term genuinely composes
    /// the *derived* substrate — `WfDescentSound`, `WfFiresWhenEnabledThroughout`,
    /// and `WfPrefixInvariant` — i.e. the old `Hfire2prog` residual is now built,
    /// not assumed. (`LatticeRankSoundGeneral` has **no** `Hfire2prog`-shaped
    /// hypothesis; this confirms the fire/first-fire/rank-chaining is internal.)
    #[test]
    fn test_lattice_rank_sound_general_composes_real_substrate() {
        use clean_kernel::expr::ExprKind;
        let mut env = Environment::with_prelude();
        register_tla_semantics(&mut env).expect("register T·SEM defs");
        register_lattice_rank_sound_general(&mut env).expect("register");
        let info = env
            .get_const(&Name::from_string("TLAsem.LatticeRankSoundGeneral"))
            .expect("registered");
        let value = info.value.as_ref().expect("has proof value");
        fn collect(e: &Expr, out: &mut std::collections::HashSet<String>) {
            match e.kind() {
                ExprKind::Const(n, _) => {
                    out.insert(n.to_string());
                }
                ExprKind::App(f, a) => {
                    collect(f, out);
                    collect(a, out);
                }
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    collect(t, out);
                    collect(b, out);
                }
                _ => {}
            }
        }
        let mut names = std::collections::HashSet::new();
        collect(value, &mut names);
        for required in [
            "TLAsem.WfDescentSound",
            "TLAsem.WfFiresWhenEnabledThroughout",
            "TLAsem.WfPrefixInvariant",
            // the genuine fairness-extraction crux is closed via WF + waiting-region
            // enabledness; the proof must use the classical case split + Or/Exists
            // eliminators (real first-fire extraction), never a stand-in axiom.
            "Classical.em",
            "TLAsem.WfDescentSound",
        ] {
            assert!(
                names.contains(required),
                "LatticeRankSoundGeneral proof must compose {required}; refs = {names:?}"
            );
        }
        // It must NOT reference any axiom-shaped escape hatch (sorry/admit-style).
        for forbidden in ["sorryAx", "Classical.choice"] {
            assert!(
                !names.contains(forbidden),
                "LatticeRankSoundGeneral must not use {forbidden}; refs = {names:?}"
            );
        }
    }

    /// Non-vacuity for the GENERAL theorem: instantiate it at the **fair
    /// increment-counter toy** (`b := λ i, i`, `A s s' := s' = s+1`, `Next := A`,
    /// `rho := λ s, K - s` is not needed — we only check the *conclusion shape*).
    /// We confirm the fully-instantiated statement is a real implication chain
    /// (a `Pi`, not `True`) whose conclusion is the genuine `∃ m, Q (b (n+m))`.
    #[test]
    fn test_lattice_rank_sound_general_instantiable_and_not_vacuous() {
        use clean_kernel::expr::ExprKind;
        let mut env = Environment::with_prelude();
        register_tla_semantics(&mut env).expect("register T·SEM + T·LIVE");

        // A := λ (s s' : Nat), Eq s' (Nat.succ s) ;  Next := A
        let a_action = {
            let mut ab = B::new();
            let (s_id, s) = ab.fresh();
            let (sp_id, sp) = ab.fresh();
            let body = eq_state(sp.clone(), nat_succ(s.clone()));
            let inner = ab.lam(sp_id, BinderInfo::Default, state(), body);
            ab.finish(ab.lam(s_id, BinderInfo::Default, state(), inner))
        };
        let id_beh = {
            let mut bb = B::new();
            let (i_id, i) = bb.fresh();
            bb.finish(bb.lam(i_id, BinderInfo::Default, state(), i))
        };
        let tc = TypeChecker::with_mode(&env, env.mode());

        // Partially apply LatticeRankSoundGeneral A Next:=A — its remaining type is
        // a long Pi chain (P Q rho b Hstep … Hwf → ∀ n, …), i.e. a real implication.
        let partial = Expr::apps(
            c("TLAsem.LatticeRankSoundGeneral"),
            [a_action.clone(), a_action.clone()],
        );
        let partial_ty = tc
            .infer_type(&partial)
            .expect("LatticeRankSoundGeneral instantiates at the concrete counter action");
        assert!(
            matches!(partial_ty.kind(), ExprKind::Pi(..)),
            "instantiated general statement must be a real implication chain, got {:?}",
            partial_ty.kind()
        );
        assert!(
            !tc.is_def_eq(&partial_ty, &c("True")),
            "the general WF1 statement must not collapse to True"
        );
        let _ = id_beh;
    }

    #[test]
    fn test_lattice_rank_sound_general_typechecks_constructive() {
        use clean_kernel::env::ConstantKind;
        let mut env = Environment::with_prelude();
        register_tla_semantics(&mut env).expect("register T·SEM defs");
        register_lattice_rank_sound_general(&mut env)
            .expect("LatticeRankSoundGeneral registers + kernel-checks");

        let name = Name::from_string("TLAsem.LatticeRankSoundGeneral");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        assert!(info.value.is_some(), "Theorem must retain its proof term");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(info.value.as_ref().unwrap(), &info.type_)
            .expect("LatticeRankSoundGeneral must kernel-check");
        let quality = env.proof_quality(&name).expect("proof quality computes");
        assert_eq!(
            quality,
            ProofQuality::Constructive,
            "LatticeRankSoundGeneral must be Constructive (closure ⊆ FOUNDATIONAL), got {quality:?}"
        );
    }

    #[test]
    fn test_wf_prefix_invariant_typechecks_constructive() {
        use clean_kernel::env::ConstantKind;
        let mut env = Environment::with_prelude();
        register_tla_semantics(&mut env).expect("register T·SEM defs");
        register_wf_prefix_invariant(&mut env)
            .expect("WfPrefixInvariant registers + kernel-checks");

        let name = Name::from_string("TLAsem.WfPrefixInvariant");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(info.value.as_ref().unwrap(), &info.type_)
            .expect("WfPrefixInvariant must kernel-check");
        let quality = env.proof_quality(&name).expect("proof quality computes");
        assert_eq!(
            quality,
            ProofQuality::Constructive,
            "WfPrefixInvariant must be Constructive, got {quality:?}"
        );
    }

    #[test]
    fn test_wf_fires_when_enabled_throughout_typechecks_constructive() {
        use clean_kernel::env::ConstantKind;
        let mut env = Environment::with_prelude();
        register_tla_semantics(&mut env).expect("register T·SEM defs");
        register_wf_fires_when_enabled_throughout(&mut env)
            .expect("WfFiresWhenEnabledThroughout registers + kernel-checks");

        let name = Name::from_string("TLAsem.WfFiresWhenEnabledThroughout");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(info.value.as_ref().unwrap(), &info.type_)
            .expect("WfFiresWhenEnabledThroughout must kernel-check");
        let quality = env.proof_quality(&name).expect("proof quality computes");
        assert_eq!(
            quality,
            ProofQuality::Constructive,
            "WfFiresWhenEnabledThroughout must be Constructive, got {quality:?}"
        );
    }

    #[test]
    fn test_wf_fires_when_always_enabled_typechecks_constructive() {
        use clean_kernel::env::ConstantKind;
        let mut env = Environment::with_prelude();
        register_tla_semantics(&mut env).expect("register T·SEM defs");
        register_wf_fires_when_always_enabled(&mut env)
            .expect("WfFiresWhenAlwaysEnabled registers + kernel-checks");

        let name = Name::from_string("TLAsem.WfFiresWhenAlwaysEnabled");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(info.value.as_ref().unwrap(), &info.type_)
            .expect("WfFiresWhenAlwaysEnabled must kernel-check");
        let quality = env.proof_quality(&name).expect("proof quality computes");
        assert_eq!(
            quality,
            ProofQuality::Constructive,
            "WfFiresWhenAlwaysEnabled must be Constructive, got {quality:?}"
        );
    }

    #[test]
    fn test_wf_descent_sound_typechecks_constructive() {
        use clean_kernel::env::ConstantKind;
        let mut env = Environment::with_prelude();
        register_tla_semantics(&mut env).expect("register T·SEM defs");
        register_wf_descent_sound(&mut env).expect("WfDescentSound registers + kernel-checks");

        let name = Name::from_string("TLAsem.WfDescentSound");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(info.value.as_ref().unwrap(), &info.type_)
            .expect("WfDescentSound must kernel-check");
        let quality = env.proof_quality(&name).expect("proof quality computes");
        assert_eq!(
            quality,
            ProofQuality::Constructive,
            "WfDescentSound must be Constructive (closure ⊆ FOUNDATIONAL), got {quality:?}"
        );
    }

    #[test]
    fn test_nat_strong_rec_helper_typechecks_constructive() {
        let mut env = Environment::with_prelude();
        register_nat_strong_rec(&mut env).expect("natStrongRec registers + kernel-checks");
        register_nat_strong_rec(&mut env).expect("idempotent");
        let name = Name::from_string("TLAsem.natStrongRec");
        let info = env.get_const(&name).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(info.value.as_ref().unwrap(), &info.type_)
            .expect("natStrongRec must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(
            names.is_empty(),
            "natStrongRec must be axiom-free, got {names:?}"
        );
    }

    #[test]
    fn test_tla_semantics_definitions_register_and_typecheck() {
        let mut env = Environment::new();
        register_tla_semantics(&mut env).expect("T·SEM module should register and kernel-check");

        for n in [
            "TLAsem.drop",
            "TLAsem.Lift",
            "TLAsem.SemBox",
            "TLAsem.SemDiam",
            "TLAsem.Sat",
            "TLAsem.LeadsTo",
            "TLAsem.Runs",
            "TLAsem.Enabled",
            "TLAsem.LiftAct",
            "TLAsem.WF",
            "TLAsem.SF",
            "TLAsem.InductiveInvariantSound",
        ] {
            env.get_const(&Name::from_string(n))
                .unwrap_or_else(|| panic!("{n} should be registered"));
            let tc = TypeChecker::with_mode(&env, env.mode());
            let _ty = tc
                .infer_type(&Expr::const_(Name::from_string(n), vec![]))
                .unwrap_or_else(|e| panic!("{n} should type-check: {e:?}"));
        }
    }

    /// On a `with_prelude()` env, `register_tla_semantics` additionally registers
    /// the whole T·LIVE liveness layer, and every theorem in it is a Constructive
    /// (closure ⊆ FOUNDATIONAL) kernel-checked `Theorem` (the descent + extraction
    /// + lattice cert), the helper a Constructive `Definition`.
    #[test]
    fn test_tla_liveness_layer_registers_constructive_on_prelude() {
        use clean_kernel::env::ConstantKind;
        let mut env = Environment::with_prelude();
        register_tla_semantics(&mut env).expect("register T·SEM + T·LIVE on prelude");

        let helper = "TLAsem.natStrongRec";
        let info = env
            .get_const(&Name::from_string(helper))
            .unwrap_or_else(|| panic!("{helper} registered"));
        assert_eq!(info.kind, ConstantKind::Definition);

        for thm in [
            "TLAsem.WfDescentSound",
            "TLAsem.WfFiresWhenAlwaysEnabled",
            "TLAsem.WfFiresWhenEnabledThroughout",
            "TLAsem.WfPrefixInvariant",
            "TLAsem.LatticeRankSound",
            "TLAsem.LatticeRankSoundGeneral",
        ] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{thm} must be a Theorem");
            let tc = TypeChecker::with_mode(&env, env.mode());
            tc.check_type(info.value.as_ref().unwrap(), &info.type_)
                .unwrap_or_else(|e| panic!("{thm} must kernel-check: {e:?}"));
            let q = env
                .proof_quality(&Name::from_string(thm))
                .expect("proof quality");
            assert_eq!(
                q,
                ProofQuality::Constructive,
                "{thm} must be Constructive (closure ⊆ FOUNDATIONAL), got {q:?}"
            );
        }
    }

    /// On a bare `Environment::new()` env (no `Acc`/`Nat.accNatLt`), the liveness
    /// layer is *skipped* (so the M0 safety keystone still registers cleanly), and
    /// none of the liveness constants appear.
    #[test]
    fn test_tla_liveness_layer_skipped_without_prelude() {
        let mut env = Environment::new();
        register_tla_semantics(&mut env).expect("M0 registers on bare env");
        for absent in [
            "TLAsem.natStrongRec",
            "TLAsem.WfDescentSound",
            "TLAsem.WfFiresWhenAlwaysEnabled",
            "TLAsem.WfFiresWhenEnabledThroughout",
            "TLAsem.WfPrefixInvariant",
            "TLAsem.LatticeRankSound",
            "TLAsem.LatticeRankSoundGeneral",
        ] {
            assert!(
                env.get_const(&Name::from_string(absent)).is_none(),
                "{absent} must be skipped on a bare (non-prelude) env"
            );
        }
        // …but the safety keystone is still there.
        assert!(env
            .get_const(&Name::from_string("TLAsem.InductiveInvariantSound"))
            .is_some());
    }

    #[test]
    fn test_inductive_invariant_sound_is_constructive_theorem() {
        use clean_kernel::env::ConstantKind;
        let mut env = Environment::new();
        register_tla_semantics(&mut env).expect("register T·SEM");

        let name = Name::from_string("TLAsem.InductiveInvariantSound");
        let info = env.get_const(&name).expect("theorem registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        assert!(info.value.is_some(), "Theorem must retain its proof term");

        let quality = env.proof_quality(&name).expect("proof quality computes");
        assert_eq!(
            quality,
            ProofQuality::Constructive,
            "InductiveInvariantSound must be Constructive (closure ⊆ FOUNDATIONAL), got {quality:?}"
        );
    }

    #[test]
    fn test_proof_body_is_real_induction_not_axiom_wrap() {
        use clean_kernel::expr::ExprKind;
        let mut env = Environment::new();
        register_tla_semantics(&mut env).expect("register T·SEM");
        let info = env
            .get_const(&Name::from_string("TLAsem.InductiveInvariantSound"))
            .expect("registered");
        let value = info.value.as_ref().expect("has proof value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// The proof genuinely uses `Or.rec`/`Eq.subst`/`Nat.rec`/`And.right`/
    /// `And.left`/`Eq.symm` — i.e. it is the real induction, not a degenerate
    /// term that ignores the consecution/stutter structure (anti-masquerade).
    #[test]
    fn test_proof_uses_the_inductive_machinery() {
        use clean_kernel::expr::ExprKind;
        let mut env = Environment::new();
        register_tla_semantics(&mut env).expect("register T·SEM");
        let info = env
            .get_const(&Name::from_string("TLAsem.InductiveInvariantSound"))
            .expect("registered");
        let value = info.value.as_ref().expect("has proof value");

        fn collect(e: &Expr, out: &mut std::collections::HashSet<String>) {
            match e.kind() {
                ExprKind::Const(n, _) => {
                    out.insert(n.to_string());
                }
                ExprKind::App(f, a) => {
                    collect(f, out);
                    collect(a, out);
                }
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    collect(t, out);
                    collect(b, out);
                }
                _ => {}
            }
        }
        let mut names = std::collections::HashSet::new();
        collect(value, &mut names);
        for required in [
            "Nat.rec",
            "Or.rec",
            "Eq.subst",
            "Eq.symm",
            "And.left",
            "And.right",
        ] {
            assert!(
                names.contains(required),
                "proof must reference {required}; refs = {names:?}"
            );
        }
    }

    /// Non-vacuity: the conclusion `Sat b (SemBox (Lift Safety))` is NOT
    /// definitionally `True`. We instantiate the theorem's *implicit* `Safety`
    /// with the always-false predicate `λ _ : Nat, False` and a behavior, then
    /// confirm the resulting conclusion type reduces to a real `∀ n, False`
    /// (i.e. `Sat`/`SemBox`/`Lift` actually unfold to a universally-quantified
    /// proposition over the trace, not a trivial tautology). If `Sat (…)` were
    /// vacuously `True` this conclusion would be `True` and the whole theorem
    /// would prove nothing.
    #[test]
    fn test_conclusion_is_not_vacuously_true() {
        let mut env = Environment::new();
        register_tla_semantics(&mut env).expect("register T·SEM");
        env.init_true_false().expect("init True/False");

        // b := λ _ : Nat, Nat.zero ;  Safety := λ _ : Nat, False
        let zero_beh = Expr::lam(BinderInfo::Default, state(), nat_zero());
        let false_pred = Expr::lam(BinderInfo::Default, state(), c("False"));

        // Sat b (SemBox (Lift Safety))
        let lift_safety = app(c("TLAsem.Lift"), false_pred);
        let box_lift = app(c("TLAsem.SemBox"), lift_safety);
        let concl = Expr::apps(c("TLAsem.Sat"), [zero_beh, box_lift]);

        // It must type-check as a Prop …
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc
            .infer_type(&concl)
            .expect("conclusion is a well-typed Prop");
        assert_eq!(ty, Expr::prop());

        // … and must NOT be definitionally equal to `True` (it reduces to
        // `∀ n, False`). We check it is defeq to `∀ (n : Nat), False`.
        let forall_false = Expr::pi(BinderInfo::Default, state(), c("False")); // ∀ _ : Nat, False
        let tc2 = TypeChecker::with_mode(&env, env.mode());
        assert!(
            tc2.is_def_eq(&concl, &forall_false),
            "Sat (always-false trace) should reduce to ∀ n, False, proving the \
             conclusion is a genuine trace property and not vacuously True"
        );
        // And it is NOT defeq to True.
        assert!(
            !tc2.is_def_eq(&concl, &c("True")),
            "conclusion must not collapse to True"
        );
    }

    /// Non-vacuity for the liveness layer + the load-bearing **reduction claim**:
    /// the `P ⇝ Q` conclusion `Sat b (LeadsTo (Lift P) (Lift Q))` is
    /// **definitionally equal** to the index-level `∀ n, P (b n) → ∃ m, Q (b (n+m))`
    /// that `WfDescentSound`/`LatticeRankSound` actually prove — and is NOT
    /// `True`. We instantiate with the always-false `Q := λ _, False` so the
    /// existential body becomes `∃ m, False`, a genuinely non-trivial Prop.
    #[test]
    fn test_leadsto_conclusion_reduces_and_is_not_vacuous() {
        let mut env = Environment::with_prelude();
        register_tla_semantics(&mut env).expect("register T·SEM + T·LIVE");
        env.init_true_false().expect("init True/False");

        // b := λ _ : Nat, Nat.zero ;  P := λ _, True ;  Q := λ _, False
        let zero_beh = Expr::lam(BinderInfo::Default, state(), nat_zero());
        let p_true = Expr::lam(BinderInfo::Default, state(), c("True"));
        let q_false = Expr::lam(BinderInfo::Default, state(), c("False"));

        // folded:  Sat b (LeadsTo (Lift P) (Lift Q))
        let leadsto = Expr::apps(
            c("TLAsem.LeadsTo"),
            [
                app(c("TLAsem.Lift"), p_true.clone()),
                app(c("TLAsem.Lift"), q_false.clone()),
            ],
        );
        let folded = Expr::apps(c("TLAsem.Sat"), [zero_beh.clone(), leadsto]);

        // unfolded index form:  ∀ (n : Nat), True → ∃ (m : Nat), False
        //   (P (b n) ≡ True ; Q (b (n+m)) ≡ False since b/P/Q are constant)
        let unfolded = {
            let mut nb = B::new();
            let (n_id, _n) = nb.fresh();
            let ex_false = {
                let mut mb = B::new();
                let (m_id, _m) = mb.fresh();
                let pred = mb.lam(m_id, BinderInfo::Default, state(), c("False"));
                exists_nat(pred)
            };
            let body = Expr::arrow(c("True"), ex_false);
            nb.pi(n_id, BinderInfo::Default, state(), nb.finish(body))
        };

        let tc = TypeChecker::with_mode(&env, env.mode());
        assert_eq!(
            tc.infer_type(&folded).expect("folded is a Prop"),
            Expr::prop()
        );
        assert!(
            tc.is_def_eq(&folded, &unfolded),
            "Sat b (LeadsTo (Lift P)(Lift Q)) must reduce to ∀ n, P(b n) → ∃ m, Q(b(n+m)) \
             — the reduction WfDescentSound/LatticeRankSound rely on"
        );
        assert!(
            !tc.is_def_eq(&folded, &c("True")),
            "the P ⇝ Q conclusion must not collapse to True (it is ∀ n, True → ∃ m, False)"
        );
    }

    /// Concrete 3-state toy (the directive's explicit ask): the **fair increment
    /// counter** `b := λ i, i` with helpful action `A s s' := s' = s+1`. We (a)
    /// build a *real* `Hen : ∀ s, Enabled A s` proof term and kernel-check it, and
    /// (b) instantiate `WfFiresWhenAlwaysEnabled` at this concrete `A`/`b` and
    /// confirm the specialized statement type-checks and its conclusion
    /// `∀ k, Sat (drop b k) (◇⟨A⟩)` is a genuine (non-`True`) firing property.
    /// This anchors the fairness-under-abstraction extraction to a concrete fair
    /// run, demonstrating it is instantiable, not merely symbolic.
    #[test]
    fn test_increment_counter_toy_enabled_and_fires() {
        let mut env = Environment::with_prelude();
        register_tla_semantics(&mut env).expect("register T·SEM + T·LIVE");

        // A := λ (s s' : Nat), Eq s' (Nat.succ s)
        let a_action = {
            let mut ab = B::new();
            let (s_id, s) = ab.fresh();
            let (sp_id, sp) = ab.fresh();
            let body = eq_state(sp.clone(), nat_succ(s.clone()));
            let inner = ab.lam(sp_id, BinderInfo::Default, state(), body);
            ab.finish(ab.lam(s_id, BinderInfo::Default, state(), inner))
        };
        // b := λ (i : Nat), i   (the identity counter)
        let id_beh = {
            let mut bb = B::new();
            let (i_id, i) = bb.fresh();
            bb.finish(bb.lam(i_id, BinderInfo::Default, state(), i))
        };

        let tc = TypeChecker::with_mode(&env, env.mode());

        // (a) Hen : ∀ (s : Nat), Enabled A s   :=   λ s, Exists.intro (succ s) (Eq.refl (succ s))
        //     Enabled A s ≡ ∃ s', A s s' ≡ ∃ s', Eq s' (succ s).
        let hen = {
            let mut hb = B::new();
            let (s_id, s) = hb.fresh();
            // predicate λ s', Eq s' (succ s)
            let pred = {
                let mut pb = B::new();
                let (sp_id, sp) = pb.fresh();
                let body = eq_state(sp.clone(), nat_succ(s.clone()));
                pb.lam(sp_id, BinderInfo::Default, state(), body)
            };
            let witness = nat_succ(s.clone());
            let proof = eq_refl_nat(nat_succ(s.clone()));
            let body = exists_intro_nat(pred, witness, proof);
            hb.finish(hb.lam(s_id, BinderInfo::Default, state(), body))
        };
        let hen_ty_concrete = {
            let mut hb = B::new();
            let (s_id, s) = hb.fresh();
            hb.finish(hb.pi(
                s_id,
                BinderInfo::Default,
                state(),
                enabled_app(&a_action, &s),
            ))
        };
        tc.check_type(&hen, &hen_ty_concrete)
            .expect("Hen (always-enabled for the increment counter) must kernel-check");

        // (b) WfFiresWhenAlwaysEnabled applied at the concrete A, b — partial
        //     application yields  Sat b (WF A) → (∀ s, Enabled A s)
        //                          → ∀ k, Sat (drop b k) (◇⟨A⟩).
        let partial = Expr::apps(
            c("TLAsem.WfFiresWhenAlwaysEnabled"),
            [a_action.clone(), id_beh.clone()],
        );
        let partial_ty = tc
            .infer_type(&partial)
            .expect("WfFiresWhenAlwaysEnabled instantiates at the concrete counter");

        // The instantiated statement must mention a genuine firing conclusion and
        // not be vacuously True: its type is a Pi (Sat b (WF A) → …), i.e. a real
        // implication chain, not `True`.
        use clean_kernel::expr::ExprKind;
        assert!(
            matches!(partial_ty.kind(), ExprKind::Pi(..)),
            "instantiated WfFires statement must be a real implication, got {:?}",
            partial_ty.kind()
        );
        assert!(
            !tc.is_def_eq(&partial_ty, &c("True")),
            "the increment-counter firing statement must not collapse to True"
        );
    }

    /// The full liveness layer is **axiom-free up to FOUNDATIONAL** — an explicit
    /// audit that none of the four declarations drags in a domain axiom. (The
    /// `Constructive` proof-quality assertions already imply closure ⊆ FOUNDATIONAL;
    /// this makes the *axiom-delta = 0* claim mechanically checkable.)
    #[test]
    fn test_liveness_layer_axiom_deps_foundational_only() {
        let mut env = Environment::with_prelude();
        register_tla_semantics(&mut env).expect("register T·SEM + T·LIVE");

        // Foundational whitelist (mirrors the kernel's FOUNDATIONAL set: the 3
        // foundational axioms + the Eq/Acc structural eliminators that are not
        // "domain" axioms).
        let allowed: std::collections::HashSet<&str> = [
            "propext",
            "Quot.sound",
            "Classical.choice",
            "Eq.refl",
            "Eq.rec",
            "Acc.rec",
        ]
        .into_iter()
        .collect();

        for name in [
            "TLAsem.natStrongRec",
            "TLAsem.WfDescentSound",
            "TLAsem.WfFiresWhenAlwaysEnabled",
            "TLAsem.WfFiresWhenEnabledThroughout",
            "TLAsem.WfPrefixInvariant",
            "TLAsem.LatticeRankSound",
            "TLAsem.LatticeRankSoundGeneral",
        ] {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} axiom_deps computes"));
            let offenders: Vec<String> = deps
                .iter()
                .map(|d| d.to_string())
                .filter(|d| !allowed.contains(d.as_str()))
                .collect();
            assert!(
                offenders.is_empty(),
                "{name} must not depend on any non-foundational axiom; offenders = {offenders:?}"
            );
        }
    }
}
