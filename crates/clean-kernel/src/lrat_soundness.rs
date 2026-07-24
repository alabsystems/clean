// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PROVED soundness of the computational LRAT (RUP) checker
//! ([`crate::lrat_check`]).
//!
//! This module discharges `checkLrat_sound` as a kernel-checked
//! `Declaration::Theorem` whose transitive axiom closure is
//! `⊆ FOUNDATIONAL_AXIOMS`, in the SAME semantic vocabulary as
//! `checkRefutes3_sound` ([`crate::resolution_soundness`]): the model is a
//! total+exclusive literal-truth predicate (`resConsistent`/`resExclusive`),
//! clause satisfaction is `clauseOr`, DB satisfaction is `allSat`/`allSatTrie`,
//! and the conclusion is the SAME `Unsat cs`. Both checkers therefore share one
//! unsatisfiability notion.
//!
//! # Bool-only formulation (the trust-wp `List.Mem` escape)
//!
//! trust-wp's LRAT groundwork
//! (`~/trust-wp/verification/clean/lrat_soundness_foundation.lean`) documents
//! the RUP induction as blocked on Prop-level `List.Mem` (`∈`) resolution. The
//! development below is the pre-scoped Bool-only escape: every membership /
//! lookup / subsumption in the checker AND in the computational side of each
//! soundness statement is a Bool-valued recursive kernel `Definition`
//! (`clauseMem`, `trieGet`, `lratReduce`, `listIsNil`, `listNatIsCons`) — no
//! `List.Mem` appears anywhere. The only Prop-level structures are the model
//! folds (`clauseOr`, `allNotHolds`, `allSatTrie`), reused from / mirroring the
//! resolution layer.
//!
//! # What is PROVED (every one a kernel `Theorem`, closure ⊆ FOUNDATIONAL)
//!
//!   * `memAllNotHolds` — a Bool-membership hit in the falsified set refutes
//!     the literal (`clauseMem x F = true → allNotHolds H F → H x → False`).
//!   * `clauseOrDecide` — under a total+exclusive model, every clause is
//!     either satisfied or all-false (`Or (clauseOr H C) (allNotHolds H C)`) —
//!     the CONSTRUCTIVE case split that seeds the RUP argument with
//!     `F₀ = clause` (no classical reasoning, no negation pass).
//!   * `lratReduceSat` — dropping falsified literals preserves clause
//!     satisfaction: `clauseOr H D → clauseOr H (lratReduce F D)`.
//!   * `lratRupSound` — the propagation induction: if every literal in `F` is
//!     false yet `lratRup db hints F = true` (a hinted conflict was reached)
//!     under a satisfied DB, then `False`. Unit case: the reduct `u :: tail`
//!     (with `tail` all duplicate copies of `u`, discharged via
//!     `dropFalseSat`) must have `u` as its hint clause's satisfied literal,
//!     so `litNeg u` joins the falsified set; conflict case: the reduct `[]`
//!     contradicts `lratReduceSat`.
//!   * `checkLratStepSat` — the step bridge: an accepted step's clause is
//!     satisfied (`clauseOrDecide`'s all-false branch is killed by
//!     `lratRupSound`).
//!   * `goLratSound` — the trace-fold induction (mirror of `go3Sound`):
//!     `trieInsPreservesAllSat` threads the trie invariant over accepted
//!     clauses; the empty-clause endpoint is `listIsNilSat`.
//!   * `checkLrat_sound` — the top-level bridge:
//!     `checkLrat (initialTrie cs) (listLen cs) trace = true → Unsat cs`
//!     (with `Unsat cs` spelled δ-unfolded, exactly as `checkRefutes3_sound`).
//!
//! The absent-hint guard (`listNatIsCons (trieGet db h)`) is load-bearing in
//! `lratRupSound`: it kills the `trieGet = nil` disjunct of `trieGetSat`, which
//! would otherwise let a forged hint id fabricate a conflict from the
//! indistinguishable-from-empty absent clause.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::lrat_check::names as lnames;
use crate::name::Name;
use crate::resolution_check::names as rnames;
use crate::resolution_soundness::names as snames;
use crate::resolution_soundness::INITIAL_TRIE_ALL_SAT;
use crate::{BinderInfo, Declaration, EnvError, Environment, Expr, Level};

/// Names registered by the LRAT soundness layer.
pub mod names {
    /// `Clean.Res.allNotHolds : (Nat → Prop) → List Nat → Prop` — the And-fold
    /// of literal FALSITY over the falsified set (`And ((H l) → False) …`).
    pub const ALL_NOT_HOLDS: &str = "Clean.Res.allNotHolds";
    /// PROVED `Clean.Res.memAllNotHolds` — Bool membership in an all-false set
    /// refutes the literal.
    pub const MEM_ALL_NOT_HOLDS: &str = "Clean.Res.memAllNotHolds";
    /// PROVED `Clean.Res.clauseOrDecide` — every clause is satisfied or
    /// all-false under a total+exclusive model (the constructive RUP seed).
    pub const CLAUSE_OR_DECIDE: &str = "Clean.Res.clauseOrDecide";
    /// PROVED `Clean.Res.lratReduceSat` — dropping falsified literals preserves
    /// clause satisfaction.
    pub const LRAT_REDUCE_SAT: &str = "Clean.Res.lratReduceSat";
    /// PROVED `Clean.Res.lratRupSound` — the unit-propagation induction.
    pub const LRAT_RUP_SOUND: &str = "Clean.Res.lratRupSound";
    /// PROVED `Clean.Res.checkLratStepSat` — the step-level soundness bridge.
    pub const CHECK_LRAT_STEP_SAT: &str = "Clean.Res.checkLratStepSat";
    /// PROVED `Clean.Res.goLratSound` — the trace-fold induction helper.
    pub const GO_LRAT_SOUND: &str = "Clean.Res.goLratSound";
    /// PROVED `Clean.Res.checkLrat_sound` — the top-level soundness bridge:
    /// `checkLrat (initialTrie cs) (listLen cs) trace = true → Unsat cs`.
    pub const CHECK_LRAT_SOUND: &str = "Clean.Res.checkLrat_sound";
}

// ── small shared Expr helpers (mirrors resolution_soundness.rs; kept local) ────

fn nat_ty() -> Expr {
    Expr::const_str("Nat")
}
fn bool_ty() -> Expr {
    Expr::const_str("Bool")
}
fn btrue() -> Expr {
    Expr::const_str("Bool.true")
}
fn bfalse() -> Expr {
    Expr::const_str("Bool.false")
}
fn nat_succ(x: Expr) -> Expr {
    Expr::app(Expr::const_str("Nat.succ"), x)
}
fn u1() -> Level {
    Level::succ(Level::zero())
}
/// `@Eq.{u} ty x y`.
fn eq_at(u: Level, ty: Expr, x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![u]), [ty, x, y])
}
fn eq_bool(x: Expr, y: Expr) -> Expr {
    eq_at(u1(), bool_ty(), x, y)
}
/// `@Eq.refl.{u} ty x`.
fn eq_refl_at(u: Level, ty: Expr, x: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![u]), [ty, x])
}
/// `@Eq.symm.{u} ty a b h : Eq b a`.
fn eq_symm_at(u: Level, ty: Expr, a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![u]),
        [ty, a, b, h],
    )
}
fn false_c() -> Expr {
    Expr::const_str("False")
}
/// `False.elim.{u} C h`.
fn false_elim(u: Level, c: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![u]),
        [c, h],
    )
}
fn list_nat() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        nat_ty(),
    )
}
fn list_list_nat() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        list_nat(),
    )
}
fn holds_ty() -> Expr {
    Expr::arrow(nat_ty(), Expr::prop())
}
fn lit_neg(l: Expr) -> Expr {
    Expr::app(Expr::const_str(rnames::LIT_NEG), l)
}
fn clause_mem(x: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(rnames::CLAUSE_MEM), [x, c])
}
fn list_cons_nat(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [nat_ty(), h, t],
    )
}
fn list_nil_nat() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        nat_ty(),
    )
}
/// `Clean.Res.clauseOr Holds c : Prop`.
fn clause_or(holds: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.Res.clauseOr"), [holds, c])
}
/// `Clean.Res.allNotHolds Holds c : Prop`.
fn all_not_holds(holds: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::ALL_NOT_HOLDS), [holds, c])
}
fn or_t(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Or"), vec![]), [a, b])
}
fn or_inl(a: Expr, b: Expr, ha: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Or.inl"), vec![]),
        [a, b, ha],
    )
}
fn or_inr(a: Expr, b: Expr, hb: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Or.inr"), vec![]),
        [a, b, hb],
    )
}
fn and_t(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [a, b])
}
fn and_left(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [a, b, h],
    )
}
fn and_right(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.right"), vec![]),
        [a, b, h],
    )
}
fn and_intro(a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [a, b, ha, hb],
    )
}
/// `Or.rec` eliminating into a `Prop` motive `c`.
fn or_elim(a: Expr, b: Expr, c: Expr, fl: Expr, fr: Expr, hor: Expr) -> Expr {
    let motive = Expr::lam(BinderInfo::Default, or_t(a.clone(), b.clone()), c);
    Expr::apps(
        Expr::const_(Name::from_string("Or.rec"), vec![]),
        [a, b, motive, fl, fr, hor],
    )
}
/// `@Eq.subst.{1} α motive a b h m : motive b` (α a Sort-1 type: Bool/Nat/List …).
fn eq_subst1(alpha: Expr, motive: Expr, a: Expr, b: Expr, h: Expr, m: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![u1()]),
        [alpha, motive, a, b, h, m],
    )
}
/// Case-split on a `Bool`-typed `scrut` via the `Eq.refl` trick (Prop goal).
fn bool_cases(scrut: Expr, goal: Expr, case_f: Expr, case_t: Expr) -> Expr {
    let motive = {
        let inner = Expr::arrow(eq_bool(scrut.clone(), Expr::bvar(0)), goal);
        Expr::lam(BinderInfo::Default, bool_ty(), inner)
    };
    let rec = Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        [motive, case_f, case_t, scrut.clone()],
    );
    Expr::app(rec, eq_refl_at(u1(), bool_ty(), scrut))
}
/// Case-split on a `List Nat`-typed `scrut` via the `Eq.refl` trick (Prop goal):
/// `(List.rec.{0,0} Nat (motive := fun rr => Eq scrut rr → goal) case_nil case_cons
///   scrut) (Eq.refl scrut)`
/// with `case_nil : Eq scrut nil → goal` and
/// `case_cons : (u : Nat) → (tail : List Nat) → (Eq scrut tail → goal) →
///              Eq scrut (cons u tail) → goal` (the ih is usually unused).
fn list_nat_cases(scrut: Expr, goal: Expr, case_nil: Expr, case_cons: Expr) -> Expr {
    let motive = {
        let inner = Expr::arrow(eq_at(u1(), list_nat(), scrut.clone(), Expr::bvar(0)), goal);
        Expr::lam(BinderInfo::Default, list_nat(), inner)
    };
    let rec = Expr::apps(
        Expr::const_(
            Name::from_string("List.rec"),
            vec![Level::zero(), Level::zero()],
        ),
        [nat_ty(), motive, case_nil, case_cons, scrut.clone()],
    );
    Expr::app(rec, eq_refl_at(u1(), list_nat(), scrut))
}
/// From `h : Bool.and b1 b2 = true`, prove `b1 = true` (mirror of the
/// resolution_soundness helper; kept local to keep the modules independent).
fn bool_and_elim_left(b1: Expr, b2: Expr, h: Expr) -> Expr {
    let goal = eq_bool(b1.clone(), btrue());
    let and_motive = {
        let inner = eq_bool(
            Expr::apps(Expr::const_str("Bool.and"), [Expr::bvar(0), b2.clone()]),
            btrue(),
        );
        Expr::lam(BinderInfo::Default, bool_ty(), inner)
    };
    let case_f = {
        let heq_ty = eq_bool(b1.clone(), bfalse());
        let false_true = eq_subst1(
            bool_ty(),
            and_motive.clone(),
            b1.clone(),
            bfalse(),
            Expr::bvar(0),
            h.clone(),
        );
        let ff = tf_to_false(eq_symm_at(u1(), bool_ty(), bfalse(), btrue(), false_true));
        let body = false_elim(Level::zero(), goal.clone(), ff);
        Expr::lam(BinderInfo::Default, heq_ty, body)
    };
    let case_t = {
        let heq_ty = eq_bool(b1.clone(), btrue());
        Expr::lam(BinderInfo::Default, heq_ty, Expr::bvar(0))
    };
    bool_cases(b1, goal, case_f, case_t)
}
/// From `h : Bool.and b1 b2 = true`, prove `b2 = true`.
fn bool_and_elim_right(b1: Expr, b2: Expr, h: Expr) -> Expr {
    let goal = eq_bool(b2.clone(), btrue());
    let and_motive = {
        let inner = eq_bool(
            Expr::apps(Expr::const_str("Bool.and"), [Expr::bvar(0), b2.clone()]),
            btrue(),
        );
        Expr::lam(BinderInfo::Default, bool_ty(), inner)
    };
    let case_f = {
        let heq_ty = eq_bool(b1.clone(), bfalse());
        let false_true = eq_subst1(
            bool_ty(),
            and_motive.clone(),
            b1.clone(),
            bfalse(),
            Expr::bvar(0),
            h.clone(),
        );
        let ff = tf_to_false(eq_symm_at(u1(), bool_ty(), bfalse(), btrue(), false_true));
        let body = false_elim(Level::zero(), goal.clone(), ff);
        Expr::lam(BinderInfo::Default, heq_ty, body)
    };
    let case_t = {
        let heq_ty = eq_bool(b1.clone(), btrue());
        let body = eq_subst1(bool_ty(), and_motive, b1.clone(), btrue(), Expr::bvar(0), h);
        Expr::lam(BinderInfo::Default, heq_ty, body)
    };
    bool_cases(b1, goal, case_f, case_t)
}
/// `htf : Eq Bool.true Bool.false → False` (mirror; local).
fn tf_to_false(htf: Expr) -> Expr {
    let p = {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![u1()]);
        let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), Expr::prop());
        let body = Expr::apps(
            bool_rec,
            [
                inner_motive,
                false_c(),
                Expr::const_str("True"),
                Expr::bvar(0),
            ],
        );
        Expr::lam(BinderInfo::Default, bool_ty(), body)
    };
    Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![u1()]),
        [
            bool_ty(),
            p,
            btrue(),
            bfalse(),
            htf,
            Expr::const_str("True.intro"),
        ],
    )
}

// ── trie / LRAT-specific helpers ────────────────────────────────────────────────

fn trie_ty() -> Expr {
    Expr::const_str(rnames::TRIE)
}
fn trie_get(db: Expr, key: Expr) -> Expr {
    Expr::apps(Expr::const_str(rnames::TRIE_GET), [db, key])
}
fn all_sat_trie(holds: Expr, db: Expr) -> Expr {
    Expr::apps(Expr::const_str(snames::ALL_SAT_TRIE), [holds, db])
}
fn cons_pred(h: &Expr) -> Expr {
    Expr::app(Expr::const_str(snames::RES_CONSISTENT), h.clone())
}
fn excl_pred(h: &Expr) -> Expr {
    Expr::app(Expr::const_str(snames::RES_EXCLUSIVE), h.clone())
}
fn list_nat_is_cons(c: Expr) -> Expr {
    Expr::app(Expr::const_str(lnames::LIST_NAT_IS_CONS), c)
}
fn list_is_nil(c: Expr) -> Expr {
    Expr::app(Expr::const_str("Clean.Res.listIsNil"), c)
}
fn drop_lit(x: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(rnames::DROP_LIT), [x, c])
}
fn lrat_reduce(f: Expr, d: Expr) -> Expr {
    Expr::apps(Expr::const_str(lnames::LRAT_REDUCE), [f, d])
}
fn lrat_rup(db: Expr, hints: Expr, f: Expr) -> Expr {
    Expr::apps(Expr::const_str(lnames::LRAT_RUP), [db, hints, f])
}
fn list_lrat_step() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        Expr::const_str(lnames::LRAT_STEP),
    )
}
/// `(H l) → False` — literal falsity (the Bool-free side of `allNotHolds`).
fn not_holds(holds: &Expr, l: Expr) -> Expr {
    Expr::arrow(Expr::app(holds.clone(), l), false_c())
}
/// `Bool.rec (motive := fun _ => Bool) fcase tcase scrut` (data motive) — used
/// to SPELL the checker's reducts when transporting Bool equations.
fn bool_rec_bool(fcase: Expr, tcase: Expr, scrut: Expr) -> Expr {
    let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), bool_ty());
    Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![u1()]),
        [inner_motive, fcase, tcase, scrut],
    )
}

impl Environment {
    /// Register the PROVED LRAT (RUP) soundness layer and the `checkLrat_sound`
    /// theorem. Idempotent. Runs [`Environment::init_lrat_check`] and
    /// [`Environment::init_resolution_soundness`] (the shared semantic
    /// vocabulary + trie invariant lemmas) if absent.
    ///
    /// # Errors
    /// Propagates any [`EnvError`] from declaration insertion / kernel checking.
    pub fn init_lrat_soundness(&mut self) -> Result<(), EnvError> {
        self.init_lrat_check()?;
        self.init_resolution_soundness()?;
        self.register_all_not_holds()?;
        self.register_mem_all_not_holds()?;
        self.register_clause_or_decide()?;
        self.register_lrat_reduce_sat()?;
        self.register_lrat_rup_sound()?;
        self.register_check_lrat_step_sat()?;
        self.register_go_lrat_sound()?;
        self.register_check_lrat_sound_thm()
    }

    // ── §1 allNotHolds — the falsified-set invariant (a real Definition) ──────

    /// `allNotHolds H F := List.rec True (fun l _ ih => And ((H l) → False) ih) F`.
    fn register_all_not_holds(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::ALL_NOT_HOLDS))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::arrow(holds_ty(), Expr::arrow(list_nat(), Expr::prop()));
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (fid, f) = b.fresh_local(list_nat());
            // cons case : fun (l : Nat) (_ : List Nat) (ih : Prop) =>
            //   And ((H l) → False) ih
            let cons_case = {
                let head = not_holds(&holds, Expr::bvar(2));
                let and = and_t(head, Expr::bvar(0));
                Expr::lam(
                    BinderInfo::Default,
                    nat_ty(),
                    Expr::lam(
                        BinderInfo::Default,
                        list_nat(),
                        Expr::lam(BinderInfo::Default, Expr::prop(), and),
                    ),
                )
            };
            let rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(Level::zero()), Level::zero()],
            );
            let motive = Expr::lam(BinderInfo::Default, list_nat(), Expr::prop());
            let body = Expr::apps(
                rec,
                [nat_ty(), motive, Expr::const_str("True"), cons_case, f],
            );
            let e = b.mk_lam(fid, BinderInfo::Default, list_nat(), body);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(names::ALL_NOT_HOLDS),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    // ── §2 memAllNotHolds — Bool membership refutes the literal ───────────────

    /// `memAllNotHolds : (H)(x : Nat)(F : List Nat) →`
    /// `Eq (clauseMem x F) true → allNotHolds H F → (H x) → False`.
    ///
    /// `List.rec` on `F` (mirror of `memSat`'s induction). `nil` ⇒ the
    /// membership hypothesis is `false = true` (absurd). `cons l t` ⇒ split on
    /// `litBeq x l`: equal ⇒ `natBeqEq` transports `H x` to `H l`, refuted by
    /// the invariant's head; else the `Bool.or` rewrites to the tail membership
    /// and the IH recurses with the invariant's tail.
    fn register_mem_all_not_holds(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::MEM_ALL_NOT_HOLDS))
            .is_some()
        {
            return Ok(());
        }
        let mk_type = |holds: &Expr, x: &Expr, f: &Expr| -> Expr {
            Expr::arrow(
                eq_bool(clause_mem(x.clone(), f.clone()), btrue()),
                Expr::arrow(
                    all_not_holds(holds.clone(), f.clone()),
                    Expr::arrow(Expr::app(holds.clone(), x.clone()), false_c()),
                ),
            )
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (xid, x) = b.fresh_local(nat_ty());
            let (fid, f) = b.fresh_local(list_nat());
            let body = mk_type(&holds, &x, &f);
            let e = b.mk_pi(fid, BinderInfo::Default, list_nat(), body);
            let e = b.mk_pi(xid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (xid, x) = b.fresh_local(nat_ty());
            let (fid, f) = b.fresh_local(list_nat());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_nat());
                let body = mk_type(&holds, &x, &m);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_nat(), body))
            };
            // nil : fun (hmem : clauseMem x nil = true ≡ false = true)(_)(_) => absurd
            let nil_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let hmem_ty = eq_bool(clause_mem(x.clone(), list_nil_nat()), btrue());
                let (hmid, hm) = d.fresh_local(hmem_ty.clone());
                let hall_ty = all_not_holds(holds.clone(), list_nil_nat());
                let (haid, _ha) = d.fresh_local(hall_ty.clone());
                let hx_ty = Expr::app(holds.clone(), x.clone());
                let (hxid, _hx) = d.fresh_local(hx_ty.clone());
                let ff = tf_to_false(eq_symm_at(u1(), bool_ty(), bfalse(), btrue(), hm));
                let r = d.mk_lam(hxid, BinderInfo::Default, hx_ty, ff);
                let r = d.mk_lam(haid, BinderInfo::Default, hall_ty, r);
                d.finish_child(d.mk_lam(hmid, BinderInfo::Default, hmem_ty, r))
            };
            // cons l t ih : split on litBeq x l.
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (lid, l) = d.fresh_local(nat_ty());
                let (tid, t) = d.fresh_local(list_nat());
                let ih_ty = mk_type(&holds, &x, &t);
                let (ihid, ih) = d.fresh_local(ih_ty.clone());
                let cons_f = list_cons_nat(l.clone(), t.clone());
                let hmem_ty = eq_bool(clause_mem(x.clone(), cons_f.clone()), btrue());
                let (hmid, hm) = d.fresh_local(hmem_ty.clone());
                let hall_ty = all_not_holds(holds.clone(), cons_f.clone());
                let (haid, ha) = d.fresh_local(hall_ty.clone());
                let hx_ty = Expr::app(holds.clone(), x.clone());
                let (hxid, hx) = d.fresh_local(hx_ty.clone());

                let beq = Expr::apps(Expr::const_str(rnames::LIT_BEQ), [x.clone(), l.clone()]);
                let mem_t = clause_mem(x.clone(), t.clone());
                let head_ty = not_holds(&holds, l.clone());
                let tail_ty = all_not_holds(holds.clone(), t.clone());

                // case_t (heq : litBeq x l = true): x = l; H l; head refutes.
                let case_t = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let heq_ty = eq_bool(beq.clone(), btrue());
                    let (heqid, heq) = e.fresh_local(heq_ty.clone());
                    let xeql = Expr::apps(
                        Expr::const_str(snames::NAT_BEQ_EQ),
                        [x.clone(), l.clone(), heq],
                    );
                    let hl = eq_subst1(
                        nat_ty(),
                        holds.clone(),
                        x.clone(),
                        l.clone(),
                        xeql,
                        hx.clone(),
                    );
                    let not_hl = and_left(head_ty.clone(), tail_ty.clone(), ha.clone());
                    let body = Expr::app(not_hl, hl);
                    e.finish_child(e.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                };
                // case_f (heq : litBeq x l = false): tail membership; recurse.
                let case_f = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let heq_ty = eq_bool(beq.clone(), bfalse());
                    let (heqid, heq) = e.fresh_local(heq_ty.clone());
                    let rewrite_motive = {
                        let inner = eq_bool(
                            Expr::apps(Expr::const_str("Bool.or"), [Expr::bvar(0), mem_t.clone()]),
                            btrue(),
                        );
                        Expr::lam(BinderInfo::Default, bool_ty(), inner)
                    };
                    let mem_true = eq_subst1(
                        bool_ty(),
                        rewrite_motive,
                        beq.clone(),
                        bfalse(),
                        heq,
                        hm.clone(),
                    );
                    let ha_tail = and_right(head_ty.clone(), tail_ty.clone(), ha.clone());
                    let body = Expr::apps(ih.clone(), [mem_true, ha_tail, hx.clone()]);
                    e.finish_child(e.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                };
                let split = bool_cases(beq, false_c(), case_f, case_t);
                let r = d.mk_lam(hxid, BinderInfo::Default, hx_ty, split);
                let r = d.mk_lam(haid, BinderInfo::Default, hall_ty, r);
                let r = d.mk_lam(hmid, BinderInfo::Default, hmem_ty, r);
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                let r = d.mk_lam(tid, BinderInfo::Default, list_nat(), r);
                d.finish_child(d.mk_lam(lid, BinderInfo::Default, nat_ty(), r))
            };
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            );
            let folded = Expr::apps(list_rec, [nat_ty(), motive, nil_case, cons_case, f.clone()]);
            let e = b.mk_lam(fid, BinderInfo::Default, list_nat(), folded);
            let e = b.mk_lam(xid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::MEM_ALL_NOT_HOLDS),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §3 clauseOrDecide — satisfied or all-false (constructive) ─────────────

    /// `clauseOrDecide : (H) → resConsistent H → resExclusive H →`
    /// `(C : List Nat) → Or (clauseOr H C) (allNotHolds H C)`.
    ///
    /// `List.rec` on `C`. `nil` ⇒ right (`allNotHolds H nil ≡ True`). `cons l t`
    /// ⇒ `resConsistent` decides `l`: `H l` ⇒ left; `H (litNeg l)` ⇒
    /// `resExclusive` refutes `H l`, and the IH decides the tail. This is the
    /// CONSTRUCTIVE seed of the RUP argument — no classical case split.
    fn register_clause_or_decide(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::CLAUSE_OR_DECIDE))
            .is_some()
        {
            return Ok(());
        }
        let result_of = |holds: &Expr, c: &Expr| -> Expr {
            or_t(
                clause_or(holds.clone(), c.clone()),
                all_not_holds(holds.clone(), c.clone()),
            )
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (cid, _hc) = b.fresh_local(cons_pred(&holds));
            let (eid, _he) = b.fresh_local(excl_pred(&holds));
            let (clid, c) = b.fresh_local(list_nat());
            let body = result_of(&holds, &c);
            let r = b.mk_pi(clid, BinderInfo::Default, list_nat(), body);
            let r = b.mk_pi(eid, BinderInfo::Default, excl_pred(&holds), r);
            let r = b.mk_pi(cid, BinderInfo::Default, cons_pred(&holds), r);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), r))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (hcid, hcons) = b.fresh_local(cons_pred(&holds));
            let (heid, hexcl) = b.fresh_local(excl_pred(&holds));
            let (clid, c) = b.fresh_local(list_nat());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_nat());
                let body = result_of(&holds, &m);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_nat(), body))
            };
            // nil: Or.inr True.intro   (allNotHolds H nil ≡ True)
            let nil_case = or_inr(
                clause_or(holds.clone(), list_nil_nat()),
                all_not_holds(holds.clone(), list_nil_nat()),
                Expr::const_str("True.intro"),
            );
            // cons l t ih:
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (lid, l) = d.fresh_local(nat_ty());
                let (tid, t) = d.fresh_local(list_nat());
                let ih_ty = result_of(&holds, &t);
                let (ihid, ih) = d.fresh_local(ih_ty.clone());
                let cons_c = list_cons_nat(l.clone(), t.clone());
                let goal_l = clause_or(holds.clone(), cons_c.clone());
                let goal_r = all_not_holds(holds.clone(), cons_c.clone());
                let goal = or_t(goal_l.clone(), goal_r.clone());
                let hl_ty = Expr::app(holds.clone(), l.clone());
                let hnl_ty = Expr::app(holds.clone(), lit_neg(l.clone()));
                let co_t = clause_or(holds.clone(), t.clone());
                let an_t = all_not_holds(holds.clone(), t.clone());

                // case (hl : H l): Or.inl (Or.inl hl).
                let case_hl = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (hlid, hl) = e.fresh_local(hl_ty.clone());
                    let inner = or_inl(hl_ty.clone(), co_t.clone(), hl);
                    let body = or_inl(goal_l.clone(), goal_r.clone(), inner);
                    e.finish_child(e.mk_lam(hlid, BinderInfo::Default, hl_ty.clone(), body))
                };
                // case (hnl : H (litNeg l)): decide the tail via the IH.
                let case_hnl = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (hnlid, hnl) = e.fresh_local(hnl_ty.clone());
                    // tail satisfied ⇒ Or.inl (Or.inr ·)
                    let case_co = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let (coid, hco) = g.fresh_local(co_t.clone());
                        let inner = or_inr(hl_ty.clone(), co_t.clone(), hco);
                        let body = or_inl(goal_l.clone(), goal_r.clone(), inner);
                        g.finish_child(g.mk_lam(coid, BinderInfo::Default, co_t.clone(), body))
                    };
                    // tail all-false ⇒ Or.inr (And.intro (H l → False) ·) with the
                    // head refuted by resExclusive at l.
                    let case_an = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let (anid, han) = g.fresh_local(an_t.clone());
                        let not_hl = {
                            let mut k = EnvDeclBuilder::child_of(&g);
                            let (hlid, hl) = k.fresh_local(hl_ty.clone());
                            let body =
                                Expr::apps(Expr::app(hexcl.clone(), l.clone()), [hl, hnl.clone()]);
                            k.finish_child(k.mk_lam(hlid, BinderInfo::Default, hl_ty.clone(), body))
                        };
                        let pair =
                            and_intro(not_holds(&holds, l.clone()), an_t.clone(), not_hl, han);
                        let body = or_inr(goal_l.clone(), goal_r.clone(), pair);
                        g.finish_child(g.mk_lam(anid, BinderInfo::Default, an_t.clone(), body))
                    };
                    let body = or_elim(
                        co_t.clone(),
                        an_t.clone(),
                        goal.clone(),
                        case_co,
                        case_an,
                        ih.clone(),
                    );
                    e.finish_child(e.mk_lam(hnlid, BinderInfo::Default, hnl_ty.clone(), body))
                };
                let split = or_elim(
                    hl_ty,
                    hnl_ty,
                    goal,
                    case_hl,
                    case_hnl,
                    Expr::app(hcons.clone(), l.clone()),
                );
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, split);
                let r = d.mk_lam(tid, BinderInfo::Default, list_nat(), r);
                d.finish_child(d.mk_lam(lid, BinderInfo::Default, nat_ty(), r))
            };
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            );
            let folded = Expr::apps(list_rec, [nat_ty(), motive, nil_case, cons_case, c.clone()]);
            let r = b.mk_lam(clid, BinderInfo::Default, list_nat(), folded);
            let r = b.mk_lam(heid, BinderInfo::Default, excl_pred(&holds), r);
            let r = b.mk_lam(hcid, BinderInfo::Default, cons_pred(&holds), r);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::CLAUSE_OR_DECIDE),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §4 lratReduceSat — dropping falsified literals preserves sat ──────────

    /// `lratReduceSat : (H)(F : List Nat) → allNotHolds H F → (D : List Nat) →`
    /// `clauseOr H D → clauseOr H (lratReduce F D)`.
    ///
    /// `List.rec` on `D`. `nil` ⇒ vacuous. `cons d t` ⇒ split on
    /// `clauseMem d F`: a falsified `d` cannot be the satisfied literal
    /// (`memAllNotHolds`), so satisfaction lives in the tail either way; the
    /// branch proofs are transported along the case equations into the stuck
    /// `Bool.rec` reduct (the `checkStep3Sat` `Eq.subst` pattern).
    fn register_lrat_reduce_sat(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::LRAT_REDUCE_SAT))
            .is_some()
        {
            return Ok(());
        }
        let mk_concl = |holds: &Expr, f: &Expr, d: &Expr| -> Expr {
            Expr::arrow(
                clause_or(holds.clone(), d.clone()),
                clause_or(holds.clone(), lrat_reduce(f.clone(), d.clone())),
            )
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (fid, f) = b.fresh_local(list_nat());
            let hall_ty = all_not_holds(holds.clone(), f.clone());
            let (haid, _ha) = b.fresh_local(hall_ty.clone());
            let (did, d) = b.fresh_local(list_nat());
            let body = mk_concl(&holds, &f, &d);
            let r = b.mk_pi(did, BinderInfo::Default, list_nat(), body);
            let r = b.mk_pi(haid, BinderInfo::Default, hall_ty, r);
            let r = b.mk_pi(fid, BinderInfo::Default, list_nat(), r);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), r))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (fid, f) = b.fresh_local(list_nat());
            let hall_ty = all_not_holds(holds.clone(), f.clone());
            let (haid, hall) = b.fresh_local(hall_ty.clone());
            let (did, d_var) = b.fresh_local(list_nat());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_nat());
                let body = mk_concl(&holds, &f, &m);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_nat(), body))
            };
            // nil : fun (hco : clauseOr H nil ≡ False) => False.elim hco
            let nil_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let hco_ty = clause_or(holds.clone(), list_nil_nat());
                let (hcoid, hco) = d.fresh_local(hco_ty.clone());
                let goal = clause_or(holds.clone(), lrat_reduce(f.clone(), list_nil_nat()));
                let body = false_elim(Level::zero(), goal, hco);
                d.finish_child(d.mk_lam(hcoid, BinderInfo::Default, hco_ty, body))
            };
            // cons d t ih:
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (lid, lit) = d.fresh_local(nat_ty());
                let (tid, t) = d.fresh_local(list_nat());
                let ih_ty = mk_concl(&holds, &f, &t);
                let (ihid, ih) = d.fresh_local(ih_ty.clone());
                let cons_d = list_cons_nat(lit.clone(), t.clone());
                let hco_ty = clause_or(holds.clone(), cons_d.clone());
                let (hcoid, hco) = d.fresh_local(hco_ty.clone());

                let red_t = lrat_reduce(f.clone(), t.clone());
                let scrut = clause_mem(lit.clone(), f.clone());
                let goal = clause_or(holds.clone(), lrat_reduce(f.clone(), cons_d.clone()));
                // M bb := clauseOr H (Bool.rec (cons d red_t) red_t bb)
                let m_of = {
                    let keep = list_cons_nat(lit.clone(), red_t.clone());
                    let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), list_nat());
                    let brec = Expr::apps(
                        Expr::const_(Name::from_string("Bool.rec"), vec![u1()]),
                        [inner_motive, keep, red_t.clone(), Expr::bvar(0)],
                    );
                    Expr::lam(
                        BinderInfo::Default,
                        bool_ty(),
                        clause_or(holds.clone(), brec),
                    )
                };
                let hl_ty = Expr::app(holds.clone(), lit.clone());
                let co_t = clause_or(holds.clone(), t.clone());
                let co_red_t = clause_or(holds.clone(), red_t.clone());

                // case_t (heq : mem = true): d is falsified — satisfaction is in
                // the tail; the H d branch is absurd by memAllNotHolds.
                let case_t = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let heq_ty = eq_bool(scrut.clone(), btrue());
                    let (heqid, heq) = e.fresh_local(heq_ty.clone());
                    let case_hd = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let (hdid, hd) = g.fresh_local(hl_ty.clone());
                        let ff = Expr::apps(
                            Expr::const_str(names::MEM_ALL_NOT_HOLDS),
                            [
                                holds.clone(),
                                lit.clone(),
                                f.clone(),
                                heq.clone(),
                                hall.clone(),
                                hd,
                            ],
                        );
                        let body = false_elim(Level::zero(), co_red_t.clone(), ff);
                        g.finish_child(g.mk_lam(hdid, BinderInfo::Default, hl_ty.clone(), body))
                    };
                    let case_tail = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let (ctid, hct) = g.fresh_local(co_t.clone());
                        let body = Expr::app(ih.clone(), hct);
                        g.finish_child(g.mk_lam(ctid, BinderInfo::Default, co_t.clone(), body))
                    };
                    // : clauseOr H red_t ≡ M true; transport to M scrut ≡ goal.
                    let m_true = or_elim(
                        hl_ty.clone(),
                        co_t.clone(),
                        co_red_t.clone(),
                        case_hd,
                        case_tail,
                        hco.clone(),
                    );
                    let body = eq_subst1(
                        bool_ty(),
                        m_of.clone(),
                        btrue(),
                        scrut.clone(),
                        eq_symm_at(u1(), bool_ty(), scrut.clone(), btrue(), heq),
                        m_true,
                    );
                    e.finish_child(e.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                };
                // case_f (heq : mem = false): d is kept — inject into the cons.
                let case_f = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let heq_ty = eq_bool(scrut.clone(), bfalse());
                    let (heqid, heq) = e.fresh_local(heq_ty.clone());
                    let keep_or = or_t(hl_ty.clone(), co_red_t.clone());
                    let case_hd = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let (hdid, hd) = g.fresh_local(hl_ty.clone());
                        let body = or_inl(hl_ty.clone(), co_red_t.clone(), hd);
                        g.finish_child(g.mk_lam(hdid, BinderInfo::Default, hl_ty.clone(), body))
                    };
                    let case_tail = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let (ctid, hct) = g.fresh_local(co_t.clone());
                        let body =
                            or_inr(hl_ty.clone(), co_red_t.clone(), Expr::app(ih.clone(), hct));
                        g.finish_child(g.mk_lam(ctid, BinderInfo::Default, co_t.clone(), body))
                    };
                    // : Or (H d)(clauseOr H red_t) ≡ M false; transport to M scrut.
                    let m_false = or_elim(
                        hl_ty.clone(),
                        co_t.clone(),
                        keep_or,
                        case_hd,
                        case_tail,
                        hco.clone(),
                    );
                    let body = eq_subst1(
                        bool_ty(),
                        m_of.clone(),
                        bfalse(),
                        scrut.clone(),
                        eq_symm_at(u1(), bool_ty(), scrut.clone(), bfalse(), heq),
                        m_false,
                    );
                    e.finish_child(e.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                };
                let split = bool_cases(scrut, goal, case_f, case_t);
                let r = d.mk_lam(hcoid, BinderInfo::Default, hco_ty, split);
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                let r = d.mk_lam(tid, BinderInfo::Default, list_nat(), r);
                d.finish_child(d.mk_lam(lid, BinderInfo::Default, nat_ty(), r))
            };
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            );
            let folded = Expr::apps(
                list_rec,
                [nat_ty(), motive, nil_case, cons_case, d_var.clone()],
            );
            let r = b.mk_lam(did, BinderInfo::Default, list_nat(), folded);
            let r = b.mk_lam(haid, BinderInfo::Default, hall_ty, r);
            let r = b.mk_lam(fid, BinderInfo::Default, list_nat(), r);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::LRAT_REDUCE_SAT),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §5 lratRupSound — the unit-propagation induction ──────────────────────

    /// `lratRupSound : (H) → resConsistent H → resExclusive H → (db : Trie) →`
    /// `allSatTrie H db → (hints : List Nat) → (F : List Nat) →`
    /// `allNotHolds H F → Eq (lratRup db hints F) true → False`.
    ///
    /// `List.rec` on `hints` with `F` generalised (the falsified set grows by
    /// `litNeg u` at each unit). Per hint: `trieGetSat` + the `listNatIsCons`
    /// guard give `clauseOr H D`; `lratReduceSat` pushes satisfaction through
    /// the reduction; then a `List.rec` case split on the reduct `R`:
    ///
    ///   * `R = []` (conflict): `clauseOr H [] ≡ False` directly.
    ///   * `R = u :: tail` with `listIsNil (dropLit u tail) = true` (unit —
    ///     the tail is all duplicate copies of `u`): the satisfied literal of
    ///     `R` must be `u` (`dropFalseSat` + `listIsNilSat` kill the tail
    ///     disjunct), so `H (litNeg u)` is refuted by `resExclusive` — the
    ///     invariant extends and the IH recurses.
    ///   * `R = u :: tail` with a second distinct literal: the checker
    ///     returned `false` (absurd).
    fn register_lrat_rup_sound(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::LRAT_RUP_SOUND))
            .is_some()
        {
            return Ok(());
        }
        // motive over hints : fun hints => (F : List Nat) → allNotHolds H F →
        //   Eq (lratRup db hints F) true → False
        let mk_motive_body =
            |holds: &Expr, db: &Expr, hints: &Expr, parent: &EnvDeclBuilder| -> Expr {
                let mut c = EnvDeclBuilder::child_of(parent);
                let (fid, f) = c.fresh_local(list_nat());
                let inner = Expr::arrow(
                    all_not_holds(holds.clone(), f.clone()),
                    Expr::arrow(
                        eq_bool(lrat_rup(db.clone(), hints.clone(), f.clone()), btrue()),
                        false_c(),
                    ),
                );
                c.finish_child(c.mk_pi(fid, BinderInfo::Default, list_nat(), inner))
            };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (hcid, _hc) = b.fresh_local(cons_pred(&holds));
            let (heid, _he) = b.fresh_local(excl_pred(&holds));
            let (dbid, db) = b.fresh_local(trie_ty());
            let hall_ty = all_sat_trie(holds.clone(), db.clone());
            let (haid, _ha) = b.fresh_local(hall_ty.clone());
            let (hintsid, hints) = b.fresh_local(list_nat());
            let mb = mk_motive_body(&holds, &db, &hints, &b);
            let r = b.mk_pi(hintsid, BinderInfo::Default, list_nat(), mb);
            let r = b.mk_pi(haid, BinderInfo::Default, hall_ty, r);
            let r = b.mk_pi(dbid, BinderInfo::Default, trie_ty(), r);
            let r = b.mk_pi(heid, BinderInfo::Default, excl_pred(&holds), r);
            let r = b.mk_pi(hcid, BinderInfo::Default, cons_pred(&holds), r);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), r))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (hcid, hcons) = b.fresh_local(cons_pred(&holds));
            let (heid, hexcl) = b.fresh_local(excl_pred(&holds));
            let (dbid, db) = b.fresh_local(trie_ty());
            let hall_ty = all_sat_trie(holds.clone(), db.clone());
            let (haid, hall) = b.fresh_local(hall_ty.clone());
            let (hintsid, hints) = b.fresh_local(list_nat());

            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_nat());
                let body = mk_motive_body(&holds, &db, &m, &d);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_nat(), body))
            };
            // nil : fun (F)(_ : allNotHolds F)(hck : lratRup db nil F = true ≡ false = true)
            let nil_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (fid, f) = d.fresh_local(list_nat());
                let hf_ty = all_not_holds(holds.clone(), f.clone());
                let (hfid, _hf) = d.fresh_local(hf_ty.clone());
                let nil_hints = list_nil_nat();
                let hck_ty = eq_bool(lrat_rup(db.clone(), nil_hints, f.clone()), btrue());
                let (hckid, hck) = d.fresh_local(hck_ty.clone());
                let ff = tf_to_false(eq_symm_at(u1(), bool_ty(), bfalse(), btrue(), hck));
                let r = d.mk_lam(hckid, BinderInfo::Default, hck_ty, ff);
                let r = d.mk_lam(hfid, BinderInfo::Default, hf_ty, r);
                d.finish_child(d.mk_lam(fid, BinderInfo::Default, list_nat(), r))
            };
            // cons h rest ihf : fun (F)(hF)(hck) => …
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (hintid, hint) = d.fresh_local(nat_ty());
                let (restid, rest) = d.fresh_local(list_nat());
                let ihf_ty = mk_motive_body(&holds, &db, &rest, &d);
                let (ihfid, ihf) = d.fresh_local(ihf_ty.clone());
                let (fid, f) = d.fresh_local(list_nat());
                let hf_ty = all_not_holds(holds.clone(), f.clone());
                let (hfid, hf) = d.fresh_local(hf_ty.clone());
                let cons_hints = list_cons_nat(hint.clone(), rest.clone());
                let hck_ty = eq_bool(lrat_rup(db.clone(), cons_hints.clone(), f.clone()), btrue());
                let (hckid, hck) = d.fresh_local(hck_ty.clone());

                let d_cl = trie_get(db.clone(), hint.clone());
                let guard = list_nat_is_cons(d_cl.clone());
                let red = lrat_reduce(f.clone(), d_cl.clone());
                // BODY := List.rec (motive := fun _ => Bool) true bcons red — the
                // definitional reduct of the per-hint step (`lratRup`'s cons case).
                let body_bool = {
                    // bcons : fun (u)(tail)(_ihr) =>
                    //   Bool.rec false (lratRup db rest (cons (litNeg u) F))
                    //            (listIsNil (dropLit u tail))
                    //   bvars: _ihr=0, tail=1, u=2 ; db/rest/F are fvars.
                    let bcons = {
                        let u = Expr::bvar(2);
                        let tail = Expr::bvar(1);
                        let new_f = list_cons_nat(lit_neg(u.clone()), f.clone());
                        let go = lrat_rup(db.clone(), rest.clone(), new_f);
                        let inner = bool_rec_bool(bfalse(), go, list_is_nil(drop_lit(u, tail)));
                        Expr::lam(
                            BinderInfo::Default,
                            nat_ty(),
                            Expr::lam(
                                BinderInfo::Default,
                                list_nat(),
                                Expr::lam(BinderInfo::Default, bool_ty(), inner),
                            ),
                        )
                    };
                    let rec = Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::succ(Level::zero()), Level::zero()],
                    );
                    let inner_motive = Expr::lam(BinderInfo::Default, list_nat(), bool_ty());
                    Expr::apps(rec, [nat_ty(), inner_motive, btrue(), bcons, red.clone()])
                };

                let hguard = bool_and_elim_left(guard.clone(), body_bool.clone(), hck.clone());
                let hbody = bool_and_elim_right(guard.clone(), body_bool.clone(), hck);

                // clauseOr H D from trieGetSat; the nil disjunct is killed by the guard.
                let co_d = clause_or(holds.clone(), d_cl.clone());
                let eqnil = eq_at(u1(), list_nat(), d_cl.clone(), list_nil_nat());
                let h_d = {
                    let getsat = Expr::apps(
                        Expr::const_str(snames::TRIE_GET_SAT),
                        [holds.clone(), db.clone(), hall.clone(), hint.clone()],
                    );
                    let case_l = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (xid, xc) = e.fresh_local(co_d.clone());
                        e.finish_child(e.mk_lam(xid, BinderInfo::Default, co_d.clone(), xc))
                    };
                    let case_r = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (xid, xnil) = e.fresh_local(eqnil.clone());
                        let guard_motive = {
                            let inner = eq_bool(list_nat_is_cons(Expr::bvar(0)), btrue());
                            Expr::lam(BinderInfo::Default, list_nat(), inner)
                        };
                        let guard_nil = eq_subst1(
                            list_nat(),
                            guard_motive,
                            d_cl.clone(),
                            list_nil_nat(),
                            xnil,
                            hguard.clone(),
                        );
                        // : listNatIsCons nil = true ≡ false = true — absurd.
                        let ff =
                            tf_to_false(eq_symm_at(u1(), bool_ty(), bfalse(), btrue(), guard_nil));
                        let body = false_elim(Level::zero(), co_d.clone(), ff);
                        e.finish_child(e.mk_lam(xid, BinderInfo::Default, eqnil.clone(), body))
                    };
                    or_elim(co_d.clone(), eqnil, co_d.clone(), case_l, case_r, getsat)
                };
                // clauseOr H (lratReduce F D).
                let h_red = Expr::apps(
                    Expr::const_str(names::LRAT_REDUCE_SAT),
                    [holds.clone(), f.clone(), hf.clone(), d_cl.clone(), h_d],
                );

                // Case split on the reduct R (the Eq.refl List trick).
                let co_of = |c: Expr| clause_or(holds.clone(), c);
                // case_nil (hR : red = nil): clauseOr H nil ≡ False directly.
                let case_nil = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let hr_ty = eq_at(u1(), list_nat(), red.clone(), list_nil_nat());
                    let (hrid, hr) = e.fresh_local(hr_ty.clone());
                    let co_motive = {
                        let inner = co_of(Expr::bvar(0));
                        Expr::lam(BinderInfo::Default, list_nat(), inner)
                    };
                    let body = eq_subst1(
                        list_nat(),
                        co_motive,
                        red.clone(),
                        list_nil_nat(),
                        hr,
                        h_red.clone(),
                    );
                    e.finish_child(e.mk_lam(hrid, BinderInfo::Default, hr_ty, body))
                };
                // case_cons u tail _ih (hR : red = cons u tail):
                let case_cons = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (uid, u) = e.fresh_local(nat_ty());
                    let (tailid, tail) = e.fresh_local(list_nat());
                    let ihr_ty = Expr::arrow(
                        eq_at(u1(), list_nat(), red.clone(), tail.clone()),
                        false_c(),
                    );
                    let (ihrid, _ihr) = e.fresh_local(ihr_ty.clone());
                    let cons_ut = list_cons_nat(u.clone(), tail.clone());
                    let hr_ty = eq_at(u1(), list_nat(), red.clone(), cons_ut.clone());
                    let (hrid, hr) = e.fresh_local(hr_ty.clone());

                    // transport the Bool equation + the satisfaction along hR.
                    let body_motive = {
                        // fun rr => Eq (List.rec … true bcons rr) true — respell the
                        // same fold with the scrutinee abstracted.
                        let bcons = {
                            let uu = Expr::bvar(2);
                            let tt = Expr::bvar(1);
                            let new_f = list_cons_nat(lit_neg(uu.clone()), f.clone());
                            let go = lrat_rup(db.clone(), rest.clone(), new_f);
                            let inner = bool_rec_bool(bfalse(), go, list_is_nil(drop_lit(uu, tt)));
                            Expr::lam(
                                BinderInfo::Default,
                                nat_ty(),
                                Expr::lam(
                                    BinderInfo::Default,
                                    list_nat(),
                                    Expr::lam(BinderInfo::Default, bool_ty(), inner),
                                ),
                            )
                        };
                        let rec = Expr::const_(
                            Name::from_string("List.rec"),
                            vec![Level::succ(Level::zero()), Level::zero()],
                        );
                        let inner_motive = Expr::lam(BinderInfo::Default, list_nat(), bool_ty());
                        let fold = Expr::apps(
                            rec,
                            [nat_ty(), inner_motive, btrue(), bcons, Expr::bvar(0)],
                        );
                        Expr::lam(BinderInfo::Default, list_nat(), eq_bool(fold, btrue()))
                    };
                    let hbody2 = eq_subst1(
                        list_nat(),
                        body_motive,
                        red.clone(),
                        cons_ut.clone(),
                        hr.clone(),
                        hbody.clone(),
                    );
                    let co_motive = {
                        let inner = co_of(Expr::bvar(0));
                        Expr::lam(BinderInfo::Default, list_nat(), inner)
                    };
                    let hco2 = eq_subst1(
                        list_nat(),
                        co_motive,
                        red.clone(),
                        cons_ut.clone(),
                        hr.clone(),
                        h_red.clone(),
                    );

                    let scrut2 = list_is_nil(drop_lit(u.clone(), tail.clone()));
                    let new_f = list_cons_nat(lit_neg(u.clone()), f.clone());
                    let rup_next = lrat_rup(db.clone(), rest.clone(), new_f.clone());
                    let m2 = {
                        let inner = eq_bool(
                            bool_rec_bool(bfalse(), rup_next.clone(), Expr::bvar(0)),
                            btrue(),
                        );
                        Expr::lam(BinderInfo::Default, bool_ty(), inner)
                    };
                    // case2_f (h2 : listIsNil (dropLit u tail) = false): the reduct
                    // has a second DISTINCT literal — checker returned false.
                    let case2_f = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let h2_ty = eq_bool(scrut2.clone(), bfalse());
                        let (h2id, h2) = g.fresh_local(h2_ty.clone());
                        let false_true = eq_subst1(
                            bool_ty(),
                            m2.clone(),
                            scrut2.clone(),
                            bfalse(),
                            h2,
                            hbody2.clone(),
                        );
                        let body =
                            tf_to_false(eq_symm_at(u1(), bool_ty(), bfalse(), btrue(), false_true));
                        g.finish_child(g.mk_lam(h2id, BinderInfo::Default, h2_ty, body))
                    };
                    // case2_t (h2 : listIsNil (dropLit u tail) = true): unit (the
                    // tail is all duplicate copies of u) — extend F, recurse.
                    let case2_t = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let h2_ty = eq_bool(scrut2.clone(), btrue());
                        let (h2id, h2) = g.fresh_local(h2_ty.clone());
                        let hrup = eq_subst1(
                            bool_ty(),
                            m2.clone(),
                            scrut2.clone(),
                            btrue(),
                            h2.clone(),
                            hbody2.clone(),
                        );
                        // H (litNeg u) → False: the satisfied literal of (u :: tail)
                        // must be u — if it lived in the tail, dropFalseSat (u is
                        // refuted under H (litNeg u)) would leave dropLit u tail
                        // satisfied, contradicting listIsNilSat — and resExclusive
                        // refutes u against litNeg u.
                        let hu_ty = Expr::app(holds.clone(), u.clone());
                        let hnu_ty = Expr::app(holds.clone(), lit_neg(u.clone()));
                        let co_tail = clause_or(holds.clone(), tail.clone());
                        let not_u = {
                            let mut k = EnvDeclBuilder::child_of(&g);
                            let (hnuid, hnu) = k.fresh_local(hnu_ty.clone());
                            let case_u = {
                                let mut k2 = EnvDeclBuilder::child_of(&k);
                                let (huid, hu) = k2.fresh_local(hu_ty.clone());
                                let body = Expr::apps(
                                    Expr::app(hexcl.clone(), u.clone()),
                                    [hu, hnu.clone()],
                                );
                                k2.finish_child(k2.mk_lam(
                                    huid,
                                    BinderInfo::Default,
                                    hu_ty.clone(),
                                    body,
                                ))
                            };
                            let case_tail = {
                                let mut k2 = EnvDeclBuilder::child_of(&k);
                                let (ctid, hct) = k2.fresh_local(co_tail.clone());
                                // (H u → False) from hnu via resExclusive.
                                let not_hu = {
                                    let mut k3 = EnvDeclBuilder::child_of(&k2);
                                    let (huid, hu) = k3.fresh_local(hu_ty.clone());
                                    let body = Expr::apps(
                                        Expr::app(hexcl.clone(), u.clone()),
                                        [hu, hnu.clone()],
                                    );
                                    k3.finish_child(k3.mk_lam(
                                        huid,
                                        BinderInfo::Default,
                                        hu_ty.clone(),
                                        body,
                                    ))
                                };
                                // clauseOr H (dropLit u tail): duplicates of the
                                // refuted u drop away, satisfaction survives.
                                let dropped_sat = Expr::apps(
                                    Expr::const_str(snames::DROP_FALSE_SAT),
                                    [holds.clone(), u.clone(), tail.clone(), hct, not_hu],
                                );
                                let body = Expr::apps(
                                    Expr::const_str(snames::LIST_IS_NIL_SAT),
                                    [
                                        holds.clone(),
                                        drop_lit(u.clone(), tail.clone()),
                                        h2.clone(),
                                        dropped_sat,
                                    ],
                                );
                                k2.finish_child(k2.mk_lam(
                                    ctid,
                                    BinderInfo::Default,
                                    co_tail.clone(),
                                    body,
                                ))
                            };
                            let body = or_elim(
                                hu_ty.clone(),
                                co_tail.clone(),
                                false_c(),
                                case_u,
                                case_tail,
                                hco2.clone(),
                            );
                            k.finish_child(k.mk_lam(
                                hnuid,
                                BinderInfo::Default,
                                hnu_ty.clone(),
                                body,
                            ))
                        };
                        let hf2 = and_intro(
                            not_holds(&holds, lit_neg(u.clone())),
                            all_not_holds(holds.clone(), f.clone()),
                            not_u,
                            hf.clone(),
                        );
                        // ihf newF hf2 hrup : False
                        let body = Expr::apps(ihf.clone(), [new_f.clone(), hf2, hrup]);
                        g.finish_child(g.mk_lam(h2id, BinderInfo::Default, h2_ty, body))
                    };
                    let split = bool_cases(scrut2, false_c(), case2_f, case2_t);
                    let r = e.mk_lam(hrid, BinderInfo::Default, hr_ty, split);
                    let r = e.mk_lam(ihrid, BinderInfo::Default, ihr_ty, r);
                    let r = e.mk_lam(tailid, BinderInfo::Default, list_nat(), r);
                    e.finish_child(e.mk_lam(uid, BinderInfo::Default, nat_ty(), r))
                };
                let split = list_nat_cases(red.clone(), false_c(), case_nil, case_cons);
                let r = d.mk_lam(hckid, BinderInfo::Default, hck_ty, split);
                let r = d.mk_lam(hfid, BinderInfo::Default, hf_ty, r);
                let r = d.mk_lam(fid, BinderInfo::Default, list_nat(), r);
                let r = d.mk_lam(ihfid, BinderInfo::Default, ihf_ty, r);
                let r = d.mk_lam(restid, BinderInfo::Default, list_nat(), r);
                d.finish_child(d.mk_lam(hintid, BinderInfo::Default, nat_ty(), r))
            };
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            );
            let folded = Expr::apps(
                list_rec,
                [nat_ty(), motive, nil_case, cons_case, hints.clone()],
            );
            let r = b.mk_lam(hintsid, BinderInfo::Default, list_nat(), folded);
            let r = b.mk_lam(haid, BinderInfo::Default, hall_ty, r);
            let r = b.mk_lam(dbid, BinderInfo::Default, trie_ty(), r);
            let r = b.mk_lam(heid, BinderInfo::Default, excl_pred(&holds), r);
            let r = b.mk_lam(hcid, BinderInfo::Default, cons_pred(&holds), r);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::LRAT_RUP_SOUND),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §6 checkLratStepSat — the step-level soundness bridge ─────────────────

    /// `checkLratStepSat : (H) → (db : Trie) → (s : LratStep) →`
    /// `resConsistent H → resExclusive H → allSatTrie H db →`
    /// `Eq (checkLratStep db s) true → clauseOr H (lratStepClause s)`.
    ///
    /// `clauseOrDecide` splits the recorded clause: satisfied ⇒ done; all-false
    /// ⇒ the clause IS a valid falsified seed `F₀`, so `lratRupSound` turns the
    /// accepted propagation into `False`.
    fn register_check_lrat_step_sat(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::CHECK_LRAT_STEP_SAT))
            .is_some()
        {
            return Ok(());
        }
        let step_ty = Expr::const_str(lnames::LRAT_STEP);
        let check_step =
            |db: Expr, s: Expr| Expr::apps(Expr::const_str(lnames::CHECK_LRAT_STEP), [db, s]);
        let step_clause = |s: Expr| Expr::app(Expr::const_str(lnames::LRAT_STEP_CLAUSE), s);

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (dbid, db) = b.fresh_local(trie_ty());
            let (sid, s) = b.fresh_local(step_ty.clone());
            let concl = clause_or(holds.clone(), step_clause(s.clone()));
            let inner = Expr::arrow(eq_bool(check_step(db.clone(), s.clone()), btrue()), concl);
            let inner = Expr::arrow(all_sat_trie(holds.clone(), db.clone()), inner);
            let inner = Expr::arrow(excl_pred(&holds), inner);
            let inner = Expr::arrow(cons_pred(&holds), inner);
            let e = b.mk_pi(sid, BinderInfo::Default, step_ty.clone(), inner);
            let e = b.mk_pi(dbid, BinderInfo::Default, trie_ty(), e);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (dbid, db) = b.fresh_local(trie_ty());
            let (sid, s) = b.fresh_local(step_ty.clone());
            let (hcid, hcons) = b.fresh_local(cons_pred(&holds));
            let (heid, hexcl) = b.fresh_local(excl_pred(&holds));
            let (haid, hall) = b.fresh_local(all_sat_trie(holds.clone(), db.clone()));

            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(step_ty.clone());
                let body = Expr::arrow(
                    eq_bool(check_step(db.clone(), m.clone()), btrue()),
                    clause_or(holds.clone(), step_clause(m.clone())),
                );
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, step_ty.clone(), body))
            };
            // mk clause hints:
            let mk_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (cid, clause) = d.fresh_local(list_nat());
                let (hintsid, hints) = d.fresh_local(list_nat());
                let step_e = Expr::apps(
                    Expr::const_str(lnames::LRAT_STEP_MK),
                    [clause.clone(), hints.clone()],
                );
                let hck_ty = eq_bool(check_step(db.clone(), step_e), btrue());
                let (hckid, hck) = d.fresh_local(hck_ty.clone());

                let co_c = clause_or(holds.clone(), clause.clone());
                let an_c = all_not_holds(holds.clone(), clause.clone());
                let decide = Expr::apps(
                    Expr::const_str(names::CLAUSE_OR_DECIDE),
                    [holds.clone(), hcons.clone(), hexcl.clone(), clause.clone()],
                );
                let case_sat = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (xid, xc) = e.fresh_local(co_c.clone());
                    e.finish_child(e.mk_lam(xid, BinderInfo::Default, co_c.clone(), xc))
                };
                let case_allfalse = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (anid, han) = e.fresh_local(an_c.clone());
                    // checkLratStep db (mk clause hints) ≡ lratRup db hints clause,
                    // so hck feeds lratRupSound with F₀ = clause directly.
                    let ff = Expr::apps(
                        Expr::const_str(names::LRAT_RUP_SOUND),
                        [
                            holds.clone(),
                            hcons.clone(),
                            hexcl.clone(),
                            db.clone(),
                            hall.clone(),
                            hints.clone(),
                            clause.clone(),
                            han,
                            hck.clone(),
                        ],
                    );
                    let body = false_elim(Level::zero(), co_c.clone(), ff);
                    e.finish_child(e.mk_lam(anid, BinderInfo::Default, an_c.clone(), body))
                };
                let proof = or_elim(
                    co_c.clone(),
                    an_c.clone(),
                    co_c.clone(),
                    case_sat,
                    case_allfalse,
                    decide,
                );
                let r = d.mk_lam(hckid, BinderInfo::Default, hck_ty, proof);
                let r = d.mk_lam(hintsid, BinderInfo::Default, list_nat(), r);
                d.finish_child(d.mk_lam(cid, BinderInfo::Default, list_nat(), r))
            };
            let step_rec = Expr::const_(
                Name::from_string("Clean.Res.LratStep.rec"),
                vec![Level::zero()],
            );
            let folded = Expr::apps(step_rec, [motive, mk_case, s.clone()]);
            let r = b.mk_lam(
                haid,
                BinderInfo::Default,
                all_sat_trie(holds.clone(), db.clone()),
                folded,
            );
            let r = b.mk_lam(heid, BinderInfo::Default, excl_pred(&holds), r);
            let r = b.mk_lam(hcid, BinderInfo::Default, cons_pred(&holds), r);
            let r = b.mk_lam(sid, BinderInfo::Default, step_ty.clone(), r);
            let r = b.mk_lam(dbid, BinderInfo::Default, trie_ty(), r);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::CHECK_LRAT_STEP_SAT),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §7 goLratSound — the trace-fold induction (mirror of go3Sound) ────────

    /// `goLratSound : (H) → resConsistent H → resExclusive H →`
    /// `(pf : List LratStep) → (db : Trie) → (nextId : Nat) → allSatTrie H db →`
    /// `Eq (checkLrat db nextId pf) true → False`.
    fn register_go_lrat_sound(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::GO_LRAT_SOUND))
            .is_some()
        {
            return Ok(());
        }
        let step_ty = Expr::const_str(lnames::LRAT_STEP);
        let check_lrat = |db: Expr, nid: Expr, pf: Expr| {
            Expr::apps(Expr::const_str(lnames::CHECK_LRAT), [db, nid, pf])
        };
        let step_clause = |s: Expr| Expr::app(Expr::const_str(lnames::LRAT_STEP_CLAUSE), s);
        let step_empty = |s: Expr| Expr::app(Expr::const_str(lnames::LRAT_STEP_CLAUSE_EMPTY), s);
        let check_step =
            |db: Expr, s: Expr| Expr::apps(Expr::const_str(lnames::CHECK_LRAT_STEP), [db, s]);
        let is_cons = |l: Expr| Expr::app(Expr::const_str(lnames::LIST_LRAT_STEP_IS_CONS), l);
        let trie_ins =
            |db: Expr, k: Expr, c: Expr| Expr::apps(Expr::const_str(rnames::TRIE_INS), [db, k, c]);

        let mk_motive_body = |holds: &Expr, pf: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut c = EnvDeclBuilder::child_of(parent);
            let (dbid, db) = c.fresh_local(trie_ty());
            let (nid, nextid) = c.fresh_local(nat_ty());
            let inner = Expr::arrow(
                all_sat_trie(holds.clone(), db.clone()),
                Expr::arrow(
                    eq_bool(check_lrat(db.clone(), nextid.clone(), pf.clone()), btrue()),
                    false_c(),
                ),
            );
            let inner = c.mk_pi(nid, BinderInfo::Default, nat_ty(), inner);
            c.finish_child(c.mk_pi(dbid, BinderInfo::Default, trie_ty(), inner))
        };

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (cid, _hc) = b.fresh_local(cons_pred(&holds));
            let (eid, _he) = b.fresh_local(excl_pred(&holds));
            let (pfid, pf) = b.fresh_local(list_lrat_step());
            let mb = mk_motive_body(&holds, &pf, &b);
            let r = b.mk_pi(pfid, BinderInfo::Default, list_lrat_step(), mb);
            let r = b.mk_pi(eid, BinderInfo::Default, excl_pred(&holds), r);
            let r = b.mk_pi(cid, BinderInfo::Default, cons_pred(&holds), r);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), r))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (hcid, hcons) = b.fresh_local(cons_pred(&holds));
            let (heid, hexcl) = b.fresh_local(excl_pred(&holds));
            let (pfid, pf) = b.fresh_local(list_lrat_step());

            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_lrat_step());
                let body = mk_motive_body(&holds, &m, &d);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_lrat_step(), body))
            };

            // nil : checkLrat db nextId nil ≡ false — absurd.
            let nil_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let nil_pf = Expr::app(
                    Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                    step_ty.clone(),
                );
                let (dbid, db) = d.fresh_local(trie_ty());
                let (nid, nextid) = d.fresh_local(nat_ty());
                let as_ty = all_sat_trie(holds.clone(), db.clone());
                let (asid, _as) = d.fresh_local(as_ty.clone());
                let hck_ty = eq_bool(
                    check_lrat(db.clone(), nextid.clone(), nil_pf.clone()),
                    btrue(),
                );
                let (hckid, hck) = d.fresh_local(hck_ty.clone());
                let ff = tf_to_false(eq_symm_at(u1(), bool_ty(), bfalse(), btrue(), hck));
                let r = d.mk_lam(hckid, BinderInfo::Default, hck_ty, ff);
                let r = d.mk_lam(asid, BinderInfo::Default, as_ty, r);
                let r = d.mk_lam(nid, BinderInfo::Default, nat_ty(), r);
                d.finish_child(d.mk_lam(dbid, BinderInfo::Default, trie_ty(), r))
            };

            // cons s rest ih:
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (sid, s) = d.fresh_local(step_ty.clone());
                let (restid, rest) = d.fresh_local(list_lrat_step());
                let ih_ty = mk_motive_body(&holds, &rest, &d);
                let (ihid, ih) = d.fresh_local(ih_ty.clone());
                let (dbid, db) = d.fresh_local(trie_ty());
                let (nid, nextid) = d.fresh_local(nat_ty());
                let hall_ty = all_sat_trie(holds.clone(), db.clone());
                let (hallid, hall) = d.fresh_local(hall_ty.clone());
                let pf_cons = Expr::apps(
                    Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                    [step_ty.clone(), s.clone(), rest.clone()],
                );
                let hck_ty = eq_bool(
                    check_lrat(db.clone(), nextid.clone(), pf_cons.clone()),
                    btrue(),
                );
                let (hckid, hck) = d.fresh_local(hck_ty.clone());

                let new_db = trie_ins(db.clone(), nextid.clone(), step_clause(s.clone()));
                let new_next = nat_succ(nextid.clone());
                let tail_of = |bb: Expr| -> Expr {
                    let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), bool_ty());
                    Expr::apps(
                        Expr::const_(Name::from_string("Bool.rec"), vec![u1()]),
                        [
                            inner_motive,
                            step_empty(s.clone()),
                            check_lrat(new_db.clone(), new_next.clone(), rest.clone()),
                            bb,
                        ],
                    )
                };
                let tail = tail_of(is_cons(rest.clone()));
                let cs_e = check_step(db.clone(), s.clone());
                let cs_true = bool_and_elim_left(cs_e.clone(), tail.clone(), hck.clone());
                let tail_true = bool_and_elim_right(cs_e.clone(), tail.clone(), hck);
                // clauseOr H (lratStepClause s)
                let res_sat = Expr::apps(
                    Expr::const_str(names::CHECK_LRAT_STEP_SAT),
                    [
                        holds.clone(),
                        db.clone(),
                        s.clone(),
                        hcons.clone(),
                        hexcl.clone(),
                        hall.clone(),
                        cs_true,
                    ],
                );
                let res = step_clause(s.clone());
                let sat_or_nil_res = or_inl(
                    clause_or(holds.clone(), res.clone()),
                    eq_at(u1(), list_nat(), res.clone(), list_nil_nat()),
                    res_sat.clone(),
                );
                let all_ins = Expr::apps(
                    Expr::const_str(snames::TRIE_INS_PRESERVES_ALL_SAT),
                    [
                        holds.clone(),
                        db.clone(),
                        nextid.clone(),
                        res.clone(),
                        hall.clone(),
                        sat_or_nil_res,
                    ],
                );

                let isc = is_cons(rest.clone());
                let subst_motive = {
                    let inner = eq_bool(tail_of(Expr::bvar(0)), btrue());
                    Expr::lam(BinderInfo::Default, bool_ty(), inner)
                };
                // case_f: rest = nil ⇒ the step's clause is [] and satisfied — absurd.
                let case_f = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let heq_ty = eq_bool(isc.clone(), bfalse());
                    let (heqid, heq) = e.fresh_local(heq_ty.clone());
                    let se_true = eq_subst1(
                        bool_ty(),
                        subst_motive.clone(),
                        isc.clone(),
                        bfalse(),
                        heq,
                        tail_true.clone(),
                    );
                    let body = Expr::apps(
                        Expr::const_str(snames::LIST_IS_NIL_SAT),
                        [
                            holds.clone(),
                            step_clause(s.clone()),
                            se_true,
                            res_sat.clone(),
                        ],
                    );
                    e.finish_child(e.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                };
                // case_t: recurse with the grown trie.
                let case_t = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let heq_ty = eq_bool(isc.clone(), btrue());
                    let (heqid, heq) = e.fresh_local(heq_ty.clone());
                    let go_true = eq_subst1(
                        bool_ty(),
                        subst_motive.clone(),
                        isc.clone(),
                        btrue(),
                        heq,
                        tail_true.clone(),
                    );
                    let body = Expr::apps(
                        ih.clone(),
                        [new_db.clone(), new_next.clone(), all_ins.clone(), go_true],
                    );
                    e.finish_child(e.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                };
                let body = bool_cases(isc, false_c(), case_f, case_t);
                let r = d.mk_lam(hckid, BinderInfo::Default, hck_ty, body);
                let r = d.mk_lam(hallid, BinderInfo::Default, hall_ty, r);
                let r = d.mk_lam(nid, BinderInfo::Default, nat_ty(), r);
                let r = d.mk_lam(dbid, BinderInfo::Default, trie_ty(), r);
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                let r = d.mk_lam(restid, BinderInfo::Default, list_lrat_step(), r);
                d.finish_child(d.mk_lam(sid, BinderInfo::Default, step_ty.clone(), r))
            };

            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            );
            let folded = Expr::apps(
                list_rec,
                [step_ty.clone(), motive, nil_case, cons_case, pf.clone()],
            );
            let r = b.mk_lam(pfid, BinderInfo::Default, list_lrat_step(), folded);
            let r = b.mk_lam(heid, BinderInfo::Default, excl_pred(&holds), r);
            let r = b.mk_lam(hcid, BinderInfo::Default, cons_pred(&holds), r);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::GO_LRAT_SOUND),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §8 checkLrat_sound — the top-level bridge ─────────────────────────────

    /// `checkLrat_sound :`
    /// `(cs : List (List Nat)) → (trace : List LratStep) →`
    /// `Eq (checkLrat (initialTrie cs) (listLen cs) trace) true → Unsat cs`.
    ///
    /// SAME shape and semantic vocabulary as `checkRefutes3_sound`: the
    /// `Unsat cs` conclusion is spelled δ-unfolded, `initialTrieAllSat`
    /// converts the model's `allSat H cs` into the trie invariant, and
    /// `goLratSound` walks the trace.
    fn register_check_lrat_sound_thm(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::CHECK_LRAT_SOUND))
            .is_some()
        {
            return Ok(());
        }
        let check_lrat = |db: Expr, nid: Expr, pf: Expr| {
            Expr::apps(Expr::const_str(lnames::CHECK_LRAT), [db, nid, pf])
        };
        let list_len = |cs: Expr| Expr::app(Expr::const_str(rnames::LIST_LEN), cs);
        let initial_trie = |cs: Expr| Expr::app(Expr::const_str(rnames::INITIAL_TRIE), cs);

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (csid, cs) = b.fresh_local(list_list_nat());
            let (stepsid, steps) = b.fresh_local(list_lrat_step());
            // Unsat cs spelled δ-unfolded (same presentation as checkRefutes3_sound).
            let unsat = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hid, holds) = c.fresh_local(holds_ty());
                let all_cs = Expr::apps(
                    Expr::const_str(snames::ALL_SAT),
                    [holds.clone(), cs.clone()],
                );
                let body = Expr::arrow(all_cs, false_c());
                let body = Expr::arrow(excl_pred(&holds), body);
                let body = Expr::arrow(cons_pred(&holds), body);
                c.finish_child(c.mk_pi(hid, BinderInfo::Default, holds_ty(), body))
            };
            let hck = eq_bool(
                check_lrat(
                    initial_trie(cs.clone()),
                    list_len(cs.clone()),
                    steps.clone(),
                ),
                btrue(),
            );
            let inner = Expr::arrow(hck, unsat);
            let e = b.mk_pi(stepsid, BinderInfo::Default, list_lrat_step(), inner);
            b.finish(b.mk_pi(csid, BinderInfo::Default, list_list_nat(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (csid, cs) = b.fresh_local(list_list_nat());
            let (stepsid, steps) = b.fresh_local(list_lrat_step());
            let hck_ty = eq_bool(
                check_lrat(
                    initial_trie(cs.clone()),
                    list_len(cs.clone()),
                    steps.clone(),
                ),
                btrue(),
            );
            let (hckid, hck) = b.fresh_local(hck_ty.clone());
            let (hid, holds) = b.fresh_local(holds_ty());
            let (hcid, hcons) = b.fresh_local(cons_pred(&holds));
            let (heid, hexcl) = b.fresh_local(excl_pred(&holds));
            let all_cs = Expr::apps(
                Expr::const_str(snames::ALL_SAT),
                [holds.clone(), cs.clone()],
            );
            let (haid, hall) = b.fresh_local(all_cs.clone());
            let all_db0 = Expr::apps(
                Expr::const_str(INITIAL_TRIE_ALL_SAT),
                [holds.clone(), cs.clone(), hall],
            );
            let body = Expr::apps(
                Expr::const_str(names::GO_LRAT_SOUND),
                [
                    holds.clone(),
                    hcons,
                    hexcl,
                    steps.clone(),
                    initial_trie(cs.clone()),
                    list_len(cs.clone()),
                    all_db0,
                    hck.clone(),
                ],
            );
            let r = b.mk_lam(haid, BinderInfo::Default, all_cs, body);
            let r = b.mk_lam(heid, BinderInfo::Default, excl_pred(&holds), r);
            let r = b.mk_lam(hcid, BinderInfo::Default, cons_pred(&holds), r);
            let r = b.mk_lam(hid, BinderInfo::Default, holds_ty(), r);
            let r = b.mk_lam(hckid, BinderInfo::Default, hck_ty, r);
            let r = b.mk_lam(stepsid, BinderInfo::Default, list_lrat_step(), r);
            b.finish(b.mk_lam(csid, BinderInfo::Default, list_list_nat(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::CHECK_LRAT_SOUND),
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
#[path = "lrat_soundness_tests.rs"]
mod tests;
