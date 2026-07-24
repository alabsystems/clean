// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PROVED soundness of the computational resolution checker
//! ([`crate::resolution_check`]).
//!
//! This module discharges the residual obligation `checkRefutes_sound` as a
//! kernel-checked `Declaration::Theorem` whose transitive axiom closure is
//! `⊆ FOUNDATIONAL_AXIOMS` — eliminating the previously-STATED soundness axiom and
//! making the reflection certificate FULLY zero-trust (zero residual domain
//! axioms).
//!
//! # The semantics (real kernel definitions, not opaque axioms)
//!
//! A *model* is a literal-truth predicate `Holds : Nat → Prop` that is
//!
//!   * **total** (`resConsistent`): `∀ l, Holds l ∨ Holds (litNeg l)`, and
//!   * **exclusive** (`resExclusive`): `∀ l, Holds l → Holds (litNeg l) → False`.
//!
//! Together these say `Holds` is exactly a Boolean variable assignment read off as
//! literal truth — every literal is true or false, never both. We define
//!
//!   * `clauseSat Holds c` — the right-folded `Or` of the literals' `Holds`
//!     (reuses `Clean.Res.clauseOr`); `clauseSat Holds nil ≡ False`.
//!   * `allSat Holds cs` — the `And`-fold of `clauseSat` over the clause DB;
//!     `allSat Holds nil ≡ True`.
//!   * `Unsat cs := ∀ Holds, resConsistent Holds → resExclusive Holds →
//!     allSat Holds cs → False`.
//!
//! These REPLACE the previously opaque `Holds` / `Unsat` axioms.
//!
//! # What is PROVED (every one a kernel `Theorem`, closure ⊆ FOUNDATIONAL_AXIOMS)
//!
//!   * `natBeqEq` — `Nat.beq x y = true → x = y` (double induction).
//!   * `dropFalseSat` — dropping a FALSE literal preserves clause satisfaction.
//!   * `appendSatL` / `appendSatR` — satisfaction is preserved under `append`.
//!   * `resolveStepSat` — the SINGLE-STEP resolution-soundness lemma: under a
//!     consistent+exclusive model satisfying both premises, the oriented resolvent
//!     `resolve a b p = dropLit p a ++ dropLit ¬p b` is satisfied (case-split on
//!     the pivot via `resConsistent`/`resExclusive`).
//!   * `memSat` / `subsetSat` / `seteqSat` — membership / `clauseSubset` /
//!     `clauseSeteq` reflection of satisfaction.
//!   * `nthSat` — every in-range DB clause is satisfied; `memNotNil` discharges the
//!     out-of-range (`nth = nil`) case once a pivot is a known member.
//!   * `checkStepSat` — the step-level bridge: `checkStep db s = true` + model ⇒ the
//!     recorded resolvent is satisfied (both legal orientations).
//!   * `allSatSnoc` / `listIsNilSat` — the threading + empty-clause endpoint lemmas.
//!   * `goSound` / `checkRefutes_sound` — the fold induction over the refutation
//!     list and the top-level bridge: every clause in the threaded DB stays
//!     satisfied, so the final empty clause would be satisfied — a contradiction.
//!
//! # The soundness bug this fixed
//!
//! Proving `checkRefutes_sound` forced a REAL soundness fix in
//! [`crate::resolution_check`]: the old `resolve` did a DOUBLE-polarity drop
//! `(a∪b) \ {p,¬p}`, which is UNSOUND — from the SATISFIABLE set `{(x),(¬x∨x)}` it
//! derives the empty clause. `resolve` is now a SINGLE oriented drop `dropLit p a ++
//! dropLit ¬p b`, and `checkStep` validates both legal pivot orientations against
//! it.
//!
//! # One residual non-foundational dependency: NONE in the proof; a kernel
//! transparency note
//!
//! `checkRefutes_sound`'s stated type spells `Unsat cs` in its δ-unfolded form
//! (the literal body of the `Unsat` `Definition`) rather than the `Unsat cs`
//! alias — the two are definitionally equal, but the kernel's `add_decl` defeq does
//! not fire lazy-δ when comparing the proof's inferred `Pi`-type against an
//! `Unsat`-headed `Const`-app. This is a presentation detail of the *statement*, not
//! a gap in the *proof*: the term genuinely inhabits `Unsat cs`, and the axiom
//! closure is `⊆ FOUNDATIONAL_AXIOMS`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::name::Name;
use crate::resolution_check::names as rnames;
use crate::{BinderInfo, Declaration, EnvError, Environment, Expr, Level};

/// Names registered by the soundness layer.
pub mod names {
    /// `Clean.Res.natBeqEq : (x y : Nat) → Eq (Nat.beq x y) true → Eq x y`.
    pub const NAT_BEQ_EQ: &str = "Clean.Res.natBeqEq";
    /// PROVED `Clean.Res.dropFalseSat` — dropping a false literal preserves sat.
    pub const DROP_FALSE_SAT: &str = "Clean.Res.dropFalseSat";
    /// PROVED `Clean.Res.appendSatL` — left premise satisfies the append.
    pub const APPEND_SAT_L: &str = "Clean.Res.appendSatL";
    /// PROVED `Clean.Res.appendSatR` — right premise satisfies the append.
    pub const APPEND_SAT_R: &str = "Clean.Res.appendSatR";
    /// PROVED `Clean.Res.resolveStepSat` — single-step resolution soundness.
    pub const RESOLVE_STEP_SAT: &str = "Clean.Res.resolveStepSat";
    /// PROVED `Clean.Res.memSat` — `x ∈ c` and `H x` ⇒ `clauseOr H c`.
    pub const MEM_SAT: &str = "Clean.Res.memSat";
    /// PROVED `Clean.Res.subsetSat` — `clauseSubset`-reflection of satisfaction.
    pub const SUBSET_SAT: &str = "Clean.Res.subsetSat";
    /// PROVED `Clean.Res.memNotNil` — a member literal ⇒ clause is non-nil.
    pub const MEM_NOT_NIL: &str = "Clean.Res.memNotNil";
    /// `Clean.Res.allSat : (Nat→Prop) → List (List Nat) → Prop` (And-fold of sat).
    pub const ALL_SAT: &str = "Clean.Res.allSat";
    /// PROVED `Clean.Res.nthSat` — every in-range DB clause is satisfied.
    pub const NTH_SAT: &str = "Clean.Res.nthSat";
    /// PROVED `Clean.Res.seteqSat` — set-equal clauses are co-satisfiable.
    pub const SETEQ_SAT: &str = "Clean.Res.seteqSat";
    /// `Clean.Res.resConsistent : (Nat→Prop) → Prop`.
    pub const RES_CONSISTENT: &str = "Clean.Res.resConsistent";
    /// `Clean.Res.resExclusive : (Nat→Prop) → Prop`.
    pub const RES_EXCLUSIVE: &str = "Clean.Res.resExclusive";
    /// `Clean.Res.Unsat : List (List Nat) → Prop` (real model definition).
    pub const UNSAT: &str = "Clean.Res.Unsat";
    /// PROVED `Clean.Res.checkStepSat` — step-level soundness bridge.
    pub const CHECK_STEP_SAT: &str = "Clean.Res.checkStepSat";
    /// PROVED `Clean.Res.allSatSnoc` — snoc preserves DB satisfaction.
    pub const ALL_SAT_SNOC: &str = "Clean.Res.allSatSnoc";
    /// PROVED `Clean.Res.listIsNilSat` — an empty clause is not satisfied.
    pub const LIST_IS_NIL_SAT: &str = "Clean.Res.listIsNilSat";
    /// PROVED `Clean.Res.goSound` — the fold-invariant induction helper.
    pub const GO_SOUND: &str = "Clean.Res.goSound";
    /// PROVED `Clean.Res.checkRefutes_sound` — the top-level soundness bridge.
    pub const CHECK_REFUTES_SOUND: &str = "Clean.Res.checkRefutes_sound";

    // ── §12 trie-checker (checkRefutes3) soundness ─────────────────────────────
    /// `Clean.Res.allSatTrie : (Nat→Prop) → Trie → Prop` — every trie node's value
    /// is SAT-or-nil (the trie analogue of `allSat`, via `Trie.rec`).
    pub const ALL_SAT_TRIE: &str = "Clean.Res.allSatTrie";
    /// PROVED `Clean.Res.trieGetSat` — every value fetched from a SAT-or-nil trie is
    /// itself SAT-or-nil (the `nthSat` analogue, by `Trie.rec` induction).
    pub const TRIE_GET_SAT: &str = "Clean.Res.trieGetSat";
    /// PROVED `Clean.Res.trieInsPreservesAllSat` — path-copy insert of a SAT-or-nil
    /// value preserves `allSatTrie` (fuel `Nat.rec` induction).
    pub const TRIE_INS_PRESERVES_ALL_SAT: &str = "Clean.Res.trieInsPreservesAllSat";
    /// PROVED `Clean.Res.checkStep3Sat` — step-level soundness bridge for `checkStep3`.
    pub const CHECK_STEP3_SAT: &str = "Clean.Res.checkStep3Sat";
    /// PROVED `Clean.Res.go3Sound` — the trie-fold induction helper.
    pub const GO3_SOUND: &str = "Clean.Res.go3Sound";
    /// PROVED `Clean.Res.checkRefutes3_sound` — the sub-quadratic trie checker's
    /// top-level soundness bridge.
    pub const CHECK_REFUTES3_SOUND: &str = "Clean.Res.checkRefutes3_sound";
}

// ── small shared Expr helpers (mirrors resolution_check.rs) ────────────────────

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
fn nat_zero() -> Expr {
    Expr::const_str("Nat.zero")
}
/// `@Eq.{u} ty x y`.
fn eq_at(u: Level, ty: Expr, x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![u]), [ty, x, y])
}
fn eq_nat(x: Expr, y: Expr) -> Expr {
    eq_at(Level::succ(Level::zero()), nat_ty(), x, y)
}
fn eq_bool(x: Expr, y: Expr) -> Expr {
    eq_at(Level::succ(Level::zero()), bool_ty(), x, y)
}
/// `@Eq.refl.{u} ty x`.
fn eq_refl_at(u: Level, ty: Expr, x: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![u]), [ty, x])
}
fn eq_refl_nat(x: Expr) -> Expr {
    eq_refl_at(Level::succ(Level::zero()), nat_ty(), x)
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
fn nat_beq(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.beq"), [x, y])
}
/// `@congrArg.{u,v} α β a1 a2 f h : Eq (f a1) (f a2)`.
fn congr_arg(
    u: Level,
    v: Level,
    alpha: Expr,
    beta: Expr,
    a1: Expr,
    a2: Expr,
    f: Expr,
    h: Expr,
) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![u, v]),
        [alpha, beta, a1, a2, f, h],
    )
}
/// `False.elim.{u} C h`.
fn false_elim(u: Level, c: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![u]),
        [c, h],
    )
}

// ── List / clause / logic helpers ──────────────────────────────────────────────

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
fn drop_lit(x: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(rnames::DROP_LIT), [x, c])
}
fn lit_beq(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str(rnames::LIT_BEQ), [x, y])
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
fn append(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str(rnames::APPEND), [a, b])
}
/// `Clean.Res.clauseOr Holds c : Prop` (right-folded `Or` of the literals).
fn clause_or(holds: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.Res.clauseOr"), [holds, c])
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
/// `@And.left a b h : a`.
fn and_left(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [a, b, h],
    )
}
/// `@And.right a b h : b`.
fn and_right(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.right"), vec![]),
        [a, b, h],
    )
}
/// `@And.intro a b ha hb : And a b`.
fn and_intro(a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [a, b, ha, hb],
    )
}
/// `Or.rec` eliminating into a `Prop` motive `c`:
/// `@Or.rec a b (motive := fun _ => c) fl fr hor` where `fl : a → c`, `fr : b → c`.
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
        Expr::const_(
            Name::from_string("Eq.subst"),
            vec![Level::succ(Level::zero())],
        ),
        [alpha, motive, a, b, h, m],
    )
}
/// Case-split on a `Bool`-typed expression `scrut` via the `Eq.refl` trick:
/// `(Bool.rec (motive := fun bb => Eq scrut bb → goal) caseF caseT scrut) (Eq.refl scrut)`
/// with `caseF : Eq scrut false → goal`, `caseT : Eq scrut true → goal`, `goal : Prop`.
fn bool_cases(scrut: Expr, goal: Expr, case_f: Expr, case_t: Expr) -> Expr {
    let motive = {
        let inner = Expr::arrow(eq_bool(scrut.clone(), Expr::bvar(0)), goal);
        Expr::lam(BinderInfo::Default, bool_ty(), inner)
    };
    let rec = Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        [motive, case_f, case_t, scrut.clone()],
    );
    Expr::app(
        rec,
        eq_refl_at(Level::succ(Level::zero()), bool_ty(), scrut),
    )
}

// ── trie helpers (for the checkRefutes3 soundness layer) ───────────────────────

fn trie_ty() -> Expr {
    Expr::const_str(rnames::TRIE)
}
fn trie_leaf() -> Expr {
    Expr::const_str(rnames::TRIE_LEAF)
}
fn trie_node(v: Expr, lo: Expr, hi: Expr) -> Expr {
    Expr::apps(Expr::const_str(rnames::TRIE_NODE), [v, lo, hi])
}
fn trie_get(db: Expr, key: Expr) -> Expr {
    Expr::apps(Expr::const_str(rnames::TRIE_GET), [db, key])
}
/// `allSatTrie H db : Prop`.
fn all_sat_trie(holds: Expr, db: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::ALL_SAT_TRIE), [holds, db])
}
/// `Or (clauseOr H c) (Eq c List.nil)` — the "SAT-or-nil" predicate on a clause.
fn sat_or_nil(holds: &Expr, c: &Expr) -> Expr {
    or_t(
        clause_or(holds.clone(), c.clone()),
        eq_at(
            Level::succ(Level::zero()),
            list_nat(),
            c.clone(),
            list_nil_nat(),
        ),
    )
}
fn nat_div(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.div"), [x, y])
}
fn nat_mod(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.mod"), [x, y])
}
fn nat_ble(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.ble"), [x, y])
}
fn nat_lit(n: u64) -> Expr {
    Expr::nat_lit(n)
}

impl Environment {
    /// Register the PROVED resolution-soundness layer and the
    /// `checkRefutes_sound` theorem. Idempotent. Assumes
    /// [`Environment::init_resolution_check`] has run (or runs it).
    ///
    /// # Errors
    /// Propagates any [`EnvError`] from declaration insertion / kernel checking.
    pub fn init_resolution_soundness(&mut self) -> Result<(), EnvError> {
        self.init_resolution_check()?;
        self.init_or()?;
        self.init_and()?;
        self.init_true_false()?;
        self.register_nat_beq_eq()?;
        self.register_drop_false_sat()?;
        self.register_append_sat_l()?;
        self.register_append_sat_r()?;
        self.register_resolve_step_sat()?;
        self.register_mem_sat()?;
        self.register_subset_sat()?;
        self.register_seteq_sat()?;
        self.register_semantics()?;
        self.register_nth_sat()?;
        self.register_mem_not_nil()?;
        self.register_check_step_sat()?;
        self.register_all_sat_snoc()?;
        self.register_list_is_nil_sat()?;
        self.register_check_refutes_sound()?;
        self.register_check_refutes3_sound()?;
        Ok(())
    }

    // ── §1 natBeqEq : reflect Nat.beq into propositional equality ──────────────

    /// `natBeqEq : (x y : Nat) → Eq (Nat.beq x y) Bool.true → Eq x y`.
    ///
    /// Standard double induction on `x` then `y`. Built as
    /// `Nat.rec (motive := fun x => ∀ y, beq x y = true → x = y) zeroCase succCase x y`.
    fn register_nat_beq_eq(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::NAT_BEQ_EQ))
            .is_some()
        {
            return Ok(());
        }
        let u1 = Level::succ(Level::zero());
        // P x := ∀ (y : Nat), Eq (Nat.beq x y) true → Eq x y.
        // Built with a child builder so a parent's `x` fvar is tolerated; only the
        // freshly-bound `y` is abstracted here.
        let p_of = |x: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (yid, y) = b.fresh_local(nat_ty());
            let hyp = eq_bool(nat_beq(x.clone(), y.clone()), btrue());
            let concl = eq_nat(x.clone(), y.clone());
            let inner = Expr::arrow(hyp, concl);
            b.finish_child(b.mk_pi(yid, BinderInfo::Default, nat_ty(), inner))
        };

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (xid, x) = b.fresh_local(nat_ty());
            let (yid, y) = b.fresh_local(nat_ty());
            let hyp = eq_bool(nat_beq(x.clone(), y.clone()), btrue());
            let concl = eq_nat(x.clone(), y.clone());
            let inner = Expr::arrow(hyp, concl);
            let e = b.mk_pi(yid, BinderInfo::Default, nat_ty(), inner);
            b.finish(b.mk_pi(xid, BinderInfo::Default, nat_ty(), e))
        };

        // ── inner helper: beqYzero : ∀ y, beq 0 y = true → 0 = y ──
        // by Nat.rec on y. y=0: refl. y=succ y': beq 0 (succ y') ≡ false, hyp false=true absurd.
        let zero_case = {
            let mut b = EnvDeclBuilder::new();
            let (yid, y) = b.fresh_local(nat_ty());
            // motive_y : fun y => beq 0 y = true → 0 = y
            let motive_y = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(nat_ty());
                let body = Expr::arrow(
                    eq_bool(nat_beq(nat_zero(), m.clone()), btrue()),
                    eq_nat(nat_zero(), m.clone()),
                );
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, nat_ty(), body))
            };
            // y=0 case: fun (_h : beq 0 0 = true) => Eq.refl Nat 0
            let yzero = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let hty = eq_bool(nat_beq(nat_zero(), nat_zero()), btrue());
                let (hid, _h) = c.fresh_local(hty.clone());
                c.finish_child(c.mk_lam(hid, BinderInfo::Default, hty, eq_refl_nat(nat_zero())))
            };
            // y=succ case: fun (y' : Nat) (_ih) (h : beq 0 (succ y') = true) =>
            //   absurd: beq 0 (succ y') ≡ false, so h : false = true; tf_false (symm h) elim.
            let ysucc = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ypid, yp) = c.fresh_local(nat_ty());
                let ih_ty = Expr::arrow(
                    eq_bool(nat_beq(nat_zero(), yp.clone()), btrue()),
                    eq_nat(nat_zero(), yp.clone()),
                );
                let (ihid, _ih) = c.fresh_local(ih_ty.clone());
                let hty = eq_bool(nat_beq(nat_zero(), nat_succ(yp.clone())), btrue());
                let (hid, h) = c.fresh_local(hty.clone());
                // h : false = true (defeq). symm h : true = false. tf_to_false → False.
                let ff = tf_to_false(eq_symm_at(u1.clone(), bool_ty(), bfalse(), btrue(), h));
                let concl = eq_nat(nat_zero(), nat_succ(yp.clone()));
                let body = false_elim(Level::zero(), concl, ff);
                let r = c.mk_lam(hid, BinderInfo::Default, hty, body);
                let r = c.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                c.finish_child(c.mk_lam(ypid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let body = Expr::apps(nat_rec, [motive_y, yzero, ysucc, y]);
            b.finish(b.mk_lam(yid, BinderInfo::Default, nat_ty(), body))
        };

        // ── succ_case : fun (x' : Nat) (ihx : P x') => (P (succ x')) ──
        // P (succ x') = ∀ y, beq (succ x') y = true → succ x' = y, by Nat.rec on y.
        let succ_case = {
            let mut b = EnvDeclBuilder::new();
            let (xpid, xp) = b.fresh_local(nat_ty());
            let (ihxid, ihx) = b.fresh_local(p_of(&xp, &b));
            // motive_y : fun y => beq (succ x') y = true → succ x' = y
            let sx = nat_succ(xp.clone());
            let motive_y = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(nat_ty());
                let body = Expr::arrow(
                    eq_bool(nat_beq(sx.clone(), m.clone()), btrue()),
                    eq_nat(sx.clone(), m.clone()),
                );
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, nat_ty(), body))
            };
            // y=0: fun (h : beq (succ x') 0 = true) => absurd (beq _ 0 ≡ false).
            let yzero = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let hty = eq_bool(nat_beq(sx.clone(), nat_zero()), btrue());
                let (hid, h) = c.fresh_local(hty.clone());
                let ff = tf_to_false(eq_symm_at(u1.clone(), bool_ty(), bfalse(), btrue(), h));
                let concl = eq_nat(sx.clone(), nat_zero());
                let body = false_elim(Level::zero(), concl, ff);
                c.finish_child(c.mk_lam(hid, BinderInfo::Default, hty, body))
            };
            // y=succ y': fun (y' : Nat) (_ih) (h : beq (succ x')(succ y') = true) =>
            //   beq (succ x')(succ y') ≡ beq x' y', so h : beq x' y' = true.
            //   ihx y' h : x' = y'. congrArg Nat.succ → succ x' = succ y'.
            let ysucc = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ypid, yp) = c.fresh_local(nat_ty());
                let ih_ty = Expr::arrow(
                    eq_bool(nat_beq(sx.clone(), yp.clone()), btrue()),
                    eq_nat(sx.clone(), yp.clone()),
                );
                let (ihid, _ih) = c.fresh_local(ih_ty.clone());
                let hty = eq_bool(nat_beq(sx.clone(), nat_succ(yp.clone())), btrue());
                let (hid, h) = c.fresh_local(hty.clone());
                // h : beq x' y' = true (defeq to hty). ihx y' h : x' = y'.
                let xeq = Expr::app(Expr::app(ihx.clone(), yp.clone()), h);
                // congrArg Nat Nat x' y' Nat.succ xeq : succ x' = succ y'
                let body = congr_arg(
                    u1.clone(),
                    u1.clone(),
                    nat_ty(),
                    nat_ty(),
                    xp.clone(),
                    yp.clone(),
                    Expr::const_str("Nat.succ"),
                    xeq,
                );
                let r = c.mk_lam(hid, BinderInfo::Default, hty, body);
                let r = c.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                c.finish_child(c.mk_lam(ypid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            // body : P (succ x') = fun y => Nat.rec motive_y yzero ysucc y
            let inner = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (yid, y) = c.fresh_local(nat_ty());
                let fold = Expr::apps(nat_rec, [motive_y, yzero, ysucc, y]);
                c.finish_child(c.mk_lam(yid, BinderInfo::Default, nat_ty(), fold))
            };
            let r = b.mk_lam(ihxid, BinderInfo::Default, p_of(&xp, &b), inner);
            b.finish(b.mk_lam(xpid, BinderInfo::Default, nat_ty(), r))
        };

        // value : fun (x y : Nat) => Nat.rec (motive := P) zero_case succ_case x y
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (xid, x) = b.fresh_local(nat_ty());
            let (yid, y) = b.fresh_local(nat_ty());
            // motive_x : fun x => P x
            let motive_x = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(nat_ty());
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, nat_ty(), p_of(&m, &c)))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let px = Expr::apps(nat_rec, [motive_x, zero_case, succ_case, x]);
            // (P x) applied to y : beq x y = true → x = y. Result is a Pi; return it.
            let body = Expr::app(px, y);
            let e = b.mk_lam(yid, BinderInfo::Default, nat_ty(), body);
            b.finish(b.mk_lam(xid, BinderInfo::Default, nat_ty(), e))
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::NAT_BEQ_EQ),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §2 dropFalseSat : dropping a FALSE literal preserves satisfaction ──────

    /// `dropFalseSat : (H : Nat→Prop) → (x : Nat) → (c : List Nat) →
    ///    clauseOr H c → (H x → False) → clauseOr H (dropLit x c)`.
    ///
    /// `List.rec` on `c`. The `cons hd tl` case splits on `litBeq x hd` (via the
    /// `Eq.refl` trick): if `x = hd` (`= true`) the head is dropped — and `H hd`
    /// would give `H x`, contradicting the hypothesis (`natBeqEq` bridges `beq`→`=`);
    /// if `x ≠ hd` (`= false`) the head survives and the `Or` is rebuilt.
    fn register_drop_false_sat(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::DROP_FALSE_SAT))
            .is_some()
        {
            return Ok(());
        }
        let u1 = Level::succ(Level::zero());
        // goal predicate as a function of c: clauseOr H c → (H x → False) → clauseOr H (dropLit x c)
        let mk_type = |holds: &Expr, x: &Expr, c: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let _ = parent;
            let hxf = Expr::arrow(Expr::app(holds.clone(), x.clone()), false_c());
            Expr::arrow(
                clause_or(holds.clone(), c.clone()),
                Expr::arrow(
                    hxf,
                    clause_or(holds.clone(), drop_lit(x.clone(), c.clone())),
                ),
            )
        };

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (xid, x) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(list_nat());
            let body = mk_type(&holds, &x, &c, &b);
            let e = b.mk_pi(cid, BinderInfo::Default, list_nat(), body);
            let e = b.mk_pi(xid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (xid, x) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(list_nat());

            // motive : fun c => mk_type holds x c
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_nat());
                let body = mk_type(&holds, &x, &m, &d);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_nat(), body))
            };

            // nil case : fun (h : clauseOr H nil) (_ : H x → False) => h
            let nil_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let co_nil = clause_or(
                    holds.clone(),
                    Expr::app(
                        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                        nat_ty(),
                    ),
                );
                let hxf = Expr::arrow(Expr::app(holds.clone(), x.clone()), false_c());
                let (h0id, h0) = d.fresh_local(co_nil.clone());
                let (h1id, _h1) = d.fresh_local(hxf.clone());
                let r = d.mk_lam(h1id, BinderInfo::Default, hxf, h0);
                d.finish_child(d.mk_lam(h0id, BinderInfo::Default, co_nil, r))
            };

            // cons case : fun (hd) (tl) (ih) (hco) (hxf) => <goal>
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (hdid, hd) = d.fresh_local(nat_ty());
                let (tlid, tl) = d.fresh_local(list_nat());
                let ih_ty = mk_type(&holds, &x, &tl, &d);
                let (ihid, ih) = d.fresh_local(ih_ty.clone());
                let co_cons = clause_or(
                    holds.clone(),
                    Expr::apps(
                        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                        [nat_ty(), hd.clone(), tl.clone()],
                    ),
                );
                let (hcoid, hco) = d.fresh_local(co_cons.clone());
                let hxf_ty = Expr::arrow(Expr::app(holds.clone(), x.clone()), false_c());
                let (hxfid, hxf) = d.fresh_local(hxf_ty.clone());

                // D bb := Bool.rec (cons hd (dropLit x tl)) (dropLit x tl) bb : List Nat
                let d_of = |bb: Expr| -> Expr {
                    let keep = Expr::apps(
                        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                        [nat_ty(), hd.clone(), drop_lit(x.clone(), tl.clone())],
                    );
                    let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), list_nat());
                    Expr::apps(
                        Expr::const_(Name::from_string("Bool.rec"), vec![u1.clone()]),
                        [inner_motive, keep, drop_lit(x.clone(), tl.clone()), bb],
                    )
                };
                let beq = Expr::apps(Expr::const_str(rnames::LIT_BEQ), [x.clone(), hd.clone()]);
                // goal : clauseOr H (dropLit x (hd::tl)) ≡ clauseOr H (D (litBeq x hd))
                let goal = clause_or(holds.clone(), d_of(beq.clone()));

                // subst motive over bb : fun bb => clauseOr H (D bb)
                let subst_motive = {
                    let inner = clause_or(holds.clone(), d_of(Expr::bvar(0)));
                    Expr::lam(BinderInfo::Default, bool_ty(), inner)
                };

                // ===== case_t : Eq (litBeq x hd) true → goal =====
                let case_t = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let heq_ty = eq_bool(beq.clone(), btrue());
                    let (heqid, heq) = e.fresh_local(heq_ty.clone());
                    // m : clauseOr H (D true) ≡ clauseOr H (dropLit x tl)
                    let co_drop_tl = clause_or(holds.clone(), drop_lit(x.clone(), tl.clone()));
                    // from hco : Or (H hd) (clauseOr H tl), build m.
                    let case_hd = {
                        // fun (hhd : H hd) => contradiction → False.elim
                        let mut f = EnvDeclBuilder::child_of(&e);
                        let hhd_ty = Expr::app(holds.clone(), hd.clone());
                        let (hhdid, hhd) = f.fresh_local(hhd_ty.clone());
                        // x = hd : natBeqEq x hd heq
                        let xeqhd = Expr::apps(
                            Expr::const_str(names::NAT_BEQ_EQ),
                            [x.clone(), hd.clone(), heq.clone()],
                        );
                        // H x from H hd via Eq.subst (motive H) hd x (symm xeqhd) hhd
                        let hx = eq_subst1(
                            nat_ty(),
                            holds.clone(),
                            hd.clone(),
                            x.clone(),
                            eq_symm_at(u1.clone(), nat_ty(), x.clone(), hd.clone(), xeqhd),
                            hhd,
                        );
                        let ff = Expr::app(hxf.clone(), hx);
                        let body = false_elim(Level::zero(), co_drop_tl.clone(), ff);
                        f.finish_child(f.mk_lam(hhdid, BinderInfo::Default, hhd_ty, body))
                    };
                    let case_tl = {
                        let mut f = EnvDeclBuilder::child_of(&e);
                        let htl_ty = clause_or(holds.clone(), tl.clone());
                        let (htlid, htl) = f.fresh_local(htl_ty.clone());
                        // ih htl hxf : clauseOr H (dropLit x tl)
                        let body = Expr::apps(ih.clone(), [htl, hxf.clone()]);
                        f.finish_child(f.mk_lam(htlid, BinderInfo::Default, htl_ty, body))
                    };
                    let m = or_elim(
                        Expr::app(holds.clone(), hd.clone()),
                        clause_or(holds.clone(), tl.clone()),
                        co_drop_tl.clone(),
                        case_hd,
                        case_tl,
                        hco.clone(),
                    );
                    // Eq.subst subst_motive true (litBeq x hd) (symm heq) m : clauseOr H (D (litBeq x hd))
                    let body = eq_subst1(
                        bool_ty(),
                        subst_motive.clone(),
                        btrue(),
                        beq.clone(),
                        eq_symm_at(u1.clone(), bool_ty(), beq.clone(), btrue(), heq),
                        m,
                    );
                    e.finish_child(e.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                };

                // ===== case_f : Eq (litBeq x hd) false → goal =====
                let case_f = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let heq_ty = eq_bool(beq.clone(), bfalse());
                    let (heqid, heq) = e.fresh_local(heq_ty.clone());
                    // m : clauseOr H (D false) ≡ Or (H hd) (clauseOr H (dropLit x tl))
                    let or_target = or_t(
                        Expr::app(holds.clone(), hd.clone()),
                        clause_or(holds.clone(), drop_lit(x.clone(), tl.clone())),
                    );
                    let case_hd = {
                        let mut f = EnvDeclBuilder::child_of(&e);
                        let hhd_ty = Expr::app(holds.clone(), hd.clone());
                        let (hhdid, hhd) = f.fresh_local(hhd_ty.clone());
                        let body = or_inl(
                            Expr::app(holds.clone(), hd.clone()),
                            clause_or(holds.clone(), drop_lit(x.clone(), tl.clone())),
                            hhd,
                        );
                        f.finish_child(f.mk_lam(hhdid, BinderInfo::Default, hhd_ty, body))
                    };
                    let case_tl = {
                        let mut f = EnvDeclBuilder::child_of(&e);
                        let htl_ty = clause_or(holds.clone(), tl.clone());
                        let (htlid, htl) = f.fresh_local(htl_ty.clone());
                        let inner = Expr::apps(ih.clone(), [htl, hxf.clone()]);
                        let body = or_inr(
                            Expr::app(holds.clone(), hd.clone()),
                            clause_or(holds.clone(), drop_lit(x.clone(), tl.clone())),
                            inner,
                        );
                        f.finish_child(f.mk_lam(htlid, BinderInfo::Default, htl_ty, body))
                    };
                    let m = or_elim(
                        Expr::app(holds.clone(), hd.clone()),
                        clause_or(holds.clone(), tl.clone()),
                        or_target,
                        case_hd,
                        case_tl,
                        hco.clone(),
                    );
                    let body = eq_subst1(
                        bool_ty(),
                        subst_motive.clone(),
                        bfalse(),
                        beq.clone(),
                        eq_symm_at(u1.clone(), bool_ty(), beq.clone(), bfalse(), heq),
                        m,
                    );
                    e.finish_child(e.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                };

                let split = bool_cases(beq, goal, case_f, case_t);
                // fun hd tl ih hco hxf => split
                let r = d.mk_lam(hxfid, BinderInfo::Default, hxf_ty, split);
                let r = d.mk_lam(hcoid, BinderInfo::Default, co_cons, r);
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                let r = d.mk_lam(tlid, BinderInfo::Default, list_nat(), r);
                d.finish_child(d.mk_lam(hdid, BinderInfo::Default, nat_ty(), r))
            };

            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            );
            let folded = Expr::apps(list_rec, [nat_ty(), motive, nil_case, cons_case, c.clone()]);
            let e = b.mk_lam(cid, BinderInfo::Default, list_nat(), folded);
            let e = b.mk_lam(xid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::DROP_FALSE_SAT),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §3 appendSatL / appendSatR : append preserves satisfaction ─────────────

    /// `appendSatL : (H) → (a b : List Nat) → clauseOr H a → clauseOr H (append a b)`.
    fn register_append_sat_l(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::APPEND_SAT_L))
            .is_some()
        {
            return Ok(());
        }
        // mk_type a : clauseOr H a → clauseOr H (append a b)
        let mk_type = |holds: &Expr, a: &Expr, bb: &Expr| -> Expr {
            Expr::arrow(
                clause_or(holds.clone(), a.clone()),
                clause_or(holds.clone(), append(a.clone(), bb.clone())),
            )
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (aid, a) = b.fresh_local(list_nat());
            let (bid, bb) = b.fresh_local(list_nat());
            let body = mk_type(&holds, &a, &bb);
            let e = b.mk_pi(bid, BinderInfo::Default, list_nat(), body);
            let e = b.mk_pi(aid, BinderInfo::Default, list_nat(), e);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (bid, bb) = b.fresh_local(list_nat());
            let (aid, a) = b.fresh_local(list_nat());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_nat());
                let body = mk_type(&holds, &m, &bb);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_nat(), body))
            };
            // nil : fun (h : clauseOr H nil) => False.elim (clauseOr H (append nil b)) h
            let nil_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let nil = Expr::app(
                    Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                    nat_ty(),
                );
                let co_nil = clause_or(holds.clone(), nil.clone());
                let (h0id, h0) = d.fresh_local(co_nil.clone());
                let target = clause_or(holds.clone(), append(nil, bb.clone()));
                let body = false_elim(Level::zero(), target, h0);
                d.finish_child(d.mk_lam(h0id, BinderInfo::Default, co_nil, body))
            };
            // cons : fun hd tl ih (hco : Or (H hd)(clauseOr H tl)) => Or (H hd)(clauseOr H (append tl b))
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (hdid, hd) = d.fresh_local(nat_ty());
                let (tlid, tl) = d.fresh_local(list_nat());
                let ih_ty = mk_type(&holds, &tl, &bb);
                let (ihid, ih) = d.fresh_local(ih_ty.clone());
                let co_cons = clause_or(
                    holds.clone(),
                    Expr::apps(
                        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                        [nat_ty(), hd.clone(), tl.clone()],
                    ),
                );
                let (hcoid, hco) = d.fresh_local(co_cons.clone());
                let hhd = Expr::app(holds.clone(), hd.clone());
                let co_app_tl = clause_or(holds.clone(), append(tl.clone(), bb.clone()));
                // goal at cons: clauseOr H (append (hd::tl) b) ≡ Or (H hd) co_app_tl
                let goal = or_t(hhd.clone(), co_app_tl.clone());
                // case_hd : H hd → goal
                let case_hd = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (xid, xh) = e.fresh_local(hhd.clone());
                    let body = or_inl(hhd.clone(), co_app_tl.clone(), xh);
                    e.finish_child(e.mk_lam(xid, BinderInfo::Default, hhd.clone(), body))
                };
                let case_tl = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let co_tl = clause_or(holds.clone(), tl.clone());
                    let (xid, xt) = e.fresh_local(co_tl.clone());
                    let inner = Expr::app(ih.clone(), xt);
                    let body = or_inr(hhd.clone(), co_app_tl.clone(), inner);
                    e.finish_child(e.mk_lam(xid, BinderInfo::Default, co_tl, body))
                };
                let body = or_elim(
                    hhd,
                    clause_or(holds.clone(), tl.clone()),
                    goal,
                    case_hd,
                    case_tl,
                    hco,
                );
                let r = d.mk_lam(hcoid, BinderInfo::Default, co_cons, body);
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                let r = d.mk_lam(tlid, BinderInfo::Default, list_nat(), r);
                d.finish_child(d.mk_lam(hdid, BinderInfo::Default, nat_ty(), r))
            };
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            );
            let folded = Expr::apps(list_rec, [nat_ty(), motive, nil_case, cons_case, a.clone()]);
            let e = b.mk_lam(bid, BinderInfo::Default, list_nat(), folded);
            let e = b.mk_lam(aid, BinderInfo::Default, list_nat(), e);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::APPEND_SAT_L),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `appendSatR : (H) → (a b : List Nat) → clauseOr H b → clauseOr H (append a b)`.
    fn register_append_sat_r(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::APPEND_SAT_R))
            .is_some()
        {
            return Ok(());
        }
        // mk_type a : clauseOr H b → clauseOr H (append a b)
        let mk_type = |holds: &Expr, a: &Expr, bb: &Expr| -> Expr {
            Expr::arrow(
                clause_or(holds.clone(), bb.clone()),
                clause_or(holds.clone(), append(a.clone(), bb.clone())),
            )
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (aid, a) = b.fresh_local(list_nat());
            let (bid, bb) = b.fresh_local(list_nat());
            let body = mk_type(&holds, &a, &bb);
            let e = b.mk_pi(bid, BinderInfo::Default, list_nat(), body);
            let e = b.mk_pi(aid, BinderInfo::Default, list_nat(), e);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (bid, bb) = b.fresh_local(list_nat());
            let (aid, a) = b.fresh_local(list_nat());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_nat());
                let body = mk_type(&holds, &m, &bb);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_nat(), body))
            };
            // nil : fun (h : clauseOr H b) => h   (append nil b ≡ b)
            let nil_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let co_b = clause_or(holds.clone(), bb.clone());
                let (h0id, h0) = d.fresh_local(co_b.clone());
                d.finish_child(d.mk_lam(h0id, BinderInfo::Default, co_b, h0))
            };
            // cons : fun hd tl ih (hb : clauseOr H b) => Or.inr (H hd) (ih hb)
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (hdid, hd) = d.fresh_local(nat_ty());
                let (tlid, tl) = d.fresh_local(list_nat());
                let ih_ty = mk_type(&holds, &tl, &bb);
                let (ihid, ih) = d.fresh_local(ih_ty.clone());
                let co_b = clause_or(holds.clone(), bb.clone());
                let (hbid, hb) = d.fresh_local(co_b.clone());
                let hhd = Expr::app(holds.clone(), hd.clone());
                let co_app_tl = clause_or(holds.clone(), append(tl.clone(), bb.clone()));
                let inner = Expr::app(ih.clone(), hb);
                let body = or_inr(hhd, co_app_tl, inner);
                let r = d.mk_lam(hbid, BinderInfo::Default, co_b, body);
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                let r = d.mk_lam(tlid, BinderInfo::Default, list_nat(), r);
                d.finish_child(d.mk_lam(hdid, BinderInfo::Default, nat_ty(), r))
            };
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            );
            let folded = Expr::apps(list_rec, [nat_ty(), motive, nil_case, cons_case, a.clone()]);
            let e = b.mk_lam(bid, BinderInfo::Default, list_nat(), folded);
            let e = b.mk_lam(aid, BinderInfo::Default, list_nat(), e);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::APPEND_SAT_R),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §4 resolveStepSat : SINGLE-STEP resolution soundness ───────────────────

    /// `resolveStepSat :`
    /// `(H : Nat→Prop) → (a b : List Nat) → (p : Nat) →`
    /// `Or (H p) (H (litNeg p)) →            -- pivot total (model excluded middle)`
    /// `(H p → H (litNeg p) → False) →       -- pivot exclusive (consistent model)`
    /// `clauseOr H a → clauseOr H b →`
    /// `clauseOr H (resolve a b p)`.
    ///
    /// The CORE resolution-soundness lemma. `resolve a b p ≡ dropLit p a ++ dropLit
    /// ¬p b`. Case-split on the pivot via the model's excluded middle:
    ///   * `H p` true: then `H ¬p` is false, so `b`'s satisfaction survives
    ///     `dropLit ¬p` (`dropFalseSat`) and lands in the resolvent's right part
    ///     (`appendSatR`).
    ///   * `H ¬p` true: then `H p` is false, so `a`'s satisfaction survives
    ///     `dropLit p` (`dropFalseSat`) and lands in the left part (`appendSatL`).
    ///
    /// Soundness hinges on the SINGLE oriented drop — the double-polarity drop is
    /// unsound (it can erase the surviving true literal).
    fn register_resolve_step_sat(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::RESOLVE_STEP_SAT))
            .is_some()
        {
            return Ok(());
        }
        let u1 = Level::succ(Level::zero());
        let _ = u1;
        // shared sub-expressions builder
        let build = |val: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (aid, a) = b.fresh_local(list_nat());
            let (bid, bb) = b.fresh_local(list_nat());
            let (pid, p) = b.fresh_local(nat_ty());
            let hp = Expr::app(holds.clone(), p.clone());
            let hnp = Expr::app(holds.clone(), lit_neg(p.clone()));
            let em_ty = or_t(hp.clone(), hnp.clone());
            let excl_ty = Expr::arrow(hp.clone(), Expr::arrow(hnp.clone(), false_c()));
            let co_a = clause_or(holds.clone(), a.clone());
            let co_b = clause_or(holds.clone(), bb.clone());
            let resolvent = clause_or(
                holds.clone(),
                append(
                    drop_lit(p.clone(), a.clone()),
                    drop_lit(lit_neg(p.clone()), bb.clone()),
                ),
            );

            if !val {
                // type_
                let inner = Expr::arrow(co_b.clone(), resolvent.clone());
                let inner = Expr::arrow(co_a.clone(), inner);
                let inner = Expr::arrow(excl_ty.clone(), inner);
                let inner = Expr::arrow(em_ty.clone(), inner);
                let e = b.mk_pi(pid, BinderInfo::Default, nat_ty(), inner);
                let e = b.mk_pi(bid, BinderInfo::Default, list_nat(), e);
                let e = b.mk_pi(aid, BinderInfo::Default, list_nat(), e);
                return b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e));
            }

            // value: fun H a b p (hem : Or (H p)(H ¬p)) (hexcl) (hca) (hcb) => <proof>
            let (hemid, hem) = b.fresh_local(em_ty.clone());
            let (hexclid, hexcl) = b.fresh_local(excl_ty.clone());
            let (hcaid, hca) = b.fresh_local(co_a.clone());
            let (hcbid, hcb) = b.fresh_local(co_b.clone());

            let dl_p_a = drop_lit(p.clone(), a.clone());
            let dl_np_b = drop_lit(lit_neg(p.clone()), bb.clone());

            // case inl (hp : H p): drop ¬p from b is false.
            let case_inl = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let (hpid, hpv) = e.fresh_local(hp.clone());
                // hnpf : H ¬p → False := fun hnp => hexcl hp hnp
                let hnpf = {
                    let mut f = EnvDeclBuilder::child_of(&e);
                    let (xid, xnp) = f.fresh_local(hnp.clone());
                    let body = Expr::apps(hexcl.clone(), [hpv.clone(), xnp]);
                    f.finish_child(f.mk_lam(xid, BinderInfo::Default, hnp.clone(), body))
                };
                // dropFalseSat H ¬p b hcb hnpf : clauseOr H (dropLit ¬p b)
                let dfs = Expr::apps(
                    Expr::const_str(names::DROP_FALSE_SAT),
                    [
                        holds.clone(),
                        lit_neg(p.clone()),
                        bb.clone(),
                        hcb.clone(),
                        hnpf,
                    ],
                );
                // appendSatR H (dropLit p a) (dropLit ¬p b) dfs
                let body = Expr::apps(
                    Expr::const_str(names::APPEND_SAT_R),
                    [holds.clone(), dl_p_a.clone(), dl_np_b.clone(), dfs],
                );
                e.finish_child(e.mk_lam(hpid, BinderInfo::Default, hp.clone(), body))
            };

            // case inr (hnp : H ¬p): drop p from a is false.
            let case_inr = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let (hnpid, hnpv) = e.fresh_local(hnp.clone());
                // hpf : H p → False := fun hp => hexcl hp hnp
                let hpf = {
                    let mut f = EnvDeclBuilder::child_of(&e);
                    let (xid, xp) = f.fresh_local(hp.clone());
                    let body = Expr::apps(hexcl.clone(), [xp, hnpv.clone()]);
                    f.finish_child(f.mk_lam(xid, BinderInfo::Default, hp.clone(), body))
                };
                // dropFalseSat H p a hca hpf : clauseOr H (dropLit p a)
                let dfs = Expr::apps(
                    Expr::const_str(names::DROP_FALSE_SAT),
                    [holds.clone(), p.clone(), a.clone(), hca.clone(), hpf],
                );
                // appendSatL H (dropLit p a) (dropLit ¬p b) dfs
                let body = Expr::apps(
                    Expr::const_str(names::APPEND_SAT_L),
                    [holds.clone(), dl_p_a.clone(), dl_np_b.clone(), dfs],
                );
                e.finish_child(e.mk_lam(hnpid, BinderInfo::Default, hnp.clone(), body))
            };

            let proof = or_elim(hp, hnp, resolvent, case_inl, case_inr, hem.clone());
            let r = b.mk_lam(hcbid, BinderInfo::Default, co_b, proof);
            let r = b.mk_lam(hcaid, BinderInfo::Default, co_a, r);
            let r = b.mk_lam(hexclid, BinderInfo::Default, excl_ty, r);
            let r = b.mk_lam(hemid, BinderInfo::Default, em_ty, r);
            let r = b.mk_lam(pid, BinderInfo::Default, nat_ty(), r);
            let r = b.mk_lam(bid, BinderInfo::Default, list_nat(), r);
            let r = b.mk_lam(aid, BinderInfo::Default, list_nat(), r);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), r))
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::RESOLVE_STEP_SAT),
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }

    // ── §5 membership / subset reflection ──────────────────────────────────────

    /// `memSat : (H) → (x : Nat) → (c : List Nat) → Eq (clauseMem x c) true →`
    /// `H x → clauseOr H c`.
    ///
    /// `List.rec` on `c`. At `cons hd tl`, `clauseMem x (hd::tl) ≡ Bool.or (litBeq x
    /// hd) (clauseMem x tl)`; split on `litBeq x hd` — `true` ⇒ `x = hd` (`natBeqEq`)
    /// so `H x` gives `H hd` (`Or.inl`); `false` ⇒ the disjunction's truth lands on
    /// the tail, recurse (`Or.inr`).
    fn register_mem_sat(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(names::MEM_SAT)).is_some() {
            return Ok(());
        }
        let u1 = Level::succ(Level::zero());
        let mk_type = |holds: &Expr, x: &Expr, c: &Expr| -> Expr {
            Expr::arrow(
                eq_bool(clause_mem(x.clone(), c.clone()), btrue()),
                Expr::arrow(
                    Expr::app(holds.clone(), x.clone()),
                    clause_or(holds.clone(), c.clone()),
                ),
            )
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (xid, x) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(list_nat());
            let body = mk_type(&holds, &x, &c);
            let e = b.mk_pi(cid, BinderInfo::Default, list_nat(), body);
            let e = b.mk_pi(xid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (xid, x) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(list_nat());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_nat());
                let body = mk_type(&holds, &x, &m);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_nat(), body))
            };
            // nil : fun (hmem : clauseMem x nil = true) (_ : H x) =>
            //   clauseMem x nil ≡ false ⇒ hmem : false = true ⇒ absurd.
            let nil_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let hmem_ty = eq_bool(clause_mem(x.clone(), list_nil_nat()), btrue());
                let (hmid, hm) = d.fresh_local(hmem_ty.clone());
                let hhx_ty = Expr::app(holds.clone(), x.clone());
                let (hxid, _hx) = d.fresh_local(hhx_ty.clone());
                let ff = tf_to_false(eq_symm_at(u1.clone(), bool_ty(), bfalse(), btrue(), hm));
                let target = clause_or(holds.clone(), list_nil_nat());
                let body = false_elim(Level::zero(), target, ff);
                let r = d.mk_lam(hxid, BinderInfo::Default, hhx_ty, body);
                d.finish_child(d.mk_lam(hmid, BinderInfo::Default, hmem_ty, r))
            };
            // cons hd tl ih (hmem : Bool.or (litBeq x hd)(clauseMem x tl) = true)(hx : H x)
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (hdid, hd) = d.fresh_local(nat_ty());
                let (tlid, tl) = d.fresh_local(list_nat());
                let ih_ty = mk_type(&holds, &x, &tl);
                let (ihid, ih) = d.fresh_local(ih_ty.clone());
                let beq = lit_beq(x.clone(), hd.clone());
                let mem_tl = clause_mem(x.clone(), tl.clone());
                let bor_e = Expr::apps(Expr::const_str("Bool.or"), [beq.clone(), mem_tl.clone()]);
                let hmem_ty = eq_bool(bor_e.clone(), btrue());
                let (hmid, hm) = d.fresh_local(hmem_ty.clone());
                let hhx_ty = Expr::app(holds.clone(), x.clone());
                let (hxid, hx) = d.fresh_local(hhx_ty.clone());
                let hhd = Expr::app(holds.clone(), hd.clone());
                let co_tl = clause_or(holds.clone(), tl.clone());
                let goal = or_t(hhd.clone(), co_tl.clone());
                // split on litBeq x hd
                // case_t (heq : litBeq x hd = true): x=hd, H hd from H x, Or.inl.
                let case_t = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let heq_ty = eq_bool(beq.clone(), btrue());
                    let (heqid, heq) = e.fresh_local(heq_ty.clone());
                    let xeqhd = Expr::apps(
                        Expr::const_str(names::NAT_BEQ_EQ),
                        [x.clone(), hd.clone(), heq],
                    );
                    // H hd := Eq.subst H x hd xeqhd hx
                    let hhd_proof = eq_subst1(
                        nat_ty(),
                        holds.clone(),
                        x.clone(),
                        hd.clone(),
                        xeqhd,
                        hx.clone(),
                    );
                    let body = or_inl(hhd.clone(), co_tl.clone(), hhd_proof);
                    e.finish_child(e.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                };
                // case_f (heq : litBeq x hd = false): Bool.or false (mem tl) ≡ mem tl,
                //   so mem tl = true. ih (that) hx : clauseOr H tl. Or.inr.
                let case_f = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let heq_ty = eq_bool(beq.clone(), bfalse());
                    let (heqid, heq) = e.fresh_local(heq_ty.clone());
                    // rewrite hmem along heq : Eq.subst (fun bb => Bool.or bb (mem tl) = true)
                    //   beq false heq hmem : Bool.or false (mem tl) = true ≡ mem tl = true
                    let rewrite_motive = {
                        let inner = eq_bool(
                            Expr::apps(Expr::const_str("Bool.or"), [Expr::bvar(0), mem_tl.clone()]),
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
                    // ih mem_true hx : clauseOr H tl
                    let co = Expr::apps(ih.clone(), [mem_true, hx.clone()]);
                    let body = or_inr(hhd.clone(), co_tl.clone(), co);
                    e.finish_child(e.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                };
                let split = bool_cases(beq, goal, case_f, case_t);
                let r = d.mk_lam(hxid, BinderInfo::Default, hhx_ty, split);
                let r = d.mk_lam(hmid, BinderInfo::Default, hmem_ty, r);
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                let r = d.mk_lam(tlid, BinderInfo::Default, list_nat(), r);
                d.finish_child(d.mk_lam(hdid, BinderInfo::Default, nat_ty(), r))
            };
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            );
            let folded = Expr::apps(list_rec, [nat_ty(), motive, nil_case, cons_case, c.clone()]);
            let e = b.mk_lam(cid, BinderInfo::Default, list_nat(), folded);
            let e = b.mk_lam(xid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::MEM_SAT),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `subsetSat : (H) → (c1 c2 : List Nat) → Eq (clauseSubset c1 c2) true →`
    /// `clauseOr H c1 → clauseOr H c2`.
    ///
    /// `List.rec` on `c1`. `clauseSubset (hd::tl) c2 ≡ Bool.and (clauseMem hd c2)
    /// (clauseSubset tl c2)`; from `= true` both conjuncts are `true`. `clauseOr H
    /// (hd::tl) ≡ Or (H hd) (clauseOr H tl)`: the `H hd` case uses `memSat hd c2`
    /// (`hd ∈ c2`); the tail case recurses.
    fn register_subset_sat(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::SUBSET_SAT))
            .is_some()
        {
            return Ok(());
        }
        let u1 = Level::succ(Level::zero());
        let subset = |a: Expr, c: Expr| Expr::apps(Expr::const_str(rnames::CLAUSE_SUBSET), [a, c]);
        let mk_type = |holds: &Expr, c1: &Expr, c2: &Expr| -> Expr {
            Expr::arrow(
                eq_bool(subset(c1.clone(), c2.clone()), btrue()),
                Expr::arrow(
                    clause_or(holds.clone(), c1.clone()),
                    clause_or(holds.clone(), c2.clone()),
                ),
            )
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (c1id, c1) = b.fresh_local(list_nat());
            let (c2id, c2) = b.fresh_local(list_nat());
            let body = mk_type(&holds, &c1, &c2);
            let e = b.mk_pi(c2id, BinderInfo::Default, list_nat(), body);
            let e = b.mk_pi(c1id, BinderInfo::Default, list_nat(), e);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (c2id, c2) = b.fresh_local(list_nat());
            let (c1id, c1) = b.fresh_local(list_nat());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_nat());
                let body = mk_type(&holds, &m, &c2);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_nat(), body))
            };
            // nil : fun (_hsub)(hco : clauseOr H nil ≡ False) => False.elim _ hco
            let nil_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let hsub_ty = eq_bool(subset(list_nil_nat(), c2.clone()), btrue());
                let (hsid, _hs) = d.fresh_local(hsub_ty.clone());
                let co_nil = clause_or(holds.clone(), list_nil_nat());
                let (hcoid, hco) = d.fresh_local(co_nil.clone());
                let target = clause_or(holds.clone(), c2.clone());
                let body = false_elim(Level::zero(), target, hco);
                let r = d.mk_lam(hcoid, BinderInfo::Default, co_nil, body);
                d.finish_child(d.mk_lam(hsid, BinderInfo::Default, hsub_ty, r))
            };
            // cons hd tl ih (hsub : Bool.and (clauseMem hd c2)(clauseSubset tl c2) = true)
            //              (hco : Or (H hd)(clauseOr H tl)) => clauseOr H c2
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (hdid, hd) = d.fresh_local(nat_ty());
                let (tlid, tl) = d.fresh_local(list_nat());
                let ih_ty = mk_type(&holds, &tl, &c2);
                let (ihid, ih) = d.fresh_local(ih_ty.clone());
                let mem_hd = clause_mem(hd.clone(), c2.clone());
                let sub_tl = subset(tl.clone(), c2.clone());
                let band_e = Expr::apps(
                    Expr::const_str("Bool.and"),
                    [mem_hd.clone(), sub_tl.clone()],
                );
                let hsub_ty = eq_bool(band_e.clone(), btrue());
                let (hsid, hs) = d.fresh_local(hsub_ty.clone());
                let co_cons = clause_or(holds.clone(), list_cons_nat(hd.clone(), tl.clone()));
                let (hcoid, hco) = d.fresh_local(co_cons.clone());
                let hhd = Expr::app(holds.clone(), hd.clone());
                let co_tl = clause_or(holds.clone(), tl.clone());
                let co_c2 = clause_or(holds.clone(), c2.clone());
                // From hs : Bool.and (mem hd c2)(sub tl c2) = true, derive both.
                //   memHd_true := Eq.trans? Simpler: Bool.and b1 b2 = true ⇒ b1=true via
                //   Eq.subst on Bool.rec. We use andElim helpers inline:
                //   mem hd c2 = true := bool_and_elim_left ; sub tl c2 = true := right.
                let mem_true = bool_and_elim_left(mem_hd.clone(), sub_tl.clone(), hs.clone());
                let sub_true = bool_and_elim_right(mem_hd, sub_tl, hs);
                // case_hd : H hd → clauseOr H c2 := fun hhd_p => memSat H hd c2 mem_true hhd_p
                let case_hd = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (xid, xh) = e.fresh_local(hhd.clone());
                    let body = Expr::apps(
                        Expr::const_str(names::MEM_SAT),
                        [holds.clone(), hd.clone(), c2.clone(), mem_true.clone(), xh],
                    );
                    e.finish_child(e.mk_lam(xid, BinderInfo::Default, hhd.clone(), body))
                };
                // case_tl : clauseOr H tl → clauseOr H c2 := fun htl => ih sub_true htl
                let case_tl = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (xid, xt) = e.fresh_local(co_tl.clone());
                    let body = Expr::apps(ih.clone(), [sub_true.clone(), xt]);
                    e.finish_child(e.mk_lam(xid, BinderInfo::Default, co_tl.clone(), body))
                };
                let body = or_elim(hhd, co_tl, co_c2, case_hd, case_tl, hco);
                let r = d.mk_lam(hcoid, BinderInfo::Default, co_cons, body);
                let r = d.mk_lam(hsid, BinderInfo::Default, hsub_ty, r);
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                let r = d.mk_lam(tlid, BinderInfo::Default, list_nat(), r);
                d.finish_child(d.mk_lam(hdid, BinderInfo::Default, nat_ty(), r))
            };
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            );
            let folded = Expr::apps(
                list_rec,
                [nat_ty(), motive, nil_case, cons_case, c1.clone()],
            );
            let _ = u1;
            let e = b.mk_lam(c2id, BinderInfo::Default, list_nat(), folded);
            let e = b.mk_lam(c1id, BinderInfo::Default, list_nat(), e);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::SUBSET_SAT),
            level_params: vec![],
            type_,
            value,
        })
    }
}

impl Environment {
    // ── §6 seteqSat : set-equal clauses are co-satisfiable ─────────────────────

    /// `seteqSat : (H) → (c1 c2 : List Nat) → Eq (clauseSeteq c1 c2) true →`
    /// `clauseOr H c1 → clauseOr H c2`.
    ///
    /// `clauseSeteq c1 c2 ≡ Bool.and (clauseSubset c1 c2) (clauseSubset c2 c1)`; the
    /// left conjunct (`c1 ⊆ c2`) plus `subsetSat` gives the implication.
    fn register_seteq_sat(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::SETEQ_SAT))
            .is_some()
        {
            return Ok(());
        }
        let subset = |a: Expr, c: Expr| Expr::apps(Expr::const_str(rnames::CLAUSE_SUBSET), [a, c]);
        let seteq = |a: Expr, c: Expr| Expr::apps(Expr::const_str(rnames::CLAUSE_SETEQ), [a, c]);
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (c1id, c1) = b.fresh_local(list_nat());
            let (c2id, c2) = b.fresh_local(list_nat());
            let inner = Expr::arrow(
                eq_bool(seteq(c1.clone(), c2.clone()), btrue()),
                Expr::arrow(
                    clause_or(holds.clone(), c1.clone()),
                    clause_or(holds.clone(), c2.clone()),
                ),
            );
            let e = b.mk_pi(c2id, BinderInfo::Default, list_nat(), inner);
            let e = b.mk_pi(c1id, BinderInfo::Default, list_nat(), e);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (c1id, c1) = b.fresh_local(list_nat());
            let (c2id, c2) = b.fresh_local(list_nat());
            let hseteq_ty = eq_bool(seteq(c1.clone(), c2.clone()), btrue());
            let (hsid, hs) = b.fresh_local(hseteq_ty.clone());
            let co1_ty = clause_or(holds.clone(), c1.clone());
            let (hcoid, hco) = b.fresh_local(co1_ty.clone());
            // subset c1 c2 = true from And-left of hs
            let sub12_true = bool_and_elim_left(
                subset(c1.clone(), c2.clone()),
                subset(c2.clone(), c1.clone()),
                hs,
            );
            // subsetSat H c1 c2 sub12_true hco
            let body = Expr::apps(
                Expr::const_str(names::SUBSET_SAT),
                [holds.clone(), c1.clone(), c2.clone(), sub12_true, hco],
            );
            let r = b.mk_lam(hcoid, BinderInfo::Default, co1_ty, body);
            let r = b.mk_lam(hsid, BinderInfo::Default, hseteq_ty, r);
            let r = b.mk_lam(c2id, BinderInfo::Default, list_nat(), r);
            let r = b.mk_lam(c1id, BinderInfo::Default, list_nat(), r);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::SETEQ_SAT),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §7 model semantics (real kernel definitions, replacing the opaque axioms)

    /// Register `allSat`, `resConsistent`, `resExclusive`, `Unsat` as `Definition`s.
    fn register_semantics(&mut self) -> Result<(), EnvError> {
        // allSat H db := List.rec True (fun c _ ih => And (clauseOr H c) ih) db
        if self.get_const(&Name::from_string(names::ALL_SAT)).is_none() {
            let ty = Expr::arrow(holds_ty(), Expr::arrow(list_list_nat(), Expr::prop()));
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty());
                let (dbid, db) = b.fresh_local(list_list_nat());
                // cons case : fun (c : List Nat) (_ : List(List Nat)) (ih : Prop) =>
                //   And (clauseOr H c) ih
                let cons_case = {
                    let c = Expr::bvar(2);
                    let and = Expr::apps(
                        Expr::const_(Name::from_string("And"), vec![]),
                        [clause_or(holds.clone(), c), Expr::bvar(0)],
                    );
                    Expr::lam(
                        BinderInfo::Default,
                        list_nat(),
                        Expr::lam(
                            BinderInfo::Default,
                            list_list_nat(),
                            Expr::lam(BinderInfo::Default, Expr::prop(), and),
                        ),
                    )
                };
                let rec = Expr::const_(
                    Name::from_string("List.rec"),
                    vec![Level::succ(Level::zero()), Level::zero()],
                );
                let motive = Expr::lam(BinderInfo::Default, list_list_nat(), Expr::prop());
                let body = Expr::apps(
                    rec,
                    [list_nat(), motive, Expr::const_str("True"), cons_case, db],
                );
                let e = b.mk_lam(dbid, BinderInfo::Default, list_list_nat(), body);
                b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::ALL_SAT),
                level_params: vec![],
                type_: ty,
                value: val,
                is_reducible: true,
            })?;
        }

        // resConsistent H := (l : Nat) → Or (H l) (H (litNeg l))
        if self
            .get_const(&Name::from_string(names::RES_CONSISTENT))
            .is_none()
        {
            let ty = Expr::arrow(holds_ty(), Expr::prop());
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty());
                let inner = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (lid, l) = c.fresh_local(nat_ty());
                    let body = or_t(
                        Expr::app(holds.clone(), l.clone()),
                        Expr::app(holds.clone(), lit_neg(l.clone())),
                    );
                    c.finish_child(c.mk_pi(lid, BinderInfo::Default, nat_ty(), body))
                };
                b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), inner))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::RES_CONSISTENT),
                level_params: vec![],
                type_: ty,
                value: val,
                is_reducible: true,
            })?;
        }

        // resExclusive H := (l : Nat) → H l → H (litNeg l) → False
        if self
            .get_const(&Name::from_string(names::RES_EXCLUSIVE))
            .is_none()
        {
            let ty = Expr::arrow(holds_ty(), Expr::prop());
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty());
                let inner = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (lid, l) = c.fresh_local(nat_ty());
                    let body = Expr::arrow(
                        Expr::app(holds.clone(), l.clone()),
                        Expr::arrow(Expr::app(holds.clone(), lit_neg(l.clone())), false_c()),
                    );
                    c.finish_child(c.mk_pi(lid, BinderInfo::Default, nat_ty(), body))
                };
                b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), inner))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::RES_EXCLUSIVE),
                level_params: vec![],
                type_: ty,
                value: val,
                is_reducible: true,
            })?;
        }

        // Unsat cs := (H : Nat→Prop) → resConsistent H → resExclusive H → allSat H cs → False
        if self.get_const(&Name::from_string(names::UNSAT)).is_none() {
            let ty = Expr::arrow(list_list_nat(), Expr::prop());
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (csid, cs) = b.fresh_local(list_list_nat());
                let inner = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hid, holds) = c.fresh_local(holds_ty());
                    let cons = Expr::app(Expr::const_str(names::RES_CONSISTENT), holds.clone());
                    let excl = Expr::app(Expr::const_str(names::RES_EXCLUSIVE), holds.clone());
                    let all =
                        Expr::apps(Expr::const_str(names::ALL_SAT), [holds.clone(), cs.clone()]);
                    let body = Expr::arrow(all, false_c());
                    let body = Expr::arrow(excl, body);
                    let body = Expr::arrow(cons, body);
                    c.finish_child(c.mk_pi(hid, BinderInfo::Default, holds_ty(), body))
                };
                b.finish(b.mk_lam(csid, BinderInfo::Default, list_list_nat(), inner))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::UNSAT),
                level_params: vec![],
                type_: ty,
                value: val,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    // ── §8 nthSat : every clause fetched from a satisfied DB is satisfied ──────

    /// `nthSat : (H) → (db : List (List Nat)) → allSat H db → (i : Nat) →`
    /// `Or (clauseOr H (nth db i)) (Eq (nth db i) List.nil)`.
    ///
    /// `List.rec` on `db` with `i` generalised. `nil` ⇒ `nth = nil` (right). `cons c
    /// cs` ⇒ `allSat ≡ And (clauseOr H c) (allSat H cs)`; case on `i` — `0` fetches
    /// `c` (left, from `And`-left), `succ k` recurses into `cs` with `And`-right.
    fn register_nth_sat(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(names::NTH_SAT)).is_some() {
            return Ok(());
        }
        let u1 = Level::succ(Level::zero());
        let nth = |db: Expr, i: Expr| Expr::apps(Expr::const_str(rnames::NTH), [db, i]);
        let all_sat = |db: Expr, holds: &Expr| {
            Expr::apps(Expr::const_str(names::ALL_SAT), [holds.clone(), db])
        };
        // result_of db i := Or (clauseOr H (nth db i)) (Eq (nth db i) nil)
        let result_of = |holds: &Expr, db: &Expr, i: &Expr| -> Expr {
            or_t(
                clause_or(holds.clone(), nth(db.clone(), i.clone())),
                eq_at(
                    u1.clone(),
                    list_nat(),
                    nth(db.clone(), i.clone()),
                    list_nil_nat(),
                ),
            )
        };
        // motive over db : fun db => allSat H db → (i : Nat) → result_of db i
        let mk_motive_body = |holds: &Expr, db: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut c = EnvDeclBuilder::child_of(parent);
            let (iid, i) = c.fresh_local(nat_ty());
            let res = result_of(holds, db, &i);
            let forall_i = c.finish_child(c.mk_pi(iid, BinderInfo::Default, nat_ty(), res));
            Expr::arrow(all_sat(db.clone(), holds), forall_i)
        };

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (dbid, db) = b.fresh_local(list_list_nat());
            let body = mk_motive_body(&holds, &db, &b);
            let e = b.mk_pi(dbid, BinderInfo::Default, list_list_nat(), body);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (dbid, db) = b.fresh_local(list_list_nat());

            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_list_nat());
                let body = mk_motive_body(&holds, &m, &d);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_list_nat(), body))
            };

            // nil : fun (_ : allSat H nil) (i : Nat) => Or.inr (rfl : nth nil i = nil)
            let nil_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let nil_db = Expr::app(
                    Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                    list_nat(),
                );
                let as_ty = all_sat(nil_db.clone(), &holds);
                let (asid, _as) = d.fresh_local(as_ty.clone());
                let inner = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (iid, i) = e.fresh_local(nat_ty());
                    // nth nil i ≡ nil, so rfl : nth nil i = nil
                    let lhs = nth(nil_db.clone(), i.clone());
                    let refl = eq_refl_at(u1.clone(), list_nat(), lhs.clone());
                    let body = or_inr(
                        clause_or(holds.clone(), lhs.clone()),
                        eq_at(u1.clone(), list_nat(), lhs, list_nil_nat()),
                        refl,
                    );
                    e.finish_child(e.mk_lam(iid, BinderInfo::Default, nat_ty(), body))
                };
                d.finish_child(d.mk_lam(asid, BinderInfo::Default, as_ty, inner))
            };

            // cons c cs ih (hall : allSat H (c::cs) ≡ And (clauseOr H c)(allSat H cs)) (i) => ...
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (cid, c) = d.fresh_local(list_nat());
                let (csid, cs) = d.fresh_local(list_list_nat());
                let ih_ty = mk_motive_body(&holds, &cs, &d);
                let (ihid, ih) = d.fresh_local(ih_ty.clone());
                let db_cons = Expr::apps(
                    Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                    [list_nat(), c.clone(), cs.clone()],
                );
                let hall_ty = all_sat(db_cons.clone(), &holds);
                let (hallid, hall) = d.fresh_local(hall_ty.clone());
                // And components: hall : And (clauseOr H c) (allSat H cs)
                let co_c = clause_or(holds.clone(), c.clone());
                let all_cs = all_sat(cs.clone(), &holds);
                let left = and_left(co_c.clone(), all_cs.clone(), hall.clone());
                let right = and_right(co_c.clone(), all_cs.clone(), hall.clone());
                // fun (i : Nat) => Nat.rec (motive := fun i => result_of (c::cs) i) i0 isucc i
                let inner = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (iid, i) = e.fresh_local(nat_ty());
                    // i-motive : fun i => result_of (c::cs) i
                    let i_motive = {
                        let mut f = EnvDeclBuilder::child_of(&e);
                        let (mid, m) = f.fresh_local(nat_ty());
                        let body = result_of(&holds, &db_cons, &m);
                        f.finish_child(f.mk_lam(mid, BinderInfo::Default, nat_ty(), body))
                    };
                    // i=0 : nth (c::cs) 0 ≡ c. Or.inl (left : clauseOr H c).
                    let i0 = {
                        let z = nat_zero();
                        let lhs = nth(db_cons.clone(), z);
                        or_inl(
                            clause_or(holds.clone(), lhs.clone()),
                            eq_at(u1.clone(), list_nat(), lhs, list_nil_nat()),
                            left.clone(),
                        )
                    };
                    // i=succ k : fun (k : Nat) (_ih) => ih right k : result_of cs k
                    //   (nth (c::cs)(succ k) ≡ nth cs k, defeq).
                    let isucc = {
                        let mut f = EnvDeclBuilder::child_of(&e);
                        let (kid, k) = f.fresh_local(nat_ty());
                        // Nat.rec succ-minor: (k) → M k → M (succ k), M i := result_of (c::cs) i.
                        let rec_res_ty = result_of(&holds, &db_cons, &k);
                        let (ihkid, _ihk) = f.fresh_local(rec_res_ty.clone());
                        // ih right k : result_of cs k ≡ result_of (c::cs) (succ k) by defeq.
                        let body = Expr::app(Expr::app(ih.clone(), right.clone()), k.clone());
                        let r = f.mk_lam(ihkid, BinderInfo::Default, rec_res_ty, body);
                        f.finish_child(f.mk_lam(kid, BinderInfo::Default, nat_ty(), r))
                    };
                    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
                    let fold = Expr::apps(nat_rec, [i_motive, i0, isucc, i.clone()]);
                    e.finish_child(e.mk_lam(iid, BinderInfo::Default, nat_ty(), fold))
                };
                let r = d.mk_lam(hallid, BinderInfo::Default, hall_ty, inner);
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                let r = d.mk_lam(csid, BinderInfo::Default, list_list_nat(), r);
                d.finish_child(d.mk_lam(cid, BinderInfo::Default, list_nat(), r))
            };

            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            );
            let folded = Expr::apps(
                list_rec,
                [list_nat(), motive, nil_case, cons_case, db.clone()],
            );
            let e = b.mk_lam(dbid, BinderInfo::Default, list_list_nat(), folded);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::NTH_SAT),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `memNotNil : (x : Nat) → (c : List Nat) → Eq (clauseMem x c) true →`
    /// `Eq c List.nil → False`.
    ///
    /// Rewriting `c ↦ nil` in `clauseMem x c = true` gives `clauseMem x nil = true ≡
    /// false = true`, absurd. (Discharges the `nth db i = nil` disjunct of `nthSat`
    /// once a pivot is known to be a member of that clause.)
    fn register_mem_not_nil(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::MEM_NOT_NIL))
            .is_some()
        {
            return Ok(());
        }
        let u1 = Level::succ(Level::zero());
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (xid, x) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(list_nat());
            let inner = Expr::arrow(
                eq_bool(clause_mem(x.clone(), c.clone()), btrue()),
                Expr::arrow(
                    eq_at(u1.clone(), list_nat(), c.clone(), list_nil_nat()),
                    false_c(),
                ),
            );
            let e = b.mk_pi(cid, BinderInfo::Default, list_nat(), inner);
            b.finish(b.mk_pi(xid, BinderInfo::Default, nat_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (xid, x) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(list_nat());
            let hmem_ty = eq_bool(clause_mem(x.clone(), c.clone()), btrue());
            let (hmid, hm) = b.fresh_local(hmem_ty.clone());
            let hnil_ty = eq_at(u1.clone(), list_nat(), c.clone(), list_nil_nat());
            let (hnid, hn) = b.fresh_local(hnil_ty.clone());
            let motive = {
                let inner = eq_bool(clause_mem(x.clone(), Expr::bvar(0)), btrue());
                Expr::lam(BinderInfo::Default, list_nat(), inner)
            };
            let mem_nil_true = eq_subst1(list_nat(), motive, c.clone(), list_nil_nat(), hn, hm);
            let ff = tf_to_false(eq_symm_at(
                u1.clone(),
                bool_ty(),
                bfalse(),
                btrue(),
                mem_nil_true,
            ));
            let r = b.mk_lam(hnid, BinderInfo::Default, hnil_ty, ff);
            let r = b.mk_lam(hmid, BinderInfo::Default, hmem_ty, r);
            let r = b.mk_lam(cid, BinderInfo::Default, list_nat(), r);
            b.finish(b.mk_lam(xid, BinderInfo::Default, nat_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::MEM_NOT_NIL),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §9 checkStepSat : step-level soundness bridge ──────────────────────────

    /// `checkStepSat :`
    /// `(H) → (db) → (s : Step) → resConsistent H → resExclusive H → allSat H db →`
    /// `Eq (checkStep db s) true → clauseOr H (stepResolvent s)`.
    ///
    /// Destructure `s = mk r p1 p2 pivot` (`Step.rec`). `checkStep ≡ And oriented
    /// tautFree`; `oriented ≡ Bool.or branchA branchB`. `bool_or_elim` splits the two
    /// legal orientations; in each, the premises are non-nil (`memNotNil` discharges
    /// the `nth = nil` disjunct of `nthSat`, giving `clauseOr H A`, `clauseOr H B`),
    /// `resolveStepSat` (with the model's `resConsistent`/`resExclusive` at the pivot)
    /// gives `clauseOr H (resolve …)`, and `subsetSat` on the recorded-vs-computed
    /// set-equality transports it to `clauseOr H r`.
    fn register_check_step_sat(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::CHECK_STEP_SAT))
            .is_some()
        {
            return Ok(());
        }
        let step_ty = Expr::const_str(rnames::STEP);
        let check_step =
            |db: Expr, s: Expr| Expr::apps(Expr::const_str(rnames::CHECK_STEP), [db, s]);
        let step_resolvent = |s: Expr| Expr::app(Expr::const_str("Clean.Res.stepResolvent"), s);
        let cons_pred = |h: &Expr| Expr::app(Expr::const_str(names::RES_CONSISTENT), h.clone());
        let excl_pred = |h: &Expr| Expr::app(Expr::const_str(names::RES_EXCLUSIVE), h.clone());
        let all_sat =
            |db: Expr, h: &Expr| Expr::apps(Expr::const_str(names::ALL_SAT), [h.clone(), db]);

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (dbid, db) = b.fresh_local(list_list_nat());
            let (sid, s) = b.fresh_local(step_ty.clone());
            let concl = clause_or(holds.clone(), step_resolvent(s.clone()));
            let inner = Expr::arrow(eq_bool(check_step(db.clone(), s.clone()), btrue()), concl);
            let inner = Expr::arrow(all_sat(db.clone(), &holds), inner);
            let inner = Expr::arrow(excl_pred(&holds), inner);
            let inner = Expr::arrow(cons_pred(&holds), inner);
            let e = b.mk_pi(sid, BinderInfo::Default, step_ty.clone(), inner);
            let e = b.mk_pi(dbid, BinderInfo::Default, list_list_nat(), e);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (dbid, db) = b.fresh_local(list_list_nat());
            let (sid, s) = b.fresh_local(step_ty.clone());
            let (hcid, hcons) = b.fresh_local(cons_pred(&holds));
            let (heid, hexcl) = b.fresh_local(excl_pred(&holds));
            let (haid, hall) = b.fresh_local(all_sat(db.clone(), &holds));

            // Step.rec motive : fun s => Eq (checkStep db s) true → clauseOr H (stepResolvent s)
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(step_ty.clone());
                let body = Expr::arrow(
                    eq_bool(check_step(db.clone(), m.clone()), btrue()),
                    clause_or(holds.clone(), step_resolvent(m.clone())),
                );
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, step_ty.clone(), body))
            };

            // mk_case : fun (r : List Nat)(p1 p2 pivot : Nat) =>
            //   fun (hcheck : Eq (checkStep db (mk r p1 p2 pivot)) true) => <proof of clauseOr H r>
            let mk_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (rid, r) = d.fresh_local(list_nat());
                let (p1id, p1) = d.fresh_local(nat_ty());
                let (p2id, p2) = d.fresh_local(nat_ty());
                let (pvid, pivot) = d.fresh_local(nat_ty());
                let step_e = Expr::apps(
                    Expr::const_str(rnames::STEP_MK),
                    [r.clone(), p1.clone(), p2.clone(), pivot.clone()],
                );
                let hcheck_ty = eq_bool(check_step(db.clone(), step_e), btrue());
                let (hcheckid, hcheck) = d.fresh_local(hcheck_ty.clone());

                // computed pieces
                let a_cl = Expr::apps(Expr::const_str(rnames::NTH), [db.clone(), p1.clone()]);
                let b_cl = Expr::apps(Expr::const_str(rnames::NTH), [db.clone(), p2.clone()]);
                let np = lit_neg(pivot.clone());
                let resolve = |x: Expr, y: Expr| {
                    Expr::apps(Expr::const_str(rnames::RESOLVE), [x, y, pivot.clone()])
                };
                let seteq = |c1: Expr, c2: Expr| {
                    Expr::apps(Expr::const_str(rnames::CLAUSE_SETEQ), [c1, c2])
                };
                let subset = |c1: Expr, c2: Expr| {
                    Expr::apps(Expr::const_str(rnames::CLAUSE_SUBSET), [c1, c2])
                };
                let memx = |x: Expr, c: Expr| clause_mem(x, c);

                let pos_a = memx(pivot.clone(), a_cl.clone());
                let neg_a = memx(np.clone(), a_cl.clone());
                let pos_b = memx(pivot.clone(), b_cl.clone());
                let neg_b = memx(np.clone(), b_cl.clone());
                let mem_and_a =
                    Expr::apps(Expr::const_str("Bool.and"), [pos_a.clone(), neg_b.clone()]);
                let seteq_a = seteq(r.clone(), resolve(a_cl.clone(), b_cl.clone()));
                let branch_a = Expr::apps(
                    Expr::const_str("Bool.and"),
                    [mem_and_a.clone(), seteq_a.clone()],
                );
                let mem_and_b =
                    Expr::apps(Expr::const_str("Bool.and"), [neg_a.clone(), pos_b.clone()]);
                let seteq_b = seteq(r.clone(), resolve(b_cl.clone(), a_cl.clone()));
                let branch_b = Expr::apps(
                    Expr::const_str("Bool.and"),
                    [mem_and_b.clone(), seteq_b.clone()],
                );
                let oriented = Expr::apps(
                    Expr::const_str("Bool.or"),
                    [branch_a.clone(), branch_b.clone()],
                );
                let taut_free = Expr::app(Expr::const_str(rnames::CLAUSE_TAUT_FREE), r.clone());

                let co_r = clause_or(holds.clone(), r.clone());

                // oriented = true (And-left of hcheck), then case both branches.
                let oriented_true = bool_and_elim_left(oriented.clone(), taut_free, hcheck.clone());
                let or_cases = bool_or_elim(branch_a.clone(), branch_b.clone(), oriented_true);

                // helper: derive clauseOr H clause from nthSat + a membership proof.
                //   nthSat H db prem : Or (clauseOr H clause)(clause = nil)
                //   + memNotNil lit clause (mem_true) discharges the nil disjunct.
                let clause_sat = |prem: Expr,
                                  clause: Expr,
                                  lit: Expr,
                                  mem_true: Expr,
                                  parent: &EnvDeclBuilder|
                 -> Expr {
                    let nthsat = Expr::apps(
                        Expr::const_str(names::NTH_SAT),
                        [holds.clone(), db.clone(), hall.clone(), prem],
                    );
                    let co = clause_or(holds.clone(), clause.clone());
                    let eqnil = eq_at(
                        Level::succ(Level::zero()),
                        list_nat(),
                        clause.clone(),
                        list_nil_nat(),
                    );
                    // case_l (h : clauseOr H clause) => h
                    let case_l = {
                        let mut e = EnvDeclBuilder::child_of(parent);
                        let (xid, xc) = e.fresh_local(co.clone());
                        e.finish_child(e.mk_lam(xid, BinderInfo::Default, co.clone(), xc))
                    };
                    // case_r (h : clause = nil) => False.elim (memNotNil lit clause mem_true h)
                    let case_r = {
                        let mut e = EnvDeclBuilder::child_of(parent);
                        let (xid, xnil) = e.fresh_local(eqnil.clone());
                        let ff = Expr::apps(
                            Expr::const_str(names::MEM_NOT_NIL),
                            [lit.clone(), clause.clone(), mem_true.clone(), xnil],
                        );
                        let body = false_elim(Level::zero(), co.clone(), ff);
                        e.finish_child(e.mk_lam(xid, BinderInfo::Default, eqnil.clone(), body))
                    };
                    or_elim(co.clone(), eqnil, co, case_l, case_r, nthsat)
                };

                // branch A proof : (ha : branch_a = true) → clauseOr H r
                let case_branch_a = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let ha_ty = eq_bool(branch_a.clone(), btrue());
                    let (haid, ha) = e.fresh_local(ha_ty.clone());
                    let memcond =
                        bool_and_elim_left(mem_and_a.clone(), seteq_a.clone(), ha.clone());
                    let seteq_true = bool_and_elim_right(mem_and_a.clone(), seteq_a.clone(), ha);
                    let pos_a_true =
                        bool_and_elim_left(pos_a.clone(), neg_b.clone(), memcond.clone());
                    let neg_b_true = bool_and_elim_right(pos_a.clone(), neg_b.clone(), memcond);
                    let co_a = clause_sat(p1.clone(), a_cl.clone(), pivot.clone(), pos_a_true, &e);
                    let co_b = clause_sat(p2.clone(), b_cl.clone(), np.clone(), neg_b_true, &e);
                    // resolveStepSat H A B pivot (hcons pivot)(hexcl pivot) co_a co_b
                    let res_sat = Expr::apps(
                        Expr::const_str(names::RESOLVE_STEP_SAT),
                        [
                            holds.clone(),
                            a_cl.clone(),
                            b_cl.clone(),
                            pivot.clone(),
                            Expr::app(hcons.clone(), pivot.clone()),
                            Expr::app(hexcl.clone(), pivot.clone()),
                            co_a,
                            co_b,
                        ],
                    );
                    // subset (resolve A B p) r from seteq r (resolve A B p) = And-right.
                    let resolved = resolve(a_cl.clone(), b_cl.clone());
                    let sub_res_r = bool_and_elim_right(
                        subset(r.clone(), resolved.clone()),
                        subset(resolved.clone(), r.clone()),
                        seteq_true,
                    );
                    let body = Expr::apps(
                        Expr::const_str(names::SUBSET_SAT),
                        [holds.clone(), resolved, r.clone(), sub_res_r, res_sat],
                    );
                    e.finish_child(e.mk_lam(haid, BinderInfo::Default, ha_ty, body))
                };

                // branch B proof : (hb : branch_b = true) → clauseOr H r
                let case_branch_b = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let hb_ty = eq_bool(branch_b.clone(), btrue());
                    let (hbid, hb) = e.fresh_local(hb_ty.clone());
                    let memcond =
                        bool_and_elim_left(mem_and_b.clone(), seteq_b.clone(), hb.clone());
                    let seteq_true = bool_and_elim_right(mem_and_b.clone(), seteq_b.clone(), hb);
                    let neg_a_true =
                        bool_and_elim_left(neg_a.clone(), pos_b.clone(), memcond.clone());
                    let pos_b_true = bool_and_elim_right(neg_a.clone(), pos_b.clone(), memcond);
                    // orientation B: ¬p∈A, p∈B. clause A non-nil via np, B via pivot.
                    let co_a = clause_sat(p1.clone(), a_cl.clone(), np.clone(), neg_a_true, &e);
                    let co_b = clause_sat(p2.clone(), b_cl.clone(), pivot.clone(), pos_b_true, &e);
                    // resolveStepSat H B A pivot (hcons pivot)(hexcl pivot) co_b co_a
                    let res_sat = Expr::apps(
                        Expr::const_str(names::RESOLVE_STEP_SAT),
                        [
                            holds.clone(),
                            b_cl.clone(),
                            a_cl.clone(),
                            pivot.clone(),
                            Expr::app(hcons.clone(), pivot.clone()),
                            Expr::app(hexcl.clone(), pivot.clone()),
                            co_b,
                            co_a,
                        ],
                    );
                    let resolved = resolve(b_cl.clone(), a_cl.clone());
                    let sub_res_r = bool_and_elim_right(
                        subset(r.clone(), resolved.clone()),
                        subset(resolved.clone(), r.clone()),
                        seteq_true,
                    );
                    let body = Expr::apps(
                        Expr::const_str(names::SUBSET_SAT),
                        [holds.clone(), resolved, r.clone(), sub_res_r, res_sat],
                    );
                    e.finish_child(e.mk_lam(hbid, BinderInfo::Default, hb_ty, body))
                };

                let proof = or_elim(
                    eq_bool(branch_a, btrue()),
                    eq_bool(branch_b, btrue()),
                    co_r,
                    case_branch_a,
                    case_branch_b,
                    or_cases,
                );
                // fun r p1 p2 pivot hcheck => proof
                let rr = d.mk_lam(hcheckid, BinderInfo::Default, hcheck_ty, proof);
                let rr = d.mk_lam(pvid, BinderInfo::Default, nat_ty(), rr);
                let rr = d.mk_lam(p2id, BinderInfo::Default, nat_ty(), rr);
                let rr = d.mk_lam(p1id, BinderInfo::Default, nat_ty(), rr);
                d.finish_child(d.mk_lam(rid, BinderInfo::Default, list_nat(), rr))
            };

            let step_rec =
                Expr::const_(Name::from_string("Clean.Res.Step.rec"), vec![Level::zero()]);
            let folded = Expr::apps(step_rec, [motive, mk_case, s.clone()]);
            let r = b.mk_lam(
                haid,
                BinderInfo::Default,
                all_sat(db.clone(), &holds),
                folded,
            );
            let r = b.mk_lam(heid, BinderInfo::Default, excl_pred(&holds), r);
            let r = b.mk_lam(hcid, BinderInfo::Default, cons_pred(&holds), r);
            let r = b.mk_lam(sid, BinderInfo::Default, step_ty.clone(), r);
            let r = b.mk_lam(dbid, BinderInfo::Default, list_list_nat(), r);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::CHECK_STEP_SAT),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §10 allSatSnoc / listIsNilSat ──────────────────────────────────────────

    /// `allSatSnoc : (H) → (db) → (s : Step) → allSat H db →`
    /// `clauseOr H (stepResolvent s) → allSat H (snocStep db s)`.
    ///
    /// `snocStep db s ≡ db ++ [stepResolvent s]`. `List.rec` on `db`: `nil` ⇒ the
    /// new singleton DB is satisfied by the resolvent hypothesis; `cons` ⇒ peel the
    /// head `And` and recurse.
    fn register_all_sat_snoc(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::ALL_SAT_SNOC))
            .is_some()
        {
            return Ok(());
        }
        let step_ty = Expr::const_str(rnames::STEP);
        let step_resolvent = |s: Expr| Expr::app(Expr::const_str("Clean.Res.stepResolvent"), s);
        let snoc = |db: Expr, s: Expr| Expr::apps(Expr::const_str("Clean.Res.snocStep"), [db, s]);
        let all_sat =
            |db: Expr, h: &Expr| Expr::apps(Expr::const_str(names::ALL_SAT), [h.clone(), db]);

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (dbid, db) = b.fresh_local(list_list_nat());
            let (sid, s) = b.fresh_local(step_ty.clone());
            // Order: clauseOr (resolvent) BEFORE allSat db, so the resolvent witness is
            // in scope inside the List.rec on db.
            let inner = Expr::arrow(
                clause_or(holds.clone(), step_resolvent(s.clone())),
                Expr::arrow(
                    all_sat(db.clone(), &holds),
                    all_sat(snoc(db.clone(), s.clone()), &holds),
                ),
            );
            let e = b.mk_pi(sid, BinderInfo::Default, step_ty.clone(), inner);
            let e = b.mk_pi(dbid, BinderInfo::Default, list_list_nat(), e);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (dbid, db) = b.fresh_local(list_list_nat());
            let (sid, s) = b.fresh_local(step_ty.clone());
            let (hresid, hres) = b.fresh_local(clause_or(holds.clone(), step_resolvent(s.clone())));
            let res = step_resolvent(s.clone());

            // motive : fun db => allSat H db → allSat H (snocStep db s)
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_list_nat());
                let body = Expr::arrow(
                    all_sat(m.clone(), &holds),
                    all_sat(snoc(m.clone(), s.clone()), &holds),
                );
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_list_nat(), body))
            };
            // nil : fun (_ : allSat H nil ≡ True) =>
            //   And.intro (clauseOr H res) True hres True.intro
            let nil_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let nil_db = Expr::app(
                    Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                    list_nat(),
                );
                let as_ty = all_sat(nil_db, &holds);
                let (asid, _as) = d.fresh_local(as_ty.clone());
                let body = and_intro(
                    clause_or(holds.clone(), res.clone()),
                    Expr::const_str("True"),
                    hres.clone(),
                    Expr::const_str("True.intro"),
                );
                d.finish_child(d.mk_lam(asid, BinderInfo::Default, as_ty, body))
            };
            // cons c cs ih (hall : And (clauseOr H c)(allSat H cs)) =>
            //   And.intro (clauseOr H c)(allSat H (snoc cs s)) (left)(ih (right))
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (cid, c) = d.fresh_local(list_nat());
                let (csid, cs) = d.fresh_local(list_list_nat());
                let ih_ty = Expr::arrow(
                    all_sat(cs.clone(), &holds),
                    all_sat(snoc(cs.clone(), s.clone()), &holds),
                );
                let (ihid, ih) = d.fresh_local(ih_ty.clone());
                let db_cons = Expr::apps(
                    Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                    [list_nat(), c.clone(), cs.clone()],
                );
                let hall_ty = all_sat(db_cons, &holds);
                let (hallid, hall) = d.fresh_local(hall_ty.clone());
                let co_c = clause_or(holds.clone(), c.clone());
                let all_cs = all_sat(cs.clone(), &holds);
                let left = and_left(co_c.clone(), all_cs.clone(), hall.clone());
                let right = and_right(co_c.clone(), all_cs.clone(), hall);
                let body = and_intro(
                    co_c,
                    all_sat(snoc(cs.clone(), s.clone()), &holds),
                    left,
                    Expr::app(ih.clone(), right),
                );
                let r = d.mk_lam(hallid, BinderInfo::Default, hall_ty, body);
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                let r = d.mk_lam(csid, BinderInfo::Default, list_list_nat(), r);
                d.finish_child(d.mk_lam(cid, BinderInfo::Default, list_nat(), r))
            };

            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            );
            let folded = Expr::apps(
                list_rec,
                [list_nat(), motive, nil_case, cons_case, db.clone()],
            );
            // applied to hall? No — value is fun H s db hres => List.rec ... db.
            // The recursion yields (allSat H db → allSat H (snoc db s)); caller passes hall.
            let r = b.mk_lam(
                hresid,
                BinderInfo::Default,
                clause_or(holds.clone(), res),
                folded,
            );
            let r = b.mk_lam(sid, BinderInfo::Default, step_ty.clone(), r);
            let r = b.mk_lam(dbid, BinderInfo::Default, list_list_nat(), r);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::ALL_SAT_SNOC),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `listIsNilSat : (H) → (c : List Nat) → Eq (listIsNil c) true →`
    /// `clauseOr H c → False`. An empty clause has no satisfying literal.
    fn register_list_is_nil_sat(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::LIST_IS_NIL_SAT))
            .is_some()
        {
            return Ok(());
        }
        let u1 = Level::succ(Level::zero());
        let list_is_nil = |c: Expr| Expr::app(Expr::const_str("Clean.Res.listIsNil"), c);
        let mk_type = |holds: &Expr, c: &Expr| -> Expr {
            Expr::arrow(
                eq_bool(list_is_nil(c.clone()), btrue()),
                Expr::arrow(clause_or(holds.clone(), c.clone()), false_c()),
            )
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (cid, c) = b.fresh_local(list_nat());
            let body = mk_type(&holds, &c);
            let e = b.mk_pi(cid, BinderInfo::Default, list_nat(), body);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (cid, c) = b.fresh_local(list_nat());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_nat());
                let body = mk_type(&holds, &m);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_nat(), body))
            };
            // nil : fun (_ : listIsNil nil = true)(hco : clauseOr H nil ≡ False) => hco
            let nil_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let hnil_ty = eq_bool(list_is_nil(list_nil_nat()), btrue());
                let (hnid, _hn) = d.fresh_local(hnil_ty.clone());
                let co_nil = clause_or(holds.clone(), list_nil_nat());
                let (hcoid, hco) = d.fresh_local(co_nil.clone());
                // co_nil ≡ False, goal False; hco : False.
                let r = d.mk_lam(hcoid, BinderInfo::Default, co_nil, hco);
                d.finish_child(d.mk_lam(hnid, BinderInfo::Default, hnil_ty, r))
            };
            // cons hd tl _ih : fun (hnil : listIsNil (hd::tl) = true ≡ false = true)(_) => absurd
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (hdid, hd) = d.fresh_local(nat_ty());
                let (tlid, tl) = d.fresh_local(list_nat());
                let ih_ty = mk_type(&holds, &tl);
                let (ihid, _ih) = d.fresh_local(ih_ty.clone());
                let cons_c = list_cons_nat(hd.clone(), tl.clone());
                let hnil_ty = eq_bool(list_is_nil(cons_c.clone()), btrue());
                let (hnid, hn) = d.fresh_local(hnil_ty.clone());
                let co_cons = clause_or(holds.clone(), cons_c.clone());
                let (hcoid, _hco) = d.fresh_local(co_cons.clone());
                // hn : false = true ; absurd.
                let ff = tf_to_false(eq_symm_at(u1.clone(), bool_ty(), bfalse(), btrue(), hn));
                let r = d.mk_lam(hcoid, BinderInfo::Default, co_cons, ff);
                let r = d.mk_lam(hnid, BinderInfo::Default, hnil_ty, r);
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                let r = d.mk_lam(tlid, BinderInfo::Default, list_nat(), r);
                d.finish_child(d.mk_lam(hdid, BinderInfo::Default, nat_ty(), r))
            };
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            );
            let folded = Expr::apps(list_rec, [nat_ty(), motive, nil_case, cons_case, c.clone()]);
            let e = b.mk_lam(cid, BinderInfo::Default, list_nat(), folded);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::LIST_IS_NIL_SAT),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §11 goSound (fold induction) + checkRefutes_sound ──────────────────────

    /// `goSound :`
    /// `(H) → resConsistent H → resExclusive H → (pf : List Step) → (db) →`
    /// `allSat H db → Eq (checkRefutes db pf) true → False`.
    ///
    /// Induction over `pf`. `nil` ⇒ `checkRefutes db nil ≡ false`, so the hypothesis
    /// is `false = true` (absurd). `cons s rest` ⇒ `checkRefutes` splits as `And
    /// (checkStep db s) tail`: `checkStepSat` gives the recorded resolvent is
    /// satisfied, `allSatSnoc` extends the DB invariant; then case on `listStepIsCons
    /// rest` — `nil` reaches the empty-clause endpoint (`listIsNilSat` ⇒ `False`),
    /// `cons` recurses with the grown DB.
    fn register_go_sound(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::GO_SOUND))
            .is_some()
        {
            return Ok(());
        }
        let u1 = Level::succ(Level::zero());
        let step_ty = Expr::const_str(rnames::STEP);
        let list_step = Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            step_ty.clone(),
        );
        let check_refutes =
            |db: Expr, pf: Expr| Expr::apps(Expr::const_str(rnames::CHECK_REFUTES), [db, pf]);
        let all_sat =
            |db: Expr, h: &Expr| Expr::apps(Expr::const_str(names::ALL_SAT), [h.clone(), db]);
        let cons_pred = |h: &Expr| Expr::app(Expr::const_str(names::RES_CONSISTENT), h.clone());
        let excl_pred = |h: &Expr| Expr::app(Expr::const_str(names::RES_EXCLUSIVE), h.clone());
        let step_resolvent = |s: Expr| Expr::app(Expr::const_str("Clean.Res.stepResolvent"), s);
        let step_empty = |s: Expr| Expr::app(Expr::const_str("Clean.Res.stepResolventEmpty"), s);
        let snoc = |db: Expr, s: Expr| Expr::apps(Expr::const_str("Clean.Res.snocStep"), [db, s]);
        let check_step =
            |db: Expr, s: Expr| Expr::apps(Expr::const_str(rnames::CHECK_STEP), [db, s]);
        let is_cons = |l: Expr| Expr::app(Expr::const_str("Clean.Res.listStepIsCons"), l);

        // motive over pf : fun pf => (db) → allSat H db → Eq (checkRefutes db pf) true → False
        let mk_motive_body = |holds: &Expr, pf: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut c = EnvDeclBuilder::child_of(parent);
            let (dbid, db) = c.fresh_local(list_list_nat());
            let inner = Expr::arrow(
                all_sat(db.clone(), holds),
                Expr::arrow(
                    eq_bool(check_refutes(db.clone(), pf.clone()), btrue()),
                    false_c(),
                ),
            );
            c.finish_child(c.mk_pi(dbid, BinderInfo::Default, list_list_nat(), inner))
        };

        // type: (H) → resConsistent H → resExclusive H → (pf) → motive_body
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (cid, _hc) = b.fresh_local(cons_pred(&holds));
            let (eid, _he) = b.fresh_local(excl_pred(&holds));
            let (pfid, pf) = b.fresh_local(list_step.clone());
            let mb = mk_motive_body(&holds, &pf, &b);
            let r = b.mk_pi(pfid, BinderInfo::Default, list_step.clone(), mb);
            let r = b.mk_pi(eid, BinderInfo::Default, excl_pred(&holds), r);
            let r = b.mk_pi(cid, BinderInfo::Default, cons_pred(&holds), r);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), r))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (hcid, hcons) = b.fresh_local(cons_pred(&holds));
            let (heid, hexcl) = b.fresh_local(excl_pred(&holds));
            let (pfid, pf) = b.fresh_local(list_step.clone());

            // motive : fun pf => mk_motive_body pf
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_step.clone());
                let body = mk_motive_body(&holds, &m, &d);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_step.clone(), body))
            };

            // nil : fun (db)(_ : allSat H db)(hck : checkRefutes db nil = true ≡ false = true) =>
            //   tf_to_false (symm hck)
            let nil_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let nil_pf = Expr::app(
                    Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                    step_ty.clone(),
                );
                let (dbid, db) = d.fresh_local(list_list_nat());
                let as_ty = all_sat(db.clone(), &holds);
                let (asid, _as) = d.fresh_local(as_ty.clone());
                let hck_ty = eq_bool(check_refutes(db.clone(), nil_pf.clone()), btrue());
                let (hckid, hck) = d.fresh_local(hck_ty.clone());
                let ff = tf_to_false(eq_symm_at(u1.clone(), bool_ty(), bfalse(), btrue(), hck));
                let r = d.mk_lam(hckid, BinderInfo::Default, hck_ty, ff);
                let r = d.mk_lam(asid, BinderInfo::Default, as_ty, r);
                d.finish_child(d.mk_lam(dbid, BinderInfo::Default, list_list_nat(), r))
            };

            // cons s rest ih : fun (db)(hall)(hck : And (checkStep db s) tail = true) => ...
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (sid, s) = d.fresh_local(step_ty.clone());
                let (restid, rest) = d.fresh_local(list_step.clone());
                let ih_ty = mk_motive_body(&holds, &rest, &d);
                let (ihid, ih) = d.fresh_local(ih_ty.clone());
                let (dbid, db) = d.fresh_local(list_list_nat());
                let hall_ty = all_sat(db.clone(), &holds);
                let (hallid, hall) = d.fresh_local(hall_ty.clone());
                let pf_cons = Expr::apps(
                    Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                    [step_ty.clone(), s.clone(), rest.clone()],
                );
                let hck_ty = eq_bool(check_refutes(db.clone(), pf_cons.clone()), btrue());
                let (hckid, hck) = d.fresh_local(hck_ty.clone());

                // tail := Bool.rec (motive:=fun _=>Bool) (stepEmpty s) (checkRefutes (snoc db s) rest)
                //                   (listStepIsCons rest)
                let tail = {
                    let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), bool_ty());
                    Expr::apps(
                        Expr::const_(Name::from_string("Bool.rec"), vec![u1.clone()]),
                        [
                            inner_motive,
                            step_empty(s.clone()),
                            check_refutes(snoc(db.clone(), s.clone()), rest.clone()),
                            is_cons(rest.clone()),
                        ],
                    )
                };
                let cs_e = check_step(db.clone(), s.clone());
                // checkStep db s = true, tail = true.
                let cs_true = bool_and_elim_left(cs_e.clone(), tail.clone(), hck.clone());
                let tail_true = bool_and_elim_right(cs_e.clone(), tail.clone(), hck);
                // clauseOr H (stepResolvent s)
                let res_sat = Expr::apps(
                    Expr::const_str(names::CHECK_STEP_SAT),
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
                // allSat H (snoc db s)
                let all_snoc = Expr::apps(
                    Expr::const_str(names::ALL_SAT_SNOC),
                    [
                        holds.clone(),
                        db.clone(),
                        s.clone(),
                        res_sat.clone(),
                        hall.clone(),
                    ],
                );

                // case on isCons := listStepIsCons rest, transporting tail_true.
                let isc = is_cons(rest.clone());
                // subst motive over bb : fun bb => Eq (Bool.rec (stepEmpty s)(go)(bb)) true
                let tail_of = |bb: Expr| -> Expr {
                    let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), bool_ty());
                    Expr::apps(
                        Expr::const_(Name::from_string("Bool.rec"), vec![u1.clone()]),
                        [
                            inner_motive,
                            step_empty(s.clone()),
                            check_refutes(snoc(db.clone(), s.clone()), rest.clone()),
                            bb,
                        ],
                    )
                };
                let subst_motive = {
                    let inner = eq_bool(tail_of(Expr::bvar(0)), btrue());
                    Expr::lam(BinderInfo::Default, bool_ty(), inner)
                };
                // case_f (heq : isCons = false): tail ≡ stepEmpty s; transport tail_true.
                let case_f = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let heq_ty = eq_bool(isc.clone(), bfalse());
                    let (heqid, heq) = e.fresh_local(heq_ty.clone());
                    // stepEmpty s = true := Eq.subst subst_motive isc false heq tail_true
                    let se_true = eq_subst1(
                        bool_ty(),
                        subst_motive.clone(),
                        isc.clone(),
                        bfalse(),
                        heq,
                        tail_true.clone(),
                    );
                    // stepEmpty s ≡ listIsNil (stepResolvent s). listIsNilSat H (stepResolvent s) se_true res_sat : False
                    let body = Expr::apps(
                        Expr::const_str(names::LIST_IS_NIL_SAT),
                        [
                            holds.clone(),
                            step_resolvent(s.clone()),
                            se_true,
                            res_sat.clone(),
                        ],
                    );
                    let _ = step_empty(s.clone());
                    e.finish_child(e.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                };
                // case_t (heq : isCons = true): tail ≡ checkRefutes (snoc db s) rest; transport.
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
                    // ih (snoc db s) all_snoc go_true : False
                    let body = Expr::apps(
                        ih.clone(),
                        [snoc(db.clone(), s.clone()), all_snoc.clone(), go_true],
                    );
                    e.finish_child(e.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                };
                let body = bool_cases(isc, false_c(), case_f, case_t);
                let r = d.mk_lam(hckid, BinderInfo::Default, hck_ty, body);
                let r = d.mk_lam(hallid, BinderInfo::Default, hall_ty, r);
                let r = d.mk_lam(dbid, BinderInfo::Default, list_list_nat(), r);
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                let r = d.mk_lam(restid, BinderInfo::Default, list_step.clone(), r);
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
            let r = b.mk_lam(pfid, BinderInfo::Default, list_step.clone(), folded);
            let r = b.mk_lam(heid, BinderInfo::Default, excl_pred(&holds), r);
            let r = b.mk_lam(hcid, BinderInfo::Default, cons_pred(&holds), r);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::GO_SOUND),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `checkRefutes_sound : (cs) → (pf) → Eq (checkRefutes cs pf) true → Unsat cs`.
    ///
    /// The top-level bridge — now a kernel-checked `Theorem` (closure ⊆
    /// FOUNDATIONAL). `Unsat cs ≡ (H) → resConsistent H → resExclusive H → allSat H
    /// cs → False`; feed those to `goSound` with the ORIGINAL clauses as the initial
    /// DB.
    fn register_check_refutes_sound(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::CHECK_REFUTES_SOUND))
            .is_some()
        {
            return Ok(());
        }
        self.register_go_sound()?;
        let step_ty = Expr::const_str(rnames::STEP);
        let list_step = Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            step_ty,
        );
        let check_refutes =
            |db: Expr, pf: Expr| Expr::apps(Expr::const_str(rnames::CHECK_REFUTES), [db, pf]);

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (csid, cs) = b.fresh_local(list_list_nat());
            let (pfid, pf) = b.fresh_local(list_step.clone());
            // `Unsat cs` spelled in its δ-unfolded form (definitionally equal to
            // `Clean.Res.Unsat cs`). The kernel's `add_decl` defeq compares the proof
            // term's *inferred* `Pi`-headed type against the *declared* type; with the
            // declared type written as the `Unsat`-alias `Const`-app the lazy-delta loop
            // does not fire here, so we state the model semantics inline (the very body
            // of `Unsat`). `unsatEqUnfold` below pins this `≡ Unsat cs`.
            let unsat = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hid, holds) = c.fresh_local(holds_ty());
                let cons_pred = Expr::app(Expr::const_str(names::RES_CONSISTENT), holds.clone());
                let excl_pred = Expr::app(Expr::const_str(names::RES_EXCLUSIVE), holds.clone());
                let all_cs =
                    Expr::apps(Expr::const_str(names::ALL_SAT), [holds.clone(), cs.clone()]);
                let body = Expr::arrow(all_cs, false_c());
                let body = Expr::arrow(excl_pred, body);
                let body = Expr::arrow(cons_pred, body);
                c.finish_child(c.mk_pi(hid, BinderInfo::Default, holds_ty(), body))
            };
            let inner = Expr::arrow(
                eq_bool(check_refutes(cs.clone(), pf.clone()), btrue()),
                unsat,
            );
            let e = b.mk_pi(pfid, BinderInfo::Default, list_step.clone(), inner);
            b.finish(b.mk_pi(csid, BinderInfo::Default, list_list_nat(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (csid, cs) = b.fresh_local(list_list_nat());
            let (pfid, pf) = b.fresh_local(list_step.clone());
            let hck_ty = eq_bool(check_refutes(cs.clone(), pf.clone()), btrue());
            let (hckid, hck) = b.fresh_local(hck_ty.clone());
            // Unsat cs ≡ (H) → resConsistent H → resExclusive H → allSat H cs → False
            let (hid, holds) = b.fresh_local(holds_ty());
            let cons_pred = Expr::app(Expr::const_str(names::RES_CONSISTENT), holds.clone());
            let (hcid, hcons) = b.fresh_local(cons_pred.clone());
            let excl_pred = Expr::app(Expr::const_str(names::RES_EXCLUSIVE), holds.clone());
            let (heid, hexcl) = b.fresh_local(excl_pred.clone());
            let all_cs = Expr::apps(Expr::const_str(names::ALL_SAT), [holds.clone(), cs.clone()]);
            let (haid, hall) = b.fresh_local(all_cs.clone());
            // goSound H hcons hexcl pf cs hall hck : False
            // (checkRefutes cs pf threads the ORIGINAL clauses cs as the initial DB.)
            let body = Expr::apps(
                Expr::const_str(names::GO_SOUND),
                [
                    holds.clone(),
                    hcons,
                    hexcl,
                    pf.clone(),
                    cs.clone(),
                    hall,
                    hck.clone(),
                ],
            );
            let r = b.mk_lam(haid, BinderInfo::Default, all_cs, body);
            let r = b.mk_lam(heid, BinderInfo::Default, excl_pred, r);
            let r = b.mk_lam(hcid, BinderInfo::Default, cons_pred, r);
            let r = b.mk_lam(hid, BinderInfo::Default, holds_ty(), r);
            let r = b.mk_lam(hckid, BinderInfo::Default, hck_ty, r);
            let r = b.mk_lam(pfid, BinderInfo::Default, list_step.clone(), r);
            b.finish(b.mk_lam(csid, BinderInfo::Default, list_list_nat(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::CHECK_REFUTES_SOUND),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §12 trie-checker (checkRefutes3) soundness ─────────────────────────────

    /// Register the soundness layer for the sub-quadratic trie checker
    /// `checkRefutes3`, culminating in `checkRefutes3_sound`. Idempotent.
    ///
    /// Mirrors the `checkRefutes_sound` layer with the `List`-db replaced by a
    /// `Trie`: `allSatTrie` (the SAT-or-nil invariant on every node), `trieGetSat`
    /// (every fetched value is SAT-or-nil — the `nthSat` analogue),
    /// `trieInsPreservesAllSat` (path-copy insert keeps the invariant),
    /// `checkStep3Sat` (the step bridge via `trieGet`), and `go3Sound` (the trie-fold
    /// induction). Every declaration is a kernel-checked `Theorem`/`Definition` with
    /// axiom closure ⊆ FOUNDATIONAL.
    fn register_check_refutes3_sound(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::CHECK_REFUTES3_SOUND))
            .is_some()
        {
            return Ok(());
        }
        self.register_all_sat_trie()?;
        self.register_trie_get_sat()?;
        self.register_trie_proj_lemmas()?;
        self.register_trie_ins_preserves_all_sat()?;
        self.register_check_step3_sat()?;
        self.register_go3_sound()?;
        self.register_check_refutes3_sound_thm()
    }

    /// `trieInsPreservesAllSat : (H)(db : Trie)(k : Nat)(c : List Nat) →`
    /// `allSatTrie H db → Or (clauseOr H c)(c = nil) → allSatTrie H (trieIns db k c)`.
    ///
    /// `trieIns db k c ≡ trieInsAux FUEL db k c`; proved via the fuel helper
    /// `trieInsAuxPreservesAllSat` by `Nat.rec` on the fuel (db and k generalised, as
    /// the recursive call descends to a child with `k/2`). At each level the inserted
    /// node's value is SAT-or-nil by hypothesis; the untouched siblings keep their
    /// invariant by `trieValSat`/`trieLoAllSat`/`trieHiAllSat`. The stuck boolean
    /// scrutinees (`Nat.ble k 0`, `Nat.ble 1 (k%2)`) are discharged by transporting
    /// the branch proofs along the case equations (`Eq.subst`).
    fn register_trie_ins_preserves_all_sat(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::TRIE_INS_PRESERVES_ALL_SAT))
            .is_some()
        {
            return Ok(());
        }
        let u1 = Level::succ(Level::zero());
        let trie_val = |t: Expr| Expr::app(Expr::const_str("Clean.Res.trieVal"), t);
        let trie_lo = |t: Expr| Expr::app(Expr::const_str("Clean.Res.trieLo"), t);
        let trie_hi = |t: Expr| Expr::app(Expr::const_str("Clean.Res.trieHi"), t);
        let ins_aux = |fuel: Expr, db: Expr, k: Expr, c: Expr| {
            Expr::apps(Expr::const_str("Clean.Res.trieInsAux"), [fuel, db, k, c])
        };
        let val_sat = |db: Expr, hall: Expr, holds: &Expr| {
            Expr::apps(Expr::const_str(TRIE_VAL_SAT), [holds.clone(), db, hall])
        };
        let lo_all = |db: Expr, hall: Expr, holds: &Expr| {
            Expr::apps(Expr::const_str(TRIE_LO_ALL_SAT), [holds.clone(), db, hall])
        };
        let hi_all = |db: Expr, hall: Expr, holds: &Expr| {
            Expr::apps(Expr::const_str(TRIE_HI_ALL_SAT), [holds.clone(), db, hall])
        };
        // setHere db c ≡ node c (trieLo db)(trieHi db).
        let set_here =
            |db: &Expr, c: &Expr| trie_node(c.clone(), trie_lo(db.clone()), trie_hi(db.clone()));
        // node Trie.rec motive (Sort 1) for descend/full (returns Trie).
        let bool_rec_trie = |fcase: Expr, tcase: Expr, scrut: Expr| {
            let m = Expr::lam(BinderInfo::Default, bool_ty(), trie_ty());
            Expr::apps(
                Expr::const_(Name::from_string("Bool.rec"), vec![u1.clone()]),
                [m, fcase, tcase, scrut],
            )
        };

        // ── fuel helper: trieInsAuxPreservesAllSat ──
        if self
            .get_const(&Name::from_string(TRIE_INS_AUX_PRESERVES))
            .is_none()
        {
            // P fuel := (db)(k) → allSatTrie H db → satOrNil H c → allSatTrie H (insAux fuel db k c)
            let mk_p = |holds: &Expr, c: &Expr, fuel: &Expr, parent: &EnvDeclBuilder| -> Expr {
                let mut g = EnvDeclBuilder::child_of(parent);
                let (dbid, db) = g.fresh_local(trie_ty());
                let (kid, k) = g.fresh_local(nat_ty());
                let concl = Expr::arrow(
                    all_sat_trie(holds.clone(), db.clone()),
                    Expr::arrow(
                        sat_or_nil(holds, c),
                        all_sat_trie(
                            holds.clone(),
                            ins_aux(fuel.clone(), db.clone(), k.clone(), c.clone()),
                        ),
                    ),
                );
                let inner = g.mk_pi(kid, BinderInfo::Default, nat_ty(), concl);
                g.finish_child(g.mk_pi(dbid, BinderInfo::Default, trie_ty(), inner))
            };

            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty());
                let (cid, c) = b.fresh_local(list_nat());
                let (fid, fuel) = b.fresh_local(nat_ty());
                let body = mk_p(&holds, &c, &fuel, &b);
                let e = b.mk_pi(fid, BinderInfo::Default, nat_ty(), body);
                let e = b.mk_pi(cid, BinderInfo::Default, list_nat(), e);
                b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
            };

            // proof of allSatTrie H (setHere db c) from (hall : allSatTrie H db)(hc : satOrNil c):
            //   And.intro hc (And.intro (loAll db hall)(hiAll db hall))
            let here_proof = |holds: &Expr, db: &Expr, c: &Expr, hall: &Expr, hc: &Expr| -> Expr {
                let head = sat_or_nil(holds, c);
                let lo_as = all_sat_trie(holds.clone(), trie_lo(db.clone()));
                let hi_as = all_sat_trie(holds.clone(), trie_hi(db.clone()));
                let children = and_intro(
                    lo_as.clone(),
                    hi_as.clone(),
                    lo_all(db.clone(), hall.clone(), holds),
                    hi_all(db.clone(), hall.clone(), holds),
                );
                let children_ty = Expr::apps(
                    Expr::const_(Name::from_string("And"), vec![]),
                    [lo_as, hi_as],
                );
                and_intro(head, children_ty, hc.clone(), children)
            };

            let value = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty());
                let (cid, c) = b.fresh_local(list_nat());

                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (mid, m) = d.fresh_local(nat_ty());
                    let body = mk_p(&holds, &c, &m, &d);
                    d.finish_child(d.mk_lam(mid, BinderInfo::Default, nat_ty(), body))
                };

                // base (fuel = 0): fun (db)(k)(hall)(hc) => here_proof
                //   (insAux 0 db k c ≡ setHere db c)
                let base_case = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (dbid, db) = d.fresh_local(trie_ty());
                    let (kid, _k) = d.fresh_local(nat_ty());
                    let hall_ty = all_sat_trie(holds.clone(), db.clone());
                    let (hallid, hall) = d.fresh_local(hall_ty.clone());
                    let hc_ty = sat_or_nil(&holds, &c);
                    let (hcid, hc) = d.fresh_local(hc_ty.clone());
                    let body = here_proof(&holds, &db, &c, &hall, &hc);
                    let r = d.mk_lam(hcid, BinderInfo::Default, hc_ty, body);
                    let r = d.mk_lam(hallid, BinderInfo::Default, hall_ty, r);
                    let r = d.mk_lam(kid, BinderInfo::Default, nat_ty(), r);
                    d.finish_child(d.mk_lam(dbid, BinderInfo::Default, trie_ty(), r))
                };

                // step (fuel = succ f, ih : P f): fun (db)(k)(hall)(hc) => <transport>
                let step_case = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (fid, f) = d.fresh_local(nat_ty());
                    let ih_ty = mk_p(&holds, &c, &f, &d);
                    let (ihid, ih) = d.fresh_local(ih_ty.clone());
                    let (dbid, db) = d.fresh_local(trie_ty());
                    let (kid, k) = d.fresh_local(nat_ty());
                    let hall_ty = all_sat_trie(holds.clone(), db.clone());
                    let (hallid, hall) = d.fresh_local(hall_ty.clone());
                    let hc_ty = sat_or_nil(&holds, &c);
                    let (hcid, hc) = d.fresh_local(hc_ty.clone());

                    let half = nat_div(k.clone(), nat_lit(2));
                    let is_zero = nat_ble(k.clone(), nat_lit(0));
                    let is_odd = nat_ble(nat_lit(1), nat_mod(k.clone(), nat_lit(2)));

                    let ins_here = set_here(&db, &c);
                    let ins_even = trie_node(
                        trie_val(db.clone()),
                        ins_aux(f.clone(), trie_lo(db.clone()), half.clone(), c.clone()),
                        trie_hi(db.clone()),
                    );
                    let ins_odd = trie_node(
                        trie_val(db.clone()),
                        trie_lo(db.clone()),
                        ins_aux(f.clone(), trie_hi(db.clone()), half.clone(), c.clone()),
                    );
                    let descend = |bp: Expr| bool_rec_trie(ins_even.clone(), ins_odd.clone(), bp);
                    let descend_p = descend(is_odd.clone());
                    let full = |b0: Expr| bool_rec_trie(descend_p.clone(), ins_here.clone(), b0);

                    // M_full b0 := allSatTrie H (full b0)
                    let m_full = {
                        let body = all_sat_trie(holds.clone(), full(Expr::bvar(0)));
                        Expr::lam(BinderInfo::Default, bool_ty(), body)
                    };
                    // M_desc bp := allSatTrie H (descend bp)
                    let m_desc = {
                        let body = all_sat_trie(holds.clone(), descend(Expr::bvar(0)));
                        Expr::lam(BinderInfo::Default, bool_ty(), body)
                    };

                    let goal = all_sat_trie(
                        holds.clone(),
                        ins_aux(nat_succ(f.clone()), db.clone(), k.clone(), c.clone()),
                    );

                    // case k = 0 (h0 : is_zero = true): here_proof : allSatTrie (setHere db c) ≡ M_full true.
                    let case_zero = {
                        let mut g = EnvDeclBuilder::child_of(&d);
                        let h0_ty = eq_bool(is_zero.clone(), btrue());
                        let (h0id, h0) = g.fresh_local(h0_ty.clone());
                        let hp = here_proof(&holds, &db, &c, &hall, &hc);
                        let body = eq_subst1(
                            bool_ty(),
                            m_full.clone(),
                            btrue(),
                            is_zero.clone(),
                            eq_symm_at(u1.clone(), bool_ty(), is_zero.clone(), btrue(), h0),
                            hp,
                        );
                        g.finish_child(g.mk_lam(h0id, BinderInfo::Default, h0_ty, body))
                    };
                    // case k ≠ 0 (h0 : is_zero = false): case on parity.
                    let case_nonzero = {
                        let mut g = EnvDeclBuilder::child_of(&d);
                        let h0_ty = eq_bool(is_zero.clone(), bfalse());
                        let (h0id, h0) = g.fresh_local(h0_ty.clone());
                        // lift: M_full false → M_full is_zero ≡ goal.
                        let lift_to_goal = |p: Expr| -> Expr {
                            eq_subst1(
                                bool_ty(),
                                m_full.clone(),
                                bfalse(),
                                is_zero.clone(),
                                eq_symm_at(
                                    u1.clone(),
                                    bool_ty(),
                                    is_zero.clone(),
                                    bfalse(),
                                    h0.clone(),
                                ),
                                p,
                            )
                        };
                        // proof of allSatTrie (node (trieVal db) child (trieHi db / trieLo db)) given
                        //   `inserted` : allSatTrie H (the freshly-inserted child subtree).
                        // odd: ins_odd = node (trieVal db)(trieLo db)(insAux f (trieHi db) (k/2) c)
                        let case_odd = {
                            let mut h = EnvDeclBuilder::child_of(&g);
                            let hp_ty = eq_bool(is_odd.clone(), btrue());
                            let (hpid, hodd) = h.fresh_local(hp_ty.clone());
                            // inserted := ih (trieHi db) (k/2) (hiAll db hall) hc : allSatTrie (insAux f (trieHi db)(k/2) c)
                            let inserted = Expr::apps(
                                ih.clone(),
                                [
                                    trie_hi(db.clone()),
                                    half.clone(),
                                    hi_all(db.clone(), hall.clone(), &holds),
                                    hc.clone(),
                                ],
                            );
                            // allSatTrie ins_odd ≡ And (satOrNil (trieVal db)) (And (allSatTrie (trieLo db))(allSatTrie inserted-subtree))
                            let head = sat_or_nil(&holds, &trie_val(db.clone()));
                            let lo_as = all_sat_trie(holds.clone(), trie_lo(db.clone()));
                            let child_as = all_sat_trie(
                                holds.clone(),
                                ins_aux(f.clone(), trie_hi(db.clone()), half.clone(), c.clone()),
                            );
                            let children = and_intro(
                                lo_as.clone(),
                                child_as.clone(),
                                lo_all(db.clone(), hall.clone(), &holds),
                                inserted,
                            );
                            let children_ty = Expr::apps(
                                Expr::const_(Name::from_string("And"), vec![]),
                                [lo_as, child_as],
                            );
                            let p_odd = and_intro(
                                head,
                                children_ty,
                                val_sat(db.clone(), hall.clone(), &holds),
                                children,
                            );
                            // p_odd : allSatTrie ins_odd ≡ M_desc true. subst to M_desc is_odd.
                            let p_desc = eq_subst1(
                                bool_ty(),
                                m_desc.clone(),
                                btrue(),
                                is_odd.clone(),
                                eq_symm_at(u1.clone(), bool_ty(), is_odd.clone(), btrue(), hodd),
                                p_odd,
                            );
                            let body = lift_to_goal(p_desc);
                            h.finish_child(h.mk_lam(hpid, BinderInfo::Default, hp_ty, body))
                        };
                        // even: ins_even = node (trieVal db)(insAux f (trieLo db)(k/2) c)(trieHi db)
                        let case_even = {
                            let mut h = EnvDeclBuilder::child_of(&g);
                            let hp_ty = eq_bool(is_odd.clone(), bfalse());
                            let (hpid, hev) = h.fresh_local(hp_ty.clone());
                            let inserted = Expr::apps(
                                ih.clone(),
                                [
                                    trie_lo(db.clone()),
                                    half.clone(),
                                    lo_all(db.clone(), hall.clone(), &holds),
                                    hc.clone(),
                                ],
                            );
                            let head = sat_or_nil(&holds, &trie_val(db.clone()));
                            let child_as = all_sat_trie(
                                holds.clone(),
                                ins_aux(f.clone(), trie_lo(db.clone()), half.clone(), c.clone()),
                            );
                            let hi_as = all_sat_trie(holds.clone(), trie_hi(db.clone()));
                            let children = and_intro(
                                child_as.clone(),
                                hi_as.clone(),
                                inserted,
                                hi_all(db.clone(), hall.clone(), &holds),
                            );
                            let children_ty = Expr::apps(
                                Expr::const_(Name::from_string("And"), vec![]),
                                [child_as, hi_as],
                            );
                            let p_even = and_intro(
                                head,
                                children_ty,
                                val_sat(db.clone(), hall.clone(), &holds),
                                children,
                            );
                            let p_desc = eq_subst1(
                                bool_ty(),
                                m_desc.clone(),
                                bfalse(),
                                is_odd.clone(),
                                eq_symm_at(u1.clone(), bool_ty(), is_odd.clone(), bfalse(), hev),
                                p_even,
                            );
                            let body = lift_to_goal(p_desc);
                            h.finish_child(h.mk_lam(hpid, BinderInfo::Default, hp_ty, body))
                        };
                        let goal_parity = all_sat_trie(
                            holds.clone(),
                            ins_aux(nat_succ(f.clone()), db.clone(), k.clone(), c.clone()),
                        );
                        let body = bool_cases(is_odd.clone(), goal_parity, case_even, case_odd);
                        g.finish_child(g.mk_lam(h0id, BinderInfo::Default, h0_ty, body))
                    };
                    let body = bool_cases(is_zero, goal, case_nonzero, case_zero);
                    let r = d.mk_lam(hcid, BinderInfo::Default, hc_ty, body);
                    let r = d.mk_lam(hallid, BinderInfo::Default, hall_ty, r);
                    let r = d.mk_lam(kid, BinderInfo::Default, nat_ty(), r);
                    let r = d.mk_lam(dbid, BinderInfo::Default, trie_ty(), r);
                    let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                    d.finish_child(d.mk_lam(fid, BinderInfo::Default, nat_ty(), r))
                };

                let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
                // value : fun H c => Nat.rec (motive := P) base step   (a function of fuel)
                let folded = Expr::apps(nat_rec, [motive, base_case, step_case]);
                let e = b.mk_lam(cid, BinderInfo::Default, list_nat(), folded);
                b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(TRIE_INS_AUX_PRESERVES),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── trieInsPreservesAllSat := the fuel helper specialised at FUEL ──
        // trieIns db k c ≡ trieInsAux FUEL db k c, so apply the helper at fuel = FUEL.
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (dbid, db) = b.fresh_local(trie_ty());
            let (kid, k) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(list_nat());
            let trie_ins = Expr::apps(
                Expr::const_str(rnames::TRIE_INS),
                [db.clone(), k.clone(), c.clone()],
            );
            let concl = Expr::arrow(
                all_sat_trie(holds.clone(), db.clone()),
                Expr::arrow(
                    sat_or_nil(&holds, &c),
                    all_sat_trie(holds.clone(), trie_ins),
                ),
            );
            let e = b.mk_pi(cid, BinderInfo::Default, list_nat(), concl);
            let e = b.mk_pi(kid, BinderInfo::Default, nat_ty(), e);
            let e = b.mk_pi(dbid, BinderInfo::Default, trie_ty(), e);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (dbid, db) = b.fresh_local(trie_ty());
            let (kid, k) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(list_nat());
            // trieInsAuxPreservesAllSat H c FUEL db k : allSatTrie db → satOrNil c →
            //   allSatTrie (insAux FUEL db k c) ≡ allSatTrie (trieIns db k c).
            let body = Expr::apps(
                Expr::const_str(TRIE_INS_AUX_PRESERVES),
                [
                    holds.clone(),
                    c.clone(),
                    nat_lit(TRIE_FUEL),
                    db.clone(),
                    k.clone(),
                ],
            );
            let r = b.mk_lam(cid, BinderInfo::Default, list_nat(), body);
            let r = b.mk_lam(kid, BinderInfo::Default, nat_ty(), r);
            let r = b.mk_lam(dbid, BinderInfo::Default, trie_ty(), r);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::TRIE_INS_PRESERVES_ALL_SAT),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `checkStep3Sat :`
    /// `(H) → (db : Trie) → (s : Step) → resConsistent H → resExclusive H →`
    /// `allSatTrie H db → Eq (checkStep3 db s) true → clauseOr H (stepResolvent s)`.
    ///
    /// Identical in shape to `checkStepSat`, with `nth db premK` replaced by `trieGet
    /// db premK` and `allSat`/`nthSat` replaced by `allSatTrie`/`trieGetSat`. The two
    /// premises are non-nil (`memNotNil` discharges the `trieGet = nil` disjunct of
    /// `trieGetSat` once a pivot is a known member), `resolveStepSat` discharges the
    /// resolution step, and `subsetSat` transports along the recorded `clauseSeteq`.
    fn register_check_step3_sat(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::CHECK_STEP3_SAT))
            .is_some()
        {
            return Ok(());
        }
        let step_ty = Expr::const_str(rnames::STEP);
        let check_step3 =
            |db: Expr, s: Expr| Expr::apps(Expr::const_str(rnames::CHECK_STEP3), [db, s]);
        let step_resolvent = |s: Expr| Expr::app(Expr::const_str("Clean.Res.stepResolvent"), s);
        let cons_pred = |h: &Expr| Expr::app(Expr::const_str(names::RES_CONSISTENT), h.clone());
        let excl_pred = |h: &Expr| Expr::app(Expr::const_str(names::RES_EXCLUSIVE), h.clone());

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (dbid, db) = b.fresh_local(trie_ty());
            let (sid, s) = b.fresh_local(step_ty.clone());
            let concl = clause_or(holds.clone(), step_resolvent(s.clone()));
            let inner = Expr::arrow(eq_bool(check_step3(db.clone(), s.clone()), btrue()), concl);
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
                    eq_bool(check_step3(db.clone(), m.clone()), btrue()),
                    clause_or(holds.clone(), step_resolvent(m.clone())),
                );
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, step_ty.clone(), body))
            };

            let mk_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (rid, r) = d.fresh_local(list_nat());
                let (p1id, p1) = d.fresh_local(nat_ty());
                let (p2id, p2) = d.fresh_local(nat_ty());
                let (pvid, pivot) = d.fresh_local(nat_ty());
                let step_e = Expr::apps(
                    Expr::const_str(rnames::STEP_MK),
                    [r.clone(), p1.clone(), p2.clone(), pivot.clone()],
                );
                let hcheck_ty = eq_bool(check_step3(db.clone(), step_e), btrue());
                let (hcheckid, hcheck) = d.fresh_local(hcheck_ty.clone());

                let a_cl = trie_get(db.clone(), p1.clone());
                let b_cl = trie_get(db.clone(), p2.clone());
                let np = lit_neg(pivot.clone());
                let resolve = |x: Expr, y: Expr| {
                    Expr::apps(Expr::const_str(rnames::RESOLVE), [x, y, pivot.clone()])
                };
                let seteq = |c1: Expr, c2: Expr| {
                    Expr::apps(Expr::const_str(rnames::CLAUSE_SETEQ), [c1, c2])
                };
                let subset = |c1: Expr, c2: Expr| {
                    Expr::apps(Expr::const_str(rnames::CLAUSE_SUBSET), [c1, c2])
                };

                let pos_a = clause_mem(pivot.clone(), a_cl.clone());
                let neg_a = clause_mem(np.clone(), a_cl.clone());
                let pos_b = clause_mem(pivot.clone(), b_cl.clone());
                let neg_b = clause_mem(np.clone(), b_cl.clone());
                let mem_and_a =
                    Expr::apps(Expr::const_str("Bool.and"), [pos_a.clone(), neg_b.clone()]);
                let seteq_a = seteq(r.clone(), resolve(a_cl.clone(), b_cl.clone()));
                let branch_a = Expr::apps(
                    Expr::const_str("Bool.and"),
                    [mem_and_a.clone(), seteq_a.clone()],
                );
                let mem_and_b =
                    Expr::apps(Expr::const_str("Bool.and"), [neg_a.clone(), pos_b.clone()]);
                let seteq_b = seteq(r.clone(), resolve(b_cl.clone(), a_cl.clone()));
                let branch_b = Expr::apps(
                    Expr::const_str("Bool.and"),
                    [mem_and_b.clone(), seteq_b.clone()],
                );
                let oriented = Expr::apps(
                    Expr::const_str("Bool.or"),
                    [branch_a.clone(), branch_b.clone()],
                );
                let taut_free = Expr::app(Expr::const_str(rnames::CLAUSE_TAUT_FREE), r.clone());
                let co_r = clause_or(holds.clone(), r.clone());

                let oriented_true = bool_and_elim_left(oriented.clone(), taut_free, hcheck.clone());
                let or_cases = bool_or_elim(branch_a.clone(), branch_b.clone(), oriented_true);

                // clauseOr H clause from trieGetSat + a membership proof (memNotNil kills nil).
                let clause_sat = |prem: Expr,
                                  clause: Expr,
                                  lit: Expr,
                                  mem_true: Expr,
                                  parent: &EnvDeclBuilder|
                 -> Expr {
                    let getsat = Expr::apps(
                        Expr::const_str(names::TRIE_GET_SAT),
                        [holds.clone(), db.clone(), hall.clone(), prem],
                    );
                    let co = clause_or(holds.clone(), clause.clone());
                    let eqnil = eq_at(
                        Level::succ(Level::zero()),
                        list_nat(),
                        clause.clone(),
                        list_nil_nat(),
                    );
                    let case_l = {
                        let mut e = EnvDeclBuilder::child_of(parent);
                        let (xid, xc) = e.fresh_local(co.clone());
                        e.finish_child(e.mk_lam(xid, BinderInfo::Default, co.clone(), xc))
                    };
                    let case_r = {
                        let mut e = EnvDeclBuilder::child_of(parent);
                        let (xid, xnil) = e.fresh_local(eqnil.clone());
                        let ff = Expr::apps(
                            Expr::const_str(names::MEM_NOT_NIL),
                            [lit.clone(), clause.clone(), mem_true.clone(), xnil],
                        );
                        let body = false_elim(Level::zero(), co.clone(), ff);
                        e.finish_child(e.mk_lam(xid, BinderInfo::Default, eqnil.clone(), body))
                    };
                    or_elim(co.clone(), eqnil, co, case_l, case_r, getsat)
                };

                // branch A : (ha : branch_a = true) → clauseOr H r
                let case_branch_a = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let ha_ty = eq_bool(branch_a.clone(), btrue());
                    let (haid, ha) = e.fresh_local(ha_ty.clone());
                    let memcond =
                        bool_and_elim_left(mem_and_a.clone(), seteq_a.clone(), ha.clone());
                    let seteq_true = bool_and_elim_right(mem_and_a.clone(), seteq_a.clone(), ha);
                    let pos_a_true =
                        bool_and_elim_left(pos_a.clone(), neg_b.clone(), memcond.clone());
                    let neg_b_true = bool_and_elim_right(pos_a.clone(), neg_b.clone(), memcond);
                    let co_a = clause_sat(p1.clone(), a_cl.clone(), pivot.clone(), pos_a_true, &e);
                    let co_b = clause_sat(p2.clone(), b_cl.clone(), np.clone(), neg_b_true, &e);
                    let res_sat = Expr::apps(
                        Expr::const_str(names::RESOLVE_STEP_SAT),
                        [
                            holds.clone(),
                            a_cl.clone(),
                            b_cl.clone(),
                            pivot.clone(),
                            Expr::app(hcons.clone(), pivot.clone()),
                            Expr::app(hexcl.clone(), pivot.clone()),
                            co_a,
                            co_b,
                        ],
                    );
                    let resolved = resolve(a_cl.clone(), b_cl.clone());
                    let sub_res_r = bool_and_elim_right(
                        subset(r.clone(), resolved.clone()),
                        subset(resolved.clone(), r.clone()),
                        seteq_true,
                    );
                    let body = Expr::apps(
                        Expr::const_str(names::SUBSET_SAT),
                        [holds.clone(), resolved, r.clone(), sub_res_r, res_sat],
                    );
                    e.finish_child(e.mk_lam(haid, BinderInfo::Default, ha_ty, body))
                };

                // branch B : (hb : branch_b = true) → clauseOr H r
                let case_branch_b = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let hb_ty = eq_bool(branch_b.clone(), btrue());
                    let (hbid, hb) = e.fresh_local(hb_ty.clone());
                    let memcond =
                        bool_and_elim_left(mem_and_b.clone(), seteq_b.clone(), hb.clone());
                    let seteq_true = bool_and_elim_right(mem_and_b.clone(), seteq_b.clone(), hb);
                    let neg_a_true =
                        bool_and_elim_left(neg_a.clone(), pos_b.clone(), memcond.clone());
                    let pos_b_true = bool_and_elim_right(neg_a.clone(), pos_b.clone(), memcond);
                    let co_a = clause_sat(p1.clone(), a_cl.clone(), np.clone(), neg_a_true, &e);
                    let co_b = clause_sat(p2.clone(), b_cl.clone(), pivot.clone(), pos_b_true, &e);
                    let res_sat = Expr::apps(
                        Expr::const_str(names::RESOLVE_STEP_SAT),
                        [
                            holds.clone(),
                            b_cl.clone(),
                            a_cl.clone(),
                            pivot.clone(),
                            Expr::app(hcons.clone(), pivot.clone()),
                            Expr::app(hexcl.clone(), pivot.clone()),
                            co_b,
                            co_a,
                        ],
                    );
                    let resolved = resolve(b_cl.clone(), a_cl.clone());
                    let sub_res_r = bool_and_elim_right(
                        subset(r.clone(), resolved.clone()),
                        subset(resolved.clone(), r.clone()),
                        seteq_true,
                    );
                    let body = Expr::apps(
                        Expr::const_str(names::SUBSET_SAT),
                        [holds.clone(), resolved, r.clone(), sub_res_r, res_sat],
                    );
                    e.finish_child(e.mk_lam(hbid, BinderInfo::Default, hb_ty, body))
                };

                let proof = or_elim(
                    eq_bool(branch_a, btrue()),
                    eq_bool(branch_b, btrue()),
                    co_r,
                    case_branch_a,
                    case_branch_b,
                    or_cases,
                );
                let rr = d.mk_lam(hcheckid, BinderInfo::Default, hcheck_ty, proof);
                let rr = d.mk_lam(pvid, BinderInfo::Default, nat_ty(), rr);
                let rr = d.mk_lam(p2id, BinderInfo::Default, nat_ty(), rr);
                let rr = d.mk_lam(p1id, BinderInfo::Default, nat_ty(), rr);
                d.finish_child(d.mk_lam(rid, BinderInfo::Default, list_nat(), rr))
            };

            let step_rec =
                Expr::const_(Name::from_string("Clean.Res.Step.rec"), vec![Level::zero()]);
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
            name: Name::from_string(names::CHECK_STEP3_SAT),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `go3Sound :`
    /// `(H) → resConsistent H → resExclusive H → (pf : List Step) → (db : Trie) →`
    /// `(nextId : Nat) → allSatTrie H db → Eq (checkRefutes3 db nextId pf) true → False`.
    ///
    /// Mirror of `goSound` with the `List`-db threaded as a `Trie`: `nil` ⇒
    /// `checkRefutes3 db nextId nil ≡ false` (absurd); `cons s rest` ⇒ `checkStep3Sat`
    /// proves the recorded resolvent is satisfied, `trieInsPreservesAllSat` extends the
    /// `allSatTrie` invariant under the `trieIns` of the resolvent at `nextId`, and the
    /// `listStepIsCons rest` case-split reaches the empty-clause endpoint
    /// (`listIsNilSat`) or recurses with the grown trie + bumped `nextId`.
    fn register_go3_sound(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::GO3_SOUND))
            .is_some()
        {
            return Ok(());
        }
        let u1 = Level::succ(Level::zero());
        let step_ty = Expr::const_str(rnames::STEP);
        let list_step = Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            step_ty.clone(),
        );
        // checkRefutes3 db nextId pf
        let check_refutes3 = |db: Expr, nid: Expr, pf: Expr| {
            Expr::apps(Expr::const_str(rnames::CHECK_REFUTES3), [db, nid, pf])
        };
        let cons_pred = |h: &Expr| Expr::app(Expr::const_str(names::RES_CONSISTENT), h.clone());
        let excl_pred = |h: &Expr| Expr::app(Expr::const_str(names::RES_EXCLUSIVE), h.clone());
        let step_resolvent = |s: Expr| Expr::app(Expr::const_str("Clean.Res.stepResolvent"), s);
        let step_empty = |s: Expr| Expr::app(Expr::const_str("Clean.Res.stepResolventEmpty"), s);
        let check_step3 =
            |db: Expr, s: Expr| Expr::apps(Expr::const_str(rnames::CHECK_STEP3), [db, s]);
        let is_cons = |l: Expr| Expr::app(Expr::const_str("Clean.Res.listStepIsCons"), l);
        let trie_ins =
            |db: Expr, k: Expr, c: Expr| Expr::apps(Expr::const_str(rnames::TRIE_INS), [db, k, c]);

        // motive over pf : fun pf => (db : Trie)(nextId : Nat) → allSatTrie H db →
        //   Eq (checkRefutes3 db nextId pf) true → False
        let mk_motive_body = |holds: &Expr, pf: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut c = EnvDeclBuilder::child_of(parent);
            let (dbid, db) = c.fresh_local(trie_ty());
            let (nid, nextid) = c.fresh_local(nat_ty());
            let inner = Expr::arrow(
                all_sat_trie(holds.clone(), db.clone()),
                Expr::arrow(
                    eq_bool(
                        check_refutes3(db.clone(), nextid.clone(), pf.clone()),
                        btrue(),
                    ),
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
            let (pfid, pf) = b.fresh_local(list_step.clone());
            let mb = mk_motive_body(&holds, &pf, &b);
            let r = b.mk_pi(pfid, BinderInfo::Default, list_step.clone(), mb);
            let r = b.mk_pi(eid, BinderInfo::Default, excl_pred(&holds), r);
            let r = b.mk_pi(cid, BinderInfo::Default, cons_pred(&holds), r);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), r))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (hcid, hcons) = b.fresh_local(cons_pred(&holds));
            let (heid, hexcl) = b.fresh_local(excl_pred(&holds));
            let (pfid, pf) = b.fresh_local(list_step.clone());

            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(list_step.clone());
                let body = mk_motive_body(&holds, &m, &d);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_step.clone(), body))
            };

            // nil : fun (db)(nextId)(_ : allSatTrie H db)(hck : checkRefutes3 db nextId nil = true) =>
            //   tf_to_false (symm hck)   (checkRefutes3 db nextId nil ≡ false)
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
                    check_refutes3(db.clone(), nextid.clone(), nil_pf.clone()),
                    btrue(),
                );
                let (hckid, hck) = d.fresh_local(hck_ty.clone());
                let ff = tf_to_false(eq_symm_at(u1.clone(), bool_ty(), bfalse(), btrue(), hck));
                let r = d.mk_lam(hckid, BinderInfo::Default, hck_ty, ff);
                let r = d.mk_lam(asid, BinderInfo::Default, as_ty, r);
                let r = d.mk_lam(nid, BinderInfo::Default, nat_ty(), r);
                d.finish_child(d.mk_lam(dbid, BinderInfo::Default, trie_ty(), r))
            };

            // cons s rest ih : fun (db)(nextId)(hall)(hck : And (checkStep3 db s) tail = true) => ...
            let cons_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (sid, s) = d.fresh_local(step_ty.clone());
                let (restid, rest) = d.fresh_local(list_step.clone());
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
                    check_refutes3(db.clone(), nextid.clone(), pf_cons.clone()),
                    btrue(),
                );
                let (hckid, hck) = d.fresh_local(hck_ty.clone());

                // new_db := trieIns db nextId (stepResolvent s) ; new_next := succ nextId.
                let new_db = trie_ins(db.clone(), nextid.clone(), step_resolvent(s.clone()));
                let new_next = nat_succ(nextid.clone());
                // tail := Bool.rec (stepEmpty s) (checkRefutes3 new_db new_next rest) (isCons rest)
                let tail_of = |bb: Expr| -> Expr {
                    let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), bool_ty());
                    Expr::apps(
                        Expr::const_(Name::from_string("Bool.rec"), vec![u1.clone()]),
                        [
                            inner_motive,
                            step_empty(s.clone()),
                            check_refutes3(new_db.clone(), new_next.clone(), rest.clone()),
                            bb,
                        ],
                    )
                };
                let tail = tail_of(is_cons(rest.clone()));
                let cs_e = check_step3(db.clone(), s.clone());
                let cs_true = bool_and_elim_left(cs_e.clone(), tail.clone(), hck.clone());
                let tail_true = bool_and_elim_right(cs_e.clone(), tail.clone(), hck);
                // clauseOr H (stepResolvent s)
                let res_sat = Expr::apps(
                    Expr::const_str(names::CHECK_STEP3_SAT),
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
                // allSatTrie H new_db := trieInsPreservesAllSat H db nextId (stepResolvent s) hall (Or.inl res_sat)
                let res = step_resolvent(s.clone());
                let sat_or_nil_res = or_inl(
                    clause_or(holds.clone(), res.clone()),
                    eq_at(u1.clone(), list_nat(), res.clone(), list_nil_nat()),
                    res_sat.clone(),
                );
                let all_ins = Expr::apps(
                    Expr::const_str(names::TRIE_INS_PRESERVES_ALL_SAT),
                    [
                        holds.clone(),
                        db.clone(),
                        nextid.clone(),
                        res.clone(),
                        hall.clone(),
                        sat_or_nil_res,
                    ],
                );

                // case on isCons rest, transporting tail_true.
                let isc = is_cons(rest.clone());
                let subst_motive = {
                    let inner = eq_bool(tail_of(Expr::bvar(0)), btrue());
                    Expr::lam(BinderInfo::Default, bool_ty(), inner)
                };
                // case_f (heq : isCons = false): tail ≡ stepEmpty s; transport tail_true.
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
                        Expr::const_str(names::LIST_IS_NIL_SAT),
                        [
                            holds.clone(),
                            step_resolvent(s.clone()),
                            se_true,
                            res_sat.clone(),
                        ],
                    );
                    e.finish_child(e.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                };
                // case_t (heq : isCons = true): tail ≡ checkRefutes3 new_db new_next rest; recurse.
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
                    // ih new_db new_next all_ins go_true : False
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
                let r = d.mk_lam(restid, BinderInfo::Default, list_step.clone(), r);
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
            let r = b.mk_lam(pfid, BinderInfo::Default, list_step.clone(), folded);
            let r = b.mk_lam(heid, BinderInfo::Default, excl_pred(&holds), r);
            let r = b.mk_lam(hcid, BinderInfo::Default, cons_pred(&holds), r);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::GO3_SOUND),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `checkRefutes3_sound :`
    /// `(cs : List (List Nat)) → (steps : List Step) →`
    /// `Eq (checkRefutes3 (initialTrie cs) (listLen cs) steps) true → Unsat cs`.
    ///
    /// The top-level bridge for the sub-quadratic trie checker. Its `Unsat cs`
    /// conclusion is the δ-unfolded model body (same presentation as
    /// `checkRefutes_sound`). The initial trie `initialTrie cs` (clause `cs[i]` at id
    /// `i`) satisfies `allSatTrie H` whenever `allSat H cs` holds — `initialTrieAllSat`
    /// — so `go3Sound` applies with the initial trie + `nextId = listLen cs`.
    fn register_check_refutes3_sound_thm(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::CHECK_REFUTES3_SOUND))
            .is_some()
        {
            return Ok(());
        }
        self.register_initial_trie_all_sat()?;
        let step_ty = Expr::const_str(rnames::STEP);
        let list_step = Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            step_ty,
        );
        let check_refutes3 = |db: Expr, nid: Expr, pf: Expr| {
            Expr::apps(Expr::const_str(rnames::CHECK_REFUTES3), [db, nid, pf])
        };
        let list_len = |cs: Expr| Expr::app(Expr::const_str(rnames::LIST_LEN), cs);
        let initial_trie = |cs: Expr| Expr::app(Expr::const_str(INITIAL_TRIE), cs);

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (csid, cs) = b.fresh_local(list_list_nat());
            let (stepsid, steps) = b.fresh_local(list_step.clone());
            // Unsat cs spelled δ-unfolded (same presentation as checkRefutes_sound).
            let unsat = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hid, holds) = c.fresh_local(holds_ty());
                let cons_pred = Expr::app(Expr::const_str(names::RES_CONSISTENT), holds.clone());
                let excl_pred = Expr::app(Expr::const_str(names::RES_EXCLUSIVE), holds.clone());
                let all_cs =
                    Expr::apps(Expr::const_str(names::ALL_SAT), [holds.clone(), cs.clone()]);
                let body = Expr::arrow(all_cs, false_c());
                let body = Expr::arrow(excl_pred, body);
                let body = Expr::arrow(cons_pred, body);
                c.finish_child(c.mk_pi(hid, BinderInfo::Default, holds_ty(), body))
            };
            let hck = eq_bool(
                check_refutes3(
                    initial_trie(cs.clone()),
                    list_len(cs.clone()),
                    steps.clone(),
                ),
                btrue(),
            );
            let inner = Expr::arrow(hck, unsat);
            let e = b.mk_pi(stepsid, BinderInfo::Default, list_step.clone(), inner);
            b.finish(b.mk_pi(csid, BinderInfo::Default, list_list_nat(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (csid, cs) = b.fresh_local(list_list_nat());
            let (stepsid, steps) = b.fresh_local(list_step.clone());
            let hck_ty = eq_bool(
                check_refutes3(
                    initial_trie(cs.clone()),
                    list_len(cs.clone()),
                    steps.clone(),
                ),
                btrue(),
            );
            let (hckid, hck) = b.fresh_local(hck_ty.clone());
            // Unsat cs ≡ (H) → resConsistent H → resExclusive H → allSat H cs → False
            let (hid, holds) = b.fresh_local(holds_ty());
            let cons_pred = Expr::app(Expr::const_str(names::RES_CONSISTENT), holds.clone());
            let (hcid, hcons) = b.fresh_local(cons_pred.clone());
            let excl_pred = Expr::app(Expr::const_str(names::RES_EXCLUSIVE), holds.clone());
            let (heid, hexcl) = b.fresh_local(excl_pred.clone());
            let all_cs = Expr::apps(Expr::const_str(names::ALL_SAT), [holds.clone(), cs.clone()]);
            let (haid, hall) = b.fresh_local(all_cs.clone());
            // allSatTrie H (initialTrie cs) := initialTrieAllSat H cs hall.
            let all_db0 = Expr::apps(
                Expr::const_str(INITIAL_TRIE_ALL_SAT),
                [holds.clone(), cs.clone(), hall],
            );
            // go3Sound H hcons hexcl steps (initialTrie cs) (listLen cs) all_db0 hck : False
            let body = Expr::apps(
                Expr::const_str(names::GO3_SOUND),
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
            let r = b.mk_lam(heid, BinderInfo::Default, excl_pred, r);
            let r = b.mk_lam(hcid, BinderInfo::Default, cons_pred, r);
            let r = b.mk_lam(hid, BinderInfo::Default, holds_ty(), r);
            let r = b.mk_lam(hckid, BinderInfo::Default, hck_ty, r);
            let r = b.mk_lam(stepsid, BinderInfo::Default, list_step.clone(), r);
            b.finish(b.mk_lam(csid, BinderInfo::Default, list_list_nat(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::CHECK_REFUTES3_SOUND),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Define the kernel initial-trie builder + prove `initialTrieAllSat`.
    ///
    /// ```text
    ///   initialTrieAux cs : Nat → Trie :=
    ///     List.rec (motive := fun _ => Nat → Trie)
    ///       (fun _id => Trie.leaf)
    ///       (fun c rest ih => fun id => trieIns (ih (Nat.succ id)) id c)
    ///       cs
    ///   initialTrie cs := initialTrieAux cs 0
    /// ```
    ///
    /// (Clause `cs[i]` is inserted at global id `i`.) `initialTrieAuxAllSat` is the
    /// `List.rec` induction on `cs` (id generalised): `nil ↦ allSatTrie leaf ≡ True`;
    /// `cons c rest ↦ trieInsPreservesAllSat` with the inserted `c` SAT-or-nil from
    /// `allSat`'s head `And`, and the inner trie SAT-or-nil from the IH at `id+1`.
    /// Define the kernel initial-trie builder + prove `initialTrieAllSat`.
    ///
    /// ```text
    ///   initialTrieGo : List (List Nat) → Trie → Nat → Trie :=
    ///     List.rec (motive := fun _ => Trie → Nat → Trie)
    ///       (fun acc _id => acc)                                          -- nil
    ///       (fun c rest ih => fun acc id => ih (trieIns acc id c) (Nat.succ id))
    ///   initialTrie cs := initialTrieGo cs Trie.leaf 0
    /// ```
    ///
    /// A LEFT (accumulator) fold: clause `cs[i]` is inserted at global id `i`. The
    /// accumulator placement is deliberate — the cons-case reduction
    /// `initialTrieGo (c::rest) acc id ≡ initialTrieGo rest (trieIns acc id c) (succ id)`
    /// keeps the head `initialTrieGo` (NOT `trieIns`), so the `List.rec`
    /// recursor-boundary defeq in `initialTrieGoAllSat` never has to whnf-expand the
    /// 60-fuel `trieIns` (which would stall on a symbolic id). `initialTrieGoAllSat`
    /// generalises `acc` and `id`: `nil ↦ acc` (the accumulator invariant is the hyp);
    /// `cons c rest ↦` recurse with `acc' = trieIns acc id c` (SAT-or-nil via
    /// `trieInsPreservesAllSat`).
    fn register_initial_trie_all_sat(&mut self) -> Result<(), EnvError> {
        let u1 = Level::succ(Level::zero());
        let trie_ins =
            |db: Expr, k: Expr, c: Expr| Expr::apps(Expr::const_str(rnames::TRIE_INS), [db, k, c]);
        // carrier of the fold: Trie → Nat → Trie   (acc, id).
        let carrier = Expr::arrow(trie_ty(), Expr::arrow(nat_ty(), trie_ty()));
        let go = |cs: Expr, acc: Expr, id: Expr| {
            Expr::apps(Expr::const_str(INITIAL_TRIE_GO), [cs, acc, id])
        };

        // ── initialTrieGo : List (List Nat) → Trie → Nat → Trie ──
        if self
            .get_const(&Name::from_string(INITIAL_TRIE_GO))
            .is_none()
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (csid, cs) = b.fresh_local(list_list_nat());
                // nil case : fun (acc : Trie)(_id : Nat) => acc
                let nil_case = Expr::lam(
                    BinderInfo::Default,
                    trie_ty(),
                    Expr::lam(BinderInfo::Default, nat_ty(), Expr::bvar(1)),
                );
                // cons case : fun (c)(rest)(ih : carrier) => fun (acc)(id) =>
                //   ih (trieIns acc id c) (succ id)
                //   bvars: id=0, acc=1, ih=2, rest=3, c=4
                let cons_case = {
                    let c = Expr::bvar(4);
                    let ih = Expr::bvar(2);
                    let acc = Expr::bvar(1);
                    let id = Expr::bvar(0);
                    let new_acc = trie_ins(acc, id.clone(), c);
                    let body = Expr::apps(ih, [new_acc, nat_succ(id)]);
                    Expr::lam(
                        BinderInfo::Default,
                        list_nat(),
                        Expr::lam(
                            BinderInfo::Default,
                            list_list_nat(),
                            Expr::lam(
                                BinderInfo::Default,
                                carrier.clone(),
                                Expr::lam(
                                    BinderInfo::Default,
                                    trie_ty(),
                                    Expr::lam(BinderInfo::Default, nat_ty(), body),
                                ),
                            ),
                        ),
                    )
                };
                let rec = Expr::const_(
                    Name::from_string("List.rec"),
                    vec![Level::succ(Level::zero()), Level::zero()],
                );
                let motive = Expr::lam(BinderInfo::Default, list_list_nat(), carrier.clone());
                let folded = Expr::apps(rec, [list_nat(), motive, nil_case, cons_case, cs.clone()]);
                b.finish(b.mk_lam(csid, BinderInfo::Default, list_list_nat(), folded))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(INITIAL_TRIE_GO),
                level_params: vec![],
                type_: Expr::arrow(list_list_nat(), carrier.clone()),
                value: val,
                is_reducible: true,
            })?;
        }

        // ── initialTrie cs := initialTrieGo cs Trie.leaf 0 ──
        // SUB-QUADRATIC (2026-06-20 fix): the starting insert id is the BigNat
        // LITERAL 0 (`nat_lit(0)`), NOT the `Nat.zero` constructor. `initialTrieGo`
        // threads `Nat.succ id`, which on a BigNat literal reduces NATIVELY to the
        // next literal (`tc/reduction/nat.rs`), so every `trieIns acc id c` extracts
        // its key bits via `Nat.div`/`Nat.mod` natively → O(log id) per insert and an
        // O(|cs| log|cs|) initial-trie build (vs O(|cs|²) when the ids were the unary
        // `Nat.zero, Nat.succ Nat.zero, …`). The proof (`initialTrieGoAllSat`) is
        // id-AGNOSTIC — it threads `id` symbolically and never whnf's it — so this
        // change is value-preserving and the soundness proof is unaffected (the
        // `initialTrieGoAllSat` instance below seeds the SAME `nat_lit(0)`).
        if self.get_const(&Name::from_string(INITIAL_TRIE)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (csid, cs) = b.fresh_local(list_list_nat());
                let body = go(cs.clone(), trie_leaf(), nat_lit(0));
                b.finish(b.mk_lam(csid, BinderInfo::Default, list_list_nat(), body))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(INITIAL_TRIE),
                level_params: vec![],
                type_: Expr::arrow(list_list_nat(), trie_ty()),
                value: val,
                is_reducible: true,
            })?;
        }

        // ── initialTrieGoAllSat : (H)(cs) → (acc)(id) → allSatTrie H acc →
        //                          allSat H cs → allSatTrie H (initialTrieGo cs acc id) ──
        // (acc and id generalised; the accumulator invariant is the extra premise.)
        if self
            .get_const(&Name::from_string(INITIAL_TRIE_GO_ALL_SAT))
            .is_none()
        {
            let all_sat =
                |cs: Expr, h: &Expr| Expr::apps(Expr::const_str(names::ALL_SAT), [h.clone(), cs]);
            // motive over cs : fun cs => (acc)(id) → allSatTrie H acc → allSat H cs →
            //                            allSatTrie H (initialTrieGo cs acc id)
            let mk_motive_body = |holds: &Expr, cs: &Expr, parent: &EnvDeclBuilder| -> Expr {
                let mut c = EnvDeclBuilder::child_of(parent);
                let (accid, acc) = c.fresh_local(trie_ty());
                let (idid, id) = c.fresh_local(nat_ty());
                let concl = Expr::arrow(
                    all_sat_trie(holds.clone(), acc.clone()),
                    Expr::arrow(
                        all_sat(cs.clone(), holds),
                        all_sat_trie(holds.clone(), go(cs.clone(), acc.clone(), id.clone())),
                    ),
                );
                let inner = c.mk_pi(idid, BinderInfo::Default, nat_ty(), concl);
                c.finish_child(c.mk_pi(accid, BinderInfo::Default, trie_ty(), inner))
            };

            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty());
                let (csid, cs) = b.fresh_local(list_list_nat());
                let body = mk_motive_body(&holds, &cs, &b);
                let e = b.mk_pi(csid, BinderInfo::Default, list_list_nat(), body);
                b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty());
                let (csid, cs) = b.fresh_local(list_list_nat());
                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (mid, m) = d.fresh_local(list_list_nat());
                    let body = mk_motive_body(&holds, &m, &d);
                    d.finish_child(d.mk_lam(mid, BinderInfo::Default, list_list_nat(), body))
                };
                // nil : fun (acc)(id)(hacc : allSatTrie H acc)(_ : allSat H nil) => hacc
                //   (initialTrieGo nil acc id ≡ acc)
                let nil_case = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (accid, acc) = d.fresh_local(trie_ty());
                    let (idid, _id) = d.fresh_local(nat_ty());
                    let hacc_ty = all_sat_trie(holds.clone(), acc.clone());
                    let (haccid, hacc) = d.fresh_local(hacc_ty.clone());
                    let nil_db = Expr::app(
                        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                        list_nat(),
                    );
                    let has_ty = all_sat(nil_db, &holds);
                    let (hasid, _has) = d.fresh_local(has_ty.clone());
                    let r = d.mk_lam(hasid, BinderInfo::Default, has_ty, hacc);
                    let r = d.mk_lam(haccid, BinderInfo::Default, hacc_ty, r);
                    let r = d.mk_lam(idid, BinderInfo::Default, nat_ty(), r);
                    d.finish_child(d.mk_lam(accid, BinderInfo::Default, trie_ty(), r))
                };
                // cons c rest ih : fun (acc)(id)(hacc)(hall : And (clauseOr H c)(allSat H rest)) =>
                //   ih (trieIns acc id c) (succ id)
                //     (trieInsPreservesAllSat H acc id c hacc (Or.inl (And.left hall)))   -- allSatTrie acc'
                //     (And.right hall)                                                     -- allSat rest
                let cons_case = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (cid, c) = d.fresh_local(list_nat());
                    let (restid, rest) = d.fresh_local(list_list_nat());
                    let ih_ty = mk_motive_body(&holds, &rest, &d);
                    let (ihid, ih) = d.fresh_local(ih_ty.clone());
                    let (accid, acc) = d.fresh_local(trie_ty());
                    let (idid, id) = d.fresh_local(nat_ty());
                    let hacc_ty = all_sat_trie(holds.clone(), acc.clone());
                    let (haccid, hacc) = d.fresh_local(hacc_ty.clone());
                    let db_cons = Expr::apps(
                        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                        [list_nat(), c.clone(), rest.clone()],
                    );
                    let hall_ty = all_sat(db_cons, &holds);
                    let (hallid, hall) = d.fresh_local(hall_ty.clone());
                    let co_c = clause_or(holds.clone(), c.clone());
                    let all_rest = all_sat(rest.clone(), &holds);
                    let left = and_left(co_c.clone(), all_rest.clone(), hall.clone());
                    let right = and_right(co_c.clone(), all_rest.clone(), hall);
                    // acc' := trieIns acc id c
                    let new_acc = trie_ins(acc.clone(), id.clone(), c.clone());
                    // allSatTrie H acc' via trieInsPreservesAllSat
                    let sat_or_nil_c = or_inl(
                        co_c.clone(),
                        eq_at(u1.clone(), list_nat(), c.clone(), list_nil_nat()),
                        left.clone(),
                    );
                    let acc_prime_sat = Expr::apps(
                        Expr::const_str(names::TRIE_INS_PRESERVES_ALL_SAT),
                        [
                            holds.clone(),
                            acc.clone(),
                            id.clone(),
                            c.clone(),
                            hacc.clone(),
                            sat_or_nil_c,
                        ],
                    );
                    // ih (trieIns acc id c) (succ id) acc_prime_sat right
                    //   : allSatTrie H (initialTrieGo rest acc' (succ id))
                    //   ≡ allSatTrie H (initialTrieGo (c::rest) acc id)   (List.rec ι; head = initialTrieGo)
                    let body = Expr::apps(
                        ih.clone(),
                        [new_acc, nat_succ(id.clone()), acc_prime_sat, right],
                    );
                    let r = d.mk_lam(hallid, BinderInfo::Default, hall_ty, body);
                    let r = d.mk_lam(haccid, BinderInfo::Default, hacc_ty, r);
                    let r = d.mk_lam(idid, BinderInfo::Default, nat_ty(), r);
                    let r = d.mk_lam(accid, BinderInfo::Default, trie_ty(), r);
                    let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, r);
                    let r = d.mk_lam(restid, BinderInfo::Default, list_list_nat(), r);
                    d.finish_child(d.mk_lam(cid, BinderInfo::Default, list_nat(), r))
                };
                let list_rec = Expr::const_(
                    Name::from_string("List.rec"),
                    vec![Level::zero(), Level::zero()],
                );
                let folded = Expr::apps(
                    list_rec,
                    [list_nat(), motive, nil_case, cons_case, cs.clone()],
                );
                let e = b.mk_lam(csid, BinderInfo::Default, list_list_nat(), folded);
                b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(INITIAL_TRIE_GO_ALL_SAT),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── initialTrieAllSat : (H)(cs) → allSat H cs → allSatTrie H (initialTrie cs) ──
        if self
            .get_const(&Name::from_string(INITIAL_TRIE_ALL_SAT))
            .is_none()
        {
            let all_sat =
                |cs: Expr, h: &Expr| Expr::apps(Expr::const_str(names::ALL_SAT), [h.clone(), cs]);
            let initial_trie = |cs: Expr| Expr::app(Expr::const_str(INITIAL_TRIE), cs);
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty());
                let (csid, cs) = b.fresh_local(list_list_nat());
                let body = Expr::arrow(
                    all_sat(cs.clone(), &holds),
                    all_sat_trie(holds.clone(), initial_trie(cs.clone())),
                );
                let e = b.mk_pi(csid, BinderInfo::Default, list_list_nat(), body);
                b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty());
                let (csid, cs) = b.fresh_local(list_list_nat());
                let hall_ty = all_sat(cs.clone(), &holds);
                let (hallid, hall) = b.fresh_local(hall_ty.clone());
                // initialTrie cs ≡ initialTrieGo cs leaf 0   (0 = BigNat literal,
                // matching `initialTrie`'s definition above — keeps the proof's
                // conclusion `allSatTrie H (initialTrieGo cs leaf 0)` syntactically the
                // δ-unfolding of `allSatTrie H (initialTrie cs)`).
                //   initialTrieGoAllSat H cs leaf 0 (True.intro : allSatTrie H leaf) hall
                let leaf_sat = Expr::const_str("True.intro");
                let body = Expr::apps(
                    Expr::const_str(INITIAL_TRIE_GO_ALL_SAT),
                    [
                        holds.clone(),
                        cs.clone(),
                        trie_leaf(),
                        nat_lit(0),
                        leaf_sat,
                        hall,
                    ],
                );
                let r = b.mk_lam(hallid, BinderInfo::Default, hall_ty, body);
                let r = b.mk_lam(csid, BinderInfo::Default, list_list_nat(), r);
                b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), r))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(INITIAL_TRIE_ALL_SAT),
                level_params: vec![],
                type_,
                value,
            })?;
        }
        Ok(())
    }

    /// Three one-step projection lemmas from `allSatTrie H db`, each by `Trie.rec`:
    ///
    ///   * `trieValSat  : allSatTrie H db → Or (clauseOr H (trieVal db)) (trieVal db = nil)`
    ///   * `trieLoAllSat : allSatTrie H db → allSatTrie H (trieLo db)`
    ///   * `trieHiAllSat : allSatTrie H db → allSatTrie H (trieHi db)`
    ///
    /// (`leaf`: `trieVal leaf ≡ nil`, `trieLo/Hi leaf ≡ leaf`, `allSatTrie leaf ≡
    /// True`; `node`: project the `And`-tree of `allSatTrie (node …)`.)
    fn register_trie_proj_lemmas(&mut self) -> Result<(), EnvError> {
        let u1 = Level::succ(Level::zero());
        let trie_val = |t: Expr| Expr::app(Expr::const_str("Clean.Res.trieVal"), t);
        let trie_lo = |t: Expr| Expr::app(Expr::const_str("Clean.Res.trieLo"), t);
        let trie_hi = |t: Expr| Expr::app(Expr::const_str("Clean.Res.trieHi"), t);

        // ── trieValSat : allSatTrie H db → satOrNil (trieVal db) ──
        if self.get_const(&Name::from_string(TRIE_VAL_SAT)).is_none() {
            let mk_concl = |holds: &Expr, db: &Expr| -> Expr {
                let tv = trie_val(db.clone());
                sat_or_nil(holds, &tv)
            };
            // motive m := allSatTrie H m → satOrNil (trieVal m)  (the IH binder types).
            let mk_motive_body = |holds: &Expr, m: &Expr| -> Expr {
                Expr::arrow(all_sat_trie(holds.clone(), m.clone()), mk_concl(holds, m))
            };
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty());
                let (dbid, db) = b.fresh_local(trie_ty());
                let body = Expr::arrow(
                    all_sat_trie(holds.clone(), db.clone()),
                    mk_concl(&holds, &db),
                );
                let e = b.mk_pi(dbid, BinderInfo::Default, trie_ty(), body);
                b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty());
                let (dbid, db) = b.fresh_local(trie_ty());
                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (mid, m) = d.fresh_local(trie_ty());
                    let body = mk_motive_body(&holds, &m);
                    d.finish_child(d.mk_lam(mid, BinderInfo::Default, trie_ty(), body))
                };
                // leaf : fun (_ : allSatTrie H leaf) => Or.inr (rfl : trieVal leaf = nil)
                let leaf_case = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let as_ty = all_sat_trie(holds.clone(), trie_leaf());
                    let (asid, _as) = d.fresh_local(as_ty.clone());
                    let tv = trie_val(trie_leaf());
                    let refl = eq_refl_at(u1.clone(), list_nat(), tv.clone());
                    let body = or_inr(
                        clause_or(holds.clone(), tv.clone()),
                        eq_at(u1.clone(), list_nat(), tv, list_nil_nat()),
                        refl,
                    );
                    d.finish_child(d.mk_lam(asid, BinderInfo::Default, as_ty, body))
                };
                // node v lo hi ih_lo ih_hi : fun (hall) => And.left (head)(children) hall
                //   (trieVal (node v lo hi) ≡ v, satOrNil v is the head conjunct)
                let node_case = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (vid, v) = d.fresh_local(list_nat());
                    let (loid, lo) = d.fresh_local(trie_ty());
                    let (hiid, hi) = d.fresh_local(trie_ty());
                    let ih_lo_ty = mk_motive_body(&holds, &lo);
                    let (ihloid, _il) = d.fresh_local(ih_lo_ty.clone());
                    let ih_hi_ty = mk_motive_body(&holds, &hi);
                    let (ihhiid, _ih) = d.fresh_local(ih_hi_ty.clone());
                    let node_e = trie_node(v.clone(), lo.clone(), hi.clone());
                    let hall_ty = all_sat_trie(holds.clone(), node_e);
                    let (hallid, hall) = d.fresh_local(hall_ty.clone());
                    let head = sat_or_nil(&holds, &v);
                    let children = Expr::apps(
                        Expr::const_(Name::from_string("And"), vec![]),
                        [
                            all_sat_trie(holds.clone(), lo.clone()),
                            all_sat_trie(holds.clone(), hi.clone()),
                        ],
                    );
                    let body = and_left(head, children, hall);
                    let r = d.mk_lam(hallid, BinderInfo::Default, hall_ty, body);
                    let r = d.mk_lam(ihhiid, BinderInfo::Default, ih_hi_ty, r);
                    let r = d.mk_lam(ihloid, BinderInfo::Default, ih_lo_ty, r);
                    let r = d.mk_lam(hiid, BinderInfo::Default, trie_ty(), r);
                    let r = d.mk_lam(loid, BinderInfo::Default, trie_ty(), r);
                    d.finish_child(d.mk_lam(vid, BinderInfo::Default, list_nat(), r))
                };
                let trie_rec =
                    Expr::const_(Name::from_string("Clean.Res.Trie.rec"), vec![Level::zero()]);
                let folded = Expr::apps(trie_rec, [motive, leaf_case, node_case, db.clone()]);
                let e = b.mk_lam(dbid, BinderInfo::Default, trie_ty(), folded);
                b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(TRIE_VAL_SAT),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── trieLoAllSat / trieHiAllSat : allSatTrie H db → allSatTrie H (trieLo/Hi db) ──
        // Built by the same Trie.rec shape; `pick_child` selects lo or hi.
        let mut mk_child_lemma = |name: &str, is_lo: bool| -> Result<(), EnvError> {
            if self.get_const(&Name::from_string(name)).is_some() {
                return Ok(());
            }
            let child = |t: Expr| if is_lo { trie_lo(t) } else { trie_hi(t) };
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty());
                let (dbid, db) = b.fresh_local(trie_ty());
                let body = Expr::arrow(
                    all_sat_trie(holds.clone(), db.clone()),
                    all_sat_trie(holds.clone(), child(db.clone())),
                );
                let e = b.mk_pi(dbid, BinderInfo::Default, trie_ty(), body);
                b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
            };
            let mk_motive_body = |holds: &Expr, m: &Expr| -> Expr {
                Expr::arrow(
                    all_sat_trie(holds.clone(), m.clone()),
                    all_sat_trie(holds.clone(), child(m.clone())),
                )
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty());
                let (dbid, db) = b.fresh_local(trie_ty());
                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (mid, m) = d.fresh_local(trie_ty());
                    let body = mk_motive_body(&holds, &m);
                    d.finish_child(d.mk_lam(mid, BinderInfo::Default, trie_ty(), body))
                };
                // leaf : fun (h : allSatTrie H leaf) => h   (trieLo/Hi leaf ≡ leaf, so target ≡ allSatTrie H leaf)
                let leaf_case = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let as_ty = all_sat_trie(holds.clone(), trie_leaf());
                    let (asid, h) = d.fresh_local(as_ty.clone());
                    d.finish_child(d.mk_lam(asid, BinderInfo::Default, as_ty, h))
                };
                // node v lo hi ih_lo ih_hi : fun (hall) => project the And tree to lo/hi
                let node_case = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (vid, v) = d.fresh_local(list_nat());
                    let (loid, lo) = d.fresh_local(trie_ty());
                    let (hiid, hi) = d.fresh_local(trie_ty());
                    let ih_lo_ty = mk_motive_body(&holds, &lo);
                    let (ihloid, _il) = d.fresh_local(ih_lo_ty.clone());
                    let ih_hi_ty = mk_motive_body(&holds, &hi);
                    let (ihhiid, _ih) = d.fresh_local(ih_hi_ty.clone());
                    let node_e = trie_node(v.clone(), lo.clone(), hi.clone());
                    let hall_ty = all_sat_trie(holds.clone(), node_e);
                    let (hallid, hall) = d.fresh_local(hall_ty.clone());
                    let head = sat_or_nil(&holds, &v);
                    let lo_as = all_sat_trie(holds.clone(), lo.clone());
                    let hi_as = all_sat_trie(holds.clone(), hi.clone());
                    let children = Expr::apps(
                        Expr::const_(Name::from_string("And"), vec![]),
                        [lo_as.clone(), hi_as.clone()],
                    );
                    let children_proof = and_right(head, children, hall);
                    let body = if is_lo {
                        and_left(lo_as, hi_as, children_proof)
                    } else {
                        and_right(lo_as, hi_as, children_proof)
                    };
                    let r = d.mk_lam(hallid, BinderInfo::Default, hall_ty, body);
                    let r = d.mk_lam(ihhiid, BinderInfo::Default, ih_hi_ty, r);
                    let r = d.mk_lam(ihloid, BinderInfo::Default, ih_lo_ty, r);
                    let r = d.mk_lam(hiid, BinderInfo::Default, trie_ty(), r);
                    let r = d.mk_lam(loid, BinderInfo::Default, trie_ty(), r);
                    d.finish_child(d.mk_lam(vid, BinderInfo::Default, list_nat(), r))
                };
                let trie_rec =
                    Expr::const_(Name::from_string("Clean.Res.Trie.rec"), vec![Level::zero()]);
                let folded = Expr::apps(trie_rec, [motive, leaf_case, node_case, db.clone()]);
                let e = b.mk_lam(dbid, BinderInfo::Default, trie_ty(), folded);
                b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(name),
                level_params: vec![],
                type_,
                value,
            })
        };
        mk_child_lemma(TRIE_LO_ALL_SAT, true)?;
        mk_child_lemma(TRIE_HI_ALL_SAT, false)?;
        Ok(())
    }

    /// `allSatTrie H db : Prop` — every node's value is SAT-or-nil, recursively.
    ///
    /// ```text
    ///   allSatTrie H := Trie.rec (motive := fun _ => Prop)
    ///     /-leaf-/ True
    ///     /-node-/ (fun val lo hi ih_lo ih_hi =>
    ///                And (Or (clauseOr H val) (val = nil)) (And ih_lo ih_hi))
    /// ```
    fn register_all_sat_trie(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::ALL_SAT_TRIE))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::arrow(holds_ty(), Expr::arrow(trie_ty(), Expr::prop()));
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            // node case : fun (val : List Nat)(lo hi : Trie)(ih_lo ih_hi : Prop) =>
            //   And (Or (clauseOr H val)(val = nil)) (And ih_lo ih_hi)
            //   bvars: ih_hi=0, ih_lo=1, hi=2, lo=3, val=4
            let node_case = {
                let val_b = Expr::bvar(4);
                let ih_lo = Expr::bvar(1);
                let ih_hi = Expr::bvar(0);
                let head = sat_or_nil(&holds, &val_b);
                let children = Expr::apps(
                    Expr::const_(Name::from_string("And"), vec![]),
                    [ih_lo, ih_hi],
                );
                let body = Expr::apps(
                    Expr::const_(Name::from_string("And"), vec![]),
                    [head, children],
                );
                Expr::lam(
                    BinderInfo::Default,
                    list_nat(), // val
                    Expr::lam(
                        BinderInfo::Default,
                        trie_ty(), // lo
                        Expr::lam(
                            BinderInfo::Default,
                            trie_ty(), // hi
                            Expr::lam(
                                BinderInfo::Default,
                                Expr::prop(), // ih_lo
                                Expr::lam(BinderInfo::Default, Expr::prop(), body), // ih_hi
                            ),
                        ),
                    ),
                )
            };
            let trie_rec = Expr::const_(
                Name::from_string("Clean.Res.Trie.rec"),
                vec![Level::succ(Level::zero())],
            );
            let motive = Expr::lam(BinderInfo::Default, trie_ty(), Expr::prop());
            // λ db => Trie.rec motive True node_case db
            let inner = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (dbid, db) = d.fresh_local(trie_ty());
                let folded = Expr::apps(
                    trie_rec,
                    [motive, Expr::const_str("True"), node_case, db.clone()],
                );
                d.finish_child(d.mk_lam(dbid, BinderInfo::Default, trie_ty(), folded))
            };
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), inner))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(names::ALL_SAT_TRIE),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    /// `trieGetSat : (H) → (db : Trie) → allSatTrie H db → (j : Nat) →`
    /// `Or (clauseOr H (trieGet db j)) (Eq (trieGet db j) List.nil)`.
    ///
    /// Structural induction on `db` via `Trie.rec` with the key `j` generalised
    /// (motive `fun db => allSatTrie H db → (j) → result_of db j`). `leaf` ⇒
    /// `trieGet leaf j ≡ nil` (right disjunct). `node val lo hi` ⇒ `allSatTrie ≡ And
    /// (satOrNil val)(And (allSatTrie lo)(allSatTrie hi))`; case `Nat.ble j 0`:
    /// `j = 0` returns `val` (the head conjunct, which IS `result_of (node…) 0`);
    /// `j ≠ 0` cases `Nat.ble 1 (j%2)` and applies `ih_lo`/`ih_hi` at `j/2` (whose
    /// `result_of` is defeq to `result_of (node…) j` in that branch).
    fn register_trie_get_sat(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::TRIE_GET_SAT))
            .is_some()
        {
            return Ok(());
        }
        let u1 = Level::succ(Level::zero());
        // result_of db j := Or (clauseOr H (trieGet db j)) (trieGet db j = nil)
        let result_of = |holds: &Expr, db: &Expr, j: &Expr| -> Expr {
            or_t(
                clause_or(holds.clone(), trie_get(db.clone(), j.clone())),
                eq_at(
                    u1.clone(),
                    list_nat(),
                    trie_get(db.clone(), j.clone()),
                    list_nil_nat(),
                ),
            )
        };
        // motive over db : fun db => allSatTrie H db → (j : Nat) → result_of db j
        let mk_motive_body = |holds: &Expr, db: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut c = EnvDeclBuilder::child_of(parent);
            let (jid, j) = c.fresh_local(nat_ty());
            let res = result_of(holds, db, &j);
            let forall_j = c.finish_child(c.mk_pi(jid, BinderInfo::Default, nat_ty(), res));
            Expr::arrow(all_sat_trie(holds.clone(), db.clone()), forall_j)
        };

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (dbid, db) = b.fresh_local(trie_ty());
            let body = mk_motive_body(&holds, &db, &b);
            let e = b.mk_pi(dbid, BinderInfo::Default, trie_ty(), body);
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty());
            let (dbid, db) = b.fresh_local(trie_ty());

            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(trie_ty());
                let body = mk_motive_body(&holds, &m, &d);
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, trie_ty(), body))
            };

            // leaf : fun (_ : allSatTrie H leaf)(j : Nat) => Or.inr (rfl : trieGet leaf j = nil)
            let leaf_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let as_ty = all_sat_trie(holds.clone(), trie_leaf());
                let (asid, _as) = d.fresh_local(as_ty.clone());
                let inner = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (jid, j) = e.fresh_local(nat_ty());
                    // trieGet leaf j ≡ nil, so rfl : trieGet leaf j = nil
                    let lhs = trie_get(trie_leaf(), j.clone());
                    let refl = eq_refl_at(u1.clone(), list_nat(), lhs.clone());
                    let body = or_inr(
                        clause_or(holds.clone(), lhs.clone()),
                        eq_at(u1.clone(), list_nat(), lhs, list_nil_nat()),
                        refl,
                    );
                    e.finish_child(e.mk_lam(jid, BinderInfo::Default, nat_ty(), body))
                };
                d.finish_child(d.mk_lam(asid, BinderInfo::Default, as_ty, inner))
            };

            // node val lo hi ih_lo ih_hi : fun (hall : allSatTrie H (node val lo hi))(j) => ...
            let node_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (vid, v) = d.fresh_local(list_nat());
                let (loid, lo) = d.fresh_local(trie_ty());
                let (hiid, hi) = d.fresh_local(trie_ty());
                let ih_lo_ty = mk_motive_body(&holds, &lo, &d);
                let (ihloid, ih_lo) = d.fresh_local(ih_lo_ty.clone());
                let ih_hi_ty = mk_motive_body(&holds, &hi, &d);
                let (ihhiid, ih_hi) = d.fresh_local(ih_hi_ty.clone());
                let node_e = trie_node(v.clone(), lo.clone(), hi.clone());
                let hall_ty = all_sat_trie(holds.clone(), node_e.clone());
                let (hallid, hall) = d.fresh_local(hall_ty.clone());

                // allSatTrie H (node v lo hi) ≡ And (satOrNil v) (And (allSatTrie lo)(allSatTrie hi))
                let head = sat_or_nil(&holds, &v);
                let lo_as = all_sat_trie(holds.clone(), lo.clone());
                let hi_as = all_sat_trie(holds.clone(), hi.clone());
                let children = Expr::apps(
                    Expr::const_(Name::from_string("And"), vec![]),
                    [lo_as.clone(), hi_as.clone()],
                );
                let head_proof = and_left(head.clone(), children.clone(), hall.clone());
                let children_proof = and_right(head.clone(), children.clone(), hall);
                let lo_proof = and_left(lo_as.clone(), hi_as.clone(), children_proof.clone());
                let hi_proof = and_right(lo_as.clone(), hi_as.clone(), children_proof);

                let inner = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (jid, j) = e.fresh_local(nat_ty());
                    let goal = result_of(&holds, &node_e, &j);
                    let half = nat_div(j.clone(), nat_lit(2));
                    let is_zero = nat_ble(j.clone(), nat_lit(0));
                    let is_odd = nat_ble(nat_lit(1), nat_mod(j.clone(), nat_lit(2)));

                    // res_at g := Or (clauseOr H g) (g = nil)   (goal ≡ res_at (trieGet (node…) j)).
                    let res_at = |g: &Expr| -> Expr {
                        or_t(
                            clause_or(holds.clone(), g.clone()),
                            eq_at(u1.clone(), list_nat(), g.clone(), list_nil_nat()),
                        )
                    };
                    // The closed-form unfolding of `trieGet (node v lo hi) j` (defeq to it):
                    //   full(b0) := Bool.rec (descend (Nat.ble 1 (j%2))) v b0
                    //   descend(bp) := Bool.rec (trieGet lo (j/2)) (trieGet hi (j/2)) bp
                    let glo = trie_get(lo.clone(), half.clone());
                    let ghi = trie_get(hi.clone(), half.clone());
                    let descend = |bp: Expr| -> Expr {
                        let m = Expr::lam(BinderInfo::Default, bool_ty(), list_nat());
                        Expr::apps(
                            Expr::const_(Name::from_string("Bool.rec"), vec![u1.clone()]),
                            [m, glo.clone(), ghi.clone(), bp],
                        )
                    };
                    let descend_p = descend(is_odd.clone());
                    let full = |b0: Expr| -> Expr {
                        let m = Expr::lam(BinderInfo::Default, bool_ty(), list_nat());
                        Expr::apps(
                            Expr::const_(Name::from_string("Bool.rec"), vec![u1.clone()]),
                            [m, descend_p.clone(), v.clone(), b0],
                        )
                    };

                    // ── j = 0 branch (h0 : Nat.ble j 0 = true) ──
                    // head_proof : res_at v ≡ res_at (full false). Transport along
                    // (symm h0 : true → no): we need res_at (full (Nat.ble j 0)).
                    //   m_full b0 := res_at (full b0); m_full true ≡ res_at (full true) ≡ res_at v.
                    let case_zero = {
                        let mut f = EnvDeclBuilder::child_of(&e);
                        let heq_ty = eq_bool(is_zero.clone(), btrue());
                        let (heqid, heq) = f.fresh_local(heq_ty.clone());
                        // motive m_full : fun b0 => res_at (full b0)
                        let m_full = {
                            let body = res_at(&full(Expr::bvar(0)));
                            Expr::lam(BinderInfo::Default, bool_ty(), body)
                        };
                        // head_proof : res_at v ≡ m_full true. subst a:=true b:=(Nat.ble j 0)
                        //   along (symm heq : true = Nat.ble j 0) → m_full (Nat.ble j 0) ≡ goal.
                        let body = eq_subst1(
                            bool_ty(),
                            m_full,
                            btrue(),
                            is_zero.clone(),
                            eq_symm_at(u1.clone(), bool_ty(), is_zero.clone(), btrue(), heq),
                            head_proof.clone(),
                        );
                        let _ = goal.clone();
                        f.finish_child(f.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                    };
                    // ── j ≠ 0 branch (h0 : Nat.ble j 0 = false), case on parity ──
                    let case_nonzero = {
                        let mut f = EnvDeclBuilder::child_of(&e);
                        let heq_ty = eq_bool(is_zero.clone(), bfalse());
                        let (heqid, h0) = f.fresh_local(heq_ty.clone());
                        let goal_parity = result_of(&holds, &node_e, &j);
                        // m_full b0 := res_at (full b0) — used to rewrite Nat.ble j 0 → false.
                        let m_full = {
                            let body = res_at(&full(Expr::bvar(0)));
                            Expr::lam(BinderInfo::Default, bool_ty(), body)
                        };
                        // Transport a proof `p : res_at (descend (Nat.ble 1 (j%2)))` ≡
                        //   m_full false  to  res_at (full (Nat.ble j 0)) ≡ goal, via (symm h0).
                        let lift_to_goal = |p: Expr| -> Expr {
                            eq_subst1(
                                bool_ty(),
                                m_full.clone(),
                                bfalse(),
                                is_zero.clone(),
                                eq_symm_at(
                                    u1.clone(),
                                    bool_ty(),
                                    is_zero.clone(),
                                    bfalse(),
                                    h0.clone(),
                                ),
                                p,
                            )
                        };
                        // m_desc bp := res_at (descend bp) — rewrite Nat.ble 1 (j%2) → its value.
                        let m_desc = {
                            let body = res_at(&descend(Expr::bvar(0)));
                            Expr::lam(BinderInfo::Default, bool_ty(), body)
                        };
                        // odd branch: ih_hi hi_proof (j/2) : res_at ghi ≡ m_desc true.
                        //   subst a:=true b:=(Nat.ble 1(j%2)) along (symm hp) → res_at (descend …).
                        let case_odd = {
                            let mut g = EnvDeclBuilder::child_of(&f);
                            let hodd_ty = eq_bool(is_odd.clone(), btrue());
                            let (hoddid, hp) = g.fresh_local(hodd_ty.clone());
                            let ih =
                                Expr::app(Expr::app(ih_hi.clone(), hi_proof.clone()), half.clone());
                            let p_desc = eq_subst1(
                                bool_ty(),
                                m_desc.clone(),
                                btrue(),
                                is_odd.clone(),
                                eq_symm_at(u1.clone(), bool_ty(), is_odd.clone(), btrue(), hp),
                                ih,
                            );
                            let body = lift_to_goal(p_desc);
                            g.finish_child(g.mk_lam(hoddid, BinderInfo::Default, hodd_ty, body))
                        };
                        // even branch: ih_lo lo_proof (j/2) : res_at glo ≡ m_desc false.
                        let case_even = {
                            let mut g = EnvDeclBuilder::child_of(&f);
                            let hev_ty = eq_bool(is_odd.clone(), bfalse());
                            let (hevid, hp) = g.fresh_local(hev_ty.clone());
                            let ih =
                                Expr::app(Expr::app(ih_lo.clone(), lo_proof.clone()), half.clone());
                            let p_desc = eq_subst1(
                                bool_ty(),
                                m_desc.clone(),
                                bfalse(),
                                is_odd.clone(),
                                eq_symm_at(u1.clone(), bool_ty(), is_odd.clone(), bfalse(), hp),
                                ih,
                            );
                            let body = lift_to_goal(p_desc);
                            g.finish_child(g.mk_lam(hevid, BinderInfo::Default, hev_ty, body))
                        };
                        let body = bool_cases(is_odd.clone(), goal_parity, case_even, case_odd);
                        f.finish_child(f.mk_lam(heqid, BinderInfo::Default, heq_ty, body))
                    };
                    let body = bool_cases(is_zero, goal, case_nonzero, case_zero);
                    e.finish_child(e.mk_lam(jid, BinderInfo::Default, nat_ty(), body))
                };
                let r = d.mk_lam(hallid, BinderInfo::Default, hall_ty, inner);
                let r = d.mk_lam(ihhiid, BinderInfo::Default, ih_hi_ty, r);
                let r = d.mk_lam(ihloid, BinderInfo::Default, ih_lo_ty, r);
                let r = d.mk_lam(hiid, BinderInfo::Default, trie_ty(), r);
                let r = d.mk_lam(loid, BinderInfo::Default, trie_ty(), r);
                d.finish_child(d.mk_lam(vid, BinderInfo::Default, list_nat(), r))
            };

            let trie_rec =
                Expr::const_(Name::from_string("Clean.Res.Trie.rec"), vec![Level::zero()]);
            let folded = Expr::apps(trie_rec, [motive, leaf_case, node_case, db.clone()]);
            let e = b.mk_lam(dbid, BinderInfo::Default, trie_ty(), folded);
            b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::TRIE_GET_SAT),
            level_params: vec![],
            type_,
            value,
        })
    }
}

/// From `h : Bool.or b1 b2 = true`, prove `Or (Eq b1 true) (Eq b2 true)`.
/// Case on `b1`: `true` ⇒ `Or.inl rfl`; `false` ⇒ `Bool.or false b2 ≡ b2`, so the
/// hypothesis rewrites to `b2 = true` (`Or.inr`).
fn bool_or_elim(b1: Expr, b2: Expr, h: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    let goal = or_t(eq_bool(b1.clone(), btrue()), eq_bool(b2.clone(), btrue()));
    // case_t (heq : b1 = true): Or.inl heq
    let case_t = {
        let heq_ty = eq_bool(b1.clone(), btrue());
        let body = or_inl(
            eq_bool(b1.clone(), btrue()),
            eq_bool(b2.clone(), btrue()),
            Expr::bvar(0),
        );
        Expr::lam(BinderInfo::Default, heq_ty, body)
    };
    // case_f (heq : b1 = false): rewrite h along heq → Bool.or false b2 = true ≡ b2 = true.
    let case_f = {
        let heq_ty = eq_bool(b1.clone(), bfalse());
        let motive = {
            let inner = eq_bool(
                Expr::apps(Expr::const_str("Bool.or"), [Expr::bvar(0), b2.clone()]),
                btrue(),
            );
            Expr::lam(BinderInfo::Default, bool_ty(), inner)
        };
        let b2_true = eq_subst1(
            bool_ty(),
            motive,
            b1.clone(),
            bfalse(),
            Expr::bvar(0),
            h.clone(),
        );
        let body = or_inr(
            eq_bool(b1.clone(), btrue()),
            eq_bool(b2.clone(), btrue()),
            b2_true,
        );
        Expr::lam(BinderInfo::Default, heq_ty, body)
    };
    let _ = u1;
    bool_cases(b1, goal, case_f, case_t)
}

/// From `h : Bool.and b1 b2 = true`, prove `b1 = true`.
/// `Eq.subst (fun bb => bb = true → b1 = true) ... ` — done via casing `b1`:
/// `Bool.and false _ ≡ false`, so the hyp would be `false = true` (absurd) at `b1=false`,
/// and at `b1=true` the goal `true=true` is `rfl`. Realized with the `Eq.refl`-trick.
fn bool_and_elim_left(b1: Expr, b2: Expr, h: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    let band = Expr::apps(Expr::const_str("Bool.and"), [b1.clone(), b2.clone()]);
    let goal = eq_bool(b1.clone(), btrue());
    // case_f (heq : b1 = false): Bool.and false b2 ≡ false; rewrite h to false=true; absurd.
    let case_f = {
        // rewrite h : Bool.and b1 b2 = true along heq:b1=false →
        //   Eq.subst (fun bb => Bool.and bb b2 = true) b1 false heq h : Bool.and false b2 = true
        //   ≡ false = true. tf_to_false (symm ·) → False → False.elim goal.
        let heq_ty = eq_bool(b1.clone(), bfalse());
        let motive = {
            let inner = eq_bool(
                Expr::apps(Expr::const_str("Bool.and"), [Expr::bvar(0), b2.clone()]),
                btrue(),
            );
            Expr::lam(BinderInfo::Default, bool_ty(), inner)
        };
        let false_true = eq_subst1(
            bool_ty(),
            motive,
            b1.clone(),
            bfalse(),
            Expr::bvar(0),
            h.clone(),
        );
        let ff = tf_to_false(eq_symm_at(
            u1.clone(),
            bool_ty(),
            bfalse(),
            btrue(),
            false_true,
        ));
        let body = false_elim(Level::zero(), goal.clone(), ff);
        // wrap fun (heq) => body : the bvar(0) above refers to heq
        Expr::lam(BinderInfo::Default, heq_ty, body)
    };
    // case_t (heq : b1 = true): goal b1=true is heq itself.
    let case_t = {
        let heq_ty = eq_bool(b1.clone(), btrue());
        Expr::lam(BinderInfo::Default, heq_ty, Expr::bvar(0))
    };
    let _ = band;
    bool_cases(b1, goal, case_f, case_t)
}

/// From `h : Bool.and b1 b2 = true`, prove `b2 = true`.
/// Case on `b1`: at `b1=false` the hyp is `false = true` (absurd); at `b1=true`,
/// `Bool.and true b2 ≡ b2`, so rewriting `h` yields `b2 = true`.
fn bool_and_elim_right(b1: Expr, b2: Expr, h: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    let goal = eq_bool(b2.clone(), btrue());
    let case_f = {
        let heq_ty = eq_bool(b1.clone(), bfalse());
        let motive = {
            let inner = eq_bool(
                Expr::apps(Expr::const_str("Bool.and"), [Expr::bvar(0), b2.clone()]),
                btrue(),
            );
            Expr::lam(BinderInfo::Default, bool_ty(), inner)
        };
        let false_true = eq_subst1(
            bool_ty(),
            motive,
            b1.clone(),
            bfalse(),
            Expr::bvar(0),
            h.clone(),
        );
        let ff = tf_to_false(eq_symm_at(
            u1.clone(),
            bool_ty(),
            bfalse(),
            btrue(),
            false_true,
        ));
        let body = false_elim(Level::zero(), goal.clone(), ff);
        Expr::lam(BinderInfo::Default, heq_ty, body)
    };
    let case_t = {
        // heq : b1 = true. rewrite h : Bool.and b1 b2 = true →
        //   Eq.subst (fun bb => Bool.and bb b2 = true) b1 true heq h : Bool.and true b2 = true
        //   ≡ b2 = true.
        let heq_ty = eq_bool(b1.clone(), btrue());
        let motive = {
            let inner = eq_bool(
                Expr::apps(Expr::const_str("Bool.and"), [Expr::bvar(0), b2.clone()]),
                btrue(),
            );
            Expr::lam(BinderInfo::Default, bool_ty(), inner)
        };
        let body = eq_subst1(
            bool_ty(),
            motive,
            b1.clone(),
            btrue(),
            Expr::bvar(0),
            h.clone(),
        );
        Expr::lam(BinderInfo::Default, heq_ty, body)
    };
    bool_cases(b1, goal, case_f, case_t)
}

/// `htf : Eq Bool.true Bool.false → False` via the `Bool.rec`-into-`Prop`
/// predicate `P x := Bool.rec (fun _ => Prop) True False x`. (Mirror of the
/// `bitvec_compute` helper; kept local to keep the modules independent.)
fn tf_to_false(htf: Expr) -> Expr {
    let p = {
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
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
    let eq_subst = Expr::const_(
        Name::from_string("Eq.subst"),
        vec![Level::succ(Level::zero())],
    );
    Expr::apps(
        eq_subst,
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

// Internal (non-public) lemma names for the trie-checker soundness layer.
const TRIE_VAL_SAT: &str = "Clean.Res.trieValSat";
const TRIE_LO_ALL_SAT: &str = "Clean.Res.trieLoAllSat";
const TRIE_HI_ALL_SAT: &str = "Clean.Res.trieHiAllSat";
const TRIE_INS_AUX_PRESERVES: &str = "Clean.Res.trieInsAuxPreservesAllSat";
/// Fuel `trieIns` is defined with (`resolution_check::TRIE_FUEL`). Must match so
/// `trieInsAux FUEL db k c ≡ trieIns db k c` holds definitionally.
const TRIE_FUEL: u64 = 60;
/// `Clean.Res.initialTrieGo : List (List Nat) → Trie → Nat → Trie` — the
/// accumulator left-fold that builds the initial clause trie (clause `i` inserted
/// at id `startId + i`).
const INITIAL_TRIE_GO: &str = "Clean.Res.initialTrieGo";
/// `Clean.Res.initialTrie : List (List Nat) → Trie` — `initialTrieGo cs leaf 0`.
const INITIAL_TRIE: &str = "Clean.Res.initialTrie";
/// PROVED `Clean.Res.initialTrieAllSat` — `allSat H cs → allSatTrie H (initialTrie cs)`.
/// `pub(crate)` for the LRAT soundness layer ([`crate::lrat_soundness`]), whose
/// top-level bridge reuses the same initial-trie invariant.
pub(crate) const INITIAL_TRIE_ALL_SAT: &str = "Clean.Res.initialTrieAllSat";
/// PROVED `Clean.Res.initialTrieGoAllSat` — the acc/id-generalised helper.
const INITIAL_TRIE_GO_ALL_SAT: &str = "Clean.Res.initialTrieGoAllSat";

#[cfg(test)]
#[path = "resolution_soundness_tests.rs"]
mod tests;
