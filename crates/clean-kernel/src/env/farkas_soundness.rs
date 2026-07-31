// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Foundational soundness substrate for the computational Farkas (LRA)
//! infeasibility checker, over a **Quot-free** difference-pair `Int`.
//!
//! HONEST SCOPE (read first). This module PROVES — as kernel-checked, axiom-free
//! `Declaration::Theorem`s — the full additive/order arithmetic tower over the
//! difference-pair `Int` (up to `intLeTrans`, `intAddMono`, `leNegFalse`, and the
//! multiplicative-monotonicity base case `natLeMulMonoR`). It DEFINES the checker
//! `farkasChecks` and the real semantic model (`rowsHold`/`Unsat`), and it builds
//! the TYPE of the headline bridge `farkasChecks_sound`. It does **NOT** prove
//! `farkasChecks_sound`: that theorem is NOT registered as a proof term, and
//! `Clean.Farkas.farkasChecks_sound` is absent from the environment. Nothing here
//! is `sorry`'d or axiom'd; the open obligation (the multiplicative half of the
//! tower) is documented below and deliberately left unproven rather than faked.
//!
//! This is the clean-side counterpart of the ck0-native reflection certificate
//! `crates/clean-ck0/tests/m5_farkas_cert.rs`. That cert builds a computational
//! checker `farkasChecks : Rows -> Bounds -> Mults -> Bool` over ck0 inductives
//! and *states* (kernel-checks the TYPE of) the soundness bridge but does NOT
//! prove it (the fold-induction over the rows + the LRA metatheorem are out of
//! ck0's closed-term scope). Here we DEFINE the same checker over clean's
//! prelude `Nat`/`List`/`Bool`/`Eq`/`And`/`Or`/`False` (plus a bespoke
//! difference-pair `Int := mk (pos neg : Nat)` — NOT `Quot`, NOT `Rat`) and prove
//! the supporting arithmetic. Every `Theorem` registered here has a transitive
//! axiom closure `⊆ FOUNDATIONAL_AXIOMS` (and in fact uses NO `Quot`/`propext` —
//! the substrate is Quot-free).
//!
//! # The mechanism (Farkas' lemma)
//!
//! A system of integer linear constraints `Σ_j a_ij x_j ≤ b_i` (i = 1..m) is
//! INFEASIBLE if there are nonneg multipliers `y_i ≥ 0` with
//!   (1) `Σ_i y_i a_ij = 0` for every column j, AND
//!   (2) `Σ_i y_i b_i < 0`.
//! Then for any assignment `x`,
//!   `0 = Σ_j (Σ_i y_i a_ij) x_j = Σ_i y_i (Σ_j a_ij x_j) ≤ Σ_i y_i b_i < 0`,
//! a contradiction (`0 ≤ negative`), so no `x` exists.
//!
//! # The Int encoding (difference pairs over Nat — Quot-free)
//!
//! `Int.mk (pos neg : Nat)` denotes `pos - neg`. Operations are total and
//! COMPUTE; comparison is semantic (`a ≤ b  ⇔  a.pos + b.neg ≤Nat b.pos + a.neg`).
//! Every op matches the m5 cert byte-for-byte.
//!
//! # Status (PROVED vs. precise remaining obligation — honest accounting)
//!
//! **Substrate (all PROVED / kernel-checked `Definition`s, Quot-free):** the
//! difference-pair `Int` inductive + `intPos`/`intNeg`; `natAdd`/`natMul`/
//! `natLe`/`natLt`/`band`; `intAdd`/`intMul`/`intLe`/`intLt`/`intEqZero`/
//! `intIsNeg`/`intIsNonneg`/`intEq`/`int0`; `headZ`/`tailZ`/`intListAdd`/
//! `intListScale`/`allEqZero`/`combineColumns`/`intDot`/`allNonneg`/
//! `farkasChecks`; the model `rowsHold` and `Unsat` (the REAL semantic
//! infeasibility `∀ x, rowsHold rows bounds x → False`).
//!
//! **Non-vacuity (computational, in tests):** the concrete m5 infeasible system
//! with its valid cert reduces `farkasChecks` to `Bool.true`; a feasible system
//! and bogus certs reduce to `Bool.false`. So `Unsat` is provable for a
//! genuinely infeasible system and the theorem is non-vacuous.
//!
//! **PROVED arithmetic (every one a `Theorem`, transitive axiom closure EMPTY —
//! no domain axioms, no `Quot`, no `propext`):**
//!   * Nat additive: `natAddZeroL`, `natAddSuccL`, `natAddComm`, `natAddAssoc`,
//!     `natAddReshuffle`, `natAddReshuffle2`.
//!   * Nat order: `natLeRefl`, `natLeAddR`, `natLeAddL`, `natLeAddBoth`,
//!     `natLeTrans`, `natLeAddCancelR`, `natLeContra`.
//!   * Int additive order: `intAddMono` (`a≤b → c≤d → a+c ≤ b+d`),
//!     `intLeTrans` (transitivity of `intLe` through cancellation).
//!   * Nat multiplicative (base case): `natLeMulMonoR`
//!     (`a≤b → natMul a c ≤ natMul b c`, induction on `c`).
//!   * Endpoint: `leNegFalse` — `intLe int0 d = true → intIsNeg d = true → False`
//!     (the `0 ≤ d < 0` arithmetic contradiction at the heart of Farkas).
//!
//! **CONCRETE soundness fragment (PROVED).** `m5UnsatConcrete : Unsat [[1],[-1]]
//! [-1,-1]` is a genuine kernel-checked, axiom-free `Declaration::Theorem`
//! (registered by [`Environment::init_farkas_proofs`]; see
//! `register_m5_unsat_concrete`). It witnesses that the m5 system `x ≤ -1 ∧
//! -x ≤ -1` has NO integer solution, via the Farkas combination with `y=(1,1)`:
//! `intAddMono` adds the two row hypotheses, the column sum cancels (a
//! comm/`reshuffle2` permutation identity gives `(d1+d2).neg = (d1+d2).pos`,
//! whence `natLeRefl`+`natAddZeroL` yield `int0 ≤ d1+d2`), `intLeTrans` chains
//! `int0 ≤ d1+d2 ≤ mk 0 2`, and `leNegFalse` closes it on the negative bound.
//! This is the clean-side parallel of the software kingdom's `emptyClauseUnsat`.
//!
//! **The headline (GENERAL) `farkasChecks_sound` is NOT proved.** Its TYPE is
//! kernel-checked to `Prop` (see [`farkas_checks_sound_type`] +
//! `test_farkas_checks_sound_type_is_well_formed_prop`), so the certificate
//! *structure* lives in clean's kernel — but no proof term is registered and
//! `Clean.Farkas.farkasChecks_sound` is absent from the environment. Closing it
//! honestly requires the rest of the MULTIPLICATIVE half of the tower, the PRECISE
//! REMAINING OBLIGATION:
//!   1. **(PROVED)** `natMulZeroL`/`natMulSuccL`/`natMulComm`/`natMulDistribR`
//!      (standard `Nat.rec` inductions; registered by
//!      [`Environment::init_farkas_mul_tower`]) — the genuine Nat multiplicative
//!      lemmas that, with the base case `natLeMulMonoR`, finish multiplicative
//!      monotonicity in both factors. These ARE kernel-checked, axiom-free
//!      Theorems.
//!   2. `intMulNonnegMono : intIsNonneg m = true → intLe a b = true →`
//!      `intLe (intMul m a)(intMul m b) = true` — over diff pairs this needs (1)
//!      plus a `mp·X + mn·X' ≤ mp·X' + mn·X` rearrangement (nonneg-multiplier
//!      monotonicity), which is itself a nontrivial inductive lemma. NOT yet proved.
//!   3. **(PARTIAL — equational substrate PROVED)** the Int *equational* tower
//!      `intEta` (structure eta), `intAddZeroL`, `intAddAssoc`, and `intMulDistribR`
//!      (right-distributivity of `intMul` over `intAdd` on the difference-pair rep)
//!      are now kernel-checked, axiom-free Theorems (registered by
//!      [`Environment::init_farkas_structural`]). These are the additive/distributive
//!      Eq-lemmas the `dotScale`/`dotDistAdd` folds consume. The folds themselves —
//!      `dotScale : intDot (intListScale m row) x = intMul m (intDot row x)` and
//!      `dotDistAdd : intDot (intListAdd u v) x = intAdd (intDot u x)(intDot v x)`
//!      (`List.rec` inductions; `dotDistAdd` additionally needs an `intDot`-unfold
//!      lemma for the variable second vector, and `intMulDistribL`) — are NOT yet
//!      registered.
//!   4. `dotZeroLowerBound : allEqZero v = true → intLe int0 (intDot v x) = true`
//!      (`List.rec` on `v`, using `intMul`-by-zero ≡ 0 and `intAddMono`). NOT yet proved.
//!   5. `farkasCore : allNonneg mults = true → rowsHold rows bounds x →`
//!      `intLe (intDot (combineColumns rows mults) x)(intDot mults bounds) = true`
//!      (the row/bound fold-induction, using (2),(3),`intAddMono`). NOT yet proved.
//!   6. `farkasChecks_sound`: split `farkasChecks = true` (three `band`-elims),
//!      chain `int0 ≤ intDot(combineColumns…) x` [via (4)] `≤ intDot mults bounds`
//!      [via (5)] with `intLeTrans`, then `leNegFalse` on `intIsNeg(intDot mults
//!      bounds)` closes it. NOT yet proved. (The concrete `m5UnsatConcrete` above
//!      is exactly this argument specialized to one infeasible instance.)
//!
//! Steps (1)–(6) are NOT registered here so that nothing is `sorry`'d or axiom'd
//! (which would be ingested as a false bridge through the clean→ck0 reflection).
//! Everything in this module that claims "proved" IS a kernel-checked, axiom-free
//! `Theorem`; the bridge itself is left honestly open, not faked.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::name::Name;
use crate::{
    BinderInfo, Constructor, Declaration, EnvError, Environment, Expr, InductiveDecl,
    InductiveType, Level,
};

/// Names registered by the Farkas-soundness layer. All live under the
/// `Clean.Farkas.*` namespace to avoid clashing with the prelude `Int`
/// (which is the standard Lean `ofNat`/`negSucc` integer, not a difference
/// pair).
pub mod names {
    // ── the Quot-free difference-pair Int ───────────────────────────────────
    /// `Clean.Farkas.Int : Type` — single ctor `mk (pos neg : Nat)`.
    pub const INT: &str = "Clean.Farkas.Int";
    /// `Clean.Farkas.Int.mk : Nat -> Nat -> Int`.
    pub const INT_MK: &str = "Clean.Farkas.Int.mk";
    /// `intPos : Int -> Nat` (the positive component).
    pub const INT_POS: &str = "Clean.Farkas.intPos";
    /// `intNeg : Int -> Nat` (the negative component).
    pub const INT_NEG: &str = "Clean.Farkas.intNeg";

    // ── Nat ops (own copies, recursion on 2nd arg, to control reduction) ────
    pub const NAT_ADD: &str = "Clean.Farkas.natAdd";
    pub const NAT_MUL: &str = "Clean.Farkas.natMul";
    pub const NAT_LE: &str = "Clean.Farkas.natLe";
    pub const NAT_LT: &str = "Clean.Farkas.natLt";
    pub const BAND: &str = "Clean.Farkas.band";

    // ── Int ops ─────────────────────────────────────────────────────────────
    pub const INT0: &str = "Clean.Farkas.int0";
    pub const INT_ADD: &str = "Clean.Farkas.intAdd";
    pub const INT_MUL: &str = "Clean.Farkas.intMul";
    pub const INT_LE: &str = "Clean.Farkas.intLe";
    pub const INT_LT: &str = "Clean.Farkas.intLt";
    pub const INT_EQ_ZERO: &str = "Clean.Farkas.intEqZero";
    pub const INT_IS_NEG: &str = "Clean.Farkas.intIsNeg";
    pub const INT_IS_NONNEG: &str = "Clean.Farkas.intIsNonneg";
    pub const INT_EQ: &str = "Clean.Farkas.intEq";

    // ── vector / checker ops ────────────────────────────────────────────────
    pub const HEAD_Z: &str = "Clean.Farkas.headZ";
    pub const TAIL_Z: &str = "Clean.Farkas.tailZ";
    pub const INT_LIST_ADD: &str = "Clean.Farkas.intListAdd";
    pub const INT_LIST_SCALE: &str = "Clean.Farkas.intListScale";
    pub const ALL_EQ_ZERO: &str = "Clean.Farkas.allEqZero";
    pub const COMBINE_COLUMNS: &str = "Clean.Farkas.combineColumns";
    pub const INT_DOT: &str = "Clean.Farkas.intDot";
    pub const ALL_NONNEG: &str = "Clean.Farkas.allNonneg";
    pub const FARKAS_CHECKS: &str = "Clean.Farkas.farkasChecks";

    // ── model semantics ─────────────────────────────────────────────────────
    /// `rowsHold : Rows -> Bounds -> (x : List Int) -> Prop` — every row
    /// constraint `intDot row x ≤ bound` holds (And-fold, bounds threaded).
    pub const ROWS_HOLD: &str = "Clean.Farkas.rowsHold";
    /// `Unsat rows bounds := (x : List Int) -> rowsHold rows bounds x -> False`
    /// — no integer assignment satisfies every row.
    pub const UNSAT: &str = "Clean.Farkas.Unsat";

    // ── the headline (target name; the PROVED arithmetic ladder toward it lives
    //    in `proof_names`) ─────────────────────────────────────────────────────
    /// `farkasChecks_sound : (rows)(bounds)(mults) ->`
    /// `Eq (farkasChecks rows bounds mults) true -> Unsat rows bounds`.
    pub const FARKAS_CHECKS_SOUND: &str = "Clean.Farkas.farkasChecks_sound";
}

// ── small shared Expr helpers ──────────────────────────────────────────────

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
fn false_c() -> Expr {
    Expr::const_str("False")
}
fn nat_zero() -> Expr {
    Expr::const_str("Nat.zero")
}
fn nat_succ(x: Expr) -> Expr {
    Expr::app(Expr::const_str("Nat.succ"), x)
}
fn int_ty() -> Expr {
    Expr::const_str(names::INT)
}
fn int_mk(p: Expr, q: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::INT_MK), [p, q])
}
fn int_pos(i: Expr) -> Expr {
    Expr::app(Expr::const_str(names::INT_POS), i)
}
fn int_neg(i: Expr) -> Expr {
    Expr::app(Expr::const_str(names::INT_NEG), i)
}
fn na(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::NAT_ADD), [x, y])
}
fn nm(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::NAT_MUL), [x, y])
}
fn nle(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::NAT_LE), [x, y])
}
fn band(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::BAND), [x, y])
}
fn iadd(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::INT_ADD), [x, y])
}
fn imul(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::INT_MUL), [x, y])
}
fn ile(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::INT_LE), [x, y])
}
fn int0() -> Expr {
    Expr::const_str(names::INT0)
}
fn list_int() -> Expr {
    // Int : Type 0 ⇒ List.{0} Int (clean's List.{u} : Type u → Type u).
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        int_ty(),
    )
}
fn list_list_int() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        list_int(),
    )
}
fn nil_int() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        int_ty(),
    )
}
fn cons_int(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [int_ty(), h, t],
    )
}
fn nil_list_int() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        list_int(),
    )
}
fn cons_list_int(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [list_int(), h, t],
    )
}
fn head_z(xs: Expr) -> Expr {
    Expr::app(Expr::const_str(names::HEAD_Z), xs)
}
fn tail_z(xs: Expr) -> Expr {
    Expr::app(Expr::const_str(names::TAIL_Z), xs)
}
fn int_dot(xs: Expr, ys: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::INT_DOT), [xs, ys])
}
fn nat_lit(k: u32) -> Expr {
    let mut e = nat_zero();
    for _ in 0..k {
        e = nat_succ(e);
    }
    e
}

/// `List.rec.{1,1}` into a `Sort 1` (`Type`) result `ret` over element type
/// `int_ty()` — used for `Int`-list folds whose result is `List Int`/`Int`/etc.
/// `nil_case`, `cons_case` (a `λ h t ih => …`), `major`.
fn list_int_rec_into_type(ret_motive: Expr, nil_case: Expr, cons_case: Expr, major: Expr) -> Expr {
    // motive returns Int / List Int : Type 0 = Sort 1 ⇒ motive level 1; element
    // type Int : Type 0 ⇒ List elem level 0. List.rec.{v, u} = .{1, 0}.
    let rec = Expr::const_(
        Name::from_string("List.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    Expr::apps(rec, [int_ty(), ret_motive, nil_case, cons_case, major])
}

impl Environment {
    /// Register the Farkas-soundness substrate (difference-pair `Int` + Nat/Int
    /// ops + checker `farkasChecks` + the model `rowsHold`/`Unsat`). Idempotent.
    /// The PROVED arithmetic lemmas are registered separately by
    /// [`Environment::init_farkas_proofs`]; the top-level bridge
    /// `farkasChecks_sound` is NOT registered here (or anywhere) — only its TYPE is
    /// available, via [`farkas_checks_sound_type`].
    ///
    /// # Errors
    /// Propagates any [`EnvError`] from declaration insertion / kernel checking.
    pub fn init_farkas_soundness(&mut self) -> Result<(), EnvError> {
        self.init_true_false()?;
        self.init_and()?;
        self.init_or()?;
        self.register_farkas_int_inductive()?;
        self.register_farkas_nat_ops()?;
        self.register_farkas_int_ops()?;
        self.register_farkas_vector_ops()?;
        self.register_farkas_checks()?;
        self.register_farkas_model()?;
        Ok(())
    }

    // ── §1 the difference-pair Int inductive ───────────────────────────────

    fn register_farkas_int_inductive(&mut self) -> Result<(), EnvError> {
        if self.get_inductive(&Name::from_string(names::INT)).is_some() {
            return Ok(());
        }
        // inductive Clean.Farkas.Int : Type where | mk (pos neg : Nat) : Int
        let int_decl_ty = Expr::type_();
        let mk_ty = {
            let mut b = EnvDeclBuilder::new();
            let (pid, _) = b.fresh_local(nat_ty());
            let (nid, _) = b.fresh_local(nat_ty());
            let r = int_ty();
            let r = b.mk_pi(nid, BinderInfo::Default, nat_ty(), r);
            let r = b.mk_pi(pid, BinderInfo::Default, nat_ty(), r);
            b.finish(r)
        };
        self.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(names::INT),
                type_: int_decl_ty,
                constructors: vec![Constructor {
                    name: Name::from_string(names::INT_MK),
                    type_: mk_ty,
                }],
            }],
        })?;

        // intPos i := Int.rec (motive := fun _ => Nat) (fun p n => p) i
        let int_to_nat = Expr::arrow(int_ty(), nat_ty());
        let int_rec = Expr::const_(
            Name::from_string(&format!("{}.rec", names::INT)),
            vec![Level::succ(Level::zero())],
        );
        let pos_val = {
            let mut b = EnvDeclBuilder::new();
            let (iid, i) = b.fresh_local(int_ty());
            let mk_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (pid, p) = c.fresh_local(nat_ty());
                let (nid, _n) = c.fresh_local(nat_ty());
                let r = c.mk_lam(nid, BinderInfo::Default, nat_ty(), p);
                c.finish_child(c.mk_lam(pid, BinderInfo::Default, nat_ty(), r))
            };
            let motive = Expr::lam(BinderInfo::Default, int_ty(), nat_ty());
            let body = Expr::apps(int_rec.clone(), [motive, mk_case, i]);
            b.finish(b.mk_lam(iid, BinderInfo::Default, int_ty(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(names::INT_POS),
            level_params: vec![],
            type_: int_to_nat.clone(),
            value: pos_val,
            is_reducible: true,
        })?;
        let neg_val = {
            let mut b = EnvDeclBuilder::new();
            let (iid, i) = b.fresh_local(int_ty());
            let mk_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (pid, _p) = c.fresh_local(nat_ty());
                let (nid, nn) = c.fresh_local(nat_ty());
                let r = c.mk_lam(nid, BinderInfo::Default, nat_ty(), nn);
                c.finish_child(c.mk_lam(pid, BinderInfo::Default, nat_ty(), r))
            };
            let motive = Expr::lam(BinderInfo::Default, int_ty(), nat_ty());
            let body = Expr::apps(int_rec, [motive, mk_case, i]);
            b.finish(b.mk_lam(iid, BinderInfo::Default, int_ty(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(names::INT_NEG),
            level_params: vec![],
            type_: int_to_nat,
            value: neg_val,
            is_reducible: true,
        })?;
        Ok(())
    }

    // ── §2 Nat ops (own copies; recurse on 2nd arg, matching m5) ───────────

    fn register_farkas_nat_ops(&mut self) -> Result<(), EnvError> {
        let nn_n = Expr::arrow(nat_ty(), Expr::arrow(nat_ty(), nat_ty()));
        let nn_b = Expr::arrow(nat_ty(), Expr::arrow(nat_ty(), bool_ty()));
        let nat_rec_t1 = || {
            Expr::const_(
                Name::from_string("Nat.rec"),
                vec![Level::succ(Level::zero())],
            )
        };

        // natAdd m n := Nat.rec (fun _ => Nat) m (fun _ ih => succ ih) n
        if self.get_const(&Name::from_string(names::NAT_ADD)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (mid, m) = b.fresh_local(nat_ty());
                let (nid, n) = b.fresh_local(nat_ty());
                let motive = Expr::lam(BinderInfo::Default, nat_ty(), nat_ty());
                let step = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (kid, _k) = c.fresh_local(nat_ty());
                    let (ihid, ih) = c.fresh_local(nat_ty());
                    let r = c.mk_lam(ihid, BinderInfo::Default, nat_ty(), nat_succ(ih));
                    c.finish_child(c.mk_lam(kid, BinderInfo::Default, nat_ty(), r))
                };
                let body = Expr::apps(nat_rec_t1(), [motive, m, step, n]);
                let e = b.mk_lam(nid, BinderInfo::Default, nat_ty(), body);
                b.finish(b.mk_lam(mid, BinderInfo::Default, nat_ty(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::NAT_ADD),
                level_params: vec![],
                type_: nn_n.clone(),
                value: val,
                is_reducible: true,
            })?;
        }

        // natMul m n := Nat.rec (fun _ => Nat) 0 (fun _ ih => natAdd ih m) n
        if self.get_const(&Name::from_string(names::NAT_MUL)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (mid, m) = b.fresh_local(nat_ty());
                let (nid, n) = b.fresh_local(nat_ty());
                let motive = Expr::lam(BinderInfo::Default, nat_ty(), nat_ty());
                let step = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (kid, _k) = c.fresh_local(nat_ty());
                    let (ihid, ih) = c.fresh_local(nat_ty());
                    let r = c.mk_lam(ihid, BinderInfo::Default, nat_ty(), na(ih, m.clone()));
                    c.finish_child(c.mk_lam(kid, BinderInfo::Default, nat_ty(), r))
                };
                let body = Expr::apps(nat_rec_t1(), [motive, nat_zero(), step, n]);
                let e = b.mk_lam(nid, BinderInfo::Default, nat_ty(), body);
                b.finish(b.mk_lam(mid, BinderInfo::Default, nat_ty(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::NAT_MUL),
                level_params: vec![],
                type_: nn_n,
                value: val,
                is_reducible: true,
            })?;
        }

        // natLe m n : Bool — structural double Nat.rec (m outer, n inner).
        //   le 0 _ = true ; le (S _) 0 = false ; le (S k)(S j) = le k j.
        if self.get_const(&Name::from_string(names::NAT_LE)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (mid, m) = b.fresh_local(nat_ty());
                let (nid, n) = b.fresh_local(nat_ty());
                let nat_to_bool = Expr::arrow(nat_ty(), bool_ty());
                // outer motive : fun _ => Nat -> Bool
                let motive = Expr::lam(BinderInfo::Default, nat_ty(), nat_to_bool.clone());
                // zero case : fun (_n : Nat) => true
                let zero_case = Expr::lam(BinderInfo::Default, nat_ty(), btrue());
                // succ case : fun (k : Nat)(ih : Nat -> Bool)(n : Nat) =>
                //   Nat.rec (fun _ => Bool) false (fun j _ => ih j) n
                let succ_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (kid, _k) = c.fresh_local(nat_ty());
                    let (ihid, ih) = c.fresh_local(nat_to_bool.clone());
                    let (n2id, n2) = c.fresh_local(nat_ty());
                    let inner_motive = Expr::lam(BinderInfo::Default, nat_ty(), bool_ty());
                    let inner_succ = {
                        let mut e = EnvDeclBuilder::child_of(&c);
                        let (jid, j) = e.fresh_local(nat_ty());
                        let (bid, _bb) = e.fresh_local(bool_ty());
                        let r = e.mk_lam(
                            bid,
                            BinderInfo::Default,
                            bool_ty(),
                            Expr::app(ih.clone(), j.clone()),
                        );
                        e.finish_child(e.mk_lam(jid, BinderInfo::Default, nat_ty(), r))
                    };
                    // inner Nat.rec returns Bool (Sort 1) ⇒ motive level 1.
                    let inner = Expr::apps(
                        nat_rec_t1(),
                        [inner_motive, bfalse(), inner_succ, n2.clone()],
                    );
                    let r = c.mk_lam(n2id, BinderInfo::Default, nat_ty(), inner);
                    let r = c.mk_lam(ihid, BinderInfo::Default, nat_to_bool.clone(), r);
                    c.finish_child(c.mk_lam(kid, BinderInfo::Default, nat_ty(), r))
                };
                let outer = Expr::apps(nat_rec_t1(), [motive, zero_case, succ_case, m]);
                let body = Expr::app(outer, n.clone());
                let e = b.mk_lam(nid, BinderInfo::Default, nat_ty(), body);
                b.finish(b.mk_lam(mid, BinderInfo::Default, nat_ty(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::NAT_LE),
                level_params: vec![],
                type_: nn_b.clone(),
                value: val,
                is_reducible: true,
            })?;
        }

        // natLt m n := natLe (succ m) n
        if self.get_const(&Name::from_string(names::NAT_LT)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (mid, m) = b.fresh_local(nat_ty());
                let (nid, n) = b.fresh_local(nat_ty());
                let body = nle(nat_succ(m), n);
                let e = b.mk_lam(nid, BinderInfo::Default, nat_ty(), body);
                b.finish(b.mk_lam(mid, BinderInfo::Default, nat_ty(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::NAT_LT),
                level_params: vec![],
                type_: nn_b,
                value: val,
                is_reducible: true,
            })?;
        }

        // band x y := Bool.rec (fun _ => Bool) false y x
        if self.get_const(&Name::from_string(names::BAND)).is_none() {
            let bb_b = Expr::arrow(bool_ty(), Expr::arrow(bool_ty(), bool_ty()));
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xid, x) = b.fresh_local(bool_ty());
                let (yid, y) = b.fresh_local(bool_ty());
                let bool_rec = Expr::const_(
                    Name::from_string("Bool.rec"),
                    vec![Level::succ(Level::zero())],
                );
                let motive = Expr::lam(BinderInfo::Default, bool_ty(), bool_ty());
                let body = Expr::apps(bool_rec, [motive, bfalse(), y.clone(), x.clone()]);
                let e = b.mk_lam(yid, BinderInfo::Default, bool_ty(), body);
                b.finish(b.mk_lam(xid, BinderInfo::Default, bool_ty(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::BAND),
                level_params: vec![],
                type_: bb_b,
                value: val,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    // ── §3 Int ops over difference pairs ───────────────────────────────────

    fn register_farkas_int_ops(&mut self) -> Result<(), EnvError> {
        let ii_i = Expr::arrow(int_ty(), Expr::arrow(int_ty(), int_ty()));
        let ii_b = Expr::arrow(int_ty(), Expr::arrow(int_ty(), bool_ty()));
        let i_b = Expr::arrow(int_ty(), bool_ty());

        // int0 := mk 0 0
        if self.get_const(&Name::from_string(names::INT0)).is_none() {
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::INT0),
                level_params: vec![],
                type_: int_ty(),
                value: int_mk(nat_zero(), nat_zero()),
                is_reducible: true,
            })?;
        }

        // intAdd a b := mk (a.pos + b.pos) (a.neg + b.neg)
        if self.get_const(&Name::from_string(names::INT_ADD)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (aid, a) = b.fresh_local(int_ty());
                let (bid, bb) = b.fresh_local(int_ty());
                let p = na(int_pos(a.clone()), int_pos(bb.clone()));
                let q = na(int_neg(a.clone()), int_neg(bb.clone()));
                let body = int_mk(p, q);
                let e = b.mk_lam(bid, BinderInfo::Default, int_ty(), body);
                b.finish(b.mk_lam(aid, BinderInfo::Default, int_ty(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::INT_ADD),
                level_params: vec![],
                type_: ii_i.clone(),
                value: val,
                is_reducible: true,
            })?;
        }

        // intMul a b := mk (a.pos*b.pos + a.neg*b.neg) (a.pos*b.neg + a.neg*b.pos)
        if self.get_const(&Name::from_string(names::INT_MUL)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (aid, a) = b.fresh_local(int_ty());
                let (bid, bb) = b.fresh_local(int_ty());
                let ap = || int_pos(a.clone());
                let an = || int_neg(a.clone());
                let bp = || int_pos(bb.clone());
                let bn = || int_neg(bb.clone());
                let p = na(nm(ap(), bp()), nm(an(), bn()));
                let q = na(nm(ap(), bn()), nm(an(), bp()));
                let body = int_mk(p, q);
                let e = b.mk_lam(bid, BinderInfo::Default, int_ty(), body);
                b.finish(b.mk_lam(aid, BinderInfo::Default, int_ty(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::INT_MUL),
                level_params: vec![],
                type_: ii_i,
                value: val,
                is_reducible: true,
            })?;
        }

        // intLe a b := natLe (a.pos + b.neg) (b.pos + a.neg)
        if self.get_const(&Name::from_string(names::INT_LE)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (aid, a) = b.fresh_local(int_ty());
                let (bid, bb) = b.fresh_local(int_ty());
                let lhs = na(int_pos(a.clone()), int_neg(bb.clone()));
                let rhs = na(int_pos(bb.clone()), int_neg(a.clone()));
                let body = nle(lhs, rhs);
                let e = b.mk_lam(bid, BinderInfo::Default, int_ty(), body);
                b.finish(b.mk_lam(aid, BinderInfo::Default, int_ty(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::INT_LE),
                level_params: vec![],
                type_: ii_b.clone(),
                value: val,
                is_reducible: true,
            })?;
        }

        // intLt a b := natLt (a.pos + b.neg) (b.pos + a.neg)
        if self.get_const(&Name::from_string(names::INT_LT)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (aid, a) = b.fresh_local(int_ty());
                let (bid, bb) = b.fresh_local(int_ty());
                let lhs = na(int_pos(a.clone()), int_neg(bb.clone()));
                let rhs = na(int_pos(bb.clone()), int_neg(a.clone()));
                let body = Expr::apps(Expr::const_str(names::NAT_LT), [lhs, rhs]);
                let e = b.mk_lam(bid, BinderInfo::Default, int_ty(), body);
                b.finish(b.mk_lam(aid, BinderInfo::Default, int_ty(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::INT_LT),
                level_params: vec![],
                type_: ii_b.clone(),
                value: val,
                is_reducible: true,
            })?;
        }

        // intEqZero i := band (natLe i.pos i.neg) (natLe i.neg i.pos)
        if self
            .get_const(&Name::from_string(names::INT_EQ_ZERO))
            .is_none()
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (iid, i) = b.fresh_local(int_ty());
                let body = band(
                    nle(int_pos(i.clone()), int_neg(i.clone())),
                    nle(int_neg(i.clone()), int_pos(i.clone())),
                );
                b.finish(b.mk_lam(iid, BinderInfo::Default, int_ty(), body))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::INT_EQ_ZERO),
                level_params: vec![],
                type_: i_b.clone(),
                value: val,
                is_reducible: true,
            })?;
        }

        // intIsNeg i := intLt i 0
        if self
            .get_const(&Name::from_string(names::INT_IS_NEG))
            .is_none()
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (iid, i) = b.fresh_local(int_ty());
                let body = Expr::apps(Expr::const_str(names::INT_LT), [i.clone(), int0()]);
                b.finish(b.mk_lam(iid, BinderInfo::Default, int_ty(), body))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::INT_IS_NEG),
                level_params: vec![],
                type_: i_b.clone(),
                value: val,
                is_reducible: true,
            })?;
        }

        // intIsNonneg i := natLe i.neg i.pos
        if self
            .get_const(&Name::from_string(names::INT_IS_NONNEG))
            .is_none()
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (iid, i) = b.fresh_local(int_ty());
                let body = nle(int_neg(i.clone()), int_pos(i.clone()));
                b.finish(b.mk_lam(iid, BinderInfo::Default, int_ty(), body))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::INT_IS_NONNEG),
                level_params: vec![],
                type_: i_b,
                value: val,
                is_reducible: true,
            })?;
        }

        // intEq a b := band (intLe a b) (intLe b a)
        if self.get_const(&Name::from_string(names::INT_EQ)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (aid, a) = b.fresh_local(int_ty());
                let (bid, bb) = b.fresh_local(int_ty());
                let body = band(ile(a.clone(), bb.clone()), ile(bb.clone(), a.clone()));
                let e = b.mk_lam(bid, BinderInfo::Default, int_ty(), body);
                b.finish(b.mk_lam(aid, BinderInfo::Default, int_ty(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::INT_EQ),
                level_params: vec![],
                type_: ii_b,
                value: val,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    // ── §4 vector ops: headZ/tailZ, intListAdd, intListScale, allEqZero,
    //        combineColumns, intDot, allNonneg ──────────────────────────────

    fn register_farkas_vector_ops(&mut self) -> Result<(), EnvError> {
        let li_li = Expr::arrow(list_int(), list_int());

        // headZ ys := List.rec int0 (fun h _ _ => h) ys   : List Int -> Int
        if self.get_const(&Name::from_string(names::HEAD_Z)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (ysid, ys) = b.fresh_local(list_int());
                let motive = Expr::lam(BinderInfo::Default, list_int(), int_ty());
                let cc = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hid, h) = c.fresh_local(int_ty());
                    let (tid, _t) = c.fresh_local(list_int());
                    let (ihid, _ih) = c.fresh_local(int_ty());
                    let r = c.mk_lam(ihid, BinderInfo::Default, int_ty(), h);
                    let r = c.mk_lam(tid, BinderInfo::Default, list_int(), r);
                    c.finish_child(c.mk_lam(hid, BinderInfo::Default, int_ty(), r))
                };
                let body = list_int_rec_into_type(motive, int0(), cc, ys);
                b.finish(b.mk_lam(ysid, BinderInfo::Default, list_int(), body))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::HEAD_Z),
                level_params: vec![],
                type_: Expr::arrow(list_int(), int_ty()),
                value: val,
                is_reducible: true,
            })?;
        }

        // tailZ ys := List.rec nil (fun _ t _ => t) ys
        if self.get_const(&Name::from_string(names::TAIL_Z)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (ysid, ys) = b.fresh_local(list_int());
                let motive = Expr::lam(BinderInfo::Default, list_int(), list_int());
                let cc = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hid, _h) = c.fresh_local(int_ty());
                    let (tid, t) = c.fresh_local(list_int());
                    let (ihid, _ih) = c.fresh_local(list_int());
                    let r = c.mk_lam(ihid, BinderInfo::Default, list_int(), t);
                    let r = c.mk_lam(tid, BinderInfo::Default, list_int(), r);
                    c.finish_child(c.mk_lam(hid, BinderInfo::Default, int_ty(), r))
                };
                let body = list_int_rec_into_type(motive, nil_int(), cc, ys);
                b.finish(b.mk_lam(ysid, BinderInfo::Default, list_int(), body))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::TAIL_Z),
                level_params: vec![],
                type_: Expr::arrow(list_int(), list_int()),
                value: val,
                is_reducible: true,
            })?;
        }

        // intListAdd xs ys := (List.rec (motive := fun _ => List Int -> List Int)
        //   (fun ys => ys)
        //   (fun x xs ihf => fun ys => cons (intAdd x (headZ ys)) (ihf (tailZ ys)))
        //   xs) ys
        if self
            .get_const(&Name::from_string(names::INT_LIST_ADD))
            .is_none()
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xsid, xs) = b.fresh_local(list_int());
                let (ysid, ys) = b.fresh_local(list_int());
                let motive = Expr::lam(BinderInfo::Default, list_int(), li_li.clone());
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ys2id, ys2) = c.fresh_local(list_int());
                    c.finish_child(c.mk_lam(ys2id, BinderInfo::Default, list_int(), ys2))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (xid, x) = c.fresh_local(int_ty());
                    let (xsid2, _xs2) = c.fresh_local(list_int());
                    let (ihfid, ihf) = c.fresh_local(li_li.clone());
                    let (ys2id, ys2) = c.fresh_local(list_int());
                    let head = iadd(x, head_z(ys2.clone()));
                    let rest = Expr::app(ihf, tail_z(ys2.clone()));
                    let body = cons_int(head, rest);
                    let r = c.mk_lam(ys2id, BinderInfo::Default, list_int(), body);
                    let r = c.mk_lam(ihfid, BinderInfo::Default, li_li.clone(), r);
                    let r = c.mk_lam(xsid2, BinderInfo::Default, list_int(), r);
                    c.finish_child(c.mk_lam(xid, BinderInfo::Default, int_ty(), r))
                };
                let folded = list_int_rec_into_type(motive, nil_case, cons_case, xs);
                let applied = Expr::app(folded, ys.clone());
                let e = b.mk_lam(ysid, BinderInfo::Default, list_int(), applied);
                b.finish(b.mk_lam(xsid, BinderInfo::Default, list_int(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::INT_LIST_ADD),
                level_params: vec![],
                type_: Expr::arrow(list_int(), Expr::arrow(list_int(), list_int())),
                value: val,
                is_reducible: true,
            })?;
        }

        // intListScale s xs := List.rec nil (fun h _ ih => cons (intMul s h) ih) xs
        if self
            .get_const(&Name::from_string(names::INT_LIST_SCALE))
            .is_none()
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (sid, s) = b.fresh_local(int_ty());
                let (xsid, xs) = b.fresh_local(list_int());
                let motive = Expr::lam(BinderInfo::Default, list_int(), list_int());
                let cc = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hid, h) = c.fresh_local(int_ty());
                    let (tid, _t) = c.fresh_local(list_int());
                    let (ihid, ih) = c.fresh_local(list_int());
                    let body = cons_int(imul(s.clone(), h.clone()), ih.clone());
                    let r = c.mk_lam(ihid, BinderInfo::Default, list_int(), body);
                    let r = c.mk_lam(tid, BinderInfo::Default, list_int(), r);
                    c.finish_child(c.mk_lam(hid, BinderInfo::Default, int_ty(), r))
                };
                let body = list_int_rec_into_type(motive, nil_int(), cc, xs);
                let e = b.mk_lam(xsid, BinderInfo::Default, list_int(), body);
                b.finish(b.mk_lam(sid, BinderInfo::Default, int_ty(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::INT_LIST_SCALE),
                level_params: vec![],
                type_: Expr::arrow(int_ty(), Expr::arrow(list_int(), list_int())),
                value: val,
                is_reducible: true,
            })?;
        }

        // allEqZero xs := List.rec true (fun h _ ih => band (intEqZero h) ih) xs
        if self
            .get_const(&Name::from_string(names::ALL_EQ_ZERO))
            .is_none()
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xsid, xs) = b.fresh_local(list_int());
                let motive = Expr::lam(BinderInfo::Default, list_int(), bool_ty());
                let cc = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hid, h) = c.fresh_local(int_ty());
                    let (tid, _t) = c.fresh_local(list_int());
                    let (ihid, ih) = c.fresh_local(bool_ty());
                    let body = band(
                        Expr::app(Expr::const_str(names::INT_EQ_ZERO), h.clone()),
                        ih.clone(),
                    );
                    let r = c.mk_lam(ihid, BinderInfo::Default, bool_ty(), body);
                    let r = c.mk_lam(tid, BinderInfo::Default, list_int(), r);
                    c.finish_child(c.mk_lam(hid, BinderInfo::Default, int_ty(), r))
                };
                let body = list_int_rec_into_type(motive, btrue(), cc, xs);
                b.finish(b.mk_lam(xsid, BinderInfo::Default, list_int(), body))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::ALL_EQ_ZERO),
                level_params: vec![],
                type_: Expr::arrow(list_int(), bool_ty()),
                value: val,
                is_reducible: true,
            })?;
        }

        // allNonneg xs := List.rec true (fun h _ ih => band (intIsNonneg h) ih) xs
        if self
            .get_const(&Name::from_string(names::ALL_NONNEG))
            .is_none()
        {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xsid, xs) = b.fresh_local(list_int());
                let motive = Expr::lam(BinderInfo::Default, list_int(), bool_ty());
                let cc = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hid, h) = c.fresh_local(int_ty());
                    let (tid, _t) = c.fresh_local(list_int());
                    let (ihid, ih) = c.fresh_local(bool_ty());
                    let body = band(
                        Expr::app(Expr::const_str(names::INT_IS_NONNEG), h.clone()),
                        ih.clone(),
                    );
                    let r = c.mk_lam(ihid, BinderInfo::Default, bool_ty(), body);
                    let r = c.mk_lam(tid, BinderInfo::Default, list_int(), r);
                    c.finish_child(c.mk_lam(hid, BinderInfo::Default, int_ty(), r))
                };
                let body = list_int_rec_into_type(motive, btrue(), cc, xs);
                b.finish(b.mk_lam(xsid, BinderInfo::Default, list_int(), body))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::ALL_NONNEG),
                level_params: vec![],
                type_: Expr::arrow(list_int(), bool_ty()),
                value: val,
                is_reducible: true,
            })?;
        }

        // intDot xs ys := (List.rec (motive := fun _ => List Int -> Int)
        //   (fun _ => int0)
        //   (fun x xs ihf => fun ys => intAdd (intMul x (headZ ys)) (ihf (tailZ ys)))
        //   xs) ys
        if self.get_const(&Name::from_string(names::INT_DOT)).is_none() {
            let ys_to_int = Expr::arrow(list_int(), int_ty());
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xsid, xs) = b.fresh_local(list_int());
                let (ysid, ys) = b.fresh_local(list_int());
                let motive = Expr::lam(BinderInfo::Default, list_int(), ys_to_int.clone());
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ys2id, _ys2) = c.fresh_local(list_int());
                    c.finish_child(c.mk_lam(ys2id, BinderInfo::Default, list_int(), int0()))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (xid, x) = c.fresh_local(int_ty());
                    let (xsid2, _xs2) = c.fresh_local(list_int());
                    let (ihfid, ihf) = c.fresh_local(ys_to_int.clone());
                    let (ys2id, ys2) = c.fresh_local(list_int());
                    let prod = imul(x, head_z(ys2.clone()));
                    let rest = Expr::app(ihf, tail_z(ys2.clone()));
                    let body = iadd(prod, rest);
                    let r = c.mk_lam(ys2id, BinderInfo::Default, list_int(), body);
                    let r = c.mk_lam(ihfid, BinderInfo::Default, ys_to_int.clone(), r);
                    let r = c.mk_lam(xsid2, BinderInfo::Default, list_int(), r);
                    c.finish_child(c.mk_lam(xid, BinderInfo::Default, int_ty(), r))
                };
                let folded = list_int_rec_into_type(motive, nil_case, cons_case, xs);
                let applied = Expr::app(folded, ys.clone());
                let e = b.mk_lam(ysid, BinderInfo::Default, list_int(), applied);
                b.finish(b.mk_lam(xsid, BinderInfo::Default, list_int(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::INT_DOT),
                level_params: vec![],
                type_: Expr::arrow(list_int(), Expr::arrow(list_int(), int_ty())),
                value: val,
                is_reducible: true,
            })?;
        }

        // combineColumns rows mults := (List.rec
        //   (motive := fun _ => List Int -> List Int)
        //   (fun _ => nil)
        //   (fun row rows ihf => fun ms =>
        //      intListAdd (intListScale (headZ ms) row) (ihf (tailZ ms)))
        //   rows) mults
        if self
            .get_const(&Name::from_string(names::COMBINE_COLUMNS))
            .is_none()
        {
            let ms_to_li = Expr::arrow(list_int(), list_int());
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (rowsid, rows) = b.fresh_local(list_list_int());
                let (multsid, mults) = b.fresh_local(list_int());
                let motive = Expr::lam(BinderInfo::Default, list_list_int(), ms_to_li.clone());
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (msid, _ms) = c.fresh_local(list_int());
                    c.finish_child(c.mk_lam(msid, BinderInfo::Default, list_int(), nil_int()))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (rowid, row) = c.fresh_local(list_int());
                    let (rowsid2, _rows2) = c.fresh_local(list_list_int());
                    let (ihfid, ihf) = c.fresh_local(ms_to_li.clone());
                    let (msid, ms) = c.fresh_local(list_int());
                    let scaled = Expr::apps(
                        Expr::const_str(names::INT_LIST_SCALE),
                        [head_z(ms.clone()), row.clone()],
                    );
                    let rest = Expr::app(ihf, tail_z(ms.clone()));
                    let body = Expr::apps(Expr::const_str(names::INT_LIST_ADD), [scaled, rest]);
                    let r = c.mk_lam(msid, BinderInfo::Default, list_int(), body);
                    let r = c.mk_lam(ihfid, BinderInfo::Default, ms_to_li.clone(), r);
                    let r = c.mk_lam(rowsid2, BinderInfo::Default, list_list_int(), r);
                    c.finish_child(c.mk_lam(rowid, BinderInfo::Default, list_int(), r))
                };
                // List.rec over List (List Int): element type List Int : Type 0 ⇒
                // elem level 0; motive returns List Int -> List Int : Sort 1 ⇒ level 1.
                let rec = Expr::const_(
                    Name::from_string("List.rec"),
                    vec![Level::succ(Level::zero()), Level::zero()],
                );
                let folded = Expr::apps(rec, [list_int(), motive, nil_case, cons_case, rows]);
                let applied = Expr::app(folded, mults.clone());
                let e = b.mk_lam(multsid, BinderInfo::Default, list_int(), applied);
                b.finish(b.mk_lam(rowsid, BinderInfo::Default, list_list_int(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::COMBINE_COLUMNS),
                level_params: vec![],
                type_: Expr::arrow(list_list_int(), Expr::arrow(list_int(), list_int())),
                value: val,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    // ── §5 the farkasChecks checker ────────────────────────────────────────

    fn register_farkas_checks(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::FARKAS_CHECKS))
            .is_some()
        {
            return Ok(());
        }
        // farkasChecks rows bounds mults :=
        //   band (allNonneg mults)
        //   (band (allEqZero (combineColumns rows mults))
        //         (intIsNeg (intDot mults bounds)))
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (rowsid, rows) = b.fresh_local(list_list_int());
            let (boundsid, bounds) = b.fresh_local(list_int());
            let (multsid, mults) = b.fresh_local(list_int());
            let nonneg = Expr::app(Expr::const_str(names::ALL_NONNEG), mults.clone());
            let combo = Expr::apps(
                Expr::const_str(names::COMBINE_COLUMNS),
                [rows.clone(), mults.clone()],
            );
            let cols_zero = Expr::app(Expr::const_str(names::ALL_EQ_ZERO), combo);
            let dot = int_dot(mults.clone(), bounds.clone());
            let bound_neg = Expr::app(Expr::const_str(names::INT_IS_NEG), dot);
            let inner = band(cols_zero, bound_neg);
            let body = band(nonneg, inner);
            let e = b.mk_lam(multsid, BinderInfo::Default, list_int(), body);
            let e = b.mk_lam(boundsid, BinderInfo::Default, list_int(), e);
            b.finish(b.mk_lam(rowsid, BinderInfo::Default, list_list_int(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(names::FARKAS_CHECKS),
            level_params: vec![],
            type_: Expr::arrow(
                list_list_int(),
                Expr::arrow(list_int(), Expr::arrow(list_int(), bool_ty())),
            ),
            value: val,
            is_reducible: true,
        })
    }

    // ── §6 the model: rowsHold / Sat / Unsat ───────────────────────────────

    fn register_farkas_model(&mut self) -> Result<(), EnvError> {
        // rowsHold rows bounds x :=
        //   (List.rec (motive := fun _ => List Int -> Prop)
        //      (fun _ => True)
        //      (fun row rows ih => fun bs =>
        //         And (Eq Bool (intLe (intDot row x) (headZ bs)) true) (ih (tailZ bs)))
        //      rows) bounds
        if self
            .get_const(&Name::from_string(names::ROWS_HOLD))
            .is_none()
        {
            let _u1 = Level::succ(Level::zero());
            let bs_to_prop = Expr::arrow(list_int(), Expr::prop());
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (rowsid, rows) = b.fresh_local(list_list_int());
                let (boundsid, bounds) = b.fresh_local(list_int());
                let (xid, x) = b.fresh_local(list_int());
                let motive = Expr::lam(BinderInfo::Default, list_list_int(), bs_to_prop.clone());
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (bsid, _bs) = c.fresh_local(list_int());
                    c.finish_child(c.mk_lam(
                        bsid,
                        BinderInfo::Default,
                        list_int(),
                        Expr::const_str("True"),
                    ))
                };
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (rowid, row) = c.fresh_local(list_int());
                    let (rowsid2, _rows2) = c.fresh_local(list_list_int());
                    let (ihid, ih) = c.fresh_local(bs_to_prop.clone());
                    let (bsid, bs) = c.fresh_local(list_int());
                    let le = ile(int_dot(row.clone(), x.clone()), head_z(bs.clone()));
                    let eq_true = eq_bool_(le, btrue());
                    let rest = Expr::app(ih.clone(), tail_z(bs.clone()));
                    let body = and_(eq_true, rest);
                    let r = c.mk_lam(bsid, BinderInfo::Default, list_int(), body);
                    let r = c.mk_lam(ihid, BinderInfo::Default, bs_to_prop.clone(), r);
                    let r = c.mk_lam(rowsid2, BinderInfo::Default, list_list_int(), r);
                    c.finish_child(c.mk_lam(rowid, BinderInfo::Default, list_int(), r))
                };
                // The motive `fun _ => (List Int -> Prop)` returns a *type*
                // (`List Int -> Prop : Sort 1`), so the recursor motive level is 1;
                // element List Int : Type 0 ⇒ elem level 0. List.rec.{1, 0}.
                let rec = Expr::const_(
                    Name::from_string("List.rec"),
                    vec![Level::succ(Level::zero()), Level::zero()],
                );
                let folded = Expr::apps(rec, [list_int(), motive, nil_case, cons_case, rows]);
                let applied = Expr::app(folded, bounds.clone());
                let e = b.mk_lam(xid, BinderInfo::Default, list_int(), applied);
                let e = b.mk_lam(boundsid, BinderInfo::Default, list_int(), e);
                b.finish(b.mk_lam(rowsid, BinderInfo::Default, list_list_int(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::ROWS_HOLD),
                level_params: vec![],
                type_: Expr::arrow(
                    list_list_int(),
                    Expr::arrow(list_int(), Expr::arrow(list_int(), Expr::prop())),
                ),
                value: val,
                is_reducible: true,
            })?;
        }

        // Unsat rows bounds := (x : List Int) -> rowsHold rows bounds x -> False
        //   — the REAL semantic infeasibility: NO assignment x makes every row
        //   constraint hold. (A `Sat` "∀x hold" notion would be unsound — the
        //   genuine model quantifies x existentially, so its negation is this
        //   ∀x ¬hold form.)
        if self.get_const(&Name::from_string(names::UNSAT)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (rowsid, rows) = b.fresh_local(list_list_int());
                let (boundsid, bounds) = b.fresh_local(list_int());
                let inner = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (xid, x) = c.fresh_local(list_int());
                    let hold = Expr::apps(
                        Expr::const_str(names::ROWS_HOLD),
                        [rows.clone(), bounds.clone(), x.clone()],
                    );
                    let body = Expr::arrow(hold, false_c());
                    c.finish_child(c.mk_pi(xid, BinderInfo::Default, list_int(), body))
                };
                let e = b.mk_lam(boundsid, BinderInfo::Default, list_int(), inner);
                b.finish(b.mk_lam(rowsid, BinderInfo::Default, list_list_int(), e))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(names::UNSAT),
                level_params: vec![],
                type_: Expr::arrow(list_list_int(), Expr::arrow(list_int(), Expr::prop())),
                value: val,
                is_reducible: true,
            })?;
        }
        Ok(())
    }
}

/// Names registered by the PROVED arithmetic / soundness layer.
pub mod proof_names {
    /// `natAddZeroL : (n) -> natAdd 0 n = n`.
    pub const NAT_ADD_ZERO_L: &str = "Clean.Farkas.natAddZeroL";
    /// `natAddSuccL : (m n) -> natAdd (succ m) n = succ (natAdd m n)`.
    pub const NAT_ADD_SUCC_L: &str = "Clean.Farkas.natAddSuccL";
    /// `natAddComm : (m n) -> natAdd m n = natAdd n m`.
    pub const NAT_ADD_COMM: &str = "Clean.Farkas.natAddComm";
    /// `natAddAssoc : (m n k) -> natAdd (natAdd m n) k = natAdd m (natAdd n k)`.
    pub const NAT_ADD_ASSOC: &str = "Clean.Farkas.natAddAssoc";
    /// `natLeRefl : (n) -> natLe n n = true`.
    pub const NAT_LE_REFL: &str = "Clean.Farkas.natLeRefl";
    /// `natLeAddR : (c a b) -> natLe a b = true -> natLe (natAdd a c)(natAdd b c) = true`.
    pub const NAT_LE_ADD_R: &str = "Clean.Farkas.natLeAddR";
    /// `natLeTrans : (a b c) -> natLe a b = true -> natLe b c = true -> natLe a c = true`.
    pub const NAT_LE_TRANS: &str = "Clean.Farkas.natLeTrans";
    /// `natLeAddL : (c a b) -> natLe a b = true -> natLe (natAdd c a)(natAdd c b) = true`.
    pub const NAT_LE_ADD_L: &str = "Clean.Farkas.natLeAddL";
    /// `natLeAddBoth : (a b c d) -> natLe a b = true -> natLe c d = true ->`
    /// `natLe (natAdd a c)(natAdd b d) = true`.
    pub const NAT_LE_ADD_BOTH: &str = "Clean.Farkas.natLeAddBoth";
    /// `natAddReshuffle : (p q r s) -> (p+q)+(r+s) = (p+r)+(q+s)` (swap inner).
    pub const NAT_ADD_RESHUFFLE: &str = "Clean.Farkas.natAddReshuffle";
    /// `natAddReshuffle2 : (p q r s) -> (p+q)+(r+s) = (p+s)+(q+r)`.
    pub const NAT_ADD_RESHUFFLE2: &str = "Clean.Farkas.natAddReshuffle2";
    /// `natLeAddCancelR : (k a b) -> natLe (natAdd a k)(natAdd b k) = true ->`
    /// `natLe a b = true`.
    pub const NAT_LE_ADD_CANCEL_R: &str = "Clean.Farkas.natLeAddCancelR";
    /// `natLeContra : (a b) -> natLe a b = true -> natLe (succ b) a = true -> False`.
    pub const NAT_LE_CONTRA: &str = "Clean.Farkas.natLeContra";
    /// `leNegFalse : (d : Int) -> intLe int0 d = true -> intIsNeg d = true -> False`.
    pub const LE_NEG_FALSE: &str = "Clean.Farkas.leNegFalse";
    /// `intAddMono : (a b c d) -> intLe a b = true -> intLe c d = true ->`
    /// `intLe (intAdd a c)(intAdd b d) = true`.
    pub const INT_ADD_MONO: &str = "Clean.Farkas.intAddMono";
    /// `intLeTrans : (a b c) -> intLe a b = true -> intLe b c = true ->`
    /// `intLe a c = true`.
    pub const INT_LE_TRANS: &str = "Clean.Farkas.intLeTrans";
    /// `natLeMulMonoR : (c a b) -> natLe a b = true ->`
    /// `natLe (natMul a c)(natMul b c) = true`. Induction on `c`.
    pub const NAT_LE_MUL_MONO_R: &str = "Clean.Farkas.natLeMulMonoR";
    /// `m5UnsatConcrete : Unsat [[1],[-1]] [-1,-1]` — the concrete proved
    /// infeasibility for the m5 system `x ≤ -1 ∧ -x ≤ -1`. This is a genuine
    /// `Declaration::Theorem` (the parallel of `emptyClauseUnsat`).
    pub const M5_UNSAT_CONCRETE: &str = "Clean.Farkas.m5UnsatConcrete";

    // ── multiplicative tower toward farkasChecks_sound (STEP 2) ─────────────
    /// `natMulZeroL : (n) -> natMul 0 n = 0`. Induction on `n`.
    pub const NAT_MUL_ZERO_L: &str = "Clean.Farkas.natMulZeroL";
    /// `natMulSuccL : (m n) -> natMul (succ m) n = natAdd (natMul m n) n`.
    /// Induction on `n`.
    pub const NAT_MUL_SUCC_L: &str = "Clean.Farkas.natMulSuccL";
    /// `natMulComm : (m n) -> natMul m n = natMul n m`. Induction on `n`.
    pub const NAT_MUL_COMM: &str = "Clean.Farkas.natMulComm";
    /// `natMulDistribR : (a b c) -> natMul (natAdd a b) c =`
    /// `natAdd (natMul a c)(natMul b c)`. Induction on `c`.
    pub const NAT_MUL_DISTRIB_R: &str = "Clean.Farkas.natMulDistribR";

    // ── Int equational multiplicative/additive tower (STEP 3 structural) ─────
    /// `intEta : (i) -> Eq (Int.mk (intPos i)(intNeg i)) i`. Structure eta via `Int.rec`.
    pub const INT_ETA: &str = "Clean.Farkas.intEta";
    /// `intAddZeroL : (w) -> Eq (intAdd int0 w) w`. Componentwise `natAddZeroL` + `intEta`.
    pub const INT_ADD_ZERO_L: &str = "Clean.Farkas.intAddZeroL";
    /// `intAddAssoc : (a b c) -> Eq (intAdd (intAdd a b) c)(intAdd a (intAdd b c))`.
    pub const INT_ADD_ASSOC: &str = "Clean.Farkas.intAddAssoc";
    /// `intMulDistribR : (a b z) -> Eq (intMul (intAdd a b) z)`
    /// `(intAdd (intMul a z)(intMul b z))`. Componentwise `natMulDistribR` + reshuffle.
    pub const INT_MUL_DISTRIB_R: &str = "Clean.Farkas.intMulDistribR";
}

impl Environment {
    /// Register the PROVED arithmetic lemmas (the foundational additive/order
    /// tower over the diff-pair `Int`, up to `intLeTrans`/`intAddMono`/`leNegFalse`
    /// and the multiplicative base case `natLeMulMonoR`). Idempotent. Assumes
    /// [`Environment::init_farkas_soundness`] has run (or runs it). This does NOT
    /// register the top-level bridge `farkasChecks_sound` (it is not proved); see
    /// the module-level status note for the remaining obligation.
    ///
    /// # Errors
    /// Propagates any [`EnvError`] from declaration insertion / kernel checking.
    pub fn init_farkas_proofs(&mut self) -> Result<(), EnvError> {
        self.init_farkas_soundness()?;
        self.register_nat_add_zero_l()?;
        self.register_nat_add_succ_l()?;
        self.register_nat_add_comm()?;
        self.register_nat_add_assoc()?;
        self.register_nat_le_refl()?;
        self.register_nat_le_add_r()?;
        self.register_nat_le_trans()?;
        self.register_nat_le_add_l()?;
        self.register_nat_le_add_both()?;
        self.register_nat_add_reshuffle()?;
        self.register_nat_add_reshuffle2()?;
        self.register_nat_le_add_cancel_r()?;
        self.register_nat_le_contra()?;
        self.register_le_neg_false()?;
        self.register_int_add_mono()?;
        self.register_int_le_trans()?;
        self.register_nat_le_mul_mono_r()?;
        self.register_m5_unsat_concrete()?;
        Ok(())
    }

    /// `natAddReshuffle : (p q r s) -> Eq (natAdd (natAdd p q)(natAdd r s))`
    /// `(natAdd (natAdd p r)(natAdd q s))`. Pure comm/assoc chain.
    fn register_nat_add_reshuffle(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_ADD_RESHUFFLE))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_add_comm()?;
        self.register_nat_add_assoc()?;
        let assoc = |x: Expr, y: Expr, z: Expr| {
            Expr::apps(Expr::const_str(proof_names::NAT_ADD_ASSOC), [x, y, z])
        };
        let comm =
            |x: Expr, y: Expr| Expr::apps(Expr::const_str(proof_names::NAT_ADD_COMM), [x, y]);
        // congrArg (fun z => natAdd p z) h : natAdd p u = natAdd p v.
        // Built with a raw bvar lambda (p may be a parent fvar; a builder's
        // `finish` would reject it).
        let cong_add_l = |p: Expr, u: Expr, v: Expr, h: Expr| {
            let f = Expr::lam(BinderInfo::Default, nat_ty(), na(p.clone(), Expr::bvar(0)));
            congr_arg_nat(u, v, f, h)
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (pid, p) = b.fresh_local(nat_ty());
            let (qid, q) = b.fresh_local(nat_ty());
            let (rid, r) = b.fresh_local(nat_ty());
            let (sid, s) = b.fresh_local(nat_ty());
            let goal = eq_nat(
                na(na(p.clone(), q.clone()), na(r.clone(), s.clone())),
                na(na(p.clone(), r.clone()), na(q.clone(), s.clone())),
            );
            let e = b.mk_pi(sid, BinderInfo::Default, nat_ty(), goal);
            let e = b.mk_pi(rid, BinderInfo::Default, nat_ty(), e);
            let e = b.mk_pi(qid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_pi(pid, BinderInfo::Default, nat_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (pid, p) = b.fresh_local(nat_ty());
            let (qid, q) = b.fresh_local(nat_ty());
            let (rid, r) = b.fresh_local(nat_ty());
            let (sid, s) = b.fresh_local(nat_ty());
            // Let A=(p+q)+(r+s), and build A = (p+r)+(q+s).
            // step1 : (p+q)+(r+s) = p+(q+(r+s))           [assoc p q (r+s)]
            let qrs = na(q.clone(), na(r.clone(), s.clone()));
            let step1 = assoc(p.clone(), q.clone(), na(r.clone(), s.clone()));
            // inner : q+(r+s) = r+(q+s)
            //   i1 : q+(r+s) = (q+r)+s        [symm assoc q r s]
            let i1 = eq_symm_nat(
                na(na(q.clone(), r.clone()), s.clone()),
                na(q.clone(), na(r.clone(), s.clone())),
                assoc(q.clone(), r.clone(), s.clone()),
            );
            //   i2 : (q+r)+s = (r+q)+s        [congr (·+s) (comm q r)]
            let i2 = {
                let f = Expr::lam(BinderInfo::Default, nat_ty(), na(Expr::bvar(0), s.clone()));
                congr_arg_nat(
                    na(q.clone(), r.clone()),
                    na(r.clone(), q.clone()),
                    f,
                    comm(q.clone(), r.clone()),
                )
            };
            //   i3 : (r+q)+s = r+(q+s)        [assoc r q s]
            let i3 = assoc(r.clone(), q.clone(), s.clone());
            //   inner = trans (trans i1 i2) i3 : q+(r+s) = r+(q+s)
            let inner12 = eq_trans_nat(
                na(q.clone(), na(r.clone(), s.clone())),
                na(na(q.clone(), r.clone()), s.clone()),
                na(na(r.clone(), q.clone()), s.clone()),
                i1,
                i2,
            );
            let inner = eq_trans_nat(
                na(q.clone(), na(r.clone(), s.clone())),
                na(na(r.clone(), q.clone()), s.clone()),
                na(r.clone(), na(q.clone(), s.clone())),
                inner12,
                i3,
            );
            // step2 : p+(q+(r+s)) = p+(r+(q+s))   [congr (p+·) inner]
            let step2 = cong_add_l(
                p.clone(),
                qrs.clone(),
                na(r.clone(), na(q.clone(), s.clone())),
                inner,
            );
            // step3 : p+(r+(q+s)) = (p+r)+(q+s)   [symm assoc p r (q+s)]
            let step3 = eq_symm_nat(
                na(na(p.clone(), r.clone()), na(q.clone(), s.clone())),
                na(p.clone(), na(r.clone(), na(q.clone(), s.clone()))),
                assoc(p.clone(), r.clone(), na(q.clone(), s.clone())),
            );
            // chain: A --step1--> p+(q+(r+s)) --step2--> p+(r+(q+s)) --step3--> (p+r)+(q+s)
            let t1 = eq_trans_nat(
                na(na(p.clone(), q.clone()), na(r.clone(), s.clone())),
                na(p.clone(), qrs.clone()),
                na(p.clone(), na(r.clone(), na(q.clone(), s.clone()))),
                step1,
                step2,
            );
            let body = eq_trans_nat(
                na(na(p.clone(), q.clone()), na(r.clone(), s.clone())),
                na(p.clone(), na(r.clone(), na(q.clone(), s.clone()))),
                na(na(p.clone(), r.clone()), na(q.clone(), s.clone())),
                t1,
                step3,
            );
            let r4 = b.mk_lam(sid, BinderInfo::Default, nat_ty(), body);
            let r4 = b.mk_lam(rid, BinderInfo::Default, nat_ty(), r4);
            let r4 = b.mk_lam(qid, BinderInfo::Default, nat_ty(), r4);
            b.finish(b.mk_lam(pid, BinderInfo::Default, nat_ty(), r4))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_ADD_RESHUFFLE),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natAddReshuffle2 : (p q r s) -> Eq (natAdd (natAdd p q)(natAdd r s))`
    /// `(natAdd (natAdd p s)(natAdd q r))`. Via `natAddReshuffle` + inner `natAddComm`.
    fn register_nat_add_reshuffle2(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_ADD_RESHUFFLE2))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_add_reshuffle()?;
        self.register_nat_add_comm()?;
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (pid, p) = b.fresh_local(nat_ty());
            let (qid, q) = b.fresh_local(nat_ty());
            let (rid, r) = b.fresh_local(nat_ty());
            let (sid, s) = b.fresh_local(nat_ty());
            let goal = eq_nat(
                na(na(p.clone(), q.clone()), na(r.clone(), s.clone())),
                na(na(p.clone(), s.clone()), na(q.clone(), r.clone())),
            );
            let e = b.mk_pi(sid, BinderInfo::Default, nat_ty(), goal);
            let e = b.mk_pi(rid, BinderInfo::Default, nat_ty(), e);
            let e = b.mk_pi(qid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_pi(pid, BinderInfo::Default, nat_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (pid, p) = b.fresh_local(nat_ty());
            let (qid, q) = b.fresh_local(nat_ty());
            let (rid, r) = b.fresh_local(nat_ty());
            let (sid, s) = b.fresh_local(nat_ty());
            // step1 : (p+q)+(r+s) = (p+q)+(s+r)   [congr ((p+q)+·) (comm r s)]
            let comm_rs = Expr::apps(
                Expr::const_str(proof_names::NAT_ADD_COMM),
                [r.clone(), s.clone()],
            );
            let f = Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                na(na(p.clone(), q.clone()), Expr::bvar(0)),
            );
            let step1 = congr_arg_nat(
                na(r.clone(), s.clone()),
                na(s.clone(), r.clone()),
                f,
                comm_rs,
            );
            // step2 : (p+q)+(s+r) = (p+s)+(q+r)   [reshuffle p q s r]
            let step2 = Expr::apps(
                Expr::const_str(proof_names::NAT_ADD_RESHUFFLE),
                [p.clone(), q.clone(), s.clone(), r.clone()],
            );
            let body = eq_trans_nat(
                na(na(p.clone(), q.clone()), na(r.clone(), s.clone())),
                na(na(p.clone(), q.clone()), na(s.clone(), r.clone())),
                na(na(p.clone(), s.clone()), na(q.clone(), r.clone())),
                step1,
                step2,
            );
            let r4 = b.mk_lam(sid, BinderInfo::Default, nat_ty(), body);
            let r4 = b.mk_lam(rid, BinderInfo::Default, nat_ty(), r4);
            let r4 = b.mk_lam(qid, BinderInfo::Default, nat_ty(), r4);
            b.finish(b.mk_lam(pid, BinderInfo::Default, nat_ty(), r4))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_ADD_RESHUFFLE2),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natLeAddCancelR : (k a b) -> Eq (natLe (natAdd a k)(natAdd b k)) true ->`
    /// `Eq (natLe a b) true`. Induction on `k`.
    fn register_nat_le_add_cancel_r(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_LE_ADD_CANCEL_R))
            .is_some()
        {
            return Ok(());
        }
        // P k := ∀ a b, natLe (natAdd a k)(natAdd b k) = true → natLe a b = true.
        let p_of = |k: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (aid, a) = d.fresh_local(nat_ty());
            let (bid, b) = d.fresh_local(nat_ty());
            let hyp = eq_bool_(
                nle(na(a.clone(), k.clone()), na(b.clone(), k.clone())),
                btrue(),
            );
            let concl = eq_bool_(nle(a.clone(), b.clone()), btrue());
            let inner = Expr::arrow(hyp, concl);
            let inner = d.mk_pi(bid, BinderInfo::Default, nat_ty(), inner);
            d.finish_child(d.mk_pi(aid, BinderInfo::Default, nat_ty(), inner))
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (kid, k) = b.fresh_local(nat_ty());
            b.finish(b.mk_pi(kid, BinderInfo::Default, nat_ty(), p_of(&k, &b)))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (kid, k) = b.fresh_local(nat_ty());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(nat_ty());
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, nat_ty(), p_of(&m, &d)))
            };
            // k=0: fun a b (h : natLe (a+0)(b+0) = true) => h  (a+0 ≡ a, b+0 ≡ b).
            let zero_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (aid, a) = d.fresh_local(nat_ty());
                let (bid, bb) = d.fresh_local(nat_ty());
                let h_ty = eq_bool_(
                    nle(na(a.clone(), nat_zero()), na(bb.clone(), nat_zero())),
                    btrue(),
                );
                let (hid, h) = d.fresh_local(h_ty.clone());
                let r = d.mk_lam(hid, BinderInfo::Default, h_ty, h);
                let r = d.mk_lam(bid, BinderInfo::Default, nat_ty(), r);
                d.finish_child(d.mk_lam(aid, BinderInfo::Default, nat_ty(), r))
            };
            // k=S j: fun (j)(ihk : P j) => fun a b (h) =>
            //   natLe (a+(S j))(b+(S j)) ≡ natLe (S(a+j))(S(b+j)) ≡ natLe (a+j)(b+j) ;
            //   so h : natLe (a+j)(b+j) = true (defeq), ihk a b h : natLe a b = true.
            let succ_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (jid, j) = d.fresh_local(nat_ty());
                let (ihkid, ihk) = d.fresh_local(p_of(&j, &d));
                let inner = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (aid, a) = e.fresh_local(nat_ty());
                    let (bid, bb) = e.fresh_local(nat_ty());
                    let h_ty = eq_bool_(
                        nle(
                            na(a.clone(), nat_succ(j.clone())),
                            na(bb.clone(), nat_succ(j.clone())),
                        ),
                        btrue(),
                    );
                    let (hid, h) = e.fresh_local(h_ty.clone());
                    let body = Expr::apps(ihk.clone(), [a.clone(), bb.clone(), h]);
                    let r = e.mk_lam(hid, BinderInfo::Default, h_ty, body);
                    let r = e.mk_lam(bid, BinderInfo::Default, nat_ty(), r);
                    e.finish_child(e.mk_lam(aid, BinderInfo::Default, nat_ty(), r))
                };
                let r = d.mk_lam(ihkid, BinderInfo::Default, p_of(&j, &d), inner);
                d.finish_child(d.mk_lam(jid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let body = Expr::apps(nat_rec, [motive, zero_case, succ_case, k.clone()]);
            b.finish(b.mk_lam(kid, BinderInfo::Default, nat_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_LE_ADD_CANCEL_R),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natLeTrans : (a b c) -> natLe a b = true -> natLe b c = true ->`
    /// `natLe a c = true`. Triple `Nat.rec` (a, then b, then c).
    fn register_nat_le_trans(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_LE_TRANS))
            .is_some()
        {
            return Ok(());
        }
        // P a := ∀ b c, natLe a b = true → natLe b c = true → natLe a c = true.
        let p_of = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (bid, b) = d.fresh_local(nat_ty());
            let (cid, c) = d.fresh_local(nat_ty());
            let h1 = eq_bool_(nle(a.clone(), b.clone()), btrue());
            let h2 = eq_bool_(nle(b.clone(), c.clone()), btrue());
            let concl = eq_bool_(nle(a.clone(), c.clone()), btrue());
            let inner = Expr::arrow(h1, Expr::arrow(h2, concl));
            let inner = d.mk_pi(cid, BinderInfo::Default, nat_ty(), inner);
            d.finish_child(d.mk_pi(bid, BinderInfo::Default, nat_ty(), inner))
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(nat_ty());
            b.finish(b.mk_pi(aid, BinderInfo::Default, nat_ty(), p_of(&a, &b)))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(nat_ty());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(nat_ty());
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, nat_ty(), p_of(&m, &d)))
            };
            // a=0: fun b c (_h1)(_h2) => rfl  (natLe 0 c ≡ true).
            let zero_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (bid, bb) = d.fresh_local(nat_ty());
                let (cid, c) = d.fresh_local(nat_ty());
                let h1_ty = eq_bool_(nle(nat_zero(), bb.clone()), btrue());
                let (h1id, _h1) = d.fresh_local(h1_ty.clone());
                let h2_ty = eq_bool_(nle(bb.clone(), c.clone()), btrue());
                let (h2id, _h2) = d.fresh_local(h2_ty.clone());
                let r = d.mk_lam(h2id, BinderInfo::Default, h2_ty, eq_refl_bool(btrue()));
                let r = d.mk_lam(h1id, BinderInfo::Default, h1_ty, r);
                let r = d.mk_lam(cid, BinderInfo::Default, nat_ty(), r);
                d.finish_child(d.mk_lam(bid, BinderInfo::Default, nat_ty(), r))
            };
            // a=S a': fun (a')(iha : P a') => fun b c => Nat.rec on b.
            let succ_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (apid, ap) = d.fresh_local(nat_ty());
                let (ihaid, iha) = d.fresh_local(p_of(&ap, &d));
                let sa = nat_succ(ap.clone());
                // build: fun (b c : Nat) => (Nat.rec over b) ... applied
                let inner = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (bid, bb) = e.fresh_local(nat_ty());
                    let (cid, c) = e.fresh_local(nat_ty());
                    // motive over b : fun b => natLe (S a') b = true → natLe b c = true → natLe (S a') c = true
                    let b_motive = {
                        let mut f = EnvDeclBuilder::child_of(&e);
                        let (mid, m) = f.fresh_local(nat_ty());
                        let h1 = eq_bool_(nle(sa.clone(), m.clone()), btrue());
                        let h2 = eq_bool_(nle(m.clone(), c.clone()), btrue());
                        let concl = eq_bool_(nle(sa.clone(), c.clone()), btrue());
                        let body = Expr::arrow(h1, Expr::arrow(h2, concl));
                        f.finish_child(f.mk_lam(mid, BinderInfo::Default, nat_ty(), body))
                    };
                    // b=0: fun (h1 : natLe (S a') 0 = true)(_h2) => absurd.
                    let b_zero = {
                        let mut f = EnvDeclBuilder::child_of(&e);
                        let h1_ty = eq_bool_(nle(sa.clone(), nat_zero()), btrue());
                        let (h1id, h1) = f.fresh_local(h1_ty.clone());
                        let h2_ty = eq_bool_(nle(nat_zero(), c.clone()), btrue());
                        let (h2id, _h2) = f.fresh_local(h2_ty.clone());
                        let concl = eq_bool_(nle(sa.clone(), c.clone()), btrue());
                        let ff = tf_to_false(eq_symm_bool(bfalse(), btrue(), h1));
                        let body = false_elim_prop(concl, ff);
                        let r = f.mk_lam(h2id, BinderInfo::Default, h2_ty, body);
                        f.finish_child(f.mk_lam(h1id, BinderInfo::Default, h1_ty, r))
                    };
                    // b=S b': fun (b')(_ihb) => Nat.rec on c.
                    let b_succ = {
                        let mut f = EnvDeclBuilder::child_of(&e);
                        let (bpid, bp) = f.fresh_local(nat_ty());
                        let ihb_ty = {
                            let h1 = eq_bool_(nle(sa.clone(), bp.clone()), btrue());
                            let h2 = eq_bool_(nle(bp.clone(), c.clone()), btrue());
                            let concl = eq_bool_(nle(sa.clone(), c.clone()), btrue());
                            Expr::arrow(h1, Expr::arrow(h2, concl))
                        };
                        let (ihbid, _ihb) = f.fresh_local(ihb_ty.clone());
                        // now case on c via Nat.rec.
                        let sb = nat_succ(bp.clone());
                        // motive over c : fun c => natLe (S a')(S b') = true → natLe (S b') c = true → natLe (S a') c = true
                        let c_motive = {
                            let mut g = EnvDeclBuilder::child_of(&f);
                            let (mid, m) = g.fresh_local(nat_ty());
                            let h1 = eq_bool_(nle(sa.clone(), sb.clone()), btrue());
                            let h2 = eq_bool_(nle(sb.clone(), m.clone()), btrue());
                            let concl = eq_bool_(nle(sa.clone(), m.clone()), btrue());
                            let body = Expr::arrow(h1, Expr::arrow(h2, concl));
                            g.finish_child(g.mk_lam(mid, BinderInfo::Default, nat_ty(), body))
                        };
                        // c=0: fun (_h1)(h2 : natLe (S b') 0 = true) => absurd.
                        let c_zero = {
                            let mut g = EnvDeclBuilder::child_of(&f);
                            let h1_ty = eq_bool_(nle(sa.clone(), sb.clone()), btrue());
                            let (h1id, _h1) = g.fresh_local(h1_ty.clone());
                            let h2_ty = eq_bool_(nle(sb.clone(), nat_zero()), btrue());
                            let (h2id, h2) = g.fresh_local(h2_ty.clone());
                            let concl = eq_bool_(nle(sa.clone(), nat_zero()), btrue());
                            let ff = tf_to_false(eq_symm_bool(bfalse(), btrue(), h2));
                            let body = false_elim_prop(concl, ff);
                            let r = g.mk_lam(h2id, BinderInfo::Default, h2_ty, body);
                            g.finish_child(g.mk_lam(h1id, BinderInfo::Default, h1_ty, r))
                        };
                        // c=S c': fun (c')(_ihc)(h1)(h2) => iha b' c' h1 h2.
                        //   natLe (S a')(S b') ≡ natLe a' b' ; natLe (S b')(S c') ≡ natLe b' c' ;
                        //   goal natLe (S a')(S c') ≡ natLe a' c'. iha b' c' h1 h2.
                        let c_succ = {
                            let mut g = EnvDeclBuilder::child_of(&f);
                            let (cpid, cp) = g.fresh_local(nat_ty());
                            let scp = nat_succ(cp.clone());
                            let ihc_ty = {
                                let h1 = eq_bool_(nle(sa.clone(), sb.clone()), btrue());
                                let h2 = eq_bool_(nle(sb.clone(), cp.clone()), btrue());
                                let concl = eq_bool_(nle(sa.clone(), cp.clone()), btrue());
                                Expr::arrow(h1, Expr::arrow(h2, concl))
                            };
                            let (ihcid, _ihc) = g.fresh_local(ihc_ty.clone());
                            let h1_ty = eq_bool_(nle(sa.clone(), sb.clone()), btrue());
                            let (h1id, h1) = g.fresh_local(h1_ty.clone());
                            let h2_ty = eq_bool_(nle(sb.clone(), scp.clone()), btrue());
                            let (h2id, h2) = g.fresh_local(h2_ty.clone());
                            let body = Expr::apps(iha.clone(), [bp.clone(), cp.clone(), h1, h2]);
                            let r = g.mk_lam(h2id, BinderInfo::Default, h2_ty, body);
                            let r = g.mk_lam(h1id, BinderInfo::Default, h1_ty, r);
                            let r = g.mk_lam(ihcid, BinderInfo::Default, ihc_ty, r);
                            g.finish_child(g.mk_lam(cpid, BinderInfo::Default, nat_ty(), r))
                        };
                        let nat_rec =
                            Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
                        let cfold = Expr::apps(nat_rec, [c_motive, c_zero, c_succ, c.clone()]);
                        let r = f.mk_lam(ihbid, BinderInfo::Default, ihb_ty, cfold);
                        f.finish_child(f.mk_lam(bpid, BinderInfo::Default, nat_ty(), r))
                    };
                    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
                    let bfold = Expr::apps(nat_rec, [b_motive, b_zero, b_succ, bb.clone()]);
                    let r = e.mk_lam(cid, BinderInfo::Default, nat_ty(), bfold);
                    e.finish_child(e.mk_lam(bid, BinderInfo::Default, nat_ty(), r))
                };
                let r = d.mk_lam(ihaid, BinderInfo::Default, p_of(&ap, &d), inner);
                d.finish_child(d.mk_lam(apid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let body = Expr::apps(nat_rec, [motive, zero_case, succ_case, a.clone()]);
            b.finish(b.mk_lam(aid, BinderInfo::Default, nat_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_LE_TRANS),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natLeAddL : (c a b) -> natLe a b = true -> natLe (natAdd c a)(natAdd c b)`
    /// `= true`. Derived from `natLeAddR` via `natAddComm`.
    fn register_nat_le_add_l(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_LE_ADD_L))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_le_add_r()?;
        self.register_nat_add_comm()?;
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (cid, c) = b.fresh_local(nat_ty());
            let (aid, a) = b.fresh_local(nat_ty());
            let (bid, bb) = b.fresh_local(nat_ty());
            let hyp = eq_bool_(nle(a.clone(), bb.clone()), btrue());
            let concl = eq_bool_(
                nle(na(c.clone(), a.clone()), na(c.clone(), bb.clone())),
                btrue(),
            );
            let inner = Expr::arrow(hyp, concl);
            let e = b.mk_pi(bid, BinderInfo::Default, nat_ty(), inner);
            let e = b.mk_pi(aid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_pi(cid, BinderInfo::Default, nat_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (cid, c) = b.fresh_local(nat_ty());
            let (aid, a) = b.fresh_local(nat_ty());
            let (bid, bb) = b.fresh_local(nat_ty());
            let hyp_ty = eq_bool_(nle(a.clone(), bb.clone()), btrue());
            let (hid, h) = b.fresh_local(hyp_ty.clone());
            // r1 : natLe (natAdd a c)(natAdd b c) = true
            let r1 = Expr::apps(
                Expr::const_str(proof_names::NAT_LE_ADD_R),
                [c.clone(), a.clone(), bb.clone(), h],
            );
            // rewrite natAdd a c ↦ natAdd c a and natAdd b c ↦ natAdd c b via natAddComm.
            //   motive1 (z) := natLe z (natAdd b c) = true, subst along
            //   natAddComm a c : natAdd a c = natAdd c a.
            let comm_ac = Expr::apps(
                Expr::const_str(proof_names::NAT_ADD_COMM),
                [a.clone(), c.clone()],
            );
            let motive1 = {
                let inner = eq_bool_(nle(Expr::bvar(0), na(bb.clone(), c.clone())), btrue());
                Expr::lam(BinderInfo::Default, nat_ty(), inner)
            };
            let r2 = eq_subst_nat(
                motive1,
                na(a.clone(), c.clone()),
                na(c.clone(), a.clone()),
                comm_ac,
                r1,
            );
            // r2 : natLe (natAdd c a)(natAdd b c) = true. Now rewrite natAdd b c ↦ natAdd c b.
            let comm_bc = Expr::apps(
                Expr::const_str(proof_names::NAT_ADD_COMM),
                [bb.clone(), c.clone()],
            );
            let motive2 = {
                let inner = eq_bool_(nle(na(c.clone(), a.clone()), Expr::bvar(0)), btrue());
                Expr::lam(BinderInfo::Default, nat_ty(), inner)
            };
            let r3 = eq_subst_nat(
                motive2,
                na(bb.clone(), c.clone()),
                na(c.clone(), bb.clone()),
                comm_bc,
                r2,
            );
            let r = b.mk_lam(hid, BinderInfo::Default, hyp_ty, r3);
            let r = b.mk_lam(bid, BinderInfo::Default, nat_ty(), r);
            let r = b.mk_lam(aid, BinderInfo::Default, nat_ty(), r);
            b.finish(b.mk_lam(cid, BinderInfo::Default, nat_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_LE_ADD_L),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natLeAddBoth : (a b c d) -> natLe a b = true -> natLe c d = true ->`
    /// `natLe (natAdd a c)(natAdd b d) = true`. From `natLeAddR`/`natLeAddL` +
    /// `natLeTrans` through the midpoint `natAdd b c`.
    fn register_nat_le_add_both(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_LE_ADD_BOTH))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_le_add_r()?;
        self.register_nat_le_add_l()?;
        self.register_nat_le_trans()?;
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(nat_ty());
            let (bid, bb) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(nat_ty());
            let (did, dd) = b.fresh_local(nat_ty());
            let h1 = eq_bool_(nle(a.clone(), bb.clone()), btrue());
            let h2 = eq_bool_(nle(c.clone(), dd.clone()), btrue());
            let concl = eq_bool_(
                nle(na(a.clone(), c.clone()), na(bb.clone(), dd.clone())),
                btrue(),
            );
            let inner = Expr::arrow(h1, Expr::arrow(h2, concl));
            let e = b.mk_pi(did, BinderInfo::Default, nat_ty(), inner);
            let e = b.mk_pi(cid, BinderInfo::Default, nat_ty(), e);
            let e = b.mk_pi(bid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_pi(aid, BinderInfo::Default, nat_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(nat_ty());
            let (bid, bb) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(nat_ty());
            let (did, dd) = b.fresh_local(nat_ty());
            let h1_ty = eq_bool_(nle(a.clone(), bb.clone()), btrue());
            let (h1id, h1) = b.fresh_local(h1_ty.clone());
            let h2_ty = eq_bool_(nle(c.clone(), dd.clone()), btrue());
            let (h2id, h2) = b.fresh_local(h2_ty.clone());
            // step1 : natLe (natAdd a c)(natAdd b c) = true  (natLeAddR c a b h1)
            let step1 = Expr::apps(
                Expr::const_str(proof_names::NAT_LE_ADD_R),
                [c.clone(), a.clone(), bb.clone(), h1],
            );
            // step2 : natLe (natAdd b c)(natAdd b d) = true  (natLeAddL b c d h2)
            let step2 = Expr::apps(
                Expr::const_str(proof_names::NAT_LE_ADD_L),
                [bb.clone(), c.clone(), dd.clone(), h2],
            );
            // natLeTrans (natAdd a c)(natAdd b c)(natAdd b d) step1 step2
            let body = Expr::apps(
                Expr::const_str(proof_names::NAT_LE_TRANS),
                [
                    na(a.clone(), c.clone()),
                    na(bb.clone(), c.clone()),
                    na(bb.clone(), dd.clone()),
                    step1,
                    step2,
                ],
            );
            let r = b.mk_lam(h2id, BinderInfo::Default, h2_ty, body);
            let r = b.mk_lam(h1id, BinderInfo::Default, h1_ty, r);
            let r = b.mk_lam(did, BinderInfo::Default, nat_ty(), r);
            let r = b.mk_lam(cid, BinderInfo::Default, nat_ty(), r);
            let r = b.mk_lam(bid, BinderInfo::Default, nat_ty(), r);
            b.finish(b.mk_lam(aid, BinderInfo::Default, nat_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_LE_ADD_BOTH),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natLeRefl : (n : Nat) -> Eq (natLe n n) true`. Induction on `n`
    /// (`natLe 0 0 ≡ true`; `natLe (succ k)(succ k) ≡ natLe k k`).
    fn register_nat_le_refl(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_LE_REFL))
            .is_some()
        {
            return Ok(());
        }
        let mk_goal = |n: &Expr| eq_bool_(nle(n.clone(), n.clone()), btrue());
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (nid, n) = b.fresh_local(nat_ty());
            b.finish(b.mk_pi(nid, BinderInfo::Default, nat_ty(), mk_goal(&n)))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (nid, n) = b.fresh_local(nat_ty());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(nat_ty());
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, nat_ty(), mk_goal(&m)))
            };
            // zero: natLe 0 0 ≡ true. rfl : true = true.
            let zero_case = eq_refl_bool(btrue());
            // succ: fun (k)(ih : natLe k k = true) => ih  (natLe (S k)(S k) ≡ natLe k k).
            let succ_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (kid, k) = c.fresh_local(nat_ty());
                let ih_ty = mk_goal(&k);
                let (ihid, ih) = c.fresh_local(ih_ty.clone());
                let r = c.mk_lam(ihid, BinderInfo::Default, ih_ty, ih);
                c.finish_child(c.mk_lam(kid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let body = Expr::apps(nat_rec, [motive, zero_case, succ_case, n.clone()]);
            b.finish(b.mk_lam(nid, BinderInfo::Default, nat_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_LE_REFL),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natLeAddR : (c a b : Nat) -> Eq (natLe a b) true ->`
    /// `Eq (natLe (natAdd a c)(natAdd b c)) true`. Induction on `c`.
    fn register_nat_le_add_r(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_LE_ADD_R))
            .is_some()
        {
            return Ok(());
        }
        // P c := ∀ a b, natLe a b = true → natLe (natAdd a c)(natAdd b c) = true.
        let p_of = |c: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (aid, a) = d.fresh_local(nat_ty());
            let (bid, b) = d.fresh_local(nat_ty());
            let hyp = eq_bool_(nle(a.clone(), b.clone()), btrue());
            let concl = eq_bool_(
                nle(na(a.clone(), c.clone()), na(b.clone(), c.clone())),
                btrue(),
            );
            let inner = Expr::arrow(hyp, concl);
            let inner = d.mk_pi(bid, BinderInfo::Default, nat_ty(), inner);
            d.finish_child(d.mk_pi(aid, BinderInfo::Default, nat_ty(), inner))
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (cid, c) = b.fresh_local(nat_ty());
            b.finish(b.mk_pi(cid, BinderInfo::Default, nat_ty(), p_of(&c, &b)))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (cid, c) = b.fresh_local(nat_ty());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(nat_ty());
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, nat_ty(), p_of(&m, &d)))
            };
            // c=0: fun a b (h : natLe a b = true) => h
            //   natAdd a 0 ≡ a, natAdd b 0 ≡ b ⇒ goal ≡ hyp.
            let zero_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (aid, a) = d.fresh_local(nat_ty());
                let (bid, bb) = d.fresh_local(nat_ty());
                let h_ty = eq_bool_(nle(a.clone(), bb.clone()), btrue());
                let (hid, h) = d.fresh_local(h_ty.clone());
                let r = d.mk_lam(hid, BinderInfo::Default, h_ty, h);
                let r = d.mk_lam(bid, BinderInfo::Default, nat_ty(), r);
                d.finish_child(d.mk_lam(aid, BinderInfo::Default, nat_ty(), r))
            };
            // c=S j: fun (j)(ihc : P j) => fun a b (h) =>
            //   natAdd a (S j) ≡ succ (natAdd a j), natAdd b (S j) ≡ succ (natAdd b j) ;
            //   natLe (succ _)(succ _) ≡ natLe (natAdd a j)(natAdd b j) ; = ihc a b h.
            let succ_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (jid, j) = d.fresh_local(nat_ty());
                let (ihcid, ihc) = d.fresh_local(p_of(&j, &d));
                let inner = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (aid, a) = e.fresh_local(nat_ty());
                    let (bid, bb) = e.fresh_local(nat_ty());
                    let h_ty = eq_bool_(nle(a.clone(), bb.clone()), btrue());
                    let (hid, h) = e.fresh_local(h_ty.clone());
                    let body = Expr::apps(ihc.clone(), [a.clone(), bb.clone(), h]);
                    let r = e.mk_lam(hid, BinderInfo::Default, h_ty, body);
                    let r = e.mk_lam(bid, BinderInfo::Default, nat_ty(), r);
                    e.finish_child(e.mk_lam(aid, BinderInfo::Default, nat_ty(), r))
                };
                let r = d.mk_lam(ihcid, BinderInfo::Default, p_of(&j, &d), inner);
                d.finish_child(d.mk_lam(jid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let body = Expr::apps(nat_rec, [motive, zero_case, succ_case, c.clone()]);
            b.finish(b.mk_lam(cid, BinderInfo::Default, nat_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_LE_ADD_R),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── Nat additive bedrock (induction on the recursion variable) ─────────

    /// `natAddZeroL : (n : Nat) -> Eq (natAdd 0 n) n`. Induction on `n`
    /// (`natAdd` recurses on its 2nd arg, so `natAdd 0 0 ≡ 0` and
    /// `natAdd 0 (succ k) ≡ succ (natAdd 0 k)`).
    fn register_nat_add_zero_l(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_ADD_ZERO_L))
            .is_some()
        {
            return Ok(());
        }
        let mk_goal = |n: &Expr| eq_nat(na(nat_zero(), n.clone()), n.clone());
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (nid, n) = b.fresh_local(nat_ty());
            b.finish(b.mk_pi(nid, BinderInfo::Default, nat_ty(), mk_goal(&n)))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (nid, n) = b.fresh_local(nat_ty());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(nat_ty());
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, nat_ty(), mk_goal(&m)))
            };
            // zero: rfl : natAdd 0 0 = 0
            let zero_case = eq_refl_nat(nat_zero());
            // succ: fun (k)(ih : natAdd 0 k = k) => congrArg succ ih
            //   natAdd 0 (succ k) ≡ succ (natAdd 0 k); goal succ (natAdd 0 k) = succ k.
            let succ_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (kid, k) = c.fresh_local(nat_ty());
                let ih_ty = eq_nat(na(nat_zero(), k.clone()), k.clone());
                let (ihid, ih) = c.fresh_local(ih_ty.clone());
                let body = congr_arg_nat(
                    na(nat_zero(), k.clone()),
                    k.clone(),
                    Expr::const_str("Nat.succ"),
                    ih,
                );
                let r = c.mk_lam(ihid, BinderInfo::Default, ih_ty, body);
                c.finish_child(c.mk_lam(kid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let body = Expr::apps(nat_rec, [motive, zero_case, succ_case, n.clone()]);
            b.finish(b.mk_lam(nid, BinderInfo::Default, nat_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_ADD_ZERO_L),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natAddSuccL : (m n : Nat) -> Eq (natAdd (succ m) n) (succ (natAdd m n))`.
    /// Induction on `n`.
    fn register_nat_add_succ_l(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_ADD_SUCC_L))
            .is_some()
        {
            return Ok(());
        }
        let mk_goal = |m: &Expr, n: &Expr| {
            eq_nat(
                na(nat_succ(m.clone()), n.clone()),
                nat_succ(na(m.clone(), n.clone())),
            )
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (mid, m) = b.fresh_local(nat_ty());
            let (nid, n) = b.fresh_local(nat_ty());
            let e = b.mk_pi(nid, BinderInfo::Default, nat_ty(), mk_goal(&m, &n));
            b.finish(b.mk_pi(mid, BinderInfo::Default, nat_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (mid, m) = b.fresh_local(nat_ty());
            let (nid, n) = b.fresh_local(nat_ty());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m2id, m2) = c.fresh_local(nat_ty());
                c.finish_child(c.mk_lam(m2id, BinderInfo::Default, nat_ty(), mk_goal(&m, &m2)))
            };
            // n=0: natAdd (succ m) 0 ≡ succ m ; succ (natAdd m 0) ≡ succ m. rfl.
            let zero_case = eq_refl_nat(nat_succ(m.clone()));
            // n=S k: fun (k)(ih) => congrArg succ ih.
            //   natAdd (succ m)(S k) ≡ succ (natAdd (succ m) k) ;
            //   succ (natAdd m (S k)) ≡ succ (succ (natAdd m k)).
            //   ih : natAdd (succ m) k = succ (natAdd m k). congrArg succ ih.
            let succ_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (kid, k) = c.fresh_local(nat_ty());
                let ih_ty = eq_nat(
                    na(nat_succ(m.clone()), k.clone()),
                    nat_succ(na(m.clone(), k.clone())),
                );
                let (ihid, ih) = c.fresh_local(ih_ty.clone());
                let body = congr_arg_nat(
                    na(nat_succ(m.clone()), k.clone()),
                    nat_succ(na(m.clone(), k.clone())),
                    Expr::const_str("Nat.succ"),
                    ih,
                );
                let r = c.mk_lam(ihid, BinderInfo::Default, ih_ty, body);
                c.finish_child(c.mk_lam(kid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let inner = Expr::apps(nat_rec, [motive, zero_case, succ_case, n.clone()]);
            let e = b.mk_lam(nid, BinderInfo::Default, nat_ty(), inner);
            b.finish(b.mk_lam(mid, BinderInfo::Default, nat_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_ADD_SUCC_L),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natAddComm : (m n : Nat) -> Eq (natAdd m n) (natAdd n m)`. Induction on
    /// `n`, using `natAddZeroL` (base) and `natAddSuccL` (step).
    fn register_nat_add_comm(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_ADD_COMM))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_add_zero_l()?;
        self.register_nat_add_succ_l()?;
        let mk_goal =
            |m: &Expr, n: &Expr| eq_nat(na(m.clone(), n.clone()), na(n.clone(), m.clone()));
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (mid, m) = b.fresh_local(nat_ty());
            let (nid, n) = b.fresh_local(nat_ty());
            let e = b.mk_pi(nid, BinderInfo::Default, nat_ty(), mk_goal(&m, &n));
            b.finish(b.mk_pi(mid, BinderInfo::Default, nat_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (mid, m) = b.fresh_local(nat_ty());
            let (nid, n) = b.fresh_local(nat_ty());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (n2id, n2) = c.fresh_local(nat_ty());
                c.finish_child(c.mk_lam(n2id, BinderInfo::Default, nat_ty(), mk_goal(&m, &n2)))
            };
            // n=0: natAdd m 0 ≡ m ; natAdd 0 m =?= m. goal: m = natAdd 0 m.
            //   symm (natAddZeroL m) : m = natAdd 0 m.
            let zero_case = {
                let zl = Expr::app(Expr::const_str(proof_names::NAT_ADD_ZERO_L), m.clone());
                eq_symm_nat(na(nat_zero(), m.clone()), m.clone(), zl)
            };
            // n=S k: goal natAdd m (S k) = natAdd (S k) m.
            //   natAdd m (S k) ≡ succ (natAdd m k).
            //   ih : natAdd m k = natAdd k m ⇒ congrArg succ ih : succ(natAdd m k) = succ(natAdd k m).
            //   natAddSuccL k m : natAdd (S k) m = succ (natAdd k m) ⇒ symm gives
            //     succ (natAdd k m) = natAdd (S k) m. Eq.trans.
            let succ_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (kid, k) = c.fresh_local(nat_ty());
                let ih_ty = mk_goal(&m, &k);
                let (ihid, ih) = c.fresh_local(ih_ty.clone());
                // step1 : succ (natAdd m k) = succ (natAdd k m)
                let step1 = congr_arg_nat(
                    na(m.clone(), k.clone()),
                    na(k.clone(), m.clone()),
                    Expr::const_str("Nat.succ"),
                    ih,
                );
                // sl : natAdd (S k) m = succ (natAdd k m)
                let sl = Expr::apps(
                    Expr::const_str(proof_names::NAT_ADD_SUCC_L),
                    [k.clone(), m.clone()],
                );
                // step2 : succ (natAdd k m) = natAdd (S k) m
                let step2 = eq_symm_nat(
                    na(nat_succ(k.clone()), m.clone()),
                    nat_succ(na(k.clone(), m.clone())),
                    sl,
                );
                // body : succ (natAdd m k) = natAdd (S k) m  (≡ goal LHS natAdd m (S k))
                let body = eq_trans_nat(
                    nat_succ(na(m.clone(), k.clone())),
                    nat_succ(na(k.clone(), m.clone())),
                    na(nat_succ(k.clone()), m.clone()),
                    step1,
                    step2,
                );
                let r = c.mk_lam(ihid, BinderInfo::Default, ih_ty, body);
                c.finish_child(c.mk_lam(kid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let inner = Expr::apps(nat_rec, [motive, zero_case, succ_case, n.clone()]);
            let e = b.mk_lam(nid, BinderInfo::Default, nat_ty(), inner);
            b.finish(b.mk_lam(mid, BinderInfo::Default, nat_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_ADD_COMM),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natAddAssoc : (m n k) -> Eq (natAdd (natAdd m n) k) (natAdd m (natAdd n k))`.
    /// Induction on `k` (`natAdd` recurses on its 2nd arg).
    fn register_nat_add_assoc(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_ADD_ASSOC))
            .is_some()
        {
            return Ok(());
        }
        let mk_goal = |m: &Expr, n: &Expr, k: &Expr| {
            eq_nat(
                na(na(m.clone(), n.clone()), k.clone()),
                na(m.clone(), na(n.clone(), k.clone())),
            )
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (mid, m) = b.fresh_local(nat_ty());
            let (nid, n) = b.fresh_local(nat_ty());
            let (kid, k) = b.fresh_local(nat_ty());
            let e = b.mk_pi(kid, BinderInfo::Default, nat_ty(), mk_goal(&m, &n, &k));
            let e = b.mk_pi(nid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_pi(mid, BinderInfo::Default, nat_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (mid, m) = b.fresh_local(nat_ty());
            let (nid, n) = b.fresh_local(nat_ty());
            let (kid, k) = b.fresh_local(nat_ty());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (k2id, k2) = c.fresh_local(nat_ty());
                c.finish_child(c.mk_lam(k2id, BinderInfo::Default, nat_ty(), mk_goal(&m, &n, &k2)))
            };
            // k=0: natAdd (natAdd m n) 0 ≡ natAdd m n ; natAdd m (natAdd n 0) ≡ natAdd m n. rfl.
            let zero_case = eq_refl_nat(na(m.clone(), n.clone()));
            // k=S j: both sides ≡ succ of the j-case via natAdd _ (S j) ≡ succ (natAdd _ j).
            //   LHS ≡ succ (natAdd (natAdd m n) j) ; RHS:
            //     natAdd m (natAdd n (S j)) ≡ natAdd m (succ (natAdd n j)) ≡ succ (natAdd m (natAdd n j)).
            //   ih : natAdd (natAdd m n) j = natAdd m (natAdd n j). congrArg succ ih.
            let succ_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (jid, j) = c.fresh_local(nat_ty());
                let ih_ty = mk_goal(&m, &n, &j);
                let (ihid, ih) = c.fresh_local(ih_ty.clone());
                let body = congr_arg_nat(
                    na(na(m.clone(), n.clone()), j.clone()),
                    na(m.clone(), na(n.clone(), j.clone())),
                    Expr::const_str("Nat.succ"),
                    ih,
                );
                let r = c.mk_lam(ihid, BinderInfo::Default, ih_ty, body);
                c.finish_child(c.mk_lam(jid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let inner = Expr::apps(nat_rec, [motive, zero_case, succ_case, k.clone()]);
            let e = b.mk_lam(kid, BinderInfo::Default, nat_ty(), inner);
            let e = b.mk_lam(nid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_lam(mid, BinderInfo::Default, nat_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_ADD_ASSOC),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `intAddMono : (a b c d : Int) -> Eq (intLe a b) true -> Eq (intLe c d) true`
    /// `-> Eq (intLe (intAdd a c)(intAdd b d)) true`. Reduces to `natLeAddBoth`
    /// plus two `natAddReshuffle` rewrites.
    fn register_int_add_mono(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::INT_ADD_MONO))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_le_add_both()?;
        self.register_nat_add_reshuffle()?;
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(int_ty());
            let (bid, bb) = b.fresh_local(int_ty());
            let (cid, c) = b.fresh_local(int_ty());
            let (did, dd) = b.fresh_local(int_ty());
            let h1 = eq_bool_(ile(a.clone(), bb.clone()), btrue());
            let h2 = eq_bool_(ile(c.clone(), dd.clone()), btrue());
            let concl = eq_bool_(
                ile(iadd(a.clone(), c.clone()), iadd(bb.clone(), dd.clone())),
                btrue(),
            );
            let inner = Expr::arrow(h1, Expr::arrow(h2, concl));
            let e = b.mk_pi(did, BinderInfo::Default, int_ty(), inner);
            let e = b.mk_pi(cid, BinderInfo::Default, int_ty(), e);
            let e = b.mk_pi(bid, BinderInfo::Default, int_ty(), e);
            b.finish(b.mk_pi(aid, BinderInfo::Default, int_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(int_ty());
            let (bid, bb) = b.fresh_local(int_ty());
            let (cid, c) = b.fresh_local(int_ty());
            let (did, dd) = b.fresh_local(int_ty());
            let h1_ty = eq_bool_(ile(a.clone(), bb.clone()), btrue());
            let (h1id, h1) = b.fresh_local(h1_ty.clone());
            let h2_ty = eq_bool_(ile(c.clone(), dd.clone()), btrue());
            let (h2id, h2) = b.fresh_local(h2_ty.clone());
            // components
            let ap = int_pos(a.clone());
            let an = int_neg(a.clone());
            let bp = int_pos(bb.clone());
            let bn = int_neg(bb.clone());
            let cp = int_pos(c.clone());
            let cn = int_neg(c.clone());
            let dp = int_pos(dd.clone());
            let dn = int_neg(dd.clone());
            // h1 : natLe (ap+bn)(bp+an) = true ; h2 : natLe (cp+dn)(dp+cn) = true (defeq).
            // M : natLe ((ap+bn)+(cp+dn)) ((bp+an)+(dp+cn)) = true.
            let m = Expr::apps(
                Expr::const_str(proof_names::NAT_LE_ADD_BOTH),
                [
                    na(ap.clone(), bn.clone()),
                    na(bp.clone(), an.clone()),
                    na(cp.clone(), dn.clone()),
                    na(dp.clone(), cn.clone()),
                    h1.clone(),
                    h2.clone(),
                ],
            );
            // reshuffle LHS: (ap+bn)+(cp+dn) = (ap+cp)+(bn+dn).
            let rsl = Expr::apps(
                Expr::const_str(proof_names::NAT_ADD_RESHUFFLE),
                [ap.clone(), bn.clone(), cp.clone(), dn.clone()],
            );
            // rewrite M's LHS via rsl. motive z := natLe z ((bp+an)+(dp+cn)) = true.
            let rhs_m = na(na(bp.clone(), an.clone()), na(dp.clone(), cn.clone()));
            let motive_l = {
                let inner = eq_bool_(nle(Expr::bvar(0), rhs_m.clone()), btrue());
                Expr::lam(BinderInfo::Default, nat_ty(), inner)
            };
            let m2 = eq_subst_nat(
                motive_l,
                na(na(ap.clone(), bn.clone()), na(cp.clone(), dn.clone())),
                na(na(ap.clone(), cp.clone()), na(bn.clone(), dn.clone())),
                rsl,
                m,
            );
            // m2 : natLe ((ap+cp)+(bn+dn)) ((bp+an)+(dp+cn)) = true.
            // reshuffle RHS: (bp+an)+(dp+cn) = (bp+dp)+(an+cn).
            let rsr = Expr::apps(
                Expr::const_str(proof_names::NAT_ADD_RESHUFFLE),
                [bp.clone(), an.clone(), dp.clone(), cn.clone()],
            );
            let lhs_m2 = na(na(ap.clone(), cp.clone()), na(bn.clone(), dn.clone()));
            let motive_r = {
                let inner = eq_bool_(nle(lhs_m2.clone(), Expr::bvar(0)), btrue());
                Expr::lam(BinderInfo::Default, nat_ty(), inner)
            };
            let m3 = eq_subst_nat(
                motive_r,
                na(na(bp.clone(), an.clone()), na(dp.clone(), cn.clone())),
                na(na(bp.clone(), dp.clone()), na(an.clone(), cn.clone())),
                rsr,
                m2,
            );
            // m3 : natLe ((ap+cp)+(bn+dn)) ((bp+dp)+(an+cn)) = true ≡ goal
            //   (intLe (intAdd a c)(intAdd b d) reduces to exactly this).
            let r = b.mk_lam(h2id, BinderInfo::Default, h2_ty, m3);
            let r = b.mk_lam(h1id, BinderInfo::Default, h1_ty, r);
            let r = b.mk_lam(did, BinderInfo::Default, int_ty(), r);
            let r = b.mk_lam(cid, BinderInfo::Default, int_ty(), r);
            let r = b.mk_lam(bid, BinderInfo::Default, int_ty(), r);
            b.finish(b.mk_lam(aid, BinderInfo::Default, int_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::INT_ADD_MONO),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `intLeTrans : (a b c : Int) -> Eq (intLe a b) true -> Eq (intLe b c) true`
    /// `-> Eq (intLe a c) true`. Adds the two reduced Nat inequalities, reshuffles
    /// to isolate the common `(b.pos + b.neg)`, then cancels it (`natLeAddCancelR`).
    fn register_int_le_trans(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::INT_LE_TRANS))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_le_add_both()?;
        self.register_nat_add_reshuffle2()?;
        self.register_nat_le_add_cancel_r()?;
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(int_ty());
            let (bid, bb) = b.fresh_local(int_ty());
            let (cid, c) = b.fresh_local(int_ty());
            let h1 = eq_bool_(ile(a.clone(), bb.clone()), btrue());
            let h2 = eq_bool_(ile(bb.clone(), c.clone()), btrue());
            let concl = eq_bool_(ile(a.clone(), c.clone()), btrue());
            let inner = Expr::arrow(h1, Expr::arrow(h2, concl));
            let e = b.mk_pi(cid, BinderInfo::Default, int_ty(), inner);
            let e = b.mk_pi(bid, BinderInfo::Default, int_ty(), e);
            b.finish(b.mk_pi(aid, BinderInfo::Default, int_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(int_ty());
            let (bid, bb) = b.fresh_local(int_ty());
            let (cid, c) = b.fresh_local(int_ty());
            let h1_ty = eq_bool_(ile(a.clone(), bb.clone()), btrue());
            let (h1id, h1) = b.fresh_local(h1_ty.clone());
            let h2_ty = eq_bool_(ile(bb.clone(), c.clone()), btrue());
            let (h2id, h2) = b.fresh_local(h2_ty.clone());
            let ap = int_pos(a.clone());
            let an = int_neg(a.clone());
            let bp = int_pos(bb.clone());
            let bn = int_neg(bb.clone());
            let cp = int_pos(c.clone());
            let cn = int_neg(c.clone());
            // h1 : natLe (ap+bn)(bp+an) ; h2 : natLe (bp+cn)(cp+bn).
            // M : natLe ((ap+bn)+(bp+cn)) ((bp+an)+(cp+bn)).
            let m = Expr::apps(
                Expr::const_str(proof_names::NAT_LE_ADD_BOTH),
                [
                    na(ap.clone(), bn.clone()),
                    na(bp.clone(), an.clone()),
                    na(bp.clone(), cn.clone()),
                    na(cp.clone(), bn.clone()),
                    h1.clone(),
                    h2.clone(),
                ],
            );
            // Reshuffle2 LHS (ap+bn)+(bp+cn) = (ap+cn)+(bn+bp).
            let rsl = Expr::apps(
                Expr::const_str(proof_names::NAT_ADD_RESHUFFLE2),
                [ap.clone(), bn.clone(), bp.clone(), cn.clone()],
            );
            let rhs_m = na(na(bp.clone(), an.clone()), na(cp.clone(), bn.clone()));
            let motive_l = {
                let inner = eq_bool_(nle(Expr::bvar(0), rhs_m.clone()), btrue());
                Expr::lam(BinderInfo::Default, nat_ty(), inner)
            };
            let m2 = eq_subst_nat(
                motive_l,
                na(na(ap.clone(), bn.clone()), na(bp.clone(), cn.clone())),
                na(na(ap.clone(), cn.clone()), na(bn.clone(), bp.clone())),
                rsl,
                m,
            );
            // Reshuffle2 RHS (bp+an)+(cp+bn) = (bp+bn)+(an+cp).
            let rsr = Expr::apps(
                Expr::const_str(proof_names::NAT_ADD_RESHUFFLE2),
                [bp.clone(), an.clone(), cp.clone(), bn.clone()],
            );
            let lhs_m2 = na(na(ap.clone(), cn.clone()), na(bn.clone(), bp.clone()));
            let motive_r = {
                let inner = eq_bool_(nle(lhs_m2.clone(), Expr::bvar(0)), btrue());
                Expr::lam(BinderInfo::Default, nat_ty(), inner)
            };
            let m3 = eq_subst_nat(
                motive_r,
                na(na(bp.clone(), an.clone()), na(cp.clone(), bn.clone())),
                na(na(bp.clone(), bn.clone()), na(an.clone(), cp.clone())),
                rsr,
                m2,
            );
            // m3 : natLe ((ap+cn)+(bn+bp)) ((bp+bn)+(an+cp)).
            // We want to cancel the common (bp+bn) on the RIGHT addend of both sides.
            // Currently LHS right addend is (bn+bp), RHS left addend is (bp+bn).
            // Normalize both to a common k := (bp+bn) added on the RIGHT, so we can use
            // natLeAddCancelR. Rewrite LHS (bn+bp) ↦ (bp+bn) via comm; rewrite RHS
            // (bp+bn)+(an+cp) ↦ (an+cp)+(bp+bn) via comm.
            let comm_bnbp = Expr::apps(
                Expr::const_str(proof_names::NAT_ADD_COMM),
                [bn.clone(), bp.clone()],
            );
            // motive: natLe ((ap+cn)+z) ((bp+bn)+(an+cp)) = true, rewrite z (bn+bp)↦(bp+bn).
            let motive_la = {
                let inner = eq_bool_(
                    nle(
                        na(na(ap.clone(), cn.clone()), Expr::bvar(0)),
                        na(na(bp.clone(), bn.clone()), na(an.clone(), cp.clone())),
                    ),
                    btrue(),
                );
                Expr::lam(BinderInfo::Default, nat_ty(), inner)
            };
            let m4 = eq_subst_nat(
                motive_la,
                na(bn.clone(), bp.clone()),
                na(bp.clone(), bn.clone()),
                comm_bnbp,
                m3,
            );
            // m4 : natLe ((ap+cn)+(bp+bn)) ((bp+bn)+(an+cp)).
            // Rewrite RHS (bp+bn)+(an+cp) ↦ (an+cp)+(bp+bn) via comm.
            let comm_rhs = Expr::apps(
                Expr::const_str(proof_names::NAT_ADD_COMM),
                [na(bp.clone(), bn.clone()), na(an.clone(), cp.clone())],
            );
            let motive_ra = {
                let inner = eq_bool_(
                    nle(
                        na(na(ap.clone(), cn.clone()), na(bp.clone(), bn.clone())),
                        Expr::bvar(0),
                    ),
                    btrue(),
                );
                Expr::lam(BinderInfo::Default, nat_ty(), inner)
            };
            let m5 = eq_subst_nat(
                motive_ra,
                na(na(bp.clone(), bn.clone()), na(an.clone(), cp.clone())),
                na(na(an.clone(), cp.clone()), na(bp.clone(), bn.clone())),
                comm_rhs,
                m4,
            );
            // m5 : natLe ((ap+cn)+(bp+bn)) ((an+cp)+(bp+bn)).
            // Cancel k := (bp+bn): natLeAddCancelR k (ap+cn)(an+cp) m5.
            let cancelled = Expr::apps(
                Expr::const_str(proof_names::NAT_LE_ADD_CANCEL_R),
                [
                    na(bp.clone(), bn.clone()),
                    na(ap.clone(), cn.clone()),
                    na(an.clone(), cp.clone()),
                    m5,
                ],
            );
            // cancelled : natLe (ap+cn)(an+cp) = true.
            // Goal intLe a c = natLe (ap+cn)(cp+an). Need RHS (an+cp) ↦ (cp+an) via comm.
            let comm_ancp = Expr::apps(
                Expr::const_str(proof_names::NAT_ADD_COMM),
                [an.clone(), cp.clone()],
            );
            let motive_goal = {
                let inner = eq_bool_(nle(na(ap.clone(), cn.clone()), Expr::bvar(0)), btrue());
                Expr::lam(BinderInfo::Default, nat_ty(), inner)
            };
            let goal_proof = eq_subst_nat(
                motive_goal,
                na(an.clone(), cp.clone()),
                na(cp.clone(), an.clone()),
                comm_ancp,
                cancelled,
            );
            let r = b.mk_lam(h2id, BinderInfo::Default, h2_ty, goal_proof);
            let r = b.mk_lam(h1id, BinderInfo::Default, h1_ty, r);
            let r = b.mk_lam(cid, BinderInfo::Default, int_ty(), r);
            let r = b.mk_lam(bid, BinderInfo::Default, int_ty(), r);
            b.finish(b.mk_lam(aid, BinderInfo::Default, int_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::INT_LE_TRANS),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natLeMulMonoR : (c a b : Nat) -> Eq (natLe a b) true ->`
    /// `Eq (natLe (natMul a c)(natMul b c)) true`. Induction on `c`
    /// (`natMul _ 0 ≡ 0`; `natMul _ (S k) ≡ natAdd (natMul _ k) _`).
    fn register_nat_le_mul_mono_r(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_LE_MUL_MONO_R))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_le_add_both()?;
        self.register_nat_le_refl()?;
        // P c := ∀ a b, natLe a b = true → natLe (natMul a c)(natMul b c) = true.
        let p_of = |c: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (aid, a) = d.fresh_local(nat_ty());
            let (bid, b) = d.fresh_local(nat_ty());
            let hyp = eq_bool_(nle(a.clone(), b.clone()), btrue());
            let concl = eq_bool_(
                nle(nm(a.clone(), c.clone()), nm(b.clone(), c.clone())),
                btrue(),
            );
            let inner = Expr::arrow(hyp, concl);
            let inner = d.mk_pi(bid, BinderInfo::Default, nat_ty(), inner);
            d.finish_child(d.mk_pi(aid, BinderInfo::Default, nat_ty(), inner))
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (cid, c) = b.fresh_local(nat_ty());
            b.finish(b.mk_pi(cid, BinderInfo::Default, nat_ty(), p_of(&c, &b)))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (cid, c) = b.fresh_local(nat_ty());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (mid, m) = d.fresh_local(nat_ty());
                d.finish_child(d.mk_lam(mid, BinderInfo::Default, nat_ty(), p_of(&m, &d)))
            };
            // c=0: fun a b (_h) => natLeRefl 0  (natMul a 0 ≡ 0, natMul b 0 ≡ 0).
            let zero_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (aid, a) = d.fresh_local(nat_ty());
                let (bid, bb) = d.fresh_local(nat_ty());
                let h_ty = eq_bool_(nle(a.clone(), bb.clone()), btrue());
                let (hid, _h) = d.fresh_local(h_ty.clone());
                let body = Expr::app(Expr::const_str(proof_names::NAT_LE_REFL), nat_zero());
                let r = d.mk_lam(hid, BinderInfo::Default, h_ty, body);
                let r = d.mk_lam(bid, BinderInfo::Default, nat_ty(), r);
                d.finish_child(d.mk_lam(aid, BinderInfo::Default, nat_ty(), r))
            };
            // c=S k: fun (k)(ihc : P k) => fun a b (h) =>
            //   natMul a (S k) ≡ natAdd (natMul a k) a ; likewise for b.
            //   natLeAddBoth (natMul a k)(natMul b k) a b (ihc a b h) h.
            let succ_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (kid, k) = d.fresh_local(nat_ty());
                let (ihcid, ihc) = d.fresh_local(p_of(&k, &d));
                let inner = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (aid, a) = e.fresh_local(nat_ty());
                    let (bid, bb) = e.fresh_local(nat_ty());
                    let h_ty = eq_bool_(nle(a.clone(), bb.clone()), btrue());
                    let (hid, h) = e.fresh_local(h_ty.clone());
                    let ih_app = Expr::apps(ihc.clone(), [a.clone(), bb.clone(), h.clone()]);
                    let body = Expr::apps(
                        Expr::const_str(proof_names::NAT_LE_ADD_BOTH),
                        [
                            nm(a.clone(), k.clone()),
                            nm(bb.clone(), k.clone()),
                            a.clone(),
                            bb.clone(),
                            ih_app,
                            h,
                        ],
                    );
                    let r = e.mk_lam(hid, BinderInfo::Default, h_ty, body);
                    let r = e.mk_lam(bid, BinderInfo::Default, nat_ty(), r);
                    e.finish_child(e.mk_lam(aid, BinderInfo::Default, nat_ty(), r))
                };
                let r = d.mk_lam(ihcid, BinderInfo::Default, p_of(&k, &d), inner);
                d.finish_child(d.mk_lam(kid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let body = Expr::apps(nat_rec, [motive, zero_case, succ_case, c.clone()]);
            b.finish(b.mk_lam(cid, BinderInfo::Default, nat_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_LE_MUL_MONO_R),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §7 natLeContra — the foundational Nat antisymmetry lemma ────────────

    /// `natLeContra : (a b : Nat) -> Eq (natLe a b) true -> Eq (natLe (succ b) a)`
    /// `true -> False`. (`a ≤ b` and `b < a` are jointly impossible.)
    ///
    /// Double `Nat.rec` on `a` then `b`:
    ///   * a=0: `natLe (succ b) 0 ≡ false`, so the 2nd hyp is `false = true`.
    ///   * a=S a', b=0: `natLe (S a') 0 ≡ false`, so the 1st hyp is `false = true`.
    ///   * a=S a', b=S b': both `natLe` peel a `succ`, so `ih a' b'` applies.
    fn register_nat_le_contra(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_LE_CONTRA))
            .is_some()
        {
            return Ok(());
        }
        // P a := ∀ b, natLe a b = true → natLe (succ b) a = true → False
        let p_of = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut c = EnvDeclBuilder::child_of(parent);
            let (bid, b) = c.fresh_local(nat_ty());
            let h1 = eq_bool_(nle(a.clone(), b.clone()), btrue());
            let h2 = eq_bool_(nle(nat_succ(b.clone()), a.clone()), btrue());
            let inner = Expr::arrow(h1, Expr::arrow(h2, false_c()));
            c.finish_child(c.mk_pi(bid, BinderInfo::Default, nat_ty(), inner))
        };

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(nat_ty());
            let body = p_of(&a, &b);
            b.finish(b.mk_pi(aid, BinderInfo::Default, nat_ty(), body))
        };

        // zeroCase : P 0 = ∀ b, natLe 0 b = true → natLe (succ b) 0 = true → False.
        //   natLe (succ b) 0 ≡ false, so h2 : false = true is absurd.
        let zero_case = {
            let mut b = EnvDeclBuilder::new();
            let (bid, bb) = b.fresh_local(nat_ty());
            let h1_ty = eq_bool_(nle(nat_zero(), bb.clone()), btrue());
            let (h1id, _h1) = b.fresh_local(h1_ty.clone());
            let h2_ty = eq_bool_(nle(nat_succ(bb.clone()), nat_zero()), btrue());
            let (h2id, h2) = b.fresh_local(h2_ty.clone());
            let ff = tf_to_false(eq_symm_bool(bfalse(), btrue(), h2));
            let r = b.mk_lam(h2id, BinderInfo::Default, h2_ty, ff);
            let r = b.mk_lam(h1id, BinderInfo::Default, h1_ty, r);
            b.finish(b.mk_lam(bid, BinderInfo::Default, nat_ty(), r))
        };

        // succCase : (a' : Nat) → P a' → P (succ a').
        //   P (succ a') = ∀ b, natLe (succ a') b = true → natLe (succ b)(succ a') = true → False.
        //   Inner Nat.rec on b:
        //     b=0: natLe (succ a') 0 ≡ false ⇒ h1 absurd.
        //     b=S b': natLe (succ a')(S b') ≡ natLe a' b' ; natLe (succ(S b'))(succ a') ≡
        //             natLe (succ b') a'. ihA b' h1 h2 : False.
        let succ_case = {
            let mut b = EnvDeclBuilder::new();
            let (apid, ap) = b.fresh_local(nat_ty());
            let (ihaid, iha) = b.fresh_local(p_of(&ap, &b));
            let sa = nat_succ(ap.clone());
            // inner motive over b : fun b => natLe (succ a') b = true →
            //                                natLe (succ b)(succ a') = true → False
            let inner_motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(nat_ty());
                let h1 = eq_bool_(nle(sa.clone(), m.clone()), btrue());
                let h2 = eq_bool_(nle(nat_succ(m.clone()), sa.clone()), btrue());
                let body = Expr::arrow(h1, Expr::arrow(h2, false_c()));
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, nat_ty(), body))
            };
            // b=0 case : fun (h1 : natLe (succ a') 0 = true)(_h2) => absurd.
            let bzero = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let h1_ty = eq_bool_(nle(sa.clone(), nat_zero()), btrue());
                let (h1id, h1) = c.fresh_local(h1_ty.clone());
                let h2_ty = eq_bool_(nle(nat_succ(nat_zero()), sa.clone()), btrue());
                let (h2id, _h2) = c.fresh_local(h2_ty.clone());
                let ff = tf_to_false(eq_symm_bool(bfalse(), btrue(), h1));
                let r = c.mk_lam(h2id, BinderInfo::Default, h2_ty, ff);
                c.finish_child(c.mk_lam(h1id, BinderInfo::Default, h1_ty, r))
            };
            // b=S b' case : fun (b' : Nat)(_ihb)(h1)(h2) => ihA b' h1 h2.
            let bsucc = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (bpid, bp) = c.fresh_local(nat_ty());
                // inner ih over b (the Nat.rec minor's motive-applied hyp) — unused.
                let ihb_ty = {
                    let h1 = eq_bool_(nle(sa.clone(), bp.clone()), btrue());
                    let h2 = eq_bool_(nle(nat_succ(bp.clone()), sa.clone()), btrue());
                    Expr::arrow(h1, Expr::arrow(h2, false_c()))
                };
                let (ihbid, _ihb) = c.fresh_local(ihb_ty.clone());
                // goal at b=S b' : natLe (succ a')(S b') = true → natLe (succ(S b'))(succ a') = true → False
                let h1_ty = eq_bool_(nle(sa.clone(), nat_succ(bp.clone())), btrue());
                let (h1id, h1) = c.fresh_local(h1_ty.clone());
                let h2_ty = eq_bool_(nle(nat_succ(nat_succ(bp.clone())), sa.clone()), btrue());
                let (h2id, h2) = c.fresh_local(h2_ty.clone());
                // ihA b' : natLe a' b' = true → natLe (succ b') a' = true → False.
                //   h1 : natLe (succ a')(S b') = true ≡ natLe a' b' = true (defeq).
                //   h2 : natLe (S(S b'))(succ a') = true ≡ natLe (succ b') a' = true (defeq).
                let app = Expr::apps(iha.clone(), [bp.clone()]);
                let app = Expr::apps(app, [h1, h2]);
                let r = c.mk_lam(h2id, BinderInfo::Default, h2_ty, app);
                let r = c.mk_lam(h1id, BinderInfo::Default, h1_ty, r);
                let r = c.mk_lam(ihbid, BinderInfo::Default, ihb_ty, r);
                c.finish_child(c.mk_lam(bpid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            // body : P (succ a') = fun b => Nat.rec inner_motive bzero bsucc b
            let inner = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (bid, bb) = c.fresh_local(nat_ty());
                let fold = Expr::apps(nat_rec, [inner_motive, bzero, bsucc, bb.clone()]);
                c.finish_child(c.mk_lam(bid, BinderInfo::Default, nat_ty(), fold))
            };
            let r = b.mk_lam(ihaid, BinderInfo::Default, p_of(&ap, &b), inner);
            b.finish(b.mk_lam(apid, BinderInfo::Default, nat_ty(), r))
        };

        // value : fun (a : Nat) => Nat.rec (motive := P) zeroCase succCase a
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(nat_ty());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(nat_ty());
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, nat_ty(), p_of(&m, &c)))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let body = Expr::apps(nat_rec, [motive, zero_case, succ_case, a.clone()]);
            b.finish(b.mk_lam(aid, BinderInfo::Default, nat_ty(), body))
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_LE_CONTRA),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §8 leNegFalse — the endpoint "0 ≤ d < 0 is impossible" lemma ───────

    /// `leNegFalse : (d : Int) -> Eq (intLe int0 d) true -> Eq (intIsNeg d) true`
    /// `-> False`. The arithmetic core of the Farkas contradiction `0 ≤ d < 0`.
    ///
    /// `intLe int0 d ≡ natLe (natAdd 0 d.neg) d.pos` and `intIsNeg d ≡
    /// natLe (succ d.pos) (natAdd 0 d.neg)`; with `q := natAdd 0 d.neg`, `p := d.pos`
    /// these are exactly the two hypotheses of `natLeContra q p`.
    fn register_le_neg_false(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::LE_NEG_FALSE))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_le_contra()?;
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (did, d) = b.fresh_local(int_ty());
            let h1 = eq_bool_(ile(int0(), d.clone()), btrue());
            let h2 = eq_bool_(
                Expr::app(Expr::const_str(names::INT_IS_NEG), d.clone()),
                btrue(),
            );
            let inner = Expr::arrow(h1, Expr::arrow(h2, false_c()));
            b.finish(b.mk_pi(did, BinderInfo::Default, int_ty(), inner))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (did, d) = b.fresh_local(int_ty());
            let h1_ty = eq_bool_(ile(int0(), d.clone()), btrue());
            let (h1id, h1) = b.fresh_local(h1_ty.clone());
            let h2_ty = eq_bool_(
                Expr::app(Expr::const_str(names::INT_IS_NEG), d.clone()),
                btrue(),
            );
            let (h2id, h2) = b.fresh_local(h2_ty.clone());
            // q := natAdd 0 d.neg ; p := d.pos.
            let q = na(nat_zero(), int_neg(d.clone()));
            let p = int_pos(d.clone());
            // natLeContra q p : natLe q p = true → natLe (succ p) q = true → False.
            //   h1 : intLe int0 d = true ≡ natLe q p = true (defeq).
            //   h2 : intIsNeg d = true ≡ natLe (succ p) q = true (defeq).
            let app = Expr::apps(
                Expr::const_str(proof_names::NAT_LE_CONTRA),
                [q, p, h1.clone(), h2.clone()],
            );
            let r = b.mk_lam(h2id, BinderInfo::Default, h2_ty, app);
            let r = b.mk_lam(h1id, BinderInfo::Default, h1_ty, r);
            b.finish(b.mk_lam(did, BinderInfo::Default, int_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::LE_NEG_FALSE),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §9 m5UnsatConcrete — the concrete proved infeasibility ──────────────

    /// `m5UnsatConcrete : Unsat [[1],[-1]] [-1,-1]` — a genuine
    /// `Declaration::Theorem` witnessing that the m5 system `x ≤ -1 ∧ -x ≤ -1`
    /// has NO integer solution. The parallel of the software kingdom's
    /// `emptyClauseUnsat`: a concrete, kernel-checked, axiom-free soundness
    /// fragment.
    ///
    /// Proof (the Farkas combination, specialized to multipliers `y = (1,1)`):
    /// given `x` with `rowsHold`, extract `h1 : intLe (intDot [1] x)(-1) = true`
    /// and `h2 : intLe (intDot [-1] x)(-1) = true`. With `d1 := intDot [1] x`,
    /// `d2 := intDot [-1] x`, `intAddMono h1 h2` gives `intLe (d1+d2)(-1 + -1) =
    /// true` (where `-1 + -1 ≡ mk 0 2`). The column sum cancels: `(d1+d2).pos`
    /// and `(d1+d2).neg` are the SAME four atoms permuted, so a comm/reshuffle
    /// chain `E` proves `(d1+d2).neg = (d1+d2).pos`, whence `natLeRefl` +
    /// `natAddZeroL` give `intLe int0 (d1+d2) = true`. `intLeTrans` chains
    /// `int0 ≤ d1+d2 ≤ mk 0 2`, and `leNegFalse` on `intIsNeg (mk 0 2) ≡ true`
    /// closes it. Foundational (no domain axioms; Quot-free).
    fn register_m5_unsat_concrete(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::M5_UNSAT_CONCRETE))
            .is_some()
        {
            return Ok(());
        }
        self.register_int_add_mono()?;
        self.register_int_le_trans()?;
        self.register_le_neg_false()?;
        self.register_nat_le_refl()?;
        self.register_nat_add_zero_l()?;
        self.register_nat_add_comm()?;
        self.register_nat_add_reshuffle2()?;

        // concrete data: rows = [[mk 1 0],[mk 0 1]], bounds = [mk 0 1, mk 0 1].
        let pos1 = || int_mk(nat_lit(1), nat_lit(0)); // +1
        let neg1 = || int_mk(nat_lit(0), nat_lit(1)); // -1
        let rows = || {
            cons_list_int(
                cons_int(pos1(), nil_int()),
                cons_list_int(cons_int(neg1(), nil_int()), nil_list_int()),
            )
        };
        let bounds = || cons_int(neg1(), cons_int(neg1(), nil_int()));

        let type_ = Expr::apps(Expr::const_str(names::UNSAT), [rows(), bounds()]);

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (xid, x) = b.fresh_local(list_int());
            // d1 := intDot [mk 1 0] x ; d2 := intDot [mk 0 1] x.
            let d1 = int_dot(cons_int(pos1(), nil_int()), x.clone());
            let d2 = int_dot(cons_int(neg1(), nil_int()), x.clone());
            // the rowsHold hypothesis type (Unsat unfolds to ∀ x, rowsHold → False).
            let rh = Expr::apps(
                Expr::const_str(names::ROWS_HOLD),
                [rows(), bounds(), x.clone()],
            );
            let (hid, h) = b.fresh_local(rh.clone());

            // component atoms of z := headZ x.
            let zp = int_pos(head_z(x.clone()));
            let zn = int_neg(head_z(x.clone()));
            let atom_a = || nm(nat_lit(1), zp.clone()); // natMul 1 z.pos
            let atom_b = || nm(nat_lit(0), zn.clone()); // natMul 0 z.neg
            let atom_c = || nm(nat_lit(1), zn.clone()); // natMul 1 z.neg
            let atom_d = || nm(nat_lit(0), zp.clone()); // natMul 0 z.pos
                                                        // W := intAdd d1 d2 ; W.pos ≡ (A+B)+(D+C) ; W.neg ≡ (C+D)+(B+A).
            let w_pos = || na(na(atom_a(), atom_b()), na(atom_d(), atom_c()));
            let w_neg = || na(na(atom_c(), atom_d()), na(atom_b(), atom_a()));

            // conjunct props (rowsHold reduces headZ/tailZ of bounds to mk 0 1).
            let p1 = eq_bool_(ile(d1.clone(), neg1()), btrue());
            let rest = and_(
                eq_bool_(ile(d2.clone(), neg1()), btrue()),
                Expr::const_str("True"),
            );
            let p2 = eq_bool_(ile(d2.clone(), neg1()), btrue());
            // h1 := And.left p1 rest h ; h2 := And.left p2 True (And.right p1 rest h).
            let h1 = Expr::apps(
                Expr::const_(Name::from_string("And.left"), vec![]),
                [p1.clone(), rest.clone(), h.clone()],
            );
            let h_right = Expr::apps(
                Expr::const_(Name::from_string("And.right"), vec![]),
                [p1, rest, h.clone()],
            );
            let h2 = Expr::apps(
                Expr::const_(Name::from_string("And.left"), vec![]),
                [p2, Expr::const_str("True"), h_right],
            );

            // E : W.neg = W.pos  (the column-sum permutation identity).
            let comm =
                |x: Expr, y: Expr| Expr::apps(Expr::const_str(proof_names::NAT_ADD_COMM), [x, y]);
            let reshuffle2 = |p: Expr, q: Expr, r: Expr, s: Expr| {
                Expr::apps(
                    Expr::const_str(proof_names::NAT_ADD_RESHUFFLE2),
                    [p, q, r, s],
                )
            };
            // s1 : (C+D)+(B+A) = (C+A)+(D+B).
            let s1 = reshuffle2(atom_c(), atom_d(), atom_b(), atom_a());
            // s2a : (C+A)+(D+B) = (A+C)+(D+B).
            let f_s2a = Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                na(Expr::bvar(0), na(atom_d(), atom_b())),
            );
            let s2a = congr_arg_nat(
                na(atom_c(), atom_a()),
                na(atom_a(), atom_c()),
                f_s2a,
                comm(atom_c(), atom_a()),
            );
            // s2b : (A+C)+(D+B) = (A+C)+(B+D).
            let f_s2b = Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                na(na(atom_a(), atom_c()), Expr::bvar(0)),
            );
            let s2b = congr_arg_nat(
                na(atom_d(), atom_b()),
                na(atom_b(), atom_d()),
                f_s2b,
                comm(atom_d(), atom_b()),
            );
            let s2 = eq_trans_nat(
                na(na(atom_c(), atom_a()), na(atom_d(), atom_b())),
                na(na(atom_a(), atom_c()), na(atom_d(), atom_b())),
                na(na(atom_a(), atom_c()), na(atom_b(), atom_d())),
                s2a,
                s2b,
            );
            // s3 : (A+C)+(B+D) = (A+B)+(D+C)  = symm (reshuffle2 A B D C).
            let s3 = eq_symm_nat(
                na(na(atom_a(), atom_b()), na(atom_d(), atom_c())),
                na(na(atom_a(), atom_c()), na(atom_b(), atom_d())),
                reshuffle2(atom_a(), atom_b(), atom_d(), atom_c()),
            );
            // E := trans s1 (trans s2 s3) : (C+D)+(B+A) = (A+B)+(D+C)  [= W.neg = W.pos].
            let s23 = eq_trans_nat(
                na(na(atom_c(), atom_a()), na(atom_d(), atom_b())),
                na(na(atom_a(), atom_c()), na(atom_b(), atom_d())),
                na(na(atom_a(), atom_b()), na(atom_d(), atom_c())),
                s2,
                s3,
            );
            let big_e = eq_trans_nat(
                w_neg(),
                na(na(atom_c(), atom_a()), na(atom_d(), atom_b())),
                w_pos(),
                s1,
                s23,
            );

            // lb : intLe int0 W = true.
            //   refl : natLe W.pos W.pos = true.
            let refl = Expr::app(Expr::const_str(proof_names::NAT_LE_REFL), w_pos());
            //   step : natLe W.neg W.pos = true   (subst W.pos↦W.neg along symm E).
            let motive_step = {
                let inner = eq_bool_(nle(Expr::bvar(0), w_pos()), btrue());
                Expr::lam(BinderInfo::Default, nat_ty(), inner)
            };
            let step = eq_subst_nat(
                motive_step,
                w_pos(),
                w_neg(),
                eq_symm_nat(w_neg(), w_pos(), big_e),
                refl,
            );
            //   lb : natLe (natAdd 0 W.neg) W.pos = true   (subst W.neg↦natAdd 0 W.neg).
            let zl = Expr::app(Expr::const_str(proof_names::NAT_ADD_ZERO_L), w_neg());
            let motive_lb = {
                let inner = eq_bool_(nle(Expr::bvar(0), w_pos()), btrue());
                Expr::lam(BinderInfo::Default, nat_ty(), inner)
            };
            let lb = eq_subst_nat(
                motive_lb,
                w_neg(),
                na(nat_zero(), w_neg()),
                eq_symm_nat(na(nat_zero(), w_neg()), w_neg(), zl),
                step,
            );

            // mono : intLe (intAdd d1 d2)(intAdd (mk 0 1)(mk 0 1)) = true.
            let big_n = iadd(neg1(), neg1());
            let mono = Expr::apps(
                Expr::const_str(proof_names::INT_ADD_MONO),
                [d1.clone(), neg1(), d2.clone(), neg1(), h1, h2],
            );
            // trans : intLe int0 (intAdd d1 d2) -> ... -> intLe int0 N.
            let trans = Expr::apps(
                Expr::const_str(proof_names::INT_LE_TRANS),
                [
                    int0(),
                    iadd(d1.clone(), d2.clone()),
                    big_n.clone(),
                    lb,
                    mono,
                ],
            );
            // negFact : intIsNeg N = true  (N ≡ mk 0 2, intIsNeg ≡ true defeq).
            let neg_fact = eq_refl_bool(btrue());
            // leNegFalse N trans negFact : False.
            let body = Expr::apps(
                Expr::const_str(proof_names::LE_NEG_FALSE),
                [big_n, trans, neg_fact],
            );

            let r = b.mk_lam(hid, BinderInfo::Default, rh, body);
            b.finish(b.mk_lam(xid, BinderInfo::Default, list_int(), r))
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::M5_UNSAT_CONCRETE),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §10 Nat multiplicative tower (toward the general bridge, STEP 2) ─────

    /// Register the genuine Nat multiplicative lemmas proved so far toward the
    /// general `farkasChecks_sound` (obligation (1) of the module note):
    /// `natMulZeroL`, `natMulSuccL`, `natMulComm`, `natMulDistribR`. All are
    /// foundational `Nat.rec` inductions (zero domain axioms).
    pub fn init_farkas_mul_tower(&mut self) -> Result<(), EnvError> {
        self.init_farkas_proofs()?;
        self.register_nat_mul_zero_l()?;
        self.register_nat_mul_succ_l()?;
        self.register_nat_mul_comm()?;
        self.register_nat_mul_distrib_r()?;
        Ok(())
    }

    /// `natMulZeroL : (n) -> Eq (natMul 0 n) 0`. Induction on `n`
    /// (`natMul 0 0 ≡ 0`; `natMul 0 (succ k) ≡ natAdd (natMul 0 k) 0 ≡ natMul 0 k`).
    fn register_nat_mul_zero_l(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_MUL_ZERO_L))
            .is_some()
        {
            return Ok(());
        }
        let mk_goal = |n: &Expr| eq_nat(nm(nat_zero(), n.clone()), nat_zero());
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (nid, n) = b.fresh_local(nat_ty());
            b.finish(b.mk_pi(nid, BinderInfo::Default, nat_ty(), mk_goal(&n)))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (nid, n) = b.fresh_local(nat_ty());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(nat_ty());
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, nat_ty(), mk_goal(&m)))
            };
            // zero: natMul 0 0 ≡ 0. rfl.
            let zero_case = eq_refl_nat(nat_zero());
            // succ: fun (k)(ih : natMul 0 k = 0) => ih
            //   (natMul 0 (succ k) ≡ natAdd (natMul 0 k) 0 ≡ natMul 0 k).
            let succ_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (kid, k) = c.fresh_local(nat_ty());
                let ih_ty = mk_goal(&k);
                let (ihid, ih) = c.fresh_local(ih_ty.clone());
                let r = c.mk_lam(ihid, BinderInfo::Default, ih_ty, ih);
                c.finish_child(c.mk_lam(kid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let body = Expr::apps(nat_rec, [motive, zero_case, succ_case, n.clone()]);
            b.finish(b.mk_lam(nid, BinderInfo::Default, nat_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_MUL_ZERO_L),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natMulSuccL : (m n) -> Eq (natMul (succ m) n) (natAdd (natMul m n) n)`.
    /// Induction on `n`. The step needs the `(P+k)+m = (P+m)+k` rearrangement
    /// (`natAddAssoc` + `natAddComm`).
    fn register_nat_mul_succ_l(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_MUL_SUCC_L))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_add_assoc()?;
        self.register_nat_add_comm()?;
        let mk_goal = |m: &Expr, n: &Expr| {
            eq_nat(
                nm(nat_succ(m.clone()), n.clone()),
                na(nm(m.clone(), n.clone()), n.clone()),
            )
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (mid, m) = b.fresh_local(nat_ty());
            let (nid, n) = b.fresh_local(nat_ty());
            let e = b.mk_pi(nid, BinderInfo::Default, nat_ty(), mk_goal(&m, &n));
            b.finish(b.mk_pi(mid, BinderInfo::Default, nat_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (mid, m) = b.fresh_local(nat_ty());
            let (nid, n) = b.fresh_local(nat_ty());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (n2id, n2) = c.fresh_local(nat_ty());
                c.finish_child(c.mk_lam(n2id, BinderInfo::Default, nat_ty(), mk_goal(&m, &n2)))
            };
            // n=0: natMul (succ m) 0 ≡ 0 ; natAdd (natMul m 0) 0 ≡ natAdd 0 0 ≡ 0. rfl.
            let zero_case = eq_refl_nat(nat_zero());
            // n=S k: ih : natMul (succ m) k = natAdd (natMul m k) k.
            //   Goal inner (after peeling succ on both sides):
            //     natAdd (natMul (succ m) k) m = natAdd (natAdd (natMul m k) m) k.
            //   Sub ih → natAdd (natAdd (natMul m k) k) m ; then with P:=natMul m k
            //   prove (P+k)+m = (P+m)+k by assoc/comm. Overall congrArg succ of that.
            let succ_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (kid, k) = c.fresh_local(nat_ty());
                let ih_ty = mk_goal(&m, &k);
                let (ihid, ih) = c.fresh_local(ih_ty.clone());
                let p = nm(m.clone(), k.clone());
                // ihAddM : natAdd (natMul (succ m) k) m = natAdd (natAdd (natMul m k) k) m
                //   = congrArg (·+m) ih.
                let f_addm = Expr::lam(BinderInfo::Default, nat_ty(), na(Expr::bvar(0), m.clone()));
                let ih_add_m = congr_arg_nat(
                    nm(nat_succ(m.clone()), k.clone()),
                    na(p.clone(), k.clone()),
                    f_addm,
                    ih,
                );
                // rearr : (P+k)+m = (P+m)+k.
                //   a1 : (P+k)+m = P+(k+m)        [assoc P k m]
                let a1 = Expr::apps(
                    Expr::const_str(proof_names::NAT_ADD_ASSOC),
                    [p.clone(), k.clone(), m.clone()],
                );
                //   a2 : P+(k+m) = P+(m+k)        [congr (P+·) (comm k m)]
                let f_pl = Expr::lam(BinderInfo::Default, nat_ty(), na(p.clone(), Expr::bvar(0)));
                let a2 = congr_arg_nat(
                    na(k.clone(), m.clone()),
                    na(m.clone(), k.clone()),
                    f_pl,
                    Expr::apps(
                        Expr::const_str(proof_names::NAT_ADD_COMM),
                        [k.clone(), m.clone()],
                    ),
                );
                //   a3 : P+(m+k) = (P+m)+k        [symm (assoc P m k)]
                let a3 = eq_symm_nat(
                    na(na(p.clone(), m.clone()), k.clone()),
                    na(p.clone(), na(m.clone(), k.clone())),
                    Expr::apps(
                        Expr::const_str(proof_names::NAT_ADD_ASSOC),
                        [p.clone(), m.clone(), k.clone()],
                    ),
                );
                let a12 = eq_trans_nat(
                    na(na(p.clone(), k.clone()), m.clone()),
                    na(p.clone(), na(k.clone(), m.clone())),
                    na(p.clone(), na(m.clone(), k.clone())),
                    a1,
                    a2,
                );
                let rearr = eq_trans_nat(
                    na(na(p.clone(), k.clone()), m.clone()),
                    na(p.clone(), na(m.clone(), k.clone())),
                    na(na(p.clone(), m.clone()), k.clone()),
                    a12,
                    a3,
                );
                // inner : natAdd (natMul (succ m) k) m = (P+m)+k
                //   = trans ih_add_m rearr.
                let inner = eq_trans_nat(
                    na(nm(nat_succ(m.clone()), k.clone()), m.clone()),
                    na(na(p.clone(), k.clone()), m.clone()),
                    na(na(p.clone(), m.clone()), k.clone()),
                    ih_add_m,
                    rearr,
                );
                // body : congrArg succ inner.
                //   LHS succ (natAdd (natMul (succ m) k) m) ≡ natMul (succ m)(succ k).
                //   RHS succ ((P+m)+k) ≡ natAdd (natAdd (natMul m k) m)(succ k)
                //       ≡ natAdd (natMul m (succ k))(succ k).
                let body = congr_arg_nat(
                    na(nm(nat_succ(m.clone()), k.clone()), m.clone()),
                    na(na(p.clone(), m.clone()), k.clone()),
                    Expr::const_str("Nat.succ"),
                    inner,
                );
                let r = c.mk_lam(ihid, BinderInfo::Default, ih_ty, body);
                c.finish_child(c.mk_lam(kid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let inner = Expr::apps(nat_rec, [motive, zero_case, succ_case, n.clone()]);
            let e = b.mk_lam(nid, BinderInfo::Default, nat_ty(), inner);
            b.finish(b.mk_lam(mid, BinderInfo::Default, nat_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_MUL_SUCC_L),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natMulComm : (m n) -> Eq (natMul m n) (natMul n m)`. Induction on `n`,
    /// base `natMulZeroL`, step `natMulSuccL` + `congrArg succ`-style rewrite.
    fn register_nat_mul_comm(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_MUL_COMM))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_mul_zero_l()?;
        self.register_nat_mul_succ_l()?;
        let mk_goal =
            |m: &Expr, n: &Expr| eq_nat(nm(m.clone(), n.clone()), nm(n.clone(), m.clone()));
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (mid, m) = b.fresh_local(nat_ty());
            let (nid, n) = b.fresh_local(nat_ty());
            let e = b.mk_pi(nid, BinderInfo::Default, nat_ty(), mk_goal(&m, &n));
            b.finish(b.mk_pi(mid, BinderInfo::Default, nat_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (mid, m) = b.fresh_local(nat_ty());
            let (nid, n) = b.fresh_local(nat_ty());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (n2id, n2) = c.fresh_local(nat_ty());
                c.finish_child(c.mk_lam(n2id, BinderInfo::Default, nat_ty(), mk_goal(&m, &n2)))
            };
            // n=0: natMul m 0 ≡ 0 ; goal 0 = natMul 0 m. symm (natMulZeroL m).
            let zero_case = {
                let zl = Expr::app(Expr::const_str(proof_names::NAT_MUL_ZERO_L), m.clone());
                eq_symm_nat(nm(nat_zero(), m.clone()), nat_zero(), zl)
            };
            // n=S k: goal natMul m (S k) = natMul (S k) m.
            //   LHS ≡ natAdd (natMul m k) m.
            //   ih : natMul m k = natMul k m ⇒ congrArg (·+m) ih :
            //        natAdd (natMul m k) m = natAdd (natMul k m) m.
            //   natMulSuccL k m : natMul (S k) m = natAdd (natMul k m) m ⇒ symm.
            let succ_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (kid, k) = c.fresh_local(nat_ty());
                let ih_ty = mk_goal(&m, &k);
                let (ihid, ih) = c.fresh_local(ih_ty.clone());
                // step1 : natAdd (natMul m k) m = natAdd (natMul k m) m.
                let f_addm = Expr::lam(BinderInfo::Default, nat_ty(), na(Expr::bvar(0), m.clone()));
                let step1 = congr_arg_nat(
                    nm(m.clone(), k.clone()),
                    nm(k.clone(), m.clone()),
                    f_addm,
                    ih,
                );
                // sl : natMul (S k) m = natAdd (natMul k m) m.
                let sl = Expr::apps(
                    Expr::const_str(proof_names::NAT_MUL_SUCC_L),
                    [k.clone(), m.clone()],
                );
                // step2 : natAdd (natMul k m) m = natMul (S k) m.
                let step2 = eq_symm_nat(
                    nm(nat_succ(k.clone()), m.clone()),
                    na(nm(k.clone(), m.clone()), m.clone()),
                    sl,
                );
                // body : natAdd (natMul m k) m = natMul (S k) m  (≡ LHS natMul m (S k)).
                let body = eq_trans_nat(
                    na(nm(m.clone(), k.clone()), m.clone()),
                    na(nm(k.clone(), m.clone()), m.clone()),
                    nm(nat_succ(k.clone()), m.clone()),
                    step1,
                    step2,
                );
                let r = c.mk_lam(ihid, BinderInfo::Default, ih_ty, body);
                c.finish_child(c.mk_lam(kid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let inner = Expr::apps(nat_rec, [motive, zero_case, succ_case, n.clone()]);
            let e = b.mk_lam(nid, BinderInfo::Default, nat_ty(), inner);
            b.finish(b.mk_lam(mid, BinderInfo::Default, nat_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_MUL_COMM),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `natMulDistribR : (a b c) -> Eq (natMul (natAdd a b) c)`
    /// `(natAdd (natMul a c)(natMul b c))`. Induction on `c`. Step uses the
    /// 4-term `natAddReshuffle` (`(natMul(a+b)k)+(a+b) = ...`).
    fn register_nat_mul_distrib_r(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::NAT_MUL_DISTRIB_R))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_add_reshuffle()?;
        let mk_goal = |a: &Expr, b2: &Expr, c: &Expr| {
            eq_nat(
                nm(na(a.clone(), b2.clone()), c.clone()),
                na(nm(a.clone(), c.clone()), nm(b2.clone(), c.clone())),
            )
        };
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(nat_ty());
            let (bid, b2) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(nat_ty());
            let e = b.mk_pi(cid, BinderInfo::Default, nat_ty(), mk_goal(&a, &b2, &c));
            let e = b.mk_pi(bid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_pi(aid, BinderInfo::Default, nat_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(nat_ty());
            let (bid, b2) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(nat_ty());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (c2id, c2) = d.fresh_local(nat_ty());
                d.finish_child(d.mk_lam(c2id, BinderInfo::Default, nat_ty(), mk_goal(&a, &b2, &c2)))
            };
            // c=0: natMul (a+b) 0 ≡ 0 ; natAdd (natMul a 0)(natMul b 0) ≡ natAdd 0 0 ≡ 0. rfl.
            let zero_case = eq_refl_nat(nat_zero());
            // c=S k: LHS natMul (a+b)(S k) ≡ natAdd (natMul (a+b) k)(a+b).
            //   RHS natAdd (natMul a (S k))(natMul b (S k))
            //       ≡ natAdd (natAdd (natMul a k) a)(natAdd (natMul b k) b).
            //   ih : natMul (a+b) k = natAdd (natMul a k)(natMul b k).
            //   congrArg (·+(a+b)) ih :
            //     natAdd (natMul (a+b) k)(a+b)
            //       = natAdd (natAdd (natMul a k)(natMul b k))(natAdd a b).
            //   reshuffle (natMul a k)(natMul b k) a b :
            //     (Ak+Bk)+(a+b) = (Ak+a)+(Bk+b)  — exactly the RHS.
            let succ_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (kid, k) = d.fresh_local(nat_ty());
                let ih_ty = mk_goal(&a, &b2, &k);
                let (ihid, ih) = d.fresh_local(ih_ty.clone());
                let ak = nm(a.clone(), k.clone());
                let bk = nm(b2.clone(), k.clone());
                let ab = na(a.clone(), b2.clone());
                // step1 : natAdd (natMul (a+b) k)(a+b)
                //         = natAdd (natAdd Ak Bk)(a+b)   [congrArg (·+(a+b)) ih]
                let f_add_ab =
                    Expr::lam(BinderInfo::Default, nat_ty(), na(Expr::bvar(0), ab.clone()));
                let step1 = congr_arg_nat(
                    nm(ab.clone(), k.clone()),
                    na(ak.clone(), bk.clone()),
                    f_add_ab,
                    ih,
                );
                // step2 : (Ak+Bk)+(a+b) = (Ak+a)+(Bk+b)   [reshuffle Ak Bk a b]
                let step2 = Expr::apps(
                    Expr::const_str(proof_names::NAT_ADD_RESHUFFLE),
                    [ak.clone(), bk.clone(), a.clone(), b2.clone()],
                );
                // body : natAdd (natMul (a+b) k)(a+b) = (Ak+a)+(Bk+b)
                //   ≡ goal: LHS natMul (a+b)(S k) ; RHS natAdd (natMul a (S k))(natMul b (S k)).
                let body = eq_trans_nat(
                    na(nm(ab.clone(), k.clone()), ab.clone()),
                    na(na(ak.clone(), bk.clone()), ab.clone()),
                    na(na(ak.clone(), a.clone()), na(bk.clone(), b2.clone())),
                    step1,
                    step2,
                );
                let r = d.mk_lam(ihid, BinderInfo::Default, ih_ty, body);
                d.finish_child(d.mk_lam(kid, BinderInfo::Default, nat_ty(), r))
            };
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let inner = Expr::apps(nat_rec, [motive, zero_case, succ_case, c.clone()]);
            let e = b.mk_lam(cid, BinderInfo::Default, nat_ty(), inner);
            let e = b.mk_lam(bid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_lam(aid, BinderInfo::Default, nat_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::NAT_MUL_DISTRIB_R),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §11 Int equational structural tower (toward farkasChecks_sound) ──────

    /// Register the proved Int *equational* structural lemmas: `intEta`,
    /// `intAddZeroL`, `dotDistAdd`. All foundational (zero domain axioms). These
    /// are the genuine additive-structural half of the remaining obligation; the
    /// multiplicative inequality `intMulNonnegMono` + the row/column folds remain
    /// the stated open obligation (see module note).
    ///
    /// # Errors
    /// Propagates any [`EnvError`] from declaration insertion / kernel checking.
    pub fn init_farkas_structural(&mut self) -> Result<(), EnvError> {
        self.init_farkas_mul_tower()?;
        self.register_int_eta()?;
        self.register_int_add_zero_l()?;
        self.register_int_add_assoc()?;
        self.register_int_mul_distrib_r()?;
        Ok(())
    }

    /// `intEta : (i : Int) -> Eq (Int.mk (intPos i)(intNeg i)) i`. Structure-eta
    /// via `Int.rec`: at `i = mk p n`, `intPos`/`intNeg` reduce so the goal is
    /// `mk p n = mk p n` (`Eq.refl`).
    fn register_int_eta(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::INT_ETA))
            .is_some()
        {
            return Ok(());
        }
        let mk_goal = |i: &Expr| eq_int_(int_mk(int_pos(i.clone()), int_neg(i.clone())), i.clone());
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (iid, i) = b.fresh_local(int_ty());
            b.finish(b.mk_pi(iid, BinderInfo::Default, int_ty(), mk_goal(&i)))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (iid, i) = b.fresh_local(int_ty());
            // motive : fun i => Eq Int (mk (intPos i)(intNeg i)) i  (a Prop ⇒ Int.rec level 0).
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(int_ty());
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, int_ty(), mk_goal(&m)))
            };
            // mk_case : fun (p n : Nat) => Eq.refl (mk p n)
            //   goal at mk p n ≡ Eq (mk p n)(mk p n).
            let mk_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (pid, p) = c.fresh_local(nat_ty());
                let (nid, n) = c.fresh_local(nat_ty());
                let body = eq_refl_int(int_mk(p.clone(), n.clone()));
                let r = c.mk_lam(nid, BinderInfo::Default, nat_ty(), body);
                c.finish_child(c.mk_lam(pid, BinderInfo::Default, nat_ty(), r))
            };
            let int_rec = Expr::const_(
                Name::from_string(&format!("{}.rec", names::INT)),
                vec![Level::zero()],
            );
            let body = Expr::apps(int_rec, [motive, mk_case, i.clone()]);
            b.finish(b.mk_lam(iid, BinderInfo::Default, int_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::INT_ETA),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `intAddZeroL : (w : Int) -> Eq (intAdd int0 w) w`.
    /// `intAdd int0 w ≡ mk (natAdd 0 w.pos)(natAdd 0 w.neg)`; `natAddZeroL` on each
    /// component rewrites to `mk w.pos w.neg`, then `intEta` closes to `w`.
    fn register_int_add_zero_l(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::INT_ADD_ZERO_L))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_add_zero_l()?;
        self.register_int_eta()?;
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (wid, w) = b.fresh_local(int_ty());
            let goal = eq_int_(iadd(int0(), w.clone()), w.clone());
            b.finish(b.mk_pi(wid, BinderInfo::Default, int_ty(), goal))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (wid, w) = b.fresh_local(int_ty());
            let wp = int_pos(w.clone());
            let wn = int_neg(w.clone());
            // intAdd int0 w ≡ mk (natAdd 0 wp)(natAdd 0 wn).
            // step_p : mk (natAdd 0 wp)(natAdd 0 wn) = mk wp (natAdd 0 wn)
            //   = congrArg (fun z => mk z (natAdd 0 wn)) (natAddZeroL wp).
            let zl_p = Expr::app(Expr::const_str(proof_names::NAT_ADD_ZERO_L), wp.clone());
            let f_p = Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                int_mk(Expr::bvar(0), na(nat_zero(), wn.clone())),
            );
            let step_p = congr_arg_nat_int(na(nat_zero(), wp.clone()), wp.clone(), f_p, zl_p);
            // step_n : mk wp (natAdd 0 wn) = mk wp wn
            //   = congrArg (fun z => mk wp z) (natAddZeroL wn).
            let zl_n = Expr::app(Expr::const_str(proof_names::NAT_ADD_ZERO_L), wn.clone());
            let f_n = Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                int_mk(wp.clone(), Expr::bvar(0)),
            );
            let step_n = congr_arg_nat_int(na(nat_zero(), wn.clone()), wn.clone(), f_n, zl_n);
            // eta : mk wp wn = w.
            let eta = Expr::app(Expr::const_str(proof_names::INT_ETA), w.clone());
            // chain: mk (0+wp)(0+wn) -> mk wp (0+wn) -> mk wp wn -> w.
            let t1 = eq_trans_int(
                int_mk(na(nat_zero(), wp.clone()), na(nat_zero(), wn.clone())),
                int_mk(wp.clone(), na(nat_zero(), wn.clone())),
                int_mk(wp.clone(), wn.clone()),
                step_p,
                step_n,
            );
            let body = eq_trans_int(
                int_mk(na(nat_zero(), wp.clone()), na(nat_zero(), wn.clone())),
                int_mk(wp.clone(), wn.clone()),
                w.clone(),
                t1,
                eta,
            );
            b.finish(b.mk_lam(wid, BinderInfo::Default, int_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::INT_ADD_ZERO_L),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `intAddAssoc : (a b c : Int) -> Eq (intAdd (intAdd a b) c)`
    /// `(intAdd a (intAdd b c))`. Componentwise `natAddAssoc` on `pos`/`neg`
    /// (chained via `congrArg (mk · ·)`).
    fn register_int_add_assoc(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::INT_ADD_ASSOC))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_add_assoc()?;
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(int_ty());
            let (bid, bb) = b.fresh_local(int_ty());
            let (cid, c) = b.fresh_local(int_ty());
            let goal = eq_int_(
                iadd(iadd(a.clone(), bb.clone()), c.clone()),
                iadd(a.clone(), iadd(bb.clone(), c.clone())),
            );
            let e = b.mk_pi(cid, BinderInfo::Default, int_ty(), goal);
            let e = b.mk_pi(bid, BinderInfo::Default, int_ty(), e);
            b.finish(b.mk_pi(aid, BinderInfo::Default, int_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(int_ty());
            let (bid, bb) = b.fresh_local(int_ty());
            let (cid, c) = b.fresh_local(int_ty());
            let ap = int_pos(a.clone());
            let an = int_neg(a.clone());
            let bp = int_pos(bb.clone());
            let bn = int_neg(bb.clone());
            let cp = int_pos(c.clone());
            let cn = int_neg(c.clone());
            // LHS intAdd (intAdd a b) c ≡ mk ((ap+bp)+cp) ((an+bn)+cn).
            // RHS intAdd a (intAdd b c) ≡ mk (ap+(bp+cp)) (an+(bn+cn)).
            let assoc = |x: Expr, y: Expr, z: Expr| {
                Expr::apps(Expr::const_str(proof_names::NAT_ADD_ASSOC), [x, y, z])
            };
            // step_p : mk ((ap+bp)+cp)((an+bn)+cn) = mk (ap+(bp+cp))((an+bn)+cn).
            let f_p = Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                int_mk(Expr::bvar(0), na(na(an.clone(), bn.clone()), cn.clone())),
            );
            let step_p = congr_arg_nat_int(
                na(na(ap.clone(), bp.clone()), cp.clone()),
                na(ap.clone(), na(bp.clone(), cp.clone())),
                f_p,
                assoc(ap.clone(), bp.clone(), cp.clone()),
            );
            // step_n : mk (ap+(bp+cp))((an+bn)+cn) = mk (ap+(bp+cp))(an+(bn+cn)).
            let f_n = Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                int_mk(na(ap.clone(), na(bp.clone(), cp.clone())), Expr::bvar(0)),
            );
            let step_n = congr_arg_nat_int(
                na(na(an.clone(), bn.clone()), cn.clone()),
                na(an.clone(), na(bn.clone(), cn.clone())),
                f_n,
                assoc(an.clone(), bn.clone(), cn.clone()),
            );
            let body = eq_trans_int(
                int_mk(
                    na(na(ap.clone(), bp.clone()), cp.clone()),
                    na(na(an.clone(), bn.clone()), cn.clone()),
                ),
                int_mk(
                    na(ap.clone(), na(bp.clone(), cp.clone())),
                    na(na(an.clone(), bn.clone()), cn.clone()),
                ),
                int_mk(
                    na(ap.clone(), na(bp.clone(), cp.clone())),
                    na(an.clone(), na(bn.clone(), cn.clone())),
                ),
                step_p,
                step_n,
            );
            let r = b.mk_lam(cid, BinderInfo::Default, int_ty(), body);
            let r = b.mk_lam(bid, BinderInfo::Default, int_ty(), r);
            b.finish(b.mk_lam(aid, BinderInfo::Default, int_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::INT_ADD_ASSOC),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `intMulDistribR : (a b z : Int) -> Eq (intMul (intAdd a b) z)`
    /// `(intAdd (intMul a z)(intMul b z))`. Componentwise: each of the `pos`/`neg`
    /// components is a `natMulDistribR` expansion followed by a `natAddReshuffle`
    /// to match the additive grouping on the RHS.
    fn register_int_mul_distrib_r(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(proof_names::INT_MUL_DISTRIB_R))
            .is_some()
        {
            return Ok(());
        }
        self.register_nat_mul_distrib_r()?;
        self.register_nat_add_reshuffle()?;
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(int_ty());
            let (bid, bb) = b.fresh_local(int_ty());
            let (zid, z) = b.fresh_local(int_ty());
            let goal = eq_int_(
                imul(iadd(a.clone(), bb.clone()), z.clone()),
                iadd(imul(a.clone(), z.clone()), imul(bb.clone(), z.clone())),
            );
            let e = b.mk_pi(zid, BinderInfo::Default, int_ty(), goal);
            let e = b.mk_pi(bid, BinderInfo::Default, int_ty(), e);
            b.finish(b.mk_pi(aid, BinderInfo::Default, int_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(int_ty());
            let (bid, bb) = b.fresh_local(int_ty());
            let (zid, z) = b.fresh_local(int_ty());
            let ap = int_pos(a.clone());
            let an = int_neg(a.clone());
            let bp = int_pos(bb.clone());
            let bn = int_neg(bb.clone());
            let zp = int_pos(z.clone());
            let zn = int_neg(z.clone());
            let distrib = |x: Expr, y: Expr, w: Expr| {
                Expr::apps(Expr::const_str(proof_names::NAT_MUL_DISTRIB_R), [x, y, w])
            };
            let reshuffle = |p: Expr, q: Expr, r: Expr, s: Expr| {
                Expr::apps(
                    Expr::const_str(proof_names::NAT_ADD_RESHUFFLE),
                    [p, q, r, s],
                )
            };
            // LHS intMul (intAdd a b) z ≡
            //   mk ((ap+bp)*zp + (an+bn)*zn) ((ap+bp)*zn + (an+bn)*zp).
            // RHS intAdd (intMul a z)(intMul b z) ≡
            //   mk ((ap*zp+an*zn)+(bp*zp+bn*zn)) ((ap*zn+an*zp)+(bp*zn+bn*zp)).
            // Build a proof per component:
            //   pos: (ap+bp)*zp + (an+bn)*zn
            //        = (ap*zp+bp*zp) + (an*zn+bn*zn)        [distribR twice, congr]
            //        = (ap*zp+an*zn) + (bp*zp+bn*zn).       [reshuffle]
            //   neg analogous with zn/zp swapped on the second factor.
            //
            // Helper: prove one component equality
            //   ((X+Y)*P) + ((U+V)*Q)
            //     = (X*P+U*Q) + (Y*P+V*Q)
            // for atoms X,Y,U,V and factors P,Q. Steps:
            //   d1 : (X+Y)*P = X*P + Y*P            [distribR X Y P]
            //   d2 : (U+V)*Q = U*Q + V*Q            [distribR U V Q]
            //   c1 : LHS = (X*P+Y*P) + (U+V)*Q      [congr (·+(U+V)*Q) d1]
            //   c2 : (X*P+Y*P)+(U+V)*Q = (X*P+Y*P)+(U*Q+V*Q)  [congr ((X*P+Y*P)+·) d2]
            //   rs : (X*P+Y*P)+(U*Q+V*Q) = (X*P+U*Q)+(Y*P+V*Q)  [reshuffle (X*P)(Y*P)(U*Q)(V*Q)]
            //   component = trans c1 (trans c2 rs).
            let component = |x: Expr, y: Expr, u: Expr, v: Expr, p: Expr, q: Expr| -> Expr {
                let xp = nm(x.clone(), p.clone());
                let yp = nm(y.clone(), p.clone());
                let uq = nm(u.clone(), q.clone());
                let vq = nm(v.clone(), q.clone());
                let d1 = distrib(x.clone(), y.clone(), p.clone());
                let d2 = distrib(u.clone(), v.clone(), q.clone());
                // c1 : ((X+Y)*P)+((U+V)*Q) = (X*P+Y*P)+((U+V)*Q)
                let f_c1 = Expr::lam(
                    BinderInfo::Default,
                    nat_ty(),
                    na(Expr::bvar(0), nm(na(u.clone(), v.clone()), q.clone())),
                );
                let c1 = congr_arg_nat(
                    nm(na(x.clone(), y.clone()), p.clone()),
                    na(xp.clone(), yp.clone()),
                    f_c1,
                    d1,
                );
                // c2 : (X*P+Y*P)+((U+V)*Q) = (X*P+Y*P)+(U*Q+V*Q)
                let f_c2 = Expr::lam(
                    BinderInfo::Default,
                    nat_ty(),
                    na(na(xp.clone(), yp.clone()), Expr::bvar(0)),
                );
                let c2 = congr_arg_nat(
                    nm(na(u.clone(), v.clone()), q.clone()),
                    na(uq.clone(), vq.clone()),
                    f_c2,
                    d2,
                );
                // rs : (X*P+Y*P)+(U*Q+V*Q) = (X*P+U*Q)+(Y*P+V*Q)
                let rs = reshuffle(xp.clone(), yp.clone(), uq.clone(), vq.clone());
                // xyp_uvq := ((X+Y)*P) + ((U+V)*Q) — the true LHS of c1 (≡ component LHS).
                let xyp_uvq = na(
                    nm(na(x.clone(), y.clone()), p.clone()),
                    nm(na(u.clone(), v.clone()), q.clone()),
                );
                let c12 = eq_trans_nat(
                    xyp_uvq.clone(),
                    na(
                        na(xp.clone(), yp.clone()),
                        nm(na(u.clone(), v.clone()), q.clone()),
                    ),
                    na(na(xp.clone(), yp.clone()), na(uq.clone(), vq.clone())),
                    c1,
                    c2,
                );
                eq_trans_nat(
                    xyp_uvq,
                    na(na(xp.clone(), yp.clone()), na(uq.clone(), vq.clone())),
                    na(na(xp.clone(), uq.clone()), na(yp.clone(), vq.clone())),
                    c12,
                    rs,
                )
            };
            // pos component: X=ap,Y=bp,U=an,V=bn,P=zp,Q=zn.
            let pos_eq = component(
                ap.clone(),
                bp.clone(),
                an.clone(),
                bn.clone(),
                zp.clone(),
                zn.clone(),
            );
            // neg component: X=ap,Y=bp,U=an,V=bn,P=zn,Q=zp.
            let neg_eq = component(
                ap.clone(),
                bp.clone(),
                an.clone(),
                bn.clone(),
                zn.clone(),
                zp.clone(),
            );
            // Assemble the two component equalities into the mk-equality.
            // LHS pos atom: (ap+bp)*zp + (an+bn)*zn ; RHS pos atom:
            //   (ap*zp+an*zn)+(bp*zp+bn*zn).
            let lhs_pos = na(
                nm(na(ap.clone(), bp.clone()), zp.clone()),
                nm(na(an.clone(), bn.clone()), zn.clone()),
            );
            let rhs_pos = na(
                na(nm(ap.clone(), zp.clone()), nm(an.clone(), zn.clone())),
                na(nm(bp.clone(), zp.clone()), nm(bn.clone(), zn.clone())),
            );
            let lhs_neg = na(
                nm(na(ap.clone(), bp.clone()), zn.clone()),
                nm(na(an.clone(), bn.clone()), zp.clone()),
            );
            let rhs_neg = na(
                na(nm(ap.clone(), zn.clone()), nm(an.clone(), zp.clone())),
                na(nm(bp.clone(), zn.clone()), nm(bn.clone(), zp.clone())),
            );
            // Assemble via Eq.subst rewrites on the difference-pair components,
            // starting from refl at the LHS form (mk lhs_pos lhs_neg ≡
            // imul (iadd a b) z). This avoids congrArg-redex typing fragility.
            //   base : Eq (mk lhs_pos lhs_neg)(mk lhs_pos lhs_neg)  [refl]
            let base = eq_refl_int(int_mk(lhs_pos.clone(), lhs_neg.clone()));
            //   r1 : Eq (mk lhs_pos lhs_neg)(mk rhs_pos lhs_neg)
            //     motive z := Eq (mk lhs_pos lhs_neg)(mk z lhs_neg) ; subst lhs_pos↦rhs_pos.
            let motive_p = {
                let inner = eq_int_(
                    int_mk(lhs_pos.clone(), lhs_neg.clone()),
                    int_mk(Expr::bvar(0), lhs_neg.clone()),
                );
                Expr::lam(BinderInfo::Default, nat_ty(), inner)
            };
            let r1 = eq_subst_nat(motive_p, lhs_pos.clone(), rhs_pos.clone(), pos_eq, base);
            //   r2 : Eq (mk lhs_pos lhs_neg)(mk rhs_pos rhs_neg)
            //     motive z := Eq (mk lhs_pos lhs_neg)(mk rhs_pos z) ; subst lhs_neg↦rhs_neg.
            let motive_n = {
                let inner = eq_int_(
                    int_mk(lhs_pos.clone(), lhs_neg.clone()),
                    int_mk(rhs_pos.clone(), Expr::bvar(0)),
                );
                Expr::lam(BinderInfo::Default, nat_ty(), inner)
            };
            let body = eq_subst_nat(motive_n, lhs_neg.clone(), rhs_neg.clone(), neg_eq, r1);
            let r = b.mk_lam(zid, BinderInfo::Default, int_ty(), body);
            let r = b.mk_lam(bid, BinderInfo::Default, int_ty(), r);
            b.finish(b.mk_lam(aid, BinderInfo::Default, int_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(proof_names::INT_MUL_DISTRIB_R),
            level_params: vec![],
            type_,
            value,
        })
    }
}

/// The TYPE of the headline soundness bridge
/// `farkasChecks_sound : (rows)(bounds)(mults) ->`
/// `Eq (farkasChecks rows bounds mults) true -> Unsat rows bounds`.
///
/// This is a well-formed `Prop` (kernel-checkable) given
/// [`Environment::init_farkas_soundness`] has run. Exposed so callers / tests
/// can confirm the certificate STRUCTURE lives in clean's kernel even while the
/// multiplicative half of the *proof* (see the module-level status note) is the
/// stated remaining obligation.
pub fn farkas_checks_sound_type() -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rowsid, rows) = b.fresh_local(list_list_int());
    let (boundsid, bounds) = b.fresh_local(list_int());
    let (multsid, mults) = b.fresh_local(list_int());
    let checks = Expr::apps(
        Expr::const_str(names::FARKAS_CHECKS),
        [rows.clone(), bounds.clone(), mults.clone()],
    );
    let hyp = eq_bool_(checks, btrue());
    let unsat = Expr::apps(
        Expr::const_str(names::UNSAT),
        [rows.clone(), bounds.clone()],
    );
    let inner = Expr::arrow(hyp, unsat);
    let e = b.mk_pi(multsid, BinderInfo::Default, list_int(), inner);
    let e = b.mk_pi(boundsid, BinderInfo::Default, list_int(), e);
    b.finish(b.mk_pi(rowsid, BinderInfo::Default, list_list_int(), e))
}

// ── shared Prop/Eq helpers ─────────────────────────────────────────────────

/// `@Eq.{1} Bool x y`.
fn eq_bool_(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [bool_ty(), x, y],
    )
}
/// `@And a b`.
fn and_(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [a, b])
}
/// `@False.elim.{0} C h : C` (C : Prop).
fn false_elim_prop(c: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        [c, h],
    )
}
/// `@Eq.refl.{1} Bool x : Eq Bool x x`.
fn eq_refl_bool(x: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_ty(), x],
    )
}
/// `@Eq.symm.{1} Bool a b h : Eq b a`.
fn eq_symm_bool(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_ty(), a, b, h],
    )
}
/// `@Eq.{1} Nat x y`.
fn eq_nat(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat_ty(), x, y],
    )
}
/// `@Eq.refl.{1} Nat x : Eq Nat x x`.
fn eq_refl_nat(x: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat_ty(), x],
    )
}
/// `@Eq.symm.{1} Nat a b h : Eq b a`.
fn eq_symm_nat(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [nat_ty(), a, b, h],
    )
}
/// `@Eq.trans.{1} Nat a b c h1 h2 : Eq a c`.
fn eq_trans_nat(a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [nat_ty(), a, b, c, h1, h2],
    )
}
/// `@congrArg.{1,1} Nat Nat a1 a2 f h : Eq (f a1)(f a2)`.
fn congr_arg_nat(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1]),
        [nat_ty(), nat_ty(), a1, a2, f, h],
    )
}
/// `@Eq.{1} Int x y`.
fn eq_int_(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [int_ty(), x, y],
    )
}
/// `@Eq.refl.{1} Int x : Eq Int x x`.
fn eq_refl_int(x: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [int_ty(), x],
    )
}
/// `@Eq.trans.{1} Int a b c h1 h2 : Eq a c`.
fn eq_trans_int(a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [int_ty(), a, b, c, h1, h2],
    )
}
/// `@congrArg.{1,1} Nat Int a1 a2 f h : Eq (f a1)(f a2)` (`f : Nat -> Int`).
fn congr_arg_nat_int(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1]),
        [nat_ty(), int_ty(), a1, a2, f, h],
    )
}
/// `@Eq.subst.{1} Nat motive a b h m : motive b`.
fn eq_subst_nat(motive: Expr, a: Expr, b: Expr, h: Expr, m: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.subst"),
            vec![Level::succ(Level::zero())],
        ),
        [nat_ty(), motive, a, b, h, m],
    )
}

/// `htf : Eq Bool.true Bool.false → False` via `P x := Bool.rec (fun _ => Prop)
/// False True x`. (`P false = True`, `P true = False`; transport `True.intro`.)
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

#[cfg(test)]
#[path = "farkas_soundness_tests.rs"]
mod tests;
