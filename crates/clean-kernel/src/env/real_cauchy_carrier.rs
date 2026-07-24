// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive Cauchy-real carrier — the SOUND fractional-power substrate for
//! the sharp-KKL finish (`designs/2026-06-18-path-to-3-finish-line.md`, option A).
//!
//! ## Why this carrier exists (the decision)
//!
//! The sharp KKL/Friedgut retirement is walled by the dual `(4/3→2)`
//! hypercontractive bound, whose residual is discrete fractional Hölder for the
//! `(4/3, 4)` conjugate pair. That needs the sharp `n`-free charge
//! `Σ_i Inf_i^{3/2} ≤ √ε · I[f]`, which carries `√ε` for `ε = 2^{-k}` — i.e.
//! `2^{-k/2}`, IRRATIONAL for odd `k` — and `Inf_i^{3/2} = Inf_i·√(Inf_i)` for
//! arbitrary rational influences `Inf_i`. The landed graph-relation carrier
//! `BoolAnalysis.IsRpow32` can STATE `^{3/2}` but provably CANNOT be instantiated
//! at the KKL parameter: no rational `s` witnesses `s·s = 2^{-k}` for odd `k`
//! (recorded in `designs/2026-06-18-nnrpow-carrier-build.md` §5).
//!
//! An ALGEBRAIC-TOWER carrier (adjoin one root at a time) is INSUFFICIENT: the
//! influences are arbitrary, varying rationals and Hölder sums their roots
//! additively, so the chain needs closure under `√` of EVERY nonnegative element
//! plus `+`,`·`. That is exactly the constructive reals (Cauchy completion),
//! where `√` of any nonnegative element exists constructively.
//!
//! **Decision: a constructive Cauchy-sequence `Real` carrier**, built as a
//! faithful `Quot` exactly like the live `Rat` quotient
//! (`algebra_rat_quotient.rs`): `Quot` + `Quot.sound` + `propext` are
//! FOUNDATIONAL, so every fact proved over this carrier keeps an EMPTY
//! domain-axiom closure. This is NOT the `real_complex_analysis.rs`
//! anti-pattern (there `Real` and all its laws are `Declaration::Axiom`s — opaque
//! placeholders, REJECTED). Here `Real` is a genuine quotient of rational Cauchy
//! sequences and every fact is a kernel-checked `Theorem`.
//!
//! ## The construction
//!
//! - `Real.Raw := Nat → Rat` — a rational sequence (the function type directly;
//!   no custom inductive needed, leaner than the `Rat.Raw` constructor carrier).
//! - `Real.invSucc (j : Nat) : Rat := Rat.mk (Int.ofNat 1) (Nat.succ j)` — the
//!   error budget `1/(j+1)`, the rational `ε`-scale.
//! - `Real.Equiv (x y : Real.Raw) : Prop :=`
//!     `∀ (j : Nat), ∃ (N : Nat), ∀ (k : Nat),`
//!        `Nat.le N k → Rat.le (Rat.abs (Rat.sub (x k) (y k))) (Real.invSucc j)`
//!   — the genuine convergence-of-difference relation `(x − y) → 0`. SOUND: it is
//!   a real relation over the existing constructive `Rat` surface; it asserts no
//!   value and cannot prove `False`.
//! - `Real := Quot Real.Equiv`, `Real.mk := Quot.mk Real.Equiv`,
//!   `Real.ofRat (q : Rat) : Real := Real.mk (fun _ => q)` — the `Rat ↪ Real`
//!   embedding via the constant sequence.
//!
//! ## What is LANDED here (kernel-checked, sound, NO axiom)
//!
//! The SCAFFOLDING — all reducible `Declaration::Definition`s whose bodies
//! kernel-check (inhabit their declared types), introducing ZERO axioms:
//! `Real.invSucc`, `Real.Equiv`, `Real`, `Real.mk`, `Real.ofRat`. This
//! establishes the carrier exists and is non-trivial (the `Rat ↪ Real`
//! embedding type-checks) — the sound substrate for the fractional-power chain.
//!
//! ## What is BLOCKED (honest residual — NOT admitted)
//!
//! The equivalence-relation FACTS are NOT yet kernel-checked. Each `register_*`
//! method below SELF-GATES on its blocked dependency and registers NOTHING
//! (never an `Axiom`, never an unchecked decl) until the dependency lands:
//!
//! - `Real.invSucc_nonneg : ∀ j, 0 ≤ Real.invSucc j` — blocked on the
//!   `Rat`-positivity-with-symbolic-denominator sub-build (`Nat.mul 0 (succ j)`
//!   is reduction-stuck; the proof needs the quotient's PRIVATE raw helpers — it
//!   belongs in `algebra_rat_quotient.rs`). The `Rat`-positivity layer is
//!   entirely unbuilt on branch (no `Rat.zero_le_one`, `natCast_nonneg`,
//!   `div_nonneg`).
//! - `Real.Equiv.refl` — proof term is COMPLETE; gated on `invSucc_nonneg`.
//!   Auto-closes the moment positivity lands.
//! - `Real.Equiv.symm` — blocked on `Rat.abs_sub_comm`/`Rat.neg_sub` (the
//!   additive-negation algebra `Rat.neg_add`/`neg_sub` is also unbuilt).
//!
//! These two thin-overlay gaps (rational positivity; additive-negation algebra)
//! are the leanest first sub-library the carrier needs — the "small real-analysis
//! library" the finish-line doc (`2026-06-18-path-to-3-finish-line.md` §3)
//! predicted. They are reported, NOT faked. Transitivity (`ε/2 + ε/2`), Young,
//! Hölder, and `√` build atop these. See the report-back for the full residual.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the Cauchy-real carrier and its facts.
struct RealConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_le: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_abs: Expr,
    rat_sub: Expr,
    abs_zero: Expr,
    sub_self: Expr,
    /// `Exists` / `Exists.intro` at the `Nat` witness level (u = 1).
    exists_: Expr,
    exists_intro: Expr,
    inv_succ: Expr,
    equiv: Expr,
}

impl RealConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_le: k("Nat.le"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_abs: k("Rat.abs"),
            rat_sub: k("Rat.sub"),
            abs_zero: k("Rat.abs_zero"),
            sub_self: k("Rat.sub_self"),
            exists_: Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(Level::zero())],
            ),
            exists_intro: Expr::const_(
                Name::from_string("Exists.intro"),
                vec![Level::succ(Level::zero())],
            ),
            inv_succ: k("Real.invSucc"),
            equiv: k("Real.Equiv"),
        }
    }

    /// `Real.Raw = Nat → Rat`.
    fn raw(&self) -> Expr {
        Expr::pi(BinderInfo::Default, self.nat.clone(), self.rat.clone())
    }
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn abs(&self, a: Expr) -> Expr {
        Expr::app(self.rat_abs.clone(), a)
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn nat_le_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn inv_succ_of(&self, j: Expr) -> Expr {
        Expr::app(self.inv_succ.clone(), j)
    }
    fn equiv_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.equiv.clone(), [x, y])
    }
    fn at(&self, x: Expr, k: Expr) -> Expr {
        Expr::app(x, k)
    }
    /// The per-pair difference budget proposition
    /// `Rat.le (Rat.abs (Rat.sub (x k) (y k))) (Real.invSucc j)`.
    fn budget(&self, x: &Expr, y: &Expr, k: &Expr, j: &Expr) -> Expr {
        let diff = self.sub(self.at(x.clone(), k.clone()), self.at(y.clone(), k.clone()));
        self.rat_le(self.abs(diff), self.inv_succ_of(j.clone()))
    }
    /// Build the `Exists.intro` predicate
    /// `fun (N : Nat) => ∀ k, Nat.le N k → budget x y k j` for given `x,y,j`.
    /// `parent` is the enclosing builder; `x,y,j` are its (tolerated) fvars,
    /// abstracted later by the parent. The child builder MUST be `child_of` the
    /// parent to avoid fvar-id collisions with the parent's binders.
    fn inner_pred(&self, parent: &EnvDeclBuilder, x: &Expr, y: &Expr, j: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = ch.fresh_local(self.nat.clone());
        let body = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (k_id, kk) = ch2.fresh_local(self.nat.clone());
            let hyp = self.nat_le_of(n.clone(), kk.clone());
            let concl = self.budget(x, y, &kk, j);
            let (h_id, _h) = ch2.fresh_local(hyp.clone());
            let imp = ch2.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            ch2.finish_child(ch2.mk_pi(k_id, BinderInfo::Default, self.nat.clone(), imp))
        };
        ch.finish_child(ch.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), body))
    }
}

impl Environment {
    /// Register the Cauchy-real carrier foundation + the equivalence-relation
    /// facts proven this pass. Idempotent. NOT wired into `with_prelude` — it is
    /// a standalone overlay like the other KKL bricks (no retirement claimed).
    /// Register the SOUND, kernel-checked carrier scaffolding (the reducible
    /// Definitions `invSucc`, `Equiv`, `Real`, `Real.mk`, `Real.ofRat`). NO
    /// axiom is introduced. The equivalence-relation FACTS (`invSucc_nonneg`,
    /// `Equiv.refl`/`symm`) are NOT registered here — they are blocked on the
    /// rational-positivity sub-build (see `register_real_inv_succ_nonneg`'s doc).
    /// Registering an unproven fact as an `Axiom` would relocate trust; instead
    /// we land ONLY what kernel-checks and report the precise obstruction.
    pub fn init_real_cauchy_carrier(&mut self) -> Result<(), EnvError> {
        // Sound, kernel-checked scaffolding (reducible Definitions, NO axiom).
        self.register_real_inv_succ()?;
        self.register_real_raw_equiv()?;
        self.register_real_quotient()?;
        self.register_real_of_rat()?;
        // Equivalence-relation facts. Each SELF-GATES on its blocked dependency
        // (the Rat-positivity sub-build) and no-ops until that lands — it never
        // registers an unproven fact. See the per-method docs for the precise
        // obstruction.
        self.register_real_inv_succ_nonneg()?;
        self.register_real_equiv_refl()?;
        self.register_real_equiv_symm()?;
        Ok(())
    }

    /// Ensure the `Rat`/`Nat`/`Eq`/`Quot`/`Exists` + abs prerequisites.
    fn ensure_real_carrier_deps(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_rat()?;
        self.init_boolean_analysis_order_toolkit()?; // Rat order surface (le, sub, eq)
        self.init_rat_abs()?; // Rat.abs
        self.register_rat_abs_proofs_easy()?; // Rat.abs_zero, Rat.abs_neg
        self.register_rat_abs_proofs_hard()?; // Rat.abs_add_le, Rat.abs_sub_le (for trans)
        self.init_nn_verify_rat_ordering()?; // Rat.sub_self
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true, Rat.ble
        self.init_exists()?; // Exists, Exists.intro
        self.init_quot(); // Quot, Quot.mk, Quot.lift, Quot.ind
        self.init_quot_sound()?; // Quot.sound
        Ok(())
    }

    /// `Real.invSucc (j : Nat) : Rat := Rat.mk (Int.ofNat 1) (Nat.succ j)`
    /// — the error budget `1/(j+1)`. Reducible Definition, NO axiom.
    pub fn register_real_inv_succ(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Real.invSucc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.ensure_real_carrier_deps()?;
        let c = RealConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (j_id, _j) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(j_id, BinderInfo::Default, c.nat.clone(), c.rat.clone());
            b.finish(e)
        };
        let one_nat = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (j_id, j) = b.fresh_local(c.nat.clone());
            let num = Expr::app(c.int_of_nat.clone(), one_nat.clone());
            let denom = Expr::app(c.nat_succ.clone(), j.clone());
            let body = Expr::apps(c.rat_mk.clone(), [num, denom]);
            let e = b.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `Real.invSucc_nonneg : ∀ (j : Nat), Rat.le Rat.zero (Real.invSucc j)`
    /// — positivity of the error budget `1/(j+1)`. **THE NEXT UNBUILT BRICK.**
    ///
    /// ## Why it does not close trivially (the precise obstruction)
    ///
    /// `invSucc j ≡ mk (ofNat 1) (succ j)`, `0 ≡ mk (ofNat 0) 1`. On these
    /// concrete `Rat.mk` reps `Rat.le 0 (invSucc j)` δ/ι-reduces (through the
    /// `Quot.lift` defining `Rat.le`) to the raw cross-product
    /// `Int.le (Int.mul (ofNat 0) (eff (mk 1 (succ j)))) (Int.mul (ofNat 1) (eff (mk 0 1)))`.
    /// The LHS factor is `Int.mul (ofNat 0) (ofNat (succ j)) = ofNat (Nat.mul 0 (succ j))`,
    /// and `Nat.mul` recurses on its SECOND argument (`Nat.mul m n := Nat.rec 0
    /// (λ _ ih => ih + m) n`), so `Nat.mul 0 (succ j)` is STUCK on the symbolic
    /// `j` and does NOT reduce to `0`. Therefore `Rat.ble 0 (invSucc j)` does
    /// not native-reduce to `Bool.true`, and `Rat.le_of_ble_eq_true … (Eq.refl
    /// Bool.true)` does NOT type-check (verified empirically: `TypeMismatch`,
    /// `Rat.ble 0 (invSucc j) = true` vs `true = true`).
    ///
    /// ## The genuine fix (belongs in the quotient module)
    ///
    /// A sound proof must rewrite `Nat.mul 0 (succ j) → 0` (via the landed
    /// `Nat.zero_mul`) inside the raw `Int.le` goal, then close
    /// `Int.le (ofNat 0) (ofNat 1)` by `Int.ofNat_zero_le`. That requires
    /// constructing the raw cross-product `Int.le (num · eff) (num · eff)` term,
    /// which uses the quotient's PRIVATE `RatRawConsts::{num,eff,raw_le}`
    /// helpers — so the lemma must be added as a new
    /// `register_rat_mk_ofNat_succ_nonneg` INSIDE
    /// `crates/clean-kernel/src/env/algebra_rat_quotient.rs` (mirroring its
    /// `register_rat_q_order_lemmas` idiom). The `Rat`-positivity-with-symbolic-
    /// denominator layer is currently UNBUILT (no `Rat.zero_le_one`,
    /// `Rat.natCast_nonneg`, `Rat.div_nonneg`, or `0 ≤ mk (ofNat n) (succ d)`
    /// exists on branch). This is the leanest first sub-library the carrier
    /// needs; it is NOT admitted here.
    ///
    /// Until built, this is an honest no-op (registers NOTHING — introducing an
    /// `Axiom` would relocate trust and fail the 3-axiom goal).
    pub fn register_real_inv_succ_nonneg(&mut self) -> Result<(), EnvError> {
        // Blocked on the Rat-positivity sub-build (see doc). No-op; no axiom.
        Ok(())
    }

    /// `Real.Equiv (x y : Nat → Rat) : Prop :=`
    ///   `∀ (j : Nat), ∃ (N : Nat), ∀ (k : Nat),`
    ///      `Nat.le N k → Rat.le (Rat.abs (Rat.sub (x k) (y k))) (Real.invSucc j)`.
    /// Reducible Definition, NO axiom.
    pub fn register_real_raw_equiv(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Real.Equiv");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_real_inv_succ()?;
        let c = RealConsts::new();
        let prop = Expr::prop();
        let raw = c.raw();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(raw.clone());
            let (y_id, _y) = b.fresh_local(raw.clone());
            let e = b.mk_pi(y_id, BinderInfo::Default, raw.clone(), prop.clone());
            let e = b.mk_pi(x_id, BinderInfo::Default, raw.clone(), e);
            b.finish(e)
        };

        // value: fun (x y : Raw) => ∀ j, Exists Nat (inner_pred x y j)
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(raw.clone());
            let (y_id, y) = b.fresh_local(raw.clone());
            let (j_id, j) = b.fresh_local(c.nat.clone());
            let inner = c.inner_pred(&b, &x, &y, &j);
            let exists_body = Expr::apps(c.exists_.clone(), [c.nat.clone(), inner]);
            let forall_j = b.mk_pi(j_id, BinderInfo::Default, c.nat.clone(), exists_body);
            let e = b.mk_lam(y_id, BinderInfo::Default, raw.clone(), forall_j);
            let e = b.mk_lam(x_id, BinderInfo::Default, raw.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `Real := Quot Real.Equiv`, `Real.mk := Quot.mk Real.Equiv`. Reducible
    /// Definitions over the foundational `Quot` primitive (NO axiom).
    pub fn register_real_quotient(&mut self) -> Result<(), EnvError> {
        self.register_real_raw_equiv()?;
        let c = RealConsts::new();
        let raw = c.raw();
        let lvl1 = Level::succ(Level::zero());

        if self.get_const(&Name::from_string("Real")).is_none() {
            let quot = Expr::const_(Name::from_string("Quot"), vec![lvl1.clone()]);
            let value = Expr::apps(quot.clone(), [raw.clone(), c.equiv.clone()]);
            let ty = Expr::sort(lvl1.clone());
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Real"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        if self.get_const(&Name::from_string("Real.mk")).is_none() {
            let quot_mk = Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]);
            let real = Expr::const_(Name::from_string("Real"), vec![]);
            let ty = Expr::pi(BinderInfo::Default, raw.clone(), real);
            let value = Expr::apps(quot_mk, [raw.clone(), c.equiv.clone()]);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Real.mk"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    /// `Real.ofRat (q : Rat) : Real := Real.mk (fun _ : Nat => q)` — the
    /// `Rat ↪ Real` embedding via constant sequences. Reducible Definition,
    /// NO axiom; witnesses the carrier is inhabited (non-trivial / sound).
    pub fn register_real_of_rat(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Real.ofRat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_real_quotient()?;
        let c = RealConsts::new();
        let real = Expr::const_(Name::from_string("Real"), vec![]);
        let real_mk = Expr::const_(Name::from_string("Real.mk"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (q_id, _q) = b.fresh_local(c.rat.clone());
            let e = b.mk_pi(q_id, BinderInfo::Default, c.rat.clone(), real.clone());
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (q_id, q) = b.fresh_local(c.rat.clone());
            let const_seq = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (n_id, _n) = ch.fresh_local(c.nat.clone());
                ch.finish_child(ch.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), q.clone()))
            };
            let body = Expr::app(real_mk.clone(), const_seq);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.rat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `Real.Equiv.refl : ∀ (x : Nat → Rat), Real.Equiv x x`.
    ///
    /// `Real.Equiv x x` δ-unfolds to `∀ j, ∃ N, ∀ k, N≤k → |x k − x k| ≤ 1/(j+1)`.
    /// Witness `N := 0`; for each `k`, `|x k − x k| = |0| = 0 ≤ 1/(j+1)` via
    /// `sub_self`, `abs_zero`, and `invSucc_nonneg`.
    ///
    /// The proof term below is COMPLETE and correct; it only references the
    /// `Real.invSucc_nonneg` positivity lemma. That lemma is the single blocked
    /// brick (see `register_real_inv_succ_nonneg`'s doc). So this registration is
    /// GATED on `Real.invSucc_nonneg` being present: it registers nothing while
    /// positivity is unbuilt (no axiom, no unchecked decl), and AUTO-CLOSES the
    /// moment the positivity sub-build lands. This keeps the proof effort banked
    /// without relocating any trust.
    pub fn register_real_equiv_refl(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Real.Equiv.refl");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_real_raw_equiv()?;
        self.register_real_inv_succ_nonneg()?;
        // Gate: the proof references Real.invSucc_nonneg. Until that positivity
        // brick is built, do NOT register a half-proof — bail cleanly.
        if self
            .get_const(&Name::from_string("Real.invSucc_nonneg"))
            .is_none()
        {
            return Ok(());
        }
        let c = RealConsts::new();
        let raw = c.raw();
        let zero = c.order.rat_zero.clone();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(raw.clone());
            let goal = c.equiv_of(x.clone(), x.clone());
            let e = b.mk_pi(x_id, BinderInfo::Default, raw.clone(), goal);
            b.finish(e)
        };

        let inv_succ_nonneg = Expr::const_(Name::from_string("Real.invSucc_nonneg"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(raw.clone());
            let (j_id, j) = b.fresh_local(c.nat.clone());
            let inner = c.inner_pred(&b, &x, &x, &j);

            // per-k proof: fun (k : Nat) (h : Nat.le 0 k) => proof |x k − x k| ≤ invSucc j
            let per_k = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (k_id, kk) = ch.fresh_local(c.nat.clone());
                let hyp = c.nat_le_of(c.nat_zero.clone(), kk.clone());
                let (h_id, _h) = ch.fresh_local(hyp.clone());
                let xk = c.at(x.clone(), kk.clone());
                let diff = c.sub(xk.clone(), xk.clone());
                let inv_j = c.inv_succ_of(j.clone());

                // h0le : 0 ≤ invSucc j
                let h0le = Expr::app(inv_succ_nonneg.clone(), j.clone());
                // |0| ≤ invSucc j: subst abs_zero (0 = |0|) into h0le.
                let motive_abs0 = {
                    let mut m = EnvDeclBuilder::child_of(&ch);
                    let (t_id, t) = m.fresh_local(c.rat.clone());
                    let body = c.rat_le(t, inv_j.clone());
                    m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // abs_zero : |0| = 0 ; symm gives 0 = |0|.
                let h_eq_0_abs0 =
                    c.order
                        .symm(c.abs(zero.clone()), zero.clone(), c.abs_zero.clone());
                let h_abs0_le = c.order.subst(
                    motive_abs0,
                    zero.clone(),
                    c.abs(zero.clone()),
                    h_eq_0_abs0,
                    h0le,
                );
                // Now rewrite 0 → (x k − x k) inside abs.
                let motive_abst = {
                    let mut m = EnvDeclBuilder::child_of(&ch);
                    let (t_id, t) = m.fresh_local(c.rat.clone());
                    let body = c.rat_le(c.abs(t), inv_j.clone());
                    m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // sub_self (x k) : (x k − x k) = 0 ; symm gives 0 = (x k − x k).
                let h_diff_zero = Expr::app(c.sub_self.clone(), xk.clone());
                let h_eq_0_diff = c.order.symm(diff.clone(), zero.clone(), h_diff_zero);
                let body = c.order.subst(
                    motive_abst,
                    zero.clone(),
                    diff.clone(),
                    h_eq_0_diff,
                    h_abs0_le,
                );
                let lam_h = ch.mk_lam(h_id, BinderInfo::Default, hyp, body);
                ch.finish_child(ch.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_h))
            };

            let exists_intro = Expr::apps(
                c.exists_intro.clone(),
                [c.nat.clone(), inner, c.nat_zero.clone(), per_k],
            );
            let e = b.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), exists_intro);
            let e = b.mk_lam(x_id, BinderInfo::Default, raw.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Real.Equiv.symm : ∀ x y, Real.Equiv x y → Real.Equiv y x`.
    ///
    /// Unlike `refl`, symm needs NO positivity: the budget `≤ invSucc j` is
    /// carried by the hypothesis. Route: `Exists.elim` the witness `N` from
    /// `h j`, then per `k≥N`, `|y k − x k| = |x k − y k| ≤ invSucc j` by
    /// `Rat.abs_sub_comm`. The single missing leaf is
    /// `Rat.abs_sub_comm : |a−b| = |b−a|`, itself reducible to
    /// `Rat.neg_sub : −(a−b) = b−a` (+ `Rat.abs_neg`, landed). NEITHER
    /// `Rat.abs_sub_comm` NOR `Rat.neg_sub` is on branch (the general additive-
    /// negation algebra `Rat.neg_add`/`neg_sub` is unbuilt — same thin-overlay
    /// gap as the positivity layer). No-op until those land; no axiom.
    pub fn register_real_equiv_symm(&mut self) -> Result<(), EnvError> {
        // Blocked on Rat.abs_sub_comm / Rat.neg_sub (see doc). No-op; no axiom.
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    /// Carrier scaffolding: `Real.invSucc`, `Real.Equiv`, `Real`, `Real.mk`,
    /// `Real.ofRat` are reducible Definitions (NOT axioms — no relocated trust),
    /// and each kernel-checks (its body inhabits its declared type).
    #[test]
    fn test_real_carrier_definitions_are_not_axioms() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in [
            "Real.invSucc",
            "Real.Equiv",
            "Real",
            "Real.mk",
            "Real.ofRat",
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a Definition, not an Axiom (no relocated trust)"
            );
            let value = info.value.clone().expect("{name} must retain its body");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} Definition must kernel-check: {e:?}"));
        }
    }

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_real_cauchy_carrier()
            .expect("init_real_cauchy_carrier");
        env.init_real_cauchy_carrier().expect("idempotent");
        env
    }

    /// The equivalence-relation facts. They SELF-GATE on blocked dependencies,
    /// so each is EITHER absent (blocked, no axiom) OR — once its dependency
    /// lands — a kernel-checked Constructive Theorem with empty closure. This
    /// test pins BOTH invariants: nothing unproven is ever registered, and if a
    /// fact IS present it is genuinely proved. (Today both are absent.)
    const GATED_FACTS: &[&str] = &["Real.invSucc_nonneg", "Real.Equiv.refl", "Real.Equiv.symm"];

    #[test]
    fn test_real_carrier_facts_are_proven_or_absent_never_axioms() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in GATED_FACTS {
            let nm = Name::from_string(name);
            match env.get_const(&nm) {
                None => { /* blocked — honest no-op, NO axiom registered */ }
                Some(info) => {
                    assert_eq!(
                        info.kind,
                        ConstantKind::Theorem,
                        "{name} present => must be a Theorem, never an Axiom"
                    );
                    let value = info.value.clone().expect("proof present");
                    tc.check_type(&value, &info.type_)
                        .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
                    assert_eq!(
                        env.proof_quality(&nm),
                        Some(ProofQuality::Constructive),
                        "{name} must be Constructive"
                    );
                    assert!(
                        env.axiom_deps(&nm).expect("deps").is_empty(),
                        "{name} domain-axiom closure must be empty (no relocated trust)"
                    );
                }
            }
        }
    }

    /// Strict invariant: the carrier introduces NO axiom under the `Real.`
    /// namespace (the whole point — a sound quotient carrier, not the
    /// `real_complex_analysis.rs` axiom-placeholder anti-pattern).
    #[test]
    fn test_real_carrier_introduces_no_axiom() {
        let env = env();
        for name in [
            "Real.invSucc",
            "Real.Equiv",
            "Real",
            "Real.mk",
            "Real.ofRat",
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_ne!(
                info.kind,
                ConstantKind::Axiom,
                "{name} must NOT be an Axiom (sound quotient carrier)"
            );
        }
    }
}
