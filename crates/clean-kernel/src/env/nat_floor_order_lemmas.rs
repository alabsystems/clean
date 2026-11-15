// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The elementary `Nat` floor that real Rust→Lean conversions keep hitting.
//!
//! Three independent efforts (the Trust `as nat` contract lift, the z4
//! pseudo-Boolean `saturate_sound` proof, and the a3d kernel conversion) each
//! stalled on the SAME missing elementary facts — not on hard automation. This
//! module supplies the arithmetic half of that floor as real kernel-checked
//! `Declaration::Theorem`s (NO `sorry`, NO new axiom):
//!
//! ```text
//! Nat.le_add_left           : ∀ (n m : Nat), n ≤ m + n
//! Nat.le_mul_of_pos_right   : ∀ {m : Nat} (n : Nat), 0 < m → n ≤ n * m
//! Nat.mod_eq_of_lt          : ∀ {a b : Nat}, a < b → a % b = a
//! Nat.div_le_self           : ∀ (n k : Nat), n / k ≤ n
//! Nat.lt_of_mul_lt_mul_left : ∀ {a b c : Nat}, a * b < a * c → b < c
//! ```
//!
//! plus the private helper `Nat.floorAux.modCore_eq_of_lt`.
//!
//! # Statements are Lean's, exactly
//!
//! Each statement is pinned Lean v4.30.0-rc2's (`#check` under `pp.explicit`
//! / `pp.universes`): its binder kinds, its argument ORDER, and its class
//! notation (`@LE.le Nat instLENat`, `@HMul.hMul … (@instHMul Nat
//! instMulNat)`, `@HDiv.hDiv … (@instHDiv Nat Nat.instDiv)`, the numeral
//! `@OfNat.ofNat Nat 0 (instOfNatNat 0)`) — `lean_nat_spelling.rs` builds
//! them. Until 2026-09-30 they were stated over the BARE functions with every
//! argument explicit, "in this prelude's order", so a Lean-style call
//! (`Nat.le_mul_of_pos_right n h`, `Nat.mod_eq_of_lt h`) did not elaborate and
//! `data/prelude_collision_census.json` recorded each as a divergence. The
//! PROOFS are unchanged: each is built over the bare functions as before, and
//! the registered value is that term re-applied in Lean's argument order —
//! the kernel accepts it because every class-notation spelling δ-reduces to
//! the bare function it names. Callers in this crate pass arguments in Lean's
//! order (implicit ones explicitly, as every kernel term does).
//!
//! # Two lemmas were already proved and simply unreachable
//!
//! `Nat.lt_trans` and `Nat.lt_of_lt_of_le` are constructive theorems that have
//! existed for a long time (`order_nat_lt_trans_proof.rs`, `order_lemmas.rs`),
//! but the only initializers that register them — `init_nat_lt_trans`,
//! `init_nat_trans_lt_le_lt`, `init_smt_bridge_nat_order_lemmas` — are not on
//! `try_with_prelude`'s path. So `clean check` answered `Unknown identifier`
//! for both while their sibling `Nat.lt_of_le_of_lt` resolved. That is an
//! AVAILABILITY gap, not a proof gap, and it is closed in
//! `init_prelude_extended` by calling the two standalone `register_*` fns (not
//! the `init_*` fns, which would also build `Trans` instances the prelude does
//! not otherwise carry). `prelude_carries_both_mixed_transitivity_lemmas`
//! below pins it.
//!
//! # Why these proofs are short
//!
//! `Nat.div` and `Nat.mod` are GENUINE structural definitions here (fuel-based
//! `Nat.divCore` / `Nat.modCore`, see `data_types_nat.rs`), and
//! `data_types_nat_div_mod_lemmas.rs` already proves the euclidean identity
//! `Nat.div_add_mod : (a / n) * n + a % n = a` and the helper
//! `Nat.divmodAux.sub_zero_le : n - a = 0 → n ≤ a`. So:
//!
//! * `Nat.div_le_self` needs NO induction on `divCore`: split on the divisor,
//!   use `a / 0 ≡ 0`, and at `succ k` chain
//!   `q ≤ q * n ≤ q * n + a % n = a`.
//! * `Nat.mod_eq_of_lt` needs no induction hypothesis either: `modCore f a n`
//!   tests `n - a` with an inline `Nat.rec`, and `a < n` makes that test a
//!   `succ`, so BOTH fuel cases hand back `a` directly.
//!
//! # Axiom closure
//!
//! Every term below mentions only `Nat` recursors/constructors, `Eq`
//! built-ins, `False.elim`, and the already-constructive theorems
//! `Nat.le_trans`, `Nat.lt_irrefl`, `Nat.zero_le`, `Nat.zero_lt_succ`,
//! `Nat.add_comm`, `Nat.le_add_right`, `Nat.div_add_mod` and
//! `Nat.divmodAux.sub_zero_le`. None is a `Declaration::Axiom`, so each new
//! theorem has an empty `axiom_deps`.

use super::decl_builder::EnvDeclBuilder;
use super::lean_nat_spelling::LeanNat;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// The private helper this module registers under the `Nat.floorAux.`
/// namespace (the same convention `data_types_nat_div_mod_lemmas.rs` uses for
/// `Nat.divmodAux.`).
pub(super) const MODCORE_EQ_OF_LT: &str = "Nat.floorAux.modCore_eq_of_lt";

/// Kernel constants shared by the `Nat` floor proofs in this module and its
/// siblings (`nat_floor_min_lemmas`, `uint_floor_tonat_lemmas`).
///
/// Deliberately the same shape as `data_types_nat_div_mod_lemmas::Nat`: one
/// allocation per `init_*` call, no per-lemma re-spelling of `Expr::const_`.
pub(super) struct FloorConsts {
    pub(super) nat: Expr,
    pub(super) zero: Expr,
    pub(super) succ: Expr,
    pub(super) add: Expr,
    pub(super) mul: Expr,
    pub(super) sub: Expr,
    pub(super) le: Expr,
    pub(super) lt: Expr,
    /// `fun _ : Nat => Nat` — the `Nat.rec` motive for `Nat`-valued splits.
    nat_motive: Expr,
    /// `Nat.rec.{0}` (Prop motives) and `Nat.rec.{1}` (`Nat`-valued motives).
    rec0: Expr,
    rec1: Expr,
    eq: Expr,
    eq_refl: Expr,
    eq_subst: Expr,
    false_elim: Expr,
}

impl FloorConsts {
    pub(super) fn new() -> Self {
        let n = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let l1 = Level::succ(Level::zero());
        let nat = n("Nat");
        let nat_motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
        Self {
            zero: n("Nat.zero"),
            succ: n("Nat.succ"),
            add: n("Nat.add"),
            mul: n("Nat.mul"),
            sub: n("Nat.sub"),
            le: n("Nat.le"),
            lt: n("Nat.lt"),
            nat_motive,
            rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            rec1: Expr::const_(Name::from_string("Nat.rec"), vec![l1.clone()]),
            eq: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1]),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            nat,
        }
    }

    pub(super) fn const_(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }

    pub(super) fn succ_of(&self, x: Expr) -> Expr {
        Expr::app(self.succ.clone(), x)
    }
    pub(super) fn add_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.add.clone(), [a, b])
    }
    pub(super) fn mul_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul.clone(), [a, b])
    }
    pub(super) fn sub_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.sub.clone(), [a, b])
    }
    /// `@Nat.le a b : Prop`
    pub(super) fn le_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.le.clone(), [a, b])
    }
    /// `@Nat.lt a b : Prop` (defeq `Nat.le (succ a) b`)
    pub(super) fn lt_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.lt.clone(), [a, b])
    }
    /// `@Eq.{1} Nat lhs rhs : Prop`
    pub(super) fn eq_of(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.nat.clone(), lhs, rhs])
    }
    /// `@Eq.refl.{1} Nat x`
    pub(super) fn refl(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.nat.clone(), x])
    }
    /// `@Eq.subst.{1} Nat motive a b h h2 : motive b`
    pub(super) fn subst(&self, motive: Expr, a: Expr, b: Expr, h: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.nat.clone(), motive, a, b, h, h2],
        )
    }
    /// `@False.elim.{0} C h : C`
    pub(super) fn false_elim(&self, c: Expr, h: Expr) -> Expr {
        Expr::apps(self.false_elim.clone(), [c, h])
    }
    /// `@Nat.rec.{0} motive base step major` (Prop motive)
    pub(super) fn rec0(&self, motive: Expr, base: Expr, step: Expr, major: Expr) -> Expr {
        Expr::apps(self.rec0.clone(), [motive, base, step, major])
    }
    /// `@Nat.rec.{1} (fun _ => Nat) zcase scase major` — the inline
    /// `Nat`-valued case split `divCore` / `modCore` perform on `n - a`.
    pub(super) fn nat_rec_case(&self, zcase: Expr, scase: Expr, major: Expr) -> Expr {
        Expr::apps(
            self.rec1.clone(),
            [self.nat_motive.clone(), zcase, scase, major],
        )
    }
}

/// `dom → cod`, a NON-dependent arrow.
///
/// Built directly rather than through `EnvDeclBuilder::mk_pi` on purpose: a
/// child builder created to allocate a binder that nothing references hands
/// back an FVarId the PARENT will hand out again (`child_of` snapshots
/// `next_fvar` and the child's allocations never advance it). Both uses would
/// be closed, so nothing breaks today — but the shape is a trap, and a
/// non-dependent arrow needs no fresh variable at all. `cod` is built from
/// fvars and constants here, so it carries no loose `BVar` for the new binder
/// to capture.
fn arrow(dom: Expr, cod: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, dom, cod)
}

impl Environment {
    /// Register the elementary `Nat` arithmetic floor
    /// (`Nat.le_add_left`, `Nat.le_mul_of_pos_right`, `Nat.mod_eq_of_lt`,
    /// `Nat.div_le_self`) as kernel-checked theorems.
    ///
    /// Idempotent per-lemma (each site is `get_const`-guarded).
    ///
    /// # Errors
    ///
    /// Propagates any `EnvError` from a dependency initializer or from
    /// `add_decl`'s kernel check of a proof term.
    pub(crate) fn init_nat_floor_order_lemmas(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate — the whole
        // family is stated over the import-gated `Nat.add/mul/sub/div/mod/
        // modCore` seeds (see `data_types_nat.rs::init_nat`), and
        // `Nat.div_add_mod` (which `Nat.div_le_self` cites) is itself withheld
        // in import mode because Clean's factor order diverges from Lean's.
        // The genuine lemmas import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_true_false()?;
        // `Nat.zero_lt_succ`, `Nat.succ_le_succ`, `Nat.le_refl`.
        self.init_nat_top_level_ordering()?;
        self.register_nat_le_trans_proof()?; // Nat.le_trans
        self.register_nat_lt_irrefl_theorem()?; // Nat.lt_irrefl
        self.register_nat_ble_le_lemmas()?; // Nat.zero_le
        self.register_nat_add_comm_proof()?; // Nat.add_comm
        self.register_nat_mul_le_mul_left_proof()?; // Nat.le_add_right, Nat.mul_le_mul_left
        self.register_nat_mul_left_cancel_succ_proof()?; // Nat.le_or_lt
        self.register_nat_lt_of_lt_of_le_proof()?; // Nat.lt_of_lt_of_le
        self.init_nat_div_mod_lemmas()?; // Nat.div_add_mod, Nat.divmodAux.sub_zero_le
                                         // `instHAdd` / `instHMul` / `instHDiv` / `instHMod`, `Nat.instDiv`,
                                         // `Nat.instMod` — the constants Lean's statements name.
        self.init_lean_arith_bridges()?;

        let c = FloorConsts::new();
        self.register_nat_le_add_left(&c)?;
        self.register_nat_le_mul_of_pos_right(&c)?;
        self.register_floor_modcore_eq_of_lt(&c)?;
        self.register_nat_mod_eq_of_lt(&c)?;
        self.register_nat_div_le_self(&c)?;
        self.register_nat_lt_of_mul_lt_mul_left(&c)?;
        Ok(())
    }

    /// `theorem Nat.lt_of_mul_lt_mul_left {a b c : Nat} (h : a * b < a * c) : b < c`
    /// (Lean's statement). The proof below is built over the bare functions
    /// with the multiplier LAST (`n n1 n2`, `n2 * n < n2 * n1 → n < n1`, the
    /// shape `Nat.mul_le_mul_left` composes with) and registered re-applied
    /// in Lean's order: `a := n2`, `b := n`, `c := n1`.
    ///
    /// Proof by trichotomy on `Nat.le_or_lt n1 n`: the `n1 ≤ n` arm gives
    /// `n2*n1 ≤ n2*n` (the neighbour), which with `h` makes `n2*n < n2*n`, and
    /// `Nat.lt_irrefl` closes it.
    fn register_nat_lt_of_mul_lt_mul_left(&mut self, c: &FloorConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_of_mul_lt_mul_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let or_rec = FloorConsts::const_("Or.rec");
        let or_const = FloorConsts::const_("Or");
        let le_or_lt = FloorConsts::const_("Nat.le_or_lt");
        let mul_le_mul_left = FloorConsts::const_("Nat.mul_le_mul_left");
        let lt_of_lt_of_le = FloorConsts::const_("Nat.lt_of_lt_of_le");
        let lt_irrefl = FloorConsts::const_("Nat.lt_irrefl");

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (n1_id, n1) = b.fresh_local(c.nat.clone());
        let (n2_id, n2) = b.fresh_local(c.nat.clone());
        let kn = c.mul_of(n2.clone(), n.clone());
        let kn1 = c.mul_of(n2.clone(), n1.clone());
        let h_ty = c.lt_of(kn.clone(), kn1.clone());
        let (h_id, h) = b.fresh_local(h_ty.clone());
        let goal = c.lt_of(n.clone(), n1.clone());

        // `Nat.le_or_lt n1 n : Or (Nat.le n1 n) (Nat.le (Nat.succ n) n1)`; the
        // right disjunct is spelled `Nat.lt n n1` here (reducibly the same).
        let left_prop = c.le_of(n1.clone(), n.clone());
        let right_prop = goal.clone();

        // The proof in the multiplier-last order, re-applied below.
        let value = {
            // motive : fun (_ : Or _ _) => Nat.lt n n1
            let or_motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let dom = Expr::apps(or_const.clone(), [left_prop.clone(), right_prop.clone()]);
                let (o_id, _o) = mb.fresh_local(dom.clone());
                mb.finish_child(mb.mk_lam(o_id, BinderInfo::Default, dom, goal.clone()))
            };
            // inl : n1 ≤ n is impossible under `h`.
            let case_inl = {
                let mut lb = EnvDeclBuilder::child_of(&b);
                let (hle_id, hle) = lb.fresh_local(left_prop.clone());
                // Nat.mul_le_mul_left n1 n n2 hle : Nat.le (n2*n1) (n2*n)
                let mono = Expr::apps(
                    mul_le_mul_left.clone(),
                    [n1.clone(), n.clone(), n2.clone(), hle],
                );
                // Nat.lt_of_lt_of_le (n2*n) (n2*n1) (n2*n) h mono : Nat.lt (n2*n) (n2*n)
                let self_lt = Expr::apps(
                    lt_of_lt_of_le.clone(),
                    [kn.clone(), kn1.clone(), kn.clone(), h.clone(), mono],
                );
                let falsity = Expr::apps(lt_irrefl.clone(), [kn.clone(), self_lt]);
                let body = c.false_elim(goal.clone(), falsity);
                lb.finish_child(lb.mk_lam(hle_id, BinderInfo::Default, left_prop.clone(), body))
            };
            // inr : exactly the goal.
            let case_inr = {
                let mut rb = EnvDeclBuilder::child_of(&b);
                let (hlt_id, hlt) = rb.fresh_local(right_prop.clone());
                rb.finish_child(rb.mk_lam(hlt_id, BinderInfo::Default, right_prop.clone(), hlt))
            };
            let major = Expr::apps(le_or_lt.clone(), [n1.clone(), n.clone()]);
            let body = Expr::apps(
                or_rec,
                [left_prop, right_prop, or_motive, case_inl, case_inr, major],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = b.mk_lam(n2_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n1_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // Lean's statement: `∀ {a b c : Nat}, a * b < a * c → b < c`.
        let mut lb = EnvDeclBuilder::new();
        let (a_id, a) = lb.fresh_local(LeanNat::nat());
        let (b_id, bb) = lb.fresh_local(LeanNat::nat());
        let (cc_id, cc) = lb.fresh_local(LeanNat::nat());
        let h_ty = LeanNat::lt(
            LeanNat::mul(a.clone(), bb.clone()),
            LeanNat::mul(a.clone(), cc.clone()),
        );
        let (h_id, h) = lb.fresh_local(h_ty.clone());
        let concl = LeanNat::lt(bb.clone(), cc.clone());
        let nat = LeanNat::nat();
        let lean_type = {
            let e = lb.mk_pi(h_id, BinderInfo::Default, h_ty.clone(), concl);
            let e = lb.mk_pi(cc_id, BinderInfo::Implicit, nat.clone(), e);
            let e = lb.mk_pi(b_id, BinderInfo::Implicit, nat.clone(), e);
            lb.mk_pi(a_id, BinderInfo::Implicit, nat.clone(), e)
        };
        let lean_value = {
            let body = Expr::apps(value, [bb, cc, a, h]);
            let e = lb.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = lb.mk_lam(cc_id, BinderInfo::Implicit, nat.clone(), e);
            let e = lb.mk_lam(b_id, BinderInfo::Implicit, nat.clone(), e);
            lb.mk_lam(a_id, BinderInfo::Implicit, nat, e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: lb.finish(lean_type),
            value: lb.finish(lean_value),
        })
    }

    /// `theorem Nat.le_add_left (n m : Nat) : n ≤ m + n` (Lean's statement;
    /// the proof is over the bare `Nat.le` / `Nat.add`, which the notation
    /// δ-reduces to).
    ///
    /// The mirror of the already-present `Nat.le_add_right`, transported
    /// across `Nat.add_comm`:
    ///
    /// ```text
    /// @Eq.subst Nat (fun x => Nat.le a x) (a + b) (b + a)
    ///   (Nat.add_comm a b) (Nat.le_add_right a b)
    /// ```
    fn register_nat_le_add_left(&mut self, c: &FloorConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_add_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let le_add_right = FloorConsts::const_("Nat.le_add_right");
        let add_comm = FloorConsts::const_("Nat.add_comm");

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bv_id, bv) = b.fresh_local(c.nat.clone());

        let type_ = {
            let concl = LeanNat::le(a.clone(), LeanNat::add(bv.clone(), a.clone()));
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive : fun (x : Nat) => Nat.le a x
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = mb.fresh_local(c.nat.clone());
            let body = c.le_of(a.clone(), x);
            mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body))
        };

        let value = {
            let h_le = Expr::apps(le_add_right, [a.clone(), bv.clone()]);
            let h_comm = Expr::apps(add_comm, [a.clone(), bv.clone()]);
            let body = c.subst(
                motive,
                c.add_of(a.clone(), bv.clone()),
                c.add_of(bv.clone(), a.clone()),
                h_comm,
                h_le,
            );
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem Nat.le_mul_of_pos_right {m : Nat} (n : Nat) (h : 0 < m) : n ≤ n * m`
    /// (Lean's statement). The proof is built as `(a m : Nat) → Nat.lt 0 m →
    /// Nat.le a (Nat.mul a m)` over the bare functions and registered
    /// re-applied in Lean's order.
    ///
    /// `Nat.mul a (succ k) ≡ Nat.add (Nat.mul a k) a` (ι on `Nat.mul`'s
    /// second argument), so the `succ` case IS `Nat.le_add_left a (a * k)`.
    /// The `zero` case is refuted by the hypothesis via `Nat.lt_irrefl`.
    fn register_nat_le_mul_of_pos_right(&mut self, c: &FloorConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_mul_of_pos_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let le_add_left = FloorConsts::const_("Nat.le_add_left");
        let lt_irrefl = FloorConsts::const_("Nat.lt_irrefl");

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let h_ty = c.lt_of(c.zero.clone(), m.clone());
        let (h_id, h) = b.fresh_local(h_ty.clone());

        // motive : fun (x : Nat) => Nat.lt 0 x → Nat.le a (Nat.mul a x)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = mb.fresh_local(c.nat.clone());
            let hyp = c.lt_of(c.zero.clone(), x.clone());
            let concl = c.le_of(a.clone(), c.mul_of(a.clone(), x.clone()));
            let pi = arrow(hyp, concl);
            mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), pi))
        };

        // zero minor: `Nat.lt 0 0` is `Nat.le 1 0`, refuted by `Nat.lt_irrefl 0`.
        let zcase = {
            let mut zb = EnvDeclBuilder::child_of(&b);
            let hyp = c.lt_of(c.zero.clone(), c.zero.clone());
            let (h0_id, h0) = zb.fresh_local(hyp.clone());
            let falsity = Expr::apps(lt_irrefl, [c.zero.clone(), h0]);
            let goal = c.le_of(a.clone(), c.mul_of(a.clone(), c.zero.clone()));
            let body = c.false_elim(goal, falsity);
            zb.finish_child(zb.mk_lam(h0_id, BinderInfo::Default, hyp, body))
        };

        // succ minor: `Nat.le_add_left a (a * k) : Nat.le a (a * k + a)`
        // and `Nat.mul a (succ k) ≡ Nat.add (Nat.mul a k) a`.
        let scase = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let ih_ty = arrow(
                c.lt_of(c.zero.clone(), k.clone()),
                c.le_of(a.clone(), c.mul_of(a.clone(), k.clone())),
            );
            let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
            let hyp = c.lt_of(c.zero.clone(), c.succ_of(k.clone()));
            let (hs_id, _hs) = sb.fresh_local(hyp.clone());
            let body = Expr::apps(le_add_left, [a.clone(), c.mul_of(a.clone(), k.clone())]);
            let lam = sb.mk_lam(hs_id, BinderInfo::Default, hyp, body);
            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
            sb.finish_child(sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam))
        };

        let value = {
            let rec = c.rec0(motive, zcase, scase, m.clone());
            let body = Expr::app(rec, h.clone());
            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // Lean's statement: `∀ {m : Nat} (n : Nat), 0 < m → n ≤ n * m`.
        let mut lb = EnvDeclBuilder::new();
        let nat = LeanNat::nat();
        let (m_id, m) = lb.fresh_local(nat.clone());
        let (n_id, n) = lb.fresh_local(nat.clone());
        let h_ty = LeanNat::lt(LeanNat::lit(0), m.clone());
        let (h_id, h) = lb.fresh_local(h_ty.clone());
        let lean_type = {
            let concl = LeanNat::le(n.clone(), LeanNat::mul(n.clone(), m.clone()));
            let e = lb.mk_pi(h_id, BinderInfo::Default, h_ty.clone(), concl);
            let e = lb.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
            lb.mk_pi(m_id, BinderInfo::Implicit, nat.clone(), e)
        };
        let lean_value = {
            let body = Expr::apps(value, [n, m, h]);
            let e = lb.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = lb.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
            lb.mk_lam(m_id, BinderInfo::Implicit, nat, e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: lb.finish(lean_type),
            value: lb.finish(lean_value),
        })
    }

    /// `theorem Nat.floorAux.modCore_eq_of_lt (f a n : Nat) (h : Nat.lt a n)
    ///   : @Eq Nat (Nat.modCore f a n) a`
    ///
    /// `Nat.modCore` is fuel-recursive:
    ///
    /// ```text
    /// modCore 0        a n = a
    /// modCore (succ f) a n = Nat.rec (fun _ => Nat) (modCore f (a-n) n) (fun _ _ => a) (n - a)
    /// ```
    ///
    /// Under `a < n` the test `n - a` is a `succ`, so the `succ`-fuel case
    /// takes the `else` arm and returns `a` too — the induction hypothesis is
    /// never used. The `n - a = 0` arm is refuted by
    /// `Nat.divmodAux.sub_zero_le` + `Nat.le_trans` + `Nat.lt_irrefl`.
    fn register_floor_modcore_eq_of_lt(&mut self, c: &FloorConsts) -> Result<(), EnvError> {
        let name = Name::from_string(MODCORE_EQ_OF_LT);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let modcore = FloorConsts::const_("Nat.modCore");
        let sub_zero_le = FloorConsts::const_("Nat.divmodAux.sub_zero_le");
        let le_trans = FloorConsts::const_("Nat.le_trans");
        let lt_irrefl = FloorConsts::const_("Nat.lt_irrefl");
        let modcore_of = |f: Expr, a: Expr, n: Expr| Expr::apps(modcore.clone(), [f, a, n]);

        let mut b = EnvDeclBuilder::new();
        let (f_id, f) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let h_ty = c.lt_of(a.clone(), n.clone());
        let (h_id, h) = b.fresh_local(h_ty.clone());

        let type_ = {
            let concl = c.eq_of(modcore_of(f.clone(), a.clone(), n.clone()), a.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty.clone(), concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive : fun (x : Nat) => @Eq Nat (Nat.modCore x a n) a
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = mb.fresh_local(c.nat.clone());
            let body = c.eq_of(modcore_of(x, a.clone(), n.clone()), a.clone());
            mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body))
        };

        // fuel 0: `Nat.modCore 0 a n ≡ a`.
        let base = c.refl(a.clone());

        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (fp_id, fp) = sb.fresh_local(c.nat.clone());
            let ih_ty = c.eq_of(modcore_of(fp.clone(), a.clone(), n.clone()), a.clone());
            let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());

            // The `Nat`-valued inline test `modCore (succ fp) a n` performs.
            let then_arm = modcore_of(fp.clone(), c.sub_of(a.clone(), n.clone()), n.clone());
            let else_arm = {
                let mut eb = EnvDeclBuilder::child_of(&sb);
                let (k_id, _k) = eb.fresh_local(c.nat.clone());
                let (kih_id, _kih) = eb.fresh_local(c.nat.clone());
                let lam = eb.mk_lam(kih_id, BinderInfo::Default, c.nat.clone(), a.clone());
                eb.finish_child(eb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam))
            };
            let test = c.sub_of(n.clone(), a.clone());
            let branch_at = |x: Expr| c.nat_rec_case(then_arm.clone(), else_arm.clone(), x);

            // inner motive : fun (x : Nat) =>
            //   @Eq Nat (n - a) x → @Eq Nat (branch_at x) a
            let inner_motive = {
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (x_id, x) = ib.fresh_local(c.nat.clone());
                let hyp = c.eq_of(test.clone(), x.clone());
                let concl = c.eq_of(branch_at(x.clone()), a.clone());
                let pi = arrow(hyp, concl);
                ib.finish_child(ib.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), pi))
            };

            // `n - a = 0` contradicts `a < n`.
            let inner_zero = {
                let mut zb = EnvDeclBuilder::child_of(&sb);
                let hyp = c.eq_of(test.clone(), c.zero.clone());
                let (he_id, he) = zb.fresh_local(hyp.clone());
                let n_le_a = Expr::apps(sub_zero_le.clone(), [n.clone(), a.clone(), he]);
                // Nat.le (succ a) a ≡ Nat.lt a a
                let contra = Expr::apps(
                    le_trans.clone(),
                    [
                        c.succ_of(a.clone()),
                        n.clone(),
                        a.clone(),
                        h.clone(),
                        n_le_a,
                    ],
                );
                let falsity = Expr::apps(lt_irrefl.clone(), [a.clone(), contra]);
                let goal = c.eq_of(branch_at(c.zero.clone()), a.clone());
                let body = c.false_elim(goal, falsity);
                zb.finish_child(zb.mk_lam(he_id, BinderInfo::Default, hyp, body))
            };

            // `n - a = succ m`: the inline test takes the `else` arm, which IS `a`.
            let inner_succ = {
                let mut nb = EnvDeclBuilder::child_of(&sb);
                let (m_id, m) = nb.fresh_local(c.nat.clone());
                let mih_ty = arrow(
                    c.eq_of(test.clone(), m.clone()),
                    c.eq_of(branch_at(m.clone()), a.clone()),
                );
                let (mih_id, _mih) = nb.fresh_local(mih_ty.clone());
                let hyp = c.eq_of(test.clone(), c.succ_of(m.clone()));
                let (he_id, _he) = nb.fresh_local(hyp.clone());
                let body = c.refl(a.clone());
                let lam = nb.mk_lam(he_id, BinderInfo::Default, hyp, body);
                let lam = nb.mk_lam(mih_id, BinderInfo::Default, mih_ty, lam);
                nb.finish_child(nb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam))
            };

            let inner = Expr::app(
                c.rec0(inner_motive, inner_zero, inner_succ, test.clone()),
                c.refl(test.clone()),
            );
            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, inner);
            sb.finish_child(sb.mk_lam(fp_id, BinderInfo::Default, c.nat.clone(), lam))
        };

        let value = {
            let body = c.rec0(motive, base, step, f.clone());
            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem Nat.mod_eq_of_lt {a b : Nat} (h : a < b) : a % b = a` (Lean's
    /// statement; same argument order as the proof, which is over the bare
    /// `Nat.lt` / `Nat.mod`).
    ///
    /// `Nat.mod a n ≡ Nat.modCore a a n` (fuel = `a`), so this is the helper
    /// above at `f := a`.
    fn register_nat_mod_eq_of_lt(&mut self, c: &FloorConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mod_eq_of_lt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let helper = FloorConsts::const_(MODCORE_EQ_OF_LT);

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let h_ty = LeanNat::lt(a.clone(), n.clone());
        let (h_id, h) = b.fresh_local(h_ty.clone());

        let type_ = {
            let concl = LeanNat::eq(LeanNat::modulo(a.clone(), n.clone()), a.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty.clone(), concl);
            let e = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let body = Expr::apps(helper, [a.clone(), a.clone(), n.clone(), h.clone()]);
            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem Nat.div_le_self (n k : Nat) : n / k ≤ n` (Lean's statement; the
    /// proof is over the bare `Nat.le` / `Nat.div`).
    ///
    /// Case split on the DIVISOR, not induction on `divCore`:
    ///
    /// * `b = 0`: `Nat.div a 0 ≡ 0`, closed by `Nat.zero_le a`.
    /// * `b = succ k`: with `q := a / b` and `r := a % b`,
    ///   `q ≤ q * b` (`Nat.le_mul_of_pos_right`, `0 < succ k`) and
    ///   `q * b ≤ q * b + r = a` (`Nat.le_add_right` transported across the
    ///   already-proved euclidean identity `Nat.div_add_mod`).
    fn register_nat_div_le_self(&mut self, c: &FloorConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.div_le_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nat_div = FloorConsts::const_("Nat.div");
        let nat_mod = FloorConsts::const_("Nat.mod");
        let zero_le = FloorConsts::const_("Nat.zero_le");
        let zero_lt_succ = FloorConsts::const_("Nat.zero_lt_succ");
        let le_add_right = FloorConsts::const_("Nat.le_add_right");
        let le_trans = FloorConsts::const_("Nat.le_trans");
        let le_mul_pos = FloorConsts::const_("Nat.le_mul_of_pos_right");
        let div_add_mod = FloorConsts::const_("Nat.div_add_mod");

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bv_id, bv) = b.fresh_local(c.nat.clone());
        let div_of = |x: Expr, y: Expr| Expr::apps(nat_div.clone(), [x, y]);
        let mod_of = |x: Expr, y: Expr| Expr::apps(nat_mod.clone(), [x, y]);

        let type_ = {
            let concl = LeanNat::le(LeanNat::div(a.clone(), bv.clone()), a.clone());
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive : fun (x : Nat) => Nat.le (Nat.div a x) a
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = mb.fresh_local(c.nat.clone());
            let body = c.le_of(div_of(a.clone(), x), a.clone());
            mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body))
        };

        // `Nat.div a 0 ≡ Nat.zero`.
        let zcase = Expr::app(zero_le, a.clone());

        let scase = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let ih_ty = c.le_of(div_of(a.clone(), k.clone()), a.clone());
            let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());

            let n = c.succ_of(k.clone());
            let q = div_of(a.clone(), n.clone());
            let r = mod_of(a.clone(), n.clone());
            let qn = c.mul_of(q.clone(), n.clone());
            let qn_plus_r = c.add_of(qn.clone(), r.clone());

            // h1 : q ≤ q * succ k — `@Nat.le_mul_of_pos_right (succ k) q _`
            // (Lean's order: the multiplier `{m}` first).
            let h1 = Expr::apps(
                le_mul_pos.clone(),
                [
                    n.clone(),
                    q.clone(),
                    Expr::app(zero_lt_succ.clone(), k.clone()),
                ],
            );
            // h2 : Nat.le (q * n) (q * n + r)
            let h2 = Expr::apps(le_add_right.clone(), [qn.clone(), r.clone()]);
            // hdm : @Eq Nat (q * n + r) a
            let hdm = Expr::apps(div_add_mod.clone(), [a.clone(), n.clone()]);
            // submotive : fun (x : Nat) => Nat.le (q * n) x
            let submotive = {
                let mut mb = EnvDeclBuilder::child_of(&sb);
                let (x_id, x) = mb.fresh_local(c.nat.clone());
                let body = c.le_of(qn.clone(), x);
                mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // h3 : Nat.le (q * n) a
            let h3 = c.subst(submotive, qn_plus_r, a.clone(), hdm, h2);
            let body = Expr::apps(le_trans.clone(), [q, qn, a.clone(), h1, h3]);

            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
            sb.finish_child(sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam))
        };

        let value = {
            let body = c.rec0(motive, zcase, scase, bv.clone());
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ConstantKind;
    use crate::tc::TypeChecker;

    /// The `Nat` numeral `succ^k zero`.
    fn numeral(c: &FloorConsts, k: u32) -> Expr {
        let mut e = c.zero.clone();
        for _ in 0..k {
            e = c.succ_of(e);
        }
        e
    }

    /// Every lemma this module adds is in the DEFAULT prelude, is a
    /// `Declaration::Theorem` that kept its proof value, and rests on no axiom.
    ///
    /// This is the positive form of "no `sorry`, no new axiom": an empty
    /// `axiom_deps` is a statement about the whole transitive closure, not the
    /// absence of a warning.
    #[test]
    fn nat_floor_order_lemmas_are_axiom_free_theorems_in_the_prelude() {
        let env = Environment::with_prelude();
        for short in [
            "Nat.le_add_left",
            "Nat.le_mul_of_pos_right",
            "Nat.mod_eq_of_lt",
            "Nat.div_le_self",
            "Nat.lt_of_mul_lt_mul_left",
            MODCORE_EQ_OF_LT,
        ] {
            let name = Name::from_string(short);
            let info = env
                .get_const(&name)
                .unwrap_or_else(|| panic!("{short} must be in the default prelude"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{short} must be a Theorem"
            );
            assert!(info.value.is_some(), "{short} must retain its proof value");
            let deps = env
                .axiom_deps(&name)
                .unwrap_or_else(|| panic!("{short}: axiom_deps None"));
            assert!(deps.is_empty(), "{short} rests on {deps:?}");
        }
    }

    /// `Nat.lt_of_lt_of_le` was a kernel-checked theorem that the PRELUDE never
    /// registered (only `init_nat_trans_lt_le_lt` did, and nothing in
    /// `try_with_prelude` calls it), so `clean check` answered
    /// `Unknown identifier` for it while its mirror `Nat.lt_of_le_of_lt`
    /// resolved. Pin the fix: both are present, as Theorems.
    #[test]
    fn prelude_carries_both_mixed_transitivity_lemmas() {
        let env = Environment::with_prelude();
        for short in ["Nat.lt_of_lt_of_le", "Nat.lt_of_le_of_lt", "Nat.lt_trans"] {
            let info = env
                .get_const(&Name::from_string(short))
                .unwrap_or_else(|| panic!("{short} must be in the default prelude"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{short} must be a Theorem"
            );
        }
    }

    /// ANTI-VACUITY: a ground instance of `Nat.mod_eq_of_lt` checks against the
    /// explicit statement `@Eq Nat (Nat.mod 2 5) 2`, with the `2 < 5` witness
    /// spelled out. A lemma that only type-checks in the abstract proves
    /// nothing about use.
    #[test]
    fn nat_mod_eq_of_lt_ground_instance_checks() {
        let env = Environment::with_prelude();
        let c = FloorConsts::new();
        let n2 = numeral(&c, 2);
        let n5 = numeral(&c, 5);
        let nat_mod = FloorConsts::const_("Nat.mod");
        let stmt = c.eq_of(Expr::apps(nat_mod, [n2.clone(), n5.clone()]), n2.clone());
        // 2 < 5 is `Nat.le 3 5`: `Nat.le.step 3 4 (Nat.le.step 3 3 (Nat.le.refl 3))`.
        let le_refl = FloorConsts::const_("Nat.le.refl");
        let le_step = FloorConsts::const_("Nat.le.step");
        let n3 = numeral(&c, 3);
        let n4 = numeral(&c, 4);
        let h = Expr::apps(
            le_step.clone(),
            [
                n3.clone(),
                n4,
                Expr::apps(le_step, [n3.clone(), n3.clone(), Expr::app(le_refl, n3)]),
            ],
        );
        let proof = Expr::apps(FloorConsts::const_("Nat.mod_eq_of_lt"), [n2, n5, h]);
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&proof, &stmt)
            .expect("Nat.mod_eq_of_lt 2 5 (2<5) must check against `Nat.mod 2 5 = 2`");
    }

    /// ANTI-VACUITY: `Nat.div_le_self` at a ground pair, and at the divisor
    /// `0` — the branch the `Nat.rec` zero case covers and the one a
    /// `divCore` induction would have had to special-case.
    #[test]
    fn nat_div_le_self_ground_instances_check() {
        let env = Environment::with_prelude();
        let c = FloorConsts::new();
        let nat_div = FloorConsts::const_("Nat.div");
        let tc = TypeChecker::with_mode(&env, env.mode());
        for (a, b) in [(7u32, 3u32), (7, 0), (0, 3)] {
            let na = numeral(&c, a);
            let nb = numeral(&c, b);
            let stmt = c.le_of(
                Expr::apps(nat_div.clone(), [na.clone(), nb.clone()]),
                na.clone(),
            );
            let proof = Expr::apps(FloorConsts::const_("Nat.div_le_self"), [na, nb]);
            tc.check_type(&proof, &stmt)
                .unwrap_or_else(|e| panic!("Nat.div_le_self {a} {b} failed: {e:?}"));
        }
    }

    /// ANTI-VACUITY for `Nat.le_mul_of_pos_right`: `3 ≤ 3 * 4`, with the
    /// `0 < 4` witness supplied — in Lean's argument order, the multiplier
    /// `{m}` first.
    #[test]
    fn nat_le_mul_of_pos_right_ground_instance_checks() {
        let env = Environment::with_prelude();
        let c = FloorConsts::new();
        let n3 = numeral(&c, 3);
        let n4 = numeral(&c, 4);
        let stmt = c.le_of(n3.clone(), c.mul_of(n3.clone(), n4.clone()));
        let pos = Expr::app(FloorConsts::const_("Nat.zero_lt_succ"), numeral(&c, 3));
        let proof = Expr::apps(
            FloorConsts::const_("Nat.le_mul_of_pos_right"),
            [n4, n3, pos],
        );
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&proof, &stmt)
            .expect("Nat.le_mul_of_pos_right 3 4 (0<4) must check against `3 <= 3 * 4`");
    }

    /// The import-verification prelude does NOT gain these: they are stated
    /// over the import-gated `Nat.div`/`Nat.mod`/`Nat.modCore` seeds, so the
    /// genuine Lean lemmas must be free to import in their place.
    #[test]
    fn import_prelude_withholds_the_floor() {
        let env = Environment::try_with_prelude_for_import().expect("import prelude must build");
        for short in [
            "Nat.mod_eq_of_lt",
            "Nat.div_le_self",
            "Nat.lt_of_mul_lt_mul_left",
            MODCORE_EQ_OF_LT,
        ] {
            assert!(
                env.get_const(&Name::from_string(short)).is_none(),
                "{short} must NOT be seeded in the import prelude"
            );
        }
    }
}
