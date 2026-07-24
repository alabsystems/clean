// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generic *Boolean-valued model* layer for the resolution-soundness semantics.
//!
//! # What this is
//!
//! [`crate::resolution_soundness`] defines a *model* as a literal-truth predicate
//! `Holds : Nat → Prop` that is **total** (`resConsistent`) and **exclusive**
//! (`resExclusive`). To *apply* `Clean.Res.Unsat` (the model-theoretic
//! unsatisfiability of a clause set) one must EXHIBIT such a `Holds` together with
//! proofs of those two side conditions.
//!
//! This module builds the canonical such model from an arbitrary **Boolean
//! assignment** `f : Nat → Bool` (one bit per *variable*), matching the literal
//! encoding `Clean.Res.encode_lit` uses (`literal = 2·var + polarity`):
//!
//!   * `boolModelLit f l := if oddp l then ¬(f (half l)) else f (half l)` — the
//!     truth value of the *literal* `l` (even `2v` = positive var `v` → `f v`;
//!     odd `2v+1` = negative var `v` → `¬(f v)`).
//!   * `boolModel f := fun l => Eq (boolModelLit f l) Bool.true` — the `Nat → Prop`
//!     model itself.
//!
//! ## What is PROVED (every one a kernel `Theorem`, closure ⊆ FOUNDATIONAL_AXIOMS)
//!
//!   * `boolModelLitNeg : (f) (l) → Eq (boolModelLit f (litNeg l)) (Bool.not (boolModelLit f l))`
//!     — flipping the literal polarity (`litNeg`) flips its truth value. The single
//!     load-bearing fact; proved via the auxiliary `halfOddLitNeg` 2-step induction.
//!   * `boolModelConsistent : (f) → resConsistent (boolModel f)` — totality, an
//!     immediate `boolEm`-style case split given `boolModelLitNeg`.
//!   * `boolModelExclusive : (f) → resExclusive (boolModel f)` — exclusivity, an
//!     immediate `litClash`-style contradiction given `boolModelLitNeg`.
//!
//! Together these let a consumer discharge the `resConsistent`/`resExclusive`
//! obligations of `Unsat` for the canonical Boolean model FOR FREE, leaving only
//! the `allSat` obligation (clause-by-clause satisfaction) to establish.
//!
//! `half`/`oddp` are honest reducible `Nat → Nat` / `Nat → Bool` `Definition`s
//! (`half(2v)=half(2v+1)=v`, `oddp(2v)=false`, `oddp(2v+1)=true`).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::name::Name;
use crate::resolution_check::names as rnames;
use crate::resolution_soundness::names as snames;
use crate::{BinderInfo, Declaration, EnvError, Environment, Expr, Level};

/// Names of the declarations the Boolean-model layer registers.
pub mod names {
    /// `Clean.Res.oddp : Nat → Bool` — parity (`oddp (2v+r) = r`).
    pub const ODDP: &str = "Clean.Res.oddp";
    /// `Clean.Res.half : Nat → Nat` — `half (2v+r) = v`.
    pub const HALF: &str = "Clean.Res.half";
    /// `Clean.Res.boolModelLit : (Nat → Bool) → Nat → Bool`.
    pub const BOOL_MODEL_LIT: &str = "Clean.Res.boolModelLit";
    /// `Clean.Res.boolModel : (Nat → Bool) → Nat → Prop`.
    pub const BOOL_MODEL: &str = "Clean.Res.boolModel";
    /// PROVED `Clean.Res.halfOddLitNeg` — the 2-step parity/half induction helper.
    pub const HALF_ODD_LIT_NEG: &str = "Clean.Res.halfOddLitNeg";
    /// PROVED `Clean.Res.boolModelLitNeg` — `litNeg` flips the literal's value.
    pub const BOOL_MODEL_LIT_NEG: &str = "Clean.Res.boolModelLitNeg";
    /// PROVED `Clean.Res.boolModelConsistent` — model totality.
    pub const BOOL_MODEL_CONSISTENT: &str = "Clean.Res.boolModelConsistent";
    /// PROVED `Clean.Res.boolModelExclusive` — model exclusivity.
    pub const BOOL_MODEL_EXCLUSIVE: &str = "Clean.Res.boolModelExclusive";
}

// ── small shared Expr helpers ──────────────────────────────────────────────────

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
fn bnot(x: Expr) -> Expr {
    Expr::app(Expr::const_str("Bool.not"), x)
}
fn nat_zero() -> Expr {
    Expr::const_str("Nat.zero")
}
fn nat_succ(x: Expr) -> Expr {
    Expr::app(Expr::const_str("Nat.succ"), x)
}
fn nat_to_bool_ty() -> Expr {
    Expr::arrow(nat_ty(), bool_ty())
}
fn lit_neg(l: Expr) -> Expr {
    Expr::app(Expr::const_str(rnames::LIT_NEG), l)
}
fn half(l: Expr) -> Expr {
    Expr::app(Expr::const_str(names::HALF), l)
}
fn oddp(l: Expr) -> Expr {
    Expr::app(Expr::const_str(names::ODDP), l)
}
fn u1() -> Level {
    Level::succ(Level::zero())
}
fn eq_at(u: Level, ty: Expr, x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![u]), [ty, x, y])
}
fn eq_nat(x: Expr, y: Expr) -> Expr {
    eq_at(u1(), nat_ty(), x, y)
}
fn eq_bool(x: Expr, y: Expr) -> Expr {
    eq_at(u1(), bool_ty(), x, y)
}
fn eq_refl_at(u: Level, ty: Expr, x: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![u]), [ty, x])
}
fn eq_refl_nat(x: Expr) -> Expr {
    eq_refl_at(u1(), nat_ty(), x)
}
fn eq_refl_bool(x: Expr) -> Expr {
    eq_refl_at(u1(), bool_ty(), x)
}
fn and_t(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [a, b])
}
fn and_intro(a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [a, b, ha, hb],
    )
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
/// `boolModelLit f l`.
fn bml(f: &Expr, l: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::BOOL_MODEL_LIT), [f.clone(), l])
}
/// `Eq Bool.true Bool.false → False`, transported `True.intro`.
fn tf_to_false(htf: Expr) -> Expr {
    let p = {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![u1()]);
        let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), Expr::prop());
        let body = Expr::apps(
            bool_rec,
            [
                inner_motive,
                Expr::const_str("False"),
                Expr::const_str("True"),
                Expr::bvar(0),
            ],
        );
        Expr::lam(BinderInfo::Default, bool_ty(), body)
    };
    let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![u1()]);
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

impl Environment {
    /// Register the generic Boolean-model layer (`oddp`/`half`/`boolModelLit`/
    /// `boolModel` definitions + the consistency/exclusivity model theorems).
    ///
    /// Idempotent. Assumes [`Environment::init_resolution_soundness`] has run (it
    /// supplies `litNeg`, `resConsistent`, `resExclusive`); initializes it if not.
    ///
    /// # Errors
    /// Propagates any [`EnvError`] from declaration insertion / kernel checking.
    pub fn init_bool_model(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::BOOL_MODEL_CONSISTENT))
            .is_some()
        {
            return Ok(());
        }
        self.init_resolution_soundness()?;
        self.init_or()?;
        self.init_and()?;
        self.init_true_false()?;
        self.register_oddp()?;
        self.register_half()?;
        self.register_bool_model_lit()?;
        self.register_bool_model()?;
        self.register_half_odd_lit_neg()?;
        self.register_bool_model_lit_neg()?;
        self.register_bool_model_consistent()?;
        self.register_bool_model_exclusive()?;
        Ok(())
    }

    // ── §1 oddp / half / boolModelLit / boolModel definitions ──────────────────

    /// `oddp l := Nat.rec false (fun _ ih => Bool.not ih) l`.
    fn register_oddp(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(names::ODDP)).is_some() {
            return Ok(());
        }
        // Nat.rec (motive := fun _ => Bool) false (fun p ih => not ih) l
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (lid, l) = b.fresh_local(nat_ty());
            let motive = Expr::lam(BinderInfo::Default, nat_ty(), bool_ty());
            // succ case: fun (p : Nat) (ih : Bool) => Bool.not ih
            let succ_case = Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                Expr::lam(BinderInfo::Default, bool_ty(), bnot(Expr::bvar(0))),
            );
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![u1()]);
            let body = Expr::apps(nat_rec, [motive, bfalse(), succ_case, l]);
            b.finish(b.mk_lam(lid, BinderInfo::Default, nat_ty(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(names::ODDP),
            level_params: vec![],
            type_: nat_to_bool_ty(),
            value,
            is_reducible: true,
        })
    }

    /// `half l := H l Bool.false` where `H : Nat → Bool → Nat`,
    /// `H l false = half l`, `H l true = half (succ l)` (parallel-pair recursion,
    /// same trick as `litNeg`):
    ///   `H 0       = fun s => Bool.rec 0 0 s`
    ///   `H (succ p) = fun s => Bool.rec (H p true) (Nat.succ (H p false)) s`.
    fn register_half(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(names::HALF)).is_some() {
            return Ok(());
        }
        let g_carrier = Expr::arrow(bool_ty(), nat_ty()); // Bool → Nat
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![u1()]);
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![u1()]);
        // motive : fun (_ : Nat) => Bool → Nat
        let motive = Expr::lam(BinderInfo::Default, nat_ty(), g_carrier.clone());
        // zero case : fun (s : Bool) => Bool.rec (fun _ => Nat) 0 0 s
        let zero_case = {
            let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), nat_ty());
            let body = Expr::apps(
                bool_rec.clone(),
                [inner_motive, nat_zero(), nat_zero(), Expr::bvar(0)],
            );
            Expr::lam(BinderInfo::Default, bool_ty(), body)
        };
        // succ case : fun (p : Nat) (ih : Bool → Nat) (s : Bool) =>
        //   Bool.rec (ih true) (Nat.succ (ih false)) s
        let succ_case = {
            // bvars: s=0, ih=1, p=2
            let ih = Expr::bvar(1);
            let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), nat_ty());
            let ih_true = Expr::app(ih.clone(), btrue());
            let succ_ih_false = nat_succ(Expr::app(ih, bfalse()));
            let body = Expr::apps(
                bool_rec,
                [inner_motive, ih_true, succ_ih_false, Expr::bvar(0)],
            );
            Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                Expr::lam(
                    BinderInfo::Default,
                    g_carrier.clone(),
                    Expr::lam(BinderInfo::Default, bool_ty(), body),
                ),
            )
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (lid, l) = b.fresh_local(nat_ty());
            let g = Expr::apps(nat_rec, [motive, zero_case, succ_case, l]);
            let body = Expr::app(g, bfalse());
            b.finish(b.mk_lam(lid, BinderInfo::Default, nat_ty(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(names::HALF),
            level_params: vec![],
            type_: Expr::arrow(nat_ty(), nat_ty()),
            value,
            is_reducible: true,
        })
    }

    /// `boolModelLit f l := Bool.rec (f (half l)) (Bool.not (f (half l))) (oddp l)`.
    fn register_bool_model_lit(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::BOOL_MODEL_LIT))
            .is_some()
        {
            return Ok(());
        }
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (fid, f) = b.fresh_local(nat_to_bool_ty());
            let (lid, l) = b.fresh_local(nat_ty());
            let fhl = Expr::app(f.clone(), half(l.clone()));
            // Bool.rec (motive := fun _ => Bool) (f (half l)) (not (f (half l))) (oddp l)
            let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), bool_ty());
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![u1()]);
            let body = Expr::apps(
                bool_rec,
                [inner_motive, fhl.clone(), bnot(fhl), oddp(l.clone())],
            );
            let e = b.mk_lam(lid, BinderInfo::Default, nat_ty(), body);
            b.finish(b.mk_lam(fid, BinderInfo::Default, nat_to_bool_ty(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(names::BOOL_MODEL_LIT),
            level_params: vec![],
            type_: Expr::arrow(nat_to_bool_ty(), Expr::arrow(nat_ty(), bool_ty())),
            value,
            is_reducible: true,
        })
    }

    /// `boolModel f := fun (l : Nat) => Eq (boolModelLit f l) Bool.true`.
    fn register_bool_model(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::BOOL_MODEL))
            .is_some()
        {
            return Ok(());
        }
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (fid, f) = b.fresh_local(nat_to_bool_ty());
            let inner = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (lid, l) = c.fresh_local(nat_ty());
                let body = eq_bool(bml(&f, l), btrue());
                c.finish_child(c.mk_lam(lid, BinderInfo::Default, nat_ty(), body))
            };
            b.finish(b.mk_lam(fid, BinderInfo::Default, nat_to_bool_ty(), inner))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(names::BOOL_MODEL),
            level_params: vec![],
            type_: Expr::arrow(nat_to_bool_ty(), Expr::arrow(nat_ty(), Expr::prop())),
            value,
            is_reducible: true,
        })
    }

    // ── §2 halfOddLitNeg : the 2-step parity/half induction ────────────────────

    /// `halfOddLitNeg : (l : Nat) → Q l` where
    ///   `Q l := And (Eq (half (litNeg l)) (half l))`
    ///          `(And (Eq (oddp (litNeg l)) (Bool.not (oddp l)))`
    ///          `(And (Eq (half (litNeg (succ l))) (half (succ l)))`
    ///          `(Eq (oddp (litNeg (succ l))) (Bool.not (oddp (succ l))))))`.
    ///
    /// `Nat.rec` on `l`. Base `Q 0` (covers `l=0` and `l=1`) reduces to four `rfl`s
    /// (`litNeg 0 = 1`, `litNeg 1 = 0`, `litNeg 2 = 3`, `half`/`oddp` reduce). Step
    /// `Q (succ p)` reuses `Q p`'s third/fourth conjuncts directly for `succ p`, and
    /// derives the `succ (succ p)` conjuncts by `congrArg` over the reductions
    /// `litNeg (succ (succ x)) = succ (succ (litNeg x))`,
    /// `half (succ (succ x)) = succ (half x)`, `oddp (succ (succ x)) = oddp x`.
    fn register_half_odd_lit_neg(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::HALF_ODD_LIT_NEG))
            .is_some()
        {
            return Ok(());
        }
        // Conjunct prop builders.
        let c_half = |x: Expr| eq_nat(half(lit_neg(x.clone())), half(x));
        let c_odd = |x: Expr| eq_bool(oddp(lit_neg(x.clone())), bnot(oddp(x)));
        let q_of = |x: Expr| {
            let sx = nat_succ(x.clone());
            and_t(
                c_half(x.clone()),
                and_t(c_odd(x.clone()), and_t(c_half(sx.clone()), c_odd(sx))),
            )
        };

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (lid, l) = b.fresh_local(nat_ty());
            b.finish(b.mk_pi(lid, BinderInfo::Default, nat_ty(), q_of(l)))
        };

        // motive : fun (l : Nat) => Q l
        let motive = {
            let mut b = EnvDeclBuilder::new();
            let (mid, m) = b.fresh_local(nat_ty());
            b.finish(b.mk_lam(mid, BinderInfo::Default, nat_ty(), q_of(m)))
        };

        // base : Q 0. All four conjuncts reduce to rfl.
        //   half (litNeg 0) = half 1 = 0 = half 0  → rfl 0
        //   oddp (litNeg 0) = oddp 1 = true = not false = not (oddp 0) → rfl true
        //   half (litNeg 1) = half 0 = 0 = half 1  → rfl 0
        //   oddp (litNeg 1) = oddp 0 = false = not true = not (oddp 1) → rfl false
        let base = {
            let z = nat_zero();
            let one = nat_succ(nat_zero());
            let h0 = eq_refl_nat(half(z.clone())); // : half (litNeg 0) = half 0  (defeq)
            let o0 = eq_refl_bool(bnot(oddp(z.clone()))); // : oddp(litNeg 0) = not (oddp 0)
            let h1 = eq_refl_nat(half(one.clone())); // : half(litNeg 1) = half 1
            let o1 = eq_refl_bool(bnot(oddp(one.clone()))); // : oddp(litNeg 1) = not (oddp 1)
            and_intro(
                c_half(z.clone()),
                and_t(
                    c_odd(z.clone()),
                    and_t(c_half(one.clone()), c_odd(one.clone())),
                ),
                h0,
                and_intro(
                    c_odd(z.clone()),
                    and_t(c_half(one.clone()), c_odd(one.clone())),
                    o0,
                    and_intro(c_half(one.clone()), c_odd(one.clone()), h1, o1),
                ),
            )
        };

        // succ case: fun (p : Nat) (ih : Q p) => Q (succ p)
        let succ_case = {
            let mut b = EnvDeclBuilder::new();
            let (pid, p) = b.fresh_local(nat_ty());
            let (ihid, ih) = b.fresh_local(q_of(p.clone()));
            let sp = nat_succ(p.clone());
            let ssp = nat_succ(sp.clone());

            // Q p's four conjuncts.
            let qp1 = c_half(p.clone());
            let qp2 = c_odd(p.clone());
            let qp3 = c_half(sp.clone());
            let qp4 = c_odd(sp.clone());
            // ih components.
            let rest1 = and_t(qp2.clone(), and_t(qp3.clone(), qp4.clone()));
            let ih_rest = and_right(qp1.clone(), rest1.clone(), ih.clone());
            let rest2 = and_t(qp3.clone(), qp4.clone());
            let ih_rest2 = and_right(qp2.clone(), rest2.clone(), ih_rest.clone());
            // ih3 : half (litNeg (succ p)) = half (succ p)   (= Q(succ p) conjunct 1)
            let ih3 = and_left(qp3.clone(), qp4.clone(), ih_rest2.clone());
            // ih4 : oddp (litNeg (succ p)) = not (oddp (succ p))  (= Q(succ p) conjunct 2)
            let ih4 = and_right(qp3.clone(), qp4.clone(), ih_rest2);

            // We must build Q (succ p) = And (c_half sp) (And (c_odd sp) (And (c_half ssp) (c_odd ssp))).
            // conjunct1 = ih3, conjunct2 = ih4.
            // conjunct3 : half (litNeg (succ (succ p))) = half (succ (succ p)).
            //   litNeg (succ (succ p)) ≡ succ (succ (litNeg p))  (litNeg recursion).
            //   half (succ (succ x)) ≡ succ (half x).
            //   So LHS ≡ succ (half (litNeg p)); RHS ≡ succ (half p).
            //   From ih1 : half (litNeg p) = half p, congrArg Nat.succ → succ (..) = succ (..).
            let ih1 = and_left(qp1.clone(), rest1.clone(), ih.clone());
            let conj3 = congr_arg(
                u1(),
                u1(),
                nat_ty(),
                nat_ty(),
                half(lit_neg(p.clone())),
                half(p.clone()),
                Expr::const_str("Nat.succ"),
                ih1,
            );
            // conjunct4 : oddp (litNeg (succ (succ p))) = not (oddp (succ (succ p))).
            //   litNeg (succ (succ p)) ≡ succ (succ (litNeg p)); oddp (succ (succ x)) ≡
            //   Bool.not (Bool.not (oddp x)) (NOT def-eq to oddp x — not-not is propositional).
            //   So LHS ≡ not (not (oddp (litNeg p))), RHS ≡ not (not (not (oddp p))).
            //   From ih2 : oddp (litNeg p) = not (oddp p), apply congrArg Bool.not TWICE.
            let ih2 = and_left(qp2.clone(), rest2.clone(), ih_rest);
            let cong_not = |x: Expr, y: Expr, h: Expr| {
                congr_arg(
                    u1(),
                    u1(),
                    bool_ty(),
                    bool_ty(),
                    x,
                    y,
                    Expr::const_str("Bool.not"),
                    h,
                )
            };
            // ih2 : oddp(litNeg p) = not(oddp p)
            let c1 = cong_not(oddp(lit_neg(p.clone())), bnot(oddp(p.clone())), ih2);
            // c1 : not(oddp(litNeg p)) = not(not(oddp p))
            let conj4 = cong_not(
                bnot(oddp(lit_neg(p.clone()))),
                bnot(bnot(oddp(p.clone()))),
                c1,
            );
            // conj4 : not(not(oddp(litNeg p))) = not(not(not(oddp p)))

            // Assemble Q (succ p) with the EXACT conjunct props at succ p.
            let s1 = c_half(sp.clone());
            let s2 = c_odd(sp.clone());
            let s3 = c_half(ssp.clone());
            let s4 = c_odd(ssp.clone());
            let body = and_intro(
                s1,
                and_t(s2.clone(), and_t(s3.clone(), s4.clone())),
                ih3,
                and_intro(
                    s2,
                    and_t(s3.clone(), s4.clone()),
                    ih4,
                    and_intro(s3, s4, conj3, conj4),
                ),
            );
            let r = b.mk_lam(ihid, BinderInfo::Default, q_of(p.clone()), body);
            b.finish(b.mk_lam(pid, BinderInfo::Default, nat_ty(), r))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (lid, l) = b.fresh_local(nat_ty());
            let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
            let body = Expr::apps(nat_rec, [motive, base, succ_case, l]);
            b.finish(b.mk_lam(lid, BinderInfo::Default, nat_ty(), body))
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::HALF_ODD_LIT_NEG),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §3 boolModelLitNeg : litNeg flips the literal's value ──────────────────

    /// `boolModelLitNeg : (f : Nat → Bool) → (l : Nat) →`
    /// `  Eq (boolModelLit f (litNeg l)) (Bool.not (boolModelLit f l))`.
    ///
    /// `boolModelLit f l ≡ Bool.rec (f (half l)) (¬ f (half l)) (oddp l)`. Using the
    /// `halfOddLitNeg` facts `half (litNeg l) = half l` and `oddp (litNeg l) =
    /// ¬ oddp l`, substitute to rewrite the goal to one over `half l` / `oddp l`,
    /// then `Bool.rec` case analysis on `oddp l` closes both leaves by reflexivity
    /// (`Bool.rec t f false = t`, `… true = f`, and `Bool.not (Bool.not x) ≡` … is
    /// discharged by ground `Bool.rec` over `f (half l)`).
    fn register_bool_model_lit_neg(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::BOOL_MODEL_LIT_NEG))
            .is_some()
        {
            return Ok(());
        }
        let goal_of = |f: &Expr, l: Expr| eq_bool(bml(f, lit_neg(l.clone())), bnot(bml(f, l)));
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (fid, f) = b.fresh_local(nat_to_bool_ty());
            let (lid, l) = b.fresh_local(nat_ty());
            let e = b.mk_pi(lid, BinderInfo::Default, nat_ty(), goal_of(&f, l));
            b.finish(b.mk_pi(fid, BinderInfo::Default, nat_to_bool_ty(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (fid, f) = b.fresh_local(nat_to_bool_ty());
            let (lid, l) = b.fresh_local(nat_ty());

            // q := halfOddLitNeg l : And (half(litNeg l)=half l) (And (oddp(litNeg l)=not oddp l) _)
            let c_half = eq_nat(half(lit_neg(l.clone())), half(l.clone()));
            let sl = nat_succ(l.clone());
            let c_odd = eq_bool(oddp(lit_neg(l.clone())), bnot(oddp(l.clone())));
            let rest = and_t(
                c_odd.clone(),
                and_t(
                    eq_nat(half(lit_neg(sl.clone())), half(sl.clone())),
                    eq_bool(oddp(lit_neg(sl.clone())), bnot(oddp(sl.clone()))),
                ),
            );
            let q = Expr::app(Expr::const_str(names::HALF_ODD_LIT_NEG), l.clone());
            let h_half = and_left(c_half.clone(), rest.clone(), q.clone()); // half(litNeg l)=half l
            let h_odd = and_left(
                c_odd.clone(),
                and_t(
                    eq_nat(half(lit_neg(sl.clone())), half(sl.clone())),
                    eq_bool(oddp(lit_neg(sl.clone())), bnot(oddp(sl.clone()))),
                ),
                and_right(c_half.clone(), rest.clone(), q),
            ); // oddp(litNeg l) = not (oddp l)

            // Step 1: rewrite `half (litNeg l)` to `half l` in the goal LHS via Eq.subst.
            //   target after: Eq (Bool.rec (f (half l)) (not (f (half l))) (oddp (litNeg l)))
            //                    (not (boolModelLit f l))
            // Build a predicate P_half (hv : Nat) :=
            //   Eq (Bool.rec (f hv) (not (f hv)) (oddp (litNeg l))) (not (boolModelLit f l)).
            let fhv = |hv: Expr| Expr::app(f.clone(), hv);
            let brec = |t: Expr, fa: Expr, s: Expr| {
                let im = Expr::lam(BinderInfo::Default, bool_ty(), bool_ty());
                let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![u1()]);
                Expr::apps(bool_rec, [im, t, fa, s])
            };
            let rhs = bnot(bml(&f, l.clone()));
            // Eq.subst over Nat: motive on `hv`.
            let p_half = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hvid, hv) = c.fresh_local(nat_ty());
                let lhs = brec(
                    fhv(hv.clone()),
                    bnot(fhv(hv.clone())),
                    oddp(lit_neg(l.clone())),
                );
                c.finish_child(c.mk_lam(
                    hvid,
                    BinderInfo::Default,
                    nat_ty(),
                    eq_bool(lhs, rhs.clone()),
                ))
            };
            // base_half : P_half (half l) — i.e. with hv := half l.
            //   Eq (Bool.rec (f (half l)) (not (f (half l))) (oddp (litNeg l))) (not (bml f l))
            // We will obtain this from step 2 (rewriting oddp). Build that first.

            // Step 2: rewrite `oddp (litNeg l)` to `not (oddp l)`.
            // predicate P_odd (ov : Bool) :=
            //   Eq (Bool.rec (f (half l)) (not (f (half l))) ov) (not (boolModelLit f l)).
            let fhl = fhv(half(l.clone()));
            let p_odd = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ovid, ov) = c.fresh_local(bool_ty());
                let lhs = brec(fhl.clone(), bnot(fhl.clone()), ov);
                c.finish_child(c.mk_lam(
                    ovid,
                    BinderInfo::Default,
                    bool_ty(),
                    eq_bool(lhs, rhs.clone()),
                ))
            };
            // base_odd : P_odd (not (oddp l)) :=
            //   Eq (Bool.rec (f (half l)) (not (f (half l))) (not (oddp l))) (not (bml f l)).
            // bml f l ≡ Bool.rec (f (half l)) (not (f (half l))) (oddp l).
            // Case on `oddp l` via Bool.rec to prove this ground-shaped equality.
            //   oddp l = false: LHS ≡ Bool.rec .. (not false=true) = not(f hl);
            //                   RHS = not (Bool.rec .. false) = not (f hl). rfl.
            //   oddp l = true:  LHS ≡ Bool.rec .. (not true=false) = f hl;
            //                   RHS = not (Bool.rec .. true) = not (not (f hl)) = f hl. rfl.
            let base_odd = {
                // motive : fun (w : Bool) => Eq (Bool.rec fhl (not fhl) (not w)) (not (Bool.rec fhl (not fhl) w))
                let im = {
                    let w = Expr::bvar(0);
                    let lhs = brec(fhl.clone(), bnot(fhl.clone()), bnot(w.clone()));
                    let rhs2 = bnot(brec(fhl.clone(), bnot(fhl.clone()), w));
                    Expr::lam(BinderInfo::Default, bool_ty(), eq_bool(lhs, rhs2))
                };
                // false leaf: Eq (Bool.rec fhl (not fhl) (not false)) (not (Bool.rec fhl (not fhl) false))
                //   ≡ Eq (not fhl) (not fhl) → rfl (not fhl)
                let f_leaf = eq_refl_bool(bnot(fhl.clone()));
                // true leaf: Eq (Bool.rec fhl (not fhl) (not true)) (not (Bool.rec fhl (not fhl) true))
                //   ≡ Eq fhl (not (not fhl)). Reduce not(not fhl) by Bool.rec on fhl.
                //   Prove by Bool.rec on fhl: each leaf rfl.
                let t_leaf = {
                    let imf = {
                        let z = Expr::bvar(0);
                        Expr::lam(
                            BinderInfo::Default,
                            bool_ty(),
                            eq_bool(z.clone(), bnot(bnot(z))),
                        )
                    };
                    // false: Eq false (not (not false)) ≡ Eq false false → rfl
                    let ff = eq_refl_bool(bfalse());
                    // true: Eq true (not (not true)) ≡ Eq true true → rfl
                    let tt = eq_refl_bool(btrue());
                    // motive is Prop-valued (`Eq … : Prop`), so eliminate at level 0.
                    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
                    Expr::apps(bool_rec, [imf, ff, tt, fhl.clone()])
                };
                // motive is Prop-valued (`Eq … : Prop`), so eliminate at level 0.
                let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
                Expr::apps(bool_rec, [im, f_leaf, t_leaf, oddp(l.clone())])
            };
            // step2 : P_odd (oddp (litNeg l)) via Eq.subst with h_odd : oddp(litNeg l) = not (oddp l).
            //   We have base at (not (oddp l)); want at (oddp (litNeg l)). Use Eq.subst with
            //   h_odd reversed direction: Eq.subst P_odd a:=(not oddp l) ... no — Eq.subst needs
            //   motive b from a, h:Eq a b, m:motive a → motive b. We have base : P_odd (not oddp l)
            //   and want P_odd (oddp (litNeg l)). h_odd : Eq (oddp(litNeg l)) (not (oddp l)).
            //   So Eq.symm h_odd : Eq (not (oddp l)) (oddp (litNeg l)); subst that.
            let eq_symm = |ty: Expr, a: Expr, c: Expr, h: Expr| {
                Expr::apps(
                    Expr::const_(Name::from_string("Eq.symm"), vec![u1()]),
                    [ty, a, c, h],
                )
            };
            let eq_subst = |alpha: Expr, motivev: Expr, a: Expr, c: Expr, h: Expr, m: Expr| {
                Expr::apps(
                    Expr::const_(Name::from_string("Eq.subst"), vec![u1()]),
                    [alpha, motivev, a, c, h, m],
                )
            };
            let h_odd_sym = eq_symm(
                bool_ty(),
                oddp(lit_neg(l.clone())),
                bnot(oddp(l.clone())),
                h_odd,
            ); // : not (oddp l) = oddp (litNeg l)
            let step2 = eq_subst(
                bool_ty(),
                p_odd,
                bnot(oddp(l.clone())),
                oddp(lit_neg(l.clone())),
                h_odd_sym,
                base_odd,
            ); // : P_odd (oddp (litNeg l)) = Eq (Bool.rec (f hl)(not f hl)(oddp(litNeg l))) (not (bml f l))

            // step1 : the goal. We have step2 : the goal with `half (litNeg l)` already as `half l`.
            //   Goal : Eq (Bool.rec (f (half (litNeg l))) (not (f (half (litNeg l)))) (oddp (litNeg l)))
            //             (not (bml f l))
            //        = boolModelLit f (litNeg l) (after δ) vs not (bml f l).
            //   step2 has `half l` where the goal has `half (litNeg l)`. Use Eq.subst with
            //   Eq.symm h_half : Eq (half l) (half (litNeg l)) to go from step2 (at half l) to
            //   the goal (at half (litNeg l)).
            let h_half_sym = eq_symm(nat_ty(), half(lit_neg(l.clone())), half(l.clone()), h_half); // : half l = half (litNeg l)
            let goal_term = eq_subst(
                nat_ty(),
                p_half,
                half(l.clone()),
                half(lit_neg(l.clone())),
                h_half_sym,
                step2,
            );

            let r = b.mk_lam(lid, BinderInfo::Default, nat_ty(), goal_term);
            b.finish(b.mk_lam(fid, BinderInfo::Default, nat_to_bool_ty(), r))
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::BOOL_MODEL_LIT_NEG),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §4 boolModelConsistent / boolModelExclusive ────────────────────────────

    /// `boolModelConsistent : (f : Nat → Bool) → resConsistent (boolModel f)`.
    ///
    /// `resConsistent H ≡ (l : Nat) → Or (H l) (H (litNeg l))`, here
    /// `Or (boolModelLit f l = true) (boolModelLit f (litNeg l) = true)`. Case on
    /// `boolModelLit f l` by `Bool.rec`: `true` ⇒ `Or.inl rfl`; `false` ⇒ the
    /// negation literal is `true` because `boolModelLit f (litNeg l) = ¬(boolModelLit
    /// f l)` (`boolModelLitNeg`) and `¬false = true`, so `Or.inr`.
    fn register_bool_model_consistent(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::BOOL_MODEL_CONSISTENT))
            .is_some()
        {
            return Ok(());
        }
        let model = |f: &Expr| Expr::app(Expr::const_str(names::BOOL_MODEL), f.clone());
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (fid, f) = b.fresh_local(nat_to_bool_ty());
            let concl = Expr::app(Expr::const_str(snames::RES_CONSISTENT), model(&f));
            b.finish(b.mk_pi(fid, BinderInfo::Default, nat_to_bool_ty(), concl))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (fid, f) = b.fresh_local(nat_to_bool_ty());
            // The δ-unfolded body of resConsistent (boolModel f):
            //   (l : Nat) → Or (boolModelLit f l = true) (boolModelLit f (litNeg l) = true)
            let inner = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (lid, l) = c.fresh_local(nat_ty());
                let p_pos = eq_bool(bml(&f, l.clone()), btrue());
                let p_neg = eq_bool(bml(&f, lit_neg(l.clone())), btrue());
                // boolModelLitNeg f l : bml f (litNeg l) = not (bml f l)
                let bmln = Expr::apps(
                    Expr::const_str(names::BOOL_MODEL_LIT_NEG),
                    [f.clone(), l.clone()],
                );
                // Case on b := bml f l via Bool.rec.
                // motive : fun (w : Bool) => (bml f l = w) → Or (bml f l = true) (bml f (litNeg l) = true)
                let b_l = bml(&f, l.clone());
                let motive = {
                    let w = Expr::bvar(0);
                    let hyp = eq_bool(b_l.clone(), w);
                    let body = Expr::arrow(hyp, or_t(p_pos.clone(), p_neg.clone()));
                    Expr::lam(BinderInfo::Default, bool_ty(), body)
                };
                // false leaf: fun (h : bml f l = false) =>
                //   Or.inr — need bml f (litNeg l) = true. We have bmln : bml f (litNeg l) = not (bml f l).
                //   Eq.subst with h into not: not (bml f l) -> not false = true... build:
                //   trans: bml f (litNeg l) = not (bml f l) = not false = true.
                let eq_trans = |ty: Expr, x: Expr, y: Expr, z: Expr, hxy: Expr, hyz: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq.trans"), vec![u1()]),
                        [ty, x, y, z, hxy, hyz],
                    )
                };
                let f_leaf = {
                    let hty = eq_bool(b_l.clone(), bfalse());
                    let (hid, h) = c.fresh_local(hty.clone());
                    // congrArg Bool.not (h : bml f l = false) : not (bml f l) = not false
                    let cong = congr_arg(
                        u1(),
                        u1(),
                        bool_ty(),
                        bool_ty(),
                        b_l.clone(),
                        bfalse(),
                        Expr::const_str("Bool.not"),
                        h.clone(),
                    ); // : not (bml f l) = not false   (not false ≡ true)
                       // bml f (litNeg l) = not (bml f l) = not false (≡ true)
                    let chain = eq_trans(
                        bool_ty(),
                        bml(&f, lit_neg(l.clone())),
                        bnot(b_l.clone()),
                        bnot(bfalse()),
                        bmln.clone(),
                        cong,
                    ); // : bml f (litNeg l) = not false ; not false ≡ true so this : ... = true (defeq)
                    let inr = or_inr(p_pos.clone(), p_neg.clone(), chain);
                    c.mk_lam(hid, BinderInfo::Default, hty, inr)
                };
                // true leaf: fun (h : bml f l = true) => Or.inl h
                let t_leaf = {
                    let hty = eq_bool(b_l.clone(), btrue());
                    let (hid, h) = c.fresh_local(hty.clone());
                    let inl = or_inl(p_pos.clone(), p_neg.clone(), h.clone());
                    c.mk_lam(hid, BinderInfo::Default, hty, inl)
                };
                let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
                let scrutinee = Expr::apps(bool_rec, [motive, f_leaf, t_leaf, b_l.clone()]);
                // Apply to (Eq.refl Bool (bml f l)) : bml f l = bml f l.
                let body = Expr::app(scrutinee, eq_refl_bool(b_l));
                c.finish_child(c.mk_lam(lid, BinderInfo::Default, nat_ty(), body))
            };
            b.finish(b.mk_lam(fid, BinderInfo::Default, nat_to_bool_ty(), inner))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::BOOL_MODEL_CONSISTENT),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `boolModelExclusive : (f : Nat → Bool) → resExclusive (boolModel f)`.
    ///
    /// `resExclusive H ≡ (l : Nat) → H l → H (litNeg l) → False`, here
    /// `(l) → boolModelLit f l = true → boolModelLit f (litNeg l) = true → False`.
    /// From `boolModelLitNeg`, `boolModelLit f (litNeg l) = ¬(boolModelLit f l)`,
    /// and with `boolModelLit f l = true` this makes the second hypothesis
    /// `¬true = true`, i.e. `false = true`, absurd.
    fn register_bool_model_exclusive(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::BOOL_MODEL_EXCLUSIVE))
            .is_some()
        {
            return Ok(());
        }
        let model = |f: &Expr| Expr::app(Expr::const_str(names::BOOL_MODEL), f.clone());
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (fid, f) = b.fresh_local(nat_to_bool_ty());
            let concl = Expr::app(Expr::const_str(snames::RES_EXCLUSIVE), model(&f));
            b.finish(b.mk_pi(fid, BinderInfo::Default, nat_to_bool_ty(), concl))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (fid, f) = b.fresh_local(nat_to_bool_ty());
            // δ-body: (l) → bml f l = true → bml f (litNeg l) = true → False
            let inner = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (lid, l) = c.fresh_local(nat_ty());
                let b_l = bml(&f, l.clone());
                let hpos_ty = eq_bool(b_l.clone(), btrue());
                let hneg_ty = eq_bool(bml(&f, lit_neg(l.clone())), btrue());
                let (hposid, hpos) = c.fresh_local(hpos_ty.clone());
                let (hnegid, hneg) = c.fresh_local(hneg_ty.clone());

                let eq_symm = |ty: Expr, a: Expr, cc: Expr, h: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq.symm"), vec![u1()]),
                        [ty, a, cc, h],
                    )
                };
                let eq_trans = |ty: Expr, x: Expr, y: Expr, z: Expr, hxy: Expr, hyz: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq.trans"), vec![u1()]),
                        [ty, x, y, z, hxy, hyz],
                    )
                };
                // bmln : bml f (litNeg l) = not (bml f l)
                let bmln = Expr::apps(
                    Expr::const_str(names::BOOL_MODEL_LIT_NEG),
                    [f.clone(), l.clone()],
                );
                // congrArg Bool.not hpos : not (bml f l) = not true   (not true ≡ false)
                let cong = congr_arg(
                    u1(),
                    u1(),
                    bool_ty(),
                    bool_ty(),
                    b_l.clone(),
                    btrue(),
                    Expr::const_str("Bool.not"),
                    hpos.clone(),
                );
                // eq1 : bml f (litNeg l) = not true  (trans bmln cong)
                let eq1 = eq_trans(
                    bool_ty(),
                    bml(&f, lit_neg(l.clone())),
                    bnot(b_l.clone()),
                    bnot(btrue()),
                    bmln,
                    cong,
                );
                // hneg_sym : true = bml f (litNeg l)
                let hneg_sym = eq_symm(
                    bool_ty(),
                    bml(&f, lit_neg(l.clone())),
                    btrue(),
                    hneg.clone(),
                );
                // eq2 : true = not true   (not true ≡ false → tf_to_false applies)
                let eq2 = eq_trans(
                    bool_ty(),
                    btrue(),
                    bml(&f, lit_neg(l.clone())),
                    bnot(btrue()),
                    hneg_sym,
                    eq1,
                );
                let body = tf_to_false(eq2);
                let lam_neg = c.mk_lam(hnegid, BinderInfo::Default, hneg_ty, body);
                let lam_pos = c.mk_lam(hposid, BinderInfo::Default, hpos_ty, lam_neg);
                let r = c.mk_lam(lid, BinderInfo::Default, nat_ty(), lam_pos);
                c.finish_child(r)
            };
            b.finish(b.mk_lam(fid, BinderInfo::Default, nat_to_bool_ty(), inner))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::BOOL_MODEL_EXCLUSIVE),
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
#[path = "bool_model_tests.rs"]
mod tests;
