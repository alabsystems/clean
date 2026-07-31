// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SCALABLE (inductive) machine-vs-IR bit-vector add fidelity, as raw kernel
//! `Expr`s — reachable from `clean-auto` (clean-kernel only; no parser/elab/.lean).
//!
//! # Why this exists (rung-3 scalable substrate)
//!
//! [`crate::bitvec_compute`] proves the machine-vs-IR adder fidelity at the FIXED
//! width 4 by a 2⁸-leaf exhaustive `Bool.rec` case split — which does NOT scale
//! (width 8 = 2¹⁶ leaves, width 32 = 2⁶⁴). Real self-compilation uses i8…i64.
//! This module proves the SAME fidelity by INDUCTION OVER BIT-POSITION (the
//! technique g16's `add_equiv` used over `Word32`), so a SINGLE kernel theorem
//! covers EVERY width at once:
//!
//! ```text
//!   addRec_eq_ir : ∀ (xs ys : List Bool) (c : Bool),
//!                    addRecM xs ys c = addRecIr xs ys c
//! ```
//!
//! Bitvectors are `List Bool` (LSB-first); the list length is the width, so the
//! `∀ xs` quantifier ranges over all widths. The proof is `List.rec` induction on
//! `xs` (NOT a case split): nil closes by `rfl`, cons rewrites the per-bit carry
//! by the gate-equality lemma and recurses via the induction hypothesis.
//!
//! # Non-vacuity (the make-or-break guard, NOT softened)
//!
//! The machine adder `addRecM` (gates `xor3`/`maj`: left-assoc sum,
//! OR-of-pairwise-ANDs carry) and the IR adder `addRecIr` (gates `xor3Ir`/`majIr`:
//! right-assoc sum, `(a&&b)||(c&&(a||b))` carry) are SEPARATELY-defined recursive
//! Definitions over genuinely DIFFERENT per-bit Bool terms. So the symbolic goal
//! is NOT closeable by `rfl`; the theorem must DISCHARGE the gate difference. The
//! tests assert: (a) the theorem is a PROVED `Theorem` with empty domain-axiom
//! closure; (b) a symbolic-tail goal does NOT close by `Eq.refl` (no rfl-collapse);
//! (c) a CORRUPTED IR adder (carry dropped) makes a concrete instance FALSE / the
//! theorem unprovable; (d) a discriminating ground witness (1+1=2) holds.
//!
//! All names live under the `Clean.BVI.` namespace (BVI = bit-vector inductive).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::name::Name;
use crate::{BinderInfo, Declaration, EnvError, Environment, Expr, Level};

/// Declaration names for the inductive bit-vector fidelity layer.
pub mod names {
    /// `xor3 a b c := Bool.xor (Bool.xor a b) c` — machine sum gate (left-assoc).
    pub const XOR3: &str = "Clean.BVI.xor3";
    /// `maj a b c := (a&&b) || ((a&&c) || (b&&c))` — machine carry gate.
    pub const MAJ: &str = "Clean.BVI.maj";
    /// `xor3Ir a b c := Bool.xor a (Bool.xor b c)` — IR sum gate (right-assoc).
    pub const XOR3_IR: &str = "Clean.BVI.xor3Ir";
    /// `majIr a b c := (a&&b) || (c && (a||b))` — IR carry gate (different term).
    pub const MAJ_IR: &str = "Clean.BVI.majIr";
    /// `bhead : List Bool → Bool` (head, `false` on nil).
    pub const BHEAD: &str = "Clean.BVI.bhead";
    /// `btail : List Bool → List Bool` (tail, `nil` on nil).
    pub const BTAIL: &str = "Clean.BVI.btail";
    /// `addRecM : List Bool → List Bool → Bool → List Bool` — machine ripple adder.
    pub const ADD_REC_M: &str = "Clean.BVI.addRecM";
    /// `addRecIr : List Bool → List Bool → Bool → List Bool` — IR ripple adder.
    pub const ADD_REC_IR: &str = "Clean.BVI.addRecIr";
    /// `xor3_eq_ir : ∀ a b c, xor3 a b c = xor3Ir a b c`.
    pub const XOR3_EQ_IR: &str = "Clean.BVI.xor3_eq_ir";
    /// `maj_eq_ir : ∀ a b c, maj a b c = majIr a b c`.
    pub const MAJ_EQ_IR: &str = "Clean.BVI.maj_eq_ir";
    /// THE HEADLINE: `addRec_eq_ir : ∀ xs ys c, addRecM xs ys c = addRecIr xs ys c`.
    pub const ADD_REC_EQ_IR: &str = "Clean.BVI.addRec_eq_ir";
}

// ── Bool term helpers ─────────────────────────────────────────────────────────
fn bool_ty() -> Expr {
    Expr::const_str("Bool")
}
fn btrue() -> Expr {
    Expr::const_str("Bool.true")
}
fn bfalse() -> Expr {
    Expr::const_str("Bool.false")
}
fn bxor(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.xor"), [x, y])
}
fn band(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.and"), [x, y])
}
fn bor(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.or"), [x, y])
}
fn list_bool() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        bool_ty(),
    )
}
fn list_nil_bool() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        bool_ty(),
    )
}
fn list_cons_bool(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [bool_ty(), h, t],
    )
}

fn ternary_lam(f: impl Fn(Expr, Expr, Expr) -> Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (i0, a) = b.fresh_local(bool_ty());
    let (i1, bb) = b.fresh_local(bool_ty());
    let (i2, c) = b.fresh_local(bool_ty());
    let body = f(a, bb, c);
    let e = b.mk_lam(i2, BinderInfo::Default, bool_ty(), body);
    let e = b.mk_lam(i1, BinderInfo::Default, bool_ty(), e);
    let e = b.mk_lam(i0, BinderInfo::Default, bool_ty(), e);
    b.finish(e)
}

fn xor3(a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::XOR3), [a, b, c])
}
fn maj(a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::MAJ), [a, b, c])
}
fn xor3_ir(a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::XOR3_IR), [a, b, c])
}
fn maj_ir(a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::MAJ_IR), [a, b, c])
}
fn bhead(v: Expr) -> Expr {
    Expr::app(Expr::const_str(names::BHEAD), v)
}
fn btail(v: Expr) -> Expr {
    Expr::app(Expr::const_str(names::BTAIL), v)
}
fn add_rec_m(xs: Expr, ys: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::ADD_REC_M), [xs, ys, c])
}
fn add_rec_ir(xs: Expr, ys: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::ADD_REC_IR), [xs, ys, c])
}

/// `@Eq.{1} Bool x y`.
fn eq_bool(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [bool_ty(), x, y],
    )
}
/// `@Eq.{1} (List Bool) x y`.
fn eq_list(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [list_bool(), x, y],
    )
}
/// `@Eq.refl.{1} Bool v`.
fn eq_refl_bool(v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_ty(), v],
    )
}
/// `@Eq.refl.{1} (List Bool) v`.
fn eq_refl_list(v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [list_bool(), v],
    )
}
/// `@Eq.trans.{1} (List Bool) a b c h1 h2`.
fn eq_trans_list(a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [list_bool(), a, b, c, h1, h2],
    )
}
/// `@Eq.symm.{1} (List Bool) a b h`.
#[cfg(test)]
fn eq_symm_list(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [list_bool(), a, b, h],
    )
}
/// `@congrArg.{1,1} (List Bool) (List Bool) a1 a2 f h : Eq (f a1) (f a2)`.
fn congr_arg_ll(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let l1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [list_bool(), list_bool(), a1, a2, f, h],
    )
}
/// `@congrArg.{1,1} Bool (List Bool) a1 a2 f h` for `f : Bool → List Bool`.
fn congr_arg_bl(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let l1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [bool_ty(), list_bool(), a1, a2, f, h],
    )
}

/// `@Bool.rec.{0} (motive := fun _ => Bool) f t b` — exhaustive Bool elimination
/// into Bool. Used for the per-bit gate-equality leaves. (Here the motive result
/// is an `Eq` Prop, so we use `Level::zero` motive level.)
fn bool_rec_prop(motive: Expr, false_case: Expr, true_case: Expr, major: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        [motive, false_case, true_case, major],
    )
}

impl Environment {
    /// Register the SCALABLE inductive machine-vs-IR add fidelity layer.
    ///
    /// Registers (all `Clean.BVI.*`): the machine/IR per-bit gates
    /// `xor3`/`maj`/`xor3Ir`/`majIr`, the total `bhead`/`btail`, the recursive
    /// ripple adders `addRecM`/`addRecIr` (via `List.rec` into `Type`), the per-bit
    /// gate-equality lemmas `xor3_eq_ir`/`maj_eq_ir`, and the HEADLINE inductive
    /// fidelity theorem `addRec_eq_ir : ∀ xs ys c, addRecM xs ys c = addRecIr xs ys c`
    /// (proved by `List.rec` induction on `xs` — PARAMETRIC in width).
    ///
    /// Idempotent. # Errors: propagates kernel-checking failures (a broken proof
    /// fails registration here).
    pub fn init_bv_inductive(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::ADD_REC_EQ_IR))
            .is_some()
        {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_list()?;
        self.register_bvi_gates()?;
        self.register_bvi_head_tail()?;
        self.register_bvi_adders()?;
        self.register_bvi_gate_eqs()?;
        self.register_bvi_add_eq_ir()?;
        Ok(())
    }

    fn register_bvi_gates(&mut self) -> Result<(), EnvError> {
        let tern_ty = Expr::arrow(
            bool_ty(),
            Expr::arrow(bool_ty(), Expr::arrow(bool_ty(), bool_ty())),
        );
        let defs: [(&str, Expr); 4] = [
            (names::XOR3, ternary_lam(|a, b, c| bxor(bxor(a, b), c))),
            (
                names::MAJ,
                ternary_lam(|a, b, c| {
                    bor(
                        band(a.clone(), b.clone()),
                        bor(band(a, c.clone()), band(b, c)),
                    )
                }),
            ),
            (names::XOR3_IR, ternary_lam(|a, b, c| bxor(a, bxor(b, c)))),
            (
                names::MAJ_IR,
                ternary_lam(|a, b, c| bor(band(a.clone(), b.clone()), band(c, bor(a, b)))),
            ),
        ];
        for (name, value) in defs {
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(name),
                level_params: vec![],
                type_: tern_ty.clone(),
                value,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    /// `bhead xs := List.rec (fun _ => Bool) false (fun h _ _ => h) xs`
    /// `btail xs := List.rec (fun _ => List Bool) nil (fun _ t _ => t) xs`
    fn register_bvi_head_tail(&mut self) -> Result<(), EnvError> {
        // bhead : List Bool → Bool
        let bhead_val = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(list_bool());
            // motive : List Bool → Sort 1  =  fun _ => Bool
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(list_bool());
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), bool_ty()))
            };
            // nil_case : Bool = false
            let nil_case = bfalse();
            // cons_case : (h : Bool) → (t : List Bool) → (ih : Bool) → Bool  = fun h _ _ => h
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(bool_ty());
                let (t_id, _t) = c.fresh_local(list_bool());
                let (ih_id, _ih) = c.fresh_local(bool_ty());
                let r = c.mk_lam(ih_id, BinderInfo::Default, bool_ty(), h);
                let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
            };
            // @List.rec.{1,0} Bool motive nil cons xs
            let rec = Expr::apps(
                Expr::const_(
                    Name::from_string("List.rec"),
                    vec![Level::succ(Level::zero()), Level::zero()],
                ),
                [bool_ty(), motive, nil_case, cons_case, xs.clone()],
            );
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::BHEAD),
            level_params: vec![],
            type_: Expr::arrow(list_bool(), bool_ty()),
            value: bhead_val,
            is_reducible: true,
        })?;

        // btail : List Bool → List Bool
        let btail_val = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(list_bool());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(list_bool());
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), list_bool()))
            };
            let nil_case = list_nil_bool();
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, _h) = c.fresh_local(bool_ty());
                let (t_id, t) = c.fresh_local(list_bool());
                let (ih_id, _ih) = c.fresh_local(list_bool());
                let r = c.mk_lam(ih_id, BinderInfo::Default, list_bool(), t);
                let r = c.mk_lam(t_id, BinderInfo::Default, list_bool(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, bool_ty(), r))
            };
            let rec = Expr::apps(
                Expr::const_(
                    Name::from_string("List.rec"),
                    vec![Level::succ(Level::zero()), Level::zero()],
                ),
                [bool_ty(), motive, nil_case, cons_case, xs.clone()],
            );
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::BTAIL),
            level_params: vec![],
            type_: Expr::arrow(list_bool(), list_bool()),
            value: btail_val,
            is_reducible: true,
        })?;
        Ok(())
    }

    /// Register `addRecM` / `addRecIr` — the recursive ripple adders. Recursion is
    /// over the FIRST list (`xs`) via `List.rec` into `Type` with motive
    /// `fun _ => List Bool → Bool → List Bool` (the g16 `addRec` shape):
    ///   nil   ↦ fun _ _ => nil
    ///   cons a as ↦ fun ih ys c =>
    ///       cons (xor3 a (bhead ys) c) (ih (btail ys) (maj a (bhead ys) c))
    fn register_bvi_adders(&mut self) -> Result<(), EnvError> {
        for (name, is_ir) in [(names::ADD_REC_M, false), (names::ADD_REC_IR, true)] {
            let sum = |a: Expr, b: Expr, c: Expr| {
                if is_ir {
                    xor3_ir(a, b, c)
                } else {
                    xor3(a, b, c)
                }
            };
            let carry = |a: Expr, b: Expr, c: Expr| {
                if is_ir {
                    maj_ir(a, b, c)
                } else {
                    maj(a, b, c)
                }
            };
            // type: List Bool → List Bool → Bool → List Bool
            let ty = Expr::arrow(
                list_bool(),
                Expr::arrow(list_bool(), Expr::arrow(bool_ty(), list_bool())),
            );
            // motive : List Bool → Sort 1 = fun _ => (List Bool → Bool → List Bool)
            let consumer_ty = Expr::arrow(list_bool(), Expr::arrow(bool_ty(), list_bool()));
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_bool());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_bool());
                    c.finish_child(c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_bool(),
                        consumer_ty.clone(),
                    ))
                };
                // nil_case : List Bool → Bool → List Bool = fun _ _ => nil
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ys_id, _ys) = c.fresh_local(list_bool());
                    let (cc_id, _cc) = c.fresh_local(bool_ty());
                    let r = c.mk_lam(cc_id, BinderInfo::Default, bool_ty(), list_nil_bool());
                    c.finish_child(c.mk_lam(ys_id, BinderInfo::Default, list_bool(), r))
                };
                // cons_case : (a:Bool)→(as:List Bool)→(ih:consumer)→consumer
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, a) = c.fresh_local(bool_ty());
                    let (as_id, _as_) = c.fresh_local(list_bool());
                    let (ih_id, ih) = c.fresh_local(consumer_ty.clone());
                    // fun ys c => cons (sum a (bhead ys) c) (ih (btail ys) (carry a (bhead ys) c))
                    let inner = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (ys_id, ys) = d.fresh_local(list_bool());
                        let (cc_id, cc) = d.fresh_local(bool_ty());
                        let head = bhead(ys.clone());
                        let sum_bit = sum(a.clone(), head.clone(), cc.clone());
                        let next_carry = carry(a.clone(), head, cc.clone());
                        let rest = Expr::apps(ih.clone(), [btail(ys.clone()), next_carry]);
                        let body = list_cons_bool(sum_bit, rest);
                        let r = d.mk_lam(cc_id, BinderInfo::Default, bool_ty(), body);
                        d.finish_child(d.mk_lam(ys_id, BinderInfo::Default, list_bool(), r))
                    };
                    let r = c.mk_lam(ih_id, BinderInfo::Default, consumer_ty.clone(), inner);
                    let r = c.mk_lam(as_id, BinderInfo::Default, list_bool(), r);
                    c.finish_child(c.mk_lam(a_id, BinderInfo::Default, bool_ty(), r))
                };
                // @List.rec.{1,0} Bool motive nil_case cons_case xs  : consumer_ty
                let rec = Expr::apps(
                    Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::succ(Level::zero()), Level::zero()],
                    ),
                    [bool_ty(), motive, nil_case, cons_case, xs.clone()],
                );
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(name),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    /// Per-bit gate equality lemmas, proved by exhaustive 8-way `Bool.rec`:
    ///   xor3_eq_ir : ∀ a b c, xor3 a b c = xor3Ir a b c
    ///   maj_eq_ir  : ∀ a b c, maj  a b c = majIr  a b c
    fn register_bvi_gate_eqs(&mut self) -> Result<(), EnvError> {
        for (name, lhs, rhs) in [
            (
                names::XOR3_EQ_IR,
                xor3 as fn(Expr, Expr, Expr) -> Expr,
                xor3_ir as fn(Expr, Expr, Expr) -> Expr,
            ),
            (names::MAJ_EQ_IR, maj, maj_ir),
        ] {
            // type: ∀ (a b c : Bool), Eq Bool (lhs a b c) (rhs a b c)
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bool_ty());
                let (bb_id, bb) = b.fresh_local(bool_ty());
                let (c_id, c) = b.fresh_local(bool_ty());
                let goal = eq_bool(lhs(a.clone(), bb.clone(), c.clone()), rhs(a, bb, c));
                let t = b.mk_pi(c_id, BinderInfo::Default, bool_ty(), goal);
                let t = b.mk_pi(bb_id, BinderInfo::Default, bool_ty(), t);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, bool_ty(), t))
            };
            // value: fun a b c => <8-way Bool.rec on a,b,c, each leaf Eq.refl>
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bool_ty());
                let (bb_id, bb) = b.fresh_local(bool_ty());
                let (c_id, c) = b.fresh_local(bool_ty());
                // Build the nested case split returning a proof of
                //   Eq Bool (lhs a b c) (rhs a b c)
                // by splitting a, then b, then c; each ground leaf is Eq.refl of
                // the (reduced) lhs value.
                let proof = bvi_bool_split3(&b, &lhs, &rhs, a.clone(), bb.clone(), c.clone());
                let r = b.mk_lam(c_id, BinderInfo::Default, bool_ty(), proof);
                let r = b.mk_lam(bb_id, BinderInfo::Default, bool_ty(), r);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, bool_ty(), r))
            };
            self.add_decl_if_absent(Declaration::Theorem {
                name: Name::from_string(name),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }
        Ok(())
    }

    /// THE HEADLINE: `addRec_eq_ir : ∀ (xs ys : List Bool) (c : Bool),
    /// addRecM xs ys c = addRecIr xs ys c`, by `List.rec` induction on `xs`.
    ///
    /// Motive (over xs): `fun w => ∀ ys c, addRecM w ys c = addRecIr w ys c`.
    /// nil:  ∀ ys c, nil = nil  — `fun ys c => Eq.refl nil`.
    /// cons a as (ih : ∀ ys c, addRecM as ys c = addRecIr as ys c):
    ///   ∀ ys c, cons (xor3 a (bhead ys) c) (addRecM as (btail ys) (maj a (bhead ys) c))
    ///          = cons (xor3Ir a (bhead ys) c) (addRecIr as (btail ys) (majIr a (bhead ys) c))
    ///   chain:
    ///     (A) rewrite the HEAD by xor3_eq_ir  (congrArg (cons · tailM))
    ///     (B) rewrite the TAIL: addRecM as (btail ys) (maj …)
    ///                          = addRecM as (btail ys) (majIr …)   [congrArg (carry) via maj_eq_ir]
    ///                          = addRecIr as (btail ys) (majIr …)  [ih (btail ys) (majIr …)]
    ///   Because addRecM/addRecIr cons-unfold definitionally (List.rec ι on cons),
    ///   the LHS/RHS *are* these cons terms; we prove the cons-of-(head,tail) eq.
    fn register_bvi_add_eq_ir(&mut self) -> Result<(), EnvError> {
        let goal_of = |xs: Expr, ys: Expr, c: Expr| {
            eq_list(
                add_rec_m(xs.clone(), ys.clone(), c.clone()),
                add_rec_ir(xs, ys, c),
            )
        };
        // type: ∀ xs ys c, addRecM xs ys c = addRecIr xs ys c
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(list_bool());
            let (ys_id, ys) = b.fresh_local(list_bool());
            let (c_id, c) = b.fresh_local(bool_ty());
            let goal = goal_of(xs.clone(), ys.clone(), c.clone());
            let t = b.mk_pi(c_id, BinderInfo::Default, bool_ty(), goal);
            let t = b.mk_pi(ys_id, BinderInfo::Default, list_bool(), t);
            b.finish(b.mk_pi(xs_id, BinderInfo::Default, list_bool(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(list_bool());
            // motive : List Bool → Prop = fun w => ∀ ys c, addRecM w ys c = addRecIr w ys c
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(list_bool());
                let inner = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (ys_id, ys) = d.fresh_local(list_bool());
                    let (cc_id, cc) = d.fresh_local(bool_ty());
                    let g = goal_of(w.clone(), ys.clone(), cc.clone());
                    let t = d.mk_pi(cc_id, BinderInfo::Default, bool_ty(), g);
                    d.finish_child(d.mk_pi(ys_id, BinderInfo::Default, list_bool(), t))
                };
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, list_bool(), inner))
            };
            // nil_case : ∀ ys c, addRecM nil ys c = addRecIr nil ys c
            //          = fun ys c => Eq.refl (List Bool) nil    (both sides ι-reduce to nil)
            let nil_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ys_id, _ys) = c.fresh_local(list_bool());
                let (cc_id, _cc) = c.fresh_local(bool_ty());
                let r = c.mk_lam(
                    cc_id,
                    BinderInfo::Default,
                    bool_ty(),
                    eq_refl_list(list_nil_bool()),
                );
                c.finish_child(c.mk_lam(ys_id, BinderInfo::Default, list_bool(), r))
            };
            // cons_case : (a:Bool)(as:List Bool)(ih:motive as) → motive (cons a as)
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(bool_ty());
                let (as_id, as_) = c.fresh_local(list_bool());
                // ih : ∀ ys c, addRecM as ys c = addRecIr as ys c
                let ih_ty = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (ys_id, ys) = d.fresh_local(list_bool());
                    let (cc_id, cc) = d.fresh_local(bool_ty());
                    let g = goal_of(as_.clone(), ys.clone(), cc.clone());
                    let t = d.mk_pi(cc_id, BinderInfo::Default, bool_ty(), g);
                    d.finish_child(d.mk_pi(ys_id, BinderInfo::Default, list_bool(), t))
                };
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                // body : ∀ ys c, addRecM (cons a as) ys c = addRecIr (cons a as) ys c
                let body = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (ys_id, ys) = d.fresh_local(list_bool());
                    let (cc_id, cc) = d.fresh_local(bool_ty());
                    let head = bhead(ys.clone());
                    let tl = btail(ys.clone());
                    // machine head/carry and ir head/carry
                    let h_m = xor3(a.clone(), head.clone(), cc.clone());
                    let h_ir = xor3_ir(a.clone(), head.clone(), cc.clone());
                    let cm = maj(a.clone(), head.clone(), cc.clone());
                    let cir = maj_ir(a.clone(), head.clone(), cc.clone());
                    // tailM   = addRecM as (btail ys) cm
                    // tailMir = addRecM as (btail ys) cir
                    // tailIr  = addRecIr as (btail ys) cir
                    let tail_m = add_rec_m(as_.clone(), tl.clone(), cm.clone());
                    let tail_m_ir = add_rec_m(as_.clone(), tl.clone(), cir.clone());
                    let tail_ir = add_rec_ir(as_.clone(), tl.clone(), cir.clone());
                    // LHS (def-unfolds to)  : cons h_m  tail_m
                    // RHS (def-unfolds to)  : cons h_ir tail_ir
                    // Strategy: prove  cons h_m tail_m = cons h_ir tail_ir  by:
                    //   step1: cons h_m tail_m = cons h_m tail_ir
                    //          via congrArg (cons h_m ·) of (tail_m = tail_ir)
                    //   tail_m = tail_ir:
                    //          tail_m = tail_m_ir  [congrArg (addRecM as (btail ys) ·) (maj_eq_ir …)]
                    //          tail_m_ir = tail_ir [ih (btail ys) cir]
                    //   step2: cons h_m tail_ir = cons h_ir tail_ir
                    //          via congrArg (cons · tail_ir) of (h_m = h_ir) [xor3_eq_ir …]
                    // maj_eq_ir a head cc : Eq cm cir
                    let maj_eq = Expr::apps(
                        Expr::const_str(names::MAJ_EQ_IR),
                        [a.clone(), head.clone(), cc.clone()],
                    );
                    // congrArg (fun k => addRecM as (btail ys) k) : Eq cm cir → Eq tail_m tail_m_ir
                    let carry_fn = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (k_id, k) = e.fresh_local(bool_ty());
                        let app = add_rec_m(as_.clone(), tl.clone(), k);
                        e.finish_child(e.mk_lam(k_id, BinderInfo::Default, bool_ty(), app))
                    };
                    let h_tail_a = bool_to_list_congr(cm.clone(), cir.clone(), carry_fn, maj_eq);
                    // ih (btail ys) cir : Eq tail_m_ir tail_ir
                    let h_tail_b = Expr::apps(ih.clone(), [tl.clone(), cir.clone()]);
                    // tail_m = tail_ir
                    let tail_eq = eq_trans_list(
                        tail_m.clone(),
                        tail_m_ir.clone(),
                        tail_ir.clone(),
                        h_tail_a,
                        h_tail_b,
                    );
                    // step1: congrArg (fun t => cons h_m t) tail_eq : Eq (cons h_m tail_m) (cons h_m tail_ir)
                    let cons_hm_fn = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (t_id, t) = e.fresh_local(list_bool());
                        let app = list_cons_bool(h_m.clone(), t);
                        e.finish_child(e.mk_lam(t_id, BinderInfo::Default, list_bool(), app))
                    };
                    let step1 = congr_arg_ll(tail_m.clone(), tail_ir.clone(), cons_hm_fn, tail_eq);
                    // xor3_eq_ir a head cc : Eq h_m h_ir
                    let xor3_eq = Expr::apps(
                        Expr::const_str(names::XOR3_EQ_IR),
                        [a.clone(), head.clone(), cc.clone()],
                    );
                    // step2: congrArg (fun hh => cons hh tail_ir) xor3_eq
                    let cons_tail_fn = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (hh_id, hh) = e.fresh_local(bool_ty());
                        let app = list_cons_bool(hh, tail_ir.clone());
                        e.finish_child(e.mk_lam(hh_id, BinderInfo::Default, bool_ty(), app))
                    };
                    let step2 = congr_arg_bl(h_m.clone(), h_ir.clone(), cons_tail_fn, xor3_eq);
                    // chain: (cons h_m tail_m) = (cons h_m tail_ir) = (cons h_ir tail_ir)
                    let cons_hm_tm = list_cons_bool(h_m.clone(), tail_m.clone());
                    let cons_hm_tir = list_cons_bool(h_m.clone(), tail_ir.clone());
                    let cons_hir_tir = list_cons_bool(h_ir.clone(), tail_ir.clone());
                    let proof = eq_trans_list(cons_hm_tm, cons_hm_tir, cons_hir_tir, step1, step2);
                    let r = d.mk_lam(cc_id, BinderInfo::Default, bool_ty(), proof);
                    d.finish_child(d.mk_lam(ys_id, BinderInfo::Default, list_bool(), r))
                };
                let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let r = c.mk_lam(as_id, BinderInfo::Default, list_bool(), r);
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, bool_ty(), r))
            };
            // @List.rec.{0,0} Bool motive nil_case cons_case xs  (motive into Prop)
            let rec = Expr::apps(
                Expr::const_(
                    Name::from_string("List.rec"),
                    vec![Level::zero(), Level::zero()],
                ),
                [bool_ty(), motive, nil_case, cons_case, xs.clone()],
            );
            // wrap: fun xs ys c => (rec) ys c  — but rec : motive xs = ∀ ys c, …
            // so the full theorem value is fun xs => List.rec … xs   (a ∀ys c proof)
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_bool(), rec))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::ADD_REC_EQ_IR),
            level_params: vec![],
            type_: ty,
            value: val,
        })?;
        Ok(())
    }
}

/// `@congrArg.{1,1} Bool (List Bool) a1 a2 f h` — congrArg for `f : Bool → List Bool`.
fn bool_to_list_congr(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let l1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [bool_ty(), list_bool(), a1, a2, f, h],
    )
}

/// Exhaustive 3-bit `Bool.rec` proof of `Eq Bool (lhs a b c) (rhs a b c)`: split
/// `a`, then `b`, then `c`; each of the 8 ground leaves is `Eq.refl` of the
/// (definitionally-reduced) lhs. The two gate terms agree on every ground input.
fn bvi_bool_split3(
    builder: &EnvDeclBuilder,
    lhs: &impl Fn(Expr, Expr, Expr) -> Expr,
    rhs: &impl Fn(Expr, Expr, Expr) -> Expr,
    a: Expr,
    b: Expr,
    c: Expr,
) -> Expr {
    // innermost: split c, given ground a,b
    let split_c = |ag: Expr, bg: Expr| -> Expr {
        let motive = {
            let mut m = EnvDeclBuilder::child_of(builder);
            let (z_id, z) = m.fresh_local(bool_ty());
            let body = eq_bool(
                lhs(ag.clone(), bg.clone(), z.clone()),
                rhs(ag.clone(), bg.clone(), z),
            );
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, bool_ty(), body))
        };
        let leaf = |cg: Expr| eq_refl_bool(lhs(ag.clone(), bg.clone(), cg));
        bool_rec_prop(motive, leaf(bfalse()), leaf(btrue()), c.clone())
    };
    // split b, given ground a
    let split_b = |ag: Expr| -> Expr {
        let motive = {
            let mut m = EnvDeclBuilder::child_of(builder);
            let (y_id, y) = m.fresh_local(bool_ty());
            let inner = {
                let mut n = EnvDeclBuilder::child_of(&m);
                let (z_id, z) = n.fresh_local(bool_ty());
                let body = eq_bool(
                    lhs(ag.clone(), y.clone(), z.clone()),
                    rhs(ag.clone(), y.clone(), z),
                );
                n.finish_child(n.mk_lam(z_id, BinderInfo::Default, bool_ty(), body))
            };
            // motive over y is itself `∀ c, Eq …` — but Bool.rec needs a non-dependent
            // result here; we instead split c inside each b-leaf. So motive over y is
            // `Eq … at the specific c` only after c is split. To keep it simple we make
            // the b-motive `fun y => Eq Bool (lhs ag y c) (rhs ag y c)` and split c
            // OUTSIDE. Easier: split c first (outermost), then b, then a — see below.
            let _ = inner;
            m.finish_child(m.mk_lam(
                y_id,
                BinderInfo::Default,
                bool_ty(),
                eq_bool(
                    lhs(ag.clone(), y.clone(), c.clone()),
                    rhs(ag.clone(), y.clone(), c.clone()),
                ),
            ))
        };
        // leaves: b ground -> split c
        bool_rec_prop(
            motive,
            split_c(ag.clone(), bfalse()),
            split_c(ag.clone(), btrue()),
            b.clone(),
        )
    };
    // split a (outermost)
    let motive_a = {
        let mut m = EnvDeclBuilder::child_of(builder);
        let (x_id, x) = m.fresh_local(bool_ty());
        m.finish_child(m.mk_lam(
            x_id,
            BinderInfo::Default,
            bool_ty(),
            eq_bool(
                lhs(x.clone(), b.clone(), c.clone()),
                rhs(x.clone(), b.clone(), c.clone()),
            ),
        ))
    };
    bool_rec_prop(motive_a, split_b(bfalse()), split_b(btrue()), a)
}

#[cfg(test)]
#[path = "bitvec_inductive_tests.rs"]
mod tests;
