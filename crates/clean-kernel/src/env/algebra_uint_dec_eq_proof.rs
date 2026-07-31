// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive `<T>.decEq : (a b : <T>) → Decidable (Eq a b)` for the
//! single-constructor `Nat`-wrapper types `UInt8`/`UInt16`/`UInt32`/`UInt64`/
//! `USize`/`Float` — real kernel terms (NO `sorry`, NO axiom), backing the
//! `instDecidableEq<T>` instances so `if ((x : UInt8) = y)` / `decide` resolve an
//! instance and (for concrete literals) fire the sound native `<T>.decEq`
//! reducer, instead of emitting a synthetic `sorry` at elaboration time.
//!
//! Each `<T>` is `structure <T> where val : Nat` — i.e. `<T>.mk : Nat → <T>`,
//! projection `<T>.val : <T> → Nat` with `<T>.val (<T>.mk n) ≡ n` (ι), and a
//! reducible recursor `<T>.rec.{1}`. Equality on `<T>` is therefore decided by
//! equality on the underlying `Nat`, dispatched through the (axiom-free,
//! recursive) `Nat.decEq`.
//!
//! # Proof shape
//!
//! Rather than rely on structure-eta to relate `<T>.mk a.val` to `a` (which does
//! not fire for *symbolic* `a` because both `<T>.val a` and the eta projection
//! `a.0` are stuck on an fvar), we destructure `a` and `b` with `<T>.rec`, so
//! both are *literally* `<T>.mk na` / `<T>.mk nb` in the leaf. Then:
//!
//! ```text
//! <T>.decEq : (a b : <T>) → Decidable (Eq a b) :=
//!   fun (a b : <T>) =>
//!     @<T>.rec.{1} (fun (_a : <T>) => Decidable (Eq <T> _a b))
//!       (fun (na : Nat) =>                              -- a ≡ <T>.mk na
//!          @<T>.rec.{1} (fun (_b : <T>) => Decidable (Eq <T> (<T>.mk na) _b))
//!            (fun (nb : Nat) =>                          -- b ≡ <T>.mk nb
//!               @Decidable.rec.{1} (Eq Nat na nb)
//!                 (fun _ => Decidable (Eq <T> (<T>.mk na) (<T>.mk nb)))     -- motive
//!                 (fun (hne : Eq Nat na nb → False) =>                       -- isFalse minor
//!                    @Decidable.isFalse (Eq <T> (<T>.mk na) (<T>.mk nb))
//!                      (fun (h : Eq <T> (<T>.mk na) (<T>.mk nb)) =>
//!                         hne (@congrArg.{1,1} <T> Nat (<T>.mk na) (<T>.mk nb) <T>.val h)))
//!                 (fun (heq : Eq Nat na nb) =>                               -- isTrue minor
//!                    @Decidable.isTrue (Eq <T> (<T>.mk na) (<T>.mk nb))
//!                      (@congrArg.{1,1} Nat <T> na nb <T>.mk heq))
//!                 (Nat.decEq na nb))
//!            b)
//!       a
//! ```
//!
//! - **isTrue**: `congrArg <T>.mk heq : Eq <T> (<T>.mk na) (<T>.mk nb)` —
//!   *syntactically* the goal, no eta needed.
//! - **isFalse**: from `h : <T>.mk na = <T>.mk nb` derive
//!   `congrArg <T>.val h : Eq Nat (<T>.val (<T>.mk na)) (<T>.val (<T>.mk nb))`;
//!   `<T>.val (<T>.mk n) ≡ n` (ι), so this is `Eq Nat na nb` by def-eq, refuted
//!   by `hne`.
//!
//! # Axiom closure
//!
//! The term mentions only `Eq`, `<T>`, `<T>.mk`, `<T>.val`, `<T>.rec`, `Nat`,
//! `Nat.decEq`, `Decidable`(`.rec`/`.isTrue`/`.isFalse`), `congrArg`, `False` —
//! all constructive (generated recursors / reducible definitions / the
//! axiom-free `Nat.decEq`). So `env.axiom_deps("<T>.decEq")` is empty.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Underlying carrier of a single-constructor wrapper structure, which selects
/// how `<T>.decEq` (and the ordering procs) destructure and compare the payload.
///
/// - `Nat`: `<T>.mk : Nat → <T>`, `<T>.val : <T> → Nat` (Char/Float). Equality
///   is decided by `Nat.decEq` on the `Nat` payloads.
/// - `Fin(size_lit)`: `<T>.mk : Fin <T>.size → <T>`, `<T>.val : <T> → Fin
///   <T>.size` (UInt8/16/32/64, USize — Lean 4.8.0 fidelity). Equality is decided
///   by `instDecidableEqFin` on the `Fin <T>.size` payloads. `size_lit` is the
///   Nat literal `<T>.size` (the `Fin`'s index).
#[derive(Clone)]
pub(crate) enum WrapperCarrier {
    Nat,
    #[cfg(test)]
    Fin(Expr),
    /// v4.30 UInt/USize carrier: `<T>.ofBitVec : BitVec <width> → <T>`,
    /// projection `<T>.toBitVec : <T> → BitVec <width>`. Equality is decided by
    /// `instDecidableEqBitVec` on the `BitVec <width>` payloads. `Expr` is the
    /// width (`8`/`16`/`32`/`64` or `System.Platform.numBits`).
    BitVec(Expr),
}

impl Environment {
    /// Register `<name>.decEq` as a kernel-checked `Declaration::Definition` for a
    /// single-constructor wrapper structure `<name>` with the given `carrier`.
    ///
    /// For a `Nat` carrier (`<name>.mk : Nat → <name>`) equality dispatches on the
    /// axiom-free `Nat.decEq`; for a `Fin <name>.size` carrier
    /// (`<name>.mk : Fin <name>.size → <name>`, Lean 4.8.0's real UInt carrier)
    /// it dispatches on the axiom-free `instDecidableEqFin`. Both destructure both
    /// operands with `<name>.rec` so the leaf sees literal constructor
    /// applications, lift `isTrue` via `congrArg <name>.mk` and discharge
    /// `isFalse` via `congrArg <name>.val`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `<name>`, `<name>.mk`, `<name>.val`, `<name>.rec`, `Nat`,
    ///           `Nat.decEq`, `Eq`, `congrArg`, `Decidable`(+ctors/rec), `False`
    ///           are registered (and, for a `Fin` carrier, `Fin`/`Fin.val`/
    ///           `instDecidableEqFin`). Callers run the relevant `init_*` first.
    /// ENSURES: On success, `<name>.decEq` is a `Definition` whose value
    ///          type-checks at `(a b : <name>) → Decidable (Eq a b)` and whose
    ///          axiom closure is empty.
    /// ENSURES: Idempotent.
    pub(crate) fn register_wrapper_dec_eq_proof_carrier(
        &mut self,
        name: &str,
        carrier: WrapperCarrier,
    ) -> Result<(), EnvError> {
        let dec_eq_name = format!("{name}.decEq");
        if self.get_const(&Name::from_string(&dec_eq_name)).is_some() {
            return Ok(());
        }

        // Dependencies. `init_true_false` before `init_decidable` so
        // `Decidable.isFalse` carries the real `(p → False)` negation type.
        self.init_eq()?;
        self.init_nat()?;
        self.init_true_false()?;
        self.init_decidable()?;
        // The `Nat`-equality discriminant — axiom-free, recursive decision proc.
        self.register_nat_dec_eq_proof()?;
        // The `Fin`-equality discriminant (axiom-free) for a Fin carrier.
        #[cfg(test)]
        if matches!(carrier, WrapperCarrier::Fin(_)) {
            self.register_fin_dec_eq_proof()?;
        }
        // The `BitVec`-equality discriminant for a BitVec carrier (v4.30 UInt).
        if matches!(carrier, WrapperCarrier::BitVec(_)) {
            self.init_bitvec()?;
        }

        // ----- shared constants -----
        // The constructor / payload projection names depend on the carrier: the
        // `Nat`/`Fin` carriers use `<T>.mk`/`<T>.val`; the v4.30 `BitVec` carrier
        // uses `<T>.ofBitVec`/`<T>.toBitVec`. The congrArg-based isTrue/isFalse
        // lifts are proof-irrelevant, so any correct projection to the payload
        // makes the term type-check and value-def-eq to the oracle.
        let (ctor_suffix, proj_suffix) = match &carrier {
            WrapperCarrier::BitVec(_) => ("ofBitVec", "toBitVec"),
            _ => ("mk", "val"),
        };
        let type1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let ty_c = Expr::const_(Name::from_string(name), vec![]);
        let mk_c = Expr::const_(Name::from_string(&format!("{name}.{ctor_suffix}")), vec![]);
        let val_c = Expr::const_(Name::from_string(&format!("{name}.{proj_suffix}")), vec![]);
        let ty_rec = Expr::const_(
            Name::from_string(&format!("{name}.rec")),
            vec![type1.clone()],
        );
        let eq_ty = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![type1.clone()]);
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![type1.clone(), type1.clone()],
        );
        let false_c = Expr::const_(Name::from_string("False"), vec![]);

        // Carrier-dependent pieces:
        //  - `payload_ty`: the constructor field type (`Nat` or `Fin <size>`).
        //  - `payload_eq(l, r)`: `@Eq payload_ty l r`.
        //  - `payload_dec_eq(l, r)`: the `Decidable (@Eq payload_ty l r)`
        //    discriminant (`Nat.decEq l r` or `@instDecidableEqFin size l r`).
        let (payload_ty, payload_dec_eq): (Expr, Box<dyn Fn(Expr, Expr) -> Expr>) = match &carrier {
            WrapperCarrier::Nat => {
                let nat_dec_eq = Expr::const_(Name::from_string("Nat.decEq"), vec![]);
                (
                    nat.clone(),
                    Box::new(move |l: Expr, r: Expr| Expr::apps(nat_dec_eq.clone(), [l, r])),
                )
            }
            #[cfg(test)]
            WrapperCarrier::Fin(size_lit) => {
                let fin_c = Expr::const_(Name::from_string("Fin"), vec![]);
                let fin_size = Expr::app(fin_c, size_lit.clone());
                let fin_dec = Expr::const_(Name::from_string("instDecidableEqFin"), vec![]);
                let size = size_lit.clone();
                (
                    fin_size,
                    Box::new(move |l: Expr, r: Expr| {
                        // @instDecidableEqFin {size} l r  (size is implicit)
                        Expr::apps(fin_dec.clone(), [size.clone(), l, r])
                    }),
                )
            }
            WrapperCarrier::BitVec(width) => {
                let bitvec_c = Expr::const_(Name::from_string("BitVec"), vec![]);
                let bv_w = Expr::app(bitvec_c, width.clone());
                let bv_dec = Expr::const_(Name::from_string("instDecidableEqBitVec"), vec![]);
                let w = width.clone();
                (
                    bv_w,
                    Box::new(move |l: Expr, r: Expr| {
                        // @instDecidableEqBitVec {w} l r  (w is implicit)
                        Expr::apps(bv_dec.clone(), [w.clone(), l, r])
                    }),
                )
            }
        };

        // helper closures
        let mk = |n: Expr| Expr::app(mk_c.clone(), n);
        let eq_t = |l: Expr, r: Expr| Expr::apps(eq_ty.clone(), [ty_c.clone(), l, r]);
        let eq_n = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
                [payload_ty.clone(), l, r],
            )
        };
        let dec_eq_t = |l: Expr, r: Expr| Expr::app(dec.clone(), eq_t(l, r));

        // ----- Type: (a b : <T>) → Decidable (Eq a b) -----
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(ty_c.clone());
            let (bv_id, bv) = b.fresh_local(ty_c.clone());
            let concl = dec_eq_t(a.clone(), bv.clone());
            let e = b.mk_pi(bv_id, BinderInfo::Default, ty_c.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, ty_c.clone(), e);
            b.finish(e)
        };

        // ----- value -----
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(ty_c.clone());
            let (bv_id, bv) = b.fresh_local(ty_c.clone());

            // outer motive: fun (_a : <T>) => Decidable (Eq <T> _a b)
            let motive_a = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ap_id, ap) = c.fresh_local(ty_c.clone());
                c.finish_child(c.mk_lam(
                    ap_id,
                    BinderInfo::Default,
                    ty_c.clone(),
                    dec_eq_t(ap, bv.clone()),
                ))
            };

            // a-minor: fun (na : <payload>) => @<T>.rec.{1} <motive_b> <b-minor> b
            let a_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (na_id, na) = c.fresh_local(payload_ty.clone());
                let mk_na = mk(na.clone());

                // inner motive: fun (_b : <T>) => Decidable (Eq <T> (<T>.mk na) _b)
                let motive_b = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (bp_id, bp) = d.fresh_local(ty_c.clone());
                    d.finish_child(d.mk_lam(
                        bp_id,
                        BinderInfo::Default,
                        ty_c.clone(),
                        dec_eq_t(mk_na.clone(), bp),
                    ))
                };

                // b-minor: fun (nb : <payload>) => @Decidable.rec ... (<payloadDecEq> na nb)
                let b_minor = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (nb_id, nb) = d.fresh_local(payload_ty.clone());
                    let mk_nb = mk(nb.clone());

                    let p_nat = eq_n(na.clone(), nb.clone()); // Eq <payload> na nb
                    let concl = dec_eq_t(mk_na.clone(), mk_nb.clone());

                    // dec.rec motive: fun (_ : Decidable (Eq Nat na nb)) => concl
                    let dmotive = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (dsc_id, _dsc) = e.fresh_local(Expr::app(dec.clone(), p_nat.clone()));
                        e.finish_child(e.mk_lam(
                            dsc_id,
                            BinderInfo::Default,
                            Expr::app(dec.clone(), p_nat.clone()),
                            concl.clone(),
                        ))
                    };

                    // isFalse minor: fun (hne : Eq Nat na nb → False) =>
                    //   @Decidable.isFalse concl
                    //     (fun (h : Eq <T> (mk na) (mk nb)) =>
                    //        hne (@congrArg.{1,1} <T> Nat (mk na) (mk nb) <T>.val h))
                    let is_false_min = {
                        let not_p = Expr::pi(BinderInfo::Default, p_nat.clone(), false_c.clone());
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (hne_id, hne) = e.fresh_local(not_p.clone());
                        let eq_mk = eq_t(mk_na.clone(), mk_nb.clone());
                        let disproof = {
                            let mut g = EnvDeclBuilder::child_of(&e);
                            let (h_id, h) = g.fresh_local(eq_mk.clone());
                            // congrArg <T>.val h : Eq <payload> (<T>.val (mk na)) (<T>.val (mk nb))
                            //                    ≡ Eq <payload> na nb  (ι on <T>.val (<T>.mk _))
                            let cong = Expr::apps(
                                congr_arg.clone(),
                                [
                                    ty_c.clone(),
                                    payload_ty.clone(),
                                    mk_na.clone(),
                                    mk_nb.clone(),
                                    val_c.clone(),
                                    h,
                                ],
                            );
                            let body = Expr::app(hne.clone(), cong);
                            g.finish_child(g.mk_lam(h_id, BinderInfo::Default, eq_mk.clone(), body))
                        };
                        let body = Expr::apps(is_false.clone(), [eq_mk, disproof]);
                        e.finish_child(e.mk_lam(hne_id, BinderInfo::Default, not_p, body))
                    };

                    // isTrue minor: fun (heq : Eq <payload> na nb) =>
                    //   @Decidable.isTrue concl
                    //     (@congrArg.{1,1} <payload> <T> na nb <T>.mk heq)
                    let is_true_min = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (heq_id, heq) = e.fresh_local(p_nat.clone());
                        let lifted = Expr::apps(
                            congr_arg.clone(),
                            [
                                payload_ty.clone(),
                                ty_c.clone(),
                                na.clone(),
                                nb.clone(),
                                mk_c.clone(),
                                heq,
                            ],
                        );
                        let body = Expr::apps(
                            is_true.clone(),
                            [eq_t(mk_na.clone(), mk_nb.clone()), lifted],
                        );
                        e.finish_child(e.mk_lam(heq_id, BinderInfo::Default, p_nat.clone(), body))
                    };

                    let discriminant = payload_dec_eq(na.clone(), nb.clone());
                    let rec_app = Expr::apps(
                        dec_rec.clone(),
                        [p_nat, dmotive, is_false_min, is_true_min, discriminant],
                    );
                    d.finish_child(d.mk_lam(
                        nb_id,
                        BinderInfo::Default,
                        payload_ty.clone(),
                        rec_app,
                    ))
                };

                let inner_rec = Expr::apps(ty_rec.clone(), [motive_b, b_minor, bv.clone()]);
                c.finish_child(c.mk_lam(na_id, BinderInfo::Default, payload_ty.clone(), inner_rec))
            };

            let outer_rec = Expr::apps(ty_rec.clone(), [motive_a, a_minor, a.clone()]);
            let e = b.mk_lam(bv_id, BinderInfo::Default, ty_c.clone(), outer_rec);
            let e = b.mk_lam(a_id, BinderInfo::Default, ty_c.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string(&dec_eq_name),
            level_params: vec![],
            type_,
            value,
            is_reducible: true,
        })
    }

    /// Back-compat shim: register `<name>.decEq` for a `Nat`-carrier wrapper
    /// (Char/Float). Delegates to [`register_wrapper_dec_eq_proof_carrier`] with
    /// [`WrapperCarrier::Nat`].
    pub(crate) fn register_wrapper_dec_eq_proof(&mut self, name: &str) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // if this wrapper's carrier stub was import-suppressed (Fin-carrier
        // UInt8..64/USize/Float — see init_uint8..64), its dec-proof web is
        // suppressed with it; the genuine v4.31 declarations import instead.
        // Wrappers whose carriers remain (Char/String/Int default lanes)
        // register as before.
        if self.suppress_lossy_structure_stubs && self.get_const(&Name::from_string(name)).is_none()
        {
            return Ok(());
        }
        self.register_wrapper_dec_eq_proof_carrier(name, WrapperCarrier::Nat)
    }

    /// Register the genuine v4.30 `Char.decEq : (a b : Char) → Decidable (Eq a b)`
    /// for the 2-field structure `Char.mk (val : UInt32) (valid : val.isValidChar)`.
    ///
    /// Destructures `a`/`b` with `Char.rec` so both are literal `Char.mk vx px`,
    /// dispatches on `instDecidableEqUInt32` of the `UInt32` `val`s:
    /// - **isFalse**: from `h : Char.mk va pa = Char.mk vb pb` derive
    ///   `congrArg Char.val h : va = vb` (`Char.val (Char.mk v p) ≡ v` by ι),
    ///   refuted by the `va ≠ vb` hypothesis.
    /// - **isTrue** (`heq : va = vb`): lift to `Char.mk va pa = Char.mk vb pb` via
    ///   `Eq.rec` on `heq` with a function motive `fun v _ => (pv : v.isValidChar)
    ///   → Char.mk va pa = Char.mk v pv`; the refl case is `Eq.refl (Char.mk va
    ///   pa)`, well-typed because `Char.mk va pa ≡ Char.mk va pv` by PROOF
    ///   IRRELEVANCE of the `valid` field. Applied to `pb`.
    ///
    /// Axiom-free (only recursors / `Eq`/`congrArg` / the axiom-free
    /// `instDecidableEqUInt32`). Idempotent.
    pub(crate) fn register_char_dec_eq_proof(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Char.decEq")).is_some() {
            return Ok(());
        }
        // The `UInt32`-equality discriminant (`Char.mk`'s `val` field). Built
        // here idempotently because the `init_decidable_eq` UInt loop that
        // normally seeds it runs AFTER the Char block.
        self.register_wrapper_dec_eq_proof_carrier(
            "UInt32",
            WrapperCarrier::BitVec(Self::ofnat_nat_lit(32)),
        )?;
        let one = Level::succ(Level::zero());
        let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let char_c = c("Char");
        let u32 = c("UInt32");
        let is_valid = |v: Expr| Expr::app(c("UInt32.isValidChar"), v);
        let eq_char = |x: Expr, y: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
                [char_c.clone(), x, y],
            )
        };
        let eq_u32 = |x: Expr, y: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
                [u32.clone(), x, y],
            )
        };
        let dec = |p: Expr| Expr::app(c("Decidable"), p);
        let mk = |v: Expr, p: Expr| Expr::apps(c("Char.mk"), [v, p]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(char_c.clone());
            let (bb_id, bb) = b.fresh_local(char_c.clone());
            let concl = dec(eq_char(a, bb));
            let r = b.mk_pi(bb_id, BinderInfo::Default, char_c.clone(), concl);
            let r = b.mk_pi(a_id, BinderInfo::Default, char_c.clone(), r);
            b.finish(r)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(char_c.clone());
            let (b_id, bfv) = b.fresh_local(char_c.clone());

            let char_rec = |motive: Expr, minor: Expr, scrut: Expr| {
                Expr::apps(
                    Expr::const_(Name::from_string("Char.rec"), vec![one.clone()]),
                    [motive, minor, scrut],
                )
            };

            // minor_a : (va : UInt32) → (pa : va.isValidChar) → Decidable (Eq (mk va pa) b)
            let minor_a = {
                let (va_id, va) = b.fresh_local(u32.clone());
                let (pa_id, pa) = b.fresh_local(is_valid(va.clone()));
                let a_mk = mk(va.clone(), pa.clone());

                let motive_b = {
                    let (mb_id, mb) = b.fresh_local(char_c.clone());
                    b.mk_lam(
                        mb_id,
                        BinderInfo::Default,
                        char_c.clone(),
                        dec(eq_char(a_mk.clone(), mb)),
                    )
                };
                let minor_b = {
                    let (vb_id, vb) = b.fresh_local(u32.clone());
                    let (pb_id, pb) = b.fresh_local(is_valid(vb.clone()));
                    let b_mk = mk(vb.clone(), pb.clone());
                    let goal = eq_char(a_mk.clone(), b_mk.clone());

                    let motive_d = {
                        let (d_id, _) = b.fresh_local(dec(eq_u32(va.clone(), vb.clone())));
                        b.mk_lam(
                            d_id,
                            BinderInfo::Default,
                            dec(eq_u32(va.clone(), vb.clone())),
                            dec(goal.clone()),
                        )
                    };
                    let false_minor = {
                        let not_eq = Expr::app(c("Not"), eq_u32(va.clone(), vb.clone()));
                        let (hne_id, hne) = b.fresh_local(not_eq.clone());
                        let (h_id, h) = b.fresh_local(goal.clone());
                        let cong = Expr::apps(
                            Expr::const_(
                                Name::from_string("congrArg"),
                                vec![one.clone(), one.clone()],
                            ),
                            [
                                char_c.clone(),
                                u32.clone(),
                                a_mk.clone(),
                                b_mk.clone(),
                                c("Char.val"),
                                h,
                            ],
                        );
                        let disproof_body = Expr::app(hne, cong);
                        let disproof =
                            b.mk_lam(h_id, BinderInfo::Default, goal.clone(), disproof_body);
                        let isfalse = Expr::apps(c("Decidable.isFalse"), [goal.clone(), disproof]);
                        b.mk_lam(hne_id, BinderInfo::Default, not_eq, isfalse)
                    };
                    let true_minor = {
                        let (heq_id, heq) = b.fresh_local(eq_u32(va.clone(), vb.clone()));
                        let motive_ext = {
                            let (v_id, v) = b.fresh_local(u32.clone());
                            let (heq2_id, _) = b.fresh_local(eq_u32(va.clone(), v.clone()));
                            let (pv_id, pv) = b.fresh_local(is_valid(v.clone()));
                            let inner = eq_char(a_mk.clone(), mk(v.clone(), pv.clone()));
                            let body =
                                b.mk_pi(pv_id, BinderInfo::Default, is_valid(v.clone()), inner);
                            // The eq-proof argument of `Eq.rec`'s motive is a
                            // λ-binder (motive : (v) → (va = v) → Sort), NOT a Π.
                            let body = b.mk_lam(
                                heq2_id,
                                BinderInfo::Default,
                                eq_u32(va.clone(), v.clone()),
                                body,
                            );
                            b.mk_lam(v_id, BinderInfo::Default, u32.clone(), body)
                        };
                        let base = {
                            let (pv_id, pv) = b.fresh_local(is_valid(va.clone()));
                            let refl = Expr::apps(
                                Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
                                [char_c.clone(), a_mk.clone()],
                            );
                            let _ = &pv;
                            b.mk_lam(pv_id, BinderInfo::Default, is_valid(va.clone()), refl)
                        };
                        let eqrec = Expr::apps(
                            Expr::const_(
                                Name::from_string("Eq.rec"),
                                vec![Level::zero(), one.clone()],
                            ),
                            [u32.clone(), va.clone(), motive_ext, base, vb.clone(), heq],
                        );
                        let lift = Expr::app(eqrec, pb.clone());
                        let istrue = Expr::apps(c("Decidable.isTrue"), [goal.clone(), lift]);
                        b.mk_lam(
                            heq_id,
                            BinderInfo::Default,
                            eq_u32(va.clone(), vb.clone()),
                            istrue,
                        )
                    };
                    let dec_rec = Expr::apps(
                        Expr::const_(Name::from_string("Decidable.rec"), vec![one.clone()]),
                        [
                            eq_u32(va.clone(), vb.clone()),
                            motive_d,
                            false_minor,
                            true_minor,
                            Expr::apps(c("UInt32.decEq"), [va.clone(), vb.clone()]),
                        ],
                    );
                    let inner = b.mk_lam(pb_id, BinderInfo::Default, is_valid(vb.clone()), dec_rec);
                    b.mk_lam(vb_id, BinderInfo::Default, u32.clone(), inner)
                };
                let inner_rec = char_rec(motive_b, minor_b, bfv.clone());
                let inner = b.mk_lam(pa_id, BinderInfo::Default, is_valid(va.clone()), inner_rec);
                b.mk_lam(va_id, BinderInfo::Default, u32.clone(), inner)
            };

            let motive_a = {
                let (ma_id, ma) = b.fresh_local(char_c.clone());
                b.mk_lam(
                    ma_id,
                    BinderInfo::Default,
                    char_c.clone(),
                    dec(eq_char(ma, bfv.clone())),
                )
            };
            let outer = char_rec(motive_a, minor_a, a.clone());
            let e = b.mk_lam(b_id, BinderInfo::Default, char_c.clone(), outer);
            let e = b.mk_lam(a_id, BinderInfo::Default, char_c.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Char.decEq"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: false,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    const WRAPPERS: &[&str] = &["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Float"];

    /// `with_prelude` initializes `Fin`/`Nat`/all UInt widths/`USize`/`Float`/
    /// `Decidable`, so the wrapper structures' `.toFin`/`.size` axioms type-check.
    /// The explicit `register_wrapper_dec_eq_proof` is idempotent — it asserts
    /// registration regardless of whether `init_decidable_eq` already wired it.
    fn env_with(name: &str) -> Environment {
        let mut env = Environment::with_prelude();
        env.register_wrapper_dec_eq_proof(name).expect("register");
        env
    }

    /// Each `<T>.decEq` registers as a `Definition` (not `Axiom`), idempotently,
    /// and `tc.infer_type` of the const succeeds — proving the whole term
    /// type-checks at `(a b : <T>) → Decidable (Eq a b)`.
    #[test]
    fn test_wrapper_dec_eq_registered_and_type_checks() {
        for &name in WRAPPERS {
            let mut env = env_with(name);
            // idempotent
            env.register_wrapper_dec_eq_proof(name)
                .expect("idempotent re-registration");

            let dec_eq = format!("{name}.decEq");
            let info = env
                .get_const(&Name::from_string(&dec_eq))
                .unwrap_or_else(|| panic!("{dec_eq} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{dec_eq} must be a Definition"
            );
            assert!(info.value.is_some(), "{dec_eq} must retain its value");

            let tc = TypeChecker::with_mode(&env, env.mode());
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(&dec_eq), vec![]))
                .unwrap_or_else(|e| panic!("{dec_eq} should type-check: {e:?}"));
        }
    }

    /// Axiom closure is empty for every width + Float — the sorry/axiom guard.
    #[test]
    fn test_wrapper_dec_eq_axiom_closure_empty() {
        for &name in WRAPPERS {
            let env = env_with(name);
            let dec_eq = format!("{name}.decEq");
            let deps = env
                .axiom_deps(&Name::from_string(&dec_eq))
                .unwrap_or_else(|| panic!("{dec_eq} is registered"));
            let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                names.is_empty(),
                "{dec_eq} must have empty axiom closure, got {names:?}"
            );
        }
    }

    /// The body genuinely dispatches via `Decidable.rec`, `<T>.rec`, `Nat.decEq`,
    /// and lifts via `congrArg` — and contains NO `sorryAx`.
    #[test]
    fn test_wrapper_dec_eq_uses_real_dispatch() {
        fn mentions(e: &Expr, target: &str) -> bool {
            fn go(e: &Expr, target: &str, hit: &mut bool) {
                if *hit {
                    return;
                }
                match e.kind() {
                    ExprKind::Const(n, _) if n.to_string() == target => *hit = true,
                    ExprKind::App(f, a) => {
                        go(f, target, hit);
                        go(a, target, hit);
                    }
                    ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                        go(t, target, hit);
                        go(b, target, hit);
                    }
                    ExprKind::Let(_, t, v, b, _) => {
                        go(t, target, hit);
                        go(v, target, hit);
                        go(b, target, hit);
                    }
                    _ => {}
                }
            }
            let mut hit = false;
            go(e, target, &mut hit);
            hit
        }

        for &name in WRAPPERS {
            let env = env_with(name);
            let dec_eq = format!("{name}.decEq");
            let info = env.get_const(&Name::from_string(&dec_eq)).unwrap();
            let value = info.value.as_ref().expect("Definition has value");
            assert!(
                mentions(value, "Decidable.rec"),
                "{dec_eq} must dispatch via Decidable.rec"
            );
            assert!(
                mentions(value, &format!("{name}.rec")),
                "{dec_eq} must destructure via {name}.rec"
            );
            // Carrier-specific discriminant: Fin-carrier UInt/USize dispatch on
            // `instDecidableEqFin`; Nat-carrier Char/Float dispatch on `Nat.decEq`.
            let discriminant = match super::super::uint_wrapper_carrier(name) {
                WrapperCarrier::BitVec(_) => "instDecidableEqBitVec",
                WrapperCarrier::Fin(_) => "instDecidableEqFin",
                WrapperCarrier::Nat => "Nat.decEq",
            };
            assert!(
                mentions(value, discriminant),
                "{dec_eq} must dispatch via {discriminant}"
            );
            assert!(
                mentions(value, "congrArg"),
                "{dec_eq} must lift via congrArg"
            );
            assert!(
                !mentions(value, "sorryAx"),
                "{dec_eq} must not contain sorryAx"
            );
        }
    }

    /// SYMBOLIC soundness: instantiate `<T>.decEq` on two fresh fvars `a b : <T>`
    /// and infer the type of the application — proving the eta-free lift and the
    /// `congrArg <T>.val`-based disproof actually check inside the kernel for
    /// symbolic args (not just concrete literals reduced by the native reducer).
    #[test]
    fn test_wrapper_dec_eq_symbolic_application_checks() {
        for &name in WRAPPERS {
            let env = env_with(name);
            let dec_eq = format!("{name}.decEq");
            let ty_c = Expr::const_(Name::from_string(name), vec![]);

            // fun (a b : <T>) => <T>.decEq a b  — checking this type-checks (its
            // body is the fully-applied recursor on symbolic a, b) is the in-kernel
            // proof the output is sound for symbolic arguments.
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(ty_c.clone());
            let (bv_id, bv) = b.fresh_local(ty_c.clone());
            let app = Expr::apps(Expr::const_(Name::from_string(&dec_eq), vec![]), [a, bv]);
            let e = b.mk_lam(bv_id, BinderInfo::Default, ty_c.clone(), app);
            let e = b.mk_lam(a_id, BinderInfo::Default, ty_c.clone(), e);
            let term = b.finish(e);

            let tc = TypeChecker::with_mode(&env, env.mode());
            let _ = tc.infer_type(&term).unwrap_or_else(|err| {
                panic!("symbolic application of {dec_eq} should type-check: {err:?}")
            });
        }
    }

    /// `init_decidable_eq` (run by `with_prelude`) registers each
    /// `instDecidableEq<T>` as a resolvable `DecidableEq` class instance, backed
    /// by the real `<T>.decEq` term — so the `decEq` bridge resolves
    /// `Decidable (Eq <T> a b)`. Each instance Definition also type-checks at
    /// `DecidableEq <T>` (no axiom, no sorry).
    #[test]
    fn test_inst_decidable_eq_registered_as_class_instance() {
        let env = Environment::with_prelude();
        let insts = env.get_class_instances(&Name::from_string("DecidableEq"));
        let tc = TypeChecker::with_mode(&env, env.mode());
        for &name in WRAPPERS {
            let inst_name = format!("instDecidableEq{name}");
            assert!(
                insts
                    .iter()
                    .any(|i| i.name == Name::from_string(&inst_name)),
                "{inst_name} must be a registered DecidableEq instance"
            );
            // The instance Definition must itself type-check at `DecidableEq <T>`.
            let info = env
                .get_const(&Name::from_string(&inst_name))
                .unwrap_or_else(|| panic!("{inst_name} should be a registered Definition"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{inst_name} must be a Definition (not Axiom)"
            );
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(&inst_name), vec![]))
                .unwrap_or_else(|e| panic!("{inst_name} should type-check: {e:?}"));
            // No axiom snuck in via the instance.
            let deps = env
                .axiom_deps(&Name::from_string(&inst_name))
                .unwrap_or_else(|| panic!("{inst_name} registered"));
            let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                names.is_empty(),
                "{inst_name} must be axiom-free, got {names:?}"
            );
        }
    }
}
