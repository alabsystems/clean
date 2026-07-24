// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! BitVec substrate + `Pow`/`NatPow` instance stack for the v4.30 carrier
//! reshape (`designs/2026-07-03-carrier-types-bitvec-parity.md` Phase 1).
//!
//! Genuine Lean v4.30 backs every `UInt*`/`USize` by a `BitVec`, and `BitVec w`
//! is `structure BitVec (w : Nat) where ofFin :: (toFin : Fin (2 ^ w))`. Seeding
//! `BitVec` (and the `Pow`/`NatPow` classes its `2 ^ w` index needs) here lets
//! `init_uint_type` reshape `UInt*` to the faithful `ofBitVec`/`toBitVec` shape.
//!
//! Everything here is transcribed byte-faithfully against the v4.30.0-rc2 oracle
//! (`tests/fixtures/carrier_v4_30/oracle_decls.txt`); the seeded-dup value-def-eq
//! gate on import re-checks each one, and the differential harness pins the
//! literal semantics.

use super::algebra_uint_dec_eq_proof::WrapperCarrier;
use super::decl_builder::EnvDeclBuilder;
use super::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// `@OfNat.ofNat.{0} Nat (nat_lit n) (instOfNatNat (nat_lit n))` — the
    /// OfNat-wrapped literal spelling v4.30 uses for BitVec widths / sizes.
    pub(crate) fn ofnat_nat_lit(n: u64) -> Expr {
        let lit = Expr::nat_lit(n);
        Expr::apps(
            Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
            [
                Expr::const_(Name::from_string("Nat"), vec![]),
                lit.clone(),
                Expr::app(Expr::const_(Name::from_string("instOfNatNat"), vec![]), lit),
            ],
        )
    }

    /// `2 ^ w` spelled exactly as the oracle: `@HPow.hPow.{0,0,0} Nat Nat Nat
    /// (@instHPow.{0,0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
    /// (@OfNat.ofNat 2 ..) w`.
    pub(crate) fn two_pow(w: Expr) -> Expr {
        let inst_pow_nat = Expr::apps(
            Expr::const_(Name::from_string("instPowNat"), vec![Level::zero()]),
            [
                Expr::const_(Name::from_string("Nat"), vec![]),
                Expr::const_(Name::from_string("instNatPowNat"), vec![]),
            ],
        );
        let inst_hpow = Expr::apps(
            Expr::const_(
                Name::from_string("instHPow"),
                vec![Level::zero(), Level::zero()],
            ),
            [
                Expr::const_(Name::from_string("Nat"), vec![]),
                Expr::const_(Name::from_string("Nat"), vec![]),
                inst_pow_nat,
            ],
        );
        Expr::apps(
            Expr::const_(
                Name::from_string("HPow.hPow"),
                vec![Level::zero(), Level::zero(), Level::zero()],
            ),
            [
                Expr::const_(Name::from_string("Nat"), vec![]),
                Expr::const_(Name::from_string("Nat"), vec![]),
                Expr::const_(Name::from_string("Nat"), vec![]),
                inst_hpow,
                Self::ofnat_nat_lit(2),
                w,
            ],
        )
    }

    /// Seed `NatPow` + `instNatPowNat`/`instPowNat`/`instHPow` (the generic
    /// instances the BitVec `2 ^ w` index resolves through). `Pow`/`HPow` and
    /// `instOfNatNat` are seeded elsewhere; this pulls them idempotently.
    pub(crate) fn init_pow_nat_instances(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("instHPow")).is_some() {
            return Ok(());
        }
        self.init_nat()?; // Nat + Nat.pow
        self.init_pow()?; // Pow + Pow.pow + Pow.mk
        self.init_hpow()?; // HPow + HPow.hPow + HPow.mk
        self.init_ofnat_nat()?; // instOfNatNat

        let u = Name::from_string("u");
        let u_lvl = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_lvl.clone()));
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);

        // ── NatPow : (α : Type u) → Type u  with  NatPow.mk : (pow : α → Nat → α) → NatPow α ──
        let natpow_c = |lvl: Level| Expr::const_(Name::from_string("NatPow"), vec![lvl]);
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            // pow : α → Nat → α
            let pow_ty = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, _) = s.fresh_local(alpha.clone());
                let (n_id, _) = s.fresh_local(nat.clone());
                let r = alpha.clone();
                let r = s.mk_pi(n_id, BinderInfo::Default, nat.clone(), r);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (pow_id, _) = b.fresh_local(pow_ty.clone());
            let r = Expr::app(natpow_c(u_lvl.clone()), alpha.clone());
            let r = b.mk_pi(pow_id, BinderInfo::Default, pow_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let natpow_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("NatPow"),
                type_: Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone()),
                constructors: vec![Constructor {
                    name: Name::from_string("NatPow.mk"),
                    type_: ctor_type,
                }],
            }],
        };
        self.add_inductive(natpow_ind)?;
        self.register_structure_fields(
            Name::from_string("NatPow"),
            vec![Name::from_string("pow")],
        )?;

        // NatPow.pow : {α : Type u} → (self : NatPow α) → α → Nat → α := fun α self => self.1
        let natpow_pow_ty = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (self_id, _) = b.fresh_local(Expr::app(natpow_c(u_lvl.clone()), alpha.clone()));
            // α → Nat → α
            let r = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, _) = s.fresh_local(alpha.clone());
                let (n_id, _) = s.fresh_local(nat.clone());
                let r = alpha.clone();
                let r = s.mk_pi(n_id, BinderInfo::Default, nat.clone(), r);
                s.finish_child(s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r))
            };
            let r = b.mk_pi(
                self_id,
                BinderInfo::Default,
                Expr::app(natpow_c(u_lvl.clone()), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let natpow_pow_val = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (self_id, self_e) =
                b.fresh_local(Expr::app(natpow_c(u_lvl.clone()), alpha.clone()));
            let body = Expr::proj(Name::from_string("NatPow"), 0, self_e);
            let r = b.mk_lam(
                self_id,
                BinderInfo::Default,
                Expr::app(natpow_c(u_lvl.clone()), alpha.clone()),
                body,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NatPow.pow"),
            level_params: vec![u.clone()],
            type_: natpow_pow_ty,
            value: natpow_pow_val,
            is_reducible: true,
        })?;

        // instNatPowNat : NatPow Nat := @NatPow.mk.{0} Nat Nat.pow
        self.add_decl(Declaration::Definition {
            name: Name::from_string("instNatPowNat"),
            level_params: vec![],
            type_: Expr::app(natpow_c(Level::zero()), nat.clone()),
            value: Expr::apps(
                Expr::const_(Name::from_string("NatPow.mk"), vec![Level::zero()]),
                [
                    nat.clone(),
                    Expr::const_(Name::from_string("Nat.pow"), vec![]),
                ],
            ),
            is_reducible: true,
        })?;

        // instPowNat : {α : Type u} → [NatPow α] → Pow α Nat
        //   := fun {α} [inst] => @Pow.mk.{u,0} α Nat (fun a n => @NatPow.pow.{u} α inst a n)
        {
            let pow_c = |lu: Level, lv: Level| Expr::const_(Name::from_string("Pow"), vec![lu, lv]);
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (inst_id, _) = b.fresh_local(Expr::app(natpow_c(u_lvl.clone()), alpha.clone()));
                let r = Expr::apps(
                    pow_c(u_lvl.clone(), Level::zero()),
                    [alpha.clone(), nat.clone()],
                );
                let r = b.mk_pi(
                    inst_id,
                    BinderInfo::InstImplicit,
                    Expr::app(natpow_c(u_lvl.clone()), alpha.clone()),
                    r,
                );
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (inst_id, inst) =
                    b.fresh_local(Expr::app(natpow_c(u_lvl.clone()), alpha.clone()));
                // fun (a : α) (n : Nat) => @NatPow.pow.{u} α inst a n
                let op = {
                    let mut s = EnvDeclBuilder::child_of(&b);
                    let (a_id, a) = s.fresh_local(alpha.clone());
                    let (n_id, n) = s.fresh_local(nat.clone());
                    let body = Expr::apps(
                        Expr::const_(Name::from_string("NatPow.pow"), vec![u_lvl.clone()]),
                        [alpha.clone(), inst.clone(), a, n],
                    );
                    let r = s.mk_lam(n_id, BinderInfo::Default, nat.clone(), body);
                    s.finish_child(s.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r))
                };
                let body = Expr::apps(
                    Expr::const_(
                        Name::from_string("Pow.mk"),
                        vec![u_lvl.clone(), Level::zero()],
                    ),
                    [alpha.clone(), nat.clone(), op],
                );
                let r = b.mk_lam(
                    inst_id,
                    BinderInfo::InstImplicit,
                    Expr::app(natpow_c(u_lvl.clone()), alpha.clone()),
                    body,
                );
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instPowNat"),
                level_params: vec![u.clone()],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // instHPow : {α : Type u} → {β : Type v} → [Pow α β] → HPow α β α
        //   := fun {α β} [inst] => @HPow.mk.{u,v,u} α β α (fun a b => @Pow.pow.{u,v} α β inst a b)
        {
            let v = Name::from_string("v");
            let v_lvl = Level::param(v.clone());
            let type_v = Expr::sort(Level::succ(v_lvl.clone()));
            let pow_c = |lu: Level, lv: Level| Expr::const_(Name::from_string("Pow"), vec![lu, lv]);
            let hpow_c = |lu: Level, lv: Level, lw: Level| {
                Expr::const_(Name::from_string("HPow"), vec![lu, lv, lw])
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (beta_id, beta) = b.fresh_local(type_v.clone());
                let pow_ab = Expr::apps(
                    pow_c(u_lvl.clone(), v_lvl.clone()),
                    [alpha.clone(), beta.clone()],
                );
                let (inst_id, _) = b.fresh_local(pow_ab.clone());
                let r = Expr::apps(
                    hpow_c(u_lvl.clone(), v_lvl.clone(), u_lvl.clone()),
                    [alpha.clone(), beta.clone(), alpha.clone()],
                );
                let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, pow_ab, r);
                let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (beta_id, beta) = b.fresh_local(type_v.clone());
                let pow_ab = Expr::apps(
                    pow_c(u_lvl.clone(), v_lvl.clone()),
                    [alpha.clone(), beta.clone()],
                );
                let (inst_id, inst) = b.fresh_local(pow_ab.clone());
                let op = {
                    let mut s = EnvDeclBuilder::child_of(&b);
                    let (a_id, a) = s.fresh_local(alpha.clone());
                    let (bb_id, bb) = s.fresh_local(beta.clone());
                    let body = Expr::apps(
                        Expr::const_(
                            Name::from_string("Pow.pow"),
                            vec![u_lvl.clone(), v_lvl.clone()],
                        ),
                        [alpha.clone(), beta.clone(), inst.clone(), a, bb],
                    );
                    let r = s.mk_lam(bb_id, BinderInfo::Default, beta.clone(), body);
                    s.finish_child(s.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r))
                };
                let body = Expr::apps(
                    Expr::const_(
                        Name::from_string("HPow.mk"),
                        vec![u_lvl.clone(), v_lvl.clone(), u_lvl.clone()],
                    ),
                    [alpha.clone(), beta.clone(), alpha.clone(), op],
                );
                let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, pow_ab, body);
                let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), r);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instHPow"),
                level_params: vec![u, v],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        Ok(())
    }

    /// Seed the `BitVec` skeleton + the projections/decEq/order instances the
    /// UInt reshape needs in-env at prelude-init. All transcribed against the
    /// v4.30 oracle; the ~10 seeded names go through the seeded-dup value-def-eq
    /// gate on import (every other `BitVec.*` row stays kernel-verified).
    pub(crate) fn init_bitvec(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("BitVec")).is_some() {
            return Ok(());
        }
        self.init_nat()?;
        self.init_fin()?; // Fin + Fin.val + Fin.mk
        self.init_le()?;
        self.init_lt()?;
        self.init_decidable()?;
        self.init_pow_nat_instances()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let type0 = Expr::sort(Level::succ(Level::zero()));
        let bitvec_c = Expr::const_(Name::from_string("BitVec"), vec![]);
        let fin_c = Expr::const_(Name::from_string("Fin"), vec![]);

        // ── BitVec : (w : Nat) → Type  with  ofFin :: (toFin : Fin (2^w)) ──
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(nat.clone());
            let fin_pow = Expr::app(fin_c.clone(), Self::two_pow(w.clone()));
            let (tofin_id, _) = b.fresh_local(fin_pow.clone());
            let r = Expr::app(bitvec_c.clone(), w.clone());
            let r = b.mk_pi(tofin_id, BinderInfo::Default, fin_pow, r);
            let r = b.mk_pi(w_id, BinderInfo::Implicit, nat.clone(), r);
            b.finish(r)
        };
        let bitvec_ind = InductiveDecl {
            level_params: vec![],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("BitVec"),
                type_: Expr::pi(BinderInfo::Default, nat.clone(), type0.clone()),
                constructors: vec![Constructor {
                    name: Name::from_string("BitVec.ofFin"),
                    type_: ctor_type,
                }],
            }],
        };
        self.add_inductive(bitvec_ind)?;
        self.register_structure_fields(
            Name::from_string("BitVec"),
            vec![Name::from_string("toFin")],
        )?;

        // BitVec.toFin : {w} → (self : BitVec w) → Fin (2^w) := fun w self => self.1
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(nat.clone());
                let (self_id, _) = b.fresh_local(Expr::app(bitvec_c.clone(), w.clone()));
                let r = Expr::app(fin_c.clone(), Self::two_pow(w.clone()));
                let r = b.mk_pi(
                    self_id,
                    BinderInfo::Default,
                    Expr::app(bitvec_c.clone(), w.clone()),
                    r,
                );
                let r = b.mk_pi(w_id, BinderInfo::Implicit, nat.clone(), r);
                b.finish(r)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(nat.clone());
                let (self_id, self_e) = b.fresh_local(Expr::app(bitvec_c.clone(), w.clone()));
                let body = Expr::proj(Name::from_string("BitVec"), 0, self_e);
                let r = b.mk_lam(
                    self_id,
                    BinderInfo::Default,
                    Expr::app(bitvec_c.clone(), w.clone()),
                    body,
                );
                let r = b.mk_lam(w_id, BinderInfo::Implicit, nat.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("BitVec.toFin"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        let bitvec_tofin = Expr::const_(Name::from_string("BitVec.toFin"), vec![]);
        let bitvec_offin = Expr::const_(Name::from_string("BitVec.ofFin"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);

        // BitVec.toNat : {w} → (x : BitVec w) → Nat := fun w x => @Fin.val (2^w) (@BitVec.toFin w x)
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(nat.clone());
                let (x_id, _) = b.fresh_local(Expr::app(bitvec_c.clone(), w.clone()));
                let r = b.mk_pi(
                    x_id,
                    BinderInfo::Default,
                    Expr::app(bitvec_c.clone(), w.clone()),
                    nat.clone(),
                );
                let r = b.mk_pi(w_id, BinderInfo::Implicit, nat.clone(), r);
                b.finish(r)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(nat.clone());
                let (x_id, x) = b.fresh_local(Expr::app(bitvec_c.clone(), w.clone()));
                let tofin = Expr::apps(bitvec_tofin.clone(), [w.clone(), x]);
                let body = Expr::apps(fin_val.clone(), [Self::two_pow(w.clone()), tofin]);
                let r = b.mk_lam(
                    x_id,
                    BinderInfo::Default,
                    Expr::app(bitvec_c.clone(), w.clone()),
                    body,
                );
                let r = b.mk_lam(w_id, BinderInfo::Implicit, nat.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("BitVec.toNat"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // BitVec.ofNatLT : {w} → (i : Nat) → (p : i < 2^w) → BitVec w
        //   := fun w i p => @BitVec.ofFin w (@Fin.mk (2^w) i p)
        {
            let lt = |l: Expr, r: Expr| {
                Expr::apps(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    [
                        nat.clone(),
                        Expr::const_(Name::from_string("instLTNat"), vec![]),
                        l,
                        r,
                    ],
                )
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(nat.clone());
                let (i_id, i) = b.fresh_local(nat.clone());
                let p_ty = lt(i.clone(), Self::two_pow(w.clone()));
                let (p_id, _) = b.fresh_local(p_ty.clone());
                let r = Expr::app(bitvec_c.clone(), w.clone());
                let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
                let r = b.mk_pi(i_id, BinderInfo::Default, nat.clone(), r);
                let r = b.mk_pi(w_id, BinderInfo::Implicit, nat.clone(), r);
                b.finish(r)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(nat.clone());
                let (i_id, i) = b.fresh_local(nat.clone());
                let p_ty = lt(i.clone(), Self::two_pow(w.clone()));
                let (p_id, p) = b.fresh_local(p_ty.clone());
                let fin = Expr::apps(fin_mk.clone(), [Self::two_pow(w.clone()), i.clone(), p]);
                let body = Expr::apps(bitvec_offin.clone(), [w.clone(), fin]);
                let r = b.mk_lam(p_id, BinderInfo::Default, p_ty, body);
                let r = b.mk_lam(i_id, BinderInfo::Default, nat.clone(), r);
                let r = b.mk_lam(w_id, BinderInfo::Implicit, nat.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("BitVec.ofNatLT"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // The BitVec decEq witness chain — `instDecidableEqFin` (the payload
        // discriminant) → `BitVec.decEq` → `instDecidableEqBitVec` — is WITHHELD
        // in IMPORT mode. Its ultimate discriminant is Clean's hand-rolled
        // `Nat.decEq`, which `register_nat_dec_eq_proof` itself suppresses in
        // import mode (it references the gated `Nat.succ_inj` overlay); building
        // this chain there would reference an absent constant and abort the whole
        // import prelude. The genuine `BitVec.decEq`/`instDecidableEqBitVec`/
        // `instDecidableEqFin` arrive through the checked `.olean` import instead
        // (design 2026-07-03 §4.2 / WS17 suppression pattern). In the DEFAULT lane
        // the full chain is built — UInt `.decEq` (`register_wrapper_dec_eq_proof_
        // carrier`, BitVec-carrier branch) depends on it. Pre-P1 parity: the
        // standalone Fin/BitVec decEq builders were never reached during import
        // prelude construction; only `init_bitvec` newly pulls them in, so this
        // gate restores the import lane's baseline shape. The BitVec skeleton and
        // order instances (no `Nat.decEq` dependence) are seeded in BOTH lanes
        // because the UInt reshape needs them at prelude-init time.
        if !self.suppress_lossy_structure_stubs {
            // instDecidableEqFin — the `Fin (2^w)` payload discriminant.
            self.register_fin_dec_eq_proof()?;

            // BitVec.decEq : {w} → (x y : BitVec w) → Decidable (Eq x y)
            //   — rec-destructure both to `Fin (2^w)` payloads, dispatch on
            //   `instDecidableEqFin`, lift isTrue via `congrArg BitVec.ofFin` and
            //   discharge isFalse via `congrArg BitVec.toFin`. Value-def-eq to the
            //   oracle's `match_1 + dite` form (nested casesOn = nested rec, dite =
            //   Decidable.rec, proof args proof-irrelevant).
            self.register_bitvec_dec_eq_proof()?;

            // instDecidableEqBitVec : {w} → DecidableEq (BitVec w) := fun {w} => @BitVec.decEq w
            // Type spelled as the unfolded `(a b : BitVec w) → Decidable (Eq a b)`
            // (`DecidableEq` is not registered this early; the forms are def-eq).
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(nat.clone());
                let bv_w = Expr::app(bitvec_c.clone(), w.clone());
                let (a_id, a) = b.fresh_local(bv_w.clone());
                let (bb_id, bb) = b.fresh_local(bv_w.clone());
                let concl = Expr::app(
                    Expr::const_(Name::from_string("Decidable"), vec![]),
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        [bv_w.clone(), a, bb],
                    ),
                );
                let r = b.mk_pi(bb_id, BinderInfo::Default, bv_w.clone(), concl);
                let r = b.mk_pi(a_id, BinderInfo::Default, bv_w.clone(), r);
                let r = b.mk_pi(w_id, BinderInfo::Implicit, nat.clone(), r);
                b.finish(r)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(nat.clone());
                let body = Expr::app(
                    Expr::const_(Name::from_string("BitVec.decEq"), vec![]),
                    w.clone(),
                );
                let r = b.mk_lam(w_id, BinderInfo::Implicit, nat.clone(), body);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instDecidableEqBitVec"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // instLEBitVec / instLTBitVec : {w} → LE/LT (BitVec w)
        //   := fun {w} => @LE.mk (BitVec w) (fun x1 x2 => Nat.{le,lt} x1.toNat x2.toNat)
        self.register_bitvec_order_instances()?;

        Ok(())
    }

    /// `BitVec.decEq` — parameterized (over `w`) rec-destructure decEq on the
    /// `Fin (2^w)` payloads via `instDecidableEqFin`. Axiom-free; value-def-eq to
    /// the v4.30 oracle by proof-irrelevance on the `Decidable` witnesses.
    fn register_bitvec_dec_eq_proof(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("BitVec.decEq")).is_some() {
            return Ok(());
        }
        let type1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bitvec_c = Expr::const_(Name::from_string("BitVec"), vec![]);
        let fin_c = Expr::const_(Name::from_string("Fin"), vec![]);
        let offin = Expr::const_(Name::from_string("BitVec.ofFin"), vec![]);
        let tofin = Expr::const_(Name::from_string("BitVec.toFin"), vec![]);
        let bv_rec = Expr::const_(Name::from_string("BitVec.rec"), vec![type1.clone()]);
        let eq_ty = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![type1.clone()]);
        let congr = Expr::const_(
            Name::from_string("congrArg"),
            vec![type1.clone(), type1.clone()],
        );
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let fin_dec = Expr::const_(Name::from_string("instDecidableEqFin"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(nat.clone());
            let bv_w = Expr::app(bitvec_c.clone(), w.clone());
            let (x_id, x) = b.fresh_local(bv_w.clone());
            let (y_id, y) = b.fresh_local(bv_w.clone());
            let concl = Expr::app(dec.clone(), Expr::apps(eq_ty.clone(), [bv_w.clone(), x, y]));
            let r = b.mk_pi(y_id, BinderInfo::Default, bv_w.clone(), concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, bv_w.clone(), r);
            let r = b.mk_pi(w_id, BinderInfo::Implicit, nat.clone(), r);
            b.finish(r)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(nat.clone());
            let bv_w = Expr::app(bitvec_c.clone(), w.clone());
            let payload = Expr::app(fin_c.clone(), Self::two_pow(w.clone()));
            let (x_id, x) = b.fresh_local(bv_w.clone());
            let (y_id, y) = b.fresh_local(bv_w.clone());

            let eq_bv = |l: Expr, r: Expr| Expr::apps(eq_ty.clone(), [bv_w.clone(), l, r]);
            let eq_fin = |l: Expr, r: Expr| Expr::apps(eq_ty.clone(), [payload.clone(), l, r]);
            let of = |n: Expr| Expr::apps(offin.clone(), [w.clone(), n]);
            let dec_bv = |l: Expr, r: Expr| Expr::app(dec.clone(), eq_bv(l, r));

            // outer motive: fun (_x : BitVec w) => Decidable (Eq _x y)
            let motive_x = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (xp_id, xp) = c.fresh_local(bv_w.clone());
                c.finish_child(c.mk_lam(
                    xp_id,
                    BinderInfo::Default,
                    bv_w.clone(),
                    dec_bv(xp, y.clone()),
                ))
            };
            // x-minor: fun (n : Fin (2^w)) => @BitVec.rec w motive_y (y-minor) y
            let x_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = c.fresh_local(payload.clone());
                let of_n = of(n.clone());
                let motive_y = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (yp_id, yp) = d.fresh_local(bv_w.clone());
                    d.finish_child(d.mk_lam(
                        yp_id,
                        BinderInfo::Default,
                        bv_w.clone(),
                        dec_bv(of_n.clone(), yp),
                    ))
                };
                let y_minor = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (m_id, m) = d.fresh_local(payload.clone());
                    let of_m = of(m.clone());
                    let p_fin = eq_fin(n.clone(), m.clone());
                    let concl = dec_bv(of_n.clone(), of_m.clone());
                    // Decidable.rec motive
                    let dmotive = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (dsc_id, _) = e.fresh_local(Expr::app(dec.clone(), p_fin.clone()));
                        e.finish_child(e.mk_lam(
                            dsc_id,
                            BinderInfo::Default,
                            Expr::app(dec.clone(), p_fin.clone()),
                            concl.clone(),
                        ))
                    };
                    // isFalse: fun hne => isFalse concl (fun h => hne (congrArg BitVec.toFin h))
                    let is_false_min = {
                        let not_p = Expr::pi(BinderInfo::Default, p_fin.clone(), false_c.clone());
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (hne_id, hne) = e.fresh_local(not_p.clone());
                        let eq_of = eq_bv(of_n.clone(), of_m.clone());
                        let disproof = {
                            let mut g = EnvDeclBuilder::child_of(&e);
                            let (h_id, h) = g.fresh_local(eq_of.clone());
                            // congrArg needs `@BitVec.toFin w : BitVec w → Fin (2^w)`
                            // (the implicit width applied), not the bare const.
                            let tofin_w = Expr::apps(tofin.clone(), [w.clone()]);
                            let cong = Expr::apps(
                                congr.clone(),
                                [
                                    bv_w.clone(),
                                    payload.clone(),
                                    of_n.clone(),
                                    of_m.clone(),
                                    tofin_w,
                                    h,
                                ],
                            );
                            let body = Expr::app(hne.clone(), cong);
                            g.finish_child(g.mk_lam(h_id, BinderInfo::Default, eq_of.clone(), body))
                        };
                        let body = Expr::apps(is_false.clone(), [eq_of, disproof]);
                        e.finish_child(e.mk_lam(hne_id, BinderInfo::Default, not_p, body))
                    };
                    // isTrue: fun heq => isTrue concl (congrArg BitVec.ofFin heq)
                    let is_true_min = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (heq_id, heq) = e.fresh_local(p_fin.clone());
                        // congrArg needs the ofFin partially applied at w: fun n => BitVec.ofFin w n
                        let of_fn = {
                            let mut g = EnvDeclBuilder::child_of(&e);
                            let (k_id, k) = g.fresh_local(payload.clone());
                            g.finish_child(g.mk_lam(
                                k_id,
                                BinderInfo::Default,
                                payload.clone(),
                                of(k),
                            ))
                        };
                        let lifted = Expr::apps(
                            congr.clone(),
                            [
                                payload.clone(),
                                bv_w.clone(),
                                n.clone(),
                                m.clone(),
                                of_fn,
                                heq,
                            ],
                        );
                        let body = Expr::apps(
                            is_true.clone(),
                            [eq_bv(of_n.clone(), of_m.clone()), lifted],
                        );
                        e.finish_child(e.mk_lam(heq_id, BinderInfo::Default, p_fin.clone(), body))
                    };
                    let discriminant = Expr::apps(
                        fin_dec.clone(),
                        [Self::two_pow(w.clone()), n.clone(), m.clone()],
                    );
                    let rec_app = Expr::apps(
                        dec_rec.clone(),
                        [p_fin, dmotive, is_false_min, is_true_min, discriminant],
                    );
                    d.finish_child(d.mk_lam(m_id, BinderInfo::Default, payload.clone(), rec_app))
                };
                let inner = Expr::apps(bv_rec.clone(), [w.clone(), motive_y, y_minor, y.clone()]);
                c.finish_child(c.mk_lam(n_id, BinderInfo::Default, payload.clone(), inner))
            };
            let outer = Expr::apps(bv_rec.clone(), [w.clone(), motive_x, x_minor, x.clone()]);
            let r = b.mk_lam(y_id, BinderInfo::Default, bv_w.clone(), outer);
            let r = b.mk_lam(x_id, BinderInfo::Default, bv_w.clone(), r);
            let r = b.mk_lam(w_id, BinderInfo::Implicit, nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BitVec.decEq"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `instLEBitVec` / `instLTBitVec` — `LE`/`LT (BitVec w)` reducing to
    /// `Nat.le`/`Nat.lt` on `BitVec.toNat`. Backs `UInt*.le`/`UInt*.lt`.
    fn register_bitvec_order_instances(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("instLEBitVec")).is_some() {
            return Ok(());
        }
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bitvec_c = Expr::const_(Name::from_string("BitVec"), vec![]);
        let to_nat = Expr::const_(Name::from_string("BitVec.toNat"), vec![]);

        for (inst, class, mk, rel, nat_inst) in [
            ("instLEBitVec", "LE", "LE.mk", "LE.le", "instLENat"),
            ("instLTBitVec", "LT", "LT.mk", "LT.lt", "instLTNat"),
        ] {
            let class_c = |a: Expr| {
                Expr::app(
                    Expr::const_(Name::from_string(class), vec![Level::zero()]),
                    a,
                )
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(nat.clone());
                let r = class_c(Expr::app(bitvec_c.clone(), w.clone()));
                let r = b.mk_pi(w_id, BinderInfo::Implicit, nat.clone(), r);
                b.finish(r)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(nat.clone());
                let bv_w = Expr::app(bitvec_c.clone(), w.clone());
                // fun (x1 x2 : BitVec w) => Nat.rel (x1.toNat) (x2.toNat)
                let op = {
                    let mut s = EnvDeclBuilder::child_of(&b);
                    let (x1_id, x1) = s.fresh_local(bv_w.clone());
                    let (x2_id, x2) = s.fresh_local(bv_w.clone());
                    let n1 = Expr::apps(to_nat.clone(), [w.clone(), x1]);
                    let n2 = Expr::apps(to_nat.clone(), [w.clone(), x2]);
                    let body = Expr::apps(
                        Expr::const_(Name::from_string(rel), vec![Level::zero()]),
                        [
                            nat.clone(),
                            Expr::const_(Name::from_string(nat_inst), vec![]),
                            n1,
                            n2,
                        ],
                    );
                    let r = s.mk_lam(x2_id, BinderInfo::Default, bv_w.clone(), body);
                    s.finish_child(s.mk_lam(x1_id, BinderInfo::Default, bv_w.clone(), r))
                };
                let body = Expr::apps(
                    Expr::const_(Name::from_string(mk), vec![Level::zero()]),
                    [bv_w.clone(), op],
                );
                let r = b.mk_lam(w_id, BinderInfo::Implicit, nat.clone(), body);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(inst),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    /// Convenience: the `WrapperCarrier::BitVec` for a fixed-width UInt name,
    /// carrying the OfNat-wrapped width literal (`8`/`16`/`32`/`64`).
    pub(crate) fn bitvec_carrier_width(width: u64) -> WrapperCarrier {
        WrapperCarrier::BitVec(Self::ofnat_nat_lit(width))
    }

    /// `BitVec.ofNat : (w n : Nat) → BitVec w` — the numeric-literal lowering
    /// target for `(n : BitVec w)` — plus the `instOfNatBitVec` OfNat instance so
    /// `def x : BitVec 8 := 5` elaborates through OfNat instance synthesis exactly
    /// like `Fin` (see `instOfNatFin`).
    ///
    /// The exact sibling of [`Environment::register_usize_of_nat`]: a genuine
    /// kernel-checked def built from `BitVec.ofNatLT` + `Nat.mod_lt` + a
    /// `Nat.pow_le_pow_right` positivity witness for `0 < 2 ^ w`. The one
    /// difference from the USize sibling is that the width `w` is an *explicit
    /// parameter* rather than the opaque `System.Platform.numBits` const, so the
    /// positivity witness `hpos_w` (which mentions the bound `w`) is built INSIDE
    /// the value lambda where `w` is in scope. NO new lemma is needed — the
    /// task's "`0 < 2^w` may be deep" premise was a false alarm; `2 ^ 0 ≤ 2 ^ w`
    /// via the already-shipped `Nat.pow_le_pow_right` is def-eq to `0 < 2 ^ w`.
    ///
    /// `instOfNatBitVec` deliberately omits any `succ`-constraint (unlike
    /// `instOfNatFin`), because `2 ^ w > 0` for *every* `w`, so `BitVec 0`
    /// literals also elaborate (harmless: `i % 2^0 = i % 1 = 0`).
    ///
    /// Zero axioms; `add_decl` re-checks both terms. Import mode
    /// (`suppress_lossy_structure_stubs`) skips this — the genuine olean-supplied
    /// `BitVec.ofNat` / `instOfNatBitVec` import through the checked path (same as
    /// USize).
    pub(crate) fn register_bitvec_of_nat(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.get_const(&Name::from_string("BitVec.ofNat")).is_some() {
            return Ok(());
        }
        // Dependencies (all idempotent, self-seeding): the BitVec carrier +
        // `BitVec.ofNatLT`, the modulus bound `Nat.mod_lt`, and the
        // pow-monotonicity lemma `Nat.pow_le_pow_right` used for positivity.
        self.init_bitvec()?;
        self.init_nat_div_mod_lemmas()?;
        self.register_nat_pow_le_pow_right_proof()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bitvec_c = Expr::const_(Name::from_string("BitVec"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let one = Expr::app(nat_succ.clone(), nat_zero.clone());
        let two = Expr::app(nat_succ.clone(), one.clone());

        // BitVec.ofNat : (w : Nat) → (n : Nat) → BitVec w
        // Both binders Default — the native reducer `reduce_bitvec_of_nat`
        // treats args[0]=width, args[1]=value as explicit.
        let of_nat_ty = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(nat.clone());
            let (n_id, _n) = b.fresh_local(nat.clone());
            let r = Expr::app(bitvec_c.clone(), w.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), r);
            let r = b.mk_pi(w_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // fun (w n : Nat) => @BitVec.ofNatLT w (Nat.mod n (2^w))
        //                                       (Nat.mod_lt n (2^w) hpos_w)
        // where — because `hpos_w` mentions the BOUND local `w` — the positivity
        // witness is built inside the value lambda:
        //   h12    := Nat.le.step 1 1 (Nat.le.refl 1)          : Nat.le 1 2
        //   hpos_w := Nat.pow_le_pow_right 2 0 w h12 (Nat.zero_le w)
        //             : Nat.le (Nat.pow 2 0) (Nat.pow 2 w) ≡ Nat.lt 0 (2^w).
        // `Self::two_pow(w)` (the HPow `2^w` spelling) is used for the modulus
        // EVERYWHERE so it matches ofNatLT's `Fin (2^w)` carrier and mod_lt's
        // output; hpos_w's `Nat.pow 2 w` form is def-eq to it (same chain the
        // shipped USize sibling discharges).
        let of_nat_val = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(nat.clone());
            let (n_id, n) = b.fresh_local(nat.clone());
            let two_pow_w = Self::two_pow(w.clone());
            let le_refl_1 = Expr::app(
                Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
                one.clone(),
            );
            let h12 = Expr::apps(
                Expr::const_(Name::from_string("Nat.le.step"), vec![]),
                [one.clone(), one.clone(), le_refl_1],
            );
            let zero_le_w = Expr::app(
                Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
                w.clone(),
            );
            let hpos_w = Expr::apps(
                Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]),
                [two.clone(), nat_zero.clone(), w.clone(), h12, zero_le_w],
            );
            let modv = Expr::apps(
                Expr::const_(Name::from_string("Nat.mod"), vec![]),
                [n.clone(), two_pow_w.clone()],
            );
            let modlt = Expr::apps(
                Expr::const_(Name::from_string("Nat.mod_lt"), vec![]),
                [n.clone(), two_pow_w, hpos_w],
            );
            let body = Expr::apps(
                Expr::const_(Name::from_string("BitVec.ofNatLT"), vec![]),
                [w.clone(), modv, modlt],
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(w_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("BitVec.ofNat"),
            level_params: vec![],
            type_: of_nat_ty,
            value: of_nat_val,
            is_reducible: true,
        })?;

        // instOfNatBitVec : {w i : Nat} → OfNat (BitVec w) i
        //   := fun {w i} => OfNat.mk (BitVec w) i (@BitVec.ofNat w i)
        // Mirrors `instOfNatFin` (data.rs) but at `BitVec w : Type 0` and with NO
        // succ-constraint. `OfNat`/`OfNat.mk` are at `Level::zero()`.
        if self
            .get_const(&Name::from_string("instOfNatBitVec"))
            .is_none()
            && self.get_const(&Name::from_string("BitVec.ofNat")).is_some()
            && self.get_const(&Name::from_string("OfNat.mk")).is_some()
        {
            let ofnat_c = Expr::const_(Name::from_string("OfNat"), vec![Level::zero()]);
            let ofnat_mk = Expr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]);
            let bitvec_ofnat = Expr::const_(Name::from_string("BitVec.ofNat"), vec![]);

            let inst_type = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(nat.clone());
                let (i_id, i) = b.fresh_local(nat.clone());
                let bv_w = Expr::app(bitvec_c.clone(), w.clone());
                let e = Expr::apps(ofnat_c.clone(), [bv_w, i.clone()]);
                let e = b.mk_pi(i_id, BinderInfo::Implicit, nat.clone(), e);
                let e = b.mk_pi(w_id, BinderInfo::Implicit, nat.clone(), e);
                b.finish(e)
            };
            let inst_value = {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(nat.clone());
                let (i_id, i) = b.fresh_local(nat.clone());
                let bv_w = Expr::app(bitvec_c.clone(), w.clone());
                // @BitVec.ofNat w i : BitVec w
                let val = Expr::apps(bitvec_ofnat.clone(), [w.clone(), i.clone()]);
                // OfNat.mk (BitVec w) i val
                let body = Expr::apps(ofnat_mk.clone(), [bv_w, i.clone(), val]);
                let e = b.mk_lam(i_id, BinderInfo::Implicit, nat.clone(), body);
                let e = b.mk_lam(w_id, BinderInfo::Implicit, nat.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instOfNatBitVec"),
                level_params: vec![],
                type_: inst_type,
                value: inst_value,
                is_reducible: true,
            })?;
            self.register_instance(crate::env::KernelInstanceInfo {
                name: Name::from_string("instOfNatBitVec"),
                class_name: Name::from_string("OfNat"),
                priority: 100,
                type_: None,
                value: None,
            });
        }
        Ok(())
    }
}
