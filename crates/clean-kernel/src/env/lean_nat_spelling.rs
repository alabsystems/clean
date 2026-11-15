// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's exact spelling of the `Nat` notation a prelude statement is written
//! in, so a Clean-registered lemma states what pinned Lean v4.30.0-rc2 states,
//! constant for constant.
//!
//! The prelude's older floor lemmas were stated over the BARE functions
//! (`Nat.le a (Nat.add b a)`) where Lean states them through the class
//! notation (`@LE.le Nat instLENat a (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat
//! instAddNat) b a)`). The two are definitionally equal — every instance
//! δ-reduces to the bare function — but `rw` / `simp` match the term as
//! written, and `data/prelude_collision_census.json` compares the statements
//! structurally, so each such lemma was a recorded divergence from Lean. Every
//! builder here is read off `#check` under `pp.explicit` / `pp.universes` on
//! the pinned binary; nothing is inferred.

use crate::expr::{Expr, MDataValue};
use crate::level::Level;
use crate::name::Name;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn c0(name: &str, arity: usize) -> Expr {
    Expr::const_(Name::from_string(name), vec![Level::zero(); arity])
}

/// Builders for Lean's `Nat` spellings (all at universe 0).
pub(crate) struct LeanNat;

impl LeanNat {
    pub(crate) fn nat() -> Expr {
        c("Nat")
    }

    /// `@LE.le.{0} Nat instLENat a b`
    pub(crate) fn le(a: Expr, b: Expr) -> Expr {
        Expr::apps(c0("LE.le", 1), [Self::nat(), c("instLENat"), a, b])
    }

    /// `@LT.lt.{0} Nat instLTNat a b`
    pub(crate) fn lt(a: Expr, b: Expr) -> Expr {
        Expr::apps(c0("LT.lt", 1), [Self::nat(), c("instLTNat"), a, b])
    }

    /// `@GE.ge.{0} Nat instLENat a b`
    pub(crate) fn ge(a: Expr, b: Expr) -> Expr {
        Expr::apps(c0("GE.ge", 1), [Self::nat(), c("instLENat"), a, b])
    }

    /// `Not p`
    pub(crate) fn not(p: Expr) -> Expr {
        Expr::app(c("Not"), p)
    }

    /// `@Eq.{1} Nat a b`
    pub(crate) fn eq(a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [Self::nat(), a, b],
        )
    }

    /// `@HAdd.hAdd.{0,0,0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b`
    pub(crate) fn add(a: Expr, b: Expr) -> Expr {
        Self::hetero("HAdd.hAdd", "instHAdd", "instAddNat", a, b)
    }

    /// `@HMul.hMul.{0,0,0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a b`
    pub(crate) fn mul(a: Expr, b: Expr) -> Expr {
        Self::hetero("HMul.hMul", "instHMul", "instMulNat", a, b)
    }

    /// `@HDiv.hDiv.{0,0,0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) a b`
    pub(crate) fn div(a: Expr, b: Expr) -> Expr {
        Self::hetero("HDiv.hDiv", "instHDiv", "Nat.instDiv", a, b)
    }

    /// `@HMod.hMod.{0,0,0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) a b`
    pub(crate) fn modulo(a: Expr, b: Expr) -> Expr {
        Self::hetero("HMod.hMod", "instHMod", "Nat.instMod", a, b)
    }

    /// `@H.op.{0,0,0} T T T (@bridge.{0} T homog) a b` over `carrier`.
    pub(crate) fn hetero_at(
        carrier: &Expr,
        op: &str,
        bridge: &str,
        homog: &str,
        a: Expr,
        b: Expr,
    ) -> Expr {
        let inst = Expr::apps(c0(bridge, 1), [carrier.clone(), c(homog)]);
        Expr::apps(
            c0(op, 3),
            [
                carrier.clone(),
                carrier.clone(),
                carrier.clone(),
                inst,
                a,
                b,
            ],
        )
    }

    fn hetero(op: &str, bridge: &str, homog: &str, a: Expr, b: Expr) -> Expr {
        Self::hetero_at(&Self::nat(), op, bridge, homog, a, b)
    }

    /// `@OfNat.ofNat.{0} Nat (nat_lit n) (instOfNatNat (nat_lit n))` — the
    /// numeral `n` as Lean elaborates it at `Nat`.
    pub(crate) fn lit(n: u64) -> Expr {
        Expr::apps(
            c0("OfNat.ofNat", 1),
            [
                Self::nat(),
                Expr::nat_lit(n),
                Expr::app(c("instOfNatNat"), Expr::nat_lit(n)),
            ],
        )
    }

    /// `@HPow.hPow.{0,0,0} Nat Nat Nat
    ///    (@instHPow.{0,0} Nat Nat (@instPowNat.{0} Nat instNatPowNat)) a b`
    pub(crate) fn pow(a: Expr, b: Expr) -> Expr {
        let pow_nat = Expr::apps(c0("instPowNat", 1), [Self::nat(), c("instNatPowNat")]);
        let inst = Expr::apps(c0("instHPow", 2), [Self::nat(), Self::nat(), pow_nat]);
        Expr::apps(
            c0("HPow.hPow", 3),
            [Self::nat(), Self::nat(), Self::nat(), inst, a, b],
        )
    }

    /// `@Min.min.{0} Nat instMinNat a b`
    pub(crate) fn min(a: Expr, b: Expr) -> Expr {
        Expr::apps(c0("Min.min", 1), [Self::nat(), c("instMinNat"), a, b])
    }

    /// `mdata {borrowed := true} ty` — Lean's `@& ty` (a borrowed argument of
    /// an `@[extern]` / implemented function), which it stores on the binder
    /// DOMAIN (`Nat.toUInt8 : (n : @& Nat) → UInt8`).
    pub(crate) fn borrowed(ty: Expr) -> Expr {
        Expr::mdata(
            vec![(Name::from_string("borrowed"), MDataValue::Bool(true))],
            ty,
        )
    }

    /// `mdata {noindex := true} e` — Lean's `no_index e`, which keeps a
    /// subterm out of the simp discrimination tree (`UInt8.toNat_ofNat`).
    pub(crate) fn noindex(e: Expr) -> Expr {
        Expr::mdata(
            vec![(Name::from_string("noindex"), MDataValue::Bool(true))],
            e,
        )
    }
}
