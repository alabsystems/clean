// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The Lean-core constants a Lean-spelled arithmetic statement names, so the
//! prelude's floor lemmas can state what pinned Lean v4.30.0-rc2 states.
//!
//! `Nat.div_le_self` is `n / k ≤ n` in Lean, and `n / k` is
//! `@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) n k`: it names the
//! homogeneous→heterogeneous bridge `instHDiv`, the `Div` class, and Lean's
//! `Nat.instDiv`. None of those existed in the default prelude — Clean
//! resolves `/` at `Nat` through its own monomorphic `instHDivNat` — so the
//! lemma could only be stated over the bare `Nat.div`, and was a recorded
//! divergence from Lean (`data/prelude_collision_census.json`). This module
//! registers exactly the constants such statements name, each with Lean's type
//! and Lean's value, read off `#check` / `#print` on the pinned binary:
//!
//! ```text
//! class Div (α : Type u) where div : α → α → α          -- and `Mod` / `mod`
//! instHAdd.{u} : {α : Type u} → [Add α] → HAdd α α α := fun {α} [inst] =>
//!   @HAdd.mk α α α fun a b => @Add.add α inst a b       -- and instHMul/Div/Mod
//! Nat.instDiv : Div Nat := @Div.mk Nat Nat.div           -- and Nat.instMod
//! instDivUInt8 : Div UInt8 := @Div.mk UInt8 UInt8.div    -- 8/16/32/64
//! UInt8.instOfNat : {n : Nat} → OfNat UInt8 n :=
//!   fun {n} => @OfNat.mk UInt8 n (UInt8.ofNat n)          -- 8/16/32/64
//! ```
//!
//! # What this deliberately does NOT change
//!
//! None of the new constants is registered with the INSTANCE resolver here.
//! Clean elaborates `a / b : Nat` through `instHDivNat` today, and registering
//! Lean's generic chain beside it would change the elaborated spelling of every
//! operator in the prelude — a different change, with its own blast radius.
//! The homogeneous bridges `instHAdd` / `instHMul` / `instHSub` are the one
//! exception, and not a new one: the elaborator has always registered them
//! (priority 50, below every monomorphic instance) when it seeds them
//! (`clean-elab` `hetero_bridge_seed.rs`); that seed now registers the
//! kernel-defined constant instead of defining its own.
//!
//! IMPORT MODE (`suppress_lossy_structure_stubs`): withheld — the genuine
//! Lean declarations import through the checked path. Nothing here is an
//! axiom; every declaration is kernel-checked by `add_decl`.

use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// `(bridge, hetero class, hetero ctor, homog class, homog method)`, in
/// Lean's naming. `instHSub` is Lean core's too; it is registered with its
/// siblings so the elaborator's bridge seed finds one shape for all three.
const BRIDGES: [(&str, &str, &str, &str, &str); 5] = [
    ("instHAdd", "HAdd", "HAdd.mk", "Add", "Add.add"),
    ("instHSub", "HSub", "HSub.mk", "Sub", "Sub.sub"),
    ("instHMul", "HMul", "HMul.mk", "Mul", "Mul.mul"),
    ("instHDiv", "HDiv", "HDiv.mk", "Div", "Div.div"),
    ("instHMod", "HMod", "HMod.mk", "Mod", "Mod.mod"),
];

/// The four fixed-width carriers (`USize` excluded: its width is abstract).
const UINTS: [&str; 4] = ["UInt8", "UInt16", "UInt32", "UInt64"];

fn cst(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

impl Environment {
    /// Register `Div` / `Mod`, the five `instH*` bridges, `Nat.instDiv` and
    /// `Nat.instMod` (module doc). Idempotent per declaration.
    ///
    /// # Errors
    ///
    /// Propagates any `EnvError` from a dependency initializer or from
    /// `add_decl`'s kernel check.
    pub(crate) fn init_lean_arith_bridges(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_nat()?;
        self.init_add()?;
        self.init_sub()?;
        self.init_mul()?;
        self.init_div()?;
        self.init_mod()?;
        self.init_hadd()?;
        self.init_hsub()?;
        self.init_hmul()?;
        self.init_hdiv()?;
        self.init_hmod()?;

        for (bridge, hclass, hctor, class, method) in BRIDGES {
            self.add_lean_bridge(bridge, hclass, hctor, class, method)?;
        }
        let nat = cst("Nat", vec![]);
        for (name, class_ctor, op) in [
            ("Nat.instDiv", "Div.mk", "Nat.div"),
            ("Nat.instMod", "Mod.mk", "Nat.mod"),
        ] {
            let class = class_ctor.trim_end_matches(".mk");
            self.add_if_absent(Declaration::Definition {
                name: Name::from_string(name),
                level_params: vec![],
                type_: Expr::app(cst(class, vec![Level::zero()]), nat.clone()),
                value: Expr::app(
                    Expr::app(cst(class_ctor, vec![Level::zero()]), nat.clone()),
                    cst(op, vec![]),
                ),
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    /// `instDivUIntN : Div UIntN` and `UIntN.instOfNat : {n} → OfNat UIntN n`
    /// for the four fixed widths (module doc). Idempotent per declaration.
    ///
    /// # Errors
    ///
    /// Propagates any `EnvError` from a dependency initializer or from
    /// `add_decl`'s kernel check.
    pub(crate) fn init_lean_uint_instances(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_lean_arith_bridges()?;
        self.init_ofnat()?;
        self.init_uint_types()?;
        self.init_uint_arith()?; // UIntN.div
        let nat = cst("Nat", vec![]);
        for ty_name in UINTS {
            let ty = cst(ty_name, vec![]);
            self.add_if_absent(Declaration::Definition {
                name: Name::from_string(&format!("instDiv{ty_name}")),
                level_params: vec![],
                type_: Expr::app(cst("Div", vec![Level::zero()]), ty.clone()),
                value: Expr::app(
                    Expr::app(cst("Div.mk", vec![Level::zero()]), ty.clone()),
                    cst(&format!("{ty_name}.div"), vec![]),
                ),
                is_reducible: true,
            })?;
            // fun {n : Nat} => @OfNat.mk.{0} UIntN n (UIntN.ofNat n)
            let of_nat_ty = Expr::apps(
                cst("OfNat", vec![Level::zero()]),
                [ty.clone(), Expr::bvar(0)],
            );
            let body = Expr::apps(
                cst("OfNat.mk", vec![Level::zero()]),
                [
                    ty.clone(),
                    Expr::bvar(0),
                    Expr::app(cst(&format!("{ty_name}.ofNat"), vec![]), Expr::bvar(0)),
                ],
            );
            self.add_if_absent(Declaration::Definition {
                name: Name::from_string(&format!("{ty_name}.instOfNat")),
                level_params: vec![],
                type_: Expr::pi(BinderInfo::Implicit, nat.clone(), of_nat_ty),
                value: Expr::lam(BinderInfo::Implicit, nat.clone(), body),
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    /// `bridge.{u} : {α : Type u} → [Homog α] → Hetero α α α :=
    ///   fun {α} [inst] => @Hetero.mk α α α fun a b => @Homog.method α inst a b`
    fn add_lean_bridge(
        &mut self,
        bridge: &str,
        hclass: &str,
        hctor: &str,
        class: &str,
        method: &str,
    ) -> Result<(), EnvError> {
        let u = Level::param(Name::from_string("u"));
        let type_u = Expr::sort(Level::succ(u.clone()));
        let uuu = vec![u.clone(), u.clone(), u.clone()];
        // Under `{α} [inst]`: α = BVar(1), inst = BVar(0).
        let homog = |alpha: Expr| Expr::app(cst(class, vec![u.clone()]), alpha);
        let hetero_at = |head: &str, alpha: Expr| {
            Expr::apps(
                cst(head, uuu.clone()),
                [alpha.clone(), alpha.clone(), alpha],
            )
        };
        let type_ = Expr::pi(
            BinderInfo::Implicit,
            type_u.clone(),
            Expr::pi(
                BinderInfo::InstImplicit,
                homog(Expr::bvar(0)),
                hetero_at(hclass, Expr::bvar(1)),
            ),
        );
        // `fun a b => @Homog.method α inst a b` under `{α} [inst]`: inside the
        // two new binders α = BVar(3), inst = BVar(2), a = BVar(1), b = BVar(0).
        let op = Expr::lam(
            BinderInfo::Default,
            Expr::bvar(1),
            Expr::lam(
                BinderInfo::Default,
                Expr::bvar(2),
                Expr::apps(
                    cst(method, vec![u.clone()]),
                    [Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
                ),
            ),
        );
        let value = Expr::lam(
            BinderInfo::Implicit,
            type_u,
            Expr::lam(
                BinderInfo::InstImplicit,
                homog(Expr::bvar(0)),
                Expr::app(hetero_at(hctor, Expr::bvar(1)), op),
            ),
        );
        self.add_if_absent(Declaration::Definition {
            name: Name::from_string(bridge),
            level_params: vec![Name::from_string("u")],
            type_,
            value,
            is_reducible: true,
        })
    }

    /// `add_decl` unless a constant of that name is already registered.
    fn add_if_absent(&mut self, decl: Declaration) -> Result<(), EnvError> {
        let name = match &decl {
            Declaration::Definition { name, .. } => name.clone(),
            _ => return self.add_decl(decl),
        };
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(decl)
    }
}

#[cfg(test)]
#[path = "lean_arith_bridges_tests.rs"]
mod tests;
