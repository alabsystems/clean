// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `UIntN.toNat` bridge a Trust contract cites to discharge a
//! division-carrying clause.
//!
//! ```text
//! UIntN.toNat_lt        : ∀ (n : UIntN), n.toNat < 2 ^ N
//! UIntN.toNat_div       : ∀ (a b : UIntN), (a / b).toNat = a.toNat / b.toNat
//! UIntN.lt_iff_toNat_lt : ∀ {a b : UIntN}, a < b ↔ a.toNat < b.toNat
//! UIntN.le_iff_toNat_le : ∀ {a b : UIntN}, a ≤ b ↔ a.toNat ≤ b.toNat
//! UIntN.toNat_ofNat     : ∀ {n : Nat}, (no_index (OfNat.ofNat n : UIntN)).toNat = n % 2 ^ N
//! ```
//!
//! for `N ∈ {8, 16, 32, 64}` — pinned Lean v4.30.0-rc2's statements exactly
//! (`#check` under `pp.explicit`, `repr` of the stored type for the
//! `no_index` mdata): implicit arguments, `/` as `@HDiv.hDiv UIntN UIntN UIntN
//! (@instHDiv UIntN instDivUIntN)`, the bound spelled `2 ^ N` through
//! `instHPow` / `instPowNat` / `instNatPowNat`, `%` through `Nat.instMod`, and
//! the numeral `@OfNat.ofNat UIntN n (@UIntN.instOfNat n)`
//! (`lean_nat_spelling.rs`, `lean_arith_bridges.rs`). Until 2026-09-30 they
//! were stated over the bare `UIntN.div` / `Nat.div` / `Nat.mod` /
//! `UIntN.ofNat` with a `UIntN.size` bound and every argument explicit; the
//! proofs are unchanged — each notation δ-reduces to the function it names,
//! and `2 ^ N` evaluates to `UIntN.size`.
//!
//! # The comparison bridge is DEFINITIONAL, and that is exactly why it needs a name
//!
//! Measured on this branch before the lemmas were written: all three of
//!
//! ```lean
//! theorem t1 (a b : UInt32) : Iff (LT.lt a b) (Nat.lt (UInt32.toNat a) (UInt32.toNat b)) :=
//!   Iff.intro (fun h => h) (fun h => h)
//! theorem t2 (a b : UInt32) : Iff (LE.le a b) (Nat.le (UInt32.toNat a) (UInt32.toNat b)) :=
//!   Iff.intro (fun h => h) (fun h => h)
//! theorem t3 (n : Nat) : Eq (UInt32.toNat (UInt32.ofNat n)) (Nat.mod n UInt32.size) := rfl
//! ```
//!
//! already CHECK — the carrier chain
//! `@LT.lt UIntN instLTUIntN a b` → `UIntN.lt a b`
//! → `@LT.lt (BitVec w) (instLTBitVec w) a.toBitVec b.toBitVec`
//! → `Nat.lt (BitVec.toNat w a.toBitVec) (BitVec.toNat w b.toBitVec)`
//! is δ all the way down, and `UIntN.toNat` is the same composite
//! (`algebra_uint_dec_le_proof.rs`, `data_types_bitvec.rs`,
//! `data_types_uint.rs`).
//!
//! So these lemmas add no mathematical content. What they add is a SYNTACTIC
//! handle. `rw`, `simp` and `omega` work on the term as written, not up to
//! `whnf`: a3d's `depth_fits_eq_span_fits` reduces to an `Iff` between a
//! `UInt32` comparison and a `Nat` one, and `omega` answers
//! `could not extract linear constraints` because nothing in the goal it can
//! see is arithmetic. A named `Iff` is what lets `rw` turn one carrier into the
//! other before the arithmetic solver is asked anything. Proving it is the
//! cheap part; HAVING it is the whole point — which is why the proof terms
//! below are `Iff.intro (fun h => h) (fun h => h)` and `Eq.refl`, deliberately
//! and with the reduction chain written out rather than hidden.
//!
//! # Why `toNat_div` is the payoff
//!
//! A Trust contract's `as nat` lift discharges definitionally only when the
//! Rust body's `Nat` image needs no modular reasoning. `UInt32.div` is
//! `fun a b => UInt32.ofNat (Nat.div a.toNat b.toNat)` and `UInt32.ofNat`
//! reduces mod `2^32`, so
//!
//! ```text
//! UInt32.toNat (a / k)  ≡  Nat.mod (Nat.div a.toNat k.toNat) 4294967296
//! ```
//!
//! while the contract's goal is `Nat.div a.toNat k.toNat`. The two are equal —
//! a quotient of a bounded number is bounded — but only by THEOREM, which is
//! why `rfl` declines and the row fail-closes to `Unknown`. `toNat_div` is
//! that theorem, and its proof is the three-line one the report predicted:
//!
//! ```text
//! Nat.mod_eq_of_lt _ _ (Nat.lt_of_le_of_lt _ _ _ (Nat.div_le_self _ _) (UInt32.toNat_lt a))
//! ```
//!
//! `Nat.mod_eq_of_lt` and `Nat.div_le_self` come from
//! `nat_floor_order_lemmas.rs`; `Nat.lt_of_le_of_lt` was already present.
//!
//! `toNat_lt` itself is not an induction: `UIntN.toNat x` δ-reduces to
//! `Fin.val (2^N) (BitVec.toFin N x.toBitVec)`, so the bound IS the `Fin`
//! carrier's own `isLt` field, read out by `Fin.isLt`.
//!
//! # Statement shape
//!
//! The bound is stated as Lean states it, `2 ^ N`, not against `UIntN.size`.
//! `UIntN.size` is a reducible `Definition` equal to that power
//! (`data_types_uint.rs`), so a goal spelled either way is closed by this
//! lemma.
//!
//! No `sorry`, no new axiom.

use super::decl_builder::EnvDeclBuilder;
use super::lean_nat_spelling::LeanNat;
use super::nat_floor_order_lemmas::FloorConsts;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Which order relation a `*_iff_toNat_*` bridge is being built for. The two
/// differ only in four names, so they share one builder.
#[derive(Clone, Copy)]
enum OrderSide {
    Lt,
    Le,
}

impl OrderSide {
    /// `lt_iff_toNat_lt` / `le_iff_toNat_le`.
    fn lemma_suffix(self) -> &'static str {
        match self {
            Self::Lt => "lt_iff_toNat_lt",
            Self::Le => "le_iff_toNat_le",
        }
    }
    /// The class projection the surface `<` / `≤` elaborates to.
    fn projection(self) -> &'static str {
        match self {
            Self::Lt => "LT.lt",
            Self::Le => "LE.le",
        }
    }
    /// `instLT` / `instLE`, completed with the UInt type name.
    fn inst_prefix(self) -> &'static str {
        match self {
            Self::Lt => "instLT",
            Self::Le => "instLE",
        }
    }
    fn nat_inst(self) -> &'static str {
        match self {
            Self::Lt => "instLTNat",
            Self::Le => "instLENat",
        }
    }
}

/// The four concrete widths. `USize` is excluded on purpose: its width is
/// platform-abstract, so `USize.size` is `2 ^ numBits` with no literal behind
/// it and `USize.div` is not seeded by `init_uint_arith` either.
const WIDTHS: [(&str, u64); 4] = [("UInt8", 8), ("UInt16", 16), ("UInt32", 32), ("UInt64", 64)];

impl Environment {
    /// Register `UInt{8,16,32,64}.toNat_lt` and `.toNat_div` as kernel-checked
    /// theorems. Idempotent per-lemma.
    ///
    /// # Errors
    ///
    /// Propagates any `EnvError` from a dependency initializer or from
    /// `add_decl`'s kernel check of a proof term.
    pub(crate) fn init_uint_floor_tonat_lemmas(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode gate — the whole Fin/BitVec-carrier UInt
        // cluster (`UIntN.toNat`/`.ofNat`/`.div`, `Fin.isLt`) is suppressed in
        // import mode so the genuine v4.31 declarations import through the
        // checked path; these lemmas are stated over exactly those seeds.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        self.init_lt()?;
        self.init_le()?;
        self.init_iff()?;
        self.init_uint_types()?; // UIntN, .toNat, .toBitVec, .size (+ BitVec, Fin)
        self.init_uint_arith()?; // UIntN.div
        self.init_uint_decidable_ord()?; // UIntN.le/.lt, instLE/instLT UIntN
        self.init_nat_floor_order_lemmas()?; // Nat.mod_eq_of_lt, Nat.div_le_self
        self.register_nat_lt_of_le_of_lt_proof()?; // quotient bound in UInt.toNat_div
                                                   // `instDivUIntN`, `UIntN.instOfNat` — the constants Lean's statements name.
        self.init_lean_uint_instances()?;

        let c = FloorConsts::new();
        for (name, width) in WIDTHS {
            self.register_uint_tonat_lt(name, width)?;
            self.register_uint_tonat_div(name)?;
            self.register_uint_order_iff(&c, name, OrderSide::Lt)?;
            self.register_uint_order_iff(&c, name, OrderSide::Le)?;
            self.register_uint_tonat_ofnat(&c, name)?;
        }
        Ok(())
    }

    /// `theorem <T>.{lt,le}_iff_toNat_{lt,le} {a b : <T>}
    ///   : Iff (@LT.lt <T> instLT<T> a b) (@LT.lt Nat instLTNat (<T>.toNat a) (<T>.toNat b))`
    ///
    /// Stated with the TYPECLASS `<`/`≤` on BOTH sides — the spelling `a < b`
    /// elaborates to on each carrier — so `rw` matches a user's goal as
    /// written. The proof is the identity both ways: the two sides are
    /// definitionally the same proposition (see the module doc), which is a
    /// statement about this carrier and NOT a general fact, so it is pinned by
    /// a control test rather than assumed.
    fn register_uint_order_iff(
        &mut self,
        c: &FloorConsts,
        ty_name: &str,
        side: OrderSide,
    ) -> Result<(), EnvError> {
        let name = Name::from_string(&format!("{ty_name}.{}", side.lemma_suffix()));
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = FloorConsts::const_(ty_name);
        let to_nat = FloorConsts::const_(&format!("{ty_name}.toNat"));
        let rel = Expr::const_(Name::from_string(side.projection()), vec![Level::zero()]);
        let uint_inst = FloorConsts::const_(&format!("{}{ty_name}", side.inst_prefix()));
        let nat_inst = FloorConsts::const_(side.nat_inst());
        let iff = FloorConsts::const_("Iff");
        let iff_intro = FloorConsts::const_("Iff.intro");

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ty.clone());
        let (bv_id, bv) = b.fresh_local(ty.clone());

        // `@LT.lt <T> instLT<T> a b` / `@LE.le <T> instLE<T> a b`
        let lhs = Expr::apps(rel.clone(), [ty.clone(), uint_inst, a.clone(), bv.clone()]);
        // `@LT.lt Nat instLTNat a.toNat b.toNat` / the `LE` twin
        let rhs = Expr::apps(
            rel,
            [
                c.nat.clone(),
                nat_inst,
                Expr::app(to_nat.clone(), a.clone()),
                Expr::app(to_nat, bv.clone()),
            ],
        );

        // `∀ {a b : <T>}` — Lean's binders (pinned v4.30.0-rc2).
        let type_ = {
            let concl = Expr::apps(iff, [lhs.clone(), rhs.clone()]);
            let e = b.mk_pi(bv_id, BinderInfo::Implicit, ty.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Implicit, ty.clone(), e);
            b.finish(e)
        };

        // `fun (h : lhs) => h` and `fun (h : rhs) => h`: the two sides are the
        // same proposition after δ.
        let ident = |dom: &Expr, parent: &EnvDeclBuilder| {
            let mut ib = EnvDeclBuilder::child_of(parent);
            let (h_id, h) = ib.fresh_local(dom.clone());
            ib.finish_child(ib.mk_lam(h_id, BinderInfo::Default, dom.clone(), h))
        };

        let value = {
            let mp = ident(&lhs, &b);
            let mpr = ident(&rhs, &b);
            let body = Expr::apps(iff_intro, [lhs, rhs, mp, mpr]);
            let e = b.mk_lam(bv_id, BinderInfo::Implicit, ty.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Implicit, ty, e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem <T>.toNat_ofNat {n : Nat}
    ///   : @Eq Nat (<T>.toNat (no_index (@OfNat.ofNat <T> n (@<T>.instOfNat n))))
    ///       (n % 2 ^ w)`
    ///
    /// The TRUE statement, checked against the carrier rather than assumed:
    /// `<T>.ofNat n ≡ <T>.ofBitVec (BitVec.ofFin w (Fin.ofNat (2^w - 1) n))`
    /// and `Fin.ofNat` is `Fin.mk (Nat.mod n (Nat.succ (2^w - 1))) _`, so the
    /// round trip is `n` reduced MOD the width — never `n` itself. `rfl`
    /// closes it; the modulus is spelled `<T>.size` for the same reason
    /// `toNat_lt` is (see the module doc).
    fn register_uint_tonat_ofnat(
        &mut self,
        c: &FloorConsts,
        ty_name: &str,
    ) -> Result<(), EnvError> {
        let name = Name::from_string(&format!("{ty_name}.toNat_ofNat"));
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let to_nat = FloorConsts::const_(&format!("{ty_name}.toNat"));
        let inst_of_nat = FloorConsts::const_(&format!("{ty_name}.instOfNat"));
        let width = WIDTHS
            .iter()
            .find(|(t, _)| *t == ty_name)
            .map_or(0, |(_, w)| *w);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let rhs = LeanNat::modulo(
            n.clone(),
            LeanNat::pow(LeanNat::lit(2), LeanNat::lit(width)),
        );

        let type_ = {
            let numeral = Expr::apps(
                Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
                [
                    FloorConsts::const_(ty_name),
                    n.clone(),
                    Expr::app(inst_of_nat, n.clone()),
                ],
            );
            let lhs = Expr::app(to_nat, LeanNat::noindex(numeral));
            let concl = LeanNat::eq(lhs, rhs.clone());
            b.finish(b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), concl))
        };
        let value = {
            let body = c.refl(rhs);
            b.finish(b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), body))
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem <T>.toNat_lt (n : <T>) : n.toNat < 2 ^ w` (Lean's statement)
    ///
    /// ```text
    /// fun x => @Fin.isLt (2 ^ w) (@BitVec.toFin w (<T>.toBitVec x))
    /// ```
    ///
    /// `Fin.isLt : {n} → (x : Fin n) → Nat.lt (Fin.val x) n` and
    /// `<T>.toNat x ≡ BitVec.toNat w x.toBitVec ≡ Fin.val (2^w) (BitVec.toFin w x.toBitVec)`,
    /// so both sides of the conclusion match after δ; `<T>.size ≡ 2 ^ w` is the
    /// same def-eq `<T>.ofNatLT`'s own type already relies on.
    fn register_uint_tonat_lt(&mut self, ty_name: &str, width: u64) -> Result<(), EnvError> {
        let name = Name::from_string(&format!("{ty_name}.toNat_lt"));
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = FloorConsts::const_(ty_name);
        let to_nat = FloorConsts::const_(&format!("{ty_name}.toNat"));
        let to_bitvec = FloorConsts::const_(&format!("{ty_name}.toBitVec"));
        let bitvec_tofin = FloorConsts::const_("BitVec.toFin");
        let fin_islt = FloorConsts::const_("Fin.isLt");
        let width_e = Self::ofnat_nat_lit(width);
        let two_pow_w = Self::two_pow(width_e.clone());

        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(ty.clone());

        let type_ = {
            let bound = LeanNat::pow(LeanNat::lit(2), LeanNat::lit(width));
            let concl = LeanNat::lt(Expr::app(to_nat, x.clone()), bound);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, ty.clone(), concl))
        };

        let value = {
            let fin = Expr::apps(bitvec_tofin, [width_e, Expr::app(to_bitvec, x.clone())]);
            let body = Expr::apps(fin_islt, [two_pow_w, fin]);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, ty, body))
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem <T>.toNat_div (a b : <T>) : (a / b).toNat = a.toNat / b.toNat`
    /// (Lean's statement: `/` through `instHDiv` over `instDiv<T>` and
    /// `Nat.instDiv`). The proof is over the bare `<T>.div` / `Nat.div`:
    ///
    /// ```text
    /// fun a b =>
    ///   Nat.mod_eq_of_lt (a.toNat / b.toNat) <T>.size
    ///     (Nat.lt_of_le_of_lt (a.toNat / b.toNat) a.toNat <T>.size
    ///        (Nat.div_le_self a.toNat b.toNat)
    ///        (<T>.toNat_lt a))
    /// ```
    ///
    /// The declared left-hand side reduces to `Nat.mod (a.toNat / b.toNat)
    /// <T>.size` through `<T>.div` → `<T>.ofNat` → `Fin.ofNat`'s `Nat.mod`,
    /// which is exactly the equation's left-hand side.
    fn register_uint_tonat_div(&mut self, ty_name: &str) -> Result<(), EnvError> {
        let name = Name::from_string(&format!("{ty_name}.toNat_div"));
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = FloorConsts::const_(ty_name);
        let to_nat = FloorConsts::const_(&format!("{ty_name}.toNat"));
        let size = FloorConsts::const_(&format!("{ty_name}.size"));
        let tonat_lt = FloorConsts::const_(&format!("{ty_name}.toNat_lt"));
        let nat_div = FloorConsts::const_("Nat.div");
        let mod_eq_of_lt = FloorConsts::const_("Nat.mod_eq_of_lt");
        let div_le_self = FloorConsts::const_("Nat.div_le_self");
        let lt_of_le_of_lt = FloorConsts::const_("Nat.lt_of_le_of_lt");

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ty.clone());
        let (bv_id, bv) = b.fresh_local(ty.clone());
        let a_nat = Expr::app(to_nat.clone(), a.clone());
        let b_nat = Expr::app(to_nat.clone(), bv.clone());
        let quotient = Expr::apps(nat_div, [a_nat.clone(), b_nat.clone()]);

        let type_ = {
            let quot_u = LeanNat::hetero_at(
                &ty,
                "HDiv.hDiv",
                "instHDiv",
                &format!("instDiv{ty_name}"),
                a.clone(),
                bv.clone(),
            );
            let lhs = Expr::app(to_nat.clone(), quot_u);
            let concl = LeanNat::eq(lhs, LeanNat::div(a_nat.clone(), b_nat.clone()));
            let e = b.mk_pi(bv_id, BinderInfo::Default, ty.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, ty.clone(), e);
            b.finish(e)
        };

        let value = {
            // Nat.div_le_self a.toNat b.toNat : Nat.le (a.toNat / b.toNat) a.toNat
            let h_le = Expr::apps(div_le_self, [a_nat.clone(), b_nat.clone()]);
            // <T>.toNat_lt a : Nat.lt a.toNat <T>.size
            let h_lt = Expr::app(tonat_lt, a.clone());
            // Nat.lt_of_le_of_lt … : Nat.lt (a.toNat / b.toNat) <T>.size
            let bound = Expr::apps(
                lt_of_le_of_lt,
                [quotient.clone(), a_nat.clone(), size.clone(), h_le, h_lt],
            );
            let body = Expr::apps(mod_eq_of_lt, [quotient.clone(), size, bound]);
            let e = b.mk_lam(bv_id, BinderInfo::Default, ty.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, ty, e);
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

    /// Both bridges, at all four widths, are in the DEFAULT prelude, are
    /// `Declaration::Theorem`s that kept their proof values, and rest on no
    /// axiom.
    #[test]
    fn uint_tonat_bridges_are_axiom_free_theorems_in_the_prelude() {
        let env = Environment::with_prelude();
        for (ty_name, _) in WIDTHS {
            for suffix in [
                "toNat_lt",
                "toNat_div",
                "lt_iff_toNat_lt",
                "le_iff_toNat_le",
                "toNat_ofNat",
            ] {
                let short = format!("{ty_name}.{suffix}");
                let info = env
                    .get_const(&Name::from_string(&short))
                    .unwrap_or_else(|| panic!("{short} must be in the default prelude"));
                assert_eq!(
                    info.kind,
                    ConstantKind::Theorem,
                    "{short} must be a Theorem"
                );
                assert!(info.value.is_some(), "{short} must retain its proof value");
                let deps = env
                    .axiom_deps(&Name::from_string(&short))
                    .unwrap_or_else(|| panic!("{short}: axiom_deps None"));
                assert!(deps.is_empty(), "{short} rests on {deps:?}");
            }
        }
    }

    /// ANTI-VACUITY / CONTROL: the division lift is NOT definitional — `rfl`
    /// must fail on `UInt32.toNat_div`'s own statement (the modulus in
    /// `UInt32.ofNat` is the whole obstacle) — and `UInt32.toNat_div` must
    /// close it.
    ///
    /// This is the measurement the Trust report made against the shipped pack;
    /// pinning it here means a future change that makes the lift definitional
    /// announces itself instead of quietly making this module pointless.
    #[test]
    fn uint32_tonat_div_is_load_bearing_not_rfl() {
        let env = Environment::with_prelude();
        let c = FloorConsts::new();
        let stmt = env
            .get_const(&Name::from_string("UInt32.toNat_div"))
            .expect("UInt32.toNat_div must be registered")
            .type_
            .clone();
        let tc = TypeChecker::with_mode(&env, env.mode());

        // fun (a b : UInt32) => @Eq.refl Nat (UInt32.toNat (UInt32.div a b))
        let ty = FloorConsts::const_("UInt32");
        let to_nat = FloorConsts::const_("UInt32.toNat");
        let udiv = FloorConsts::const_("UInt32.div");
        let by_rfl = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(ty.clone());
            let (bv_id, bv) = b.fresh_local(ty.clone());
            let lhs = Expr::app(to_nat, Expr::apps(udiv, [a.clone(), bv.clone()]));
            let body = c.refl(lhs);
            let e = b.mk_lam(bv_id, BinderInfo::Default, ty.clone(), body);
            b.finish(b.mk_lam(a_id, BinderInfo::Default, ty.clone(), e))
        };
        assert!(
            tc.check_type(&by_rfl, &stmt).is_err(),
            "`UInt32.toNat (a / b) = a.toNat / b.toNat` must NOT be rfl — \
             the left side carries a `% 2^32` the right side does not"
        );

        tc.check_type(&FloorConsts::const_("UInt32.toNat_div"), &stmt)
            .expect("UInt32.toNat_div must prove its own statement");
    }

    /// The import-verification prelude does NOT gain these: the whole
    /// Fin/BitVec-carrier UInt cluster they are stated over is suppressed
    /// there.
    #[test]
    fn import_prelude_withholds_the_uint_bridges() {
        let env = Environment::try_with_prelude_for_import().expect("import prelude must build");
        for (ty_name, _) in WIDTHS {
            for suffix in [
                "toNat_lt",
                "toNat_div",
                "lt_iff_toNat_lt",
                "le_iff_toNat_le",
                "toNat_ofNat",
            ] {
                let short = format!("{ty_name}.{suffix}");
                assert!(
                    env.get_const(&Name::from_string(&short)).is_none(),
                    "{short} must NOT be seeded in the import prelude"
                );
            }
        }
    }

    /// The comparison bridge claims the two carriers are DEFINITIONALLY the
    /// same proposition. That is a property of this `BitVec`-carrier stack, not
    /// a theorem of `UInt32`, so pin it: the identity function must prove the
    /// lemma's own statement in BOTH directions.
    ///
    /// If this ever fails, `UIntN.lt`/`instLTUIntN` has been respelled and
    /// `register_uint_order_iff`'s `fun h => h` needs a real proof — the
    /// failure is the notice.
    #[test]
    fn uint_order_bridge_is_definitional_on_this_carrier() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for (ty_name, _) in WIDTHS {
            for suffix in ["lt_iff_toNat_lt", "le_iff_toNat_le"] {
                let short = format!("{ty_name}.{suffix}");
                let stmt = env
                    .get_const(&Name::from_string(&short))
                    .unwrap_or_else(|| panic!("{short} must be registered"))
                    .type_
                    .clone();
                tc.check_type(&FloorConsts::const_(&short), &stmt)
                    .unwrap_or_else(|e| panic!("{short} must prove its own statement: {e:?}"));
            }
        }
    }

    /// ANTI-VACUITY for `toNat_ofNat`: the round trip is `n % size`, NOT `n`.
    /// A statement of the un-reduced form must be REFUSED — otherwise the
    /// lemma would be asserting something false about a wrapping carrier.
    #[test]
    fn uint32_tonat_ofnat_is_modular_not_the_identity() {
        let env = Environment::with_prelude();
        let c = FloorConsts::new();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let to_nat = FloorConsts::const_("UInt32.toNat");
        let of_nat = FloorConsts::const_("UInt32.ofNat");

        // The false statement `∀ n, (UInt32.ofNat n).toNat = n`.
        let (false_stmt, by_rfl) = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let lhs = Expr::app(to_nat, Expr::app(of_nat, n.clone()));
            let stmt = c.eq_of(lhs.clone(), n.clone());
            let proof = c.refl(n.clone());
            (
                b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), stmt)),
                b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), proof)),
            )
        };
        assert!(
            tc.check_type(&by_rfl, &false_stmt).is_err(),
            "`(UInt32.ofNat n).toNat = n` must NOT check — UInt32 wraps"
        );

        // And the true one does.
        let stmt = env
            .get_const(&Name::from_string("UInt32.toNat_ofNat"))
            .expect("UInt32.toNat_ofNat must be registered")
            .type_
            .clone();
        tc.check_type(&FloorConsts::const_("UInt32.toNat_ofNat"), &stmt)
            .expect("UInt32.toNat_ofNat must prove its own statement");
    }
}
