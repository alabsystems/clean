// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real `Nat → String` decimal rendering for the prelude (B04,
//! GAP_SWEEP_2026-07-09).
//!
//! Before this module, the prelude's `instToStringNat` carried the placeholder
//! body `toString := fun _ => ""`, so the kernel rfl-CERTIFIED wrong values:
//! `s!"one {1 + 1} three" = "one  three"` and `(toString (2 : Nat)).length = 0`
//! were provable. This module registers the genuine digit recursion so
//! `toString (42 : Nat) = "42"` holds by `rfl` with an EMPTY axiom closure.
//!
//! Lean ground truth (lean4 `Init/Data/Repr.lean`):
//!
//! ```lean
//! def Nat.toDigitsCore (base : Nat) : Nat → Nat → List Char → List Char
//!   | 0,      _, ds => ds
//!   | fuel+1, n, ds =>
//!     let d := Nat.digitChar (n % base)
//!     let n' := n / base
//!     if n' = 0 then d :: ds else Nat.toDigitsCore base fuel n' (d :: ds)
//!
//! def Nat.toDigits (base : Nat) (n : Nat) : List Char :=
//!   Nat.toDigitsCore base (n + 1) n []
//!
//! protected def Nat.repr (n : Nat) : String :=
//!   (Nat.toDigits 10 n).asString
//! ```
//!
//! plus `Nat.digitChar` (the 16-way `if n = d then '…'` chain ending in `'*'`)
//! and `List.asString (s : List Char) : String := ⟨s⟩` (lean4
//! `Init/Data/String/Basic.lean`).
//!
//! Clean-faithful deviations (all defeq-neutral, never silent):
//! - `Nat.toDigitsCore`'s fuel `match` is spelled directly as the `Nat.rec`
//!   it compiles to (the kernel prelude has no match compiler), and the two
//!   `let`s are inlined; both forms are definitionally equal to Lean's.
//! - `Nat.toDigits`'s `n + 1` is spelled `Nat.succ n` (defeq).
//!
//! Every declaration goes through the fully-checked `add_decl` path — no
//! `Axiom` / `Opaque` / `sorry` / structural bypass (the P1 pattern). Ground
//! `toString (k : Nat)` terms reduce inside the kernel via δ (reducible
//! definitions), ι over `ToString.rec`/`Nat.rec` (with
//! `nat_lit_to_constructor` for literal fuel) and the trusted native
//! reducers for `Nat.div` / `Nat.mod` / `Nat.decEq` literal arithmetic;
//! the final `String.mk [c…] = "…"` comparison uses
//! `string_lit_to_constructor` — exactly the paths the value-pin tests below
//! replay.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// `'0'..'9'` then `'a'..'f'` — the 16 digit characters of `Nat.digitChar`
/// (lean4 `Init/Data/Repr.lean`), followed by the `'*'` fallback.
const DIGIT_CHARS: [char; 16] = [
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f',
];

impl Environment {
    /// Register `Nat.digitChar`, `Nat.toDigitsCore`, `Nat.toDigits`,
    /// `List.asString`, and `Nat.repr` — the genuine Lean digit-rendering
    /// chain (B04). Idempotent; every constant is a fully-checked
    /// `Declaration::Definition`.
    ///
    /// # Contract
    ///
    /// REQUIRES: nothing (dependencies are initialized here, idempotently)
    /// ENSURES: `Nat.repr` is a `Definition` with an empty axiom closure and
    ///          `Nat.repr 42` is definitionally equal to `"42"`
    pub(crate) fn init_nat_repr(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): withhold the chain —
        // the genuine Lean `Nat.repr`/`Nat.toDigits(Core)`/`Nat.digitChar`
        // import through the checked `.olean` path (and this chain's
        // dependencies — Clean's `Nat.decEq`/`Nat.div`/`Nat.mod` overlays —
        // are themselves withheld there). Same gate as `init_to_string`,
        // the only caller.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.get_const(&Name::from_string("Nat.repr")).is_some() {
            return Ok(());
        }

        // Dependencies (all idempotent). `init_nat` provides `Nat`, `Nat.rec`,
        // `Nat.succ`, and the genuine `Nat.div`/`Nat.mod`; `init_string`
        // provides `Char`/`List`/`String`; `init_ite` the `ite` definition;
        // `register_nat_dec_eq_proof` the constructive `Nat.decEq` backing the
        // `if … = 0` conditions.
        self.init_nat()?;
        self.init_string()?;
        self.init_ite()?;
        self.register_nat_dec_eq_proof()?;

        let lvl1 = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let char_ = Expr::const_(Name::from_string("Char"), vec![]);
        let string = Expr::const_(Name::from_string("String"), vec![]);
        let list_char = Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            char_.clone(),
        );
        let eq_nat = |a: Expr, b: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
                [nat.clone(), a, b],
            )
        };
        let nat_dec_eq = |a: Expr, b: Expr| {
            Expr::apps(Expr::const_(Name::from_string("Nat.decEq"), vec![]), [a, b])
        };
        // Fully applied `ite.{1} α (a = b) (Nat.decEq a b) t e`.
        let ite_eq_nat = |alpha: Expr, a: Expr, b: Expr, then_e: Expr, else_e: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("ite"), vec![lvl1.clone()]),
                [
                    alpha,
                    eq_nat(a.clone(), b.clone()),
                    nat_dec_eq(a, b),
                    then_e,
                    else_e,
                ],
            )
        };
        let char_of_nat = |c: char| {
            Expr::app(
                Expr::const_(Name::from_string("Char.ofNat"), vec![]),
                Expr::nat_lit(c as u64),
            )
        };
        let nat_div = |a: Expr, b: Expr| {
            Expr::apps(Expr::const_(Name::from_string("Nat.div"), vec![]), [a, b])
        };
        let nat_mod = |a: Expr, b: Expr| {
            Expr::apps(Expr::const_(Name::from_string("Nat.mod"), vec![]), [a, b])
        };
        let list_cons_char = |head: Expr, tail: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [char_.clone(), head, tail],
            )
        };

        // ── Nat.digitChar : Nat → Char ────────────────────────────────────
        // Lean's 16-way `if n = d then '…'` chain ending in `'*'`
        // (lean4 `Init/Data/Repr.lean`, `Nat.digitChar`).
        let digit_char_ty = Expr::pi(BinderInfo::Default, nat.clone(), char_.clone());
        let digit_char_val = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let mut body = char_of_nat('*');
            for (d, c) in DIGIT_CHARS.iter().enumerate().rev() {
                body = ite_eq_nat(
                    char_.clone(),
                    n.clone(),
                    Expr::nat_lit(d as u64),
                    char_of_nat(*c),
                    body,
                );
            }
            b.finish(b.mk_lam(n_id, BinderInfo::Default, nat.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Nat.digitChar"),
            level_params: vec![],
            type_: digit_char_ty,
            value: digit_char_val,
            is_reducible: true,
        })?;
        let digit_char =
            |e: Expr| Expr::app(Expr::const_(Name::from_string("Nat.digitChar"), vec![]), e);

        // ── Nat.toDigitsCore : Nat → Nat → Nat → List Char → List Char ───
        // (base, fuel, n, ds). Lean's fuel `match` spelled as the `Nat.rec`
        // it compiles to:
        //   fun base fuel => Nat.rec
        //     (motive := fun _ => Nat → List Char → List Char)
        //     (fun _ ds => ds)                                 -- fuel = 0
        //     (fun _fuel ih n ds =>                            -- fuel = _fuel+1
        //        if n / base = 0
        //        then Nat.digitChar (n % base) :: ds
        //        else ih (n / base) (Nat.digitChar (n % base) :: ds))
        //     fuel
        let nat_to_list_to_list = Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(BinderInfo::Default, list_char.clone(), list_char.clone()),
        );
        let to_digits_core_ty = Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(
                BinderInfo::Default,
                nat.clone(),
                nat_to_list_to_list.clone(),
            ),
        );
        let to_digits_core_val = {
            let mut b = EnvDeclBuilder::new();
            let (base_id, base) = b.fresh_local(nat.clone());
            let (fuel_id, fuel) = b.fresh_local(nat.clone());

            // motive := fun (_ : Nat) => Nat → List Char → List Char
            let motive = Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                nat_to_list_to_list.clone(),
            );

            // zero case := fun (_ : Nat) (ds : List Char) => ds
            let zero_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (n_id, _n) = c.fresh_local(nat.clone());
                let (ds_id, ds) = c.fresh_local(list_char.clone());
                let r = c.mk_lam(ds_id, BinderInfo::Default, list_char.clone(), ds);
                c.finish_child(c.mk_lam(n_id, BinderInfo::Default, nat.clone(), r))
            };

            // succ case := fun (_fuel : Nat) (ih : Nat → List Char → List Char)
            //                  (n : Nat) (ds : List Char) => if …
            let succ_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (fp_id, _fp) = c.fresh_local(nat.clone());
                let (ih_id, ih) = c.fresh_local(nat_to_list_to_list.clone());
                let (n_id, n) = c.fresh_local(nat.clone());
                let (ds_id, ds) = c.fresh_local(list_char.clone());
                let quotient = nat_div(n.clone(), base.clone());
                let digit_cons = list_cons_char(digit_char(nat_mod(n.clone(), base.clone())), ds);
                let body = ite_eq_nat(
                    list_char.clone(),
                    quotient.clone(),
                    Expr::nat_lit(0),
                    digit_cons.clone(),
                    Expr::apps(ih, [quotient, digit_cons]),
                );
                let r = c.mk_lam(ds_id, BinderInfo::Default, list_char.clone(), body);
                let r = c.mk_lam(n_id, BinderInfo::Default, nat.clone(), r);
                let r = c.mk_lam(ih_id, BinderInfo::Default, nat_to_list_to_list.clone(), r);
                c.finish_child(c.mk_lam(fp_id, BinderInfo::Default, nat.clone(), r))
            };

            let body = Expr::apps(
                Expr::const_(Name::from_string("Nat.rec"), vec![lvl1.clone()]),
                [motive, zero_case, succ_case, fuel],
            );
            let r = b.mk_lam(fuel_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(base_id, BinderInfo::Default, nat.clone(), r))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Nat.toDigitsCore"),
            level_params: vec![],
            type_: to_digits_core_ty,
            value: to_digits_core_val,
            is_reducible: true,
        })?;

        // ── Nat.toDigits : Nat → Nat → List Char ─────────────────────────
        //   := fun base n => Nat.toDigitsCore base (Nat.succ n) n []
        // (`n + 1` spelled as its defeq normal form `Nat.succ n`).
        let to_digits_ty = Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(BinderInfo::Default, nat.clone(), list_char.clone()),
        );
        let to_digits_val = {
            let mut b = EnvDeclBuilder::new();
            let (base_id, base) = b.fresh_local(nat.clone());
            let (n_id, n) = b.fresh_local(nat.clone());
            let body = Expr::apps(
                Expr::const_(Name::from_string("Nat.toDigitsCore"), vec![]),
                [
                    base,
                    Expr::app(
                        Expr::const_(Name::from_string("Nat.succ"), vec![]),
                        n.clone(),
                    ),
                    n,
                    Expr::app(
                        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                        char_.clone(),
                    ),
                ],
            );
            let r = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(base_id, BinderInfo::Default, nat.clone(), r))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Nat.toDigits"),
            level_params: vec![],
            type_: to_digits_ty,
            value: to_digits_val,
            is_reducible: true,
        })?;

        // ── List.asString : List Char → String := fun l => String.mk l ───
        // lean4 `Init/Data/String/Basic.lean`: `⟨s⟩` over the v4.8-shape
        // `String.mk : List Char → String` Clean models.
        let as_string_ty = Expr::pi(BinderInfo::Default, list_char.clone(), string.clone());
        let as_string_val = Expr::lam(
            BinderInfo::Default,
            list_char.clone(),
            Expr::app(
                Expr::const_(Name::from_string("String.mk"), vec![]),
                Expr::bvar(0),
            ),
        );
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("List.asString"),
            level_params: vec![],
            type_: as_string_ty,
            value: as_string_val,
            is_reducible: true,
        })?;

        // ── Nat.repr : Nat → String ──────────────────────────────────────
        //   := fun n => List.asString (Nat.toDigits 10 n)
        let repr_ty = Expr::pi(BinderInfo::Default, nat.clone(), string.clone());
        let repr_val = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let body = Expr::app(
                Expr::const_(Name::from_string("List.asString"), vec![]),
                Expr::apps(
                    Expr::const_(Name::from_string("Nat.toDigits"), vec![]),
                    [Expr::nat_lit(10), n],
                ),
            );
            b.finish(b.mk_lam(n_id, BinderInfo::Default, nat.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Nat.repr"),
            level_params: vec![],
            type_: repr_ty,
            value: repr_val,
            is_reducible: true,
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    fn tostring_nat_app(n: u64) -> Expr {
        // toString.{0} Nat instToStringNat (lit n)
        Expr::apps(
            Expr::const_(Name::from_string("toString"), vec![Level::zero()]),
            [
                Expr::const_(Name::from_string("Nat"), vec![]),
                Expr::const_(Name::from_string("instToStringNat"), vec![]),
                Expr::nat_lit(n),
            ],
        )
    }

    /// B04 value pins: `toString (0 : Nat) = "0"` and
    /// `toString (42 : Nat) = "42"` hold BY DEFEQ (the `rfl` path), and the
    /// old certified-wrong `toString 42 = ""` is REJECTED.
    #[test]
    fn test_tostring_nat_computes_decimal_digits() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        assert!(
            tc.is_def_eq(&tostring_nat_app(0), &Expr::str_lit("0")),
            "toString 0 must be defeq to \"0\""
        );
        assert!(
            tc.is_def_eq(&tostring_nat_app(42), &Expr::str_lit("42")),
            "toString 42 must be defeq to \"42\""
        );
        assert!(
            tc.is_def_eq(&tostring_nat_app(1234567890), &Expr::str_lit("1234567890")),
            "toString 1234567890 must be defeq to \"1234567890\""
        );
        assert!(
            !tc.is_def_eq(&tostring_nat_app(42), &Expr::str_lit("")),
            "the pre-B04 certified-wrong value toString 42 = \"\" must be REJECTED"
        );
    }

    /// `Nat.digitChar` matches Lean beyond the decimal range (hex digits and
    /// the `'*'` fallback).
    #[test]
    fn test_digit_char_matches_lean_table() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let digit_char = |n: u64| {
            Expr::app(
                Expr::const_(Name::from_string("Nat.digitChar"), vec![]),
                Expr::nat_lit(n),
            )
        };
        let char_of = |c: char| {
            Expr::app(
                Expr::const_(Name::from_string("Char.ofNat"), vec![]),
                Expr::nat_lit(c as u64),
            )
        };
        for (d, c) in DIGIT_CHARS.iter().enumerate() {
            assert!(
                tc.is_def_eq(&digit_char(d as u64), &char_of(*c)),
                "Nat.digitChar {d} must be '{c}'"
            );
        }
        assert!(
            tc.is_def_eq(&digit_char(16), &char_of('*')),
            "Nat.digitChar 16 must be the '*' fallback"
        );
    }

    /// No-fake guard: the whole chain is `Definition`s (never Axiom/Opaque)
    /// with EMPTY transitive axiom closures.
    #[test]
    fn test_nat_repr_chain_axiom_free_definitions() {
        let env = Environment::with_prelude();
        for name in [
            "Nat.digitChar",
            "Nat.toDigitsCore",
            "Nat.toDigits",
            "List.asString",
            "Nat.repr",
            "instToStringNat",
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} must be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a Definition"
            );
            assert!(info.value.is_some(), "{name} must retain its value");
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} is registered"));
            assert!(
                deps.is_empty(),
                "{name} must have an EMPTY axiom closure, got {deps:?}"
            );
        }
    }
}
