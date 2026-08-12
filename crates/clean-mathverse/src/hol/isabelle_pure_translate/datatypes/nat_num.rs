// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Ctx` datatype-embedding methods for the `nat`/`num` recursors and case
//! combinator: `embed_rec_nat`, `embed_case_nat`, `embed_rec_num`. Moved
//! verbatim from the original single-file `datatypes` module; behaviour is
//! byte-identical.

use clean_kernel::{BinderInfo, Expr};

use super::super::super::isabelle_pure::IsaType;
use super::super::*;

impl Ctx {
    /// Embed an occurrence of HOL's `nat` recursor `Nat.old.nat.rec_nat` to a
    /// bare clean lambda built over the prelude's `Nat.rec`.
    ///
    /// Isabelle's `rec_nat` is primitive recursion over `nat` with a *constant*
    /// (non-dependent) motive: its instantiated type is
    /// `α ⇒ (nat ⇒ α ⇒ α) ⇒ nat ⇒ α`. Clean's `Nat.rec` is the dependent
    /// eliminator
    /// `{motive : Nat → Sort u} → motive 0 → ((n:Nat)→motive n→motive (succ n))
    ///  → (t:Nat) → motive t`,
    /// so the faithful specialisation takes `motive := λ_:Nat. α`:
    /// ```text
    /// λ(z:α)(s:Nat→α→α)(t:Nat).
    ///   @Nat.rec.{u} (λ_:Nat. α) z (λ(k:Nat)(ih:α). s k ih) t
    /// ```
    /// `α` (and the recursor's universe level `u`) are read off the constant's
    /// instantiated type, so the result is monomorphic — no polymorphic-Definition
    /// universe threading is needed, and the kernel re-checks the saturated term.
    /// Returns `None` if the type is not the expected `α ⇒ (nat ⇒ α ⇒ α) ⇒ nat ⇒ α`
    /// shape (then the caller falls back to an opaque param, honestly typed).
    pub(crate) fn embed_rec_nat(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = α ⇒ ((nat ⇒ (α ⇒ α)) ⇒ (nat ⇒ α))
        let IsaType::Type { n: f1, a: a1 } = t else {
            return Ok(None);
        };
        if f1 != "fun" || a1.len() != 2 {
            return Ok(None);
        }
        let alpha_ty = &a1[0];
        let alpha = self.embed_type(alpha_ty)?;
        // The motive is the constant `λ_:Nat. α`, so its type is `Nat → typeof(α)`
        // and the kernel's `Nat.rec.{u}` requires the motive to have type
        // `Nat → Sort u`. Hence `u` is the universe `α` *inhabits* — `α : Sort u` —
        // computed structurally with Prop-impredicativity (see
        // [`type_universe_level`]). E.g. an `α` that is the *result type*
        // `Nat → bool = Nat → Prop` inhabits `Sort 1` (`imax(1,1)`), and a bare
        // `α = bool = Prop` inhabits `Sort 1` too (`Prop : Sort 1`) — NOT `Sort 0`.
        let u = type_universe_level(&alpha);
        let nat = Expr::const_str("Nat");
        // motive : Nat → Sort u, constant `λ_:Nat. α`.
        let motive = Expr::lam(BinderInfo::Default, nat.clone(), alpha.clone());
        // succ-case adaptor: Isabelle's `s : nat ⇒ α ⇒ α` already matches clean's
        // `(k:Nat) → motive k → motive (succ k)` (motive is constant α), so the
        // bound `s` (bvar 1 inside the two recursor-arg binders) is applied directly.
        // We η-wrap it so the clean recursor sees a literal `λ k ih. s k ih`:
        //   inside `λ(z)(s)(t).`, s = bvar 1; inside the added `λ(k)(ih).`, s = bvar 3.
        let succ_arm = Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::lam(
                BinderInfo::Default,
                alpha.clone(),
                Expr::apps(Expr::bvar(3), [Expr::bvar(1), Expr::bvar(0)]),
            ),
        );
        // λ(z:α)(s:Nat→α→α)(t:Nat). Nat.rec.{u} motive z succ_arm t
        let s_ty = Expr::arrow(nat.clone(), Expr::arrow(alpha.clone(), alpha.clone()));
        let body = Expr::apps(
            Expr::const_str_levels("Nat.rec", vec![u]),
            [
                motive,
                Expr::bvar(2), // z
                succ_arm,
                Expr::bvar(0), // t
            ],
        );
        let lam = Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            Expr::lam(
                BinderInfo::Default,
                s_ty,
                Expr::lam(BinderInfo::Default, nat, body),
            ),
        );
        Ok(Some(lam))
    }

    /// Embed an occurrence of HOL's `nat` **case combinator** `Nat.nat.case_nat`
    /// (`case t of 0 ⇒ z | Suc k ⇒ f k`) to a bare clean lambda over `Nat.rec`.
    ///
    /// Its instantiated type is `α ⇒ (nat ⇒ α) ⇒ nat ⇒ α`. Clean's `Nat.rec` with
    /// the constant motive `λ_:Nat. α` and a successor arm that *drops* the
    /// recursive value gives exactly case analysis:
    /// ```text
    /// λ(z:α)(f:Nat→α)(t:Nat). @Nat.rec.{u} (λ_:Nat. α) z (λ(k:Nat)(_ih:α). f k) t
    /// ```
    /// `α` and the universe `u` are read off the constant's instantiated type, so
    /// the result is monomorphic; the kernel re-checks the saturated term. Returns
    /// `None` if the type is not the expected `α ⇒ (nat ⇒ α) ⇒ nat ⇒ α` shape.
    pub(crate) fn embed_case_nat(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = α ⇒ ((nat ⇒ α) ⇒ (nat ⇒ α))
        let IsaType::Type { n: f1, a: a1 } = t else {
            return Ok(None);
        };
        if f1 != "fun" || a1.len() != 2 {
            return Ok(None);
        }
        let alpha = self.embed_type(&a1[0])?;
        // `u` is the universe `α` inhabits (`α : Sort u`), computed with
        // Prop-impredicativity — see [`embed_rec_nat`] and [`type_universe_level`].
        let u = type_universe_level(&alpha);
        let nat = Expr::const_str("Nat");
        // motive : Nat → Sort u, constant `λ_:Nat. α`.
        let motive = Expr::lam(BinderInfo::Default, nat.clone(), alpha.clone());
        // succ-case adaptor: `f : nat ⇒ α` applied to the predecessor `k`, ignoring
        // the recursive value `_ih`. Inside `λ(z)(f)(t).`, `f` = bvar 1; inside the
        // added `λ(k)(_ih).`, `f` = bvar 3 and `k` = bvar 1.
        let succ_arm = Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::lam(
                BinderInfo::Default,
                alpha.clone(),
                Expr::app(Expr::bvar(3), Expr::bvar(1)),
            ),
        );
        // λ(z:α)(f:Nat→α)(t:Nat). Nat.rec.{u} motive z succ_arm t
        let f_ty = Expr::arrow(nat.clone(), alpha.clone());
        let body = Expr::apps(
            Expr::const_str_levels("Nat.rec", vec![u]),
            [motive, Expr::bvar(2), succ_arm, Expr::bvar(0)],
        );
        let lam = Expr::lam(
            BinderInfo::Default,
            alpha,
            Expr::lam(
                BinderInfo::Default,
                f_ty,
                Expr::lam(BinderInfo::Default, nat, body),
            ),
        );
        Ok(Some(lam))
    }

    /// Embed an occurrence of HOL's `num` recursor `Num.num.rec_num` to a bare
    /// clean lambda over the registered `Num` inductive's `Num.rec`.
    ///
    /// `Num = One | Bit0 of num | Bit1 of num`, so the constant-motive recursor
    /// type is `α ⇒ (num ⇒ α ⇒ α) ⇒ (num ⇒ α ⇒ α) ⇒ num ⇒ α` (a `One` case and
    /// two recursive `Bit0`/`Bit1` cases). Clean's generated `Num.rec` is
    /// `{motive} → motive One → ((a:Num)→motive a→motive (Bit0 a))
    ///  → ((a:Num)→motive a→motive (Bit1 a)) → (t:Num) → motive t`, so with the
    /// constant motive `λ_:Num. α` the faithful wrapper is
    /// ```text
    /// λ(z:α)(b0:Num→α→α)(b1:Num→α→α)(t:Num).
    ///   @Num.rec.{u} (λ_.α) z (λ(a:Num)(ih:α). b0 a ih)
    ///                         (λ(a:Num)(ih:α). b1 a ih) t
    /// ```
    /// α and its level `u` are read off the constant's instantiated type. Returns
    /// `None` if the type is not the expected shape (caller falls back to a param).
    pub(crate) fn embed_rec_num(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = α ⇒ (num⇒α⇒α) ⇒ (num⇒α⇒α) ⇒ num ⇒ α
        let IsaType::Type { n: f1, a: a1 } = t else {
            return Ok(None);
        };
        if f1 != "fun" || a1.len() != 2 {
            return Ok(None);
        }
        let alpha = self.embed_type(&a1[0])?;
        // `u` is the universe `α` inhabits (`α : Sort u`), computed with
        // Prop-impredicativity — see [`embed_rec_nat`] and [`type_universe_level`].
        let u = type_universe_level(&alpha);
        let num = Expr::const_str("Num");
        let motive = Expr::lam(BinderInfo::Default, num.clone(), alpha.clone());
        let case_ty = Expr::arrow(num.clone(), Expr::arrow(alpha.clone(), alpha.clone()));
        // Inside `λ(z)(b0)(b1)(t).` the operands are: z=bvar3, b0=bvar2, b1=bvar1,
        // t=bvar0. Each case adaptor adds `λ(a:Num)(ih:α).` (two binders), so the
        // captured operand index is lifted by 2: b0→bvar4, b1→bvar3.
        let bit0_arm = Expr::lam(
            BinderInfo::Default,
            num.clone(),
            Expr::lam(
                BinderInfo::Default,
                alpha.clone(),
                Expr::apps(Expr::bvar(4), [Expr::bvar(1), Expr::bvar(0)]),
            ),
        );
        let bit1_arm = Expr::lam(
            BinderInfo::Default,
            num.clone(),
            Expr::lam(
                BinderInfo::Default,
                alpha.clone(),
                Expr::apps(Expr::bvar(3), [Expr::bvar(1), Expr::bvar(0)]),
            ),
        );
        let body = Expr::apps(
            Expr::const_str_levels("Num.rec", vec![u]),
            [
                motive,
                Expr::bvar(3), // z (One case)
                bit0_arm,
                bit1_arm,
                Expr::bvar(0), // t
            ],
        );
        let lam = Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            Expr::lam(
                BinderInfo::Default,
                case_ty.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    case_ty,
                    Expr::lam(BinderInfo::Default, num, body),
                ),
            ),
        );
        Ok(Some(lam))
    }
}
