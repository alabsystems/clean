// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Ctx::embed_const_term` — the first half of `embed_term`'s `Const`-arm
//! dispatch (coercions, connectives, datatype constructors/recursors, BNF
//! combinators). Any `Const` not matched here falls through to
//! `embed_const_term2`. Moved verbatim from the original single-file
//! `isabelle_pure_translate` module; behaviour is byte-identical (arm order
//! and guards unchanged).

use std::collections::BTreeMap;

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr};

use super::super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaTerm, IsaType};
use super::*;

impl Ctx {
    /// First-half `Const` dispatch for [`Self::embed_term`]; unmatched
    /// `Const`s fall through to [`Self::embed_const_term2`]. See that method
    /// for the trailing arms and the catch-all.
    pub(crate) fn embed_const_term(&mut self, tm: &IsaTerm) -> Result<Expr, TranslateError> {
        match tm {
            // HOL logical connectives → the CONST of their registered clean
            // `Definition` (`isabelle.def.HOL.conj`, …), NOT the inlined encoding.
            // The definition unfolds to the encoding via the kernel's defeq when
            // needed, so the connective `_def` theorems are still reflexivity and
            // the intro/elim proofs translate directly — but now an abstract
            // occurrence (a `Pure.all`-bound `Bound`) and a concrete `Const HOL.conj`
            // share one head symbol, eliminating the fold/unfold asymmetry that
            // kernel-rejected conjI/disjI/notI. The verifier registers these
            // definitions in its accumulating environment before replay.
            IsaTerm::Const { n, .. } if connective_def_name(n).is_some() => {
                // The guard already established `Some`; match (rather than
                // `.expect`) to stay panic-free in the production path.
                match connective_def_name(n) {
                    Some(def) => Ok(Expr::const_str(def)),
                    None => Err(TranslateError::Unsupported("connective_def_name")),
                }
            }
            // Bare identity-coercion constants. `HOL.Trueprop` (`bool ⇒ prop`) and
            // `Pure.prop` (`prop ⇒ prop`, the `PROP P ≡ P` wrapper) are the
            // *identity* in this embedding — embedded applications already strip
            // them. As a bare (un-applied) constant — e.g. as a `Pure.combination`
            // function argument `Trueprop ≡ Trueprop` — they must embed to the
            // clean identity `λ(x:Prop). x`, NOT an abstract parameter (which would
            // spuriously quantify the theorem over a fresh `Prop→Prop`). The kernel
            // β-reduces the resulting `congr (λx.x) (λx.x) …`, recovering the
            // intended equation.
            IsaTerm::Const { n, .. }
                if n == "HOL.Trueprop" || n == "Trueprop" || n == "Pure.prop" =>
            {
                Ok(Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)))
            }
            // Bare (un-applied) logical/structural connectives. When `Pure.imp`,
            // `HOL.implies`, `Pure.all`, `HOL.All`, or `HOL.eq`/`Pure.eq` appear
            // *fully applied* they embed (above) to their clean meaning — `Pi`,
            // binder `Pi`, `@Eq`. But when they appear **bare** as a higher-order
            // argument — e.g. `Pure.combination`'s function operand in the
            // connective `*_def_raw` proofs, where the conj/disj definitional
            // equation is built as `imp ≡ imp` combined with `(conj P Q) ≡ (∀R.…)`
            // — the generic `Const` arm below abstracts them as a *fresh* term
            // parameter FVar. That FVar then appears on the `congr`/`equal_elim`
            // side while the statement uses the concrete `Pi`/`Eq`, producing the
            // exact fold/unfold `TypeMismatch` that kernel-rejected conjI/disjI/
            // iffI/conjunct/disjE. Embedding the bare connective to its
            // η-expanded *semantic lambda* makes the bare and applied occurrences
            // β-equal: e.g. `(λA B. A → B) X Y` β-reduces to the same `X → Y`
            // (`Pi (_:X) Y`) the applied `Pure.imp` arm yields, so the two sides
            // of the definitional equation now share one head and the kernel
            // accepts. Soundness-neutral — the kernel re-checks the β-reduced
            // result against the statement, rejecting any mismatch.
            // Bare (un-applied) set coercions under the `'a set = 'a → Prop`
            // model. `Set.Collect : ('a ⇒ bool) ⇒ 'a set` is the identity
            // `λ(P:'a→Prop). P`; `Set.member : 'a ⇒ 'a set ⇒ bool` is
            // `λ(x:'a)(S:'a→Prop). S x`. Embedding the bare forms to exactly the
            // β-η-expanded lambdas the *applied* arms (above) produce keeps every
            // occurrence consistent (e.g. when `Set.member` appears bare as a
            // `Pure.combination` operand in a set-instance `*_def_raw` proof). The
            // operand object type `α` is read from the constant's HOL type.
            IsaTerm::Const { n, t } if n == "Set.Collect" => {
                // `('a ⇒ bool) ⇒ 'a set` — domain is the predicate type `'a→Prop`.
                let pred = match eq_operand_type(t) {
                    Some(p) => self.embed_type(p)?,
                    None => return Err(TranslateError::Unsupported("Set.Collect type")),
                };
                Ok(Expr::lam(BinderInfo::Default, pred, Expr::bvar(0)))
            }
            IsaTerm::Const { n, t } if n == "Set.member" => {
                // `'a ⇒ 'a set ⇒ bool` — element type `'a`, then `'a set = 'a→Prop`.
                let elem = match eq_operand_type(t) {
                    Some(e) => self.embed_type(e)?,
                    None => return Err(TranslateError::Unsupported("Set.member type")),
                };
                let set_ty = Expr::arrow(elem.clone(), Expr::prop());
                // λ(x:'a)(S:'a→Prop). S x  — x is bvar 1, S is bvar 0.
                Ok(Expr::lam(
                    BinderInfo::Default,
                    elem,
                    Expr::lam(
                        BinderInfo::Default,
                        set_ty,
                        Expr::app(Expr::bvar(0), Expr::bvar(1)),
                    ),
                ))
            }
            IsaTerm::Const { n, t } if is_bare_connective(n) => self.embed_bare_connective(n, t),
            // Pure's judgement-forming markers `Pure.term : 'a ⇒ prop` and
            // `Pure.sort_constraint : 'a itself ⇒ prop` — embed the bare const to
            // its registered polymorphic def-const applied to the argument type
            // (`@isabelle.def.Pure.term α` / `@isabelle.def.Pure.sort_constraint α`,
            // both δ-unfolding to `λ_. ∀A. A → A` — the meta-truth their `_def`
            // bodies denote; see [`pure_meta_true_value_and_type`]). `embed_app`
            // then applies the marker's own argument, so `Pure.term x` δβ-reduces
            // to `∀A. A → A`, making `term_def`/`sort_constraint_def` genuinely
            // reflexive and every marker use-site δ-consistent. The argument type
            // `α` is read off the constant's instantiated HOL type (`α ⇒ prop`);
            // both markers' arg types embed at clean `Type`, matching the def
            // signature `Π(α:Type). α → Prop`. Falls back to the opaque param if the
            // type is not the expected function shape — the kernel re-checks either
            // way, so a wrong embedding is rejected, never miscounted.
            IsaTerm::Const { n, t } if pure_meta_def_name(n).is_some() => {
                match (pure_meta_def_name(n), eq_operand_type(t)) {
                    (Some(def), Some(arg_ty)) => {
                        let alpha = self.embed_type(arg_ty)?;
                        Ok(Expr::app(Expr::const_str(def), alpha))
                    }
                    _ => {
                        let ty = self.embed_type(t)?;
                        Ok(self.const_param(n, ty))
                    }
                }
            }
            // HOL's `Nat.nat` datatype constructor `Nat.Suc : nat ⇒ nat` IS clean's
            // `Nat.succ : Nat → Nat` (under `Nat.nat → Nat`). Mapped to the real
            // constructor so `Suc`-headed terms reduce through `Nat.rec`'s iota rule.
            IsaTerm::Const { n, .. } if n == "Nat.Suc" => Ok(Expr::const_str("Nat.succ")),
            // HOL's `'a list` datatype constructors `List.list.Nil : 'a list` and
            // `List.list.Cons : 'a ⇒ 'a list ⇒ 'a list` ARE clean's `List.nil` and
            // `List.cons` (under `List.list 'a → List 'a`). Clean's constructors take
            // the element type `α` as a leading IMPLICIT argument, which the bare HOL
            // constant never records, so we read `α` off the constant's instantiated
            // HOL type and supply it explicitly (`@List.nil α` / `@List.cons α`). This
            // makes `Cons`/`Nil`-headed terms reduce through `List.rec`'s iota rule.
            // Returns to an opaque param if the type is not the expected shape.
            IsaTerm::Const { n, t } if n == "List.list.Nil" => {
                if let Some(e) = self.embed_list_nil(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            IsaTerm::Const { n, t } if n == "List.list.Cons" => {
                if let Some(e) = self.embed_list_cons(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // The `'a list` datatype **recursor** `List.list.rec_list`. Isabelle's
            // primitive-recursion combinator over `list` has the (constant-motive)
            // type `'b ⇒ ('a ⇒ 'a list ⇒ 'b ⇒ 'b) ⇒ 'a list ⇒ 'b`, exactly clean's
            // `List.rec` specialised to a non-dependent motive `λ_:List α. β`. We
            // embed each occurrence to the bare wrapper lambda over `List.rec`, so the
            // recursive list-function definitions (`append`, `map`, `rev`, `length`,
            // …) — whose bodies are `rec_list`-folds — verify by native iota/β
            // reduction. Bare and applied occurrences agree after β.
            IsaTerm::Const { n, t } if n == "List.list.rec_list" => {
                if let Some(e) = self.embed_rec_list(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // The `'a list` datatype **case combinator** `List.list.case_list`. Its
            // instantiated type `'b ⇒ ('a ⇒ 'a list ⇒ 'b) ⇒ 'a list ⇒ 'b` is the
            // non-recursive case analysis (`case t of [] ⇒ z | x#xs ⇒ f x xs`) —
            // clean's `List.rec` with the constant motive `λ_:List α. β` and a cons
            // arm that *ignores* the recursive value. Mapping it (like `rec_list`)
            // lets the `case_list`-spelled definitions and their consumers verify by
            // native iota reduction.
            IsaTerm::Const { n, t } if n == "List.list.case_list" => {
                if let Some(e) = self.embed_case_list(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // The `'a list` **functor map** `List.list.map : ('a⇒'b) ⇒ 'a list ⇒
            // 'b list`. HOL defines it through the BNF `ctor_fold_list`/`map_pre_list`
            // machinery (a `Hilbert_Choice.Eps`-defined unique morphism — see
            // [`embed_map_list`]), so its `…map_def` axiom does NOT close in the
            // list-function registry. Mapping the constant *directly* to the genuine
            // `List.rec`-fold image (exactly as `rec_list`/`case_list` bypass their own
            // non-computational `_def` axioms) makes `map`-headed terms reduce by iota:
            // `map f [] ⟶ []`, `map f (x#xs) ⟶ (f x)#(map f xs)` — HOL's `map_1`/`map_2`
            // — so those simp lemmas and `map`'s consumers verify. Gated on
            // `instance_unfold` (final escalation pass, strictly additive); the kernel
            // re-checks the saturated term, so a wrong shape is rejected.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "List.list.map" => {
                if let Some(e) = self.embed_map_list(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // ── HOL **BNF (bounded-natural-functor) combinators** for `list`
            // (gated on `instance_unfold`, strictly additive). HOL constructs the
            // `list` datatype through the BNF machinery: the shape functor
            // `pre_list = unit + 'a×'b` (its map `map_pre_list = map_sum id
            // (map_prod f1 f2)`), the constructor `ctor_list : unit + 'a×'a list ⇒
            // 'a list`, and the initial-algebra fold `ctor_fold_list : (unit + 'a×'b
            // ⇒ 'b) ⇒ 'a list ⇒ 'b` (HOL's `SOME f. mor_list … f`, the unique
            // morphism = the structural fold by initiality). The `map`/`set`/`those`
            // `_def` axioms and the BNF infrastructure lemmas (`map_id`, `map_comp`,
            // `set_map`, …) bottom out at these. Mapping each *directly* to its
            // genuine clean image (`Sum.rec`/`Prod`/`Option.rec`/`List.rec` folds —
            // `id_bnf = λx.x`) makes those equations REFLEXIVE: e.g. `map_def`
            // (`map ≡ λf. ctor_fold_list (ctor_list ∘ map_pre_list f id)`) closes by
            // `Eq.refl` because the BNF-combinator RHS is definitionally equal to
            // `map`'s `List.rec` image. The kernel re-checks every saturated term, so
            // a wrong BNF model is rejected — never miscounted.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Sum_Type.map_sum" => {
                if let Some(e) = self.embed_map_sum(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Product_Type.map_prod" => {
                if let Some(e) = self.embed_map_prod(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Option.map_option" => {
                if let Some(e) = self.embed_map_option(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            IsaTerm::Const { n, t } if self.instance_unfold && n == "BNF_Composition.id_bnf" => {
                if let Some(e) = self.embed_id_bnf(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            IsaTerm::Const { n, t } if self.instance_unfold && n == "List.list.ctor_list" => {
                if let Some(e) = self.embed_ctor_list(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            IsaTerm::Const { n, t } if self.instance_unfold && n == "List.list.ctor_fold_list" => {
                if let Some(e) = self.embed_ctor_fold_list(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            IsaTerm::Const { n, t }
                if self.instance_unfold && n == "List.pre_list.list.map_pre_list" =>
            {
                if let Some(e) = self.embed_map_pre_list(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // `Num.num` datatype constructors → the registered clean inductive's
            // constructors (`register_datatype_inductives`). Kept under the same
            // names so the recursor's iota rule fires.
            IsaTerm::Const { n, .. } if n == "Num.num.One" => Ok(Expr::const_str("Num.num.One")),
            IsaTerm::Const { n, .. } if n == "Num.num.Bit0" => Ok(Expr::const_str("Num.num.Bit0")),
            IsaTerm::Const { n, .. } if n == "Num.num.Bit1" => Ok(Expr::const_str("Num.num.Bit1")),
            // The `Num.num` datatype recursor `Num.num.rec_num`. Like `rec_nat`, its
            // instantiated type `α ⇒ (num ⇒ α ⇒ α) ⇒ (num ⇒ α ⇒ α) ⇒ num ⇒ α` is
            // the constant-motive form of clean's auto-generated `Num.rec`. Embedded
            // to the bare wrapper lambda specialised to α (read off the const type).
            IsaTerm::Const { n, t } if n == "Num.num.rec_num" => {
                if let Some(e) = self.embed_rec_num(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // The `Nat.nat` datatype **recursor** `Nat.old.nat.rec_nat`. Isabelle's
            // primitive-recursion combinator over `nat` has the (constant-motive)
            // type `'a ⇒ (nat ⇒ 'a ⇒ 'a) ⇒ nat ⇒ 'a`, which is exactly clean's
            // `Nat.rec` specialised to a non-dependent motive `λ_:Nat. α`. We embed
            // each occurrence to the bare wrapper lambda
            //   `λ(z:α)(s:Nat→α→α)(t:Nat). @Nat.rec.{u} (λ_.α) z (λ(k:Nat)(ih:α). s k ih) t`
            // reading α (and its sort `u`) off the constant's instantiated type, so
            // the recursive arithmetic definitions (`plus_nat`, `times_nat`,
            // `power`, …) — whose bodies are `rec_nat`-folds — verify by the kernel's
            // native iota/β reduction. Bare and applied occurrences agree after β.
            IsaTerm::Const { n, t } if n == "Nat.old.nat.rec_nat" => {
                if let Some(e) = self.embed_rec_nat(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // The `Nat.nat` datatype **case combinator** `Nat.nat.case_nat`. Its
            // instantiated type `α ⇒ (nat ⇒ α) ⇒ nat ⇒ α` is the non-recursive
            // case analysis (`case t of 0 ⇒ z | Suc k ⇒ f k`) — exactly clean's
            // `Nat.rec` with a constant motive `λ_:Nat. α` and a successor arm that
            // *ignores* the recursive value: `λ(k:Nat)(_ih:α). f k`. Mapping it (like
            // `rec_nat`) lets the `case_nat`-spelled definitions (`less_eq_nat`,
            // `minus_nat`, …) and their consumers verify by native iota reduction.
            // Returns to an opaque param if the type is not the expected shape.
            IsaTerm::Const { n, t } if n == "Nat.nat.case_nat" => {
                if let Some(e) = self.embed_case_nat(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // A **nat base constructor** instantiated at `nat`
            // (`Groups.zero_class.zero : nat`, `Groups.one_class.one : nat`). HOL's
            // `0 :: nat` and `1 :: nat` ARE clean's `Nat.zero` and `Nat.succ
            // Nat.zero` — the same faithfulness basis as `Nat.Suc → Nat.succ` (the
            // datatype-level identification). Their own `…_nat_def` axioms unfold
            // them to the `typedef` representation (`Abs_Nat Zero_Rep`) which has no
            // clean image, so they cannot be registered as embeddable definitions;
            // mapping them directly here lets the *recursive* nat ops (`plus`,
            // `times`, …) — whose `rec_nat` bodies mention `0::nat` in the base case
            // — embed to closed clean terms and verify. Gated on `instance_unfold`
            // (strictly additive, like the registry arm below). The kernel re-checks
            // against the use-site type, so a wrong mapping is rejected.
            IsaTerm::Const { n, t }
                if self.instance_unfold
                    && n == "Groups.zero_class.zero"
                    && matches!(t, IsaType::Type { n, a } if n == "Nat.nat" && a.is_empty()) =>
            {
                Ok(Expr::const_str("Nat.zero"))
            }
            IsaTerm::Const { n, t }
                if self.instance_unfold
                    && n == "Groups.one_class.one"
                    && matches!(t, IsaType::Type { n, a } if n == "Nat.nat" && a.is_empty()) =>
            {
                Ok(Expr::app(
                    Expr::const_str("Nat.succ"),
                    Expr::const_str("Nat.zero"),
                ))
            }
            // ── HOL `Int.int` quotient-bridge constants (gated on `instance_unfold`,
            // strictly additive). Isabelle defines `int = (nat × nat) // intrel`
            // and lifts every integer operation through the quotient's abstraction
            // `Abs_Integ : nat×nat ⇒ int` and representative `Rep_Integ : int ⇒
            // nat×nat`. Clean's prelude `Int` (`ofNat | negSucc`) is a faithful
            // *canonical representative* of each `intrel` class, so we bridge:
            //   • `Abs_Integ (a,b) = a − b`  →  `Int.subNatNat a b`
            //   • `Rep_Integ i` = a canonical `(a,b)` with `a − b = i`
            //                   →  `ofNat n ↦ (n,0)`, `negSucc n ↦ (0, n+1)`
            // These make the int instance-op `…_def` axioms (`plus_int_def`,
            // `times_int_def`, `zero_int_def`, …) embed to *closed* clean terms,
            // so `register_instance_op_def` stores each int op as a real clean
            // `Definition` and the `…_def` becomes faithfully reflexive. The kernel
            // re-checks every term, so a wrong bridge is rejected — never miscounted.
            //
            // `Int.Abs_Integ : nat×nat ⇒ int`  →  `λp:Prod Nat Nat. Int.subNatNat (fst p) (snd p)`.
            IsaTerm::Const { n, .. } if self.instance_unfold && n == "Int.Abs_Integ" => {
                Ok(self.int_abs_integ())
            }
            // `Int.Rep_Integ : int ⇒ nat×nat`  →  the canonical representative
            // `λi:Int. Int.rec (λn. (n,0)) (λn. (0, Suc n)) i`.
            IsaTerm::Const { n, .. } if self.instance_unfold && n == "Int.Rep_Integ" => {
                Ok(self.int_rep_integ())
            }
            // `Product_Type.Pair : 'a ⇒ 'b ⇒ 'a×'b`  →  `Prod.mk` at the
            // instantiated element types (read off the constant's HOL type).
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Product_Type.Pair" => {
                if let Some(e) = self.embed_pair(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // `Product_Type.prod.case_prod : ('a ⇒ 'b ⇒ 'c) ⇒ 'a×'b ⇒ 'c`  →
            // `λf p. f (fst p) (snd p)` — case analysis on a pair via the prelude
            // projections. Bare and applied occurrences agree after β.
            IsaTerm::Const { n, t }
                if self.instance_unfold && n == "Product_Type.prod.case_prod" =>
            {
                if let Some(e) = self.embed_case_prod(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // ── HOL `Sum_Type.sum` (`'a + 'b`) datatype structure (gated on
            // `instance_unfold`, the final escalation pass — strictly additive).
            // `Sum_Type.Inl : 'a ⇒ 'a+'b`  →  `@Sum.inl.{0,0} α β` (a function
            // `α → Sum α β`); the element types `α`,`β` are read off the constant's
            // instantiated HOL type. Mapping the constructor to the real clean
            // `Sum.inl` (with its implicit type args supplied explicitly) makes
            // `case_sum f g (Inl a)` reduce to `f a` by the kernel's iota rule, so the
            // `Sum_Type` case/injectivity lemmas verify. Kernel-re-checked.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Sum_Type.Inl" => {
                if let Some(e) = self.embed_sum_ctor(t, "Sum.inl")? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // `Sum_Type.Inr : 'b ⇒ 'a+'b`  →  `@Sum.inr.{0,0} α β`.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Sum_Type.Inr" => {
                if let Some(e) = self.embed_sum_ctor(t, "Sum.inr")? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // `Sum_Type.sum.case_sum : ('a⇒'c) ⇒ ('b⇒'c) ⇒ 'a+'b ⇒ 'c`  →
            // `λ(f:α→γ)(g:β→γ)(s:Sum α β). @Sum.rec.{w,0,0} (λ_.γ) f g s` — the
            // constant-motive specialisation of clean's `Sum.rec` (sum is
            // non-recursive, so the recursor arms ignore no recursive value). HOL's
            // `case_sum f g` applies `f` to `Inl`, `g` to `Inr`, matching `Sum.rec`'s
            // `inl_case` then `inr_case` order. Bare and applied occurrences agree
            // after β; the kernel re-checks the saturated term.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Sum_Type.sum.case_sum" => {
                if let Some(e) = self.embed_case_sum(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // `Sum_Type.sum.rec_sum` is the (non-recursive) sum recursor; it has the
            // SAME constant-motive type as `case_sum` (`('a⇒'c)⇒('b⇒'c)⇒'a+'b⇒'c`,
            // sum constructors carry no recursive field), so it embeds identically.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Sum_Type.sum.rec_sum" => {
                if let Some(e) = self.embed_case_sum(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // ── HOL `Option.option` (`'a option`) datatype structure (gated on
            // `instance_unfold`). `Option.option.None : 'a option`  →  `@Option.none.{0} α`.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Option.option.None" => {
                if let Some(e) = self.embed_option_none(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // `Option.option.Some : 'a ⇒ 'a option`  →  `@Option.some.{0} α`.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Option.option.Some" => {
                if let Some(e) = self.embed_option_some(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // `Option.option.case_option : 'b ⇒ ('a⇒'b) ⇒ 'a option ⇒ 'b`  →
            // `λ(z:β)(f:α→β)(o:Option α). @Option.rec.{w,0} (λ_.β) z f o` — HOL's
            // `case None ⇒ z | Some a ⇒ f a`, matching `Option.rec`'s `none_case`
            // then `some_case` order. Kernel-re-checked.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Option.option.case_option" => {
                if let Some(e) = self.embed_case_option(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // `Option.option.rec_option` — like `rec_sum`, option is non-recursive so
            // its recursor has the SAME type as `case_option` and embeds identically.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Option.option.rec_option" => {
                if let Some(e) = self.embed_case_option(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // `Fun.map_fun : ('a⇒'b) ⇒ ('c⇒'d) ⇒ ('b⇒'c) ⇒ ('a⇒'d)`  →  `λg h f x.
            // h (f (g x))` (HOL's `map_fun g h f = h ∘ f ∘ g`). The lifted int ops
            // are spelled `map_fun Rep_Integ (map_fun Rep_Integ Abs_Integ) (op on
            // representatives)`, so this closes the body to a real Int computation.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Fun.map_fun" => {
                if let Some(e) = self.embed_map_fun(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            _ => self.embed_const_term2(tm),
        }
    }
}
