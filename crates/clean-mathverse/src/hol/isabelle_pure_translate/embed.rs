// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Ctx` type/term-parameter embedding for the Isabelle Pure translator
//! (`embed_type` + the param-registration helpers). Moved verbatim from the
//! original single-file `isabelle_pure_translate` module; behaviour is
//! byte-identical.

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::Expr;

use super::super::isabelle_pure::IsaType;
use super::*;

impl Ctx {
    /// Embed a HOL type, registering any free object type as a `Type` parameter.
    pub(crate) fn embed_type(&mut self, ty: &IsaType) -> Result<Expr, TranslateError> {
        match ty {
            IsaType::Type { n, a } if n == "fun" && a.len() == 2 => {
                let dom = self.embed_type(&a[0])?;
                let cod = self.embed_type(&a[1])?;
                // Non-dependent: codomain is closed, no lift needed.
                Ok(Expr::arrow(dom, cod))
            }
            // Pure/HOL truth lives in `Prop`.
            IsaType::Type { n, .. } if n == "prop" || n == "bool" || n == "HOL.bool" => {
                Ok(Expr::prop())
            }
            // HOL's `Nat.nat` IS the natural-number datatype `0 | Suc n` — exactly
            // clean's prelude `Nat` inductive (`Nat.zero` | `Nat.succ`). Mapping it
            // to the FAITHFUL clean inductive (rather than an opaque `Type` param)
            // lets `Nat.Suc → Nat.succ` and `Nat.old.nat.rec_nat → Nat.rec`, so the
            // recursive arithmetic `*_def`s (which spell `+`/`*`/`^` via `rec_nat`)
            // verify by the kernel's native iota/δ reduction. The kernel re-checks
            // every term, so a wrong constructor/recursor mapping is rejected.
            IsaType::Type { n, a } if n == "Nat.nat" && a.is_empty() => Ok(Expr::const_str("Nat")),
            // HOL's `Num.num` is the binary-numeral datatype `One | Bit0 of num |
            // Bit1 of num`. Clean's prelude has no `Num`, so the verifier registers
            // it as a faithful inductive up front (`register_datatype_inductives`);
            // here we map the type to that inductive's const so `Num.num.One/Bit0/
            // Bit1 → Num.num.{One,Bit0,Bit1}` and `Num.num.rec_num → Num.rec`,
            // making the numeral definitions verify by the kernel's iota reduction.
            IsaType::Type { n, a } if n == "Num.num" && a.is_empty() => Ok(Expr::const_str("Num")),
            // HOL's `'a set` is, by definition, a *type-copy* of `'a ⇒ bool`
            // (`Set.set` in `Set.thy`: `typedef 'a set = "UNIV :: ('a ⇒ bool) set"`;
            // sets ARE predicates). We model it faithfully as the predicate type
            // `embed('a) → Prop` (`bool` already embeds to `Prop`), rather than
            // dropping the `'a` argument and treating `Set.set` as an opaque base
            // type-param. This makes the set-lattice instance definitions
            // (`bot_set_def`, `inf_set_def`, `less_eq_set_def`, …) faithfully
            // reflexive: each defines the `set` operation as `Collect ∘ <the same
            // class operation on the `'a ⇒ bool` instance>`, and under this model
            // `'a set` and `'a ⇒ bool` are the SAME clean type, while `Collect`
            // and `member` are the identity / application coercions (see
            // `embed_term`). The kernel re-checks every resulting term, so a wrong
            // model is rejected — never miscounted.
            IsaType::Type { n, a } if n == "Set.set" && a.len() == 1 => {
                let elem = self.embed_type(&a[0])?;
                Ok(Expr::arrow(elem, Expr::prop()))
            }
            // HOL's `'a list` (`List.list`, `datatype 'a list = Nil | Cons 'a "'a
            // list"`) IS clean's prelude inductive `List : Type u → Type u`
            // (`List.nil` | `List.cons`). Mapping the type CONSTRUCTOR (rather than
            // dropping the `'a` argument and treating `List.list` as an opaque base
            // type) lets `List.list.Nil → List.nil`, `List.list.Cons → List.cons`
            // (at the instantiated element type), and `List.list.rec_list` /
            // `List.list.case_list` → wrappers over the prelude `List.rec`, so the
            // (recursive, `rec_list`-folded) list-function `…_def` axioms (`append`,
            // `map`, `rev`, `length`, …) verify by the kernel's native iota/β
            // reduction. The element type lives in `Type = Sort 1`, so clean's
            // `List.{0}` (element-level `u = 0`) is the faithful instantiation. The
            // kernel re-checks every term, so a wrong constructor/recursor mapping is
            // rejected — never miscounted.
            IsaType::Type { n, a } if n == "List.list" && a.len() == 1 => {
                let elem = self.embed_type(&a[0])?;
                Ok(Expr::app(
                    Expr::const_str_levels("List", vec![Level::zero()]),
                    elem,
                ))
            }
            // HOL's `Int.int` is `typedef int = (nat × nat) // intrel` — the
            // quotient of `nat × nat` by the difference relation `(a,b) ~ (c,d) ⟺
            // a+d = c+b`, with the integer `a − b` as the denoted value. Clean's
            // prelude already provides a FAITHFUL integer model: the Lean-style
            // inductive `Int = Int.ofNat (n:Nat) | Int.negSucc (n:Nat)` (a canonical
            // representative of each equivalence class — `ofNat n` for `n ≥ 0`,
            // `negSucc n` for `−(n+1)`). We map `Int.int → Int` and bridge the
            // quotient abstraction/representative maps to it (see `Int.Abs_Integ` /
            // `Int.Rep_Integ` in `embed_term`), so the int instance operations'
            // `…_def` axioms become faithfully reflexive. The kernel re-checks every
            // resulting term, so a wrong model is rejected — never miscounted.
            IsaType::Type { n, a } if n == "Int.int" && a.is_empty() => Ok(Expr::const_str("Int")),
            // HOL's `'a × 'b` product (`Product_Type.prod`) IS clean's prelude
            // structure `Prod α β`. Mapping it (rather than treating `prod` as an
            // opaque base type with dropped arguments) lets the int-quotient
            // representative `nat × nat` and the `Pair`/`case_prod`/`fst`/`snd`
            // structure embed faithfully. Both clean `Prod` arguments live in
            // `Type` (`Sort ≥ 1`); `Nat`/`Int` qualify, so the kernel accepts the
            // `Prod.{0,0}`-style application produced below.
            IsaType::Type { n, a } if n == "Product_Type.prod" && a.len() == 2 => {
                let l = self.embed_type(&a[0])?;
                let r = self.embed_type(&a[1])?;
                Ok(Expr::apps(
                    Expr::const_str_levels("Prod", vec![Level::zero(), Level::zero()]),
                    [l, r],
                ))
            }
            // HOL's `'a + 'b` disjoint sum (`Sum_Type.sum`) IS clean's prelude
            // inductive `Sum α β` (`Sum.inl | Sum.inr`). Mapping it (rather than
            // treating `sum` as an opaque base type with dropped arguments) lets the
            // `Inl`/`Inr`/`case_sum`/`rec_sum` structure embed faithfully so the
            // `Sum_Type.*` library lemmas (case rules, injectivity, exhaustion)
            // verify by the kernel's native iota/β reduction. Both clean `Sum`
            // arguments live in `Type` (`Sort ≥ 1`) and every embedded HOL object
            // type is `Sort 1`, so the `Sum.{0,0}` application typechecks. Gated on
            // `instance_unfold` (the final escalation pass), so passes 1–3 keep the
            // historical opaque-`sum` embedding and no prior success regresses; the
            // kernel re-checks every term, so a wrong mapping is rejected.
            IsaType::Type { n, a }
                if self.instance_unfold && n == "Sum_Type.sum" && a.len() == 2 =>
            {
                let l = self.embed_type(&a[0])?;
                let r = self.embed_type(&a[1])?;
                Ok(Expr::apps(
                    Expr::const_str_levels("Sum", vec![Level::zero(), Level::zero()]),
                    [l, r],
                ))
            }
            // HOL's `'a option` (`Option.option`) IS clean's prelude inductive
            // `Option α` (`Option.none | Option.some`). Same faithfulness basis as
            // `sum`/`prod`: mapping it (not an opaque type-param) lets the
            // `None`/`Some`/`case_option`/`rec_option` structure embed so the
            // `Option.*` library lemmas verify by native iota/β reduction. The single
            // clean `Option` argument lives in `Type` (`Sort ≥ 1`), matching the
            // `Sort 1` of every embedded HOL object type, so `Option.{0}` typechecks.
            // Gated on `instance_unfold` for strict additivity; kernel-re-checked.
            IsaType::Type { n, a }
                if self.instance_unfold && n == "Option.option" && a.len() == 1 =>
            {
                let elem = self.embed_type(&a[0])?;
                Ok(Expr::app(
                    Expr::const_str_levels("Option", vec![Level::zero()]),
                    elem,
                ))
            }
            // HOL's `unit` (`Product_Type.unit`) — the single-element type `{()}` —
            // IS clean's prelude `Unit` (`Sort 1`, single ctor `Unit.unit`). Mapping
            // it (rather than an opaque base param) lets the BNF shape functor
            // `pre_list = unit + 'a×'b` and its constructor/fold combinators
            // (`ctor_list`/`ctor_fold_list`/`map_pre_list`) embed faithfully, so the
            // list `map`/`set`/`those` `_def` axioms and BNF lemmas close. Gated on
            // `instance_unfold` (strictly additive); the kernel re-checks every term.
            IsaType::Type { n, a }
                if self.instance_unfold && n == "Product_Type.unit" && a.is_empty() =>
            {
                Ok(Expr::const_str("Unit"))
            }
            // Any other base type / free type var → an abstract `Type` parameter.
            // A `TFree` may be a box-internal spelling of the statement's
            // varified `?'a.0` — see [`Self::type_param_free`] (aliasing active
            // only while the recorded proof value is translated).
            IsaType::Type { n, .. } => Ok(self.type_param(n)),
            IsaType::TFree { n } => Ok(self.type_param_free(n)),
            IsaType::TVar { n, i } => Ok(self.type_param(&format!("{n}.{i}"))),
        }
    }

    /// Register (idempotently) an abstract object type as a quantified `Type`
    /// parameter and return its fvar.
    pub(crate) fn type_param(&mut self, name: &str) -> Expr {
        let fvar = param_fvar(0, name);
        if !self.type_params.iter().any(|(k, _)| k == name) {
            self.type_params.push((
                name.to_string(),
                Param {
                    fvar,
                    ty: Expr::type_(),
                },
            ));
        }
        Expr::fvar(fvar)
    }

    /// Register (idempotently) a class object type variable `(name, index)` as a
    /// quantified `Type` parameter, using the SAME key as [`Self::embed_type`]'s
    /// `TVar` arm (`"{n}.{i}"`), so a method-def body's `α` binder coincides with
    /// any occurrence the embedder discovers in operation types.
    pub(crate) fn tvar_param(&mut self, tv: &(String, i64)) -> Expr {
        self.type_param(&format!("{}.{}", tv.0, tv.1))
    }

    /// Register (idempotently) an overloaded/opaque HOL constant `n` at embedded
    /// type `ty` as a shared `const:` term param, keyed by name **AND** type via
    /// [`const_param_key`]. Two occurrences of the same constant at DIFFERENT
    /// embedded types get DISTINCT params (fixing the two-`Field`/two-carrier
    /// poly-inst collision); at the SAME embedded type they share one param
    /// exactly as the historical name-only key did (the disc is identical), so
    /// every single-instantiation reflexivity is byte-preserved.
    pub(crate) fn const_param(&mut self, n: &str, ty: Expr) -> Expr {
        let key = const_param_key(n, &ty);
        self.term_param(&key, ty)
    }

    /// Register (idempotently) a free term variable as a quantified parameter.
    pub(crate) fn term_param(&mut self, name: &str, ty: Expr) -> Expr {
        let fvar = param_fvar(1, name);
        if !self.term_params.iter().any(|(k, _)| k == name) {
            self.term_params
                .push((name.to_string(), Param { fvar, ty }));
        }
        Expr::fvar(fvar)
    }

    /// [`Self::term_param`] for a **`Free`-spelled** variable, with box-internal
    /// free → statement-schematic aliasing when [`Ctx::alias_frees`] is active.
    ///
    /// The zproof export spells a derivation box's INTERNAL variables as
    /// unvarified `Free x` while the exported statement carries the varified
    /// `?x.0` (`Thm.generalize` renames `x ↦ ?x.0` at the box boundary — the
    /// SAME variable, two spellings). The two spellings embed under DIFFERENT
    /// param keys (`x` vs `x.0`), so a proof-internal `Free x` operand could
    /// never match the statement's quantified parameter — the mixed-keying
    /// `expected=FVar got=FVar` reject family. When aliasing is active (ONLY
    /// while the recorded proof VALUE is translated — the statement and every
    /// stored-type override embed with it off), a `Free x` whose bare key `x`
    /// is not yet registered but whose varified key `x.0` IS — with the SAME
    /// embedded type — reuses that statement param. FAITHFUL: the stored
    /// theorem type is untouched (aliasing never runs while it is embedded),
    /// and the kernel re-checks `value : type`, so a wrong aliasing is
    /// rejected — never miscounted.
    pub(crate) fn term_param_free(&mut self, name: &str, ty: Expr) -> Expr {
        if self.alias_frees && !self.term_params.iter().any(|(k, _)| k == name) {
            let varified = format!("{name}.0");
            if let Some((_, p)) = self.term_params.iter().find(|(k, _)| *k == varified) {
                if p.ty == ty {
                    return Expr::fvar(p.fvar);
                }
            }
            // Method-constant flavor (round 9): a class-target derivation box
            // fixes the class OPERATIONS as frees named like the method's short
            // name (`Free less_eq` for `Orderings.ord_class.less_eq`), while the
            // consumer's statement spells the METHOD CONSTANT itself, registered
            // under `const:<full-name>`. The two spellings are the SAME variable
            // (Isabelle's class target replaces the fixed free by the global
            // method constant on export); embedding the free verbatim would mint
            // a second operand pair next to the statement's, desynchronizing
            // every dependency premise against the statement-flavored hypothesis
            // PBounds (the `polyinst.class.<c>(…,le,lt)` vs `(…,le',lt')`
            // intro_of_class family). Alias to the UNIQUE type-identical
            // `const:*.{name}` param when one exists; ambiguity or a type
            // mismatch falls through to the verbatim mint. Active only while the
            // recorded proof VALUE is translated (`alias_frees`), so the stored
            // statement embedding is untouched; the kernel re-checks
            // `value : type`, so a wrong aliasing is rejected — never miscounted.
            let dotted = format!(".{name}");
            let mut matched: Option<FVarId> = None;
            for (k, p) in &self.term_params {
                let is_const_flavor =
                    const_key_name(k).is_some_and(|full| full.ends_with(dotted.as_str()));
                if is_const_flavor && p.ty == ty {
                    if matched.is_some() {
                        matched = None; // ambiguous — embed verbatim
                        break;
                    }
                    matched = Some(p.fvar);
                }
            }
            if let Some(fvar) = matched {
                return Expr::fvar(fvar);
            }
        }
        self.term_param(name, ty)
    }

    /// [`Self::type_param`] for a **`TFree`-spelled** type variable, with the
    /// same box-internal free → statement-schematic aliasing as
    /// [`Self::term_param_free`] (`'a` vs the statement's varified `?'a.0`),
    /// active only under [`Ctx::alias_frees`]. Type params carry no
    /// distinguishing type, so the alias is keyed purely on `"{n}.0"` being
    /// registered while `"{n}"` is not; the kernel re-checks the proof value
    /// built with it, so a wrong aliasing is rejected — never miscounted.
    pub(crate) fn type_param_free(&mut self, name: &str) -> Expr {
        if self.alias_frees && !self.type_params.iter().any(|(k, _)| k == name) {
            let varified = format!("{name}.0");
            if let Some((_, p)) = self.type_params.iter().find(|(k, _)| *k == varified) {
                return Expr::fvar(p.fvar);
            }
        }
        self.type_param(name)
    }

    /// Register (idempotently) a free Pure hypothesis as a quantified proof
    /// parameter `(h : Hprop)`, keyed by the hypothesis text.
    pub(crate) fn hyp_param(&mut self, key: &str, prop_ty: Expr) -> Expr {
        let fvar = param_fvar(2, key);
        if !self.hyp_params.iter().any(|(k, _)| k == key) {
            self.hyp_params
                .push((key.to_string(), Param { fvar, ty: prop_ty }));
        }
        Expr::fvar(fvar)
    }
}
