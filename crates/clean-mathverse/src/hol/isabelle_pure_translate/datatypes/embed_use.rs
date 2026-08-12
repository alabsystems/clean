// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Ctx` connective / class-membership / registered-use embedding and the core
//! application-dispatch + type-inference helpers: `embed_bare_connective`,
//! `embed_class_membership`, `embed_method_use`, `embed_list_fn_use`,
//! `embed_poly_inst_use`, `embed_hol_if`, `embed_fun_comp`, `embed_fun_id`,
//! `embed_app`, `infer_type`, `prop_result_head`, `embed_type_or_infer`. Moved
//! verbatim from the original single-file `datatypes` module; behaviour is
//! byte-identical.

use clean_kernel::{BinderInfo, Expr};

use super::super::super::isabelle_pure::{IsaTerm, IsaType};
use super::super::*;

impl Ctx {
    /// Embed a **bare** (un-applied) logical/structural connective to its
    /// η-expanded semantic lambda, matching exactly what the *applied* arms of
    /// [`Self::embed_term`] produce after β-reduction. See the call site for why
    /// this fixes the connective fold/unfold `TypeMismatch`.
    ///
    /// - `Pure.imp` / `HOL.implies` (`prop ⇒ prop ⇒ prop`):
    ///   `λ(A:Prop)(B:Prop). A → B`.
    /// - `Pure.all` / `HOL.All` (`(α ⇒ prop) ⇒ prop`):
    ///   `λ(P:α→Prop). ∀(x:α). P x`.
    /// - `HOL.eq` / `Pure.eq` / `=` (`α ⇒ α ⇒ bool`):
    ///   `λ(x:α)(y:α). @Eq α x y`.
    pub(crate) fn embed_bare_connective(
        &mut self,
        n: &str,
        t: &IsaType,
    ) -> Result<Expr, TranslateError> {
        match n {
            // `λ(A:Prop)(B:Prop). A → B` — both operands embed to `Prop`. The
            // arrow is `Pi(_:A) B`; `B` (`bvar 0` in the lambda body) sits under
            // the fresh `Pi` binder, so it lifts to `bvar 1`. `A` is the `Pi`
            // domain (evaluated outside the `Pi`), so it stays `bvar 1`.
            "Pure.imp" | "HOL.implies" => Ok(Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(
                    BinderInfo::Default,
                    Expr::prop(),
                    Expr::arrow(Expr::bvar(1), Expr::bvar(1)),
                ),
            )),
            // `λ(P:α→Prop). ∀(x:α). P x` — α is the binder quantifier's object
            // type, read from the predicate type `α ⇒ prop` in `(α⇒prop)⇒prop`.
            "Pure.all" | "HOL.All" => {
                let pred_ty = eq_operand_type(t)
                    .ok_or(TranslateError::Unsupported("bare all: no predicate type"))?;
                let dom_ty = eq_operand_type(pred_ty)
                    .ok_or(TranslateError::Unsupported("bare all: no domain type"))?;
                let dom = self.embed_type(dom_ty)?;
                // P : α → Prop is the outer binder (bvar 1 inside), x : α inner.
                let pred = Expr::arrow(dom.clone(), Expr::prop());
                let body = Expr::pi(
                    BinderInfo::Default,
                    dom,
                    Expr::app(Expr::bvar(1), Expr::bvar(0)),
                );
                Ok(Expr::lam(BinderInfo::Default, pred, body))
            }
            // `λ(x:α)(y:α). @Eq α x y` — α from the operand type `α ⇒ α ⇒ bool`.
            "HOL.eq" | "Pure.eq" | "=" => {
                let dom_ty = eq_operand_type(t)
                    .ok_or(TranslateError::Unsupported("bare eq: no operand type"))?;
                let dom = self.embed_type(dom_ty)?;
                let eq_body = Expr::apps(
                    Expr::const_str_levels("Eq", vec![obj_level()]),
                    [dom.clone().lift(2), Expr::bvar(1), Expr::bvar(0)],
                );
                Ok(Expr::lam(
                    BinderInfo::Default,
                    dom.clone(),
                    Expr::lam(BinderInfo::Default, dom.lift(1), eq_body),
                ))
            }
            _ => Err(TranslateError::Unsupported("bare connective unmapped")),
        }
    }

    /// Embed a class-membership application `c_class (TYPE('a))` (the proof-term
    /// encoding of `OFCLASS('a, c_class)`).
    ///
    /// - If `c_class` is a **structured** class registered in
    ///   [`Self::class_registry`], produce the real membership proposition
    ///   `isabelle.def.<c_class> α op₁ … opₙ` — the registered polymorphic
    ///   definition applied to the object type `α` (read from the `itself('a)`
    ///   argument) and to each class operation in the registered order. Each
    ///   operation is re-embedded **in this consumer's context**, so it registers
    ///   the same `term_param("const:<op>")` the rest of the theorem uses,
    ///   keeping the operations coherent across the membership premise and the
    ///   conclusion. The kernel δ-unfolds the def-const to the axiom conjunction.
    /// - Otherwise (a base sort, `HOL.type_class`, or an as-yet-unregistered
    ///   class) it is vacuous → `True`.
    pub(crate) fn embed_class_membership(&mut self, tm: &IsaTerm) -> Result<Expr, TranslateError> {
        // In the default `Erase` pass, every class membership is vacuous `True`
        // (the historical behaviour). Only the `Real` retry consults the registry.
        if !self.class_membership {
            // `NonemptyErase` (the trailing faithfulness-restoring mode): embed the
            // sort premise as the weakest faithful carrier `Nonempty α` (HOL types
            // are inhabited) instead of `True`, so the vacuous-quantifier and
            // `∧`-miniscoping simp laws — false-as-embedded under `True`-erasure —
            // gain the witness `Classical.choice` needs. Falls back to `True`
            // (byte-identical to the historical erasure) whenever the object type `α`
            // cannot be read from the `itself('a)` argument.
            if self.nonempty_erase {
                return self.embed_nonempty_erase_membership(tm);
            }
            return Ok(Expr::const_str("True"));
        }
        let (class_name, itself_arg) = match tm {
            IsaTerm::App { f, a } => match f.as_ref() {
                IsaTerm::Const { n, .. } => (n.as_str(), a.as_ref()),
                _ => return Ok(Expr::const_str("True")),
            },
            _ => return Ok(Expr::const_str("True")),
        };
        let Some(info) = self.class_registry.get(class_name).cloned() else {
            return Ok(Expr::const_str("True"));
        };
        // The object type `α` is the parameter of the `itself('a)` argument's
        // type (`Pure.type : itself('a)`).
        let alpha = match class_type_arg(itself_arg) {
            Some(ty) => self.embed_type(ty)?,
            None => return Ok(Expr::const_str("True")),
        };
        // Apply the def-const to α, then to each extra fixed ground-type param
        // (re-embedded in this context as the same global `type_param(name)`, so a
        // class whose body references a fixed type like `Nat.nat`/`'a set`
        // saturates every type binder of the definition), then to each class
        // operation (re-embedded as the shared `const:<op>` param).
        let mut e = Expr::app(Expr::const_str(&info.def_name), alpha);
        for ty_name in &info.extra_type_consts {
            let ty_e = self.type_param(ty_name);
            e = Expr::app(e, ty_e);
        }
        for (op_name, op_ty) in &info.ops {
            // Each class operation is re-embedded through the FULL `Const`
            // dispatch ([`Self::embed_element_op`]) — the SAME path a term-level
            // occurrence of the operation takes in the current pass. Under the
            // Opaque passes this is the shared `const:<op>` param exactly as
            // before; under an Unfold pass a registered LOCALE-PREDICATE op
            // (`Thy.class.c`, quantified by a structured class-def body since
            // r8) embeds as its `isabelle.polyinst.<c>` def-const application —
            // the same spelling the statement's own `class.c le lt` hypotheses
            // take in that pass. One spelling per pass keeps a membership's
            // `def.<c>_class α ops…` structurally reconcilable with the
            // membership chain (`intro_of_class` verified the whole chain only
            // when the class was UNREGISTERED — uniformly opaque; round 9). The
            // kernel re-checks the consuming proof either way.
            let op_e = self.embed_element_op(op_name, op_ty)?;
            e = Expr::app(e, op_e);
        }
        Ok(e)
    }

    /// [`ClassMembership::NonemptyErase`] embedding of a class-membership app
    /// `c_class (TYPE('a))`: the weakest faithful carrier `@Nonempty.{1} α`, where
    /// `α` is read from the `itself('a)` argument (`Pure.type : itself('a)`). This is
    /// SOUND for every sort class — `type_class` is the weakest HOL sort and all
    /// classes extend it, so any `OFCLASS('a, c)` entails `'a` is an inhabited type.
    /// Falls back to the vacuous `True` (the historical `Erase` spelling) when the
    /// object type cannot be read, so a shape we do not recognise degrades to the
    /// byte-identical historical behaviour for that premise. The kernel re-checks the
    /// consuming proof, so a wrong witness is rejected — never miscounted.
    fn embed_nonempty_erase_membership(&mut self, tm: &IsaTerm) -> Result<Expr, TranslateError> {
        let itself_arg = match tm {
            IsaTerm::App { f, a } if matches!(f.as_ref(), IsaTerm::Const { .. }) => a.as_ref(),
            _ => return Ok(Expr::const_str("True")),
        };
        let Some(ty) = class_type_arg(itself_arg) else {
            return Ok(Expr::const_str("True"));
        };
        let alpha = self.embed_type(ty)?;
        Ok(Expr::apps(
            Expr::const_str_levels("Nonempty", vec![obj_level()]),
            [alpha],
        ))
    }

    /// Embed a use of a **registered overloaded class method** `c_class.method`
    /// (instantiated HOL type `use_ty`) to its dictionary def-const application
    /// `method_def α₁…αₖ impl op₁ … opₙ`. The object types are solved by
    /// simultaneously matching the registered method type against `use_ty`
    /// ([`match_tvars`]); the impl and ops are re-embedded at that concrete
    /// instantiation as the shared global `const:<n>` params (exactly the
    /// constants the `…_dict` RHS embeds, so the equation is reflexive). A ground
    /// (zero-`TVar`) method matches only when the use-site type coincides
    /// verbatim. Returns `None` when the use-site type does not match the
    /// registered method type (the caller then falls back to the opaque-param
    /// embedding). See [`MethodDefInfo`].
    pub(crate) fn embed_method_use(
        &mut self,
        name: &str,
        use_ty: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        let Some(info) = self.method_registry.get(name).cloned() else {
            return Ok(None);
        };
        // Solve each `'aᵢ := Tᵢ` by matching the registered method type against
        // this use. For a ground method (no `TVar`s) the match degenerates to a
        // structural equality check of the two types.
        let Some(subs) = match_tvars(&info.method_ty, use_ty, &info.obj_tvars) else {
            return Ok(None);
        };
        // `method_def α₁ … αₖ` …
        let mut e = Expr::const_str(&info.def_name);
        for (_tv, inst) in &subs {
            let alpha = self.embed_type(inst)?;
            e = Expr::app(e, alpha);
        }
        // … each extra fixed ground type constructor (`Num.num`, `Nat.nat`, …),
        // re-embedded as the same global `type_param(name)` so every type binder
        // of the definition is saturated …
        for ty_name in &info.extra_type_consts {
            let ty_e = self.type_param(ty_name);
            e = Expr::app(e, ty_e);
        }
        // … `impl` and each operation, re-embedded at the use-site instantiation
        // **through the shared const embedder** — the SAME path any other
        // occurrence of that constant takes in this context. This keeps the
        // method unfolding definitionally consistent with the `…_dict` RHS in
        // EVERY escalation mode: under `InstanceEmbed::Opaque` the embedder's
        // catch-all produces exactly the historical `const:<n>` param
        // (byte-identical behaviour), while under `InstanceEmbed::Unfold` a
        // dictionary impl with a semantic arm (`Orderings.ord.max`/`min` → the
        // If-lambda) embeds semantically HERE too — previously the impl stayed a
        // hardcoded opaque param while the equation RHS embedded semantically,
        // so `method.max α impl ops` could never δ-reduce to the RHS and every
        // dict-glue reflexivity kernel-rejected (`expected=Eq got=Eq` with
        // `impl ops` vs the semantic lambda). The kernel re-checks the result,
        // so a wrong embedding is rejected — never miscounted.
        let impl_ty = subst_tvars(&info.impl_const.1, &subs);
        let impl_tm = IsaTerm::Const {
            n: info.impl_const.0.clone(),
            t: impl_ty,
        };
        let impl_e = self.embed_const_term(&impl_tm)?;
        e = Expr::app(e, impl_e);
        for (op_name, op_ty) in &info.ops {
            let op_ty_inst = subst_tvars(op_ty, &subs);
            let op_tm = IsaTerm::Const {
                n: op_name.clone(),
                t: op_ty_inst,
            };
            let op_e = self.embed_const_term(&op_tm)?;
            e = Expr::app(e, op_e);
        }
        Ok(Some(e))
    }

    /// Embed a use of a **registered plain polymorphic list function** `c` at the
    /// use-site instantiated HOL type `use_ty` to `@isabelle.listfn.<c> T₁ … Tₙ`,
    /// where `Tᵢ` is the type each object type variable `'aᵢ` was instantiated to
    /// (solved by matching the registered function type against `use_ty`, in the
    /// canonical `obj_tvars` order the def-const abstracts them). The def-const
    /// δ-unfolds to the registered `rec_list`/`case_list`-fold body specialised at
    /// the `Tᵢ`, so the function's `…_def` axiom is reflexive and consumers stay
    /// consistent. Returns `None` when the use-site type does not match the
    /// registered type (the caller then falls back to the opaque-param embedding).
    pub(crate) fn embed_list_fn_use(
        &mut self,
        name: &str,
        use_ty: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        let Some(info) = self.list_fn_registry.get(name).cloned() else {
            return Ok(None);
        };
        // Solve each `'aᵢ := Tᵢ` by matching the registered function type against
        // this use, IN THE CANONICAL ORDER the def-const abstracts the binders, and
        // embed each solution as a leading type argument. A mismatch on any
        // variable (wrong shape, or the same variable solved to two different
        // types) bails to the opaque fallback.
        let mut e = Expr::const_str(&info.def_name);
        for tv in &info.obj_tvars {
            let Some(inst) = match_tvar(&info.fn_ty, use_ty, tv) else {
                return Ok(None);
            };
            let alpha = self.embed_type(&inst)?;
            e = Expr::app(e, alpha);
        }
        Ok(Some(e))
    }

    /// Embed a use of a **registered polymorphic instance operation** `c` at the
    /// use-site instantiated HOL type `use_ty` to
    /// `isabelle.polyinst.<c> α extra-types… op₁ … opₘ`, where `α` is the object type
    /// `'a` was instantiated to (solved by matching the registered type against
    /// `use_ty`), each extra ground type constructor is re-embedded as the same global
    /// `type_param`, and each operation is re-embedded at the use-site instantiation as
    /// the same global `const:<op>` param. The def-const δ-unfolds to the registered
    /// body and the residual argument arrows are filled by the consumer's own
    /// application, so the `_def` axiom is reflexive and every use-site stays
    /// consistent. Returns `None` when the use-site type does not match (the caller
    /// falls back to the opaque-param embedding; the kernel re-checks either way).
    pub(crate) fn embed_poly_inst_use(
        &mut self,
        name: &str,
        use_ty: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        let Some(info) = self.poly_inst_registry.get(name).cloned() else {
            return Ok(None);
        };
        // **G4 instance-link ALIAS** (`Enum.enum_fun_inst.enum_fun`, …): the
        // impl const IS the class operation at its instance, so re-embed it as
        // the METHOD at the occurrence type through the full `Const` dispatch —
        // the registry-driven generalisation of [`bool_impl_const_class_op`] /
        // [`ground_impl_const_class_op`] (same fresh-binder discipline via
        // [`Self::embed_element_op`], same `instance_unfold` gating at the call
        // site). Whatever the method's embedding at that type is in this pass
        // (opaque `const:` param, ground/dict def-const, a G4 `instk`
        // def-const), the impl now shares it, so the overloading LINK axiom
        // `method ≡ impl` is genuinely reflexive and every impl use-site stays
        // consistent with every method use-site. Kernel-re-checked either way.
        if let Some(method) = &info.alias_of {
            let method = method.clone();
            return self.embed_element_op(&method, use_ty).map(Some);
        }
        self.embed_poly_inst_info_use(&info, use_ty)
    }

    /// Shared applier for a [`PolyInstInfo`] registration (poly-inst lane and
    /// the G4 method-inst lane): solve the object tvars against `use_ty`, then
    /// apply the def-const to the solved types, the extra ground type
    /// constructors, and the re-embedded class operations.
    fn embed_poly_inst_info_use(
        &mut self,
        info: &PolyInstInfo,
        use_ty: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        // Solve every `'aᵢ := Tᵢ` SIMULTANEOUSLY by matching the registered type
        // against this use, in the def-const's binder (first-occurrence) order —
        // the multi-tvar G1 generalization ([`match_tvars`], exactly the dict
        // machinery's discipline). Empty for a ground constant (the match then
        // just checks the use-site type coincides structurally).
        let Some(subs) = match_tvars(&info.fn_ty, use_ty, &info.obj_tvars) else {
            return Ok(None);
        };
        let mut e = Expr::const_str(&info.def_name);
        for (_tv, inst) in &subs {
            let alpha = self.embed_type(inst)?;
            e = Expr::app(e, alpha);
        }
        // Each extra fixed ground type constructor, re-embedded as the same global
        // `type_param(name)` so every type binder of the definition is saturated.
        for ty_name in &info.extra_type_consts {
            let ty_e = self.type_param(ty_name);
            e = Expr::app(e, ty_e);
        }
        // Each class operation, re-embedded at the use-site instantiation through
        // the FULL `Const` dispatch ([`Self::embed_element_op`]) — the SAME path
        // the theorem's own RHS occurrence of the operation takes in the current
        // pass. For an unregistered operation this is the opaque `const:<op>`
        // param (the identical key the registration discovered, exactly as
        // before); for an operation that IS registered elsewhere (e.g. `lfp` as
        // an overloaded method under `method_unfold`) it is that registration's
        // def-const form. Supplying the SAME form the RHS uses keeps the
        // def-const's δβ-unfold `body[op := supplied]` bit-identical to the
        // embedded RHS, so the `_def` equation stays reflexive in every pass —
        // a raw `term_param` here would diverge from a method-unfolded RHS
        // (`finite_def`'s `lfp` was exactly that mismatch). The kernel re-checks
        // the result either way, so a wrong supply is rejected — never miscounted.
        for (op_name, op_ty) in &info.ops {
            let op_ty_inst = subst_tvars(op_ty, &subs);
            let op_e = self.embed_element_op(op_name, &op_ty_inst)?;
            e = Expr::app(e, op_e);
        }
        Ok(Some(e))
    }

    /// **G4 lookup:** the registered **method-at-constructor instance
    /// definition** matching an occurrence of overloaded method `name` at
    /// instantiated type `use_ty`, or `None`. Range-scans the composite
    /// `"{name}\t…"` keys ([`method_inst_registry_key`]) and returns the first
    /// registration whose recorded instance type unifies with `use_ty`
    /// ([`match_tvars`] over the registration's own tvars — the same solve the
    /// applier re-runs). Pure (`&self`), so the `embed_const_term2` dispatch
    /// arm can use it as a match GUARD: when no registration matches, the arm
    /// never fires and the historical dispatch (dict method arm, catch-all)
    /// continues byte-identically.
    pub(crate) fn find_method_inst(&self, name: &str, use_ty: &IsaType) -> Option<PolyInstInfo> {
        let prefix = format!("{name}\t");
        for (key, info) in self.poly_inst_registry.range(prefix.clone()..) {
            if !key.starts_with(&prefix) {
                break;
            }
            if match_tvars(&info.fn_ty, use_ty, &info.obj_tvars).is_some() {
                return Some(info.clone());
            }
        }
        None
    }

    /// **G4 use-site embedding:** embed an occurrence of overloaded method
    /// `name` at instance type `use_ty` to its registered method-at-constructor
    /// def-const application `@isabelle.instk.<m>@<K> T₁ … Tₖ extra… op₁ … opₘ`
    /// (which δ-unfolds to the registered body — the instance `_def` equation
    /// and every consumer then share one defeq-unfolding head), via the shared
    /// [`Self::embed_poly_inst_info_use`] applier. Returns `None` when no
    /// registration matches (the caller falls back; kernel re-checks always).
    pub(crate) fn embed_method_inst_use(
        &mut self,
        name: &str,
        use_ty: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        let Some(info) = self.find_method_inst(name, use_ty) else {
            return Ok(None);
        };
        self.embed_poly_inst_info_use(&info, use_ty)
    }

    /// Embed an occurrence of HOL's if-then-else `HOL.If : bool ⇒ 'a ⇒ 'a ⇒ 'a`
    /// (condition first) to the registered polymorphic def-const applied to the
    /// use-site element type: `@isabelle.def.HOL.If.{u} T`.
    ///
    /// `use_ty` is the constant's instantiated type `bool ⇒ T ⇒ T ⇒ T`; the
    /// element type `T` is its second arrow domain, and `u` is the universe `T`
    /// inhabits (so the recursor-level matches). The def-const δ-unfolds to
    /// `λ(c)(x)(y). ite T c (decInst c) x y` specialised at `T`, so the `…_def`
    /// body and any use-site share one head and stay definitionally consistent.
    /// Returns `None` when `use_ty` is not the expected `bool ⇒ T ⇒ T ⇒ T` shape
    /// (e.g. a `dummy`-typed `_def_raw` occurrence), so the caller can fall back to
    /// the opaque-param embedding (the kernel re-checks the result either way).
    pub(crate) fn embed_hol_if(
        &mut self,
        use_ty: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        // use_ty = bool ⇒ (T ⇒ (T ⇒ T)); read `T` off the second arrow's domain.
        let Some((_cond_ty, rest)) = fun_split(use_ty) else {
            return Ok(None);
        };
        let Some((elem_ty, _)) = fun_split(rest) else {
            return Ok(None);
        };
        let alpha = self.embed_type(elem_ty)?;
        let u = type_universe_level(&alpha);
        Ok(Some(Expr::app(
            Expr::const_str_levels(hol_if_def_name(), vec![u]),
            alpha,
        )))
    }

    /// Embed an occurrence of HOL's function composition
    /// `Fun.comp : ('b⇒'c) ⇒ ('a⇒'b) ⇒ ('a⇒'c)` to the registered polymorphic
    /// def-const applied to the use-site's three solved element types, in the
    /// def-const's binder order `(α, β, γ)`:
    /// `isabelle.def.Fun.comp T_a T_b T_c`.
    ///
    /// `use_ty` is the constant's instantiated type `(β⇒γ) ⇒ (α⇒β) ⇒ (α⇒γ)`; read
    /// `β`/`γ` off the first arrow's domain `β⇒γ` and `α` off the second arrow's
    /// domain `α⇒β`. The def-const δ-unfolds to `λf g x. f (g x)` specialised at
    /// those three types, so the `comp_def` LHS use and the RHS body share one head
    /// and stay definitionally consistent. Returns `None` when `use_ty` is not the
    /// expected nested-arrow shape (e.g. a `dummy`-typed `_def_raw` occurrence), so
    /// the caller falls back to the opaque-param embedding (kernel re-checks either
    /// way).
    pub(crate) fn embed_fun_comp(
        &mut self,
        use_ty: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        // use_ty = (β⇒γ) ⇒ ((α⇒β) ⇒ (α⇒γ))
        let Some((f_ty, rest)) = fun_split(use_ty) else {
            return Ok(None);
        };
        let Some((g_ty, _res)) = fun_split(rest) else {
            return Ok(None);
        };
        // f_ty = β ⇒ γ ; g_ty = α ⇒ β.
        let Some((beta_ty, gamma_ty)) = fun_split(f_ty) else {
            return Ok(None);
        };
        let Some((alpha_ty, _beta2)) = fun_split(g_ty) else {
            return Ok(None);
        };
        let alpha = self.embed_type(alpha_ty)?;
        let beta = self.embed_type(beta_ty)?;
        let gamma = self.embed_type(gamma_ty)?;
        Ok(Some(Expr::apps(
            Expr::const_str(fun_comp_def_name()),
            [alpha, beta, gamma],
        )))
    }

    /// Embed an occurrence of HOL's identity `Fun.id : 'a⇒'a` to the registered
    /// polymorphic def-const applied to the use-site element type:
    /// `isabelle.def.Fun.id T`. `use_ty` is `α⇒α`; `α` is its arrow domain. The
    /// def-const δ-unfolds to `λx. x` specialised at `α`, so `id_def` (`id ≡ λx. x`)
    /// verifies reflexively. Returns `None` when `use_ty` is not the expected
    /// `α⇒α` shape.
    pub(crate) fn embed_fun_id(
        &mut self,
        use_ty: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        let Some((alpha_ty, _cod)) = fun_split(use_ty) else {
            return Ok(None);
        };
        let alpha = self.embed_type(alpha_ty)?;
        Ok(Some(Expr::app(Expr::const_str(fun_id_def_name()), alpha)))
    }

    /// Embed an occurrence of a **point-free HOL logical constant**
    /// (`HOL.Uniq`/`Ex1`/`Let`/`induct_forall`/`induct_equal`/`NO_MATCH`) to its
    /// registered polymorphic def-const ([`pointfree_const_def_name`]) applied to
    /// the use-site's solved object type(s), so the constant's `…_def_raw` axiom
    /// verifies reflexively (`C args` δβ-reduces to the embedded body) and every
    /// occurrence shares one defeq-unfolding head. `use_ty` is the constant's
    /// instantiated HOL type; the object type parameters are read from its arrow
    /// structure:
    ///   - unary (`Uniq`/`Ex1`/`induct_forall` = `(α⇒Prop)⇒Prop`,
    ///     `induct_equal` = `α⇒α⇒Prop`): α from the first domain (peeling the
    ///     predicate wrapper for the `(α⇒Prop)⇒Prop` shapes);
    ///   - binary (`Let` = `α⇒(α⇒β)⇒β`, `NO_MATCH` = `α⇒β⇒Prop`): α then β.
    /// Returns `None` when `use_ty` is not the expected arrow shape (the caller then
    /// falls back to the opaque `const:` param; the kernel re-checks either way).
    pub(crate) fn embed_pointfree_const(
        &mut self,
        n: &str,
        use_ty: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        let Some(def) = pointfree_const_def_name(n) else {
            return Ok(None);
        };
        // The object type arguments, in the def-const's leading-`Type`-binder order.
        let type_args: Vec<&IsaType> = match n {
            // `(α⇒Prop)⇒Prop` (and fComp's `(α⇒Prop)⇒α⇒Prop` / fChoice's
            // `(α⇒Prop)⇒α`) — α is the domain of the predicate argument type.
            "HOL.Uniq" | "HOL.Ex1" | "HOL.induct_forall" | "ATP.fAll" | "ATP.fEx" | "ATP.fComp"
            | "ATP.fChoice" => {
                let Some((pred_ty, _)) = fun_split(use_ty) else {
                    return Ok(None);
                };
                let Some((alpha_ty, _)) = fun_split(pred_ty) else {
                    return Ok(None);
                };
                vec![alpha_ty]
            }
            // `α⇒α⇒Prop` — α is the first arrow domain.
            "HOL.induct_equal" | "ATP.fequal" => {
                let Some((alpha_ty, _)) = fun_split(use_ty) else {
                    return Ok(None);
                };
                vec![alpha_ty]
            }
            // `α⇒(α⇒β)⇒β` — α from the first domain, β from the `(α⇒β)` codomain.
            "HOL.Let" => {
                let Some((alpha_ty, rest)) = fun_split(use_ty) else {
                    return Ok(None);
                };
                let Some((fn_ty, _)) = fun_split(rest) else {
                    return Ok(None);
                };
                let Some((_a2, beta_ty)) = fun_split(fn_ty) else {
                    return Ok(None);
                };
                vec![alpha_ty, beta_ty]
            }
            // `α⇒β⇒Prop` — α from the first domain, β from the second.
            "HOL.NO_MATCH" => {
                let Some((alpha_ty, rest)) = fun_split(use_ty) else {
                    return Ok(None);
                };
                let Some((beta_ty, _)) = fun_split(rest) else {
                    return Ok(None);
                };
                vec![alpha_ty, beta_ty]
            }
            // Monomorphic (`bool`/`prop`-only) constants — no type args to solve.
            "HOL.induct_conj"
            | "HOL.ASSUMPTION"
            | "Code_Generator.holds"
            | "ATP.fFalse"
            | "ATP.fTrue"
            | "ATP.fNot"
            | "ATP.fconj"
            | "ATP.fdisj"
            | "ATP.fimplies" => Vec::new(),
            _ => return Ok(None),
        };
        let mut e = Expr::const_str(def);
        for ty in type_args {
            let te = self.embed_type(ty)?;
            e = Expr::app(e, te);
        }
        // `ATP.fChoice ≡ Hilbert_Choice.Eps` is a dictionary-style alias: its
        // def-const additionally binds the (opaque) `Eps` argument, supplied here
        // as the SAME shared `const:Hilbert_Choice.Eps` param a bare `Eps`
        // occurrence embeds to — so `fChoice_def α eps` δβ-reduces to that very
        // param and the `fChoice_def_raw` equation is reflexive.
        if n == "ATP.fChoice" {
            let eps_clean_ty = self.embed_type(use_ty)?;
            let eps = self.const_param("Hilbert_Choice.Eps", eps_clean_ty);
            e = Expr::app(e, eps);
        }
        Ok(Some(e))
    }

    /// Embed a non-connective application `f $ y`: the HOL `=`/`≡` spine
    /// (`(eq $ x) $ y → @Eq u α x y`) or a plain application.
    pub(crate) fn embed_app(
        &mut self,
        f: &IsaTerm,
        y: &IsaTerm,
        binders: &mut Vec<Binder>,
    ) -> Result<Expr, TranslateError> {
        if let IsaTerm::App { f: eqf, a: x } = f {
            if let IsaTerm::Const { n, t } = eqf.as_ref() {
                if n == "HOL.eq" || n == "Pure.eq" || n == "=" {
                    let alpha = match eq_operand_type(t) {
                        Some(ty) => self.embed_type(ty)?,
                        None => self.infer_type(x, binders)?,
                    };
                    let xe = self.embed_term(x, binders)?;
                    let ye = self.embed_term(y, binders)?;
                    return Ok(Expr::apps(
                        Expr::const_str_levels("Eq", vec![obj_level()]),
                        [alpha, xe, ye],
                    ));
                }
            }
        }
        let fe = self.embed_term(f, binders)?;
        let ae = self.embed_term(y, binders)?;
        Ok(Expr::app(fe, ae))
    }

    /// Best-effort embedded type of a term (used only when an `Eq` constant
    /// lacks its operand type).
    pub(crate) fn infer_type(
        &mut self,
        tm: &IsaTerm,
        binders: &[Binder],
    ) -> Result<Expr, TranslateError> {
        match tm {
            IsaTerm::Free { t, .. } | IsaTerm::Var { t, .. } | IsaTerm::Const { t, .. } => {
                self.embed_type(t)
            }
            IsaTerm::Bound { i } => term_bvar(binders, *i as usize)
                .map(|(_, ty)| ty)
                .ok_or(TranslateError::Unsupported("loose Bound type")),
            // See through identity coercions (Pure.prop / Trueprop).
            IsaTerm::App { f, a }
                if is_const(f, "Pure.prop")
                    || is_const(f, "HOL.Trueprop")
                    || is_const(f, "Trueprop") =>
            {
                self.infer_type(a, binders)
            }
            // General application `g x`: the result type is the codomain of g's
            // function type. Several HOL heads do not embed to a clean function
            // type (the result is nonetheless determined), so handle them before
            // falling back to `split_arrow`:
            //   - a fully-applied equation `eq a b`, an implication `A ⟶ B`, a
            //     universal `All/Ex/⋀ P`, or a logical connective → a `Prop`;
            //   - otherwise the codomain of the (recursively inferred) head type.
            IsaTerm::App { f, .. } => {
                if let Some(p) = self.prop_result_head(tm) {
                    return Ok(p);
                }
                let f_ty = self.infer_type(f, binders)?;
                match split_arrow(&f_ty) {
                    Some((_, cod)) => Ok(cod),
                    // The head did not embed to a function type. Rather than hard
                    // error (which fails the whole node), fall back to the head's
                    // own inferred type — a best-effort that the kernel re-checks.
                    // This keeps `infer_type` total over the shapes that arise
                    // (e.g. an `Eq`-headed partial application).
                    None => Ok(f_ty),
                }
            }
            // Lambda `λ(x:t). b` has function type `t → type(b)`. HOL function
            // types are non-dependent, so the codomain needs no de Bruijn lift.
            IsaTerm::Abs { t, b, .. } => {
                let dom = self.embed_type(t)?;
                let mut local = binders.to_vec();
                local.push(Binder {
                    kind: BKind::Term,
                    ty: dom.clone(),
                });
                let cod = self.infer_type(b, &local)?;
                Ok(Expr::arrow(dom, cod))
            }
        }
    }

    /// If `tm` is a fully-applied **proposition-producing** HOL head — a binary
    /// equation `eq a b`, an implication `A ⟶ B`, a Pure implication `A ⟹ B`, a
    /// quantifier `All/Ex/⋀ P`, or a logical connective applied to its arguments —
    /// return the embedded result type `Prop`. These heads do not embed to a
    /// clean function type, so [`Self::infer_type`]'s generic `split_arrow` path
    /// cannot see through them. Returns `None` for any other shape.
    pub(crate) fn prop_result_head(&self, tm: &IsaTerm) -> Option<Expr> {
        // Peel the application spine to its head constant and argument count.
        let mut argc = 0usize;
        let mut cur = tm;
        while let IsaTerm::App { f, .. } = cur {
            argc += 1;
            cur = f;
        }
        let IsaTerm::Const { n, .. } = cur else {
            return None;
        };
        let prop = matches!(
            (n.as_str(), argc),
            ("HOL.eq" | "Pure.eq" | "=", 2)
                | ("HOL.implies" | "Pure.imp", 2)
                | ("HOL.All" | "HOL.Ex" | "Pure.all", 1)
                | ("HOL.conj" | "HOL.disj", 2)
                | ("HOL.Not", 1)
        );
        prop.then(Expr::prop)
    }

    /// Embed the operand type `α` of an equality from the equality constant's
    /// own type (`α ⇒ α ⇒ _`); fall back to inferring it from `lhs` when the
    /// constant type is degenerate.
    pub(crate) fn embed_type_or_infer(
        &mut self,
        eq_const_ty: &IsaType,
        lhs: &IsaTerm,
        binders: &mut [Binder],
    ) -> Result<Expr, TranslateError> {
        match eq_operand_type(eq_const_ty) {
            Some(ty) => self.embed_type(ty),
            None => self.infer_type(lhs, binders),
        }
    }
}
