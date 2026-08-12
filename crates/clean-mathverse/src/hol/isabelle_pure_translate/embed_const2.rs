// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Ctx::embed_const_term2` — the second half of `embed_term`'s `Const`-arm
//! dispatch (registered instance ops / list fns / poly insts / `HOL.If` /
//! `Fun.comp`/`id` / overloaded methods) plus the generic `Const` catch-all.
//! Reached only from [`Self::embed_const_term`]. Moved verbatim from the
//! original single-file `isabelle_pure_translate` module; behaviour is
//! byte-identical (arm order and guards unchanged).

use clean_kernel::Expr;

use super::super::isabelle_pure::IsaTerm;
use super::*;

impl Ctx {
    /// Second-half `Const` dispatch for [`Self::embed_term`] (continuation of
    /// [`Self::embed_const_term`]); includes the generic `const:<n>` catch-all.
    pub(crate) fn embed_const_term2(&mut self, tm: &IsaTerm) -> Result<Expr, TranslateError> {
        match tm {
            // A **registered monomorphic instance operation** at a closed ground
            // type (`Groups.plus_class.plus : nat ⇒ nat ⇒ nat`,
            // `Groups.times_class.times : nat ⇒ nat ⇒ nat`, …). Embed to the
            // registered instance-op def-const (`isabelle.inst.<c>@<ground-type-key>`),
            // which δ-unfolds to the embedded body of the operation's `…_def` axiom
            // (a closed `rec_nat`/`rec_num` fold). This makes the recursive-arithmetic
            // `…_def` axiom reflexive AND keeps every nat/num use-site consistent (the
            // same def-const everywhere). The constant is genuinely monomorphic, so no
            // type/operation arguments are threaded — the def-const is nullary. The
            // kernel re-checks the result against the use-site type, so a wrong body
            // is rejected — never miscounted. Tried before the polymorphic method
            // arm because a ground match is the more specific embedding.
            IsaTerm::Const { n, t }
                if self.instance_unfold && is_ground_type(t) && {
                    let key = (n.clone(), isa_ground_type_key(t));
                    self.instance_op_registry.contains_key(&key)
                } =>
            {
                let key = (n.clone(), isa_ground_type_key(t));
                if let Some(info) = self.instance_op_registry.get(&key) {
                    return Ok(Expr::const_str(&info.def_name));
                }
                // Defensive fall-through (unreachable given the guard): keep the
                // theorem closed and honestly typed.
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // A **registered plain polymorphic list function** (`List.append`,
            // `List.rev`, `List.map`, …) — embed to its def-const applied to the
            // use-site element type `@isabelle.listfn.<c> T` (which δ-unfolds to the
            // registered `rec_list`-fold body specialised at `T`), so the recursive
            // list-function `…_def` axiom `c ≡ (λ…. rec_list …)` verifies reflexively
            // and every list use-site stays consistent. The element type `T` is
            // solved by matching the registered function type against this use-site's
            // instantiated type. The kernel re-checks the result against the use-site
            // type, so a wrong body is rejected — never miscounted. Gated on
            // `instance_unfold` (same escalating-pass discipline → strictly additive).
            IsaTerm::Const { n, t }
                if self.instance_unfold && self.list_fn_registry.contains_key(n) =>
            {
                if let Some(e) = self.embed_list_fn_use(n, t)? {
                    return Ok(e);
                }
                // Fall through to the opaque-param embedding if the use-site type
                // does not match the registered function type (defensive — keeps the
                // theorem closed and honestly typed; the kernel still re-checks).
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // A **registered polymorphic instance operation** (`Int.power_int`, …) —
            // embed to its def-const applied to the use-site object type and each class
            // operation (`isabelle.polyinst.<c> α extra… op₁ … opₘ`, which δ-unfolds to
            // the registered body), leaving the function's residual argument arrows for
            // the consumer's own application. So the `_def` axiom verifies reflexively
            // and every use-site stays consistent. The kernel re-checks the result, so
            // a wrong body is rejected. Gated on `instance_unfold` → strictly additive.
            //
            // **#107 superclass-conjunct spelling alignment** (`ISA_CLASS_OPERAND_ALIGN`,
            // default OFF): under the flag, a registered **locale-predicate** const
            // (`Thy.class.<c>`, e.g. `Orderings.class.preorder`) ALSO takes the
            // poly-inst def-const embedding in the `InstanceEmbed::Opaque` passes, not
            // just under `Unfold`. This is the ONLY spelling under which such an
            // operand — which a superclass locale predicate bakes into the
            // once-registered structured class-def body (poly-inst-flavored) once its
            // `class.<c>_def` is registered — reconciles with the operand the OfClass /
            // `order_class.axioms`-leg reconstruction produces; the `Opaque` opaque
            // `const:` param desyncs against it (see `zproof-eta-operand-decode.md`
            // §11). Flag OFF ⇒ the guard is the historical `instance_unfold` gate,
            // byte-identical. The kernel re-checks the result either way, so a wrong
            // body is rejected — never miscounted.
            IsaTerm::Const { n, t }
                if (self.instance_unfold
                    || (class_operand_align_enabled() && is_locale_predicate_const(n)))
                    && self.poly_inst_registry.contains_key(n) =>
            {
                // **#107 align scale guard.** The flag-added locale-predicate
                // poly-inst embedding recurses through the superclass
                // locale-predicate op-DAG: `embed_poly_inst_use` re-embeds each
                // op via `embed_element_op`, and a nested locale-predicate op
                // re-enters THIS arm, descending the class hierarchy. That
                // descent is invisible to the per-line node budget — the budget
                // is bumped once per PROOF node in `translate_proof` /
                // `translate_proof_expecting`, but the whole op-DAG of a class
                // membership embeds inside ONE node, and a class-heavy analysis
                // proof repeats it across millions of nodes, so the node budget
                // only cuts after ~45 min on a big line (`ISA_CLASS_OPERAND_ALIGN`
                // §13 scale pathology). Charge each flag-added locale-predicate
                // embed against the SAME per-line budget so the align path is
                // bounded exactly like every proof node, and a pathological line
                // fails FAST as an honest `translate-budget` reject. Gated on the
                // precise extra condition the flag adds
                // (`class_operand_align_enabled() && is_locale_predicate_const`),
                // so flag-OFF and the historical `instance_unfold` poly-inst
                // embeds are byte-identical (no bump); a no-op when no budget is
                // configured (the production default), so it is zero-cost there.
                if class_operand_align_enabled() && is_locale_predicate_const(n) {
                    if let Some(budget) = bump_translate_steps() {
                        return Err(TranslateError::BudgetExceeded(budget));
                    }
                }
                if let Some(e) = self.embed_poly_inst_use(n, t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // **G4:** a registered **method-at-constructor instance definition**
            // (`Enum.enum_class.enum @ (α⇒β) list`, `Orderings.ord_class.less_eq @
            // 'a filter ⇒ …`, …) — an overloaded method whose occurrence type
            // unifies with a registered instance shape ([`Ctx::find_method_inst`],
            // pure, so it doubles as the match guard: no registration match means
            // this arm never fires and the dispatch below — including the dict
            // method arm — continues byte-identically). Embed to the instance
            // def-const applied to the solved instantiation tvars and the
            // re-embedded class operations (`@isabelle.instk.<m>@<K> T… op…`,
            // which δ-unfolds to the registered body), so the instance `_def`
            // equation verifies reflexively and every use-site of the method at
            // that instance stays consistent. Placed BEFORE the dict method arm:
            // an instance-specific definition is the more specific embedding (the
            // dict lane's generic `method ≡ impl ops` glue carries the method at
            // its GENERIC type, which never unifies with a constructor-instance
            // shape, so the dict lane is untouched). Gated on `instance_unfold`
            // (final escalating passes → strictly additive); the kernel re-checks
            // the saturated application, so a wrong solve is rejected — never
            // miscounted.
            IsaTerm::Const { n, t }
                if self.instance_unfold
                    && is_overloaded_method_const(n)
                    && self.find_method_inst(n, t).is_some() =>
            {
                if let Some(e) = self.embed_method_inst_use(n, t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // HOL's if-then-else `HOL.If : bool ⇒ 'a ⇒ 'a ⇒ 'a` — embed to its
            // registered polymorphic def-const at the use-site element type
            // (`@isabelle.def.HOL.If.{u} T`, which δ-unfolds to the faithful
            // `ite`-via-classical-decidability body). This closes the `…_def`
            // bodies of the recursive list/option functions that branch with `if`
            // (`List.filter`, `List.find`, `List.takeWhile`/`dropWhile`,
            // `List.butlast`, `List.remove1`/`removeAll`, …) so their definitional
            // axioms verify reflexively. Gated on `instance_unfold` (same escalating
            // pass discipline → strictly additive: bare/opaque occurrences in
            // earlier passes are unchanged). The kernel re-checks the saturated
            // application, so a wrong element type is rejected — never miscounted.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "HOL.If" => {
                if let Some(e) = self.embed_hol_if(t)? {
                    return Ok(e);
                }
                // Fall through to the opaque-param embedding if the use-site type is
                // not the expected `bool ⇒ T ⇒ T ⇒ T` shape (e.g. a `dummy`-typed
                // `_def_raw` occurrence); the kernel still re-checks the result.
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // HOL's function composition `Fun.comp : ('b⇒'c)⇒('a⇒'b)⇒'a⇒'c` — embed
            // to its registered polymorphic def-const at the use-site's three solved
            // element types (`isabelle.def.Fun.comp T_a T_b T_c`, which δ-unfolds to
            // `λf g x. f (g x)`). `comp` is PERVASIVE across HOL (`foldr_def` and many
            // list/function lemmas mention `comp f g` on a RHS or as a dep), so a
            // single shared head makes `comp_def` reflexive and every consumer
            // δ-consistent. Gated on `instance_unfold` (escalating-pass discipline →
            // strictly additive). The kernel re-checks the saturated application, so a
            // wrong element type is rejected — never miscounted.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Fun.comp" => {
                if let Some(e) = self.embed_fun_comp(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // HOL's identity `Fun.id : 'a⇒'a` — embed to its registered polymorphic
            // def-const at the use-site element type (`isabelle.def.Fun.id T`, which
            // δ-unfolds to `λx. x`). Same escalating-pass discipline; `id_def` then
            // verifies reflexively and `id`-using lemmas stay δ-consistent.
            IsaTerm::Const { n, t } if self.instance_unfold && n == "Fun.id" => {
                if let Some(e) = self.embed_fun_id(t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // A **`Fun.*` combinator constant** (`fcomp`/`inj_on`/`bij_betw`/
            // `fun_upd`/`monotone_on`) — embed to its registered polymorphic
            // def-const at the use-site's solved object types
            // ([`Ctx::embed_fun_combinator`], which δβ-unfolds to the same
            // `Ball`/`image`/`If`-built body its `…_def`/`…_def_raw` RHS spells),
            // so the definitional axiom verifies reflexively and every occurrence
            // shares one defeq-unfolding head. Same escalating-pass discipline
            // (`instance_unfold` → strictly additive); the kernel re-checks the
            // saturated application, so a wrong element type is rejected — never
            // miscounted.
            IsaTerm::Const { n, t } if self.instance_unfold && fun_def_const_name(n).is_some() => {
                if let Some(e) = self.embed_fun_combinator(n, t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // A **BNF combinator constant** (`convol`/`rel_fun`/`rel_set`/`eq_onp`/
            // `vimage2p`/`Grp`/`Gr`/`csquare`/`id_bnf`) — embed to its registered
            // polymorphic def-const at the use-site's solved object types
            // ([`Ctx::embed_bnf_combinator`], which δβ-unfolds to the same
            // `∀`/`Ball`/`Bex`/`∃`/`∧`/`@Eq`/`Prod.mk`-built body its `…_def`/
            // `…_def_raw` RHS spells), so the definitional axiom verifies reflexively
            // and every occurrence shares one defeq-unfolding head. Same escalating-
            // pass discipline (`instance_unfold` → strictly additive); the kernel
            // re-checks the saturated application, so a wrong object-type solution is
            // rejected — never miscounted.
            IsaTerm::Const { n, t } if self.instance_unfold && bnf_def_const_name(n).is_some() => {
                if let Some(e) = self.embed_bnf_combinator(n, t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // An **opaque-arg BNF combinator constant** (`cinfinite`/`cfinite`/
            // `csum`/`cprod`/`cexp`/`Csum`/`pick_middlep`/`fstOp`/`sndOp`) — embed to
            // its registered def-const applied to the use-site's solved object types
            // AND the re-embedded opaque HOL constants it abstracts (`Field`/`finite`/
            // `card_of`/`Plus`/`Sigma`/`Func`/`Eps`/prod-selectors — see
            // [`Ctx::embed_bnf_opaque_combinator`]). The def-const δβ-reduces to
            // exactly the RHS embedding (the opaque args are the SAME `const:` params
            // the RHS mints), so the `_def`/`_def_raw` axiom verifies reflexively.
            // Same escalating-pass discipline (`instance_unfold` → strictly additive);
            // the kernel re-checks the saturated application, so a wrong object-type /
            // opaque supply is rejected — never miscounted.
            IsaTerm::Const { n, t }
                if self.instance_unfold && bnf_opaque_def_const_name(n).is_some() =>
            {
                if let Some(e) = self.embed_bnf_opaque_combinator(n, t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // A **`wo_rel` `The`-threaded constant** (`minim`/`supr`/`suc`) — embed to
            // its registered def-const ([`Ctx::embed_wo_the_const`]) applied to the
            // object type, the shared `Nonempty α` witness (and, for `supr`/`suc`, the
            // re-embedded `Relation.Field` argument their `Above`/`AboveS` component
            // abstracts). The def-const δ-unfolds to the epsilon-`The`-over-`isMinim`
            // body the RHS spells, so the `_def`/`_def_raw` axiom verifies reflexively.
            // Same escalating-pass discipline (`instance_unfold` → strictly additive);
            // the kernel re-checks the saturated application, so a wrong object-type /
            // witness / `Field` supply is rejected — never miscounted.
            IsaTerm::Const { n, t }
                if self.instance_unfold && wo_the_def_const_name(n).is_some() =>
            {
                if let Some(e) = self.embed_wo_the_const(n, t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // A **`The`-defined order extremum** (`Orderings.ord.Least` /
            // `Orderings.order.Greatest`) — embed to its registered def-const applied
            // to the object type and a shared `Nonempty α` parameter
            // (`@isabelle.def.<C> α hne`, which η/δ-unfolds to `λle P. THE x. P x ∧ …`).
            // So `Least/Greatest le P` shares one defeq-unfolding head with the RHS of
            // its `…_def` / `…_def_raw` equation, making that axiom reflexive. Gated on
            // `instance_unfold` (final escalating pass → strictly additive: bare /
            // earlier-pass occurrences keep the opaque `const:` param). The `Nonempty α`
            // parameter is quantified (HOL types are nonempty; clean makes it explicit).
            // Falls through to the opaque param if the type is not the expected
            // `(α⇒α⇒bool)⇒(α⇒bool)⇒α` shape; the kernel re-checks either way.
            IsaTerm::Const { n, t } if self.instance_unfold && is_order_extremum(n) => {
                if let Some(e) = self.embed_extremum_const(n, t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // A **point-free HOL logical constant** (`HOL.Uniq`/`Ex1`/`Let`/
            // `induct_forall`/`induct_equal`/`NO_MATCH`) — embed to its registered
            // polymorphic def-const at the use-site's solved object type(s)
            // ([`Ctx::embed_pointfree_const`], which δβ-unfolds to the same body the
            // constant's `…_def_raw` RHS spells), so the point-free definitional axiom
            // `C ≡ λargs. body` verifies reflexively and every occurrence shares one
            // defeq-unfolding head. Gated on `instance_unfold` (final escalating pass →
            // strictly additive: bare/earlier-pass occurrences keep the opaque param).
            // The kernel re-checks the saturated application, so a wrong element type
            // is rejected — never miscounted.
            IsaTerm::Const { n, t }
                if self.instance_unfold && pointfree_const_def_name(n).is_some() =>
            {
                if let Some(e) = self.embed_pointfree_const(n, t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // A **registered overloaded class method** (`c_class.method`) — embed to
            // its dictionary def-const application `method_def α impl op₁ … opₙ`
            // (which δ-unfolds to `impl op₁ … opₙ`), so the method's `…_dict` axiom
            // `c_class.method ≡ impl ops` verifies reflexively. The object type `α`
            // is solved by matching the registered method type against this
            // use-site's instantiated type; the impl/op constants are re-embedded at
            // that instantiation as the same global `const:<n>` params (so the
            // `…_dict` RHS, which embeds those constants identically, coincides
            // definitionally). The kernel re-checks the result against the use-site
            // type, so a wrong dictionary model is rejected — never miscounted.
            IsaTerm::Const { n, t }
                if self.method_unfold && self.method_registry.contains_key(n) =>
            {
                if let Some(e) = self.embed_method_use(n, t)? {
                    return Ok(e);
                }
                // Fall through to the opaque-param embedding if the use-site type
                // does not match the registered method type (defensive — keeps the
                // theorem closed and honestly typed; the kernel still re-checks).
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // A RAW **bool-instance** implementation constant
            // `<M>.<c>_bool_inst.<c>_bool` (`Boolean_Algebras.sup_bool_inst.sup_bool`,
            // `Orderings.bot_bool_inst.bot_bool`, …) IS Isabelle's `instance … :: bool`
            // registration of the class op at `bool`: it denotes the identical element
            // as the class op `<c>_class.<c>` at that ground type. So it embeds to the
            // SAME opaque `const:<c>_class.<c>` parameter the class op embeds to
            // ([`bool_impl_const_class_op`] rewrites the name, then the ordinary
            // `Const` dispatch re-embeds at the same type). This makes the
            // `<c>_class.<c> ≡ <c>_bool_inst.<c>_bool` registration equation genuinely
            // reflexive — both sides are the identical opaque param — so the
            // `def_axiom_body` `Eq.refl` proof the kernel re-checks is accepted (iff
            // the two truly coincide; a wrong mapping is rejected, never miscounted).
            // Ground-type analogue of the `<c>_fun_inst.<c>_fun` rewrite in
            // [`pointwise_fun_instance_op`]. Gated on `instance_unfold` (final
            // escalating pass → strictly additive: an earlier opaque pass keeps the two
            // params distinct). Placed BEFORE the function-instance arm so the bool
            // impl const is rewritten first (its type is not a `fun` arrow, so it would
            // otherwise fall through to the generic catch-all as a distinct param).
            IsaTerm::Const { n, t }
                if self.instance_unfold && bool_impl_const_class_op(n).is_some() =>
            {
                // `bool_impl_const_class_op(n)` is `Some` here (the guard matched); the
                // `if let` binds it without an `unwrap`. The rewritten class op is a
                // closed constant (it references no outer bound variable), so re-embed
                // it with a FRESH binder context — the same discipline
                // [`Ctx::embed_element_op`] uses for the element-op re-embedding on the
                // RHS of a pointwise instance def.
                if let Some(class_op) = bool_impl_const_class_op(n) {
                    return self.embed_element_op(class_op, t);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // A RAW **ground/type-constructor instance** implementation constant
            // (`Nat.inf_nat_inst.inf_nat`, `Nat.zero_nat_inst.zero_nat`,
            // `Product_Type.equal_prod_inst.equal_prod`, …) IS Isabelle's
            // `instance …` registration of the class op at that instance: it
            // denotes the identical element as the class op at the same type. So
            // it embeds through the SAME `Const` dispatch the class op uses
            // ([`ground_impl_const_class_op`] rewrites the name, then the ordinary
            // dispatch re-embeds at the same type — the direct `0::nat ↦ Nat.zero`
            // mapping, the `inf@nat ↦ min` / `sup@nat ↦ max` collapse, the
            // `equal@sum/prod ↦ @Eq` encoding, or the shared opaque
            // `const:<c>_class.<c>` param). This makes the
            // `<c>_class.<c> ≡ <c>_<T>_inst.<c>_<T>` registration equation
            // genuinely reflexive, so its `…_inst.…_def` axiom (and the composed
            // `…_def_raw` consumers) verify by a kernel-re-checked `Eq.refl` —
            // a wrong mapping is rejected, never miscounted. Non-`bool` analogue
            // of the arm above; same `instance_unfold` gating (final escalating
            // pass → strictly additive: an earlier opaque pass keeps the two
            // params distinct).
            IsaTerm::Const { n, t }
                if self.instance_unfold && ground_impl_const_class_op(n).is_some() =>
            {
                // The guard matched, so the mapping is `Some`; the `if let` binds it
                // without an `unwrap`. Re-embed the class op with a FRESH binder
                // context (the rewritten constant is closed), mirroring the bool arm.
                if let Some(class_op) = ground_impl_const_class_op(n) {
                    return self.embed_element_op(class_op, t);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // An overloaded lattice/order **class operation at a FUNCTION instance**
            // (`sup`/`inf`/`minus`/`uminus`/`bot`/`top`/`less_eq` on `'a ⇒ 'b`) —
            // embed to the faithful **pointwise-lift** lambda
            // [`pointwise_fun_instance_op`] (`(f ⊓ g) = λx. f x ⊓ g x`, …), whose
            // inner element-instance operation is the SAME abstract `const:<op>`
            // parameter the RHS embeds it to. This makes the `…_fun_inst.…_fun_def`
            // pointwise definitional equation genuinely reflexive — the LHS
            // `op@fun args` β-reduces to the embedded RHS, and the kernel accepts the
            // `Eq.refl` proof iff the two coincide (faithful, not a `B=B` tautology).
            // Gated on `instance_unfold` (final escalating pass → strictly additive:
            // earlier-pass occurrences keep the opaque param). Placed before the
            // generic catch-all so it takes precedence for the function instance; the
            // element/ground/set instances (operand not a `fun` arrow) fall through.
            IsaTerm::Const { n, t } if self.instance_unfold => {
                if let Some(e) = pointwise_fun_instance_op(self, n, t)? {
                    return Ok(e);
                }
                if let Some(e) = set_op_encoding(self, n, t)? {
                    return Ok(e);
                }
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            IsaTerm::Const { n, t } => {
                // Bare (un-applied) HOL set / complete-lattice **operations** under
                // the `'a set = 'a → Prop` model embed to the faithful predicate
                // lambda [`set_op_encoding`] (β-η-equal to the operation's own HOL
                // `…_def` RHS), so the definitional axiom (`Ball_def`, `Bex_def`,
                // `image_def`, `Pow_def`, …) becomes genuinely reflexive — `op args`
                // β-reduces to exactly the embedded RHS, and the kernel accepts the
                // `Eq.refl` proof iff the two coincide (faithful, not a tautology).
                // Applied occurrences reach here via `embed_app`'s recursion on the
                // application head, then the kernel β-reduces the saturated lambda.
                if let Some(e) = set_op_encoding(self, n, t)? {
                    return Ok(e);
                }
                // Otherwise abstract the constant as a term parameter keyed by name
                // so the theorem stays closed and honestly typed.
                let ty = self.embed_type(t)?;
                Ok(self.const_param(n, ty))
            }
            // Defensive: only `Const`-headed terms reach here (via
            // `embed_const_term`); other shapes are handled in `embed_term`.
            _ => Err(TranslateError::Unsupported(
                "embed_const_term2: non-const term",
            )),
        }
    }
}
