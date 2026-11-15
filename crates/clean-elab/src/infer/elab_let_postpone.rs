// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Postponing an unannotated `let` value that is a leading-dot constructor
//! (G36, ledger class (106)).
//!
//! `let m := .nullPtr; some m` at `Option V`: the value has no expected type,
//! so `.nullPtr` names no constructor yet. Lean's `elabLetDeclAux` gives the
//! binder a fresh type metavariable, `elabDotIdent` POSTPONES on it
//! (`tryPostponeIfNoneOrMVar`), the body `some m` solves the type against
//! `Option V`, and `synthesizeSyntheticMVars` resumes `.nullPtr` against `V`.
//! The same holds when the dot sits in a branch: `if c then .nullPtr else
//! .ptr a` is an `ite` whose shared type is the open metavariable.
//!
//! Clean postpones the whole value, and only after the eager elaboration (the
//! old path, unchanged) FAILED on a value whose result position is a
//! leading-dot constructor ([`ElabCtx::let_value_postponable`]): the binder
//! gets `?T : Sort ?u` and the value the placeholder `?v : ?T`, the body is
//! elaborated, and the value is then elaborated against the instantiated
//! `?T`, outside the binder. If the body or the resumed value fails, the
//! eager attempt's error is reported, exactly as before postponement existed.
//! The resulting `let` is kernel-checked like any other.

use super::*;

impl ElabCtx<'_> {
    /// Is a leading-dot constructor (`.c`, `.c args`) in a RESULT position of
    /// `val` — the value itself, through parentheses, or an `if` branch?
    /// Those are the shapes whose meaning Lean reads off the expected type and
    /// postpones without one.
    pub(super) fn let_value_postponable(val: &SurfaceExpr) -> bool {
        match val {
            SurfaceExpr::Ident(_, name) => name.is_relative_constructor(),
            SurfaceExpr::Paren(_, inner) => Self::let_value_postponable(inner),
            SurfaceExpr::App(_, func, _) => {
                matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n.is_relative_constructor())
            }
            SurfaceExpr::If(_, _, then_br, else_br)
            | SurfaceExpr::IfDecidable(_, _, _, then_br, else_br) => {
                Self::let_value_postponable(then_br) || Self::let_value_postponable(else_br)
            }
            _ => false,
        }
    }

    /// The binder type `?T : Sort ?u` and value placeholder `?v : ?T` of a
    /// postponed `let` value (Lean's `mkFreshTypeMVar` for the omitted type).
    pub(super) fn postponed_let_value_placeholder(&mut self) -> (Expr, Expr) {
        let sort = Expr::sort(self.fresh_universe_param());
        let ty = self.fresh_meta(sort);
        let value = self.fresh_meta(ty.clone());
        (ty, value)
    }

    /// Elaborate the postponed `val` against its binder type as the body left
    /// it, and solve the placeholder with it. Any failure reports `original`
    /// (the eager attempt's error). Returns the instantiated `(type, value)`.
    pub(super) fn resume_postponed_let_value(
        &mut self,
        val: &SurfaceExpr,
        ty: &Expr,
        placeholder: &Expr,
        original: ElabError,
    ) -> Result<(Expr, Expr), ElabError> {
        let expected = self.metas.instantiate(ty);
        // The resumed value is elaborated as before numerals could wait: its
        // numerals take the type the body left, or `Nat` at once.
        let resumed = self.with_eager_numerals(|this| {
            this.elaborate_with_expected_type(val, Some(expected.clone()))
        });
        let Ok(value) = resumed else {
            return Err(original);
        };
        let Ok(value_ty) = self.infer_type(&value) else {
            return Err(original);
        };
        let value_ty = self.metas.instantiate(&value_ty);
        if !self.try_unify(&value_ty, &expected) {
            return Err(original);
        }
        let assigned = match placeholder.kind() {
            ExprKind::FVar(fvar) => MetaState::from_fvar(*fvar).is_some_and(|m| {
                self.metas.get_assignment(m).is_none() && self.metas.assign(m, value.clone())
            }),
            _ => false,
        };
        // The body may already have solved the placeholder (by unification
        // through the `let` value); the elaborated value must then agree.
        if !assigned {
            let current = self.metas.instantiate(placeholder);
            if !self.try_unify(&current, &value) {
                return Err(original);
            }
        }
        let ty = self.metas.instantiate_levels(&self.metas.instantiate(ty));
        let value = self
            .metas
            .instantiate_levels(&self.metas.instantiate(placeholder));
        Ok((ty, value))
    }
}

/// `@[default_instance 100] instOfNatNat`'s priority: the numerals' default
/// tier (`Init/Prelude.lean`).
const INST_OF_NAT_NAT_DEFAULT_PRIORITY: u32 = 100;

/// When an unannotated `let` value is elaborated relative to its body
/// (`ElabCtx::elab_let_binding_ordered`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LetValueOrder {
    /// Value first, every numeral defaulted at once (Clean's historical order).
    Eager,
    /// The whole value after the body (a bare numeral `let`, R157).
    AfterBody,
    /// Value first, as in Lean, but a numeral whose carrier is still open
    /// waits for the body: Lean's `OfNat ?α n` stays pending until the term
    /// pins `?α` or defaulting makes it `Nat`.
    NumeralsWait,
}

impl ElabCtx<'_> {
    /// Does a `let` with this binder and value hold a numeral whose carrier
    /// Lean would leave open for the body? The binder is unannotated or `_`,
    /// and a literal sits in the value under applications, parentheses,
    /// ascriptions, projections, a `fun`'s body and an `if`'s branches (`id
    /// 5`, `max 5 3`, `(5, 0)`, `[5]`, `some 5`, `k + 1`, `(5 : _)`, `fun x
    /// => x + 1`, `if c then 5 else 6`, `let j := 5; j + 0`). Literals in
    /// `match`es, `do` blocks and the like are not looked for: those values
    /// keep the eager order.
    pub(super) fn let_value_numerals_may_wait(binder: &SurfaceBinder, val: &SurfaceExpr) -> bool {
        let open_binder = match binder.ty.as_deref() {
            None | Some(SurfaceExpr::Hole(_)) => true,
            Some(_) => false,
        };
        open_binder && Self::surface_value_holds_numeral(val) == Some(true)
    }

    /// `Some(true)` when a numeral sits in `val` (see
    /// [`Self::let_value_numerals_may_wait`]), `None` when a power `a ^ b`
    /// does: Lean settles its operands through the `HPow`/`Pow`/`OfNat`
    /// default instances together (`let k := 2 ^ 3; (k : Int)` asks for
    /// `HPow Nat Nat Int` and fails), which waiting numerals do not model.
    /// [`Self::let_value_numerals_may_wait`], or a `fun` value in a file with
    /// a user `@[default_instance]`: its body's goals wait for the `let`'s
    /// body before a default applies (`let f := fun k => Tag.tag k; f (5 :
    /// Nat)` is `Tag Nat` in Lean even with a default `Tag Int`).
    pub(super) fn let_value_may_wait(&self, binder: &SurfaceBinder, val: &SurfaceExpr) -> bool {
        Self::let_value_numerals_may_wait(binder, val)
            || (binder.ty.is_none()
                && !self.default_instances.is_empty()
                && matches!(Self::unwrap_surface_parens(val), SurfaceExpr::Lambda(..)))
    }

    /// [`Self::surface_value_holds_numeral`], for a field-notation receiver
    /// (`elab_proj_waiting.rs`).
    pub(super) fn surface_value_holds_numeral_pub(val: &SurfaceExpr) -> Option<bool> {
        Self::surface_value_holds_numeral(val)
    }

    fn surface_value_holds_numeral(val: &SurfaceExpr) -> Option<bool> {
        match val {
            SurfaceExpr::Lit(_, SurfaceLit::Nat(_) | SurfaceLit::BigNat(_)) => Some(true),
            SurfaceExpr::Paren(_, inner)
            | SurfaceExpr::Explicit(_, inner)
            | SurfaceExpr::NamedArg(_, _, inner)
            | SurfaceExpr::Proj(_, inner, _)
            | SurfaceExpr::Ascription(_, inner, _) => Self::surface_value_holds_numeral(inner),
            // `let f := fun x => x + 5`: the body's numeral waits like any
            // other (Lean: `f : ?α → ?α` until the body pins `?α`).
            SurfaceExpr::Lambda(_, _, body) => Self::surface_value_holds_numeral(body),
            // `let k := if c then 5 else 6`: the branches share the open
            // carrier (the condition is not looked into).
            SurfaceExpr::If(_, _, then_br, else_br)
            | SurfaceExpr::IfDecidable(_, _, _, then_br, else_br) => Some(
                Self::surface_value_holds_numeral(then_br)?
                    | Self::surface_value_holds_numeral(else_br)?,
            ),
            // `let k := (let j := 5; j + 0)`: the nested `let` joins this
            // one's scope, so its numerals wait for the outer body too.
            SurfaceExpr::Let(_, _, inner_val, inner_body)
            | SurfaceExpr::Have(_, _, inner_val, inner_body) => Some(
                Self::surface_value_holds_numeral(inner_val)?
                    | Self::surface_value_holds_numeral(inner_body)?,
            ),
            SurfaceExpr::App(_, func, args) => {
                if matches!(func.as_ref(), SurfaceExpr::Ident(_, op) if op.to_string() == "HPow.hPow")
                {
                    return None;
                }
                let mut holds = Self::surface_value_holds_numeral(func)?;
                for arg in args {
                    holds |= Self::surface_value_holds_numeral(&arg.expr)?;
                }
                Some(holds)
            }
            _ => Some(false),
        }
    }

    /// Run the elaboration of a `let` that postpones numerals (its value and
    /// body). Only the outermost such scope drains them, after everything in
    /// it, so a nested one leaves its numerals to the rest of the enclosing
    /// body; the drained term is instantiated.
    pub(super) fn with_postponing_let_scope(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<Expr, ElabError>,
    ) -> Result<Expr, ElabError> {
        let start = self.metas.postponed_numeral_count();
        if self.postponing_let_depth == 0 {
            self.postponing_scope_start = start;
        }
        self.postponing_let_depth += 1;
        // The whole scope (value and body): Lean leaves every numeral whose
        // carrier is open pending until defaulting, so `let k := 5; Tag.tag
        // (k - 7) + Tag.tag (k : Int)` has `k - 7 : Int`.
        self.numeral_postpone_depth += 1;
        let result = f(self);
        self.numeral_postpone_depth -= 1;
        self.postponing_let_depth -= 1;
        let term = result?;
        if self.postponing_let_depth > 0 {
            return Ok(term);
        }
        self.apply_deferred_user_defaults();
        self.drain_postponed_numerals(start)?;
        // A queued goal over a local the scope has already closed (`Decidable
        // (i = 2)` in a `for` body whose collection waits) would be solved
        // with that local escaping its binder: the eager order, which solves
        // it in place, is taken instead.
        if self.postponed_goal_mentions_closed_local() {
            self.redex_binder_escaped = true;
            return Err(ElabError::CannotInfer);
        }
        // The operator goals the numerals' carriers now ground (`HMul Nat
        // Nat ?γ`) collapse and resolve as the eager order had them at once
        // (Lean's `instHMul`-style default instances, above the numerals').
        self.retry_postponed_open_carrier_instances();
        self.resolve_ground_instance_args(&term)?;
        Ok(self
            .metas
            .instantiate_levels(&self.metas.instantiate(&term)))
    }

    /// The carriers (with every metavariable linked to them) of the numerals
    /// waiting in the current postponing scope whose carrier is still open,
    /// taken before an application is elaborated: what Lean would still see
    /// as an unknown type when it synthesizes that application's instances
    /// (`settle_at_open_out_param_result`). Empty outside a scope.
    pub(super) fn open_waiting_carriers(&self) -> std::collections::HashSet<MetaId> {
        let mut open = std::collections::HashSet::new();
        if self.postponing_let_depth == 0 {
            return open;
        }
        for (id, _) in self
            .metas
            .postponed_numerals_since(self.postponing_scope_start)
        {
            if self.metas.is_assigned(id) {
                continue;
            }
            let Some(var) = self.metas.get(id) else {
                continue;
            };
            let carrier = var.ty.clone();
            if instance::bare_unassigned_meta(&self.metas, &self.metas.instantiate(&carrier))
                .is_none()
            {
                continue;
            }
            open.extend(self.meta_link_chain(&carrier));
        }
        // A bare numeral `let` whose value waits past its body (`AfterBody`)
        // is a waiting numeral too, at its binder type.
        for ty in &self.open_numeral_let_types {
            if instance::bare_unassigned_meta(&self.metas, &self.metas.instantiate(ty)).is_some() {
                open.extend(self.meta_link_chain(ty));
            }
        }
        open
    }

    /// Lean's result-is-outParam support (`Elab/App.lean`, `ElabAppArgs`'s
    /// `finalize`): an application written without `@` whose head's result
    /// type is an implicit binder that an instance binder's class takes as an
    /// `outParam` (`HAdd.hAdd 2 3 : ?γ`, `getElem! xs 0 : ?elem`), and whose
    /// result is still that open metavariable once the application's
    /// instances were tried, runs `synthesizeSyntheticMVarsUsingDefault` on
    /// the spot: every pending numeral of the term defaults then (`let k :=
    /// 5; Tag.tag (k - 7) + xs[0]! + Tag.tag (k : Int)` has `k : Nat`, 106).
    /// The operator notations Lean elaborates with `binop%`/`rightact%`/
    /// `unop%` (`a + b`, `a ^ b`, `-a`) build their application without
    /// `elabAppArgs` and do not settle; their compiler-authored heads are
    /// told apart from a user's `HAdd.hAdd` by
    /// [`SurfaceName::is_global_reference`]. Inside a postponing scope this
    /// applies the scope's deferred user defaults and defaults its waiting
    /// numerals (`settle_postponed_numerals_now`); anything the drain cannot
    /// settle fails the scope, which then keeps the eager order.
    /// `open_before` is [`Self::open_waiting_carriers`] before the
    /// application.
    pub(super) fn settle_at_open_out_param_result(
        &mut self,
        func: &SurfaceExpr,
        surface_args: &[SurfaceArg],
        term: &Expr,
        open_before: &std::collections::HashSet<MetaId>,
    ) -> Result<(), ElabError> {
        if self.postponing_let_depth == 0 || Self::is_lean_binop_notation_head(func) {
            return Ok(());
        }
        if !self.out_param_result_stuck(surface_args, term, open_before) {
            return Ok(());
        }
        // An operator tree's leaf probe watches this count
        // (`elab_binop_leaf.rs`, `binop_tree_plan`).
        self.lean_default_points += 1;
        self.settle_postponed_numerals_now()
    }

    /// Lean's `synthesizeSyntheticMVarsUsingDefault` inside a postponing
    /// scope: the deferred user defaults above the numerals' tier, then the
    /// scope's waiting numerals' `Nat` default, then the operator goals that
    /// made ground. Numerals elaborated after this keep waiting.
    fn settle_postponed_numerals_now(&mut self) -> Result<(), ElabError> {
        // Inside a `binrel%` relation only what was written inside it is
        // pending to Lean (`settle_floor`); the scope's own deferred user
        // defaults and earlier numerals are not touched.
        if let Some(floor) = self.settle_floor {
            let start = floor.max(self.postponing_scope_start);
            self.drain_postponed_numerals(start)?;
            self.retry_postponed_open_carrier_instances();
            return Ok(());
        }
        // A bare numeral `let` whose whole value waits past its body (R157's
        // `AfterBody`) is a numeral Lean would default here too, which that
        // order cannot do: it fails at once (that order runs only as a
        // transaction), and the next order (`NumeralsWait`) settles it.
        let after_body_open = self.open_numeral_let_types.iter().any(|ty| {
            let ty = self.metas.instantiate(ty);
            instance::bare_unassigned_meta(&self.metas, &ty).is_some()
        });
        if after_body_open {
            return Err(ElabError::CannotInfer);
        }
        self.apply_deferred_user_defaults();
        self.drain_postponed_numerals(self.postponing_scope_start)?;
        self.retry_postponed_open_carrier_instances();
        Ok(())
    }

    /// The `BEq.beq` head's span when `func args` is the parser's `a != b`
    /// (`Bool.not (BEq.beq a b)`, both compiler-authored heads at the
    /// operator's span); a written `!(a == b)` has two different spans.
    pub(super) fn bne_desugaring_beq_head(
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Option<clean_parser::Span> {
        let SurfaceExpr::Ident(not_span, not_name) = func else {
            return None;
        };
        if !not_name.is_global_reference() || not_name.name().to_string() != "Bool.not" {
            return None;
        }
        let [arg] = args else {
            return None;
        };
        let SurfaceExpr::App(_, inner, _) = &arg.expr else {
            return None;
        };
        match inner.as_ref() {
            SurfaceExpr::Ident(beq_span, beq_name)
                if beq_name.is_global_reference()
                    && beq_name.name().to_string() == "BEq.beq"
                    && beq_span == not_span =>
            {
                Some(*beq_span)
            }
            _ => None,
        }
    }

    /// Whether `func` is the compiler-authored head of a relation Lean 4.8.0
    /// elaborates with `binrel%` or `binrel_no_prop%` (`Init/Notation.lean`:
    /// `≤`, `<`, `>`, `≥`, `=`, `==`).
    pub(super) fn is_lean_binrel_notation_head(func: &SurfaceExpr) -> bool {
        const BINREL_HEADS: &[&str] = &["LE.le", "LT.lt", "GT.gt", "GE.ge", "Eq", "BEq.beq"];
        match Self::unwrap_surface_parens(func) {
            SurfaceExpr::Ident(_, name) if name.is_global_reference() => {
                let spelled = name.name().to_string();
                BINREL_HEADS.iter().any(|head| *head == spelled)
            }
            _ => false,
        }
    }

    /// Whether `func` is the compiler-authored head of an operator notation
    /// Lean 4.8.0 elaborates with `binop%`, `rightact%` or `unop%`
    /// (`Init/Notation.lean`); `<<<`, `>>>` and the like are plain notations
    /// and go through `elabAppArgs`.
    pub(super) fn is_lean_binop_notation_head(func: &SurfaceExpr) -> bool {
        const BINOP_HEADS: &[&str] = &[
            "HOr.hOr",
            "HXor.hXor",
            "HAnd.hAnd",
            "HAdd.hAdd",
            "HSub.hSub",
            "HMul.hMul",
            "HDiv.hDiv",
            "HMod.hMod",
            "HPow.hPow",
            "HAppend.hAppend",
            "Neg.neg",
        ];
        match Self::unwrap_surface_parens(func) {
            SurfaceExpr::Ident(_, name) if name.is_global_reference() => {
                let spelled = name.name().to_string();
                BINOP_HEADS.iter().any(|head| *head == spelled)
            }
            _ => false,
        }
    }

    /// The test of [`Self::settle_at_open_out_param_result`] on the
    /// elaborated application `term`: its head constant's type ends in a
    /// bound variable that names an implicit binder `j`, a later
    /// instance-implicit binder's class takes binder `j` at an `outParam`
    /// position, and the application is full (one argument per binder).
    /// Lean defaults when argument `j` is still open after the application's
    /// instances were tried, which is when that instance was stuck on an
    /// input type it did not know yet. Clean's instance search may have
    /// answered such a goal before the explicit arguments were elaborated (it
    /// collapses `HAdd Nat ?β ?γ` to `instHAdd`, `GetElem (Array Nat) ?idx
    /// ..` to the `Nat` index), so an input also counts as unknown when an
    /// explicit argument typed by it is what Lean would have left open: a
    /// bare numeral with no earlier argument of that type (`HAdd.hAdd (1 :
    /// Nat) 1`, `xs[0]!`), or a waiting numeral or a local whose type is the
    /// carrier of a numeral that was waiting at an open carrier before the
    /// application (`open_before`).
    fn out_param_result_stuck(
        &self,
        surface_args: &[SurfaceArg],
        term: &Expr,
        open_before: &std::collections::HashSet<MetaId>,
    ) -> bool {
        let term = self.metas.instantiate(term);
        let ExprKind::Const(name, _) = term.get_app_fn().kind() else {
            return false;
        };
        let Some(info) = self.env.get_const(name) else {
            return false;
        };
        let mut binders: Vec<(BinderInfo, Expr)> = Vec::new();
        let mut ty = info.type_.clone();
        while let ExprKind::Pi(data, domain, body) = ty.kind() {
            binders.push((data.info, domain.as_ref().clone()));
            let next = body.as_ref().clone();
            ty = next;
        }
        let ExprKind::BVar(index) = ty.kind() else {
            return false;
        };
        let count = binders.len();
        let Some(result_binder) = count.checked_sub(1 + *index as usize) else {
            return false;
        };
        if binders[result_binder].0 != BinderInfo::Implicit {
            return false;
        }
        let args = term.get_app_args();
        if args.len() != count {
            return false;
        }
        // The binder a bound variable at binder `at` names.
        let named_binder = |at: usize, arg: &Expr| -> Option<usize> {
            match arg.kind() {
                ExprKind::BVar(k) => at.checked_sub(1 + *k as usize),
                _ => None,
            }
        };
        let mut out_param_instance = false;
        let mut inputs: Vec<usize> = Vec::new();
        for (at, (info, domain)) in binders.iter().enumerate().skip(result_binder + 1) {
            if *info != BinderInfo::InstImplicit {
                continue;
            }
            let ExprKind::Const(class, _) = domain.get_app_fn().kind() else {
                continue;
            };
            let out_params = self
                .instances
                .get_class(class)
                .map(|c| c.out_params.clone())
                .or_else(|| self.env.get_class_info(class).map(|c| c.out_params.clone()))
                .unwrap_or_default();
            let class_args = domain.get_app_args();
            let takes_result = out_params.iter().any(|position| {
                class_args
                    .get(*position)
                    .is_some_and(|arg| named_binder(at, arg) == Some(result_binder))
            });
            if !takes_result {
                continue;
            }
            out_param_instance = true;
            for (position, arg) in class_args.iter().enumerate() {
                if !out_params.contains(&position) {
                    inputs.extend(named_binder(at, arg));
                }
            }
        }
        if !out_param_instance {
            return false;
        }
        if instance::bare_unassigned_meta(&self.metas, &self.metas.instantiate(args[result_binder]))
            .is_some()
        {
            return true;
        }
        // The explicit binders in order, each with the input binder its type
        // is (if it is one); positional surface arguments map onto them only
        // when every argument is positional and there is one per binder.
        let explicit: Vec<(usize, Option<usize>)> = binders
            .iter()
            .enumerate()
            .filter(|(_, (info, _))| *info == BinderInfo::Default)
            .map(|(at, (_, domain))| (at, named_binder(at, domain).filter(|b| inputs.contains(b))))
            .collect();
        let surface_maps = surface_args.len() == explicit.len()
            && surface_args.iter().all(|arg| arg.name.is_none());
        let mut typed_inputs: Vec<usize> = Vec::new();
        for (slot, (at, input)) in explicit.iter().enumerate() {
            let Some(input) = *input else {
                continue;
            };
            let bare_literal = surface_maps
                && matches!(
                    Self::unwrap_surface_parens(&surface_args[slot].expr),
                    SurfaceExpr::Lit(_, SurfaceLit::Nat(_) | SurfaceLit::BigNat(_))
                );
            if bare_literal && !typed_inputs.contains(&input) {
                return true;
            }
            if !open_before.is_empty() && self.arg_type_was_open(args[*at], open_before) {
                return true;
            }
            typed_inputs.push(input);
        }
        false
    }

    /// Whether the elaborated argument `arg` is a waiting numeral or a local
    /// whose type is linked to one of `open_before`'s carriers.
    fn arg_type_was_open(
        &self,
        arg: &Expr,
        open_before: &std::collections::HashSet<MetaId>,
    ) -> bool {
        let linked = |ty: &Expr| {
            self.meta_link_chain(ty)
                .iter()
                .any(|id| open_before.contains(id))
        };
        match self.metas.instantiate(arg).kind() {
            ExprKind::FVar(fvar) => match MetaState::from_fvar(*fvar) {
                Some(id) => self.metas.get(id).is_some_and(|var| linked(&var.ty)),
                None => self
                    .locals
                    .iter()
                    .rev()
                    .find(|(_, local, _)| local == fvar)
                    .is_some_and(|(_, _, ty)| linked(ty)),
            },
            _ => false,
        }
    }

    /// The metavariables `e` names through metavariable-to-metavariable
    /// assignments (`?a := ?b := ?c := Nat` gives `[?a, ?b, ?c]`).
    fn meta_link_chain(&self, e: &Expr) -> Vec<MetaId> {
        let mut chain = Vec::new();
        let mut current = e.clone();
        while let ExprKind::FVar(fvar) = current.kind() {
            let Some(id) = MetaState::from_fvar(*fvar) else {
                break;
            };
            if chain.contains(&id) {
                break;
            }
            chain.push(id);
            match self.metas.get_assignment(id) {
                Some(next) => {
                    let next = next.clone();
                    current = next;
                }
                None => break,
            }
        }
        chain
    }

    /// Lean checks a `let`/`have` value against its annotation where it
    /// stands (`elabTermEnsuringType`), and a numeral still waiting there is
    /// `OfNat.ofNat ?α n ?inst` with its instance pending, which no
    /// definitional unfolding computes through: `let k := 5; have _h : k - 7
    /// = -2 := rfl; Tag.tag (k : Int)` is refused by Lean 4.8.0. Clean leaves
    /// a value whose type does not unify with its annotation to the kernel's
    /// check of the finished term, where the numerals have long been settled
    /// (`k - 7 = -2` at `Int`, accepted). So in a postponing scope, while a
    /// numeral's value still waits, such a value REFUSES the declaration, as
    /// a ground goal with no instance does (`lean_order_ground_refusal`): the
    /// eager order would only retype the term (`k : Nat` makes `have _h : k +
    /// 1 = 6 := rfl` hold, which Lean refuses too). Lean postpones a few such
    /// checks and passes them later (`have _h : k = 2 + 3 := rfl`); those are
    /// refused here, a true statement refused rather than a false one
    /// accepted.
    pub(super) fn check_annotated_value_in_scope(
        &mut self,
        value: &Expr,
        annotation: &Expr,
    ) -> Result<(), ElabError> {
        if self.postponing_let_depth == 0 || !self.postponed_numeral_value_pending() {
            return Ok(());
        }
        let value_ty = self.infer_type(value)?;
        if self.try_unify(&value_ty, annotation) {
            return Ok(());
        }
        let err = ElabError::TypeMismatch {
            expected: crate::error_render::term(&self.metas.instantiate(annotation)),
            actual: crate::error_render::term(&self.metas.instantiate(&value_ty)),
        };
        self.lean_order_ground_refusal = Some(err.clone());
        Err(err)
    }

    /// Whether a numeral postponed in the current scope has no value yet
    /// (whatever its carrier).
    fn postponed_numeral_value_pending(&self) -> bool {
        self.metas
            .postponed_numerals_since(self.postponing_scope_start)
            .iter()
            .any(|(id, _)| !self.metas.is_assigned(*id))
    }

    /// Lean's default stage before the numerals': the goals a user
    /// `@[default_instance]` would have answered at once are re-resolved now,
    /// with B99 answering. (A user default's priority, `default` unless
    /// written, is above `instOfNatNat`'s 100, so in Lean it applies first:
    /// with a default `Tag Int`, `let k := 5; Tag.tag k` is 105.) The answers
    /// are the alternative's own, so they are not counted as early ones for
    /// `lean_order_attempt`'s watch.
    pub(super) fn apply_deferred_user_defaults(&mut self) {
        if self.deferred_user_default_goals == 0 {
            return;
        }
        let answers = self.user_default_instance_answers;
        let defer = std::mem::take(&mut self.defer_user_defaults);
        self.user_default_priority_floor = Some(INST_OF_NAT_NAT_DEFAULT_PRIORITY);
        self.retry_postponed_open_carrier_instances();
        self.user_default_priority_floor = None;
        self.defer_user_defaults = defer;
        self.user_default_instance_answers = answers;
    }

    /// Resolve every instance argument of `term` that the defaulted numerals
    /// made ground (`Tag ?α` once `?α := Int`, `BEq ?α` for `x == 3` over a
    /// waiting `for` collection). Such a goal's answer is determined, so it
    /// is taken now rather than at the declaration's drain: in the eager
    /// order its carrier was already known where it was met and it was
    /// resolved on the spot, and some call sites neither resolve nor queue an
    /// open goal. One with no instance refuses (`lean_order_ground_refusal`):
    /// Lean's typing needs an instance that does not exist (`[5].head! :
    /// Int` asks for `Inhabited Int`, which the prelude may lack), and the
    /// eager order would only retype the term. Goals still open stay open.
    fn resolve_ground_instance_args(&mut self, term: &Expr) -> Result<(), ElabError> {
        let term = self.metas.instantiate(term);
        let mut metas: Vec<FVarId> = self.collect_meta_fvars(&term).into_iter().collect();
        metas.sort_by_key(|fvar| fvar.as_u64());
        for fvar in metas {
            let Some(meta_id) = MetaState::from_fvar(fvar) else {
                continue;
            };
            if self.metas.is_assigned(meta_id) {
                continue;
            }
            let Some(var) = self.metas.get(meta_id) else {
                continue;
            };
            if var.span.is_some() {
                continue;
            }
            let goal = self.metas.instantiate(&var.ty);
            let is_class_goal = crate::instances::extract_class_app(&goal)
                .is_some_and(|(class, _)| self.instances.is_class(&class));
            if !is_class_goal || self.has_metavars(&goal) {
                continue;
            }
            // A goal over a local the scope has already closed (a `for`
            // body's loop variable, `Decidable (i < 3)`) cannot be resolved
            // out here; the eager order resolves it in place, so that order
            // is taken instead (no refusal).
            if self.mentions_closed_local(&goal) {
                return Err(ElabError::CannotInfer);
            }
            let goal_whnf = self.whnf(&goal);
            let solved = self
                .resolve_instance(&goal_whnf)
                .is_some_and(|inst| self.metas.assign(meta_id, inst));
            if !solved {
                let err = ElabError::FailedToSynthesizeInstance {
                    goal: crate::error_render::term(&goal),
                    detail: self.instance_failure_detail(&goal),
                };
                self.lean_order_ground_refusal = Some(err.clone());
                return Err(err);
            }
        }
        Ok(())
    }

    /// Whether an unsolved queued instance goal mentions a closed local.
    fn postponed_goal_mentions_closed_local(&self) -> bool {
        self.postponed_open_carrier_instances
            .iter()
            .any(|(meta_arg, goal)| {
                bare_meta_unassigned(&self.metas, meta_arg)
                    && self.mentions_closed_local(&self.metas.instantiate(goal))
            })
    }

    /// Whether `e` mentions a local (not a metavariable) that is no longer in
    /// the local context.
    fn mentions_closed_local(&self, e: &Expr) -> bool {
        match e.kind() {
            ExprKind::FVar(fvar) => {
                MetaState::from_fvar(*fvar).is_none()
                    && !self.locals.iter().any(|(_, local, _)| local == fvar)
            }
            ExprKind::App(f, a) => self.mentions_closed_local(f) || self.mentions_closed_local(a),
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                self.mentions_closed_local(t) || self.mentions_closed_local(b)
            }
            ExprKind::Let(_, t, v, b, _) => {
                self.mentions_closed_local(t)
                    || self.mentions_closed_local(v)
                    || self.mentions_closed_local(b)
            }
            ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => self.mentions_closed_local(x),
            _ => false,
        }
    }

    /// A `let`'s Lean-order alternative (`lean_order_attempt`): `Ok(Some)` is
    /// its term, `Ok(None)` sends the caller to the eager order, and `Err` is
    /// the refusal of a ground instance goal Lean's typing needs
    /// (`lean_order_ground_refusal`), as for a β-redex in Lean's order.
    pub(super) fn lean_order_let_attempt(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<Expr, ElabError>,
    ) -> Result<Option<Expr>, ElabError> {
        self.lean_order_ground_refusal = None;
        match self.lean_order_attempt(f) {
            Ok(term) => Ok(Some(term)),
            Err(_) => self.lean_order_ground_refusal.take().map_or(Ok(None), Err),
        }
    }

    /// Run `f` with numerals defaulting at once: a `let rec` header, a
    /// tactic block or a `calc` (Lean settles pending numerals before a `let
    /// rec` header and runs tactic blocks after defaulting; Clean elaborates
    /// both in place, so its numerals take the eager order there).
    pub(super) fn with_eager_numerals<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let saved = std::mem::take(&mut self.numeral_postpone_depth);
        let result = f(self);
        self.numeral_postpone_depth = saved;
        result
    }

    /// Whether a numeral postponed in the current postponing scope still
    /// waits (its value unassigned, its carrier open).
    pub(super) fn postponed_numeral_still_open(&self) -> bool {
        if self.postponing_let_depth == 0 {
            return false;
        }
        self.metas
            .postponed_numerals_since(self.postponing_scope_start)
            .iter()
            .any(|(id, _)| {
                !self.metas.is_assigned(*id)
                    && self.metas.get(*id).is_some_and(|var| {
                        let ty = self.metas.instantiate(&var.ty);
                        instance::bare_unassigned_meta(&self.metas, &ty).is_some()
                    })
            })
    }

    /// Elaborate a `let` value with its open numerals waiting
    /// ([`LetValueOrder::NumeralsWait`]).
    pub(super) fn elab_value_with_waiting_numerals(
        &mut self,
        val: &SurfaceExpr,
        expected: Option<Expr>,
    ) -> Result<Expr, ElabError> {
        self.numeral_postpone_depth += 1;
        let result = self.elaborate_with_expected_type(val, expected);
        self.numeral_postpone_depth -= 1;
        result
    }

    /// Whether the file registered an `OfNat` default instance at or above
    /// `instOfNatNat`'s tier (B99), which then decides an open numeral.
    /// `instOfNatNat` is `@[default_instance 100]` in Lean 4.8.0, and a
    /// user's `OfNat` default at that priority is tried before it (Lean keeps
    /// a class's default instances newest first), so any priority from 100 up
    /// wins: `@[default_instance 200] instance : OfNat W n` makes `Tag.tag 5`
    /// a `W`.
    pub(super) fn has_user_ofnat_default_at_nat_tier(&self) -> bool {
        self.default_instances
            .get(&Name::from_string("OfNat"))
            .is_some_and(|entries| {
                entries
                    .iter()
                    .any(|(_, priority)| *priority >= INST_OF_NAT_NAT_DEFAULT_PRIORITY)
            })
    }

    /// The literal `n` at the open carrier `carrier`, as a value
    /// metavariable `?v : carrier` recorded for `drain_postponed_numerals`.
    pub(super) fn postpone_open_numeral(&mut self, n: &BigNat, carrier: &Expr) -> Expr {
        let value = self.fresh_meta(carrier.clone());
        if let ExprKind::FVar(fvar) = value.kind() {
            if let Some(id) = MetaState::from_fvar(*fvar) {
                self.metas.postpone_numeral(id, n.clone());
            }
        }
        value
    }

    /// Settle the numerals postponed since `start`, after the outermost
    /// postponing `let`'s body: a carrier the body left open defaults to
    /// `Nat` (Lean's `@[default_instance] instOfNatNat`), and each literal is
    /// then elaborated at its now-ground carrier exactly as an eager literal
    /// is, and unified with its value metavariable. A carrier that is still
    /// not ground (`Fin ?n`), or a literal that does not elaborate at its
    /// carrier, fails: the caller's transaction then keeps the eager order.
    pub(super) fn drain_postponed_numerals(&mut self, start: usize) -> Result<(), ElabError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        for (id, n) in self.metas.postponed_numerals_since(start) {
            let Some(var) = self.metas.get(id) else {
                return Err(ElabError::CannotInfer);
            };
            let carrier = self.whnf(&self.metas.instantiate(&var.ty));
            // A user `OfNat` default at `instOfNatNat`'s tier or above decides
            // an open carrier before `Nat` does (B99, `coercion.rs`): with
            // `@[default_instance] instance : OfNat W n`, `let k := id 5;
            // Tag.tag k` is a `W`, while `Tag.tag ((k : Int) - 7)` pins `Int`
            // first. Its answer is this order's own, so it is not counted as
            // an early one (`lean_order_attempt`'s watch).
            if instance::bare_unassigned_meta(&self.metas, &carrier).is_some()
                && self.has_user_ofnat_default_at_nat_tier()
            {
                let answers = self.user_default_instance_answers;
                let _ = self
                    .with_eager_numerals(|this| this.elab_nat_literal_with_expected(&n, &carrier));
                self.user_default_instance_answers = answers;
            }
            let carrier = self.whnf(&self.metas.instantiate(&carrier));
            if instance::bare_unassigned_meta(&self.metas, &carrier).is_some()
                && !self.try_unify(&carrier, &nat)
            {
                return Err(ElabError::CannotInfer);
            }
            let carrier = self.metas.instantiate(&carrier);
            if self.has_metavars(&carrier) {
                return Err(ElabError::CannotInfer);
            }
            let literal = self.elab_nat_literal_with_expected(&n, &carrier);
            let literal_ty = self.infer_type(&literal)?;
            if !self.try_unify(&literal_ty, &carrier) {
                return Err(ElabError::CannotInfer);
            }
            let current = self.metas.instantiate(&Expr::fvar(MetaState::to_fvar(id)));
            if instance::bare_unassigned_meta(&self.metas, &current).is_some() {
                if !self.try_unify(&current, &literal) {
                    return Err(ElabError::CannotInfer);
                }
                continue;
            }
            // Unification already gave the waiting numeral a value. To Lean the
            // numeral was `OfNat.ofNat ?α n ?inst` all along, which unifies
            // with that same numeral and with nothing it would have to compute
            // through the pending instance: `have _h : k + 1 = 6 := rfl` made
            // `6`'s metavariable `k + 1`, true at `Int` by evaluation, and
            // Lean refuses it (type mismatch). Only the very literal stands;
            // anything else refuses, as the annotation check does.
            let current = self.metas.instantiate_levels(&current);
            let literal = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&literal));
            if current != literal {
                let err = ElabError::TypeMismatch {
                    expected: crate::error_render::term(&literal),
                    actual: crate::error_render::term(&current),
                };
                self.lean_order_ground_refusal = Some(err.clone());
                return Err(err);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "elab_let_postpone_tests.rs"]
mod tests;

/// Whether `e` is a metavariable with no assignment.
fn bare_meta_unassigned(metas: &MetaState, e: &Expr) -> bool {
    match metas.instantiate(e).kind() {
        ExprKind::FVar(fvar) => MetaState::from_fvar(*fvar).is_some(),
        _ => false,
    }
}
