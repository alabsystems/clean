// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's `binop%` elaborates each LEAF of an operator tree with no expected
//! type (`Lean/Elab/Extra.lean`, `toTree`'s `processLeaf`: `elabTerm s
//! none`), then coerces the leaves whose types differ from the tree's maximal
//! type, which starts at the expected type. Clean's stand-in pins the
//! operator's slots from the expected type first and elaborates every operand
//! AGAINST them, so a compound leaf (`id (nN - 7)`, an `if`, a projection)
//! was elaborated at the expected type instead: `(id ((1 : Nat) - 7) - 7 :
//! Int) = -13 := by decide` was accepted (Lean 4.8.0: `↑(id 0) - 7 = -7`).

use super::*;
use crate::infer::elab_core::{DottedIdent, IdentTarget};

impl ElabCtx<'_> {
    /// Does `arg`, an operand of a homogeneous arithmetic operator whose slot
    /// is the ground type `slot`, settle a DIFFERENT ground type when it is
    /// elaborated alone, as Lean's `binop%` elaborates a leaf? Then the caller
    /// elaborates it with no expected type and coerces it into the slot.
    ///
    /// Only a compound leaf is asked: an operator node (another arithmetic
    /// operator, `-x`) is part of Lean's tree, and a numeral, a name, a hole
    /// or a tactic block elaborates the same either way or is postponed. The
    /// probe is rolled back, and inside it every numeral whose carrier is open
    /// waits (`numeral_postpone_depth`), as Lean's pending `OfNat ?α n` does:
    /// a leaf whose type such a numeral decides (`id (1 - 7)`) has no settled
    /// type, and keeps meeting the slot (Lean unifies that leaf's type with the
    /// maximal type). Inside a postponing scope this is not asked (an open
    /// item: such a leaf still meets the slot there).
    pub(super) fn binop_leaf_settles_alone(&mut self, arg: &SurfaceExpr, slot: &Expr) -> bool {
        if !self.binop_leaf_probe_allowed() || !Self::is_binop_compound_leaf(arg) {
            return false;
        }
        let slot = self.metas.instantiate(slot);
        if self.has_metavars(&slot) {
            return false;
        }
        self.binop_leaf_probe(arg, Some(&slot)).settles
    }

    /// Outside every postponing scope and Lean-order alternative only: a
    /// probe is rolled back, but those scopes keep queues and counters
    /// outside the metavariable state that a probe must not disturb.
    fn binop_leaf_probe_allowed(&self) -> bool {
        self.postponing_let_depth == 0
            && self.numeral_postpone_depth == 0
            && self.defer_user_defaults == 0
    }

    /// Elaborate `arg` alone, as Lean's `processLeaf` does (`elabTerm s
    /// none`), and roll it back. Inside the probe every numeral whose carrier
    /// is open waits, as Lean's pending `OfNat ?α n` does, and an application
    /// whose result is an open `outParam` defaults them on the spot
    /// (`settle_at_open_out_param_result`), as Lean's `elabAppArgs` does.
    fn binop_leaf_probe(&mut self, arg: &SurfaceExpr, slot: Option<&Expr>) -> LeafProbe {
        let queued = self.postponed_open_carrier_instances.clone();
        let queued_do_pure = self.do_pure_obligations.clone();
        let default_answers = self.user_default_instance_answers;
        let let_rec_settled = self.let_rec_settled_open_numerals;
        let deferred_defaults = self.deferred_user_default_goals;
        let ground_refusal = self.lean_order_ground_refusal.take();
        let scope_start = self.postponing_scope_start;
        let default_points = self.lean_default_points;
        let mut probe = LeafProbe::default();
        let _ = self.with_local_scope_rollback(|this| {
            // A postponing scope that never drains: a `let` or β-redex inside
            // the leaf joins it, so its numerals wait too instead of
            // defaulting at its own end.
            this.postponing_scope_start = this.metas.postponed_numeral_count();
            this.postponing_let_depth += 1;
            this.numeral_postpone_depth += 1;
            let elaborated = this.elaborate_arg_with_expected_type(arg, None);
            this.numeral_postpone_depth -= 1;
            this.postponing_let_depth -= 1;
            probe.defaults = this.lean_default_points != default_points;
            if let Ok(term) = elaborated {
                if let Ok(ty) = this.infer_type(&term) {
                    let ty = this.metas.instantiate(&ty);
                    probe.open = this.has_metavars(&ty);
                    probe.settles =
                        !probe.open && slot.is_some_and(|slot| !this.is_def_eq(&ty, slot));
                }
            }
            Err::<(), _>(ElabError::CannotInfer)
        });
        self.postponed_open_carrier_instances = queued;
        self.do_pure_obligations = queued_do_pure;
        self.user_default_instance_answers = default_answers;
        self.let_rec_settled_open_numerals = let_rec_settled;
        self.deferred_user_default_goals = deferred_defaults;
        self.lean_order_ground_refusal = ground_refusal;
        self.postponing_scope_start = scope_start;
        self.lean_default_points = default_points;
        probe
    }

    /// The plan of the operator tree `func args` heads, when it is the ROOT
    /// of a Lean operator tree (a compiler-authored `binop%`/`unop%`/
    /// `rightact%` head that is not itself a node of the tree being
    /// elaborated) and forces a leaf; `None` for a node of an enclosing tree
    /// or a tree that forces nothing.
    ///
    /// Lean elaborates the leaves left to right (`toTree`), each with no
    /// expected type, so a leaf whose type only its numerals decide
    /// (`id (1 - 7)`) is still `?α` when the next leaf is elaborated. When a
    /// LATER leaf is an application whose result is an open `outParam`
    /// (`HAdd.hAdd (1 : Nat) 0`, `xs[0]!`), its `elabAppArgs` runs
    /// `synthesizeSyntheticMVarsUsingDefault` (`Lean/Elab/App.lean:398-404`),
    /// which defaults EVERY pending numeral: the earlier leaf becomes `Nat`
    /// and is coerced, `(id (1 - 7) + HAdd.hAdd (1 : Nat) 0 : Int)` is
    /// `↑(id 0) + ↑1 = 1` in Lean 4.8.0. Such an earlier leaf is
    /// `forced_alone`: elaborated alone with its numerals defaulted, and
    /// coerced into its slot.
    pub(super) fn binop_tree_plan(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Option<BinopTreePlan> {
        if !Self::is_lean_binop_notation_head(func) {
            return None;
        }
        binop_node_key(args)?;
        if let Some(plan) = self.binop_tree_plans.last() {
            if plan.nodes.contains(&node_fingerprint(func, args)) {
                return None;
            }
        }
        if !self.binop_leaf_probe_allowed() {
            return None;
        }
        let mut nodes: Vec<(&SurfaceExpr, &[SurfaceArg])> = Vec::new();
        let mut leaves: Vec<(&SurfaceExpr, bool)> = Vec::new();
        let mut forced: Vec<usize> = Vec::new();
        Self::collect_binop_tree(func, args, true, &mut nodes, &mut leaves);
        let last_defaulting = leaves
            .iter()
            .rposition(|(leaf, _)| self.leaf_may_default_numerals(leaf))?;
        // Leaves before the next defaulting leaf whose numerals are pending.
        // A leaf Lean postpones whole (`leaf_may_postpone`: a `match`, a `by`
        // block, …) is not one: its elaboration waits past the defaulting and
        // then meets the tree's type, as Clean's slot has it
        // (`((match 0 with | _ => 1 - 7) + (HAdd.hAdd (1 : Nat) 0 : Nat) :
        // Int)` is `-5` in Lean 4.8.0).
        let mut open: Vec<usize> = Vec::new();
        for (index, (leaf, coerced)) in leaves.iter().enumerate().take(last_defaulting + 1) {
            let open_candidate =
                *coerced && index < last_defaulting && Self::is_binop_compound_leaf(leaf);
            let defaulting_candidate = !open.is_empty() && self.leaf_may_default_numerals(leaf);
            if !(open_candidate || defaulting_candidate) {
                continue;
            }
            let probe = self.binop_leaf_probe(leaf, None);
            if defaulting_candidate && probe.defaults {
                forced.append(&mut open);
            }
            if open_candidate && probe.open {
                open.push(index);
            }
        }
        // A tree with nothing forced is elaborated as before, and each of its
        // nodes asks again (finding nothing more).
        if forced.is_empty() {
            return None;
        }
        let mut plan = BinopTreePlan {
            nodes: nodes
                .iter()
                .map(|(func, args)| node_fingerprint(func, args))
                .collect(),
            ..BinopTreePlan::default()
        };
        // A forced leaf is told apart by its text (the parser's desugarings
        // carry no spans): one written the same as a leaf that is not forced
        // cannot be, so the tree is refused.
        let prints: Vec<String> = leaves
            .iter()
            .map(|(leaf, _)| surface_fingerprint(leaf))
            .collect();
        for (index, print) in prints.iter().enumerate() {
            if forced.contains(&index) {
                plan.forced_alone.push(print.clone());
            }
        }
        if prints
            .iter()
            .enumerate()
            .any(|(index, print)| !forced.contains(&index) && plan.forced_alone.contains(print))
        {
            plan.refuse = true;
        }
        Some(plan)
    }

    /// Is `arg`, an operand of the node being elaborated, a leaf the active
    /// tree plan elaborates alone (`BinopTreePlan::forced_alone`)?
    pub(super) fn binop_leaf_forced_alone(&self, arg: &SurfaceExpr) -> bool {
        self.binop_tree_plans.last().is_some_and(|plan| {
            !plan.forced_alone.is_empty() && plan.forced_alone.contains(&surface_fingerprint(arg))
        })
    }

    /// Lean's `toTree` over the parser's spelling: a compiler-authored
    /// `binop%` head with two operands, `Neg.neg` (`unop%`) with one, and
    /// `HPow.hPow` (`rightact%`), whose right operand is a leaf outside the
    /// tree's coercions (`coerced` false). Parentheses are transparent.
    fn collect_binop_tree<'e>(
        func: &'e SurfaceExpr,
        args: &'e [SurfaceArg],
        coerced: bool,
        nodes: &mut Vec<(&'e SurfaceExpr, &'e [SurfaceArg])>,
        leaves: &mut Vec<(&'e SurfaceExpr, bool)>,
    ) {
        nodes.push((func, args));
        let pow = Self::is_pow_head(func);
        for (index, arg) in args.iter().enumerate() {
            let coerced = coerced && !(pow && index == 1);
            match Self::unwrap_surface_parens(&arg.expr) {
                SurfaceExpr::App(_, head, inner)
                    if Self::is_lean_binop_notation_head(head)
                        && binop_node_key(inner).is_some() =>
                {
                    Self::collect_binop_tree(head, inner, coerced, nodes, leaves);
                }
                _ => leaves.push((&arg.expr, coerced)),
            }
        }
    }

    fn is_pow_head(func: &SurfaceExpr) -> bool {
        matches!(
            Self::unwrap_surface_parens(func),
            SurfaceExpr::Ident(_, name) if name == &SurfaceName::generated_path("HPow.hPow")
        )
    }

    /// Does `e` hold an application Lean elaborates with `elabAppArgs` whose
    /// head constant returns an `outParam` of one of its instance binders
    /// (`HAdd.hAdd` written out, `getElem!` from `xs[i]!`)? Only such an
    /// application can default the pending numerals (`binop_tree_plan`); the
    /// probe then says whether it does.
    fn leaf_may_default_numerals(&self, e: &SurfaceExpr) -> bool {
        let mut stack = vec![e];
        while let Some(e) = stack.pop() {
            match e {
                SurfaceExpr::App(_, head, args) => {
                    if !Self::is_lean_binop_notation_head(head)
                        && self
                            .surface_head_global(head)
                            .is_some_and(|global| self.global_returns_out_param(&global))
                    {
                        return true;
                    }
                    stack.push(head);
                    stack.extend(args.iter().map(|a| &a.expr));
                }
                SurfaceExpr::Paren(_, inner)
                | SurfaceExpr::Explicit(_, inner)
                | SurfaceExpr::NamedArg(_, _, inner)
                | SurfaceExpr::Proj(_, inner, _)
                | SurfaceExpr::UniverseInst(_, inner, _)
                | SurfaceExpr::Lambda(_, _, inner) => stack.push(inner),
                SurfaceExpr::Ascription(_, inner, ty) => {
                    stack.push(inner);
                    stack.push(ty);
                }
                SurfaceExpr::Let(_, _, value, body) | SurfaceExpr::Have(_, _, value, body) => {
                    stack.push(value);
                    stack.push(body);
                }
                SurfaceExpr::If(_, cond, then_br, else_br) => {
                    stack.push(cond);
                    stack.push(then_br);
                    stack.push(else_br);
                }
                _ => {}
            }
        }
        false
    }

    /// The global constant an application head names: an identifier, or a
    /// dotted spelling the parser reads as field notation on an identifier
    /// (`HAdd.hAdd` is `Proj(HAdd, hAdd)`); `None` for a local or anything
    /// else.
    fn surface_head_global(&self, head: &SurfaceExpr) -> Option<Name> {
        match Self::unwrap_surface_parens(head) {
            SurfaceExpr::Ident(_, name) => match self.resolve_ident_target(name) {
                IdentTarget::Global(global) => Some(global),
                _ => None,
            },
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                let base = Self::surface_dotted_spelling(base)?;
                match self.resolve_dotted_ident(&base, field) {
                    DottedIdent::Global(global) => Some(global),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// `A.b.c` spelled as an identifier under named projections.
    fn surface_dotted_spelling(e: &SurfaceExpr) -> Option<SurfaceName> {
        match e {
            SurfaceExpr::Ident(_, name) => Some(name.clone()),
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                Some(Self::surface_dotted_spelling(base)?.append(field))
            }
            _ => None,
        }
    }

    /// Lean's `isNextOutParamOfLocalInstanceAndResult` on the global
    /// constant `global`.
    fn global_returns_out_param(&self, global: &Name) -> bool {
        self.env
            .get_const(global)
            .is_some_and(|info| self.result_is_out_param_of_local_instance(&info.type_.clone()))
    }

    /// A leaf of Lean's operator tree that is not a numeral, a name, a hole, a
    /// tactic block or an ascription, and not itself an operator node; and
    /// that holds nothing Lean postpones while its expected type is unknown
    /// (`leaf_may_postpone`).
    fn is_binop_compound_leaf(arg: &SurfaceExpr) -> bool {
        Self::is_binop_compound_leaf_shape(arg) && !Self::leaf_may_postpone(arg)
    }

    /// Does `e` hold a term Lean elaborates later when its expected type is
    /// a metavariable (`tryPostponeIfMVar`: a `match`, a `by` block, an
    /// anonymous constructor, a leading-dot name, a `do` block)? Clean
    /// elaborates those in place, so alone they settle a type Lean's leaf
    /// leaves open: `(fun z => z - 7) (match 0 with | _ => Nat.succ 0)` is
    /// at `?α` in Lean, which the tree's `Int` then pins (`-6`). Unknown
    /// forms count as postponing.
    fn leaf_may_postpone(e: &SurfaceExpr) -> bool {
        match e {
            SurfaceExpr::Lit(..) | SurfaceExpr::Universe(..) => false,
            SurfaceExpr::Ident(_, name) => name.is_relative_constructor(),
            SurfaceExpr::Paren(_, inner)
            | SurfaceExpr::Explicit(_, inner)
            | SurfaceExpr::NamedArg(_, _, inner)
            | SurfaceExpr::Proj(_, inner, _)
            | SurfaceExpr::UniverseInst(_, inner, _) => Self::leaf_may_postpone(inner),
            SurfaceExpr::Ascription(_, inner, ty) => {
                Self::leaf_may_postpone(inner) || Self::leaf_may_postpone(ty)
            }
            SurfaceExpr::Lambda(_, _, body) => Self::leaf_may_postpone(body),
            SurfaceExpr::Let(_, _, value, body) | SurfaceExpr::Have(_, _, value, body) => {
                Self::leaf_may_postpone(value) || Self::leaf_may_postpone(body)
            }
            SurfaceExpr::If(_, cond, then_br, else_br) => {
                Self::leaf_may_postpone(cond)
                    || Self::leaf_may_postpone(then_br)
                    || Self::leaf_may_postpone(else_br)
            }
            SurfaceExpr::App(_, head, args) => {
                Self::leaf_may_postpone(head)
                    || args.iter().any(|a| Self::leaf_may_postpone(&a.expr))
            }
            _ => true,
        }
    }

    /// `-x` (`Neg.neg`), Lean's `unop%` node: its operand is a leaf of the
    /// same tree, so `(-(id (nN - 7)) : Int)` is `-↑(id 0) = 0` in Lean 4.8.0.
    pub(super) fn is_neg_head(func: &SurfaceExpr) -> bool {
        matches!(
            Self::unwrap_surface_parens(func),
            SurfaceExpr::Ident(_, name) if name == &SurfaceName::generated_path("Neg.neg")
        )
    }

    fn is_binop_compound_leaf_shape(arg: &SurfaceExpr) -> bool {
        match Self::unwrap_surface_parens(arg) {
            SurfaceExpr::Lit(..)
            | SurfaceExpr::Ident(..)
            | SurfaceExpr::Hole(_)
            | SurfaceExpr::NamedHole(..)
            | SurfaceExpr::ByTactic(..)
            | SurfaceExpr::Ascription(..) => false,
            SurfaceExpr::App(_, head, _) => {
                !Self::is_hetero_binop_head(head) && !Self::is_neg_head(head)
            }
            _ => true,
        }
    }
}

/// What [`ElabCtx::binop_leaf_probe`] saw of a leaf elaborated alone.
#[derive(Default)]
struct LeafProbe {
    /// Its type still holds a metavariable (a pending numeral's carrier).
    open: bool,
    /// Its type is ground and differs from the slot it was asked against.
    settles: bool,
    /// It ran Lean's result-is-`outParam` defaulting.
    defaults: bool,
}

/// An operator tree being elaborated (`ElabCtx::binop_tree_plan`).
#[derive(Debug, Default)]
pub(super) struct BinopTreePlan {
    /// Every operator node of the tree, by [`node_fingerprint`].
    nodes: Vec<String>,
    /// The leaves elaborated alone and coerced, by [`surface_fingerprint`].
    forced_alone: Vec<String>,
    /// The tree cannot be elaborated as Lean does: refused.
    pub(super) refuse: bool,
}

/// An operator node's operands as the tree reads them: one or two, all
/// positional; `None` otherwise.
fn binop_node_key(args: &[SurfaceArg]) -> Option<()> {
    ((1..=2).contains(&args.len()) && args.iter().all(|a| a.name.is_none())).then_some(())
}

/// A surface term's identity within one tree: its full structure (names,
/// literals and spans; the parser's desugarings carry dummy spans, so two
/// leaves written alike print alike).
fn surface_fingerprint(e: &SurfaceExpr) -> String {
    format!("{e:?}")
}

fn node_fingerprint(func: &SurfaceExpr, args: &[SurfaceArg]) -> String {
    format!("{func:?}{args:?}")
}
