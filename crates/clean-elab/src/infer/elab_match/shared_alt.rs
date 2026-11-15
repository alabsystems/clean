// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One elaboration per catch-all alternative of a constant-motive `match`
//! (gap G76 of `docs/issues/2026-09-19-trust-ir-semantics-elaborator-gaps.md`,
//! ledger class (146)).
//!
//! The constructor-ordered `casesOn` builder
//! (`ctor_order.rs::try_build_ctor_ordered_match_alts`) walks the scrutinee
//! type's CONSTRUCTORS and emits one minor premise per constructor, so a
//! trailing `| _ => rhs` (or `| x => rhs`) arm becomes the minor of every
//! constructor no earlier arm names. It used to ELABORATE `rhs` once per such
//! constructor. A catch-all whose right-hand side is itself a `match` with a
//! catch-all therefore cost `k₁ · k₂ · …` elaborations — exponential in the
//! nesting depth. trust-ir `Pred.impliesFuel` (`TrustIr/Pred.lean:532`, nine
//! constructors, catch-alls five deep) never finished.
//!
//! Lean elaborates each alternative's right-hand side ONCE, as a lambda over
//! its pattern variables (`Lean.Elab.Term.elabMatchAltView` builds the
//! alternative, `Lean.Meta.Match.mkMatcher` threads it to every leaf of the
//! decision tree as an argument of the auxiliary `match_N`), so its cost is
//! linear in the source. This module does the same for a catch-all: the
//! right-hand side is elaborated once, in the context of the match plus the
//! arm's own binder (the alias `x` of `| x => …`; a wildcard binds nothing),
//! and every constructor's minor premise is built around that one term —
//! `fun fields… => rhs` for `_`, `fun fields… => let x := ctor fields…; rhs`
//! for `x`, exactly the shapes the per-constructor elaboration produced.
//!
//! Sharing is restricted to what makes the per-constructor elaborations
//! identical:
//!
//! * a CONSTANT motive (`match_dependent_motive` unset): every minor then has
//!   the same expected type, `branch_ty`; under a dependent motive each
//!   constructor refines it, and that path elaborates per constructor as
//!   before;
//! * the same local context: an entry is reused only while the locals in scope
//!   are the ones it was elaborated under (constructor arms elaborate inside
//!   temporary scopes, so this always holds today; the check keeps it a fact
//!   rather than an assumption).
//!
//! A named catch-all's right-hand side no longer sees the constructor's field
//! locals (`_match_ctor_field.i`, which no source name can reach). Lean's
//! alternative `fun x => rhs` does not have them either, so a tactic block
//! there (`by assumption`) can no longer pick up a field Lean never offers.
//!
//! Elaborating once is not enough on its own: copied into every minor, the one
//! term is a small DAG but a TREE as large as before, and every consumer that
//! walks terms as trees (simp's equation synthesis, the kernel's let-scoped
//! inference memo, the sorry scan) pays the exponential size again — trust-ir
//! `Proofs/PredLatticeProps.lean` went from a timeout to an 8 GB memory cap
//! that way. So a right-hand side of at least [`LET_BIND_MIN_TREE_NODES`]
//! nodes that is the WHOLE minor of two constructors or more is bound once by
//! a `let` around the eliminator (`let alt := rhs` / `let alt := fun x =>
//! rhs`), and those minors name it (`fun fields… => alt`, `fun fields… => let
//! x := ctor fields…; alt x`): definitionally the copied form (zeta), linear as
//! a tree, as Lean's matcher is linear in its alternatives. This is the
//! arm-scope fallback binding of `nested_ctor.rs`
//! (`apply_nested_plans_with_fallback`, G15) one level up. The binding is NOT
//! in scope while any arm elaborates (a tactic body could take it for a
//! hypothesis); the caller binds it only around the finished eliminator
//! (`push_shared_alt_bindings`, `bind_shared_alts`). Smaller right-hand sides
//! keep the copied form, so small matches keep their exact terms.

use super::*;

/// The tree size (expression nodes) from which a shared right-hand side is
/// bound by a `let` instead of copied: small enough that nesting cannot grow a
/// copied term past a few constructors' worth of it, large enough that the
/// everyday small `match` (`| _ => 0`, `| _ => none`) keeps its exact term.
const LET_BIND_MIN_TREE_NODES: usize = 64;

/// A shared right-hand side bound by a `let` around the eliminator.
pub(in crate::infer) struct SharedAltBinding {
    /// The placeholder the minors name; never in scope while an arm
    /// elaborates.
    pub(in crate::infer) fvar: FVarId,
    pub(in crate::infer) name: SurfaceName,
    /// `branch_ty`, or `scrutinee_ty → branch_ty` for a named catch-all.
    pub(in crate::infer) ty: Expr,
    /// `rhs`, or `fun x => rhs` for a named catch-all.
    pub(in crate::infer) value: Expr,
}

/// A catch-all right-hand side, elaborated once for one `match`.
struct SharedCatchAll {
    /// The alternative's source index (after or-pattern expansion).
    arm_idx: usize,
    /// The locals in scope when it was elaborated, innermost last.
    scope: Vec<FVarId>,
    /// `rhs` (wildcard arm) or `rhs` with the arm's binder abstracted to
    /// `BVar 0` (named arm), already wrapped in the extra parameters.
    body: Expr,
    /// The `let` placeholder when the right-hand side is bound once.
    bound: Option<FVarId>,
}

/// The catch-all right-hand sides one constructor-ordered `match` has
/// elaborated so far. Lives exactly as long as that `match`'s minor-premise
/// walk.
#[derive(Default)]
pub(in crate::infer) struct SharedCatchAlls {
    entries: Vec<SharedCatchAll>,
    /// Per catch-all alternative: how many constructors it is the WHOLE minor
    /// of (no earlier alternative names them).
    whole_minor_counts: Vec<(usize, usize)>,
    bindings: Vec<SharedAltBinding>,
}

impl SharedCatchAlls {
    pub(super) fn with_whole_minor_counts(counts: Vec<(usize, usize)>) -> Self {
        Self {
            whole_minor_counts: counts,
            ..Self::default()
        }
    }

    fn whole_minor_count(&self, arm_idx: usize) -> usize {
        self.whole_minor_counts
            .iter()
            .find(|(arm, _)| *arm == arm_idx)
            .map_or(0, |(_, count)| *count)
    }

    /// The bindings some of `minors` name, in creation order.
    pub(super) fn into_bindings(self, minors: &[Expr]) -> Vec<SharedAltBinding> {
        self.bindings
            .into_iter()
            .filter(|binding| minors.iter().any(|minor| names_fvar(minor, binding.fvar)))
            .collect()
    }
}

/// The minor-premise body a constructor gets from a shared right-hand side:
/// the term itself, or a reference to its `let`.
pub(super) enum SharedRhs {
    /// Copy this term (a named catch-all's has its binder at `BVar 0`).
    Copied(Expr),
    /// Name the `let` placeholder.
    Bound(FVarId),
}

impl SharedRhs {
    /// The body under the minor's binders: for a named catch-all, under the
    /// `let x := ctor fields…` (`BVar 0`).
    pub(super) fn minor_body(self, named: bool) -> Expr {
        match self {
            Self::Copied(body) => body,
            Self::Bound(fvar) if named => Expr::app(Expr::fvar(fvar), Expr::bvar(0)),
            Self::Bound(fvar) => Expr::fvar(fvar),
        }
    }
}

impl<'a> ElabCtx<'a> {
    fn local_scope_fvars(&self) -> Vec<FVarId> {
        self.locals.iter().map(|(_, fvar, _)| *fvar).collect()
    }

    /// The right-hand side of catch-all alternative `arm_idx`, elaborated
    /// against the constant branch type `branch_ty` — once per `match`.
    ///
    /// `binder` is the arm's pattern variable (`| x => …`), bound as an opaque
    /// local of the scrutinee's type while `rhs` elaborates and returned
    /// abstracted to `BVar 0`; `None` is a wildcard. The caller wraps the
    /// result per constructor and must only call this under a constant motive.
    /// `whole_minor` says the caller's minor IS this right-hand side (no
    /// constructor arm of its own to fall back from): only such a minor may
    /// name the `let`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn shared_catch_all_body(
        &mut self,
        shared: &mut SharedCatchAlls,
        arm: &clean_parser::SurfaceMatchArm,
        arm_idx: usize,
        binder: Option<&SurfaceName>,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
        whole_minor: bool,
    ) -> Result<SharedRhs, ElabError> {
        debug_assert!(self.match_dependent_motive.is_none());
        let scope = self.local_scope_fvars();
        if let Some(entry) = shared
            .entries
            .iter()
            .find(|entry| entry.arm_idx == arm_idx && entry.scope == scope)
        {
            return Ok(match entry.bound {
                Some(fvar) if whole_minor => SharedRhs::Bound(fvar),
                _ => SharedRhs::Copied(entry.body.clone()),
            });
        }
        let body = match binder {
            None => {
                let arm_body =
                    self.elaborate_with_expected_type(&arm.body, Some(branch_ty.clone()))?;
                if arm_idx > 0 {
                    self.check_arm_type(&arm_body, branch_ty, arm_idx)?;
                }
                wrap_with_extra_params(arm_body, extra_param_info)
            }
            Some(name) => {
                let alias = self.push_local(name.clone(), scrutinee_ty.clone());
                let elaborated = self
                    .elaborate_with_expected_type(&arm.body, Some(branch_ty.clone()))
                    .and_then(|arm_body| {
                        if arm_idx > 0 {
                            self.check_arm_type(&arm_body, branch_ty, arm_idx)?;
                        }
                        Ok(arm_body)
                    });
                self.pop_local();
                wrap_with_extra_params(elaborated?, extra_param_info).abstract_fvar(alias)
            }
        };
        let bound = (shared.whole_minor_count(arm_idx) >= 2
            && tree_size_reaches(&body, LET_BIND_MIN_TREE_NODES))
        .then(|| {
            let fvar = self.fresh_fvar();
            let (ty, value) = match binder {
                None => (branch_ty.clone(), body.clone()),
                // `branch_ty` is closed under the new binder: a constant
                // motive does not mention the scrutinee.
                Some(_) => (
                    Expr::pi(BinderInfo::Default, scrutinee_ty.clone(), branch_ty.clone()),
                    Expr::lam(BinderInfo::Default, scrutinee_ty.clone(), body.clone()),
                ),
            };
            shared.bindings.push(SharedAltBinding {
                fvar,
                // Named by the alternative, never by the fvar counter: the
                // term must not depend on what was elaborated before it (an
                // importer re-elaborates its imports and compares them).
                name: SurfaceName::unspellable("_match_alt", arm_idx as u64),
                ty,
                value,
            });
            fvar
        });
        shared.entries.push(SharedCatchAll {
            arm_idx,
            scope,
            body: body.clone(),
            bound,
        });
        Ok(match bound {
            Some(fvar) if whole_minor => SharedRhs::Bound(fvar),
            _ => SharedRhs::Copied(body),
        })
    }

    /// Bring the `let` placeholders of a finished minor walk into scope (as
    /// let-bound locals) for the rest of the eliminator's assembly.
    pub(in crate::infer) fn push_shared_alt_bindings(&mut self, bindings: &[SharedAltBinding]) {
        for binding in bindings {
            self.push_local_let_with_fvar(
                binding.name.clone(),
                binding.fvar,
                binding.ty.clone(),
                binding.value.clone(),
            );
        }
    }

    /// Close the finished eliminator application `result` over the bindings
    /// [`Self::push_shared_alt_bindings`] brought into scope: pop them and
    /// wrap `result` in their `let`s, outermost first.
    pub(in crate::infer) fn bind_shared_alts(
        &mut self,
        result: Expr,
        bindings: &[SharedAltBinding],
    ) -> Result<Expr, ElabError> {
        if bindings.is_empty() {
            return Ok(result);
        }
        let base = self.locals.len().checked_sub(bindings.len());
        let on_top = base.is_some_and(|base| {
            self.locals[base..]
                .iter()
                .map(|(_, fvar, _)| *fvar)
                .eq(bindings.iter().map(|binding| binding.fvar))
        });
        if !on_top {
            return Err(ElabError::InternalInvariant(
                "shared match alternative bindings are not the innermost locals".to_string(),
            ));
        }
        let mut result = result;
        for binding in bindings.iter().rev() {
            self.pop_local();
            result = Expr::let_named(
                binding.name.name().clone(),
                binding.ty.clone(),
                binding.value.clone(),
                result.abstract_fvar(binding.fvar),
                false,
            );
        }
        Ok(result)
    }

    /// The minor premise of `ctor_name` for a NAMED catch-all whose shared
    /// right-hand side is `body` (`BVar 0` = the arm's binder):
    /// `fun fields… => let x : T := ctor fields…; body`.
    pub(super) fn named_catch_all_minor(
        &mut self,
        ctor_name: &Name,
        binder: &SurfaceName,
        body: Expr,
        scrutinee_ty: &Expr,
    ) -> Result<Expr, ElabError> {
        let field_tys = self.compute_ctor_field_types(ctor_name, scrutinee_ty)?;
        let mut field_fvars: Vec<(FVarId, Expr)> = Vec::with_capacity(field_tys.len());
        for (idx, field_ty) in field_tys.iter().enumerate() {
            let prior_fvars: Vec<FVarId> = field_fvars.iter().map(|(f, _)| *f).collect();
            let field_ty = Self::open_field_type_with_fvars(field_ty, &prior_fvars);
            let fvar = self.push_local(
                SurfaceName::from_name(Name::anon().str("_match_ctor_field").num(idx as u64)),
                field_ty.clone(),
            );
            field_fvars.push((fvar, field_ty));
        }
        let field_ids: Vec<FVarId> = field_fvars.iter().map(|(fvar, _)| *fvar).collect();
        let ctor_value = self.build_ctor_value(ctor_name, scrutinee_ty, &field_ids);
        for _ in &field_fvars {
            self.pop_local();
        }
        // The field locals are fresh, so only the constructor value and the
        // later fields' types can mention them: close those alone instead of
        // walking the shared body once per field. `abstract_fvar` shifts the
        // loose indices already present, so closing `f₀, f₁, …` in that order
        // leaves `fᵢ` at `BVar (n - 1 - i)` under the `n` field binders.
        let close = |term: Expr, fields: &[(FVarId, Expr)]| {
            fields
                .iter()
                .fold(term, |acc, (fvar, _)| acc.abstract_fvar(*fvar))
        };
        let ctor_value = close(ctor_value?, &field_fvars);
        // `body` mentions no field (they did not exist while it elaborated);
        // its one loose index is the binder, bound by this `let`.
        let mut result = Expr::let_named(
            binder.name().clone(),
            scrutinee_ty.clone(),
            ctor_value,
            body,
            false,
        );
        for (idx, (_, field_ty)) in field_fvars.iter().enumerate().rev() {
            let domain = close(field_ty.clone(), &field_fvars[..idx]);
            result = Expr::lam(BinderInfo::Default, domain, result);
        }
        Ok(result)
    }
}

/// Whether `expr`, read as a TREE, has at least `limit` nodes; stops counting
/// there, so the cost is at most `limit` steps whatever the sharing.
fn tree_size_reaches(expr: &Expr, limit: usize) -> bool {
    let mut count = 0usize;
    let mut stack: Vec<&Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        count += 1;
        if count >= limit {
            return true;
        }
        match e.kind() {
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => stack.push(inner),
            _ => {}
        }
    }
    false
}

/// Whether `expr` mentions `fvar`, visiting each distinct node once.
fn names_fvar(expr: &Expr, fvar: FVarId) -> bool {
    let mut seen: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut stack: Vec<&Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        if !e.has_fvar_quick() || !seen.insert(std::ptr::from_ref(e) as usize) {
            continue;
        }
        match e.kind() {
            ExprKind::FVar(id) if *id == fvar => return true,
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => stack.push(inner),
            ExprKind::FVar(_)
            | ExprKind::BVar(_)
            | ExprKind::Const(..)
            | ExprKind::Sort(_)
            | ExprKind::Lit(_) => {}
            // Clean's non-Lean forms never come out of a `match`; a full walk
            // keeps the answer exact if one ever does.
            _ => {
                if crate::tactic::builtins_replace::mentions_fvar(e, fvar) {
                    return true;
                }
            }
        }
    }
    false
}
