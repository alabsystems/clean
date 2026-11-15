// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lifting `where` / `let rec` helpers to top-level auxiliary declarations.
//!
//! Lean never leaves a `let rec` inside the term that defines it. Each helper
//! `go` of a declaration `parent` becomes its own declaration `parent.go`
//! (`Lean/Elab/LetRec.lean:46`, `declName := currDeclName ++ shortDeclName`;
//! a helper nested in `go`'s value is `parent.go.inner`, because the value is
//! elaborated under `withDeclName view.declName`). Its parameters are the
//! locals it captures — the free variables of its type and value, closed
//! under their own types, in local-context order, each keeping its binder
//! info — followed by its own (`Lean/Elab/MutualDef.lean` `MutualClosure`,
//! `mkClosureFor` / `mkLetRecClosureFor`). Every use of `go` in the parent
//! becomes `parent.go c₁ … cₖ`. So
//!
//! ```lean
//! def Memory.readBytes (mem : Memory) (addr : Addr) (n : Nat) :=
//!   let rec go (remaining : Nat) (cur : Addr) : Option (List UInt8) := … mem …
//!   go n addr
//! ```
//!
//! registers `Memory.readBytes.go : Memory → Nat → Addr → Option (List UInt8)`
//! and `Memory.readBytes := fun mem addr n => Memory.readBytes.go mem n addr`
//! (pinned `lean` v4.8.0, `#print`). Proofs name the helper directly
//! (`simp [Memory.readBytes.go]`), and `simp only [Memory.readBytes]` exposes
//! `Memory.readBytes.go …` for a lemma about it to rewrite with. Clean used to
//! inline the helper as a `let`, so the name did not exist and every such
//! reference died as dot notation on a function value.
//!
//! # How the auxiliary travels to registration
//!
//! The elaborator's environment is immutable while a declaration elaborates,
//! so `parent.go` cannot exist yet when the parent's body is elaborated — and
//! the body is still being type-checked after the helper is done. The helper
//! is therefore bound as
//!
//! ```text
//! let parent.go : T[c] := ((fun (x : Π c, T[c]) => x) (fun c => V[c])) c₁ … cₖ; body
//! ```
//!
//! — an ordinary, kernel-checkable `let` whose value carries the CLOSED type
//! and value of the auxiliary. Everything the parent's finishing passes do
//! (metavariable instantiation, abstraction over its binders, universe
//! canonicalization and renaming) applies to that closed copy exactly as to
//! the rest of the term, so at the declaration boundary
//! [`ElabCtx::finish_let_rec_lifts`] can read the auxiliary off the term in
//! its final form, register it with the parent's universe parameters (Lean
//! gives every declaration of the block the same list,
//! `Lean/Elab/PreDefinition/Basic.lean` `fixLevelParams`), and replace the
//! `let` by `body[parent.go := parent.go.{us} c₁ … cₖ]`.
//!
//! A helper whose type or value still holds an unassigned metavariable, or
//! that captures a local this context cannot type, is NOT lifted: it keeps the
//! historical inline `let`, which is a correct (if un-nameable) term.
//!
//! # What Lean refuses, and what a `partial` parent changes
//!
//! * A helper whose name is already declared, and a second helper of the same
//!   name in one declaration, are errors (`'p.go' has already been declared`,
//!   pinned v4.8.0, even when the two helpers are identical). A body the value
//!   elaborator runs twice (a failed speculative pass, then the retry) lifts
//!   the SAME helper twice; the two are told apart by where they were written.
//! * A recursive helper of a `partial` declaration is an `opaque`
//!   (`getModifiersForLetRecs` gives it `recKind := partial`, and
//!   `addPreDefinitions` sends its recursive clique to `addAndCompilePartial`,
//!   `Lean/Elab/PreDefinition/Main.lean`), which needs its type inhabited
//!   (`mkInhabitantFor`). So `partial def pp (n : Nat) : Nat := go n where go
//!   : Nat → Nat | 0 => 0 | k+1 => go k` has `pp.go 3 = 0` and `pp 3 = 0` NOT
//!   provable by `rfl` (pinned v4.8.0). The auxiliary registers as an opaque
//!   carrying its kernel-checked value, which the compiler still runs; a
//!   non-recursive helper stays an ordinary definition, as in Lean
//!   (`isNonRecursive`). A recursive helper of a `partial` parent that cannot
//!   be lifted is refused rather than inlined: inline, it would reduce.

use std::collections::{HashMap, HashSet};

use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level, Name};
use clean_parser::{DeclModifiers, Span, SurfaceName};

use super::{ElabCtx, ElabResult};
use crate::ElabError;

/// One declaration's lifting state.
#[derive(Debug, Default)]
pub(super) struct LetRecLiftScope {
    /// The declaration being elaborated, then each enclosing helper whose
    /// value is being elaborated (`parent`, `parent.go`, …).
    decl_names: Vec<Name>,
    /// Every auxiliary name bound so far, in elaboration order.
    lifted: Vec<Name>,
    /// The declaration is `partial`, so its recursive helpers are opaque
    /// (module docs).
    parent_partial: bool,
    /// The helpers lifted from a RECURSIVE binding.
    recursive: HashSet<Name>,
    /// Where each helper was written: the same site lifting twice is one
    /// helper elaborated twice, two sites are two helpers (module docs).
    sites: HashMap<Name, Span>,
    /// Each helper's parameter names and binder infos, a prefix of its
    /// telescope: its captured locals, then the own parameters its type
    /// names.
    params: HashMap<Name, Vec<(Name, BinderInfo)>>,
}

/// Whether `span` is a source region (a synthesized node carries the dummy).
fn is_source_span(span: Span) -> bool {
    span != Span::dummy()
}

/// Whether two source regions share no byte.
fn disjoint(a: Span, b: Span) -> bool {
    a.end <= b.start || b.end <= a.start
}

/// The lifting state an [`ElabCtx`] carries.
#[derive(Debug, Default)]
pub(super) struct LetRecLiftState {
    /// `Some` while a declaration that lifts its helpers is elaborating.
    scope: Option<LetRecLiftScope>,
    /// For each lifted helper whose body is elaborating: the local bound to
    /// it, mapped to the term that stands for one use of it. A sibling helper
    /// whose value mentions the local has it replaced by that term before its
    /// own captures are computed, so it captures what the helper captures
    /// (Lean's `mkFreeVarMap`) instead of the helper itself.
    uses: HashMap<FVarId, Expr>,
    /// Binder infos of the locals a binder introduced while the declaration
    /// elaborates — its own parameters, a `fun {β}` / `fun [inst : C α]`
    /// binder of its body, and a binder the implicit-lambda rule introduced
    /// from an expected type — so a captured `{α}` or `[inst : C α]` stays
    /// implicit / instance-implicit on the auxiliary, as Lean's
    /// `mkClosureForAux` keeps each local's binder info (pinned v4.8.0:
    /// `@f.go : {β : Type} → β → Nat → List β` for a `let rec` under `fun {β}
    /// b =>`). Any other captured local (`let`, `have`, a match variable) is
    /// explicit, as it is in Lean's local context.
    binder_infos: HashMap<FVarId, BinderInfo>,
    /// Locals whose binder info is unknown: tactic hypotheses bridged into
    /// term elaboration (the bridge carries none). A helper capturing one is
    /// not lifted: guessing explicit could accept a call Lean refuses.
    unknown_binders: HashSet<FVarId>,
    /// The parameter names of every auxiliary a finished declaration
    /// produced, for named arguments on it (`parent.go (k := 2)`), waiting to
    /// be registered after the auxiliary is ([`crate::decl_attributes`]).
    finished_params: Vec<(Name, Vec<(Name, BinderInfo)>)>,
}

impl ElabCtx<'_> {
    /// Start lifting the helpers of declaration `decl_name` (`partial` when
    /// `parent_partial`). Returns the enclosing scope, which
    /// [`Self::end_let_rec_lift`] restores.
    pub(super) fn begin_let_rec_lift(
        &mut self,
        decl_name: Name,
        parent_partial: bool,
    ) -> Option<LetRecLiftScope> {
        self.let_rec_lift.scope.replace(LetRecLiftScope {
            decl_names: vec![decl_name],
            parent_partial,
            ..LetRecLiftScope::default()
        })
    }

    /// The parameter names of the auxiliaries finished so far, for
    /// registration beside them.
    pub(crate) fn take_let_rec_param_infos(&mut self) -> Vec<(Name, Vec<(Name, BinderInfo)>)> {
        std::mem::take(&mut self.let_rec_lift.finished_params)
    }

    /// Stop lifting for the current declaration, restoring `saved`. Returns
    /// the finished scope for [`Self::finish_let_rec_lifts`].
    pub(super) fn end_let_rec_lift(
        &mut self,
        saved: Option<LetRecLiftScope>,
    ) -> Option<LetRecLiftScope> {
        if saved.is_none() {
            // The outermost declaration is done elaborating; its parameter
            // locals are gone.
            self.let_rec_lift.binder_infos.clear();
            self.let_rec_lift.unknown_binders.clear();
        }
        std::mem::replace(&mut self.let_rec_lift.scope, saved)
    }

    /// `result` preceded by the auxiliary declarations its helpers lifted to
    /// (dependencies first), registered as one unit.
    pub(super) fn with_let_rec_auxiliaries(
        mut auxiliaries: Vec<ElabResult>,
        result: ElabResult,
    ) -> ElabResult {
        if auxiliaries.is_empty() {
            return result;
        }
        auxiliaries.push(result);
        ElabResult::Multiple(auxiliaries)
    }

    /// Record the binder info of a local a binder introduced (see
    /// [`LetRecLiftState::binder_infos`]).
    pub(super) fn note_let_rec_binder(&mut self, fvar: FVarId, info: BinderInfo) {
        self.locals.set_binder_info(fvar, info.into());
        if self.let_rec_lift.scope.is_some() {
            self.let_rec_lift.binder_infos.insert(fvar, info);
        }
    }

    /// Record a local whose binder info is unknown (see
    /// [`LetRecLiftState::unknown_binders`]).
    pub(super) fn note_let_rec_unknown_binder(&mut self, fvar: FVarId) {
        if self.let_rec_lift.scope.is_some() && !self.let_rec_lift.binder_infos.contains_key(&fvar)
        {
            self.let_rec_lift.unknown_binders.insert(fvar);
        }
    }

    /// The name helper `short` lifts to — `None` outside a lifting scope.
    pub(super) fn let_rec_aux_name(&self, short: &SurfaceName) -> Option<Name> {
        let scope = self.let_rec_lift.scope.as_ref()?;
        let current = scope.decl_names.last()?;
        Some(crate::namespace::append_names(current, short.name()))
    }

    /// Run `f` — the elaboration of helper `aux`'s value — with `aux` as the
    /// current declaration name, so a helper nested in it lifts to `aux.inner`.
    pub(super) fn with_let_rec_decl_name<T>(
        &mut self,
        aux: Option<&Name>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let pushed = match (aux, self.let_rec_lift.scope.as_mut()) {
            (Some(name), Some(scope)) => {
                scope.decl_names.push(name.clone());
                true
            }
            _ => false,
        };
        let out = f(self);
        if pushed {
            if let Some(scope) = self.let_rec_lift.scope.as_mut() {
                scope.decl_names.pop();
            }
        }
        out
    }

    /// Closure-convert helper `site.aux` (elaborated as `helper_val :
    /// helper_ty` in the current local context) and return the value its
    /// binding `let` carries: [`ascribe_closed`] of the auxiliary applied to
    /// the captured locals. `Ok(None)` when the helper cannot be lifted
    /// (module docs) and may stay inline; `Err` for what Lean refuses — a name
    /// already declared, a second helper of the name, and a recursive helper
    /// of a `partial` declaration that cannot be lifted.
    pub(super) fn let_rec_lifted_value(
        &mut self,
        site: HelperSite<'_>,
        helper_ty: &Expr,
        helper_val: &Expr,
    ) -> Result<Option<Expr>, ElabError> {
        let Some(scope) = self.let_rec_lift.scope.as_ref() else {
            return Ok(None);
        };
        let aux = site.aux;
        // Lean's `checkNotAlreadyDeclared` (`Lean/Elab/LetRec.lean`).
        if self.env.get_const(aux).is_some() {
            return Err(ElabError::LetRecAuxAlreadyDeclared {
                name: aux.to_string(),
            });
        }
        // The same name lifted again: a retry of the same helper (its source
        // region again, or one containing it) or a second helper (a disjoint
        // region: two helpers of one name are never nested, as a helper
        // nested in another lifts under that one's name). A synthesized
        // binding without a source region is told apart at the declaration
        // boundary, by its value.
        if let Some(prev) = scope.sites.get(aux) {
            if is_source_span(*prev) && is_source_span(site.span) && disjoint(*prev, site.span) {
                return Err(ElabError::LetRecAuxAlreadyDeclared {
                    name: aux.to_string(),
                });
            }
        }
        let parent_partial = scope.parent_partial;
        let Some((lifted, captured)) = self.close_let_rec_helper(helper_ty, helper_val) else {
            if parent_partial && site.recursion == HelperRecursion::Recursive {
                return Err(ElabError::WhereLetRecUnsupported {
                    name: aux.to_string(),
                    shape: "a recursive helper of a `partial` declaration must lift to its \
                            own opaque declaration (Lean `addAndCompilePartial`), and this \
                            one could not be closed over the locals it uses; inline, it \
                            would reduce where Lean's helper does not"
                        .to_string(),
                });
            }
            return Ok(None);
        };
        // Parameter names, a prefix of the auxiliary's telescope: the
        // captured locals', then the ones its type gives its own parameters
        // (an equation-form helper's matched argument has none, and named
        // arguments then reach only the captured locals, as in Lean).
        let mut params: Vec<(Name, BinderInfo)> = captured
            .iter()
            .map(|(fvar, info)| {
                let name = self
                    .locals
                    .iter()
                    .find(|(_, f, _)| f == fvar)
                    .map(|(n, _, _)| n.name().clone())
                    .unwrap_or_else(Name::anon);
                (name, *info)
            })
            .collect();
        params.extend(site.own_params.unwrap_or_default());
        if let Some(scope) = self.let_rec_lift.scope.as_mut() {
            if !scope.lifted.contains(aux) {
                scope.lifted.push(aux.clone());
            }
            scope.sites.entry(aux.clone()).or_insert(site.span);
            if site.recursion == HelperRecursion::Recursive {
                scope.recursive.insert(aux.clone());
            }
            if params.is_empty() || params.iter().any(|(n, _)| n.is_anon()) {
                scope.params.remove(aux);
            } else {
                scope.params.insert(aux.clone(), params);
            }
        }
        Ok(Some(lifted))
    }

    /// While the body of lifted helper `fvar` elaborates, a sibling helper's
    /// use of it stands for `let aux : ty := lifted; aux`.
    pub(super) fn push_let_rec_use(&mut self, fvar: FVarId, aux: &Name, ty: &Expr, lifted: &Expr) {
        let use_term = Expr::let_named(
            aux.clone(),
            ty.clone(),
            lifted.clone(),
            Expr::bvar(0),
            false,
        );
        self.let_rec_lift.uses.insert(fvar, use_term);
    }

    pub(super) fn pop_let_rec_use(&mut self, fvar: FVarId) {
        self.let_rec_lift.uses.remove(&fvar);
    }

    /// At the declaration boundary: read every lifted helper of `scope` off
    /// the finished value `val` (and off each other's values), turn each into
    /// a declaration with the parent's universe parameters `levels`, and
    /// replace its binding by applications of the new constant.
    ///
    /// Returns the auxiliary declarations, dependencies first, and the
    /// rewritten parent value. A helper that no longer appears in its
    /// recognisable form stays inline — unless it is a recursive helper of a
    /// `partial` declaration, which is refused (module docs), as is one that
    /// does not appear at all. Two different
    /// helpers under one name are refused, as Lean refuses the second.
    pub(super) fn finish_let_rec_lifts(
        &mut self,
        scope: Option<LetRecLiftScope>,
        levels: &[Name],
        parent_modifiers: &DeclModifiers,
        val: Expr,
    ) -> Result<(Vec<ElabResult>, Expr), ElabError> {
        let scope = match scope {
            Some(scope) if !scope.lifted.is_empty() => scope,
            _ => return Ok((Vec::new(), val)),
        };
        let LetRecLiftScope {
            lifted,
            parent_partial,
            recursive,
            mut params,
            ..
        } = scope;
        let names: HashSet<Name> = lifted.into_iter().collect();
        let us: Vec<Level> = levels.iter().cloned().map(Level::param).collect();
        let mut rewriter = LiftRewriter {
            names: &names,
            us: &us,
            found: Vec::new(),
            seen: HashMap::new(),
            memo: HashMap::new(),
            conflicts: Vec::new(),
            inline: HashSet::new(),
        };
        let val = rewriter.rewrite(&val);
        if let Some(name) = rewriter.conflicts.first() {
            return Err(ElabError::LetRecAuxAlreadyDeclared {
                name: name.to_string(),
            });
        }
        if parent_partial {
            // Every recursive helper must arrive as exactly what registers:
            // found in lifted form and never left inline. One that stayed
            // inline anywhere would reduce, and one that reached the boundary
            // in NEITHER form (a finishing pass dropped or reshaped its
            // binding) would register nothing, so `parent.go` could not be
            // the opaque Lean declares. Both are refused, in name order.
            let mut unregistered: Vec<&Name> = recursive
                .iter()
                .filter(|name| {
                    rewriter.inline.contains(*name) || !rewriter.seen.contains_key(*name)
                })
                .collect();
            unregistered.sort_by_key(|name| name.to_string());
            if let Some(name) = unregistered.first() {
                return Err(ElabError::WhereLetRecUnsupported {
                    name: name.to_string(),
                    shape: "a recursive helper of a `partial` declaration must lift to its own \
                            opaque declaration (Lean `addAndCompilePartial`), and this one did \
                            not reach the declaration boundary in liftable form; inline, it \
                            would reduce where Lean's helper does not"
                        .to_string(),
                });
            }
        }
        // Lean (`getModifiersForLetRecs`) gives a helper the block's
        // `noncomputable` / `partial` / `unsafe`, and nothing else; a private
        // parent's helper is private because its name lives under the
        // parent's private name. `protected` does not carry over.
        let visibility = match parent_modifiers.visibility {
            clean_parser::Visibility::Private => clean_parser::Visibility::Private,
            _ => clean_parser::Visibility::Public,
        };
        let modifiers = DeclModifiers {
            visibility,
            is_partial: parent_modifiers.is_partial,
            is_noncomputable: parent_modifiers.is_noncomputable,
            is_unsafe: parent_modifiers.is_unsafe,
            ..DeclModifiers::default()
        };
        let mut auxiliaries = Vec::with_capacity(rewriter.found.len());
        let mut finished_params = Vec::new();
        for (name, ty, aux_val) in rewriter.found {
            self.ensure_no_residual_fvars(
                "def",
                &SurfaceName::from_name(name.clone()),
                &ty,
                Some(&aux_val),
            )?;
            if let Some(names) = params.remove(&name) {
                finished_params.push((name.clone(), names));
            }
            // A recursive helper of a `partial` declaration: an opaque whose
            // type must be inhabited (`addAndCompilePartial`).
            if parent_partial && recursive.contains(&name) {
                self.check_partial_helper(&name, &ty)?;
                auxiliaries.push(ElabResult::Opaque {
                    name,
                    universe_params: levels.to_vec(),
                    ty,
                    val: Some(aux_val),
                    modifiers,
                });
                continue;
            }
            // Lean (`pushLetRecs`): a helper whose type is a proposition is a
            // theorem, any other a definition, whatever the parent is.
            let is_prop = matches!(
                self.infer_type(&ty).map(|s| self.whnf(&s)),
                Ok(sort) if matches!(sort.kind(), ExprKind::Sort(l) if l.is_zero())
            );
            auxiliaries.push(if is_prop {
                ElabResult::Theorem {
                    name,
                    universe_params: levels.to_vec(),
                    ty,
                    proof: aux_val,
                    modifiers,
                }
            } else {
                ElabResult::Definition {
                    name,
                    universe_params: levels.to_vec(),
                    ty,
                    val: aux_val,
                    modifiers,
                }
            });
        }
        self.let_rec_lift.finished_params.extend(finished_params);
        Ok((auxiliaries, val))
    }
}

#[path = "let_rec_close.rs"]
mod close;
#[path = "let_rec_partial.rs"]
mod partial;
#[path = "let_rec_rewrite.rs"]
mod rewrite;

pub(super) use close::{helper_own_params, helper_site_span, HelperRecursion, HelperSite};
use rewrite::LiftRewriter;
#[cfg(test)]
use rewrite::{ascribe_closed, read_lifted_value};

#[cfg(test)]
#[path = "let_rec_lift_tests.rs"]
mod tests;
