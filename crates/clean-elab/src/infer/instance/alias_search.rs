// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instance search across reducible class ALIASES — the resolver half of
//! [`crate::instance_alias`].
//!
//! Lean indexes every instance by its type after a reducible ∀-telescope
//! (`Lean/Meta/Instances.lean`, `mkInstanceKey`) and opens every goal the same
//! way before lookup (`Lean/Meta/SynthInstance.lean`, `getInstances` and
//! `preprocess`), so the alias an instance or a goal is SPELLED with never
//! decides which instances can meet. Clean files by the spelled head, so the
//! two directions need a bridge each:
//!
//! - a FINAL-class goal (`Decidable (a < b)`) must see the candidates filed
//!   under the aliases that unfold to it (`LinearOrder.toDecidableLT`, filed
//!   under `DecidableLT`) — [`ElabCtx::alias_candidate_order`];
//! - an ALIAS goal (`DecidableEq α`, `DecidablePred p`) whose own bucket has no
//!   answer must be opened to its final-class telescope and searched there
//!   (`Classical.propDecidable`, a local `[∀ a b, Decidable (a = b)]`) —
//!   [`ElabCtx::resolve_alias_goal_by_opening`].

use super::super::ElabCtx;
use crate::unify::MetaState;
use clean_kernel::name::NameInner;
use clean_kernel::{Expr, ExprKind, FVarId, Name};

/// Cap on the ∀-telescope opened to read an alias-filed instance's
/// final-class conclusion. `LinearOrder.toDecidableLT` needs four
/// (`{α} [self] a b`); a longer telescope is read as "anything".
const MAX_ALIAS_TELESCOPE: usize = 32;

/// The head of an instance-goal argument after the normalisation the
/// elaborator applies to it (instance transparency), for the discrimination
/// check. A structure projection reads the same whether it is still spelled
/// through its projection function (`LT.lt`) or already reduced to a
/// primitive projection (`inst.1`): Clean's `whnf` unfolds the function even
/// where the projection is stuck on a local instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::infer) enum HeadKey {
    /// A constant that is not a projection function.
    Const(Name),
    /// Field `idx` of structure `S`, by function or by primitive projection.
    Proj(Name, u32),
    /// A ∀ / →.
    Arrow,
    /// A local of the declaration being elaborated.
    Local(FVarId),
    /// A metavariable.
    Open,
    /// Anything else (a sort, a λ, a literal).
    Other,
}

impl HeadKey {
    fn is_rigid(&self) -> bool {
        matches!(self, Self::Const(_) | Self::Proj(..) | Self::Arrow)
    }
}

impl std::fmt::Display for HeadKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Const(name) => write!(f, "{name}"),
            Self::Proj(structure, idx) => write!(f, "{structure}.{idx}"),
            Self::Arrow => write!(f, "→"),
            Self::Local(id) => write!(f, "fvar#{}", id.as_u64()),
            Self::Open => write!(f, "?"),
            Self::Other => write!(f, "*"),
        }
    }
}

/// `[k₁, k₂, …]` for the instance trace.
fn render_keys(keys: &[HeadKey]) -> String {
    let parts: Vec<String> = keys.iter().map(ToString::to_string).collect();
    format!("[{}]", parts.join(", "))
}

/// Discrimination check: `false` only when both heads are rigid and differ,
/// which is exactly when Lean's `DiscrTree.getUnify` cannot return the
/// candidate for this goal. A candidate's own local or metavariable (a binder
/// of its telescope) matches anything; so does a goal still open there.
fn compatible(inst: &HeadKey, goal: &HeadKey) -> bool {
    if !inst.is_rigid() {
        return true;
    }
    match goal {
        HeadKey::Local(_) => false,
        g if g.is_rigid() => inst == g,
        _ => true,
    }
}

impl<'a> ElabCtx<'a> {
    /// `(S, idx)` when `name` is the projection function of field `idx` of the
    /// structure `S` (`LT.lt` ⟶ `(LT, 0)`).
    fn projection_of(&self, name: &Name) -> Option<(Name, u32)> {
        // Split structurally (`S.f` is the parent `S` and the component `f`);
        // a rendered name cannot tell `A.b` from the single component `«A.b»`.
        let NameInner::Str(structure, field) = name.inner() else {
            return None;
        };
        let structure = structure.as_ref().clone();
        let fields = self.env.get_structure_field_names(&structure)?;
        let idx = fields
            .iter()
            .position(|f| matches!(f.inner(), NameInner::Str(_, last) if last == field))?;
        Some((structure, u32::try_from(idx).ok()?))
    }

    /// The [`HeadKey`] of `e` read at instance transparency — the form
    /// `elab_app` has already put a `Sort`-valued argument feeding an
    /// instance-implicit parameter into (`needsDec (a < b)` asks for
    /// `Decidable (fooLt a b)`), so both sides of the comparison are read at it.
    ///
    /// A projection stuck on a METAVARIABLE structure (`?inst.1`, a
    /// candidate's own instance binder) is `Open`: once the binder is solved
    /// the projection may reduce to any head, exactly as the goal's own did.
    fn head_key(&self, e: &Expr) -> HeadKey {
        let e = self.whnf_instances(e);
        let is_meta_headed = |x: &Expr| matches!(x.get_app_fn().kind(), ExprKind::FVar(id) if MetaState::from_fvar(*id).is_some());
        match e.get_app_fn().kind() {
            ExprKind::Const(name, _) => match self.projection_of(name) {
                Some((structure, idx)) => {
                    let self_arg = self
                        .env
                        .get_inductive(&structure)
                        .and_then(|ind| e.get_app_args().get(ind.num_params as usize).copied());
                    if self_arg.is_none_or(is_meta_headed) {
                        HeadKey::Open
                    } else {
                        HeadKey::Proj(structure, idx)
                    }
                }
                None => HeadKey::Const(name.clone()),
            },
            ExprKind::Proj(_, _, inner) if is_meta_headed(inner) => HeadKey::Open,
            ExprKind::Proj(structure, idx, _) => HeadKey::Proj(structure.clone(), *idx),
            ExprKind::Pi(..) => HeadKey::Arrow,
            ExprKind::FVar(id) if MetaState::from_fvar(*id).is_some() => HeadKey::Open,
            ExprKind::FVar(id) => HeadKey::Local(*id),
            _ => HeadKey::Other,
        }
    }

    /// The [`HeadKey`] of each argument of the final-class application the
    /// alias-filed instance `bucket[idx]` unfolds to, with its telescope opened
    /// over fresh metavariables (rolled back). Empty when the telescope does
    /// not reach `final_class`, which the caller reads as "anything". Cached
    /// for the declaration.
    fn alias_instance_heads(
        &mut self,
        bucket: &Name,
        idx: usize,
        final_class: &Name,
    ) -> Vec<HeadKey> {
        if let Some(heads) = self.alias_instance_heads.get(&(bucket.clone(), idx)) {
            return heads.clone();
        }
        let inst_type = self.instances.get_instances(bucket)[idx].type_.clone();
        let is_final = |e: &Expr| {
            crate::instances::extract_class_app(e).is_some_and(|(n, _)| n == *final_class)
        };
        self.metas.push_scope();
        let mut cursor = if is_final(&inst_type) {
            inst_type
        } else {
            self.whnf(&inst_type)
        };
        let mut opened = 0;
        while let ExprKind::Pi(_, dom, body) = cursor.kind() {
            if opened >= MAX_ALIAS_TELESCOPE {
                break;
            }
            let dom = self.metas.instantiate(dom);
            let meta = self.fresh_meta(dom);
            let next = self.metas.instantiate(&body.instantiate(&meta));
            cursor = if is_final(&next) {
                next
            } else {
                self.whnf(&next)
            };
            opened += 1;
        }
        let heads = match crate::instances::extract_class_app(&cursor) {
            Some((class, args)) if class == *final_class => {
                args.iter().map(|arg| self.head_key(arg)).collect()
            }
            _ => Vec::new(),
        };
        self.metas.pop_scope();
        self.alias_instance_heads
            .insert((bucket.clone(), idx), heads.clone());
        heads
    }

    /// Candidates filed under an ALIAS of `class_name` that Lean's
    /// discrimination tree would return for the goal `class_name goal_args`,
    /// as `(bucket, index)` pairs in descending priority.
    ///
    /// # What decides admission
    ///
    /// An alias whose own unfolding fixes a STABLE head at some position
    /// (`DecidableEq` puts the inductive `Eq`) is admitted or skipped as a
    /// whole bucket by that head. Everywhere else the head is read per
    /// instance ([`Self::alias_instance_heads`]): `LinearOrder.toDecidableLT`
    /// reads as the `LT` projection, a `DecidableLT Foo` instance whose `<` is
    /// `fooLt` as `fooLt`. A candidate is skipped only when the goal and the
    /// candidate carry rigid heads that differ. Admission is only the right to
    /// be TRIED: every admitted candidate still goes through the full
    /// candidate loop (freshened levels, telescope, unification, sub-goals,
    /// hygiene) and the kernel re-checks the term.
    ///
    /// # Why the prefilter is not optional
    ///
    /// A `Decidable` goal is the most common instance goal there is, and the
    /// `DecidableEq` bucket of a Mathlib environment holds well over a thousand
    /// instances. Admitting them unfiltered would spend the per-query
    /// candidate budget (`INSTANCE_SEARCH_BUDGET`) on candidates that cannot
    /// match, and turn deep searches that succeed today into failures.
    ///
    /// `skip_dec_eq` drops the `DecidableEq` alias when the caller's `decEq`
    /// bridge already resolved `DecidableEq α` for this very goal (a
    /// `Decidable (@Eq α a b)`): that bridge searched the same bucket, at the
    /// alias level.
    pub(super) fn alias_candidate_order(
        &mut self,
        class_name: &Name,
        goal_args: &[Expr],
        skip_dec_eq: bool,
    ) -> Vec<(Name, usize)> {
        let aliases = self.instances.aliases_of(class_name).to_vec();
        if aliases.is_empty() {
            return Vec::new();
        }
        let goal_keys: Vec<HeadKey> = goal_args.iter().map(|a| self.head_key(a)).collect();
        super::inst_trace(|| {
            let buckets: Vec<String> = aliases.iter().map(|a| a.name.to_string()).collect();
            format!(
                "{class_name}: alias buckets [{}], goal heads {}",
                buckets.join(", "),
                render_keys(&goal_keys)
            )
        });
        // A goal still open everywhere (`Decidable ?p`) is postponed by the
        // candidate loop's open-input rule for every rigid candidate; the alias
        // buckets can add nothing to it.
        if goal_keys.iter().all(|k| *k == HeadKey::Open) {
            return Vec::new();
        }
        let mut admitted: Vec<(u32, Name, usize)> = Vec::new();
        for alias in aliases {
            if skip_dec_eq && alias.name == Name::anon().str("DecidableEq") {
                continue;
            }
            if alias.heads.len() != goal_keys.len() {
                continue;
            }
            // The alias's own heads, where they survive every normalisation.
            let stable: Vec<Option<HeadKey>> = alias
                .heads
                .iter()
                .map(|h| {
                    h.as_ref()
                        .filter(|c| crate::instance_alias::is_stable_head(self.env, c))
                        .map(|c| HeadKey::Const(c.clone()))
                })
                .collect();
            if !stable
                .iter()
                .zip(&goal_keys)
                .all(|(h, g)| h.as_ref().is_none_or(|h| compatible(h, g)))
            {
                continue;
            }
            // Read the instances' own heads only where the alias does not fix
            // a stable one and the goal can reject.
            let per_instance = stable
                .iter()
                .zip(&goal_keys)
                .any(|(h, g)| h.is_none() && (g.is_rigid() || matches!(g, HeadKey::Local(_))));
            let count = self.instances.get_instances(&alias.name).len();
            for idx in 0..count {
                let (name, priority) = {
                    let inst = &self.instances.get_instances(&alias.name)[idx];
                    (inst.name.clone(), inst.priority)
                };
                if !self.instance_visible(&name) {
                    continue;
                }
                if per_instance {
                    let heads = self.alias_instance_heads(&alias.name, idx, class_name);
                    super::inst_trace(|| {
                        format!("alias candidate {name}: heads {}", render_keys(&heads))
                    });
                    if heads.len() == goal_keys.len()
                        && !heads.iter().zip(&goal_keys).all(|(h, g)| compatible(h, g))
                    {
                        continue;
                    }
                }
                admitted.push((priority, alias.name.clone(), idx));
            }
        }
        // Stable: within one priority, buckets keep their table order.
        admitted.sort_by_key(|(priority, _, _)| std::cmp::Reverse(*priority));
        admitted
            .into_iter()
            .map(|(_, bucket, idx)| (bucket, idx))
            .collect()
    }

    /// Interleave the goal class's own ordered candidates with the admitted
    /// alias candidates by priority, the class's own first within a tier.
    /// Both inputs are already in descending priority.
    pub(super) fn merge_candidate_orders(
        &self,
        class_name: &Name,
        own: Vec<usize>,
        aliased: Vec<(Name, usize)>,
    ) -> Vec<(Name, usize)> {
        if aliased.is_empty() {
            return own
                .into_iter()
                .map(|idx| (class_name.clone(), idx))
                .collect();
        }
        let priority_of =
            |bucket: &Name, idx: usize| self.instances.get_instances(bucket)[idx].priority;
        let mut merged = Vec::with_capacity(own.len() + aliased.len());
        let mut pending = aliased.into_iter().peekable();
        for idx in own {
            let own_priority = priority_of(class_name, idx);
            while let Some(next) = pending.next_if(|(b, i)| priority_of(b, *i) > own_priority) {
                merged.push(next);
            }
            merged.push((class_name.clone(), idx));
        }
        merged.extend(pending);
        merged
    }

    /// An ALIAS goal, opened the way Lean opens every goal
    /// (`forallTelescopeReducing` in `SynthInstance.lean`'s `preprocess` /
    /// `getInstances`), after its own bucket, the local instances and both
    /// telescope fallbacks all returned `None`.
    ///
    /// # The residue this closes
    ///
    /// `resolve_instance_with_depth` keeps a goal un-whnf'd when its head is a
    /// registered class, so the alias-filed instances meet it at the alias
    /// level. That is also what shuts it off from every instance of the class
    /// it unfolds to: `DecidablePred p`, `DecidableRel r` and `DecidableEq α`
    /// never reach `Classical.propDecidable : (a : Prop) → Decidable a`
    /// (`Mathlib/Logic/Basic.lean`: `Classical.decPred`, `decRel`, `decEq`,
    /// each `by infer_instance` inside `namespace Classical`), and
    /// `DecidableLE α := open scoped Classical in inferInstance` fails, while
    /// the pinned Lean elaborates every one of them to
    /// `fun a … => Classical.propDecidable (…)`.
    ///
    /// # Why it cannot admit a wrong candidate
    ///
    /// - It runs only after every other path returned `None`, so it adds
    ///   resolutions and never changes one.
    /// - It unfolds only a REDUCIBLE definition that is a registered class — the
    ///   transparency Lean's telescope uses — and the opened goal goes through
    ///   [`Self::resolve_pi_goal_by_abstraction`] with its ground-goal and
    ///   instance-binder refusals intact, or, for a non-Π synonym, through the
    ///   ordinary search one level deeper.
    /// - Termination: the conclusion search that can re-raise the alias goal
    ///   (`Decidable (a = b)` → the `decEq` bridge → `DecidableEq α`) meets it
    ///   on the active goal path and fails there.
    /// - The emitted term is kernel-re-checked exactly as before.
    pub(super) fn resolve_alias_goal_by_opening(
        &mut self,
        goal_ty: &Expr,
        depth: usize,
        goal_path: &mut Vec<String>,
        strict: bool,
    ) -> Option<Expr> {
        let (head, _) = crate::instances::extract_class_app(goal_ty)?;
        if !self.instances.is_class(&head)
            || !crate::instance_alias::is_reducible_definition(self.env, &head)
        {
            return None;
        }
        let opened = self.whnf(goal_ty);
        let opened = self.metas.instantiate(&opened);
        if matches!(opened.kind(), ExprKind::Pi(..)) {
            let opened_is_ground = !self.has_metavars(&opened);
            return self.resolve_pi_goal_by_abstraction(
                &opened,
                opened_is_ground,
                depth,
                goal_path,
                strict,
            );
        }
        // A class SYNONYM (`abbrev C' α := C α`): search the class it names.
        let (opened_head, _) = crate::instances::extract_class_app(&opened)?;
        if opened_head == head {
            return None;
        }
        self.resolve_instance_with_depth(&opened, depth + 1, goal_path, strict)
    }
}
