// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural lowering of a `mutual` block's recursive members onto ONE shared
//! recursor application (gap G23, ledger class (92); design
//! `designs/2026-10-08-mutual-nested-recursion.md`).
//!
//! `elab_mutual` elaborates every member against forward-declared locals
//! (pass 2) — the PRE-DEFINITIONS. [`ElabCtx::lower_mutual_predefs`] splits
//! the block into strongly connected components of its call graph:
//!
//! * a non-recursive component keeps the old local→constant replacement, now
//!   registered in dependency order;
//! * a recursive component is LIFTED: one major premise per member, all in one
//!   recursor family, one motive per slot (the owner's type with its major
//!   abstracted; a `PProd`/`And` tuple of them for a slot several members
//!   own; the tuple of its fields' hypotheses for a transparent intermediate
//!   such as `String × T`; `PUnit` for any other unowned slot), and each
//!   minor premise built by
//!   substituting the slot's constructor into the owner's body, contracting the
//!   case splits that become redexes, and replacing each sibling call on a
//!   constructor field by that field's induction hypothesis. Each member's
//!   value is then `fun params => T.rec_k indparams motives minors major rest`.
//!
//! Every value is closed, kernel-checked here before anything registers and
//! again by `add_decl`; a block the lift cannot lower is refused whole with a
//! structured `Unsupported` naming the member, the call and the reason. No
//! `WellFounded`, no axiom, no `sorry`, no unchecked declaration.

mod arms;
mod assemble;
mod eqns;
mod lift;
mod minors;
mod motives;
mod registry;
mod replace;
mod scc;
mod slots;
mod specialize;
mod tuple;

pub(crate) use arms::PendingEqLemma;
pub(crate) use registry::{mutual_lift_idx, MutualLiftEntry, MutualLiftState};

use clean_kernel::{Expr, ExprFolder, FVarId, Name};

use self::replace::CallRefusal;
use super::ElabCtx;
use crate::ElabError;

/// Combinations of major premises tried before the block is refused.
const MAX_MAJOR_COMBINATIONS: usize = 64;

/// One member as pass 2 left it: siblings and itself are forward locals.
#[derive(Debug, Clone)]
pub(in crate::infer) struct PreDef {
    pub(in crate::infer) name: Name,
    pub(in crate::infer) fvar: FVarId,
    pub(in crate::infer) is_theorem: bool,
    pub(in crate::infer) universe_params: Vec<Name>,
    pub(in crate::infer) ty: Expr,
    pub(in crate::infer) val: Expr,
    /// Explicit structural major in full parameter space, including auto-implicits.
    pub(in crate::infer) structural_major: Option<usize>,
}

/// A member ready to register: index into the block, closed type and value.
#[derive(Debug, Clone)]
pub(in crate::infer) struct Lowered {
    pub(in crate::infer) index: usize,
    /// For a lifted member, the union of its component's lists: every
    /// member's value carries every member's body.
    pub(in crate::infer) universe_params: Vec<Name>,
    pub(in crate::infer) ty: Expr,
    pub(in crate::infer) val: Expr,
}

/// Why a lift attempt failed (rendered by [`ElabCtx::render_lift_error`]).
#[derive(Debug, Clone)]
enum LiftError {
    Block(String),
    Member { name: Name, reason: String },
    Call { caller: Name, refusal: CallRefusal },
}

impl LiftError {
    fn block(reason: String) -> Self {
        Self::Block(reason)
    }
    fn member(name: &Name, reason: String) -> Self {
        Self::Member {
            name: name.clone(),
            reason,
        }
    }
}

/// How one member of a lifted component was compiled.
#[derive(Clone)]
struct LiftedMember {
    value: Expr,
    recursor: Name,
    slot: usize,
    major: usize,
    rest: Vec<usize>,
    fixed: usize,
    owner_index: usize,
    owner_count: usize,
    /// Per-constructor equations over forward locals (closed statements;
    /// empty for a theorem or when synthesis declined).
    equations: Vec<Expr>,
}

/// Replace every forward local by its member constant.
pub(super) fn replace_forward_locals(defs: &[PreDef], expr: &Expr) -> Expr {
    struct Folder<'b>(&'b [PreDef]);
    impl ExprFolder for Folder<'_> {
        fn fold_fvar(&mut self, id: FVarId) -> Expr {
            match self.0.iter().find(|d| d.fvar == id) {
                Some(def) => Expr::const_(
                    def.name.clone(),
                    def.universe_params
                        .iter()
                        .map(|n| clean_kernel::Level::param(n.clone()))
                        .collect::<Vec<_>>(),
                ),
                None => Expr::fvar(id),
            }
        }
    }
    Folder(defs).fold_expr(expr)
}

fn trace_on() -> bool {
    std::env::var_os("CLEAN_MUTUAL_LIFT_TRACE").is_some()
}

impl ElabCtx<'_> {
    /// Lower a `mutual` block's pre-definitions: SCCs in dependency order,
    /// recursive ones lifted. Lifted members' registry entries are queued for
    /// registration after the members themselves register.
    pub(in crate::infer) fn lower_mutual_predefs(
        &mut self,
        defs: &[PreDef],
    ) -> Result<Vec<Lowered>, ElabError> {
        let forward: Vec<FVarId> = defs.iter().map(|d| d.fvar).collect();
        if trace_on() {
            for def in defs {
                eprintln!(
                    "mutual-lift: {} universe params {:?}",
                    def.name, def.universe_params
                );
            }
        }
        let edges: Vec<Vec<usize>> = defs
            .iter()
            .map(|def| {
                let mut out: Vec<usize> = scc::mentioned_members(&forward, &[&def.ty, &def.val])
                    .into_iter()
                    .collect();
                out.sort_unstable();
                out
            })
            .collect();
        let components = scc::components_in_dependency_order(&edges);
        // Lift every recursive component first: its values mention other
        // components only through their forward locals.
        let mut lifted: Vec<Option<LiftedMember>> = vec![None; defs.len()];
        for component in components.iter().filter(|c| c.recursive) {
            let members: Vec<&PreDef> = component.members.iter().map(|i| &defs[*i]).collect();
            let values = self.lift_recursive_scc(&members, &forward)?;
            for (index, member) in component.members.iter().zip(values) {
                lifted[*index] = Some(member);
            }
        }
        // A lifted member's value holds all of its component's bodies, so the
        // component shares ONE universe-parameter list: the levels its
        // (canonicalized) types and values use — pass 1's lists carry every
        // level minted so far, and pass 2 can leave a proof's level
        // unassigned. References to a member are built from that list below.
        let mut defs: Vec<PreDef> = defs.to_vec();
        for component in components.iter().filter(|c| c.recursive) {
            let mut used: Vec<Name> = Vec::new();
            for i in &component.members {
                let ty = self.metas.canonicalize_levels_in_expr(&defs[*i].ty);
                defs[*i].ty = ty;
                if let Some(member) = lifted[*i].as_mut() {
                    member.value = self.metas.canonicalize_levels_in_expr(&member.value);
                    super::elab_decl_value::collect_def_level_params(&member.value, &mut used);
                }
                super::elab_decl_value::collect_def_level_params(&defs[*i].ty, &mut used);
            }
            for i in &component.members {
                defs[*i].universe_params = used.clone();
            }
        }
        let defs = defs.as_slice();
        let mut lowered = Vec::with_capacity(defs.len());
        for component in &components {
            if trace_on() {
                let names: Vec<String> = component
                    .members
                    .iter()
                    .map(|i| defs[*i].name.to_string())
                    .collect();
                eprintln!(
                    "mutual-lift: component [{}] recursive={}",
                    names.join(", "),
                    component.recursive
                );
            }
            if !component.recursive {
                let def = &defs[component.members[0]];
                lowered.push(Lowered {
                    index: component.members[0],
                    universe_params: def.universe_params.clone(),
                    ty: replace_forward_locals(defs, &def.ty),
                    val: replace_forward_locals(defs, &def.val),
                });
                continue;
            }
            let block: Vec<Name> = component
                .members
                .iter()
                .map(|i| defs[*i].name.clone())
                .collect();
            for index in &component.members {
                let def = &defs[*index];
                let Some(member) = lifted[*index].take() else {
                    return Err(ElabError::InternalInvariant(format!(
                        "mutual lift: `{}` has no lowered value",
                        def.name
                    )));
                };
                let val = replace_forward_locals(defs, &member.value);
                if trace_on() {
                    eprintln!(
                        "mutual-lift: {}.{{{:?}}} := {val}  [major param {}, slot {}, {}]",
                        def.name, def.universe_params, member.major, member.slot, member.recursor
                    );
                }
                self.mutual_lift_entries.push(MutualLiftEntry {
                    member: def.name.clone(),
                    block: block.clone(),
                    recursor: member.recursor,
                    slot: member.slot,
                    owner_index: member.owner_index,
                    owner_count: member.owner_count,
                    fixed_arity: member.fixed,
                    major_param: member.major,
                    rest_params: member.rest,
                    predef: replace_forward_locals(defs, &def.val),
                    equations: member
                        .equations
                        .iter()
                        .map(|eq| {
                            let eq = self.metas.canonicalize_levels_in_expr(eq);
                            replace_forward_locals(defs, &eq)
                        })
                        .collect(),
                });
                lowered.push(Lowered {
                    index: *index,
                    universe_params: def.universe_params.clone(),
                    ty: replace_forward_locals(defs, &def.ty),
                    val,
                });
            }
        }
        Ok(lowered)
    }

    /// The registry entries of the members lifted so far (drained).
    pub(crate) fn take_mutual_lift_entries(&mut self) -> Vec<MutualLiftEntry> {
        std::mem::take(&mut self.mutual_lift_entries)
    }

    fn render_lift_error(&self, members: &[&PreDef], err: LiftError) -> ElabError {
        let block: Vec<String> = members.iter().map(|m| format!("`{}`", m.name)).collect();
        let what = match err {
            LiftError::Block(reason) => reason,
            LiftError::Member { name, reason } => format!("member `{name}`: {reason}"),
            LiftError::Call { caller, refusal } => format!(
                "in `{caller}`, the recursive call `{}` to `{}` cannot be lowered: {}",
                self.display_with_locals(&refusal.call),
                refusal.callee,
                refusal.reason
            ),
        };
        ElabError::Unsupported {
            feature: format!(
                "mutual structural recursion (block {}): {what}. Clean compiles a recursive \
                 `mutual` block onto the shared recursor of the inductive family it recurses \
                 over, and every recursive call must be on a constructor field of the major \
                 premise; Lean 4.8 compiles such blocks by well-founded recursion instead \
                 (gap G23, designs/2026-10-08-mutual-nested-recursion.md)",
                block.join(", ")
            ),
        }
    }

    /// `expr` with every local named by its binder name, for messages.
    fn display_with_locals(&self, expr: &Expr) -> String {
        struct Namer<'b>(&'b [(clean_parser::SurfaceName, FVarId, Expr)]);
        impl ExprFolder for Namer<'_> {
            fn fold_fvar(&mut self, id: FVarId) -> Expr {
                match self.0.iter().rev().find(|(_, fvar, _)| *fvar == id) {
                    Some((name, _, _)) => {
                        Expr::const_(Name::from_string(&name.to_string()), vec![])
                    }
                    None => Expr::fvar(id),
                }
            }
        }
        format!("{}", Namer(self.locals.as_slice()).fold_expr(expr))
    }
}
