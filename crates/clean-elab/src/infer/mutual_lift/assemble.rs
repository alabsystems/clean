// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Opening the members, the fixed prefix, and the assembly of one shared
//! recursor application (design §5.3 steps 1, 2, 5–7).

use clean_kernel::{BinderInfo, Expr, ExprFolder, ExprKind, FVarId, Name};
use clean_parser::SurfaceName;

use super::minors::MinorCtx;
use super::motives::{Layout, SlotPlan};
use super::replace::CallShape;
use super::slots::FamilyInfo;
use super::specialize::strip_mdata;
use super::{LiftError, PreDef};
use crate::infer::ElabCtx;

/// One opened parameter.
#[derive(Debug, Clone)]
pub(super) struct Param {
    pub(super) fvar: FVarId,
    pub(super) info: BinderInfo,
    pub(super) ty: Expr,
}

/// Every member opened over its type's `Π` telescope; the first `fixed`
/// parameters are SHARED fvars.
#[derive(Debug, Clone)]
pub(super) struct Opened {
    pub(super) params: Vec<Vec<Param>>,
    pub(super) codomains: Vec<Expr>,
    pub(super) bodies: Vec<Expr>,
    pub(super) fixed: usize,
}

/// `fun xs => body` (or `Π xs, body`) over opened parameters.
pub(super) fn abstract_params(params: &[Param], body: Expr, pi: bool) -> Expr {
    params.iter().rev().fold(body, |acc, param| {
        let abstracted = acc.abstract_fvar(param.fvar);
        if pi {
            Expr::pi(param.info, param.ty.clone(), abstracted)
        } else {
            Expr::lam(param.info, param.ty.clone(), abstracted)
        }
    })
}

/// `val a₁ … aₙ`, β-reducing the leading lambdas.
fn beta_apply(val: &Expr, args: &[Expr]) -> Expr {
    let mut cur = val.clone();
    let mut used = 0;
    while used < args.len() {
        let ExprKind::Lam(_, _, body) = cur.kind() else {
            break;
        };
        cur = body.instantiate(&args[used]);
        used += 1;
    }
    Expr::apps(cur, args[used..].iter().cloned())
}

fn pi_arity(ty: &Expr) -> usize {
    let mut n = 0;
    let mut cur = ty;
    while let ExprKind::Pi(_, _, body) = cur.kind() {
        n += 1;
        cur = body;
    }
    n
}

/// Smallest number of leading arguments any call passes unchanged.
struct FixedScan<'a> {
    members: &'a [FVarId],
    shared: &'a [FVarId],
    fixed: usize,
}

impl ExprFolder for FixedScan<'_> {
    fn fold_app(&mut self, f: &Expr, a: &Expr) -> Expr {
        let whole = Expr::app(f.clone(), a.clone());
        if let ExprKind::FVar(id) = strip_mdata(whole.get_app_fn()).kind() {
            if self.members.contains(id) {
                let args = whole.get_app_args();
                let same = args
                    .iter()
                    .zip(self.shared)
                    .take_while(|(arg, shared)| strip_mdata(arg) == &Expr::fvar(**shared))
                    .count();
                self.fixed = self.fixed.min(same);
                for arg in args {
                    let _ = self.fold_expr(arg);
                }
                return whole;
            }
        }
        Expr::app(self.fold_expr(f), self.fold_expr(a))
    }

    fn fold_fvar(&mut self, id: FVarId) -> Expr {
        if self.members.contains(&id) {
            self.fixed = 0; // an unapplied reference passes nothing
        }
        Expr::fvar(id)
    }
}

impl ElabCtx<'_> {
    /// Open every member with the first `fixed` parameters shared. Pushes
    /// locals; the caller truncates them.
    pub(super) fn open_members(&mut self, defs: &[&PreDef], fixed: usize) -> Opened {
        let mut shared: Vec<Param> = Vec::new();
        let mut opened = Opened {
            params: Vec::new(),
            codomains: Vec::new(),
            bodies: Vec::new(),
            fixed,
        };
        for def in defs {
            let mut ty = def.ty.clone();
            let mut params: Vec<Param> = Vec::new();
            for pos in 0..pi_arity(&def.ty) {
                let ExprKind::Pi(bd, dom, body) = ty.kind() else {
                    break;
                };
                let param = if pos < fixed && pos < shared.len() {
                    shared[pos].clone()
                } else {
                    let name = SurfaceName::generated_path(&format!("{}✝{pos}", def.name));
                    let fvar = self.push_local(name, dom.as_ref().clone());
                    let param = Param {
                        fvar,
                        info: bd.info,
                        ty: dom.as_ref().clone(),
                    };
                    if pos < fixed {
                        shared.push(param.clone());
                    }
                    param
                };
                ty = body.instantiate(&Expr::fvar(param.fvar));
                params.push(param);
            }
            let args: Vec<Expr> = params.iter().map(|p| Expr::fvar(p.fvar)).collect();
            opened.bodies.push(beta_apply(&def.val, &args));
            opened.codomains.push(ty);
            opened.params.push(params);
        }
        opened
    }

    /// Lean's `getFixedPrefix`: the longest prefix of parameters whose types
    /// agree across members and which every call passes unchanged.
    pub(super) fn fixed_prefix(&mut self, defs: &[&PreDef]) -> usize {
        // Types agree (opened with the same fvars).
        let mut tys: Vec<Expr> = defs.iter().map(|d| d.ty.clone()).collect();
        let mut by_type = 0;
        loop {
            let doms: Vec<(BinderInfo, Expr, Expr)> = tys
                .iter()
                .filter_map(|ty| match ty.kind() {
                    ExprKind::Pi(bd, dom, body) => {
                        Some((bd.info, dom.as_ref().clone(), body.as_ref().clone()))
                    }
                    _ => None,
                })
                .collect();
            if doms.len() != tys.len() || doms.iter().any(|d| d.1 != doms[0].1) {
                break;
            }
            let shared = Expr::fvar(self.fresh_fvar());
            tys = doms.iter().map(|d| d.2.instantiate(&shared)).collect();
            by_type += 1;
        }
        if by_type == 0 {
            return 0;
        }
        let depth = self.locals.len();
        let opened = self.open_members(defs, by_type);
        let members: Vec<FVarId> = defs.iter().map(|d| d.fvar).collect();
        let shared: Vec<FVarId> = opened.params[0][..by_type].iter().map(|p| p.fvar).collect();
        let mut scan = FixedScan {
            members: &members,
            shared: &shared,
            fixed: by_type,
        };
        for body in &opened.bodies {
            let _ = scan.fold_expr(body);
        }
        let fixed = scan.fixed;
        self.locals.truncate(depth);
        fixed
    }

    /// Build every member's value for one choice of major premises.
    /// `slots[i]` is member `i`'s slot; several members may share one.
    /// Returns closed values (up to forward locals outside the component)
    /// and each member's `(owner index, owner count)` in its slot.
    pub(super) fn assemble(
        &mut self,
        defs: &[&PreDef],
        opened: &Opened,
        fam: &FamilyInfo,
        majors: &[usize],
        slots: &[usize],
    ) -> Result<Assembled, LiftError> {
        let k = opened.fixed;
        let rest: Vec<Vec<Param>> = (0..defs.len())
            .map(|i| {
                opened.params[i]
                    .iter()
                    .enumerate()
                    .filter(|(pos, _)| *pos >= k && *pos != majors[i])
                    .map(|(_, p)| p.clone())
                    .collect()
            })
            .collect();
        // Each member's `Π rest, R` and the block's common motive universe.
        let mut body_tys = Vec::with_capacity(defs.len());
        let mut level: Option<clean_kernel::Level> = None;
        for (i, def) in defs.iter().enumerate() {
            let body_ty = abstract_params(&rest[i], opened.codomains[i].clone(), true);
            let lvl = self.infer_sort(&body_ty).map_err(|e| {
                LiftError::member(&def.name, format!("its result type has no universe: {e}"))
            })?;
            if let Some(l0) = level.clone() {
                if !self.is_def_eq(&Expr::sort(l0.clone()), &Expr::sort(lvl.clone())) {
                    return Err(LiftError::member(
                        &def.name,
                        format!("its result lives in `Sort {lvl}` but a sibling's in `Sort {l0}`: the members must share one motive universe"),
                    ));
                }
            } else {
                level = Some(lvl);
            }
            body_tys.push(body_ty);
        }
        let (Some(level), Some(first_body)) = (level, body_tys.first().cloned()) else {
            return Err(LiftError::block("the block has no members".to_string()));
        };
        if !fam.has_motive_level && !self.is_def_eq(&Expr::sort(level.clone()), &Expr::prop()) {
            return Err(LiftError::block(format!(
                "`{}` eliminates only into `Prop`",
                fam.key.name
            )));
        }
        let punit = self
            .punit_dummy_at_result_sort(&first_body)
            .map_err(|e| LiftError::block(format!("{e}")))?;
        let layout = Layout {
            defs,
            opened,
            majors,
            slots,
            rest: &rest,
            body_tys: &body_tys,
        };
        let motives = self.build_motives(&layout, fam, &level, punit.as_ref().map(|p| &p.0))?;
        // The family recursor instantiated through its motives.
        let rec0_name = fam.key.name.clone().str("rec");
        let rec0 = self
            .env
            .get_recursor(&rec0_name)
            .cloned()
            .ok_or_else(|| LiftError::block(format!("`{rec0_name}` vanished")))?;
        let rec_levels = self.rec_levels(rec0.level_params.len(), &fam.key, level.clone());
        let mut cursor = rec0
            .type_
            .instantiate_level_params_direct(&rec0.level_params, &rec_levels);
        for val in fam.key.indparams.iter().chain(&motives.motives) {
            let ExprKind::Pi(_, _, body) = cursor.kind() else {
                return Err(LiftError::block("malformed recursor type".to_string()));
            };
            cursor = body.instantiate(val);
        }
        let owner_of = |i: usize| -> (usize, usize) {
            match &motives.plans[slots[i]] {
                SlotPlan::Owned { owners } => (
                    owners.iter().position(|o| *o == i).unwrap_or(0),
                    owners.len(),
                ),
                _ => (0, 1),
            }
        };
        let shapes: Vec<CallShape> = defs
            .iter()
            .enumerate()
            .map(|(i, def)| CallShape {
                name: def.name.clone(),
                fvar: def.fvar,
                arity: opened.params[i].len(),
                major: majors[i],
                slot: slots[i],
                owner_index: owner_of(i).0,
                owner_count: owner_of(i).1,
            })
            .collect();
        let fixed: Vec<FVarId> = opened.params[0][..k].iter().map(|p| p.fvar).collect();
        let ctx = MinorCtx {
            layout: &layout,
            motives: &motives,
            shapes: &shapes,
            fixed: &fixed,
            unit: punit.as_ref().map(|(_, unit)| unit),
        };
        let mut minors = Vec::with_capacity(fam.minors.len());
        for shape in &fam.minors {
            let ExprKind::Pi(_, minor_ty, body) = cursor.kind() else {
                return Err(LiftError::block("malformed recursor minors".to_string()));
            };
            let minor = self.build_minor(&ctx, shape, minor_ty)?;
            cursor = body.instantiate(&minor);
            minors.push(minor);
        }
        // Each member: `fun params => (T.rec_k indparams motives minors major).j rest`.
        let mut values = Vec::with_capacity(defs.len());
        for (i, def) in defs.iter().enumerate() {
            let rec_name: Name = fam.rec_by_slot[slots[i]].clone().ok_or_else(|| {
                LiftError::member(
                    &def.name,
                    "the kernel generated no recursor for its slot".to_string(),
                )
            })?;
            let mut app = Expr::apps(
                Expr::const_(rec_name, rec_levels.clone()),
                fam.key
                    .indparams
                    .iter()
                    .chain(&motives.motives)
                    .chain(&minors)
                    .cloned(),
            );
            app = Expr::app(app, Expr::fvar(opened.params[i][majors[i]].fvar));
            let (index, count) = owner_of(i);
            app = motives.kind.project(app, index, count);
            app = Expr::apps(app, rest[i].iter().map(|p| Expr::fvar(p.fvar)));
            values.push(abstract_params(&opened.params[i], app, false));
        }
        Ok(Assembled {
            owners: (0..defs.len()).map(owner_of).collect(),
            values,
        })
    }
}

/// One lowering: each member's value and `(owner index, owner count)`.
pub(super) struct Assembled {
    pub(super) values: Vec<Expr>,
    pub(super) owners: Vec<(usize, usize)>,
}
