// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge-lemma synthesis for nested-local lifting (rung P3 of
//! `designs/2026-07-29-rocq-features-into-clean.md` §B).
//!
//! For every lifted family `_lifted.C_k` the lift replaced a local-capturing
//! occurrence `C A[ℓ…]` with the specialized family. This module synthesizes
//! the kernel-checked equivalence back to the USER'S ORIGINAL SPELLING:
//!
//! ```text
//! _lifted.C_k.bridge_mp  : ∀ ℓ… idx…, _lifted.C_k ℓ… idx… → C A[ℓ…] idx…
//! _lifted.C_k.bridge_mpr : ∀ ℓ… idx…, C A[ℓ…] idx… → _lifted.C_k ℓ… idx…
//! _lifted.C_k.bridge     : ∀ ℓ… idx…, _lifted.C_k ℓ… idx… ↔ C A[ℓ…] idx…
//! ```
//!
//! Proof mechanism (no propext, no congruence, no funext — every obligation
//! is pure beta, closed by the kernel's own `is_def_eq` at `add_decl`):
//! - `bridge_mp` is ONE application of the lifted block's mutual recursor,
//!   choosing each aux family's motive to be its ORIGINAL container spelling
//!   (the IH then hands exactly the original-side proposition at every
//!   rewritten field position) and each user member's motive to rebuild
//!   itself.
//! - `bridge_mpr` applies the CONTAINER's recursor at the capturing
//!   instantiation; fields the lift rewrote to a DIFFERENT family transport
//!   through that family's `bridge_mpr`, so the lemmas are emitted in
//!   reverse topological order of the cross-family reference graph.
//!
//! Trust posture: identical to the lift — non-trust-bearing synthesis; every
//! emitted declaration is an ordinary `Declaration::Theorem` the caller
//! registers through the checked `add_decl` path.
//!
//! Failure split (consumed by the elaborator retry):
//! - [`BridgeOutcome::OutOfScope`] — a declared v1 limitation (cyclic
//!   capture chain, non-head block occurrence in a field, missing container
//!   recursor, missing `Iff`, name collision). The lift stands WITHOUT
//!   bridges; skipping is additive, never a soundness gap.
//! - [`LocalLiftBridgeError`] — synthesis invariant violations; the caller
//!   rolls back the whole retry (evidence of a bug, fail-closed).

use crate::expr::{BinderInfo, Expr, ExprKind, FVarId};
use crate::inductive::{mentions_name, InductiveDecl, RecursorArgOrder};
use crate::level::Level;
use crate::name::Name;

use super::decl_builder::EnvDeclBuilder;
use super::inductive_local_lift::LiftedFamilyInfo;
use super::rec_apply::{close_lams, close_pis, walk_telescope, RecApply};
use super::types::Declaration;
use super::Environment;

/// Result of bridge synthesis.
#[derive(Debug)]
#[non_exhaustive]
pub enum BridgeOutcome {
    /// The bridge theorems, in registration order (all `bridge_mp`s, then
    /// `bridge_mpr`s in reverse topological order, then the `bridge` iffs).
    Bridges(Vec<Declaration>),
    /// A declared v1 limitation; the lift stands without bridges.
    OutOfScope {
        /// Stable human-readable reason for diagnostics.
        reason: String,
    },
}

/// Synthesis invariant violations (caller must roll back — Class B).
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum LocalLiftBridgeError {
    /// The synthesizer's own coherence checks failed.
    #[error("nested-local lift bridge synthesis invariant violated: {0}")]
    Invariant(String),
}

fn inv(msg: impl Into<String>) -> LocalLiftBridgeError {
    LocalLiftBridgeError::Invariant(msg.into())
}

/// The forall-telescope of one family's bridge statements: the ℓ+idx binders
/// walked off `aux_type` as fresh locals, plus the two statement sides.
struct FamilyTele {
    b: EnvDeclBuilder,
    /// `(id, fvar, ty)` in telescope order (ℓ first, then idx).
    binders: Vec<(FVarId, Expr, Expr)>,
    /// `_lifted.C_k ℓ… idx…`
    lhs: Expr,
    /// `C A[ℓ…] idx…` — the original spelling.
    rhs: Expr,
    /// The container param instantiation at the ℓ fvars.
    a_inst: Vec<Expr>,
}

fn bridge_names(aux: &Name) -> (Name, Name, Name) {
    (
        Name::from_string(&format!("{aux}.bridge_mp")),
        Name::from_string(&format!("{aux}.bridge_mpr")),
        Name::from_string(&format!("{aux}.bridge")),
    )
}

impl Environment {
    /// Synthesize the bridge theorems for a REGISTERED lifted block.
    ///
    /// `decl` is the ORIGINAL (pre-lift) declaration — its member names,
    /// together with the family names, form the block-member set the field
    /// scanner and the proof builders reason about. Read-only: the caller
    /// registers the returned declarations through the checked path.
    ///
    /// # Errors
    ///
    /// [`LocalLiftBridgeError::Invariant`] on synthesis coherence failures
    /// (caller must roll back). Declared v1 limitations come back as
    /// `Ok(BridgeOutcome::OutOfScope)` instead.
    pub fn synthesize_local_lift_bridges(
        &self,
        decl: &InductiveDecl,
        families: &[LiftedFamilyInfo],
    ) -> Result<BridgeOutcome, LocalLiftBridgeError> {
        // ── Presence probes (declared limitations → OutOfScope) ────────────
        if self.get_const(&Name::from_string("Iff")).is_none()
            || self.get_const(&Name::from_string("Iff.intro")).is_none()
        {
            return Ok(BridgeOutcome::OutOfScope {
                reason: "Iff/Iff.intro are not registered in this environment".to_string(),
            });
        }
        for f in families {
            let crec = Name::from_string(&format!("{}.rec", f.container));
            match self.get_recursor(&crec) {
                None => {
                    return Ok(BridgeOutcome::OutOfScope {
                        reason: format!(
                            "container {} is registered without {crec}; bridge lemmas require \
                             its recursor",
                            f.container
                        ),
                    });
                }
                Some(r) if r.arg_order != RecursorArgOrder::MajorAfterMinors => {
                    return Ok(BridgeOutcome::OutOfScope {
                        reason: format!("{crec} has a non-standard argument order"),
                    });
                }
                Some(_) => {}
            }
            let (mp, mpr, iff) = bridge_names(&f.aux_name);
            for n in [&mp, &mpr, &iff] {
                if self.get_const(n).is_some() {
                    return Ok(BridgeOutcome::OutOfScope {
                        reason: format!("bridge name {n} already exists"),
                    });
                }
            }
            let stored = self
                .inductives
                .get(&f.aux_name)
                .ok_or_else(|| inv(format!("family {} is not registered", f.aux_name)))?;
            if (stored.num_params as usize) > f.captured_tys.len() {
                return Ok(BridgeOutcome::OutOfScope {
                    reason: format!(
                        "promotion moved params beyond the captured-local telescope of {}",
                        f.aux_name
                    ),
                });
            }
        }

        // ── Field scan + cross-family edges (Kahn topo; cycle → OutOfScope) ─
        let block: Vec<Name> = decl
            .types
            .iter()
            .map(|t| t.name.clone())
            .chain(families.iter().map(|f| f.aux_name.clone()))
            .collect();
        let fam_idx = |n: &Name| families.iter().position(|f| &f.aux_name == n);
        let mut edges: Vec<Vec<usize>> = vec![Vec::new(); families.len()];
        for (fi, f) in families.iter().enumerate() {
            for (aux_ctor, _) in &f.ctor_map {
                let cv = self
                    .constructors
                    .get(aux_ctor)
                    .ok_or_else(|| inv(format!("aux constructor {aux_ctor} is not registered")))?;
                let mut cursor = cv.type_.clone();
                while let ExprKind::Pi(_, dom, body) = &cursor.kind {
                    let dom = &**dom;
                    if block.iter().any(|b| mentions_name(dom, b)) {
                        let head = dom.get_app_fn();
                        let ExprKind::Const(hname, _) = &head.kind else {
                            return Ok(BridgeOutcome::OutOfScope {
                                reason: format!(
                                    "constructor {aux_ctor} has a field mentioning a block \
                                     member outside head position"
                                ),
                            });
                        };
                        if !block.iter().any(|b| b == hname)
                            || dom
                                .get_app_args()
                                .iter()
                                .any(|a| block.iter().any(|b| mentions_name(a, b)))
                        {
                            return Ok(BridgeOutcome::OutOfScope {
                                reason: format!(
                                    "constructor {aux_ctor} has a field mentioning a block \
                                     member outside head position"
                                ),
                            });
                        }
                        if let Some(ti) = fam_idx(hname) {
                            if ti != fi {
                                edges[fi].push(ti);
                            }
                        }
                    }
                    cursor = (**body).clone();
                }
            }
        }
        let topo = match kahn_topo(&edges) {
            Some(order) => order,
            None => {
                return Ok(BridgeOutcome::OutOfScope {
                    reason: "cyclic capture chain between lifted families".to_string(),
                });
            }
        };

        // ── Build declarations ─────────────────────────────────────────────
        let mut decls = Vec::with_capacity(families.len() * 3);
        for f in families {
            decls.push(self.build_mp(decl, families, f)?);
        }
        // mprs deepest-first: reverse topological order of the edge graph
        // (edges point from user to used; used families must come first).
        for &fi in topo.iter().rev() {
            decls.push(self.build_mpr(families, &families[fi])?);
        }
        for f in families {
            decls.push(self.build_iff(families, f)?);
        }
        Ok(BridgeOutcome::Bridges(decls))
    }

    /// Walk `aux_type` into the shared statement telescope and both sides.
    fn build_family_tele(
        &self,
        families: &[LiftedFamilyInfo],
        f: &LiftedFamilyInfo,
    ) -> Result<FamilyTele, LocalLiftBridgeError> {
        let m = f.captured_tys.len();
        let mut b = EnvDeclBuilder::new();
        let (binders, codomain) = walk_telescope(&mut b, &f.aux_type);
        if !matches!(&codomain.kind, ExprKind::Sort(l) if l.is_zero()) {
            return Err(inv(format!(
                "family {} former does not end in Prop",
                f.aux_name
            )));
        }
        if binders.len() != m + f.container_num_indices as usize {
            return Err(inv(format!(
                "family {} former telescope disagrees with its record",
                f.aux_name
            )));
        }
        let fvars: Vec<Expr> = binders.iter().map(|(_, fv, _)| fv.clone()).collect();
        let lhs = Expr::apps(Expr::const_(f.aux_name.clone(), Vec::new()), fvars.clone());
        let l_rev: Vec<Expr> = fvars[..m].iter().rev().cloned().collect();
        let a_inst: Vec<Expr> = f
            .canonical_args
            .iter()
            .map(|a| a.instantiate_rev(&l_rev))
            .collect();
        let rhs = Expr::apps(
            Expr::const_(f.container.clone(), f.container_levels.clone()),
            a_inst.iter().cloned().chain(fvars[m..].iter().cloned()),
        );
        // Anti-vacuity firewall: the RHS must be the container spelling and
        // mention no lifted family — an `Iff X X`-shaped construction bug
        // must be unbuildable, not merely untested.
        if families.iter().any(|g| mentions_name(&rhs, &g.aux_name)) {
            return Err(inv(format!(
                "bridge RHS for {} mentions a lifted family — record is not the \
                 original spelling",
                f.aux_name
            )));
        }
        Ok(FamilyTele {
            b,
            binders,
            lhs,
            rhs,
            a_inst,
        })
    }

    /// `bridge_mp`: one application of the lifted block's mutual recursor
    /// with original-spelling motives for aux members and rebuild motives
    /// for user members.
    fn build_mp(
        &self,
        decl: &InductiveDecl,
        families: &[LiftedFamilyInfo],
        f: &LiftedFamilyInfo,
    ) -> Result<Declaration, LocalLiftBridgeError> {
        let mut tele = self.build_family_tele(families, f)?;
        let stored = self
            .inductives
            .get(&f.aux_name)
            .ok_or_else(|| inv(format!("family {} is not registered", f.aux_name)))?;
        let np = stored.num_params as usize;
        let fvars: Vec<Expr> = tele.binders.iter().map(|(_, fv, _)| fv.clone()).collect();

        let (h_id, h_fv) = tele.b.fresh_local(tele.lhs.clone());
        let rec_name = Name::from_string(&format!("{}.rec", f.aux_name));
        let rec = self
            .get_recursor(&rec_name)
            .ok_or_else(|| inv(format!("{rec_name} is not registered")))?
            .clone();
        if rec.arg_order != RecursorArgOrder::MajorAfterMinors {
            return Err(inv(format!("{rec_name} has a non-standard argument order")));
        }
        // The lifted block is level-monomorphic; every extra recursor level
        // param is a motive universe, instantiated at Prop.
        let rec_levels: Vec<Level> = vec![Level::zero(); rec.level_params.len()];
        let rec_ty = rec
            .type_
            .instantiate_level_params_direct(&rec.level_params, &rec_levels);
        let mut ra = RecApply::new(Expr::const_(rec_name.clone(), rec_levels), rec_ty);

        for fv in &fvars[..np] {
            ra.apply(fv.clone()).map_err(inv)?;
        }
        for _ in 0..rec.num_motives {
            let dom = ra.peek_domain().map_err(inv)?;
            let motive = self.build_mp_motive(&tele.b, families, &fvars[..np], &dom)?;
            ra.apply(motive).map_err(inv)?;
        }
        // A mutual recursor's STORED rules cover only its own member's
        // constructors, but its TYPE has one minor slot per block ctor —
        // classify each slot by the ctor application in its codomain.
        let block: Vec<Name> = decl
            .types
            .iter()
            .map(|t| t.name.clone())
            .chain(families.iter().map(|g| g.aux_name.clone()))
            .collect();
        for _ in 0..rec.num_minors {
            let dom = ra.peek_domain().map_err(inv)?;
            let minor = self.build_mp_minor(&tele.b, families, &block, &fvars[..np], np, &dom)?;
            ra.apply(minor).map_err(inv)?;
        }
        for fv in &fvars[np..] {
            ra.apply(fv.clone()).map_err(inv)?;
        }
        ra.apply(h_fv).map_err(inv)?;

        let value_body = tele
            .b
            .mk_lam(h_id, BinderInfo::Default, tele.lhs.clone(), ra.term);
        let value = tele
            .b
            .finish(close_lams(&tele.b, &tele.binders, value_body));
        let type_ = tele.b.finish(close_pis(
            &tele.b,
            &tele.binders,
            Expr::arrow(tele.lhs.clone(), tele.rhs.clone()),
        ));
        let (mp_name, _, _) = bridge_names(&f.aux_name);
        Ok(Declaration::Theorem {
            name: mp_name,
            level_params: Vec::new(),
            type_,
            value,
        })
    }

    /// A `bridge_mp` motive: for an aux member, the ORIGINAL container
    /// spelling at the member's full argument sequence; for a user member,
    /// the member itself (rebuild).
    fn build_mp_motive(
        &self,
        parent: &EnvDeclBuilder,
        families: &[LiftedFamilyInfo],
        param_fvars: &[Expr],
        dom: &Expr,
    ) -> Result<Expr, LocalLiftBridgeError> {
        let mut cb = EnvDeclBuilder::child_of(parent);
        let (locals, _sort) = walk_telescope(&mut cb, dom);
        let Some((_, major_fv, major_ty)) = locals.last() else {
            return Err(inv("motive slot has no major binder"));
        };
        let _ = major_fv;
        let ExprKind::Const(member, _) = &major_ty.get_app_fn().kind else {
            return Err(inv("motive major is not constant-headed"));
        };
        let idx_vals: Vec<Expr> = locals[..locals.len() - 1]
            .iter()
            .map(|(_, fv, _)| fv.clone())
            .collect();
        let body = if let Some(r) = families.iter().find(|g| &g.aux_name == member) {
            let m_r = r.captured_tys.len();
            let full: Vec<Expr> = param_fvars.iter().cloned().chain(idx_vals).collect();
            if full.len() != m_r + r.container_num_indices as usize {
                return Err(inv(format!(
                    "motive telescope for {} disagrees with its record",
                    r.aux_name
                )));
            }
            let l_rev: Vec<Expr> = full[..m_r].iter().rev().cloned().collect();
            Expr::apps(
                Expr::const_(r.container.clone(), r.container_levels.clone()),
                r.canonical_args
                    .iter()
                    .map(|a| a.instantiate_rev(&l_rev))
                    .chain(full[m_r..].iter().cloned()),
            )
        } else {
            Expr::apps(
                Expr::const_(member.clone(), Vec::new()),
                param_fvars.iter().cloned().chain(idx_vals),
            )
        };
        Ok(cb.finish_child(close_lams(&cb, &locals, body)))
    }

    /// A `bridge_mp` minor: for an aux ctor, the container constructor at
    /// the capturing instantiation with IHs at every block-headed field; for
    /// a user ctor, the ctor itself rebuilt from its fields. The slot's own
    /// codomain names the ctor; field recursiveness is read off the ctor's
    /// REGISTERED field heads (block-member-headed = recursive, matching the
    /// recursor builder's mutual classification).
    fn build_mp_minor(
        &self,
        parent: &EnvDeclBuilder,
        families: &[LiftedFamilyInfo],
        block: &[Name],
        param_fvars: &[Expr],
        np: usize,
        dom: &Expr,
    ) -> Result<Expr, LocalLiftBridgeError> {
        let mut cb = EnvDeclBuilder::child_of(parent);
        let (locals, cod) = walk_telescope(&mut cb, dom);
        let ctor_app = cod
            .get_app_args()
            .last()
            .cloned()
            .ok_or_else(|| inv("minor slot codomain is not a motive application"))?;
        let ExprKind::Const(ctor, _) = &ctor_app.get_app_fn().kind else {
            return Err(inv(
                "minor slot codomain does not end in a ctor application",
            ));
        };
        let ctor = ctor.clone();
        let cv = self
            .constructors
            .get(&ctor)
            .ok_or_else(|| inv(format!("minor ctor {ctor} is not registered")))?;
        let nf = cv.num_fields as usize;
        // Recursive flags from the registered ctor type: skip the promoted
        // params, then flag each field whose head is a block member.
        let mut recursive_fields = Vec::with_capacity(nf);
        {
            let mut cursor = cv.type_.clone();
            for _ in 0..cv.num_params {
                let ExprKind::Pi(_, _, body) = &cursor.kind else {
                    return Err(inv(format!("ctor {ctor} shorter than its num_params")));
                };
                cursor = (**body).clone();
            }
            for _ in 0..nf {
                let ExprKind::Pi(_, fdom, body) = &cursor.kind else {
                    return Err(inv(format!("ctor {ctor} shorter than its num_fields")));
                };
                let head = fdom.get_app_fn();
                let is_rec =
                    matches!(&head.kind, ExprKind::Const(h, _) if block.iter().any(|b| b == h));
                recursive_fields.push(is_rec);
                cursor = (**body).clone();
            }
        }
        let n_ih = recursive_fields.iter().filter(|&&x| x).count();
        if locals.len() != nf + n_ih {
            return Err(inv(format!(
                "minor telescope for {ctor} has {} binders, expected {} fields + {} IHs",
                locals.len(),
                nf,
                n_ih
            )));
        }
        let fields = &locals[..nf];
        let ihs = &locals[nf..];
        let recursive_fields = &recursive_fields;

        let owning = families
            .iter()
            .find(|g| g.ctor_map.iter().any(|(a, _)| a == &ctor));
        let body = if let Some(r) = owning {
            let (_, c_orig) = r
                .ctor_map
                .iter()
                .find(|(a, _)| a == &ctor)
                .expect("owning family located by this ctor");
            let m_r = r.captured_tys.len();
            if np > m_r {
                return Err(inv(format!(
                    "params promoted beyond the ℓ-telescope of {}",
                    r.aux_name
                )));
            }
            // ℓ values: promoted prefix from the params, remnant from fields.
            let l_vals: Vec<Expr> = (0..m_r)
                .map(|i| {
                    if i < np {
                        param_fvars[i].clone()
                    } else {
                        fields[i - np].1.clone()
                    }
                })
                .collect();
            let l_rev: Vec<Expr> = l_vals.iter().rev().cloned().collect();
            let a_inst: Vec<Expr> = r
                .canonical_args
                .iter()
                .map(|a| a.instantiate_rev(&l_rev))
                .collect();
            let remnant = m_r - np;
            let mut args: Vec<Expr> = a_inst;
            let mut ih_iter = ihs.iter();
            for (i, (_, fv, _)) in fields.iter().enumerate().skip(remnant) {
                if recursive_fields[i] {
                    let (_, ih_fv, _) = ih_iter
                        .next()
                        .ok_or_else(|| inv(format!("IH underflow in minor for {ctor}")))?;
                    args.push(ih_fv.clone());
                } else {
                    args.push(fv.clone());
                }
            }
            Expr::apps(
                Expr::const_(c_orig.clone(), r.container_levels.clone()),
                args,
            )
        } else {
            // User ctor: rebuild from params + fields; IHs unused.
            Expr::apps(
                Expr::const_(ctor.clone(), Vec::new()),
                param_fvars
                    .iter()
                    .cloned()
                    .chain(fields.iter().map(|(_, fv, _)| fv.clone())),
            )
        };
        Ok(cb.finish_child(close_lams(&cb, &locals, body)))
    }

    /// `bridge_mpr`: one application of the container's recursor at the
    /// capturing instantiation; rewritten fields transport through the used
    /// family's already-registered `bridge_mpr` (reverse-topo emission).
    fn build_mpr(
        &self,
        families: &[LiftedFamilyInfo],
        f: &LiftedFamilyInfo,
    ) -> Result<Declaration, LocalLiftBridgeError> {
        let m = f.captured_tys.len();
        let mut tele = self.build_family_tele(families, f)?;
        let fvars: Vec<Expr> = tele.binders.iter().map(|(_, fv, _)| fv.clone()).collect();

        let (h_id, h_fv) = tele.b.fresh_local(tele.rhs.clone());
        let rec_name = Name::from_string(&format!("{}.rec", f.container));
        let rec = self
            .get_recursor(&rec_name)
            .ok_or_else(|| inv(format!("{rec_name} is not registered")))?
            .clone();
        let container_val = self
            .inductives
            .get(&f.container)
            .ok_or_else(|| inv(format!("container {} is not registered", f.container)))?;
        let extra = rec
            .level_params
            .len()
            .checked_sub(container_val.level_params.len())
            .ok_or_else(|| inv(format!("{rec_name} has fewer levels than its inductive")))?;
        let rec_levels: Vec<Level> = std::iter::repeat_n(Level::zero(), extra)
            .chain(f.container_levels.iter().cloned())
            .collect();
        let rec_ty = rec
            .type_
            .instantiate_level_params_direct(&rec.level_params, &rec_levels);
        let mut ra = RecApply::new(Expr::const_(rec_name.clone(), rec_levels), rec_ty);

        // Container params: the capturing instantiation.
        for a in &tele.a_inst {
            ra.apply(a.clone()).map_err(inv)?;
        }
        if rec.num_motives != 1 {
            return Err(inv(format!(
                "{rec_name} is a mutual recursor; single-container v1 gate violated"
            )));
        }
        // Motive: λ (container indices…) (x), _lifted.C_k ℓ… indices….
        {
            let dom = ra.peek_domain().map_err(inv)?;
            let mut cb = EnvDeclBuilder::child_of(&tele.b);
            let (locals, _sort) = walk_telescope(&mut cb, &dom);
            if locals.is_empty() {
                return Err(inv("container motive slot has no major binder"));
            }
            let idx_vals = locals[..locals.len() - 1]
                .iter()
                .map(|(_, fv, _)| fv.clone());
            let body = Expr::apps(
                Expr::const_(f.aux_name.clone(), Vec::new()),
                fvars[..m].iter().cloned().chain(idx_vals),
            );
            let motive = cb.finish_child(close_lams(&cb, &locals, body));
            ra.apply(motive).map_err(inv)?;
        }
        // Minors, per container ctor.
        for rule in &rec.rules {
            let c_orig = &rule.constructor_name;
            let (aux_ctor, _) = f
                .ctor_map
                .iter()
                .find(|(_, o)| o == c_orig)
                .map(|(a, o)| (a.clone(), o))
                .ok_or_else(|| inv(format!("no aux ctor mapped for {c_orig}")))?;
            let dom = ra.peek_domain().map_err(inv)?;
            let minor = self.build_mpr_minor(
                &tele.b,
                families,
                f,
                &fvars,
                m,
                &aux_ctor,
                rule.num_fields as usize,
                &rule.recursive_fields,
                &dom,
            )?;
            ra.apply(minor).map_err(inv)?;
        }
        for fv in &fvars[m..] {
            ra.apply(fv.clone()).map_err(inv)?;
        }
        ra.apply(h_fv).map_err(inv)?;

        let value_body = tele
            .b
            .mk_lam(h_id, BinderInfo::Default, tele.rhs.clone(), ra.term);
        let value = tele
            .b
            .finish(close_lams(&tele.b, &tele.binders, value_body));
        let type_ = tele.b.finish(close_pis(
            &tele.b,
            &tele.binders,
            Expr::arrow(tele.rhs.clone(), tele.lhs.clone()),
        ));
        let (_, mpr_name, _) = bridge_names(&f.aux_name);
        Ok(Declaration::Theorem {
            name: mpr_name,
            level_params: Vec::new(),
            type_,
            value,
        })
    }

    /// A `bridge_mpr` minor: the aux constructor, with container fields fed
    /// straight through, self-loop fields from the IH, and cross-family
    /// fields transported through the used family's `bridge_mpr`.
    #[allow(clippy::too_many_arguments)]
    fn build_mpr_minor(
        &self,
        parent: &EnvDeclBuilder,
        families: &[LiftedFamilyInfo],
        f: &LiftedFamilyInfo,
        fvars: &[Expr],
        m: usize,
        aux_ctor: &Name,
        nf: usize,
        recursive_fields: &[bool],
        dom: &Expr,
    ) -> Result<Expr, LocalLiftBridgeError> {
        let mut cb = EnvDeclBuilder::child_of(parent);
        let (locals, _cod) = walk_telescope(&mut cb, dom);
        let n_ih = recursive_fields.iter().filter(|&&x| x).count();
        if locals.len() != nf + n_ih {
            return Err(inv(format!(
                "container minor telescope for {aux_ctor} has {} binders, expected {nf}+{n_ih}",
                locals.len()
            )));
        }
        let cfields = &locals[..nf];
        let ihs = &locals[nf..];

        // Walk the REGISTERED aux ctor telescope alongside, to read each
        // expected aux field type at the current instantiation.
        let aux_cv = self
            .constructors
            .get(aux_ctor)
            .ok_or_else(|| inv(format!("aux constructor {aux_ctor} is not registered")))?;
        let mut cursor = aux_cv.type_.clone();
        let mut ctor_args: Vec<Expr> = Vec::with_capacity(m + nf);
        // Params + ℓ-remnants: the ℓ fvars (positions 0..m of the statement
        // telescope) in order.
        for fv in &fvars[..m] {
            let ExprKind::Pi(_, _, body) = &cursor.kind else {
                return Err(inv(format!("aux ctor {aux_ctor} telescope shorter than ℓ")));
            };
            cursor = body.instantiate(fv);
            ctor_args.push(fv.clone());
        }
        let mut ih_iter = ihs.iter();
        for (i, (_, field_fv, _)) in cfields.iter().enumerate() {
            let ExprKind::Pi(_, dom_aux, body) = &cursor.kind else {
                return Err(inv(format!(
                    "aux ctor {aux_ctor} has fewer fields than the container rule"
                )));
            };
            let dom_aux = (**dom_aux).clone();
            let head = dom_aux.get_app_fn();
            let arg = match &head.kind {
                ExprKind::Const(hname, _) if hname == &f.aux_name => {
                    // Self-loop: the container recursor's IH is exactly the
                    // aux proposition (the motive above).
                    if !recursive_fields[i] {
                        return Err(inv(format!(
                            "self-loop field {i} of {aux_ctor} is not recursive in the \
                             container rule"
                        )));
                    }
                    let (_, ih_fv, _) = ih_iter
                        .next()
                        .ok_or_else(|| inv(format!("IH underflow in {aux_ctor}")))?;
                    ih_fv.clone()
                }
                ExprKind::Const(hname, _) if families.iter().any(|g| &g.aux_name == hname) => {
                    // Cross-family: transport the original-side field through
                    // the used family's bridge_mpr (already registered by
                    // reverse-topo emission order).
                    let (_, used_mpr, _) = bridge_names(hname);
                    let mut mpr_args: Vec<Expr> =
                        dom_aux.get_app_args().into_iter().cloned().collect();
                    mpr_args.push(field_fv.clone());
                    Expr::apps(Expr::const_(used_mpr, Vec::new()), mpr_args)
                }
                _ => field_fv.clone(),
            };
            cursor = body.instantiate(&arg);
            ctor_args.push(arg);
        }
        let body = Expr::apps(Expr::const_(aux_ctor.clone(), Vec::new()), ctor_args);
        Ok(cb.finish_child(close_lams(&cb, &locals, body)))
    }

    /// `bridge`: `Iff.intro` of the two directions.
    fn build_iff(
        &self,
        families: &[LiftedFamilyInfo],
        f: &LiftedFamilyInfo,
    ) -> Result<Declaration, LocalLiftBridgeError> {
        let tele = self.build_family_tele(families, f)?;
        let fvars: Vec<Expr> = tele.binders.iter().map(|(_, fv, _)| fv.clone()).collect();
        let (mp_name, mpr_name, iff_name) = bridge_names(&f.aux_name);
        let iff_body = Expr::apps(
            Expr::const_(Name::from_string("Iff"), Vec::new()),
            [tele.lhs.clone(), tele.rhs.clone()],
        );
        let type_ = tele.b.finish(close_pis(&tele.b, &tele.binders, iff_body));
        let value_body = Expr::apps(
            Expr::const_(Name::from_string("Iff.intro"), Vec::new()),
            [
                tele.lhs.clone(),
                tele.rhs.clone(),
                Expr::apps(Expr::const_(mp_name, Vec::new()), fvars.clone()),
                Expr::apps(Expr::const_(mpr_name, Vec::new()), fvars),
            ],
        );
        let value = tele
            .b
            .finish(close_lams(&tele.b, &tele.binders, value_body));
        Ok(Declaration::Theorem {
            name: iff_name,
            level_params: Vec::new(),
            type_,
            value,
        })
    }
}

/// Kahn topological sort over the family edge lists; `None` on a cycle.
fn kahn_topo(edges: &[Vec<usize>]) -> Option<Vec<usize>> {
    let n = edges.len();
    let mut indeg = vec![0usize; n];
    for out in edges {
        for &t in out {
            indeg[t] += 1;
        }
    }
    let mut queue: Vec<usize> = (0..n).filter(|&i| indeg[i] == 0).collect();
    let mut order = Vec::with_capacity(n);
    while let Some(i) = queue.pop() {
        order.push(i);
        for &t in &edges[i] {
            indeg[t] -= 1;
            if indeg[t] == 0 {
                queue.push(t);
            }
        }
    }
    (order.len() == n).then_some(order)
}
