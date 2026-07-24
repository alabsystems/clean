// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nested-inductive RESTORE pass (design
//! `designs/2026-07-02-parameterized-nested-inductives.md` §4, corrections
//! [R4]/[R10]–[R15]; Lean reference `restore_nested` + the restore driver,
//! inductive.cpp:828-872, :1088-1187).
//!
//! After the transformed mutual block (originals + `_nested.*` aux mirrors)
//! has been kernel-checked and registered, this pass rewrites the
//! environment to Lean's post-restore artifact set:
//!
//! - original constructor types restored to container spelling (hard-checked
//!   byte-equal to the user's input — the ROUND-TRIP LAW);
//! - original `InductiveVal`s: `all_names` = originals only, `is_nested` set;
//! - original `T.rec` (and `casesOn`/`recOn` on the Generate lane): types and
//!   rule RHSs rewritten through [`restore_expr`], metadata untouched;
//! - each aux recursor renamed `<firstOriginal>.rec_N` (creation order),
//!   rules re-keyed to the real container constructors, registered in BOTH
//!   `constants` and `recursors` ([R4] — the mathverse replay acceptor
//!   probes `get_const` first);
//! - every aux registration removed — no `_nested.*` name survives.
//!
//! Discipline: COMPUTE-THEN-COMMIT. Every fallible step (expression
//! restoration, round-trip assertion, residual scan, duplicate-name check)
//! runs in a pure phase producing a plan; applying the plan is infallible.
//! A restore error therefore leaves the environment exactly as Pass 1 built
//! it, and the caller's error path unregisters the whole family as before.

use std::collections::HashMap;

use crate::expr::{Expr, ExprKind};
use crate::inductive::{InductiveDecl, InductiveError, InductiveType, InductiveVal, RecursorVal};
use crate::name::Name;

use super::inductive_nested_elim::NestedAuxEntry;
use super::types::{ConstantInfo, EnvError};
use super::Environment;

/// Everything the commit phase writes. Built entirely by the pure phase.
struct RestorePlan {
    /// Restored constructor types for the ORIGINAL members (written to both
    /// `constants` and `constructors`).
    ctor_types: Vec<(Name, Expr)>,
    /// Replacement `InductiveVal`s for the original members.
    inductive_vals: Vec<(Name, InductiveVal)>,
    /// Restored eliminators for original members (`rec`, and
    /// `casesOn`/`recOn` when they exist), written to both tables. The
    /// third element is the restored definitional VALUE (casesOn/recOn are
    /// value-bearing rec-reordering wrappers; rec has none).
    eliminators: Vec<(Name, RecursorVal, Option<Expr>)>,
    /// Renamed aux recursors `<first>.rec_N`, inserted fresh in both tables.
    renamed: Vec<(Name, RecursorVal)>,
    /// The restored original `InductiveType`s (container spelling), for the
    /// caller's post-restore generation passes (noConfusion/below/brecOn).
    restored_types: Vec<InductiveType>,
}

/// Expression-level restore (design §4.2, Lean :828-872 in de Bruijn terms).
struct RestoreCtx<'a> {
    /// aux TYPE name → its entry (case b).
    aux_types: HashMap<&'a Name, &'a NestedAuxEntry>,
    /// aux CTOR name → (container ctor name, owning entry) (case c).
    aux_ctors: HashMap<&'a Name, (&'a Name, &'a NestedAuxEntry)>,
    /// `_nested.X_j.rec` → `<first>.rec_N` (case a).
    rec_map: HashMap<Name, Name>,
    /// Shared parameter count of the declaration.
    p: u32,
}

impl RestoreCtx<'_> {
    /// Restore `e` at binder depth `t` (binders crossed from the artifact
    /// root — recursor types are Pi-telescopes, rule RHSs are Lam-telescopes;
    /// both open with the `p` shared params, so aux occurrences sit at
    /// `t ≥ p`).
    fn restore(&self, e: &Expr, t: u32) -> Result<Expr, InductiveError> {
        // Case (a): a recursor constant, bare or as a spine head — a plain
        // rename with levels preserved (they are the recursor's own
        // `[elim] ++ decl` params).
        if let ExprKind::Const(name, levels) = &e.kind {
            if let Some(new_name) = self.rec_map.get(name) {
                return Ok(Expr::const_(new_name.clone(), levels.to_vec()));
            }
        }

        // Cases (b)/(c): a spine headed by an aux type / aux constructor.
        // `get_app_fn` of a bare const is the const itself, covering the
        // `p = 0` zero-argument case (design §4.2 note).
        let head = e.get_app_fn();
        if let ExprKind::Const(head_name, _) = &head.kind {
            if let Some(entry) = self.aux_types.get(head_name) {
                return self.rebuild_spine(e, t, entry, &entry.sibling_name);
            }
            if let Some((container_ctor, entry)) = self.aux_ctors.get(head_name) {
                return self.rebuild_spine(e, t, entry, container_ctor);
            }
        }

        // No match: descend structurally (MData/Proj included, [R5]).
        match &e.kind {
            ExprKind::App(f, a) => Ok(Expr::app(self.restore(f, t)?, self.restore(a, t)?)),
            ExprKind::Pi(bi, domain, body) => Ok(Expr::pi(
                *bi,
                self.restore(domain, t)?,
                self.restore(body, t + 1)?,
            )),
            ExprKind::Lam(bi, domain, body) => Ok(Expr::lam(
                *bi,
                self.restore(domain, t)?,
                self.restore(body, t + 1)?,
            )),
            ExprKind::Let(name, ty, val, body, non_dep) => Ok(Expr::from_kind(ExprKind::Let(
                name.clone(),
                std::sync::Arc::new(self.restore(ty, t)?),
                std::sync::Arc::new(self.restore(val, t)?),
                std::sync::Arc::new(self.restore(body, t + 1)?),
                *non_dep,
            ))),
            ExprKind::MData(meta, inner) => Ok(Expr::from_kind(ExprKind::MData(
                meta.clone(),
                std::sync::Arc::new(self.restore(inner, t)?),
            ))),
            ExprKind::Proj(struct_name, idx, inner) => Ok(Expr::from_kind(ExprKind::Proj(
                struct_name.clone(),
                *idx,
                std::sync::Arc::new(self.restore(inner, t)?),
            ))),
            _ => Ok(e.clone()),
        }
    }

    /// `Aux A₀…A_{p−1} rest…` ↦ `target Ds′.lift(k) rest…` where
    /// `k = t − p`. The first `p` args must be exactly the shared param
    /// bvars (generation guarantees this; violation is an internal error).
    /// Trailing args are transplanted verbatim (Lean `replace_fn` early-exit
    /// semantics); the caller's residual scan is the tripwire for anything
    /// they might still carry.
    fn rebuild_spine(
        &self,
        e: &Expr,
        t: u32,
        entry: &NestedAuxEntry,
        target: &Name,
    ) -> Result<Expr, InductiveError> {
        let args = e.get_app_args();
        let p = self.p as usize;
        if args.len() < p || t < self.p {
            return Err(InductiveError::NestedRestoreInvariant(format!(
                "aux occurrence of {} under-applied at restore (args={}, depth={t})",
                entry.aux_name,
                args.len()
            )));
        }
        for (i, arg) in args.iter().take(p).enumerate() {
            let expected = Expr::bvar(t - 1 - i as u32);
            if **arg != expected {
                return Err(InductiveError::NestedRestoreInvariant(format!(
                    "aux occurrence of {} does not apply the shared param bvars \
                     (arg {i} at depth {t})",
                    entry.aux_name
                )));
            }
        }
        let k = t - self.p;
        let mut result = Expr::const_(target.clone(), entry.container_levels.clone());
        for d in &entry.canonical_args {
            result = Expr::app(result, d.lift(k));
        }
        for arg in &args[p..] {
            result = Expr::app(result, (*arg).clone());
        }
        Ok(result)
    }
}

/// Scan for surviving `_nested.*` constants (the residual tripwire).
fn scan_residuals(e: &Expr, context: &str) -> Result<(), InductiveError> {
    let residual = e
        .collect_constants()
        .into_iter()
        .find(|name| name.to_string().starts_with("_nested."));
    match residual {
        Some(name) => Err(InductiveError::NestedRestoreInvariant(format!(
            "restored {context} still references {name}"
        ))),
        None => Ok(()),
    }
}

impl Environment {
    /// Run the restore pass. `decl` is the TRANSFORMED block as registered by
    /// Pass 1 (originals first, aux mirrors after); `pre_elim_ctor_types` are
    /// the user's constructor types cloned before elimination ([R13]);
    /// `has_generated_eliminators` says whether `casesOn`/`recOn` exist for
    /// originals (Generate lane).
    ///
    /// On success, returns the restored original `InductiveType`s for the
    /// caller's later generation passes. On error, the environment is
    /// UNCHANGED relative to entry (compute-then-commit).
    pub(crate) fn restore_nested_block(
        &mut self,
        decl: &InductiveDecl,
        entries: &[NestedAuxEntry],
        pre_elim_ctor_types: &[(Name, Expr)],
        has_generated_eliminators: bool,
    ) -> Result<Vec<InductiveType>, EnvError> {
        let n_orig = decl.types.len() - entries.len();
        let first_name = &decl.types[0].name;
        let originals: Vec<Name> = decl.types[..n_orig]
            .iter()
            .map(|t| t.name.clone())
            .collect();

        // ---- PURE PHASE -------------------------------------------------
        let mut rec_map = HashMap::new();
        for (j, entry) in entries.iter().enumerate() {
            rec_map.insert(
                Name::from_string(&format!("{}.rec", entry.aux_name)),
                Name::from_string(&format!("{first_name}.rec_{}", j + 1)),
            );
        }
        let mut aux_types = HashMap::new();
        let mut aux_ctors = HashMap::new();
        for entry in entries {
            aux_types.insert(&entry.aux_name, entry);
            for (aux_ctor, container_ctor) in &entry.ctor_map {
                aux_ctors.insert(aux_ctor, (container_ctor, entry));
            }
        }
        let ctx = RestoreCtx {
            aux_types,
            aux_ctors,
            rec_map,
            p: decl.num_params,
        };
        let restore_err = EnvError::Inductive;

        // 1. Original constructor types: restore + round-trip law + scan.
        let pre_elim: HashMap<&Name, &Expr> =
            pre_elim_ctor_types.iter().map(|(n, e)| (n, e)).collect();
        let mut ctor_types = Vec::new();
        let mut restored_types = Vec::with_capacity(n_orig);
        for member in &decl.types[..n_orig] {
            let mut restored_ctors = Vec::with_capacity(member.constructors.len());
            for ctor in &member.constructors {
                let restored = ctx.restore(&ctor.type_, 0).map_err(restore_err)?;
                scan_residuals(&restored, &format!("constructor {}", ctor.name))
                    .map_err(restore_err)?;
                let original = pre_elim.get(&ctor.name).ok_or_else(|| {
                    restore_err(InductiveError::NestedRestoreInvariant(format!(
                        "no pre-elimination clone for constructor {}",
                        ctor.name
                    )))
                })?;
                if restored != **original {
                    return Err(restore_err(InductiveError::NestedRestoreInvariant(
                        format!(
                            "round-trip law violated: restored type of {} differs \
                             from the declared constructor type",
                            ctor.name
                        ),
                    )));
                }
                let level_params = self
                    .constants
                    .get(&ctor.name)
                    .ok_or_else(|| {
                        restore_err(InductiveError::NestedRestoreInvariant(format!(
                            "constructor {} lost its constant entry before restore",
                            ctor.name
                        )))
                    })?
                    .level_params
                    .clone();
                self.check_decl_readonly_strict(&super::Declaration::Axiom {
                    name: ctor.name.clone(),
                    level_params,
                    type_: restored.clone(),
                })?;
                ctor_types.push((ctor.name.clone(), restored.clone()));
                restored_ctors.push(crate::inductive::Constructor {
                    name: ctor.name.clone(),
                    type_: restored,
                });
            }
            restored_types.push(InductiveType {
                name: member.name.clone(),
                type_: member.type_.clone(),
                constructors: restored_ctors,
            });
        }

        // 2. Original InductiveVals: all_names = originals, is_nested = true
        //    block-wide on elim-fired originals (design §4.3 item 1).
        let mut inductive_vals = Vec::with_capacity(n_orig);
        for member in &decl.types[..n_orig] {
            let mut val = self.inductives.get(&member.name).cloned().ok_or_else(|| {
                restore_err(InductiveError::NestedRestoreInvariant(format!(
                    "original member {} not registered at restore",
                    member.name
                )))
            })?;
            val.all_names = originals.clone();
            val.is_nested = true;
            inductive_vals.push((member.name.clone(), val));
        }

        // 3. Original eliminators: rec always; casesOn/recOn on Generate.
        //    casesOn/recOn carry definitional VALUES (mechanical
        //    rec-reordering wrappers, Lean parity) whose bodies mention the
        //    pre-restore spellings — restore those too, or the stored value
        //    would dangle on erased `_nested.*` constants.
        let mut eliminators = Vec::new();
        let elim_suffixes: &[&str] = if has_generated_eliminators {
            &["rec", "casesOn", "recOn"]
        } else {
            &["rec"]
        };
        for member in &decl.types[..n_orig] {
            for suffix in elim_suffixes {
                let name = Name::from_string(&format!("{}.{suffix}", member.name));
                let Some(val) = self.recursors.get(&name) else {
                    // HIT members legitimately skip casesOn/recOn.
                    continue;
                };
                let mut val = val.clone();
                val.type_ = ctx.restore(&val.type_, 0).map_err(restore_err)?;
                scan_residuals(&val.type_, &format!("{name} type")).map_err(restore_err)?;
                for rule in &mut val.rules {
                    rule.rhs = ctx.restore(&rule.rhs, 0).map_err(restore_err)?;
                    scan_residuals(&rule.rhs, &format!("{name} rule rhs")).map_err(restore_err)?;
                }
                let restored_value = match self.constants.get(&name).and_then(|c| c.value.clone()) {
                    Some(value) => {
                        let restored = ctx.restore(&value, 0).map_err(restore_err)?;
                        scan_residuals(&restored, &format!("{name} value")).map_err(restore_err)?;
                        Some(restored)
                    }
                    None => None,
                };
                eliminators.push((name, val, restored_value));
            }
        }

        // 4. Renamed aux recursors `<first>.rec_N` (creation order = entry
        //    order, design §4.3; field recipe per the B3 surgical map).
        let mut renamed = Vec::new();
        for (j, entry) in entries.iter().enumerate() {
            let old_name = Name::from_string(&format!("{}.rec", entry.aux_name));
            let new_name = Name::from_string(&format!("{first_name}.rec_{}", j + 1));
            if self.constants.contains_key(&new_name) || self.recursors.contains_key(&new_name) {
                return Err(EnvError::DuplicateName(new_name));
            }
            let Some(val) = self.recursors.get(&old_name) else {
                return Err(restore_err(InductiveError::NestedRestoreInvariant(
                    format!("aux recursor {old_name} not registered at restore"),
                )));
            };
            let mut val = val.clone();
            val.name = new_name.clone();
            val.inductive_name = first_name.clone();
            val.type_ = ctx.restore(&val.type_, 0).map_err(restore_err)?;
            scan_residuals(&val.type_, &format!("{new_name} type")).map_err(restore_err)?;
            let ctor_rekey: HashMap<&Name, &Name> =
                entry.ctor_map.iter().map(|(a, c)| (a, c)).collect();
            for rule in &mut val.rules {
                let new_key = ctor_rekey.get(&rule.constructor_name).ok_or_else(|| {
                    restore_err(InductiveError::NestedRestoreInvariant(format!(
                        "{new_name} rule keyed to unknown aux constructor {}",
                        rule.constructor_name
                    )))
                })?;
                rule.constructor_name = (*new_key).clone();
                rule.rhs = ctx.restore(&rule.rhs, 0).map_err(restore_err)?;
                scan_residuals(&rule.rhs, &format!("{new_name} rule rhs")).map_err(restore_err)?;
                // `num_fields` and `recursive_fields` copied verbatim: aux
                // nfields == container nfields (design §1.3), positions 1:1.
            }
            renamed.push((new_name, val));
        }

        let plan = RestorePlan {
            ctor_types,
            inductive_vals,
            eliminators,
            renamed,
            restored_types,
        };
        let restored_recursor_names: Vec<Name> = plan
            .eliminators
            .iter()
            .map(|(name, _, _)| name.clone())
            .chain(plan.renamed.iter().map(|(name, _)| name.clone()))
            .collect();

        // ---- COMMIT PHASE (infallible) ----------------------------------
        for (name, ty) in &plan.ctor_types {
            if let Some(info) = self.constants.get(name) {
                let new_info = ConstantInfo::new(
                    name.clone(),
                    info.level_params.clone(),
                    ty.clone(),
                    None,
                    false,
                );
                self.constants.insert(name.clone(), new_info);
                self.declaration_verification.insert(
                    name.clone(),
                    super::DeclarationVerification::FullKernelCheck,
                );
            }
            if let Some(cv) = self.constructors.get_mut(name) {
                cv.type_ = ty.clone();
            }
        }
        for (name, val) in plan.inductive_vals {
            self.inductives.insert(name, val);
        }
        for (name, val, value) in plan.eliminators {
            // Preserve the reducibility flag of the existing registration
            // (casesOn/recOn are registered reducible-style definitions).
            let reducible = self
                .constants
                .get(&name)
                .map(|c| c.is_reducible)
                .unwrap_or(false);
            let info = ConstantInfo::new(
                name.clone(),
                val.level_params.clone(),
                val.type_.clone(),
                value,
                reducible,
            );
            self.constants.insert(name.clone(), info);
            self.declaration_verification
                .insert(name.clone(), super::DeclarationVerification::StructuralOnly);
            self.recursors.insert(name, val);
        }
        for (name, val) in plan.renamed {
            let info = ConstantInfo::new(
                name.clone(),
                val.level_params.clone(),
                val.type_.clone(),
                None,
                false,
            );
            self.constants.insert(name.clone(), info);
            self.declaration_verification.insert(
                name.clone(),
                // Provisional until the container-major metadata and every
                // reduction rule are revalidated below.
                super::DeclarationVerification::StructuralOnly,
            );
            self.recursors.insert(name, val);
        }
        // Aux erasure — exactly six kinds per entry (surgical map F); the
        // caller gates casesOn/recOn/noConfusion/below/brecOn generation to
        // originals, so no other aux artifact exists.
        for entry in entries {
            let aux = &entry.aux_name;
            self.constants.remove(aux);
            self.declaration_verification.remove(aux);
            self.inductives.remove(aux);
            for (aux_ctor, _) in &entry.ctor_map {
                self.constants.remove(aux_ctor);
                self.declaration_verification.remove(aux_ctor);
                self.constructors.remove(aux_ctor);
            }
            let aux_rec = Name::from_string(&format!("{aux}.rec"));
            self.constants.remove(&aux_rec);
            self.declaration_verification.remove(&aux_rec);
            self.recursors.remove(&aux_rec);
        }
        // Restoration rewrites both recursor types and rule RHSs.  Re-earn
        // authority for the exact post-restore bytes, including the renamed
        // container-major companions, before the public transaction commits.
        for name in &restored_recursor_names {
            self.validate_and_stamp_recursor(name)?;
        }
        #[cfg(debug_assertions)]
        {
            debug_assert!(
                !self
                    .constants
                    .keys()
                    .chain(self.inductives.keys())
                    .chain(self.constructors.keys())
                    .chain(self.recursors.keys())
                    .any(|n| n.to_string().starts_with("_nested.")),
                "restore left a _nested.* registration behind"
            );
        }

        Ok(plan.restored_types)
    }
}
