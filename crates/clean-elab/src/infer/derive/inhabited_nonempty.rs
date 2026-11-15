// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `deriving Inhabited` and `deriving Nonempty` for an inductive type, as
//! Lean 4.8.0's handlers build them (trust-ir gaps G43 and G55, ledger
//! classes (113) and (125)).
//!
//! **Inhabited** (`Lean/Elab/Deriving/Inhabited.lean`,
//! `mkInhabitedInstanceHandler`): try each constructor IN ORDER, first without
//! and then with `[Inhabited a]` hypotheses for the type parameters; a
//! constructor qualifies when every field's type has a synthesized `Inhabited`
//! instance (the field types read with the parameters and the earlier fields
//! as locals). The instance is `⟨@C _ … Inhabited.default …⟩` with only the
//! hypotheses some field instance USED, `{a}` binders for the parameters, and
//! no constructor at all is "failed to generate 'Inhabited' instance for 'T'".
//! Until 2026-10-16 Clean required EVERY constructor to be nullary and took
//! the first, so `inductive DecodeError | unsupported (s : String) | …
//! deriving Inhabited` (trust-ir `TrustIrEval/Decode.lean`) was refused.
//!
//! **Nonempty** (`Lean/Elab/Deriving/Nonempty.lean`): `variable {a} [Nonempty
//! a] … in instance : Nonempty (@T a …) := ⟨by first | apply @C₁ <;> exact
//! Classical.ofNonempty | …⟩`: a `[Nonempty a]` hypothesis available for
//! every parameter whose type is `Type _` (kept only where used, by the
//! `variable … in` inclusion rule), and the first constructor whose fields
//! all have a `Nonempty` instance, each field filled with
//! `Classical.ofNonempty`. Until 2026-10-16 Clean built `Nonempty.intro C`
//! without `Nonempty.intro`'s type argument, which the kernel refused at
//! registration, taking the inductive down with it.
//!
//! Both read the constructor telescopes from the kernel's own registration of
//! the inductive (the candidate environment), with the inductive itself bound
//! as a local so a field such as `List T` can synthesize
//! (`instInhabitedList`) before `T` is published. A field whose type depends
//! on an earlier field is read the way Lean reads it (against the field
//! variable), and the instance at the substituted type is synthesized again
//! for the term; failing there is Lean's failure too. Indexed families are
//! refused (fail-closed): Lean's `{i}` index binder only elaborates when a
//! constructor's indices are fully general.

use super::super::{DerivedInstance, ElabCtx};
use super::witness_folders::{decrements, mentions_fvar, ConstToFVar, FVarToExpr};
use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, FVarId, InductiveVal, Level};
use clean_parser::SurfaceName;

/// Which class is being derived.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Witness {
    Inhabited,
    Nonempty,
}

impl Witness {
    fn class(self) -> &'static str {
        match self {
            Self::Inhabited => "Inhabited",
            Self::Nonempty => "Nonempty",
        }
    }
}

/// One opened constructor attempt: the locals it pushed and what it found.
struct Attempt {
    /// `(fvar, type)` of each parameter, outermost first.
    params: Vec<(FVarId, Expr)>,
    /// Per parameter, the hypothesis `(fvar, type)` this attempt opened.
    hyps: Vec<Option<(FVarId, Expr)>>,
    /// The constructor's field arguments, in order.
    field_args: Vec<Expr>,
}

impl<'a> ElabCtx<'a> {
    /// `deriving Inhabited` for an inductive (module doc).
    pub(super) fn derive_inhabited_inductive_lean(
        &mut self,
        candidate: &Environment,
        ind_name: &Name,
    ) -> Result<DerivedInstance, ElabError> {
        self.derive_witness_instance(candidate, ind_name, Witness::Inhabited)
    }

    /// `deriving Nonempty` for an inductive (module doc).
    pub(super) fn derive_nonempty_inductive_lean(
        &mut self,
        candidate: &Environment,
        ind_name: &Name,
    ) -> Result<DerivedInstance, ElabError> {
        self.derive_witness_instance(candidate, ind_name, Witness::Nonempty)
    }

    fn derive_witness_instance(
        &mut self,
        candidate: &Environment,
        ind_name: &Name,
        witness: Witness,
    ) -> Result<DerivedInstance, ElabError> {
        let ind = candidate.get_inductive(ind_name).cloned().ok_or_else(|| {
            ElabError::InternalInvariant(format!(
                "deriving {}: `{ind_name}` is not registered in the candidate environment",
                witness.class()
            ))
        })?;
        if ind.num_indices != 0 {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "deriving {} for the indexed family `{ind_name}`",
                    witness.class()
                ),
            });
        }
        let passes: &[bool] = match witness {
            // Lean's `doIt false <||> doIt true`.
            Witness::Inhabited => &[false, true],
            // Lean's `variable … [Nonempty a] in`: always assumed.
            Witness::Nonempty => &[true],
        };
        let mut last_failure: Option<Expr> = None;
        for &add_hyps in passes {
            for ctor in &ind.constructor_names {
                match self.try_ctor_witness(candidate, &ind, ctor, witness, add_hyps)? {
                    Ok(instance) => {
                        // Kernel-check the instance in the candidate
                        // environment HERE, where a failure is a logged
                        // deriving failure beside the declared type
                        // (`deriving_log`), never a registration failure that
                        // takes the type down with it (G55's second face).
                        let tc = clean_kernel::TypeChecker::new(candidate);
                        tc.check_type(&instance.val, &instance.ty)
                            .map_err(|error| {
                                ElabError::InternalInvariant(format!(
                                "deriving {} for `{ind_name}` built an ill-typed instance: {error}",
                                witness.class()
                            ))
                            })?;
                        return Ok(instance);
                    }
                    Err(goal) => last_failure = Some(goal),
                }
            }
        }
        Err(match (witness, last_failure) {
            (Witness::Nonempty, Some(goal)) => ElabError::FailedToSynthesize {
                class_name: Name::from_string("Nonempty"),
                goal: goal.to_string(),
            },
            _ => ElabError::DerivingRefused {
                message: format!(
                    "failed to generate '{}' instance for '{ind_name}'",
                    witness.class()
                ),
            },
        })
    }

    /// Try one constructor. `Ok(Err(goal))` is "this constructor does not
    /// qualify" with the field goal that failed (Lean moves on to the next).
    fn try_ctor_witness(
        &mut self,
        candidate: &Environment,
        ind: &InductiveVal,
        ctor: &Name,
        witness: Witness,
        add_hyps: bool,
    ) -> Result<Result<DerivedInstance, Expr>, ElabError> {
        let ctor_ty = candidate
            .get_const(ctor)
            .map(|info| info.type_.clone())
            .ok_or_else(|| {
                ElabError::InternalInvariant(format!("deriving: constructor `{ctor}` is missing"))
            })?;
        let saved_locals = self.locals.len();
        let mut pushed_instances = 0usize;
        let self_fvar = self.fresh_fvar();
        self.push_local_with_fvar(
            SurfaceName::from_name(ind.name.clone()),
            self_fvar,
            ind.type_.clone(),
        );
        let result = self.try_ctor_witness_opened(
            ind,
            ctor,
            ctor_ty,
            witness,
            add_hyps,
            self_fvar,
            &mut pushed_instances,
        );
        for _ in 0..pushed_instances {
            self.pop_local_instance();
        }
        self.locals.truncate(saved_locals);
        result
    }

    #[allow(clippy::too_many_arguments)]
    fn try_ctor_witness_opened(
        &mut self,
        ind: &InductiveVal,
        ctor: &Name,
        ctor_ty: Expr,
        witness: Witness,
        add_hyps: bool,
        self_fvar: FVarId,
        pushed_instances: &mut usize,
    ) -> Result<Result<DerivedInstance, Expr>, ElabError> {
        let class = Name::from_string(witness.class());
        let mut cur = ctor_ty.fold_opt_or_clone(&mut ConstToFVar {
            name: &ind.name,
            fvar: self_fvar,
        });
        let mut ind_ty = ind.type_.clone();
        let mut attempt = Attempt {
            params: Vec::new(),
            hyps: Vec::new(),
            field_args: Vec::new(),
        };
        for _ in 0..ind.num_params {
            let ExprKind::Pi(_, dom, body) = cur.kind() else {
                return Err(ElabError::InternalInvariant(format!(
                    "deriving {}: `{ctor}` has fewer binders than `{}` has parameters",
                    witness.class(),
                    ind.name
                )));
            };
            let dom = dom.as_ref().clone();
            let fvar = self.fresh_fvar();
            self.push_local_with_fvar(SurfaceName::component("a", false), fvar, dom.clone());
            cur = body.instantiate(&Expr::fvar(fvar));
            if let ExprKind::Pi(_, _, ind_body) = ind_ty.kind() {
                ind_ty = ind_body.instantiate(&Expr::fvar(fvar));
            }
            let hyp = if add_hyps {
                self.param_hypothesis(&dom, fvar, witness)
            } else {
                None
            };
            if let Some((hyp_fvar, hyp_ty)) = &hyp {
                self.push_local_with_fvar(
                    SurfaceName::component("inst", false),
                    *hyp_fvar,
                    hyp_ty.clone(),
                );
                self.push_local_instance(*hyp_fvar, hyp_ty.clone());
                *pushed_instances += 1;
            }
            attempt.params.push((fvar, dom));
            attempt.hyps.push(hyp);
        }

        // Fields, read against field variables exactly as Lean's
        // `forallTelescopeReducing` reads them.
        let mut field_fvars = Vec::new();
        let mut field_insts = Vec::new();
        let mut dependent = false;
        while let ExprKind::Pi(_, dom, body) = cur.kind() {
            let dom = dom.as_ref().clone();
            if body.has_loose_bvar(0) {
                dependent = true;
            }
            let Some((level, inst)) = self.synth_field_witness(&class, &dom)? else {
                // Report the field type with the inductive spelled by name.
                let levels: Vec<Level> =
                    ind.level_params.iter().cloned().map(Level::param).collect();
                let self_const = Expr::const_(ind.name.clone(), levels);
                let shown = dom.fold_opt_or_clone(&mut FVarToExpr {
                    fvar: self_fvar,
                    replacement: &self_const,
                });
                // Moving on to the next constructor is Lean's move only when
                // Lean fails here too. Clean's prelude lacks instances Lean has
                // (`True`, `UInt8`, `Int`, `Fin (n+1)`, `Prod`, `Pi`, ...), so a
                // failure on such a field type would silently pick a later
                // constructor than Lean's and change `default` (review r6, X6;
                // docs/DECISIONS.md R137); where both pinned Leans fail too (a
                // type this source declared with no instance, a proposition, a
                // `Fin n`, a parameter with no hypothesis, the inductive itself)
                // Clean moves on as they do. `Nonempty` is a proof whose
                // constructor cannot be observed, so it keeps moving on.
                if witness == Witness::Inhabited
                    && !lean_has_no_instance_either(&dom, self_fvar, &attempt)
                    && self.lean_init_inhabited(&dom)
                        != crate::infer::lean_init_inhabited::LeanInhabited::No
                {
                    return Err(ElabError::DerivingRefused {
                        message: format!(
                            "failed to generate 'Inhabited' instance for '{}': Clean finds no \
                             `Inhabited {}` for a field of `{ctor}`, which Lean may synthesize; \
                             taking a later constructor could change `default`",
                            ind.name, shown
                        ),
                    });
                }
                return Ok(Err(shown));
            };
            let fvar = self.fresh_fvar();
            self.push_local_with_fvar(SurfaceName::component("x", false), fvar, dom.clone());
            cur = body.instantiate(&Expr::fvar(fvar));
            field_fvars.push(fvar);
            field_insts.push((dom, level, inst));
        }

        // The terms: `Inhabited.default` / `Classical.ofNonempty` per field.
        // A dependent telescope is re-read with the earlier fields replaced by
        // their terms, and each instance synthesized again at that type.
        let mut substituted = Vec::with_capacity(field_insts.len());
        for (dom, level, inst) in field_insts {
            let (dom, level, inst) = if dependent {
                let mut ty = dom;
                for (fvar, term) in field_fvars.iter().zip(&substituted) {
                    ty = ty.fold_opt_or_clone(&mut FVarToExpr {
                        fvar: *fvar,
                        replacement: term,
                    });
                }
                match self.synth_field_witness(&class, &ty)? {
                    Some((level, inst)) => (ty, level, inst),
                    None => {
                        return Err(ElabError::FailedToSynthesize {
                            class_name: class.clone(),
                            goal: ty.to_string(),
                        })
                    }
                }
            } else {
                (dom, level, inst)
            };
            let term = match witness {
                Witness::Inhabited => Expr::apps(
                    Expr::const_(Name::from_string("Inhabited.default"), vec![level]),
                    [dom, inst],
                ),
                Witness::Nonempty => Expr::apps(
                    Expr::const_(Name::from_string("Classical.ofNonempty"), vec![level]),
                    [dom, inst],
                ),
            };
            substituted.push(term);
        }
        attempt.field_args = substituted;
        self.close_witness_instance(ind, ctor, witness, &attempt, self_fvar, &ind_ty)
            .map(Ok)
    }

    /// The `[Inhabited a]` / `[Nonempty a]` hypothesis Lean opens for a
    /// parameter `a : dom`: `Inhabited` for any `a : Sort u` (Lean's
    /// `isTypeCorrect (Inhabited a)`), `Nonempty` only for `a : Type _`
    /// (Lean's `decLevel?` on the sort).
    fn param_hypothesis(
        &mut self,
        dom: &Expr,
        param: FVarId,
        witness: Witness,
    ) -> Option<(FVarId, Expr)> {
        let ExprKind::Sort(level) = self.whnf(dom).kind().clone() else {
            return None;
        };
        if witness == Witness::Nonempty && !decrements(&level) {
            return None;
        }
        let ty = Expr::app(
            Expr::const_(Name::from_string(witness.class()), vec![level]),
            Expr::fvar(param),
        );
        Some((self.fresh_fvar(), ty))
    }

    /// Synthesize `class.{l} ty` for a field type, returning the field's sort
    /// level and a metavariable-free instance, or `None` when there is none.
    fn synth_field_witness(
        &mut self,
        class: &Name,
        ty: &Expr,
    ) -> Result<Option<(Level, Expr)>, ElabError> {
        let sort = self.infer_type(ty)?;
        let ExprKind::Sort(level) = self.whnf(&sort).kind().clone() else {
            return Ok(None);
        };
        let goal = Expr::app(Expr::const_(class.clone(), vec![level.clone()]), ty.clone());
        let Some(inst) = self.resolve_instance(&goal) else {
            return Ok(None);
        };
        let inst = self.metas.instantiate(&inst);
        if self.has_metavars(&inst) {
            return Ok(None);
        }
        Ok(Some((level, inst)))
    }

    /// Abstract the attempt into the instance declaration: `{a}` per
    /// parameter, the hypotheses a field instance used, and `⟨@C a… args…⟩`.
    fn close_witness_instance(
        &mut self,
        ind: &InductiveVal,
        ctor: &Name,
        witness: Witness,
        attempt: &Attempt,
        self_fvar: FVarId,
        ind_result: &Expr,
    ) -> Result<DerivedInstance, ElabError> {
        let ExprKind::Sort(level) = self.whnf(ind_result).kind().clone() else {
            return Err(ElabError::InternalInvariant(format!(
                "deriving {}: `{}` applied to its parameters is not a type",
                witness.class(),
                ind.name
            )));
        };
        let levels: Vec<Level> = ind.level_params.iter().cloned().map(Level::param).collect();
        let self_const = Expr::const_(ind.name.clone(), levels.clone());
        let param_args: Vec<Expr> = attempt.params.iter().map(|(f, _)| Expr::fvar(*f)).collect();
        let target = Expr::apps(self_const.clone(), param_args.clone());
        let ctor_app = Expr::apps(
            Expr::apps(Expr::const_(ctor.clone(), levels), param_args),
            attempt.field_args.iter().cloned(),
        );
        let (ty, val) = match witness {
            Witness::Inhabited => (
                Expr::app(
                    Expr::const_(Name::from_string("Inhabited"), vec![level.clone()]),
                    target.clone(),
                ),
                Expr::apps(
                    Expr::const_(Name::from_string("Inhabited.mk"), vec![level]),
                    [target, ctor_app],
                ),
            ),
            Witness::Nonempty => (
                Expr::app(
                    Expr::const_(Name::from_string("Nonempty"), vec![level.clone()]),
                    target.clone(),
                ),
                Expr::apps(
                    Expr::const_(Name::from_string("Nonempty.intro"), vec![level]),
                    [target, ctor_app],
                ),
            ),
        };

        // Binders, outermost first.
        let mut binders: Vec<(FVarId, BinderInfo, Expr)> = Vec::new();
        for ((fvar, dom), hyp) in attempt.params.iter().zip(&attempt.hyps) {
            binders.push((*fvar, BinderInfo::Implicit, dom.clone()));
            if let Some((hyp_fvar, hyp_ty)) = hyp {
                // Lean keeps a hypothesis only where a field instance used it:
                // `Inhabited`'s `usedInstIdxs`, and for `Nonempty` the
                // `variable … in` rule (pinned 4.8.0: `instNonemptyW2 : ∀
                // {α}, Nonempty (W2 α)` for `| mk (n : Nat)`).
                let used = attempt
                    .field_args
                    .iter()
                    .any(|arg| mentions_fvar(arg, *hyp_fvar));
                if used {
                    binders.push((*hyp_fvar, BinderInfo::InstImplicit, hyp_ty.clone()));
                }
            }
        }
        let mut ty = ty;
        let mut val = val;
        for (fvar, info, dom) in binders.iter().rev() {
            ty = Expr::pi(*info, dom.clone(), ty.abstract_fvar(*fvar));
            val = Expr::lam(*info, dom.clone(), val.abstract_fvar(*fvar));
        }
        let mut restore = FVarToExpr {
            fvar: self_fvar,
            replacement: &self_const,
        };
        let ty = ty.fold_opt_or_clone(&mut restore);
        let val = val.fold_opt_or_clone(&mut restore);
        if ty.has_fvar_quick() || val.has_fvar_quick() {
            return Err(ElabError::InternalInvariant(format!(
                "deriving {} for `{}` left a free variable in the instance",
                witness.class(),
                ind.name
            )));
        }
        Ok(DerivedInstance {
            name: crate::derive::builtin_instance_name(&ind.name, witness.class()),
            class_name: Name::from_string(witness.class()),
            ty,
            val,
            // Lean's `instance` command: the default priority (pinned Lean
            // 4.8.0, `getInstancePriority?` on a derived instance: 1000).
            priority: crate::instances::DEFAULT_PRIORITY,
            level_params: ind.level_params.clone(),
        })
    }
}

/// Whether a field of type `dom` that Clean found no `Inhabited` instance for
/// is one Lean finds none for either, at this point of its handler: the
/// inductive being derived applied to exactly its own parameters (no instance
/// exists until this one is built), or a bare parameter with no hypothesis
/// opened for it (the first pass of `doIt false <||> doIt true`).
fn lean_has_no_instance_either(dom: &Expr, self_fvar: FVarId, attempt: &Attempt) -> bool {
    let params: Vec<Expr> = attempt
        .params
        .iter()
        .map(|(fvar, _)| Expr::fvar(*fvar))
        .collect();
    let self_applied = matches!(dom.get_app_fn().kind(), ExprKind::FVar(id) if *id == self_fvar)
        && dom
            .get_app_args()
            .iter()
            .copied()
            .cloned()
            .eq(params.iter().cloned());
    let bare_param_without_hypothesis = match dom.kind() {
        ExprKind::FVar(id) => attempt
            .params
            .iter()
            .zip(&attempt.hyps)
            .any(|((fvar, _), hyp)| fvar == id && hyp.is_none()),
        _ => false,
    };
    self_applied || bare_param_without_hypothesis
}
