// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.8.0's testing and audit commands, elaborated: `#guard e`,
//! `#print axioms c` and `#guard_msgs (spec)? in cmd`.
//!
//! * `#guard e` — `Lean/Elab/Tactic/Guard.lean` `evalGuardCmd`: `e` is
//!   elaborated ensuring type `Bool` (a decidable proposition is coerced
//!   through `decide`), every metavariable must be solved, and the value must
//!   be `true`. Lean runs its compiled evaluator; Clean evaluates by KERNEL
//!   reduction instead, and records the pass as the checked `example : e =
//!   true := rfl` — a certificate every checker re-validates — so a `#guard`
//!   that passes in Clean has been proved, which Lean's does not claim. A term
//!   kernel reduction cannot bring to a `Bool` literal (an opaque or
//!   `implemented_by` function) is refused, never passed.
//! * `#print axioms c` — `Lean/Elab/Print.lean` `elabPrintAxioms`: the census
//!   is `crate::print_axioms`.
//! * `#guard_msgs` — `Lean/Elab/GuardMsgs.lean`: the comparison is
//!   `crate::guard_msgs`; this file only runs the inner command.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level, TypeChecker};
use clean_parser::{GuardMsgsSpecElt, SurfaceDecl, SurfaceExpr, SurfaceName};

use super::{CommandOutput, ElabCtx, ElabResult};
use crate::name_resolution::{resolve_global_const_no_overload, GlobalConstResolution};
use crate::print_axioms::{axioms_message, collect_axioms, lean_name_to_string, PrintAxiomsResult};
use crate::ElabError;

impl ElabCtx<'_> {
    /// `#guard e`.
    pub(super) fn elab_guard_cmd(&mut self, expr: &SurfaceExpr) -> Result<ElabResult, ElabError> {
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        // A value position: an unknown identifier is an error, never an
        // auto-bound implicit, and `variable`s are not in scope (Lean
        // elaborates `#guard` without them).
        let elaborated =
            self.with_term_body_scope(|this| this.elaborate_with_type(expr, bool_ty.clone()))?;
        let elaborated = self.metas.instantiate(&elaborated);
        let elaborated = self.metas.instantiate_levels(&elaborated);
        // Lean: `synthesizeSyntheticMVarsNoPostponing`, then any metavariable
        // left is reported instead of evaluated.
        self.ensure_no_residual_fvars("#guard", &SurfaceName::default(), &elaborated, None)?;
        if !clean_kernel::env::collect_fvar_ids_for_diagnostics(&[&elaborated]).is_empty() {
            return Err(ElabError::CommandFailed {
                message: format!(
                    "#guard: don't know how to synthesize the placeholders of\n  {elaborated}"
                ),
            });
        }
        let tc = TypeChecker::new(self.env);
        let ty = tc
            .infer_type(&elaborated)
            .map_err(|e| ElabError::KernelCheckFailed {
                name: Name::from_string("#guard"),
                detail: e.to_string(),
            })?;
        if !tc.is_def_eq(&ty, &bool_ty) {
            return Err(ElabError::TypeMismatch {
                expected: bool_ty.to_string(),
                actual: ty.to_string(),
            });
        }
        let value = tc.whnf(&elaborated);
        match value.kind() {
            ExprKind::Const(name, _) if *name == Name::from_string("Bool.true") => {
                let bool_level = vec![Level::succ(Level::zero())];
                let true_ = Expr::const_(Name::from_string("Bool.true"), vec![]);
                let eq = Expr::const_(Name::from_string("Eq"), bool_level.clone());
                let ty = Expr::app(
                    Expr::app(Expr::app(eq, bool_ty.clone()), elaborated),
                    true_.clone(),
                );
                let refl = Expr::const_(Name::from_string("Eq.refl"), bool_level);
                let val = Expr::app(Expr::app(refl, bool_ty), true_);
                Ok(ElabResult::Example { ty, val })
            }
            ExprKind::Const(name, _) if *name == Name::from_string("Bool.false") => {
                Err(ElabError::CommandFailed {
                    message: format!("expression\n  {elaborated}\ndid not evaluate to `true`"),
                })
            }
            _ => Err(ElabError::CommandFailed {
                message: format!(
                    "expression\n  {elaborated}\ncould not be evaluated by kernel reduction: it \
                     reduced to\n  {value}\nwhich is not a `Bool` literal"
                ),
            }),
        }
    }

    /// `#print axioms c`: one census per constant `c` resolves to.
    pub(super) fn elab_print_axioms_cmd(
        &self,
        name: &SurfaceName,
    ) -> Result<ElabResult, ElabError> {
        let constants = match resolve_global_const_no_overload(
            name,
            &self.namespace_state,
            self.env,
            &self.foreign_private_decls,
        ) {
            Ok(constant) => vec![constant],
            // `realizeGlobalConstWithInfos` keeps every interpretation and
            // `printAxiomsOf` runs on each.
            Err(GlobalConstResolution::Ambiguous(constants)) => constants,
            Err(GlobalConstResolution::Unknown) => {
                return Err(ElabError::CommandFailed {
                    message: format!("unknown constant '{}'", lean_name_to_string(name.name())),
                })
            }
        };
        let mut messages = Vec::with_capacity(constants.len());
        for constant in &constants {
            let axioms =
                collect_axioms(self.env, constant).map_err(|refusal| ElabError::CommandFailed {
                    message: refusal.to_string(),
                })?;
            messages.push(axioms_message(constant, &axioms));
        }
        Ok(ElabResult::Command(CommandOutput::PrintAxioms(
            PrintAxiomsResult { messages },
        )))
    }

    /// `#guard_msgs (spec)? in cmd`, for a caller that registers what this
    /// returns (the block elaborators of this context). The file-level
    /// pipeline runs `cmd` through registration itself
    /// (`crate::elaborate_decl_and_register_inner`), so a kernel refusal at
    /// registration is one of the messages compared there.
    pub(super) fn elab_guard_msgs_cmd(
        &mut self,
        doc: Option<&str>,
        spec: &[GuardMsgsSpecElt],
        cmd: &SurfaceDecl,
    ) -> Result<ElabResult, ElabError> {
        let outcome = self.elab_decl_inner(cmd);
        crate::guard_msgs::conclude(doc, spec, outcome, None)
    }
}
