// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Equation theorems whose recursion is visible only in their proof terms.
//!
//! The ordinary theorem entry retains modifier validation, where desugaring,
//! explicit termination handling, section pruning and finalization. This body
//! stage uses a hidden forward declaration and the existing one-member SCC
//! lift, so calls inside arbitrary tactic terms need no surface name scan.

use clean_kernel::{Expr, ExprKind, FVarId};
use clean_parser::{DeclModifiers, SurfaceBinder, SurfaceExpr, SurfaceName};

use super::elaborate_decl::PrivateNameKind;
use super::mutual_lift::PreDef;
use super::ElabCtx;
use crate::ElabError;

/// The prefix is identified by semantic section-variable marks assigned by
/// preprocessing, rather than by identifier text or source-position guesses.
#[derive(Clone)]
pub(super) struct SingleTheoremCapture {
    forward: FVarId,
    auto_implicits: Vec<(SurfaceName, FVarId, Expr)>,
    own_auto_implicits: Vec<(SurfaceName, FVarId, Expr)>,
    sections: Vec<SurfaceName>,
    section_arguments: Vec<FVarId>,
    remaining_header: Expr,
    header_binders_left: usize,
    header_fvars: Vec<FVarId>,
    body_entered: bool,
}

impl ElabCtx<'_> {
    /// A local helper inside a header annotation has its own binders. It must
    /// not consume the enclosing theorem's declaration-header telescope.
    pub(super) fn elaborate_single_theorem_header_annotation(
        &mut self,
        annotation: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        if !self
            .single_theorem_capture
            .as_ref()
            .is_some_and(|capture| !capture.body_entered)
        {
            return self.elaborate_type_observing(annotation);
        }
        let capture = self.single_theorem_capture.take();
        let result = self.elaborate_type_observing(annotation);
        self.single_theorem_capture = capture;
        result
    }

    pub(super) fn elab_single_equation_theorem(
        &mut self,
        name: &SurfaceName,
        binders: &[SurfaceBinder],
        public_binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        proof: &SurfaceExpr,
        modifiers: &DeclModifiers,
    ) -> Result<(Expr, Expr, usize), ElabError> {
        let auxiliary = self.aux_decl_locals.clone();
        let auto_implicits = self.auto_implicits.clone();
        let auto_lookup = self.auto_implicit_lookup.clone();
        let lift_mark = self.mutual_lift_entries.len();
        let previous_capture = self.single_theorem_capture.take();
        let result = self.with_local_scope_rollback(|this| {
            this.elab_single_equation_theorem_inner(
                name,
                binders,
                public_binders,
                ty,
                proof,
                modifiers,
            )
        });
        self.single_theorem_capture = previous_capture;
        if result.is_err() {
            self.auto_implicits = auto_implicits;
            self.auto_implicit_lookup = auto_lookup;
            self.mutual_lift_entries.truncate(lift_mark);
        }
        self.aux_decl_locals = auxiliary;
        result
    }

    fn elab_single_equation_theorem_inner(
        &mut self,
        name: &SurfaceName,
        binders: &[SurfaceBinder],
        public_binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        proof: &SurfaceExpr,
        modifiers: &DeclModifiers,
    ) -> Result<(Expr, Expr, usize), ElabError> {
        // Allocate the forward local before opening the header. The prepared
        // result's forall locals must start above this auxiliary, just as
        // tactic introductions do when the forward local is in their scope.
        // Otherwise the exact-type forall-name records keep different local
        // identities from the hypotheses introduced from that same result.
        let fvar = self.fresh_fvar();
        let (signature, header_fvars, section_auto_count) = self.elab_def_header(binders, ty)?;
        let signature = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&signature));
        // Generalize the header's auto-implicits on the forward declaration,
        // while keeping their locals available to the body. Recursive calls
        // then pass exactly the same implicit prefix as the final theorem.
        let header_auto = self.snapshot_auto_implicits_since(0);
        let remaining_header = signature.clone();
        let section_count = Self::section_binder_count(binders);
        let section_fvars = header_fvars.get(..section_count).ok_or_else(|| {
            ElabError::InternalInvariant("single theorem lost its section locals".to_string())
        })?;
        let (signature, captured_auto_count) = self.wrap_decl_type_auto_implicits(
            section_count,
            signature,
            &header_auto,
            Some(section_fvars),
        )?;
        if captured_auto_count > section_auto_count {
            return Err(ElabError::InternalInvariant(
                "single theorem section auto dependency exceeds its header packet".to_string(),
            ));
        }
        let own_auto = header_auto.get(captured_auto_count..).ok_or_else(|| {
            ElabError::InternalInvariant(
                "single theorem section auto-prefix exceeds its header packet".to_string(),
            )
        })?;
        let own_auto = own_auto.to_vec();
        self.push_local_with_fvar(name.clone(), fvar, signature);
        self.aux_decl_locals.insert(fvar);
        let sections: Vec<SurfaceName> = binders
            .iter()
            .take_while(|binder| binder.name.is_section_variable())
            .map(|binder| binder.name.clone())
            .collect();
        self.single_theorem_capture = Some(SingleTheoremCapture {
            forward: fvar,
            auto_implicits: header_auto,
            own_auto_implicits: own_auto,
            sections,
            section_arguments: Vec::new(),
            remaining_header,
            header_binders_left: binders.len(),
            header_fvars,
            body_entered: false,
        });
        let (ty_expr, proof_expr, section_fvars) = self.elab_decl_body(binders, Some(ty), proof)?;
        let ty_expr = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&ty_expr));
        let proof_expr = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&proof_expr));
        let auto_implicits = self.take_auto_implicits();
        let (ty_expr, proof_expr, auto_count) = self.wrap_decl_auto_implicits(
            section_count,
            ty_expr,
            proof_expr,
            &auto_implicits,
            Some(&section_fvars),
        )?;
        let decl_name = self.kernel_decl_name(name, modifiers, PrivateNameKind::Theorem);
        let declaration = PreDef {
            name: decl_name.clone(),
            fvar,
            is_theorem: true,
            universe_params: self
                .universe_params
                .iter()
                .map(|p| p.name().clone())
                .collect(),
            ty: ty_expr,
            val: proof_expr,
            structural_major: None,
        };
        let mut lowered = self.lower_mutual_predefs(&[declaration])?;
        self.locals.retain(|(_, id, _)| *id != fvar);
        match lowered.pop() {
            Some(member) if lowered.is_empty() => {
                self.note_public_param_infos(
                    &decl_name,
                    public_binders,
                    &auto_implicits,
                    auto_count,
                );
                Ok((member.ty, member.val, auto_count))
            }
            _ => Err(ElabError::InternalInvariant(
                "single theorem pre-definition did not produce exactly one member".to_string(),
            )),
        }
    }

    /// Reopen the original header telescope, preserving both rigid Sort*
    /// universes and any local-helper captures created while elaborating it.
    pub(super) fn single_theorem_prepared_binder(
        &self,
    ) -> Result<Option<(FVarId, Expr)>, ElabError> {
        let Some(capture) = self.single_theorem_capture.as_ref() else {
            return Ok(None);
        };
        if capture.body_entered || capture.header_binders_left == 0 {
            return Ok(None);
        }
        let Some(index) = capture
            .header_fvars
            .len()
            .checked_sub(capture.header_binders_left)
        else {
            return Err(ElabError::InternalInvariant(
                "single theorem header binder count exceeds its telescope".to_string(),
            ));
        };
        let Some(fvar) = capture.header_fvars.get(index) else {
            return Err(ElabError::InternalInvariant(
                "single theorem header has no recorded binder".to_string(),
            ));
        };
        let header = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&capture.remaining_header));
        let ExprKind::Pi(_, domain, _) = header.kind() else {
            return Err(ElabError::InternalInvariant(
                "single theorem prepared header lost its binder".to_string(),
            ));
        };
        Ok(Some((*fvar, domain.as_ref().clone())))
    }

    pub(super) fn single_theorem_prepared_result_type(&self) -> Option<Expr> {
        let capture = self.single_theorem_capture.as_ref()?;
        (capture.header_binders_left == 0 && !capture.body_entered).then(|| {
            self.metas
                .instantiate_levels(&self.metas.instantiate(&capture.remaining_header))
        })
    }

    pub(super) fn note_single_theorem_header_binder(
        &mut self,
        name: &SurfaceName,
        fvar: FVarId,
        ty: &Expr,
    ) -> Result<Option<SingleTheoremCapture>, ElabError> {
        let Some(mut capture) = self.single_theorem_capture.take() else {
            return Ok(None);
        };
        if capture.header_binders_left == 0 || capture.body_entered {
            self.single_theorem_capture = Some(capture);
            return Ok(None);
        }
        let mark = capture.clone();
        let header = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&capture.remaining_header));
        let ExprKind::Pi(_, domain, body) = header.kind() else {
            self.single_theorem_capture = Some(capture);
            return Err(ElabError::InternalInvariant(
                "single theorem body has more binders than its header".to_string(),
            ));
        };
        if !self.try_unify(domain, ty) {
            self.single_theorem_capture = Some(capture);
            return Err(ElabError::TypeMismatch {
                expected: domain.to_string(),
                actual: ty.to_string(),
            });
        }
        self.commit_pending_level_assigns();
        capture.remaining_header = body.instantiate(&Expr::fvar(fvar));
        capture.header_binders_left -= 1;
        if name.is_section_variable()
            && capture.sections.get(capture.section_arguments.len()) == Some(name)
        {
            capture.section_arguments.push(fvar);
        }
        self.single_theorem_capture = Some(capture);
        Ok(Some(mark))
    }

    pub(super) fn restore_single_theorem_header_binder(
        &mut self,
        mark: Option<SingleTheoremCapture>,
    ) {
        if let Some(mark) = mark {
            self.single_theorem_capture = Some(mark);
        }
    }

    pub(super) fn sync_single_theorem_result_type(&mut self, ty: &Expr) -> Result<(), ElabError> {
        let Some(mut capture) = self.single_theorem_capture.take() else {
            return Ok(());
        };
        if capture.header_binders_left != 0 || capture.body_entered {
            self.single_theorem_capture = Some(capture);
            return Ok(());
        }
        let expected = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&capture.remaining_header));
        let valid = self.try_unify(&expected, ty);
        self.commit_pending_level_assigns();
        capture.body_entered = true;
        self.single_theorem_capture = Some(capture);
        if valid {
            Ok(())
        } else {
            Err(ElabError::TypeMismatch {
                expected: expected.to_string(),
                actual: ty.to_string(),
            })
        }
    }

    pub(super) fn single_theorem_captured_reference(&self, id: FVarId) -> Option<Expr> {
        let capture = self.single_theorem_capture.as_ref()?;
        if capture.forward != id || capture.sections.is_empty() {
            return None;
        }
        let mut reference = Expr::fvar(id);
        let captured = capture.auto_implicits.len() - capture.own_auto_implicits.len();
        for argument in capture.auto_implicits[..captured]
            .iter()
            .map(|(_, id, _)| id)
            .chain(&capture.section_arguments)
            .chain(capture.own_auto_implicits.iter().map(|(_, id, _)| id))
        {
            reference = Expr::app(reference, Expr::fvar(*argument));
        }
        // Section arguments are captured, but the theorem's own implicit
        // header arguments remain binders of its recursive reference. In
        // particular, `@f α ...` still explicitly supplies such an argument.
        let (_, reference) =
            Self::wrap_with_auto_implicits(Expr::prop(), reference, &capture.own_auto_implicits);
        Some(reference)
    }
}
