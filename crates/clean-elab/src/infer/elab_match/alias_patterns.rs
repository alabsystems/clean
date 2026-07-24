// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Alias-pattern helpers for match/do-match lowering.
//!
//! Handles:
//! - `name @ inner` rewriting onto existing inner-pattern lowering
//! - top-level `As(name, Or(...))` arm expansion
//! - helper-generated alias let bindings for expression and do-block bodies

use super::*;

fn build_surface_app(func: SurfaceExpr, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    SurfaceExpr::App(
        func.span(),
        Box::new(func),
        args.into_iter().map(SurfaceArg::positional).collect(),
    )
}

fn build_nat_succ_chain(mut expr: SurfaceExpr, k: u64) -> SurfaceExpr {
    for _ in 0..k {
        expr = build_surface_app(
            SurfaceExpr::Ident(clean_parser::Span::dummy(), "Nat.succ".to_string()),
            vec![expr],
        );
    }
    expr
}

pub(in crate::infer) fn wrap_alias_surface_body(
    alias_name: &str,
    alias_value: SurfaceExpr,
    body: &SurfaceExpr,
) -> SurfaceExpr {
    SurfaceExpr::Let(
        clean_parser::Span::dummy(),
        SurfaceBinder::new(
            alias_name.to_string(),
            None,
            clean_parser::SurfaceBinderInfo::Explicit,
        ),
        Box::new(alias_value),
        Box::new(body.clone()),
    )
}

pub(in crate::infer) fn prepend_do_alias_binding(
    alias_name: &str,
    alias_value: SurfaceExpr,
    body: &[DoElem],
) -> Vec<DoElem> {
    let mut rewritten = Vec::with_capacity(body.len() + 1);
    rewritten.push(DoElem::Let(
        clean_parser::Span::dummy(),
        SurfaceBinder::new(
            alias_name.to_string(),
            None,
            clean_parser::SurfaceBinderInfo::Explicit,
        ),
        Box::new(alias_value),
    ));
    rewritten.extend(body.iter().cloned());
    rewritten
}

/// Flatten Or-patterns into separate alternatives.
///
/// `Or(a, Or(b, c))` → `[a, b, c]`.
/// `As(x, Or(a, b))` → `[As(x, a), As(x, b)]`.
fn flatten_or_pattern(pat: &SurfacePattern) -> Vec<SurfacePattern> {
    match pat {
        SurfacePattern::Or(left, right) => {
            let mut result = flatten_or_pattern(left);
            result.extend(flatten_or_pattern(right));
            result
        }
        SurfacePattern::As(name, inner) => flatten_or_pattern(inner)
            .into_iter()
            .map(|pat| SurfacePattern::As(name.clone(), Box::new(pat)))
            .collect(),
        _ => vec![pat.clone()],
    }
}

/// Expand Or-pattern arms in a regular match into separate arms with cloned bodies.
pub(in crate::infer) fn expand_or_match_arms(
    arms: &[clean_parser::SurfaceMatchArm],
) -> Vec<clean_parser::SurfaceMatchArm> {
    let mut result = Vec::with_capacity(arms.len());
    for arm in arms {
        let flat = flatten_or_pattern(&arm.pattern);
        for pat in flat {
            result.push(clean_parser::SurfaceMatchArm {
                span: arm.span,
                pattern: pat,
                body: arm.body.clone(),
            });
        }
    }
    result
}

/// Expand Or-pattern arms in a do-match into separate arms with cloned bodies.
pub(in crate::infer) fn expand_do_or_match_arms(arms: &[DoMatchArm]) -> Vec<DoMatchArm> {
    let mut result = Vec::with_capacity(arms.len());
    for arm in arms {
        if arm.patterns.len() == 1 {
            let flat = flatten_or_pattern(&arm.patterns[0]);
            for pat in flat {
                result.push(DoMatchArm {
                    span: arm.span,
                    patterns: vec![pat],
                    body: arm.body.clone(),
                });
            }
        } else {
            result.push(arm.clone());
        }
    }
    result
}

impl<'a> ElabCtx<'a> {
    fn is_available_match_alias_name(&self, candidate: &str) -> bool {
        self.lookup_local(candidate).is_none()
            && !self
                .shared_if_let_scrutinees
                .iter()
                .any(|active| active == candidate)
            && self.env.get_const(&Name::from_string(candidate)).is_none()
    }

    pub(in crate::infer) fn fresh_match_alias_name(&mut self) -> String {
        const BASE: &str = "__match_alias";

        // Advance a counter on EVERY call so sibling and nested wildcard fields
        // within a single as-pattern rewrite each receive a DISTINCT name.
        //
        // This used to be stateless (`&self`) and returned the bare `BASE`
        // whenever `BASE` was free. But an as-pattern rewrite only BUILDS surface
        // patterns — it does not push the generated binders as locals — so
        // nothing consumed `BASE` between calls. For a multi-`_` constructor
        // pattern (`w@(_ :: _)`, `w@(List.cons _ _)`) both wildcard fields minted
        // the same `__match_alias`, collapsing head and tail onto one binder. The
        // reconstruction `List.cons __match_alias __match_alias` then unified the
        // head against the tail's `List Nat`, inferring `List (List Nat)` and
        // crashing with a "different shape: Discriminant(3) vs Discriminant(4)"
        // mismatch. Bumping `next_fvar` here guarantees uniqueness across the
        // whole rewrite (the skipped fvar ids are harmless).
        loop {
            let suffix = self.next_fvar;
            self.next_fvar += 1;
            let candidate = format!("{BASE}_{suffix}");
            if self.is_available_match_alias_name(&candidate) {
                return candidate;
            }
        }
    }

    fn rewrite_as_ctor_pattern(
        &mut self,
        context: &str,
        scrutinee_ty: &Expr,
        ctor_name: &str,
        sub_pats: &[SurfacePattern],
    ) -> Result<(SurfacePattern, SurfaceExpr), ElabError> {
        let type_name = self.get_type_name(scrutinee_ty)?;
        let expected_inductive = Name::from_string(&type_name);
        // Resolve through opened namespaces too, falling back to the literal
        // qualification so the UnknownIdent diagnostic names what the user wrote.
        let full_ctor = self.ctor_pattern_full_name(ctor_name, &type_name);
        let ctor_name = Name::from_string(&full_ctor);
        let ctor_info = self
            .env
            .get_constructor(&ctor_name)
            .cloned()
            .ok_or_else(|| ElabError::UnknownIdent(full_ctor.clone()))?;
        if ctor_info.inductive_name != expected_inductive {
            return Err(ElabError::NotImplemented(format!(
                "{context}: nested constructor {full_ctor} does not belong to field type {type_name}"
            )));
        }
        ensure_ctor_pattern_arity(
            context,
            &full_ctor,
            Some(ctor_info.num_fields as usize),
            sub_pats.len(),
        )?;

        let field_tys = self.compute_ctor_field_types(&ctor_name, scrutinee_ty)?;
        if field_tys.len() != sub_pats.len() {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{full_ctor}` exposes {} fields but the alias pattern has {} slots",
                field_tys.len(),
                sub_pats.len()
            )));
        }
        let mut rewritten_sub_pats = Vec::with_capacity(sub_pats.len());
        let mut ctor_args = Vec::with_capacity(sub_pats.len());
        for (pat, field_ty) in sub_pats.iter().zip(field_tys) {
            let (rewritten_sub_pat, ctor_arg) =
                self.rewrite_as_pattern_inner(context, &field_ty, pat)?;
            rewritten_sub_pats.push(rewritten_sub_pat);
            ctor_args.push(ctor_arg);
        }

        Ok((
            SurfacePattern::Ctor(full_ctor.clone(), rewritten_sub_pats),
            build_surface_app(
                SurfaceExpr::Ident(clean_parser::Span::dummy(), full_ctor),
                ctor_args,
            ),
        ))
    }

    pub(in crate::infer) fn rewrite_as_pattern_inner(
        &mut self,
        context: &str,
        scrutinee_ty: &Expr,
        inner_pat: &SurfacePattern,
    ) -> Result<(SurfacePattern, SurfaceExpr), ElabError> {
        match inner_pat {
            SurfacePattern::Var(name) => Ok((
                SurfacePattern::Var(name.clone()),
                SurfaceExpr::Ident(clean_parser::Span::dummy(), name.clone()),
            )),
            SurfacePattern::Wildcard => {
                let fresh = self.fresh_match_alias_name();
                Ok((
                    SurfacePattern::Var(fresh.clone()),
                    SurfaceExpr::Ident(clean_parser::Span::dummy(), fresh),
                ))
            }
            SurfacePattern::Lit(lit) => {
                let type_name = self.get_type_name(scrutinee_ty)?;
                ensure_supported_literal_pattern(context, &type_name, lit)?;
                match lit {
                    SurfaceLit::Nat(0) => Ok((
                        inner_pat.clone(),
                        SurfaceExpr::Ident(
                            clean_parser::Span::dummy(),
                            format!("{type_name}.zero"),
                        ),
                    )),
                    SurfaceLit::Nat(k) => Ok((
                        desugar_nonzero_nat_lit(*k),
                        build_nat_succ_chain(
                            SurfaceExpr::Ident(
                                clean_parser::Span::dummy(),
                                format!("{type_name}.zero"),
                            ),
                            *k,
                        ),
                    )),
                    _ => Err(ElabError::NotImplemented(format!(
                        "{context}: non-Nat literal alias pattern {lit:?}"
                    ))),
                }
            }
            SurfacePattern::NumeralAdd(inner, k) => {
                let type_name = self.get_type_name(scrutinee_ty)?;
                let binder_name =
                    numeral_add_pattern_binder_name(context, &type_name, inner.as_ref(), *k)?;
                let binder_name = if matches!(inner.as_ref(), SurfacePattern::Wildcard) {
                    self.fresh_match_alias_name()
                } else {
                    binder_name
                };
                let pred = SurfaceExpr::Ident(clean_parser::Span::dummy(), binder_name.clone());
                Ok((
                    desugar_nat_numeral_add_pattern(&SurfacePattern::Var(binder_name), *k),
                    build_nat_succ_chain(pred, *k),
                ))
            }
            SurfacePattern::Ctor(ctor_name, sub_pats) => {
                self.rewrite_as_ctor_pattern(context, scrutinee_ty, ctor_name, sub_pats)
            }
            _ => Err(ElabError::NotImplemented(format!(
                "{context}: as-pattern with inner pattern {inner_pat:?} is not supported; \
                 only variable, wildcard, literal, numeral-add, and constructor inner patterns are currently handled"
            ))),
        }
    }
}
