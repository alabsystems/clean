// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The template walk over patterns: the names a pattern binds, their
//! scopes, and the terms a pattern carries (see the parent module doc).

use super::*;

impl Walker<'_> {
    // ------------------------------------------------------------------
    // Patterns
    // ------------------------------------------------------------------
    /// A bare pattern identifier: a binder or a constructor (module doc).
    pub(super) fn pattern_var(
        &mut self,
        name: &SurfaceName,
        binds: &mut PatternBinds,
    ) -> Walked<SurfaceName> {
        if name.is_relative_constructor() {
            return self.relative_constructor(name);
        }
        if Self::inert(name) {
            return Ok(name.clone());
        }
        if name.template_scope().is_some() {
            // Marked by the marking walk (or by a notation expanded inside
            // this template): a scoped pattern variable.
            if self.mark.is_some() {
                return Ok(name.clone());
            }
            if let Some(out) = binds.get(name) {
                return Ok(out.clone());
            }
            let out = self.rescope(name);
            binds
                .0
                .push((name.clone(), out.clone(), Binding::Pattern(out.clone())));
            return Ok(out);
        }
        if Self::foreign(name) {
            return Ok(name.clone());
        }
        if let Some(out) = binds.get(name) {
            return Ok(out.clone());
        }
        if let Some(index) = self.operand_index(name) {
            // The pattern variable IS the operand.
            return if self.mark.is_some() {
                Ok(name.clone())
            } else {
                self.operand_identifier(index, "a pattern variable")
            };
        }
        let (out, binding) = match &self.mark {
            Some(mark) => {
                // A spelling bound to a template binder, or to a section
                // variable where the template is declared, names a LOCAL:
                // the pattern identifier is certainly a binder (Lean's
                // `processId` finds the local). Otherwise it is a binder or a
                // constructor by what it resolves to at the declaration.
                let certainly_binder = matches!(self.lookup(name), Some(Binding::Bound(_)))
                    || mark.section_variables.iter().any(|var| var == name);
                if certainly_binder {
                    (name.clone(), Binding::Bound(name.clone()))
                } else {
                    let out = name
                        .clone()
                        .with_template_origin(Arc::clone(&mark.plain))
                        .with_template_scope(fresh_scope());
                    self.record(&out);
                    (out.clone(), Binding::Pattern(out))
                }
            }
            // Unhygienic: the pattern identifier is kept as written, and the
            // use site classifies it.
            None if !self.hygienic => (name.clone(), Binding::Bound(name.clone())),
            None => {
                // Unscoped after the marking walk: certainly a binder.
                let fresh = Self::fresh(name);
                (fresh.clone(), Binding::Bound(fresh))
            }
        };
        binds.0.push((name.clone(), out.clone(), binding));
        Ok(out)
    }

    /// An `n@p` name: always a binder.
    pub(super) fn pattern_alias(
        &mut self,
        name: &SurfaceName,
        binds: &mut PatternBinds,
    ) -> Walked<SurfaceName> {
        if Self::inert(name) || Self::foreign(name) {
            return Ok(name.clone());
        }
        if let Some(out) = binds.get(name) {
            return Ok(out.clone());
        }
        let (out, binding) = self.binder_name(name)?;
        if let Some(binding) = binding {
            binds.0.push((name.clone(), out.clone(), binding));
        }
        Ok(out)
    }

    /// The shape of a pattern: its names classified and written out, its
    /// constructor heads resolved as references. Inaccessible terms are
    /// walked afterwards ([`Self::pattern_terms`]), once the pattern's own
    /// variables are in scope.
    pub(super) fn pattern_shape(
        &mut self,
        pattern: &SurfacePattern,
        binds: &mut PatternBinds,
    ) -> Walked<SurfacePattern> {
        Ok(match pattern {
            SurfacePattern::Var(name) => SurfacePattern::Var(self.pattern_var(name, binds)?),
            SurfacePattern::Ctor(head, args) => {
                let head = self.reference_name(head)?;
                let args = args
                    .iter()
                    .map(|arg| self.pattern_shape(arg, binds))
                    .collect::<Walked<Vec<_>>>()?;
                SurfacePattern::Ctor(head, args)
            }
            SurfacePattern::As(name, inner) => {
                let name = self.pattern_alias(name, binds)?;
                SurfacePattern::As(name, Box::new(self.pattern_shape(inner, binds)?))
            }
            SurfacePattern::Or(left, right) => SurfacePattern::Or(
                Box::new(self.pattern_shape(left, binds)?),
                Box::new(self.pattern_shape(right, binds)?),
            ),
            SurfacePattern::NumeralAdd(inner, k) => {
                SurfacePattern::NumeralAdd(Box::new(self.pattern_shape(inner, binds)?), *k)
            }
            // `{ x := p, .. } : S`: each field name is a name position (the
            // operand there, as in a structure-instance term), each field
            // pattern a pattern, the ascription a term.
            SurfacePattern::StructInst {
                fields,
                ellipsis,
                ty,
            } => SurfacePattern::StructInst {
                fields: fields
                    .iter()
                    .map(|(name, pat)| {
                        Ok((
                            self.name_position(name, "a structure-instance pattern field")?,
                            self.pattern_shape(pat, binds)?,
                        ))
                    })
                    .collect::<Walked<Vec<_>>>()?,
                ellipsis: *ellipsis,
                ty: ty.as_deref().map(|ty| self.boxed(ty)).transpose()?,
            },
            SurfacePattern::Wildcard => SurfacePattern::Wildcard,
            SurfacePattern::Ellipsis => SurfacePattern::Ellipsis,
            SurfacePattern::Lit(lit) => SurfacePattern::Lit(lit.clone()),
            SurfacePattern::Inaccessible(term) => SurfacePattern::Inaccessible(term.clone()),
            SurfacePattern::QPattern(_) => {
                return Err(TemplateRefusal::new(
                    "a Qq pattern `q(…)` in a notation or macro template is not supported",
                ))
            }
        })
    }

    /// Walk the inaccessible terms of a shaped pattern.
    pub(super) fn pattern_terms(&mut self, pattern: SurfacePattern) -> Walked<SurfacePattern> {
        Ok(match pattern {
            SurfacePattern::Inaccessible(term) => {
                SurfacePattern::Inaccessible(Box::new(self.expr(&term)?))
            }
            SurfacePattern::Ctor(head, args) => SurfacePattern::Ctor(
                head,
                args.into_iter()
                    .map(|arg| self.pattern_terms(arg))
                    .collect::<Walked<Vec<_>>>()?,
            ),
            SurfacePattern::As(name, inner) => {
                SurfacePattern::As(name, Box::new(self.pattern_terms(*inner)?))
            }
            SurfacePattern::Or(left, right) => SurfacePattern::Or(
                Box::new(self.pattern_terms(*left)?),
                Box::new(self.pattern_terms(*right)?),
            ),
            SurfacePattern::NumeralAdd(inner, k) => {
                SurfacePattern::NumeralAdd(Box::new(self.pattern_terms(*inner)?), k)
            }
            SurfacePattern::StructInst {
                fields,
                ellipsis,
                ty,
            } => SurfacePattern::StructInst {
                fields: fields
                    .into_iter()
                    .map(|(name, pat)| Ok((name, self.pattern_terms(pat)?)))
                    .collect::<Walked<Vec<_>>>()?,
                ellipsis,
                ty,
            },
            leaf @ (SurfacePattern::Var(_)
            | SurfacePattern::Wildcard
            | SurfacePattern::Ellipsis
            | SurfacePattern::Lit(_)
            | SurfacePattern::QPattern(_)) => leaf,
        })
    }

    /// Walk `patterns` and bring the names they bind into scope (the caller
    /// truncates the environment when their scope ends).
    pub(super) fn patterns_in_scope(
        &mut self,
        patterns: &[SurfacePattern],
    ) -> Walked<Vec<SurfacePattern>> {
        let mut binds = PatternBinds::default();
        let shaped = patterns
            .iter()
            .map(|pattern| self.pattern_shape(pattern, &mut binds))
            .collect::<Walked<Vec<_>>>()?;
        self.bring_into_scope(binds);
        shaped
            .into_iter()
            .map(|pattern| self.pattern_terms(pattern))
            .collect()
    }

    /// [`Self::patterns_in_scope`] for one pattern.
    pub(super) fn pattern_in_scope(&mut self, pattern: &SurfacePattern) -> Walked<SurfacePattern> {
        let mut binds = PatternBinds::default();
        let shaped = self.pattern_shape(pattern, &mut binds)?;
        self.bring_into_scope(binds);
        self.pattern_terms(shaped)
    }

    /// Push the names a pattern binds, in order (the caller truncates the
    /// environment when their scope ends).
    pub(super) fn bring_into_scope(&mut self, binds: PatternBinds) {
        for (written, _, binding) in binds.0 {
            self.env.push((written, binding));
        }
    }

    /// A pattern whose names REFER to variables already in scope (`(a, b)
    /// := e` reassigns the mutable `a` and `b`).
    pub(super) fn pattern_refs(&mut self, pattern: &SurfacePattern) -> Walked<SurfacePattern> {
        Ok(match pattern {
            SurfacePattern::Var(name) => SurfacePattern::Var(self.reference_name(name)?),
            SurfacePattern::Ctor(head, args) => SurfacePattern::Ctor(
                self.reference_name(head)?,
                args.iter()
                    .map(|arg| self.pattern_refs(arg))
                    .collect::<Walked<Vec<_>>>()?,
            ),
            SurfacePattern::As(name, inner) => SurfacePattern::As(
                self.reference_name(name)?,
                Box::new(self.pattern_refs(inner)?),
            ),
            SurfacePattern::Or(left, right) => SurfacePattern::Or(
                Box::new(self.pattern_refs(left)?),
                Box::new(self.pattern_refs(right)?),
            ),
            SurfacePattern::NumeralAdd(inner, k) => {
                SurfacePattern::NumeralAdd(Box::new(self.pattern_refs(inner)?), *k)
            }
            SurfacePattern::StructInst {
                fields,
                ellipsis,
                ty,
            } => SurfacePattern::StructInst {
                fields: fields
                    .iter()
                    .map(|(name, pat)| {
                        Ok((
                            self.name_position(name, "a structure-instance pattern field")?,
                            self.pattern_refs(pat)?,
                        ))
                    })
                    .collect::<Walked<Vec<_>>>()?,
                ellipsis: *ellipsis,
                ty: ty.as_deref().map(|ty| self.boxed(ty)).transpose()?,
            },
            SurfacePattern::Inaccessible(term) => SurfacePattern::Inaccessible(self.boxed(term)?),
            SurfacePattern::Wildcard => SurfacePattern::Wildcard,
            SurfacePattern::Ellipsis => SurfacePattern::Ellipsis,
            SurfacePattern::Lit(lit) => SurfacePattern::Lit(lit.clone()),
            SurfacePattern::QPattern(_) => {
                return Err(TemplateRefusal::new(
                    "a Qq pattern `q(…)` in a notation or macro template is not supported",
                ))
            }
        })
    }

    /// `| p => b`: the arm's pattern variables are bound in its body.
    pub(super) fn match_arm(&mut self, arm: &SurfaceMatchArm) -> Walked<SurfaceMatchArm> {
        let depth = self.env.len();
        let pattern = self.pattern_in_scope(&arm.pattern)?;
        let body = self.expr(&arm.body)?;
        self.env.truncate(depth);
        Ok(SurfaceMatchArm {
            span: arm.span,
            pattern,
            body,
        })
    }
}
