// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The template walk over terms: applications, projections, the
//! expression node dispatch, structure literals, levels and `calc` (see
//! the parent module doc).

use super::*;

impl Walker<'_> {
    // ------------------------------------------------------------------
    // Terms
    // ------------------------------------------------------------------
    pub(super) fn boxed(&mut self, expr: &SurfaceExpr) -> Walked<Box<SurfaceExpr>> {
        self.expr(expr).map(Box::new)
    }

    pub(super) fn arg(&mut self, arg: &SurfaceArg) -> Walked<SurfaceArg> {
        Ok(SurfaceArg {
            span: arg.span,
            expr: self.expr(&arg.expr)?,
            // A named argument's name is a PARAMETER name, not a reference.
            name: arg
                .name
                .as_ref()
                .map(|name| self.name_position(name, "a named-argument name"))
                .transpose()?,
        })
    }

    /// The dotted spelling a (walked) receiver chain `r.f₁.….fₖ` forms when
    /// its leading identifier is a marked free reference.
    pub(super) fn marked_chain(expr: &SurfaceExpr) -> Option<SurfaceName> {
        match expr {
            SurfaceExpr::Ident(_, name)
                if name.template_origin().is_some() && name.template_scope().is_none() =>
            {
                Some(name.clone())
            }
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                Self::marked_chain(base).map(|base| base.append(field))
            }
            _ => None,
        }
    }

    /// Whether the field `.field` of the projection node spanning `proj_span`
    /// is written right after its receiver `base`, with no gap: the parser
    /// reads `x.f` and `(e).f.g` as projection chains, where Lean's lexer reads
    /// ONE identifier token (`x.f`) and one `rawIdent` (`f.g`).
    pub(super) fn field_is_adjacent(
        proj_span: Span,
        base: &SurfaceExpr,
        field: &SurfaceName,
    ) -> bool {
        let Some(spelling) = field.source_spelling() else {
            return false;
        };
        let base_end = base.span().end;
        base_end != 0 && proj_span.end == base_end + 1 + spelling.len()
    }

    /// `e.f`. Lean's `notation` antiquotes an identifier token spelled like an
    /// operand variable, and a gap-free run of dotted names is ONE token:
    ///
    /// * `x.f₁.….fₖ` (an identifier, then fields with no gap) is the
    ///   identifier `x.f₁.….fₖ` — never an operand variable, so neither `x`
    ///   nor a field is antiquoted, and `x` is a free name of the template
    ///   (Lean: with `def x.succ := 77`, `x.succ` in a template over `x` is
    ///   `77`, not the operand's successor);
    /// * `(e).f` (one field after a non-identifier) is a projection whose
    ///   field token is `f`: an operand-variable `f` is antiquoted
    ///   (`(sx0).x` with the operand `w` is `(sx0).w`);
    /// * `(e).f.g` is the field token `f.g`: nothing is antiquoted.
    pub(super) fn projection(
        &mut self,
        span: Span,
        base: &SurfaceExpr,
        projection: &Projection,
    ) -> Walked<SurfaceExpr> {
        let Projection::Named(field) = projection else {
            return Ok(SurfaceExpr::Proj(
                span,
                self.boxed(base)?,
                projection.clone(),
            ));
        };
        // The gap-free run of named fields ending here, outermost first, and
        // the expression it is written on.
        let mut run: Vec<(Span, &SurfaceName)> = vec![(span, field)];
        // The innermost link of the run so far (its last element).
        let (mut link_span, mut link_field) = (span, field);
        let mut head = base;
        let mut head_adjacent;
        loop {
            head_adjacent = Self::field_is_adjacent(link_span, head, link_field);
            match head {
                SurfaceExpr::Proj(inner_span, inner_base, Projection::Named(inner_field))
                    if head_adjacent =>
                {
                    (link_span, link_field) = (*inner_span, inner_field);
                    run.push((link_span, link_field));
                    head = inner_base;
                }
                _ => break,
            }
        }
        let identifier_head = head_adjacent && matches!(head, SurfaceExpr::Ident(..));
        let walked_head = match head {
            // `x.f…` on an operand variable `x`: one identifier, a free name.
            SurfaceExpr::Ident(ident_span, name)
                if identifier_head
                    && !Self::foreign(name)
                    && self.operand_index(name).is_some() =>
            {
                match &self.mark {
                    Some(_) => SurfaceExpr::Ident(*ident_span, self.free_reference(name)),
                    None => head.clone(),
                }
            }
            _ => self.expr(head)?,
        };
        let substitutable = !identifier_head && run.len() == 1;
        let mut out = walked_head;
        for (link_span, link_field) in run.into_iter().rev() {
            let link_field = if substitutable {
                self.name_position(link_field, "a projection field")?
            } else {
                link_field.clone()
            };
            if let Some(chain) = Self::marked_chain(&out) {
                self.record(&chain.append(&link_field));
            }
            out = SurfaceExpr::Proj(link_span, Box::new(out), Projection::Named(link_field));
        }
        Ok(out)
    }

    /// Every recursion of the walk passes through here, so the stack is
    /// grown on demand as the parser's own expression entry does
    /// (`Parser::expr_in_slot`): a notation's operands are whole user terms,
    /// and the walk runs inside the parser, between its stack checkpoints.
    /// Without it, a 1 MB elaboration thread overflowed while expanding the
    /// codata seed's notations (regression pin
    /// `codata_cmd_tests::test_codata_stream_encoding_survives_small_thread_stack`).
    pub(super) fn expr(&mut self, expr: &SurfaceExpr) -> Walked<SurfaceExpr> {
        stacker::maybe_grow(WALK_STACK_RED_ZONE, WALK_STACK_GROW_SIZE, || {
            self.expr_node(expr)
        })
    }

    #[allow(clippy::too_many_lines)] // one arm per surface node kind, by design
    pub(super) fn expr_node(&mut self, expr: &SurfaceExpr) -> Walked<SurfaceExpr> {
        Ok(match expr {
            SurfaceExpr::Ident(span, name) => self.reference(*span, name)?,
            SurfaceExpr::SyntheticSorry(_)
            | SurfaceExpr::Lit(..)
            | SurfaceExpr::Hole(_)
            // A nested quotation is text: its identifiers belong to the
            // syntax it builds, not to this template's scope.
            | SurfaceExpr::SyntaxQuote(..)
            // A spliced operand of a macro template: caller syntax.
            | SurfaceExpr::QAntiquot { .. } => expr.clone(),
            SurfaceExpr::Universe(span, universe) => {
                SurfaceExpr::Universe(*span, self.universe(universe)?)
            }
            // A `?x` names a goal, not a term. Its identifier is antiquoted
            // like any other: `?x` with the operand `w` is `?w`, and with an
            // operand that is no identifier Lean's `elabSyntheticHole` finds
            // no name (`arg.isIdent` fails) and makes the anonymous `?_`.
            SurfaceExpr::NamedHole(span, name) => {
                match (self.mark.is_none() && !Self::foreign(name))
                    .then(|| self.operand_index(name))
                    .flatten()
                {
                    Some(index) => match self.operand_identifier(index, "a goal name") {
                        Ok(operand) => SurfaceExpr::NamedHole(*span, operand),
                        Err(_) => SurfaceExpr::Hole(*span),
                    },
                    None => expr.clone(),
                }
            }
            SurfaceExpr::App(span, func, args) => {
                let func = self.boxed(func)?;
                let args = args
                    .iter()
                    .map(|arg| self.arg(arg))
                    .collect::<Walked<Vec<_>>>()?;
                SurfaceExpr::App(*span, func, args)
            }
            SurfaceExpr::Lambda(span, binders, body) => {
                let (binders, body) = self.telescope(binders, body)?;
                SurfaceExpr::Lambda(*span, binders, body)
            }
            SurfaceExpr::PatternMatchLambda(span, binders, body) => {
                let (binders, body) = self.telescope(binders, body)?;
                SurfaceExpr::PatternMatchLambda(*span, binders, body)
            }
            SurfaceExpr::Pi(span, binders, body) => {
                let (binders, body) = self.telescope(binders, body)?;
                SurfaceExpr::Pi(*span, binders, body)
            }
            SurfaceExpr::Arrow(span, dom, cod) => {
                SurfaceExpr::Arrow(*span, self.boxed(dom)?, self.boxed(cod)?)
            }
            SurfaceExpr::Let(span, binder, val, body) => {
                let depth = self.env.len();
                let mut binder_out = self.binder_parts(binder)?;
                let val = self.boxed(val)?;
                binder_out.name = self.bind(&binder.name)?;
                let body = self.boxed(body)?;
                self.env.truncate(depth);
                SurfaceExpr::Let(*span, binder_out, val, body)
            }
            SurfaceExpr::Have(span, binder, val, body) => {
                let depth = self.env.len();
                let mut binder_out = self.binder_parts(binder)?;
                let val = self.boxed(val)?;
                binder_out.name = self.bind(&binder.name)?;
                let body = self.boxed(body)?;
                self.env.truncate(depth);
                SurfaceExpr::Have(*span, binder_out, val, body)
            }
            // `let rec f := v; b`: `f` is in scope in `v` as well as `b`.
            SurfaceExpr::LetRec(span, binder, val, body) => {
                let depth = self.env.len();
                let binder = self.binder(binder)?;
                let val = self.boxed(val)?;
                let body = self.boxed(body)?;
                self.env.truncate(depth);
                SurfaceExpr::LetRec(*span, binder, val, body)
            }
            SurfaceExpr::LetPattern(..) => {
                return Err(TemplateRefusal::new(
                    "a Qq `let q(…) := …` in a notation or macro template is not supported",
                ))
            }
            SurfaceExpr::Paren(span, inner) => SurfaceExpr::Paren(*span, self.boxed(inner)?),
            SurfaceExpr::Ascription(span, inner, ty) => {
                SurfaceExpr::Ascription(*span, self.boxed(inner)?, self.boxed(ty)?)
            }
            SurfaceExpr::OutParam(span, inner) => SurfaceExpr::OutParam(*span, self.boxed(inner)?),
            SurfaceExpr::SemiOutParam(span, inner) => {
                SurfaceExpr::SemiOutParam(*span, self.boxed(inner)?)
            }
            SurfaceExpr::If(span, cond, then_br, else_br) => SurfaceExpr::If(
                *span,
                self.boxed(cond)?,
                self.boxed(then_br)?,
                self.boxed(else_br)?,
            ),
            // `if let p := e then t else f`: `p`'s variables scope over `t`.
            SurfaceExpr::IfLet(span, pattern, scrutinee, then_br, else_br) => {
                let scrutinee = self.boxed(scrutinee)?;
                let depth = self.env.len();
                let pattern = self.pattern_in_scope(pattern)?;
                let then_br = self.boxed(then_br)?;
                self.env.truncate(depth);
                let else_br = self.boxed(else_br)?;
                SurfaceExpr::IfLet(*span, pattern, scrutinee, then_br, else_br)
            }
            // `if h : c then t else e`: `h` is bound in both branches.
            SurfaceExpr::IfDecidable(span, hyp, cond, then_br, else_br) => {
                let cond = self.boxed(cond)?;
                let depth = self.env.len();
                let hyp = self.bind(hyp)?;
                let then_br = self.boxed(then_br)?;
                let else_br = self.boxed(else_br)?;
                self.env.truncate(depth);
                SurfaceExpr::IfDecidable(*span, hyp, cond, then_br, else_br)
            }
            // `match [h :] e with | p => b …`: each arm's pattern variables
            // (and `h`) are bound in its body.
            SurfaceExpr::Match(span, hyp, scrutinee, arms) => {
                let scrutinee = self.boxed(scrutinee)?;
                let depth = self.env.len();
                let hyp = hyp.as_ref().map(|hyp| self.bind(hyp)).transpose()?;
                let arms = arms
                    .iter()
                    .map(|arm| self.match_arm(arm))
                    .collect::<Walked<Vec<_>>>()?;
                self.env.truncate(depth);
                SurfaceExpr::Match(*span, hyp, scrutinee, arms)
            }
            SurfaceExpr::Proj(span, base, projection) => self.projection(*span, base, projection)?,
            SurfaceExpr::UniverseInst(span, inner, levels) => SurfaceExpr::UniverseInst(
                *span,
                self.boxed(inner)?,
                levels
                    .iter()
                    .map(|level| self.level(level))
                    .collect::<Walked<Vec<_>>>()?,
            ),
            // `(name := e)`: `name` is a parameter name.
            SurfaceExpr::NamedArg(span, name, value) => SurfaceExpr::NamedArg(
                *span,
                self.name_position(name, "a named-argument name")?,
                self.boxed(value)?,
            ),
            SurfaceExpr::QQuotation { .. } => {
                return Err(TemplateRefusal::new(
                    "a Qq quotation `q(…)`/`Q(…)` in a notation or macro template is not supported",
                ))
            }
            SurfaceExpr::Explicit(span, inner) => SurfaceExpr::Explicit(*span, self.boxed(inner)?),
            SurfaceExpr::StructLit { .. } => self.struct_lit(expr, false)?,
            SurfaceExpr::ByTactic(span, tactics) => {
                SurfaceExpr::ByTactic(*span, self.tactic_block(tactics)?)
            }
            SurfaceExpr::CalcBlock(span, steps) => SurfaceExpr::CalcBlock(*span, self.calc(steps)?),
            SurfaceExpr::Do(span, elems) => SurfaceExpr::Do(*span, self.do_seq(elems)?),
            SurfaceExpr::LiftMethod(span, inner) => {
                SurfaceExpr::LiftMethod(*span, self.boxed(inner)?)
            }
            SurfaceExpr::InterpolatedStr { span, kind, parts } => SurfaceExpr::InterpolatedStr {
                span: *span,
                kind: *kind,
                parts: parts
                    .iter()
                    .map(|part| {
                        Ok(match part {
                            InterpolationPart::Literal(text) => {
                                InterpolationPart::Literal(text.clone())
                            }
                            InterpolationPart::Expr(e) => InterpolationPart::Expr(self.expr(e)?),
                        })
                    })
                    .collect::<Walked<Vec<_>>>()?,
            },
            // `open X in e`: the opened namespaces are names, not references;
            // the body's free references are pre-resolved at the declaration.
            SurfaceExpr::OpenIn {
                span,
                paths,
                scoped,
                body,
            } => SurfaceExpr::OpenIn {
                span: *span,
                paths: paths
                    .iter()
                    .map(|path| self.open_path(path))
                    .collect::<Walked<Vec<_>>>()?,
                scoped: *scoped,
                body: self.boxed(body)?,
            },
        })
    }

    /// `{ s with f := v, g }` (see [`Self::name_position`] for the field
    /// names). A dotted field path `x.v := e` is ONE identifier in Lean
    /// (`structInstLVal`), never an operand variable; the parser desugars it
    /// to `x := { s.x with v := e }`, whose nested literal carries the span of
    /// the literal it came from, and whose field names are all path
    /// components (`desugared_path`).
    pub(super) fn struct_lit(
        &mut self,
        expr: &SurfaceExpr,
        desugared_path: bool,
    ) -> Walked<SurfaceExpr> {
        let SurfaceExpr::StructLit {
            span,
            struct_type,
            base,
            fields,
        } = expr
        else {
            return self.expr(expr);
        };
        let struct_type = struct_type
            .as_deref()
            .map(|ty| self.boxed(ty))
            .transpose()?;
        let base = match base.as_deref() {
            // `s.x`, the source of a desugared path: its field is the path's
            // component, and `s` is the enclosing literal's own source.
            Some(SurfaceExpr::Proj(proj_span, source, projection)) if desugared_path => {
                Some(Box::new(SurfaceExpr::Proj(
                    *proj_span,
                    self.boxed(source)?,
                    projection.clone(),
                )))
            }
            Some(base) => Some(self.boxed(base)?),
            None => None,
        };
        let fields = fields
            .iter()
            .map(|field| {
                let path = matches!(&field.val, SurfaceExpr::StructLit { span: inner, .. } if inner == span);
                let name = if desugared_path || path {
                    field.name.clone()
                } else {
                    self.name_position(&field.name, "a structure-instance field")?
                };
                let val = if path {
                    self.struct_lit(&field.val, true)?
                } else {
                    self.expr(&field.val)?
                };
                Ok(SurfaceFieldAssign {
                    span: field.span,
                    name,
                    val,
                })
            })
            .collect::<Walked<Vec<_>>>()?;
        Ok(SurfaceExpr::StructLit {
            span: *span,
            struct_type,
            base,
            fields,
        })
    }

    /// `open X in e`: each namespace is a name (see [`Self::name_position`]).
    pub(super) fn open_path(&mut self, path: &OpenPath) -> Walked<OpenPath> {
        let names = |walker: &Self, names: &[SurfaceName]| {
            names
                .iter()
                .map(|name| walker.name_position(name, "an `open` name"))
                .collect::<Walked<Vec<_>>>()
        };
        Ok(OpenPath {
            path: self.name_position(&path.path, "an `open` namespace")?,
            names: names(self, &path.names)?,
            hiding: names(self, &path.hiding)?,
            renaming: path
                .renaming
                .iter()
                .map(|rename| {
                    Ok(OpenRename {
                        from: self.name_position(&rename.from, "an `open` name")?,
                        to: self.name_position(&rename.to, "an `open` name")?,
                    })
                })
                .collect::<Walked<Vec<_>>>()?,
        })
    }

    /// A universe level: a level name is a name (see [`Self::name_position`]).
    pub(super) fn level(&mut self, level: &LevelExpr) -> Walked<LevelExpr> {
        Ok(match level {
            LevelExpr::Lit(n) => LevelExpr::Lit(*n),
            LevelExpr::Param(name) => {
                LevelExpr::Param(self.name_position(name, "a universe name")?)
            }
            LevelExpr::Succ(inner) => LevelExpr::Succ(Box::new(self.level(inner)?)),
            LevelExpr::Max(a, b) => {
                LevelExpr::Max(Box::new(self.level(a)?), Box::new(self.level(b)?))
            }
            LevelExpr::IMax(a, b) => {
                LevelExpr::IMax(Box::new(self.level(a)?), Box::new(self.level(b)?))
            }
            // A macro splice: caller syntax.
            LevelExpr::Antiquot(name) => LevelExpr::Antiquot(name.clone()),
        })
    }

    pub(super) fn universe(&mut self, universe: &UniverseExpr) -> Walked<UniverseExpr> {
        Ok(match universe {
            UniverseExpr::TypeLevel(level) => UniverseExpr::TypeLevel(Box::new(self.level(level)?)),
            UniverseExpr::Sort(level) => UniverseExpr::Sort(Box::new(self.level(level)?)),
            UniverseExpr::Prop => UniverseExpr::Prop,
            UniverseExpr::Type => UniverseExpr::Type,
            UniverseExpr::TypeImplicit => UniverseExpr::TypeImplicit,
            UniverseExpr::SortImplicit => UniverseExpr::SortImplicit,
            UniverseExpr::SortStar => UniverseExpr::SortStar,
        })
    }

    pub(super) fn calc(&mut self, steps: &[SurfaceCalcStep]) -> Walked<Vec<SurfaceCalcStep>> {
        steps
            .iter()
            .map(|step| {
                Ok(SurfaceCalcStep {
                    span: step.span,
                    rel: self.expr(&step.rel)?,
                    proof: match &step.proof {
                        SurfaceCalcJustification::Term(term) => {
                            SurfaceCalcJustification::Term(self.expr(term)?)
                        }
                        SurfaceCalcJustification::Tactic(tactics) => {
                            SurfaceCalcJustification::Tactic(self.tactic_block(tactics)?)
                        }
                    },
                })
            })
            .collect()
    }
}
