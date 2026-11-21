// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Compile a unary list equation that calls itself on a proper nested constructor tail.
//! The auxiliary recurses on the immediate tail and carries the results on
//! its next suffixes. Its value and the public wrapper are ordinary definitions.

use super::{course_of_values::PairThreaded, elab_core::IdentTarget, ElabCtx};
use clean_parser::{
    Projection, Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr, SurfaceMatchArm,
    SurfaceName, SurfacePattern,
};

fn ident(name: &SurfaceName) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), name.clone())
}

fn lambda(names: &[&SurfaceName], body: SurfaceExpr) -> SurfaceExpr {
    let binders = names
        .iter()
        .map(|name| SurfaceBinder::new_typed((*name).clone(), None, SurfaceBinderInfo::Explicit))
        .collect();
    SurfaceExpr::Lambda(Span::dummy(), binders, Box::new(body))
}

fn apply(head: SurfaceExpr, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    SurfaceExpr::App(
        Span::dummy(),
        Box::new(head),
        args.into_iter().map(SurfaceArg::positional).collect(),
    )
}

fn right_pair(global: &str, mut values: Vec<SurfaceExpr>) -> Option<SurfaceExpr> {
    let last = values.pop()?;
    Some(values.into_iter().rev().fold(last, |tail, head| {
        apply(ident(&SurfaceName::global_path(global)), vec![head, tail])
    }))
}

fn field(name: &SurfaceName, n: usize, width: usize) -> SurfaceExpr {
    let mut value = ident(name);
    for _ in 0..n {
        value = SurfaceExpr::Proj(Span::dummy(), Box::new(value), Projection::Index(2));
    }
    if n + 1 < width {
        value = SurfaceExpr::Proj(Span::dummy(), Box::new(value), Projection::Index(1));
    }
    value
}
fn bind(name: &SurfaceName, value: SurfaceExpr, body: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::Let(
        Span::dummy(),
        SurfaceBinder::new_typed(name.clone(), None, SurfaceBinderInfo::Explicit),
        Box::new(value),
        Box::new(body),
    )
}

fn is_source_name(name: &SurfaceName) -> bool {
    !name.is_global_reference()
        && !name.is_relative_constructor()
        && name.template_origin().is_none()
        && name.template_scope().is_none()
        && !name.is_section_variable()
        && !name.is_header_binder()
}

struct ListSuffixes<'a> {
    heads: &'a [&'a SurfaceName],
    tail: &'a SurfaceName,
    previous: &'a SurfaceName,
}

impl ListSuffixes<'_> {
    // Recognize only the bound suffix itself or notation rebuilding it with the
    // very heads from this arm. Reordering, replacing, or prepending a head must
    // never supply a recursive result for a different list.
    fn start(&self, expr: &SurfaceExpr) -> Option<usize> {
        match expr {
            SurfaceExpr::Paren(_, value) => self.start(value),
            SurfaceExpr::Ident(_, n) if n == self.tail && is_source_name(n) => {
                Some(self.heads.len())
            }
            SurfaceExpr::App(_, cons, args) => {
                let SurfaceExpr::Ident(_, n) = &**cons else {
                    return None;
                };
                if !n.same_syntax(&SurfaceName::global_path("List.cons"))
                    || !n.is_global_reference()
                {
                    return None;
                }
                let [head, tail] = args.as_slice() else {
                    return None;
                };
                if head.name.is_some() || tail.name.is_some() {
                    return None;
                }
                let index = self.start(&tail.expr)?.checked_sub(1)?;
                match &head.expr {
                    SurfaceExpr::Ident(_, n) if n == self.heads[index] && is_source_name(n) => {
                        Some(index)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn result(&self, expr: &SurfaceExpr) -> Option<SurfaceExpr> {
        let index = self.start(expr)?.checked_sub(1)?;
        Some(field(self.previous, index, self.heads.len()))
    }
}

struct SourceBody<'a> {
    function: &'a SurfaceName,
    bindings: Vec<(&'a SurfaceName, SurfaceName)>,
    smaller: Option<ListSuffixes<'a>>,
    found: bool,
}

impl SourceBody<'_> {
    /// Only enter binder-free forms. A bare function or another decrease
    /// selects the regular equation compiler with the original source intact.
    fn rewrite(&mut self, expr: &SurfaceExpr) -> Option<SurfaceExpr> {
        match expr {
            SurfaceExpr::App(span, head, args) => {
                if matches!(&**head, SurfaceExpr::Ident(_, n) if n == self.function && is_source_name(n))
                {
                    let [arg] = args.as_slice() else { return None };
                    if arg.name.is_some() {
                        return None;
                    }
                    let result = self.smaller.as_ref()?.result(&arg.expr)?;
                    self.found = true;
                    return Some(result);
                }
                let head = self.rewrite(head)?;
                let args = args
                    .iter()
                    .map(|arg| {
                        Some(SurfaceArg {
                            span: arg.span,
                            name: arg.name.clone(),
                            expr: self.rewrite(&arg.expr)?,
                        })
                    })
                    .collect::<Option<_>>()?;
                Some(SurfaceExpr::App(*span, Box::new(head), args))
            }
            SurfaceExpr::Ident(_, n) if is_source_name(n) && n == self.function => None,
            SurfaceExpr::Ident(_, n) if is_source_name(n) => Some(
                self.bindings
                    .iter()
                    .find(|(source, _)| *source == n)
                    .map_or_else(|| expr.clone(), |(_, dest)| ident(dest)),
            ),
            SurfaceExpr::Ident(..) | SurfaceExpr::Lit(..) => Some(expr.clone()),
            SurfaceExpr::Proj(span, base, projection) => Some(SurfaceExpr::Proj(
                *span,
                Box::new(self.rewrite(base)?),
                projection.clone(),
            )),
            SurfaceExpr::Paren(span, value) => {
                Some(SurfaceExpr::Paren(*span, Box::new(self.rewrite(value)?)))
            }
            _ => None,
        }
    }
}

impl ElabCtx<'_> {
    pub(super) fn lower_list_tail_equations(
        &mut self,
        function: &SurfaceName,
        ty: Option<&SurfaceExpr>,
        val: &SurfaceExpr,
    ) -> Option<PairThreaded> {
        let SurfaceExpr::PatternMatchLambda(_, params, body) = val else {
            return None;
        };
        let [param] = params.as_slice() else {
            return None;
        };
        if !param
            .name
            .same_syntax(&SurfaceName::pattern_lambda_binder())
        {
            return None;
        }
        let SurfaceExpr::Match(_, None, scrut, arms) = &**body else {
            return None;
        };
        if !matches!(&**scrut, SurfaceExpr::Ident(_, n) if n.same_syntax(&param.name)) {
            return None;
        }
        let [arm, fallback] = arms.as_slice() else {
            return None;
        };
        if !matches!(fallback.pattern, SurfacePattern::Wildcard) {
            return None;
        }
        let SurfaceExpr::Arrow(_, domain, result) = ty? else {
            return None;
        };
        let SurfaceExpr::App(_, list, args) = &**domain else {
            return None;
        };
        let SurfaceExpr::Ident(_, list_name) = &**list else {
            return None;
        };
        let [element] = args.as_slice() else {
            return None;
        };
        if element.name.is_some() || !self.head_denotes_global(list_name, "List") {
            return None;
        }
        let mut element_head = &element.expr;
        while let SurfaceExpr::Paren(_, inner) | SurfaceExpr::App(_, inner, _) = element_head {
            element_head = inner;
        }
        let SurfaceExpr::Ident(_, element_name) = element_head else {
            return None;
        };
        let IdentTarget::Global(element_owner) = self.resolve_ident_target(element_name) else {
            return None;
        };
        self.env.get_inductive(&element_owner)?;
        let element_owner = SurfaceName::from_name(element_owner);
        let list_owner = SurfaceName::global_path("List");
        let mut names = Vec::new();
        let mut pat = &arm.pattern;
        while let SurfacePattern::Ctor(constructor, fields) = pat {
            if !self.head_denotes_global(constructor, "List.cons") {
                return None;
            }
            let [SurfacePattern::Var(name), next] = fields.as_slice() else {
                return None;
            };
            if !self.list_equation_pattern_binder(name, &element_owner) {
                return None;
            }
            names.push(name);
            pat = next;
        }
        let SurfacePattern::Var(last) = pat else {
            return None;
        };
        let depth = names.len();
        if depth < 2
            || !self.list_equation_pattern_binder(last, &list_owner)
            || names
                .iter()
                .copied()
                .chain([last])
                .any(|n| n == function || !is_source_name(n))
        {
            return None;
        }

        let heads: Vec<_> = (0..depth)
            .map(|i| SurfaceName::unspellable("_listHead", i as u64))
            .collect();
        let suffix = SurfaceName::unspellable("_listSuffix", 0);
        let immediate = SurfaceName::unspellable("_listTail", 0);
        let previous = SurfaceName::unspellable("_listPrior", 0);
        let current = SurfaceName::unspellable("_listCurrent", 0);
        let mut recursive = SourceBody {
            function,
            bindings: names.iter().copied().zip(heads.iter().cloned()).collect(),
            smaller: Some(ListSuffixes {
                heads: &names,
                tail: last,
                previous: &previous,
            }),
            found: false,
        };
        recursive.bindings.push((last, suffix.clone()));
        let body = recursive.rewrite(&arm.body)?;
        if !recursive.found {
            return None;
        }
        let default = SourceBody {
            function,
            bindings: Vec::new(),
            smaller: None,
            found: false,
        }
        .rewrite(&fallback.body)?;

        // The auxiliary stores (f xs, f xs.tail, ..., f (tail^(k-1) xs)).
        // Each proper suffix selected by the source has its own field in the tail tuple.
        let aux_name = function.append(&SurfaceName::unspellable("_listResults", 0));
        let mut suffix_pattern = SurfacePattern::Var(suffix);
        for head in heads[1..].iter().rev() {
            suffix_pattern = SurfacePattern::Ctor(
                SurfaceName::global_path("List.cons"),
                vec![SurfacePattern::Var(head.clone()), suffix_pattern],
            );
        }
        let row = |pattern, body| SurfaceMatchArm {
            span: arm.span,
            pattern,
            body,
        };
        let select = SurfaceExpr::Match(
            arm.span,
            None,
            Box::new(ident(&immediate)),
            vec![
                row(suffix_pattern, body),
                row(SurfacePattern::Wildcard, default.clone()),
            ],
        );
        let old = apply(ident(&aux_name), vec![ident(&immediate)]);
        let mut fields = vec![ident(&current)];
        fields.extend((0..depth - 1).map(|i| field(&previous, i, depth)));
        let shifted = bind(
            &previous,
            old,
            bind(&current, select, right_pair("Prod.mk", fields)?),
        );
        let outer = SurfaceExpr::Match(
            arm.span,
            None,
            Box::new(ident(&param.name)),
            vec![
                row(
                    SurfacePattern::Ctor(SurfaceName::global_path("List.nil"), vec![]),
                    right_pair("Prod.mk", vec![default; depth])?,
                ),
                row(
                    SurfacePattern::Ctor(
                        SurfaceName::global_path("List.cons"),
                        vec![
                            SurfacePattern::Var(heads[0].clone()),
                            SurfacePattern::Var(immediate),
                        ],
                    ),
                    shifted,
                ),
            ],
        );
        let aux_val = SurfaceExpr::PatternMatchLambda(arm.span, params.clone(), Box::new(outer));
        let aux_ty = SurfaceExpr::Arrow(
            arm.span,
            domain.clone(),
            Box::new(right_pair("Prod", vec![(**result).clone(); depth])?),
        );
        let input = SurfaceName::unspellable("_listInput", 0);
        let wrapper_val = lambda(
            &[&input],
            SurfaceExpr::Proj(
                arm.span,
                Box::new(apply(ident(&aux_name), vec![ident(&input)])),
                Projection::Index(1),
            ),
        );
        Some(PairThreaded {
            aux_name,
            aux_ty,
            aux_val,
            wrapper_ty: ty?.clone(),
            wrapper_val,
        })
    }
}
