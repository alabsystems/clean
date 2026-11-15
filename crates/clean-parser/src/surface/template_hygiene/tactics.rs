// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The template walk over tactic blocks, and the tables of which tactic
//! arguments introduce names (see the parent module doc).

use super::*;

impl Walker<'_> {
    // ------------------------------------------------------------------
    // Tactic blocks. A hypothesis a tactic introduces stays in the goal for
    // the rest of the `by` block, so its binding lasts until the block ends
    // (Lean's hygiene is syntactic: every occurrence of the spelling carries
    // the same scope); the alternatives of `cases`/`induction`/`case` bind
    // their names in their own tactics only.
    // ------------------------------------------------------------------
    pub(super) fn tactic_block(&mut self, tactics: &[SurfaceTactic]) -> Walked<Vec<SurfaceTactic>> {
        let depth = self.env.len();
        let out = self.tactic_seq(tactics)?;
        self.env.truncate(depth);
        Ok(out)
    }

    pub(super) fn tactic_seq(&mut self, tactics: &[SurfaceTactic]) -> Walked<Vec<SurfaceTactic>> {
        tactics.iter().map(|tactic| self.tactic(tactic)).collect()
    }

    pub(super) fn location(
        &mut self,
        location: &SurfaceTacticLocation,
    ) -> Walked<SurfaceTacticLocation> {
        Ok(match location {
            SurfaceTacticLocation::Hyps(names) => SurfaceTacticLocation::Hyps(
                names
                    .iter()
                    .map(|name| self.reference_name(name))
                    .collect::<Walked<Vec<_>>>()?,
            ),
            SurfaceTacticLocation::HypsAndGoal(names) => SurfaceTacticLocation::HypsAndGoal(
                names
                    .iter()
                    .map(|name| self.reference_name(name))
                    .collect::<Walked<Vec<_>>>()?,
            ),
            SurfaceTacticLocation::Goal => SurfaceTacticLocation::Goal,
            SurfaceTacticLocation::Wildcard => SurfaceTacticLocation::Wildcard,
        })
    }

    pub(super) fn rw_rules(&mut self, rules: &[SurfaceRwRule]) -> Walked<Vec<SurfaceRwRule>> {
        rules
            .iter()
            .map(|rule| {
                Ok(SurfaceRwRule {
                    span: rule.span,
                    reverse: rule.reverse,
                    term: self.expr(&rule.term)?,
                })
            })
            .collect()
    }

    pub(super) fn simp_args(&mut self, args: &[SurfaceSimpArg]) -> Walked<Vec<SurfaceSimpArg>> {
        args.iter()
            .map(|arg| {
                Ok(SurfaceSimpArg {
                    span: arg.span,
                    phase: arg.phase,
                    reverse: arg.reverse,
                    erase: arg.erase,
                    term: self.expr(&arg.term)?,
                })
            })
            .collect()
    }

    /// `| C a b => tacs`: `C` is a constructor tag, `a b` are bound in
    /// `tacs` only.
    pub(super) fn induction_alts(
        &mut self,
        alts: &[SurfaceInductionAlt],
    ) -> Walked<Vec<SurfaceInductionAlt>> {
        alts.iter()
            .map(|alt| {
                let depth = self.env.len();
                let args = alt
                    .args
                    .iter()
                    .map(|arg| self.bind(arg))
                    .collect::<Walked<Vec<_>>>()?;
                let tactics = self.tactic_seq(&alt.tactics)?;
                self.env.truncate(depth);
                Ok(SurfaceInductionAlt {
                    span: alt.span,
                    explicit: alt.explicit,
                    name: self.name_position(&alt.name, "a constructor alternative")?,
                    args,
                    tactics,
                })
            })
            .collect()
    }

    /// The hypothesis an anonymous `have`/`suffices` introduces is `this`,
    /// under the scope of the syntax around it (Lean's `hygieneInfo`): the
    /// template's own `this` names it, an operand's does not.
    pub(super) fn implicit_this(
        &mut self,
        name: Option<&SurfaceName>,
    ) -> Walked<Option<SurfaceName>> {
        match name {
            Some(name) => Ok(Some(self.bind(name)?)),
            None => {
                let this = SurfaceName::component("this", false);
                if !self.renames() {
                    self.env.push((this.clone(), Binding::Bound(this)));
                    Ok(None)
                } else {
                    let fresh = Self::fresh(&this);
                    self.env.push((this, Binding::Bound(fresh.clone())));
                    Ok(Some(fresh))
                }
            }
        }
    }

    /// The patterns of an `obtain`/`rcases`/`rintro` (kept as the parser's
    /// canonical text, `SurfaceTactic::Obtain::pattern`) and the types of their
    /// typed sub-patterns (`#k`). Every identifier of an rcases pattern is a
    /// binder: its hypothesis stays in the goal for the rest of the block.
    /// The text is never rewritten; what each identifier it writes binds is
    /// recorded in `pattern_binders` (written → bound), which the tactic
    /// reads. A typed pattern's type is walked before the names of its own
    /// sub-pattern are bound, after those to its left (Lean elaborates `(p :
    /// t)`'s `t` before destructuring `p`).
    pub(super) fn rcases_patterns(
        &mut self,
        texts: &[String],
        types: &[SurfaceExpr],
        binders: &[(SurfaceName, SurfaceName)],
    ) -> Walked<(Vec<SurfaceExpr>, Vec<(SurfaceName, SurfaceName)>)> {
        let mut walked_types: Vec<Option<SurfaceExpr>> = vec![None; types.len()];
        let mut out: Vec<(SurfaceName, SurfaceName)> = Vec::new();
        for text in texts {
            let tokens: Vec<crate::lexer::Token> = crate::lexer::Lexer::tokenize(text)
                .into_iter()
                .filter(|token| !matches!(token.kind, crate::lexer::TokenKind::Eof))
                .collect();
            let node = RcasesNode::parse(&tokens)?;
            self.rcases_node(&node, types, &mut walked_types, binders, &mut out)?;
        }
        let walked_types = walked_types
            .into_iter()
            .zip(types)
            .map(|(walked, ty)| match walked {
                Some(walked) => Ok(walked),
                // A type the text never names: walked where the pattern ends.
                None => self.expr(ty),
            })
            .collect::<Walked<Vec<_>>>()?;
        Ok((walked_types, out))
    }

    pub(super) fn rcases_node(
        &mut self,
        node: &RcasesNode,
        types: &[SurfaceExpr],
        walked_types: &mut [Option<SurfaceExpr>],
        binders: &[(SurfaceName, SurfaceName)],
        out: &mut Vec<(SurfaceName, SurfaceName)>,
    ) -> Walked<()> {
        match node {
            RcasesNode::Leaf => Ok(()),
            RcasesNode::Group(children) => children
                .iter()
                .try_for_each(|child| self.rcases_node(child, types, walked_types, binders, out)),
            RcasesNode::Typed(inner, index) => {
                let ty = types.get(*index).ok_or_else(|| {
                    TemplateRefusal::new("an rcases pattern names a type it does not carry")
                })?;
                if walked_types[*index].is_none() {
                    walked_types[*index] = Some(self.expr(ty)?);
                }
                self.rcases_node(inner, types, walked_types, binders, out)
            }
            RcasesNode::Name(written) => {
                if out.iter().any(|(seen, _)| seen == written) {
                    // Another alternative of the same pattern: the same name.
                    return Ok(());
                }
                // A name an expansion inside this template already renamed.
                let current = binders
                    .iter()
                    .find(|(seen, _)| seen == written)
                    .map_or_else(|| written.clone(), |(_, bound)| bound.clone());
                let bound = if Self::inert(&current) {
                    current
                } else if let Some(index) = self.operand_index(&current) {
                    // The pattern variable IS the operand (Lean antiquotes it).
                    if self.mark.is_some() {
                        current
                    } else {
                        self.operand_identifier(index, "an rcases pattern variable")?
                    }
                } else {
                    self.bind(&current)?
                };
                out.push((written.clone(), bound));
                Ok(())
            }
        }
    }

    #[allow(clippy::too_many_lines)] // one arm per tactic kind, by design
    pub(super) fn tactic(&mut self, tactic: &SurfaceTactic) -> Walked<SurfaceTactic> {
        Ok(match tactic {
            SurfaceTactic::Cases(span, hyp, target, alts) => {
                let target = self.boxed(target)?;
                // `h` of `cases h : e` binds a hypothesis that every
                // alternative — and the tactics after an alternative-free
                // `cases` — can name, so it is bound before the alternatives
                // and outlives them (it is not truncated with an alt's args).
                let hyp = hyp.as_ref().map(|name| self.bind(name)).transpose()?;
                SurfaceTactic::Cases(*span, hyp, target, self.induction_alts(alts)?)
            }
            SurfaceTactic::Induction {
                span,
                target,
                using_recursor,
                generalizing,
                alts,
            } => SurfaceTactic::Induction {
                span: *span,
                target: self.boxed(target)?,
                using_recursor: using_recursor
                    .as_deref()
                    .map(|r| self.boxed(r))
                    .transpose()?,
                generalizing: generalizing
                    .iter()
                    .map(|name| self.reference_name(name))
                    .collect::<Walked<Vec<_>>>()?,
                alts: self.induction_alts(alts)?,
            },
            SurfaceTactic::Rw(span, rules, location) => {
                SurfaceTactic::Rw(*span, self.rw_rules(rules)?, self.location(location)?)
            }
            SurfaceTactic::Rewrite(span, rules, location) => {
                SurfaceTactic::Rewrite(*span, self.rw_rules(rules)?, self.location(location)?)
            }
            SurfaceTactic::Rwa(span, rules, location) => {
                SurfaceTactic::Rwa(*span, self.rw_rules(rules)?, self.location(location)?)
            }
            SurfaceTactic::SimpRw(span, rules, location) => {
                SurfaceTactic::SimpRw(*span, self.rw_rules(rules)?, self.location(location)?)
            }
            SurfaceTactic::Simp {
                span,
                all,
                only,
                lemmas,
                location,
                use_hypotheses,
            } => SurfaceTactic::Simp {
                span: *span,
                all: *all,
                only: *only,
                lemmas: self.simp_args(lemmas)?,
                location: self.location(location)?,
                use_hypotheses: *use_hypotheses,
            },
            SurfaceTactic::Simpa {
                span,
                only,
                lemmas,
                use_hypotheses,
                using_term,
            } => SurfaceTactic::Simpa {
                span: *span,
                only: *only,
                lemmas: self.simp_args(lemmas)?,
                use_hypotheses: *use_hypotheses,
                using_term: using_term.as_ref().map(|t| self.expr(t)).transpose()?,
            },
            // `have h : T := proof`: `T` and `proof` do not see `h`; the rest
            // of the block does.
            SurfaceTactic::Have(span, name, ty, proof) => {
                let ty = ty.as_deref().map(|ty| self.boxed(ty)).transpose()?;
                let depth = self.env.len();
                let proof = self.tactic(proof)?;
                self.env.truncate(depth);
                let name = self.implicit_this(name.as_ref())?;
                SurfaceTactic::Have(*span, name, ty, Box::new(proof))
            }
            SurfaceTactic::Let(span, name, ty, value) => {
                let ty = ty.as_deref().map(|ty| self.boxed(ty)).transpose()?;
                let value = self.boxed(value)?;
                SurfaceTactic::Let(*span, self.bind(name)?, ty, value)
            }
            SurfaceTactic::Replace(span, decl) => {
                SurfaceTactic::Replace(*span, Box::new(self.tactic(decl)?))
            }
            // `suffices h : T by tacs`: `tacs` close the goal using `h`; the
            // rest of the block proves `T`, without `h`.
            SurfaceTactic::Suffices(span, name, ty, tactics) => {
                let ty = self.boxed(ty)?;
                let depth = self.env.len();
                let name = self.implicit_this(name.as_ref())?;
                let tactics = self.tactic_seq(tactics)?;
                self.env.truncate(depth);
                SurfaceTactic::Suffices(*span, name, ty, tactics)
            }
            // `case tag x y => tacs`: `tag` names a goal; `x y` are bound in
            // `tacs`.
            SurfaceTactic::Case(span, tag, binders, tactics) => {
                let depth = self.env.len();
                let binders = binders
                    .iter()
                    .map(|binder| self.bind(binder))
                    .collect::<Walked<Vec<_>>>()?;
                let tactics = self.tactic_seq(tactics)?;
                self.env.truncate(depth);
                SurfaceTactic::Case(
                    *span,
                    self.name_position(tag, "a `case` tag")?,
                    binders,
                    tactics,
                )
            }
            SurfaceTactic::AllGoals(span, tactics) => {
                SurfaceTactic::AllGoals(*span, self.tactic_seq(tactics)?)
            }
            SurfaceTactic::AnyGoals(span, tactics) => {
                SurfaceTactic::AnyGoals(*span, self.tactic_seq(tactics)?)
            }
            SurfaceTactic::Try(span, tactics) => {
                SurfaceTactic::Try(*span, self.tactic_seq(tactics)?)
            }
            SurfaceTactic::First(span, alternatives) => SurfaceTactic::First(
                *span,
                alternatives
                    .iter()
                    .map(|alt| self.tactic_seq(alt))
                    .collect::<Walked<Vec<_>>>()?,
            ),
            SurfaceTactic::Repeat(span, tactics) => {
                SurfaceTactic::Repeat(*span, self.tactic_seq(tactics)?)
            }
            SurfaceTactic::SeqFocus(span, first, then) => {
                let first = self.tactic(first)?;
                SurfaceTactic::SeqFocus(*span, Box::new(first), Box::new(self.tactic(then)?))
            }
            SurfaceTactic::Paren(span, tactics) => {
                SurfaceTactic::Paren(*span, self.tactic_seq(tactics)?)
            }
            SurfaceTactic::FocusBlock(span, tactics) => {
                SurfaceTactic::FocusBlock(*span, self.tactic_seq(tactics)?)
            }
            SurfaceTactic::Focus(span, tactics) => {
                SurfaceTactic::Focus(*span, self.tactic_seq(tactics)?)
            }
            SurfaceTactic::Conv(span, location, tactics) => {
                let location = self.location(location)?;
                SurfaceTactic::Conv(*span, location, self.tactic_seq(tactics)?)
            }
            SurfaceTactic::ConvArg(span, index) => SurfaceTactic::ConvArg(*span, *index),
            // `enter [x]` introduces `x` for the conversion that follows.
            SurfaceTactic::ConvEnter(span, args) => SurfaceTactic::ConvEnter(
                *span,
                args.iter()
                    .map(|arg| {
                        Ok(match arg {
                            ConvEnterArg::Index(i) => ConvEnterArg::Index(*i),
                            ConvEnterArg::Name(name) => ConvEnterArg::Name(self.bind(name)?),
                        })
                    })
                    .collect::<Walked<Vec<_>>>()?,
            ),
            SurfaceTactic::Calc(span, steps) => SurfaceTactic::Calc(*span, self.calc(steps)?),
            // `match d with | p => tacs`: each arm's pattern variables are
            // hypotheses of its own goal, bound in its tactics only.
            SurfaceTactic::Match(span, hyp, discriminants, arms) => {
                let discriminants = discriminants
                    .iter()
                    .map(|d| self.expr(d))
                    .collect::<Walked<Vec<_>>>()?;
                // `match h : e with`: `h` is a hypothesis of every arm's goal.
                let depth_before_hyp = self.env.len();
                let hyp = hyp.as_ref().map(|name| self.bind(name)).transpose()?;
                let arms = arms
                    .iter()
                    .map(|arm| {
                        let depth = self.env.len();
                        let pattern = self.pattern_in_scope(&arm.pattern)?;
                        let tactics = self.tactic_seq(&arm.tactics)?;
                        self.env.truncate(depth);
                        Ok(TacticMatchArm {
                            span: arm.span,
                            pattern,
                            tactics,
                        })
                    })
                    .collect::<Walked<Vec<_>>>()?;
                self.env.truncate(depth_before_hyp);
                SurfaceTactic::Match(*span, hyp, discriminants, arms)
            }
            // `obtain pat := e`: `e` does not see the pattern's names; the
            // rest of the block does.
            SurfaceTactic::Obtain {
                span,
                pattern,
                ty,
                term,
                pattern_types,
                pattern_binders,
            } => {
                let ty = ty.as_deref().map(|ty| self.boxed(ty)).transpose()?;
                let term = term.as_deref().map(|term| self.boxed(term)).transpose()?;
                let (pattern_types, pattern_binders) = self.rcases_patterns(
                    std::slice::from_ref(pattern),
                    pattern_types,
                    pattern_binders,
                )?;
                SurfaceTactic::Obtain {
                    span: *span,
                    pattern: pattern.clone(),
                    ty,
                    term,
                    pattern_types,
                    pattern_binders,
                }
            }
            SurfaceTactic::RCases {
                span,
                targets,
                pattern,
                pattern_types,
                pattern_binders,
            } => {
                // Every target term is elaborated before any `h :` of
                // `h : e` is in scope (`RCases.rcases` elaborates the targets,
                // then generalizes them all), and each `h` outlives the
                // tactic, as `cases h : e`'s does.
                let terms = targets
                    .iter()
                    .map(|target| self.expr(&target.term))
                    .collect::<Walked<Vec<_>>>()?;
                let targets = targets
                    .iter()
                    .zip(terms)
                    .map(
                        |(target, term)| -> Walked<crate::surface::SurfaceRCasesTarget> {
                            let eq_name = target
                                .eq_name
                                .as_ref()
                                .map(|name| self.bind(name))
                                .transpose()?;
                            Ok(crate::surface::SurfaceRCasesTarget { eq_name, term })
                        },
                    )
                    .collect::<Walked<Vec<_>>>()?;
                let (pattern_types, pattern_binders) = self.rcases_patterns(
                    std::slice::from_ref(pattern),
                    pattern_types,
                    pattern_binders,
                )?;
                SurfaceTactic::RCases {
                    span: *span,
                    targets,
                    pattern: pattern.clone(),
                    pattern_types,
                    pattern_binders,
                }
            }
            SurfaceTactic::RIntro {
                span,
                patterns,
                pattern_types,
                pattern_binders,
            } => {
                let (pattern_types, pattern_binders) =
                    self.rcases_patterns(patterns, pattern_types, pattern_binders)?;
                SurfaceTactic::RIntro {
                    span: *span,
                    patterns: patterns.clone(),
                    pattern_types,
                    pattern_binders,
                }
            }
            SurfaceTactic::Named { span, name, args } => SurfaceTactic::Named {
                span: *span,
                name: name.clone(),
                args: self.named_tactic_args(name, args)?,
            },
            SurfaceTactic::Term(span, term) => SurfaceTactic::Term(*span, self.boxed(term)?),
        })
    }

    /// The arguments of a registry-dispatched tactic. Their roles (a term, a
    /// hypothesis the tactic introduces) depend on the tactic, so only
    /// tactics whose roles are listed here are walked; any other tactic with
    /// arguments is refused.
    pub(super) fn named_tactic_args(
        &mut self,
        name: &str,
        args: &[SurfaceExpr],
    ) -> Walked<Vec<SurfaceExpr>> {
        let Some((first, rest)) = args.split_first() else {
            return Ok(Vec::new());
        };
        match named_tactic_role(name) {
            Some(NamedTacticRole::Terms) => args.iter().map(|arg| self.expr(arg)).collect(),
            // `intro x y`, `ext x`, `funext x`, `by_contra h`, `rename_i a b`:
            // each argument introduces a hypothesis.
            Some(NamedTacticRole::Binders) => args
                .iter()
                .map(|arg| self.tactic_binder_arg(name, arg))
                .collect(),
            // `by_cases h : p` / `wlog h : p`: `p` first, then `h`.
            Some(NamedTacticRole::BinderThenTerms) => {
                let hyp = first;
                let rest = rest
                    .iter()
                    .map(|arg| self.expr(arg))
                    .collect::<Walked<Vec<_>>>()?;
                let hyp = self.tactic_binder_arg(name, hyp)?;
                Ok(std::iter::once(hyp).chain(rest).collect())
            }
            // `generalize (h :)? e = x` → `[e, x, h?]`; with a location
            // naming hypotheses, `[e, x, h | _, loc…]`, whose locations are
            // references to hypotheses that exist before the tactic runs.
            Some(NamedTacticRole::Generalize) => {
                let term = self.expr(first)?;
                let (binders, locations) = if rest.len() > 2 {
                    rest.split_at(2)
                } else {
                    (rest, &[][..])
                };
                let locations = locations
                    .iter()
                    .map(|arg| self.expr(arg))
                    .collect::<Walked<Vec<_>>>()?;
                let binders = binders
                    .iter()
                    .map(|arg| match arg {
                        SurfaceExpr::Hole(_) => Ok(arg.clone()),
                        _ => self.tactic_binder_arg(name, arg),
                    })
                    .collect::<Walked<Vec<_>>>()?;
                Ok(std::iter::once(term)
                    .chain(binders)
                    .chain(locations)
                    .collect())
            }
            // `choose f hf using h` (registry form `[h, f, hf]`) and the
            // registry `obtain` (`[h, x, hx]`): a hypothesis, then the names
            // it introduces.
            Some(NamedTacticRole::ReferenceThenBinders) => {
                let hyp = self.expr(first)?;
                let binders = rest
                    .iter()
                    .map(|arg| self.tactic_binder_arg(name, arg))
                    .collect::<Walked<Vec<_>>>()?;
                Ok(std::iter::once(hyp).chain(binders).collect())
            }
            // A tactic this table does not know (a user-defined one): which of
            // its arguments introduce names is not known here. An argument that
            // is no identifier the template writes (a compound term, an
            // operand, a name from a notation expanded inside) is the same
            // syntax whatever the tactic does with it; a template identifier
            // could be a binder or a reference, and reading it as the wrong one
            // would scope it differently from Lean — refused.
            None => {
                let ambiguous = args.iter().any(|arg| match arg {
                    SurfaceExpr::Ident(_, ident) => {
                        !(Self::inert(ident)
                            || Self::foreign(ident)
                            || self.operand_index(ident).is_some())
                    }
                    _ => false,
                });
                if ambiguous {
                    return Err(TemplateRefusal::new(format!(
                        "the tactic `{name}` in a notation or macro template is not supported with an identifier argument: whether it introduces that name is not modelled"
                    )));
                }
                args.iter().map(|arg| self.expr(arg)).collect()
            }
        }
    }

    pub(super) fn tactic_binder_arg(
        &mut self,
        tactic: &str,
        arg: &SurfaceExpr,
    ) -> Walked<SurfaceExpr> {
        match arg {
            SurfaceExpr::Ident(span, name) => Ok(SurfaceExpr::Ident(*span, self.bind(name)?)),
            _ => Err(TemplateRefusal::new(format!(
                "`{tactic}` with a non-identifier argument in a notation or macro template is not supported"
            ))),
        }
    }
}

/// The structure of an rcases pattern text, read with the precedence the
/// tactic reads it with (`RIntroPattern::parse`): a trailing ` : #k` types
/// the whole text, then a top-level `|` splits alternatives, then a leading
/// `@` marks the explicit pattern it prefixes, then `⟨…⟩` spanning the text
/// is a tuple, then parentheses group, and what remains is `_`, `-`, `rfl` or
/// one identifier.
pub(super) enum RcasesNode {
    Leaf,
    Name(SurfaceName),
    Typed(Box<RcasesNode>, usize),
    Group(Vec<RcasesNode>),
}

impl RcasesNode {
    fn parse(tokens: &[crate::lexer::Token]) -> Walked<Self> {
        use crate::lexer::TokenKind;
        let refuse = || TemplateRefusal::new("an rcases pattern this walk cannot read");
        let depth_at = |end: usize| {
            tokens[..end]
                .iter()
                .fold(0_i64, |depth, token| match token.kind {
                    TokenKind::LAngle | TokenKind::LParen | TokenKind::LBracket => depth + 1,
                    TokenKind::RAngle | TokenKind::RParen | TokenKind::RBracket => depth - 1,
                    _ => depth,
                })
        };
        // `p : #k`.
        if let [rest @ .., colon, hash, index] = tokens {
            if let (TokenKind::Colon, TokenKind::Hash, TokenKind::NatLit(k)) =
                (&colon.kind, &hash.kind, &index.kind)
            {
                if depth_at(rest.len()) == 0 {
                    let k = k
                        .to_u64()
                        .and_then(|k| usize::try_from(k).ok())
                        .ok_or_else(refuse)?;
                    return Ok(Self::Typed(Box::new(Self::parse(rest)?), k));
                }
            }
        }
        match tokens {
            [single]
                if matches!(
                    single.kind,
                    TokenKind::Underscore | TokenKind::Rfl | TokenKind::Minus
                ) =>
            {
                return Ok(Self::Leaf)
            }
            [single] => {
                return match &single.kind {
                    TokenKind::Ident(text) => Ok(Self::Name(SurfaceName::component(
                        text,
                        single.ident_escaped,
                    ))),
                    _ => Err(refuse()),
                }
            }
            _ => {}
        }
        // Top-level alternatives, then a tuple's fields.
        fn split<'t>(
            separator: &TokenKind,
            tokens: &'t [crate::lexer::Token],
        ) -> Vec<&'t [crate::lexer::Token]> {
            let mut parts = Vec::new();
            let mut depth = 0_i64;
            let mut start = 0;
            for (index, token) in tokens.iter().enumerate() {
                match &token.kind {
                    TokenKind::LAngle | TokenKind::LParen | TokenKind::LBracket => depth += 1,
                    TokenKind::RAngle | TokenKind::RParen | TokenKind::RBracket => depth -= 1,
                    kind if depth == 0 && kind == separator => {
                        parts.push(&tokens[start..index]);
                        start = index + 1;
                    }
                    _ => {}
                }
            }
            parts.push(&tokens[start..]);
            parts
        }
        let alternatives = split(&TokenKind::Pipe, tokens);
        if alternatives.len() > 1 {
            return alternatives
                .into_iter()
                .map(Self::parse)
                .collect::<Walked<Vec<_>>>()
                .map(Self::Group);
        }
        // `@pat`: binds what `pat` binds.
        if let [at, rest @ ..] = tokens {
            if matches!(at.kind, TokenKind::At) && !rest.is_empty() {
                return Self::parse(rest);
            }
        }
        let spans_whole = |open: &TokenKind, close: &TokenKind| {
            matches!(tokens, [first, .., last] if &first.kind == open && &last.kind == close)
                && (1..tokens.len()).all(|end| end == tokens.len() || depth_at(end) > 0)
        };
        if spans_whole(&TokenKind::LAngle, &TokenKind::RAngle) {
            let inner = &tokens[1..tokens.len() - 1];
            if inner.is_empty() {
                return Ok(Self::Leaf);
            }
            return split(&TokenKind::Comma, inner)
                .into_iter()
                .map(Self::parse)
                .collect::<Walked<Vec<_>>>()
                .map(Self::Group);
        }
        if spans_whole(&TokenKind::LParen, &TokenKind::RParen) {
            return Self::parse(&tokens[1..tokens.len() - 1]);
        }
        Err(refuse())
    }
}

/// How a registry-dispatched tactic uses its arguments.
enum NamedTacticRole {
    /// Every argument is a term or a reference (a lemma, a hypothesis, a
    /// definition to unfold); none introduces a name.
    Terms,
    /// Every argument is an identifier the tactic introduces.
    Binders,
    /// The first argument is an identifier the tactic introduces, the rest
    /// are terms walked before it.
    BinderThenTerms,
    /// `generalize`: a term, then the identifiers it introduces.
    Generalize,
    /// A hypothesis (a reference), then the identifiers the tactic introduces.
    ReferenceThenBinders,
}

fn named_tactic_role(name: &str) -> Option<NamedTacticRole> {
    Some(match name {
        "intro" | "intros" | "ext" | "funext" | "by_contra" | "rename_i" | "rintro" => {
            NamedTacticRole::Binders
        }
        "by_cases" | "wlog" => NamedTacticRole::BinderThenTerms,
        "generalize" => NamedTacticRole::Generalize,
        "choose" | "obtain" => NamedTacticRole::ReferenceThenBinders,
        // Every other tactic of the registry: its arguments are terms, lemma
        // or constant names, or hypotheses it acts on — references all.
        "exact" | "apply" | "refine" | "refine'" | "change" | "show" | "use" | "exists"
        | "existsi" | "absurd" | "exfalso" | "constructor" | "left" | "right" | "rfl" | "sorry"
        | "admit" | "trivial" | "assumption" | "contradiction" | "decide" | "native_decide"
        | "omega" | "simp_arith" | "simp_all" | "norm_num" | "linarith" | "nlinarith"
        | "positivity" | "ring" | "ring_nf" | "field_simp" | "norm_cast" | "push_cast"
        | "exact_mod_cast" | "apply_mod_cast" | "symm" | "congr" | "split" | "subst" | "revert"
        | "clear" | "specialize" | "injection" | "unfold" | "push_neg" | "dsimp" | "skip"
        | "done" | "exact?" | "apply?" | "aesop" | "tauto" | "infer_instance" | "grind"
        | "bv_decide" | "abel" | "and_intros" | "auto_cascade" | "blast" | "cc"
        | "cert_mathverse" | "cert_simp" | "classical" | "continuity" | "contrapose" | "delta"
        | "discriminate" | "fin_cases" | "gcongr" | "group" | "interval_cases" | "itauto"
        | "lhs" | "library_search" | "lift" | "mathverse_suggest" | "mathverse_use"
        | "measurability" | "mono" | "monad_pres" | "nontriviality" | "peel" | "polyrith"
        | "qify" | "reduce" | "reduce_eq" | "rhs" | "rotate_left" | "rotate_right" | "rw?"
        | "solve_by_elim" | "split_ifs" | "subst_eqs" | "trace_state" | "trans" | "whnf"
        | "zify" | "inhabit" | "convert" | "rcases" => NamedTacticRole::Terms,
        _ => return None,
    })
}
