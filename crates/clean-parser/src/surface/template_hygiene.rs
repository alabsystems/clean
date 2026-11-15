// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hygiene of user notation and macro templates.
//!
//! A `notation "G " x => gf x` or `macro "H " x:term : term => `(gf $x)` is
//! a MACRO: Lean 4 expands it by substituting the operands into the
//! template's syntax, and every identifier of the template carries the
//! expansion's macro scope. So
//!
//! * a template's FREE identifier resolves to what it named where the
//!   template was DECLARED (quotation pre-resolution), and no binder at the
//!   use site can capture it: with `def gf (n : Nat) := n + 100`, `def m1
//!   (gf : Nat → Nat) : Nat := G 1` calls the GLOBAL `gf` (Lean 4.8.0: `m1
//!   (fun _ => 0) = 101`);
//! * a template BINDER never captures an operand's identifier (`notation "T "
//!   x => fun kz => x + kz` applied to a global `kz` adds that global);
//! * an operand is elaborated IN the template, under its binders and against
//!   the expected type the template gives it (`notation "DD " x => (x : Int) -
//!   10` makes `DD (3 - 5)` an `Int` subtraction, `-12`).
//!
//! Two walks implement that over Clean's surface syntax, sharing ONE
//! traversal ([`Walker`]) so they can never disagree on which occurrence a
//! binder scopes over:
//!
//! * [`mark_template_free_references`] runs once, where the template is
//!   declared. It marks every free reference with its [`TemplateOrigin`]
//!   (name resolution then binds it to no local but a section variable that
//!   was in scope at the declaration, and walks namespaces from the
//!   declaring namespace), and gives every template PATTERN variable a
//!   [`TemplateScope`] (see below).
//! * [`instantiate_notation_template`] runs at every use: it substitutes the
//!   operands, renames every template binder to a fresh name no identifier
//!   token can spell, and gives the pattern-variable scopes fresh ids for
//!   this expansion.
//!
//! A bare pattern identifier (`| n => …`) is a binder or a constructor
//! according to what its spelling names where the template was declared
//! (Lean's `CollectPatternVars.processId`), which only the elaborator knows.
//! So it is not renamed: it keeps its spelling, gets the template's origin
//! (the elaborator classifies it at the declaration site) and a
//! [`TemplateScope`], and so does every reference the template makes to it.
//! A scoped name binds, and is bound by, only a local of the same scope —
//! exactly what Lean's macro scope does — and resolves to the constructor
//! when it names one.
//!
//! The traversal is TOTAL over the surface syntax: every `SurfaceExpr`,
//! `SurfacePattern`, `DoElem` and `SurfaceTactic` variant is matched
//! explicitly, with no wildcard arm, so a new node kind is a compile error
//! here rather than a silent fallback. A form whose binding structure Clean
//! does not model exactly (a Qq quotation, an `obtain`/`rcases`/`rintro`
//! pattern kept as source text, a tactic `match`, a tactic this walk does not
//! know the binders of) is a [`TemplateRefusal`]: the notation or macro
//! declaration is refused. It is never expanded with another meaning — in
//! particular never applied as a function to its operands, which elaborated
//! the operand outside the template (`notation "Co " x => Id.run (do let y :
//! Int := x; return (y + 10).toNat)` gave `Co (0 - 2) = 10` where Lean gives
//! `8`, and a free name resolved with the opens of the USE site; both were
//! accepted by `rfl`, measured 2026-09-26).

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

/// Stack reserved before each walk step, and the segment grown when less
/// remains (the parser's `EXPR_STACK_RED_ZONE` / `EXPR_STACK_GROW_SIZE`).
const WALK_STACK_RED_ZONE: usize = 512 * 1024;
const WALK_STACK_GROW_SIZE: usize = 8 * 1024 * 1024;

use clean_kernel::name::Name;

use super::{
    ConvEnterArg, DoCatchClause, DoElem, DoMatchArm, LevelExpr, OpenPath, OpenRename, Projection,
    Span, SurfaceArg, SurfaceBinder, SurfaceCalcJustification, SurfaceCalcStep, SurfaceExpr,
    SurfaceFieldAssign, SurfaceInductionAlt, SurfaceMatchArm, SurfaceName, SurfacePattern,
    SurfaceRwRule, SurfaceSimpArg, SurfaceTactic, SurfaceTacticLocation, TacticMatchArm,
    TemplateOrigin, TemplateScope, TemplateSiteId, UniverseExpr,
};
use crate::interpolation::InterpolationPart;

/// A template the hygiene walk refuses (see the module doc): the form it
/// names is outside what Clean models exactly, so the declaration is refused
/// rather than expanded with a different meaning.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{0}")]
pub struct TemplateRefusal(String);

impl TemplateRefusal {
    fn new(reason: impl Into<String>) -> Self {
        Self(reason.into())
    }

    /// Why the template is refused.
    #[must_use]
    pub fn reason(&self) -> &str {
        &self.0
    }
}

type Walked<T> = Result<T, TemplateRefusal>;

/// Mark the free references of the template `expr` (see the module doc).
///
/// `bound` are the notation's own pattern variables, which the expansion
/// references as ordinary (caller-supplied) operands. `namespace` is the
/// namespace the template is declared in and `section_variables` the section
/// variables in scope there; `site` is the declaring command in the file
/// being elaborated ([`TemplateOrigin::site`]).
///
/// # Errors
///
/// [`TemplateRefusal`] when the template uses a form whose binding structure
/// Clean does not model exactly.
pub fn mark_template_free_references(
    expr: &SurfaceExpr,
    bound: &[SurfaceName],
    namespace: &Name,
    section_variables: &[SurfaceName],
    site: Option<TemplateSiteId>,
) -> Result<SurfaceExpr, TemplateRefusal> {
    Walker::mark(bound, namespace, section_variables, site, false).expr(expr)
}

/// Every spelling a use of the template `expr` resolves as a GLOBAL name
/// (see [`mark_template_free_references`], same arguments): each free
/// reference, each pattern variable (a constructor when its spelling names
/// one), and each dotted identifier `r.f₁.….fₖ` written on a free reference,
/// which Lean resolves as one name. The elaborator pre-resolves exactly these
/// at the declaration.
///
/// # Errors
///
/// [`TemplateRefusal`] exactly when [`mark_template_free_references`] refuses.
pub fn template_free_reference_spellings(
    expr: &SurfaceExpr,
    bound: &[SurfaceName],
    namespace: &Name,
) -> Result<Vec<SurfaceName>, TemplateRefusal> {
    let mut walker = Walker::mark(bound, namespace, &[], None, true);
    walker.expr(expr)?;
    Ok(walker
        .mark
        .and_then(|mark| mark.spellings)
        .unwrap_or_default())
}

/// Substitute `operands` for the operand variables `vars` of a `notation`
/// template, as Lean expands a notation: the template is a syntax quotation,
/// so each operand is elaborated IN the template, under its binders and
/// against the expected type the template gives it.
///
/// Hygiene is kept by renaming every binder of the template to a fresh name
/// no identifier token can spell (Lean gives them the expansion's macro
/// scope), so a template binder never captures an identifier of an operand,
/// and by giving the template's pattern-variable scopes fresh ids. A binder
/// or pattern variable spelled like an operand variable IS that operand, as
/// in Lean, whose `notation` antiquotes every identifier of that spelling.
///
/// `template` must be the output of [`mark_template_free_references`] for
/// the same operand variables.
///
/// # Errors
///
/// [`TemplateRefusal`] when an operand stands where only an identifier can
/// (a binder, a pattern variable, a hypothesis name) and is not one, or when
/// `vars` and `operands` differ in length.
pub fn instantiate_notation_template(
    template: &SurfaceExpr,
    vars: &[SurfaceName],
    operands: &[SurfaceExpr],
) -> Result<SurfaceExpr, TemplateRefusal> {
    Walker::instantiate(vars, operands, true)?.expr(template)
}

/// [`instantiate_notation_template`] for a template declared under `set_option
/// hygiene false`: Lean's quotation then adds no macro scope and pre-resolves
/// nothing (`Lean/Elab/Quotation.lean`, `quoteSyntax`), so the expansion is the
/// bare substitution. Every identifier spelled like an operand variable is that
/// operand, as with hygiene; every other identifier is kept exactly as written
/// — a template binder captures an operand's identifier of its spelling, and a
/// free name resolves at the USE site. `template` is the template as written
/// (never marked).
///
/// # Errors
///
/// As [`instantiate_notation_template`].
pub fn instantiate_unhygienic_notation_template(
    template: &SurfaceExpr,
    vars: &[SurfaceName],
    operands: &[SurfaceExpr],
) -> Result<SurfaceExpr, TemplateRefusal> {
    Walker::instantiate(vars, operands, false)?.expr(template)
}

/// Instantiate the `by` block `template` of a TACTIC macro (`macro "kw" x:term
/// : tactic => `(tactic| …)`) with the call's arguments: the same expansion as
/// [`instantiate_notation_template`] (or its unhygienic form), over a tactic
/// sequence. `template` must be the output of [`mark_template_free_references`]
/// for the same variables when `hygienic`.
///
/// # Errors
///
/// As [`instantiate_notation_template`].
pub fn instantiate_tactic_template(
    template: &[SurfaceTactic],
    vars: &[SurfaceName],
    operands: &[SurfaceExpr],
    hygienic: bool,
) -> Result<Vec<SurfaceTactic>, TemplateRefusal> {
    Walker::instantiate(vars, operands, hygienic)?.tactic_block(template)
}

/// Process-wide counter behind [`Walker::fresh`].
static FRESH_TEMPLATE_BINDER: AtomicU64 = AtomicU64::new(0);

/// Process-wide counter behind the [`TemplateScope`] ids.
static FRESH_TEMPLATE_SCOPE: AtomicU64 = AtomicU64::new(0);

fn fresh_scope() -> TemplateScope {
    TemplateScope(FRESH_TEMPLATE_SCOPE.fetch_add(1, Ordering::Relaxed))
}

/// What a name written in the template is bound to.
#[derive(Debug, Clone)]
enum Binding {
    /// A template binder, written as the carried name (the marking walk keeps
    /// the spelling; the instantiating walk renames it).
    Bound(SurfaceName),
    /// A template pattern variable, written as the carried name (spelling
    /// kept, origin and [`TemplateScope`] attached).
    Pattern(SurfaceName),
}

/// State of the marking walk ([`mark_template_free_references`]).
struct MarkState<'a> {
    plain: Arc<TemplateOrigin>,
    section: Arc<TemplateOrigin>,
    section_variables: &'a [SurfaceName],
    /// When collecting ([`template_free_reference_spellings`]): the marked
    /// spellings seen so far.
    spellings: Option<Vec<SurfaceName>>,
}

/// The names one pattern binds. The alternatives of an or-pattern bind the
/// same names, so every occurrence of a spelling in one pattern shares one
/// entry: (written, as written out, binding).
#[derive(Default)]
struct PatternBinds(Vec<(SurfaceName, SurfaceName, Binding)>);

impl PatternBinds {
    fn get(&self, name: &SurfaceName) -> Option<&SurfaceName> {
        self.0
            .iter()
            .find(|(written, _, _)| written == name)
            .map(|(_, out, _)| out)
    }
}

/// The one traversal behind both walks (see the module doc). The marking
/// walk has `mark`; the instantiating walk has `operands`.
struct Walker<'a> {
    /// The notation's operand variables: every identifier of one of these
    /// spellings is that operand (Lean antiquotes it), whatever binds
    /// around it.
    vars: &'a [SurfaceName],
    operands: Option<&'a [SurfaceExpr]>,
    mark: Option<MarkState<'a>>,
    /// Instantiating walk: this expansion's fresh id for each pattern scope.
    scopes: HashMap<TemplateScope, TemplateScope>,
    /// Template binders in scope, innermost last.
    env: Vec<(SurfaceName, Binding)>,
    /// Instantiating walk: whether the template carries the expansion's macro
    /// scope (binders renamed apart). `false` under `set_option hygiene
    /// false`, where only the operands are substituted.
    hygienic: bool,
}

impl<'a> Walker<'a> {
    fn instantiate(
        vars: &'a [SurfaceName],
        operands: &'a [SurfaceExpr],
        hygienic: bool,
    ) -> Walked<Self> {
        if vars.len() != operands.len() {
            return Err(TemplateRefusal::new(format!(
                "notation has {} operand variables but {} operands",
                vars.len(),
                operands.len()
            )));
        }
        Ok(Self {
            vars,
            operands: Some(operands),
            mark: None,
            scopes: HashMap::new(),
            env: Vec::new(),
            hygienic,
        })
    }

    fn mark(
        vars: &'a [SurfaceName],
        namespace: &Name,
        section_variables: &'a [SurfaceName],
        site: Option<TemplateSiteId>,
        collect: bool,
    ) -> Self {
        Self {
            vars,
            operands: None,
            mark: Some(MarkState {
                plain: Arc::new(TemplateOrigin {
                    namespace: namespace.clone(),
                    section_variable: false,
                    site,
                }),
                section: Arc::new(TemplateOrigin {
                    namespace: namespace.clone(),
                    section_variable: true,
                    site,
                }),
                section_variables,
                spellings: collect.then(Vec::new),
            }),
            scopes: HashMap::new(),
            env: Vec::new(),
            hygienic: true,
        }
    }

    /// Whether this walk renames template binders apart: the instantiating
    /// walk of a hygienic template.
    fn renames(&self) -> bool {
        self.mark.is_none() && self.hygienic
    }

    fn record(&mut self, spelling: &SurfaceName) {
        if let Some(spellings) = self.mark.as_mut().and_then(|m| m.spellings.as_mut()) {
            if !spellings.contains(spelling) {
                spellings.push(spelling.clone());
            }
        }
    }

    /// The operand variable `name` spells, if any.
    fn operand_index(&self, name: &SurfaceName) -> Option<usize> {
        if name.template_origin().is_some() || name.template_scope().is_some() {
            return None;
        }
        self.vars.iter().position(|var| var == name)
    }

    /// The innermost template binding of `name`.
    fn lookup(&self, name: &SurfaceName) -> Option<&Binding> {
        self.env
            .iter()
            .rev()
            .find(|(written, _)| written == name)
            .map(|(_, binding)| binding)
    }

    /// A name no walk touches: syntax, not a reference the template makes
    /// (`_`, a leading-dot constructor, a compiler-authored global).
    fn inert(name: &SurfaceName) -> bool {
        name.is_anonymous()
            || name.is_relative_constructor()
            || name.is_global_reference()
            || name.is_unescaped_component("_")
    }

    /// A name that already carries a template's marks: it comes from a
    /// notation expanded INSIDE this template, whose own hygiene applies.
    fn foreign(name: &SurfaceName) -> bool {
        name.template_origin().is_some() || name.template_scope().is_some()
    }

    /// This expansion's id for the pattern scope `scope`.
    fn rescope(&mut self, name: &SurfaceName) -> SurfaceName {
        match name.template_scope() {
            Some(scope) => {
                let fresh = *self.scopes.entry(scope).or_insert_with(fresh_scope);
                name.clone().with_template_scope(fresh)
            }
            None => name.clone(),
        }
    }

    /// A fresh spelling for the template binder `name`. The component holds
    /// `»`, which ends a `«…»` escape and is no identifier character, so no
    /// identifier token can spell it: no operand can refer to the binder.
    fn fresh(name: &SurfaceName) -> SurfaceName {
        let n = FRESH_TEMPLATE_BINDER.fetch_add(1, Ordering::Relaxed);
        let base = name
            .component_text()
            .map_or_else(|| name.to_string(), str::to_owned);
        SurfaceName::component(format!("{base}\u{271D}\u{BB}{n}"), false)
    }

    /// The operand `index`, which stands where only an identifier can.
    fn operand_identifier(&self, index: usize, role: &str) -> Walked<SurfaceName> {
        let operand = self
            .operands
            .and_then(|operands| operands.get(index))
            .ok_or_else(|| TemplateRefusal::new("missing notation operand"))?;
        let mut inner = operand;
        while let SurfaceExpr::Paren(_, e) = inner {
            inner = e;
        }
        match inner {
            SurfaceExpr::Ident(_, name)
                if !Self::inert(name) && !Self::foreign(name) =>
            {
                Ok(name.clone())
            }
            _ => Err(TemplateRefusal::new(format!(
                "the notation operand `{}` stands in {role} position, where Lean accepts only an identifier",
                self.vars[index]
            ))),
        }
    }

    /// A NAME the template writes that is neither a reference nor a binder:
    /// a named-argument name, a structure-instance field, a projection field,
    /// a `case` tag, a constructor alternative, an `open … in` namespace, a
    /// universe name. Lean's `notation` antiquotes EVERY identifier spelled
    /// like an operand variable, whatever it stands for, so such a name is the
    /// operand there — which must then be an identifier (`fg (x := 1) 2` with
    /// the operand `w` is `fg (w := 1) 2`; with `a + 1` Lean refuses it,
    /// "invalid argument name"). Any other name is kept.
    fn name_position(&self, name: &SurfaceName, role: &str) -> Walked<SurfaceName> {
        if self.mark.is_some() || Self::foreign(name) || name.is_relative_constructor() {
            return Ok(name.clone());
        }
        match self.operand_index(name) {
            Some(index) => self.operand_name(index, role),
            None => Ok(name.clone()),
        }
    }

    /// The name a NAME position reads from the operand `index`, which must be
    /// an identifier: its spelling with any macro scope erased (Lean reads
    /// `x✝` in a field or named-argument position as `x`,
    /// `Name.eraseMacroScopes`). A `·` operand is the identifier `x✝` Lean's
    /// `expandCDot?` makes of it (`mkFreshIdent`): `({ x } : SX)` with the
    /// operand `·` assigns the field `x`.
    fn operand_name(&self, index: usize, role: &str) -> Walked<SurfaceName> {
        let operand = self
            .operands
            .and_then(|operands| operands.get(index))
            .ok_or_else(|| TemplateRefusal::new("missing notation operand"))?;
        let mut inner = operand;
        while let SurfaceExpr::Paren(_, e) = inner {
            inner = e;
        }
        if let SurfaceExpr::Ident(_, name) = inner {
            if is_cdot_placeholder(name) {
                return Ok(SurfaceName::component("x", false));
            }
            if Self::foreign(name) && !name.is_relative_constructor() {
                return Ok(name.clone().without_template_marks());
            }
        }
        self.operand_identifier(index, role)
    }

    /// A leading-dot constructor `.x` (Lean's `Term.dotIdent`, `"." rawIdent`):
    /// its identifier is antiquoted like any other, so `.x` with the operand
    /// `none` is `.none`.
    fn relative_constructor(&self, name: &SurfaceName) -> Walked<SurfaceName> {
        if self.mark.is_some() || Self::foreign(name) {
            return Ok(name.clone());
        }
        match self.operand_index(name) {
            Some(index) => Ok(self
                .operand_name(index, "a leading-dot constructor")?
                .with_relative_constructor()),
            None => Ok(name.clone()),
        }
    }

    // ------------------------------------------------------------------
    // References and binders
    // ------------------------------------------------------------------

    /// A reference the template makes to `name`, in a NAME position (a
    /// hypothesis, a constructor head, a reassigned variable).
    fn reference_name(&mut self, name: &SurfaceName) -> Walked<SurfaceName> {
        if name.is_relative_constructor() {
            return self.relative_constructor(name);
        }
        if name.template_scope().is_some() {
            return Ok(if self.mark.is_some() {
                name.clone()
            } else {
                self.rescope(name)
            });
        }
        if Self::inert(name) || Self::foreign(name) {
            return Ok(name.clone());
        }
        if let Some(index) = self.operand_index(name) {
            return if self.mark.is_some() {
                Ok(name.clone())
            } else {
                self.operand_identifier(index, "a name")
            };
        }
        if let Some(binding) = self.lookup(name).cloned() {
            return Ok(match binding {
                Binding::Bound(out) => {
                    if self.mark.is_some() {
                        name.clone()
                    } else {
                        out
                    }
                }
                Binding::Pattern(out) => {
                    if self.mark.is_some() {
                        out
                    } else {
                        self.rescope(&out)
                    }
                }
            });
        }
        // `p.f₁.….fₖ` on a template-bound `p`: a field access on that local
        // (Lean's `resolveLocalName` tries the prefixes of a dotted name).
        if let Some((head, rest)) = name.split_first() {
            if !rest.is_anonymous() {
                if let Some(binding) = self.lookup(&head).cloned() {
                    return Ok(match binding {
                        Binding::Bound(out) => {
                            if self.mark.is_some() {
                                name.clone()
                            } else {
                                out.append(&rest)
                            }
                        }
                        Binding::Pattern(out) => {
                            if self.mark.is_some() {
                                out.append(&rest)
                            } else {
                                self.rescope(&out).append(&rest)
                            }
                        }
                    });
                }
            }
        }
        // A free reference. (A dotted `x.f` on an operand variable `x` is
        // free too: Lean antiquotes only the identifier `x` itself.)
        Ok(self.free_reference(name))
    }

    /// A reference the template binds nowhere: in the marking walk, marked
    /// with the template's origin (and recorded); otherwise as written.
    fn free_reference(&mut self, name: &SurfaceName) -> SurfaceName {
        match &self.mark {
            Some(mark) => {
                let origin = if mark.section_variables.iter().any(|var| var == name) {
                    Arc::clone(&mark.section)
                } else {
                    Arc::clone(&mark.plain)
                };
                let marked = name.clone().with_template_origin(origin);
                self.record(&marked);
                marked
            }
            None => name.clone(),
        }
    }

    /// A reference in TERM position: an operand variable is replaced by its
    /// operand.
    fn reference(&mut self, span: Span, name: &SurfaceName) -> Walked<SurfaceExpr> {
        // `.x` is a leading-dot constructor whose IDENTIFIER may be an operand
        // variable; it never stands for the operand as a term.
        if name.is_relative_constructor() {
            return Ok(SurfaceExpr::Ident(span, self.relative_constructor(name)?));
        }
        if self.mark.is_none() && !Self::foreign(name) {
            if let Some(index) = self.operand_index(name) {
                let operand = self
                    .operands
                    .and_then(|operands| operands.get(index))
                    .ok_or_else(|| TemplateRefusal::new("missing notation operand"))?;
                return Ok(SurfaceExpr::Paren(
                    operand.span(),
                    Box::new(operand.clone()),
                ));
            }
        }
        Ok(SurfaceExpr::Ident(span, self.reference_name(name)?))
    }

    /// A binder of the template: the name to write and the binding to push
    /// (none for `_` or for an operand occurrence).
    fn binder_name(&mut self, name: &SurfaceName) -> Walked<(SurfaceName, Option<Binding>)> {
        if name.is_anonymous() || name.is_unescaped_component("_") {
            return Ok((name.clone(), None));
        }
        if Self::foreign(name) {
            return Ok((name.clone(), None));
        }
        if let Some(index) = self.operand_index(name) {
            // The binder IS the operand (Lean antiquotes it); it binds
            // nothing the template can name apart from the operand.
            return if self.mark.is_some() {
                Ok((name.clone(), None))
            } else {
                Ok((self.operand_identifier(index, "a binder")?, None))
            };
        }
        // The scrutinee binder of a pattern-matching lambda is recognized by
        // its exact identity (`SurfaceName::pattern_lambda_binder`), and its
        // only reference is the generated scrutinee of its own `match`: no
        // operand can refer to it, so it keeps its identity.
        if !self.renames() || name.same_syntax(&SurfaceName::pattern_lambda_binder()) {
            return Ok((name.clone(), Some(Binding::Bound(name.clone()))));
        }
        let fresh = Self::fresh(name);
        Ok((fresh.clone(), Some(Binding::Bound(fresh))))
    }

    /// Push the binding of `name` (see [`Self::binder_name`]) and return the
    /// name to write.
    fn bind(&mut self, name: &SurfaceName) -> Walked<SurfaceName> {
        let (out, binding) = self.binder_name(name)?;
        if let Some(binding) = binding {
            self.env.push((name.clone(), binding));
        }
        Ok(out)
    }

    /// A binder's type and default, walked BEFORE the binder is in scope.
    fn binder_parts(&mut self, binder: &SurfaceBinder) -> Walked<SurfaceBinder> {
        let mut out = binder.clone();
        if let Some(ty) = &binder.ty {
            out.ty = Some(self.boxed(ty)?);
        }
        if let Some(default) = &binder.default {
            out.default = Some(self.boxed(default)?);
        }
        Ok(out)
    }

    /// A binder, walked and then brought into scope.
    fn binder(&mut self, binder: &SurfaceBinder) -> Walked<SurfaceBinder> {
        let mut out = self.binder_parts(binder)?;
        out.name = self
            .bind(&binder.name)?
            .with_header_binder_origin(binder.name.is_header_binder());
        Ok(out)
    }

    /// Walk a binder telescope, then `body` with every binder in scope.
    fn telescope(
        &mut self,
        binders: &[SurfaceBinder],
        body: &SurfaceExpr,
    ) -> Walked<(Vec<SurfaceBinder>, Box<SurfaceExpr>)> {
        let depth = self.env.len();
        let binders = binders
            .iter()
            .map(|binder| self.binder(binder))
            .collect::<Walked<Vec<_>>>()?;
        let body = self.boxed(body)?;
        self.env.truncate(depth);
        Ok((binders, body))
    }
}

/// Whether `name` is the placeholder a `·` operand of a notation stands as
/// until the parentheses around the use bind it (`__cdot_operand.<position>`,
/// `grammar::expr_app::cdot`).
fn is_cdot_placeholder(name: &SurfaceName) -> bool {
    matches!(
        name.name().inner(),
        clean_kernel::name::NameInner::Num(parent, _)
            if **parent == Name::anon().str("__cdot_operand")
    )
}

mod do_elems;
mod exprs;
mod patterns;
mod tactics;
