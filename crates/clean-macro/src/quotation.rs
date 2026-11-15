// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Syntax quotations and antiquotations
//!
//! Syntax quotations allow constructing syntax programmatically:
//! - `` `(term) `` - quote a term, producing a `Syntax` value
//! - `$x` - antiquotation: splice a `Syntax` value into a quotation
//! - `$[xs]*` - splice antiquotation: splice multiple values
//!
//! Example:
//! ```text
//! def mkAdd (x y : Syntax) : Syntax := `($x + $y)
//! ```

use crate::hygiene::{HygieneState, MacroScope};
use crate::syntax::{SourceInfo, Syntax, SyntaxKind, SyntaxNode};
use clean_kernel::Name;
use clean_parser::SurfaceName;
use std::collections::HashMap;

/// A syntax quotation with potential antiquotations
#[derive(Debug, Clone)]
pub struct SyntaxQuote {
    /// The quoted syntax (may contain antiquotation nodes)
    pub syntax: Syntax,
    /// The category of syntax being quoted (term, command, tactic, etc.)
    pub category: SyntaxKind,
}

impl SyntaxQuote {
    /// Create a new syntax quotation
    pub fn new(syntax: Syntax, category: SyntaxKind) -> Self {
        Self { syntax, category }
    }

    /// Create a term quotation
    pub fn term(syntax: Syntax) -> Self {
        Self::new(syntax, SyntaxKind::term())
    }

    /// Create a command quotation
    pub fn command(syntax: Syntax) -> Self {
        Self::new(syntax, SyntaxKind::command())
    }

    /// Create a tactic quotation
    pub fn tactic(syntax: Syntax) -> Self {
        Self::new(syntax, SyntaxKind::tactic())
    }

    /// Get all antiquotation names in this quotation
    pub fn antiquot_names(&self) -> Vec<SurfaceName> {
        self.syntax
            .collect_antiquots()
            .iter()
            .filter_map(|s| s.children().first().and_then(|c| c.as_ident()).cloned())
            .collect()
    }

    /// Check if this quotation has any antiquotations
    pub fn has_antiquots(&self) -> bool {
        !self.syntax.collect_antiquots().is_empty()
    }

    /// Substitute antiquotations with provided values
    pub fn substitute(&self, bindings: &HashMap<SurfaceName, Syntax>) -> Syntax {
        substitute_antiquots(&self.syntax, bindings)
    }

    /// Whether this template carries any fresh-name marker
    /// ([`Syntax::mk_fresh_marker`]), i.e. it came from a computed macro body
    /// that introduced a `mkFreshId` / `addMacroScope` binder.
    pub fn has_fresh_markers(&self) -> bool {
        contains_fresh_marker(&self.syntax)
    }

    /// Substitute antiquotations, replace every fresh-name marker with a
    /// distinct gensym'd identifier drawn from `hygiene`, **and rename every
    /// binder the template itself introduces** so it cannot capture the syntax
    /// spliced in through an antiquotation.
    ///
    /// This is the per-expansion path: the same stored template, applied twice,
    /// yields two *different* fresh ids because each call advances the
    /// [`HygieneState`] gensym counter (and runs inside a freshly-pushed macro
    /// scope). All markers carrying the **same prefix within one application**
    /// resolve to the **same** name (so `` `(fun $f => $f) `` binds and uses the
    /// one fresh `f`), while distinct applications get distinct names.
    ///
    /// # Hygiene of template-introduced binders
    ///
    /// The template walk is the *one* place where template-authored syntax and
    /// caller-supplied syntax are still distinguishable: everything reached by
    /// recursing through the stored template came from the macro author, and
    /// everything produced by an antiquotation came from the call site. After
    /// substitution the two are byte-identical and no post-pass can tell them
    /// apart — which is exactly why hygiene has to happen here.
    ///
    /// So, while walking, a binder written literally in the template (`let a :=
    /// 1; …`, `fun a => …`) is renamed to a scope-marked name and every
    /// *template* reference under that binder is renamed with it. Spliced
    /// subtrees are copied through untouched, so an identifier the caller passed
    /// in keeps resolving to the caller's binding. That makes
    /// `` macro "capture " x:term : term => `(let a := 1; $x + a) `` behave as
    /// Lean 4 does: in `let a := 10; capture a` the spliced `a` is the caller's
    /// `10`, not the template's `1`.
    pub(crate) fn substitute_hygienic(
        &self,
        bindings: &HashMap<SurfaceName, Syntax>,
        hygiene: &mut HygieneState,
    ) -> Syntax {
        let mut subst = TemplateSubst {
            bindings,
            hygiene,
            // Gensym one concrete name per distinct marker prefix for THIS expansion.
            fresh_names: HashMap::new(),
        };
        subst.go(&self.syntax, &Renames::new())
    }
}

/// Renaming environment in force at a point in the template walk:
/// template binder base name → its hygienic (scope-marked) name.
///
/// Empty at the root, extended when the walk enters the scope of a
/// template-introduced binder, and **never** consulted for spliced syntax.
type Renames = HashMap<SurfaceName, SurfaceName>;

/// The hygienic template walk. See [`SyntaxQuote::substitute_hygienic`].
struct TemplateSubst<'a> {
    /// Antiquotation name → caller syntax captured by the pattern match.
    bindings: &'a HashMap<SurfaceName, Syntax>,
    /// Scope state of the expansion currently being performed.
    hygiene: &'a mut HygieneState,
    /// Fresh-marker prefix → gensym'd name, memoized for THIS expansion so
    /// repeated markers with one prefix (binder and its uses) agree.
    fresh_names: HashMap<SurfaceName, SurfaceName>,
}

impl TemplateSubst<'_> {
    /// The hygienic name for a template-introduced binder `base`.
    ///
    /// Keyed on the expansion's own macro scope, so two expansions of the same
    /// macro (and an inner expansion nested inside an outer one) never share a
    /// renamed binder, while two binders of the same name inside ONE template
    /// share it harmlessly — the renaming is uniform, so ordinary shadowing
    /// still picks the nearest enclosing binder.
    fn binder_name(&self, base: &SurfaceName) -> SurfaceName {
        let scope = self
            .hygiene
            .current_scope()
            .unwrap_or_else(MacroScope::root);
        base.append(&SurfaceName::from_name(
            Name::anon().str("_macro_binder").num(scope.0),
        ))
    }

    /// Walk one template node under the active `renames`.
    fn go(&mut self, syntax: &Syntax, renames: &Renames) -> Syntax {
        // A fresh-name marker resolves to a gensym'd identifier, one per prefix.
        if let Some(prefix) = syntax.fresh_marker_prefix() {
            let name = match self.fresh_names.get(prefix) {
                Some(existing) => existing.clone(),
                None => {
                    let minted = self.hygiene.gensym(prefix).mangled();
                    self.fresh_names.insert(prefix.clone(), minted.clone());
                    minted
                }
            };
            return Syntax::ident(&name);
        }

        // An antiquotation splices CALLER syntax: it is returned verbatim and is
        // never subject to `renames`. This is the boundary that makes hygiene
        // possible at all.
        if syntax.is_antiquot() {
            if let Some(antiquot) = Antiquotation::from_syntax(syntax) {
                if let Some(replacement) = self.bindings.get(&antiquot.name) {
                    return replacement.clone();
                }
            }
            return syntax.clone();
        }

        match syntax {
            // A template identifier bound by an enclosing template binder is
            // renamed with it. Everything else — global constants such as
            // `Nat.succ` or `HAdd.hAdd` — is left alone so it keeps resolving
            // normally.
            Syntax::Ident(info, name) => match renames.get(name) {
                Some(renamed) => Syntax::Ident(info.clone(), renamed.clone()),
                None => syntax.clone(),
            },
            Syntax::Node(node) => self.node(node, renames),
            _ => syntax.clone(),
        }
    }

    /// Dispatch a node: binder-introducing shapes get scope-aware treatment,
    /// everything else is rebuilt child-wise (with splice expansion).
    fn node(&mut self, node: &SyntaxNode, renames: &Renames) -> Syntax {
        match node.kind.name_str() {
            // `let x := v; body` / `let x : T := v; body`: `x` scopes over
            // `body` only — neither `T` nor `v` may see it.
            "let" if matches!(node.children.len(), 3 | 4) => self.let_like(node, renames, false),
            // `let rec f := v; body`: `f` scopes over `v` as well as `body`.
            "letRec" if matches!(node.children.len(), 3 | 4) => self.let_like(node, renames, true),
            // Binder list followed by a body; a binder's type is elaborated
            // before that binder is in scope, but sees the earlier ones.
            "fun" | "forall" | "patternMatchLambda" if node.children.len() >= 2 => {
                self.binder_list(node, renames)
            }
            // `if h : p then t else e`: `h` scopes over both branches, not `p`.
            "ifDecidable" if node.children.len() == 4 => self.if_decidable(node, renames),
            _ => self.plain_node(node, renames),
        }
    }

    /// `let` / `letRec`: children are `[name, ty?, val, body]`.
    fn let_like(&mut self, node: &SyntaxNode, renames: &Renames, recursive: bool) -> Syntax {
        let has_ty = node.children.len() == 4;
        let val_idx = if has_ty { 2 } else { 1 };

        let mut inner = renames.clone();
        let name_out = match template_binder_name(&node.children[0]) {
            Some(base) => {
                let renamed = self.binder_name(base);
                inner.insert(base.clone(), renamed.clone());
                Syntax::Ident(node.children[0].source_info().clone(), renamed)
            }
            // The binder name itself is spliced (`` `(let $x := …) ``): there is
            // no template-introduced name to protect.
            None => self.go(&node.children[0], renames),
        };

        let mut out = Vec::with_capacity(node.children.len());
        out.push(name_out);
        if has_ty {
            out.push(self.go(&node.children[1], renames));
        }
        // A recursive binding's value is inside the binder's scope; a plain
        // `let`'s value is outside it.
        let val_env = if recursive { &inner } else { renames };
        out.push(self.go(&node.children[val_idx], val_env));
        out.push(self.go(&node.children[val_idx + 1], &inner));
        Syntax::node(node.kind.clone(), out)
    }

    /// `fun` / `forall` / `patternMatchLambda`: `[binder.., body]`.
    fn binder_list(&mut self, node: &SyntaxNode, renames: &Renames) -> Syntax {
        let body_idx = node.children.len() - 1;
        let mut env = renames.clone();
        let mut out = Vec::with_capacity(node.children.len());
        for binder in &node.children[..body_idx] {
            let (rendered, introduced) = self.binder(binder, &env);
            out.push(rendered);
            if let Some((base, renamed)) = introduced {
                env.insert(base, renamed);
            }
        }
        out.push(self.go(&node.children[body_idx], &env));
        Syntax::node(node.kind.clone(), out)
    }

    /// `ifDecidable`: `[witness, prop, then, else]`.
    fn if_decidable(&mut self, node: &SyntaxNode, renames: &Renames) -> Syntax {
        let mut inner = renames.clone();
        let witness = match template_binder_name(&node.children[0]) {
            Some(base) => {
                let renamed = self.binder_name(base);
                inner.insert(base.clone(), renamed.clone());
                Syntax::Ident(node.children[0].source_info().clone(), renamed)
            }
            None => self.go(&node.children[0], renames),
        };
        let prop = self.go(&node.children[1], renames);
        let then_br = self.go(&node.children[2], &inner);
        let else_br = self.go(&node.children[3], &inner);
        Syntax::node(node.kind.clone(), vec![witness, prop, then_br, else_br])
    }

    /// Render one binder of a binder list, reporting any rename it introduces
    /// for what follows. A binder's type is rendered in `env` — the environment
    /// *before* this binder is in scope.
    fn binder(
        &mut self,
        binder: &Syntax,
        env: &Renames,
    ) -> (Syntax, Option<(SurfaceName, SurfaceName)>) {
        // Bare-identifier binder (`fun x => …`).
        if let Syntax::Ident(info, name) = binder {
            if let Some(base) = template_binder_name(binder) {
                let renamed = self.binder_name(base);
                return (
                    Syntax::Ident(info.clone(), renamed.clone()),
                    Some((name.clone(), renamed)),
                );
            }
            return (binder.clone(), None);
        }

        // Annotated binder node (`binderDefault`/`binderImplicit`/… `[name, ty]`).
        if let Syntax::Node(node) = binder {
            if node.kind.name_str().starts_with("binder") && !node.children.is_empty() {
                let mut out = Vec::with_capacity(node.children.len());
                let introduced = match template_binder_name(&node.children[0]) {
                    Some(base) => {
                        let renamed = self.binder_name(base);
                        out.push(Syntax::Ident(
                            node.children[0].source_info().clone(),
                            renamed.clone(),
                        ));
                        Some((base.clone(), renamed))
                    }
                    None => {
                        out.push(self.go(&node.children[0], env));
                        None
                    }
                };
                for rest in &node.children[1..] {
                    out.push(self.go(rest, env));
                }
                return (Syntax::node(node.kind.clone(), out), introduced);
            }
        }

        // Anything else (antiquotation, fresh marker, pattern node): no
        // template-introduced name to protect.
        (self.go(binder, env), None)
    }

    /// Rebuild a non-binder node child-wise, expanding splice antiquotations.
    fn plain_node(&mut self, node: &SyntaxNode, renames: &Renames) -> Syntax {
        let has_splice_antiquot = node.children.iter().any(Syntax::is_antiquot_splice);
        if !has_splice_antiquot {
            let new_children: Vec<Syntax> =
                node.children.iter().map(|c| self.go(c, renames)).collect();
            return Syntax::node(node.kind.clone(), new_children);
        }

        let mut new_children = Vec::new();
        for child in &node.children {
            if !child.is_antiquot_splice() {
                new_children.push(self.go(child, renames));
                continue;
            }
            let bound = Antiquotation::from_syntax(child)
                .and_then(|antiquot| self.bindings.get(&antiquot.name).cloned());
            let Some(replacement) = bound else {
                new_children.push(child.clone());
                continue;
            };
            if replacement.kind().map(SyntaxKind::name_str) == Some("splice_list") {
                // Spliced caller syntax: walked (so any nested marker/antiquot
                // still resolves) but with an EMPTY rename environment, so the
                // template's binders can never rewrite the caller's names.
                let empty = Renames::new();
                for splice_child in replacement.children() {
                    new_children.push(self.go(splice_child, &empty));
                }
            } else {
                new_children.push(replacement);
            }
        }
        Syntax::node(node.kind.clone(), new_children)
    }
}

/// The base name of a binder written literally in the template, if this binder
/// position is one that hygiene should rename.
///
/// `None` for an antiquotation (the binder name is spliced from the call site,
/// so there is nothing template-introduced to protect) and for the wildcard `_`
/// (which has no references, so renaming it would only obscure the output).
fn template_binder_name(syntax: &Syntax) -> Option<&SurfaceName> {
    match syntax {
        Syntax::Ident(_, name) if !name.name().is_anon() && !name.is_unescaped_component("_") => {
            Some(name)
        }
        _ => None,
    }
}

/// Whether `syntax` contains a fresh-name marker anywhere in its tree.
fn contains_fresh_marker(syntax: &Syntax) -> bool {
    syntax.is_fresh_marker() || syntax.children().iter().any(contains_fresh_marker)
}

/// An antiquotation inside a quotation
#[derive(Debug, Clone)]
pub struct Antiquotation {
    /// The name of the antiquotation variable
    pub name: SurfaceName,
    /// Whether this is a splice antiquotation `$[x]*`
    pub is_splice: bool,
    /// Optional syntax category annotation (`$x:term`, `$x:tactic`, etc.)
    /// When set, this constrains what kind of syntax the antiquotation expects
    pub category: Option<SurfaceName>,
    /// Source location
    pub info: SourceInfo,
}

impl Antiquotation {
    /// Create a simple antiquotation `$name`
    pub fn simple(name: &SurfaceName) -> Self {
        Self {
            name: name.clone(),
            is_splice: false,
            category: None,
            info: SourceInfo::dummy(),
        }
    }

    /// Create a type-annotated antiquotation `$name:category`
    pub fn typed(name: &SurfaceName, category: &SurfaceName) -> Self {
        Self {
            name: name.clone(),
            is_splice: false,
            category: Some(category.clone()),
            info: SourceInfo::dummy(),
        }
    }

    /// Create a splice antiquotation `$[name]*`
    pub fn splice(name: &SurfaceName) -> Self {
        Self {
            name: name.clone(),
            is_splice: true,
            category: None,
            info: SourceInfo::dummy(),
        }
    }

    /// Create a typed splice antiquotation `$[name:category]*`
    pub fn typed_splice(name: &SurfaceName, category: &SurfaceName) -> Self {
        Self {
            name: name.clone(),
            is_splice: true,
            category: Some(category.clone()),
            info: SourceInfo::dummy(),
        }
    }

    /// Create from a syntax node
    pub fn from_syntax(syntax: &Syntax) -> Option<Self> {
        if !syntax.is_antiquot() {
            return None;
        }

        let kind = syntax.kind()?;
        let is_splice = kind.is_antiquotation() && kind.name_str().contains("splice");

        // Check for typed antiquotation (has category child)
        let children = syntax.children();
        let name = children.first()?.as_ident()?.clone();

        // Second child is the category annotation if present
        let category = children.get(1).and_then(|c| c.as_ident()).cloned();

        Some(Self {
            name,
            is_splice,
            category,
            info: syntax.source_info().clone(),
        })
    }

    /// Check if this antiquotation has a type annotation
    pub fn is_typed(&self) -> bool {
        self.category.is_some()
    }
}

/// Substitute all antiquotations in syntax with provided values
/// Handles both simple antiquotations and splice antiquotations
fn substitute_antiquots(syntax: &Syntax, bindings: &HashMap<SurfaceName, Syntax>) -> Syntax {
    substitute_recursive(syntax, bindings)
}

/// Recursive substitution that handles splices in node children
fn substitute_recursive(syntax: &Syntax, bindings: &HashMap<SurfaceName, Syntax>) -> Syntax {
    // Check if this is an antiquotation to substitute
    if syntax.is_antiquot() {
        if let Some(antiquot) = Antiquotation::from_syntax(syntax) {
            if let Some(replacement) = bindings.get(&antiquot.name) {
                // For splice bindings (splice_list nodes), if used in a simple antiquot position,
                // we just return the splice_list as-is. It will be expanded by the parent if needed.
                return replacement.clone();
            }
        }
        // No binding found, leave as-is
        return syntax.clone();
    }

    // For nodes, recursively process children and handle splices
    match syntax {
        Syntax::Node(node) => {
            // Check if any children are splice antiquotations that need expansion
            let has_splice_antiquot = node.children.iter().any(Syntax::is_antiquot_splice);

            if has_splice_antiquot {
                // Need to expand splice antiquotations in children
                let mut new_children = Vec::new();
                for child in &node.children {
                    if child.is_antiquot_splice() {
                        // Splice antiquotation: expand the list binding
                        if let Some(antiquot) = Antiquotation::from_syntax(child) {
                            if let Some(replacement) = bindings.get(&antiquot.name) {
                                // If it's a splice_list, expand its children
                                if let Some(kind) = replacement.kind() {
                                    if kind.name_str() == "splice_list" {
                                        for splice_child in replacement.children() {
                                            new_children
                                                .push(substitute_recursive(splice_child, bindings));
                                        }
                                        continue;
                                    }
                                }
                                // Otherwise, treat as single element
                                new_children.push(replacement.clone());
                                continue;
                            }
                        }
                        // No binding, leave as-is
                        new_children.push(child.clone());
                    } else {
                        // Regular child, recurse
                        new_children.push(substitute_recursive(child, bindings));
                    }
                }
                Syntax::node(node.kind.clone(), new_children)
            } else {
                // No splices, just recurse into children
                let new_children: Vec<Syntax> = node
                    .children
                    .iter()
                    .map(|c| substitute_recursive(c, bindings))
                    .collect();
                Syntax::node(node.kind.clone(), new_children)
            }
        }
        // Other syntax types pass through unchanged
        _ => syntax.clone(),
    }
}

/// Parse a syntax quotation from a string
///
/// This is a simplified parser for quotations. The full implementation
/// would integrate with the main parser.
pub fn parse_quotation(input: &str) -> Result<SyntaxQuote, QuotationError> {
    let trimmed = input.trim();

    // Check for quotation syntax: `(...)
    if !trimmed.starts_with('`') {
        return Err(QuotationError::NotAQuotation);
    }

    let rest = &trimmed[1..];

    // Determine category and parse content
    let (category, content) = if rest.starts_with('(') && rest.ends_with(')') {
        // A category delimiter is a lexical token AFTER one identifier, not
        // a pipe inside an escaped name or string and not the `||` operator.
        // Keep custom categories distinct; registration decides whether the
        // category exists and has an executable consumer.
        let inner = &rest[1..rest.len() - 1];
        category_quotation_content(inner).unwrap_or((SyntaxKind::term(), inner))
    } else if rest.starts_with('[') && rest.ends_with(']') {
        // Tactic quotation: `[tactic]
        (SyntaxKind::tactic(), &rest[1..rest.len() - 1])
    } else if rest.starts_with('{') && rest.ends_with('}') {
        // Command quotation: `{command}
        (SyntaxKind::command(), &rest[1..rest.len() - 1])
    } else {
        // Simple identifier quotation
        (SyntaxKind::ident_kind(), rest)
    };

    let syntax = parse_quoted_content(content)?;

    Ok(SyntaxQuote::new(syntax, category))
}

fn category_quotation_content(content: &str) -> Option<(SyntaxKind, &str)> {
    use clean_parser::lexer::{Lexer, TokenKind};

    let mut lexer = Lexer::new(content);
    let head = lexer.next_token();
    let TokenKind::Ident(text) = &head.kind else {
        return None;
    };
    let bar = lexer.next_token();
    if bar.kind != TokenKind::Pipe || head.span.end != bar.span.start {
        return None;
    }
    let body = content.get(bar.span.end..)?;
    if body.starts_with('|') {
        return None;
    }
    let name = SurfaceName::component(text, head.ident_escaped);
    Some((SyntaxKind::from_name(name.into_name()), body))
}

/// Parse the content inside a quotation
fn parse_quoted_content(content: &str) -> Result<Syntax, QuotationError> {
    let trimmed = content.trim();

    if trimmed.is_empty() {
        return Ok(Syntax::missing());
    }

    // Whitespace inside escaped components belongs to the identifier. Never
    // split it, or treat a printed path as a sequence of identifier tokens.
    let parts = quoted_parts(trimmed)?;
    if parts.len() > 1 {
        let func = parse_quoted_content(parts[0])?;
        let args = parts[1..]
            .iter()
            .map(|part| parse_quoted_content(part))
            .collect::<Result<_, _>>()?;
        return Ok(Syntax::mk_app(func, args));
    }

    if let Some(rest) = trimmed.strip_prefix('$') {
        return parse_antiquotation(rest);
    }
    if trimmed.starts_with('(') && trimmed.ends_with(')') {
        return Ok(Syntax::mk_paren(parse_quoted_content(
            &trimmed[1..trimmed.len() - 1],
        )?));
    }

    // Check for string literal
    if trimmed.starts_with('"') && trimmed.ends_with('"') && trimmed.len() > 1 {
        return Ok(Syntax::mk_str(&trimmed[1..trimmed.len() - 1]));
    }

    // Check for numeric literal
    if let Ok(n) = trimmed.parse::<u64>() {
        return Ok(Syntax::mk_num(n));
    }

    // Bare universe keywords and the wildcard are lexical syntax, not
    // identifiers accepted by the strict source-name parser. Keep the Plain
    // wildcard distinct from the same-identity escaped identifier `«_»`.
    if matches!(trimmed, "Type" | "Prop" | "_") {
        return Ok(Syntax::ident(&SurfaceName::component(trimmed, false)));
    }
    Ok(Syntax::ident(&parse_source_name(trimmed)?))
}

fn parse_source_name(input: &str) -> Result<SurfaceName, QuotationError> {
    clean_parser::parse_name(input).map_err(|error| QuotationError::ParseError(error.to_string()))
}

/// Parse an antiquotation after the $
fn parse_antiquotation(content: &str) -> Result<Syntax, QuotationError> {
    let trimmed = content.trim();
    let (inner, splice) = if let Some(rest) = trimmed.strip_prefix('[') {
        (
            rest.strip_suffix("]*")
                .ok_or(QuotationError::MalformedAntiquotation)?,
            true,
        )
    } else if let Some(rest) = trimmed.strip_prefix('(') {
        (
            rest.strip_suffix(')')
                .ok_or(QuotationError::MalformedAntiquotation)?,
            false,
        )
    } else {
        (trimmed, false)
    };
    // A colon inside «…» is identifier text, not a category separator.
    let mut escaped = false;
    let colon = inner.char_indices().find_map(|(index, ch)| match ch {
        '«' => {
            escaped = true;
            None
        }
        '»' => {
            escaped = false;
            None
        }
        ':' if !escaped => Some(index),
        _ => None,
    });
    let (name, category) = match colon {
        Some(index) => (
            parse_source_name(inner[..index].trim())?,
            Some(parse_source_name(inner[index + 1..].trim())?),
        ),
        None => (parse_source_name(inner.trim())?, None),
    };
    Ok(match (splice, category) {
        (false, None) => Syntax::mk_antiquot(&name),
        (true, None) => Syntax::mk_antiquot_splice(&name),
        (false, Some(category)) => Syntax::mk_antiquot_typed(&name, &category),
        (true, Some(category)) => Syntax::mk_antiquot_splice_typed(&name, &category),
    })
}

/// Split only top-level whitespace; lexical identifier contents stay intact.
fn quoted_parts(content: &str) -> Result<Vec<&str>, QuotationError> {
    let mut parts = Vec::new();
    let mut start = 0;
    let mut delimiters = Vec::new();
    let mut escaped_name = false;
    let mut string = false;
    let mut slash = false;
    for (index, ch) in content.char_indices() {
        if escaped_name {
            if ch == '»' {
                escaped_name = false;
            }
            continue;
        }
        if string {
            if slash {
                slash = false;
            } else if ch == '\\' {
                slash = true;
            } else if ch == '"' {
                string = false;
            }
            continue;
        }
        match ch {
            '«' => escaped_name = true,
            '"' => string = true,
            '(' => delimiters.push(')'),
            '[' => delimiters.push(']'),
            '{' => delimiters.push('}'),
            ')' | ']' | '}' => {
                if delimiters.pop() != Some(ch) {
                    return Err(QuotationError::UnbalancedDelimiters);
                }
            }
            ch if ch.is_whitespace() && delimiters.is_empty() => {
                if start < index {
                    parts.push(&content[start..index]);
                }
                start = index + ch.len_utf8();
            }
            _ => {}
        }
    }
    if escaped_name || string || !delimiters.is_empty() {
        return Err(QuotationError::UnbalancedDelimiters);
    }
    if start < content.len() {
        parts.push(&content[start..]);
    }
    Ok(parts)
}

/// Quotation parsing error
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum QuotationError {
    /// Input is not a valid quotation (doesn't start with backtick or `q!`)
    #[error("not a quotation")]
    NotAQuotation,
    /// Antiquotation syntax is malformed (e.g., unclosed `$`)
    #[error("malformed antiquotation")]
    MalformedAntiquotation,
    /// Delimiter mismatch (e.g., unmatched parentheses or brackets)
    #[error("unbalanced delimiters")]
    UnbalancedDelimiters,
    /// General parse error with description
    #[error("parse error: {0}")]
    ParseError(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_quotation() {
        let quote = parse_quotation("`(foo)").unwrap();
        assert_eq!(quote.category, SyntaxKind::term());
        assert_eq!(
            quote.syntax.as_ident(),
            Some(&SurfaceName::generated_path("foo"))
        );
    }

    #[test]
    fn test_parse_application_quotation() {
        let quote = parse_quotation("`(f x)").unwrap();
        assert!(quote.syntax.is_node());
        assert_eq!(quote.syntax.children().len(), 2);
    }

    #[test]
    fn test_parse_antiquotation() {
        let quote = parse_quotation("`($x)").unwrap();
        assert!(quote.syntax.is_antiquot());
        let names = quote.antiquot_names();
        assert_eq!(names, vec![SurfaceName::generated_path("x")]);
    }

    #[test]
    fn test_parse_numeric_literal() {
        let quote = parse_quotation("`(42)").unwrap();
        assert!(quote.syntax.is_node());
        assert_eq!(quote.syntax.kind(), Some(&SyntaxKind::num()));
    }

    #[test]
    fn test_antiquotation_from_syntax() {
        let syntax = Syntax::generated_antiquot("x");
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, SurfaceName::generated_path("x"));
        assert!(!antiquot.is_splice);
    }

    #[test]
    fn test_substitute_antiquots() {
        let mut bindings = HashMap::new();
        bindings.insert(
            SurfaceName::generated_path("x"),
            Syntax::generated_ident("replaced"),
        );

        let quote = SyntaxQuote::term(Syntax::mk_app(
            Syntax::generated_ident("f"),
            vec![Syntax::generated_antiquot("x")],
        ));

        let result = quote.substitute(&bindings);
        let pretty = result.pretty();
        assert!(pretty.contains("replaced"));
    }

    #[test]
    fn test_has_antiquots() {
        let quote1 = SyntaxQuote::term(Syntax::generated_ident("foo"));
        assert!(!quote1.has_antiquots());

        let quote2 = SyntaxQuote::term(Syntax::generated_antiquot("x"));
        assert!(quote2.has_antiquots());
    }

    #[test]
    fn test_parse_splice_antiquotation() {
        let syntax = parse_antiquotation("[items]*").unwrap();
        assert!(syntax.is_antiquot());
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert!(antiquot.is_splice);
        assert_eq!(antiquot.name, SurfaceName::generated_path("items"));
    }

    #[test]
    fn test_quotation_error_display() {
        assert_eq!(
            format!("{}", QuotationError::NotAQuotation),
            "not a quotation"
        );
        assert_eq!(
            format!("{}", QuotationError::MalformedAntiquotation),
            "malformed antiquotation"
        );
    }

    #[test]
    fn test_substitute_splice_antiquots() {
        // Test that splice bindings are expanded in replacement
        // Pattern: `(f $[args]*)` -> `(g $[args]*)`
        // With args = [a, b], result should be (g a b)
        let mut bindings = HashMap::new();

        // Create a splice_list binding
        let splice_list = Syntax::node(
            SyntaxKind::app("splice_list"),
            vec![Syntax::generated_ident("a"), Syntax::generated_ident("b")],
        );
        bindings.insert(SurfaceName::generated_path("args"), splice_list);

        // Create replacement template with splice antiquotation
        let template = SyntaxQuote::term(Syntax::node(
            SyntaxKind::app_kind(),
            vec![
                Syntax::generated_ident("g"),
                Syntax::mk_antiquot_splice(&SurfaceName::generated_path("args")),
            ],
        ));

        let result = template.substitute(&bindings);

        // Result should be (g a b)
        assert!(result.is_node());
        let children = result.children();
        assert_eq!(children.len(), 3); // g, a, b
        assert_eq!(
            children[0].as_ident(),
            Some(&SurfaceName::generated_path("g"))
        );
        assert_eq!(
            children[1].as_ident(),
            Some(&SurfaceName::generated_path("a"))
        );
        assert_eq!(
            children[2].as_ident(),
            Some(&SurfaceName::generated_path("b"))
        );
    }

    #[test]
    fn test_substitute_empty_splice() {
        // Test splice with empty list
        // Pattern: `(f $[args]*)` with args = []
        // Result should be (f)
        let mut bindings = HashMap::new();

        // Create an empty splice_list
        let splice_list = Syntax::node(SyntaxKind::app("splice_list"), vec![]);
        bindings.insert(SurfaceName::generated_path("args"), splice_list);

        // Create replacement template
        let template = SyntaxQuote::term(Syntax::node(
            SyntaxKind::app_kind(),
            vec![
                Syntax::generated_ident("f"),
                Syntax::mk_antiquot_splice(&SurfaceName::generated_path("args")),
            ],
        ));

        let result = template.substitute(&bindings);

        // Result should be (f)
        assert!(result.is_node());
        let children = result.children();
        assert_eq!(children.len(), 1); // just f
        assert_eq!(
            children[0].as_ident(),
            Some(&SurfaceName::generated_path("f"))
        );
    }

    #[test]
    fn test_parse_typed_antiquotation_simple() {
        // $x:term
        let syntax = parse_antiquotation("x:term").unwrap();
        assert!(syntax.is_antiquot());
        assert!(syntax.is_antiquot_typed());
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, SurfaceName::generated_path("x"));
        assert!(!antiquot.is_splice);
        assert_eq!(antiquot.category, Some(SurfaceName::generated_path("term")));
    }

    #[test]
    fn test_parse_typed_antiquotation_tactic() {
        // $t:tactic
        let syntax = parse_antiquotation("t:tactic").unwrap();
        assert!(syntax.is_antiquot_typed());
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, SurfaceName::generated_path("t"));
        assert_eq!(
            antiquot.category,
            Some(SurfaceName::generated_path("tactic"))
        );
    }

    #[test]
    fn test_parse_typed_splice_antiquotation() {
        // $[args:term]*
        let syntax = parse_antiquotation("[args:term]*").unwrap();
        assert!(syntax.is_antiquot());
        assert!(syntax.is_antiquot_splice());
        assert!(syntax.is_antiquot_typed());
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, SurfaceName::generated_path("args"));
        assert!(antiquot.is_splice);
        assert_eq!(antiquot.category, Some(SurfaceName::generated_path("term")));
    }

    #[test]
    fn test_parse_parenthesized_typed_antiquotation() {
        // $(expr:term)
        let syntax = parse_antiquotation("(foo:term)").unwrap();
        assert!(syntax.is_antiquot_typed());
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, SurfaceName::generated_path("foo"));
        assert_eq!(antiquot.category, Some(SurfaceName::generated_path("term")));
    }

    #[test]
    fn test_antiquotation_typed_constructor() {
        let antiquot = Antiquotation::typed(
            &SurfaceName::generated_path("x"),
            &SurfaceName::generated_path("term"),
        );
        assert_eq!(antiquot.name, SurfaceName::generated_path("x"));
        assert!(!antiquot.is_splice);
        assert!(antiquot.is_typed());
        assert_eq!(antiquot.category, Some(SurfaceName::generated_path("term")));
    }

    #[test]
    fn test_antiquotation_typed_splice_constructor() {
        let antiquot = Antiquotation::typed_splice(
            &SurfaceName::generated_path("args"),
            &SurfaceName::generated_path("command"),
        );
        assert_eq!(antiquot.name, SurfaceName::generated_path("args"));
        assert!(antiquot.is_splice);
        assert!(antiquot.is_typed());
        assert_eq!(
            antiquot.category,
            Some(SurfaceName::generated_path("command"))
        );
    }

    #[test]
    fn test_mk_antiquot_typed() {
        let syntax = Syntax::mk_antiquot_typed(
            &SurfaceName::generated_path("x"),
            &SurfaceName::generated_path("term"),
        );
        assert!(syntax.is_antiquot());
        assert!(syntax.is_antiquot_typed());
        let children = syntax.children();
        assert_eq!(children.len(), 2);
        assert_eq!(
            children[0].as_ident(),
            Some(&SurfaceName::generated_path("x"))
        );
        assert_eq!(
            children[1].as_ident(),
            Some(&SurfaceName::generated_path("term"))
        );
    }

    #[test]
    fn test_mk_antiquot_splice_typed() {
        let syntax = Syntax::mk_antiquot_splice_typed(
            &SurfaceName::generated_path("items"),
            &SurfaceName::generated_path("tactic"),
        );
        assert!(syntax.is_antiquot());
        assert!(syntax.is_antiquot_splice());
        assert!(syntax.is_antiquot_typed());
        let children = syntax.children();
        assert_eq!(children.len(), 2);
        assert_eq!(
            children[0].as_ident(),
            Some(&SurfaceName::generated_path("items"))
        );
        assert_eq!(
            children[1].as_ident(),
            Some(&SurfaceName::generated_path("tactic"))
        );
    }

    #[test]
    fn test_antiquotation_from_typed_syntax() {
        let syntax = Syntax::mk_antiquot_typed(
            &SurfaceName::generated_path("expr"),
            &SurfaceName::generated_path("term"),
        );
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, SurfaceName::generated_path("expr"));
        assert!(!antiquot.is_splice);
        assert_eq!(antiquot.category, Some(SurfaceName::generated_path("term")));
    }

    #[test]
    fn test_antiquotation_from_typed_splice_syntax() {
        let syntax = Syntax::mk_antiquot_splice_typed(
            &SurfaceName::generated_path("stmts"),
            &SurfaceName::generated_path("command"),
        );
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, SurfaceName::generated_path("stmts"));
        assert!(antiquot.is_splice);
        assert_eq!(
            antiquot.category,
            Some(SurfaceName::generated_path("command"))
        );
    }

    #[test]
    fn test_untyped_antiquotation_has_no_category() {
        let syntax = Syntax::generated_antiquot("x");
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert!(!antiquot.is_typed());
        assert_eq!(antiquot.category, None);
    }

    // ---- Hygiene of template-introduced binders ----
    //
    // These exercise `substitute_hygienic` directly: the template walk is the
    // only place where template-authored and caller-spliced syntax are still
    // distinguishable, so it is where hygiene must happen.

    /// Run one hygienic expansion of `template` with `bindings`, inside a fresh
    /// macro scope (as `HygienicExpander` does).
    fn expand_template(template: Syntax, bindings: &[(&str, Syntax)]) -> Syntax {
        let mut state = HygieneState::new();
        let _scope = state.push_scope();
        let map: HashMap<SurfaceName, Syntax> = bindings
            .iter()
            .map(|(k, v)| (SurfaceName::generated_path(k), v.clone()))
            .collect();
        SyntaxQuote::term(template).substitute_hygienic(&map, &mut state)
    }

    #[test]
    fn test_template_let_binder_renamed_spliced_ident_untouched() {
        // Template `let a := 1; $x + a` applied with `$x := a` (the caller's own
        // `a`). The template's binder and the template's `a` must be renamed
        // together; the SPLICED `a` must survive verbatim so it still resolves
        // to the caller's binding. Before this, both `a`s were identical after
        // substitution and the template captured the argument.
        let template = Syntax::mk_let(
            Syntax::generated_ident("a"),
            None,
            Syntax::mk_num(1),
            Syntax::mk_app(
                Syntax::generated_ident("HAdd.hAdd"),
                vec![
                    Syntax::generated_antiquot("x"),
                    Syntax::generated_ident("a"),
                ],
            ),
        );
        let result = expand_template(template, &[("x", Syntax::generated_ident("a"))]);

        let binder = result.child(0).and_then(Syntax::as_ident).unwrap();
        assert_ne!(
            binder,
            &SurfaceName::generated_path("a"),
            "template binder must be renamed"
        );
        assert!(
            binder.to_string().starts_with('a'),
            "renamed binder keeps its base name"
        );

        let sum = result.child(2).expect("let body");
        assert_eq!(
            sum.child(1).and_then(Syntax::as_ident),
            Some(&SurfaceName::generated_path("a")),
            "the SPLICED argument must not be renamed"
        );
        assert_eq!(
            sum.child(2).and_then(Syntax::as_ident),
            Some(binder),
            "the template's own reference must follow the renamed binder"
        );
    }

    #[test]
    fn test_template_global_constant_reference_not_renamed() {
        // Guard against over-renaming: a template legitimately mentions global
        // constants. Only binders the template introduces (and references to
        // them) may be touched.
        let template = Syntax::mk_app(
            Syntax::generated_ident("Nat.succ"),
            vec![
                Syntax::generated_antiquot("x"),
                Syntax::generated_ident("HAdd.hAdd"),
            ],
        );
        let result = expand_template(template, &[("x", Syntax::generated_ident("n"))]);
        assert_eq!(
            result.child(0).and_then(Syntax::as_ident),
            Some(&SurfaceName::generated_path("Nat.succ"))
        );
        assert_eq!(
            result.child(1).and_then(Syntax::as_ident),
            Some(&SurfaceName::generated_path("n"))
        );
        assert_eq!(
            result.child(2).and_then(Syntax::as_ident),
            Some(&SurfaceName::generated_path("HAdd.hAdd")),
            "a global constant in the template must resolve normally"
        );
    }

    #[test]
    fn test_template_let_value_is_outside_binder_scope() {
        // In `let a := a; …` the right-hand `a` is the OUTER `a`, so it must not
        // be renamed to the binder being introduced.
        let template = Syntax::mk_let(
            Syntax::generated_ident("a"),
            None,
            Syntax::generated_ident("a"),
            Syntax::generated_ident("a"),
        );
        let result = expand_template(template, &[]);
        let binder = result.child(0).and_then(Syntax::as_ident).unwrap();
        assert_eq!(
            result.child(1).and_then(Syntax::as_ident),
            Some(&SurfaceName::generated_path("a")),
            "a plain let's value is outside its own binder's scope"
        );
        assert_eq!(
            result.child(2).and_then(Syntax::as_ident),
            Some(binder),
            "the body IS inside the binder's scope"
        );
    }

    #[test]
    fn test_template_fun_binder_renamed() {
        // Lambda binders are template-introduced too.
        let template = Syntax::mk_lambda(
            vec![Syntax::generated_ident("y")],
            Syntax::mk_app(
                Syntax::generated_ident("f"),
                vec![
                    Syntax::generated_ident("y"),
                    Syntax::generated_antiquot("x"),
                ],
            ),
        );
        let result = expand_template(template, &[("x", Syntax::generated_ident("y"))]);
        let binder = result.child(0).and_then(Syntax::as_ident).unwrap();
        assert_ne!(
            binder,
            &SurfaceName::generated_path("y"),
            "lambda binder must be renamed"
        );
        let body = result.child(1).expect("lambda body");
        assert_eq!(body.child(1).and_then(Syntax::as_ident), Some(binder));
        assert_eq!(
            body.child(2).and_then(Syntax::as_ident),
            Some(&SurfaceName::generated_path("y")),
            "the spliced `y` keeps referring to the caller's `y`"
        );
    }

    #[test]
    fn test_spliced_binder_name_not_renamed() {
        // `` `(let $n := 1; $n) `` — the binder NAME comes from the call site, so
        // there is nothing template-introduced to protect and it must pass
        // through unchanged (this is how `do`-notation desugaring works).
        let template = Syntax::mk_let(
            Syntax::generated_antiquot("n"),
            None,
            Syntax::mk_num(1),
            Syntax::generated_antiquot("n"),
        );
        let result = expand_template(template, &[("n", Syntax::generated_ident("userVar"))]);
        assert_eq!(
            result.child(0).and_then(Syntax::as_ident),
            Some(&SurfaceName::generated_path("userVar"))
        );
        assert_eq!(
            result.child(2).and_then(Syntax::as_ident),
            Some(&SurfaceName::generated_path("userVar"))
        );
    }

    #[test]
    fn test_wildcard_binder_not_renamed() {
        // `fun _ => …` has no references; renaming `_` would only obscure the
        // output (and several built-in desugarings rely on the literal `_`).
        let template = Syntax::mk_lambda(
            vec![Syntax::generated_ident("_")],
            Syntax::generated_antiquot("e"),
        );
        let result = expand_template(template, &[("e", Syntax::generated_ident("body"))]);
        assert_eq!(
            result.child(0).and_then(Syntax::as_ident),
            Some(&SurfaceName::generated_path("_"))
        );
        assert_eq!(
            result.child(1).and_then(Syntax::as_ident),
            Some(&SurfaceName::generated_path("body"))
        );
    }

    #[test]
    fn test_template_binder_distinct_per_expansion() {
        // Two expansions of the same template must not share a renamed binder,
        // so an outer expansion's binder cannot be captured by an inner one.
        let template = || {
            Syntax::mk_let(
                Syntax::generated_ident("a"),
                None,
                Syntax::mk_num(1),
                Syntax::generated_ident("a"),
            )
        };
        let first = expand_template(template(), &[]);
        let second = expand_template(template(), &[]);
        assert_ne!(
            first.child(0).and_then(Syntax::as_ident),
            second.child(0).and_then(Syntax::as_ident),
            "each expansion gets its own scope-marked binder"
        );
    }

    #[test]
    fn test_binderless_template_unchanged_by_hygiene() {
        // NEGATIVE: a template with no binders expands byte-identically to the
        // non-hygienic path, so the common case is untouched.
        let template = Syntax::mk_app(
            Syntax::generated_ident("f"),
            vec![
                Syntax::generated_antiquot("x"),
                Syntax::generated_ident("g"),
            ],
        );
        let quote = SyntaxQuote::term(template.clone());
        let mut bindings = HashMap::new();
        bindings.insert(
            SurfaceName::generated_path("x"),
            Syntax::generated_ident("arg"),
        );
        let mut state = HygieneState::new();
        let _scope = state.push_scope();
        assert_eq!(
            quote.substitute_hygienic(&bindings, &mut state).pretty(),
            quote.substitute(&bindings).pretty(),
        );
    }
}
