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
    pub fn antiquot_names(&self) -> Vec<String> {
        self.syntax
            .collect_antiquots()
            .iter()
            .filter_map(|s| {
                s.children()
                    .first()
                    .and_then(|c| c.as_ident())
                    .map(String::from)
            })
            .collect()
    }

    /// Check if this quotation has any antiquotations
    pub fn has_antiquots(&self) -> bool {
        !self.syntax.collect_antiquots().is_empty()
    }

    /// Substitute antiquotations with provided values
    pub fn substitute(&self, bindings: &HashMap<String, Syntax>) -> Syntax {
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
    pub fn substitute_hygienic(
        &self,
        bindings: &HashMap<String, Syntax>,
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

/// Character marking a binder that macro hygiene renamed.
///
/// `✝` is rejected by the lexer's identifier rule (`is_ident_continue`), so a
/// renamed template binder can never collide with a name the user could have
/// written, nor with any spliced identifier (which is never renamed).
const MACRO_BINDER_MARK: char = '✝';

/// Renaming environment in force at a point in the template walk:
/// template binder base name → its hygienic (scope-marked) name.
///
/// Empty at the root, extended when the walk enters the scope of a
/// template-introduced binder, and **never** consulted for spliced syntax.
type Renames = HashMap<String, String>;

/// The hygienic template walk. See [`SyntaxQuote::substitute_hygienic`].
struct TemplateSubst<'a> {
    /// Antiquotation name → caller syntax captured by the pattern match.
    bindings: &'a HashMap<String, Syntax>,
    /// Scope state of the expansion currently being performed.
    hygiene: &'a mut HygieneState,
    /// Fresh-marker prefix → gensym'd name, memoized for THIS expansion so
    /// repeated markers with one prefix (binder and its uses) agree.
    fresh_names: HashMap<String, String>,
}

impl TemplateSubst<'_> {
    /// The hygienic name for a template-introduced binder `base`.
    ///
    /// Keyed on the expansion's own macro scope, so two expansions of the same
    /// macro (and an inner expansion nested inside an outer one) never share a
    /// renamed binder, while two binders of the same name inside ONE template
    /// share it harmlessly — the renaming is uniform, so ordinary shadowing
    /// still picks the nearest enclosing binder.
    fn binder_name(&self, base: &str) -> String {
        let scope = self
            .hygiene
            .current_scope()
            .unwrap_or_else(MacroScope::root);
        format!("{base}{MACRO_BINDER_MARK}{}", scope.0)
    }

    /// Walk one template node under the active `renames`.
    fn go(&mut self, syntax: &Syntax, renames: &Renames) -> Syntax {
        // A fresh-name marker resolves to a gensym'd identifier, one per prefix.
        if let Some(prefix) = syntax.fresh_marker_prefix() {
            let name = match self.fresh_names.get(prefix) {
                Some(existing) => existing.clone(),
                None => {
                    let minted = self.hygiene.gensym(prefix).mangled();
                    self.fresh_names.insert(prefix.to_string(), minted.clone());
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
                inner.insert(base.to_string(), renamed.clone());
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
                inner.insert(base.to_string(), renamed.clone());
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
    fn binder(&mut self, binder: &Syntax, env: &Renames) -> (Syntax, Option<(String, String)>) {
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
                        Some((base.to_string(), renamed))
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
fn template_binder_name(syntax: &Syntax) -> Option<&str> {
    match syntax {
        Syntax::Ident(_, name) if !name.is_empty() && name != "_" => Some(name),
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
    pub name: String,
    /// Whether this is a splice antiquotation `$[x]*`
    pub is_splice: bool,
    /// Optional syntax category annotation (`$x:term`, `$x:tactic`, etc.)
    /// When set, this constrains what kind of syntax the antiquotation expects
    pub category: Option<String>,
    /// Source location
    pub info: SourceInfo,
}

impl Antiquotation {
    /// Create a simple antiquotation `$name`
    pub fn simple(name: &str) -> Self {
        Self {
            name: name.to_string(),
            is_splice: false,
            category: None,
            info: SourceInfo::dummy(),
        }
    }

    /// Create a type-annotated antiquotation `$name:category`
    pub fn typed(name: &str, category: &str) -> Self {
        Self {
            name: name.to_string(),
            is_splice: false,
            category: Some(category.to_string()),
            info: SourceInfo::dummy(),
        }
    }

    /// Create a splice antiquotation `$[name]*`
    pub fn splice(name: &str) -> Self {
        Self {
            name: name.to_string(),
            is_splice: true,
            category: None,
            info: SourceInfo::dummy(),
        }
    }

    /// Create a typed splice antiquotation `$[name:category]*`
    pub fn typed_splice(name: &str, category: &str) -> Self {
        Self {
            name: name.to_string(),
            is_splice: true,
            category: Some(category.to_string()),
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
        let name = children.first()?.as_ident()?.to_string();

        // Second child is the category annotation if present
        let category = children.get(1).and_then(|c| c.as_ident()).map(String::from);

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
fn substitute_antiquots(syntax: &Syntax, bindings: &HashMap<String, Syntax>) -> Syntax {
    substitute_recursive(syntax, bindings)
}

/// Recursive substitution that handles splices in node children
fn substitute_recursive(syntax: &Syntax, bindings: &HashMap<String, Syntax>) -> Syntax {
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
        // Term quotation: `(term)
        (SyntaxKind::term(), &rest[1..rest.len() - 1])
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

/// Parse the content inside a quotation
fn parse_quoted_content(content: &str) -> Result<Syntax, QuotationError> {
    let trimmed = content.trim();

    if trimmed.is_empty() {
        return Ok(Syntax::missing());
    }

    // Check for antiquotation
    if let Some(rest) = trimmed.strip_prefix('$') {
        return parse_antiquotation(rest);
    }

    // Check for nested parentheses (application)
    if trimmed.contains(' ') && !trimmed.starts_with('"') {
        let parts: Vec<&str> = trimmed.splitn(2, ' ').collect();
        if parts.len() == 2 {
            let func = parse_quoted_content(parts[0])?;
            let args = parse_args(parts[1])?;
            return Ok(Syntax::mk_app(func, args));
        }
    }

    // Check for string literal
    if trimmed.starts_with('"') && trimmed.ends_with('"') && trimmed.len() > 1 {
        return Ok(Syntax::mk_str(&trimmed[1..trimmed.len() - 1]));
    }

    // Check for numeric literal
    if let Ok(n) = trimmed.parse::<u64>() {
        return Ok(Syntax::mk_num(n));
    }

    // Treat as identifier
    Ok(Syntax::ident(trimmed))
}

/// Parse an antiquotation after the $
fn parse_antiquotation(content: &str) -> Result<Syntax, QuotationError> {
    let trimmed = content.trim();

    // Check for splice: $[name]* or $[name:category]*
    if trimmed.starts_with('[') {
        if let Some(end) = trimmed.find("]*") {
            let inner = &trimmed[1..end];
            // Check for type annotation within splice
            if let Some(colon_pos) = inner.find(':') {
                let name = &inner[..colon_pos];
                let category = &inner[colon_pos + 1..];
                return Ok(Syntax::mk_antiquot_splice_typed(name, category));
            }
            return Ok(Syntax::mk_antiquot_splice(inner));
        }
        return Err(QuotationError::MalformedAntiquotation);
    }

    // Check for parenthesized: $(expr) or $(expr:category)
    if trimmed.starts_with('(') {
        if let Some(end) = find_matching_paren(trimmed) {
            let inner = &trimmed[1..end];
            // Check for type annotation
            if let Some(colon_pos) = inner.rfind(':') {
                // Make sure the colon is at top level (not inside nested parens)
                let before_colon = &inner[..colon_pos];
                let depth: i32 = before_colon.chars().fold(0, |d, c| match c {
                    '(' | '[' | '{' => d + 1,
                    ')' | ']' | '}' => d - 1,
                    _ => d,
                });
                if depth == 0 {
                    let name = before_colon.trim();
                    let category = inner[colon_pos + 1..].trim();
                    return Ok(Syntax::mk_antiquot_typed(name, category));
                }
            }
            return Ok(Syntax::mk_antiquot(inner));
        }
        return Err(QuotationError::MalformedAntiquotation);
    }

    // Simple identifier antiquotation: $name or $name:category
    let name_end = trimmed
        .find(|c: char| !c.is_alphanumeric() && c != '_' && c != ':')
        .unwrap_or(trimmed.len());
    let name_and_maybe_type = &trimmed[..name_end];

    // Check for type annotation: $name:category
    if let Some(colon_pos) = name_and_maybe_type.find(':') {
        let name = &name_and_maybe_type[..colon_pos];
        let category = &name_and_maybe_type[colon_pos + 1..];
        if name.is_empty() || category.is_empty() {
            return Err(QuotationError::MalformedAntiquotation);
        }
        return Ok(Syntax::mk_antiquot_typed(name, category));
    }

    if name_and_maybe_type.is_empty() {
        return Err(QuotationError::MalformedAntiquotation);
    }

    Ok(Syntax::mk_antiquot(name_and_maybe_type))
}

/// Parse space-separated arguments
fn parse_args(content: &str) -> Result<Vec<Syntax>, QuotationError> {
    let mut args = Vec::new();
    let mut current = String::new();
    let mut depth = 0;

    for ch in content.chars() {
        match ch {
            '(' | '[' | '{' => {
                depth += 1;
                current.push(ch);
            }
            ')' | ']' | '}' => {
                depth -= 1;
                current.push(ch);
            }
            ' ' if depth == 0 => {
                if !current.is_empty() {
                    args.push(parse_quoted_content(&current)?);
                    current.clear();
                }
            }
            _ => current.push(ch),
        }
    }

    if !current.is_empty() {
        args.push(parse_quoted_content(&current)?);
    }

    Ok(args)
}

/// Find the matching closing parenthesis
fn find_matching_paren(s: &str) -> Option<usize> {
    let mut depth = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
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
        assert_eq!(quote.syntax.as_ident(), Some("foo"));
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
        assert_eq!(names, vec!["x"]);
    }

    #[test]
    fn test_parse_numeric_literal() {
        let quote = parse_quotation("`(42)").unwrap();
        assert!(quote.syntax.is_node());
        assert_eq!(quote.syntax.kind(), Some(&SyntaxKind::num()));
    }

    #[test]
    fn test_antiquotation_from_syntax() {
        let syntax = Syntax::mk_antiquot("x");
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, "x");
        assert!(!antiquot.is_splice);
    }

    #[test]
    fn test_substitute_antiquots() {
        let mut bindings = HashMap::new();
        bindings.insert("x".to_string(), Syntax::ident("replaced"));

        let quote = SyntaxQuote::term(Syntax::mk_app(
            Syntax::ident("f"),
            vec![Syntax::mk_antiquot("x")],
        ));

        let result = quote.substitute(&bindings);
        let pretty = result.pretty();
        assert!(pretty.contains("replaced"));
    }

    #[test]
    fn test_has_antiquots() {
        let quote1 = SyntaxQuote::term(Syntax::ident("foo"));
        assert!(!quote1.has_antiquots());

        let quote2 = SyntaxQuote::term(Syntax::mk_antiquot("x"));
        assert!(quote2.has_antiquots());
    }

    #[test]
    fn test_parse_splice_antiquotation() {
        let syntax = parse_antiquotation("[items]*").unwrap();
        assert!(syntax.is_antiquot());
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert!(antiquot.is_splice);
        assert_eq!(antiquot.name, "items");
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
            vec![Syntax::ident("a"), Syntax::ident("b")],
        );
        bindings.insert("args".to_string(), splice_list);

        // Create replacement template with splice antiquotation
        let template = SyntaxQuote::term(Syntax::node(
            SyntaxKind::app_kind(),
            vec![Syntax::ident("g"), Syntax::mk_antiquot_splice("args")],
        ));

        let result = template.substitute(&bindings);

        // Result should be (g a b)
        assert!(result.is_node());
        let children = result.children();
        assert_eq!(children.len(), 3); // g, a, b
        assert_eq!(children[0].as_ident(), Some("g"));
        assert_eq!(children[1].as_ident(), Some("a"));
        assert_eq!(children[2].as_ident(), Some("b"));
    }

    #[test]
    fn test_substitute_empty_splice() {
        // Test splice with empty list
        // Pattern: `(f $[args]*)` with args = []
        // Result should be (f)
        let mut bindings = HashMap::new();

        // Create an empty splice_list
        let splice_list = Syntax::node(SyntaxKind::app("splice_list"), vec![]);
        bindings.insert("args".to_string(), splice_list);

        // Create replacement template
        let template = SyntaxQuote::term(Syntax::node(
            SyntaxKind::app_kind(),
            vec![Syntax::ident("f"), Syntax::mk_antiquot_splice("args")],
        ));

        let result = template.substitute(&bindings);

        // Result should be (f)
        assert!(result.is_node());
        let children = result.children();
        assert_eq!(children.len(), 1); // just f
        assert_eq!(children[0].as_ident(), Some("f"));
    }

    #[test]
    fn test_parse_typed_antiquotation_simple() {
        // $x:term
        let syntax = parse_antiquotation("x:term").unwrap();
        assert!(syntax.is_antiquot());
        assert!(syntax.is_antiquot_typed());
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, "x");
        assert!(!antiquot.is_splice);
        assert_eq!(antiquot.category, Some("term".to_string()));
    }

    #[test]
    fn test_parse_typed_antiquotation_tactic() {
        // $t:tactic
        let syntax = parse_antiquotation("t:tactic").unwrap();
        assert!(syntax.is_antiquot_typed());
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, "t");
        assert_eq!(antiquot.category, Some("tactic".to_string()));
    }

    #[test]
    fn test_parse_typed_splice_antiquotation() {
        // $[args:term]*
        let syntax = parse_antiquotation("[args:term]*").unwrap();
        assert!(syntax.is_antiquot());
        assert!(syntax.is_antiquot_splice());
        assert!(syntax.is_antiquot_typed());
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, "args");
        assert!(antiquot.is_splice);
        assert_eq!(antiquot.category, Some("term".to_string()));
    }

    #[test]
    fn test_parse_parenthesized_typed_antiquotation() {
        // $(expr:term)
        let syntax = parse_antiquotation("(foo:term)").unwrap();
        assert!(syntax.is_antiquot_typed());
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, "foo");
        assert_eq!(antiquot.category, Some("term".to_string()));
    }

    #[test]
    fn test_antiquotation_typed_constructor() {
        let antiquot = Antiquotation::typed("x", "term");
        assert_eq!(antiquot.name, "x");
        assert!(!antiquot.is_splice);
        assert!(antiquot.is_typed());
        assert_eq!(antiquot.category, Some("term".to_string()));
    }

    #[test]
    fn test_antiquotation_typed_splice_constructor() {
        let antiquot = Antiquotation::typed_splice("args", "command");
        assert_eq!(antiquot.name, "args");
        assert!(antiquot.is_splice);
        assert!(antiquot.is_typed());
        assert_eq!(antiquot.category, Some("command".to_string()));
    }

    #[test]
    fn test_mk_antiquot_typed() {
        let syntax = Syntax::mk_antiquot_typed("x", "term");
        assert!(syntax.is_antiquot());
        assert!(syntax.is_antiquot_typed());
        let children = syntax.children();
        assert_eq!(children.len(), 2);
        assert_eq!(children[0].as_ident(), Some("x"));
        assert_eq!(children[1].as_ident(), Some("term"));
    }

    #[test]
    fn test_mk_antiquot_splice_typed() {
        let syntax = Syntax::mk_antiquot_splice_typed("items", "tactic");
        assert!(syntax.is_antiquot());
        assert!(syntax.is_antiquot_splice());
        assert!(syntax.is_antiquot_typed());
        let children = syntax.children();
        assert_eq!(children.len(), 2);
        assert_eq!(children[0].as_ident(), Some("items"));
        assert_eq!(children[1].as_ident(), Some("tactic"));
    }

    #[test]
    fn test_antiquotation_from_typed_syntax() {
        let syntax = Syntax::mk_antiquot_typed("expr", "term");
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, "expr");
        assert!(!antiquot.is_splice);
        assert_eq!(antiquot.category, Some("term".to_string()));
    }

    #[test]
    fn test_antiquotation_from_typed_splice_syntax() {
        let syntax = Syntax::mk_antiquot_splice_typed("stmts", "command");
        let antiquot = Antiquotation::from_syntax(&syntax).unwrap();
        assert_eq!(antiquot.name, "stmts");
        assert!(antiquot.is_splice);
        assert_eq!(antiquot.category, Some("command".to_string()));
    }

    #[test]
    fn test_untyped_antiquotation_has_no_category() {
        let syntax = Syntax::mk_antiquot("x");
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
        let map: HashMap<String, Syntax> = bindings
            .iter()
            .map(|(k, v)| ((*k).to_string(), v.clone()))
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
            Syntax::ident("a"),
            None,
            Syntax::mk_num(1),
            Syntax::mk_app(
                Syntax::ident("HAdd.hAdd"),
                vec![Syntax::mk_antiquot("x"), Syntax::ident("a")],
            ),
        );
        let result = expand_template(template, &[("x", Syntax::ident("a"))]);

        let binder = result.child(0).and_then(Syntax::as_ident).unwrap();
        assert_ne!(binder, "a", "template binder must be renamed");
        assert!(
            binder.starts_with('a'),
            "renamed binder keeps its base name"
        );

        let sum = result.child(2).expect("let body");
        assert_eq!(
            sum.child(1).and_then(Syntax::as_ident),
            Some("a"),
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
            Syntax::ident("Nat.succ"),
            vec![Syntax::mk_antiquot("x"), Syntax::ident("HAdd.hAdd")],
        );
        let result = expand_template(template, &[("x", Syntax::ident("n"))]);
        assert_eq!(result.child(0).and_then(Syntax::as_ident), Some("Nat.succ"));
        assert_eq!(result.child(1).and_then(Syntax::as_ident), Some("n"));
        assert_eq!(
            result.child(2).and_then(Syntax::as_ident),
            Some("HAdd.hAdd"),
            "a global constant in the template must resolve normally"
        );
    }

    #[test]
    fn test_template_let_value_is_outside_binder_scope() {
        // In `let a := a; …` the right-hand `a` is the OUTER `a`, so it must not
        // be renamed to the binder being introduced.
        let template = Syntax::mk_let(
            Syntax::ident("a"),
            None,
            Syntax::ident("a"),
            Syntax::ident("a"),
        );
        let result = expand_template(template, &[]);
        let binder = result.child(0).and_then(Syntax::as_ident).unwrap();
        assert_eq!(
            result.child(1).and_then(Syntax::as_ident),
            Some("a"),
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
            vec![Syntax::ident("y")],
            Syntax::mk_app(
                Syntax::ident("f"),
                vec![Syntax::ident("y"), Syntax::mk_antiquot("x")],
            ),
        );
        let result = expand_template(template, &[("x", Syntax::ident("y"))]);
        let binder = result.child(0).and_then(Syntax::as_ident).unwrap();
        assert_ne!(binder, "y", "lambda binder must be renamed");
        let body = result.child(1).expect("lambda body");
        assert_eq!(body.child(1).and_then(Syntax::as_ident), Some(binder));
        assert_eq!(
            body.child(2).and_then(Syntax::as_ident),
            Some("y"),
            "the spliced `y` keeps referring to the caller's `y`"
        );
    }

    #[test]
    fn test_spliced_binder_name_not_renamed() {
        // `` `(let $n := 1; $n) `` — the binder NAME comes from the call site, so
        // there is nothing template-introduced to protect and it must pass
        // through unchanged (this is how `do`-notation desugaring works).
        let template = Syntax::mk_let(
            Syntax::mk_antiquot("n"),
            None,
            Syntax::mk_num(1),
            Syntax::mk_antiquot("n"),
        );
        let result = expand_template(template, &[("n", Syntax::ident("userVar"))]);
        assert_eq!(result.child(0).and_then(Syntax::as_ident), Some("userVar"));
        assert_eq!(result.child(2).and_then(Syntax::as_ident), Some("userVar"));
    }

    #[test]
    fn test_wildcard_binder_not_renamed() {
        // `fun _ => …` has no references; renaming `_` would only obscure the
        // output (and several built-in desugarings rely on the literal `_`).
        let template = Syntax::mk_lambda(vec![Syntax::ident("_")], Syntax::mk_antiquot("e"));
        let result = expand_template(template, &[("e", Syntax::ident("body"))]);
        assert_eq!(result.child(0).and_then(Syntax::as_ident), Some("_"));
        assert_eq!(result.child(1).and_then(Syntax::as_ident), Some("body"));
    }

    #[test]
    fn test_template_binder_distinct_per_expansion() {
        // Two expansions of the same template must not share a renamed binder,
        // so an outer expansion's binder cannot be captured by an inner one.
        let template = || {
            Syntax::mk_let(
                Syntax::ident("a"),
                None,
                Syntax::mk_num(1),
                Syntax::ident("a"),
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
            Syntax::ident("f"),
            vec![Syntax::mk_antiquot("x"), Syntax::ident("g")],
        );
        let quote = SyntaxQuote::term(template.clone());
        let mut bindings = HashMap::new();
        bindings.insert("x".to_string(), Syntax::ident("arg"));
        let mut state = HygieneState::new();
        let _scope = state.push_scope();
        assert_eq!(
            quote.substitute_hygienic(&bindings, &mut state).pretty(),
            quote.substitute(&bindings).pretty(),
        );
    }
}
