// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural source identifiers and their independent lexical information.
//!
//! A token containing `«A.B»` contributes ONE string component. A token
//! containing `«7»` also contributes a string component, never `Name::Num`.
//! Display text is diagnostic only; identity is always [`SurfaceName::name`].

use clean_kernel::name::{Name, NameInner};
use std::fmt;
use std::hash::{Hash, Hasher};

/// How one structural component entered syntax. This does not change identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NameComponentSyntax {
    /// An identifier token without guillemet-escaped text.
    Plain,
    /// An identifier token containing guillemet-escaped text.
    Escaped,
    /// An explicitly generated typed component, not a source token.
    Generated,
}

/// A malformed typed syntax payload. No display-string recovery is attempted.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum SurfaceNameError {
    #[error("name has {components} components but {syntax} lexical entries")]
    ComponentCount { components: usize, syntax: usize },
    #[error("numeric name component {index} cannot originate from an identifier token")]
    NumericSourceComponent { index: usize },
}

/// A parsed or explicitly generated identifier.
///
/// Equality and hashing compare structural identity. Use [`Self::same_syntax`]
/// when lexical equality matters (for example, a macro syntax round trip).
/// There deliberately is no `Deref<str>`, `Borrow<str>`, or implicit text parser.
#[derive(Debug, Clone)]
pub struct SurfaceName {
    name: Name,
    syntax: Vec<NameComponentSyntax>,
    relative_constructor: bool,
    /// A compiler-authored reference to a GLOBAL constant (see
    /// [`Self::global_path`]). Not part of identity.
    global_reference: bool,
    /// Hygiene marks (see [`NameMarks`]). Not part of identity.
    marks: NameMarks,
}

/// Where a user notation or macro template was declared, carried by each
/// identifier the template references FREELY (not bound inside the template).
///
/// Lean 4 elaborates a notation's expansion from a syntax quotation: every
/// template identifier carries the expansion's macro scope, so no binder at
/// the USE site can capture it, and it resolves against what it named where
/// the template was DECLARED (`quoteSyntax` pre-resolves it: the global
/// constants of that spelling under the declaring namespace, and a section
/// variable of that spelling in scope there — `Lean/Elab/Quotation.lean`,
/// `Lean/Elab/Term.lean` `resolveName`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TemplateOrigin {
    /// The namespace the template was declared in.
    pub namespace: Name,
    /// Whether a section variable of this spelling was in scope at the
    /// declaration: the reference then denotes that section variable.
    pub section_variable: bool,
    /// The declaring command in the file being elaborated, when known. The
    /// elaborator records, at that command, what each free reference of the
    /// template RESOLVES to there (Lean's quotation pre-resolution, with the
    /// `open`s and the environment of the declaration), and every use of the
    /// template reads that record. `None` for a template seeded from another
    /// file, whose declaration this file never elaborates.
    pub site: Option<TemplateSiteId>,
}

/// The declaring command of a notation template: the span of the
/// `SurfaceDecl::Notation` it came from (see [`TemplateOrigin::site`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TemplateSiteId {
    /// Start of the declaration's span.
    pub start: usize,
    /// End of the declaration's span.
    pub end: usize,
}

impl TemplateSiteId {
    /// The site of the declaration spanning `span`.
    #[must_use]
    pub fn of_span(span: super::Span) -> Self {
        Self {
            start: span.start,
            end: span.end,
        }
    }
}

/// Non-identity hygiene and binder-origin marks of a [`SurfaceName`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct NameMarks {
    /// A template's free reference ([`SurfaceName::with_template_origin`]).
    template: Option<std::sync::Arc<TemplateOrigin>>,
    /// The binder name of a section `variable`
    /// ([`SurfaceName::as_section_variable`]).
    section_variable: bool,
    /// This binder came from a declaration header, including a local
    /// function header lowered to a lambda. It still needs the header's
    /// instance-annotation check; an explicit `fun` binder does not.
    header_binder: bool,
    /// A reference spelled as a Lean 4.8.0 keyword
    /// ([`SurfaceName::into_lean_keyword`]).
    lean_keyword: bool,
    /// The binding scope of a template PATTERN variable and of every
    /// reference the template makes to it ([`SurfaceName::with_template_scope`]).
    template_scope: Option<TemplateScope>,
}

/// The macro scope of a pattern variable written in a notation template
/// (`match e with | n => … n …`), carried by the pattern variable and by
/// every reference the template makes to it.
///
/// Whether such a name is a BINDER or a CONSTRUCTOR is decided by name
/// resolution where the template was declared (Lean 4.8.0
/// `CollectPatternVars.processId` resolves the macro-scoped identifier: a
/// constructor stays a constructor pattern, anything else is a variable), so
/// the walk cannot rename it the way it renames a `fun` binder. Instead the
/// identity stays as written and this scope does what Lean's macro scope
/// does: a name carrying it binds, and is bound by, only a local carrying the
/// SAME scope, and a name without it never sees such a local. The scope is
/// fresh for every expansion of the template.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TemplateScope(pub u64);

impl NameMarks {
    fn or(&self, other: &Self) -> Self {
        Self {
            template: self.template.clone().or_else(|| other.template.clone()),
            section_variable: self.section_variable || other.section_variable,
            header_binder: self.header_binder || other.header_binder,
            lean_keyword: self.lean_keyword || other.lean_keyword,
            template_scope: self.template_scope.or(other.template_scope),
        }
    }
}

impl SurfaceName {
    /// One actual identifier token; dots and decimal digits remain text.
    #[must_use]
    pub fn component(text: impl AsRef<str>, escaped: bool) -> Self {
        Self {
            name: Name::anon().str(text),
            syntax: vec![if escaped {
                NameComponentSyntax::Escaped
            } else {
                NameComponentSyntax::Plain
            }],
            relative_constructor: false,
            global_reference: false,
            marks: NameMarks::default(),
        }
    }

    /// An explicitly generated canonical path. Every segment is a string.
    ///
    /// This is for fixed compiler-authored paths such as `Nat.succ`, NOT for
    /// reparsing user spelling or a `Name` display. Numeric components require
    /// [`Self::from_name`]. Empty text denotes the anonymous generated name.
    #[must_use]
    pub fn generated_path(path: &str) -> Self {
        if path.is_empty() {
            return Self::from_name(Name::anon());
        }
        Self::from_name(
            path.split('.')
                .fold(Name::anon(), |name, part| name.str(part)),
        )
    }

    /// A compiler-authored reference to the GLOBAL constant `path`, as the
    /// head of a notation's desugaring (`a && b` is `and a b`, `a = b` is
    /// `Eq a b`, `A × B` is `Prod A B`, …).
    ///
    /// Identity is that of [`Self::generated_path`], so every recognizer of
    /// the desugared shape still matches, but name resolution never binds
    /// it to a local ([`Self::is_global_reference`]) and resolves it at the
    /// root before any namespace-relative candidate. The reference is the
    /// notation's, not the user's: Lean 4 elaborates these heads from
    /// syntax quotations whose identifiers were pre-resolved where the
    /// notation was declared, so a binder or namespace member of the same
    /// spelling at the use site cannot capture them. Resolving them like a
    /// source identifier made `def k (and : Bool → Bool → Bool) (a b : Bool)
    /// := a && b` compute `and` with the parameter, and `k (fun _ _ =>
    /// true) false false = true` was accepted by `rfl` (measured 2026-09-25;
    /// Lean 4.8.0: `false`).
    #[must_use]
    pub fn global_path(path: &str) -> Self {
        let mut name = Self::generated_path(path);
        name.global_reference = true;
        name
    }

    /// A compiler-authored reference to the already-RESOLVED global constant
    /// `name` (see [`Self::global_path`]): never a local, resolved at the
    /// root, so it names exactly `name`.
    #[must_use]
    pub fn global_constant(name: Name) -> Self {
        let mut name = Self::from_name(name);
        name.global_reference = true;
        name
    }

    /// Whether this is a [`Self::global_path`] reference (or a component or
    /// qualification of one): never a local, whatever binders are in scope.
    #[must_use]
    pub fn is_global_reference(&self) -> bool {
        self.global_reference
    }

    /// This name as a user template's FREE reference declared under
    /// `origin` ([`TemplateOrigin`]): name resolution binds it to no local
    /// except, when `origin.section_variable`, the section variable of its
    /// spelling, and walks namespaces from `origin.namespace`.
    #[must_use]
    pub fn with_template_origin(mut self, origin: std::sync::Arc<TemplateOrigin>) -> Self {
        self.marks.template = Some(origin);
        self
    }

    /// The declaration site of a template's free reference, if this is one.
    #[must_use]
    pub fn template_origin(&self) -> Option<&TemplateOrigin> {
        self.marks.template.as_deref()
    }

    /// The shared declaration site of a template's free reference, if this is
    /// one (see [`Self::template_origin`]).
    #[must_use]
    pub fn template_origin_arc(&self) -> Option<&std::sync::Arc<TemplateOrigin>> {
        self.marks.template.as_ref()
    }

    /// This name as a template PATTERN variable, or a template reference to
    /// one, in the binding scope `scope` ([`TemplateScope`]). The caller also
    /// gives it its [`TemplateOrigin`]: when no local of the same scope binds
    /// it, it is the constructor its spelling named where the template was
    /// declared.
    #[must_use]
    pub fn with_template_scope(mut self, scope: TemplateScope) -> Self {
        self.marks.template_scope = Some(scope);
        self
    }

    /// The binding scope of a template pattern variable (or of a template
    /// reference to one), if this is one.
    #[must_use]
    pub fn template_scope(&self) -> Option<TemplateScope> {
        self.marks.template_scope
    }

    /// This name without its [`TemplateScope`]: the template reference its
    /// spelling makes where the template was declared.
    #[must_use]
    pub fn without_template_scope(mut self) -> Self {
        self.marks.template_scope = None;
        self
    }

    /// This name with the hygiene marks of a notation or macro template
    /// ([`TemplateOrigin`], [`TemplateScope`]) removed: Lean's
    /// `Name.eraseMacroScopes`, the spelling a NAME position (a structure
    /// field, a named argument) reads from an identifier.
    #[must_use]
    pub(crate) fn without_template_marks(mut self) -> Self {
        self.marks.template = None;
        self.marks.template_scope = None;
        self
    }

    /// This name as the binder of a section `variable`.
    #[must_use]
    pub fn as_section_variable(mut self) -> Self {
        self.marks.section_variable = true;
        self
    }

    /// This name as a term-position reference whose token is a Lean 4.8.0
    /// keyword (`crate::lexer::Token::lean_keyword`). Lean reads the token as
    /// the keyword, so the reference is SYNTAX: it denotes no local and no
    /// constant, whatever the file binds or declares under that spelling
    /// (only an escaped `«nomatch»` can), and only Clean's own recognizer of
    /// that keyword gives it a meaning (`nomatch e`).
    #[must_use]
    pub(crate) fn into_lean_keyword(mut self) -> Self {
        self.marks.lean_keyword = true;
        self
    }

    /// Whether this is a reference spelled as a Lean 4.8.0 keyword
    /// ([`Self::into_lean_keyword`]).
    #[must_use]
    pub fn is_lean_keyword(&self) -> bool {
        self.marks.lean_keyword
    }

    /// Whether this is the binder name of a section `variable`.
    #[must_use]
    pub fn is_section_variable(&self) -> bool {
        self.marks.section_variable
    }

    /// Record whether this binder originated in a declaration header.
    ///
    /// Local function headers lower to lambdas, but Lean checks their
    /// bracketed annotations before elaborating the body. This provenance
    /// survives that lowering without changing identifier identity, spelling
    /// or resolution. Hygiene copies the original binder's provenance onto
    /// its replacement name, independently of the name's source.
    #[must_use]
    pub fn with_header_binder_origin(mut self, is_header: bool) -> Self {
        self.marks.header_binder = is_header;
        self
    }

    /// Whether this binder originated in a declaration header.
    #[must_use]
    pub fn is_header_binder(&self) -> bool {
        self.marks.header_binder
    }

    /// A compiler-introduced LOCAL name that no source identifier can spell.
    ///
    /// Its identity ends in a numeric component (`base.index`), which an
    /// identifier token never produces ([`Self::from_syntax_parts`] refuses one), so
    /// no user reference can resolve to a binder under this name and no user
    /// binder can shadow a reference to it. Every desugaring that wraps
    /// user-written code in a binder of its own must use one: a string-only
    /// "internal" name such as `_x` or `_tpl` is an ordinary identifier, and
    /// `def _tpl := (7, 7)` then `let (x, y) := (1, 2); _tpl.1 + x` read the
    /// desugaring's temporary instead of the global (measured 2026-09-25:
    /// `= 2` accepted by `rfl`; Lean 4.8.0: `8`).
    #[must_use]
    pub fn unspellable(base: &str, index: u64) -> Self {
        Self::from_name(Name::anon().str(base).num(index))
    }

    /// The scrutinee binder of a pattern-matching lambda (`fun | … => …`) and
    /// of an equation-form definition (`def f : A → B | … => …`), both of
    /// which the parser desugars to `fun <this> => match <this> with …`.
    /// Recognizers of that desugared shape compare against this name.
    #[must_use]
    pub fn pattern_lambda_binder() -> Self {
        Self::unspellable("_x", 0)
    }

    /// Preserve an already typed, explicitly generated identity.
    #[must_use]
    pub fn from_name(name: Name) -> Self {
        let count = components(&name).len();
        Self {
            name,
            syntax: vec![NameComponentSyntax::Generated; count],
            relative_constructor: false,
            global_reference: false,
            marks: NameMarks::default(),
        }
    }

    /// Exact macro/AST transport. Reject malformed metadata rather than infer it.
    pub(crate) fn from_parts(
        name: Name,
        syntax: Vec<NameComponentSyntax>,
    ) -> Result<Self, SurfaceNameError> {
        let parts = components(&name);
        if parts.len() != syntax.len() {
            return Err(SurfaceNameError::ComponentCount {
                components: parts.len(),
                syntax: syntax.len(),
            });
        }
        for (index, (part, origin)) in parts.iter().zip(&syntax).enumerate() {
            if matches!(part, NameInner::Num(..)) && *origin != NameComponentSyntax::Generated {
                return Err(SurfaceNameError::NumericSourceComponent { index });
            }
        }
        Ok(Self {
            name,
            syntax,
            relative_constructor: false,
            global_reference: false,
            marks: NameMarks::default(),
        })
    }

    /// Exact lexical transport, including a leading-dot constructor selector.
    pub fn from_syntax_parts(
        name: Name,
        syntax: Vec<NameComponentSyntax>,
        relative_constructor: bool,
    ) -> Result<Self, SurfaceNameError> {
        let mut result = Self::from_parts(name, syntax)?;
        result.relative_constructor = relative_constructor;
        Ok(result)
    }

    /// Mark actual leading-dot syntax; quoted text beginning with a dot is not this syntax.
    #[must_use]
    pub fn with_relative_constructor(mut self) -> Self {
        self.relative_constructor = true;
        self
    }

    #[must_use]
    pub fn is_relative_constructor(&self) -> bool {
        self.relative_constructor
    }

    #[must_use]
    pub fn name(&self) -> &Name {
        &self.name
    }

    #[must_use]
    pub fn into_name(self) -> Name {
        self.name
    }

    #[must_use]
    pub fn component_syntax(&self) -> &[NameComponentSyntax] {
        &self.syntax
    }

    /// UI/source spelling only. Numeric identities have no identifier-token spelling.
    /// Callers must retain the typed name even when rendering is unavailable.
    #[must_use]
    pub fn source_spelling(&self) -> Option<String> {
        let mut out = if self.relative_constructor {
            ".".to_owned()
        } else {
            String::new()
        };
        for (index, (part, syntax)) in components(&self.name).iter().zip(&self.syntax).enumerate() {
            let NameInner::Str(_, text) = part else {
                return None;
            };
            if text.contains(['«', '»']) {
                return None;
            }
            if index != 0 {
                out.push('.');
            }
            let tokens = crate::lexer::Lexer::tokenize(text);
            // A component that lexes as one of Clean's special tokens which
            // core Lean treats as an ordinary identifier (`rfl`, `rec`, …) is
            // plain too: Lean prints `Eq.rec` and `rfl`, never `Eq.«rec»`.
            let plain_identifier = matches!(tokens.as_slice(), [token, eof]
                if (matches!(&token.kind, crate::lexer::TokenKind::Ident(value) if value.as_str() == text.as_ref())
                    || (token.kind.is_core_lean_identifier_word()
                        && token.kind.as_keyword_str() == Some(text.as_ref())))
                    && !token.ident_escaped && token.span.start == 0 && token.span.end == text.len()
                    && matches!(eof.kind, crate::lexer::TokenKind::Eof));
            let generated_root_component = index == 0
                && self.syntax.len() > 1
                && *syntax == NameComponentSyntax::Generated
                && text.as_ref() == "_root_";
            let quote = *syntax == NameComponentSyntax::Escaped
                || !plain_identifier
                || generated_root_component;
            if quote {
                out.push('«');
            }
            out.push_str(text);
            if quote {
                out.push('»');
            }
        }
        Some(out)
    }

    #[must_use]
    pub fn is_anonymous(&self) -> bool {
        self.name.is_anon()
    }

    /// Structural parent, not a dot-split of a rendered string.
    #[must_use]
    pub fn parent(&self) -> Self {
        let name = match self.name.inner() {
            NameInner::Anon => Name::anon(),
            NameInner::Str(parent, _) | NameInner::Num(parent, _) => parent.as_ref().clone(),
        };
        Self {
            name,
            syntax: self.syntax[..self.syntax.len().saturating_sub(1)].to_vec(),
            relative_constructor: self.relative_constructor,
            global_reference: self.global_reference,
            marks: self.marks.clone(),
        }
    }

    /// The final typed component with its original lexical annotation.
    #[must_use]
    pub fn last_component(&self) -> Self {
        let name = match self.name.inner() {
            NameInner::Anon => return Self::default(),
            NameInner::Str(_, text) => Name::anon().str(text.as_ref()),
            NameInner::Num(_, number) => Name::anon().num(*number),
        };
        Self {
            name,
            syntax: self.syntax.last().copied().into_iter().collect(),
            relative_constructor: false,
            global_reference: self.global_reference,
            marks: self.marks.clone(),
        }
    }

    #[must_use]
    pub fn has_prefix(&self, prefix: &Self) -> bool {
        let mut current = self.name.clone();
        loop {
            if &current == prefix.name() {
                return true;
            }
            current = match current.inner() {
                NameInner::Anon => return false,
                NameInner::Str(parent, _) | NameInner::Num(parent, _) => parent.as_ref().clone(),
            };
        }
    }

    #[must_use]
    pub fn same_syntax(&self, other: &Self) -> bool {
        self.name == other.name
            && self.syntax == other.syntax
            && self.relative_constructor == other.relative_constructor
    }

    /// Exact lexical and hygiene agreement for source-origin transport.
    ///
    /// Unlike structural name equality, this also checks source spelling,
    /// global-reference policy and all template/section/header marks. It does
    /// not change name resolution or the existing equality/hash contracts.
    #[must_use]
    pub(crate) fn same_origin_metadata_for_capture(&self, other: &Self) -> bool {
        self.same_syntax(other)
            && self.global_reference == other.global_reference
            && self.marks == other.marks
    }

    /// Structural qualification, preserving every suffix constructor.
    #[must_use]
    pub fn append(&self, suffix: &Self) -> Self {
        let mut name = self.name.clone();
        for part in components(&suffix.name) {
            name = match part {
                NameInner::Str(_, text) => name.str(text.as_ref()),
                NameInner::Num(_, number) => name.num(*number),
                NameInner::Anon => name,
            };
        }
        let mut syntax = self.syntax.clone();
        syntax.extend_from_slice(&suffix.syntax);
        Self {
            name,
            syntax,
            relative_constructor: self.relative_constructor,
            global_reference: self.global_reference || suffix.global_reference,
            marks: self.marks.or(&suffix.marks),
        }
    }

    /// Qualify a source name, honoring only an actual leading `_root_.` selector.
    /// Quoted `«_root_»` is an ordinary component, as is a relative constructor.
    #[must_use]
    pub fn qualify_under(&self, namespace: &Self) -> Self {
        let parts = components(&self.name);
        let root_qualified = !self.relative_constructor
            && parts.len() > 1
            && self.syntax.first() == Some(&NameComponentSyntax::Plain)
            && matches!(parts.first(), Some(NameInner::Str(_, text)) if text.as_ref() == "_root_");
        if !root_qualified {
            return namespace.append(self);
        }
        let mut name = Name::anon();
        for part in parts.into_iter().skip(1) {
            name = match part {
                NameInner::Str(_, text) => name.str(text.as_ref()),
                NameInner::Num(_, number) => name.num(*number),
                NameInner::Anon => name,
            };
        }
        Self {
            name,
            syntax: self.syntax[1..].to_vec(),
            relative_constructor: false,
            global_reference: self.global_reference,
            marks: self.marks.clone(),
        }
    }

    /// Split off one exact leading component, preserving lexical origins.
    #[must_use]
    pub fn split_first(&self) -> Option<(Self, Self)> {
        let parts = components(&self.name);
        let first = parts.first()?;
        let first_name = match first {
            NameInner::Str(_, text) => Name::anon().str(text.as_ref()),
            NameInner::Num(_, number) => Name::anon().num(*number),
            NameInner::Anon => return None,
        };
        let mut rest = Name::anon();
        for part in parts.into_iter().skip(1) {
            rest = match part {
                NameInner::Str(_, text) => rest.str(text.as_ref()),
                NameInner::Num(_, number) => rest.num(*number),
                NameInner::Anon => rest,
            };
        }
        Some((
            Self {
                name: first_name,
                syntax: self.syntax[..1].to_vec(),
                relative_constructor: self.relative_constructor,
                global_reference: self.global_reference,
                marks: self.marks.clone(),
            },
            Self {
                name: rest,
                syntax: self.syntax[1..].to_vec(),
                relative_constructor: false,
                global_reference: self.global_reference,
                marks: self.marks.clone(),
            },
        ))
    }

    /// Structural suffix membership; a dot inside one Str is never a separator.
    #[must_use]
    pub fn has_suffix(&self, suffix: &Self) -> bool {
        let mut current = &self.name;
        let mut remaining = &suffix.name;
        loop {
            match (current.inner(), remaining.inner()) {
                (_, NameInner::Anon) => return true,
                (NameInner::Str(left, x), NameInner::Str(right, y)) if x == y => {
                    current = left;
                    remaining = right;
                }
                (NameInner::Num(left, x), NameInner::Num(right, y)) if x == y => {
                    current = left;
                    remaining = right;
                }
                _ => return false,
            }
        }
    }

    /// A local-name component, without projecting a qualified name to text.
    #[must_use]
    pub fn component_text(&self) -> Option<&str> {
        match self.name.inner() {
            NameInner::Str(prefix, text) if prefix.is_anon() => Some(text.as_ref()),
            _ => None,
        }
    }

    /// Contextual keyword recognition must not reinterpret escaped identifiers.
    #[must_use]
    pub fn is_unescaped_component(&self, text: &str) -> bool {
        self.component_text() == Some(text)
            && self.syntax.first() != Some(&NameComponentSyntax::Escaped)
            && !self.relative_constructor
    }
}

fn components(name: &Name) -> Vec<&NameInner> {
    let mut out = Vec::new();
    let mut current = name;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            inner @ (NameInner::Str(prefix, _) | NameInner::Num(prefix, _)) => {
                out.push(inner);
                current = prefix;
            }
        }
    }
    out.reverse();
    out
}

impl PartialEq for SurfaceName {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}
impl Eq for SurfaceName {}
impl Default for SurfaceName {
    fn default() -> Self {
        Self::from_name(Name::anon())
    }
}
impl PartialOrd for SurfaceName {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SurfaceName {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name.cmp(&other.name)
    }
}
impl Hash for SurfaceName {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}
impl fmt::Display for SurfaceName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.name.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structural_suffix_checks_do_not_flatten_components_or_numeric_tags() {
        let full = SurfaceName::from_name(Name::anon().str("Outer").str("A.B").num(7));
        assert!(full.has_suffix(&SurfaceName::from_name(Name::anon().str("A.B").num(7))));
        assert!(full.has_suffix(&SurfaceName::default()));
        assert!(!full.has_suffix(&SurfaceName::from_name(
            Name::anon().str("A").str("B").num(7)
        )));
        assert!(!full.has_suffix(&SurfaceName::from_name(Name::anon().str("A.B").str("7"))));
        assert!(!full.has_suffix(&SurfaceName::generated_path("Extra").append(&full)));
    }

    #[test]
    fn qualification_distinguishes_source_root_selector_from_literal_and_generated_roots() {
        let namespace = SurfaceName::component("Outer", false);
        let suffix = SurfaceName::component("A.B", true);
        let marker = SurfaceName::component("_root_", false).append(&suffix);
        let escaped = SurfaceName::component("_root_", true).append(&suffix);
        let generated = SurfaceName::from_name(escaped.name().clone());
        assert_eq!(marker.qualify_under(&namespace).name(), suffix.name());
        assert_eq!(
            escaped.qualify_under(&namespace).name(),
            &namespace.name().clone().str("_root_").str("A.B")
        );
        assert_eq!(
            generated.qualify_under(&namespace).name(),
            escaped.qualify_under(&namespace).name()
        );
        let relative = marker.clone().with_relative_constructor();
        assert_eq!(
            relative.qualify_under(&namespace).name(),
            escaped.qualify_under(&namespace).name()
        );
    }

    #[test]
    fn source_spelling_leaves_lean_identifier_words_unquoted() {
        // Measured against pinned lean v4.30.0-rc2: these are identifiers in
        // core Lean even though Clean lexes them as dedicated tokens.
        for (path, expected) in [
            (vec!["Eq", "rec"], "Eq.rec"),
            (vec!["rfl"], "rfl"),
            (vec!["Foo", "lemma"], "Foo.lemma"),
            (vec!["module"], "module"),
        ] {
            let name = path.iter().fold(Name::anon(), |acc, part| acc.str(*part));
            let spelling = SurfaceName::from_name(name)
                .source_spelling()
                .expect("string identity has a spelling");
            assert_eq!(spelling, expected);
        }
        // A genuine Lean keyword is still quoted.
        let keyword = SurfaceName::from_name(Name::anon().str("fun"));
        assert_eq!(keyword.source_spelling().as_deref(), Some("«fun»"));
    }

    #[test]
    fn source_spelling_is_lexical_and_quotes_generated_contextual_components() {
        for text in ["x+y", "Type", "A.B", "7", "λ星"] {
            let name = SurfaceName::from_name(Name::anon().str(text));
            let spelling = name
                .source_spelling()
                .expect("string identity has a spelling");
            assert_eq!(
                crate::parse_name(&spelling)
                    .expect("rendered identifier")
                    .name(),
                name.name()
            );
        }
        let generated = SurfaceName::from_name(Name::anon().str("_root_").str("foo"));
        assert_eq!(generated.source_spelling().as_deref(), Some("«_root_».foo"));
        let marker =
            SurfaceName::component("_root_", false).append(&SurfaceName::component("foo", false));
        assert_eq!(marker.source_spelling().as_deref(), Some("_root_.foo"));
        assert!(SurfaceName::from_name(Name::anon().num(7))
            .source_spelling()
            .is_none());
    }

    #[test]
    fn quoted_dot_and_numeral_are_distinct_structural_components() {
        let quoted = SurfaceName::component("A.B", true);
        let nested = SurfaceName::component("A", false).append(&SurfaceName::component("B", false));
        assert_ne!(quoted, nested);
        assert_ne!(
            SurfaceName::component("7", true).name(),
            &Name::anon().num(7)
        );
        assert_eq!(
            SurfaceName::component("λ星", true).name(),
            &Name::anon().str("λ星")
        );
    }

    #[test]
    fn syntax_transport_preserves_escaping_without_changing_name_identity() {
        let quoted = SurfaceName::component("Type", true);
        let plain = SurfaceName::component("Type", false);
        assert_eq!(quoted, plain);
        assert!(!quoted.same_syntax(&plain));
        assert!(!quoted.is_unescaped_component("Type"));
        assert!(plain.is_unescaped_component("Type"));
        let copied =
            SurfaceName::from_parts(quoted.name().clone(), quoted.component_syntax().to_vec())
                .unwrap();
        assert!(copied.same_syntax(&quoted));
    }

    #[test]
    fn malformed_transport_and_numeric_source_claims_refuse() {
        assert!(matches!(
            SurfaceName::from_parts(Name::anon().str("x"), vec![]),
            Err(SurfaceNameError::ComponentCount { .. })
        ));
        assert!(matches!(
            SurfaceName::from_parts(Name::anon().num(7), vec![NameComponentSyntax::Escaped]),
            Err(SurfaceNameError::NumericSourceComponent { .. })
        ));
        let generated = SurfaceName::from_name(Name::anon().str("A.B").num(7));
        assert!(SurfaceName::from_parts(
            generated.name().clone(),
            generated.component_syntax().to_vec()
        )
        .unwrap()
        .same_syntax(&generated));
    }
}
