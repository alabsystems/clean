// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Surface declaration types: top-level parsed declarations.

use super::attr::Attribute;
use super::binder::{OpenPath, SurfaceBinder, TerminationHints};
use super::expr::SurfaceExpr;
use super::modifiers::{DeclModifiers, DeclScope};
use super::span::Span;
use super::syntax::{MacroArm, NotationItem, NotationKind, SyntaxPatternItem};

/// A captured Lean 4 declaration documentation comment (`/-- ... -/`).
///
/// Lean attaches a `/-- ... -/` doc comment to the declaration that
/// immediately follows it. Clean captures these as a side-table during
/// parsing (see [`crate::Parser::parse_file_with_docs`]) rather than as a
/// field on every [`SurfaceDecl`] variant, so the capture is purely
/// syntactic and has zero impact on how declarations elaborate.
///
/// `/-! ... -/` *module/section* doc comments are intentionally NOT captured
/// here — only the declaration-attaching `/-- ... -/` form is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DocComment {
    /// Source span of the entire comment, including the `/--` and `-/`
    /// delimiters.
    pub span: Span,
    /// The inner documentation text, with the `/--` opener and `-/` closer
    /// stripped and surrounding whitespace trimmed.
    pub text: String,
}

impl DocComment {
    /// Create a new doc comment from its span and already-stripped text.
    #[must_use]
    pub fn new(span: Span, text: String) -> Self {
        Self { span, text }
    }
}

/// A single file-scope `attribute` command operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttributeCommandAttr {
    /// Apply an attribute to the listed declarations.
    Add(Attribute),
    /// Remove a previously applied attribute from the listed declarations.
    Remove(String),
}

/// A surface-level declaration
#[derive(Debug, Clone)]
pub enum SurfaceDecl {
    /// Definition: `def name : ty := val`
    Def {
        span: Span,
        name: String,
        universe_params: Vec<String>,
        binders: Vec<SurfaceBinder>,
        ty: Option<Box<SurfaceExpr>>,
        val: Box<SurfaceExpr>,
        /// Attributes like `@[aesop safe apply]`
        attrs: Vec<Attribute>,
        /// Optional termination hints for recursive definitions
        termination: TerminationHints,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
        /// Local definitions from a trailing `where` clause
        where_decls: Vec<WhereLocalDef>,
    },

    /// Theorem: `theorem name : ty := proof`
    Theorem {
        span: Span,
        name: String,
        universe_params: Vec<String>,
        binders: Vec<SurfaceBinder>,
        ty: Box<SurfaceExpr>,
        proof: Box<SurfaceExpr>,
        /// Attributes like `@[aesop safe apply]`
        attrs: Vec<Attribute>,
        /// Optional termination hints for recursive theorems
        termination: TerminationHints,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
        /// Local definitions from a trailing `where` clause
        where_decls: Vec<WhereLocalDef>,
    },

    /// Axiom: `axiom name : ty`
    Axiom {
        span: Span,
        name: String,
        universe_params: Vec<String>,
        binders: Vec<SurfaceBinder>,
        ty: Box<SurfaceExpr>,
        /// Attributes like `@[aesop safe apply]`
        attrs: Vec<Attribute>,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },

    /// Opaque declaration: `opaque name : ty` or `opaque name : ty := val`
    /// Type is known but implementation is hidden from the kernel.
    /// Used for FFI bindings, performance-critical code, and abstract interfaces.
    Opaque {
        span: Span,
        name: String,
        universe_params: Vec<String>,
        binders: Vec<SurfaceBinder>,
        ty: Box<SurfaceExpr>,
        /// Optional default value
        val: Option<Box<SurfaceExpr>>,
        /// Attributes like `@[extern "c_function"]`
        attrs: Vec<Attribute>,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },

    /// Inductive type
    ///
    /// ```text
    /// inductive Option (α : Type) : Type
    /// | none : Option α
    /// | some : α → Option α
    /// deriving Repr, BEq
    /// ```
    Inductive {
        span: Span,
        name: String,
        universe_params: Vec<String>,
        binders: Vec<SurfaceBinder>,
        ty: Box<SurfaceExpr>,
        ctors: Vec<SurfaceCtor>,
        /// Deriving clauses (class names to derive)
        deriving: Vec<String>,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },

    /// Coinductive predicate (Lean 4.25+ feature, #191)
    ///
    /// Uses greatest fixpoint semantics. Syntax identical to `inductive`.
    /// ```text
    /// coinductive Stream (α : Type) : Type where
    /// | nil : Stream α
    /// | cons : α → Stream α → Stream α
    /// ```
    Coinductive {
        span: Span,
        name: String,
        universe_params: Vec<String>,
        binders: Vec<SurfaceBinder>,
        ty: Box<SurfaceExpr>,
        ctors: Vec<SurfaceCtor>,
        /// Deriving clauses (class names to derive)
        deriving: Vec<String>,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },

    /// Structure (single-constructor inductive with named fields)
    ///
    /// ```text
    /// structure Point where
    ///   x : Nat
    ///   y : Nat
    /// deriving Repr, BEq
    /// ```
    Structure {
        span: Span,
        name: String,
        universe_params: Vec<String>,
        /// Parameters of the structure (before `where`)
        binders: Vec<SurfaceBinder>,
        /// Parent structures (from `extends` clause).
        /// Each element is a type expression like `Base` or `Bar α`.
        extends: Vec<Box<SurfaceExpr>>,
        /// Optional explicit result type (defaults to Type)
        ty: Option<Box<SurfaceExpr>>,
        /// Optional explicit constructor name (`structure P where make :: …`,
        /// Lean `structCtor`). `None` means the default `mk`.
        ctor_name: Option<String>,
        /// Fields of the structure
        fields: Vec<SurfaceField>,
        /// Deriving clauses (class names to derive)
        deriving: Vec<String>,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },

    /// Type class declaration (structure marked as a class)
    ///
    /// ```text
    /// class Add (α : Type) where
    ///   add : α → α → α
    /// ```
    ///
    /// With inheritance:
    /// ```text
    /// class CommRing (α : Type) extends Ring α where
    ///   mul_comm : ∀ a b, a * b = b * a
    /// ```
    Class {
        span: Span,
        name: String,
        universe_params: Vec<String>,
        /// Parameters of the class (before `where`)
        binders: Vec<SurfaceBinder>,
        /// Parent classes (from `extends` clause)
        /// Each element is a type expression like `Ring α`
        extends: Vec<Box<SurfaceExpr>>,
        /// Optional explicit result type (defaults to Type)
        ty: Option<Box<SurfaceExpr>>,
        /// Fields/methods of the class
        fields: Vec<SurfaceField>,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },

    /// Type class instance declaration
    ///
    /// ```text
    /// instance : Add Nat where
    ///   add := Nat.add
    /// ```
    ///
    /// Or with explicit name:
    /// ```text
    /// instance instAddNat : Add Nat where
    ///   add := Nat.add
    /// ```
    Instance {
        span: Span,
        /// Optional instance name (can be auto-generated)
        name: Option<String>,
        universe_params: Vec<String>,
        /// Binders for instance parameters (e.g., `[Ord A]`)
        binders: Vec<SurfaceBinder>,
        /// The class type this instance provides (e.g., `Add Nat`)
        class_type: Box<SurfaceExpr>,
        /// Field assignments
        fields: Vec<SurfaceFieldAssign>,
        /// Optional priority attribute
        priority: Option<u32>,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },

    /// Example: `example : ty := proof` (anonymous theorem, not saved to environment)
    Example {
        span: Span,
        binders: Vec<SurfaceBinder>,
        ty: Option<Box<SurfaceExpr>>,
        val: Box<SurfaceExpr>,
    },

    /// Import: `import Lean.Data.List` (supports multiple module paths)
    Import { span: Span, paths: Vec<Vec<String>> },

    /// Namespace: `namespace Foo ... end Foo`
    Namespace {
        span: Span,
        name: String,
        decls: Vec<SurfaceDecl>,
    },

    /// Section: `section Foo ... end Foo`
    Section {
        span: Span,
        name: Option<String>,
        decls: Vec<SurfaceDecl>,
    },

    /// Universe declaration: `universe u v`
    UniverseDecl { span: Span, names: Vec<String> },

    /// Variable declaration: `variable (x : Type)`
    Variable {
        span: Span,
        binders: Vec<SurfaceBinder>,
    },

    /// Open command: `open Nat in ...` or `open Nat (add mul)` (multiple paths allowed)
    /// Also handles `open scoped X` which imports only notations/syntax from namespace X.
    Open {
        span: Span,
        paths: Vec<OpenPath>,
        /// Body expression or declarations if using `in`
        body: Option<Box<SurfaceDecl>>,
        /// Whether this is `open scoped` (imports only notations/syntax)
        scoped: bool,
    },

    /// Export command: `export Namespace (name1 name2 ...)`
    /// Makes names from other namespaces visible in the current namespace.
    Export {
        span: Span,
        /// The namespace path to export from (e.g., `["Nat", "Arithmetic"]` for `Nat.Arithmetic`)
        namespace: Vec<String>,
        /// The names to export (must have at least one)
        names: Vec<String>,
    },

    /// Standalone deriving instance command: `deriving instance Repr, BEq for MyType`
    /// Derives type class instances for types defined elsewhere.
    DerivingInstance {
        span: Span,
        /// Type classes to derive (e.g., ["Repr", "BEq"])
        classes: Vec<String>,
        /// Types to derive instances for
        types: Vec<String>,
    },

    /// #check command: `#check expr`
    Check { span: Span, expr: Box<SurfaceExpr> },

    /// #eval command: `#eval expr`
    Eval { span: Span, expr: Box<SurfaceExpr> },

    /// #print command: `#print name`
    Print { span: Span, name: String },

    /// Mutual block: `mutual ... end`
    Mutual { span: Span, decls: Vec<SurfaceDecl> },

    /// Syntax declaration: defines a new syntax pattern
    ///
    /// ```text
    /// syntax [name] [prec:num]? term "+" term : term
    /// syntax:20 term "+" term : term  -- with precedence
    /// ```
    Syntax {
        span: Span,
        /// Optional name for the syntax (e.g., `[name]` attribute)
        name: Option<String>,
        /// Optional precedence level
        precedence: Option<u32>,
        /// Optional priority for disambiguation
        priority: Option<u32>,
        /// The syntax pattern (sequence of atoms, idents, category refs)
        pattern: Vec<SyntaxPatternItem>,
        /// The syntax category this extends (e.g., "term", "command", "tactic")
        category: String,
    },

    /// Declare a new syntax category
    ///
    /// ```text
    /// declare_syntax_cat mycat
    /// ```
    DeclareSyntaxCat {
        span: Span,
        /// The name of the new category
        name: String,
    },

    /// Macro declaration: short form for simple macros
    ///
    /// ```text
    /// macro "unless" cond:term "then" body:term : term =>
    ///   `(if !$cond then $body else ())
    /// ```
    Macro {
        span: Span,
        /// Optional doc comment
        doc: Option<String>,
        /// The syntax pattern to match
        pattern: Vec<SyntaxPatternItem>,
        /// The syntax category
        category: String,
        /// The expansion template (syntax quotation)
        expansion: Box<SurfaceExpr>,
    },

    /// Macro rules: multi-arm macro with pattern matching
    ///
    /// ```text
    /// macro_rules
    /// | `($x + $y) => `(Nat.add $x $y)
    /// | `($x - $y) => `(Nat.sub $x $y)
    /// ```
    MacroRules {
        span: Span,
        /// Optional name for the macro
        name: Option<String>,
        /// Match arms: (pattern, expansion)
        arms: Vec<MacroArm>,
    },

    /// Notation declaration: defines infix/prefix/postfix notation
    ///
    /// ```text
    /// infixl:65 " + " => Add.add
    /// prefix:max "!" => Not
    /// notation "⟨" a ", " b "⟩" => Prod.mk a b
    /// ```
    Notation {
        span: Span,
        /// The notation kind (infixl, infixr, prefix, postfix, notation)
        kind: NotationKind,
        /// Optional precedence level
        precedence: Option<u32>,
        /// The notation pattern
        pattern: Vec<NotationItem>,
        /// The expansion (function to apply)
        expansion: Box<SurfaceExpr>,
        /// Command scope: `Default`, `Scoped` (`scoped notation …`), or
        /// `Local` (`local notation …`). The `scoped`/`local` modifiers were
        /// previously parsed and then silently dropped, so a `scoped notation`
        /// registered as if it were global — and when its token was later
        /// unresolved the elaborator auto-bound it as a variable rather than
        /// surfacing the unsupported feature (gap sweep B13,
        /// namespaces_scoping/p10). The elaborator now consumes this field.
        scope: DeclScope,
    },

    /// Elaborator declaration: `elab <pattern> : <category> => <body>`
    ///
    /// ```text
    /// elab "myCustomSyntax" e:term : term => do
    ///   let e ← elabTerm e none
    ///   return mkApp (mkConst ``myFn) e
    /// ```
    Elab {
        span: Span,
        /// The syntax pattern to match (e.g., `"myCustomSyntax" e:term`)
        pattern: Vec<SyntaxPatternItem>,
        /// The result category (e.g., "term", "command", "tactic")
        category: String,
        /// The elaboration body expression (after `=>`)
        body: Box<SurfaceExpr>,
    },

    /// Raw/unrecognized declaration (fallback for unparsed syntax)
    RawDecl {
        span: Span,
        /// Raw content captured as a string
        content: String,
    },

    /// Attribute application: `attribute [simp] foo bar`
    Attribute {
        span: Span,
        attrs: Vec<AttributeCommandAttr>,
        names: Vec<String>,
    },

    /// `set_option` command
    ///
    /// Two forms:
    /// - File-scope: `set_option maxHeartbeats 400000` (body is None)
    /// - Per-declaration: `set_option maxHeartbeats 400000 in def ...` (body is Some)
    SetOption {
        span: Span,
        name: String,
        value: Option<String>,
        /// When present, the option is scoped to this single declaration only.
        /// Corresponds to the Lean 4 `set_option ... in <command>` syntax.
        body: Option<Box<SurfaceDecl>>,
    },

    /// Declare aesop rule sets: `declare_aesop_rule_sets [Measurable, Continuous]`
    ///
    /// This declares named rule sets that can be used with `@[aesop safe, Measurable]`
    /// and invoked via `aesop (rule_sets := [Measurable])`.
    DeclareAesopRuleSets {
        span: Span,
        /// Names of the rule sets being declared
        names: Vec<String>,
    },

    /// `library_note «title»` / `library_note "title"` (Mathlib/Batteries doc
    /// command). Records a documentation note; carries no checkable content, so
    /// it elaborates to a no-op. The trailing `/-- … -/` note body is captured
    /// by the lexer's doc-comment side table, not as a command argument.
    LibraryNote {
        span: Span,
        /// The note title (a guillemet-quoted identifier or string literal).
        title: String,
    },
}

impl SurfaceDecl {
    /// Source span of this declaration.
    ///
    /// Every `SurfaceDecl` variant carries a leading `span` field; this
    /// accessor returns it uniformly.
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            SurfaceDecl::Def { span, .. }
            | SurfaceDecl::Theorem { span, .. }
            | SurfaceDecl::Axiom { span, .. }
            | SurfaceDecl::Opaque { span, .. }
            | SurfaceDecl::Inductive { span, .. }
            | SurfaceDecl::Coinductive { span, .. }
            | SurfaceDecl::Structure { span, .. }
            | SurfaceDecl::Class { span, .. }
            | SurfaceDecl::Instance { span, .. }
            | SurfaceDecl::Example { span, .. }
            | SurfaceDecl::Import { span, .. }
            | SurfaceDecl::Namespace { span, .. }
            | SurfaceDecl::Section { span, .. }
            | SurfaceDecl::UniverseDecl { span, .. }
            | SurfaceDecl::Variable { span, .. }
            | SurfaceDecl::Open { span, .. }
            | SurfaceDecl::Export { span, .. }
            | SurfaceDecl::DerivingInstance { span, .. }
            | SurfaceDecl::Check { span, .. }
            | SurfaceDecl::Eval { span, .. }
            | SurfaceDecl::Print { span, .. }
            | SurfaceDecl::Mutual { span, .. }
            | SurfaceDecl::Syntax { span, .. }
            | SurfaceDecl::DeclareSyntaxCat { span, .. }
            | SurfaceDecl::Macro { span, .. }
            | SurfaceDecl::MacroRules { span, .. }
            | SurfaceDecl::Notation { span, .. }
            | SurfaceDecl::Elab { span, .. }
            | SurfaceDecl::RawDecl { span, .. }
            | SurfaceDecl::Attribute { span, .. }
            | SurfaceDecl::SetOption { span, .. }
            | SurfaceDecl::DeclareAesopRuleSets { span, .. }
            | SurfaceDecl::LibraryNote { span, .. } => *span,
        }
    }
}

/// Constructor of an inductive type
#[derive(Debug, Clone)]
pub struct SurfaceCtor {
    pub span: Span,
    pub name: String,
    pub ty: SurfaceExpr,
}

/// A field in a structure declaration
#[derive(Debug, Clone)]
pub struct SurfaceField {
    pub span: Span,
    /// Field name
    pub name: String,
    /// Field type
    pub ty: SurfaceExpr,
    /// Default value (optional)
    pub default: Option<SurfaceExpr>,
    /// Bare `name := value` field-default override of an inherited field (no
    /// type annotation) — `structure C extends B where x := 10` re-defaults
    /// `B`'s `x` for `C` without declaring a new field. When set, `ty` is a
    /// placeholder [`SurfaceExpr::Hole`] and `default` is always `Some`.
    pub is_default_override: bool,
}

/// A field assignment in an instance declaration
///
/// ```text
/// instance : Add Nat where
///   add := Nat.add   -- This is a SurfaceFieldAssign
/// ```
#[derive(Debug, Clone)]
pub struct SurfaceFieldAssign {
    pub span: Span,
    /// Field name
    pub name: String,
    /// Assigned value
    pub val: SurfaceExpr,
}

/// A local definition from a `where` clause on a `def` or `theorem`.
///
/// ```text
/// def foo : Nat := helper 42
/// where
///   helper (n : Nat) : Nat := n + 1
/// ```
///
/// Each `WhereLocalDef` represents one helper definition. The elaborator
/// desugars these into nested `let rec` expressions wrapping the body.
#[derive(Debug, Clone)]
pub struct WhereLocalDef {
    /// Source span of the entire where definition
    pub span: Span,
    /// Name of the local definition
    pub name: String,
    /// Parameters (binders) of the local definition
    pub binders: Vec<SurfaceBinder>,
    /// Optional return type annotation
    pub ret_ty: Option<Box<SurfaceExpr>>,
    /// Body expression of the local definition
    pub body: SurfaceExpr,
}
