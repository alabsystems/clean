// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Surface declaration types: top-level parsed declarations.

use super::name::SurfaceName;

use super::attr::Attribute;
use super::binder::{OpenPath, SurfaceBinder, TerminationHints};
use super::expr::SurfaceExpr;
use super::modifiers::{DeclModifiers, DeclScope, Visibility};
use super::span::Span;
use super::syntax::{MacroArm, NotationItem, NotationKind, SyntaxPatternItem};

/// A captured Lean 4 declaration documentation comment (`/-- ... -/`).
///
/// Lean attaches a `/-- ... -/` doc comment to the declaration that
/// immediately follows it. The parser carries this metadata on actual
/// declaration/member attachments; validation happens when they elaborate.
/// [`crate::Parser::parse_file_with_docs`] also exposes the IDE side table.
///
/// `/-! ... -/` *module/section* doc comments are intentionally NOT captured
/// here — only the declaration-attaching `/-- ... -/` form is.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DocComment {
    /// Source span of the entire comment, including the `/--` and `-/`
    /// delimiters.
    pub span: Span,
    /// Original comment range, even when an IDE side table associates `span`
    /// with a declaration. Link errors use these original byte coordinates.
    pub comment_span: Span,
    /// Untrimmed bytes between the opening and closing delimiters.
    pub raw_text: String,
    /// The inner documentation text, with the `/--` opener and `-/` closer
    /// stripped and surrounding whitespace trimmed.
    pub text: String,
}

impl DocComment {
    /// Create a new doc comment from its span and already-stripped text.
    #[must_use]
    pub(crate) fn new(span: Span, text: String) -> Self {
        Self {
            span,
            comment_span: span,
            text: text.trim().to_owned(),
            raw_text: text,
        }
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
    /// File-header `prelude`; requires an explicitly bare module environment.
    Prelude { span: Span },
    /// Definition: `def name : ty := val`
    Def {
        span: Span,
        name: SurfaceName,
        universe_params: Vec<SurfaceName>,
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

    /// A Batteries alias preserves the target's complete telescope. It is not
    /// an inferred source `def`, which would insert implicit arguments.
    Alias {
        span: Span,
        /// One plain alias, or the named directions of an iff alias.
        names: Vec<(SurfaceName, Option<bool>)>,
        target: SurfaceName,
        attrs: Vec<Attribute>,
        modifiers: DeclModifiers,
    },

    /// Theorem: `theorem name : ty := proof`
    Theorem {
        span: Span,
        name: SurfaceName,
        universe_params: Vec<SurfaceName>,
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
        name: SurfaceName,
        universe_params: Vec<SurfaceName>,
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
        name: SurfaceName,
        universe_params: Vec<SurfaceName>,
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
        name: SurfaceName,
        universe_params: Vec<SurfaceName>,
        binders: Vec<SurfaceBinder>,
        ty: Box<SurfaceExpr>,
        ctors: Vec<SurfaceCtor>,
        /// Deriving clauses (class names to derive)
        deriving: Vec<SurfaceName>,
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
        name: SurfaceName,
        universe_params: Vec<SurfaceName>,
        binders: Vec<SurfaceBinder>,
        ty: Box<SurfaceExpr>,
        ctors: Vec<SurfaceCtor>,
        /// Deriving clauses (class names to derive)
        deriving: Vec<SurfaceName>,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },

    /// Rocq-style Type-level codata, elaborated to the indexed-container
    /// M-type encoding (`Codata.*` seed library) — no kernel cofix, no new
    /// reduction rule.
    ///
    /// Two body shapes, mutually exclusive by construction (see
    /// [`CodataBody`]):
    ///
    /// ```text
    /// codata Stream (A : Type) where          -- RECORD body
    ///   head : A
    ///   tail : Stream A
    ///
    /// codata ITr (E : Type) (R : Type) where  -- VARIANT body
    ///   | Ret : R → ITr E R
    ///   | Tau : ITr E R → ITr E R
    /// ```
    Codata {
        span: Span,
        name: SurfaceName,
        universe_params: Vec<SurfaceName>,
        binders: Vec<SurfaceBinder>,
        /// Optional declared result sort (`: Type`)
        ty: Option<Box<SurfaceExpr>>,
        body: CodataBody,
        /// Deriving clauses (rejected loudly by the elaborator for now)
        deriving: Vec<SurfaceName>,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },

    /// Copattern definition into a codata type: each clause gives one
    /// observation of the result; recursive clauses are self-calls.
    /// Compiles to the codata's generated corecursor.
    ///
    /// ```text
    /// codef natsFrom (n : Nat) : Stream Nat where
    ///   head := n
    ///   tail := natsFrom (Nat.succ n)
    /// ```
    Codef {
        span: Span,
        name: SurfaceName,
        binders: Vec<SurfaceBinder>,
        ty: Box<SurfaceExpr>,
        clauses: Vec<(SurfaceName, SurfaceExpr)>,
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
        name: SurfaceName,
        universe_params: Vec<SurfaceName>,
        /// Parameters of the structure (before `where`)
        binders: Vec<SurfaceBinder>,
        /// Parent structures (from `extends` clause).
        /// Each element is a type expression like `Base` or `Bar α`.
        extends: Vec<Box<SurfaceExpr>>,
        /// Optional explicit result type (defaults to Type)
        ty: Option<Box<SurfaceExpr>>,
        /// Optional explicit constructor name (`structure P where make :: …`,
        /// Lean `structCtor`). `None` means the default `mk`.
        ctor_name: Option<SurfaceName>,
        /// Fields of the structure
        fields: Vec<SurfaceField>,
        /// Deriving clauses (class names to derive)
        deriving: Vec<SurfaceName>,
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
        name: SurfaceName,
        universe_params: Vec<SurfaceName>,
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
        name: Option<SurfaceName>,
        universe_params: Vec<SurfaceName>,
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
        /// `@[implemented_by f]` / `@[extern]` written on the instance: Lean
        /// applies them to the instance constant, and compiled code runs `f`
        /// (or the symbol) instead of the instance's value. Also
        /// `@[default_instance]`, which registers the instance for
        /// open-goal defaulting (B99); dropping it left the most recent
        /// instance to answer an open goal, so `@[default_instance] instance
        /// b : C Bool` followed by `instance n : C Nat` answered `C ?α` with
        /// `n`. Definition exposure and definitional-equality tags are also
        /// carried here. Other attributes except priority are not carried.
        compiler_attrs: Vec<Attribute>,
    },

    /// Example: `example : ty := proof` (anonymous theorem, not saved to environment)
    Example {
        span: Span,
        binders: Vec<SurfaceBinder>,
        ty: Option<Box<SurfaceExpr>>,
        val: Box<SurfaceExpr>,
    },

    /// Import: `import Lean.Data.List` (supports multiple module paths)
    Import { span: Span, paths: Vec<SurfaceName> },

    /// Namespace: `namespace Foo ... end Foo`
    Namespace {
        span: Span,
        name: SurfaceName,
        decls: Vec<SurfaceDecl>,
    },

    /// Section: `section Foo ... end Foo`
    Section {
        span: Span,
        name: Option<SurfaceName>,
        decls: Vec<SurfaceDecl>,
        /// `noncomputable section`: Lean marks a declaration inside it that its
        /// compiler cannot compile `noncomputable` instead of refusing it.
        noncomputable: bool,
    },

    /// Universe declaration: `universe u v`
    UniverseDecl { span: Span, names: Vec<SurfaceName> },

    /// Variable declaration: `variable (x : Type)`
    Variable {
        span: Span,
        binders: Vec<SurfaceBinder>,
        /// Explicit modifier, retained even in v4.36rc2 where upstream gives
        /// it no semantic effect. `None` is an unmodified variable command.
        visibility: Option<Visibility>,
    },

    /// `include x y …` — force section variables into following signatures.
    ///
    /// Lean 4 includes a section `variable` in a declaration only when the
    /// declaration MENTIONS it. `include x` overrides that for every
    /// declaration that follows it in the same scope: the variable is added to
    /// their signatures whether mentioned or not. This is how
    /// `Function.Involutive.injective` receives `(h : Involutive f)` even
    /// though its statement never names `h`.
    ///
    /// Scoped exactly like `variable`: a `section` / `namespace` boundary
    /// restores the enclosing inclusion set. Cancelled by [`Self::OmitVars`].
    IncludeVars { span: Span, names: Vec<SurfaceName> },

    /// `omit x y …` — cancel a preceding [`Self::IncludeVars`], restoring
    /// mention-based inclusion for those names.
    ///
    /// Only the NAME form is modelled. Lean also accepts bracketed instance
    /// binders (`omit [Foo α]`), which select by TYPE; that shape is refused
    /// by name rather than guessed at.
    OmitVars { span: Span, names: Vec<SurfaceName> },

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
        namespace: SurfaceName,
        /// The names to export (must have at least one)
        names: Vec<SurfaceName>,
    },

    /// Standalone deriving instance command: `deriving instance Repr, BEq for MyType`
    /// Derives type class instances for types defined elsewhere.
    DerivingInstance {
        span: Span,
        /// Type classes to derive (e.g., ["Repr", "BEq"])
        classes: Vec<SurfaceName>,
        /// Types to derive instances for
        types: Vec<SurfaceName>,
    },

    /// #check command: `#check expr`
    Check { span: Span, expr: Box<SurfaceExpr> },

    /// #eval command: `#eval expr`
    Eval { span: Span, expr: Box<SurfaceExpr> },

    /// `#reduce (proofs := true)? (types := true)? expr` (Lean 4.30.0-rc2
    /// `Lean.reduceCmd`): `Lean.Meta.reduce` of `expr`, logged. It is not
    /// `#eval`: nothing is compiled or run. Each flag is `true` when its
    /// `(… := true)` group is written, i.e. when Lean does NOT skip that class
    /// of subterm (`skipProofs := false` / `skipTypes := false`).
    Reduce {
        span: Span,
        expr: Box<SurfaceExpr>,
        reduce_proofs: bool,
        reduce_types: bool,
    },

    /// #print command: `#print name`
    Print { span: Span, name: SurfaceName },

    /// `#print axioms c` (Lean 4.8.0 `Lean.Parser.Command.printAxioms`):
    /// report the axioms `c` depends on, as an information message.
    PrintAxioms { span: Span, name: SurfaceName },

    /// `#print equations c` or `#print eqns c`: realize and report the
    /// equations of `c`.
    PrintEquations { span: Span, name: SurfaceName },

    /// `#guard e` (Lean 4.8.0 `Lean.Parser.Command.guardCmd`,
    /// `Init/Guard.lean`): `e` is elaborated at `Bool` and must evaluate to
    /// `true`.
    Guard { span: Span, expr: Box<SurfaceExpr> },

    /// `/-- expected -/ #guard_msgs (spec)? in cmd` (Lean 4.8.0
    /// `Lean.guardMsgsCmd`): run `cmd` and require the messages it produces
    /// to equal the doc comment written immediately before `#guard_msgs`.
    GuardMsgs {
        span: Span,
        /// The text of that doc comment between `/--` and `-/`, untrimmed
        /// (Lean's `getDocStringText`); `None` when there is none, which
        /// Lean reads as the empty expectation.
        doc: Option<String>,
        /// The `(…)` configuration clauses, as written.
        spec: Vec<super::guard_msgs::GuardMsgsSpecElt>,
        /// The command whose messages are checked.
        cmd: Box<SurfaceDecl>,
    },

    /// Mutual block: `mutual ... end`
    Mutual { span: Span, decls: Vec<SurfaceDecl> },

    /// Syntax declaration: defines a new syntax pattern
    ///
    /// ```text
    /// syntax:65 (name := myAdd) term "+" term : term
    /// syntax:20 term "+" term : term  -- with precedence
    /// ```
    Syntax {
        span: Span,
        /// Optional name for the syntax (e.g., `[name]` attribute)
        name: Option<SurfaceName>,
        /// Optional precedence level
        precedence: Option<u32>,
        /// Optional priority for disambiguation
        priority: Option<clean_kernel::BigNat>,
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
        name: SurfaceName,
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
        name: Option<SurfaceName>,
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
        /// Mathlib's `scoped[NS]` (`Mathlib/Tactic/ScopedNS.lean`,
        /// `with_weak_namespace _root_.NS scoped <cmd>`): the ABSOLUTE
        /// namespace the declaration runs in, in place of the current one.
        /// `None` for every other notation command.
        scope_ns: Option<SurfaceName>,
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
        names: Vec<SurfaceName>,
    },

    /// `set_option` command
    ///
    /// Two forms:
    /// - File-scope: `set_option maxHeartbeats 400000` (body is None)
    /// - Per-declaration: `set_option maxHeartbeats 400000 in def ...` (body is Some)
    SetOption {
        span: Span,
        name: SurfaceName,
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
        names: Vec<SurfaceName>,
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
    /// Declaration prefix metadata. Administrative commands and `#guard_msgs`
    /// do not attach their comments to an environment declaration here.
    pub fn modifiers_mut(&mut self) -> Option<&mut DeclModifiers> {
        match self {
            Self::Def { modifiers, .. }
            | Self::Alias { modifiers, .. }
            | Self::Theorem { modifiers, .. }
            | Self::Axiom { modifiers, .. }
            | Self::Opaque { modifiers, .. }
            | Self::Inductive { modifiers, .. }
            | Self::Coinductive { modifiers, .. }
            | Self::Codata { modifiers, .. }
            | Self::Codef { modifiers, .. }
            | Self::Structure { modifiers, .. }
            | Self::Class { modifiers, .. }
            | Self::Instance { modifiers, .. } => Some(modifiers),
            _ => None,
        }
    }

    /// Documentation on the declaration itself; field/constructor comments
    /// remain on their own parsed members.
    #[must_use]
    pub fn documentation(&self) -> Option<&DocComment> {
        match self {
            Self::Def { modifiers, .. }
            | Self::Alias { modifiers, .. }
            | Self::Theorem { modifiers, .. }
            | Self::Axiom { modifiers, .. }
            | Self::Opaque { modifiers, .. }
            | Self::Inductive { modifiers, .. }
            | Self::Coinductive { modifiers, .. }
            | Self::Codata { modifiers, .. }
            | Self::Codef { modifiers, .. }
            | Self::Structure { modifiers, .. }
            | Self::Class { modifiers, .. }
            | Self::Instance { modifiers, .. } => modifiers.documentation.as_ref(),
            _ => None,
        }
    }
    /// Source span of this declaration.
    ///
    /// Every `SurfaceDecl` variant carries a leading `span` field; this
    /// accessor returns it uniformly.
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            SurfaceDecl::Def { span, .. }
            | SurfaceDecl::Alias { span, .. }
            | SurfaceDecl::Theorem { span, .. }
            | SurfaceDecl::Axiom { span, .. }
            | SurfaceDecl::Opaque { span, .. }
            | SurfaceDecl::Inductive { span, .. }
            | SurfaceDecl::Coinductive { span, .. }
            | SurfaceDecl::Codata { span, .. }
            | SurfaceDecl::Codef { span, .. }
            | SurfaceDecl::Structure { span, .. }
            | SurfaceDecl::Class { span, .. }
            | SurfaceDecl::Instance { span, .. }
            | SurfaceDecl::Example { span, .. }
            | SurfaceDecl::Import { span, .. }
            | SurfaceDecl::Namespace { span, .. }
            | SurfaceDecl::Section { span, .. }
            | SurfaceDecl::UniverseDecl { span, .. }
            | SurfaceDecl::Variable { span, .. }
            | SurfaceDecl::IncludeVars { span, .. }
            | SurfaceDecl::OmitVars { span, .. }
            | SurfaceDecl::Open { span, .. }
            | SurfaceDecl::Export { span, .. }
            | SurfaceDecl::DerivingInstance { span, .. }
            | SurfaceDecl::Check { span, .. }
            | SurfaceDecl::Eval { span, .. }
            | SurfaceDecl::Reduce { span, .. }
            | SurfaceDecl::Print { span, .. }
            | SurfaceDecl::PrintAxioms { span, .. }
            | SurfaceDecl::PrintEquations { span, .. }
            | SurfaceDecl::Guard { span, .. }
            | SurfaceDecl::GuardMsgs { span, .. }
            | SurfaceDecl::Mutual { span, .. }
            | SurfaceDecl::Syntax { span, .. }
            | SurfaceDecl::DeclareSyntaxCat { span, .. }
            | SurfaceDecl::Macro { span, .. }
            | SurfaceDecl::MacroRules { span, .. }
            | SurfaceDecl::Notation { span, .. }
            | SurfaceDecl::Elab { span, .. }
            | SurfaceDecl::Prelude { span }
            | SurfaceDecl::RawDecl { span, .. }
            | SurfaceDecl::Attribute { span, .. }
            | SurfaceDecl::SetOption { span, .. }
            | SurfaceDecl::DeclareAesopRuleSets { span, .. }
            | SurfaceDecl::LibraryNote { span, .. } => *span,
        }
    }
}

/// The body of a `codata` declaration.
///
/// Record and variant bodies are mutually exclusive *by construction* —
/// a `codata` block is either observation fields or `|`-led constructor
/// clauses, never both. Representing them as one enum rather than two
/// possibly-non-empty vectors means "half a record and half a variant" is
/// not a state the elaborator has to defend against.
///
/// See `designs/2026-08-28-variant-codata-surface.md` §2.
#[derive(Debug, Clone)]
pub enum CodataBody {
    /// `head : A` / `tail : Stream A` observation fields (the rank-1
    /// record envelope).
    Record(Vec<SurfaceField>),
    /// `| Ret : R → T` constructor clauses (the variant envelope).
    Variant(Vec<SurfaceCtor>),
}

/// Constructor of an inductive type
#[derive(Debug, Clone)]
pub struct SurfaceCtor {
    pub span: Span,
    /// Documentation attached to this member, not an enclosing command.
    pub documentation: Option<DocComment>,
    /// A second doc after `|`, when a leading doc already precedes `|`.
    /// Lean diagnoses the duplicate but attaches the leading comment.
    pub duplicate_documentation: Option<DocComment>,
    pub name: SurfaceName,
    pub ty: SurfaceExpr,
}

/// A field in a structure declaration
#[derive(Debug, Clone)]
pub struct SurfaceField {
    pub span: Span,
    /// Documentation attached to this member, not an enclosing command.
    pub documentation: Option<DocComment>,
    /// Field name
    pub name: SurfaceName,
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
    pub name: SurfaceName,
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
    pub name: SurfaceName,
    /// Parameters (binders) of the local definition
    pub binders: Vec<SurfaceBinder>,
    /// Optional return type annotation
    pub ret_ty: Option<Box<SurfaceExpr>>,
    /// Body expression of the local definition
    pub body: SurfaceExpr,
    /// `termination_by` / `decreasing_by` written after this helper's body.
    /// Lean attaches a hint that follows a `where` helper to that helper
    /// (`Lean/Parser/Term.lean` `letRecDecl` carries `Termination.suffix`).
    pub termination: TerminationHints,
}
