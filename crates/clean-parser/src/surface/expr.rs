// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Surface expression types: the main AST node for parsed expressions.

use super::name::{NameComponentSyntax, SurfaceName};

use super::binder::{OpenPath, SurfaceBinder, SurfaceBinderInfo};
use super::decl::SurfaceFieldAssign;
use super::span::Span;
use crate::surface_tactic::SurfaceTactic;
use crate::surface_tactic_types::{DoElem, SurfaceCalcStep};

/// Kind of Qq quotation in surface syntax
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QQuotationKind {
    /// Type quotation: `Q(α)` - denotes expressions of type α
    Type,
    /// Value quotation: `q(·)` - construct expression values
    Value,
}

/// Content of a Qq antiquotation (`$x`, `$(e)`, `$(x : τ)`, `$\[xs\]*`)
#[derive(Debug, Clone)]
pub enum QAntiquotContent {
    /// Simple identifier antiquotation: `$x`
    Simple(SurfaceName),
    /// Parenthesized expression antiquotation: `$(e)`
    Expr(Box<SurfaceExpr>),
    /// Typed antiquotation: `$(x : τ)`
    Typed {
        name: SurfaceName,
        ty: Box<SurfaceExpr>,
    },
    /// Splice antiquotation: `$[xs]*` or `$[xs]+`
    /// - `name`: the variable name containing the list to splice
    /// - `separator`: optional separator between spliced elements (default: None)
    /// - `at_least_one`: true for `+`, false for `*`
    Splice {
        name: SurfaceName,
        separator: Option<String>,
        at_least_one: bool,
    },
}

/// Head identifier of the type-less ascription `(e :)`, which the parser
/// represents as `App(Ident(TYPE_ASCRIPTION_WITHOUT_TYPE), [e])`.
///
/// Lean's `typeAscription := "(" term " :" optional term ")"`
/// (`Lean/Parser/Term.lean:182-183`) makes the type optional, and
/// `(e :)` elaborates `e` with NO expected type before `ensureHasType`
/// (`Lean/Elab/BuiltinNotation.lean:433-435`). That is not `(e : _)`, whose
/// hole Clean unifies with the expected type first. The spelling contains
/// characters no identifier token can hold, so no user name collides with it.
pub const TYPE_ASCRIPTION_WITHOUT_TYPE: &str = "(· :)";

/// The compiler-authored head of `(e :)`. Its component carries
/// [`NameComponentSyntax::Generated`], which no source identifier has — an
/// escaped `«(· :)»` is [`NameComponentSyntax::Escaped`] — so
/// [`is_type_ascription_without_type`] never mistakes a user name for it.
#[must_use]
pub(crate) fn type_ascription_without_type_head() -> SurfaceName {
    SurfaceName::from_name(clean_kernel::Name::anon().str(TYPE_ASCRIPTION_WITHOUT_TYPE))
}

/// Whether `name` is the head [`type_ascription_without_type_head`] mints.
#[must_use]
pub fn is_type_ascription_without_type(name: &SurfaceName) -> bool {
    name.component_text() == Some(TYPE_ASCRIPTION_WITHOUT_TYPE)
        && !name.is_relative_constructor()
        && name.component_syntax() == [NameComponentSyntax::Generated]
}

/// Head identifier of the anonymous constructor `⟨a, b, …⟩`, which the parser
/// represents as `App(Ident(ANONYMOUS_CONSTRUCTOR), [a, b, …])`.
pub const ANONYMOUS_CONSTRUCTOR: &str = "anonymousCtor";

/// The compiler-authored head of `⟨…⟩`. Like
/// [`type_ascription_without_type_head`], its component carries
/// [`NameComponentSyntax::Generated`], which no source identifier has, so a
/// user's own `anonymousCtor` (a definition, a parameter, a `let`) is an
/// ordinary identifier and never the anonymous constructor. Recognizing the
/// head by its text alone made `anonymousCtor 1 2` build `⟨1, 2⟩` whatever
/// the user had bound under that name.
#[must_use]
pub fn anonymous_constructor_head() -> SurfaceName {
    SurfaceName::global_path(ANONYMOUS_CONSTRUCTOR)
}

/// Whether `name` is the head [`anonymous_constructor_head`] mints.
#[must_use]
pub fn is_anonymous_constructor_head(name: &SurfaceName) -> bool {
    name.component_text() == Some(ANONYMOUS_CONSTRUCTOR)
        && !name.is_relative_constructor()
        && name.component_syntax() == [NameComponentSyntax::Generated]
}

/// Surface expression (before elaboration)
#[derive(Debug, Clone)]
pub enum SurfaceExpr {
    /// Identifier: `foo`, `Nat.add`
    Ident(Span, SurfaceName),

    /// Parser-generated placeholder that should elaborate as synthetic sorry.
    SyntheticSorry(Span),

    /// Universe: `Type`, `Type u`, `Prop`, `Sort u`
    Universe(Span, UniverseExpr),

    /// Application: `f x y`
    App(Span, Box<SurfaceExpr>, Vec<SurfaceArg>),

    /// Lambda: `fun x => e` or `fun (x : T) => e`
    Lambda(Span, Vec<SurfaceBinder>, Box<SurfaceExpr>),

    /// Pattern-matching lambda: `fun | pat => e | pat2 => e2`
    /// This is separate from Lambda to signal that application parsing should stop after this
    /// (layout-sensitive construct that we can't fully disambiguate without indentation info)
    PatternMatchLambda(Span, Vec<SurfaceBinder>, Box<SurfaceExpr>),

    /// Pi/forall: `∀ (x : A), B` or `(x : A) → B`
    Pi(Span, Vec<SurfaceBinder>, Box<SurfaceExpr>),

    /// Arrow (non-dependent): `A → B`
    Arrow(Span, Box<SurfaceExpr>, Box<SurfaceExpr>),

    /// Let binding: `let x := v in e` or `let x : T := v in e`
    Let(Span, SurfaceBinder, Box<SurfaceExpr>, Box<SurfaceExpr>),

    /// Opaque term binding: `have x : T := v; e`. Retains its value for proof
    /// assembly, but the local is not definitionally equal to that value.
    Have(Span, SurfaceBinder, Box<SurfaceExpr>, Box<SurfaceExpr>),

    /// Recursive let binding: `let rec f (n : Nat) : Nat := ... in e`
    LetRec(Span, SurfaceBinder, Box<SurfaceExpr>, Box<SurfaceExpr>),

    /// Let pattern binding: `let q($pat) := e | fallback in body`
    /// Pattern, scrutinee, fallback, body
    /// Part of #23: Qq Phase 4 - let-pattern support for runtime q-patterns
    LetPattern(
        Span,
        SurfacePattern,
        Box<SurfaceExpr>,
        Box<SurfaceExpr>,
        Box<SurfaceExpr>,
    ),

    /// Literal: `42`, `"hello"`
    Lit(Span, SurfaceLit),

    /// Parenthesized expression
    Paren(Span, Box<SurfaceExpr>),

    /// Hole/placeholder: `_`
    Hole(Span),

    /// Synthetic hole: `?name` carries its tag; `?_` and `?` carry the anonymous Name.
    /// An unsolved synthetic hole can be lifted into a tactic goal.
    NamedHole(Span, SurfaceName),

    /// Type ascription: `(e : T)`
    Ascription(Span, Box<SurfaceExpr>, Box<SurfaceExpr>),

    /// Out-parameter marker: `outParam T`
    /// Used in type class parameters to indicate output parameters
    OutParam(Span, Box<SurfaceExpr>),

    /// Explicit borrowed type annotation: `@& T` (retained as kernel MData).
    Borrowed(Span, Box<SurfaceExpr>),

    /// Semi-out-parameter marker: `semiOutParam T`
    /// Like outParam but allows unification in both directions during instance resolution.
    /// Instances promise to fill in this parameter, but it can also be constrained by context.
    SemiOutParam(Span, Box<SurfaceExpr>),

    /// If-then-else: `if c then t else e`
    If(Span, Box<SurfaceExpr>, Box<SurfaceExpr>, Box<SurfaceExpr>),

    /// If-let pattern match: `if let pat := e then t else f`
    /// Pattern, scrutinee, then-branch, else-branch
    IfLet(
        Span,
        SurfacePattern,
        Box<SurfaceExpr>,
        Box<SurfaceExpr>,
        Box<SurfaceExpr>,
    ),

    /// Decidable if: `if h : p then t else e`
    /// Binds proof witness `h` of proposition `p`
    /// witness name, proposition, then-branch, else-branch
    IfDecidable(
        Span,
        SurfaceName,
        Box<SurfaceExpr>,
        Box<SurfaceExpr>,
        Box<SurfaceExpr>,
    ),

    /// Match expression (simplified for now).
    ///
    /// The `Option<String>` is the discriminant-hypothesis name of Lean's
    /// annotated `matchDiscr` form (`Lean/Parser/Term.lean:275`,
    /// `matchDiscr := optional (atomic (binderIdent " : ")) >> termParser`):
    /// `match h : e with | p => …` binds `h : e = p` in each branch
    /// (`Lean/Elab/Match.lean:67`, `Discr` with `.some h`). `None` is the
    /// plain `match e with` form.
    Match(
        Span,
        Option<SurfaceName>,
        Box<SurfaceExpr>,
        Vec<SurfaceMatchArm>,
    ),

    /// Projection: `e.field` or `e.0`
    Proj(Span, Box<SurfaceExpr>, Projection),

    /// Universe instantiation: `Foo.{u v}` - explicit universe level arguments
    UniverseInst(Span, Box<SurfaceExpr>, Vec<LevelExpr>),

    /// Named argument: `(name := expr)` - used in function applications
    /// This represents the parenthesized named argument syntax
    NamedArg(Span, SurfaceName, Box<SurfaceExpr>),

    /// Raw syntax quotation token (`` `(…) ``) preserved from the lexer
    /// Used by macro declarations and `macro_rules` patterns/expansions.
    SyntaxQuote(Span, String),

    /// Qq type-safe quotation: `Q(α)` or `q(expr)`
    /// Used for type-safe expression construction in metaprogramming.
    /// Part of #16: Qq quotation support
    QQuotation {
        span: Span,
        /// Type quotation (Q) vs value quotation (q)
        kind: QQuotationKind,
        /// The inner expression (type for Q, value for q)
        inner: Box<SurfaceExpr>,
        /// Optional explicit type annotation: `q(e : τ)`
        type_annot: Option<Box<SurfaceExpr>>,
    },

    /// Antiquotation inside q(...): `$x`, `$(e)`, `$(x : τ)`
    /// Antiquotations splice in external values during quotation.
    /// Only valid inside `q(...)` expressions.
    QAntiquot {
        span: Span,
        /// The antiquotation content
        content: QAntiquotContent,
    },

    /// Explicit application marker: `@f` - disables implicit argument insertion
    /// When elaborated, the following function will have all its implicit
    /// parameters treated as explicit, requiring explicit type arguments.
    Explicit(Span, Box<SurfaceExpr>),

    /// Structure literal: `{ x := val, y := val2 }` or `{ x := val : StructType }`
    /// Also handles with-syntax: `{ s with x := newval }`
    StructLit {
        span: Span,
        /// Optional type annotation for the structure
        struct_type: Option<Box<SurfaceExpr>>,
        /// Base value for "with" syntax: `{ s with ... }`
        base: Option<Box<SurfaceExpr>>,
        /// Field assignments
        fields: Vec<SurfaceFieldAssign>,
    },

    /// Tactic proof block: `by tac1; tac2; ...`
    /// Contains the parsed tactic sequence instead of a sorry placeholder.
    ByTactic(Span, Vec<SurfaceTactic>),

    /// Calc proof block: `calc a = b := pf1  _ = c := pf2  ...`
    /// Contains a sequence of calc steps with relations and proofs.
    CalcBlock(Span, Vec<SurfaceCalcStep>),

    /// Do notation block: `do { let x <- f; pure x }` or `do let x <- f; pure x`
    /// Contains a sequence of do-elements that are desugared to Bind.bind/Pure.pure chains.
    Do(Span, Vec<DoElem>),

    /// Nested monadic action lift: `<- expr` (or `← expr`)
    /// Only valid inside do blocks. Desugared by the elaborator pre-pass
    /// (`expand_nested_actions`) into `let __do_lift_N <- expr` bindings
    /// prepended before the containing do-element.
    /// Reference: Lean 4 `Parser.Term.liftMethod` in `src/Lean/Parser/Do.lean:24`
    LiftMethod(Span, Box<SurfaceExpr>),

    /// Interpolated string: `s!"hello {name}"`, `m!"error: {msg}"`, `f!"x = {x}"`.
    /// Desugared during elaboration. Ref: Lean 4 `Parser.Term.interpolatedStr`.
    InterpolatedStr {
        span: Span,
        kind: crate::lexer::InterpolatedStringKind,
        parts: Vec<crate::interpolation::InterpolationPart>,
    },

    /// Term-level `open`: `open X in <term>` / `open scoped X in <term>`.
    ///
    /// Mirrors the declaration-level `open … in` command (`SurfaceDecl::Open`),
    /// but scopes the opened namespaces to a *sub-term* rather than a whole
    /// declaration. Mathlib uses this heavily in `Decidable`-backed proofs
    /// (`theorem foo : T := open scoped Classical in Decidable.…`). The
    /// `paths`/`scoped` fields are preserved (not discarded) so the elaborator
    /// can open the namespaces for name/instance resolution of `body` and pop
    /// the scope afterward. Ref: Lean 4 `Parser.Term.open` (`Lean/Parser/Term.lean`).
    OpenIn {
        span: Span,
        /// Namespaces to open for the sub-term (same representation as
        /// `SurfaceDecl::Open::paths`).
        paths: Vec<OpenPath>,
        /// `open scoped X in …` — brings scoped notations/instances into scope.
        scoped: bool,
        /// The sub-term elaborated with the namespaces open.
        body: Box<SurfaceExpr>,
    },
}

/// Argument to a function application
#[derive(Debug, Clone)]
pub struct SurfaceArg {
    pub span: Span,
    /// The argument expression
    pub expr: SurfaceExpr,
    /// Named argument: `(name := e)`
    pub name: Option<SurfaceName>,
}

impl SurfaceArg {
    /// Create a positional argument.
    ///
    /// # ENSURES
    /// - `name == None`
    /// - `span` is taken from the expression
    #[must_use]
    pub fn positional(expr: SurfaceExpr) -> Self {
        let span = expr.span();
        Self {
            span,
            expr,
            name: None,
        }
    }

    /// Create a named argument `(name := expr)`.
    ///
    /// # ENSURES
    /// - `name == Some(name)`
    /// - `span` is taken from the expression
    #[must_use]
    pub fn named(name: SurfaceName, expr: SurfaceExpr) -> Self {
        let span = expr.span();
        Self {
            span,
            expr,
            name: Some(name),
        }
    }

    /// Compiler-generated syntax marker, outside source identifier space.
    /// The numeric root and lexical metadata survive exact macro transport;
    /// authored `«..»` and numeric-looking identifier text remain real names.
    fn ellipsis_name() -> SurfaceName {
        SurfaceName::from_name(
            clean_kernel::Name::anon()
                .num(u64::MAX)
                .str("application-ellipsis"),
        )
    }

    /// Create the trailing-ellipsis argument for Lean's `Term.ellipsis`
    /// (`f ..`, `Lean/Parser/Term.lean`): "fill every REMAINING explicit
    /// parameter of `f` with `_`".
    ///
    /// The arity is not known to the parser, so the marker is carried through
    /// to the elaborator, which expands it against the inferred function type
    /// (`Elaborator::expand_app_ellipsis`). The payload expression is a
    /// [`SurfaceExpr::Hole`] purely so the arg is well-formed if some
    /// unrelated pass walks it; the *marker* is the reserved typed syntax.
    ///
    /// # ENSURES
    /// - `is_ellipsis()` is true
    #[must_use]
    pub fn ellipsis(span: Span) -> Self {
        Self {
            span,
            expr: SurfaceExpr::Hole(span),
            name: Some(Self::ellipsis_name()),
        }
    }

    /// Is this the trailing application ellipsis `..` rather than a real
    /// positional or named argument?
    #[must_use]
    pub fn is_ellipsis(&self) -> bool {
        self.name
            .as_ref()
            .is_some_and(|name| name.same_syntax(&Self::ellipsis_name()))
    }
}

/// Universe expression
#[derive(Debug, Clone)]
pub enum UniverseExpr {
    /// Prop = Sort 0
    Prop,
    /// Type = Sort 1
    Type,
    /// Type u (explicit level)
    TypeLevel(Box<LevelExpr>),
    /// Type* (implicit level, equivalent to Type u for fresh u)
    /// Used in Mathlib for auto-bound universe variables
    TypeImplicit,
    /// Sort u (explicit level)
    Sort(Box<LevelExpr>),
    /// Sort (implicit level, equivalent to Sort u for fresh u)
    SortImplicit,
    /// `Sort*` (Mathlib syntax for an implicit/auto-bound universe level, the
    /// `Sort` analogue of [`UniverseExpr::TypeImplicit`]). Distinct from bare
    /// `Sort` (`SortImplicit`) so the strict `--prelude lean4-core` gate can
    /// reject it exactly as it rejects `Type*` without touching bare `Sort`.
    SortStar,
}

/// Level expression (surface syntax for universe levels)
#[derive(Debug, Clone)]
pub enum LevelExpr {
    /// Numeric literal: 0, 1, 2, ...
    Lit(u32),
    /// Level parameter: u, v
    Param(SurfaceName),
    /// Successor: u + 1
    Succ(Box<LevelExpr>),
    /// Max: max u v
    Max(Box<LevelExpr>, Box<LevelExpr>),
    /// `IMax`: `imax u v`
    IMax(Box<LevelExpr>, Box<LevelExpr>),
    /// Antiquotation: $u (used in q(...) for universe polymorphism)
    Antiquot(SurfaceName),
}

/// A match arm
#[derive(Debug, Clone)]
pub struct SurfaceMatchArm {
    pub span: Span,
    /// Pattern (simplified: just an identifier for now)
    pub pattern: SurfacePattern,
    /// Body expression
    pub body: SurfaceExpr,
}

/// Pattern for match (simplified for Phase 2)
#[derive(Debug, Clone)]
pub enum SurfacePattern {
    /// Variable pattern: `x`
    Var(SurfaceName),
    /// Constructor pattern: `Nat.zero` or `Nat.succ n`
    Ctor(SurfaceName, Vec<SurfacePattern>),
    /// Wildcard: `_`
    Wildcard,
    /// Inaccessible pattern: `.(expr)` - checked by unification, does not bind.
    Inaccessible(Box<SurfaceExpr>),
    /// Literal pattern
    Lit(SurfaceLit),
    /// Numeral addition pattern: `n + 1` (sugar for successor patterns)
    NumeralAdd(Box<SurfacePattern>, u64),
    /// As pattern: `n@pat` - binds `n` to the matched value and checks `pat`
    As(SurfaceName, Box<SurfacePattern>),
    /// Or pattern: `pat1 | pat2` - matches if either pattern matches
    Or(Box<SurfacePattern>, Box<SurfacePattern>),
    /// Qq pattern: `q(expr)` with antiquotation pattern variables
    /// Used for pattern matching on Q(α) values in type-safe metaprogramming.
    /// Part of #16: Qq quotation support - Phase 3
    QPattern(Box<SurfaceExpr>),
    /// Structure-instance pattern: `{ f := p, g := q, .. }`, optionally with a
    /// type ascription `{ f := p : S }`.
    ///
    /// Lean has no separate pattern grammar — patterns ARE terms, so
    /// `Lean.Parser.Term.structInst` parses in pattern position for free and
    /// `Lean/Elab/PatternVar.lean:304-313` walks each field's value collecting
    /// pattern variables. Clean's pattern parser is a closed token set, so the
    /// form needs its own node. The field names are resolved to constructor
    /// positions in the elaborator (`normalize_match_pattern_names_inner`),
    /// where the scrutinee type is known; the parser records them verbatim.
    ///
    /// `with` sources are refused at parse time, exactly as Lean refuses them
    /// (`Lean/Elab/PatternVar.lean:306`).
    StructInst {
        /// Field assignments, in source order. `{ x }` abbreviates `{ x := x }`.
        fields: Vec<(SurfaceName, SurfacePattern)>,
        /// Whether the literal ended with `..` (remaining fields are wildcards).
        ellipsis: bool,
        /// Optional `: S` ascription naming the structure.
        ty: Option<Box<SurfaceExpr>>,
    },
    /// Constructor-field ellipsis: the `..` in `.Ctor ..`. Appears only as the
    /// trailing element of a `Ctor` argument list. It means "every remaining
    /// explicit field is a wildcard". Constructor-pattern arity expansion
    /// (`expand_implicit_ctor_field_patterns`) drops this marker and materializes
    /// one non-binding `Wildcard` per explicit field. It binds no variables, so
    /// everywhere else it behaves exactly like `Wildcard`.
    Ellipsis,
}

impl SurfacePattern {
    /// Get a dummy span for the pattern (simplified)
    #[must_use]
    pub fn span(&self) -> Span {
        Span::dummy()
    }

    /// Collect all variable names bound by this pattern.
    ///
    /// Used by pattern reassignment to determine which mutable variables
    /// are being updated (for ControlInfo `reassigns` computation).
    pub fn collect_var_names(&self, names: &mut Vec<SurfaceName>) {
        match self {
            SurfacePattern::Var(name) => names.push(name.clone()),
            SurfacePattern::Ctor(_, args) => {
                for arg in args {
                    arg.collect_var_names(names);
                }
            }
            SurfacePattern::As(name, inner) => {
                names.push(name.clone());
                inner.collect_var_names(names);
            }
            SurfacePattern::Or(a, b) => {
                a.collect_var_names(names);
                b.collect_var_names(names);
            }
            SurfacePattern::NumeralAdd(inner, _) => inner.collect_var_names(names),
            SurfacePattern::StructInst { fields, .. } => {
                for (_, pat) in fields {
                    pat.collect_var_names(names);
                }
            }
            SurfacePattern::Wildcard
            | SurfacePattern::Ellipsis
            | SurfacePattern::Inaccessible(_)
            | SurfacePattern::Lit(_)
            | SurfacePattern::QPattern(_) => {}
        }
    }
}

/// Projection target
#[derive(Debug, Clone)]
pub enum Projection {
    /// Named field: `.foo`
    Named(SurfaceName),
    /// Indexed field: `.1`, `.2`
    Index(u32),
}

/// Surface literal
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SurfaceLit {
    Nat(u64),
    /// Natural-number literal at or above `2^64` (`18446744073709551616`,
    /// `0xFFFF_FFFF_FFFF_FFFF + 1`, a 100-digit decimal, …). Lean 4 `Nat` is
    /// unbounded, so values that do not fit in a `u64` keep their exact value in
    /// a kernel `BigNat`. The compact `Nat(u64)` arm is retained for the common
    /// (small) case; use [`SurfaceLit::nat`] to pick the right arm from a value.
    BigNat(clean_kernel::BigNat),
    /// Floating-point literal (`3.14`, `1e-5`), stored as its normalized source
    /// text (underscores stripped) so the value is represented losslessly. Lean
    /// 4 elaborates these via `OfScientific`; keeping the exact decimal text
    /// avoids the rounding an `f64` round-trip would introduce.
    Float(String),
    /// Character literal (`'a'`, `'\n'`). Lean 4 `Char`.
    Char(char),
    String(String),
}

impl SurfaceLit {
    /// Build a natural-number literal from an arbitrary-precision `BigNat`,
    /// choosing the compact `Nat(u64)` representation when the value fits in a
    /// `u64` and the arbitrary-precision `BigNat` arm otherwise. This keeps the
    /// overwhelmingly-common small case cheap while representing `>= 2^64`
    /// literals exactly.
    #[must_use]
    pub fn nat(n: clean_kernel::BigNat) -> Self {
        match n.to_u64() {
            Some(v) => SurfaceLit::Nat(v),
            None => SurfaceLit::BigNat(n),
        }
    }
}

impl SurfaceExpr {
    #[allow(clippy::match_same_arms)] // Each variant returns span; explicit arms aids maintenance
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            SurfaceExpr::Ident(s, _) => *s,
            SurfaceExpr::SyntheticSorry(s) => *s,
            SurfaceExpr::Universe(s, _) => *s,
            SurfaceExpr::App(s, _, _) => *s,
            SurfaceExpr::Lambda(s, _, _) => *s,
            SurfaceExpr::PatternMatchLambda(s, _, _) => *s,
            SurfaceExpr::Pi(s, _, _) => *s,
            SurfaceExpr::Arrow(s, _, _) => *s,
            SurfaceExpr::Let(s, _, _, _) | SurfaceExpr::Have(s, _, _, _) => *s,
            SurfaceExpr::LetRec(s, _, _, _) => *s,
            SurfaceExpr::LetPattern(s, _, _, _, _) => *s,
            SurfaceExpr::Lit(s, _) => *s,
            SurfaceExpr::Paren(s, _) => *s,
            SurfaceExpr::Hole(s) => *s,
            SurfaceExpr::NamedHole(s, _) => *s,
            SurfaceExpr::Ascription(s, _, _) => *s,
            SurfaceExpr::Borrowed(s, _) => *s,
            SurfaceExpr::OutParam(s, _) => *s,
            SurfaceExpr::SemiOutParam(s, _) => *s,
            SurfaceExpr::If(s, _, _, _) => *s,
            SurfaceExpr::IfLet(s, _, _, _, _) => *s,
            SurfaceExpr::IfDecidable(s, _, _, _, _) => *s,
            SurfaceExpr::Match(s, _, _, _) => *s,
            SurfaceExpr::Proj(s, _, _) => *s,
            SurfaceExpr::UniverseInst(s, _, _) => *s,
            SurfaceExpr::NamedArg(s, _, _) => *s,
            SurfaceExpr::SyntaxQuote(s, _) => *s,
            SurfaceExpr::QQuotation { span, .. } => *span,
            SurfaceExpr::QAntiquot { span, .. } => *span,
            SurfaceExpr::Explicit(s, _) => *s,
            SurfaceExpr::StructLit { span, .. } => *span,
            SurfaceExpr::ByTactic(s, _) => *s,
            SurfaceExpr::CalcBlock(s, _) => *s,
            SurfaceExpr::Do(s, _) => *s,
            SurfaceExpr::LiftMethod(s, _) => *s,
            SurfaceExpr::InterpolatedStr { span, .. } => *span,
            SurfaceExpr::OpenIn { span, .. } => *span,
        }
    }

    /// A compiler-authored reference to the global constant `name`, with a
    /// dummy span. It never resolves to a local
    /// ([`SurfaceName::global_path`]); a reference to a binder the caller
    /// introduced is built from that binder's own name instead.
    pub fn ident(name: impl Into<String>) -> Self {
        SurfaceExpr::Ident(Span::dummy(), SurfaceName::global_path(&name.into()))
    }

    /// Create an `App` with span from `func`; args converted to positional.
    pub fn app(func: SurfaceExpr, args: Vec<SurfaceExpr>) -> Self {
        let span = func.span();
        let args = args.into_iter().map(SurfaceArg::positional).collect();
        SurfaceExpr::App(span, Box::new(func), args)
    }

    /// Create a `Lambda` with dummy span.
    #[must_use]
    pub fn lambda(binders: Vec<SurfaceBinder>, body: SurfaceExpr) -> Self {
        SurfaceExpr::Lambda(Span::dummy(), binders, Box::new(body))
    }

    /// Create an `Arrow` with merged span.
    #[must_use]
    pub fn arrow(from: SurfaceExpr, to: SurfaceExpr) -> Self {
        let span = from.span().merge(to.span());
        SurfaceExpr::Arrow(span, Box::new(from), Box::new(to))
    }

    /// Create a `Pi` with dummy span.
    #[must_use]
    pub fn pi(binders: Vec<SurfaceBinder>, body: SurfaceExpr) -> Self {
        SurfaceExpr::Pi(Span::dummy(), binders, Box::new(body))
    }

    /// Create `Type`.
    #[must_use]
    pub fn type_() -> Self {
        SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Type)
    }

    /// Create `Prop`.
    #[must_use]
    pub fn prop() -> Self {
        SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Prop)
    }

    /// Create a nat literal.
    #[must_use]
    pub fn nat(n: u64) -> Self {
        SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(n))
    }

    /// Create a `Hole` with dummy span.
    #[must_use]
    pub fn hole() -> Self {
        SurfaceExpr::Hole(Span::dummy())
    }

    /// Create a `Let` with dummy span and no type annotation.
    #[must_use]
    pub fn let_expr(name: impl Into<String>, value: SurfaceExpr, body: SurfaceExpr) -> Self {
        let binder = SurfaceBinder {
            span: Span::dummy(),
            name: SurfaceName::component(name.into(), false),
            ty: None,
            default: None,
            info: SurfaceBinderInfo::Explicit,
        };
        SurfaceExpr::Let(Span::dummy(), binder, Box::new(value), Box::new(body))
    }

    /// Create an `If` with dummy span.
    #[must_use]
    pub fn if_expr(cond: SurfaceExpr, then_br: SurfaceExpr, else_br: SurfaceExpr) -> Self {
        SurfaceExpr::If(
            Span::dummy(),
            Box::new(cond),
            Box::new(then_br),
            Box::new(else_br),
        )
    }
}
