// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core value types for the Path-B Isabelle→Lean **statement** translator: the
//! rendered-term AST ([`LeanTerm`]), the precedence table, the render context,
//! the honest [`Unsupported`] verdict, and the top-level [`LeanGoal`] result.
//!
//! This lane translates only the *statement* (the theorem's `prop`), never the
//! proof — the downstream kernel/Aristotle re-proves it. The cardinal rule is
//! **faithful-or-unsupported**: any shape the pattern library cannot render
//! exactly becomes an [`Unsupported`] verdict, never a plausible-but-wrong
//! statement.

/// Precedence of the rendered Lean infix operators (higher binds tighter). Only
/// the *relative* order matters — it drives the parenthesization in
/// [`super::render`] so the emitted surface mirrors the batch-established hand
/// translations byte-for-byte.
pub mod prec {
    /// `=` / `↔` — the sentence-level connective (loosest binary form).
    pub const EQ: u8 = 4;
    /// `∨`.
    pub const DISJ: u8 = 5;
    /// `∧`.
    pub const CONJ: u8 = 6;
    /// `→` (object implication).
    pub const IMPLIES: u8 = 7;
    /// `≤ < > ≥` relations (non-associative).
    pub const REL: u8 = 8;
    /// `∪ ∩` lattice operators on `Set`.
    pub const LATTICE: u8 = 9;
    /// `+ -` and list `++` (all rendered fully-parenthesized like the batch).
    pub const ADD: u8 = 10;
    /// `*`.
    pub const MUL: u8 = 11;
    /// `∘` function composition.
    pub const COMP: u8 = 12;
}

/// The surface family of a [`LeanTerm::Binder`] node — which quantifier /
/// comprehension form to emit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinderKind {
    /// Universal `∀ x, body` (and bounded `∀ x ∈ S, body`).
    Forall,
    /// Existential `∃ x, body` (and bounded `∃ x ∈ S, body`).
    Exists,
    /// Unique existential `∃! x, body` (`ExistsUnique`).
    ExistsUnique,
    /// Set comprehension `{x | body}` (`Set.setOf`).
    SetOf,
}

/// A translated Lean statement fragment as an abstract term, rendered to surface
/// text by [`super::render::render_top`]. Kept structural (not string-first) so
/// parenthesization is decided by context, not guessed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeanTerm {
    /// An atomic token: a bound-variable name, a literal (`0`, `[]`), or a bare
    /// constant. Never parenthesized.
    Atom(String),
    /// A binary infix application `lhs OP rhs` at the given precedence.
    Infix {
        /// The rendered operator (e.g. `"++"`, `"="`, `"∪"`).
        op: &'static str,
        /// The operator precedence (see [`prec`]).
        prec: u8,
        /// Left operand.
        lhs: Box<LeanTerm>,
        /// Right operand.
        rhs: Box<LeanTerm>,
    },
    /// A prefix application `OP arg` (e.g. `¬ p`).
    Prefix {
        /// The rendered prefix operator.
        op: &'static str,
        /// The operand.
        arg: Box<LeanTerm>,
    },
    /// Lean dot-notation `recv.name arg₁ … argₙ` (e.g. `xs.map f`,
    /// `xs.reverse`). Binds tighter than any infix.
    Method {
        /// The receiver (Isabelle's *last* argument).
        recv: Box<LeanTerm>,
        /// The projection / method name (without the leading dot).
        name: &'static str,
        /// The method arguments (Isabelle's leading arguments, in order).
        args: Vec<LeanTerm>,
    },
    /// A plain prefix function application `head arg₁ … argₙ` (used for the rare
    /// higher-order variable application and named prefix constants).
    App {
        /// The applied head token.
        head: String,
        /// The arguments.
        args: Vec<LeanTerm>,
    },
    /// An object-level binder: a quantifier (`∀ x, body`, `∃ x, body`,
    /// `∃! x, body`, bounded `∀ x ∈ S, body` / `∃ x ∈ S, body`) or a set
    /// comprehension (`{x | body}`). Opened from an Isabelle `Abs` predicate by a
    /// capture-safe de Bruijn instantiation (see [`super::term::open_abs`]). Binds
    /// looser than every infix — the render layer parenthesizes it whenever it is
    /// an operand, argument, or receiver, so `(∀ x, P x) ∧ Q` stays faithful.
    Binder {
        /// Which surface form to emit.
        kind: BinderKind,
        /// The capture-safe bound-variable name.
        var: String,
        /// A concrete type annotation (`∀ x : ℕ, …`), emitted only when the
        /// Isabelle domain renders to a variable-free concrete type; `None`
        /// leaves the domain to Lean inference (`∀ x, …`).
        ty: Option<String>,
        /// The bounding set of a bounded quantifier (`∀ x ∈ dom, …`); `None` for
        /// the unbounded and set-comprehension forms.
        dom: Option<Box<LeanTerm>>,
        /// The binder body (rendered maximally to the right).
        body: Box<LeanTerm>,
    },
}

impl LeanTerm {
    /// A bare atom from anything `Into<String>`.
    pub fn atom(s: impl Into<String>) -> Self {
        LeanTerm::Atom(s.into())
    }

    /// A binary infix node.
    pub fn infix(op: &'static str, prec: u8, lhs: LeanTerm, rhs: LeanTerm) -> Self {
        LeanTerm::Infix {
            op,
            prec,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    /// A dot-notation method node.
    pub fn method(recv: LeanTerm, name: &'static str, args: Vec<LeanTerm>) -> Self {
        LeanTerm::Method {
            recv: Box::new(recv),
            name,
            args,
        }
    }
}

/// Why a proposition could not be rendered to a faithful Lean statement. Each
/// variant names a *first-class* declined shape — the harness returns one of
/// these rather than emitting a guessed statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Unsupported {
    /// An Isabelle constant with no faithful Lean rendering in the pattern
    /// library (carries the constant name).
    UnknownConst(String),
    /// A hypothesis / premise that is a type-class or locale predicate
    /// (`group_add …`, `OFCLASS …`): faithfully rendering the class hop needs
    /// domain knowledge the statement alone does not carry.
    ClassPremise(String),
    /// An order comparison (`≤`/`<`) over a bare type variable: the correct Lean
    /// order typeclass (`Preorder`/`PartialOrder`/`LinearOrder`) is not
    /// determined by the statement, so any choice would be a guess.
    PolymorphicOrder,
    /// A lattice operator (`sup`/`inf`/`bot`/`top`/`Sup`/`Inf`) over a non-`Set`
    /// carrier: the generic lattice rendering is not statement-determined.
    PolymorphicLattice(String),
    /// `gcd`/`lcm` over a carrier other than `ℕ`: on a bare type variable the
    /// Lean `gcd`-class instance is not statement-determined, and on `ℤ` Lean's
    /// `Int.gcd : ℤ → ℤ → ℕ` changes the result type (not a faithful drop-in for
    /// Isabelle `gcd :: 'a ⇒ 'a ⇒ 'a`). Only the `ℕ` instance renders
    /// (`Nat.gcd`/`Nat.lcm`); every other carrier is declined.
    NonNatGcd(String),
    /// `size`/`length` applied to a non-list argument (the polymorphic `size`
    /// class does not map to a single Lean function off-lists).
    NonListSize,
    /// A higher-order shape (a `λ`/`Abs`, a `Bound` variable outside a supported
    /// binder, an object quantifier) the library does not render.
    HigherOrder,
    /// A curried operator applied to fewer arguments than it needs (a point-free
    /// / section form).
    PartialApplication(String),
    /// The meta-level (`Pure`) skeleton is a shape the peeler does not handle
    /// (e.g. `Pure.all`, a nested non-`Trueprop` premise).
    MetaShape,
    /// A type mentioning a schematic/free type variable the greek map cannot
    /// name (beyond `'a…'j`), or an unrenderable type former.
    UnrenderableType(String),
}

impl std::fmt::Display for Unsupported {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Unsupported::UnknownConst(n) => write!(f, "unknown-const:{n}"),
            Unsupported::ClassPremise(n) => write!(f, "class-premise:{n}"),
            Unsupported::PolymorphicOrder => write!(f, "polymorphic-order"),
            Unsupported::PolymorphicLattice(n) => write!(f, "polymorphic-lattice:{n}"),
            Unsupported::NonNatGcd(n) => write!(f, "non-nat-gcd:{n}"),
            Unsupported::NonListSize => write!(f, "non-list-size"),
            Unsupported::HigherOrder => write!(f, "higher-order"),
            Unsupported::PartialApplication(n) => write!(f, "partial-application:{n}"),
            Unsupported::MetaShape => write!(f, "meta-shape"),
            Unsupported::UnrenderableType(t) => write!(f, "unrenderable-type:{t}"),
        }
    }
}

/// The outcome of translating one theorem `prop` to a Lean statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeanGoal {
    /// A faithful Lean statement was produced.
    Supported(SupportedGoal),
    /// The shape is outside the pattern library — a first-class decline.
    Unsupported(Unsupported),
}

/// A successfully translated goal: the theorem name plus the rendered signature
/// (`theorem NAME BINDERS :\n    BODY`, with no proof).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SupportedGoal {
    /// The Lean theorem name (last dotted component of the Isabelle name, or an
    /// explicit override).
    pub name: String,
    /// The full signature text up to (not including) `:=`.
    pub signature: String,
}

impl SupportedGoal {
    /// The signature followed by a `:= by sorry` stub, ready to drop into a
    /// batch submission file for human/agent proof curation.
    #[must_use]
    pub fn sorry_stub(&self) -> String {
        format!("{} := by\n  sorry\n", self.signature)
    }
}
