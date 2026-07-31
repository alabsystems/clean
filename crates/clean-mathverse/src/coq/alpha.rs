// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq SerAPI s-expression parser and CIC term importer.
//!
//! Parses Coq SerAPI output (s-expressions), converts CIC terms to the
//! Mathverse flat format, and writes constants to `.mathverse` shards.
//!
//! # Sort / universe model (fail-closed homomorphism)
//!
//! Coq sorts map into Clean's kernel levels as follows. This is a deliberate,
//! RECORDED collapse — anything outside it is OUT OF MODEL and fails closed
//! (the constant's value is dropped loudly and the constant is trust-gated):
//!
//! | Coq sort                          | Importer encoding      | Kernel level |
//! |-----------------------------------|------------------------|--------------|
//! | `Prop`                            | `(Sort Prop)`          | `Sort 0`     |
//! | `Set`                             | `(Sort Set)`           | `Sort 1`     |
//! | monomorphic `Type@{single level}` | `(Sort (Type 1))`      | `Sort 1`     |
//! | template `Type@{max(l1,…,ln)}` of NAMED global levels, all increments 0 | `(Sort (Type 1))` | `Sort 1` |
//! | `Type@{max(arms)}`, increment-aware: `level = max(1, max_arms(base+incr))`, `base(Set)=0`, `base(named)=1` | `(Sort (Type level))` | `Sort level` |
//! | `SProp`                           | OUT OF MODEL           | —            |
//! | bound level variables (`Var _`, universe polymorphism) | OUT OF MODEL | — |
//! | non-empty universe `Instance`s on `Const`/`Ind`/`Construct` | OUT OF MODEL | — |
//!
//! The template row is NOT a new coercion class: TEMPLATE-POLYMORPHIC
//! inductive arities (`prod`, `sum`, `sigT`, …) end in
//! `Type@{max(l1,…,ln)}` where every `li` is a named global template level.
//! Each named level already collapses to the single model level `Type 1`
//! (row 3), and `max(1,…,1) = 1`, so the n-ary max lands on the SAME kernel
//! point as each of its arms — the inductive imports as a MONOMORPHIC
//! `Type 1` inductive (level-param recursor), exactly like every other
//! Type-valued inductive under the collapse.
//!
//! `Set` and monomorphic `Type@{u}` intentionally land on the SAME kernel
//! level (`Sort 1`, the pilot-proven collapse); the `Set`-vs-`Type` syntactic
//! distinction is preserved in the importer dialect (`(Sort Set)` vs
//! `(Sort (Type 1))`) even though both lower to `Sort 1`. Impredicative-`Set`
//! reliance is therefore unsound to import at `Sort 1`; developments that
//! exploit it fail the kernel re-check (loud fallback), never a silent accept.
//!
//! Out-of-model constants keep their TYPE import when the type itself is
//! in-model after the collapse, but their VALUE is dropped loudly (counted in
//! [`CoqImportStats::value_translation_failed`] with a per-name reason) and
//! the constant is stamped `AxiomProfile::COQ_SPROP` (SProp) or
//! `AxiomProfile::UNIVERSE_INCON` (universe out-of-model) so trust gating
//! withholds it.
//!
//! # SerAPI 8.20 `Level.t` serialization (the pierced `Set` level)
//!
//! Investigated live against `~/.opam/mathverse-serapi` (coq 8.20.0 /
//! sertop 8.20.0+0.20.0), confirmed from the vendored sources:
//!
//! - Coq 8.20's runtime `Univ.Level.t` datum (`RawLevel.t`,
//!   `kernel/univ.ml`) has exactly THREE constructors:
//!   `Set | Level of UGlobal.t | Var of int`.
//! - serlib's `Ser_univ.RawLevel.t` (`serlib_8_20/ser_univ.ml`) declares FIVE:
//!   `SProp | Prop | Set | Level | Var`, and pierces (`SerType.Pierce`, an
//!   `Obj.magic` reinterpretation) the runtime value into that type. OCaml
//!   constant constructors are numbered separately from block constructors,
//!   so the runtime `Set` (constant tag 0) serializes under the serializer's
//!   constant tag 0: the atom `SProp`. `Level`/`Var` (block tags 0/1) align
//!   and print faithfully.
//!
//! Consequences, all UNAMBIGUOUS on this toolchain:
//!
//! - In any `Level.t` datum position (universe `Instance`s, `Type` universe
//!   pairs), the atom `SProp` can ONLY mean the runtime `Set` level — genuine
//!   `SProp`/`Prop` cannot occur there (the runtime type has no such
//!   constructors), and the atoms `Set`/`Prop` can never appear at all.
//! - `Sorts.t` serialization (`(Sort SProp|Prop|Set|(Type …))`) is aligned
//!   (runtime `Sorts.t` = `SProp | Prop | Set | Type | QSort` matches the
//!   serializer) and remains trustworthy as-is.
//!
//! The importer uses this finding in one place: a monomorphic
//! `Sort (Type ((<Set-level> 0)))` (i.e. `Type@{Set}`, which Coq treats as
//! `Set`) is accepted and collapses to `(Type 1)` = kernel `Sort 1`, exactly
//! like `Set`. Single-`Set`-level universe INSTANCES on
//! `Const`/`Ind`/`Construct` (a polymorphic reference instantiated at `Set`)
//! are also recognized and given a precise fail-closed reason, but are NOT
//! yet whitelisted into a translated term: carrying the level list requires a
//! level-bearing `CicTerm` reference variant, and extending `CicTerm` (or the
//! `CicCase`/`CicStructFix` payloads) breaks exhaustive matches and struct
//! literals in `coq/proof.rs` / `coq/universe.rs`, which are outside this
//! module's ownership. The drop stays loud and counted either way.
//!
//! # Well-founded recursion (`Acc` / `Fix_F`) — non-uniform demotion landed 2026-07-05
//!
//! 1. **`Acc` replays via non-uniform-parameter demotion (LANDED).** The Coq
//!    8.20 dump declares `Acc` with `NumParams 3` (`A`, `R`, **`x`**) where `x`
//!    is a NON-UNIFORM parameter: `Acc_intro`'s recursive field has type
//!    `Π y, R y x → Acc A R y` — the third parameter position varies
//!    (`y ≠ x`). Clean's kernel `add_inductive` enforces an EXACT parameter
//!    spine on every embedded occurrence (`validate_inductive_strict`,
//!    `crates/clean-kernel/src/inductive/strict.rs` — the Lean
//!    `is_valid_ind_app` rule), so a declared non-uniform parameter is
//!    rejected (`Constructor Coq.Init.Wf.Acc.0.0 return type parameter at index
//!    2 does not match declared parameter`). [`compute_uniform_num_params`]
//!    now DETECTS this — a parameter re-instantiated with a non-`Rel` value in
//!    any recursive occurrence — and DEMOTES the non-uniform suffix to indices
//!    (`num_params 3 → 2`, the Lean-shaped `Acc`). The replay then accepts and
//!    `Acc.0` mints KernelVerified; the whole `Wellfounded`/`Relation_Operators`
//!    (`clos_*`)/`Sets.Relations_2/3` cascade + `ConstructiveEpsilon` unlocks
//!    (measured 2026-07-05: stdlib KernelVerified 7,678 → 7,818, +140, 0
//!    regressions). Constants that `match` on `Acc` still fail closed — the
//!    dump's `Case` carries `ci_npar 3` while the registry now holds 2, so the
//!    `Case` handler rejects them loudly (`ci_npar disagrees with the
//!    registered inductive`); Case reparameterization on demoted inductives is
//!    the next piece (see (2)).
//! 2. **`Fix_F`'s recursion is not a match on the struct argument.** Its
//!    body is `F x (λ y h. Fix_F y (Acc_inv A R x a y h))` — there is no
//!    `Case` node at all: the structural evidence flows through the
//!    DEFINITION `Acc_inv` (a projection wrapping the match), and self-calls
//!    change the PRE-struct argument `x` (rejected in both fix encodings:
//!    pre-struct arguments are recursor parameters). Lowering to `Acc.rec`
//!    needs the motive `λ x a. P x` and the minor's IH
//!    `Π y, R y x → P y`, with self-calls `Fix_F y h'` mapped to `IH y h''`
//!    where `h''` is recovered from the `Acc_inv` application — a dedicated
//!    recognizer. `Fix_F`-shaped constants keep their precise fail-closed drop
//!    reason (`Fix: body is not a lambda spine ending in a match on the
//!    structural argument`, …) and stay loud in the corpus report.
//!
//! # Indexed matches (eq-rewrite shapes)
//!
//! A `Case` on an INDEXED inductive family (return predicate binding
//! `1 + nrealargs` variables: the indices then the scrutinee, outermost
//! first — verified live against sertop 8.20) lowers to the kernel recursor
//! spine `params → motive → minors → indices → major`
//! (`RecursorArgOrder::MajorAfterMinors`). The index terms are not stored in
//! the compact `Case` node; they are recovered SYNTACTICALLY from the
//! discriminant's type (binding-site binder type for a `Rel` discriminant,
//! lifted to the `Case` site; `Cast` annotation type otherwise) and
//! cross-checked against the registered arity. Anything unrecoverable fails
//! closed. Because the kernel's `add_inductive` replay can promote FIXED
//! indices to parameters (`fixed_indices_to_params`), which changes the
//! recursor's argument boundary, the importer mirrors that promotion
//! syntactically and fails closed on any inductive where promotion would
//! fire (`eq` provably does not promote: its index is not fixed).

use clean_kernel::flat::{FlatExpr, FlatLevel};

use crate::error::{MathverseError, MathverseResult};
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

/// A parsed s-expression: either an atom or a list.
#[derive(Clone, Debug, PartialEq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

/// Errors from s-expression parsing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SexpError {
    UnexpectedEof,
    UnexpectedChar(char, usize),
    UnmatchedParen(usize),
}

impl std::fmt::Display for SexpError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedEof => write!(f, "unexpected end of input"),
            Self::UnexpectedChar(c, pos) => write!(f, "unexpected char '{c}' at position {pos}"),
            Self::UnmatchedParen(pos) => write!(f, "unmatched parenthesis at position {pos}"),
        }
    }
}
impl std::error::Error for SexpError {}

/// Parse a single s-expression from `input`.
pub fn parse_sexp(input: &str) -> Result<Sexp, SexpError> {
    let tokens = tokenize(input)?;
    let mut pos = 0;
    parse_one(&tokens, &mut pos)
}

/// Parse multiple top-level s-expressions from `input`.
pub(crate) fn parse_sexps(input: &str) -> Result<Vec<Sexp>, SexpError> {
    let tokens = tokenize(input)?;
    let (mut pos, mut out) = (0, Vec::new());
    while pos < tokens.len() {
        out.push(parse_one(&tokens, &mut pos)?);
    }
    Ok(out)
}

#[derive(Clone, Debug)]
enum Token {
    Open(usize),
    Close(usize),
    Atom(String),
}

fn tokenize(input: &str) -> Result<Vec<Token>, SexpError> {
    let mut tokens = Vec::new();
    let b = input.as_bytes();
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b' ' | b'\t' | b'\n' | b'\r' => i += 1,
            b'(' => {
                tokens.push(Token::Open(i));
                i += 1;
            }
            b')' => {
                tokens.push(Token::Close(i));
                i += 1;
            }
            b'"' => {
                i += 1;
                let mut s = String::new();
                while i < b.len() && b[i] != b'"' {
                    if b[i] == b'\\' && i + 1 < b.len() {
                        i += 1;
                        match b[i] {
                            b'n' => s.push('\n'),
                            b't' => s.push('\t'),
                            b'\\' => s.push('\\'),
                            b'"' => s.push('"'),
                            o => {
                                s.push('\\');
                                s.push(o as char);
                            }
                        }
                    } else {
                        s.push(b[i] as char);
                    }
                    i += 1;
                }
                if i >= b.len() {
                    return Err(SexpError::UnexpectedEof);
                }
                i += 1;
                tokens.push(Token::Atom(s));
            }
            b';' => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
            }
            _ => {
                let mut s = String::new();
                while i < b.len()
                    && !matches!(b[i], b' ' | b'\t' | b'\n' | b'\r' | b'(' | b')' | b'"')
                {
                    s.push(b[i] as char);
                    i += 1;
                }
                tokens.push(Token::Atom(s));
            }
        }
    }
    Ok(tokens)
}

fn parse_one(tokens: &[Token], pos: &mut usize) -> Result<Sexp, SexpError> {
    if *pos >= tokens.len() {
        return Err(SexpError::UnexpectedEof);
    }
    match &tokens[*pos] {
        Token::Open(off) => {
            let open = *off;
            *pos += 1;
            let mut ch = Vec::new();
            loop {
                if *pos >= tokens.len() {
                    return Err(SexpError::UnmatchedParen(open));
                }
                if matches!(tokens[*pos], Token::Close(_)) {
                    *pos += 1;
                    return Ok(Sexp::List(ch));
                }
                ch.push(parse_one(tokens, pos)?);
            }
        }
        Token::Close(off) => Err(SexpError::UnexpectedChar(')', *off)),
        Token::Atom(s) => {
            *pos += 1;
            Ok(Sexp::Atom(s.clone()))
        }
    }
}

/// Coq Calculus of Inductive Constructions term.
#[derive(Clone, Debug)]
pub enum CicTerm {
    Rel(u32),
    Var(String),
    Sort(CicSort),
    Prod(String, Box<CicTerm>, Box<CicTerm>),
    Lambda(String, Box<CicTerm>, Box<CicTerm>),
    LetIn(String, Box<CicTerm>, Box<CicTerm>, Box<CicTerm>),
    App(Box<CicTerm>, Vec<CicTerm>),
    Const(String),
    /// A `Const` reference carrying an EXPLICIT universe-level instance — a
    /// reference to a universe-polymorphic constant applied at the given
    /// levels (in the constant's `level_params` order). Produced by the
    /// SerAPI adapter's fully-quality-specialized instance translation (see
    /// `translate_poly_ref_instance`); lowers to a `const_ref` with a real
    /// level list instead of the level-free `u32::MAX` sentinel.
    ConstU(String, Vec<CoqUniverseLevel>),
    Ind(String, u32),
    Construct(String, u32, u32),
    /// A Coq `match` (pattern match) expression.
    ///
    /// The Calculus of Inductive Constructions has no primitive `match`: every
    /// `match` is definitionally an application of the matched inductive's
    /// *recursor* (eliminator). Clean's kernel mirrors this — it has no native
    /// match `Expr`, only recursors auto-generated by `add_inductive`. So this
    /// node lowers (in [`cic_to_flat_expr`]) to an application of `<ind>.rec`:
    /// `@<ind>.rec <params...> <motive> <branch_0> ... <branch_n> <discriminant>`,
    /// matching the kernel recursor's standard
    /// `params → motive → minors → indices → major` argument order
    /// ([`clean_kernel::inductive::RecursorArgOrder::MajorAfterMinors`]).
    Case(Box<CicCase>),
    Fix(Vec<(String, Box<CicTerm>, Box<CicTerm>)>, u32),
    CoFix(Vec<(String, Box<CicTerm>, Box<CicTerm>)>, u32),
    /// A Coq structural fixpoint (`fix f args {struct k} := …`) in the
    /// importer's structured form.
    ///
    /// The Calculus of Inductive Constructions has no primitive recursive
    /// definition: structural recursion on an argument of inductive type `I` is
    /// definitionally an application of `I`'s *recursor* (eliminator), where the
    /// recursive self-call on the structurally-smaller predecessor is supplied
    /// by the recursor as each minor premise's induction-hypothesis argument.
    /// Clean's kernel mirrors this exactly — it has NO native fix node and NO
    /// recursive-definition-by-name; recursion exists ONLY through the recursors
    /// `add_inductive` auto-generates (with iota reduction). So a [`CicStructFix`]
    /// lowers (in [`cic_to_flat_expr`]) to the outer binder lambdas wrapped
    /// around an `<ind>.<idx>.rec` application
    ///   `λ pre… struct post…. @<ind>.<idx>.rec.{u} <params…> <motive>
    ///        <branch_0..n> <struct>`,
    /// matching the kernel recursor's `params → motive → minors → major`
    /// argument order ([`clean_kernel::inductive::RecursorArgOrder::MajorAfterMinors`]).
    /// Each recursive minor premise binds the constructor's fields followed by
    /// their induction hypotheses; a recursive self-call `f p …` becomes a
    /// reference to that hypothesis. The kernel typechecks the elimination and
    /// reduces it (iota), so a recursive definition becomes genuinely
    /// `KernelVerified`.
    StructFix(Box<CicStructFix>),
    /// Primitive projection `(Proj <struct-name> <field-idx> <record>)`.
    /// `struct-name` is the record inductive (Coq `proj_ind`); `field-idx` is
    /// Coq's own 0-based field index (`proj_arg`). Lowers to the kernel
    /// `Proj(struct_name, field_idx, record)`, which resolves the field type
    /// from that inductive's single constructor and re-checks the projection.
    Proj(String, u32, Box<CicTerm>),
    Int(i64),
    Float(f64),
}

/// The structured payload of a Coq `Case` (pattern match), carrying everything
/// the recursor application needs: the matched inductive, its parameter
/// arguments, the return-predicate (motive), the per-constructor branches (which
/// become the recursor's minor premises) and the discriminant (major premise).
#[derive(Clone, Debug)]
pub struct CicCase {
    /// The matched inductive's name and mutual-block index (e.g. `("or", 0)`).
    /// The recursor referenced is `<ind_name>.<ind_idx>.rec`.
    pub ind_name: String,
    pub ind_idx: u32,
    /// Parameter arguments of the inductive (e.g. `A`, `B` for `or A B`). These
    /// are the recursor's leading explicit arguments.
    pub params: Vec<CicTerm>,
    /// The return predicate / motive: a function from the discriminant (and any
    /// indices) to the result `Sort`. Each branch's body and the overall result
    /// are checked against this.
    pub motive: Box<CicTerm>,
    /// One branch per constructor, in constructor order, already abstracted over
    /// the constructor's fields (i.e. each is a `λ field_0 … field_k. body`).
    /// These are the recursor's minor premises.
    pub branches: Vec<CicTerm>,
    /// The scrutinee being matched (the recursor's major premise).
    pub discriminant: Box<CicTerm>,
}

/// The structured payload of a Coq structural fixpoint (`fix f … {struct k}`),
/// carrying everything the recursor application needs to encode the recursion.
///
/// A structural `Fix` recurses on one argument of inductive type `I`. It lowers
/// to `I`'s recursor applied under the function's binder lambdas (see
/// [`CicTerm::StructFix`]). The recursive self-call is provided by the recursor
/// as each minor premise's induction-hypothesis argument, so the branch bodies
/// are written referencing those hypotheses rather than the (nonexistent)
/// recursive constant — exactly as the kernel's iota rule expects.
#[derive(Clone, Debug)]
pub struct CicStructFix {
    /// The recursion inductive's name and mutual-block index (e.g. `("nat", 0)`).
    /// The recursor referenced is `<ind_name>.<ind_idx>.rec`.
    pub ind_name: String,
    pub ind_idx: u32,
    /// Universe level of the recursor's motive instance — the level of the
    /// motive's result sort. For a `nat → nat` fixpoint the motive returns
    /// `nat : Set = Sort 1`, so this is `1`. Lowered to a one-element level list
    /// on the recursor `Const` reference. Ignored when [`Self::prop_only`].
    pub rec_level: u32,
    /// Recursion over a Prop-ONLY-eliminating inductive (`le`, `between`:
    /// Prop with multiple constructors). Its `<ind>.<idx>.rec` takes NO
    /// motive universe parameter (the kernel's `build_recursor` drops the
    /// motive level param when elimination is restricted to Prop), so the
    /// lowering emits an EMPTY universe instance instead of a
    /// [`Self::rec_level`] singleton. Parsed from the `(RecLevel Prop)` atom.
    pub prop_only: bool,
    /// Parameter arguments of the recursion inductive (the recursor's leading
    /// explicit arguments). Empty for non-parameterized inductives like `nat`.
    pub params: Vec<CicTerm>,
    /// Binder types of the function's arguments *before* the structural argument
    /// (lambda-bound around the recursor application).
    pub pre_binders: Vec<CicTerm>,
    /// Type of the structural (decreasing) argument — itself an application of
    /// the recursion inductive.
    pub struct_ty: Box<CicTerm>,
    /// Binder types of the function's arguments *after* the structural argument.
    pub post_binders: Vec<CicTerm>,
    /// Index arguments of the structural argument's inductive type, for an
    /// INDEXED family (`le n m`: the index `m`). The kernel recursor spine is
    /// `params → motive → minors → INDICES → major`, so these are emitted right
    /// before the major premise. Expressed in the recursor-application context
    /// (`[pre, struct, post]`, the wrapper binders). Empty for a non-indexed
    /// inductive (`nat`, `list`), keeping the historical lowering unchanged.
    pub indices: Vec<CicTerm>,
    /// The recursor's return predicate / motive.
    pub motive: Box<CicTerm>,
    /// One branch per constructor, in constructor order, abstracted over the
    /// constructor's fields *and* their induction hypotheses (the recursor's
    /// minor premises). A recursive self-call becomes a reference to a hypothesis.
    pub branches: Vec<CicTerm>,
}

/// Coq sort (universe) classification.
#[derive(Clone, Debug, PartialEq)]
pub enum CicSort {
    Prop,
    Set,
    /// A `Type@{ℓ}` sort carrying its universe level STRUCTURALLY (see
    /// [`CoqUniverseLevel`]) rather than as a floored `u32`. A concrete
    /// predicative level `Type i` is `CoqUniverseLevel::Type(i)`; algebraic
    /// (`Max`/`Succ`) and polymorphic (`Var`) levels are preserved so the kernel
    /// — not the importer's lossy collapse — decides level equality. Build a
    /// concrete level with [`CicSort::type_at`]; read the concrete index (when
    /// the level is a plain `Type i`) with [`CicSort::type_level_nat`].
    Type(CoqUniverseLevel),
}

impl CicSort {
    /// A concrete predicative `Type i` sort.
    pub fn type_at(i: u32) -> Self {
        CicSort::Type(CoqUniverseLevel::Type(i))
    }

    /// The concrete predicative index of a `Type i` sort, if this is one and its
    /// level is a plain concrete `Type i` (not an algebraic/polymorphic level).
    /// `Prop`/`Set` and structural levels return `None`.
    pub(crate) fn type_level_nat(&self) -> Option<u32> {
        match self {
            CicSort::Type(l) => l.as_concrete_type(),
            _ => None,
        }
    }
}

impl CoqUniverseLevel {
    /// The concrete predicative index `i` if this level is a plain `Type i`
    /// (equivalently a `Succ^i(base)` reducing to a fixed nat); `None` for
    /// polymorphic (`Var`) or algebraic (`Max`) levels the importer must not
    /// flatten. `Set` is `Type 0`; `Prop` has no predicative `Type` index.
    pub(crate) fn as_concrete_type(&self) -> Option<u32> {
        match self {
            CoqUniverseLevel::Type(i) => Some(*i),
            CoqUniverseLevel::Set => Some(0),
            CoqUniverseLevel::Succ(inner) => inner.as_concrete_type().map(|i| i + 1),
            CoqUniverseLevel::Prop | CoqUniverseLevel::Var(_) | CoqUniverseLevel::Max(_) => None,
        }
    }
}

/// Normalize a raw SerAPI `Constr` s-expression into the importer's canonical
/// CIC dialect that [`sexp_to_cic`] consumes.
///
/// `sertop`'s `(Query () (Definition X))` serializes the *elaborated kernel
/// term* using its native, verbose encoding (binder annotations as records,
/// `MutInd`/`Constant` kernel names wrapped in `KerName`/`Instance`, `App`
/// arguments grouped in a sub-list, de Bruijn indices that are 1-based, and
/// `Sort (Type <universe-expr>)` carrying a full algebraic universe). The
/// importer's hand-curated dialect instead uses `(Lambda <name> ty body)`,
/// flat `App` arguments, bare `(Ind name idx)` / `(Const name)`, 0-based
/// `Rel`, and `(Sort (Type <u32>))`.
///
/// This adapter performs a faithful, purely structural rewrite between the two
/// — it never invents term structure, only re-encodes the shapes SerAPI emits.
/// Nodes already in the importer dialect pass through unchanged, so existing
/// hand-written datasets keep working. Returns `None` when the node is not a
/// recognized SerAPI-native shape (the caller then leaves it untouched).
///
/// Shapes that ARE recognized but cannot be soundly represented (SProp,
/// algebraic/polymorphic universes, `Proj`, `CoFix`, mutual `Fix`,
/// unstructuralizable `Fix`, registry-less `Case`) rewrite to a
/// `(CoqUnsupported "<reason>")` marker that [`sexp_to_cic`] turns into a
/// translation ERROR — the value is then dropped loudly by the importer
/// (never silently mistranslated).
///
/// `bctx` is the de Bruijn context of enclosing binder TYPES (normalized
/// dialect sexps, outermost first; `None` marks a binder whose type could
/// not be tracked). It exists so the `Case` arm can recover the concrete
/// index terms of an INDEXED match from the discriminant's binding-site
/// type, and so motive universe levels can be derived for `Rel`-headed
/// return predicates. Lookups outside the tracked context fail closed.
fn normalize_serapi(sexp: &Sexp, ctx: &SerapiNormCtx, bctx: &[Option<Sexp>]) -> Option<Sexp> {
    let Sexp::List(items) = sexp else {
        return None;
    };
    let head = match items.first() {
        Some(Sexp::Atom(s)) => s.as_str(),
        _ => return None,
    };
    match head {
        // (Lambda/Prod <binder-annot> ty body) where binder-annot is a record
        // list `((binder_name ...)(binder_relevance ...))`. The importer dialect
        // already uses a bare name atom here, so only rewrite the record form.
        "Lambda" | "Prod" if items.len() == 4 => {
            let name = serapi_binder_name(&items[1])?;
            let ty = normalize_serapi_rec(&items[2], ctx, bctx);
            let body_bctx = bctx_push(bctx, Some(ty.clone()));
            Some(Sexp::List(vec![
                Sexp::Atom(head.to_string()),
                Sexp::Atom(name),
                ty,
                normalize_serapi_rec(&items[3], ctx, &body_bctx),
            ]))
        }
        // (LetIn <binder-annot> value type body) — SerAPI order matches the
        // importer dialect's `(LetIn name value type body)`.
        "LetIn" if items.len() == 5 => {
            let name = serapi_binder_name(&items[1])?;
            let ty = normalize_serapi_rec(&items[3], ctx, bctx);
            let body_bctx = bctx_push(bctx, Some(ty.clone()));
            Some(Sexp::List(vec![
                Sexp::Atom("LetIn".to_string()),
                Sexp::Atom(name),
                normalize_serapi_rec(&items[2], ctx, bctx),
                ty,
                normalize_serapi_rec(&items[4], ctx, &body_bctx),
            ]))
        }
        // (Cast <term> DEFAULTcast|VMcast|NATIVEcast <type>): drop the cast and
        // keep the term. Sound because the kernel re-checks the final term
        // against the constant's declared type anyway; the cast carries no
        // computational content.
        "Cast" if items.len() == 4 => Some(normalize_serapi_rec(&items[1], ctx, bctx)),
        // (Sort Prop|Set|SProp|(Type <universe-expr>)) — see the module-level
        // sort-model table. SProp and algebraic/polymorphic universes are OUT
        // OF MODEL and rewrite to a loud `CoqUnsupported` marker.
        "Sort" if items.len() == 2 => Some(normalize_serapi_sort_node(&items[1], ctx)),
        // (Rel k): SerAPI is 1-based, importer dialect is 0-based.
        "Rel" if items.len() == 2 => {
            let k = match &items[1] {
                Sexp::Atom(s) => s.parse::<u32>().ok()?,
                _ => return None,
            };
            Some(Sexp::List(vec![
                Sexp::Atom("Rel".to_string()),
                Sexp::Atom(k.saturating_sub(1).to_string()),
            ]))
        }
        // (Var (Id x)) — section variable reference.
        "Var" if items.len() == 2 => {
            let id = serapi_id_atom(&items[1])?;
            Some(Sexp::List(vec![
                Sexp::Atom("Var".to_string()),
                Sexp::Atom(id),
            ]))
        }
        // (App f (a1 a2 ...)) — SerAPI groups args in a sub-list; flatten it.
        "App" if items.len() == 3 => {
            if let Sexp::List(args) = &items[2] {
                let mut out = vec![
                    Sexp::Atom("App".to_string()),
                    normalize_serapi_rec(&items[1], ctx, bctx),
                ];
                out.extend(args.iter().map(|a| normalize_serapi_rec(a, ctx, bctx)));
                Some(Sexp::List(out))
            } else {
                None
            }
        }
        // (Const ((Constant (KerName ...) ()) (Instance ...))) -> (Const name)
        // with the FULLY-QUALIFIED name (DirPath reversed + Id). Polymorphic
        // universe instances either drop to the monomorphic import
        // (speculatively where the drop is a guess — `Set`-specialized levels,
        // constant-quality specializations; the kernel arbitrates fail-closed
        // via the `SPECULATIVE_MOTIVE` marker) or reject out-of-model.
        "Const" if items.len() == 2 => {
            // A reference to a REGISTERED sort-polymorphic constant (emitted
            // with a real level_params window): translate its instance into
            // the explicit levels of that window instead of stripping it —
            // the decl-consistent other half of the poly emission. The
            // translation is a kernel-arbitrated guess (speculative,
            // fail-closed); an untranslatable instance falls through to
            // today's disposition, whose bare reference the kernel rejects
            // against the poly declaration (also fail-closed).
            if let Some(name) = serapi_qualified_name(&items[1]) {
                if let Some(info) = ctx.poly_const(&name) {
                    if let Some(levels) = translate_poly_ref_instance(&items[1], info) {
                        SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
                        let mut out = vec![Sexp::Atom("ConstU".to_string()), Sexp::Atom(name)];
                        out.extend(levels.iter().map(|l| Sexp::Atom(l.to_string())));
                        return Some(Sexp::List(out));
                    }
                }
            }
            match serapi_ref_instance_disposition(&items[1], "constant") {
                InstanceDisposition::Reject(reason) => return Some(coq_unsupported(&reason)),
                InstanceDisposition::EmitSpeculative => {
                    SPECULATIVE_MOTIVE_USED.with(|c| c.set(true))
                }
                InstanceDisposition::Emit => {}
            }
            let name = resolve_kerpair_name(serapi_qualified_name(&items[1])?, &items[1], ctx);
            Some(Sexp::List(vec![
                Sexp::Atom("Const".to_string()),
                Sexp::Atom(name),
            ]))
        }
        // (Ind (((MutInd (KerName ...) ()) <i>) (Instance ...))) -> (Ind name i)
        "Ind" if items.len() == 2 => {
            match serapi_ref_instance_disposition(&items[1], "inductive") {
                InstanceDisposition::Reject(reason) => return Some(coq_unsupported(&reason)),
                InstanceDisposition::EmitSpeculative => {
                    SPECULATIVE_MOTIVE_USED.with(|c| c.set(true))
                }
                InstanceDisposition::Emit => {}
            }
            let (name, i, _) = serapi_inductive_ref(&items[1])?;
            let name = resolve_ind_family_name(name, &items[1], i, ctx);
            // RECORD-STAND-IN ALIAS (2026-07-11 reject census): sertop 8.20
            // crashes serializing some Hierarchy-Builder record MInds
            // (`Finite.class_of` family), so the dumper salvages them as
            // TYPE-ONLY `(CoqAxiom <name> …)` stand-ins — plain CONSTANTS. A
            // dependent's `(Ind <name> 0)` reference lowers to the inductive
            // spelling `<name>.0`, a name the corpus can then never define;
            // measured: that one spelling mismatch gated every `<X>.type`
            // record family replay (`Pack : ∀sort, class_of sort → type`) and
            // ~15k chained mathcomp failures. When block 0 of the referenced
            // name is NOT a registered inductive anywhere in the session but
            // the SAME qualified name IS a registered sort-codomain constant
            // (exactly the stand-in shape, and impossible for a real imported
            // inductive — the two form namespaces are disjoint per qualified
            // name), alias the reference to the constant spelling so it
            // resolves against the stand-in. The alias is a kernel-arbitrated
            // guess: mark it SPECULATIVE so a rejection fails closed to a
            // clean type-only axiom (never a masked-failure taint).
            if i == 0 && ctx.lookup(&name, 0).is_none() && ctx.lookup_const_sort(&name).is_some() {
                SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
                return Some(Sexp::List(vec![
                    Sexp::Atom("Const".to_string()),
                    Sexp::Atom(name),
                ]));
            }
            Some(Sexp::List(vec![
                Sexp::Atom("Ind".to_string()),
                Sexp::Atom(name),
                Sexp::Atom(i.to_string()),
            ]))
        }
        // (Construct ((((MutInd ...) ()) <i>) <j>) (Instance ...)) ->
        // (Construct name i (j-1)); SerAPI constructor index is 1-based.
        "Construct" if items.len() == 2 => {
            match serapi_ref_instance_disposition(&items[1], "constructor") {
                InstanceDisposition::Reject(reason) => return Some(coq_unsupported(&reason)),
                InstanceDisposition::EmitSpeculative => {
                    SPECULATIVE_MOTIVE_USED.with(|c| c.set(true))
                }
                InstanceDisposition::Emit => {}
            }
            let (name, i, j) = serapi_construct_ref(&items[1])?;
            let name = resolve_ind_family_name(name, &items[1], i, ctx);
            Some(Sexp::List(vec![
                Sexp::Atom("Construct".to_string()),
                Sexp::Atom(name),
                Sexp::Atom(i.to_string()),
                Sexp::Atom(j.saturating_sub(1).to_string()),
            ]))
        }
        // Coq 8.20 compact Case — converted to the dialect `(Case ...)` (for
        // Prop-only-eliminating inductives) or to an explicit
        // `@<ind>.rec.{u}` application spine (for level-parameterized
        // recursors). Requires the matched inductive's constructor types from
        // the import-session registry; otherwise fails closed.
        "Case" if items.len() == 8 => Some(match convert_serapi_case(items, ctx, bctx) {
            Ok(pieces) => assemble_case_sexp(&pieces),
            Err(reason) => coq_unsupported(&reason),
        }),
        // Structural single fixpoint `(Fix ((<rec-indices>) <which>)
        // ((<annots>)(<types>)(<bodies>)))` — SerAPI wraps both payloads in
        // ONE argument list, so the node has arity 2. Structuralized into the
        // dialect `(StructFix ...)` recursor encoding; every unrecognized
        // shape fails closed (mutual fixpoints, non-structural recursion,
        // self-calls that are not exact structural-predecessor
        // applications, ...).
        "Fix" if items.len() == 2 => Some(match convert_serapi_fix(items, ctx, bctx) {
            Ok(sf) => sf,
            Err(reason) => coq_unsupported(&reason),
        }),
        // Corecursion has no recursor encoding in Clean's kernel: out of model.
        "CoFix" => Some(coq_unsupported(
            "corecursive CoFix value has no recursor encoding (out of model)",
        )),
        // Primitive projection. The patched dumper (sertop-projfix; see
        // docker/coq-linux-runner/serlib-projfix.patch) serializes it as
        //   (Proj (((proj_ind <ind>) (proj_npars N) (proj_arg K)
        //           (proj_name (Constant <kn>))) <unfolded:bool>)
        //         <relevance> <record-term>)
        // — the same shape the `.vo` replay path emits (vo/constr_sexp.rs).
        // Translate it to the importer-dialect
        //   (Proj <struct-name> <field-idx> <record-term>)
        // where <struct-name> is the record inductive (proj_ind) and
        // <field-idx> is Coq's own 0-based field index (proj_arg). The kernel
        // resolves the field type from that inductive's single constructor and
        // re-checks the projection, so a faithful translation is genuinely
        // KernelVerified and a misresolved one fails closed. The proj_arg ->
        // kernel-field-idx identification is a kernel-arbitrated assumption
        // (accept = KV, reject = clean type-only), so the emission is marked
        // SPECULATIVE_MOTIVE inside `convert_serapi_proj`.
        "Proj" if items.len() == 4 => Some(match convert_serapi_proj(items, ctx, bctx) {
            Ok(node) => node,
            Err(reason) => coq_unsupported(&reason),
        }),
        // Unrecognized `Proj` arity: not the projfix/.vo shape. Fail closed.
        "Proj" => Some(coq_unsupported(
            "primitive projection (Proj) with unrecognized SerAPI arity (fail closed)",
        )),
        // Elaboration leftovers must never reach the kernel importer.
        "Evar" | "Meta" => Some(coq_unsupported(
            "unresolved Evar/Meta in kernel term (elaboration leftover)",
        )),
        _ => None,
    }
}

/// Extend a de Bruijn binder-type context by one entry (outermost first).
fn bctx_push(bctx: &[Option<Sexp>], entry: Option<Sexp>) -> Vec<Option<Sexp>> {
    let mut out = Vec::with_capacity(bctx.len() + 1);
    out.extend_from_slice(bctx);
    out.push(entry);
    out
}

/// Look up the TYPE of `Rel r` (0-based, dialect) in a binder-type context.
/// `None` when the binder is out of range or untracked (fail closed).
fn bctx_lookup(bctx: &[Option<Sexp>], r: u32) -> Option<&Sexp> {
    bctx.len()
        .checked_sub(1 + r as usize)
        .and_then(|i| bctx[i].as_ref())
}

/// Apply [`normalize_serapi`] recursively, leaving importer-dialect nodes as-is.
///
/// Only invoked once the whole term has been classified as SerAPI-native by
/// [`is_serapi_native`]. This matters for `Rel`/`App`, whose syntax is shared
/// with the importer dialect but whose semantics differ (SerAPI `Rel` is
/// 1-based and `App` groups its arguments) — normalizing a hand-written
/// importer term would corrupt it, so the classifier gates this entry point.
///
/// The blind structural fallback (unrecognized list shapes) recurses with an
/// EMPTY binder context: an unrecognized shape could bind variables we cannot
/// see, so any binder-type lookup below it must fail closed rather than hit a
/// misaligned entry. Well-formed SerAPI kernel terms never take this path
/// (every `Constr` node shape is recognized above).
fn normalize_serapi_rec(sexp: &Sexp, ctx: &SerapiNormCtx, bctx: &[Option<Sexp>]) -> Sexp {
    if let Some(rewritten) = normalize_serapi(sexp, ctx, bctx) {
        return rewritten;
    }
    match sexp {
        Sexp::Atom(_) => sexp.clone(),
        Sexp::List(items) => Sexp::List(
            items
                .iter()
                .map(|i| normalize_serapi_rec(i, ctx, &[]))
                .collect(),
        ),
    }
}

/// Apply the SerAPI adapter only when the term is unambiguously SerAPI-native,
/// otherwise return it unchanged so existing importer-dialect data is preserved.
fn normalize_if_serapi_ctx(sexp: &Sexp, ctx: &SerapiNormCtx) -> Sexp {
    if is_serapi_native(sexp) {
        normalize_serapi_rec(sexp, ctx, &[])
    } else {
        sexp.clone()
    }
}

/// Detect whether a term uses raw SerAPI `Constr` encoding, identified by
/// markers absent from the importer dialect: binder-annotation records
/// (`binder_name`/`binder_relevance`), kernel-name wrappers (`KerName`,
/// `MutInd`, `MutConstruct`, `Constant`), universe `Instance` nodes, or a
/// SerAPI universe-level payload (`(hash …)`/`(data …)` fields — the importer
/// dialect writes universes as a bare `(Type N)` atom and never uses these).
///
/// The universe-payload markers matter for terms whose ONLY SerAPI content is
/// a bare `(Sort (Type <payload>))` with no surrounding binder/kername node —
/// e.g. `Definition predArgType := Type` or a record arity like
/// `ConstructiveReals : Type@{Set+1}`. Without them such a sort skips
/// normalization and reaches `sexp_to_cic` raw, failing with a misleading
/// "expected atom at 1" instead of going through the universe classifier.
fn is_serapi_native(sexp: &Sexp) -> bool {
    match sexp {
        Sexp::Atom(_) => false,
        Sexp::List(items) => {
            if let Some(Sexp::Atom(h)) = items.first() {
                if matches!(
                    h.as_str(),
                    "binder_name"
                        | "binder_relevance"
                        | "KerName"
                        | "MutInd"
                        | "MutConstruct"
                        | "Constant"
                        | "Instance"
                        | "hash"
                        | "data"
                ) {
                    return true;
                }
            }
            items.iter().any(is_serapi_native)
        }
    }
}

/// Extract a binder name from a SerAPI binder annotation record
/// `((binder_name (Name (Id x))) (binder_relevance ...))` or `... Anonymous`.
/// Returns `None` for already-canonical bare name atoms.
fn serapi_binder_name(sexp: &Sexp) -> Option<String> {
    let Sexp::List(fields) = sexp else {
        return None;
    };
    let mut saw_binder_name = false;
    for field in fields {
        if let Sexp::List(kv) = field {
            if matches!(kv.first(), Some(Sexp::Atom(k)) if k == "binder_name") {
                saw_binder_name = true;
                if let Some(id) = kv.get(1).and_then(serapi_name_atom) {
                    return Some(id);
                }
            }
        }
    }
    // Recognized as a SerAPI binder record (e.g. Anonymous) but with no Id.
    saw_binder_name.then(|| "_".to_string())
}

/// Extract the identifier from `(Name (Id x))` / `Anonymous`.
fn serapi_name_atom(sexp: &Sexp) -> Option<String> {
    match sexp {
        Sexp::Atom(s) if s == "Anonymous" => Some("_".to_string()),
        Sexp::List(v) => {
            // (Name (Id x))
            if matches!(v.first(), Some(Sexp::Atom(h)) if h == "Name") {
                if let Some(Sexp::List(idv)) = v.get(1) {
                    if matches!(idv.first(), Some(Sexp::Atom(h)) if h == "Id") {
                        if let Some(Sexp::Atom(name)) = idv.get(1) {
                            return Some(name.clone());
                        }
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// The `(CoqUnsupported "<reason>")` fail-closed marker. [`sexp_to_cic`]
/// turns it into a translation error carrying the reason, so an out-of-model
/// shape is always dropped LOUDLY, never silently mistranslated.
fn coq_unsupported(reason: &str) -> Sexp {
    Sexp::List(vec![
        Sexp::Atom("CoqUnsupported".to_string()),
        Sexp::Atom(reason.to_string()),
    ])
}

/// Normalize a SerAPI `(Sort <payload>)` node per the module-level sort model.
///
/// `Prop`/`Set` pass through. A monomorphic `Type@{single global level}`
/// collapses to the importer `(Type 1)` level: in `cic_to_flat_expr` an
/// importer `(Type u)` lowers to `Zero` followed by `u` successors, so
/// `(Type 1)` lands at `Sort(Succ Zero)` — the level of `Set` and of small
/// concrete data types like `nat`/`bool` — matching the hand-curated
/// inductive closures which declare `(A : Type)` parameters at
/// `(Sort (Type 1))` (collapsing to `(Type 0)` = `Sort Zero` = `Prop`
/// undershot the level and the kernel rejected the terms).
///
/// SProp and algebraic/polymorphic universes are OUT OF MODEL: they rewrite
/// to the loud `CoqUnsupported` marker (SProp has no proof-irrelevant sort
/// here, and a `max`/`+1`/`Var` universe carries structure the single
/// collapsed level cannot faithfully represent).
///
/// EXCEPTION (sort polymorphism, `ssr_have_upoly` class): when the import
/// loop derived a [`CoqSortPolyShape`] for the CURRENT declaration
/// (`ctx.current_poly`), a `QSort` payload whose (quality var, level var)
/// pair the shape recorded rewrites to the dialect `(Sort (Param u<q>))` —
/// the Lean-fused `Level::Param` encoding of `Sort@{q|u}` — and marks the
/// declaration SPECULATIVE so a kernel rejection fails closed to a clean
/// type-only axiom. Any `QSort` outside the recorded pairing stays
/// out-of-model.
fn normalize_serapi_sort_node(payload: &Sexp, ctx: &SerapiNormCtx) -> Sexp {
    let sort_of = |p: Sexp| Sexp::List(vec![Sexp::Atom("Sort".to_string()), p]);
    match payload {
        Sexp::Atom(s) if s == "Prop" || s == "Set" => sort_of(payload.clone()),
        Sexp::Atom(s) if s == "SProp" => coq_unsupported(
            "out-of-model (SProp): SProp sort has no sound collapse into the importer model",
        ),
        Sexp::List(v) if matches!(v.first(), Some(Sexp::Atom(h)) if h == "QSort") => {
            if let Some(shape) = &ctx.current_poly {
                if let Some(q) = qsort_quality_index(payload, shape) {
                    SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
                    return sort_of(Sexp::List(vec![
                        Sexp::Atom("Param".to_string()),
                        Sexp::Atom(format!("u{q}")),
                    ]));
                }
            }
            coq_unsupported("out-of-model (universe): unrecognized Sort payload")
        }
        Sexp::List(v) if matches!(v.first(), Some(Sexp::Atom(h)) if h == "Type") => {
            match classify_serapi_type_universe(v.get(1), &ctx.universe_bases) {
                Ok(level) => sort_of(Sexp::List(vec![
                    Sexp::Atom("Type".to_string()),
                    Sexp::Atom(level.to_string()),
                ])),
                Err(reason) => coq_unsupported(&reason),
            }
        }
        _ => coq_unsupported("out-of-model (universe): unrecognized Sort payload"),
    }
}

/// The quality-variable index of a `QSort` payload IF it matches the derived
/// per-decl sort-poly shape: `(QSort (Var q) ((… (data (Var k))) 0))` with
/// `shape.pairing[q] == k`. `None` for any other payload (fail closed).
fn qsort_quality_index(payload: &Sexp, shape: &CoqSortPolyShape) -> Option<u32> {
    let Sexp::List(v) = payload else { return None };
    if v.len() != 3 || !matches!(&v[0], Sexp::Atom(h) if h == "QSort") {
        return None;
    }
    let q = match &v[1] {
        Sexp::List(qv) if qv.len() == 2 && matches!(&qv[0], Sexp::Atom(h) if h == "Var") => {
            match &qv[1] {
                Sexp::Atom(s) => s.parse::<u32>().ok()?,
                _ => return None,
            }
        }
        _ => return None,
    };
    // Single (level-expr, increment 0) pair with a (Var k) datum.
    let Sexp::List(pairs) = &v[2] else {
        return None;
    };
    let [Sexp::List(pair)] = pairs.as_slice() else {
        return None;
    };
    if pair.len() != 2 || !matches!(&pair[1], Sexp::Atom(s) if s == "0") {
        return None;
    }
    let datum = match &pair[0] {
        Sexp::List(fields) => fields.iter().find_map(|f| match f {
            Sexp::List(kv) if kv.len() == 2 && matches!(&kv[0], Sexp::Atom(k) if k == "data") => {
                Some(&kv[1])
            }
            _ => None,
        }),
        _ => None,
    };
    let k = match datum {
        Some(Sexp::List(dv)) if dv.len() == 2 && matches!(&dv[0], Sexp::Atom(h) if h == "Var") => {
            match &dv[1] {
                Sexp::Atom(s) => s.parse::<u32>().ok()?,
                _ => return None,
            }
        }
        _ => return None,
    };
    (shape.pairing.get(q as usize) == Some(&k)).then_some(q)
}

/// Classify a SerAPI `Type` universe payload and return the collapsed importer
/// level (`Ok(level)`), or a reason when out of model (`Err`). The payload is
/// one or more `(<level-expr> <increment>)` pairs; each level datum is a named
/// global `(Level ...)` or the runtime `Set` level (serialized as the atom
/// `SProp` by sertop 8.20's pierced `RawLevel` encoding — unambiguous, see the
/// module doc: genuine `SProp`/`Prop` cannot occur as universe levels, so
/// `Type@{Set}` is the only reading, and Coq identifies `Type@{Set}` with `Set`).
///
/// MULTIPLE pairs are the `Type@{max(l1,…,ln)}` shape of TEMPLATE-POLYMORPHIC
/// arities (`prod`/`sum`/`sigT`) and of algebraic codomain sorts. The collapse
/// is INCREMENT-AWARE: each arm's model level is `base(datum) + increment`, with
/// `base(named Level) = 1` (all named template levels collapse to `Type 1`) and
/// `base(pierced Set) = 0` (`Set` is `Type 0`, so `Set + 1 = Type 1`,
/// `named + 1 = Type 2`). The sort is the MAX over arms, floored at `Type 1`
/// (the smallest `Type@{…}` sort the importer models). So `Definition foo :=
/// Type` (`Type@{u+1}`) lands at `Type 2` — one above its `Type@{u}` value —
/// and the whole Relations/Setoid hierarchy's `Type@{max(Set+1, u)}` lands at
/// `Type 1`. Only bound `(Var _)` levels (true universe polymorphism) and
/// non-global datums remain out of model, in any position. The kernel
/// re-checks every collapsed term, so an over/under-shot level fails loudly.
///
/// RE-LEVELING (`bases`, see [`super::universe_releveling`]): a named global
/// level the constraint-mining pre-pass RAISED renders at its solved base
/// instead of 1 — one uid, one base, EVERYWHERE — and marks the enclosing
/// declaration `SPECULATIVE_MOTIVE` (kernel-arbitrated fail-closed). An
/// empty map (the default) reproduces the historical collapse exactly.
fn classify_serapi_type_universe(
    payload: Option<&Sexp>,
    bases: &super::universe_releveling::UniverseBaseMap,
) -> Result<u32, String> {
    let Some(Sexp::List(pairs)) = payload else {
        return Err("out-of-model (universe): missing Type universe payload".to_string());
    };
    if pairs.is_empty() {
        return Err("out-of-model (universe): empty Type universe payload".to_string());
    }
    let mut level: u32 = 1;
    for entry in pairs {
        let Sexp::List(pair) = entry else {
            return Err("out-of-model (universe): malformed universe pair".to_string());
        };
        if pair.len() != 2 {
            return Err("out-of-model (universe): malformed universe pair".to_string());
        }
        let increment: u32 = match &pair[1] {
            Sexp::Atom(s) => s
                .parse()
                .map_err(|_| "out-of-model (universe): malformed universe increment".to_string())?,
            _ => return Err("out-of-model (universe): malformed universe increment".to_string()),
        };
        // level-expr = ((hash N)(data <datum>)) — locate the (data ...) field.
        let datum = match &pair[0] {
            Sexp::List(fields) => fields.iter().find_map(|f| match f {
                Sexp::List(kv)
                    if kv.len() == 2 && matches!(&kv[0], Sexp::Atom(k) if k == "data") =>
                {
                    Some(&kv[1])
                }
                _ => None,
            }),
            _ => None,
        };
        // Each arm's collapsed importer level = base(datum) + increment. A named
        // global template level collapses to `Type 1` (base 1); a bound
        // polymorphic `(Var _)` level ALSO collapses to `Type 1` (monomorphic
        // treatment — references are imported monomorphically with their instance
        // stripped, and the kernel re-checks); the pierced runtime `Set` level is
        // `Type 0` (base 0), so `Set + 1 = Type 1` and `named + 1 = Type 2`. The
        // sort is the MAX over arms, floored at `Type 1` (the smallest `Type@{…}`
        // sort the importer models; a bare `Set` arm alone still lands at
        // `Type 1`, matching `Type@{Set} ≡ Set`). Only non-global datums (sort
        // quality variables, unrecognized payloads) remain out of model.
        let base: u32 = match datum {
            Some(d @ Sexp::List(v)) if matches!(v.first(), Some(Sexp::Atom(h)) if h == "Level") => {
                // Named global level: base 1 historically; the solved
                // re-leveling map may RAISE it (one uid → one base
                // everywhere). A raised rendering marks the declaration
                // speculative so the kernel arbitrates fail-closed.
                match super::universe_releveling::level_datum_uid_key(d)
                    .and_then(|k| bases.raised_base(&k))
                {
                    Some(raised) => {
                        SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
                        raised
                    }
                    None => 1,
                }
            }
            Some(Sexp::Atom(a)) if a == "SProp" => 0,
            // Bound polymorphic level `(Var k)`: collapse to a monomorphic
            // `Type 1` (base 1), identically to a named global level. All
            // references to a universe-polymorphic constant are imported
            // monomorphically (their universe instance is stripped — see
            // `serapi_ref_instance_class`), so a monomorphic collapse of the
            // binder keeps the constant and its uses consistent, and the kernel
            // re-checks the result (with Coq cumulativity `Prop ≤ Set ≤ Type` on
            // this lane), so any residual mismatch is a loud rejection, never an
            // unsound accept. This recovers the universe-polymorphic setoid layer
            // (`Coq.Classes.Init.Unconvertible : ∀ A:Type@{u}, A→A→Set` and the
            // `Proper`/`Morphisms` stack) that the numeric tower and `Reals`
            // depend on pervasively. Full per-constant polymorphism
            // (`Level::Param`) is a separate, later lever.
            Some(Sexp::List(v)) if matches!(v.first(), Some(Sexp::Atom(h)) if h == "Var") => 1,
            _ => return Err("out-of-model (universe): non-global universe level datum".to_string()),
        };
        level = level.max(base + increment);
    }
    Ok(level)
}

/// Per-declaration SORT-POLYMORPHISM shape, derived from the RAW SerAPI
/// s-expression BEFORE normalization.
///
/// Coq's sort-polymorphic binders come in (quality, level) pairs:
/// `Sort@{q|u}` with a quality variable `q` (Prop/SProp/Type) and a level
/// variable `u`. Clean's kernel has no quality variables, but a Lean-style
/// `Level::Param` FUSES both: `Sort p` with `p = 0` is Prop and `p = n+1` is
/// `Type n`. So a declaration whose every `QSort` occurrence is
/// `(QSort (Var q) ((… (data (Var k))) 0))` — quality variable `q`
/// consistently paired with level variable `k`, increment 0 — encodes
/// faithfully as ONE `Level::Param` per quality variable (`u0`, `u1`, …, in
/// quality-index order). This is the measured `ssr_have_upoly` class: the
/// dominant mathcomp fail-closed shape is 1,426 fully-quality-specialized
/// (`QConstant`) references to that single sort-polymorphic constant.
///
/// The shape records the pairing (quality index → level-variable index) plus
/// the inferred level-binder count, so reference instances can be validated
/// positionally and translated (see `translate_poly_ref_instance`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CoqSortPolyShape {
    /// `pairing[q]` = the level `Var` index paired with quality `Var q` in
    /// EVERY `QSort` occurrence of the declaration. One emitted level param
    /// per entry, named `u{q}`.
    pairing: Vec<u32>,
    /// Total level binders inferred (`max paired level index + 1`). Reference
    /// instances must carry exactly this many level datums to translate.
    level_count: u32,
}

impl CoqSortPolyShape {
    /// The synthesized `level_params` names for the header window, in
    /// quality-index order (`u0`, `u1`, …).
    fn param_names(&self) -> Vec<String> {
        (0..self.pairing.len()).map(|q| format!("u{q}")).collect()
    }
}

/// Derive the [`CoqSortPolyShape`] of a declaration from its RAW type (and
/// optional value) s-expressions, or `None` when the declaration does not
/// qualify for the fused sort-poly encoding. Qualification is deliberately
/// TIGHT (fail closed — an unqualified declaration keeps today's behavior,
/// where a `QSort` sort rewrites to a loud `CoqUnsupported`):
///
/// - every `(Sort (QSort …))` occurrence must be `(QSort (Var q)
///   ((… (data (Var k))) 0))` — quality VARIABLE, single level pair, level
///   VARIABLE datum, increment 0;
/// - the pairing q→k must be functional AND injective across occurrences;
/// - quality indices must be contiguous from 0 (no phantom binders we could
///   not order);
/// - no `(Sort (Type …))` occurrence may mention a `(Var …)` level datum
///   (that datum collapses to a CONCRETE level today; letting the same Coq
///   binder render both as a `Param` and as a concrete level would split its
///   identity);
/// - at least one `QSort` occurrence exists (a declaration with none has
///   nothing to bind).
pub(crate) fn derive_sort_poly_shape(
    type_sexp: &Sexp,
    value_sexp: Option<&Sexp>,
) -> Option<CoqSortPolyShape> {
    // pairing map under construction: quality idx -> level idx.
    let mut pairing: std::collections::BTreeMap<u32, u32> = std::collections::BTreeMap::new();
    let mut ok = true;

    fn var_index(sexp: &Sexp) -> Option<u32> {
        match sexp {
            Sexp::List(v) if v.len() == 2 && matches!(&v[0], Sexp::Atom(h) if h == "Var") => {
                match &v[1] {
                    Sexp::Atom(s) => s.parse::<u32>().ok(),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    /// The `(data <datum>)` payload of a SerAPI level expression.
    fn level_datum(sexp: &Sexp) -> Option<&Sexp> {
        match sexp {
            Sexp::List(fields) => fields.iter().find_map(|f| match f {
                Sexp::List(kv)
                    if kv.len() == 2 && matches!(&kv[0], Sexp::Atom(k) if k == "data") =>
                {
                    Some(&kv[1])
                }
                _ => None,
            }),
            _ => None,
        }
    }

    fn walk(sexp: &Sexp, pairing: &mut std::collections::BTreeMap<u32, u32>, ok: &mut bool) {
        if !*ok {
            return;
        }
        let Sexp::List(items) = sexp else { return };
        // (Sort <payload>)
        if items.len() == 2 && matches!(&items[0], Sexp::Atom(h) if h == "Sort") {
            if let Sexp::List(payload) = &items[1] {
                match payload.first() {
                    Some(Sexp::Atom(h)) if h == "QSort" => {
                        // (QSort (Var q) ((((hash _)(data (Var k))) 0)))
                        let q = payload.get(1).and_then(var_index);
                        let pair = match payload.get(2) {
                            Some(Sexp::List(pairs)) if pairs.len() == 1 => pairs.first(),
                            _ => None,
                        };
                        let (k, incr_zero) = match pair {
                            Some(Sexp::List(p)) if p.len() == 2 => (
                                level_datum(&p[0]).and_then(var_index),
                                matches!(&p[1], Sexp::Atom(s) if s == "0"),
                            ),
                            _ => (None, false),
                        };
                        match (q, k, incr_zero) {
                            (Some(q), Some(k), true) => {
                                // functional + injective pairing.
                                let functional = pairing.get(&q).is_none_or(|&prev| prev == k);
                                let injective = pairing.iter().all(|(&pq, &pk)| pq == q || pk != k);
                                if functional && injective {
                                    pairing.insert(q, k);
                                } else {
                                    *ok = false;
                                }
                            }
                            _ => *ok = false,
                        }
                        return; // QSort payload fully handled
                    }
                    Some(Sexp::Atom(h)) if h == "Type" => {
                        // A concrete/named Type payload collapses today; a
                        // (Var …) datum inside it would split the binder's
                        // identity against the QSort Params — disqualify.
                        if let Some(Sexp::List(pairs)) = payload.get(1) {
                            for p in pairs {
                                if let Sexp::List(pv) = p {
                                    if pv
                                        .first()
                                        .and_then(level_datum)
                                        .and_then(var_index)
                                        .is_some()
                                    {
                                        *ok = false;
                                        return;
                                    }
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        for item in items {
            walk(item, pairing, ok);
        }
    }

    walk(type_sexp, &mut pairing, &mut ok);
    if let Some(v) = value_sexp {
        walk(v, &mut pairing, &mut ok);
    }
    if !ok || pairing.is_empty() {
        return None;
    }
    // Quality indices must be contiguous 0..n-1 (BTreeMap iterates sorted).
    let contiguous = pairing.keys().enumerate().all(|(i, &q)| i as u32 == q);
    if !contiguous {
        return None;
    }
    let level_count = pairing.values().max().map_or(0, |&k| k + 1);
    Some(CoqSortPolyShape {
        pairing: pairing.into_values().collect(),
        level_count,
    })
}

/// Translate a fully-quality-specialized universe `Instance` on a reference to
/// a registered sort-polymorphic constant into the explicit CONCRETE levels of
/// its `level_params` (in quality-index order), or `None` when any datum is
/// out of model or the instance shape disagrees with the registered arity
/// (the caller then falls back to today's fail-closed disposition).
///
/// Per fused-`Param` semantics (see [`CoqSortPolyShape`]):
/// - `(QConstant QProp)` → level `0` (Prop);
/// - `(QConstant QType)` at any in-model atomic level datum (pierced-`Set`
///   `SProp` atom, named global `(Level …)`, bound `(Var …)`) → level `1` —
///   exactly the importer's monomorphic collapse of `Type@{atomic}` to
///   `Type 1 = Sort 1`, so the instantiated constant agrees with every other
///   collapsed occurrence of the same level;
/// - `(QConstant QSProp)`, quality variables, or unrecognized datums → `None`.
fn translate_poly_ref_instance(ref_payload: &Sexp, info: &CoqSortPolyShape) -> Option<Vec<u32>> {
    let Sexp::List(elems) = ref_payload else {
        return None;
    };
    let instance = elems.iter().find_map(|e| match e {
        Sexp::List(v) if matches!(v.first(), Some(Sexp::Atom(h)) if h == "Instance") => v.get(1),
        _ => None,
    })?;
    let Sexp::List(parts) = instance else {
        return None;
    };
    let (qualities, levels) = match parts.as_slice() {
        [Sexp::List(q), Sexp::List(l)] => (q, l),
        _ => return None,
    };
    if qualities.len() != info.pairing.len() || levels.len() != info.level_count as usize {
        return None;
    }
    // Extract each level's `(data <datum>)` payload; classify as in-model
    // atomic (pierced-Set, named Level, bound Var) or out of model.
    let atomic_level: Vec<bool> = levels
        .iter()
        .map(|entry| {
            let datum = match entry {
                Sexp::List(fields) => fields.iter().find_map(|f| match f {
                    Sexp::List(kv)
                        if kv.len() == 2 && matches!(&kv[0], Sexp::Atom(k) if k == "data") =>
                    {
                        Some(&kv[1])
                    }
                    _ => None,
                }),
                _ => None,
            };
            match datum {
                Some(Sexp::Atom(a)) if a == "SProp" => true,
                Some(Sexp::List(l)) => {
                    matches!(l.first(), Some(Sexp::Atom(h)) if h == "Level" || h == "Var")
                }
                _ => false,
            }
        })
        .collect();
    let mut out = Vec::with_capacity(info.pairing.len());
    for (q_idx, &k) in info.pairing.iter().enumerate() {
        let quality = qualities.get(q_idx)?;
        let fused = match quality {
            Sexp::List(l) => match l.as_slice() {
                [Sexp::Atom(h), Sexp::Atom(c)] if h == "QConstant" && c == "QProp" => 0,
                [Sexp::Atom(h), Sexp::Atom(c)]
                    if h == "QConstant" && c == "QType" && *atomic_level.get(k as usize)? =>
                {
                    1
                }
                _ => return None, // QSProp / quality vars / non-atomic level: out of model
            },
            _ => return None,
        };
        out.push(fused);
    }
    Some(out)
}

/// Extract the FULLY-QUALIFIED constant/inductive name from a nested SerAPI
/// kernel-name structure such as
/// `(Constant (KerName (MPfile (DirPath ((Id Peano)(Id Init)(Id Coq)))) (Id plus_n_O)) ())`.
///
/// Per the shared Coq-import naming convention, `DirPath` segments are stored
/// innermost-first and are REVERSED then joined with `.`, followed by the
/// final `Id`: the example yields `Coq.Init.Peano.plus_n_O`. `MPdot` module
/// paths append their label segment. Returns `None` (caller leaves the node
/// untouched, which fails closed downstream) for functor-bound `MPbound`
/// paths and unrecognized shapes.
pub(crate) fn serapi_qualified_name(sexp: &Sexp) -> Option<String> {
    let Sexp::List(_) = sexp else {
        return None; // bare importer-dialect atoms are not SerAPI-native
    };
    let kn = find_kername_first(sexp)?;
    kername_to_string(kn)
}

/// First `KerName` node in document order — the USER spelling of a KerPair
/// (the spelling the source module referenced the constant by).
fn find_kername_first(s: &Sexp) -> Option<&Vec<Sexp>> {
    match s {
        Sexp::List(v) => {
            if v.len() >= 3 && matches!(v.first(), Some(Sexp::Atom(h)) if h == "KerName") {
                return Some(v);
            }
            v.iter().find_map(find_kername_first)
        }
        _ => None,
    }
}

fn kername_to_string(kn: &[Sexp]) -> Option<String> {
    let prefix = serapi_modpath_prefix(kn.get(1)?)?;
    let id = serapi_id_atom(kn.get(2)?)?;
    Some(if prefix.is_empty() {
        id
    } else {
        format!("{prefix}.{id}")
    })
}

/// CANONICAL spelling of a KerPair `Dual`: `(Constant (KerName <user>)
/// ((KerName <canonical>)))` (same for `MutInd`) — a constant reached through
/// a module ALIAS (`Module Positive_as_OT := Pos`) or an `Include` carries
/// BOTH spellings, and the third field is `Some(canonical)` exactly when they
/// differ (`()` otherwise). Returns `None` for `Same` KerPairs.
fn serapi_qualified_name_canonical(sexp: &Sexp) -> Option<String> {
    fn find_dual(s: &Sexp) -> Option<&Vec<Sexp>> {
        match s {
            Sexp::List(v) => {
                if v.len() >= 3
                    && matches!(v.first(), Some(Sexp::Atom(h)) if h == "Constant" || h == "MutInd")
                {
                    if let Sexp::List(canon) = &v[2] {
                        if let Some(kn) = canon.first().and_then(find_kername_first) {
                            return Some(kn);
                        }
                    }
                }
                v.iter().find_map(find_dual)
            }
            _ => None,
        }
    }
    kername_to_string(find_dual(sexp)?)
}

/// Resolve a KerPair reference REGISTRY-AWARE: the USER spelling when it names
/// a declaration known to the session (today's behavior — the spelling the
/// referencing module used, which module-alias dumps often define under), else
/// the CANONICAL (definition-site) spelling when THAT one is known, else the
/// user spelling (fail closed to the historical resolution). The Dual is Coq's
/// own record that both spellings are one kernel constant, so following it is
/// exact — but preferring it UNCONDITIONALLY was measured (2026-07-13) to
/// regress 125 stdlib constants whose canonical target is absent from the
/// dumps while the user spelling is present; only the registry can arbitrate.
fn resolve_kerpair_name(user: String, sexp: &Sexp, ctx: &SerapiNormCtx) -> String {
    if ctx.is_known_name(&user) {
        return user;
    }
    match serapi_qualified_name_canonical(sexp) {
        Some(canon) if ctx.is_known_name(&canon) => canon,
        _ => user,
    }
}

/// Qualify a SerAPI module path: `(MPfile (DirPath ((Id C)(Id B)(Id A))))`
/// => `A.B.C` (segments reversed); `(MPdot <mp> <label>)` appends its label.
fn serapi_modpath_prefix(sexp: &Sexp) -> Option<String> {
    let Sexp::List(v) = sexp else {
        return None;
    };
    match v.first() {
        Some(Sexp::Atom(h)) if h == "MPfile" => {
            let Some(Sexp::List(dp)) = v.get(1) else {
                return None;
            };
            if !matches!(dp.first(), Some(Sexp::Atom(t)) if t == "DirPath") {
                return None;
            }
            let Some(Sexp::List(segs)) = dp.get(1) else {
                return None;
            };
            let mut names: Vec<String> = Vec::with_capacity(segs.len());
            for seg in segs.iter().rev() {
                names.push(serapi_id_atom(seg)?);
            }
            Some(names.join("."))
        }
        Some(Sexp::Atom(h)) if h == "MPdot" && v.len() >= 3 => {
            let base = serapi_modpath_prefix(&v[1])?;
            let label = serapi_id_atom(&v[2])?;
            Some(if base.is_empty() {
                label
            } else {
                format!("{base}.{label}")
            })
        }
        // Functor-bound module paths cannot be qualified soundly.
        _ => None,
    }
}

/// Extract the identifier from `(Id x)` or `(Label (Id x))`.
pub(crate) fn serapi_id_atom(sexp: &Sexp) -> Option<String> {
    match sexp {
        Sexp::List(v)
            if v.len() >= 2 && matches!(&v[0], Sexp::Atom(h) if h == "Id" || h == "Label") =>
        {
            match &v[1] {
                Sexp::Atom(s) => Some(s.clone()),
                inner @ Sexp::List(_) => serapi_id_atom(inner),
            }
        }
        _ => None,
    }
}

/// Classification of a SerAPI universe `Instance` on a
/// `Const`/`Ind`/`Construct` reference (or a compact `Case` node).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SerapiInstanceClass {
    /// `(Instance (() ()))` — monomorphic reference, in model.
    Monomorphic,
    /// Exactly one level, and it is the runtime `Set` level (serialized as
    /// the atom `SProp` by the pierced 8.20 encoding — see the module doc).
    /// At the `Const`/`Ind`/`Construct` emit sites this now takes the same
    /// speculative monomorphic drop as [`MonoDropSpeculative`] (the drop is
    /// exactly the same guess); the `Case`-node path stays fail-closed.
    SingleSetLevel,
    /// The monomorphic collapse (drop the whole instance, reference the single
    /// imported version) is a plausible GUESS. Two measured shapes:
    ///
    /// 1. Every level is a named `(Level ...)`, bound `(Var k)`, OR a
    ///    pierced-`Set` (`SProp` atom) datum, WITH at least one pierced-`Set`
    ///    in the mix — a polymorphic instance partly specialized to the
    ///    runtime `Set` level.
    /// 2. A sort-polymorphic instance whose every quality is a CONSTANT
    ///    `(QConstant QProp|QSProp|QType)` — fully quality-specialized — with
    ///    any in-model level shape (measured 2026-07-10: the dominant mathcomp
    ///    fail-closed shape, 0 quality variables in the whole corpus).
    ///
    /// Specializing a floating level/quality to the mono default may or may
    /// not re-typecheck, so the emit site marks the enclosing constant
    /// `SPECULATIVE_MOTIVE`: the kernel accepts → genuine KV, rejects → clean
    /// `AxiomFallback(None)` (no taint). 0-regression by construction, unlike
    /// the value-less fail-closed [`OutOfModel`] reject.
    MonoDropSpeculative,
    /// Anything else: sort-quality variables, unrecognized payloads. Out of
    /// model.
    OutOfModel,
}

/// Classify the universe `Instance` found inside a SerAPI reference payload
/// (the record wrapped by `Const`/`Ind`/`Construct`). Missing instance node
/// counts as monomorphic (hand-written dialect data carries none).
fn serapi_ref_instance_class(sexp: &Sexp) -> SerapiInstanceClass {
    let Sexp::List(elems) = sexp else {
        return SerapiInstanceClass::Monomorphic;
    };
    let instance = elems.iter().find_map(|e| match e {
        Sexp::List(v) if matches!(v.first(), Some(Sexp::Atom(h)) if h == "Instance") => v.get(1),
        _ => None,
    });
    let Some(instance) = instance else {
        return SerapiInstanceClass::Monomorphic;
    };
    // Instance payload = (<sort-qualities> <levels>) in sertop 8.20.
    let Sexp::List(parts) = instance else {
        return SerapiInstanceClass::OutOfModel;
    };
    let (qualities, levels) = match parts.as_slice() {
        [Sexp::List(q), Sexp::List(l)] => (q, l),
        _ => return SerapiInstanceClass::OutOfModel,
    };
    // Sort qualities. A CORPUS MEASUREMENT (2026-07-10, COQ_UPOLY_DEBUG over
    // stdlib+mathcomp) found the dominant fail-closed shape is a sort-poly
    // instance whose every quality datum is a CONSTANT quality —
    // `(QConstant QProp|QSProp|QType)` — i.e. the sort polymorphism is FULLY
    // SPECIALIZED to concrete qualities at this reference (2,518 hits, 100%
    // `QConstant`, 0 quality VARIABLES). The referenced constant was imported
    // monomorphically at one fixed quality, so dropping the whole instance and
    // referencing that single version is a GUESS: classify at most
    // [`SerapiInstanceClass::MonoDropSpeculative`] (never plain `Monomorphic`)
    // so the emit site marks the enclosing constant `SPECULATIVE_MOTIVE` and
    // the kernel arbitrates fail-closed. Quality VARIABLES (`QVar`) and any
    // unrecognized quality payload stay out of model.
    let quality_specialized = !qualities.is_empty();
    if quality_specialized
        && !qualities.iter().all(|q| {
            matches!(q, Sexp::List(l) if matches!(l.as_slice(),
                [Sexp::Atom(h), Sexp::Atom(c)] if h == "QConstant"
                    && matches!(c.as_str(), "QProp" | "QSProp" | "QType")))
        })
    {
        return SerapiInstanceClass::OutOfModel; // quality variables / unknown
    }
    let level_class = serapi_ref_level_class(levels);
    if quality_specialized {
        return match level_class {
            SerapiInstanceClass::OutOfModel => SerapiInstanceClass::OutOfModel,
            // Any in-model level shape under a quality specialization is a
            // guessed drop as a whole — speculative, kernel-gated.
            _ => SerapiInstanceClass::MonoDropSpeculative,
        };
    }
    level_class
}

/// Classify the LEVEL datums of a SerAPI universe `Instance` (the second
/// payload list), ignoring qualities — see [`serapi_ref_instance_class`] for
/// how a quality-specialized instance caps the result at speculative.
fn serapi_ref_level_class(levels: &[Sexp]) -> SerapiInstanceClass {
    if levels.is_empty() {
        return SerapiInstanceClass::Monomorphic;
    }
    // Extract each level's `(data <datum>)` payload.
    let datums: Vec<Option<&Sexp>> = levels
        .iter()
        .map(|entry| match entry {
            Sexp::List(fields) => fields.iter().find_map(|f| match f {
                Sexp::List(kv)
                    if kv.len() == 2 && matches!(&kv[0], Sexp::Atom(k) if k == "data") =>
                {
                    Some(&kv[1])
                }
                _ => None,
            }),
            _ => None,
        })
        .collect();
    // Instance whose every level is a named global `(Level ((DirPath ...) uid))`
    // OR a bound polymorphic `(Var k)`: reference the constant MONOMORPHICALLY.
    // The referenced constant was itself imported monomorphically — its own named
    // AND `(Var k)` universes collapse to the concrete Sort tower (see the Sort
    // handling: a `(Var k)` sort level collapses to `Type 1`) — so dropping the
    // instance and referencing the single monomorphic version is consistent for
    // both level forms. The kernel re-checks the result, so an inconsistency can
    // only surface as a loud rejection, never an unsound accept (fail closed).
    // Named-level instances recover the setoid-rewriting `Morphisms`/`Proper`/
    // `Unconvertible` layer (`subrelation_proper`); extending to `(Var k)` recovers
    // the `Type`-polymorphic constructive layer (`CRelationClasses.Equivalence`
    // and its `Reflexive`/`Symmetric`/`Transitive` members, `CMorphisms`, and the
    // constructive-reals stack that builds on them).
    if datums.iter().all(|d| {
        matches!(d, Some(Sexp::List(l)) if matches!(l.first(), Some(Sexp::Atom(h)) if h == "Level" || h == "Var"))
    }) {
        return SerapiInstanceClass::Monomorphic;
    }
    // Single pierced `Set` level (serialized as the `SProp` atom by 8.20).
    if let [Some(Sexp::Atom(a))] = datums.as_slice() {
        if a == "SProp" {
            return SerapiInstanceClass::SingleSetLevel;
        }
    }
    // A mix of named `(Level ...)` / bound `(Var k)` levels with one-or-more
    // pierced-`Set` (`SProp`) datums: every datum is one of those three forms.
    // The all-`Level`/`Var` case was already handled (Monomorphic) above, so
    // reaching here with the whole instance in this set means at least one
    // `SProp` is present — a partly-`Set`-specialized polymorphic instance.
    // Drop it SPECULATIVELY: the monomorphic reference may or may not typecheck,
    // and the emit site fails closed on the marker.
    if datums.iter().all(|d| {
        matches!(d, Some(Sexp::List(l)) if matches!(l.first(), Some(Sexp::Atom(h)) if h == "Level" || h == "Var"))
            || matches!(d, Some(Sexp::Atom(a)) if a == "SProp")
    }) {
        return SerapiInstanceClass::MonoDropSpeculative;
    }
    SerapiInstanceClass::OutOfModel
}

/// Fail-closed reason for a reference whose universe `Instance` is not
/// monomorphic; `None` when the reference is in model. `what` names the
/// reference kind for the recorded reason.
fn serapi_ref_instance_reject_reason(sexp: &Sexp, what: &str) -> Option<String> {
    match serapi_ref_instance_class(sexp) {
        SerapiInstanceClass::Monomorphic => None,
        // The Case-node path is kept strictly fail-closed (rejects to a clean
        // axiom); only the `Const`/`Ind`/`Construct` reference emit sites take
        // the speculative monomorphic drop (see `serapi_ref_instance_disposition`).
        SerapiInstanceClass::MonoDropSpeculative | SerapiInstanceClass::SingleSetLevel => {
            Some(format!(
                "out-of-model (universe): Set-instantiated polymorphic {what} reference \
                 (speculative drop not taken on this path)"
            ))
        }
        SerapiInstanceClass::OutOfModel => Some(format!(
            "out-of-model (universe): universe-polymorphic {what} instance"
        )),
    }
}

/// What to do with a `Const`/`Ind`/`Construct` reference given its universe
/// instance: emit the monomorphic reference, emit it but mark the enclosing
/// constant speculative (a `Set`-specialized polymorphic instance dropped to the
/// mono default — kernel-gated, fail-closed), or reject to a clean axiom.
enum InstanceDisposition {
    Emit,
    EmitSpeculative,
    Reject(String),
}

fn serapi_ref_instance_disposition(sexp: &Sexp, what: &str) -> InstanceDisposition {
    match serapi_ref_instance_class(sexp) {
        SerapiInstanceClass::Monomorphic => InstanceDisposition::Emit,
        // A single pierced-`Set` instance takes the SAME speculative
        // monomorphic drop as the mixed shape: the referenced constant was
        // imported monomorphically, so referencing that version at `Set` is a
        // guess the kernel arbitrates (accept → KV, reject → clean type-only
        // axiom via the `SPECULATIVE_MOTIVE` marker; fail-closed).
        SerapiInstanceClass::MonoDropSpeculative | SerapiInstanceClass::SingleSetLevel => {
            InstanceDisposition::EmitSpeculative
        }
        SerapiInstanceClass::OutOfModel => InstanceDisposition::Reject(format!(
            "out-of-model (universe): universe-polymorphic {what} instance"
        )),
    }
}

/// Parse a SerAPI inductive reference `((MutInd (KerName ...) ()) <i>)` possibly
/// wrapped with an `Instance`. Returns `(name, block-index, _)`.
fn serapi_inductive_ref(sexp: &Sexp) -> Option<(String, u32, u32)> {
    let Sexp::List(outer) = sexp else {
        return None;
    };
    // outer = ( (((MutInd ...) ()) i) (Instance ...) )  -> take first element.
    let indref = outer.first()?;
    let Sexp::List(pair) = indref else {
        return None;
    };
    // pair = ( ((MutInd ...) ()) i )
    if pair.len() < 2 {
        return None;
    }
    let name = serapi_qualified_name(&pair[0])?;
    let i = match &pair[1] {
        Sexp::Atom(s) => s.parse::<u32>().ok()?,
        _ => return None,
    };
    Some((name, i, 0))
}

/// Look up `(field-name value)` in a SerAPI record field list, returning
/// `value`. Used to read the `Projection.Repr` fields (`proj_ind`, `proj_arg`,
/// …) out of the projfix/`.vo` `Proj` payload.
fn proj_repr_field<'a>(fields: &'a [Sexp], name: &str) -> Option<&'a Sexp> {
    fields.iter().find_map(|f| match f {
        Sexp::List(kv) if kv.len() == 2 => match &kv[0] {
            Sexp::Atom(k) if k == name => Some(&kv[1]),
            _ => None,
        },
        _ => None,
    })
}

/// Translate a dumper `(Proj (((proj_ind <ind>) (proj_npars N) (proj_arg K)
/// (proj_name <c>)) <unfolded:bool>) <relevance> <record>)` node into the
/// importer dialect `(Proj <struct-name> <K> <record>)`.
///
/// `struct-name` is the record inductive named by `proj_ind` (resolved through
/// the same KerPair dual-spelling arbitration as `(Ind …)` references); `K` is
/// Coq's own 0-based field index (`proj_arg`), which the kernel uses directly
/// as the projection field index. Marks the enclosing constant
/// [`AxiomProfile::SPECULATIVE_MOTIVE`] so a projection the kernel cannot
/// resolve (record absent, or a `proj_arg`/field-index mismatch) fails closed
/// to a clean type-only axiom instead of a masked-failure taint. Every failure
/// path returns `Err(reason)` so the caller emits `coq_unsupported` (also
/// fail-closed).
fn convert_serapi_proj(
    items: &[Sexp],
    ctx: &SerapiNormCtx,
    bctx: &[Option<Sexp>],
) -> Result<Sexp, String> {
    // items = [Proj, <projection-tuple>, <relevance>, <record-term>]
    let proj_tuple = items.get(1).ok_or("Proj: missing projection payload")?;
    let record = items.get(3).ok_or("Proj: missing record term")?;
    // projection-tuple = (<Repr-record> <unfolded:bool>)
    let Sexp::List(tuple) = proj_tuple else {
        return Err("Proj: projection payload is not a list".to_string());
    };
    let repr = tuple.first().ok_or("Proj: empty projection payload")?;
    let Sexp::List(fields) = repr else {
        return Err("Proj: Repr is not a field list".to_string());
    };
    let ind_val = proj_repr_field(fields, "proj_ind").ok_or("Proj: no proj_ind field")?;
    let arg_val = proj_repr_field(fields, "proj_arg").ok_or("Proj: no proj_arg field")?;
    let field_idx = match arg_val {
        Sexp::Atom(s) => s
            .parse::<u32>()
            .map_err(|_| "Proj: proj_arg is not a u32".to_string())?,
        _ => return Err("Proj: proj_arg is not an atom".to_string()),
    };
    // proj_ind = ((MutInd (KerName …) ()) <block>); serapi_inductive_ref reads
    // `outer.first()`, so wrap the reference in a one-element list.
    let (raw_name, block, _) = serapi_inductive_ref(&Sexp::List(vec![ind_val.clone()]))
        .ok_or("Proj: unparsable proj_ind inductive reference")?;
    // The kernel registers the record inductive under the BLOCK-INDEXED shard
    // name `<qualified>.<block>` (see `import_serapi_inductive`), and an `(Ind
    // <name> <i>)` reference lowers to `Const("{name}.{i}")` (cic_to_flat_expr).
    // The projected record term therefore has type `App(Const("<name>.<block>"),
    // …)`, so the Proj's struct-name MUST carry the same `.<block>` suffix — else
    // `infer_proj_type` compares `<name>.<block>` (the record's actual inductive
    // head) against a bare `<name>` and rejects with InvalidProjNotStruct. This
    // was the HB primitive-projection accessor wall (`Choice.base`, `pickle`, …):
    // the record inductive family replayed fine, but every `.(field)` accessor
    // failed the projection typecheck on the missing block suffix.
    let struct_name = format!(
        "{}.{}",
        resolve_ind_family_name(raw_name, ind_val, block, ctx),
        block
    );
    // The record term shares this node's binder context.
    let inner = normalize_serapi_rec(record, ctx, bctx);
    // The proj_arg -> kernel-field-idx identification is kernel-arbitrated.
    SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
    Ok(Sexp::List(vec![
        Sexp::Atom("Proj".to_string()),
        Sexp::Atom(struct_name),
        Sexp::Atom(field_idx.to_string()),
        inner,
    ]))
}

/// Parse a SerAPI constructor reference `(((MutInd ...) i) j)` (wrapped with an
/// `Instance`). Returns `(name, block-index, ctor-index)` with the raw 1-based
/// SerAPI constructor index.
fn serapi_construct_ref(sexp: &Sexp) -> Option<(String, u32, u32)> {
    let Sexp::List(outer) = sexp else {
        return None;
    };
    let cref = outer.first()?;
    // cref = ( ((MutInd ...) i) j )
    let Sexp::List(pair) = cref else {
        return None;
    };
    if pair.len() < 2 {
        return None;
    }
    let j = match &pair[1] {
        Sexp::Atom(s) => s.parse::<u32>().ok()?,
        _ => return None,
    };
    let (name, i, _) = serapi_inductive_ref(&Sexp::List(vec![pair[0].clone()]))?;
    Some((name, i, j))
}

// ===========================================================================
// SerAPI import-session registry + dialect de Bruijn machinery
// (COQ-1a/COQ-3 term fidelity: Case reconstruction and Fix structuralization)
// ===========================================================================

/// Whether an inductive's kernel recursor carries a motive universe level
/// parameter. Mirrors clean-kernel's `elim_only_at_universe_zero`:
/// `Set`/`Type`-valued inductives, empty Prop inductives (`False`) and
/// zero-field Prop singletons (`eq`) large-eliminate (recursor instance =
/// `[motive level]`); multi-constructor Prop inductives eliminate only into
/// `Prop` (no level parameter).
///
/// LOCKSTEP with the kernel's Coq-lane PARAMETRIC SINGLETON ELIMINATION rule
/// (`elim_analysis.rs`: a single-constructor inductive whose result level `R`
/// is not provably nonzero large-eliminates when every field sort is `≤ R`).
/// The mirror observes only sorts the importer's universe model has already
/// COLLAPSED (`normalize_serapi_sort_node` / `classify_serapi_type_universe`
/// flatten template-poly `Type@{max(l1,…,ln)}` to a concrete `(Sort (Type k))`,
/// `k ≥ 1`), so the possibly-zero NON-`Prop` result the parametric rule targets
/// (`max u v`, a bare param) never reaches the mirror — it arrives as a concrete
/// `Type k` and takes the `LevelParam` arm below (matching the kernel's
/// `is_nonzero` gate). For the ONE possibly-zero result the mirror does see —
/// `Prop` (`R = 0`) — the parametric premise "every field `≤ 0`" is exactly
/// "every field is `Prop`-sorted", which [`SerapiIndInfo::prop_singleton_elim_shape`]
/// already tests. So the mirror is in lockstep on every collapsed shape, and
/// the parametric rule is DORMANT here until the poly-`prod` emission cycle
/// preserves genuine level params (design U2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ElimShape {
    /// Recursor takes a leading motive universe parameter.
    LevelParam,
    /// Recursor eliminates only into `Prop`; no level parameter.
    PropOnly,
}

/// Sexp-level metadata about an inductive imported earlier in the same
/// `import_sexp` session, used by the SerAPI adapter to reconstruct binder
/// types for `Case` branches and to structuralize `Fix` nodes.
#[derive(Clone, Debug)]
pub(crate) struct SerapiIndInfo {
    num_params: u32,
    /// The FULL normalized dialect arity (parameter and index telescope plus
    /// result sort), used to derive index binder types for indexed matches
    /// and to mirror the kernel's fixed-index promotion.
    arity: Sexp,
    /// Sort of the arity codomain (`None` when unrecognized → elimination
    /// shape undecidable → Cases on this inductive fail closed).
    arity_sort: Option<CicSort>,
    /// Per constructor: the FULL dialect ctor type (leading `num_params`
    /// Prods quantify the parameters; Case conversion instantiates them with
    /// the Case's parameter arguments).
    ctor_types: Vec<Sexp>,
    /// Per constructor: which fields are DIRECT recursive occurrences of the
    /// inductive (function-typed / nested occurrences are not flagged; a
    /// mismatch surfaces as a loud kernel rejection, never a silent accept).
    ctor_recursive: Vec<Vec<bool>>,
    /// Per constructor: `Some((raw type, decl_is_let))` when the ORIGINAL
    /// telescope carried `LetIn` declarations that registration zeta-reduced
    /// away — the raw (params-quantified, LetIn-laced) constructor type plus
    /// one flag per ORIGINAL declaration (`true` at let positions), the shape
    /// a compact `Case` node's branch binder array follows
    /// (`Build_ConstructiveReals`: 35 decls = 29 fields + 6 lets). `None` for
    /// pure-Prod constructors (every previously-working inductive). Case
    /// reconstruction uses it to zeta-expand a branch that binds the full
    /// declaration telescope (see [`zeta_expand_letbound_branch`]).
    ctor_raw_lets: Vec<Option<(Sexp, Vec<bool>)>>,
    /// The registered `arity` was δ-unfolded from a type-synonym codomain
    /// (`Singleton U x : Ensemble U` → `∀ U x (a:U). Prop`). Such a family's
    /// Case reconstruction is a DERIVED shape (the index hidden behind the
    /// synonym, plus constructors whose results head an `In`/`Ensemble`
    /// abbreviation rather than the inductive), so it is marked speculative:
    /// a kernel rejection reverts to a clean type-only axiom instead of seeding
    /// a masked-failure taint that would poison dependents.
    arity_synonym_unfolded: bool,
}

impl SerapiIndInfo {
    /// Number of indices per the registered arity telescope
    /// (`arity Prods - num_params`); `None` on underflow (malformed).
    fn num_indices(&self) -> Option<u32> {
        dialect_count_prods(&self.arity).checked_sub(self.num_params)
    }

    /// Whether this inductive's kernel recursor carries a motive universe
    /// level parameter — a syntactic, fail-closed mirror of clean-kernel's
    /// `elim_only_at_universe_zero` (env/elim_analysis.rs):
    ///
    /// - `Set`/`Type`-valued arity → level param (large elimination);
    /// - Prop arity, zero constructors (`False`) → level param;
    /// - Prop arity, several constructors (`or`) → Prop-only;
    /// - Prop arity, ONE constructor: level param iff every field is
    ///   (i) Prop-sorted (decided syntactically from registry data), or
    ///   (ii) a DIRECT `Rel` among the constructor result's index arguments.
    ///   Any field whose Prop-sortedness is syntactically undecidable →
    ///   `None` (fail closed, the pre-existing behavior for fielded Prop
    ///   singletons). This admits `and`/`iff`-shaped conjunctions (all
    ///   fields Prop-sorted) while keeping `ex` Prop-only (its witness field
    ///   is `Type`-sorted and not an index), so witness extraction stays
    ///   disabled.
    ///
    /// A mirror/kernel mismatch can only surface LOUDLY: the emitted recursor
    /// reference then carries the wrong number of levels and the kernel
    /// re-check rejects the term (axiom fallback), never a silent accept.
    fn elim_shape(&self, ctx: &SerapiNormCtx) -> Option<ElimShape> {
        match self.arity_sort.as_ref()? {
            CicSort::Set | CicSort::Type(_) => Some(ElimShape::LevelParam),
            CicSort::Prop => {
                let n = self.ctor_types.len();
                if n == 0 {
                    Some(ElimShape::LevelParam) // empty type (False): large elim
                } else if n > 1 {
                    Some(ElimShape::PropOnly) // multiple ctors: Prop-only
                } else {
                    self.prop_singleton_elim_shape(ctx)
                }
            }
        }
    }

    /// The single-constructor-Prop arm of [`Self::elim_shape`]. Mirrors the
    /// kernel's per-field check over the registered dialect constructor type.
    ///
    /// This is the `R = 0` (result `Prop`) instance of the kernel's parametric
    /// singleton rule: "every field sort `≤ R`" collapses to "every field is
    /// `Prop`-sorted" when `R = 0`, so this per-field `dialect_type_prop_sorted`
    /// walk is exactly that premise (a non-`Prop` field then large-eliminates
    /// only when it is a DIRECT result index, the [R1] carve-out). The
    /// possibly-zero non-`Prop` result the parametric rule also covers is never
    /// seen here (see [`ElimShape`]: the universe collapse renders it concrete).
    fn prop_singleton_elim_shape(&self, ctx: &SerapiNormCtx) -> Option<ElimShape> {
        if self.ctor_recursive[0].is_empty() {
            return Some(ElimShape::LevelParam); // zero-field singleton (eq)
        }
        let (binders, ret) = dialect_peel_prods(&self.ctor_types[0]);
        let ctor_arity = binders.len();
        let np = self.num_params as usize;
        if ctor_arity < np {
            return None; // malformed: fewer binders than parameters
        }
        let (_, ret_args) = dialect_app_parts(&ret);
        let index_args: &[Sexp] = ret_args.get(np..).unwrap_or(&[]);
        let telescope: Vec<Sexp> = binders.iter().map(|(_, ty)| ty.clone()).collect();
        for p in np..ctor_arity {
            match dialect_type_prop_sorted(&telescope[p], &telescope[..p], ctx) {
                Some(true) => {}
                Some(false) => {
                    // Kernel rule (2): a non-Prop field large-eliminates only
                    // if it appears as a DIRECT variable among the result's
                    // index arguments.
                    let bvar = (ctor_arity - 1 - p) as u32;
                    let is_index = index_args.iter().any(|a| dialect_rel_of(a) == Some(bvar));
                    if !is_index {
                        return Some(ElimShape::PropOnly);
                    }
                }
                None => {
                    // This field's Prop-sortedness is syntactically undecidable,
                    // so the syntactic mirror cannot classify the singleton. DEFER
                    // to the kernel: emit a large-elim (level-param) recursor
                    // speculatively. If the inductive is actually Prop-only the
                    // kernel's recursor carries no level arity and REJECTS the term
                    // (clean type-only fallback via the speculative marker); if it
                    // is genuinely large-eliminable the reference is correct and
                    // kernel-verifies. Strictly ≥ the previous fail-closed None.
                    SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
                    return Some(ElimShape::LevelParam);
                }
            }
        }
        Some(ElimShape::LevelParam)
    }
}

/// Import-session registry threaded through the SerAPI adapter. Populated
/// from `(CoqInductive ...)` forms as `import_sexp` walks the input, keyed by
/// the shard constant name `<qualified>.<block_idx>`. `Clone` so a
/// cross-file [`CoqSessionRegistry`] can seed each file's import context.
#[derive(Clone, Debug, Default)]
pub(crate) struct SerapiNormCtx {
    inductives: std::collections::HashMap<String, SerapiIndInfo>,
    /// TYPE-SYNONYM definition bodies, keyed by fully-qualified constant name
    /// (e.g. `Coq.Sets.Ensembles.Ensemble` → `λU. U → Prop`). Only definitions
    /// whose value is a `λ`-telescope over a `Π`-telescope ending in a sort are
    /// stored (see [`type_synonym_body`]). Used to delta-unfold an inductive
    /// arity whose codomain is such a synonym applied to arguments
    /// (`Empty_set : ∀U, Ensemble U`) so the checked `add_inductive` replay sees
    /// an arity that ends in a syntactic sort.
    type_synonyms: std::collections::HashMap<String, CicTerm>,
    /// The SAME type-synonym bodies as [`type_synonyms`], kept in their
    /// normalized DIALECT-SEXP form (keyed identically). The Case/Fix
    /// reconstruction registry (`SerapiIndInfo::arity`) stores dialect sexps, so
    /// when an inductive arity's codomain is a synonym applied to arguments
    /// (`Singleton U x : Ensemble U`), the arity must be δ-unfolded AT THE SEXP
    /// LEVEL too (`Ensemble U := U → Prop` reveals the hidden index) — otherwise
    /// the registry's `num_indices()` undercounts and an indexed match on the
    /// family fails the return-predicate-arity guard. Mirrors the CIC-level
    /// [`unfold_arity_synonym_codomain`] already applied to `arity_cic`.
    type_synonyms_sexp: std::collections::HashMap<String, Sexp>,
    /// Result-sort shape of value-level CONSTANTS whose type CODOMAIN is a sort
    /// — type formers (`R : Set`), relations (`Rle : R → R → Prop`), predicates
    /// (`iff : Prop → Prop → Prop`) — keyed by fully-qualified name →
    /// `(Π-telescope length, codomain sort)`. Lets [`motive_result_level`]
    /// derive the recursor motive universe for a match whose return predicate is
    /// headed by such a constant (`match … return (x < y)`, `match … return R`),
    /// which the Sort/Π/Rel/registered-inductive cases cannot classify.
    /// Populated in dependency order as constants import (the same visibility
    /// discipline as [`type_synonyms`]); a const not yet seen fails closed.
    const_result_sort: std::collections::HashMap<String, (u32, CicSort)>,
    /// RELATION-DEFINITION bodies: definitions whose value is a `λ`-telescope
    /// over an INDUCTIVE application — `lt := λn m. le (S n) m`, `ge := λn m. le
    /// m n`, `Z.lt := λn m. Z.compare n m = Lt`. Keyed by fully-qualified name →
    /// the dialect value. Used to delta-unfold a `match` discriminant whose type
    /// is such an abbreviation (`n < m`) so the recovery sees the inductive it
    /// heads and its index terms. Same in-order / cross-file-pre-pass visibility
    /// discipline as [`type_synonyms`].
    relation_defs: std::collections::HashMap<String, Sexp>,
    /// Full declared TYPE of each constant whose codomain heads an INDUCTIVE
    /// (`leb : nat → nat → bool`, `Nat.compare : nat → nat → comparison`, or any
    /// indexed-family-valued function). Keyed by fully-qualified name → the
    /// dialect type. Used to synthesize the type of a COMPOUND `Const`-headed
    /// `match` discriminant (`match sqrt_iter … with`) by instantiating the
    /// constant's declared type at the discriminant's arguments — recovering the
    /// matched inductive and its index terms. Const types are closed, so the
    /// instantiated result lands directly in the Case context. Same in-order /
    /// cross-file-pre-pass discipline as [`relation_defs`].
    const_types: std::collections::HashMap<String, Sexp>,
    /// DEFINITION bodies of type-former constants whose value is a `λ`-telescope
    /// ending (after peeling any `Π`/`let`) in an INDUCTIVE application —
    /// `Equality.axiom := λT e. ∀ x y, reflect (x = y) (e x y)`. Keyed by
    /// fully-qualified name → the dialect value. Used by
    /// [`synthesize_app_disc_type`] to DELTA-UNFOLD a `Const`-definition head
    /// mid-peel: an ssreflect reflection lemma (`eqP : ∀ T, Equality.axiom …`)
    /// has a codomain headed by such a definition, so the type-instantiation
    /// peel stalls at the `Const` node; β-reducing the registered body exposes
    /// the buried `∀ x y, reflect …` telescope so the peel reaches the matched
    /// `reflect` inductive. Distinct from [`relation_defs`] (whose bodies head an
    /// inductive with NO intervening `Π`s, so they resolve a discriminant TYPE
    /// abbreviation directly). Same in-order / cross-file-pre-pass discipline as
    /// [`relation_defs`].
    const_defs: std::collections::HashMap<String, Sexp>,
    /// EVERY declaration name known to the session (constants, axioms,
    /// inductive bases) from the cross-file pre-passes. Arbitrates KerPair
    /// Dual spelling resolution (see [`resolve_kerpair_name`]): empty (e.g.
    /// single-file imports without a registry) means every Dual keeps the
    /// historical user-spelling resolution.
    known_names: std::collections::HashSet<String>,
    /// SORT-POLYMORPHIC constants emitted with a real `level_params` window
    /// (the fused quality+level `Param` encoding, see [`CoqSortPolyShape`]),
    /// keyed by fully-qualified name. A reference to a registered constant
    /// translates its fully-quality-specialized `Instance` into explicit
    /// levels (`translate_poly_ref_instance`) instead of the monomorphic
    /// strip — the decl-consistent other half of the poly emission. Same
    /// in-order / cross-file-pre-pass discipline as [`type_synonyms`].
    poly_consts: std::collections::HashMap<String, CoqSortPolyShape>,
    /// The CURRENT declaration's derived sort-poly shape, set by the import
    /// loop around the decl's type/value normalization. When present, the
    /// Sort arm rewrites qualifying `QSort` payloads to `(Sort (Param u<q>))`
    /// dialect sorts; when absent, `QSort` stays out-of-model (fail closed).
    current_poly: Option<CoqSortPolyShape>,
    /// Global solved `uid → base` universe re-leveling map (see
    /// [`super::universe_releveling`]): named global levels the
    /// constraint-mining pre-pass RAISED above the historical base 1 so one
    /// Coq level renders to ONE consistent concrete level everywhere. The
    /// default empty map reproduces the old collapse byte-for-byte. `Arc`
    /// because the ctx is cloned per file.
    universe_bases: std::sync::Arc<super::universe_releveling::UniverseBaseMap>,
}

impl SerapiNormCtx {
    fn lookup(&self, name: &str, idx: u32) -> Option<&SerapiIndInfo> {
        self.inductives.get(&format!("{name}.{idx}"))
    }

    /// Register a constant's `(Π-telescope length, codomain sort)` shape, for
    /// constants whose type ends in a sort (see [`const_result_sort`]).
    fn register_const_sort(&mut self, name: &str, prods: u32, sort: CicSort) {
        self.const_result_sort
            .insert(name.to_string(), (prods, sort));
    }

    /// Look up a registered constant's result-sort shape.
    fn lookup_const_sort(&self, name: &str) -> Option<&(u32, CicSort)> {
        self.const_result_sort.get(name)
    }

    /// Register a declaration NAME as known to the session (constants, axioms,
    /// inductive bases — populated by the cross-file pre-passes). Consulted by
    /// [`resolve_kerpair_name`] to arbitrate KerPair Dual spellings.
    fn register_known_name(&mut self, name: &str) {
        self.known_names.insert(name.to_string());
    }

    /// Whether a fully-qualified name is a session-known declaration.
    fn is_known_name(&self, name: &str) -> bool {
        self.known_names.contains(name)
    }

    /// Register a relation-definition body (see [`relation_defs`]).
    fn register_relation_def(&mut self, name: &str, body: Sexp) {
        self.relation_defs.insert(name.to_string(), body);
    }

    /// Look up a registered relation-definition body by fully-qualified name.
    fn relation_def(&self, name: &str) -> Option<&Sexp> {
        self.relation_defs.get(name)
    }

    /// Register a constant's full declared type IF its codomain heads an
    /// inductive (see [`const_types`]); a no-op otherwise (bounds the map to
    /// the constants that can head an indexed-match discriminant).
    fn register_const_type(&mut self, name: &str, ty: &Sexp) {
        // Peel the Π/`let` telescope to the ultimate codomain: an ssreflect
        // `spec` lemma's return type carries `let: … in` definitions between
        // the Π binders, so a purely-Π peel (`dialect_prod_codomain`) stops at
        // the `LetIn` and misses the inductive head (`splitP`/`split_find_nth`
        // vs the direct-headed `leqP`). ζ-reduce those lets so such lemmas
        // register and can head an indexed-match discriminant.
        let cod = dialect_telescope_codomain(ty);
        // A constant can head an indexed-match discriminant either directly
        // (its codomain heads an inductive — `leqP`, spec lemmas) OR as a
        // PROJECTION combinator whose codomain is a bare telescope binder, i.e.
        // it returns one of its own arguments (`fst`/`snd`/`projT1`/`proj1_sig`/
        // `sval`/`id`). Such a combinator's INSTANTIATED codomain heads whatever
        // inductive the projected argument is: `fst (m = m') (n = n') pr` at a
        // `matrix` cast (`castmx`) has type `m = m'`, an `eq` head the indexed
        // `eq`-match must recover. Registering these lets `synthesize_app_disc_type`
        // instantiate them; the resulting recursor is speculative-marked and
        // fails closed at the kernel, so a mis-registration is a clean type-only
        // fallback (never masked taint).
        // A THIRD shape: the codomain heads a `Const` DEFINITION that abbreviates
        // the matched inductive under a `Π`-telescope — an ssreflect reflection
        // lemma `eqP : ∀ T, Equality.axiom (sort T) (eq_op T)` where
        // `Equality.axiom := λT e. ∀ x y, reflect (x = y) (e x y)`. Registering
        // such a constant lets `synthesize_app_disc_type` peel to the `Const`
        // node and DELTA-UNFOLD it (via [`const_defs`]) to expose the buried
        // `reflect` head. The resulting recursor is speculative-marked and fails
        // closed at the kernel, so a mis-registration is a clean type-only
        // fallback (never masked taint). Safe to over-register: a const whose
        // `Const`-headed codomain is NOT a registered unfoldable def simply makes
        // `synthesize_app_disc_type` return `None` (the pre-existing fail path).
        if dialect_ind_head(&cod).is_some()
            || dialect_rel_of(&cod).is_some()
            || dialect_const_head(&cod).is_some()
        {
            self.const_types.insert(name.to_string(), ty.clone());
        }
    }

    /// Look up a registered constant's full declared type by name.
    fn const_type(&self, name: &str) -> Option<&Sexp> {
        self.const_types.get(name)
    }

    /// Register a type-former DEFINITION body for mid-peel delta-unfolding (see
    /// [`const_defs`]).
    fn register_const_def(&mut self, name: &str, body: Sexp) {
        self.const_defs.insert(name.to_string(), body);
    }

    /// Look up a registered type-former definition body by fully-qualified name.
    fn const_def(&self, name: &str) -> Option<&Sexp> {
        self.const_defs.get(name)
    }

    /// Register a type-synonym definition body (see [`type_synonym_body`]),
    /// keeping BOTH the CIC form (for `arity_cic` unfolding) and the normalized
    /// dialect-sexp form (for `arity_sexp` unfolding in the Case/Fix registry).
    fn register_type_synonym(&mut self, name: &str, body: CicTerm, body_sexp: Sexp) {
        self.type_synonyms.insert(name.to_string(), body);
        self.type_synonyms_sexp.insert(name.to_string(), body_sexp);
    }

    /// Register ONLY the dialect-sexp form of a type synonym (the CIC form is
    /// left unregistered). Used by the cross-file pre-pass so a foreign module's
    /// inductive arity ending in the synonym unfolds in the reconstruction
    /// registry WITHOUT changing that inductive's shard declaration (`arity_cic`
    /// stays folded; the kernel δ-reduces it).
    fn register_type_synonym_sexp(&mut self, name: &str, body_sexp: Sexp) {
        self.type_synonyms_sexp.insert(name.to_string(), body_sexp);
    }

    /// Register a sort-polymorphic constant's shape (see [`poly_consts`]).
    fn register_poly_const(&mut self, name: &str, shape: CoqSortPolyShape) {
        self.poly_consts.insert(name.to_string(), shape);
    }

    /// Look up a registered sort-polymorphic constant's shape by name.
    fn poly_const(&self, name: &str) -> Option<&CoqSortPolyShape> {
        self.poly_consts.get(name)
    }

    /// Look up a registered type-synonym body by fully-qualified name.
    fn type_synonym(&self, name: &str) -> Option<&CicTerm> {
        self.type_synonyms.get(name)
    }

    /// Look up a registered type-synonym body in normalized dialect-sexp form.
    fn type_synonym_sexp(&self, name: &str) -> Option<&Sexp> {
        self.type_synonyms_sexp.get(name)
    }

    /// Register an inductive's shape. Failure to derive the shape only
    /// removes Case/Fix reconstruction for it (fail closed), never the
    /// inductive import itself.
    fn register(
        &mut self,
        ind_name: &str,
        block_idx: u32,
        num_params: u32,
        arity: &Sexp,
        ctor_types: &[Sexp],
    ) {
        self.register_with_lets(ind_name, block_idx, num_params, arity, ctor_types, &[]);
    }

    /// [`Self::register`] plus the per-constructor raw LetIn-laced telescope
    /// info recorded when a constructor type was zeta-reduced at parse time
    /// (see [`SerapiIndInfo::ctor_raw_lets`]); `raw_lets` entries missing or
    /// `None` mean the constructor telescope was already pure-Prod.
    fn register_with_lets(
        &mut self,
        ind_name: &str,
        block_idx: u32,
        num_params: u32,
        arity: &Sexp,
        ctor_types: &[Sexp],
        raw_lets: &[Option<(Sexp, Vec<bool>)>],
    ) {
        let arity_sort = dialect_sort_of(dialect_prod_codomain(arity));
        let mut ctor_recursive = Vec::with_capacity(ctor_types.len());
        for ct in ctor_types {
            // Walk past the leading `num_params` Prods (no substitution —
            // heads are unaffected) to compute the FIELD recursive flags.
            let mut chain = ct;
            for _ in 0..num_params {
                match chain {
                    Sexp::List(v)
                        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") =>
                    {
                        chain = &v[3];
                    }
                    _ => return, // malformed ctor: leave unregistered (fail closed)
                }
            }
            let mut flags = Vec::new();
            let mut fields = chain;
            while let Sexp::List(v) = fields {
                if v.len() != 4 || !matches!(&v[0], Sexp::Atom(h) if h == "Prod") {
                    break;
                }
                flags.push(matches!(
                    dialect_ind_head(&v[2]),
                    Some((n, i)) if n == ind_name && i == block_idx
                ));
                fields = &v[3];
            }
            ctor_recursive.push(flags);
        }
        let ctor_raw_lets = (0..ctor_types.len())
            .map(|j| raw_lets.get(j).cloned().flatten())
            .collect();
        self.inductives.insert(
            format!("{ind_name}.{block_idx}"),
            SerapiIndInfo {
                num_params,
                arity: arity.clone(),
                arity_sort,
                ctor_types: ctor_types.to_vec(),
                ctor_recursive,
                ctor_raw_lets,
                arity_synonym_unfolded: false,
            },
        );
    }

    /// Flag a registered inductive whose registry arity was δ-unfolded from a
    /// type-synonym codomain (see [`SerapiIndInfo::arity_synonym_unfolded`]).
    fn mark_arity_synonym_unfolded(&mut self, ind_name: &str, block_idx: u32) {
        if let Some(info) = self.inductives.get_mut(&format!("{ind_name}.{block_idx}")) {
            info.arity_synonym_unfolded = true;
        }
    }
}

/// Walk a dialect Prod spine to its codomain.
fn dialect_prod_codomain(sexp: &Sexp) -> &Sexp {
    let mut cur = sexp;
    while let Sexp::List(v) = cur {
        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") {
            cur = &v[3];
        } else {
            break;
        }
    }
    cur
}

/// Like [`dialect_prod_codomain`] but also ζ-reduces leading `let x := v in …`
/// bindings interleaved in the telescope, returning the ultimate codomain
/// (owned, since ζ substitutes). Used to decide whether a constant's declared
/// type ends in an inductive head even when its return type carries local
/// definitions (`splitP`'s `let: … in spec …`). The Π binders are peeled
/// without substitution — only the codomain HEAD is inspected by the caller,
/// so residual de-Bruijn references to the peeled binders are immaterial.
fn dialect_telescope_codomain(ty: &Sexp) -> Sexp {
    let mut cur = ty.clone();
    loop {
        match &cur {
            Sexp::List(v) if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") => {
                cur = v[3].clone();
            }
            Sexp::List(v) if v.len() == 5 && matches!(&v[0], Sexp::Atom(h) if h == "LetIn") => {
                match dialect_subst_binder0(&v[4], &v[2]) {
                    Ok(reduced) => cur = reduced,
                    Err(_) => return cur,
                }
            }
            _ => return cur,
        }
    }
}

/// Recognize a dialect sort node: `Prop`/`Set` atoms, `(Sort Prop)`,
/// `(Sort Set)`, `(Sort (Type u))`.
fn dialect_sort_of(sexp: &Sexp) -> Option<CicSort> {
    match sexp {
        Sexp::Atom(s) if s == "Prop" => Some(CicSort::Prop),
        Sexp::Atom(s) if s == "Set" => Some(CicSort::Set),
        Sexp::List(v) if v.len() == 2 && matches!(&v[0], Sexp::Atom(h) if h == "Sort") => {
            match &v[1] {
                Sexp::Atom(s) if s == "Prop" => Some(CicSort::Prop),
                Sexp::Atom(s) if s == "Set" => Some(CicSort::Set),
                Sexp::List(t) if t.len() == 2 && matches!(&t[0], Sexp::Atom(h) if h == "Type") => {
                    match &t[1] {
                        Sexp::Atom(u) => u.parse::<u32>().ok().map(CicSort::type_at),
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Count the leading Prods of a dialect telescope.
fn dialect_count_prods(sexp: &Sexp) -> u32 {
    let mut n = 0;
    let mut cur = sexp;
    while let Sexp::List(v) = cur {
        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") {
            n += 1;
            cur = &v[3];
        } else {
            break;
        }
    }
    n
}

/// Recognize a dialect de Bruijn reference: `(Rel k)` or a bare numeric atom
/// (both parse as `Rel` in [`sexp_to_cic`]).
fn dialect_rel_of(sexp: &Sexp) -> Option<u32> {
    match sexp {
        Sexp::Atom(a) => a.parse::<u32>().ok(),
        Sexp::List(v) if v.len() == 2 && matches!(&v[0], Sexp::Atom(h) if h == "Rel") => {
            match &v[1] {
                Sexp::Atom(a) => a.parse::<u32>().ok(),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Decompose a dialect term into its application head and argument spine
/// (dialect `App` is flat). Non-applications return themselves with no args.
fn dialect_app_parts(sexp: &Sexp) -> (&Sexp, &[Sexp]) {
    match sexp {
        Sexp::List(v) if v.len() >= 2 && matches!(&v[0], Sexp::Atom(h) if h == "App") => {
            (&v[1], &v[2..])
        }
        other => (other, &[]),
    }
}

/// Syntactic Prop-sortedness of a dialect TYPE within a constructor
/// telescope — the mirror of the kernel's `ctor_field_sort_levels` zero test
/// used by `elim_only_at_universe_zero`. `telescope` holds the binder types
/// OUTER to the examined type, outermost first (entries are matched
/// structurally only, so no de Bruijn adjustment is needed).
///
/// - `Some(true)`: the type provably lives in `Prop` (sort level 0);
/// - `Some(false)`: it provably does not;
/// - `None`: undecidable syntactically → the caller fails closed.
fn dialect_type_prop_sorted(ty: &Sexp, telescope: &[Sexp], ctx: &SerapiNormCtx) -> Option<bool> {
    // Π-chains: Prop is impredicative, so the chain is Prop-sorted iff its
    // codomain is (imax _ 0 = 0). A non-Prop codomain would need a max of
    // domain sorts — undecidable here, but every such chain is decided
    // `false` or `None` by the codomain cases below anyway.
    if let Sexp::List(v) = ty {
        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") {
            let extended: Vec<Sexp> = telescope
                .iter()
                .cloned()
                .chain(std::iter::once(v[2].clone()))
                .collect();
            return match dialect_type_prop_sorted(&v[3], &extended, ctx) {
                Some(true) => Some(true),
                Some(false) => Some(false),
                None => None,
            };
        }
    }
    // A sort itself (`x : Prop`) lives one level up: never Prop-sorted.
    if dialect_sort_of(ty).is_some() {
        return Some(false);
    }
    let (head, args) = dialect_app_parts(ty);
    // `Rel`-headed: the head's binder type decides. A field type must be
    // saturated (a partial application would not be a type); mismatched
    // arity is malformed → undecidable.
    if let Some(r) = dialect_rel_of(head) {
        let entry = telescope
            .len()
            .checked_sub(1 + r as usize)
            .map(|i| &telescope[i])?;
        let m = dialect_count_prods(entry);
        if args.len() as u32 != m {
            return None;
        }
        return match dialect_sort_of(dialect_prod_codomain(entry)) {
            Some(CicSort::Prop) => Some(true),
            Some(_) => Some(false),
            None => None,
        };
    }
    // Inductive-headed: the registered arity's result sort decides.
    if let Some((n, i)) = dialect_ind_head(head) {
        let info = ctx.lookup(n, i)?;
        if args.len() as u32 != dialect_count_prods(&info.arity) {
            return None;
        }
        return match dialect_sort_of(dialect_prod_codomain(&info.arity)) {
            Some(CicSort::Prop) => Some(true),
            Some(_) => Some(false),
            None => None,
        };
    }
    None // Const-headed (unfoldable definition), Case, unknown: undecidable
}

/// Walk a dialect constructor-type fragment calling `f(occ_args, depth)` on
/// every APPLICATION whose head is the inductive `(Ind name idx)` — the
/// mirror of the kernel's `for_each_ind_occurrence_depth` (bare unapplied
/// occurrences are not visited there either). Unknown binder-carrying heads
/// are an error so the promotion mirror fails closed rather than
/// mis-counting binders.
fn dialect_for_each_ind_occ(
    sexp: &Sexp,
    name: &str,
    idx: u32,
    depth: u32,
    f: &mut impl FnMut(&[Sexp], u32),
) -> Result<(), String> {
    match sexp {
        Sexp::Atom(_) => Ok(()),
        Sexp::List(items) => {
            let head = match items.first() {
                Some(Sexp::Atom(h)) => h.as_str(),
                _ => return Err("promotion mirror: headless list".to_string()),
            };
            match head {
                "App" if items.len() >= 2 => {
                    if matches!(dialect_ind_head(&items[1]), Some((n, i)) if n == name && i == idx)
                    {
                        f(&items[2..], depth);
                    }
                    for child in &items[1..] {
                        dialect_for_each_ind_occ(child, name, idx, depth, f)?;
                    }
                    Ok(())
                }
                "Rel" | "Sort" | "Const" | "Ind" | "Construct" | "Int" | "Float" | "Var" => Ok(()),
                "Prod" | "Lambda" if items.len() == 4 => {
                    dialect_for_each_ind_occ(&items[2], name, idx, depth, f)?;
                    dialect_for_each_ind_occ(&items[3], name, idx, depth + 1, f)
                }
                "LetIn" if items.len() == 5 => {
                    dialect_for_each_ind_occ(&items[2], name, idx, depth, f)?;
                    dialect_for_each_ind_occ(&items[3], name, idx, depth, f)?;
                    dialect_for_each_ind_occ(&items[4], name, idx, depth + 1, f)
                }
                other => Err(format!("promotion mirror: unsupported head `{other}`")),
            }
        }
    }
}

/// Compute the effective PARAMETER count for a single-type inductive by
/// detecting NON-UNIFORM leading parameters and demoting them to indices — the
/// transform that lets Coq's `Acc` / `clos_refl_trans` / `Rstar` families
/// replay through Clean's strict `add_inductive`. Lean-shaped kernels require
/// UNIFORM parameters: a "parameter" that a constructor re-instantiates with a
/// varying value in a recursive occurrence is really an INDEX (Coq's `Acc x`
/// recurses on `Acc y`, `y ≠ x`, so its `x` is a Lean index).
///
/// A leading parameter at position `i` (`0 ≤ i < declared`) is UNIFORM iff, in
/// every constructor, every recursive occurrence `(App (Ind …) a0 a1 …)` of
/// this inductive applies it to exactly the `i`-th parameter binder — i.e.
/// `ai` is that binder's de Bruijn `Rel`. In the normalized dialect `Rel` is
/// 0-based (innermost binder = 0), so at an occurrence reached after `depth`
/// binders the `i`-th parameter binder is `Rel (depth - 1 - i)`. Parameters
/// are a prefix, so the FIRST non-uniform position `k` demotes `k..declared`
/// to indices; the result is `min(declared, k)`.
///
/// SOUNDNESS / no-regression: this only ever SHRINKS `num_params`, and only
/// when a recursive occurrence provably breaks the uniform-spine rule the
/// kernel itself enforces. A fully-uniform inductive (every normal parametric
/// or indexed type — `list`, `eq`, `vec`, …) has no violating occurrence, so
/// `k = declared` and nothing changes. When a constructor is not analyzable
/// (an occurrence under an unsupported head), the walk errs and we KEEP
/// `declared` (fail closed — no demotion; the inductive stays rejected exactly
/// as before). The kernel re-checks the resulting `InductiveDecl`, so a wrong
/// count can only become a LOUD `add_inductive` rejection, never a silent
/// unsound accept.
fn compute_uniform_num_params(
    ind_name: &str,
    block_idx: u32,
    declared: u32,
    ctor_type_sexps: &[Sexp],
) -> u32 {
    if declared == 0 {
        return 0;
    }
    let mut k = declared;
    for ct in ctor_type_sexps {
        let mut first_nonuniform: Option<u32> = None;
        let walk = dialect_for_each_ind_occ(ct, ind_name, block_idx, 0, &mut |args, depth| {
            let lim = (declared as usize).min(args.len());
            for (i, arg) in args.iter().enumerate().take(lim) {
                // The i-th parameter binder, seen from `depth` binders in, is
                // Rel (depth - 1 - i). A well-formed occurrence sits inside all
                // parameters, so the subtraction never underflows; stay
                // conservative if it somehow does (skip — never a false flag).
                let expected = match depth.checked_sub(1).and_then(|d| d.checked_sub(i as u32)) {
                    Some(e) => e,
                    None => continue,
                };
                if dialect_rel_of(arg) != Some(expected) {
                    let iu = i as u32;
                    first_nonuniform = Some(first_nonuniform.map_or(iu, |p| p.min(iu)));
                }
            }
        });
        if walk.is_err() {
            return declared; // unanalyzable constructor → keep declared (fail closed)
        }
        if let Some(nu) = first_nonuniform {
            k = k.min(nu);
        }
    }
    k
}

/// Predict how many leading indices the kernel's `fixed_indices_to_params`
/// promotion would move to parameters when this inductive is replayed
/// through `add_inductive` — a syntactic mirror of clean-kernel's
/// `compute_fixed_index_mask` (env/inductive_fixed_indices.rs, single-type
/// block: mutual members are rejected at import). `None` when the shape is
/// undecidable (fail closed).
///
/// Promotion changes the recursor's params/motive/indices argument boundary,
/// so indexed `Case` lowering must fail closed whenever this is nonzero
/// (`eq` provably yields 0: its `y` index position exceeds `eq_refl`'s
/// arity, so the index is not fixed).
fn predicted_fixed_index_promotion(
    info: &SerapiIndInfo,
    ind_name: &str,
    ind_idx: u32,
) -> Option<u32> {
    let n_idx = info.num_indices()? as usize;
    if n_idx == 0 {
        return Some(0);
    }
    let np = info.num_params as usize;
    let mut mask = vec![true; n_idx];
    for ct in &info.ctor_types {
        let (binders, ret) = dialect_peel_prods(ct);
        let ctor_arity = binders.len();
        let (_, ret_args) = dialect_app_parts(&ret);
        // Phase 1 (direct): the ctor argument at position np+i must appear
        // as the SAME variable in the result's argument at that position.
        for (i, m) in mask.iter_mut().enumerate() {
            if !*m {
                continue;
            }
            let ap = np + i;
            if ap >= ctor_arity || ap >= ret_args.len() {
                *m = false;
                continue;
            }
            let expected = (ctor_arity - 1 - ap) as u32;
            if dialect_rel_of(&ret_args[ap]) != Some(expected) {
                *m = false;
            }
        }
        // Phase 2 (recursive occurrences): every occurrence of the inductive
        // in a field's type must use the same variable at each candidate
        // index position.
        for (bidx, (_, dom)) in binders.iter().enumerate().skip(np) {
            let res =
                dialect_for_each_ind_occ(dom, ind_name, ind_idx, 0, &mut |occ_args, extra| {
                    let total = bidx as u32 + extra;
                    for (i, m) in mask.iter_mut().enumerate() {
                        if !*m {
                            continue;
                        }
                        let ap = (np + i) as u32;
                        if ap as usize >= occ_args.len() || ap >= total {
                            *m = false;
                            continue;
                        }
                        if dialect_rel_of(&occ_args[ap as usize]) != Some(total - 1 - ap) {
                            *m = false;
                        }
                    }
                });
            if res.is_err() {
                return None; // untraversable ctor shape → undecidable
            }
        }
    }
    Some(mask.iter().take_while(|&&b| b).count() as u32)
}

/// Head of a dialect term as an inductive reference: `(Ind n i)` or
/// `(App (Ind n i) ...)`.
fn dialect_ind_head(sexp: &Sexp) -> Option<(&str, u32)> {
    let target = match sexp {
        Sexp::List(v) if !v.is_empty() && matches!(&v[0], Sexp::Atom(h) if h == "App") => {
            v.get(1)?
        }
        other => other,
    };
    match target {
        Sexp::List(v) if v.len() >= 3 && matches!(&v[0], Sexp::Atom(h) if h == "Ind") => {
            match (&v[1], &v[2]) {
                (Sexp::Atom(n), Sexp::Atom(i)) => Some((n.as_str(), i.parse::<u32>().ok()?)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The `Const` name heading `sexp` (bare `(Const n)` or `(App (Const n) …)`),
/// mirroring [`dialect_ind_head`] for defined constants.
fn dialect_const_head(sexp: &Sexp) -> Option<&str> {
    let target = match sexp {
        Sexp::List(v) if !v.is_empty() && matches!(&v[0], Sexp::Atom(h) if h == "App") => {
            v.get(1)?
        }
        other => other,
    };
    match target {
        Sexp::List(v) if v.len() >= 2 && matches!(&v[0], Sexp::Atom(h) if h == "Const") => {
            match &v[1] {
                Sexp::Atom(n) => Some(n.as_str()),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Whether a dialect definition VALUE is a relation abbreviation: a (possibly
/// empty) `Lambda`-telescope whose body is headed by an INDUCTIVE — e.g.
/// `lt := λn m. le (S n) m`. Such a definition is registered
/// ([`SerapiNormCtx::register_relation_def`]) so a `match` discriminant of type
/// `lt n m` can be delta-unfolded to reveal the `le` it heads.
fn dialect_relation_def_body(value: &Sexp) -> bool {
    let mut cur = value;
    while let Sexp::List(v) = cur {
        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Lambda") {
            cur = &v[3];
        } else {
            break;
        }
    }
    let (head, _) = dialect_app_parts(cur);
    dialect_ind_head(head).is_some()
}

/// Whether a dialect definition VALUE is a TYPE-FORMER abbreviation usable for
/// mid-peel delta-unfolding: a (possibly empty) `Lambda`-telescope whose body,
/// after peeling its own `Π`/`let` telescope, heads an INDUCTIVE — e.g.
/// `Equality.axiom := λT e. ∀ x y, reflect (x = y) (e x y)`. This is the
/// `Π`-bearing generalization of [`dialect_relation_def_body`] (which requires
/// the body to head the inductive with NO intervening `Π`s). Registered into
/// [`SerapiNormCtx::const_defs`] so [`synthesize_app_disc_type`] can β-reduce
/// past a `Const`-definition head in a reflection lemma's codomain.
fn dialect_const_def_body(value: &Sexp) -> bool {
    let mut cur = value;
    while let Sexp::List(v) = cur {
        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Lambda") {
            cur = &v[3];
        } else {
            break;
        }
    }
    // Only register genuinely `Π`-bearing type-formers here; a body that already
    // heads an inductive with no `Π`s is a `relation_defs` entry, and a bare
    // (0-`Lambda`) sort/inductive alias is a `type_synonyms` concern. This keeps
    // the map to the reflection-lemma shape the peel actually needs.
    let (peeled_head, _) = dialect_app_parts(cur);
    if dialect_ind_head(peeled_head).is_some() {
        return false;
    }
    let cod = dialect_telescope_codomain(cur);
    dialect_ind_head(&cod).is_some()
}

/// Delta-unfold ONE step of a `Const`-definition-headed dialect type: if `body`
/// heads a registered [`SerapiNormCtx::const_defs`] type-former
/// (`Equality.axiom (sort T) (eq_op T)`), β-reduce the registered `λ`-telescope
/// body at `body`'s argument spine (outermost-first / application order, one `λ`
/// per argument — exactly as [`unfold_relation_def_head`] does), exposing the
/// buried `Π`/inductive structure (`∀ x y, reflect (x = y) (eq_op x y)`).
/// Returns `None` when the head is not a registered const-def or is applied to
/// more arguments than the body has leading `λ`s (fail closed). Sets the
/// speculative-conversion marker: the unfold is a best-effort abbreviation
/// resolution the kernel re-check arbitrates.
fn dialect_delta_unfold_head(body: &Sexp, ctx: &SerapiNormCtx) -> Option<Sexp> {
    let cname = dialect_const_head(body)?;
    let def = ctx.const_def(cname)?;
    let (_, args) = dialect_app_parts(body);
    let mut out = def.clone();
    for a in args {
        let Sexp::List(lv) = &out else { return None };
        if lv.len() != 4 || !matches!(&lv[0], Sexp::Atom(h) if h == "Lambda") {
            return None;
        }
        out = dialect_subst_binder0(&lv[3], a).ok()?;
    }
    SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
    Some(out)
}

/// Whether a normalized dialect term is a `Π` node (a 4-element `(Prod …)`).
fn dialect_is_prod(sexp: &Sexp) -> bool {
    matches!(sexp, Sexp::List(v) if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod"))
}

/// Bound on chained `Const`-definition delta-unfolds during discriminant-type
/// synthesis (see [`synthesize_app_disc_type`]). Coq's δ-reduction is acyclic
/// and reflection-lemma abbreviation chains are shallow (`eqP → Equality.axiom →
/// reflect`), so a small cap is ample; it only guards against a pathological
/// input and fails closed (a clean type-only fallback) when hit.
const DELTA_UNFOLD_STEP_LIMIT: u32 = 16;

/// Delta-unfold a `match` discriminant TYPE whose head is a registered
/// relation-definition (`lt n m` → `le (S n) m`): β-reduce the def body with the
/// discriminant type's argument spine. Returns the unfolded dialect type, or
/// `None` when the head is not a registered relation def or is not fully applied
/// to the def's λ-telescope. Sets the speculative-conversion marker: the unfold
/// is a best-effort abbreviation resolution, so a downstream kernel rejection
/// fails closed to a clean type-only axiom.
fn unfold_relation_def_head(disc_ty: &Sexp, ctx: &SerapiNormCtx) -> Option<Sexp> {
    let cname = dialect_const_head(disc_ty)?;
    let value = ctx.relation_def(cname)?;
    let (_, args) = dialect_app_parts(disc_ty);
    // β-reduce: peel one λ per argument (outermost-first / application order,
    // exactly as the constructor-parameter substitution does), substituting the
    // argument for the bound variable. Fewer λs than args ⇒ not this shape.
    let mut body = value.clone();
    for a in args {
        let Sexp::List(lv) = &body else { return None };
        if lv.len() != 4 || !matches!(&lv[0], Sexp::Atom(h) if h == "Lambda") {
            return None;
        }
        body = dialect_subst_binder0(&lv[3], a).ok()?;
    }
    SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
    Some(body)
}

/// Synthesize the TYPE of a compound-application `match` discriminant by
/// instantiating its HEAD's declared/binder type at the argument spine: peel
/// one `Π` per argument (application order) and substitute it, exactly as
/// [`unfold_relation_def_head`] β-reduces a relation definition. The head type
/// is placed in the Case context BEFORE the substitution loop, and every
/// argument (already normalized in the Case context) substitutes against it, so
/// application typing gives back the discriminant's own type by construction.
///
/// Two head shapes are recognized (both give a `Prod`-telescope to instantiate):
/// - `(Const c) a…` — the registered CLOSED declared type of `c`
///   (`sqrt_iter k p q r`, `leb n m`);
/// - `(Rel r) a…` — a locally-bound function/hypothesis of function type
///   (an ssreflect spec term bound in an enclosing binder, e.g.
///   `p (contents m) x (dvdz_zcontents …)` heading `eq_xor_neq …`); its binder
///   type comes from `bctx` at the binding site and is lifted by `r + 1` into
///   the Case context, mirroring the bare-`Rel` discriminant path.
///
/// Returns `None` when the head is neither of those, is not registered / not in
/// scope, or is not fully applied to its `Π`-telescope (fail closed). Sets the
/// speculative-conversion marker: a synthesized discriminant type feeds a
/// derived recursor spine, so a kernel rejection fails closed to a clean
/// type-only axiom (it can never mint a wrong `KernelVerified`).
/// Env-gated (`CLEAN_DISC_FAIL_LOG`) one-line diagnostic for an indexed-match
/// discriminant whose type could not be recovered. Prints the failure site and
/// the head shape so the residual tail can be mapped without a full re-census.
/// No-op unless the env var is set; never affects translation output.
fn debug_disc_fail(site: &str, disc: &Sexp) {
    if std::env::var_os("CLEAN_DISC_FAIL_LOG").is_none() {
        return;
    }
    let (head, args) = dialect_app_parts(disc);
    let head_tag = match head {
        Sexp::Atom(a) => format!("atom:{a}"),
        Sexp::List(v) => match v.first() {
            Some(Sexp::Atom(h)) => {
                if h == "Const" {
                    format!("Const:{}", dialect_const_head(head).unwrap_or("?"))
                } else {
                    h.clone()
                }
            }
            _ => "list".to_string(),
        },
    };
    eprintln!("[disc-fail {site}] head={head_tag} nargs={}", args.len());
}

fn synthesize_app_disc_type(
    disc: &Sexp,
    ctx: &SerapiNormCtx,
    bctx: &[Option<Sexp>],
) -> Option<Sexp> {
    let (head, args) = dialect_app_parts(disc);
    // The head's type, expressed in the Case context.
    let mut body: Sexp = if let Some(cname) = dialect_const_head(head) {
        ctx.const_type(cname)?.clone()
    } else {
        let r = dialect_rel_of(head)?;
        dialect_lift(bctx_lookup(bctx, r)?, r + 1, 0).ok()?
    };
    // Instantiate at the argument spine: for each argument, ζ-reduce any leading
    // `let x := v in …` (the head type's telescope can carry local definitions
    // between the Π binders — an ssreflect `spec` lemma's `let: … in`) so the
    // next Π binder is exposed, then peel it and substitute the argument.
    for a in args {
        body = dialect_zeta_head(body).ok()?;
        // The next binder may be buried behind a `Const`-DEFINITION head: an
        // ssreflect reflection lemma's codomain is `Equality.axiom (sort T) (op)`
        // — a `Const` abbreviation of `∀ x y, reflect …`. DELTA-UNFOLD such heads
        // (β-reducing the registered def body at its arg spine) until a `Π` is
        // exposed, so the peel can continue substituting the remaining
        // arguments. Bounded to guard against a pathological cyclic abbreviation
        // (Coq δ-unfolding is acyclic, but fail closed regardless).
        let mut guard = 0u32;
        while !dialect_is_prod(&body) && guard < DELTA_UNFOLD_STEP_LIMIT {
            match dialect_delta_unfold_head(&body, ctx) {
                Some(unfolded) => body = dialect_zeta_head(unfolded).ok()?,
                None => break,
            }
            guard += 1;
        }
        let Sexp::List(pv) = &body else { return None };
        if pv.len() != 4 || !matches!(&pv[0], Sexp::Atom(h) if h == "Prod") {
            return None;
        }
        body = dialect_subst_binder0(&pv[3], a).ok()?;
    }
    // The discriminant's own type may still be under a residual `let` (the
    // spec-family application head is inside the LetIn body) — ζ-reduce it so
    // the caller's `dialect_ind_head` sees the matched inductive.
    body = dialect_zeta_head(body).ok()?;
    // …or under a residual `Const`-DEFINITION head (`Equality.axiom (sort T) (op)`
    // when the discriminant is applied only to the reflection lemma's implicit
    // type argument): DELTA-UNFOLD until an inductive head is reached so the
    // caller's `dialect_ind_head` sees the matched inductive. Stops at the first
    // non-const-def head (an inductive-headed type is left untouched — this
    // never rewrites a body that already heads the matched inductive).
    let mut guard = 0u32;
    while dialect_ind_head(&body).is_none() && guard < DELTA_UNFOLD_STEP_LIMIT {
        match dialect_delta_unfold_head(&body, ctx) {
            Some(unfolded) => body = dialect_zeta_head(unfolded).ok()?,
            None => break,
        }
        guard += 1;
    }
    SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
    Some(body)
}

/// ζ-reduce every LEADING `(LetIn name value type body)` of a dialect type
/// (`let x := v in T` → `T[x := v]`), so a Π/Ind head buried under local
/// definitions is exposed. Non-`LetIn` heads are returned unchanged. Errors
/// only if the de-Bruijn substitution itself is malformed (fail closed).
fn dialect_zeta_head(mut body: Sexp) -> Result<Sexp, String> {
    while let Sexp::List(v) = &body {
        if v.len() == 5 && matches!(&v[0], Sexp::Atom(h) if h == "LetIn") {
            // (LetIn name value type body): substitute `value` (v[2]) for the
            // bound variable in `body` (v[4]).
            let reduced = dialect_subst_binder0(&v[4], &v[2])?;
            body = reduced;
        } else {
            break;
        }
    }
    Ok(body)
}

fn rel_sexp(k: u32) -> Sexp {
    Sexp::List(vec![
        Sexp::Atom("Rel".to_string()),
        Sexp::Atom(k.to_string()),
    ])
}

/// Binder-aware `Rel` transformation over NORMALIZED dialect terms. `f`
/// receives `(index, cutoff)` for every `Rel` (bare numeric atoms included —
/// they parse as `Rel` in `sexp_to_cic`) and returns its replacement.
/// Unknown heads are a hard error (fail closed — never silently skip a
/// binder-structure we do not understand).
fn dialect_map_rels(
    sexp: &Sexp,
    cutoff: u32,
    f: &mut dyn FnMut(u32, u32) -> Result<Sexp, String>,
) -> Result<Sexp, String> {
    let recurse = |items: &[Sexp],
                   offsets: &[u32],
                   f: &mut dyn FnMut(u32, u32) -> Result<Sexp, String>|
     -> Result<Vec<Sexp>, String> {
        debug_assert_eq!(items.len(), offsets.len());
        items
            .iter()
            .zip(offsets.iter())
            .map(|(it, off)| dialect_map_rels(it, cutoff + off, f))
            .collect()
    };
    match sexp {
        Sexp::Atom(s) => {
            if let Ok(k) = s.parse::<u32>() {
                return f(k, cutoff);
            }
            Ok(sexp.clone())
        }
        Sexp::List(items) => {
            let head = match items.first() {
                Some(Sexp::Atom(h)) => h.as_str(),
                _ => return Err("dialect traversal: headless list".to_string()),
            };
            match head {
                "Rel" if items.len() == 2 => match &items[1] {
                    Sexp::Atom(s) => {
                        let k = s
                            .parse::<u32>()
                            .map_err(|_| "dialect traversal: bad Rel index".to_string())?;
                        f(k, cutoff)
                    }
                    _ => Err("dialect traversal: bad Rel payload".to_string()),
                },
                "Sort" | "Const" | "Ind" | "Construct" | "Int" | "Float" | "Var"
                | "CoqUnsupported" => Ok(sexp.clone()),
                "Prod" | "Lambda" if items.len() == 4 => Ok(Sexp::List(vec![
                    items[0].clone(),
                    items[1].clone(),
                    dialect_map_rels(&items[2], cutoff, f)?,
                    dialect_map_rels(&items[3], cutoff + 1, f)?,
                ])),
                "LetIn" if items.len() == 5 => Ok(Sexp::List(vec![
                    items[0].clone(),
                    items[1].clone(),
                    dialect_map_rels(&items[2], cutoff, f)?,
                    dialect_map_rels(&items[3], cutoff, f)?,
                    dialect_map_rels(&items[4], cutoff + 1, f)?,
                ])),
                "App" => {
                    let mut out = vec![items[0].clone()];
                    out.extend(recurse(&items[1..], &vec![0; items.len() - 1], f)?);
                    Ok(Sexp::List(out))
                }
                // Normalized projection node `(Proj <struct-name> <field-idx>
                // <record>)` (see `convert_serapi_proj`): the struct name and the
                // NUMERIC field index are payloads, NOT `Rel`s — only the record
                // term is a subterm, and it shares this node's binder context (a
                // projection binds nothing). Recurse ONLY into the record; clone
                // the name/field-idx verbatim so the numeric field index is never
                // mistaken for a de Bruijn `Rel`. Without this arm the secondary
                // rel-remap (lift / index-promotion / Case-Fix rebind) over any
                // value containing a `Proj` errs `unsupported head Proj`, which
                // hard-fails the value and drops the constant to a type-only
                // stand-in even when the value is otherwise translatable.
                "Proj" if items.len() == 4 => Ok(Sexp::List(vec![
                    items[0].clone(),
                    items[1].clone(),
                    items[2].clone(),
                    dialect_map_rels(&items[3], cutoff, f)?,
                ])),
                "Case" => {
                    // (Case (Ind ..) (Params p..) (Motive m) (Discriminant d)
                    //       (Branch b)..) — every payload is a self-contained
                    // term in the SAME context as the Case node.
                    let mut out = vec![items[0].clone(), items[1].clone()];
                    for part in &items[2..] {
                        let Sexp::List(pv) = part else {
                            return Err("dialect traversal: malformed Case part".to_string());
                        };
                        if pv.is_empty() {
                            return Err("dialect traversal: empty Case part".to_string());
                        }
                        let mut np = vec![pv[0].clone()];
                        np.extend(recurse(&pv[1..], &vec![0; pv.len() - 1], f)?);
                        out.push(Sexp::List(np));
                    }
                    Ok(Sexp::List(out))
                }
                "StructFix" => {
                    // Components sit INSIDE the binder lambdas the lowering
                    // wraps: Pre[i] at +i, StructTy at +pre, Post[i] at
                    // +pre+1+i, Params/Motive/Branch at +pre+1+post.
                    let mut pre_len: u32 = 0;
                    let mut post_len: u32 = 0;
                    for part in &items[2..] {
                        if let Sexp::List(pv) = part {
                            match pv.first() {
                                Some(Sexp::Atom(t)) if t == "Pre" => {
                                    pre_len = (pv.len() - 1) as u32;
                                }
                                Some(Sexp::Atom(t)) if t == "Post" => {
                                    post_len = (pv.len() - 1) as u32;
                                }
                                _ => {}
                            }
                        }
                    }
                    let inner = pre_len + 1 + post_len;
                    let mut out = vec![items[0].clone(), items[1].clone()];
                    for part in &items[2..] {
                        let Sexp::List(pv) = part else {
                            return Err("dialect traversal: malformed StructFix part".to_string());
                        };
                        let tag = match pv.first() {
                            Some(Sexp::Atom(t)) => t.as_str(),
                            _ => return Err("dialect traversal: untagged StructFix part".into()),
                        };
                        let offsets: Vec<u32> = match tag {
                            "RecLevel" => {
                                out.push(part.clone());
                                continue;
                            }
                            "Pre" => (0..pre_len).collect(),
                            "StructTy" => vec![pre_len],
                            "Post" => (0..post_len).map(|i| pre_len + 1 + i).collect(),
                            "Params" | "Indices" | "Motive" | "Branch" => {
                                vec![inner; pv.len() - 1]
                            }
                            other => {
                                return Err(format!(
                                    "dialect traversal: unknown StructFix part `{other}`"
                                ))
                            }
                        };
                        let mut np = vec![pv[0].clone()];
                        np.extend(recurse(&pv[1..], &offsets, f)?);
                        out.push(Sexp::List(np));
                    }
                    Ok(Sexp::List(out))
                }
                "Fix" | "CoFix" if items.len() == 3 => {
                    // (Fix ((name ty body)...) i): types in the OUTER context,
                    // bodies under all N fix binders.
                    let Sexp::List(bodies) = &items[1] else {
                        return Err("dialect traversal: malformed Fix bodies".to_string());
                    };
                    let n = bodies.len() as u32;
                    let mut nb = Vec::with_capacity(bodies.len());
                    for b in bodies {
                        let Sexp::List(bv) = b else {
                            return Err("dialect traversal: malformed Fix body".to_string());
                        };
                        if bv.len() < 3 {
                            return Err("dialect traversal: short Fix body".to_string());
                        }
                        let mut nbv = bv.clone();
                        nbv[1] = dialect_map_rels(&bv[1], cutoff, f)?;
                        nbv[2] = dialect_map_rels(&bv[2], cutoff + n, f)?;
                        nb.push(Sexp::List(nbv));
                    }
                    Ok(Sexp::List(vec![
                        items[0].clone(),
                        Sexp::List(nb),
                        items[2].clone(),
                    ]))
                }
                other => Err(format!("dialect traversal: unsupported head `{other}`")),
            }
        }
    }
}

/// Lift free `Rel`s (index ≥ `cutoff`) by `amount`.
fn dialect_lift(sexp: &Sexp, amount: u32, cutoff: u32) -> Result<Sexp, String> {
    if amount == 0 {
        return Ok(sexp.clone());
    }
    dialect_map_rels(sexp, cutoff, &mut |k, c| {
        Ok(rel_sexp(if k >= c { k + amount } else { k }))
    })
}

/// Instantiate the OUTERMOST binder of `body` with `value` (standard de
/// Bruijn substitution: `Rel cutoff := lift(value, cutoff)`, higher `Rel`s
/// decrement).
fn dialect_subst_binder0(body: &Sexp, value: &Sexp) -> Result<Sexp, String> {
    dialect_map_rels(body, 0, &mut |k, c| {
        if k == c {
            dialect_lift(value, c, 0)
        } else if k > c {
            Ok(rel_sexp(k - 1))
        } else {
            Ok(rel_sexp(k))
        }
    })
}

/// Zeta-reduce the leading Prod/LetIn TELESCOPE of a normalized dialect
/// constructor type: each `(LetIn name value ty body)` declaration on the
/// spine is removed by substituting its value into the rest of the telescope
/// (via [`dialect_subst_binder0`]), yielding the pure-Prod field telescope
/// the kernel's recursor generator expects. Returns `None` when the spine
/// has no `LetIn` — the common case, leaving every currently-working
/// constructor type untouched — otherwise `Some((reduced, decl_is_let))`
/// where `decl_is_let` flags each declaration of the ORIGINAL telescope
/// (`true` at let positions), the shape a compact `Case` node's branch
/// binder array follows. Only telescope-SPINE `LetIn`s reduce; a `LetIn`
/// inside a field type is not a branch binder and stays put. A substitution
/// failure (an out-of-model node under the spine) also returns `None`, so
/// the raw type keeps its pre-existing fail-closed path.
fn zeta_reduce_ctor_telescope(ty: &Sexp) -> Option<(Sexp, Vec<bool>)> {
    // Cheap borrow-only scan: bail (byte-identical) unless the spine has a LetIn.
    let mut probe = ty;
    loop {
        let Sexp::List(v) = probe else { return None };
        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") {
            probe = &v[3];
        } else if v.len() == 5 && matches!(&v[0], Sexp::Atom(h) if h == "LetIn") {
            break;
        } else {
            return None;
        }
    }
    let mut flags = Vec::new();
    let mut kept: Vec<(Sexp, Sexp)> = Vec::new(); // (binder name, field type)
    let mut cur = ty.clone();
    while let Sexp::List(v) = &cur {
        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") {
            flags.push(false);
            kept.push((v[1].clone(), v[2].clone()));
            let next = v[3].clone();
            cur = next;
        } else if v.len() == 5 && matches!(&v[0], Sexp::Atom(h) if h == "LetIn") {
            flags.push(true);
            let next = dialect_subst_binder0(&v[4], &v[2]).ok()?;
            cur = next;
        } else {
            break;
        }
    }
    let mut acc = cur;
    for (name, fty) in kept.into_iter().rev() {
        acc = Sexp::List(vec![Sexp::Atom("Prod".to_string()), name, fty, acc]);
    }
    Some((acc, flags))
}

/// Zeta-reduce the leading Prod/LetIn spine of a normalized dialect inductive
/// ARITY — the arity-side companion of [`zeta_reduce_ctor_telescope`]. An HB
/// `mixin_of` record's arity interleaves a packing `let` in its leading Π
/// PARAMETER spine (`∀ T0 b, let T := Pack T0 b in ∀ p3, Type`); the kernel's
/// `count_pi_args` counts only leading CONSECUTIVE Π and STOPS at the `LetIn`,
/// so the family-replay metadata builder (`build_inductive_replay_metadata`)
/// reports an arity of 2 against a stamped `num_params` of 3, its
/// `num_params > arity` guard returns `None`, and the family falls to a clean
/// stand-in instead of reaching the kernel.
///
/// Substituting each spine `let` yields the pure-Π parameter telescope of
/// length ≥ `num_params` ending in the codomain sort, so `count_pi_args`
/// matches `num_params` and `check_block_agreement` can walk the parameters.
/// This DELEGATES to the shared spine reducer, so the arity ζ-reduces the
/// IDENTICAL leading lets the constructor already did — a structural mismatch
/// in the parameter prefixes would be a loud `add_inductive` rejection, never a
/// silent accept. Returns `None` (byte-identical) for a pure-Π arity — every
/// other inductive — leaving it untouched; the kernel re-checks the reduced
/// declaration either way (fail closed).
fn zeta_reduce_arity_telescope(arity: &Sexp) -> Option<Sexp> {
    zeta_reduce_ctor_telescope(arity).map(|(reduced, _decl_is_let)| reduced)
}

/// Re-collapse a raw SerAPI `(Sort (Type <payload>))` node on the FLAT level
/// scale — the scale [`universe_level_to_flat`] actually lowers on, where
/// `Type n` becomes `Sort n` and `Set` is `Sort 1`. Each arm is
/// `flat_base(datum) + increment` with `flat_base = 1` for every in-model
/// datum (named `Level`, bound `Var`, pierced `Set`), floored at 1, so
/// `Type@{Set+1}` lands at `Type 2` (`Sort 2`) — STRICTLY above `Set`.
///
/// [`classify_serapi_type_universe`]'s pierced-`Set` arm uses base 0 on an
/// intended "`Type 0` = `Set`" scale that the flat lowering does not share
/// (`Type 0` lowers to `Sort 0` = `Prop`), so `Set+1` under-collapses to
/// `Set` itself. That is invisible in ordinary term positions (cumulativity
/// masks an undershoot), but an inductive ARITY faces the kernel's STRICT
/// per-field universe check: a `Set`-sorted field requires the arity to sit
/// at `Sort 2`, so an under-collapsed `Type@{Set+1}` record arity is
/// rejected. Used (scoped) by [`parse_serapi_inductive`] to lift the arity
/// of a zeta-reduced let-field record; the kernel re-checks the lifted
/// declaration, so a wrong lift is a loud rejection, never a silent accept.
/// Returns `None` for anything that is not a `(Sort (Type …))` payload of
/// in-model arms.
fn serapi_sort_flat_type_level(raw_sort: &Sexp) -> Option<u32> {
    let Sexp::List(v) = raw_sort else { return None };
    if v.len() != 2 || !matches!(&v[0], Sexp::Atom(h) if h == "Sort") {
        return None;
    }
    let Sexp::List(t) = &v[1] else { return None };
    if t.len() != 2 || !matches!(&t[0], Sexp::Atom(h) if h == "Type") {
        return None;
    }
    let Sexp::List(pairs) = &t[1] else {
        return None;
    };
    if pairs.is_empty() {
        return None;
    }
    let mut level: u32 = 1;
    for entry in pairs {
        let Sexp::List(pair) = entry else { return None };
        if pair.len() != 2 {
            return None;
        }
        let increment: u32 = match &pair[1] {
            Sexp::Atom(s) => s.parse().ok()?,
            _ => return None,
        };
        let datum = match &pair[0] {
            Sexp::List(fields) => fields.iter().find_map(|f| match f {
                Sexp::List(kv)
                    if kv.len() == 2 && matches!(&kv[0], Sexp::Atom(k) if k == "data") =>
                {
                    Some(&kv[1])
                }
                _ => None,
            }),
            _ => None,
        };
        // In-model datums all sit at Set level (flat 1) monomorphically: the
        // pierced runtime `Set` IS `Sort 1`, and named/bound levels collapse
        // to `Set` (the same monomorphic treatment as the classifier).
        let base: u32 = match datum {
            Some(Sexp::List(dv)) if matches!(dv.first(), Some(Sexp::Atom(h)) if h == "Level" || h == "Var") => {
                1
            }
            Some(Sexp::Atom(a)) if a == "SProp" => 1,
            _ => return None,
        };
        level = level.max(base + increment);
    }
    Some(level)
}

/// The concrete level of a normalized dialect `(Sort (Type k))` node.
fn dialect_sort_concrete_type_level(sort: &Sexp) -> Option<u32> {
    match dialect_sort_of(sort)? {
        CicSort::Type(l) => l.as_concrete_type(),
        _ => None,
    }
}

/// Replace the codomain of a (zeta-reduced) pure-Π arity Sexp with `new_cod`,
/// walking only leading `Prod` binders. Non-`Prod` codomain is replaced.
fn replace_prod_codomain_sexp(arity: &Sexp, new_cod: &Sexp) -> Sexp {
    if let Sexp::List(v) = arity {
        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") {
            return Sexp::List(vec![
                v[0].clone(),
                v[1].clone(),
                v[2].clone(),
                replace_prod_codomain_sexp(&v[3], new_cod),
            ]);
        }
    }
    new_cod.clone()
}

/// [`replace_prod_codomain_sexp`] on the parallel [`CicTerm`] arity.
fn replace_prod_codomain_cic(arity: &CicTerm, new_cod: CicTerm) -> CicTerm {
    match arity {
        CicTerm::Prod(nm, dom, body) => CicTerm::Prod(
            nm.clone(),
            dom.clone(),
            Box::new(replace_prod_codomain_cic(body, new_cod)),
        ),
        _ => new_cod,
    }
}

/// Lift the CODOMAIN sort of a zeta-reduced record arity (a pure-Π telescope
/// ending in a `Sort`) to its flat-scale universe collapse — the spine-LetIn
/// sibling of the bare-`Sort` let-field lift in [`parse_serapi_inductive`].
///
/// [`classify_serapi_type_universe`] under-collapses a pierced `Type@{Set+n}`
/// to `Set` itself (base-0 pierced-`Set` arm), invisible in ordinary term
/// positions but rejected by the kernel's STRICT per-field universe check once
/// a zeta-reduced record exposes its full field telescope. Lifts the codomain
/// to `serapi_sort_flat_type_level` when it strictly exceeds the collapsed
/// level. Returns `None` (byte-identical) for a `Prop` codomain, a named/opaque
/// `Type` level (no concrete collapse to exceed), or a non-`Type` codomain. The
/// kernel re-checks the lifted declaration — a wrong lift is a loud rejection,
/// never a silent accept.
fn lift_arity_codomain_universe(arity_sexp: &Sexp, arity_cic: &CicTerm) -> Option<(Sexp, CicTerm)> {
    // Peel the (already zeta-reduced) Π telescope to its codomain sort.
    let mut cod = arity_sexp;
    while let Sexp::List(v) = cod {
        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") {
            cod = &v[3];
        } else {
            break;
        }
    }
    let flat = serapi_sort_flat_type_level(cod)?;
    let collapsed = dialect_sort_concrete_type_level(cod)?;
    if flat <= collapsed {
        return None;
    }
    let lifted_sort_sexp = Sexp::List(vec![
        Sexp::Atom("Sort".to_string()),
        Sexp::List(vec![
            Sexp::Atom("Type".to_string()),
            Sexp::Atom(flat.to_string()),
        ]),
    ]);
    Some((
        replace_prod_codomain_sexp(arity_sexp, &lifted_sort_sexp),
        replace_prod_codomain_cic(arity_cic, CicTerm::Sort(CicSort::type_at(flat))),
    ))
}

/// Reconstruct a compact-`Case` branch over a constructor whose ORIGINAL
/// telescope carries LET-BOUND declarations (`ci_cstr_ndecls >
/// ci_cstr_nargs` — e.g. `Build_ConstructiveReals`, 35 decls = 29 fields +
/// 6 lets). The raw branch body binds the FULL declaration telescope, but
/// the registered (zeta-reduced) inductive's recursor minor premise binds
/// only the real fields, so the let binders must be substituted away: the
/// params-instantiated raw telescope is rebuilt over the normalized body as
/// a `Lambda`/`LetIn` spine and each spine `LetIn` zeta-reduced. Returns the
/// surviving FIELD binder names plus the branch body under exactly
/// `num_fields` field binders — the shape the pure-Prod path produces
/// directly. This is a DERIVED encoding, so it sets the speculative marker:
/// a zeta mis-step is a loud kernel rejection followed by a clean type-only
/// fallback, never a silent accept.
#[allow(clippy::too_many_arguments)]
fn zeta_expand_letbound_branch(
    raw_ctor_ty: &Sexp,
    decl_is_let: &[bool],
    branch_names: &[String],
    params: &[Sexp],
    raw_body: &Sexp,
    ctx: &SerapiNormCtx,
    bctx: &[Option<Sexp>],
    num_fields: usize,
) -> Result<(Vec<String>, Sexp), String> {
    SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
    if branch_names.len() != decl_is_let.len() {
        return Err(
            "Case: branch binder count disagrees with the let-laced constructor telescope"
                .to_string(),
        );
    }
    if decl_is_let.iter().filter(|&&l| !l).count() != num_fields {
        return Err(
            "Case: let-laced telescope field count disagrees with the registered constructor"
                .to_string(),
        );
    }
    // Instantiate the leading parameter binders (Prods only — a let among
    // the parameters is out of scope, fail closed).
    let mut chain = raw_ctor_ty.clone();
    for p in params {
        let Sexp::List(cv) = &chain else {
            return Err("Case: constructor/parameter arity mismatch".to_string());
        };
        if cv.len() != 4 || !matches!(&cv[0], Sexp::Atom(h) if h == "Prod") {
            return Err("Case: constructor/parameter arity mismatch".to_string());
        }
        chain = dialect_subst_binder0(&cv[3], p)?;
    }
    // Peel the full declaration telescope: (declared type, let value).
    let mut decls: Vec<(Sexp, Option<Sexp>)> = Vec::with_capacity(decl_is_let.len());
    for &is_let in decl_is_let {
        let Sexp::List(dv) = &chain else {
            return Err(
                "Case: raw constructor telescope shorter than its declarations".to_string(),
            );
        };
        if !is_let && dv.len() == 4 && matches!(&dv[0], Sexp::Atom(h) if h == "Prod") {
            decls.push((dv[2].clone(), None));
            let next = dv[3].clone();
            chain = next;
        } else if is_let && dv.len() == 5 && matches!(&dv[0], Sexp::Atom(h) if h == "LetIn") {
            decls.push((dv[3].clone(), Some(dv[2].clone())));
            let next = dv[4].clone();
            chain = next;
        } else {
            return Err(
                "Case: raw constructor telescope disagrees with its declaration flags".to_string(),
            );
        }
    }
    // Normalize the branch body under the FULL declaration context (branch
    // `Rel`s see fields AND lets).
    let body = {
        let mut inner_bctx = bctx.to_vec();
        for (ty, _) in &decls {
            inner_bctx.push(Some(ty.clone()));
        }
        normalize_serapi_rec(raw_body, ctx, &inner_bctx)
    };
    // Rebuild the telescope over the body as a Lambda/LetIn spine…
    let mut acc = body;
    for (d, (ty, value)) in decls.into_iter().enumerate().rev() {
        acc = match value {
            Some(v) => Sexp::List(vec![
                Sexp::Atom("LetIn".to_string()),
                Sexp::Atom(branch_names[d].clone()),
                v,
                ty,
                acc,
            ]),
            None => Sexp::List(vec![
                Sexp::Atom("Lambda".to_string()),
                Sexp::Atom(branch_names[d].clone()),
                ty,
                acc,
            ]),
        };
    }
    // …then walk it, zeta-reducing each spine LetIn and peeling the field
    // lambdas, leaving the body under exactly the field binders.
    let mut names = Vec::with_capacity(num_fields);
    let mut cur = acc;
    for _ in 0..decl_is_let.len() {
        let Sexp::List(v) = &cur else {
            return Err("Case: zeta-reduced branch spine underflow".to_string());
        };
        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Lambda") {
            names.push(match &v[1] {
                Sexp::Atom(n) => n.clone(),
                _ => "_".to_string(),
            });
            let next = v[3].clone();
            cur = next;
        } else if v.len() == 5 && matches!(&v[0], Sexp::Atom(h) if h == "LetIn") {
            let next = dialect_subst_binder0(&v[4], &v[2])?;
            cur = next;
        } else {
            return Err("Case: zeta-reduced branch spine underflow".to_string());
        }
    }
    Ok((names, cur))
}

/// Remove the fix binder at index `fix_at` from a term: `Rel`s past it
/// decrement; a surviving reference TO it is a hard error (the recursive
/// self-reference escaped the recognized self-call rewrite).
fn dialect_strip_fix_binder(sexp: &Sexp, fix_at: u32) -> Result<Sexp, String> {
    dialect_map_rels(sexp, fix_at, &mut |k, c| {
        if k == c {
            Err("fix self-reference outside a recognized structural self-call".to_string())
        } else if k > c {
            Ok(rel_sexp(k - 1))
        } else {
            Ok(rel_sexp(k))
        }
    })
}

/// Peel the leading Prod spine of a dialect term into `(binder types, rest)`.
fn dialect_peel_prods(sexp: &Sexp) -> (Vec<(String, Sexp)>, Sexp) {
    let mut fields = Vec::new();
    let mut cur = sexp;
    while let Sexp::List(v) = cur {
        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") {
            let name = match &v[1] {
                Sexp::Atom(s) => s.clone(),
                _ => "_".to_string(),
            };
            fields.push((name, v[2].clone()));
            cur = &v[3];
        } else {
            break;
        }
    }
    (fields, cur.clone())
}

/// Everything the recursor application needs, extracted from a raw SerAPI
/// 8.20 compact `Case` node plus the import-session registry.
struct SerapiCasePieces {
    ind_name: String,
    ind_idx: u32,
    /// Normalized parameter arguments (outer context).
    params: Vec<Sexp>,
    /// Motive as a dialect lambda telescope
    /// `(Lambda i1 T1 … (Lambda in Tn (Lambda x (I params… i…) <ret>)))` —
    /// one binder per index plus the scrutinee (plain
    /// `(Lambda x (I params…) <ret>)` for non-indexed matches).
    motive: Sexp,
    /// The return-predicate body alone (under the `1 + indices.len()`
    /// motive binders).
    motive_body: Sexp,
    discriminant: Sexp,
    /// Concrete INDEX terms of an indexed match (outer context), recovered
    /// from the discriminant's type; empty for non-indexed matches. The
    /// recursor spine places them between the minor premises and the major.
    indices: Vec<Sexp>,
    /// Index binder TYPES (arity telescope instantiated with the params;
    /// entry k is under the k earlier index binders). Parallel to `indices`.
    index_binder_tys: Vec<Sexp>,
    /// Dialect branches shaped as recursor MINOR PREMISES:
    /// `λ fields… ihs…. body` — one induction-hypothesis binder per direct
    /// recursive field, inserted after all fields (kernel recursor order),
    /// with the branch body lifted over them.
    branches: Vec<Sexp>,
    /// Per branch: the resolved `(field name, field type)` telescope
    /// (constructor type with the Case parameters substituted; entry `i` is
    /// under the `i` earlier field binders). Parallel to `branches`.
    branch_fields: Vec<Vec<(String, Sexp)>>,
    /// Per branch: the NATURAL normalized branch body — under the field
    /// binders only, no induction-hypothesis lift. Parallel to `branches`.
    /// Used by the general (post-abstracted) `Fix` structuralization, which
    /// assembles its own minor premises.
    branch_bodies: Vec<Sexp>,
    elim: ElimShape,
    /// Motive universe level for `LevelParam` recursors (`None` when it
    /// cannot be derived from the motive's result — fail closed).
    rec_level: Option<u32>,
}

/// Convert a raw SerAPI 8.20 `Case` node
/// `(Case (ci…) (Instance …) (<params>) ((((<binders>)) <ret>) <relevance>)
///  NoInvert <discr> (<branches>))`
/// into recursor-shaped pieces.
///
/// Branch binder TYPES are not present in the compact Case node; they are
/// derived from the matched inductive's registered constructor types with the
/// Case's parameter arguments substituted in — exactly the recursor minor
/// premise domains. INDEXED matches (return predicate binding the indices
/// before the scrutinee) additionally recover the concrete index terms from
/// the discriminant's type via `bctx` (see [`normalize_serapi`]). Anything
/// underivable (unregistered inductive, let-bound constructor fields,
/// universe-polymorphic instance, `CaseInvert`, arity mismatches, an indexed
/// discriminant whose type is unrecoverable, indexed matches over
/// promotion-affected or recursive-field constructors) is a fail-closed
/// error.
fn convert_serapi_case(
    items: &[Sexp],
    ctx: &SerapiNormCtx,
    bctx: &[Option<Sexp>],
) -> Result<SerapiCasePieces, String> {
    let ci = match &items[1] {
        Sexp::List(v) => v,
        _ => return Err("Case: malformed case_info".to_string()),
    };
    let ci_field = |key: &str| -> Option<&Sexp> {
        ci.iter().find_map(|kv| match kv {
            Sexp::List(v) if v.len() >= 2 && matches!(&v[0], Sexp::Atom(k) if k == key) => {
                Some(&v[1])
            }
            _ => None,
        })
    };
    // ci_ind = ((MutInd (KerName ...)) <idx>)
    let (ind_name, ind_idx) = {
        let ci_ind = ci_field("ci_ind").ok_or("Case: missing ci_ind")?;
        let Sexp::List(pair) = ci_ind else {
            return Err("Case: malformed ci_ind".to_string());
        };
        if pair.len() < 2 {
            return Err("Case: malformed ci_ind".to_string());
        }
        let name = serapi_qualified_name(&pair[0]).ok_or("Case: unqualifiable inductive name")?;
        let idx = match &pair[1] {
            Sexp::Atom(s) => s
                .parse::<u32>()
                .map_err(|_| "Case: bad inductive block index".to_string())?,
            _ => return Err("Case: bad inductive block index".to_string()),
        };
        // Same canonical-first Dual arbitration as `(Ind …)` references, so
        // the reconstructed match (and its derived recursor spine) names the
        // SAME family the discriminant's rendered type is headed by.
        let name = resolve_ind_family_name(name, &pair[0], idx, ctx);
        (name, idx)
    };
    let mut npar = match ci_field("ci_npar") {
        Some(Sexp::Atom(s)) => s
            .parse::<u32>()
            .map_err(|_| "Case: bad ci_npar".to_string())?,
        _ => return Err("Case: missing ci_npar".to_string()),
    };
    // Let-bound constructor fields (ndecls != nargs) are in scope only when
    // registration recorded the raw LetIn-laced telescopes (checked against
    // the registry below, once `info` is resolved).
    let cstr_has_let_decls = ci_field("ci_cstr_ndecls") != ci_field("ci_cstr_nargs");
    // items[2] is the bare `(Instance …)` node — wrap it for the checker.
    if let Some(reason) =
        serapi_ref_instance_reject_reason(&Sexp::List(vec![items[2].clone()]), "Case")
    {
        return Err(reason);
    }
    let mut params: Vec<Sexp> = match &items[3] {
        Sexp::List(ps) => ps
            .iter()
            .map(|p| normalize_serapi_rec(p, ctx, bctx))
            .collect(),
        _ => return Err("Case: malformed parameter list".to_string()),
    };
    if params.len() != npar as usize {
        return Err("Case: parameter count does not match ci_npar".to_string());
    }
    let info = ctx
        .lookup(&ind_name, ind_idx)
        .ok_or_else(|| format!("Case: inductive `{ind_name}.{ind_idx}` not in import session"))?;
    // A synonym-unfolded family's Case reconstruction is a DERIVED shape (the
    // index hidden behind the synonym, constructors whose results head an
    // `In`/`Ensemble` abbreviation): mark it speculative so a kernel rejection
    // reverts to a clean type-only axiom instead of a masked-failure taint.
    if info.arity_synonym_unfolded {
        SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
    }
    // NON-UNIFORM PARAMETER DEMOTION (`Acc`, `clos_trans`, `Rstar`, `EqSt`, …).
    // Coq's `ci_npar` counts EVERY declared parameter, including the non-uniform
    // ones; but `compute_uniform_num_params` demoted those trailing non-uniform
    // params to INDICES so the family replays through Clean's strict
    // `add_inductive` (which requires uniform parameters). So a match on such a
    // family carries `ci_npar > info.num_params`, and its return predicate binds
    // ONLY the genuine Coq indices + scrutinee (Coq treats the demoted params as
    // fixed, so it omits them from the motive). Reinterpret the trailing
    // `demoted_leading_indices` params as the OUTERMOST (fixed) index arguments:
    // the kernel recursor's motive binds them, the discriminant's type supplies
    // their concrete values, and the motive body — which never mentions them —
    // is lifted over the synthesized binders below. This is GENERAL to the
    // params-vs-indices split (never a name list); the kernel re-checks the
    // reconstructed spine, so any misfit is a loud rejection (clean type-only
    // fallback), never a silent accept.
    let demoted_leading_indices: usize = if npar > info.num_params {
        let d = (npar - info.num_params) as usize;
        // The demoted params are a SUFFIX (compute_uniform_num_params only ever
        // shrinks from the tail); drop them from the kernel parameter list —
        // their values are recovered from the discriminant's type below.
        params.truncate(info.num_params as usize);
        npar = info.num_params;
        d
    } else if npar < info.num_params {
        // Registry holds MORE params than the Case declares: a genuine
        // disagreement (never produced by demotion, which only shrinks). Fail
        // closed exactly as before.
        return Err("Case: ci_npar disagrees with the registered inductive".to_string());
    } else {
        0
    };
    if cstr_has_let_decls && info.ctor_raw_lets.iter().all(|o| o.is_none()) {
        // ndecls != nargs but registration saw no LetIn telescope: the
        // pre-existing fail-closed reject.
        return Err("Case: let-bound constructor fields unsupported".to_string());
    }
    // Return predicate: (((<binder-annots>) <type>) <relevance>). The binder
    // array lists the INDEX binders first (outermost) and the scrutinee last
    // — verified live against sertop 8.20 (`eq_sym`'s predicate binds
    // `[a; h]` with body `eq A a x`, i.e. `a` is the outer binder).
    let (mut binder_names, raw_motive_body) = {
        let Sexp::List(rp) = &items[4] else {
            return Err("Case: malformed return predicate".to_string());
        };
        let Some(Sexp::List(pred)) = rp.first() else {
            return Err("Case: malformed return predicate".to_string());
        };
        if pred.len() != 2 {
            return Err("Case: malformed return predicate".to_string());
        }
        let Sexp::List(binders) = &pred[0] else {
            return Err("Case: malformed return-predicate binders".to_string());
        };
        if binders.is_empty() {
            return Err("Case: return predicate binds no scrutinee".to_string());
        }
        let names: Vec<String> = binders
            .iter()
            .map(|b| serapi_binder_name(b).ok_or("Case: unrecognized return-predicate binder"))
            .collect::<Result<_, _>>()?;
        (names, &pred[1])
    };
    // The Coq return predicate binds only its genuine indices + scrutinee; the
    // demoted (non-uniform-param) indices are outermost and omitted by Coq.
    // `nrealargs_coq` counts the frame the RAW motive body lives in.
    let nrealargs_coq = binder_names.len() - 1;
    if demoted_leading_indices > 0 {
        // Prepend one synthetic binder per demoted leading index (outermost).
        let mut names: Vec<String> = (0..demoted_leading_indices)
            .map(|j| format!("idx{j}"))
            .collect();
        names.append(&mut binder_names);
        binder_names = names;
        // A derived (motive-lifted) reconstruction: mark speculative so a kernel
        // rejection reverts to a clean type-only axiom instead of taint.
        SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
    }
    let nrealargs = binder_names.len() - 1;
    if !matches!(&items[5], Sexp::Atom(s) if s == "NoInvert") {
        return Err("Case: CaseInvert (SProp/UIP match inversion) unsupported".to_string());
    }
    let discriminant = normalize_serapi_rec(&items[6], ctx, bctx);

    // Indexed-match guards: the registered arity must agree on the index
    // count, and the kernel's fixed-index promotion must provably NOT fire
    // (it would move the params/indices boundary of the replayed recursor).
    if nrealargs > 0 {
        if info.num_indices() != Some(nrealargs as u32) {
            return Err(
                "indexed-match: return-predicate binder count disagrees with the registered arity"
                    .to_string(),
            );
        }
        match predicted_fixed_index_promotion(info, &ind_name, ind_idx) {
            Some(0) => {}
            _ => {
                return Err(
                    "indexed-match: fixed-index promotion would change the recursor \
                     parameter boundary"
                        .to_string(),
                )
            }
        }
    }

    // Recover the concrete index terms from the discriminant's TYPE:
    // - `(Cast t _ ty)` discriminant: the annotation type, already in the
    //   Case context;
    // - `Rel r` discriminant: the binding-site binder type from `bctx`,
    //   lifted by `r + 1` (the de Bruijn distance from the binding site to
    //   the Case site);
    // - anything else: fail closed.
    let indices: Vec<Sexp> = if nrealargs == 0 {
        Vec::new()
    } else {
        let disc_ty = if let Sexp::List(cv) = &items[6] {
            if cv.len() == 4 && matches!(&cv[0], Sexp::Atom(h) if h == "Cast") {
                Some(normalize_serapi_rec(&cv[3], ctx, bctx))
            } else {
                None
            }
        } else {
            None
        };
        let disc_ty = match disc_ty {
            Some(ty) => ty,
            None => {
                // A bare `Rel` discriminant: its binding-site binder type, lifted.
                // A COMPOUND application discriminant (`sqrt_iter k p q r`, or a
                // locally-bound spec term `p … : eq_xor_neq …`): synthesize its
                // type from the head's declared/binder type instantiated at the
                // arguments (see `synthesize_app_disc_type`).
                if let Some(r) = dialect_rel_of(&discriminant) {
                    let site_ty = bctx_lookup(bctx, r).ok_or_else(|| {
                        debug_disc_fail("rel-no-bctx", &discriminant);
                        "indexed-match: discriminant type unrecoverable".to_string()
                    })?;
                    dialect_lift(site_ty, r + 1, 0)?
                } else {
                    synthesize_app_disc_type(&discriminant, ctx, bctx).ok_or_else(|| {
                        debug_disc_fail("synth-none", &discriminant);
                        "indexed-match: discriminant type unrecoverable".to_string()
                    })?
                }
            }
        };
        // The discriminant type may be a definitional abbreviation of the
        // matched inductive — `n < m := lt n m := le (S n) m`. Delta-unfold a
        // registered relation-definition head (β-reducing the def body with the
        // discriminant type's args) to reveal the inductive and its index terms.
        let disc_ty = unfold_relation_def_head(&disc_ty, ctx).unwrap_or(disc_ty);
        let (head, args) = dialect_app_parts(&disc_ty);
        match dialect_ind_head(head) {
            Some((n, i)) if n == ind_name && i == ind_idx => {}
            _ => {
                return Err(
                    "indexed-match: discriminant type does not head the matched inductive"
                        .to_string(),
                )
            }
        }
        if args.len() != npar as usize + nrealargs {
            return Err(
                "indexed-match: discriminant type arity disagrees with params + indices"
                    .to_string(),
            );
        }
        args[npar as usize..].to_vec()
    };

    // Index binder TYPES from the arity telescope instantiated with the
    // Case's parameters (entry k valid under the k earlier index binders).
    let index_binder_tys: Vec<Sexp> = {
        let mut chain = info.arity.clone();
        for p in &params {
            let Sexp::List(av) = &chain else {
                return Err("indexed-match: registered arity/parameter mismatch".to_string());
            };
            if av.len() != 4 || !matches!(&av[0], Sexp::Atom(h) if h == "Prod") {
                return Err("indexed-match: registered arity/parameter mismatch".to_string());
            }
            chain = dialect_subst_binder0(&av[3], p)?;
        }
        let (idx_binders, _) = dialect_peel_prods(&chain);
        if idx_binders.len() != nrealargs {
            return Err(
                "indexed-match: registered arity index telescope disagrees with the match"
                    .to_string(),
            );
        }
        idx_binders.into_iter().map(|(_, ty)| ty).collect()
    };

    // Scrutinee binder type: the inductive applied to the parameters (lifted
    // over the index binders) and the index binder variables.
    let self_ty = {
        let ind_ref = Sexp::List(vec![
            Sexp::Atom("Ind".to_string()),
            Sexp::Atom(ind_name.clone()),
            Sexp::Atom(ind_idx.to_string()),
        ]);
        if params.is_empty() && nrealargs == 0 {
            ind_ref
        } else {
            let mut app = vec![Sexp::Atom("App".to_string()), ind_ref];
            for p in &params {
                app.push(dialect_lift(p, nrealargs as u32, 0)?);
            }
            for k in (0..nrealargs).rev() {
                app.push(rel_sexp(k as u32));
            }
            Sexp::List(app)
        }
    };

    // Normalize the return-predicate body under its real binder context
    // (indices then scrutinee), then re-wrap ALL binders as typed lambdas —
    // exactly the recursor's motive telescope `Π indices…, I params… → Sort`.
    // The RAW motive body lives in the Coq predicate frame: only the
    // `nrealargs_coq` GENUINE Coq indices (the INNERMOST index binders,
    // `index_binder_tys[demoted_leading_indices..]`) plus the scrutinee are
    // present — the demoted leading indices are absent (Coq omits them). So
    // normalize under that Coq-sized frame, then lift the body over the
    // `demoted_leading_indices` synthesized binders inserted ABOVE it (its
    // ambient references shift up; the omitted binders are never mentioned).
    let motive_body = {
        let mut inner_bctx = bctx.to_vec();
        for ty in &index_binder_tys[demoted_leading_indices..] {
            inner_bctx.push(Some(ty.clone()));
        }
        inner_bctx.push(Some(self_ty.clone()));
        let body = normalize_serapi_rec(raw_motive_body, ctx, &inner_bctx);
        if demoted_leading_indices > 0 {
            dialect_lift(
                &body,
                demoted_leading_indices as u32,
                (nrealargs_coq + 1) as u32,
            )?
        } else {
            body
        }
    };
    let motive = {
        let mut acc = Sexp::List(vec![
            Sexp::Atom("Lambda".to_string()),
            Sexp::Atom(binder_names[nrealargs].clone()),
            self_ty.clone(),
            motive_body.clone(),
        ]);
        for (name, ty) in binder_names[..nrealargs]
            .iter()
            .zip(index_binder_tys.iter())
            .rev()
        {
            acc = Sexp::List(vec![
                Sexp::Atom("Lambda".to_string()),
                Sexp::Atom(name.clone()),
                ty.clone(),
                acc,
            ]);
        }
        acc
    };
    // Branches.
    let raw_branches = match &items[7] {
        Sexp::List(bs) => bs,
        _ => return Err("Case: malformed branch list".to_string()),
    };
    if raw_branches.len() != info.ctor_types.len() {
        return Err("Case: branch count does not match constructor count".to_string());
    }
    let mut branches = Vec::with_capacity(raw_branches.len());
    let mut branch_fields = Vec::with_capacity(raw_branches.len());
    let mut branch_bodies = Vec::with_capacity(raw_branches.len());
    for (j, rb) in raw_branches.iter().enumerate() {
        let Sexp::List(bv) = rb else {
            return Err("Case: malformed branch".to_string());
        };
        if bv.len() != 2 {
            return Err("Case: malformed branch".to_string());
        }
        let Sexp::List(binders) = &bv[0] else {
            return Err("Case: malformed branch binders".to_string());
        };
        let all_names: Vec<String> = binders
            .iter()
            .enumerate()
            .map(|(i, b)| serapi_binder_name(b).unwrap_or_else(|| format!("f{i}")))
            .collect();
        // Instantiate the constructor type's leading parameter binders with
        // the Case's parameter arguments, leaving the field spine.
        let mut chain = info.ctor_types[j].clone();
        for p in &params {
            let Sexp::List(cv) = &chain else {
                return Err("Case: constructor/parameter arity mismatch".to_string());
            };
            if cv.len() != 4 || !matches!(&cv[0], Sexp::Atom(h) if h == "Prod") {
                return Err("Case: constructor/parameter arity mismatch".to_string());
            }
            chain = dialect_subst_binder0(&cv[3], p)?;
        }
        let (fields, _result) = dialect_peel_prods(&chain);
        let m = fields.len();
        let flags = &info.ctor_recursive[j];
        if flags.len() != m {
            return Err(
                "Case: registered field count disagrees with constructor spine".to_string(),
            );
        }
        let rec_fields: Vec<usize> = flags
            .iter()
            .enumerate()
            .filter_map(|(i, &r)| r.then_some(i))
            .collect();
        let q = rec_fields.len();
        let (names, body) = if let Some((raw_ty, decl_is_let)) =
            info.ctor_raw_lets.get(j).and_then(|o| o.as_ref())
        {
            // LET-BOUND constructor fields: the branch binds the full
            // declaration telescope; zeta-expand it down to the field
            // binders the registered (zeta-reduced) recursor expects.
            zeta_expand_letbound_branch(
                raw_ty,
                decl_is_let,
                &all_names,
                &params,
                &bv[1],
                ctx,
                bctx,
                m,
            )?
        } else {
            // With a demoted family the KERNEL constructor binds the demoted
            // leading-index values as its OUTERMOST fields, but Coq's branch
            // omits them (they were parameters in Coq). So the Coq branch binds
            // exactly `m - demoted_leading_indices` field binders.
            if m != all_names.len() + demoted_leading_indices {
                return Err(
                    "Case: branch binder count disagrees with constructor fields".to_string(),
                );
            }
            let genuine = all_names.len();
            let body = {
                // Branch bodies live under the constructor's GENUINE (Coq-bound)
                // field binders — the innermost `genuine` of the `m` fields.
                let mut inner_bctx = bctx.to_vec();
                for (_, fty) in &fields[demoted_leading_indices..] {
                    inner_bctx.push(Some(fty.clone()));
                }
                normalize_serapi_rec(&bv[1], ctx, &inner_bctx)
            };
            // Lift the body's ambient references over the demoted leading-index
            // field binders inserted ABOVE the genuine fields. The body never
            // mentions them (the motive ignores the index binder, so a branch
            // whose result type is `motive idx… (C idx… flds)` need not use the
            // demoted `idx…`); the kernel re-checks the result.
            let body = if demoted_leading_indices > 0 {
                dialect_lift(&body, demoted_leading_indices as u32, genuine as u32)?
            } else {
                body
            };
            let mut names = Vec::with_capacity(m);
            names.extend((0..demoted_leading_indices).map(|j| format!("cidx{j}")));
            names.extend(all_names);
            (names, body)
        };
        // Record the RAW branch parts (resolved field telescope + natural
        // body) for the general Fix structuralization before assembling the
        // plain-Case minor premise.
        branch_fields.push(
            fields
                .iter()
                .enumerate()
                .map(|(i, (fname, fty))| {
                    let name = if names[i] == "_" || names[i].is_empty() {
                        fname.clone()
                    } else {
                        names[i].clone()
                    };
                    (name, fty.clone())
                })
                .collect::<Vec<_>>(),
        );
        branch_bodies.push(body.clone());
        // Lift the body over the q inserted IH binders (innermost).
        let mut acc = dialect_lift(&body, q as u32, 0)?;
        // IH binders, innermost-last, in recursive-field order. The IH for
        // recursive field `i` (at IH position `jp`) has the type the kernel
        // recursor's minor premise expects for that field.
        for (jp, &i) in rec_fields.iter().enumerate().rev() {
            let field_ref = rel_sexp((m - 1 - i + jp) as u32);
            let ih_ty = if nrealargs == 0 {
                // Non-indexed: `motive field_i` — the motive body (one binder,
                // the scrutinee) lifted over the m fields and jp earlier IHs and
                // instantiated at the field reference. The proven path.
                let lifted_motive = dialect_lift(&motive_body, (m + jp) as u32, 1)?;
                dialect_subst_binder0(&lifted_motive, &field_ref)?
            } else {
                // Indexed family: the recursor minor premise binds an IH of type
                // `motive fidx… field_i`, where `fidx…` are the recursive field's
                // OWN index terms — read from its type `I params… fidx…`. Emit the
                // motive (the full Π/λ telescope) applied to those indices and the
                // field; the kernel β-reduces it to the exact expected IH type.
                // The field's index terms and the motive are lifted into the IH
                // binder context. This is a DERIVED recursor-branch shape, so mark
                // the conversion speculative: a kernel rejection (a field shape
                // this formula does not capture — nested/functorial recursion,
                // primitive projections) fails closed to a clean type-only axiom.
                let direct = matches!(
                    dialect_ind_head(&fields[i].1),
                    Some((n, ix)) if n == ind_name && ix == ind_idx
                );
                let (_, fargs) = dialect_app_parts(&fields[i].1);
                if !direct || fargs.len() != npar as usize + nrealargs {
                    return Err("indexed-match: recursive field is not a direct saturated \
                                occurrence of the matched inductive"
                        .to_string());
                }
                SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
                let lifted_motive = dialect_lift(&motive, (m + jp) as u32, 0)?;
                let mut app = vec![Sexp::Atom("App".to_string()), lifted_motive];
                for ix in &fargs[npar as usize..] {
                    app.push(dialect_lift(ix, (m - i + jp) as u32, 0)?);
                }
                app.push(field_ref);
                Sexp::List(app)
            };
            acc = Sexp::List(vec![
                Sexp::Atom("Lambda".to_string()),
                Sexp::Atom(format!("ih{jp}")),
                ih_ty,
                acc,
            ]);
        }
        // Field binders, innermost-last.
        for (i, (fname, fty)) in fields.into_iter().enumerate().rev() {
            let name = if names[i] == "_" || names[i].is_empty() {
                fname
            } else {
                names[i].clone()
            };
            acc = Sexp::List(vec![
                Sexp::Atom("Lambda".to_string()),
                Sexp::Atom(name),
                fty,
                acc,
            ]);
        }
        branches.push(acc);
    }
    let elim = info
        .elim_shape(ctx)
        .ok_or("Case: elimination shape undecidable (fielded Prop singleton)")?;
    let rec_level = {
        // The motive body lives under the index binders plus the scrutinee.
        let mut mb_bctx = bctx.to_vec();
        for ty in &index_binder_tys {
            mb_bctx.push(Some(ty.clone()));
        }
        mb_bctx.push(Some(self_ty));
        motive_result_level(&motive_body, ctx, &mb_bctx)
    };
    Ok(SerapiCasePieces {
        ind_name,
        ind_idx,
        params,
        motive,
        motive_body,
        discriminant,
        indices,
        index_binder_tys,
        branches,
        branch_fields,
        branch_bodies,
        elim,
        rec_level,
    })
}

thread_local! {
    /// Set by [`motive_result_level`]'s Const-headed arm whenever it derives a
    /// recursor motive universe from a defined constant's registered result
    /// sort — a best-effort GUESS. The import loop resets it before, and reads
    /// it after, each value conversion, marking the resulting constant
    /// [`AxiomProfile::SPECULATIVE_MOTIVE`] so verify can fail closed: a
    /// speculative value the kernel rejects reverts to a clean type-only axiom
    /// (no masked-failure taint) instead of a tainting fallback.
    static SPECULATIVE_MOTIVE_USED: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };

    /// The inductive family currently being parsed/registered/imported
    /// ([`parse_serapi_inductive`]), for the SELF-REFERENCE carve-out of the
    /// canonical-first INDUCTIVE Dual resolution
    /// ([`resolve_ind_family_name`]): a family's own constructor return types
    /// reference the family through the same `(user, canonical)` KerPair as
    /// everything else, but flipping THOSE to the canonical spelling would
    /// point an `Include`-copied family's constructors at the ORIGINAL
    /// family and reject its whole (baseline-KernelVerified) replay. Set
    /// around the family's own arity/constructor normalization only.
    static CURRENT_INDUCTIVE_FAMILY: std::cell::RefCell<Option<String>> =
        const { std::cell::RefCell::new(None) };
}

/// Resolve an INDUCTIVE-reference KerPair (`Ind` / `Construct` / `Case
/// ci_ind` / `Proj proj_ind`) CANONICAL-FIRST: when the reference carries a
/// canonical (definition-site) spelling DIFFERENT from the user spelling and
/// that canonical family block is registered in the session, resolve to the
/// canonical spelling — Coq's own record that both spellings are ONE kernel
/// inductive.
///
/// MEASURED MOTIVATION (2026-07-16 census): `Include`-duplicated families
/// (`Coq.PArith.BinPos.Pos.mask` ← `BinPosDef.Pos.mask`) import as TWO
/// distinct kernel families, and Coq's compiled proof terms interleave BOTH
/// spellings inside ONE declaration (`Pos.sub_mask_succ_r`: 60 user-`BinPos`
/// + 22 user-`BinPosDef` `mask` references). Conversion cannot cross the two
/// copies — they ground in different constructors/recursors — so the mixed
/// declarations reject on same-head `eq`-vs-`eq` mismatches
/// (`sub_mask_succ_r` alone masked an 83-dependent stdlib taint cone, plus
/// the `Z.ggcd_gcd` / `N.ggcd_gcd` / `Z.shiftl_spec_high` seeds). Flipping
/// every inductive reference to the canonical family makes the rendering
/// ground in ONE family; the duplicate copy family still imports under its
/// own name (self-references carved out via [`CURRENT_INDUCTIVE_FAMILY`]),
/// so its baseline-KernelVerified rows are untouched.
///
/// FAIL-CLOSED: the flip only fires when the canonical block is REGISTERED
/// (the measured `-41` regression class — canonical spellings absent from
/// the dumps — keeps the user-spelling resolution), and a flipped rendering
/// is marked SPECULATIVE, so a kernel rejection falls to a clean type-only
/// axiom, never a masked-failure taint. CONSTANT references are deliberately
/// NOT flipped: value-bearing constant copies δ-unfold across spellings once
/// the inductive ground is shared, and the constant-side user-first rule is
/// the measured-safe disposition (`resolve_kerpair_name`).
fn resolve_ind_family_name(user: String, sexp: &Sexp, block: u32, ctx: &SerapiNormCtx) -> String {
    let is_self = CURRENT_INDUCTIVE_FAMILY.with(|f| f.borrow().as_deref() == Some(user.as_str()));
    if !is_self {
        if let Some(canon) = serapi_qualified_name_canonical(sexp) {
            if canon != user && ctx.lookup(&canon, block).is_some() {
                SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
                return canon;
            }
        }
    }
    resolve_kerpair_name(user, sexp, ctx)
}

/// Derive the motive's universe level (the recursor's instance) from the
/// return-predicate body: the level ℓ with `motive : … → Sort ℓ`. `bctx` is
/// the binder-type context the body lives in (enclosing binders plus the
/// motive's own index/scrutinee binders), used to decide `Rel`-headed
/// result types (`match H with … end : A` where `A : Prop` is a bound
/// proposition — the `proj1` shape).
fn motive_result_level(mbody: &Sexp, ctx: &SerapiNormCtx, bctx: &[Option<Sexp>]) -> Option<u32> {
    if let Some(level) = motive_result_level_exact(mbody, ctx, bctx) {
        return Some(level);
    }
    // Speculative Prop default — applied ONLY at the TOP-LEVEL motive body (not
    // in the recursive sub-derivations, which must propagate `None` so a Π-chain
    // fails closed on an underivable component). This remnant class is dominated
    // by PROOF constants (`_ind` schemes, `_spec`/`_ind_rel` lemmas) whose motive
    // is Prop-valued, for which the recursor instance is level 0. Emitting the
    // level-0 recursor is a GUESS the kernel filters: a genuinely Set/Type-valued
    // motive is rejected and reverts to a clean type-only axiom
    // (`SPECULATIVE_MOTIVE` fail-closed), never dropping an existing KV.
    SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
    Some(0)
}

/// Exact motive universe derivation: the level ℓ with `motive : … → Sort ℓ`,
/// or `None` when it is not syntactically derivable. Callers that want the
/// fail-closed speculative Prop default use [`motive_result_level`]; the
/// recursive sub-derivations here call THIS (exact) form so an underivable
/// Π-component fails the whole chain rather than defaulting mid-way.
fn motive_result_level_exact(
    mbody: &Sexp,
    ctx: &SerapiNormCtx,
    bctx: &[Option<Sexp>],
) -> Option<u32> {
    if let Some(sort) = dialect_sort_of(mbody) {
        // The motive RETURNS a sort: it lives one level above it.
        return Some(match sort {
            CicSort::Prop => 1,
            CicSort::Set => 2,
            CicSort::Type(l) => l.as_concrete_type()? + 1,
        });
    }
    // A Π-chain result: a Prop-sorted codomain makes the whole chain Prop
    // (impredicativity: imax _ 0 = 0) — the partially-applied-match shape.
    // Otherwise the chain's sort is `imax(dom, cod) = max(dom, cod)` (cod > 0
    // here), so recurse into BOTH sides and fail closed when either level is
    // underivable. This is the `nat -> nat`-typed-match shape (e.g. `pred`,
    // `sub` bodies returning a function).
    if let Sexp::List(v) = mbody {
        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") {
            let inner = bctx_push(bctx, Some(v[2].clone()));
            return match motive_result_level_exact(&v[3], ctx, &inner)? {
                0 => Some(0),
                cod => {
                    let dom = motive_result_level_exact(&v[2], ctx, bctx)?;
                    Some(cod.max(dom))
                }
            };
        }
    }
    let (head, args) = dialect_app_parts(mbody);
    // `Rel`-headed result: the binder's type decides. Saturation is required
    // (a partial application would not be a type).
    if let Some(r) = dialect_rel_of(head) {
        let entry = bctx_lookup(bctx, r)?;
        if args.len() as u32 != dialect_count_prods(entry) {
            return None;
        }
        return match dialect_sort_of(dialect_prod_codomain(entry))? {
            CicSort::Prop => Some(0),
            CicSort::Set => Some(1),
            CicSort::Type(l) => l.as_concrete_type(),
        };
    }
    // Registered-inductive-headed result (bare or applied): the registered
    // arity's codomain sort decides, provided the head is SATURATED (its
    // argument count matches the arity telescope — a partial application
    // would be Prod-sorted, not the codomain sort).
    if let Some((name, idx)) = dialect_ind_head(mbody) {
        if let Some(info) = ctx.lookup(name, idx) {
            if args.len() as u32 != dialect_count_prods(&info.arity) {
                return None;
            }
            return match info.arity_sort.as_ref()? {
                CicSort::Prop => Some(0),
                CicSort::Set => Some(1),
                CicSort::Type(l) => l.as_concrete_type(),
            };
        }
    }
    // Const-headed result (bare or applied): a defined type former or relation
    // (`R : Set`, `Rle : R → R → Prop`, `iff : Prop → Prop → Prop`). The
    // constant's registered type-codomain sort decides, provided the head is
    // SATURATED. Mirrors the inductive-headed case; a const whose codomain is
    // not a sort (a value-level constant) is not registered, so this fails
    // closed — the recursor motive universe stays underivable, as before.
    if let Some(cname) = dialect_const_head(mbody) {
        let Some((prods, sort)) = ctx.lookup_const_sort(cname) else {
            if std::env::var("COQ_MOTIVE_DEBUG").is_ok() {
                eprintln!("CONST_UNREG {cname} nargs={}", args.len());
            }
            return None;
        };
        if args.len() as u32 != *prods {
            if std::env::var("COQ_MOTIVE_DEBUG").is_ok() {
                eprintln!("CONST_ARITY {cname} nargs={} prods={}", args.len(), prods);
            }
            return None;
        }
        let level = match sort {
            CicSort::Prop => Some(0),
            CicSort::Set => Some(1),
            CicSort::Type(l) => l.as_concrete_type(),
        };
        if level.is_none() && std::env::var("COQ_MOTIVE_DEBUG").is_ok() {
            eprintln!("CONST_NONCONCRETE {cname} sort={sort:?}");
        }
        // A successful Const-headed derivation is a GUESS: flag the current
        // conversion speculative so a kernel rejection fails closed (see
        // `SPECULATIVE_MOTIVE_USED`). Only on Some — a None derivation changed
        // nothing (the recursor motive stays underivable, as before).
        if level.is_some() {
            SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
        }
        return level;
    }
    // β-redex-headed motive body: a higher-order return predicate not in whnf,
    // `(App (Lambda ..) a ..)` — reduce the head Lambda against its arguments
    // (one `dialect_subst_binder0` per arg, application order, exactly as
    // `unfold_relation_def_head`) and recurse. Exact reduction, but flagged
    // speculative since a re-headed motive is still a derived shape.
    if !args.is_empty() {
        if let Sexp::List(hv) = head {
            if hv.len() == 4 && matches!(&hv[0], Sexp::Atom(h) if h == "Lambda") {
                let mut body = head.clone();
                let mut reduced = true;
                for a in args {
                    let Sexp::List(lv) = &body else {
                        reduced = false;
                        break;
                    };
                    if lv.len() != 4 || !matches!(&lv[0], Sexp::Atom(h) if h == "Lambda") {
                        reduced = false;
                        break;
                    }
                    match dialect_subst_binder0(&lv[3], a) {
                        Ok(b) => body = b,
                        Err(_) => {
                            reduced = false;
                            break;
                        }
                    }
                }
                if reduced {
                    SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
                    return motive_result_level_exact(&body, ctx, bctx);
                }
            }
        }
    }
    // ζ-redex motive body: `let x := v in T` — substitute the bound value
    // (`(LetIn name value type body)`; value = v[2], body = v[4]) and recurse.
    if let Sexp::List(v) = mbody {
        if v.len() == 5 && matches!(&v[0], Sexp::Atom(h) if h == "LetIn") {
            if let Ok(sub) = dialect_subst_binder0(&v[4], &v[2]) {
                SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
                return motive_result_level_exact(&sub, ctx, bctx);
            }
        }
    }
    None
}

/// Assemble the dialect encoding of converted Case pieces: a dialect
/// `(Case ...)` node for Prop-only recursors (no universe instance — the
/// existing lowering), or — for level-parameterized recursors, whose
/// `@<ind>.<idx>.rec.{ℓ}` reference needs a universe instance the plain
/// `Case` lowering cannot carry — a degenerate one-binder `(StructFix ...)`
/// applied to the discriminant: `(App (StructFix …) <discr>)` lowers to
/// `(λ s. @<ind>.rec.{ℓ} params motive branches s) <discr>`, a beta-redex
/// the kernel reduces to exactly the recursor application (the components
/// are lifted over the wrapper binder).
///
/// INDEXED matches use the same two encodings with APPLICATION FOLDING: the
/// kernel recursor spine is `params → motive → minors → indices → major`,
/// and both lowerings emit `… <one-term>` as the argument right after the
/// minors — so the first index takes that slot and the remaining indices
/// plus the true discriminant are applied OUTSIDE:
/// `(App (Case … (Discriminant i1) …) i2 … in d)` lowers to
/// `@rec params motive minors i1 i2 … in d`, and
/// `(App (StructFix …) i1 i2 … in d)` beta-reduces to
/// `@rec.{ℓ} params motive minors i1 i2 … in d` (the wrapper binder is the
/// FIRST INDEX, so its binder type is the first index's type, not the
/// inductive). No new dialect node is needed and the kernel re-checks the
/// exact spine either way.
fn assemble_case_sexp(pieces: &SerapiCasePieces) -> Sexp {
    match pieces.elim {
        ElimShape::PropOnly => {
            let mut out = vec![
                Sexp::Atom("Case".to_string()),
                Sexp::List(vec![
                    Sexp::Atom("Ind".to_string()),
                    Sexp::Atom(pieces.ind_name.clone()),
                    Sexp::Atom(pieces.ind_idx.to_string()),
                ]),
            ];
            let mut params = vec![Sexp::Atom("Params".to_string())];
            params.extend(pieces.params.iter().cloned());
            out.push(Sexp::List(params));
            out.push(Sexp::List(vec![
                Sexp::Atom("Motive".to_string()),
                pieces.motive.clone(),
            ]));
            // Application folding (see above): the slot right after the
            // minors is the first index when the match is indexed, the
            // discriminant otherwise.
            let first_arg = pieces
                .indices
                .first()
                .unwrap_or(&pieces.discriminant)
                .clone();
            out.push(Sexp::List(vec![
                Sexp::Atom("Discriminant".to_string()),
                first_arg,
            ]));
            for b in &pieces.branches {
                out.push(Sexp::List(vec![
                    Sexp::Atom("Branch".to_string()),
                    b.clone(),
                ]));
            }
            let case_node = Sexp::List(out);
            if pieces.indices.is_empty() {
                case_node
            } else {
                let mut app = vec![Sexp::Atom("App".to_string()), case_node];
                app.extend(pieces.indices[1..].iter().cloned());
                app.push(pieces.discriminant.clone());
                Sexp::List(app)
            }
        }
        ElimShape::LevelParam => match assemble_level_param_case(pieces) {
            Ok(s) => s,
            Err(reason) => coq_unsupported(&reason),
        },
    }
}

/// Level-parameterized arm of [`assemble_case_sexp`]: build the
/// `(App (StructFix …) …)` wrapper carrying the recursor's universe
/// instance. The wrapper binder is the argument right after the minors in
/// the recursor spine — the discriminant for a non-indexed match, the FIRST
/// INDEX for an indexed one (application folding; the remaining indices and
/// the discriminant are applied outside).
fn assemble_level_param_case(pieces: &SerapiCasePieces) -> Result<Sexp, String> {
    let level = pieces.rec_level.ok_or_else(|| {
        if std::env::var("COQ_MOTIVE_DEBUG").is_ok() {
            let (h, a) = dialect_app_parts(&pieces.motive_body);
            eprintln!(
                "MOTIVE_NONE ind={} head={:?} nargs={} body={:.360?}",
                pieces.ind_name,
                h,
                a.len(),
                pieces.motive_body
            );
        }
        "Case: recursor motive universe level underivable from the return predicate".to_string()
    })?;
    let tag = |t: &str| Sexp::Atom(t.to_string());
    // Struct (wrapper) binder type — outer context, the StructFix lowering
    // places it OUTSIDE the wrapper binder: the inductive applied to its
    // parameters (non-indexed), or the first index's type (indexed).
    let ind_ref = Sexp::List(vec![
        tag("Ind"),
        Sexp::Atom(pieces.ind_name.clone()),
        Sexp::Atom(pieces.ind_idx.to_string()),
    ]);
    let struct_ty = if let Some(first_index_ty) = pieces.index_binder_tys.first() {
        first_index_ty.clone()
    } else if pieces.params.is_empty() {
        ind_ref.clone()
    } else {
        let mut app = vec![tag("App"), ind_ref.clone()];
        app.extend(pieces.params.iter().cloned());
        Sexp::List(app)
    };
    // Params/motive/branches sit INSIDE the wrapper binder in the StructFix
    // lowering: lift them over it.
    let mut sf = vec![
        tag("StructFix"),
        ind_ref,
        Sexp::List(vec![tag("RecLevel"), Sexp::Atom(level.to_string())]),
    ];
    let mut params_part = vec![tag("Params")];
    for p in &pieces.params {
        params_part.push(dialect_lift(p, 1, 0)?);
    }
    sf.push(Sexp::List(params_part));
    sf.push(Sexp::List(vec![tag("StructTy"), struct_ty]));
    sf.push(Sexp::List(vec![
        tag("Motive"),
        dialect_lift(&pieces.motive, 1, 0)?,
    ]));
    for b in &pieces.branches {
        sf.push(Sexp::List(vec![tag("Branch"), dialect_lift(b, 1, 0)?]));
    }
    let mut app = vec![tag("App"), Sexp::List(sf)];
    app.extend(pieces.indices.iter().cloned());
    app.push(pieces.discriminant.clone());
    Ok(Sexp::List(app))
}

// ---------------------------------------------------------------------------
// Mutual fixpoints (2-body, one inductive, equal signature) — the
// `Coq.PArith.BinPos.Pos.add` / `Pos.add_carry` shape.
//
// A 2-body mutual block `Fix { f0 := λargs. match x_r … ; f1 := λargs. match
// x_r … }` where both members share the SAME function type is encoded as ONE
// single structural fixpoint plus a `bool` selector post-argument:
//
//     combined := fix c (args…) (sel : bool) := match x_r with
//                   | C_j fields… =>
//                       bool_rect (fun _ => Ret) <f0's C_j body> <f1's C_j body> sel
//                 end
//     f0 := fun args… => c args… true          (member 0 → selector `true`)
//     f1 := fun args… => c args… false          (member 1 → selector `false`)
//
// A cross-call `f0 a…` inside a body becomes `c a… true` and `f1 a…` becomes
// `c a… false`; the single fixpoint then structuralizes through the existing
// `convert_serapi_fix` general (post-abstracted) encoding, which already
// tolerates self-calls whose post-struct arguments vary — so the changed
// `sel`/other post-args are handled by the recursor's induction hypothesis.
//
// The selector is appended as the LAST (innermost) argument, i.e. a POST-struct
// argument, on purpose: the recursor's motive is post-abstracted over the
// post-args, so the IH can be instantiated at the specific `true`/`false` a
// cross-call needs. (An outermost/PRE-struct selector would demand a
// selector-uniform recursion, which the cross-calls violate.)
//
// EVERYTHING is fail-closed: any unsupported sub-shape returns `Err`, and the
// assembled value is kernel-re-checked downstream, so a mis-encoding degrades
// to today's type-only masked axiom (zero regression, never unsound).

/// Raw `Coq.Init.Datatypes` templates for the `bool` selector machinery.
fn raw_bool_template(which: &str) -> Result<Sexp, String> {
    let src = match which {
        "ind" => {
            "(Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) \
                  (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))"
        }
        "rect" => {
            "(Const ((Constant (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) \
                   (Id Coq)))) (Id bool_rect)) ()) (Instance (() ()))))"
        }
        // SerAPI constructor index is 1-based: true = 1, false = 2.
        "true" => {
            "(Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) \
                   (Id Coq)))) (Id bool)) ()) 0) 1) (Instance (() ()))))"
        }
        "false" => {
            "(Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) \
                    (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))"
        }
        _ => return Err("mutual-fix: unknown bool template".to_string()),
    };
    parse_sexp(src).map_err(|e| format!("mutual-fix: bad bool template ({e:?})"))
}

/// A fresh anonymous `Relevant` binder annotation (for the selector binder).
fn raw_anon_binder() -> Result<Sexp, String> {
    parse_sexp("((binder_name Anonymous) (binder_relevance Relevant))")
        .map_err(|e| format!("mutual-fix: bad binder template ({e:?})"))
}

// ---------------------------------------------------------------------------
// Inner-match recursion (match-commutation) — `Pos.eqb` / `Pos.compare_cont` /
// `Z.pos_sub` / `Pos.sub_mask` shape: a fixpoint recursing on argument `r`
// whose OUTER match is on a DIFFERENT argument `x_j`, with the struct argument
// `x_r` matched at INNER depth inside every `x_j` branch. Both the single- and
// mutual-fix structuralizers require the outer match to be on the struct
// argument, so these fail closed.
//
// Preprocess: (1) COMMUTE the two matches so `x_r`'s match is outermost
// (`match x_j { c_i => match x_r { d_k => b_ik } }` →
//  `match x_r { d_k => match x_j { c_i => b_ik } }`, valid because the two
//  matches are on independent arguments and every branch inner-matches `x_r`
//  uniformly with a closed return type), then (2) REORDER the argument
//  telescope so `x_r` is first (`r' = 0`) — this turns the enclosing
//  arguments into POST-struct arguments, which the existing general
//  (post-abstracted) encoder can vary across recursive calls. The transformed
//  fixpoint is re-dispatched through `convert_serapi_fix` (single AND mutual),
//  then the focused member is projected back under the original argument order.
//
// Restricted (fail closed / fall through to the normal path otherwise) to:
// non-dependent argument and result types, at least one outer branch a match
// on `x_r`, and matching constructor field counts across the inner matches.
// Relocated match shells (parameters + return predicate) and reordered
// argument types have their free de Bruijn references lifted for their new
// binder depth; an outer branch that does NOT split `x_r` (a base case such
// as `Leaf => None`) is duplicated into every `x_r` branch. Any such RELAXED
// rule marks the emission speculative (`SPECULATIVE_MOTIVE_USED`), so a
// kernel rejection fails closed to a clean type-only axiom — the historical
// Rel-free closed-signature shapes are emitted byte-identically and unmarked.
// Kernel re-checks the assembled value, so this can never be unsound or a
// regression.

/// Walk a raw term remapping every free `(Rel n)` via `f(n, depth)` where
/// `depth` is the number of binders entered since the root. Fails closed on
/// nested `Fix`/`CoFix`/`Proj` (their binder structure is out of scope here).
fn raw_remap_rels(sexp: &Sexp, depth: u32, f: &dyn Fn(u32, u32) -> u32) -> Result<Sexp, String> {
    match sexp {
        Sexp::Atom(_) => Ok(sexp.clone()),
        Sexp::List(v) => {
            let head = v.first().and_then(|h| match h {
                Sexp::Atom(s) => Some(s.as_str()),
                _ => None,
            });
            match head {
                Some("Rel") if v.len() == 2 => {
                    let n = match &v[1] {
                        Sexp::Atom(s) => s
                            .parse::<u32>()
                            .map_err(|_| "commute: bad Rel".to_string())?,
                        _ => return Err("commute: bad Rel".to_string()),
                    };
                    Ok(Sexp::List(vec![
                        Sexp::Atom("Rel".to_string()),
                        Sexp::Atom(f(n, depth).to_string()),
                    ]))
                }
                Some("App") if v.len() == 3 => {
                    let func = raw_remap_rels(&v[1], depth, f)?;
                    let args = match &v[2] {
                        Sexp::List(a) => Sexp::List(
                            a.iter()
                                .map(|x| raw_remap_rels(x, depth, f))
                                .collect::<Result<Vec<_>, _>>()?,
                        ),
                        _ => return Err("commute: malformed application".to_string()),
                    };
                    Ok(Sexp::List(vec![Sexp::Atom("App".to_string()), func, args]))
                }
                Some("Lambda") | Some("Prod") if v.len() == 4 => {
                    let ty = raw_remap_rels(&v[2], depth, f)?;
                    let body = raw_remap_rels(&v[3], depth + 1, f)?;
                    Ok(Sexp::List(vec![v[0].clone(), v[1].clone(), ty, body]))
                }
                Some("LetIn") if v.len() == 5 => {
                    let ty = raw_remap_rels(&v[2], depth, f)?;
                    let val = raw_remap_rels(&v[3], depth, f)?;
                    let body = raw_remap_rels(&v[4], depth + 1, f)?;
                    Ok(Sexp::List(vec![v[0].clone(), v[1].clone(), ty, val, body]))
                }
                Some("Cast") if v.len() == 4 => {
                    let t = raw_remap_rels(&v[1], depth, f)?;
                    let ty = raw_remap_rels(&v[3], depth, f)?;
                    Ok(Sexp::List(vec![v[0].clone(), t, v[2].clone(), ty]))
                }
                Some("Case") if v.len() == 8 => raw_remap_case_rels(v, depth, f),
                Some("Const") | Some("Ind") | Some("Construct") | Some("Sort") | Some("Var")
                | Some("Int") | Some("Float") | Some("String") => Ok(sexp.clone()),
                _ => Err("commute: unsupported node in a match body".to_string()),
            }
        }
    }
}

/// `raw_remap_rels` for a raw `Case` node: parameters and discriminant at the
/// current depth, the return-predicate body under its own binders, each branch
/// body under its constructor fields.
fn raw_remap_case_rels(
    v: &[Sexp],
    depth: u32,
    f: &dyn Fn(u32, u32) -> u32,
) -> Result<Sexp, String> {
    let params = match &v[3] {
        Sexp::List(ps) => Sexp::List(
            ps.iter()
                .map(|p| raw_remap_rels(p, depth, f))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        other => other.clone(),
    };
    let return_pred = match &v[4] {
        Sexp::List(rpv) if !rpv.is_empty() => {
            let pred = match &rpv[0] {
                Sexp::List(p) if p.len() == 2 => p,
                _ => return Err("commute: malformed return predicate".to_string()),
            };
            let nb = match &pred[0] {
                Sexp::List(bs) => bs.len() as u32,
                _ => return Err("commute: malformed return-predicate binders".to_string()),
            };
            let body = raw_remap_rels(&pred[1], depth + nb, f)?;
            let mut rpv2 = rpv.clone();
            rpv2[0] = Sexp::List(vec![pred[0].clone(), body]);
            Sexp::List(rpv2)
        }
        other => other.clone(),
    };
    let disc = raw_remap_rels(&v[6], depth, f)?;
    let branches = match &v[7] {
        Sexp::List(bs) => Sexp::List(
            bs.iter()
                .map(|b| match b {
                    Sexp::List(bv) if bv.len() == 2 => {
                        let m = match &bv[0] {
                            Sexp::List(fs) => fs.len() as u32,
                            _ => return Err("commute: malformed branch binders".to_string()),
                        };
                        let body = raw_remap_rels(&bv[1], depth + m, f)?;
                        Ok(Sexp::List(vec![bv[0].clone(), body]))
                    }
                    other => Ok(other.clone()),
                })
                .collect::<Result<Vec<_>, _>>()?,
        ),
        other => other.clone(),
    };
    Ok(Sexp::List(vec![
        v[0].clone(),
        v[1].clone(),
        v[2].clone(),
        params,
        return_pred,
        v[5].clone(),
        disc,
        branches,
    ]))
}

/// Peel ALL leading raw `Prod` binders, returning `[(annot, dom)]` + result.
fn peel_all_raw_prods(ty: &Sexp) -> (Vec<(Sexp, Sexp)>, Sexp) {
    let mut acc = Vec::new();
    let mut cur = ty.clone();
    while let Sexp::List(v) = &cur {
        if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") {
            acc.push((v[1].clone(), v[2].clone()));
            let next = v[3].clone();
            cur = next;
        } else {
            break;
        }
    }
    (acc, cur)
}

/// A raw `(Rel n)` node.
fn raw_rel(n: u32) -> Sexp {
    Sexp::List(vec![
        Sexp::Atom("Rel".to_string()),
        Sexp::Atom(n.to_string()),
    ])
}

/// Commute + reorder one body of an inner-match fixpoint (see the module
/// comment). `k` = arity, `r` = recursion index, `j` = outer-match argument
/// index. Returns the transformed body `λ x_r x_0 … (skip r) …. match x_r {…}`
/// (struct argument first). Returns `Err` on any unsupported sub-shape. Sets
/// `relaxed` when a rule beyond the historical Rel-free/all-branches-match
/// shape fired (the caller marks the emission speculative — fail closed).
fn commute_reorder_body(
    lams: &[(Sexp, Sexp)],
    outer_case: &[Sexp],
    k: u32,
    r: u32,
    j: u32,
    nmemb: u32,
    relaxed: &mut bool,
) -> Result<Sexp, String> {
    let outer_branches = match &outer_case[7] {
        Sexp::List(b) if !b.is_empty() => b,
        _ => return Err("commute: outer match has no branches".to_string()),
    };
    // Inner match template (on x_r): the FIRST outer branch whose body is a
    // match on x_r supplies the x_r constructor split (branch and field
    // counts) and the shell (params + return predicate) for the commuted
    // outer match. Branch 0 was the historical requirement; any later
    // template is a relaxed shape.
    let mut template: Option<(usize, &Vec<Sexp>, u32)> = None;
    for (i, br) in outer_branches.iter().enumerate() {
        let c_i = branch_field_count(br)?;
        if let Ok((ic, _)) = split_branch_case(br, "commute: outer branch") {
            if ic[6] == raw_rel(k - r + c_i) {
                template = Some((i, ic, c_i));
                break;
            }
        }
    }
    let (t_idx, ic0, c_t) = template
        .ok_or_else(|| "commute: no outer branch matches on the struct argument".to_string())?;
    if t_idx != 0 {
        *relaxed = true;
    }
    // Relocate the template shell from under the template branch's `c_t`
    // fields to the outer-case level: shift free references down by `c_t`;
    // references INTO those fields cannot be relocated (fail closed).
    let shell_viol = std::cell::Cell::new(false);
    let down = |n: u32, d: u32| -> u32 {
        if n <= d {
            n
        } else if n - d <= c_t {
            shell_viol.set(true);
            n
        } else {
            n - c_t
        }
    };
    let (t_params, t_pred) = remap_case_shell(&ic0[3], &ic0[4], &down)?;
    if shell_viol.get() {
        return Err(
            "commute: struct-argument match shell mentions the outer branch's fields".to_string(),
        );
    }
    if t_params != ic0[3] || t_pred != ic0[4] {
        *relaxed = true;
    }
    let xr_branches0 = match &ic0[7] {
        Sexp::List(b) if !b.is_empty() => b,
        _ => return Err("commute: inner match has no branches".to_string()),
    };
    let xr_nbr = xr_branches0.len();

    // New outer branches: one per x_r constructor kk.
    let mut new_outer_branches = Vec::with_capacity(xr_nbr);
    for (kk, xr_br0) in xr_branches0.iter().enumerate() {
        let (xr_fields_kk, _b) = match xr_br0 {
            Sexp::List(bv) if bv.len() == 2 => (&bv[0], &bv[1]),
            _ => return Err("commute: malformed inner branch".to_string()),
        };
        let a_kk = match xr_fields_kk {
            Sexp::List(fs) => fs.len() as u32,
            _ => return Err("commute: malformed inner branch fields".to_string()),
        };
        // Relocate the outer shell under the `a_kk` x_r fields now binding
        // around it: lift every free reference by `a_kk`.
        let up = |n: u32, d: u32| -> u32 {
            if n > d {
                n + a_kk
            } else {
                n
            }
        };
        let (o_params, o_pred) = remap_case_shell(&outer_case[3], &outer_case[4], &up)?;
        if o_params != outer_case[3] || o_pred != outer_case[4] {
            *relaxed = true;
        }
        // New inner branches: one per x_j constructor i.
        let mut new_inner_branches = Vec::with_capacity(outer_branches.len());
        for outer_br in outer_branches.iter() {
            // `xj_fields` = this outer branch's x_j constructor field binders.
            let (xj_fields, raw_body) = match outer_br {
                Sexp::List(bv) if bv.len() == 2 => (&bv[0], &bv[1]),
                _ => return Err("commute: malformed outer branch".to_string()),
            };
            let c_i = match xj_fields {
                Sexp::List(fs) => fs.len() as u32,
                _ => return Err("commute: malformed outer branch fields".to_string()),
            };
            // `ic_i` = this outer branch's inner Case ON x_r (raw disc ==
            // Rel(k - r + c_i)), if the branch splits x_r at all.
            let inner_on_xr = split_branch_case(outer_br, "commute: outer branch")
                .ok()
                .filter(|(ic, _)| ic[6] == raw_rel(k - r + c_i));
            let b_new = if let Some((ic_i, _)) = inner_on_xr {
                let ic_i_branches = match &ic_i[7] {
                    Sexp::List(b) => b,
                    _ => return Err("commute: malformed inner branches".to_string()),
                };
                if ic_i_branches.len() != xr_nbr {
                    return Err("commute: inner matches split x_r inconsistently".to_string());
                }
                let (kk_fields, b_ik) = match &ic_i_branches[kk] {
                    Sexp::List(bv) if bv.len() == 2 => (&bv[0], &bv[1]),
                    _ => return Err("commute: malformed inner branch body".to_string()),
                };
                let this_a = match kk_fields {
                    Sexp::List(fs) => fs.len() as u32,
                    _ => return Err("commute: malformed inner branch fields".to_string()),
                };
                if this_a != a_kk {
                    return Err("commute: inner constructor field counts disagree".to_string());
                }
                // Swap the innermost `a_kk` (x_r fields) with the next `c_i`
                // (x_j fields): the x_r match becomes outer, the x_j match
                // inner.
                let swap = move |n: u32, d: u32| -> u32 {
                    if n <= d {
                        return n;
                    }
                    let m = n - d;
                    if m <= a_kk {
                        n + c_i
                    } else if m <= a_kk + c_i {
                        n - a_kk
                    } else {
                        n
                    }
                };
                raw_remap_rels(b_ik, 0, &swap)?
            } else {
                // This outer branch does NOT split x_r (a base case such as
                // `Leaf => None`): duplicate its body into every x_r branch,
                // lifting the references above its own `c_i` fields over the
                // `a_kk` x_r fields now binding around it. A relaxed shape.
                *relaxed = true;
                let lift = move |n: u32, d: u32| -> u32 {
                    if n > d && n - d > c_i {
                        n + a_kk
                    } else {
                        n
                    }
                };
                raw_remap_rels(raw_body, 0, &lift)?
            };
            new_inner_branches.push(Sexp::List(vec![xj_fields.clone(), b_new]));
        }
        // New inner Case (on x_j) reuses the ORIGINAL outer match shell
        // (lifted over the x_r fields); discriminant is x_j under the `a_kk`
        // x_r fields: Rel(k - j + a_kk).
        let new_inner_case = Sexp::List(vec![
            outer_case[0].clone(),
            outer_case[1].clone(),
            outer_case[2].clone(),
            o_params,
            o_pred,
            outer_case[5].clone(),
            raw_rel(k - j + a_kk),
            Sexp::List(new_inner_branches),
        ]);
        new_outer_branches.push(Sexp::List(vec![xr_fields_kk.clone(), new_inner_case]));
    }
    // New outer Case (on x_r) reuses the template inner match shell
    // (relocated to the outer-case level); discriminant is x_r at the
    // argument level: Rel(k - r).
    let new_outer_case = Sexp::List(vec![
        ic0[0].clone(),
        ic0[1].clone(),
        ic0[2].clone(),
        t_params,
        t_pred,
        ic0[5].clone(),
        raw_rel(k - r),
        Sexp::List(new_outer_branches),
    ]);

    // New argument order: [x_r, x_0, … (skip r) …]. perm[new] = orig index.
    let mut order: Vec<usize> = vec![r as usize];
    order.extend((0..k as usize).filter(|&i| i != r as usize));
    let perm: Vec<u32> = order.iter().map(|&i| i as u32).collect();

    // (a) Permute the argument LIST of every self-call to the new order, then
    // (b) remap argument-reference Rel VALUES so x_r moves to the front.
    let permuted_case = permute_self_call_args(&new_outer_case, 0, k, nmemb, &perm)?;
    let reorder = move |n: u32, d: u32| -> u32 {
        if n <= d {
            return n;
        }
        let m = n - d;
        if m > k {
            return n;
        }
        let v = m;
        let nv = if v == k - r {
            k
        } else if v > k - r {
            v - 1
        } else {
            v
        };
        nv + d
    };
    let reordered_case = raw_remap_rels(&permuted_case, 0, &reorder)?;
    let mut body = reordered_case;
    for (p, &idx) in order.iter().enumerate().rev() {
        let (annot, ty) = &lams[idx];
        // A moved binder type's references above the telescope prefix (the
        // fix binders and beyond) shift by the position delta; references
        // into the prefix were rejected by the telescope-dependency check.
        let ty2 = if p == idx {
            ty.clone()
        } else {
            let shift = move |n: u32, d: u32| -> u32 {
                if n > d && (n - d) as usize > idx {
                    n - idx as u32 + p as u32
                } else {
                    n
                }
            };
            raw_remap_rels(ty, 0, &shift)?
        };
        if ty2 != *ty {
            *relaxed = true;
        }
        body = Sexp::List(vec![
            Sexp::Atom("Lambda".to_string()),
            annot.clone(),
            ty2,
            body,
        ]);
    }
    Ok(body)
}

/// The number of constructor fields bound by a raw Case branch
/// `(fields body)`.
fn branch_field_count(branch: &Sexp) -> Result<u32, String> {
    match branch {
        Sexp::List(bv) if bv.len() == 2 => match &bv[0] {
            Sexp::List(fs) => Ok(fs.len() as u32),
            _ => Err("commute: malformed branch fields".to_string()),
        },
        _ => Err("commute: malformed branch".to_string()),
    }
}

/// Remap the free de Bruijn references of a raw Case SHELL (the parameter
/// list and the return predicate) via `f`, tracking the return predicate's
/// own binders. Used when the commute relocates a shell to a different
/// binder depth.
fn remap_case_shell(
    params: &Sexp,
    return_pred: &Sexp,
    f: &dyn Fn(u32, u32) -> u32,
) -> Result<(Sexp, Sexp), String> {
    let new_params = match params {
        Sexp::List(ps) => Sexp::List(
            ps.iter()
                .map(|p| raw_remap_rels(p, 0, f))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        other => other.clone(),
    };
    let new_pred = match return_pred {
        Sexp::List(rpv) if !rpv.is_empty() => {
            let pred = match &rpv[0] {
                Sexp::List(p) if p.len() == 2 => p,
                _ => return Err("commute: malformed return predicate".to_string()),
            };
            let nb = match &pred[0] {
                Sexp::List(bs) => bs.len() as u32,
                _ => return Err("commute: malformed return-predicate binders".to_string()),
            };
            let body = raw_remap_rels(&pred[1], nb, f)?;
            let mut rpv2 = rpv.clone();
            rpv2[0] = Sexp::List(vec![pred[0].clone(), body]);
            Sexp::List(rpv2)
        }
        other => other.clone(),
    };
    Ok((new_params, new_pred))
}

/// A branch `(fields body)` whose body is a raw `Case`; returns `(case_vec,
/// fields)`.
fn split_branch_case<'a>(branch: &'a Sexp, ctx: &str) -> Result<(&'a Vec<Sexp>, &'a Sexp), String> {
    let bv = match branch {
        Sexp::List(bv) if bv.len() == 2 => bv,
        _ => return Err(format!("{ctx}: malformed branch")),
    };
    let case = match &bv[1] {
        Sexp::List(cv) if cv.len() == 8 && matches!(&cv[0], Sexp::Atom(h) if h == "Case") => cv,
        _ => return Err(format!("{ctx}: branch body is not a match")),
    };
    Ok((case, &bv[0]))
}

/// If a fixpoint recurses on argument `r` but its OUTER match is on a different
/// argument (inner-match shape), commute + reorder every body and return the
/// transformed `(header', payload')` plus the argument permutation
/// (`perm[new] = orig`), raw argument types for the projection, and a
/// `relaxed` flag. Returns `Err` (with the blocking sub-shape, surfaced in
/// the fail-class report) when the shape is not inner-match or is not
/// supported — the caller then proceeds with, and fails closed via, the
/// normal path. `relaxed` is true when a rule beyond the historical
/// Rel-free/all-branches-match shape fired (relocated Rel-bearing shells,
/// duplicated non-matching branches, position-shifted argument types): the
/// caller marks the emission speculative so a kernel rejection falls back to
/// a clean type-only axiom.
fn try_commute_reorder_fix(
    header: &Sexp,
    payload: &Sexp,
) -> Result<(Sexp, Sexp, Vec<u32>, Vec<Sexp>, bool), String> {
    let (rec_args, which) = match header {
        Sexp::List(v) if v.len() == 2 => (&v[0], &v[1]),
        _ => return Err("commute: malformed fixpoint header".to_string()),
    };
    let recs: Vec<u32> = match rec_args {
        Sexp::List(v) if !v.is_empty() => v
            .iter()
            .map(|x| match x {
                Sexp::Atom(s) => s.parse::<u32>().ok(),
                _ => None,
            })
            .collect::<Option<_>>()
            .ok_or_else(|| "commute: malformed recursive-argument indices".to_string())?,
        _ => return Err("commute: malformed recursive-argument indices".to_string()),
    };
    // Only single or 2-body blocks; all members recurse on the same index.
    if recs.len() > 2 {
        return Err("commute: mutual blocks beyond two members unsupported".to_string());
    }
    let r = recs[0];
    if recs.iter().any(|&x| x != r) {
        return Err("commute: members recurse on different argument indices".to_string());
    }
    let (annots, types, bodies) = match payload {
        Sexp::List(v) if v.len() == 3 => match (&v[1], &v[2]) {
            (Sexp::List(t), Sexp::List(b)) if t.len() == b.len() && t.len() == recs.len() => {
                (&v[0], t, b)
            }
            _ => return Err("commute: malformed fixpoint payload".to_string()),
        },
        _ => return Err("commute: malformed fixpoint payload".to_string()),
    };
    // Shared non-dependent signature: peel the arg telescope; no references
    // into the telescope prefix (external references are fine — relocations
    // lift them).
    let (arg_prods, tret) = peel_all_raw_prods(&types[0]);
    let k = arg_prods.len() as u32;
    if k < 2 {
        return Err("commute: fixpoint binds fewer than two arguments".to_string());
    }
    if r >= k {
        return Err("commute: recursive index beyond the bound arity".to_string());
    }
    if raw_mentions_rel(&tret, k) {
        return Err("commute: dependent result type".to_string());
    }
    for (i, (_, ty)) in arg_prods.iter().enumerate() {
        if raw_mentions_rel(ty, i as u32) {
            return Err("commute: dependent argument telescope".to_string());
        }
    }
    // All member types must be identical (equal signature).
    if types.iter().any(|t| t != &types[0]) {
        return Err("commute: mutual member types differ".to_string());
    }

    let mut relaxed = false;
    // Determine the outer-match argument `j` from body 0; require inner-match.
    let mut j_opt: Option<u32> = None;
    let mut new_bodies = Vec::with_capacity(bodies.len());
    for body in bodies {
        let (lams, oc) = peel_raw_lambdas(body, k)
            .map_err(|_| "commute: body binds fewer arguments than the arity".to_string())?;
        let ocv = match &oc {
            Sexp::List(v) if v.len() == 8 && matches!(&v[0], Sexp::Atom(h) if h == "Case") => v,
            _ => {
                return Err("commute: body is not a lambda spine ending in a match".to_string());
            }
        };
        // Outer discriminant Rel(dn); struct arg is Rel(k - r).
        let dn = match &ocv[6] {
            Sexp::List(d) if d.len() == 2 && matches!(&d[0], Sexp::Atom(h) if h == "Rel") => {
                match &d[1] {
                    Sexp::Atom(s) => s
                        .parse::<u32>()
                        .map_err(|_| "commute: malformed outer discriminant".to_string())?,
                    _ => return Err("commute: malformed outer discriminant".to_string()),
                }
            }
            _ => {
                return Err("commute: outer match discriminant is not an argument".to_string());
            }
        };
        if dn == k - r {
            // Outer match already on the struct arg — normal path.
            return Err("commute: outer match is already on the struct argument".to_string());
        }
        if dn == 0 || dn > k {
            return Err("commute: outer discriminant outside the argument telescope".to_string());
        }
        let j = k - dn;
        if j == r {
            return Err("commute: outer match is already on the struct argument".to_string());
        }
        match j_opt {
            None => j_opt = Some(j),
            Some(pj) if pj != j => {
                return Err("commute: members match on different arguments".to_string());
            }
            _ => {}
        }
        let new_body = commute_reorder_body(&lams, ocv, k, r, j, recs.len() as u32, &mut relaxed)?;
        new_bodies.push(new_body);
    }

    // Reorder the type telescope: x_r first, then the rest in order. A moved
    // argument type's references above the telescope prefix shift by the
    // position delta; references into the prefix were rejected above.
    let mut order: Vec<usize> = vec![r as usize];
    order.extend((0..k as usize).filter(|&i| i != r as usize));
    let mut new_doms: Vec<(Sexp, Sexp)> = Vec::with_capacity(order.len());
    for (p, &idx) in order.iter().enumerate() {
        let (annot, dom) = &arg_prods[idx];
        let dom2 = if p == idx {
            dom.clone()
        } else {
            let shift = move |n: u32, d: u32| -> u32 {
                if n > d && (n - d) as usize > idx {
                    n - idx as u32 + p as u32
                } else {
                    n
                }
            };
            raw_remap_rels(dom, 0, &shift)?
        };
        if dom2 != *dom {
            relaxed = true;
        }
        new_doms.push((annot.clone(), dom2));
    }
    let new_type = new_doms
        .iter()
        .rev()
        .fold(tret.clone(), |acc, (annot, dom)| {
            Sexp::List(vec![
                Sexp::Atom("Prod".to_string()),
                annot.clone(),
                dom.clone(),
                acc,
            ])
        });

    // Rebuild header (r' = 0) and payload. rec_args = (0) for every member.
    let new_recs =
        Sexp::List(std::iter::repeat_n(Sexp::Atom("0".to_string()), recs.len()).collect());
    let new_header = Sexp::List(vec![new_recs, which.clone()]);
    let new_payload = Sexp::List(vec![
        annots.clone(),
        Sexp::List(std::iter::repeat_n(new_type, recs.len()).collect()),
        Sexp::List(new_bodies),
    ]);
    let perm: Vec<u32> = order.iter().map(|&i| i as u32).collect();
    let raw_arg_tys: Vec<Sexp> = arg_prods.iter().map(|(_, t)| t.clone()).collect();
    Ok((new_header, new_payload, perm, raw_arg_tys, relaxed))
}

/// Last-resort structuralization for a single `Fix` recursing on argument
/// `r > 0` whose match is ALREADY on the struct argument (so
/// [`try_commute_reorder_fix`] does not apply) but a PRE-struct argument VARIES
/// across self-calls — the accumulator shape `tail_addmul (r+m) n m := match n …`
/// that both the strict encoder and the post-abstracting general encoder reject
/// (a pre-struct binder is a recursor parameter, fixed across the recursion).
///
/// Rotate the struct argument to the front (`r' = 0`): EVERY non-struct binder
/// then becomes POST-struct, which the general encoder abstracts into the motive
/// and lets vary. The permuted `(header', payload', perm, raw_arg_tys)` is
/// re-dispatched through [`convert_serapi_fix`] and projected back with
/// [`project_arg_permutation`] — the exact composition
/// [`commute_reorder_body`] uses, minus the match commutation (the match is
/// already on `x_r`). Returns `None` unless the shape is this case. Requires a
/// closed (non-dependent) argument telescope and return type so reordering the
/// binders stays well-typed; the kernel re-checks the result regardless.
fn try_rotate_struct_to_front_fix(
    header: &Sexp,
    payload: &Sexp,
) -> Option<(Sexp, Sexp, Vec<u32>, Vec<Sexp>)> {
    let (rec_args, which) = match header {
        Sexp::List(v) if v.len() == 2 => (&v[0], &v[1]),
        _ => return None,
    };
    // Single fixpoint focused on member 0; mutual blocks are handled elsewhere.
    let r = match rec_args {
        Sexp::List(v) if v.len() == 1 => match &v[0] {
            Sexp::Atom(s) => s.parse::<u32>().ok()?,
            _ => return None,
        },
        _ => return None,
    };
    if r == 0 || !matches!(which, Sexp::Atom(s) if s == "0") {
        return None; // no pre-struct binders to move (or non-zero focus)
    }
    let (annots, types, bodies) = match payload {
        Sexp::List(v) if v.len() == 3 => match (&v[1], &v[2]) {
            (Sexp::List(t), Sexp::List(b)) if t.len() == 1 && b.len() == 1 => (&v[0], &t[0], &b[0]),
            _ => return None,
        },
        _ => return None,
    };
    let (arg_prods, tret) = peel_all_raw_prods(types);
    let k = arg_prods.len() as u32;
    if k < 2 || r >= k {
        return None;
    }
    // Closed signature: reordering the telescope must stay well-typed.
    if raw_mentions_rel(&tret, k) {
        return None;
    }
    for (i, (_, ty)) in arg_prods.iter().enumerate() {
        if raw_mentions_rel(ty, i as u32) {
            return None;
        }
    }
    // Body: k lambdas down to a Case that must be ON the struct argument x_r
    // (raw disc == Rel(k - r)); anything else is the inner-match case.
    let (lams, oc) = peel_raw_lambdas(bodies, k).ok()?;
    let ocv = match &oc {
        Sexp::List(v) if v.len() == 8 && matches!(&v[0], Sexp::Atom(h) if h == "Case") => v,
        _ => return None,
    };
    if ocv[6] != raw_rel(k - r) {
        return None; // match is not on the struct argument
    }
    // New order: [x_r, x_0 … x_{r-1}, x_{r+1} … x_{k-1}]. perm[new] = orig index.
    let mut order: Vec<usize> = vec![r as usize];
    order.extend((0..k as usize).filter(|&i| i != r as usize));
    let perm: Vec<u32> = order.iter().map(|&i| i as u32).collect();
    // (a) Permute the argument LIST of every self-call to the new order, then
    // (b) remap argument-reference Rel VALUES so x_r moves to the front —
    // identical to commute_reorder_body's reorder tail.
    let permuted = permute_self_call_args(&oc, 0, k, 1, &perm).ok()?;
    let reorder = move |n: u32, d: u32| -> u32 {
        if n <= d {
            return n;
        }
        let m = n - d;
        if m > k {
            return n;
        }
        let nv = if m == k - r {
            k
        } else if m > k - r {
            m - 1
        } else {
            m
        };
        nv + d
    };
    let reordered = raw_remap_rels(&permuted, 0, &reorder).ok()?;
    // Remap an argument type/domain that moves from original index `oi` to new
    // index `ni`. Its type sits in a context with only the PRECEDING telescope
    // binders in scope, and the closedness checks above guarantee it references
    // none of them — so every free reference points at the OUTER context and
    // was counted through `oi` preceding binders. After the move it counts
    // through `ni`, shifting by `ni - oi`. The `d` depth tracks binders INTERNAL
    // to the type (a nested `Π`/`λ` domain) so only genuine outer references
    // shift; `oi == ni` (e.g. the return type, or a fixed argument) is identity.
    let remap_dom = |dom: &Sexp, oi: usize, ni: usize| -> Option<Sexp> {
        if oi == ni {
            return Some(dom.clone());
        }
        let shift = ni as i64 - oi as i64;
        raw_remap_rels(dom, 0, &move |n: u32, d: u32| {
            if (n as i64) > (d as i64) + (oi as i64) {
                (n as i64 + shift) as u32
            } else {
                n
            }
        })
        .ok()
    };
    let mut new_body = reordered;
    for ni in (0..order.len()).rev() {
        let oi = order[ni];
        let (annot, ty) = &lams[oi];
        let ty = remap_dom(ty, oi, ni)?;
        new_body = Sexp::List(vec![
            Sexp::Atom("Lambda".to_string()),
            annot.clone(),
            ty,
            new_body,
        ]);
    }
    // New type telescope: x_r first, rest in order. Each domain's outer
    // references are remapped for its changed position; `tret` (closed over the
    // telescope, all k binders retained) needs no remap.
    let mut new_type = tret;
    for ni in (0..order.len()).rev() {
        let oi = order[ni];
        let (annot, dom) = &arg_prods[oi];
        let dom = remap_dom(dom, oi, ni)?;
        new_type = Sexp::List(vec![
            Sexp::Atom("Prod".to_string()),
            annot.clone(),
            dom,
            new_type,
        ]);
    }
    let new_header = Sexp::List(vec![
        Sexp::List(vec![Sexp::Atom("0".to_string())]),
        which.clone(),
    ]);
    let new_payload = Sexp::List(vec![
        annots.clone(),
        Sexp::List(vec![new_type]),
        Sexp::List(vec![new_body]),
    ]);
    let raw_arg_tys: Vec<Sexp> = arg_prods.iter().map(|(_, t)| t.clone()).collect();
    Some((new_header, new_payload, perm, raw_arg_tys))
}

/// Binder-aware occurrence check: does the raw term reference the binder that
/// sits at 1-based `Rel t` from the term's ROOT (i.e. some `(Rel n)` with
/// `n == depth + t`)? `None` when the traversal hits a node
/// [`raw_remap_rels`] does not understand (nested `Fix`/`CoFix`/`Proj`), so
/// callers fail closed instead of trusting an incomplete scan.
fn raw_scan_rel_at(sexp: &Sexp, t: u32) -> Option<bool> {
    let hit = std::cell::Cell::new(false);
    raw_remap_rels(sexp, 0, &|n, d| {
        if n == d + t {
            hit.set(true);
        }
        n
    })
    .ok()?;
    Some(hit.get())
}

/// Last-resort structuralization for the `div2` / `even` shape: a single
/// structural `Fix` whose recursion descends TWO constructor levels — exactly
/// one outer branch's body is ANOTHER match on that branch's SINGLE field,
/// with the self-calls recursing on the INNER match's fields:
///
/// ```text
/// fix f (x…) {struct r} := match x_r with
///   | C_a …    => B_a
///   | C_b (y)  => match y with | D_c (y') => … (f … y' …) … end
/// ```
///
/// The plain recursor's induction hypothesis covers only DIRECT fields (for
/// `C_b y` it supplies `f y`, never `f y'`), so both the strict and the
/// general encoder reject the self-call ("struct argument is not a recursive
/// field"). But the shape is EQUIVALENT to a 2-body mutual fixpoint in which
/// every self-call IS on a direct field:
///
/// ```text
/// fix f (x…) := match x_r with | C_a … => B_a | C_b y => g x…[x_r:=y]
/// with g (x…) := match x_r with | D_c (y') => … (f … y' …) …
/// ```
///
/// (`g` reuses `f`'s signature with the inner scrutinee in the struct slot.)
/// The existing 2-body machinery ([`convert_serapi_mutual_fix`]) then combines
/// the members with a `bool` selector post-argument and encodes the result
/// through the general post-abstracted recursor, whose IH tolerates the
/// varying selector.
///
/// Returns the mutual `(header, payload)` ready for
/// [`convert_serapi_mutual_fix`], or `None` when the shape does not apply.
/// Restricted to: a closed argument telescope and result type (`g` reuses the
/// signature verbatim, and the selector motive downstream is non-dependent),
/// exactly ONE splittable branch (each extra one would need its own mutual
/// member), the fix self occurring inside that branch's inner match, both
/// matches on the SAME inductive, and no reference to the outer struct binder
/// `x_r` from inside the inner match (its slot is rebound to the inner
/// scrutinee, so a genuine `x_r` reference is unrepresentable). The caller
/// marks the composition speculative; the kernel re-checks the assembled
/// value, so a mis-split fails closed to a clean type-only axiom.
fn try_split_nested_match_fix(header: &Sexp, payload: &Sexp) -> Option<(Sexp, Sexp)> {
    // header = ((r) 0) — single fixpoint focused on member 0.
    let (rec_args, which) = match header {
        Sexp::List(v) if v.len() == 2 => (&v[0], &v[1]),
        _ => return None,
    };
    let r = match rec_args {
        Sexp::List(v) if v.len() == 1 => match &v[0] {
            Sexp::Atom(s) => s.parse::<u32>().ok()?,
            _ => return None,
        },
        _ => return None,
    };
    if !matches!(which, Sexp::Atom(s) if s == "0") {
        return None;
    }
    // payload = ((annot) (T) (B))
    let (annots, fix_ty, fix_body) = match payload {
        Sexp::List(v) if v.len() == 3 => match (&v[1], &v[2]) {
            (Sexp::List(t), Sexp::List(b)) if t.len() == 1 && b.len() == 1 => (&v[0], &t[0], &b[0]),
            _ => return None,
        },
        _ => return None,
    };
    let (arg_prods, tret) = peel_all_raw_prods(fix_ty);
    let k = arg_prods.len() as u32;
    if k == 0 || r >= k {
        return None;
    }
    // Closed signature: no argument type may depend on an earlier argument and
    // the result type may not depend on any.
    if raw_mentions_rel(&tret, k) {
        return None;
    }
    for (i, (_, ty)) in arg_prods.iter().enumerate() {
        if raw_mentions_rel(ty, i as u32) {
            return None;
        }
    }
    // Body: k lambdas down to a Case on the struct argument.
    let (lams, oc) = peel_raw_lambdas(fix_body, k).ok()?;
    let ocv = match &oc {
        Sexp::List(v) if v.len() == 8 && matches!(&v[0], Sexp::Atom(h) if h == "Case") => v,
        _ => return None,
    };
    if ocv[6] != raw_rel(k - r) {
        return None; // outer match is not on the struct argument
    }
    let branches = match &ocv[7] {
        Sexp::List(bs) if !bs.is_empty() => bs,
        _ => return None,
    };
    // Find the ONE splittable branch: a single field, the body EXACTLY a Case
    // on that field, same inductive as the outer match, fix self inside. From
    // the inner-case root the context is `[Γ, f, x_1..x_k, field]`, so the fix
    // binder sits at `Rel(k + 2)` and `x_r` at `Rel(1 + k - r)`.
    let mut split: Option<usize> = None;
    for (j, b) in branches.iter().enumerate() {
        let (fields, body) = match b {
            Sexp::List(bv) if bv.len() == 2 => (&bv[0], &bv[1]),
            _ => return None,
        };
        let m = match fields {
            Sexp::List(fv) => fv.len() as u32,
            _ => return None,
        };
        let nested = match body {
            Sexp::List(nv) if nv.len() == 8 && matches!(&nv[0], Sexp::Atom(h) if h == "Case") => nv,
            _ => continue,
        };
        if m != 1 || nested[6] != raw_rel(1) || nested[1] != ocv[1] {
            continue;
        }
        if !raw_scan_rel_at(body, k + 2)? {
            continue; // no self-recursion inside: a plain nested match
        }
        if split.is_some() {
            return None; // two splittable branches would need a 3-body block
        }
        if raw_scan_rel_at(body, 1 + k - r)? {
            return None; // inner match references the outer struct binder
        }
        split = Some(j);
    }
    let split_j = split?;
    let nested_case = match &branches[split_j] {
        Sexp::List(bv) => &bv[1],
        _ => return None,
    };

    // Member 0: the outer case in the widened context `[Γ, f, g, x…]` — the
    // inserted `g` shifts `f` and everything outer by one — with the split
    // branch's body replaced by the saturated `g` call (struct slot := the
    // branch field; from the branch root, `g` sits at `Rel(1 + k + 1)`).
    let shifted_outer = raw_remap_rels(&oc, 0, &|n, d| if n <= d + k { n } else { n + 1 }).ok()?;
    let g_call = {
        let args: Vec<Sexp> = (0..k)
            .map(|s| {
                if s == r {
                    raw_rel(1)
                } else {
                    raw_rel(1 + k - s)
                }
            })
            .collect();
        Sexp::List(vec![
            Sexp::Atom("App".to_string()),
            raw_rel(k + 2),
            Sexp::List(args),
        ])
    };
    let member0_case = {
        let Sexp::List(mut cv) = shifted_outer else {
            return None;
        };
        let Sexp::List(mut bs) = cv[7].clone() else {
            return None;
        };
        let Sexp::List(bv) = &bs[split_j] else {
            return None;
        };
        bs[split_j] = Sexp::List(vec![bv[0].clone(), g_call]);
        cv[7] = Sexp::List(bs);
        Sexp::List(cv)
    };

    // Member 1: the inner case relocated from `[Γ, f, x…, field]` to
    // `[Γ, f, g, x…]` — the field merges into `x_r`, the other arguments shift
    // down across the removed field binder, `f` and the outer context keep
    // their offsets (`+1` for `g` cancels `-1` for the field).
    let member1_case = raw_remap_rels(nested_case, 0, &|n, d| {
        if n <= d {
            return n;
        }
        let m = n - d;
        if m == 1 {
            d + (k - r)
        } else if m <= 1 + k {
            n - 1
        } else {
            n
        }
    })
    .ok()?;

    // Wrap both members in the argument lambdas. A lambda TYPE at binder `i`
    // (0-based) sits under `[Γ, f, x_1..x_i]` — `i` locals, then `f` at
    // `Rel(i+1)`. In the widened `[Γ, f, g, x_1..x_i]` the inserted `g` shifts
    // `f` and everything outer by one; locals keep their offsets.
    let wrap_member = |case: Sexp| -> Option<Sexp> {
        let mut b = case;
        for (i, (annot, ty)) in lams.iter().enumerate().rev() {
            let ty2 = raw_remap_rels(ty, 0, &|n, d| {
                if n <= d + i as u32 {
                    n
                } else {
                    n + 1
                }
            })
            .ok()?;
            b = Sexp::List(vec![
                Sexp::Atom("Lambda".to_string()),
                annot.clone(),
                ty2,
                b,
            ]);
        }
        Some(b)
    };
    let body0 = wrap_member(member0_case)?;
    let body1 = wrap_member(member1_case)?;

    // Assemble the 2-body mutual block: header ((r r) 0), shared signature.
    let annot0 = match annots {
        Sexp::List(a) if !a.is_empty() => a[0].clone(),
        other => other.clone(),
    };
    let mutual_header = Sexp::List(vec![
        Sexp::List(vec![Sexp::Atom(r.to_string()), Sexp::Atom(r.to_string())]),
        Sexp::Atom("0".to_string()),
    ]);
    let mutual_payload = Sexp::List(vec![
        Sexp::List(vec![annot0.clone(), annot0]),
        Sexp::List(vec![fix_ty.clone(), fix_ty.clone()]),
        Sexp::List(vec![body0, body1]),
    ]);
    Some((mutual_header, mutual_payload))
}

/// Permute the ARGUMENT LIST of every recursive self-call to match the
/// reordered argument telescope (struct argument moved to the front). At local
/// depth `fd` the fix binders sit at raw `Rel(fd+k+1 ..= fd+k+nmemb)`; a
/// saturated self-call `App(Rel(fix), [a_0..a_{k-1}])` becomes
/// `App(Rel(fix), [a_{perm[0]} .. a_{perm[k-1]}])`. Rel VALUES are untouched
/// here (a separate reorder pass remaps them); only list order changes.
fn permute_self_call_args(
    sexp: &Sexp,
    fd: u32,
    k: u32,
    nmemb: u32,
    perm: &[u32],
) -> Result<Sexp, String> {
    match sexp {
        Sexp::Atom(_) => Ok(sexp.clone()),
        Sexp::List(v) => {
            let head = v.first().and_then(|h| match h {
                Sexp::Atom(s) => Some(s.as_str()),
                _ => None,
            });
            match head {
                // Rel values are untouched here (the reorder pass remaps them);
                // pass through so a bare reference is not mistaken for an
                // unsupported node.
                Some("Rel") if v.len() == 2 => Ok(sexp.clone()),
                Some("App") if v.len() == 3 => {
                    let is_self = match &v[1] {
                        Sexp::List(hv)
                            if hv.len() == 2 && matches!(&hv[0], Sexp::Atom(h) if h == "Rel") =>
                        {
                            match &hv[1] {
                                Sexp::Atom(s) => s
                                    .parse::<u32>()
                                    .ok()
                                    .map(|n| n > fd + k && n <= fd + k + nmemb)
                                    .unwrap_or(false),
                                _ => false,
                            }
                        }
                        _ => false,
                    };
                    let args = match &v[2] {
                        Sexp::List(a) => a,
                        _ => return Err("commute: malformed application".to_string()),
                    };
                    if is_self {
                        if args.len() != k as usize {
                            return Err(
                                "commute: recursive call not saturated at the arity".to_string()
                            );
                        }
                        let permuted = perm
                            .iter()
                            .map(|&p| permute_self_call_args(&args[p as usize], fd, k, nmemb, perm))
                            .collect::<Result<Vec<_>, _>>()?;
                        Ok(Sexp::List(vec![
                            Sexp::Atom("App".to_string()),
                            v[1].clone(),
                            Sexp::List(permuted),
                        ]))
                    } else {
                        let func = permute_self_call_args(&v[1], fd, k, nmemb, perm)?;
                        let new_args = args
                            .iter()
                            .map(|a| permute_self_call_args(a, fd, k, nmemb, perm))
                            .collect::<Result<Vec<_>, _>>()?;
                        Ok(Sexp::List(vec![
                            Sexp::Atom("App".to_string()),
                            func,
                            Sexp::List(new_args),
                        ]))
                    }
                }
                Some("Lambda") | Some("Prod") if v.len() == 4 => {
                    let ty = permute_self_call_args(&v[2], fd, k, nmemb, perm)?;
                    let body = permute_self_call_args(&v[3], fd + 1, k, nmemb, perm)?;
                    Ok(Sexp::List(vec![v[0].clone(), v[1].clone(), ty, body]))
                }
                Some("LetIn") if v.len() == 5 => {
                    let ty = permute_self_call_args(&v[2], fd, k, nmemb, perm)?;
                    let val = permute_self_call_args(&v[3], fd, k, nmemb, perm)?;
                    let body = permute_self_call_args(&v[4], fd + 1, k, nmemb, perm)?;
                    Ok(Sexp::List(vec![v[0].clone(), v[1].clone(), ty, val, body]))
                }
                Some("Cast") if v.len() == 4 => {
                    let t = permute_self_call_args(&v[1], fd, k, nmemb, perm)?;
                    let ty = permute_self_call_args(&v[3], fd, k, nmemb, perm)?;
                    Ok(Sexp::List(vec![v[0].clone(), t, v[2].clone(), ty]))
                }
                Some("Case") if v.len() == 8 => {
                    let params = match &v[3] {
                        Sexp::List(ps) => Sexp::List(
                            ps.iter()
                                .map(|p| permute_self_call_args(p, fd, k, nmemb, perm))
                                .collect::<Result<Vec<_>, _>>()?,
                        ),
                        other => other.clone(),
                    };
                    let return_pred = match &v[4] {
                        Sexp::List(rpv) if !rpv.is_empty() => {
                            let pred = match &rpv[0] {
                                Sexp::List(p) if p.len() == 2 => p,
                                _ => return Err("commute: malformed return predicate".to_string()),
                            };
                            let nb = match &pred[0] {
                                Sexp::List(bs) => bs.len() as u32,
                                _ => return Err("commute: malformed return binders".to_string()),
                            };
                            let body = permute_self_call_args(&pred[1], fd + nb, k, nmemb, perm)?;
                            let mut rpv2 = rpv.clone();
                            rpv2[0] = Sexp::List(vec![pred[0].clone(), body]);
                            Sexp::List(rpv2)
                        }
                        other => other.clone(),
                    };
                    let disc = permute_self_call_args(&v[6], fd, k, nmemb, perm)?;
                    let branches = match &v[7] {
                        Sexp::List(bs) => Sexp::List(
                            bs.iter()
                                .map(|b| match b {
                                    Sexp::List(bv) if bv.len() == 2 => {
                                        let m = match &bv[0] {
                                            Sexp::List(fs) => fs.len() as u32,
                                            _ => {
                                                return Err(
                                                    "commute: malformed branch binders".to_string()
                                                )
                                            }
                                        };
                                        let body =
                                            permute_self_call_args(&bv[1], fd + m, k, nmemb, perm)?;
                                        Ok(Sexp::List(vec![bv[0].clone(), body]))
                                    }
                                    other => Ok(other.clone()),
                                })
                                .collect::<Result<Vec<_>, _>>()?,
                        ),
                        other => other.clone(),
                    };
                    Ok(Sexp::List(vec![
                        v[0].clone(),
                        v[1].clone(),
                        v[2].clone(),
                        params,
                        return_pred,
                        v[5].clone(),
                        disc,
                        branches,
                    ]))
                }
                Some("Const") | Some("Ind") | Some("Construct") | Some("Sort") | Some("Var")
                | Some("Int") | Some("Float") | Some("String") => Ok(sexp.clone()),
                _ => Err("commute: unsupported node in a match body".to_string()),
            }
        }
    }
}

/// Project the focused member back under the ORIGINAL argument order:
/// `λ x_0 … x_{k-1}. combined <args in reordered order>`.
fn project_arg_permutation(
    combined: Sexp,
    raw_arg_tys: &[Sexp],
    perm: &[u32],
    ctx: &SerapiNormCtx,
    bctx: &[Option<Sexp>],
) -> Result<Sexp, String> {
    let k = raw_arg_tys.len();
    let mut proj_bctx = bctx.to_vec();
    let mut dtys = Vec::with_capacity(k);
    for ty in raw_arg_tys {
        let dt = normalize_serapi_rec(ty, ctx, &proj_bctx);
        proj_bctx.push(Some(dt.clone()));
        dtys.push(dt);
    }
    // `combined` was converted at the ORIGINAL fix position; the projection
    // wraps it under `k` fresh binders, so its free references (e.g. an
    // enclosing type-parameter binder `A`) must be lifted over them. Identity
    // for the closed historical shapes (`Pos.eqb`, ...).
    let combined = dialect_lift(&combined, k as u32, 0)?;
    // combined applied to the original args in the reordered order.
    let mut app = vec![Sexp::Atom("App".to_string()), combined];
    for &p in perm {
        // orig arg `p` is at dialect Rel(k - 1 - p) under λ x_0 … x_{k-1}.
        app.push(raw_rel(k as u32 - 1 - p));
    }
    let mut body = Sexp::List(app);
    for i in (0..k).rev() {
        body = Sexp::List(vec![
            Sexp::Atom("Lambda".to_string()),
            Sexp::Atom(format!("x{i}")),
            dtys[i].clone(),
            body,
        ]);
    }
    Ok(body)
}

/// Does the raw term mention a de Bruijn `(Rel n)` with `n <= depth` (a
/// reference into the argument telescope, 1-based)? Used to reject dependent
/// result types (the non-dependent `bool` selector motive would be unsound).
fn raw_mentions_rel(sexp: &Sexp, depth: u32) -> bool {
    match sexp {
        Sexp::Atom(_) => false,
        Sexp::List(v) => {
            if v.len() == 2 {
                if let (Sexp::Atom(h), Sexp::Atom(n)) = (&v[0], &v[1]) {
                    if h == "Rel" {
                        if let Ok(k) = n.parse::<u32>() {
                            return k <= depth;
                        }
                    }
                }
            }
            v.iter().any(|c| raw_mentions_rel(c, depth))
        }
    }
}

/// Peel `k` raw `Prod` binders from a function type, returning
/// `[(binder-annot, dom-type)]` and the result type (under the `k` binders).
fn peel_raw_prods(ty: &Sexp, k: u32) -> Result<(Vec<(Sexp, Sexp)>, Sexp), String> {
    let mut acc = Vec::with_capacity(k as usize);
    let mut cur = ty.clone();
    for _ in 0..k {
        match cur {
            Sexp::List(v) if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") => {
                acc.push((v[1].clone(), v[2].clone()));
                cur = v[3].clone();
            }
            _ => {
                return Err("mutual-fix: type binds fewer args than the recursion arity".to_string())
            }
        }
    }
    Ok((acc, cur))
}

/// Peel `k` raw `Lambda` binders (dropping `Cast`s), returning
/// `[(binder-annot, dom-type)]` and the body (the `match` node) beneath.
fn peel_raw_lambdas(body: &Sexp, k: u32) -> Result<(Vec<(Sexp, Sexp)>, Sexp), String> {
    let mut acc = Vec::with_capacity(k as usize);
    let mut cur = body.clone();
    for _ in 0..k {
        // Drop casts along the spine.
        loop {
            match cur {
                Sexp::List(ref v)
                    if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Cast") =>
                {
                    cur = v[1].clone();
                }
                _ => break,
            }
        }
        match cur {
            Sexp::List(v) if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Lambda") => {
                acc.push((v[1].clone(), v[2].clone()));
                cur = v[3].clone();
            }
            _ => {
                return Err("mutual-fix: body binds fewer args than the recursion arity".to_string())
            }
        }
    }
    Ok((acc, cur))
}

/// Rewrite a mutual-block body for the combined single fixpoint.
///
/// `fd` = number of binders below the enclosing arguments at this point (the
/// match-field depth); `k` = the shared arity. The two fix binders sit at raw
/// `Rel(fd+k+1)` (member 1 / `add_carry`) and `Rel(fd+k+2)` (member 0 / `add`);
/// the combined single binder sits at `Rel(fd+k+2)` (one extra selector arg
/// makes up for one fewer fix binder). The rules:
///   * `n <= fd`                 — local field / deeper binder: unchanged.
///   * `fd+1 <= n <= fd+k`       — an enclosing argument: shift `+1` (the
///                                 inserted selector binder sits just below it).
///   * `n == fd+k+1` / `fd+k+2`  — bare fix reference: fail closed.
///   * `n >= fd+k+3`             — outer context: unchanged (`+1` for the
///                                 selector cancels `-1` for the merged binder).
/// A saturated self-call `App(Rel(fd+k+1|fd+k+2), a_0..a_{k-1})` becomes
/// `App(Rel(fd+k+2), a'_0..a'_{k-1}, selector)`.
fn remap_mutual_body(sexp: &Sexp, fd: u32, k: u32) -> Result<Sexp, String> {
    let self_add = fd + k + 2; // member 0
    let self_carry = fd + k + 1; // member 1
    let rel = |n: u32| {
        Sexp::List(vec![
            Sexp::Atom("Rel".to_string()),
            Sexp::Atom(n.to_string()),
        ])
    };
    match sexp {
        Sexp::Atom(_) => Ok(sexp.clone()),
        Sexp::List(v) => {
            let head = v.first().and_then(|h| match h {
                Sexp::Atom(s) => Some(s.as_str()),
                _ => None,
            });
            match head {
                Some("Rel") if v.len() == 2 => {
                    let n = match &v[1] {
                        Sexp::Atom(s) => s
                            .parse::<u32>()
                            .map_err(|_| "mutual-fix: bad Rel".to_string())?,
                        _ => return Err("mutual-fix: bad Rel".to_string()),
                    };
                    if n == self_add || n == self_carry {
                        return Err(
                            "mutual-fix: bare recursive reference (member used as a value) \
                             unsupported"
                                .to_string(),
                        );
                    }
                    if (fd + 1..=fd + k).contains(&n) {
                        Ok(rel(n + 1))
                    } else {
                        Ok(rel(n))
                    }
                }
                Some("App") if v.len() >= 2 => {
                    // Self-call?  head is a fix-binder Rel and the call is saturated.
                    if let Sexp::List(hv) = &v[1] {
                        if hv.len() == 2 && matches!(&hv[0], Sexp::Atom(h) if h == "Rel") {
                            let n = match &hv[1] {
                                Sexp::Atom(s) => s.parse::<u32>().ok(),
                                _ => None,
                            };
                            if let Some(n) = n {
                                if n == self_add || n == self_carry {
                                    // Raw App is `(App f (a0 a1 …))` — args grouped.
                                    let args = match v.get(2) {
                                        Some(Sexp::List(a)) => a,
                                        _ => {
                                            return Err(
                                                "mutual-fix: malformed self-call application"
                                                    .to_string(),
                                            )
                                        }
                                    };
                                    if args.len() != k as usize {
                                        return Err(
                                            "mutual-fix: recursive call is not saturated at the \
                                             member arity"
                                                .to_string(),
                                        );
                                    }
                                    let mut new_args = args
                                        .iter()
                                        .map(|a| remap_mutual_body(a, fd, k))
                                        .collect::<Result<Vec<_>, _>>()?;
                                    let selector = if n == self_add {
                                        raw_bool_template("true")?
                                    } else {
                                        raw_bool_template("false")?
                                    };
                                    new_args.push(selector);
                                    return Ok(Sexp::List(vec![
                                        Sexp::Atom("App".to_string()),
                                        rel(self_add),
                                        Sexp::List(new_args),
                                    ]));
                                }
                            }
                        }
                    }
                    // Ordinary application: `(App f (args))` or flattened; remap parts.
                    let f = remap_mutual_body(&v[1], fd, k)?;
                    let rest = v[2..]
                        .iter()
                        .map(|a| match a {
                            Sexp::List(args) => {
                                let mapped = args
                                    .iter()
                                    .map(|x| remap_mutual_body(x, fd, k))
                                    .collect::<Result<Vec<_>, _>>()?;
                                Ok(Sexp::List(mapped))
                            }
                            other => remap_mutual_body(other, fd, k),
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let mut out = vec![Sexp::Atom("App".to_string()), f];
                    out.extend(rest);
                    Ok(Sexp::List(out))
                }
                Some("Lambda") | Some("Prod") if v.len() == 4 => {
                    let ty = remap_mutual_body(&v[2], fd, k)?;
                    let body = remap_mutual_body(&v[3], fd + 1, k)?;
                    Ok(Sexp::List(vec![v[0].clone(), v[1].clone(), ty, body]))
                }
                Some("LetIn") if v.len() == 5 => {
                    let ty = remap_mutual_body(&v[2], fd, k)?;
                    let val = remap_mutual_body(&v[3], fd, k)?;
                    let body = remap_mutual_body(&v[4], fd + 1, k)?;
                    Ok(Sexp::List(vec![v[0].clone(), v[1].clone(), ty, val, body]))
                }
                Some("Cast") if v.len() == 4 => {
                    let t = remap_mutual_body(&v[1], fd, k)?;
                    let ty = remap_mutual_body(&v[3], fd, k)?;
                    Ok(Sexp::List(vec![v[0].clone(), t, v[2].clone(), ty]))
                }
                Some("Case") if v.len() == 8 => remap_mutual_case(v, fd, k),
                // Leaves with no de Bruijn content.
                Some("Const") | Some("Ind") | Some("Construct") | Some("Sort") | Some("Var")
                | Some("Int") | Some("Float") | Some("String") => Ok(sexp.clone()),
                // Nested Fix/CoFix/Proj and anything unrecognized: fail closed.
                _ => Err("mutual-fix: unsupported node in a mutual body".to_string()),
            }
        }
    }
}

/// Remap a raw `Case` node (8 elements) for the combined fixpoint: params and
/// discriminant at `fd`, the return-predicate body under its own binders, and
/// each branch body under its constructor fields.
fn remap_mutual_case(v: &[Sexp], fd: u32, k: u32) -> Result<Sexp, String> {
    // v = [Case, ci_info, instance, params, return_pred, NoInvert, disc, branches]
    let params = match &v[3] {
        Sexp::List(ps) => Sexp::List(
            ps.iter()
                .map(|p| remap_mutual_body(p, fd, k))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        other => other.clone(),
    };
    // Return predicate: (((binder-annots) body) …) — remap body under the
    // index+scrutinee binders; the annot list carries names only (no Rels).
    let return_pred = match &v[4] {
        Sexp::List(rpv) if !rpv.is_empty() => {
            let pred = match &rpv[0] {
                Sexp::List(p) if p.len() == 2 => p,
                _ => return Err("mutual-fix: malformed return predicate".to_string()),
            };
            let nb = match &pred[0] {
                Sexp::List(bs) => bs.len() as u32,
                _ => return Err("mutual-fix: malformed return-predicate binders".to_string()),
            };
            let body = remap_mutual_body(&pred[1], fd + nb, k)?;
            let mut rpv2 = rpv.clone();
            rpv2[0] = Sexp::List(vec![pred[0].clone(), body]);
            Sexp::List(rpv2)
        }
        other => other.clone(),
    };
    let disc = remap_mutual_body(&v[6], fd, k)?;
    let branches = match &v[7] {
        Sexp::List(bs) => Sexp::List(
            bs.iter()
                .map(|b| match b {
                    Sexp::List(bv) if bv.len() == 2 => {
                        let m = match &bv[0] {
                            Sexp::List(f) => f.len() as u32,
                            _ => return Err("mutual-fix: malformed branch binders".to_string()),
                        };
                        let body = remap_mutual_body(&bv[1], fd + m, k)?;
                        Ok(Sexp::List(vec![bv[0].clone(), body]))
                    }
                    other => Ok(other.clone()),
                })
                .collect::<Result<Vec<_>, _>>()?,
        ),
        other => other.clone(),
    };
    Ok(Sexp::List(vec![
        v[0].clone(),
        v[1].clone(),
        v[2].clone(),
        params,
        return_pred,
        v[5].clone(),
        disc,
        branches,
    ]))
}

/// Encode a 2-body mutual fixpoint over one inductive with an equal signature
/// (see the module comment above). Fails closed on any unsupported sub-shape.
fn convert_serapi_mutual_fix(
    header: &Sexp,
    payload: &Sexp,
    ctx: &SerapiNormCtx,
    bctx: &[Option<Sexp>],
) -> Result<Sexp, String> {
    // header = ((r0 r1) which)
    let (rec_args, which) = match header {
        Sexp::List(v) if v.len() == 2 => (&v[0], &v[1]),
        _ => return Err("mutual-fix: malformed header".to_string()),
    };
    let which = match which {
        Sexp::Atom(s) => s
            .parse::<usize>()
            .map_err(|_| "mutual-fix: bad focus".to_string())?,
        _ => return Err("mutual-fix: bad focus".to_string()),
    };
    if which >= 2 {
        return Err("mutual-fix: focus out of range for a 2-body block".to_string());
    }
    let recs: Vec<u32> = match rec_args {
        Sexp::List(v) => v
            .iter()
            .map(|x| match x {
                Sexp::Atom(s) => s
                    .parse::<u32>()
                    .map_err(|_| "mutual-fix: bad recursion index".to_string()),
                _ => Err("mutual-fix: bad recursion index".to_string()),
            })
            .collect::<Result<_, _>>()?,
        _ => return Err("mutual-fix: malformed recursion header".to_string()),
    };
    if recs.len() != 2 {
        return Err("mutual-fix: only 2-body blocks are supported".to_string());
    }
    let r = recs[0];
    if recs[1] != r {
        return Err("mutual-fix: members recurse on different argument indices".to_string());
    }

    // payload = (annots (T0 T1) (B0 B1))
    let (types, bodies) = match payload {
        Sexp::List(v) if v.len() == 3 => match (&v[1], &v[2]) {
            (Sexp::List(t), Sexp::List(b)) if t.len() == 2 && b.len() == 2 => (t, b),
            _ => return Err("mutual-fix: expected exactly two types and two bodies".to_string()),
        },
        _ => return Err("mutual-fix: malformed payload".to_string()),
    };
    // Equal signatures ⇒ a single `bool` selector (not a dependent tuple) is
    // enough to combine the two members.
    if types[0] != types[1] {
        return Err(
            "mutual-fix: members have different types (selector encoding needs equal signatures)"
                .to_string(),
        );
    }
    let t0 = &types[0];

    // Argument telescope + result type of the shared signature.
    let (arg_prods, tret_raw) = peel_raw_prods(t0, r + 1)?;
    // Peel enough to cover the recursion arg; then continue peeling any further
    // arguments so `k` is the FULL arity (both bodies bind exactly `k`).
    let (arg_prods, tret_raw) = {
        let mut prods = arg_prods;
        let mut cur = tret_raw;
        while let Sexp::List(v) = &cur {
            if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") {
                prods.push((v[1].clone(), v[2].clone()));
                let next = v[3].clone();
                cur = next;
            } else {
                break;
            }
        }
        (prods, cur)
    };
    let k = arg_prods.len() as u32;
    if r >= k {
        return Err("mutual-fix: recursion index beyond the shared arity".to_string());
    }
    // The selector motive `fun _ : bool => Ret` must be non-dependent.
    if raw_mentions_rel(&tret_raw, k) {
        return Err("mutual-fix: dependent result type unsupported".to_string());
    }

    // Peel both bodies to their `match` nodes; keep body0's argument lambdas.
    let (arg_lams, case0) = peel_raw_lambdas(&bodies[0], k)?;
    let (_, case1) = peel_raw_lambdas(&bodies[1], k)?;
    let ci0 = match &case0 {
        Sexp::List(v) if v.len() == 8 && matches!(&v[0], Sexp::Atom(h) if h == "Case") => v,
        _ => {
            return Err(
                "mutual-fix: member 0 is not a match on the structural argument".to_string(),
            )
        }
    };
    let ci1 = match &case1 {
        Sexp::List(v) if v.len() == 8 && matches!(&v[0], Sexp::Atom(h) if h == "Case") => v,
        _ => {
            return Err(
                "mutual-fix: member 1 is not a match on the structural argument".to_string(),
            )
        }
    };
    // Both must match on the structural argument (raw `Rel(k - r)` at the
    // case site — 1-based, `k` lambdas in scope) and split it identically.
    let struct_rel = Sexp::List(vec![
        Sexp::Atom("Rel".to_string()),
        Sexp::Atom((k - r).to_string()),
    ]);
    if ci0[6] != struct_rel || ci1[6] != struct_rel {
        return Err("mutual-fix: a member does not match on the structural argument".to_string());
    }
    let (br0, br1) = match (&ci0[7], &ci1[7]) {
        (Sexp::List(a), Sexp::List(b)) if a.len() == b.len() && !a.is_empty() => (a, b),
        _ => return Err("mutual-fix: members split the inductive differently".to_string()),
    };

    let bool_ind = raw_bool_template("ind")?;
    let bool_rect = raw_bool_template("rect")?;

    // Combined branches: bool_rect (fun _ => Ret) <member0 body> <member1 body> sel.
    let mut combined_branches = Vec::with_capacity(br0.len());
    for (b0, b1) in br0.iter().zip(br1.iter()) {
        let (fields0, body0) = match b0 {
            Sexp::List(v) if v.len() == 2 => (&v[0], &v[1]),
            _ => return Err("mutual-fix: malformed member-0 branch".to_string()),
        };
        let (fields1, body1) = match b1 {
            Sexp::List(v) if v.len() == 2 => (&v[0], &v[1]),
            _ => return Err("mutual-fix: malformed member-1 branch".to_string()),
        };
        let m = match (fields0, fields1) {
            (Sexp::List(a), Sexp::List(b)) if a.len() == b.len() => a.len() as u32,
            _ => return Err("mutual-fix: branch field counts disagree".to_string()),
        };
        let body0p = remap_mutual_body(body0, m, k)?;
        let body1p = remap_mutual_body(body1, m, k)?;
        // Selector binder sits just below the branch fields: raw `Rel(m + 1)`.
        let sel = Sexp::List(vec![
            Sexp::Atom("Rel".to_string()),
            Sexp::Atom((m + 1).to_string()),
        ]);
        let motive = Sexp::List(vec![
            Sexp::Atom("Lambda".to_string()),
            raw_anon_binder()?,
            bool_ind.clone(),
            tret_raw.clone(),
        ]);
        let sel_app = Sexp::List(vec![
            Sexp::Atom("App".to_string()),
            bool_rect.clone(),
            Sexp::List(vec![motive, body0p, body1p, sel]),
        ]);
        combined_branches.push(Sexp::List(vec![fields0.clone(), sel_app]));
    }

    // CASE' — reuse member 0's `match` shell, remapped for the inserted
    // selector binder (params / motive / discriminant shift `+1`), with the
    // merged branches spliced in.
    let case_prime = {
        let remapped = remap_mutual_case(ci0, 0, k)?;
        let Sexp::List(mut cv) = remapped else {
            return Err("mutual-fix: internal case remap failure".to_string());
        };
        cv[7] = Sexp::List(combined_branches);
        Sexp::List(cv)
    };

    // Combined body: λ args… λ (sel : bool). CASE'
    let combined_body = {
        let mut body = Sexp::List(vec![
            Sexp::Atom("Lambda".to_string()),
            raw_anon_binder()?,
            bool_ind.clone(),
            case_prime,
        ]);
        for (annot, ty) in arg_lams.iter().rev() {
            body = Sexp::List(vec![
                Sexp::Atom("Lambda".to_string()),
                annot.clone(),
                ty.clone(),
                body,
            ]);
        }
        body
    };
    // Combined type: Π args…, bool → Ret.
    let combined_type = {
        let mut ty = Sexp::List(vec![
            Sexp::Atom("Prod".to_string()),
            raw_anon_binder()?,
            bool_ind.clone(),
            tret_raw.clone(),
        ]);
        for (annot, dom) in arg_prods.iter().rev() {
            ty = Sexp::List(vec![
                Sexp::Atom("Prod".to_string()),
                annot.clone(),
                dom.clone(),
                ty,
            ]);
        }
        ty
    };

    // Reassemble as a single structural Fix and reuse the standard encoder.
    let annot0 = match payload {
        Sexp::List(v) => match &v[0] {
            Sexp::List(a) if !a.is_empty() => a[0].clone(),
            other => other.clone(),
        },
        _ => Sexp::List(vec![]),
    };
    let combined_items = Sexp::List(vec![
        Sexp::Atom("Fix".to_string()),
        Sexp::List(vec![
            // header: ((r) 0) — recursion arg unchanged (selector is appended last).
            Sexp::List(vec![
                Sexp::List(vec![Sexp::Atom(r.to_string())]),
                Sexp::Atom("0".to_string()),
            ]),
            // payload: (annots (type) (body))
            Sexp::List(vec![
                Sexp::List(vec![annot0]),
                Sexp::List(vec![combined_type]),
                Sexp::List(vec![combined_body]),
            ]),
        ]),
    ]);
    let combined = match &combined_items {
        Sexp::List(items) => convert_serapi_fix(items, ctx, bctx)?,
        _ => unreachable!("combined_items is a list"),
    };

    // Project the focused member: λ args…. combined args… <selector>.
    let selector = if which == 0 {
        Sexp::List(vec![
            Sexp::Atom("Construct".to_string()),
            Sexp::Atom("Coq.Init.Datatypes.bool".to_string()),
            Sexp::Atom("0".to_string()),
            Sexp::Atom("0".to_string()),
        ])
    } else {
        Sexp::List(vec![
            Sexp::Atom("Construct".to_string()),
            Sexp::Atom("Coq.Init.Datatypes.bool".to_string()),
            Sexp::Atom("0".to_string()),
            Sexp::Atom("1".to_string()),
        ])
    };
    // Dialect argument types (for the projection lambdas).
    let mut proj = {
        // combined args in order: Rel(k-1) … Rel(0), then selector.
        let mut app = vec![Sexp::Atom("App".to_string()), combined];
        for i in (0..k).rev() {
            app.push(Sexp::List(vec![
                Sexp::Atom("Rel".to_string()),
                Sexp::Atom(i.to_string()),
            ]));
        }
        app.push(selector);
        Sexp::List(app)
    };
    // Wrap in λ args… using the dialect-normalized argument types.
    let mut proj_bctx = bctx.to_vec();
    let mut arg_dialect_tys = Vec::with_capacity(k as usize);
    for (_, dom) in &arg_prods {
        let dty = normalize_serapi_rec(dom, ctx, &proj_bctx);
        proj_bctx.push(Some(dty.clone()));
        arg_dialect_tys.push(dty);
    }
    for (i, (annot, _)) in arg_prods.iter().enumerate().rev() {
        let name = serapi_binder_name(annot).unwrap_or_else(|| format!("x{i}"));
        proj = Sexp::List(vec![
            Sexp::Atom("Lambda".to_string()),
            Sexp::Atom(name),
            arg_dialect_tys[i].clone(),
            proj,
        ]);
    }
    Ok(proj)
}

// ---------------------------------------------------------------------------
// MEASURE recursion (fuel translation) — the `edivn_rec` / `modn_rec` /
// `gcdn_rec` / `Nat.gcd` wall: a single `Fix` over `nat` that Coq's guard
// checker accepts by UNFOLDING ARITHMETIC — the match discriminant is a
// computed value (`if m - d is m'.+1 then …`), or the self-call recurses on a
// computed value (`gcd (b mod a'.+1) a'.+1`) — so the recursive argument is
// never a constructor field and no direct recursor encoding applies.
//
// Preprocess (fail closed / fall through otherwise): when EVERY self-call's
// struct-position argument carries a syntactic STRICT-DECREASE certificate
// against the struct binder `m` (see [`measure_cert_of`]), the recursion
// performs at most `m` steps, so the fixpoint is EXTENSIONALLY EQUAL to the
// fuel-indexed STRUCTURAL fixpoint
//
// ```text
//   F : Π fuel : nat. Π x_0 … x_{k-1}. T
//   F 0         x… = body[self-call ↦ dummy]
//   F (S fuel') x… = body[self-call v… ↦ F fuel' v…]
// ```
//
// projected back as `λ x…. F x_r x…` — the fuel is the struct argument
// ITSELF. The invariant `fuel ≥ m` is preserved (fuel drops by exactly 1
// while `m` drops strictly), so on closed input the fuel never runs out
// before the recursion bottoms; at `fuel = 0` the invariant forces `m = 0`,
// under which every self-call branch is certified unreachable (nothing is
// `< 0`), so the fuel-0 arm — the original body with a type-correct dummy in
// the (unevaluated) self-call positions — computes the original's value. `F`
// recurses structurally on `fuel`, which the existing general
// (post-abstracted) encoder lowers to the `nat` recursor.
//
// The decrease certificate is the SOUNDNESS-critical piece: the kernel
// arbitrates only well-typedness, never extensional equality (the `sub 1 1`
// fidelity lesson — a wrong-but-well-typed value is the failure mode to
// fear). The certificate admits exactly:
//   * the struct binder itself (`≤ m`);
//   * truncated subtraction / predecessor of a certified term (`≤` carries);
//   * modulo of a certified term (`≤` carries), or modulo BY a certified
//     manifest successor (`x mod y < y` for `y = S _`, and `y ≤ m` gives
//     `< m`);
//   * the `S`-branch binder of a `nat` match on a certified discriminant `D`
//     (`y + 1 = D ≤ m` ⇒ `y < m`), recording `S y = D` for the divisor rule;
//   * `let`-bound aliases of certified terms.
// The arithmetic facts (`a - b ≤ a`, `pred a ≤ a`, `a mod b ≤ a`,
// `a mod b < b` for `b = S _`) are pinned to the canonical stdlib/mathcomp
// constants by fully-qualified kername. The emission is marked SPECULATIVE
// (kernel rejection fails closed to a clean type-only axiom), and the
// extensional equality is pinned by real-dump compute tests with negative
// controls.
// ---------------------------------------------------------------------------

/// `Coq.Init.Datatypes.nat`, the only inductive the measure translation
/// handles (its constructor split is what the `S`-branch inversion and the
/// pinned arithmetic facts are about).
const MEASURE_NAT: &str = "Coq.Init.Datatypes.nat";

/// `f a b ≤ a` heads (truncated subtraction).
const MEASURE_SUB_HEADS: [&str; 3] = [
    "Coq.Init.Nat.sub",
    "mathcomp.ssreflect.ssrnat.subn",
    "mathcomp.ssreflect.ssrnat.subn_rec",
];

/// `f a ≤ a` heads (predecessor).
const MEASURE_PRED_HEADS: [&str; 2] = ["Coq.Init.Nat.pred", "Coq.Init.Peano.pred"];

/// `f a b ≤ a` heads that are also `< b` for a manifestly-positive `b`
/// (modulo: `a mod 0 = a` in both libraries, `a mod b < b` for `b > 0`).
const MEASURE_MOD_HEADS: [&str; 2] = ["Coq.Init.Nat.modulo", "mathcomp.ssreflect.div.modn"];

/// Certified bound of a term against the fix's struct binder `m`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MeasureCert {
    /// `t ≤ m`.
    Le,
    /// `t < m` (what a self-call's struct argument must certify).
    Lt,
}

/// Per-binder certificate facts for the decrease analysis.
#[derive(Debug, Clone, Copy, Default)]
struct MeasureFact {
    /// Bound of the binder itself.
    cert: Option<MeasureCert>,
    /// Bound of the binder's SUCCESSOR: in the `S y` branch of a `nat` match
    /// on a certified discriminant `D`, `S y = D`, so `S y` inherits `D`'s
    /// bound (the modulo divisor rule needs exactly this).
    succ: Option<MeasureCert>,
}

/// The numeric value of a raw `(Rel n)` node.
fn raw_rel_value(sexp: &Sexp) -> Option<u32> {
    let Sexp::List(v) = sexp else { return None };
    if v.len() == 2 && matches!(&v[0], Sexp::Atom(h) if h == "Rel") {
        if let Sexp::Atom(n) = &v[1] {
            return n.parse().ok();
        }
    }
    None
}

/// Does the `(Const …)` head `sexp` name one of `heads` under EITHER its user
/// spelling OR its canonical (definition-site) spelling?
///
/// A measure-arithmetic constant referenced through a module `Include`/alias
/// carries a KerPair `Dual`: the ubiquitous `Coq.Arith.PeanoNat.Nat.gcd` (a
/// fresh Fix expanded from `Include Coq.Init.Nat`) references `sub`/`modulo`
/// as `Coq.Arith.PeanoNat.Nat.modulo` (USER) with canonical
/// `Coq.Init.Nat.modulo`. The pinned arithmetic facts (`a mod (S b) < S b`,
/// `a - b ≤ a`, …) are about the KERNEL constant, which the canonical name
/// identifies EXACTLY — Coq's own Dual is the proof both spellings are the
/// same constant — so matching either spelling is sound. Matching only the
/// user spelling (the historical name check) silently missed every aliased
/// copy, so the whole `PeanoNat`/`OrdersEx` measure-recursion tower fell to a
/// clean type-only stand-in instead of fuel-translating.
fn raw_const_head_in(sexp: &Sexp, heads: &[&str]) -> bool {
    let Sexp::List(v) = sexp else { return false };
    if v.len() != 2 || !matches!(&v[0], Sexp::Atom(h) if h == "Const") {
        return false;
    }
    match &v[1] {
        Sexp::Atom(name) => heads.contains(&name.as_str()),
        payload => {
            serapi_qualified_name(payload).is_some_and(|n| heads.contains(&n.as_str()))
                || serapi_qualified_name_canonical(payload)
                    .is_some_and(|n| heads.contains(&n.as_str()))
        }
    }
}

/// Is this raw node the `nat` inductive (block 0)?
fn raw_is_nat_ind(sexp: &Sexp) -> bool {
    let Sexp::List(v) = sexp else { return false };
    if v.len() != 2 || !matches!(&v[0], Sexp::Atom(h) if h == "Ind") {
        return false;
    }
    let Sexp::List(pv) = &v[1] else { return false };
    // Payload ((<mutind> <block>) (Instance …)) — block must be 0.
    let Some(Sexp::List(iv)) = pv.first() else {
        return false;
    };
    matches!(iv.last(), Some(Sexp::Atom(i)) if i == "0")
        && serapi_qualified_name(&v[1]).as_deref() == Some(MEASURE_NAT)
}

/// Does this raw `Case` case-info name the `nat` inductive (block 0)?
fn raw_case_ci_is_nat(ci: &Sexp) -> bool {
    let Sexp::List(parts) = ci else { return false };
    let Some(Sexp::List(first)) = parts.first() else {
        return false;
    };
    if !matches!(first.first(), Some(Sexp::Atom(h)) if h == "ci_ind") {
        return false;
    }
    let Some(payload @ Sexp::List(iv)) = first.get(1) else {
        return false;
    };
    matches!(iv.last(), Some(Sexp::Atom(i)) if i == "0")
        && serapi_qualified_name(payload).as_deref() == Some(MEASURE_NAT)
}

/// `(App (Construct S) (w))` — nat's successor (raw 1-based constructor 2)
/// applied to exactly one argument; returns `w`.
fn raw_nat_succ_arg(sexp: &Sexp) -> Option<&Sexp> {
    let Sexp::List(v) = sexp else { return None };
    if v.len() != 3 || !matches!(&v[0], Sexp::Atom(h) if h == "App") {
        return None;
    }
    let Sexp::List(args) = &v[2] else { return None };
    if args.len() != 1 {
        return None;
    }
    let Sexp::List(cv) = &v[1] else { return None };
    if cv.len() != 2 || !matches!(&cv[0], Sexp::Atom(h) if h == "Construct") {
        return None;
    }
    // Payload (((<mutind> <block>) <ctor>) (Instance …)): block 0, ctor 2.
    let Sexp::List(pv) = &cv[1] else { return None };
    let Some(Sexp::List(outer)) = pv.first() else {
        return None;
    };
    if !matches!(outer.last(), Some(Sexp::Atom(j)) if j == "2") {
        return None;
    }
    let Some(Sexp::List(inner)) = outer.first() else {
        return None;
    };
    if !matches!(inner.last(), Some(Sexp::Atom(i)) if i == "0") {
        return None;
    }
    (serapi_qualified_name(&cv[1]).as_deref() == Some(MEASURE_NAT)).then_some(&args[0])
}

/// Syntactic bound certificate of `sexp` against the struct binder, under the
/// binder facts `env` (outermost binder first; the fix binder sits just below
/// `env[0]`, at raw `Rel(env.len() + 1)`).
fn measure_cert_of(sexp: &Sexp, env: &[MeasureFact]) -> Option<MeasureCert> {
    if let Some(n) = raw_rel_value(sexp) {
        let n = n as usize;
        return if n >= 1 && n <= env.len() {
            env[env.len() - n].cert
        } else {
            None
        };
    }
    // `S w`: the recorded constructor-inversion bound (`S w = D`), or `w < m`
    // giving `S w ≤ m`.
    if let Some(w) = raw_nat_succ_arg(sexp) {
        if let Some(n) = raw_rel_value(w) {
            let n = n as usize;
            if n >= 1 && n <= env.len() {
                let f = env[env.len() - n];
                if f.succ.is_some() {
                    return f.succ;
                }
            }
        }
        return match measure_cert_of(w, env) {
            Some(MeasureCert::Lt) => Some(MeasureCert::Le),
            _ => None,
        };
    }
    let Sexp::List(v) = sexp else { return None };
    if v.len() != 3 || !matches!(&v[0], Sexp::Atom(h) if h == "App") {
        return None;
    }
    let Sexp::List(args) = &v[2] else { return None };
    // Head match is canonical-aware (see [`raw_const_head_in`]): the same
    // kernel constant reached through a module `Include`/alias — the whole
    // `PeanoNat`/`OrdersEx` measure tower — carries a user spelling outside
    // the pinned-fact table but the canonical (definition-site) spelling in it.
    let head = &v[1];
    if raw_const_head_in(head, &MEASURE_SUB_HEADS) && args.len() == 2 {
        return measure_cert_of(&args[0], env);
    }
    if raw_const_head_in(head, &MEASURE_PRED_HEADS) && args.len() == 1 {
        return measure_cert_of(&args[0], env);
    }
    if raw_const_head_in(head, &MEASURE_MOD_HEADS) && args.len() == 2 {
        if measure_divisor_strict(&args[1], env) {
            return Some(MeasureCert::Lt);
        }
        return measure_cert_of(&args[0], env);
    }
    None
}

/// `x mod y < y ≤ m`: `y` is manifestly a successor `S w` whose bound is
/// certified — either the recorded inversion `S w = D ≤ m`, or `w < m`
/// (giving `S w ≤ m`).
fn measure_divisor_strict(y: &Sexp, env: &[MeasureFact]) -> bool {
    let Some(w) = raw_nat_succ_arg(y) else {
        return false;
    };
    if let Some(n) = raw_rel_value(w) {
        let n = n as usize;
        if n >= 1 && n <= env.len() {
            let f = env[env.len() - n];
            return f.succ.is_some() || f.cert == Some(MeasureCert::Lt);
        }
        return false;
    }
    measure_cert_of(w, env) == Some(MeasureCert::Lt)
}

/// Fail-closed containment for nodes the walkers do not model: acceptable
/// only when the subtree provably never references the fix binder.
fn measure_scan_self_free(sexp: &Sexp, self_rel: u32) -> Result<(), String> {
    match raw_scan_rel_at(sexp, self_rel) {
        Some(false) => Ok(()),
        _ => Err("measure: self-reference inside an unsupported node".to_string()),
    }
}

/// Walk the fix body verifying EVERY self-reference is a saturated call whose
/// struct-position argument certifies STRICT decrease, accumulating binder
/// facts along the way. `env` holds one fact per binder below the fix binder
/// (outermost first); the fix binder is raw `Rel(env.len() + 1)`.
fn measure_verify(
    sexp: &Sexp,
    env: &mut Vec<MeasureFact>,
    k: u32,
    r: u32,
    self_calls: &mut u32,
) -> Result<(), String> {
    let self_rel = env.len() as u32 + 1;
    if let Some(n) = raw_rel_value(sexp) {
        if n == self_rel {
            return Err("measure: bare self-reference".to_string());
        }
        return Ok(());
    }
    let Sexp::List(v) = sexp else { return Ok(()) };
    let head = match v.first() {
        Some(Sexp::Atom(h)) => h.as_str(),
        _ => return measure_scan_self_free(sexp, self_rel),
    };
    match head {
        "App" if v.len() == 3 => {
            let Sexp::List(args) = &v[2] else {
                return measure_scan_self_free(sexp, self_rel);
            };
            if raw_rel_value(&v[1]) == Some(self_rel) {
                if args.len() != k as usize {
                    return Err("measure: unsaturated self-call".to_string());
                }
                if measure_cert_of(&args[r as usize], env) != Some(MeasureCert::Lt) {
                    return Err(
                        "measure: self-call struct argument lacks a strict-decrease certificate"
                            .to_string(),
                    );
                }
                *self_calls += 1;
            } else {
                measure_verify(&v[1], env, k, r, self_calls)?;
            }
            for a in args {
                measure_verify(a, env, k, r, self_calls)?;
            }
            Ok(())
        }
        "Lambda" | "Prod" if v.len() == 4 => {
            measure_verify(&v[2], env, k, r, self_calls)?;
            env.push(MeasureFact::default());
            let res = measure_verify(&v[3], env, k, r, self_calls);
            env.pop();
            res
        }
        "LetIn" if v.len() == 5 => {
            measure_verify(&v[2], env, k, r, self_calls)?;
            measure_verify(&v[3], env, k, r, self_calls)?;
            let fact = MeasureFact {
                cert: measure_cert_of(&v[2], env),
                succ: None,
            };
            env.push(fact);
            let res = measure_verify(&v[4], env, k, r, self_calls);
            env.pop();
            res
        }
        "Cast" if v.len() == 4 => {
            measure_verify(&v[1], env, k, r, self_calls)?;
            measure_verify(&v[3], env, k, r, self_calls)
        }
        "Case" if v.len() == 8 => {
            if let Sexp::List(ps) = &v[3] {
                for p in ps {
                    measure_verify(p, env, k, r, self_calls)?;
                }
            }
            if let Sexp::List(rpv) = &v[4] {
                if let Some(Sexp::List(pred)) = rpv.first() {
                    if pred.len() == 2 {
                        let nb = match &pred[0] {
                            Sexp::List(bs) => bs.len(),
                            _ => 0,
                        };
                        for _ in 0..nb {
                            env.push(MeasureFact::default());
                        }
                        let res = measure_verify(&pred[1], env, k, r, self_calls);
                        for _ in 0..nb {
                            env.pop();
                        }
                        res?;
                    }
                }
            }
            measure_verify(&v[6], env, k, r, self_calls)?;
            let dcert = measure_cert_of(&v[6], env);
            let on_nat = raw_case_ci_is_nat(&v[1]);
            let Sexp::List(brs) = &v[7] else {
                return measure_scan_self_free(sexp, self_rel);
            };
            for (j, br) in brs.iter().enumerate() {
                let bv = match br {
                    Sexp::List(x) if x.len() == 2 => x,
                    _ => return Err("measure: malformed branch".to_string()),
                };
                let nf = match &bv[0] {
                    Sexp::List(fs) => fs.len(),
                    _ => return Err("measure: malformed branch binders".to_string()),
                };
                // `S`-branch inversion on a certified nat discriminant `D`:
                // the field `y` has `y + 1 = D ≤ m`, so `y < m` (and `S y`
                // inherits `D`'s bound).
                let fact = if on_nat && j == 1 && nf == 1 && dcert.is_some() {
                    MeasureFact {
                        cert: Some(MeasureCert::Lt),
                        succ: dcert,
                    }
                } else {
                    MeasureFact::default()
                };
                for _ in 0..nf {
                    env.push(fact);
                }
                let res = measure_verify(&bv[1], env, k, r, self_calls);
                for _ in 0..nf {
                    env.pop();
                }
                res?;
            }
            Ok(())
        }
        "Sort" | "Const" | "Ind" | "Construct" | "Var" | "Int" | "Float" | "String" => Ok(()),
        _ => measure_scan_self_free(sexp, self_rel),
    }
}

/// Locate a BASE (self-call-free) branch of the fix body's outermost match
/// whose body references nothing bound after the fix arguments, and
/// re-express it in the fuel fixpoint's argument frame
/// `[…, F, fuel, x_0..x_{k-1}]` — the type-correct filler for the fuel-0
/// arm's self-call positions (certified unreachable on closed input). Also
/// requires the outer match's return predicate to be exactly the
/// (non-dependent) result type, so the filler's type matches every self-call
/// instance.
fn find_fuel_dummy(tail: &Sexp, k: u32, tret: &Sexp) -> Option<Sexp> {
    let mut lets = 0u32;
    let mut cur = tail;
    loop {
        match cur {
            Sexp::List(v) if v.len() == 5 && matches!(&v[0], Sexp::Atom(h) if h == "LetIn") => {
                cur = &v[4];
                lets += 1;
            }
            Sexp::List(v) if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Cast") => {
                cur = &v[1];
            }
            _ => break,
        }
    }
    let cv = match cur {
        Sexp::List(v) if v.len() == 8 && matches!(&v[0], Sexp::Atom(h) if h == "Case") => v,
        _ => return None,
    };
    // Return predicate must be the result type, independent of the scrutinee
    // binder(s) and the peeled lets.
    let rpv = match &cv[4] {
        Sexp::List(x) if !x.is_empty() => x,
        _ => return None,
    };
    let pred = match &rpv[0] {
        Sexp::List(p) if p.len() == 2 => p,
        _ => return None,
    };
    let nb = match &pred[0] {
        Sexp::List(bs) => bs.len() as u32,
        _ => return None,
    };
    let window = nb + lets;
    if (1..=window).any(|t| raw_scan_rel_at(&pred[1], t) != Some(false)) {
        return None;
    }
    let mb = raw_remap_rels(&pred[1], 0, &|n, d| {
        if n > d + window {
            n - window
        } else {
            n
        }
    })
    .ok()?;
    // `tret` lives outside the fix binder; insert it for the comparison.
    let tret_l = raw_remap_rels(tret, 0, &|n, d| if n > d + k { n + 1 } else { n }).ok()?;
    if mb != tret_l {
        return None;
    }
    let brs = match &cv[7] {
        Sexp::List(b) => b,
        _ => return None,
    };
    for br in brs {
        let bv = match br {
            Sexp::List(x) if x.len() == 2 => x,
            _ => continue,
        };
        let nf = match &bv[0] {
            Sexp::List(fs) => fs.len() as u32,
            _ => continue,
        };
        let fe = nf + lets;
        // Self-call-free, and free of the fields/lets window.
        if raw_scan_rel_at(&bv[1], fe + k + 1) != Some(false) {
            continue;
        }
        if (1..=fe).any(|t| raw_scan_rel_at(&bv[1], t) != Some(false)) {
            continue;
        }
        let s0 = raw_remap_rels(&bv[1], 0, &|n, d| if n > d + fe { n - fe } else { n }).ok()?;
        // Argument frame → fuel frame: lift the enclosing context over the
        // inserted `fuel` binder (the fix binder slot is reference-free here).
        let s1 = raw_remap_rels(&s0, 0, &|n, d| if n > d + k { n + 1 } else { n }).ok()?;
        return Some(s1);
    }
    None
}

/// Self-call rewrite modes for the fuel translation's two match arms.
enum FuelSelfMode<'a> {
    /// Fuel-0 arm: replace the saturated self-call with the (lifted) dummy.
    Replace(&'a Sexp),
    /// Fuel-successor arm: thread the fuel predecessor (bound at the arm
    /// root) as a new first argument.
    Thread,
}

/// Rewrite every saturated self-call `(App (Rel self_base+depth) (args…))`
/// in a fuel-arm body per `mode`. Any other reachable self-reference fails
/// closed.
fn fuel_rewrite_self_calls(
    sexp: &Sexp,
    depth: u32,
    self_base: u32,
    mode: &FuelSelfMode<'_>,
) -> Result<Sexp, String> {
    let self_rel = self_base + depth;
    if let Sexp::List(v) = sexp {
        if v.len() == 3
            && matches!(&v[0], Sexp::Atom(h) if h == "App")
            && raw_rel_value(&v[1]) == Some(self_rel)
        {
            match mode {
                FuelSelfMode::Replace(dummy) => {
                    // The dummy lives at the arm root; lift it under the
                    // binders entered since (nested self-calls inside the
                    // replaced arguments vanish with the application — the
                    // whole position is certified unreachable).
                    return raw_remap_rels(dummy, 0, &|n, d| if n > d { n + depth } else { n });
                }
                FuelSelfMode::Thread => {
                    let Sexp::List(args) = &v[2] else {
                        return Err("measure: malformed self-call application".to_string());
                    };
                    let mut na = Vec::with_capacity(args.len() + 1);
                    na.push(raw_rel(1 + depth));
                    for a in args {
                        na.push(fuel_rewrite_self_calls(a, depth, self_base, mode)?);
                    }
                    return Ok(Sexp::List(vec![
                        Sexp::Atom("App".to_string()),
                        v[1].clone(),
                        Sexp::List(na),
                    ]));
                }
            }
        }
    }
    if raw_rel_value(sexp) == Some(self_rel) {
        return Err("measure: bare self-reference in a fuel arm".to_string());
    }
    let Sexp::List(v) = sexp else {
        return Ok(sexp.clone());
    };
    let head = match v.first() {
        Some(Sexp::Atom(h)) => h.as_str(),
        _ => return fuel_clone_self_free(sexp, self_rel),
    };
    match head {
        "App" if v.len() == 3 => {
            let f = fuel_rewrite_self_calls(&v[1], depth, self_base, mode)?;
            let Sexp::List(args) = &v[2] else {
                return Err("measure: malformed application".to_string());
            };
            let na = args
                .iter()
                .map(|a| fuel_rewrite_self_calls(a, depth, self_base, mode))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::List(vec![v[0].clone(), f, Sexp::List(na)]))
        }
        "Lambda" | "Prod" if v.len() == 4 => Ok(Sexp::List(vec![
            v[0].clone(),
            v[1].clone(),
            fuel_rewrite_self_calls(&v[2], depth, self_base, mode)?,
            fuel_rewrite_self_calls(&v[3], depth + 1, self_base, mode)?,
        ])),
        "LetIn" if v.len() == 5 => Ok(Sexp::List(vec![
            v[0].clone(),
            v[1].clone(),
            fuel_rewrite_self_calls(&v[2], depth, self_base, mode)?,
            fuel_rewrite_self_calls(&v[3], depth, self_base, mode)?,
            fuel_rewrite_self_calls(&v[4], depth + 1, self_base, mode)?,
        ])),
        "Cast" if v.len() == 4 => Ok(Sexp::List(vec![
            v[0].clone(),
            fuel_rewrite_self_calls(&v[1], depth, self_base, mode)?,
            v[2].clone(),
            fuel_rewrite_self_calls(&v[3], depth, self_base, mode)?,
        ])),
        "Case" if v.len() == 8 => {
            let params = match &v[3] {
                Sexp::List(ps) => Sexp::List(
                    ps.iter()
                        .map(|p| fuel_rewrite_self_calls(p, depth, self_base, mode))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                other => other.clone(),
            };
            let return_pred = match &v[4] {
                Sexp::List(rpv) if !rpv.is_empty() => {
                    let pred = match &rpv[0] {
                        Sexp::List(p) if p.len() == 2 => p,
                        _ => return Err("measure: malformed return predicate".to_string()),
                    };
                    let nb = match &pred[0] {
                        Sexp::List(bs) => bs.len() as u32,
                        _ => return Err("measure: malformed return-predicate binders".to_string()),
                    };
                    let body = fuel_rewrite_self_calls(&pred[1], depth + nb, self_base, mode)?;
                    let mut rpv2 = rpv.clone();
                    rpv2[0] = Sexp::List(vec![pred[0].clone(), body]);
                    Sexp::List(rpv2)
                }
                other => other.clone(),
            };
            let disc = fuel_rewrite_self_calls(&v[6], depth, self_base, mode)?;
            let branches = match &v[7] {
                Sexp::List(bs) => Sexp::List(
                    bs.iter()
                        .map(|b| match b {
                            Sexp::List(bv) if bv.len() == 2 => {
                                let m = match &bv[0] {
                                    Sexp::List(fs) => fs.len() as u32,
                                    _ => {
                                        return Err("measure: malformed branch binders".to_string())
                                    }
                                };
                                Ok(Sexp::List(vec![
                                    bv[0].clone(),
                                    fuel_rewrite_self_calls(&bv[1], depth + m, self_base, mode)?,
                                ]))
                            }
                            other => Ok(other.clone()),
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                other => other.clone(),
            };
            Ok(Sexp::List(vec![
                v[0].clone(),
                v[1].clone(),
                v[2].clone(),
                params,
                return_pred,
                v[5].clone(),
                disc,
                branches,
            ]))
        }
        "Sort" | "Const" | "Ind" | "Construct" | "Var" | "Int" | "Float" | "String" => {
            Ok(sexp.clone())
        }
        _ => fuel_clone_self_free(sexp, self_rel),
    }
}

/// Clone a node the rewriter does not model — sound only when it provably
/// never references the fix binder (the rewriter never remaps other Rels).
fn fuel_clone_self_free(sexp: &Sexp, self_rel: u32) -> Result<Sexp, String> {
    match raw_scan_rel_at(sexp, self_rel) {
        Some(false) => Ok(sexp.clone()),
        _ => Err("measure: self-reference inside an unsupported node".to_string()),
    }
}

/// Raw-template nodes for the synthesized fuel match:
/// `(nat_ind, case_info, instance, fuel_binder_annot)`.
fn fuel_nat_templates() -> Option<(Sexp, Sexp, Sexp, Sexp)> {
    let nat_ind = parse_sexp(
        "(Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) \
         (Id nat)) ()) 0) (Instance (() ()))))",
    )
    .ok()?;
    let ci = parse_sexp(
        "((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) \
         (Id nat)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1)) (ci_cstr_nargs (0 1)) \
         (ci_pp_info ((style MatchStyle))))",
    )
    .ok()?;
    let inst = parse_sexp("(Instance (() ()))").ok()?;
    let fuel_annot =
        parse_sexp("((binder_name (Name (Id fuel))) (binder_relevance Relevant))").ok()?;
    Some((nat_ind, ci, inst, fuel_annot))
}

/// Recognize + fuel-translate a MEASURE-recursive single `Fix` (see the
/// section comment above). Returns the transformed
/// `(header, payload, raw_arg_tys, r)` for re-dispatch through
/// [`convert_serapi_fix`], or `None` when the shape or the strict-decrease
/// certificate does not apply (the caller's original error stands).
fn try_fuel_measure_fix(header: &Sexp, payload: &Sexp) -> Option<(Sexp, Sexp, Vec<Sexp>, u32)> {
    // Single fixpoint focused on member 0.
    let (rec_args, which) = match header {
        Sexp::List(v) if v.len() == 2 => (&v[0], &v[1]),
        _ => return None,
    };
    let r = match rec_args {
        Sexp::List(v) if v.len() == 1 => match &v[0] {
            Sexp::Atom(s) => s.parse::<u32>().ok()?,
            _ => return None,
        },
        _ => return None,
    };
    if !matches!(which, Sexp::Atom(s) if s == "0") {
        return None;
    }
    let (annots, fix_ty, fix_body) = match payload {
        Sexp::List(v) if v.len() == 3 => match (&v[1], &v[2]) {
            (Sexp::List(t), Sexp::List(b)) if t.len() == 1 && b.len() == 1 => (&v[0], &t[0], &b[0]),
            _ => return None,
        },
        _ => return None,
    };
    let (arg_prods, tret) = peel_all_raw_prods(fix_ty);
    let k = arg_prods.len() as u32;
    if k == 0 || r >= k {
        return None;
    }
    // Non-dependent result type: the fuel motive reuses it verbatim, and the
    // dummy must be type-correct at every self-call instance.
    if raw_mentions_rel(&tret, k) {
        return None;
    }
    // The struct argument must be a bare `nat` — the measure IS the argument,
    // and the `S`-branch inversion + pinned arithmetic facts are nat-only.
    if !raw_is_nat_ind(&arg_prods[r as usize].1) {
        return None;
    }
    let (_lams, tail) = peel_raw_lambdas(fix_body, k).ok()?;
    // STRICT-DECREASE certificate over every self-call — the soundness-
    // critical gate (the kernel cannot arbitrate extensional equality).
    let mut env = vec![MeasureFact::default(); k as usize];
    env[r as usize].cert = Some(MeasureCert::Le);
    let mut self_calls = 0u32;
    measure_verify(&tail, &mut env, k, r, &mut self_calls).ok()?;
    if self_calls == 0 {
        return None; // not a recursion this pass should touch
    }
    let dummy = find_fuel_dummy(&tail, k, &tret)?;
    let (nat_ind, ci, inst, fuel_annot) = fuel_nat_templates()?;
    let lift1 = |n: u32, d: u32| if n > d { n + 1 } else { n };
    // Lift the body over the inserted `fuel` binder, then split off the
    // argument lambdas: `tail1` lives in `[…, F, fuel, x_0..x_{k-1}]`.
    let lifted_body = raw_remap_rels(fix_body, 0, &lift1).ok()?;
    let (lams1, tail1) = peel_raw_lambdas(&lifted_body, k).ok()?;
    // Fuel-0 arm: self-calls (certified unreachable on closed input) → dummy.
    let o_arm = fuel_rewrite_self_calls(&tail1, 0, k + 2, &FuelSelfMode::Replace(&dummy)).ok()?;
    // Fuel-successor arm: `fuel'` bound at the arm root; self-calls thread it.
    let tail2 = raw_remap_rels(&tail1, 0, &lift1).ok()?;
    let s_arm = fuel_rewrite_self_calls(&tail2, 0, k + 3, &FuelSelfMode::Thread).ok()?;
    // Motive: the result type under `[…, F, fuel, x_0..x_{k-1}, scrutinee]`
    // (only enclosing references exist — the result type is non-dependent).
    let motive_body = raw_remap_rels(&tret, 0, &|n, d| if n > d + k { n + 3 } else { n }).ok()?;
    let s_field_annot = raw_anon_binder().ok()?;
    let case = Sexp::List(vec![
        Sexp::Atom("Case".to_string()),
        ci,
        inst,
        Sexp::List(vec![]),
        Sexp::List(vec![
            Sexp::List(vec![Sexp::List(vec![fuel_annot.clone()]), motive_body]),
            Sexp::Atom("Relevant".to_string()),
        ]),
        Sexp::Atom("NoInvert".to_string()),
        raw_rel(k + 1),
        Sexp::List(vec![
            Sexp::List(vec![Sexp::List(vec![]), o_arm]),
            Sexp::List(vec![Sexp::List(vec![s_field_annot]), s_arm]),
        ]),
    ]);
    let mut new_body = case;
    for (annot, ty) in lams1.iter().rev() {
        new_body = Sexp::List(vec![
            Sexp::Atom("Lambda".to_string()),
            annot.clone(),
            ty.clone(),
            new_body,
        ]);
    }
    new_body = Sexp::List(vec![
        Sexp::Atom("Lambda".to_string()),
        fuel_annot.clone(),
        nat_ind.clone(),
        new_body,
    ]);
    let new_type = Sexp::List(vec![
        Sexp::Atom("Prod".to_string()),
        fuel_annot,
        nat_ind,
        raw_remap_rels(fix_ty, 0, &lift1).ok()?,
    ]);
    let new_header = Sexp::List(vec![
        Sexp::List(vec![Sexp::Atom("0".to_string())]),
        Sexp::Atom("0".to_string()),
    ]);
    let new_payload = Sexp::List(vec![
        annots.clone(),
        Sexp::List(vec![new_type]),
        Sexp::List(vec![new_body]),
    ]);
    let raw_arg_tys: Vec<Sexp> = arg_prods.iter().map(|(_, t)| t.clone()).collect();
    Some((new_header, new_payload, raw_arg_tys, r))
}

thread_local! {
    /// Re-entry guard for the fuel translation: the synthesized fuel fixpoint
    /// re-enters [`convert_serapi_fix`], and its own `S`-arm self-call shape
    /// would qualify for ANOTHER wrap if the inner dispatch ever fell through
    /// to the last-resort chain — one level is exactly right.
    static FUEL_WRAP_ACTIVE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Try the measure→fuel translation; when it applies, convert the synthesized
/// structural fixpoint and project back (`λ x…. F x_r x…` — the struct
/// argument is DUPLICATED into the new fuel slot). Marked speculative: the
/// kernel re-checks the value, so a mis-translation fails closed to a clean
/// type-only axiom; extensional equality is pinned by the compute tests.
fn dispatch_fuel_measure_fix(
    header: &Sexp,
    payload: &Sexp,
    ctx: &SerapiNormCtx,
    bctx: &[Option<Sexp>],
) -> Option<Result<Sexp, String>> {
    if FUEL_WRAP_ACTIVE.with(|c| c.get()) {
        return None;
    }
    let (nh, np, raw_arg_tys, r) = try_fuel_measure_fix(header, payload)?;
    SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
    FUEL_WRAP_ACTIVE.with(|c| c.set(true));
    let result = (|| {
        let new_items = vec![Sexp::Atom("Fix".to_string()), Sexp::List(vec![nh, np])];
        let combined = convert_serapi_fix(&new_items, ctx, bctx)?;
        let mut perm: Vec<u32> = Vec::with_capacity(raw_arg_tys.len() + 1);
        perm.push(r);
        perm.extend(0..raw_arg_tys.len() as u32);
        project_arg_permutation(combined, &raw_arg_tys, &perm, ctx, bctx)
    })();
    FUEL_WRAP_ACTIVE.with(|c| c.set(false));
    Some(result)
}

/// Structuralize a raw SerAPI single structural `Fix`
/// `(Fix ((<rec-arg-indices>) <which>) ((<annots>) (<types>) (<bodies>)))`
/// into the dialect `(StructFix ...)` recursor encoding.
///
/// Recognized pattern (everything else FAILS CLOSED):
/// - single body, `which = 0`, recursive argument index `r`;
/// - body = `λ x_0 … x_{k-1}. match x_r with …` with `k > r` (Casts are
///   dropped along the spine);
/// - the matched inductive is registered and heads the struct binder's type;
///   a Prop-only-eliminating inductive (`le`) takes the STRICT encoding only
///   (its recursor has no motive universe parameter — `(RecLevel Prop)`);
/// - every self-reference is a saturated application whose struct argument is
///   a DIRECT recursive field of the enclosing branch — rewritten to that
///   field's induction hypothesis. When ALL remaining arguments are exactly
///   the enclosing fix binders, the historical STRICT encoding is emitted
///   (motive `λ x'. T`); otherwise the GENERAL post-abstracted encoding
///   ([`convert_serapi_fix_general`]) handles self-calls whose post-struct
///   arguments vary (`revapp`-shaped) or which sit inside a nested Case's
///   lowering (`uint_beq`-shaped). PRE-struct arguments must be the enclosing
///   binders in both encodings.
fn convert_serapi_fix(
    items: &[Sexp],
    ctx: &SerapiNormCtx,
    bctx: &[Option<Sexp>],
) -> Result<Sexp, String> {
    // items[1] = ( ((r0 r1 ...) which) ((annots)(types)(bodies)) )
    let (header, payload) = match &items[1] {
        Sexp::List(v) if v.len() == 2 => (&v[0], &v[1]),
        _ => return Err("Fix: malformed fixpoint payload".to_string()),
    };
    // Inner-match recursion (match-commutation): a fixpoint recursing on an
    // argument whose match sits at INNER depth (`Pos.eqb`/`compare_cont`/
    // `Z.pos_sub`/`Pos.sub_mask`/`List.nth`/`PositiveMap.find` shape).
    // Commute + reorder so the struct argument's match is outermost,
    // re-dispatch (this handles the single AND mutual encoders), then project
    // back under the original argument order. The bail reason is kept for the
    // discriminant-mismatch report below.
    let commute_bail = match try_commute_reorder_fix(header, payload) {
        Ok((nh, np, perm, raw_arg_tys, relaxed)) => {
            // A RELAXED commute (relocated Rel-bearing shells, duplicated
            // non-matching branches, position-shifted argument types) is a
            // derived encoding: mark it speculative so a kernel rejection
            // fails closed to a clean type-only axiom, never a masked
            // failure. The historical Rel-free shapes stay unmarked.
            if relaxed {
                SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
            }
            let new_items = vec![Sexp::Atom("Fix".to_string()), Sexp::List(vec![nh, np])];
            let combined = convert_serapi_fix(&new_items, ctx, bctx)?;
            return project_arg_permutation(combined, &raw_arg_tys, &perm, ctx, bctx);
        }
        Err(reason) => reason,
    };
    let (rec_args, which) = match header {
        Sexp::List(v) if v.len() == 2 => (&v[0], &v[1]),
        _ => return Err("Fix: malformed recursive-structure header".to_string()),
    };
    // A 2-body mutual block over ONE inductive with an equal signature
    // (the `Pos.add`/`Pos.add_carry` shape) is encoded via a single tupled
    // fixpoint plus a `bool` selector — see `convert_serapi_mutual_fix`. It
    // fails closed on any unsupported sub-shape, and the whole term is
    // kernel-re-checked downstream, so a mis-encoding can never regress (it
    // simply falls back to today's type-only masked axiom).
    if matches!(rec_args, Sexp::List(rs) if rs.len() == 2) {
        return convert_serapi_mutual_fix(header, payload, ctx, bctx);
    }
    if !matches!(which, Sexp::Atom(s) if s == "0") {
        return Err("Fix: mutual fixpoint (non-zero focus) unsupported".to_string());
    }
    let r = match rec_args {
        Sexp::List(rs) if rs.len() == 1 => match &rs[0] {
            Sexp::Atom(s) => s
                .parse::<u32>()
                .map_err(|_| "Fix: bad recursive-argument index".to_string())?,
            _ => return Err("Fix: bad recursive-argument index".to_string()),
        },
        _ => return Err("Fix: mutual fixpoint unsupported".to_string()),
    };
    // payload = ((annots)(types)(bodies)), each singleton for a single fix.
    let (types, bodies) = match payload {
        Sexp::List(v) if v.len() == 3 => match (&v[1], &v[2]) {
            (Sexp::List(t), Sexp::List(b)) if t.len() == 1 && b.len() == 1 => (&t[0], &b[0]),
            _ => return Err("Fix: mutual fixpoint unsupported".to_string()),
        },
        _ => return Err("Fix: malformed body payload".to_string()),
    };
    // The fix binder itself is in scope inside the body; track its TYPE (the
    // fixpoint's declared function type) so nested lookups stay aligned.
    let fix_binder_ty = normalize_serapi_rec(types, ctx, bctx);
    let mut inner_bctx = bctx_push(bctx, Some(fix_binder_ty));
    // Peel the body's lambda spine (dropping casts) down to the Case node.
    let mut binder_tys: Vec<(String, Sexp)> = Vec::new();
    let mut cur = bodies;
    loop {
        // Drop casts along the spine.
        while let Sexp::List(v) = cur {
            if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Cast") {
                cur = &v[1];
            } else {
                break;
            }
        }
        match cur {
            Sexp::List(v) if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Lambda") => {
                let name = serapi_binder_name(&v[1]).unwrap_or_else(|| "_".to_string());
                let ty = normalize_serapi_rec(&v[2], ctx, &inner_bctx);
                inner_bctx.push(Some(ty.clone()));
                binder_tys.push((name, ty));
                cur = &v[3];
            }
            _ => break,
        }
    }
    let k = binder_tys.len();
    if k <= r as usize {
        return Err("Fix: body binds fewer arguments than the recursive index".to_string());
    }
    let case_items = match cur {
        Sexp::List(v) if v.len() == 8 && matches!(&v[0], Sexp::Atom(h) if h == "Case") => v,
        _ => {
            // MEASURE recursion behind a non-match tail (`gcdn_rec`'s
            // `let n' := n %% m in match n' …`): fuel-translate when the
            // strict-decrease certificate holds (fail closed otherwise).
            if let Some(res) = dispatch_fuel_measure_fix(header, payload, ctx, bctx) {
                return res;
            }
            return Err(
                "Fix: body is not a lambda spine ending in a match on the structural argument"
                    .to_string(),
            );
        }
    };
    let pieces = convert_serapi_case(case_items, ctx, &inner_bctx)?;
    // Structural recursion over an INDEXED family: the strict encoder now emits
    // the struct argument's index terms into the recursor spine (see
    // `convert_serapi_fix_strict`), so it is no longer rejected up front. The
    // general encoder still rejects an indexed motive shape, and a mis-encoded
    // indexed spine is marked speculative and fails closed at the kernel.
    // The match must be exactly on the structural argument. Surface WHY the
    // match-commutation preprocessor did not fire so the fail-class report
    // separates the commute sub-shapes.
    let struct_rel = (k as u32) - 1 - r;
    if pieces.discriminant != rel_sexp(struct_rel) {
        // MEASURE recursion — the match is on a COMPUTED value
        // (`edivn_rec`/`modn_rec`'s `if m - d is m'.+1 then …`):
        // fuel-translate when the strict-decrease certificate holds.
        if let Some(res) = dispatch_fuel_measure_fix(header, payload, ctx, bctx) {
            return res;
        }
        return Err(format!(
            "Fix: match discriminant is not the structural argument ({commute_bail})"
        ));
    }
    // The struct binder's type must head the matched inductive — after delta-
    // unfolding a relation-definition abbreviation (`MyList A := list A`), the
    // same resolution the match discriminant recovery uses.
    let struct_ty = &binder_tys[r as usize].1;
    let struct_ty_resolved = unfold_relation_def_head(struct_ty, ctx);
    let struct_ty_head = struct_ty_resolved.as_ref().unwrap_or(struct_ty);
    match dialect_ind_head(struct_ty_head) {
        Some((n, i)) if n == pieces.ind_name && i == pieces.ind_idx => {}
        _ => {
            return Err(
                "Fix: structural argument type does not match the matched inductive".to_string(),
            )
        }
    }
    let info = ctx
        .lookup(&pieces.ind_name, pieces.ind_idx)
        .ok_or("Fix: matched inductive not in import session")?;
    // Recursion over a Prop-ONLY-eliminating inductive (`le`/`between`: Prop
    // with multiple constructors) — the Coq auto-generated induction-scheme
    // shape (`le_ind`'s inner fix). Its recursor takes NO motive universe
    // parameter (the kernel's `build_recursor` prop_only arm), which only
    // the STRICT encoder emits (`(RecLevel Prop)` → empty universe
    // instance); the general and struct-to-front fallbacks assume a
    // level-parameterized recursor, so they are not attempted. The encoding
    // is newer and marked speculative inside the strict encoder, so a
    // mis-encoding fails closed at the kernel (clean type-only axiom).
    if pieces.elim == ElimShape::PropOnly {
        return convert_serapi_fix_strict(&pieces, &binder_tys, r, info)
            .map_err(|e| format!("{e} (Prop-only recursor: strict encoding only)"));
    }

    // STRICT path first (the historical encoding — motive `λ x'. T`, minors
    // whose induction hypotheses are the recursive result at the SAME
    // enclosing non-struct arguments); any failure falls through to the
    // GENERAL post-abstracted encoding, then to the struct-to-front rotation.
    match convert_serapi_fix_strict(&pieces, &binder_tys, r, info) {
        Ok(sf) => Ok(sf),
        Err(strict_reason) => {
            match convert_serapi_fix_general(&pieces, &binder_tys, r, info, ctx, &inner_bctx) {
                Ok(sf) => Ok(sf),
                Err(general_reason) => {
                    // LAST RESORT: a pre-struct argument that VARIES across
                    // self-calls (accumulator recursion) defeats both encoders,
                    // which fix every pre-struct binder as a recursor parameter.
                    // Rotate the struct argument to the front so those binders
                    // become POST-struct — which the general encoder abstracts
                    // and lets vary — then re-dispatch and project back. Marked
                    // speculative: the rotation composition is newer, so a
                    // kernel rejection fails closed to a clean type-only axiom.
                    if let Some((nh, np, perm, raw_arg_tys)) =
                        try_rotate_struct_to_front_fix(header, payload)
                    {
                        SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
                        let new_items =
                            vec![Sexp::Atom("Fix".to_string()), Sexp::List(vec![nh, np])];
                        let combined = convert_serapi_fix(&new_items, ctx, bctx)?;
                        return project_arg_permutation(combined, &raw_arg_tys, &perm, ctx, bctx);
                    }
                    // LAST RESORT: a two-level (`div2`-shaped) recursion —
                    // one branch's body is another match on that branch's
                    // field with the self-calls on the INNER fields, which
                    // no direct-IH rewrite can express. Split it into an
                    // equivalent 2-body mutual block (outer + inner match as
                    // separate members, each self-call on a direct field)
                    // and reuse the mutual selector encoding. Marked
                    // speculative: the split composition is newer, so a
                    // kernel rejection fails closed to a type-only axiom.
                    if let Some((mh, mp)) = try_split_nested_match_fix(header, payload) {
                        SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
                        if let Ok(split) = convert_serapi_mutual_fix(&mh, &mp, ctx, bctx) {
                            return Ok(split);
                        }
                    }
                    // LAST RESORT: MEASURE recursion whose match IS on the
                    // struct argument but whose self-call recurses on a
                    // COMPUTED value (`Nat.gcd`'s `gcd (b mod a'.+1) a'.+1` —
                    // "self-call struct argument is not a recursive field"):
                    // fuel-translate when the strict-decrease certificate
                    // holds.
                    if let Some(res) = dispatch_fuel_measure_fix(header, payload, ctx, bctx) {
                        return res;
                    }
                    Err(format!(
                        "{general_reason} (strict fix encoding: {strict_reason})"
                    ))
                }
            }
        }
    }
}

/// STRICT arm of [`convert_serapi_fix`]: rewrite self-calls to induction
/// hypotheses (all non-struct self-call arguments must be exactly the
/// enclosing fix binders), branch by branch, then remove the fix binder from
/// every component and assemble the `Pre`/`Post`-bearing `StructFix`.
fn convert_serapi_fix_strict(
    pieces: &SerapiCasePieces,
    binder_tys: &[(String, Sexp)],
    r: u32,
    info: &SerapiIndInfo,
) -> Result<Sexp, String> {
    let k = binder_tys.len();
    // Prop-only-eliminating recursor (`le`): its `<ind>.<idx>.rec` takes NO
    // motive universe parameter (the kernel's `build_recursor` drops the
    // motive level param when elimination is restricted to Prop), so no
    // derived motive level is needed — the `(RecLevel Prop)` atom lowers to
    // an EMPTY universe instance. A NEWER encoding: marked speculative, so a
    // mis-encoding fails closed at the kernel (clean type-only axiom).
    let prop_only = pieces.elim == ElimShape::PropOnly;
    if prop_only {
        SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
    }
    let rec_level_part = if prop_only {
        Sexp::List(vec![
            Sexp::Atom("RecLevel".to_string()),
            Sexp::Atom("Prop".to_string()),
        ])
    } else {
        let rec_level = pieces
            .rec_level
            .ok_or("Fix: recursor motive universe level underivable")?;
        Sexp::List(vec![
            Sexp::Atom("RecLevel".to_string()),
            Sexp::Atom(rec_level.to_string()),
        ])
    };
    // For an INDEXED family the struct argument's index terms flow through some
    // of the pre-struct binders (`le_ind`'s inner `fix F (m:nat) (l:le n m)
    // {struct l}`: the index `m` sits right before `l`; `Vector.append`'s
    // `fix F (A n p:_) (v:t A n) (w:_)`: the index `n` sits TWO binders before
    // `v`, with the second parameter `p` in between). A self-call's argument at
    // such a position is the recursive field's OWN index (Coq typing forces it),
    // redundant with the induction hypothesis, so it is accepted arbitrary and
    // dropped. Identify those positions precisely: a pre-struct binder `x_s`
    // (de Bruijn `Rel(k-1-s)` in the `[Γ, fix, x_0..x_{k-1}]` frame the indices
    // live in) is an index position iff it appears verbatim as one of the
    // recovered concrete index terms. This subsumes the historical trailing
    // `[r-n_idx, r)` heuristic (which mis-fires when a non-index parameter sits
    // between the index and the struct) while staying exact — the self-call
    // check below only relaxes at these positions AND only when the argument is
    // not already the enclosing binder, so no previously-accepted shape shifts.
    let n_idx = pieces.indices.len() as u32;
    if r < n_idx {
        return Err("Fix: fewer pre-struct binders than inductive indices".to_string());
    }
    let idx_positions: Vec<u32> = (0..r)
        .filter(|&s| {
            pieces
                .indices
                .iter()
                .any(|ix| dialect_rel_of(ix) == Some(k as u32 - 1 - s))
        })
        .collect();
    let mut branches = Vec::with_capacity(pieces.branches.len());
    for (j, branch) in pieces.branches.iter().enumerate() {
        let flags = &info.ctor_recursive[j];
        let rec_fields: Vec<u32> = flags
            .iter()
            .enumerate()
            .filter_map(|(i, &rf)| rf.then_some(i as u32))
            .collect();
        let cfg = FixSelfRewrite {
            k: k as u32,
            m: flags.len() as u32,
            q: rec_fields.len() as u32,
            r,
            idx_positions: idx_positions.clone(),
            rec_fields,
            recon: StructBinderRecon {
                ind_name: pieces.ind_name.clone(),
                ind_idx: pieces.ind_idx,
                ctor_idx: j as u32,
                params: pieces.params.clone(),
            },
        };
        let rewritten = rewrite_fix_self_calls(branch, 0, &cfg)?;
        branches.push(dialect_strip_fix_binder(&rewritten, k as u32)?);
    }
    let motive = dialect_strip_fix_binder(&pieces.motive, k as u32)?;
    let params: Vec<Sexp> = pieces
        .params
        .iter()
        .map(|p| dialect_strip_fix_binder(p, k as u32))
        .collect::<Result<_, _>>()?;
    // Index terms of the struct argument's inductive type, for an INDEXED family
    // (`le n m`: index `m`). `pieces.indices` live in the `[Γ, fix, x_0..x_{k-1}]`
    // frame — the same frame as the motive — so the identical fix-binder strip at
    // depth `k` relocates them to the recursor-application frame `[pre,struct,post]`
    // (a genuine self-reference in an index errors, failing closed). A non-empty
    // indexed spine is a NEWER encoding, so mark it speculative: a wrong index
    // term yields a mis-typed recursor the kernel rejects → clean type-only axiom.
    let indices: Vec<Sexp> = pieces
        .indices
        .iter()
        .map(|ix| dialect_strip_fix_binder(ix, k as u32))
        .collect::<Result<_, _>>()?;
    if !indices.is_empty() {
        SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
    }
    let stripped_binders: Vec<Sexp> = binder_tys
        .iter()
        .enumerate()
        .map(|(j, (_, ty))| dialect_strip_fix_binder(ty, j as u32))
        .collect::<Result<_, _>>()?;
    // Assemble the dialect StructFix.
    let tag = |t: &str| Sexp::Atom(t.to_string());
    let mut out = vec![
        tag("StructFix"),
        Sexp::List(vec![
            tag("Ind"),
            Sexp::Atom(pieces.ind_name.clone()),
            Sexp::Atom(pieces.ind_idx.to_string()),
        ]),
        rec_level_part,
    ];
    let mut params_part = vec![tag("Params")];
    params_part.extend(params);
    out.push(Sexp::List(params_part));
    let mut pre_part = vec![tag("Pre")];
    pre_part.extend(stripped_binders[..r as usize].iter().cloned());
    out.push(Sexp::List(pre_part));
    out.push(Sexp::List(vec![
        tag("StructTy"),
        stripped_binders[r as usize].clone(),
    ]));
    let mut post_part = vec![tag("Post")];
    post_part.extend(stripped_binders[r as usize + 1..].iter().cloned());
    out.push(Sexp::List(post_part));
    if !indices.is_empty() {
        let mut indices_part = vec![tag("Indices")];
        indices_part.extend(indices);
        out.push(Sexp::List(indices_part));
    }
    out.push(Sexp::List(vec![tag("Motive"), motive]));
    for b in branches {
        out.push(Sexp::List(vec![tag("Branch"), b]));
    }
    Ok(Sexp::List(out))
}

/// Constructor reconstruction data for STRUCT-BINDER references inside a
/// minor-premise branch (shared by the strict and general fix encoders).
///
/// A Coq `fix f … x_r … := match x_r with C_j fields => body_j end` branch
/// body may reference `x_r` itself (the ubiquitous `| _, _ => n` idiom in
/// `Nat.sub`, `seq.drop`, `List.nth_error`, …). Coq re-binds `x_r` at every
/// recursive call (the fix unfolds by NAME), so inside branch `j` the
/// reference always denotes the CURRENT scrutinee. The recursor encoding has
/// no such re-binding: the minors are fixed once at the outer application and
/// reused through every induction hypothesis, so a minor that keeps pointing
/// at the enclosing binder captures the ORIGINAL argument — depth-correct
/// only for the first level of recursion. Measured consequence (2026-07-12,
/// the `ssrnat` reduction-parity cluster): the imported `Coq.Init.Nat.sub`
/// computed `sub 1 1 ↝ 1` (the O-branch returned the STALE captured `n`)
/// and `sub (S x) (S x)` / `sub x x` reduced to recursor applications with
/// DIFFERENT minors, so conversions Coq closes by one fix/iota step
/// (`leq (S n) (S n) ≡ leq n n`) were rejected.
///
/// The faithful translation — the standard match-compilation substitution —
/// replaces every `x_r` reference inside branch `j` with the branch's OWN
/// reconstructed constructor application `C_j params… fields…`: in branch
/// `j` the scrutinee is definitionally that constructor application (the
/// kernel's iota only fires after WHNFing the major premise to exactly this
/// shape), the reconstruction has the same type `I params…`, and the minors
/// become closed under recursion, restoring Coq's reduction behavior at
/// every depth.
struct StructBinderRecon {
    ind_name: String,
    ind_idx: u32,
    /// 0-based constructor index of this branch (dialect `Construct`
    /// numbering — SerAPI's 1-based index is already shifted by the
    /// normalizer).
    ctor_idx: u32,
    /// Case parameter arguments in the base frame `[Γ, fix, x_0..x_{k-1}]`
    /// (the same frame the motive lives in).
    params: Vec<Sexp>,
}

impl StructBinderRecon {
    /// Assemble `C_j params… fields…` at a reference site: `params_lift` is
    /// the number of binders between the base frame and the site, and
    /// `field_rels[i]` is the de Bruijn index of constructor field `i` (in
    /// constructor order) at the site. Errors (fail closed) are propagated by
    /// the caller into the encoder's ordinary reject path.
    fn assemble(&self, params_lift: u32, field_rels: &[u32]) -> Result<Sexp, String> {
        let ctor = Sexp::List(vec![
            Sexp::Atom("Construct".to_string()),
            Sexp::Atom(self.ind_name.clone()),
            Sexp::Atom(self.ind_idx.to_string()),
            Sexp::Atom(self.ctor_idx.to_string()),
        ]);
        if self.params.is_empty() && field_rels.is_empty() {
            return Ok(ctor);
        }
        let mut app = vec![Sexp::Atom("App".to_string()), ctor];
        for prm in &self.params {
            app.push(dialect_lift(prm, params_lift, 0)?);
        }
        for &fr in field_rels {
            app.push(rel_sexp(fr));
        }
        Ok(Sexp::List(app))
    }
}

/// `(Rel n)` LIST-form check for struct-binder interception. Deliberately
/// narrower than the encoders' arg-position `is_rel` (which also accepts a
/// bare numeric atom): a substitution must never fire on an incidental
/// numeric atom (e.g. a `RecLevel`), only on a genuine dialect Rel node.
fn is_rel_node(s: &Sexp, n: u32) -> bool {
    match s {
        Sexp::List(v) => {
            v.len() == 2
                && matches!(&v[0], Sexp::Atom(h) if h == "Rel")
                && matches!(&v[1], Sexp::Atom(a) if a.parse::<u32>() == Ok(n))
        }
        _ => false,
    }
}

/// Configuration for rewriting fix self-calls inside ONE minor-premise
/// branch: `k` enclosing fix-argument binders, `m` constructor fields, `q`
/// induction hypotheses, structural argument position `r`, and the branch's
/// direct recursive field indices (in field order).
struct FixSelfRewrite {
    k: u32,
    m: u32,
    q: u32,
    r: u32,
    /// Pre-struct argument positions that carry an inductive INDEX of the
    /// struct argument's family (identified precisely: a pre-struct binder
    /// whose de Bruijn `Rel` appears verbatim among the recovered concrete
    /// index terms). For an INDEXED family a self-call's argument there is the
    /// recursive field's OWN index (Coq typing forces it; `le_ind`'s `F m0 l0`
    /// passes the field `l0`'s index `m0`; `Vector.append`'s `F A n' p v' w`
    /// passes the field `v'`'s index `n'`), redundant with the kernel
    /// recursor's induction hypothesis, so it is accepted ARBITRARY and dropped
    /// — but ONLY when it is not already the enclosing binder, so a non-indexed
    /// inductive (empty set) and every historically-accepted enclosing-binder
    /// argument behave exactly as before.
    idx_positions: Vec<u32>,
    rec_fields: Vec<u32>,
    /// Constructor reconstruction replacing struct-binder references inside
    /// this branch (see [`StructBinderRecon`]).
    recon: StructBinderRecon,
}

/// Rewrite `f x_0 … x_{k-1}` self-calls (with the struct position holding a
/// recursive FIELD of the branch) into that field's induction-hypothesis
/// binder. From a site at traversal depth `d` (relative to the branch root,
/// which lives in the Case context `Γ, fix, x_0..x_{k-1}`): the fix self is
/// `Rel (k+d)`, field `i` is `Rel (d-1-i)`, outer arg `x_s` is
/// `Rel (k-1-s+d)`, and IH `j'` is `Rel (d-m-1-j')`. Any self-reference that
/// is not such an exact structural call is a hard error.
fn rewrite_fix_self_calls(sexp: &Sexp, depth: u32, cfg: &FixSelfRewrite) -> Result<Sexp, String> {
    let self_rel = cfg.k + depth;
    let is_rel = |s: &Sexp, n: u32| -> bool {
        match s {
            Sexp::Atom(a) => a.parse::<u32>() == Ok(n),
            Sexp::List(v) => {
                v.len() == 2
                    && matches!(&v[0], Sexp::Atom(h) if h == "Rel")
                    && matches!(&v[1], Sexp::Atom(a) if a.parse::<u32>() == Ok(n))
            }
        }
    };
    // Intercept saturated self-call applications.
    if let Sexp::List(v) = sexp {
        if v.len() >= 2 && matches!(&v[0], Sexp::Atom(h) if h == "App") && is_rel(&v[1], self_rel) {
            let args = &v[2..];
            if (args.len() as u32) < cfg.k {
                return Err("Fix: partially applied recursive self-call".to_string());
            }
            if depth < cfg.m + cfg.q {
                return Err("Fix: self-call outside the branch body".to_string());
            }
            // Struct argument must be a direct recursive field.
            let jp = cfg
                .rec_fields
                .iter()
                .position(|&i| depth > i && is_rel(&args[cfg.r as usize], depth - 1 - i))
                .ok_or("Fix: self-call struct argument is not a recursive field")?;
            // All other (first k) arguments must be exactly the fix binders
            // — EXCEPT at an inductive INDEX position (`cfg.idx_positions`),
            // where the argument is the recursive field's OWN index (determined
            // by the field's type), redundant with the induction hypothesis,
            // and dropped with the rest of the first-k arguments below. The
            // enclosing-binder check runs FIRST, so an argument that already IS
            // the enclosing binder is accepted exactly as before (an index that
            // happens to be constant across the recursion never triggers the
            // relaxation); the index relaxation only forgives a NON-enclosing
            // argument at a genuine index position.
            for (s, a) in args.iter().enumerate().take(cfg.k as usize) {
                let s = s as u32;
                if s == cfg.r || is_rel(a, cfg.k - 1 - s + depth) {
                    continue;
                }
                if cfg.idx_positions.contains(&s) {
                    continue;
                }
                return Err("Fix: self-call argument is not the enclosing fix binder".to_string());
            }
            let ih = rel_sexp(depth - cfg.m - 1 - jp as u32);
            let extras: Vec<Sexp> = args[cfg.k as usize..]
                .iter()
                .map(|a| rewrite_fix_self_calls(a, depth, cfg))
                .collect::<Result<_, _>>()?;
            return Ok(if extras.is_empty() {
                ih
            } else {
                let mut app = vec![Sexp::Atom("App".to_string()), ih];
                app.extend(extras);
                Sexp::List(app)
            });
        }
    }
    // A bare self-reference anywhere else is unrewritable.
    if is_rel(sexp, self_rel) {
        return Err("Fix: self-reference outside a recognized structural self-call".to_string());
    }
    // STRUCT-BINDER reference `x_r` (branch frame `[Γ, fix, x_0..x_{k-1}]`,
    // so `x_r = Rel(k-1-r+depth)`): substitute the branch's reconstructed
    // constructor application `C_j params… fields…` (see
    // [`StructBinderRecon`] — keeping the enclosing binder captured the
    // ORIGINAL argument, wrong at recursion depth ≥ 1). Field `i` is
    // `Rel(depth-1-i)`, valid only once all `m` fields are bound — a struct
    // reference inside a field TYPE has no reconstruction and fails closed.
    if is_rel_node(sexp, cfg.k - 1 - cfg.r + depth) {
        if depth < cfg.m {
            return Err(
                "Fix: struct-binder reference before the constructor fields are bound".to_string(),
            );
        }
        SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
        let field_rels: Vec<u32> = (0..cfg.m).map(|i| depth - 1 - i).collect();
        return cfg.recon.assemble(depth, &field_rels);
    }
    // Otherwise: binder-aware structural recursion. Reuse the generic
    // traversal for Rel bookkeeping; it never rewrites Rels itself here, but
    // we must intercept Apps at every depth, so recurse manually over the
    // same shapes the generic traversal understands.
    match sexp {
        Sexp::Atom(_) => Ok(sexp.clone()),
        Sexp::List(items) => {
            let head = match items.first() {
                Some(Sexp::Atom(h)) => h.as_str(),
                _ => return Err("Fix: headless list in branch body".to_string()),
            };
            match head {
                "Rel" | "Sort" | "Const" | "Ind" | "Construct" | "Int" | "Float" | "Var"
                | "CoqUnsupported" => Ok(sexp.clone()),
                "Prod" | "Lambda" if items.len() == 4 => Ok(Sexp::List(vec![
                    items[0].clone(),
                    items[1].clone(),
                    rewrite_fix_self_calls(&items[2], depth, cfg)?,
                    rewrite_fix_self_calls(&items[3], depth + 1, cfg)?,
                ])),
                "LetIn" if items.len() == 5 => Ok(Sexp::List(vec![
                    items[0].clone(),
                    items[1].clone(),
                    rewrite_fix_self_calls(&items[2], depth, cfg)?,
                    rewrite_fix_self_calls(&items[3], depth, cfg)?,
                    rewrite_fix_self_calls(&items[4], depth + 1, cfg)?,
                ])),
                "App" => {
                    let mut out = vec![items[0].clone()];
                    for a in &items[1..] {
                        out.push(rewrite_fix_self_calls(a, depth, cfg)?);
                    }
                    Ok(Sexp::List(out))
                }
                "Case" => {
                    let mut out = vec![items[0].clone(), items[1].clone()];
                    for part in &items[2..] {
                        let Sexp::List(pv) = part else {
                            return Err("Fix: malformed Case part in branch body".to_string());
                        };
                        let mut np = vec![pv[0].clone()];
                        for p in &pv[1..] {
                            np.push(rewrite_fix_self_calls(p, depth, cfg)?);
                        }
                        out.push(Sexp::List(np));
                    }
                    Ok(Sexp::List(out))
                }
                // Nested StructFix/Fix under a self-referencing scope is rare
                // and delicate; only accept it when the self does NOT occur
                // inside (checked by the strip pass) — traverse conservatively
                // by refusing (fail closed) if a self-call would need
                // rewriting at shifted depths.
                "StructFix" | "Fix" | "CoFix" => {
                    if dialect_strip_fix_binder(sexp, self_rel).is_ok() {
                        Ok(sexp.clone())
                    } else {
                        Err("Fix: self-reference inside a nested fixpoint unsupported".to_string())
                    }
                }
                other => Err(format!("Fix: unsupported head `{other}` in branch body")),
            }
        }
    }
}

/// GENERAL (post-abstracted) structuralization of a single structural `Fix`
/// — the fallback when the strict encoding's self-call shape check fails.
///
/// The strict encoding freezes every non-struct argument at the enclosing
/// binders, so a self-call `f x_0 … field … a'_{r+1} …` whose POST-struct
/// arguments differ from the enclosing binders (e.g. `revapp d (D0 d')`), or
/// which sits inside a nested Case's `StructFix` lowering (e.g. `uint_beq`'s
/// match on the second argument), cannot be expressed. The general encoding
/// abstracts the post-struct binders INTO the motive instead:
///
/// ```text
/// fix f (x_0:A_0) … (x_{k-1}:A_{k-1}) {struct r} : T :=
///     match x_r with C_j fields => body_j end
/// ⇓
/// λ x_0 … x_{k-1}.
///   (λ s:A_r. @I.rec.{ℓ} params (λ x'. Π A'_{r+1} … A'_{k-1}. T')
///       minor_1 … minor_n s)  x_r  x_{r+1} … x_{k-1}
/// ```
///
/// with `minor_j = λ fields ihs post'. body_j''` where each induction
/// hypothesis has the post-abstracted type `Π post'. T'[x':=field]` and
/// `body_j''` is `body_j` with (i) references to the enclosing post binders
/// REBOUND to the minor's own `post'` binders and (ii) every self-call
/// `f x_0 … x_{r-1} field a'_{r+1} … extras` rewritten to
/// `ih a'_{r+1} … extras` (post-struct arguments and extras arbitrary,
/// recursively transformed; PRE-struct arguments must still be exactly the
/// enclosing binders — they are recursor parameters fixed across the
/// recursion). The `(App (StructFix …) x_r x_{r+1} …)` wrapper is the same
/// degenerate one-binder beta-redex encoding [`assemble_level_param_case`]
/// uses, so no new dialect node or lowering is needed; the kernel re-checks
/// the exact recursor spine either way. Anything outside the recognized
/// shape (self-call whose struct argument is not a direct recursive field,
/// post-binder types depending on the struct argument, bare self-references)
/// remains a hard fail-closed error.
fn convert_serapi_fix_general(
    pieces: &SerapiCasePieces,
    binder_tys: &[(String, Sexp)],
    r: u32,
    info: &SerapiIndInfo,
    ctx: &SerapiNormCtx,
    inner_bctx: &[Option<Sexp>],
) -> Result<Sexp, String> {
    let k = binder_tys.len() as u32;
    let p = k - 1 - r; // post-struct binders
    let tag = |t: &str| Sexp::Atom(t.to_string());

    // Decompose the Case motive `λ s : self_ty. motive_body`.
    let (scrut_name, self_ty) = match &pieces.motive {
        Sexp::List(v)
            if v.len() == 4
                && matches!(&v[0], Sexp::Atom(h) if h == "Lambda")
                && pieces.index_binder_tys.is_empty() =>
        {
            let name = match &v[1] {
                Sexp::Atom(s) => s.clone(),
                _ => "s".to_string(),
            };
            (name, v[2].clone())
        }
        _ => return Err("Fix: unrecognized motive shape for the general encoding".to_string()),
    };

    // T' — the return type re-expressed under `[…, fix, x_0..x_{k-1}, x',
    // post'…]`: scrutinee AND struct-binder references merge into `x'`,
    // enclosing post references rebind to the new `post'` binders, everything
    // outer shifts across the removed scrutinee binder.
    let t_hat = dialect_map_rels(&pieces.motive_body, 0, &mut |n, c| {
        if n < c {
            return Ok(rel_sexp(n));
        }
        let d = n - c;
        Ok(rel_sexp(if d == 0 {
            c + (k - 1 - r) // scrutinee → x'
        } else if d <= k - r {
            n - 1 // enclosing posts → post' binders; x_r → x'
        } else {
            n + (k - r - 1) // pres / fix / outer
        }))
    })?;
    // Π-abstract the post binder types over `x'` (each `A_j` lifted from its
    // binding site into the motive telescope; post/struct references keep
    // their offsets — they now denote the new binders).
    let mut chain = t_hat;
    for j in (r + 1..k).rev() {
        let a_hat = dialect_lift(&binder_tys[j as usize].1, k - r, j - r)?;
        chain = Sexp::List(vec![
            tag("Prod"),
            Sexp::Atom(binder_tys[j as usize].0.clone()),
            a_hat,
            chain,
        ]);
    }
    // Motive universe level of the POST-ABSTRACTED motive (a Π-chain now, so
    // it differs from the plain Case's `rec_level`).
    let rec_level = {
        let mut mb_bctx = inner_bctx.to_vec();
        mb_bctx.push(Some(self_ty.clone()));
        motive_result_level(&chain, ctx, &mb_bctx)
            .ok_or("Fix: recursor motive universe level underivable (post-abstracted)")?
    };
    let new_motive = Sexp::List(vec![
        tag("Lambda"),
        Sexp::Atom(scrut_name),
        self_ty,
        chain.clone(),
    ]);

    // Minor premises.
    let mut branches = Vec::with_capacity(pieces.branch_bodies.len());
    for (j, natural_body) in pieces.branch_bodies.iter().enumerate() {
        let fields = &pieces.branch_fields[j];
        let flags = &info.ctor_recursive[j];
        let m = fields.len() as u32;
        if flags.len() as u32 != m {
            return Err("Fix: registered field count disagrees with constructor spine".to_string());
        }
        let rec_fields: Vec<u32> = flags
            .iter()
            .enumerate()
            .filter_map(|(i, &rf)| rf.then_some(i as u32))
            .collect();
        let q = rec_fields.len() as u32;
        let cfg = FixBranchCfg {
            k,
            r,
            m,
            q,
            p,
            rec_fields,
            recon: StructBinderRecon {
                ind_name: pieces.ind_name.clone(),
                ind_idx: pieces.ind_idx,
                ctor_idx: j as u32,
                params: pieces.params.clone(),
            },
        };
        let mut acc = fix_branch_transform(natural_body, 0, &cfg)?;
        // Post' binders, innermost-last.
        for jj in (r + 1..k).rev() {
            let ty = post_ty_in_branch(&binder_tys[jj as usize].1, jj, &cfg)?;
            acc = Sexp::List(vec![
                tag("Lambda"),
                Sexp::Atom(binder_tys[jj as usize].0.clone()),
                ty,
                acc,
            ]);
        }
        // Induction hypotheses: `ih_{jp} : Π post'. T'[x' := field_i]`.
        for (jp, &i) in cfg.rec_fields.iter().enumerate().rev() {
            let lifted = dialect_lift(&chain, m + jp as u32, 1)?;
            let ih_ty = dialect_subst_binder0(&lifted, &rel_sexp(m - 1 - i + jp as u32))?;
            acc = Sexp::List(vec![
                tag("Lambda"),
                Sexp::Atom(format!("ih{jp}")),
                ih_ty,
                acc,
            ]);
        }
        // Field binders, innermost-last.
        for (fname, fty) in fields.iter().rev() {
            acc = Sexp::List(vec![
                tag("Lambda"),
                Sexp::Atom(fname.clone()),
                fty.clone(),
                acc,
            ]);
        }
        branches.push(dialect_strip_fix_binder(&acc, k)?);
    }

    // Assemble the degenerate one-binder StructFix wrapper (same contract as
    // `assemble_level_param_case`: StructTy in the outer context, Params /
    // Motive / Branch lifted over the wrapper binder) and apply it to the
    // struct binder and the post binders inside the explicit lambda chain.
    // Struct binder type in the wrapper's OUTER context `Γ, x_0..x_{k-1}`:
    // strip the fix binder at its own depth, then lift across the binders
    // bound after it.
    let struct_ty_full = dialect_lift(
        &dialect_strip_fix_binder(&binder_tys[r as usize].1, r)?,
        k - r,
        0,
    )?;
    let mut sf = vec![
        tag("StructFix"),
        Sexp::List(vec![
            tag("Ind"),
            Sexp::Atom(pieces.ind_name.clone()),
            Sexp::Atom(pieces.ind_idx.to_string()),
        ]),
        Sexp::List(vec![tag("RecLevel"), Sexp::Atom(rec_level.to_string())]),
    ];
    let mut params_part = vec![tag("Params")];
    for prm in &pieces.params {
        params_part.push(dialect_lift(&dialect_strip_fix_binder(prm, k)?, 1, 0)?);
    }
    sf.push(Sexp::List(params_part));
    sf.push(Sexp::List(vec![tag("StructTy"), struct_ty_full]));
    sf.push(Sexp::List(vec![
        tag("Motive"),
        dialect_lift(&dialect_strip_fix_binder(&new_motive, k)?, 1, 0)?,
    ]));
    for b in &branches {
        sf.push(Sexp::List(vec![tag("Branch"), dialect_lift(b, 1, 0)?]));
    }
    let mut app = vec![tag("App"), Sexp::List(sf), rel_sexp(k - 1 - r)];
    for jj in r + 1..k {
        app.push(rel_sexp(k - 1 - jj));
    }
    let mut out = Sexp::List(app);
    // Wrap in the fix's explicit argument lambdas (fix binder stripped from
    // each binder type at its own depth).
    for (jj, (name, ty)) in binder_tys.iter().enumerate().rev() {
        out = Sexp::List(vec![
            tag("Lambda"),
            Sexp::Atom(name.clone()),
            dialect_strip_fix_binder(ty, jj as u32)?,
            out,
        ]);
    }
    Ok(out)
}

/// Configuration for [`fix_branch_transform`]: `k` enclosing fix binders,
/// struct position `r`, `m` constructor fields of THIS branch, `q` induction
/// hypotheses, `p = k - 1 - r` post-struct binders, and the branch's direct
/// recursive field indices (in field order).
struct FixBranchCfg {
    k: u32,
    r: u32,
    m: u32,
    q: u32,
    p: u32,
    rec_fields: Vec<u32>,
    /// Constructor reconstruction replacing struct-binder references inside
    /// this branch (see [`StructBinderRecon`]).
    recon: StructBinderRecon,
}

/// One-pass transform of a NATURAL branch body (context
/// `Γ, fix, x_0..x_{k-1}, fields…`) into the general encoding's minor-premise
/// body (context `Γ, fix, x_0..x_{k-1}, fields…, ihs…, post'…`):
///
/// - self-calls `f x_0 … x_{r-1} field a'… extras` → `ih a'… extras` (the
///   struct argument must be a direct recursive field; PRE-struct arguments
///   must be exactly the enclosing binders; post-struct arguments and extras
///   are arbitrary and recursively transformed);
/// - references to the enclosing post binders rebind to the minor's own
///   `post'` binders;
/// - all other references shift over the inserted `ihs`/`post'` binders;
/// - any other self-reference is a hard error (fail closed).
///
/// The traversal mirrors [`dialect_map_rels`]' shape table (including the
/// `StructFix` component offsets) so self-calls INSIDE a nested Case's
/// lowering are rewritten at the correct depth.
fn fix_branch_transform(sexp: &Sexp, depth: u32, cfg: &FixBranchCfg) -> Result<Sexp, String> {
    let self_rel = cfg.m + cfg.k + depth;
    let rel_of = |s: &Sexp| -> Option<u32> {
        match s {
            Sexp::Atom(a) => a.parse::<u32>().ok(),
            Sexp::List(v) => {
                if v.len() == 2 && matches!(&v[0], Sexp::Atom(h) if h == "Rel") {
                    match &v[1] {
                        Sexp::Atom(a) => a.parse::<u32>().ok(),
                        _ => None,
                    }
                } else {
                    None
                }
            }
        }
    };
    let is_rel = |s: &Sexp, n: u32| rel_of(s) == Some(n);
    // Intercept saturated self-call applications.
    if let Sexp::List(v) = sexp {
        if v.len() >= 2 && matches!(&v[0], Sexp::Atom(h) if h == "App") && is_rel(&v[1], self_rel) {
            let args = &v[2..];
            if (args.len() as u32) < cfg.k {
                return Err("Fix: partially applied recursive self-call".to_string());
            }
            // Struct argument must be a direct recursive field.
            let jp = cfg
                .rec_fields
                .iter()
                .position(|&i| is_rel(&args[cfg.r as usize], depth + cfg.m - 1 - i))
                .ok_or("Fix: self-call struct argument is not a recursive field")?;
            // PRE-struct arguments must be exactly the enclosing fix binders
            // (they are recursor parameters, fixed across the recursion).
            for s in 0..cfg.r {
                if !is_rel(&args[s as usize], depth + cfg.m + cfg.k - 1 - s) {
                    return Err(
                        "Fix: self-call pre-struct argument is not the enclosing fix binder"
                            .to_string(),
                    );
                }
            }
            let ih = rel_sexp(depth + cfg.p + (cfg.q - 1 - jp as u32));
            let rest: Vec<Sexp> = args[cfg.r as usize + 1..]
                .iter()
                .map(|a| fix_branch_transform(a, depth, cfg))
                .collect::<Result<_, _>>()?;
            return Ok(if rest.is_empty() {
                ih
            } else {
                let mut app = vec![Sexp::Atom("App".to_string()), ih];
                app.extend(rest);
                Sexp::List(app)
            });
        }
    }
    // A bare self-reference anywhere else is unrewritable.
    if is_rel(sexp, self_rel) {
        return Err("Fix: self-reference outside a recognized structural self-call".to_string());
    }
    // STRUCT-BINDER reference `x_r` (natural frame `[Γ, fix, x_0..x_{k-1},
    // fields…]`, so `x_r` sits at distance `m + p` above the branch root):
    // substitute the branch's reconstructed constructor application
    // `C_j params… fields…` (see [`StructBinderRecon`] — keeping the
    // enclosing binder captured the ORIGINAL argument, wrong at recursion
    // depth ≥ 1). In the TARGET frame (fields, ihs, post' inserted) field `i`
    // is `Rel(depth + q + p + (m-1-i))`; the params (base frame) lift over
    // fields + ihs + post' + the traversal depth.
    if is_rel_node(sexp, depth + cfg.m + cfg.p) {
        SPECULATIVE_MOTIVE_USED.with(|c| c.set(true));
        let field_rels: Vec<u32> = (0..cfg.m)
            .map(|i| depth + cfg.q + cfg.p + (cfg.m - 1 - i))
            .collect();
        return cfg
            .recon
            .assemble(cfg.m + cfg.q + cfg.p + depth, &field_rels);
    }
    // Rel leaves: remap into the minor-premise context.
    if let Some(n) = rel_of(sexp) {
        let c = depth;
        return Ok(rel_sexp(if n < c {
            n
        } else {
            let d = n - c;
            if d < cfg.m {
                n + cfg.q + cfg.p // fields: over the inserted ihs + post'
            } else if d < cfg.m + cfg.p {
                n - cfg.m // enclosing posts → the minor's post' binders
            } else {
                n + cfg.q + cfg.p // struct / pres / outer
            }
        }));
    }
    match sexp {
        Sexp::Atom(_) => Ok(sexp.clone()),
        Sexp::List(items) => {
            let head = match items.first() {
                Some(Sexp::Atom(h)) => h.as_str(),
                _ => return Err("Fix: headless list in branch body".to_string()),
            };
            match head {
                "Sort" | "Const" | "Ind" | "Construct" | "Int" | "Float" | "Var"
                | "CoqUnsupported" => Ok(sexp.clone()),
                "Prod" | "Lambda" if items.len() == 4 => Ok(Sexp::List(vec![
                    items[0].clone(),
                    items[1].clone(),
                    fix_branch_transform(&items[2], depth, cfg)?,
                    fix_branch_transform(&items[3], depth + 1, cfg)?,
                ])),
                "LetIn" if items.len() == 5 => Ok(Sexp::List(vec![
                    items[0].clone(),
                    items[1].clone(),
                    fix_branch_transform(&items[2], depth, cfg)?,
                    fix_branch_transform(&items[3], depth, cfg)?,
                    fix_branch_transform(&items[4], depth + 1, cfg)?,
                ])),
                "App" => {
                    let mut out = vec![items[0].clone()];
                    for a in &items[1..] {
                        out.push(fix_branch_transform(a, depth, cfg)?);
                    }
                    Ok(Sexp::List(out))
                }
                "Case" => {
                    let mut out = vec![items[0].clone(), items[1].clone()];
                    for part in &items[2..] {
                        let Sexp::List(pv) = part else {
                            return Err("Fix: malformed Case part in branch body".to_string());
                        };
                        let mut np = vec![pv[0].clone()];
                        for pp in &pv[1..] {
                            np.push(fix_branch_transform(pp, depth, cfg)?);
                        }
                        out.push(Sexp::List(np));
                    }
                    Ok(Sexp::List(out))
                }
                "StructFix" => {
                    // Mirror dialect_map_rels' component offsets so self-calls
                    // inside a nested Case/Fix lowering rewrite at the right
                    // depth.
                    let mut pre_len: u32 = 0;
                    let mut post_len: u32 = 0;
                    for part in &items[2..] {
                        if let Sexp::List(pv) = part {
                            match pv.first() {
                                Some(Sexp::Atom(t)) if t == "Pre" => {
                                    pre_len = (pv.len() - 1) as u32;
                                }
                                Some(Sexp::Atom(t)) if t == "Post" => {
                                    post_len = (pv.len() - 1) as u32;
                                }
                                _ => {}
                            }
                        }
                    }
                    let inner = pre_len + 1 + post_len;
                    let mut out = vec![items[0].clone(), items[1].clone()];
                    for part in &items[2..] {
                        let Sexp::List(pv) = part else {
                            return Err("Fix: malformed StructFix part in branch body".to_string());
                        };
                        let ptag = match pv.first() {
                            Some(Sexp::Atom(t)) => t.as_str(),
                            _ => return Err("Fix: untagged StructFix part in branch body".into()),
                        };
                        let offsets: Vec<u32> = match ptag {
                            "RecLevel" => {
                                out.push(part.clone());
                                continue;
                            }
                            "Pre" => (0..pre_len).collect(),
                            "StructTy" => vec![pre_len],
                            "Post" => (0..post_len).map(|i| pre_len + 1 + i).collect(),
                            "Params" | "Indices" | "Motive" | "Branch" => {
                                vec![inner; pv.len() - 1]
                            }
                            other => {
                                return Err(format!(
                                    "Fix: unknown StructFix part `{other}` in branch body"
                                ))
                            }
                        };
                        let mut np = vec![pv[0].clone()];
                        for (pp, off) in pv[1..].iter().zip(offsets.iter()) {
                            np.push(fix_branch_transform(pp, depth + off, cfg)?);
                        }
                        out.push(Sexp::List(np));
                    }
                    Ok(Sexp::List(out))
                }
                other => Err(format!("Fix: unsupported head `{other}` in branch body")),
            }
        }
    }
}

/// Re-express a post binder's TYPE `A_j` (natural context
/// `Γ, fix, x_0..x_{j-1}`) inside a minor premise (context
/// `Γ, fix, x_0..x_{k-1}, fields…, ihs…, post'_{r+1}..post'_{j-1}`):
/// references to earlier posts keep their offsets (they now denote the
/// minor's own `post'` binders); a reference to the struct binder is a hard
/// error (the motive's post telescope cannot depend on the scrutinee under
/// this encoding); everything outer shifts across the inserted binders.
fn post_ty_in_branch(a: &Sexp, j: u32, cfg: &FixBranchCfg) -> Result<Sexp, String> {
    dialect_map_rels(a, 0, &mut |n, c| {
        if n < c {
            return Ok(rel_sexp(n));
        }
        let d = n - c;
        if d + cfg.r + 1 < j {
            Ok(rel_sexp(n)) // earlier posts → the minor's post' binders
        } else if d + cfg.r + 1 == j {
            Err(
                "Fix: post-binder type depends on the structural argument (unsupported)"
                    .to_string(),
            )
        } else {
            Ok(rel_sexp(n + cfg.k + cfg.q + cfg.m - cfg.r - 1))
        }
    })
}

/// Convert a parsed s-expression to a CIC term.
pub(crate) fn sexp_to_cic(sexp: &Sexp) -> Result<CicTerm, MathverseError> {
    match sexp {
        Sexp::Atom(s) => match s.as_str() {
            "Prop" => Ok(CicTerm::Sort(CicSort::Prop)),
            "Set" => Ok(CicTerm::Sort(CicSort::Set)),
            _ => s
                .parse::<u32>()
                .map(CicTerm::Rel)
                .or_else(|_| Ok(CicTerm::Var(s.clone()))),
        },
        Sexp::List(items) if items.is_empty() => Err(coq_err("empty list")),
        Sexp::List(items) => {
            let head = match &items[0] {
                Sexp::Atom(s) => s.as_str(),
                _ => return Err(coq_err("expected atom head")),
            };
            match head {
                "Rel" => Ok(CicTerm::Rel(get_u32(items, 1)?)),
                "Var" => Ok(CicTerm::Var(get_str(items, 1)?)),
                "Sort" => parse_sort(&items[1..]),
                "Prod" | "Lambda" => {
                    let (n, ty, body) = (
                        get_str(items, 1)?,
                        sexp_to_cic(get_at(items, 2)?)?,
                        sexp_to_cic(get_at(items, 3)?)?,
                    );
                    Ok(if head == "Prod" {
                        CicTerm::Prod(n, Box::new(ty), Box::new(body))
                    } else {
                        CicTerm::Lambda(n, Box::new(ty), Box::new(body))
                    })
                }
                "LetIn" => {
                    let (n, v) = (get_str(items, 1)?, sexp_to_cic(get_at(items, 2)?)?);
                    let (t, b) = (
                        sexp_to_cic(get_at(items, 3)?)?,
                        sexp_to_cic(get_at(items, 4)?)?,
                    );
                    Ok(CicTerm::LetIn(n, Box::new(v), Box::new(t), Box::new(b)))
                }
                "App" => {
                    let f = sexp_to_cic(get_at(items, 1)?)?;
                    let args: Result<Vec<_>, _> = items[2..].iter().map(sexp_to_cic).collect();
                    Ok(CicTerm::App(Box::new(f), args?))
                }
                "Const" => {
                    // Handles (Const name) and (Const (KerName ...) (Instance ...))
                    Ok(CicTerm::Const(extract_kernel_name(get_at(items, 1)?)?))
                }
                "ConstU" => {
                    // (ConstU <name> <lean-level>...) — a reference to a
                    // universe-polymorphic constant at explicit CONCRETE
                    // levels (each `<lean-level>` is the decimal Lean-scale
                    // level, so `0` = Prop's level and `1` = Set's level).
                    let name = get_str(items, 1)?;
                    let levels = items[2..]
                        .iter()
                        .enumerate()
                        .map(|(i, _)| get_u32(items, i + 2).map(CoqUniverseLevel::Type))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(CicTerm::ConstU(name, levels))
                }
                "CoqUnsupported" => {
                    // Fail-closed marker emitted by the SerAPI adapter for
                    // out-of-model shapes; carries the reason.
                    Err(coq_err(&get_str(items, 1).unwrap_or_else(|_| {
                        "out-of-model construct (no reason recorded)".to_string()
                    })))
                }
                "Ind" => {
                    // (Ind name i) or (Ind (MutInd "name" i) (Instance ...))
                    let name = extract_kernel_name(get_at(items, 1)?)?;
                    let idx = if items.len() > 2 {
                        match &items[2] {
                            Sexp::Atom(s) => s.parse::<u32>().unwrap_or(0),
                            _ => 0,
                        }
                    } else {
                        0
                    };
                    Ok(CicTerm::Ind(name, idx))
                }
                "Construct" => {
                    // (Construct name i j) or (Construct (MutConstruct "name" i j R) ...)
                    match get_at(items, 1)? {
                        Sexp::List(inner) if !inner.is_empty() => {
                            let name = extract_kernel_name(&items[1])?;
                            let i = get_u32(inner, 2).unwrap_or(0);
                            let j = get_u32(inner, 3).unwrap_or(0);
                            Ok(CicTerm::Construct(name, i, j))
                        }
                        _ => Ok(CicTerm::Construct(
                            get_str(items, 1)?,
                            get_u32(items, 2)?,
                            get_u32(items, 3)?,
                        )),
                    }
                }
                "Case" => parse_case(items),
                "StructFix" => parse_struct_fix(items),
                "Fix" => {
                    let (bodies, idx) = parse_fix_bodies(items, 1)?;
                    Ok(CicTerm::Fix(bodies, idx))
                }
                "CoFix" => {
                    let (bodies, idx) = parse_fix_bodies(items, 1)?;
                    Ok(CicTerm::CoFix(bodies, idx))
                }
                "Int" => Ok(CicTerm::Int(get_i64(items, 1)?)),
                "Float" => Ok(CicTerm::Float(get_f64(items, 1)?)),
                "Proj" => Ok(CicTerm::Proj(
                    get_str(items, 1)?,
                    get_u32(items, 2)?,
                    Box::new(sexp_to_cic(get_at(items, 3)?)?),
                )),
                other => Err(coq_err(&format!("unknown CIC constructor: {other}"))),
            }
        }
    }
}

/// Parse a Coq `match` into the structured [`CicCase`] the recursor lowering
/// consumes.
///
/// Accepts the importer-dialect form
/// ```text
/// (Case (Ind <name> <i>) (Params <p>...) (Motive <m>) (Discriminant <d>)
///       (Branch <b0>) (Branch <b1>) ...)
/// ```
/// where the branch bodies are already abstracted over their constructor's
/// fields (i.e. each `<bk>` is a `λ field… . body`, the recursor minor
/// premise). The motive is the `match`'s return predicate; the discriminant is
/// the scrutinee. The inductive head names the recursor `<name>.<i>.rec`, and
/// the parameters become its leading explicit arguments. This shape is exactly
/// what an `<ind>.rec` application needs, so [`cic_to_flat_expr`] can emit a
/// well-typed elimination the kernel checks.
fn parse_case(items: &[Sexp]) -> Result<CicTerm, MathverseError> {
    // items[0] == "Case"; items[1] == (Ind name i)
    let (ind_name, ind_idx) = match get_at(items, 1)? {
        Sexp::List(v) if v.len() >= 3 && matches!(v.first(), Some(Sexp::Atom(h)) if h == "Ind") => {
            let name = match &v[1] {
                Sexp::Atom(s) => s.clone(),
                _ => return Err(coq_err("Case: Ind name must be an atom")),
            };
            let idx = match &v[2] {
                Sexp::Atom(s) => s
                    .parse::<u32>()
                    .map_err(|_| coq_err("Case: bad Ind index"))?,
                _ => return Err(coq_err("Case: Ind index must be an atom")),
            };
            (name, idx)
        }
        _ => return Err(coq_err("Case: expected (Ind name i) as first argument")),
    };

    let mut params: Vec<CicTerm> = Vec::new();
    let mut motive: Option<CicTerm> = None;
    let mut discriminant: Option<CicTerm> = None;
    let mut branches: Vec<CicTerm> = Vec::new();

    for item in &items[2..] {
        let parts = match item {
            Sexp::List(v) if !v.is_empty() => v,
            _ => return Err(coq_err("Case: expected a tagged sub-form")),
        };
        let tag = match &parts[0] {
            Sexp::Atom(s) => s.as_str(),
            _ => return Err(coq_err("Case: sub-form must start with a tag")),
        };
        match tag {
            "Params" => {
                for p in &parts[1..] {
                    params.push(sexp_to_cic(p)?);
                }
            }
            "Motive" => {
                motive = Some(sexp_to_cic(get_at(parts, 1)?)?);
            }
            "Discriminant" => {
                discriminant = Some(sexp_to_cic(get_at(parts, 1)?)?);
            }
            "Branch" => {
                branches.push(sexp_to_cic(get_at(parts, 1)?)?);
            }
            other => return Err(coq_err(&format!("Case: unexpected sub-form `{other}`"))),
        }
    }

    let motive = motive.ok_or_else(|| coq_err("Case: missing (Motive ...)"))?;
    let discriminant = discriminant.ok_or_else(|| coq_err("Case: missing (Discriminant ...)"))?;
    if branches.is_empty() {
        return Err(coq_err("Case: at least one (Branch ...) is required"));
    }

    Ok(CicTerm::Case(Box::new(CicCase {
        ind_name,
        ind_idx,
        params,
        motive: Box::new(motive),
        branches,
        discriminant: Box::new(discriminant),
    })))
}

/// Parse a Coq structural fixpoint into the structured [`CicStructFix`] the
/// recursor lowering consumes.
///
/// Accepts the importer-dialect form
/// ```text
/// (StructFix (Ind <name> <i>)
///   (RecLevel <u>)
///   (Params <p>...)
///   (Pre <ty>...)
///   (StructTy <ty>)
///   (Post <ty>...)
///   (Motive <m>)
///   (Branch <b0>) (Branch <b1>) ...)
/// ```
/// where each branch body is abstracted over its constructor's fields *and*
/// their induction hypotheses (the recursor minor premise); a recursive
/// self-call is written as a reference to a hypothesis binder. The inductive
/// head names the recursor `<name>.<i>.rec`; `RecLevel` supplies its motive
/// universe instance (the `(RecLevel Prop)` atom marks a Prop-ONLY-eliminating
/// recursor, which takes no motive universe parameter — empty instance);
/// `Pre`/`StructTy`/`Post` are the function's argument binder
/// types in order (the structural argument sits between `Pre` and `Post`). The
/// `Params`, `Motive` and `Branch` parts are exactly what an `<ind>.<i>.rec`
/// application needs, so [`cic_to_flat_expr`] emits a well-typed elimination the
/// kernel checks and reduces.
fn parse_struct_fix(items: &[Sexp]) -> Result<CicTerm, MathverseError> {
    // items[0] == "StructFix"; items[1] == (Ind name i)
    let (ind_name, ind_idx) = match get_at(items, 1)? {
        Sexp::List(v) if v.len() >= 3 && matches!(v.first(), Some(Sexp::Atom(h)) if h == "Ind") => {
            let name = match &v[1] {
                Sexp::Atom(s) => s.clone(),
                _ => return Err(coq_err("StructFix: Ind name must be an atom")),
            };
            let idx = match &v[2] {
                Sexp::Atom(s) => s
                    .parse::<u32>()
                    .map_err(|_| coq_err("StructFix: bad Ind index"))?,
                _ => return Err(coq_err("StructFix: Ind index must be an atom")),
            };
            (name, idx)
        }
        _ => {
            return Err(coq_err(
                "StructFix: expected (Ind name i) as first argument",
            ))
        }
    };

    let mut rec_level: u32 = 0;
    let mut prop_only = false;
    let mut params: Vec<CicTerm> = Vec::new();
    let mut pre_binders: Vec<CicTerm> = Vec::new();
    let mut struct_ty: Option<CicTerm> = None;
    let mut post_binders: Vec<CicTerm> = Vec::new();
    let mut indices: Vec<CicTerm> = Vec::new();
    let mut motive: Option<CicTerm> = None;
    let mut branches: Vec<CicTerm> = Vec::new();

    for item in &items[2..] {
        let parts = match item {
            Sexp::List(v) if !v.is_empty() => v,
            _ => return Err(coq_err("StructFix: expected a tagged sub-form")),
        };
        let tag = match &parts[0] {
            Sexp::Atom(s) => s.as_str(),
            _ => return Err(coq_err("StructFix: sub-form must start with a tag")),
        };
        match tag {
            "RecLevel" => match get_at(parts, 1)? {
                // A Prop-ONLY-eliminating recursor has no motive universe
                // parameter — `(RecLevel Prop)` lowers to an empty instance.
                Sexp::Atom(s) if s == "Prop" => prop_only = true,
                _ => rec_level = get_u32(parts, 1)?,
            },
            "Params" => {
                for p in &parts[1..] {
                    params.push(sexp_to_cic(p)?);
                }
            }
            "Pre" => {
                for p in &parts[1..] {
                    pre_binders.push(sexp_to_cic(p)?);
                }
            }
            "StructTy" => struct_ty = Some(sexp_to_cic(get_at(parts, 1)?)?),
            "Post" => {
                for p in &parts[1..] {
                    post_binders.push(sexp_to_cic(p)?);
                }
            }
            "Indices" => {
                for p in &parts[1..] {
                    indices.push(sexp_to_cic(p)?);
                }
            }
            "Motive" => motive = Some(sexp_to_cic(get_at(parts, 1)?)?),
            "Branch" => branches.push(sexp_to_cic(get_at(parts, 1)?)?),
            other => {
                return Err(coq_err(&format!(
                    "StructFix: unexpected sub-form `{other}`"
                )))
            }
        }
    }

    let struct_ty = struct_ty.ok_or_else(|| coq_err("StructFix: missing (StructTy ...)"))?;
    let motive = motive.ok_or_else(|| coq_err("StructFix: missing (Motive ...)"))?;
    // NOTE: zero branches are legal — the eliminator of an EMPTY inductive
    // (`False`, `Empty_set`) has no minor premises.

    Ok(CicTerm::StructFix(Box::new(CicStructFix {
        ind_name,
        ind_idx,
        rec_level,
        prop_only,
        params,
        pre_binders,
        struct_ty: Box::new(struct_ty),
        post_binders,
        indices,
        motive: Box::new(motive),
        branches,
    })))
}

fn parse_sort(items: &[Sexp]) -> Result<CicTerm, MathverseError> {
    if items.is_empty() {
        return Err(coq_err("Sort with no argument"));
    }
    match &items[0] {
        Sexp::Atom(s) => match s.as_str() {
            "Prop" => Ok(CicTerm::Sort(CicSort::Prop)),
            "Set" => Ok(CicTerm::Sort(CicSort::Set)),
            // SProp (strict propositions, Coq 8.10+) maps to Prop in our encoding
            "SProp" => Ok(CicTerm::Sort(CicSort::Prop)),
            _ => Ok(CicTerm::Sort(CicSort::type_at(
                s.parse::<u32>().map_err(|_| coq_err("invalid universe"))?,
            ))),
        },
        Sexp::List(inner)
            if inner.len() >= 2 && matches!(&inner[0], Sexp::Atom(t) if t == "Type") =>
        {
            Ok(CicTerm::Sort(CicSort::type_at(get_u32(inner, 1)?)))
        }
        // (Sort (Param <name>)) — a universe-POLYMORPHIC sort: the whole sort
        // is one bound level parameter of the enclosing declaration (the
        // Lean-fused encoding of Coq's `Sort@{q|u}` quality+level binder pair;
        // `Param = 0` is Prop, `Param = n+1` is `Type (n)`). Lowers to
        // `Sort(Level::Param(name))`; the declaration's header must bind
        // `name` in its `level_params` window.
        Sexp::List(inner)
            if inner.len() >= 2 && matches!(&inner[0], Sexp::Atom(t) if t == "Param") =>
        {
            Ok(CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Var(
                get_str(inner, 1)?,
            ))))
        }
        _ => Err(coq_err("invalid Sort form")),
    }
}

fn get_at(items: &[Sexp], i: usize) -> Result<&Sexp, MathverseError> {
    items
        .get(i)
        .ok_or_else(|| coq_err(&format!("missing index {i}")))
}
fn get_str(items: &[Sexp], i: usize) -> Result<String, MathverseError> {
    match items.get(i) {
        Some(Sexp::Atom(s)) => Ok(s.clone()),
        _ => Err(coq_err(&format!("expected atom at {i}"))),
    }
}
fn get_u32(items: &[Sexp], i: usize) -> Result<u32, MathverseError> {
    get_str(items, i)?
        .parse()
        .map_err(|_| coq_err("expected u32"))
}
fn get_i64(items: &[Sexp], i: usize) -> Result<i64, MathverseError> {
    get_str(items, i)?
        .parse()
        .map_err(|_| coq_err("expected i64"))
}
fn get_f64(items: &[Sexp], i: usize) -> Result<f64, MathverseError> {
    get_str(items, i)?
        .parse()
        .map_err(|_| coq_err("expected f64"))
}
fn coq_err(reason: &str) -> MathverseError {
    MathverseError::ImportFailed {
        system: "Coq".into(),
        reason: reason.into(),
    }
}

/// If `name` is a Coq machine-primitive CARRIER type that Clean's kernel models
/// as a concrete carrier, return that native carrier's constant name. Primitive
/// `float`s are `Nat` bit patterns and `int` values are `Nat`s in the kernel's
/// native model, so their carriers import as `carrier := Nat` (see the import
/// site in [`CoqImporter::import_sexp_with_registry`]).
fn coq_primitive_carrier_native(name: &str) -> Option<&'static str> {
    match name {
        "Coq.Floats.PrimFloat.float" | "Coq.Numbers.Cyclic.Int63.PrimInt63.int" => Some("Nat"),
        _ => None,
    }
}

/// The `<name>.<block>` constant name of the one Coq inductive imported
/// UNIVERSE-POLYMORPHICALLY (template polymorphism into `Prop`): `prod` — the
/// eqmx/mxalgebra unlock. Coq's `prod` is template-polymorphic (`prod P Q :
/// Prop` when `P Q : Prop`), so it is imported as
/// `prod.{u,v} : Sort u → Sort v → Sort (max u v)` (see `import_serapi_inductive`
/// and `coq_template_poly_prod_feasibility.rs`). Every reference to it, its
/// constructor, or its recursor must therefore carry an explicit level instance
/// instead of the level-free `u32::MAX` sentinel.
pub(crate) const TEMPLATE_POLY_PROD: &str = "Coq.Init.Datatypes.prod.0";

/// Universe-parameter arity of a template-polymorphic Coq inductive, keyed on
/// its `<name>.<block>` constant name. `None` for a non-template inductive (the
/// overwhelming majority — their references stay level-free, byte-identical to
/// before). Today only `prod` (2 params `u`, `v`).
pub(crate) fn template_poly_param_count(ind_const_name: &str) -> Option<usize> {
    match ind_const_name {
        TEMPLATE_POLY_PROD => Some(2),
        _ => None,
    }
}

/// Build the universe-instance level list a reference to a template-poly
/// inductive/constructor (`motive = None`) or its recursor
/// (`motive = Some(<motive-level pool index>)`) carries, and return its
/// `level_lists` offset for a `const_ref`.
///
/// The inductive's own `n` universe parameters instantiate to `Sort 1`
/// (`succ zero`), reproducing the pre-poly MONOMORPHIC `Type 1` rendering
/// EXACTLY: `prod.{1,1}` is byte-identical in type to the old
/// `prod : Sort 1 → Sort 1 → Sort 1`, so a currently-`KernelVerified` `prod`
/// use re-checks unchanged (proved in `coq_template_poly_prod_feasibility.rs`).
/// The recursor's motive slot is supplied separately (`motive`), matching the
/// kernel's generated `<ind>.rec.{motive, u, v}` level-param order.
fn template_poly_instance_list(n: usize, motive: Option<u32>, w: &mut ShardWriter) -> u32 {
    let zero = w.add_level(FlatLevel::zero());
    let one = w.add_level(FlatLevel::succ(zero));
    let mut idxs = Vec::with_capacity(n + usize::from(motive.is_some()));
    if let Some(m) = motive {
        idxs.push(m);
    }
    for _ in 0..n {
        idxs.push(one);
    }
    w.add_level_list(&idxs)
}

/// Lower a CIC term into the FlatExpr arena. Returns the arena index.
pub(crate) fn cic_to_flat_expr(term: &CicTerm, w: &mut ShardWriter) -> u32 {
    match term {
        CicTerm::Rel(n) => w.add_expr(FlatExpr::bvar(*n)),
        CicTerm::Var(name) | CicTerm::Const(name) => {
            let ni = w.add_string(name);
            w.add_expr(FlatExpr::const_ref(ni, u32::MAX))
        }
        CicTerm::Sort(sort) => {
            let li = match sort {
                CicSort::Prop => w.add_level(FlatLevel::zero()),
                CicSort::Set => {
                    let z = w.add_level(FlatLevel::zero());
                    w.add_level(FlatLevel::succ(z))
                }
                // Lower the level STRUCTURALLY (`universe_level_to_flat`): a
                // concrete `Type i` reproduces the old `succ^i(zero)` bytes
                // exactly, while `Max`/`Succ`/`Var` levels round-trip faithfully
                // for the kernel to normalize.
                CicSort::Type(level) => universe_level_to_flat(level, w),
            };
            w.add_expr(FlatExpr::sort(li))
        }
        CicTerm::Prod(_, ty, body) => {
            let (ti, bi) = (cic_to_flat_expr(ty, w), cic_to_flat_expr(body, w));
            w.add_expr(FlatExpr::pi(0, ti, bi))
        }
        CicTerm::Lambda(_, ty, body) => {
            let (ti, bi) = (cic_to_flat_expr(ty, w), cic_to_flat_expr(body, w));
            w.add_expr(FlatExpr::lam(0, ti, bi))
        }
        CicTerm::LetIn(_, val, ty, body) => {
            let (ti, vi, bi) = (
                cic_to_flat_expr(ty, w),
                cic_to_flat_expr(val, w),
                cic_to_flat_expr(body, w),
            );
            w.add_expr(FlatExpr::let_expr(ti, vi, bi))
        }
        CicTerm::App(f, args) => {
            let mut cur = cic_to_flat_expr(f, w);
            for a in args {
                let ai = cic_to_flat_expr(a, w);
                cur = w.add_expr(FlatExpr::app(cur, ai));
            }
            cur
        }
        CicTerm::ConstU(name, levels) => {
            // A universe-polymorphic constant reference at explicit levels:
            // lower each level structurally and attach a REAL level list to
            // the `const_ref` (the same encoding the `StructFix` recursor
            // head uses), so the kernel instantiates the constant's
            // `level_params` at these levels on re-check.
            let ni = w.add_string(name);
            let level_indices: Vec<u32> = levels
                .iter()
                .map(|l| universe_level_to_flat(l, w))
                .collect();
            let lvl_list = w.add_level_list(&level_indices);
            w.add_expr(FlatExpr::const_ref(ni, lvl_list))
        }
        CicTerm::Ind(name, idx) => {
            let full = format!("{name}.{idx}");
            let ni = w.add_string(&full);
            // Template-poly inductive (`prod`): carry the {1,1} monomorphic
            // instance; every other inductive stays level-free (`u32::MAX`).
            let levels = match template_poly_param_count(&full) {
                Some(n) => template_poly_instance_list(n, None, w),
                None => u32::MAX,
            };
            w.add_expr(FlatExpr::const_ref(ni, levels))
        }
        CicTerm::Construct(name, ii, ci) => {
            let ni = w.add_string(&format!("{name}.{ii}.{ci}"));
            // A constructor reference instantiates its PARENT inductive's
            // universe parameters — key on the parent `<name>.<ii>` name.
            let levels = match template_poly_param_count(&format!("{name}.{ii}")) {
                Some(n) => template_poly_instance_list(n, None, w),
                None => u32::MAX,
            };
            w.add_expr(FlatExpr::const_ref(ni, levels))
        }
        CicTerm::Case(case) => {
            // A Coq `match` is an application of the matched inductive's
            // recursor. Clean's kernel has no native match node — it only has
            // recursors that `add_inductive` auto-generates as `<ind>.rec` with
            // standard argument order `params → motive → minors → indices →
            // major`. We emit exactly that spine so the kernel typechecks it as
            // a genuine elimination (and rejects ill-typed branches):
            //   @<ind>.<idx>.rec <params...> <motive> <branch_0..n> <discriminant>
            // Indices are folded into the discriminant's parameter args by the
            // caller (non-indexed inductives like `or`/`and` have none).
            let parent = format!("{}.{}", case.ind_name, case.ind_idx);
            let rec_name = format!("{parent}.rec");
            let rec_name_idx = w.add_string(&rec_name);
            // A template-poly recursor (`prod.0.rec`) declares
            // `[motive, u, v]`. This Prop-only-shape `Case` path defaults the
            // motive slot to Prop (0); the monotone bump ladder lifts it if the
            // site needs a larger motive. Poly slots take the {1,1} instance.
            // (Non-template recursors keep the level-free `u32::MAX` sentinel —
            // byte-identical to before; `prod` normally routes through the
            // large-elim `StructFix` path, so this arm is a completeness guard.)
            let head_levels = match template_poly_param_count(&parent) {
                Some(n) => {
                    let zero = w.add_level(FlatLevel::zero());
                    template_poly_instance_list(n, Some(zero), w)
                }
                None => u32::MAX,
            };
            let mut cur = w.add_expr(FlatExpr::const_ref(rec_name_idx, head_levels));
            // Parameters first.
            for p in &case.params {
                let pi = cic_to_flat_expr(p, w);
                cur = w.add_expr(FlatExpr::app(cur, pi));
            }
            // Motive (return predicate).
            let mi = cic_to_flat_expr(&case.motive, w);
            cur = w.add_expr(FlatExpr::app(cur, mi));
            // Minor premises (one per constructor branch).
            for b in &case.branches {
                let bi = cic_to_flat_expr(b, w);
                cur = w.add_expr(FlatExpr::app(cur, bi));
            }
            // Major premise (discriminant) last.
            let di = cic_to_flat_expr(&case.discriminant, w);
            w.add_expr(FlatExpr::app(cur, di))
        }
        CicTerm::StructFix(fix) => {
            // A Coq structural fixpoint is an application of the recursion
            // inductive's recursor, wrapped in the function's argument lambdas.
            // Clean's kernel has no native fix and no recursive definition by
            // name — recursion exists ONLY through recursors `add_inductive`
            // auto-generates as `<ind>.rec` with argument order
            // `params → motive → minors → major` and iota reduction. The
            // recursive self-call is supplied by the recursor as each minor
            // premise's induction-hypothesis argument, so the branches reference
            // those hypotheses. We emit:
            //   λ pre… struct post…. @<ind>.<idx>.rec.{u} params motive
            //        branch_0..n struct
            // and the kernel typechecks AND reduces the elimination (so 2+2
            // reduces to 4).
            //
            // Build the recursor head carrying its motive universe instance as a
            // one-element level list. A `Set`/`Type`-sorted inductive's recursor
            // is universe-polymorphic over the motive's result sort; `rec_level`
            // names that level (1 for a `nat → nat` motive returning `nat:Set`).
            // A Prop-ONLY-eliminating inductive's recursor takes NO motive
            // universe parameter (the kernel's `build_recursor` prop_only arm),
            // so its instance is EMPTY.
            // A template-poly recursor (`prod.0.rec`) declares
            // `[motive, u, v]`, so the motive-level instance is prepended to the
            // poly slots (the {1,1} monomorphic instance). This is the large-elim
            // path every `match`/`fix` on `prod` routes through
            // (`assemble_level_param_case`), reproducing today's `prod` uses at
            // `[rec_level, 1, 1]` and (for the eqmx cascade) flippable to
            // `[rec_level, 0, 0]` by the incremental verifier's Prop-collapse
            // retry. Non-template recursors keep their historic level list.
            let poly = template_poly_param_count(&format!("{}.{}", fix.ind_name, fix.ind_idx));
            let lvl_list = if fix.prop_only {
                match poly {
                    // A poly recursor is large-eliminating (never Prop-only), but
                    // if the importer's mirror marked this site prop_only, still
                    // supply the poly slots with a Prop motive so the count matches.
                    Some(n) => {
                        let zero = w.add_level(FlatLevel::zero());
                        template_poly_instance_list(n, Some(zero), w)
                    }
                    None => w.add_level_list(&[]),
                }
            } else {
                let mut lvl = w.add_level(FlatLevel::zero());
                for _ in 0..fix.rec_level {
                    lvl = w.add_level(FlatLevel::succ(lvl));
                }
                match poly {
                    Some(n) => template_poly_instance_list(n, Some(lvl), w),
                    None => w.add_level_list(&[lvl]),
                }
            };
            let rec_name = format!("{}.{}.rec", fix.ind_name, fix.ind_idx);
            let rec_name_idx = w.add_string(&rec_name);
            let mut cur = w.add_expr(FlatExpr::const_ref(rec_name_idx, lvl_list));
            // Inductive parameters first.
            for p in &fix.params {
                let pi = cic_to_flat_expr(p, w);
                cur = w.add_expr(FlatExpr::app(cur, pi));
            }
            // Motive.
            let mi = cic_to_flat_expr(&fix.motive, w);
            cur = w.add_expr(FlatExpr::app(cur, mi));
            // Minor premises (one per constructor; recursive ones bind their
            // fields' induction hypotheses, which carry the recursive results).
            for b in &fix.branches {
                let bi = cic_to_flat_expr(b, w);
                cur = w.add_expr(FlatExpr::app(cur, bi));
            }
            // Index arguments (INDEXED family only): the recursor spine is
            // `params → motive → minors → INDICES → major`, so the struct
            // argument's inductive index terms are applied right before the
            // major. Empty for a non-indexed inductive, so the historical
            // `params → motive → minors → major` spine is unchanged.
            for ix in &fix.indices {
                let ii = cic_to_flat_expr(ix, w);
                cur = w.add_expr(FlatExpr::app(cur, ii));
            }
            // Major premise = the structural argument. Inside the recursor
            // application its de Bruijn index is the number of post-binders (the
            // binders introduced AFTER it), so it is `Rel(post_binders.len())`.
            let major = w.add_expr(FlatExpr::bvar(fix.post_binders.len() as u32));
            cur = w.add_expr(FlatExpr::app(cur, major));
            // Wrap in the function's argument lambdas, innermost (last post
            // binder) first: post binders, then the structural argument, then
            // pre binders.
            for ty in fix.post_binders.iter().rev() {
                let ti = cic_to_flat_expr(ty, w);
                cur = w.add_expr(FlatExpr::lam(0, ti, cur));
            }
            let struct_ti = cic_to_flat_expr(&fix.struct_ty, w);
            cur = w.add_expr(FlatExpr::lam(0, struct_ti, cur));
            for ty in fix.pre_binders.iter().rev() {
                let ti = cic_to_flat_expr(ty, w);
                cur = w.add_expr(FlatExpr::lam(0, ti, cur));
            }
            cur
        }
        CicTerm::Fix(_, _) | CicTerm::CoFix(_, _) => {
            // A raw (co)fixpoint that reaches lowering was NOT structuralized
            // into a recursor application — there is no faithful encoding for
            // it. The old behavior (emit a bare lambda) silently produced a
            // WRONG term; instead emit a poison reference to a reserved,
            // never-declared constant so any kernel re-check REJECTS the term
            // (loud failure), never accepts a mistranslation. `import_sexp`
            // pre-checks values and drops such terms loudly before lowering
            // (see `ensure_value_lowerable`), so this arm is a backstop for
            // other callers only.
            let ni = w.add_string("__coq_unsupported__.fix");
            w.add_expr(FlatExpr::const_ref(ni, u32::MAX))
        }
        CicTerm::Proj(name, idx, expr) => {
            let (ni, ei) = (w.add_string(name), cic_to_flat_expr(expr, w));
            // Coq record field counts are tiny; a proj_arg beyond u16 cannot
            // arise from a real record. `min` keeps the cast total and safe:
            // any absurd index resolves out of bounds and the kernel rejects
            // (fail closed), never silently truncating to a valid field.
            let field = u16::try_from(*idx).unwrap_or(u16::MAX);
            w.add_expr(FlatExpr::proj(ni, field, ei))
        }
        CicTerm::Int(n) => w.add_expr(FlatExpr::lit_nat(*n as u64)),
        // A primitive `float` is modeled as the `Nat` of its IEEE-754 f64 bit
        // pattern (matching the kernel's native float reducers), so a `float`
        // constant lowers to that bit pattern — not a placeholder `0`.
        CicTerm::Float(f) => w.add_expr(FlatExpr::lit_nat(f.to_bits())),
    }
}

/// Statistics from a Coq s-expression import.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CoqImportStats {
    pub total: u32,
    pub translated: u32,
    pub axiomatized: u32,
    pub skipped: u32,
    /// Value-bearing constants whose VALUE failed translation and was dropped
    /// (imported type-only, axiomatized and trust-gated). Never silent: each
    /// drop is also recorded in [`Self::value_failure_reasons`].
    pub value_translation_failed: u32,
    /// `(constant name, reason)` for every dropped value.
    pub value_failure_reasons: Vec<(String, String)>,
    /// `(name-or-form, reason)` for every skipped top-level form (type parse
    /// failures, malformed/rejected forms).
    pub skip_reasons: Vec<(String, String)>,
}

/// Verify that a CIC value term contains no raw (co)fixpoint node: those have
/// no faithful lowering (see the poison arm in [`cic_to_flat_expr`]) and must
/// be dropped LOUDLY before lowering.
fn ensure_value_lowerable(term: &CicTerm) -> Result<(), MathverseError> {
    match term {
        CicTerm::Fix(_, _) => Err(coq_err(
            "raw Fix value not structuralized into a recursor application (fail closed)",
        )),
        CicTerm::CoFix(_, _) => Err(coq_err(
            "corecursive CoFix value has no recursor encoding (fail closed)",
        )),
        CicTerm::Prod(_, a, b) | CicTerm::Lambda(_, a, b) => {
            ensure_value_lowerable(a)?;
            ensure_value_lowerable(b)
        }
        CicTerm::LetIn(_, v, t, b) => {
            ensure_value_lowerable(v)?;
            ensure_value_lowerable(t)?;
            ensure_value_lowerable(b)
        }
        CicTerm::App(f, args) => {
            ensure_value_lowerable(f)?;
            args.iter().try_for_each(ensure_value_lowerable)
        }
        CicTerm::Case(case) => {
            case.params.iter().try_for_each(ensure_value_lowerable)?;
            ensure_value_lowerable(&case.motive)?;
            case.branches.iter().try_for_each(ensure_value_lowerable)?;
            ensure_value_lowerable(&case.discriminant)
        }
        CicTerm::StructFix(fix) => {
            fix.params.iter().try_for_each(ensure_value_lowerable)?;
            fix.pre_binders
                .iter()
                .try_for_each(ensure_value_lowerable)?;
            ensure_value_lowerable(&fix.struct_ty)?;
            fix.post_binders
                .iter()
                .try_for_each(ensure_value_lowerable)?;
            fix.indices.iter().try_for_each(ensure_value_lowerable)?;
            ensure_value_lowerable(&fix.motive)?;
            fix.branches.iter().try_for_each(ensure_value_lowerable)
        }
        CicTerm::Proj(_, _, inner) => ensure_value_lowerable(inner),
        CicTerm::Rel(_)
        | CicTerm::Var(_)
        | CicTerm::Sort(_)
        | CicTerm::Const(_)
        | CicTerm::ConstU(_, _)
        | CicTerm::Ind(_, _)
        | CicTerm::Construct(_, _, _)
        | CicTerm::Int(_)
        | CicTerm::Float(_) => Ok(()),
    }
}

/// Extra profile bits for a dropped value, keyed on the failure reason.
///
/// Baseline for EVERY value-translation failure: [`AxiomProfile::SALVAGED_STAND_IN`].
/// A value we could not TRANSLATE (residual `Proj`, indexed-match discriminant
/// unrecoverable, fixed-index promotion, `Case`/`Fix` tail, out-of-model
/// sort, …) is a *reconstruction gap* — Coq's own kernel checked this value,
/// we simply cannot reproduce it in the importer's term model — NOT a
/// value-free Coq `Axiom`/`Parameter`. That is exactly the provenance the
/// dump-side crash-salvage stand-in records, so it carries the same bit.
///
/// WHY IT MATTERS (monotone regression fix): the dropped constant registers
/// TYPE-ONLY (`NO_VALUE`, `AxiomAccepted`). Without this bit it is invisible to
/// the verify-side stand-in classification, so a dependent whose value the
/// kernel rejects while delta-unfolding through this now-value-less body is
/// scored a MASKED-FAILURE taint SEED — and every transitive dependent that
/// only kernel-checks against it is then WITHHELD from `KernelVerified`,
/// cascading a regression. With the bit set the constant joins `standin_names`
/// (`verify::incremental`, the `AxiomAccepted` arm), so such a rejection is
/// classified `STANDIN_BLOCKED` (clean type-only fallback, no taint) and the
/// dependents that genuinely kernel-verify keep their `KernelVerified` verdict
/// — byte-identical to the pre-re-dump baseline where the value never
/// translated at all. The bit is a `NON_AXIOM_HINT`: it changes NO axiom
/// accounting and can never itself mint `KernelVerified` (recons­truction-gap
/// stand-ins are never `KernelVerified`).
///
/// The out-of-model sub-cases additionally gate with `COQ_SPROP` /
/// `UNIVERSE_INCON` so trust gating still records the model boundary.
fn value_failure_profile_bits(reason: &str) -> AxiomProfile {
    let standin = AxiomProfile::SALVAGED_STAND_IN;
    if reason.contains("out-of-model (SProp)") {
        standin | AxiomProfile::COQ_SPROP
    } else if reason.contains("out-of-model (universe)") {
        standin | AxiomProfile::UNIVERSE_INCON
    } else {
        standin
    }
}

/// A constant the SerAPI dumper OMITS from the `.sexp` corpus even though
/// dumped constants reference it — a genuine dumper limitation, not a
/// converter gap. The flagship case is ssrnat's `NatTrec.add`: it is the only
/// `NatTrec` member defined with an in-line `where "n + m" := (add n m)`
/// recursive notation, and the SerAPI dumper drops it, leaving
/// `NatTrec.double` / `add_mul` / `addE` / `doubleE` (31 references across
/// `ssrnat` + `prime`) pointing at a missing constant — the whole tail-
/// recursive nat tower fails to kernel-verify. Because re-dumping the shared
/// corpus is off-limits, the importer RECONSTRUCTS the omitted constant from a
/// faithful reconstruction of its known tail-recursive `Fix`.
///
/// SOUNDNESS. The reconstruction is emitted with the `Speculative` marker so a
/// wrong reconstruction is arbitrated fail-closed by the kernel (a rejected
/// value reverts to a clean value-less type-only axiom — no masked seed, zero
/// regression). More strongly, correctness is *witnessed by an imported proof*:
/// `NatTrec.addE : NatTrec.add =2 addn` is a real dumped Coq proof term, and it
/// only kernel-verifies if the reconstructed `add` reduces exactly as Coq's
/// `add` does. A wrong reconstruction makes `addE` (and the tower above it)
/// fail to verify, so the whole thing fails closed together.
struct OmittedConstant {
    /// Fully-qualified name of the omitted constant.
    full_name: &'static str,
    /// A sibling constant guaranteed co-located in the SAME module file. The
    /// reconstruction is injected only when this anchor is DEFINED in the file,
    /// so it is emitted EXACTLY ONCE (at the omitted constant's home module),
    /// never duplicated across other files that merely reference it (e.g.
    /// `prime` references `NatTrec.add` but does not define `add_mul`, so it
    /// resolves the reconstruction from the dependency-closed shard instead).
    anchor_sibling: &'static str,
    /// The reconstructed `(CoqConstant … Speculative)` form, raw SerAPI dialect.
    synthesized_sexp: &'static str,
}

/// Reconstruction of `mathcomp.ssreflect.ssrnat.NatTrec.add`:
///   `add m n := match m with O => n | S m' => add m' (S n) end`
/// the tail-recursive accumulator addition (`where "n + m" := (add n m)` makes
/// the source `m' + n.+1` mean `add m' n.+1`). Struct-recursive on `m` (arg 0),
/// accumulator `n` varies in the self-call → the general (revapp-shaped)
/// encoder. De Bruijn indices are calibrated against the known-`KernelVerified`
/// twin `Coq.Init.Nat.add` (identical arity, `(Rel 2)` discriminant). Trailing
/// `Speculative` marker makes the row fail-closed (see [`OmittedConstant`]).
const SYNTH_NATTREC_ADD_SEXP: &str = r#"(CoqConstant mathcomp.ssreflect.ssrnat.NatTrec.add (Prod ((binder_name (Name (Id m))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))))) (Fix (((0) 0) ((((binder_name (Name (Id add))) (binder_relevance Relevant))) ((Prod ((binder_name (Name (Id m))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ()))))))) ((Lambda ((binder_name (Name (Id m))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Lambda ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1)) (ci_cstr_nargs (0 1)) (ci_pp_info ((style MatchStyle)))) (Instance (() ())) () (((((binder_name (Name (Id m))) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Rel 1)) ((((binder_name (Name (Id m'))) (binder_relevance Relevant))) (App (Rel 4) ((Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 2) (Instance (() ())))) ((Rel 2)))))))))))))) Speculative)"#;

/// The dumper-omitted constants the importer reconstructs. See
/// [`OmittedConstant`] for the soundness argument.
const OMITTED_CONSTANTS: &[OmittedConstant] = &[OmittedConstant {
    full_name: "mathcomp.ssreflect.ssrnat.NatTrec.add",
    anchor_sibling: "mathcomp.ssreflect.ssrnat.NatTrec.add_mul",
    synthesized_sexp: SYNTH_NATTREC_ADD_SEXP,
}];

/// Name in `items[1]` of a top-level `(CoqConstant/CoqAxiom/CoqInductive …)`.
fn top_level_declared_name(form: &Sexp) -> Option<&str> {
    let Sexp::List(v) = form else { return None };
    let head = match v.first() {
        Some(Sexp::Atom(h)) => h.as_str(),
        _ => return None,
    };
    if head != "CoqConstant" && head != "CoqAxiom" && head != "CoqInductive" {
        return None;
    }
    match v.get(1) {
        Some(Sexp::Atom(name)) => Some(name.as_str()),
        _ => None,
    }
}

/// Collect the fully-qualified names referenced by `(Const …)` nodes anywhere
/// in `form` (a `Const`'s first `KerName` is the referenced constant).
fn collect_const_ref_names(form: &Sexp, out: &mut std::collections::HashSet<String>) {
    if let Sexp::List(v) = form {
        if matches!(v.first(), Some(Sexp::Atom(h)) if h == "Const") {
            if let Some(name) = serapi_qualified_name(form) {
                out.insert(name);
            }
        }
        for child in v {
            collect_const_ref_names(child, out);
        }
    }
}

/// Reconstruct dumper-omitted constants for a single module's parsed forms.
///
/// Returns the synthesized `(CoqConstant … Speculative)` forms the caller
/// appends to the module's stream. A reconstruction is emitted only when its
/// anchor sibling is defined in this file (single-injection guarantee), the
/// omitted name is genuinely referenced here, and it is not already defined —
/// so a future re-dump that restores the constant silently disables recovery.
///
/// The expensive `Const`-reference walk runs ONLY for the handful of files that
/// define an anchor (i.e. ssrnat); every other file pays a single cheap
/// top-level-name scan and returns on the fast path.
fn recover_dumper_omitted_constants(forms: &[Sexp]) -> Vec<Sexp> {
    // Cheap gate: collect only the top-level DECLARED names.
    let mut defined = std::collections::HashSet::new();
    for form in forms {
        if let Some(name) = top_level_declared_name(form) {
            defined.insert(name.to_string());
        }
    }
    let candidates: Vec<&OmittedConstant> = OMITTED_CONSTANTS
        .iter()
        .filter(|om| defined.contains(om.anchor_sibling) && !defined.contains(om.full_name))
        .collect();
    if candidates.is_empty() {
        // Fast path: no anchor present — the historical behavior, no walk.
        return Vec::new();
    }
    // A candidate exists: now (and only now) walk for `Const` references.
    let mut referenced = std::collections::HashSet::new();
    for form in forms {
        collect_const_ref_names(form, &mut referenced);
    }
    candidates
        .into_iter()
        .filter(|om| referenced.contains(om.full_name))
        // Fail closed: an unparsable reconstruction is simply skipped, and the
        // omitted constant stays missing (never a hard error).
        .filter_map(|om| parse_sexp(om.synthesized_sexp).ok())
        .collect()
}

/// Importer for Coq SerAPI s-expression data.
pub struct CoqImporter;

/// Cross-file inductive registry for a multi-module import SESSION.
///
/// [`CoqImporter::import_sexp`]'s normalization context is per call, so a
/// module's `Case`/`Fix` nodes over inductives DECLARED IN ANOTHER MODULE
/// (e.g. `Coq.Init.Peano` matching on `Coq.Init.Datatypes.nat`) fail closed.
/// A directory driver fixes that with two order-independent passes:
///
/// 1. call [`CoqImporter::register_inductive_forms`] on EVERY file, which
///    registers only the `(CoqInductive ...)` metadata (arity, `NumParams`,
///    constructor types) — normalized by exactly the same code path the
///    same-file import uses;
/// 2. import each file with [`CoqImporter::import_sexp_with_registry`], which
///    seeds its per-file context from this registry (the file's own forms
///    still register on top).
///
/// An empty registry reproduces the historical single-file behavior exactly.
#[derive(Clone, Debug, Default)]
pub struct CoqSessionRegistry {
    ctx: SerapiNormCtx,
}

impl CoqSessionRegistry {
    /// Number of registered inductives.
    #[must_use]
    pub fn len(&self) -> usize {
        self.ctx.inductives.len()
    }

    /// Whether the registry holds no inductives.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.ctx.inductives.is_empty()
    }

    /// Install the solved global universe re-leveling map (see
    /// [`super::universe_releveling`]). Every file imported with this
    /// registry then renders each RAISED named level at its solved base —
    /// one uid, one base, everywhere — with raised-rendering declarations
    /// marked `SPECULATIVE_MOTIVE` (kernel-arbitrated fail-closed). An
    /// empty map leaves the historical collapse untouched.
    pub fn install_universe_bases(&mut self, bases: super::universe_releveling::UniverseBaseMap) {
        self.ctx.universe_bases = std::sync::Arc::new(bases);
    }
}

impl CoqImporter {
    /// Registration-only pass over `data`'s top-level forms: register every
    /// well-formed `(CoqInductive ...)` form's metadata into `registry`,
    /// writing NOTHING. Malformed or out-of-model inductive forms are simply
    /// not registered here — the import pass over the same file counts and
    /// reasons them (so nothing is silently lost), and `Case`s on an
    /// unregistered inductive keep failing closed.
    ///
    /// Returns the number of inductives registered from `data`. Errors only
    /// when the top-level s-expression stream itself does not parse.
    pub fn register_inductive_forms(
        &self,
        data: &str,
        registry: &mut CoqSessionRegistry,
    ) -> MathverseResult<u32> {
        let sexps = parse_sexps(data).map_err(|e| coq_err(&e.to_string()))?;
        let mut registered = 0u32;
        for sexp in &sexps {
            let Sexp::List(items) = sexp else { continue };
            if !matches!(items.first(), Some(Sexp::Atom(h)) if h == "CoqInductive") {
                continue;
            }
            if let Ok(parsed) = parse_serapi_inductive(items, &registry.ctx) {
                parsed.register_into(&mut registry.ctx);
                registered += 1;
            }
        }
        // Also register the coinductive TYPES the dumper axiomatized as
        // `(CoqAxiom <base>.<N> …)` type-former + constructor triples (Streams
        // `Stream`/`EqSt`/`ForAll`), reconstructed here into the same inductive
        // shape a `CoqInductive` would register — so a `Case` OBSERVATION on the
        // coinductive (in this or another module) resolves against a real
        // recursor while its productive CoFix values stay out of model. See
        // `reconstruct_coinductive_inductives`.
        let (synth_forms, _) = reconstruct_coinductive_inductives(&sexps, &registry.ctx);
        for form in &synth_forms {
            let Sexp::List(items) = form else { continue };
            if let Ok(parsed) = parse_serapi_inductive(items, &registry.ctx) {
                parsed.register_into(&mut registry.ctx);
                registered += 1;
            }
        }
        Ok(registered)
    }

    /// Registration-only pass over `data`'s top-level forms: register every
    /// well-formed `(CoqConstant ...)` / `(CoqAxiom ...)` whose type CODOMAIN is
    /// a sort (a type former `R : Set`, relation `Rle : R → R → Prop`, or
    /// predicate) into `registry`'s constant result-sort map, writing NOTHING.
    /// Lets a `match` in ANOTHER module whose return predicate is headed by this
    /// constant derive its recursor motive universe (see
    /// [`motive_result_level`]) — the cross-file analogue of
    /// [`Self::register_inductive_forms`]. Constants whose type does not end in a
    /// sort are skipped (they cannot head a motive result type). Returns the
    /// number registered. Errors only when the top-level stream does not parse.
    pub fn register_constant_shapes(
        &self,
        data: &str,
        registry: &mut CoqSessionRegistry,
    ) -> MathverseResult<u32> {
        let sexps = parse_sexps(data).map_err(|e| coq_err(&e.to_string()))?;
        let mut registered = 0u32;
        for sexp in &sexps {
            let Sexp::List(items) = sexp else { continue };
            let is_const_or_axiom = matches!(
                items.first(),
                Some(Sexp::Atom(h)) if h == "CoqConstant" || h == "CoqAxiom"
            );
            if !is_const_or_axiom || items.len() < 3 {
                continue;
            }
            let Sexp::Atom(name) = &items[1] else {
                continue;
            };
            let type_sexp = normalize_if_serapi_ctx(&items[2], &registry.ctx);
            if let Some(sort) = dialect_sort_of(dialect_prod_codomain(&type_sexp)) {
                registry
                    .ctx
                    .register_const_sort(name, dialect_count_prods(&type_sexp), sort);
                registered += 1;
            }
            // Cross-file inductive-valued constant types (`leb : nat → nat →
            // bool`): register so a match in ANOTHER module on a compound
            // `Const`-headed discriminant can synthesize its type.
            registry.ctx.register_const_type(name, &type_sexp);
            registry.ctx.register_known_name(name);
            // A `CoqAxiom` form's optional 4th element is the dump-salvage
            // `StandIn` marker atom, never a value — exclude it from the
            // value-shape registrations below.
            let value_item = if matches!(items.first(), Some(Sexp::Atom(h)) if h == "CoqAxiom") {
                None
            } else {
                items.get(3)
            };
            // Cross-file relation-definition abbreviations (`lt := λn m. le
            // (S n) m`): register the value so a match in ANOTHER module on a
            // `lt`-typed discriminant can delta-unfold to the inductive.
            if let Some(value) = value_item {
                let value_sexp = normalize_if_serapi_ctx(value, &registry.ctx);
                if dialect_relation_def_body(&value_sexp) {
                    registry.ctx.register_relation_def(name, value_sexp);
                } else if dialect_const_def_body(&value_sexp) {
                    // A `Π`-bearing type-former abbreviation (`Equality.axiom`):
                    // register its body so a reflection lemma's `Const`-headed
                    // discriminant type can delta-unfold to the `reflect`
                    // inductive (see `synthesize_app_disc_type`).
                    registry.ctx.register_const_def(name, value_sexp);
                } else if let Ok(c) = sexp_to_cic(&value_sexp) {
                    // Cross-file TYPE-SYNONYM bodies (`Ensemble := λU. U → Prop`
                    // in Coq.Sets.Ensembles, used by Coq.Sets.Image's `Im`): seed
                    // the sexp synonym registry so a DIFFERENT module's inductive
                    // arity ending in the synonym unfolds in its Case/Fix
                    // registry (the index hidden behind the synonym is counted).
                    // Sexp-only: the CIC synonym registry stays unseeded so
                    // `arity_cic` (the shard declaration) is byte-identical to
                    // today; the kernel δ-reduces the folded codomain itself.
                    if type_synonym_body(&c).is_some() {
                        registry
                            .ctx
                            .register_type_synonym_sexp(name, value_sexp.clone());
                    }
                }
            }
            // Cross-file SORT-POLYMORPHIC constants (`ssr_have_upoly`):
            // register the fused quality+level shape derived from the RAW
            // sexp — the same derivation the import loop keys its poly
            // emission on (decl-consistency) — so a reference in ANOTHER
            // module translates its fully-quality-specialized instance into
            // the constant's explicit `level_params` levels.
            if let Some(shape) = derive_sort_poly_shape(&items[2], value_item) {
                registry.ctx.register_poly_const(name, shape);
            }
        }
        Ok(registered)
    }

    /// Import constants from SerAPI s-expression data with an EMPTY session
    /// registry (single-file behavior; the file's own `(CoqInductive ...)`
    /// forms still register for its own `Case`/`Fix` reconstruction).
    /// Expects top-level forms: `(CoqConstant name type [value])`,
    /// `(CoqAxiom name type)`, or
    /// `(CoqInductive name block-idx arity (Ctor cname ctype)...)`.
    pub fn import_sexp(
        &self,
        data: &str,
        writer: &mut ShardWriter,
    ) -> MathverseResult<CoqImportStats> {
        self.import_sexp_with_registry(data, &CoqSessionRegistry::default(), writer)
    }

    /// [`Self::import_sexp`] seeded with a cross-file session `registry`
    /// (see [`CoqSessionRegistry`]): `Case`/`Fix` reconstruction can resolve
    /// inductives declared in OTHER modules of the session. The registry is
    /// read-only here; the file's own forms register into a per-file copy.
    pub fn import_sexp_with_registry(
        &self,
        data: &str,
        registry: &CoqSessionRegistry,
        writer: &mut ShardWriter,
    ) -> MathverseResult<CoqImportStats> {
        self.import_sexp_with_registry_and_standins(
            data,
            registry,
            &std::collections::HashSet::new(),
            writer,
        )
    }

    /// [`Self::import_sexp_with_registry`] with a LEGACY dump-salvage set:
    /// `salvaged_standins` names constants the dumper's crash-salvage rungs
    /// recorded in the module's `.meta.json` sidecar notes (dumps predating
    /// the inline `(CoqAxiom … StandIn)` marker carry the evidence only
    /// there — see `structured_import::salvaged_standin_names_from_meta`).
    /// A `CoqAxiom` row whose name is in the set (or that carries the inline
    /// marker) is profiled [`AxiomProfile::SALVAGED_STAND_IN`]: a value-less
    /// stand-in for a declaration Coq's kernel checked a value/structure for,
    /// consumed by the verify-side stand-in-blocked rejection classification.
    /// The bit is set ONLY on the `CoqAxiom` arm — a name that imported as a
    /// real `CoqConstant`/`CoqInductive` (e.g. reconstructed-from-parts after
    /// its salvage note was written) never carries it.
    pub fn import_sexp_with_registry_and_standins(
        &self,
        data: &str,
        registry: &CoqSessionRegistry,
        salvaged_standins: &std::collections::HashSet<String>,
        writer: &mut ShardWriter,
    ) -> MathverseResult<CoqImportStats> {
        let sexps = parse_sexps(data).map_err(|e| coq_err(&e.to_string()))?;
        // Reconstruct any dumper-OMITTED constants this module references but
        // that the SerAPI dumper never emitted (e.g. ssrnat's `NatTrec.add`,
        // dropped because of its in-line `where` recursive notation). Emitted
        // fail-closed (`Speculative`) and APPENDED after the module's own forms:
        // the reconstruction's `Fix` needs its argument inductives registered
        // (`nat`), which the in-order pass has done by the end of the file,
        // while its consumers reference it only by NAME (no ctx dependency) and
        // the corpus verifier resolves declarations dependency-closed regardless
        // of shard order. An empty result is exactly the historical path.
        let sexps = {
            let recovered = recover_dumper_omitted_constants(&sexps);
            if recovered.is_empty() {
                sexps
            } else {
                let mut merged = sexps;
                merged.extend(recovered);
                merged
            }
        };
        let mut stats = CoqImportStats::default();
        let mut ctx = registry.ctx.clone();
        // Coinductive TYPE reconstruction (see
        // `reconstruct_coinductive_inductives`): the dumper axiomatizes each
        // CoFinite block as a `(CoqAxiom <base>.<N> …)` type-former +
        // constructor triple. Emit the reconstructed `(CoqInductive …)` at the
        // type former's position (so its ctor-referenced constants — `EqSt`'s
        // `hd`/`tl` — are already in scope) and skip the absorbed constructor
        // axioms. A failed replay falls back to the arity stand-in axiom the
        // block already carried, so this is add-only and never regresses.
        let (coind_forms, coind_consumed_ctors) = reconstruct_coinductive_inductives(&sexps, &ctx);
        let coind_by_former: std::collections::HashMap<String, &Sexp> = coind_forms
            .iter()
            .filter_map(|f| coinductive_form_former_name(f).map(|n| (n, f)))
            .collect();
        for sexp in &sexps {
            stats.total += 1;
            // The per-decl sort-poly shape must never leak across forms: a
            // stale pairing would let an UNRELATED decl's `QSort` rewrite
            // against the wrong binders. Cleared here; set per-constant below.
            ctx.current_poly = None;
            let skip = |stats: &mut CoqImportStats, name: &str, reason: String| {
                stats.skipped += 1;
                stats.skip_reasons.push((name.to_string(), reason));
            };
            let items = match sexp {
                Sexp::List(v) if !v.is_empty() => v,
                _ => {
                    skip(&mut stats, "<form>", "not a non-empty list".to_string());
                    continue;
                }
            };
            let head = match &items[0] {
                Sexp::Atom(s) => s.as_str(),
                _ => {
                    skip(&mut stats, "<form>", "form head is not an atom".to_string());
                    continue;
                }
            };
            // Top-level inductive form: import the inductive type plus all its
            // constructors as a checked inductive family the corpus verifier can
            // replay through `Environment::add_inductive`.
            if head == "CoqInductive" {
                let name_hint = match items.get(1) {
                    Some(Sexp::Atom(s)) => s.clone(),
                    _ => "<inductive>".to_string(),
                };
                match import_serapi_inductive(items, writer, &mut ctx) {
                    Ok(decl_count) => stats.translated += decl_count,
                    Err(e) => skip(&mut stats, &name_hint, e.to_string()),
                }
                continue;
            }
            // Mutual inductive blocks must go through the family export path
            // (all_names header); importing members as independent inductives
            // would be unsound. Fail closed and COUNT it.
            if head == "CoqMutual" {
                skip(
                    &mut stats,
                    "<CoqMutual>",
                    "mutual inductive blocks unsupported: family all_names \
                     header import required (rejected, not split)"
                        .to_string(),
                );
                continue;
            }
            let is_axiom = match head {
                "CoqConstant" => false,
                "CoqAxiom" => true,
                _ => {
                    skip(&mut stats, head, "unknown top-level form".to_string());
                    continue;
                }
            };
            if items.len() < 3 {
                skip(&mut stats, head, "form is missing name or type".to_string());
                continue;
            }
            let name = match &items[1] {
                Sexp::Atom(s) => s.clone(),
                _ => {
                    skip(&mut stats, head, "constant name is not an atom".to_string());
                    continue;
                }
            };
            // Coinductive TYPE reconstruction: a `CoqAxiom` type former is
            // re-emitted as the reconstructed `(CoqInductive …)` here (its
            // constructor axioms are absorbed and skipped). Everything else
            // (real axioms, constants) flows through unchanged.
            if is_axiom {
                if let Some(form) = coind_by_former.get(&name) {
                    if let Sexp::List(form_items) = form {
                        match import_serapi_inductive(form_items, writer, &mut ctx) {
                            Ok(decl_count) => stats.translated += decl_count,
                            Err(e) => skip(&mut stats, &name, e.to_string()),
                        }
                    }
                    continue;
                }
                if coind_consumed_ctors.contains(&name) {
                    // Absorbed into the reconstructed inductive emitted at its
                    // type former's position — not a separate declaration.
                    continue;
                }
            }
            // Reset the speculative-conversion flag for THIS constant BEFORE the
            // type is normalized: a speculative shape (derived recursor motive
            // universe, dropped `Set`-specialized universe instance) can appear
            // in the TYPE as well as the value, and both must mark the constant
            // so verify fails closed on a kernel rejection (see
            // `SPECULATIVE_MOTIVE_USED`). Read once after the value is converted.
            SPECULATIVE_MOTIVE_USED.with(|c| c.set(false));
            // Dump-salvage stand-in marker: `(CoqAxiom <name> <type> StandIn)`.
            // Emitted by the dumper's crash-salvage rungs so the importer can
            // profile the row `AxiomProfile::SALVAGED_STAND_IN` (a value-less
            // stand-in for a declaration Coq's kernel checked a value for);
            // legacy dumps carry the same evidence in `.meta.json` sidecar
            // notes (`salvaged_standins`). The marker atom is NEVER a value:
            // it is excluded from every value-shape derivation below.
            let inline_standin =
                is_axiom && matches!(items.get(3), Some(Sexp::Atom(a)) if a == "StandIn");
            // Instantiated-module (functor-application) member marker:
            // `(CoqConstant <name> <type> <value> Speculative)` (see
            // `emit::render_constant_speculative`). The dumper's
            // functor-enumeration prong tags every enumerated member so a value
            // the Clean kernel cannot reduce through the functor instantiation
            // is arbitrated fail-closed: the row is forced
            // `AxiomProfile::SPECULATIVE_MOTIVE`, so the verify side reverts a
            // KERNEL-rejected value to a CLEAN value-less type-only axiom (no
            // masked-failure taint; joins the stand-in set) instead of a masked
            // seed. The marker atom is NEVER a value — the value stays
            // `items[3]`, so every value-shape derivation below is unaffected
            // and the ~22 members that already verify KV keep verifying KV
            // (SPECULATIVE_MOTIVE is irrelevant to the kernel on acceptance).
            let inline_speculative =
                !is_axiom && matches!(items.get(4), Some(Sexp::Atom(a)) if a == "Speculative");
            let value_item = if is_axiom { None } else { items.get(3) };
            // SORT-POLYMORPHISM pre-scan (the `ssr_have_upoly` class): derive
            // the decl's fused quality+level pairing from the RAW sexp. When
            // it qualifies, the Sort arm below rewrites its `QSort` payloads
            // to `(Sort (Param u<q>))` and the decl is emitted with a real
            // `level_params` window; references translate their instances
            // against the registered shape (`translate_poly_ref_instance`).
            // Everything is kernel-arbitrated fail-closed via the speculative
            // marker, and an unqualified decl keeps today's behavior exactly.
            let poly_shape = derive_sort_poly_shape(&items[2], value_item);
            ctx.current_poly = poly_shape.clone();
            // Pre-normalize raw SerAPI `Constr` shapes into the importer's CIC
            // dialect; importer-dialect nodes pass through unchanged.
            let type_sexp = normalize_if_serapi_ctx(&items[2], &ctx);
            let type_cic = match sexp_to_cic(&type_sexp).and_then(|c| {
                ensure_value_lowerable(&c)?;
                Ok(c)
            }) {
                Ok(c) => c,
                Err(e) => {
                    // Type out-of-model → the whole constant is skipped
                    // (a typeless constant cannot be written), with reason.
                    skip(&mut stats, &name, format!("type: {e}"));
                    continue;
                }
            };
            // Register this constant's result-sort shape (if its type ends in a
            // sort) so a later match whose return predicate is headed by this
            // constant can derive its recursor motive universe (see
            // `motive_result_level`). Dependency order makes it visible in time;
            // a wrong derivation is caught by the kernel re-check (fail closed).
            // SORT-POLY decls are excluded from these registries (their dialect
            // shapes carry `Param` sorts the concrete-level consumers must
            // never see — today such decls registered nothing, because their
            // types failed normalization before reaching here).
            if poly_shape.is_none() {
                if let Some(sort) = dialect_sort_of(dialect_prod_codomain(&type_sexp)) {
                    ctx.register_const_sort(&name, dialect_count_prods(&type_sexp), sort);
                }
                // Register an inductive-valued constant type (`leb : nat → nat →
                // bool`) so a later compound `Const`-headed match discriminant can
                // synthesize its type (see `synthesize_app_disc_type`).
                ctx.register_const_type(&name, &type_sexp);
                ctx.register_known_name(&name);
            }
            let type_idx = cic_to_flat_expr(&type_cic, writer);
            // Value-bearing TRANSLATED definitions carry no axiom-profile bits
            // at import (the corpus verifier and later trust stamping decide);
            // axioms and valueless constants keep the honest
            // AXIOMATIZED|BRIDGE_AXIOM profile plus name-keyed bits.
            let (value_idx, confidence, profile) = if let Some(native) =
                coq_primitive_carrier_native(&name)
            {
                // A Coq machine-primitive carrier (`PrimFloat.float`,
                // `PrimInt63.int`) is opaque in Coq's kernel but modeled in
                // Clean's kernel as `Nat` (native floats are `Nat` bit patterns;
                // int values are `Nat`s). Import it as the DEFINITION
                // `carrier := Nat` (not an opaque axiom) so its primitive VALUE
                // constants (`zero`, `one`, `max_int`), lowered to `Nat`
                // literals, kernel-verify against the carrier instead of masking
                // — un-tainting their dependents. The kernel re-checks (fail
                // closed): a carrier whose Coq sort disagrees with the native
                // model is simply rejected.
                (
                    cic_to_flat_expr(&CicTerm::Const(native.to_string()), writer),
                    ImportConfidence::Translated,
                    AxiomProfile::NONE,
                )
            } else if is_axiom {
                // Dump-salvage stand-in rows additionally carry the
                // SALVAGED_STAND_IN provenance hint (inline marker or legacy
                // sidecar-note evidence): their value-less-ness is a
                // reconstruction gap, not a value-free Coq axiom.
                let standin_hint = if inline_standin || salvaged_standins.contains(&name) {
                    AxiomProfile::SALVAGED_STAND_IN
                } else {
                    AxiomProfile::NONE
                };
                (
                    NO_VALUE,
                    ImportConfidence::Axiomatized,
                    compute_coq_axiom_profile(&name) | AxiomProfile::AXIOMATIZED | standin_hint,
                )
            } else if items.len() > 3 {
                // The speculative-conversion flag was reset before the type was
                // normalized (above); do NOT reset it again here, so a speculative
                // shape appearing in the TYPE still marks this constant. A
                // Const-headed recursor motive / dropped universe instance derived
                // during THIS value's conversion also sets it.
                let value_sexp = normalize_if_serapi_ctx(&items[3], &ctx);
                // Register relation-definition abbreviations (`lt := λn m. le
                // (S n) m`) so a later match whose discriminant type is such an
                // abbreviation can delta-unfold to the inductive it heads. In-file
                // order makes the definition visible to its later users.
                // (Sort-poly decls excluded — see the type-side registries.)
                if poly_shape.is_none() && dialect_relation_def_body(&value_sexp) {
                    ctx.register_relation_def(&name, value_sexp.clone());
                } else if poly_shape.is_none() && dialect_const_def_body(&value_sexp) {
                    // A `Π`-bearing type-former abbreviation (`Equality.axiom :=
                    // λT e. ∀ x y, reflect …`): register its body so a later
                    // reflection lemma's `Const`-headed discriminant type can
                    // delta-unfold to the inductive (see
                    // `synthesize_app_disc_type`).
                    ctx.register_const_def(&name, value_sexp.clone());
                }
                let value_result = sexp_to_cic(&value_sexp).and_then(|c| {
                    ensure_value_lowerable(&c)?;
                    Ok(c)
                });
                let speculative = SPECULATIVE_MOTIVE_USED.with(|c| c.get());
                match value_result {
                    Ok(c) => {
                        let idx = cic_to_flat_expr(&c, writer);
                        // Register type-synonym definitions (`Ensemble := λU.
                        // U → Prop`) so a later inductive arity ending in
                        // `Ensemble U` can be delta-unfolded to a sort. In-file
                        // order (definition before its inductive users) makes
                        // the synonym visible when the inductive is parsed.
                        // (Sort-poly decls excluded — their bodies carry
                        // `Param` sorts the synonym unfolder must never leak.)
                        if poly_shape.is_none() && type_synonym_body(&c).is_some() {
                            ctx.register_type_synonym(&name, c, value_sexp.clone());
                        }
                        // Mark a value built with a derived (guessed) recursor
                        // motive universe — OR one the dumper flagged as a
                        // functor-generated instantiated-module member (the
                        // inline `Speculative` marker) — so verify fails closed
                        // on rejection (clean type-only axiom, never masked
                        // taint).
                        let profile = if speculative || inline_speculative {
                            AxiomProfile::SPECULATIVE_MOTIVE
                        } else {
                            AxiomProfile::NONE
                        };
                        (idx, ImportConfidence::Translated, profile)
                    }
                    Err(e) => {
                        // NEVER silently axiomatize a value-bearing decl:
                        // fail closed, COUNT it, record the reason, and
                        // trust-gate the constant.
                        let reason = e.to_string();
                        let extra = value_failure_profile_bits(&reason);
                        stats.value_translation_failed += 1;
                        stats.value_failure_reasons.push((name.clone(), reason));
                        (
                            NO_VALUE,
                            ImportConfidence::Axiomatized,
                            compute_coq_axiom_profile(&name) | AxiomProfile::AXIOMATIZED | extra,
                        )
                    }
                }
            } else {
                (
                    NO_VALUE,
                    ImportConfidence::Axiomatized,
                    compute_coq_axiom_profile(&name) | AxiomProfile::AXIOMATIZED,
                )
            };
            let name_idx = writer.add_string(&name);
            // A declaration is a `Definition` iff it carries a value body. Every
            // opaque axiom (and every value-translation failure) already lands
            // here with `value_idx == NO_VALUE`, so keying purely on the value
            // is equivalent to the old `is_axiom || …` for those paths — but it
            // also lets a `CoqAxiom` that we deliberately re-home to a modeled
            // body (primitive carriers, `carrier := Nat`) register as the
            // transparent `Definition` it now is, so its `Nat`-literal value
            // constants can delta-unfold the carrier and kernel-verify.
            let dk = if value_idx == NO_VALUE {
                DeclKind::Axiom
            } else {
                DeclKind::Definition
            };
            // A sort-polymorphic decl binds its fused `Param` levels in the
            // header's `level_params` window. The names MUST be a CONTIGUOUS
            // string-table block (`add_string_block`, never the deduplicating
            // `add_string` — the reader reconstructs `[start .. start+count)`
            // consecutive slots; see `intern_level_params_legacy` and the
            // Lean4 lane's `add_level_param_block` for the full rationale).
            // Register the shape so later references translate their
            // instances against it (decl-consistency).
            let (level_params_start, level_params_count) = match poly_shape {
                Some(shape) => {
                    let names = shape.param_names();
                    let refs: Vec<&str> = names.iter().map(String::as_str).collect();
                    let window = (writer.add_string_block(&refs), names.len() as u16);
                    ctx.register_poly_const(&name, shape);
                    window
                }
                None => (0, 0),
            };
            writer.add_constant(MathverseConstantHeader {
                name_idx,
                type_idx,
                value_idx,
                source_system: SourceSystem::Coq as u8,
                import_confidence: confidence as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: dk as u8,
                axiom_profile: profile,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start,
                level_params_count,
                _pad2: [0u8; 26],
            });
            match confidence {
                ImportConfidence::Translated => stats.translated += 1,
                _ => stats.axiomatized += 1,
            }
        }
        Ok(stats)
    }
}

/// Import a top-level `(CoqInductive <name> <block-idx> <arity> (Ctor <cname>
/// <ctype>)...)` form into shard constants the corpus verifier replays through
/// the kernel's `Environment::add_inductive`.
///
/// The constant names are chosen so a dependent term that references the type
/// via SerAPI `(Ind name i)` or a constructor via `(Construct name i j)`
/// resolves: those lower (in [`cic_to_flat_expr`]) to `name.i` and
/// `name.i.(j-1)` respectively, so the inductive constant is named `name.i` and
/// constructor `k` is named `name.i.k`. The inductive type carries
/// `NO_VALUE` but is tagged `DeclKind::Inductive` (with explicit `num_params`
/// metadata) so add_inductive replay fires; each constructor is tagged
/// `DeclKind::Constructor` with its real type. Every type s-expression is run
/// through [`normalize_if_serapi_ctx`] so SerAPI-native constructor/arity payloads
/// are accepted verbatim.
///
/// Returns the number of declarations written (1 inductive + N constructors).
/// Split the tail of a `(CoqInductive ...)` form (everything after the arity)
/// into the inductive's parameter count and the remaining constructor entries.
///
/// The tail may optionally start with a `(NumParams k)` element carrying the
/// number of leading parameters of a PARAMETERIZED inductive (e.g. `1` for
/// `eq : forall A:Type, A -> A -> Prop`). When that element is absent the count
/// defaults to `0`, preserving the prior non-parameterized behaviour. Returns
/// the parsed count plus a slice of the still-to-parse `(Ctor ...)` entries.
fn parse_inductive_num_params(tail: &[Sexp]) -> MathverseResult<(u32, &[Sexp])> {
    if let Some(Sexp::List(first)) = tail.first() {
        if matches!(first.first(), Some(Sexp::Atom(h)) if h == "NumParams") {
            let n = match first.get(1) {
                Some(Sexp::Atom(s)) => s
                    .parse::<u32>()
                    .map_err(|_| coq_err("CoqInductive: NumParams must be a u32"))?,
                _ => return Err(coq_err("CoqInductive: NumParams expects a count")),
            };
            return Ok((n, &tail[1..]));
        }
    }
    Ok((0, tail))
}

/// A `(CoqInductive ...)` form parsed and normalized, shared by the
/// registration-only pass ([`CoqImporter::register_inductive_forms`]) and the
/// full shard import ([`import_serapi_inductive`]) so BOTH paths run raw
/// SerAPI payloads through the same [`normalize_if_serapi_ctx`] pipeline —
/// a registered constructor type from another file is byte-identical to what
/// the same-file path would have registered.
struct ParsedSerapiInductive {
    ind_name: String,
    block_idx: u32,
    num_params: u32,
    arity_sexp: Sexp,
    arity_cic: CicTerm,
    /// `(shard constant name, ctor CIC type)` per constructor, in order.
    ctors: Vec<(String, CicTerm)>,
    ctor_type_sexps: Vec<Sexp>,
    /// Per constructor: the raw LetIn-laced telescope info recorded when the
    /// type was zeta-reduced at parse time (see
    /// [`SerapiIndInfo::ctor_raw_lets`]); `None` for pure-Prod telescopes.
    ctor_raw_lets: Vec<Option<(Sexp, Vec<bool>)>>,
    /// The registry `arity_sexp` was δ-unfolded from a type-synonym codomain
    /// (see [`SerapiIndInfo::arity_synonym_unfolded`]).
    arity_synonym_unfolded: bool,
}

impl ParsedSerapiInductive {
    /// Register this inductive's shape for `Case`/`Fix` reconstruction.
    fn register_into(&self, ctx: &mut SerapiNormCtx) {
        ctx.register_with_lets(
            &self.ind_name,
            self.block_idx,
            self.num_params,
            &self.arity_sexp,
            &self.ctor_type_sexps,
            &self.ctor_raw_lets,
        );
        if self.arity_synonym_unfolded {
            ctx.mark_arity_synonym_unfolded(&self.ind_name, self.block_idx);
        }
        // Inductive BASE names arbitrate KerPair Dual resolution for
        // `Ind`/`Construct` references (see `resolve_kerpair_name`).
        ctx.register_known_name(&self.ind_name);
    }
}

/// Shift the FREE de Bruijn variables of `t` (those `≥ cutoff`) up by `n`.
/// Standard capture-avoiding lift; binders raise the cutoff. `Rel` is 0-based
/// (innermost binder = 0), matching the importer's normalized dialect.
fn cic_lift(t: &CicTerm, n: u32, cutoff: u32) -> CicTerm {
    if n == 0 {
        return t.clone();
    }
    match t {
        CicTerm::Rel(r) => CicTerm::Rel(if *r >= cutoff { *r + n } else { *r }),
        CicTerm::Prod(nm, a, b) => CicTerm::Prod(
            nm.clone(),
            Box::new(cic_lift(a, n, cutoff)),
            Box::new(cic_lift(b, n, cutoff + 1)),
        ),
        CicTerm::Lambda(nm, a, b) => CicTerm::Lambda(
            nm.clone(),
            Box::new(cic_lift(a, n, cutoff)),
            Box::new(cic_lift(b, n, cutoff + 1)),
        ),
        CicTerm::App(h, xs) => CicTerm::App(
            Box::new(cic_lift(h, n, cutoff)),
            xs.iter().map(|x| cic_lift(x, n, cutoff)).collect(),
        ),
        // Leaves / no-binder nodes: nothing to shift below here. Type-synonym
        // bodies never contain the binder-bearing complex nodes (LetIn, Case,
        // Fix, …) — `type_synonym_body` rejects them — so cloning is exact for
        // every term this function is actually invoked on.
        other => other.clone(),
    }
}

/// β-reduce `(λ…. f) args…`: peel up to `args.len()` leading `λ`s of `f`,
/// substitute the peeled binders, and re-apply any leftover arguments. `f` need
/// not have as many `λ`s as there are args (an under-applied synonym just keeps
/// the residual application).
fn cic_beta_apply(f: &CicTerm, args: &[CicTerm]) -> CicTerm {
    let mut inner = f;
    let mut peeled = 0usize;
    while peeled < args.len() {
        if let CicTerm::Lambda(_, _, b) = inner {
            inner = b;
            peeled += 1;
        } else {
            break;
        }
    }
    let substituted = cic_subst_top(inner, &args[..peeled]);
    if peeled < args.len() {
        CicTerm::App(Box::new(substituted), args[peeled..].to_vec())
    } else {
        substituted
    }
}

/// β-substitute `args` (in application order) for the outermost `args.len()`
/// binders of an ALREADY-PEELED `body`. `Rel(0)` in `body` is the innermost
/// (last-applied) binder, so it maps to `args.last()`. Free variables of `body`
/// beyond the peeled binders drop by `args.len()`; each substituted argument is
/// lifted to the depth at which it lands.
fn cic_subst_top(body: &CicTerm, args: &[CicTerm]) -> CicTerm {
    fn go(t: &CicTerm, depth: u32, args: &[CicTerm]) -> CicTerm {
        let k = args.len() as u32;
        match t {
            CicTerm::Rel(r) => {
                let r = *r;
                if r < depth {
                    CicTerm::Rel(r) // bound within `body`'s own binders
                } else if r < depth + k {
                    // r - depth: 0 = innermost peeled binder = last arg.
                    let arg = &args[(k - 1 - (r - depth)) as usize];
                    cic_lift(arg, depth, 0)
                } else {
                    CicTerm::Rel(r - k) // free beyond the peeled binders
                }
            }
            CicTerm::Prod(nm, a, b) => CicTerm::Prod(
                nm.clone(),
                Box::new(go(a, depth, args)),
                Box::new(go(b, depth + 1, args)),
            ),
            CicTerm::Lambda(nm, a, b) => CicTerm::Lambda(
                nm.clone(),
                Box::new(go(a, depth, args)),
                Box::new(go(b, depth + 1, args)),
            ),
            CicTerm::App(h, xs) => CicTerm::App(
                Box::new(go(h, depth, args)),
                xs.iter().map(|x| go(x, depth, args)).collect(),
            ),
            other => other.clone(),
        }
    }
    go(body, 0, args)
}

/// If `value` is a TYPE SYNONYM — a `λ`-telescope whose body is a `Π`-telescope
/// ending in a `Sort`, built only from the simple type-forming nodes
/// (`Rel`/`Sort`/`Const`/`Ind`/`App`/`Prod`/`Lambda`) — return it for
/// registration. Anything else (a value with `LetIn`/`Case`/`Fix`/`Proj`/…,
/// or not ending in a sort) returns `None`, so only genuine type aliases like
/// `Ensemble := λU. U → Prop` are stored for arity delta-unfolding.
fn type_synonym_body(value: &CicTerm) -> Option<&CicTerm> {
    fn is_simple(t: &CicTerm) -> bool {
        match t {
            CicTerm::Rel(_) | CicTerm::Sort(_) | CicTerm::Const(_) | CicTerm::Ind(_, _) => true,
            CicTerm::App(h, xs) => is_simple(h) && xs.iter().all(is_simple),
            CicTerm::Prod(_, a, b) | CicTerm::Lambda(_, a, b) => is_simple(a) && is_simple(b),
            _ => false,
        }
    }
    // Peel λ then Π; the final codomain must be a Sort.
    let mut cur = value;
    while let CicTerm::Lambda(_, _, b) = cur {
        cur = b;
    }
    let mut cod = cur;
    while let CicTerm::Prod(_, _, b) = cod {
        cod = b;
    }
    if matches!(cod, CicTerm::Sort(_)) && is_simple(value) {
        Some(value)
    } else {
        None
    }
}

/// Delta-unfold an inductive `arity` whose codomain (after its own parameter /
/// index `Π`s) is a registered type synonym applied to arguments — e.g.
/// `∀U, Ensemble U` with `Ensemble := λU. U → Prop` becomes `∀U, U → Prop`,
/// which ENDS IN A SORT and so passes the kernel's `add_inductive` arity check.
/// Returns `Some(rewritten)` when an unfold happened, `None` otherwise (leaving
/// every non-synonym-codomain inductive — i.e. all currently-verifying ones —
/// byte-identical). At most a few unfolds; the kernel re-checks the result.
fn unfold_arity_synonym_codomain(arity: &CicTerm, ctx: &SerapiNormCtx) -> Option<CicTerm> {
    // Split leading Πs (the declared parameter+index telescope) from the codomain.
    fn rebuild(binders: &[(String, CicTerm)], cod: CicTerm) -> CicTerm {
        let mut acc = cod;
        for (nm, dom) in binders.iter().rev() {
            acc = CicTerm::Prod(nm.clone(), Box::new(dom.clone()), Box::new(acc));
        }
        acc
    }
    let mut binders: Vec<(String, CicTerm)> = Vec::new();
    let mut cod = arity;
    while let CicTerm::Prod(nm, dom, b) = cod {
        binders.push((nm.clone(), (**dom).clone()));
        cod = b;
    }
    // Codomain must be `(App (Const synonym) args…)` or a bare `Const synonym`.
    let (head, args): (&CicTerm, &[CicTerm]) = match cod {
        CicTerm::App(h, xs) => (h, xs),
        other => (other, &[]),
    };
    let CicTerm::Const(name) = head else {
        return None;
    };
    let body = ctx.type_synonym(name)?;
    let unfolded = cic_beta_apply(body, args);
    // Only report an unfold if it actually exposed more structure (a sort/Π),
    // not a residual `Const` application (guards against a mis-registered body).
    if matches!(unfolded, CicTerm::App(_, _) | CicTerm::Const(_)) {
        return None;
    }
    Some(rebuild(&binders, unfolded))
}

/// β-reduce a dialect-sexp `λ`-telescope body applied to `args`: peel one
/// `Lambda` per arg, substituting the arg for the outermost binder. Fewer
/// binders than args fails closed (`None`); the extra args would be a partial
/// application the synonym unfolder never emits.
fn sexp_beta_apply(body: &Sexp, args: &[Sexp]) -> Option<Sexp> {
    let mut cur = body.clone();
    for arg in args {
        match &cur {
            Sexp::List(v) if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Lambda") => {
                cur = dialect_subst_binder0(&v[3], arg).ok()?;
            }
            _ => return None,
        }
    }
    Some(cur)
}

/// Dialect-sexp mirror of [`unfold_arity_synonym_codomain`]: δ-unfold an
/// inductive ARITY (in normalized dialect sexp) whose codomain — after its own
/// parameter/index `Π`s — is a registered type synonym applied to arguments
/// (`∀ U (x:U), Ensemble U` with `Ensemble := λU. U → Prop` becomes
/// `∀ U (x:U) (_:U), Prop`). This is what the Case/Fix reconstruction registry
/// (`SerapiIndInfo::arity`) needs so `num_indices()` counts the index HIDDEN
/// behind the synonym, and `index_binder_tys` recovers its type. Returns
/// `Some(rewritten)` when an unfold exposed a `Π`/sort codomain, `None`
/// otherwise (leaving every non-synonym-codomain arity byte-identical). The
/// kernel re-checks the family, so a mis-unfold is a loud rejection.
fn unfold_arity_synonym_codomain_sexp(arity: &Sexp, ctx: &SerapiNormCtx) -> Option<Sexp> {
    let (binders, cod) = dialect_peel_prods(arity);
    // Codomain must be `(App (Const synonym) args…)` or a bare `(Const synonym)`.
    let (head, args): (&Sexp, Vec<Sexp>) = match &cod {
        Sexp::List(v) if !v.is_empty() && matches!(&v[0], Sexp::Atom(h) if h == "App") => {
            (&v[1], v[2..].to_vec())
        }
        other => (other, Vec::new()),
    };
    let name = match head {
        Sexp::List(v) if v.len() == 2 && matches!(&v[0], Sexp::Atom(h) if h == "Const") => {
            match &v[1] {
                Sexp::Atom(n) => n.as_str(),
                _ => return None,
            }
        }
        _ => return None,
    };
    let body = ctx.type_synonym_sexp(name)?;
    let unfolded = sexp_beta_apply(body, &args)?;
    // Only report an unfold that exposed real structure (a `Π` or a sort), not
    // a residual `App`/`Const` application (mis-registered body → fail closed).
    match &unfolded {
        Sexp::List(v) if !v.is_empty() && matches!(&v[0], Sexp::Atom(h) if h == "App") => {
            return None
        }
        Sexp::List(v) if v.len() == 2 && matches!(&v[0], Sexp::Atom(h) if h == "Const") => {
            return None
        }
        _ => {}
    }
    // Rebuild the arity's own binders around the unfolded codomain.
    let mut acc = unfolded;
    for (nm, ty) in binders.into_iter().rev() {
        acc = Sexp::List(vec![
            Sexp::Atom("Prod".to_string()),
            Sexp::Atom(nm),
            ty,
            acc,
        ]);
    }
    Some(acc)
}

/// Reconstruct `(CoqInductive …)` forms from the coinductive TYPE axiom
/// triples the dumper emits for CoFinite blocks.
///
/// A CoInductive block (`Stream A = Cons : A → Stream A → Stream A`, or the
/// `Prop` relations `EqSt`/`ForAll`) is dumped as a type-former
/// `(CoqAxiom <base>.<N> <arity>)` plus per-constructor
/// `(CoqAxiom <base>.<N>.<k> <ctor-type>)`, because a greatest-fixpoint
/// corecursor has no well-founded encoding. But every OBSERVATION the corpus
/// performs on such a type is a single-step `Case` destructor (`hd`, `tl`,
/// `eqst_ntheq`, `ForAll_Str_nth_tl`, …), which is faithfully modelled by the
/// SAME least-fixpoint recursor a `CoqInductive` installs — the productive
/// CoFix VALUES stay out of model and fail closed (`corecursive CoFix value
/// has no recursor encoding`). Registering the block as an inductive is SOUND
/// for the corpus because Coq never emits the induction recursor
/// (`Stream_rect`/`EqSt_rect`/…) for a coinductive, so the empty-base recursor
/// is never applied with a false motive (verified: 0 references corpus-wide).
///
/// Detection is coinductive-specific and fail-closed: a plain `(CoqAxiom
/// <base>.<N> …)` whose arity codomain is a Sort (a type former), WITH a
/// contiguous constructor run `<base>.<N>.0…` each concluding in `(Ind <base>
/// <N> …)` (self-reference) — the exact shape the dumper emits for CoFinite
/// blocks, and impossible for a plain predicate axiom. Any constructor that
/// does not self-reference aborts the whole block (never fabricate an inductive
/// from an unclear shape). A mis-reconstructed family is a loud `add_inductive`
/// rejection at verify time — falling back to the arity stand-in axiom the
/// block already had (byte-identical to today) — never a silent accept.
///
/// Returns the synthesized `(CoqInductive …)` forms in file order plus the set
/// of consumed constructor-axiom names (the caller emits the synthesized
/// inductive at the type former's position and skips the constructor axioms so
/// no name is double-declared).
fn reconstruct_coinductive_inductives(
    sexps: &[Sexp],
    ctx: &SerapiNormCtx,
) -> (Vec<Sexp>, std::collections::HashSet<String>) {
    use std::collections::{HashMap, HashSet};
    // Index every PLAIN top-level `CoqAxiom` (arity 3 == name + type, no
    // trailing `StandIn` marker: a salvage stand-in is never a real type
    // former) by name.
    let mut axioms: HashMap<&str, &Sexp> = HashMap::new();
    for sexp in sexps {
        if let Sexp::List(items) = sexp {
            if items.len() == 3 && matches!(items.first(), Some(Sexp::Atom(h)) if h == "CoqAxiom") {
                if let Sexp::Atom(name) = &items[1] {
                    axioms.insert(name.as_str(), &items[2]);
                }
            }
        }
    }
    let mut forms: Vec<Sexp> = Vec::new();
    let mut consumed_ctors: HashSet<String> = HashSet::new();
    for sexp in sexps {
        let Sexp::List(items) = sexp else { continue };
        if items.len() != 3 || !matches!(items.first(), Some(Sexp::Atom(h)) if h == "CoqAxiom") {
            continue;
        }
        let Sexp::Atom(name) = &items[1] else {
            continue;
        };
        // `<base>.<N>` type-former spelling with a first constructor present —
        // a cheap string/lookup pre-filter before the costly normalization.
        let Some((base, block)) = name.rsplit_once('.') else {
            continue;
        };
        let Ok(block_idx) = block.parse::<u32>() else {
            continue;
        };
        if !axioms.contains_key(format!("{name}.0").as_str()) {
            continue;
        }
        // Arity codomain must be a Sort (a genuine type former). The raw SerAPI
        // sort carries a complex level the dialect recognizer cannot read, so
        // normalize first.
        let arity_norm = normalize_if_serapi_ctx(&items[2], ctx);
        if dialect_sort_of(dialect_prod_codomain(&arity_norm)).is_none() {
            continue;
        }
        // Contiguous self-referential constructor run.
        let mut ctor_forms: Vec<Sexp> = Vec::new();
        let mut ctor_names: Vec<String> = Vec::new();
        let mut aborted = false;
        let mut k = 0u32;
        loop {
            let ctor_name = format!("{name}.{k}");
            let Some(ctor_ty) = axioms.get(ctor_name.as_str()) else {
                break;
            };
            let ctor_norm = normalize_if_serapi_ctx(ctor_ty, ctx);
            let concl = dialect_prod_codomain(&ctor_norm);
            if !matches!(dialect_ind_head(concl), Some((n, i)) if n == base && i == block_idx) {
                aborted = true;
                break;
            }
            ctor_forms.push((*ctor_ty).clone());
            ctor_names.push(ctor_name);
            k += 1;
        }
        if aborted || ctor_forms.is_empty() {
            continue;
        }
        // NumParams UPPER BOUND = leading Prods of the arity; the shared
        // `compute_uniform_num_params` (run inside `parse_serapi_inductive`)
        // demotes non-uniform leading binders (`EqSt`'s `s1`/`s2`, `ForAll`'s
        // `x`) to indices, and the kernel `add_inductive` re-checks the result.
        let num_params = dialect_count_prods(&arity_norm);
        let mut form = vec![
            Sexp::Atom("CoqInductive".to_string()),
            Sexp::Atom(base.to_string()),
            Sexp::Atom(block_idx.to_string()),
            items[2].clone(),
            Sexp::List(vec![
                Sexp::Atom("NumParams".to_string()),
                Sexp::Atom(num_params.to_string()),
            ]),
        ];
        for (ctor_name, ctor_ty) in ctor_names.iter().zip(ctor_forms) {
            form.push(Sexp::List(vec![
                Sexp::Atom("Ctor".to_string()),
                Sexp::Atom(ctor_name.clone()),
                ctor_ty,
            ]));
            consumed_ctors.insert(ctor_name.clone());
        }
        forms.push(Sexp::List(form));
    }
    (forms, consumed_ctors)
}

/// The type-former axiom name (`<base>.<N>`) a reconstructed `(CoqInductive
/// <base> <N> …)` form was synthesized from, so the import loop can emit it in
/// place of that axiom.
fn coinductive_form_former_name(form: &Sexp) -> Option<String> {
    let Sexp::List(items) = form else {
        return None;
    };
    let (Some(Sexp::Atom(base)), Some(Sexp::Atom(block))) = (items.get(1), items.get(2)) else {
        return None;
    };
    Some(format!("{base}.{block}"))
}

/// Parse and normalize a `(CoqInductive ...)` form (no shard writes).
fn parse_serapi_inductive(
    items: &[Sexp],
    ctx: &SerapiNormCtx,
) -> MathverseResult<ParsedSerapiInductive> {
    // items = [CoqInductive, name, block-idx, arity, [(NumParams k)],
    //          (Ctor cname ctype)...]
    if items.len() < 4 {
        return Err(coq_err("CoqInductive: expected name, block index, arity"));
    }
    let ind_name = match &items[1] {
        Sexp::Atom(s) => s.clone(),
        _ => return Err(coq_err("CoqInductive: name must be an atom")),
    };
    // SELF-REFERENCE CARVE-OUT for the canonical-first inductive Dual
    // resolution (see [`resolve_ind_family_name`]): while THIS family's own
    // arity/constructor types normalize, references to the family itself
    // keep the family's user spelling — an `Include`-copied family whose
    // constructors were flipped to the canonical original would reject its
    // whole replay. Guard (not set/clear) because the parse has early `?`
    // returns.
    struct FamilyGuard;
    impl Drop for FamilyGuard {
        fn drop(&mut self) {
            CURRENT_INDUCTIVE_FAMILY.with(|f| *f.borrow_mut() = None);
        }
    }
    CURRENT_INDUCTIVE_FAMILY.with(|f| *f.borrow_mut() = Some(ind_name.clone()));
    let _family_guard = FamilyGuard;
    let block_idx = get_u32(items, 2)?;
    // A non-zero block index means this is a MEMBER of a mutual inductive
    // block. Importing mutual members as independent inductives is unsound
    // (the family all_names header and joint add_inductive replay are
    // required), so fail closed — the caller counts the rejection.
    if block_idx != 0 {
        return Err(coq_err(
            "CoqInductive: mutual inductive block member (block-idx > 0) rejected: \
             mutual families require the all_names family export path",
        ));
    }
    let mut arity_sexp = normalize_if_serapi_ctx(&items[3], ctx);
    // Zeta-reduce a spine-LetIn arity telescope (an HB `mixin_of` record's
    // `∀ T0 b, let T := Pack … in ∀ p3, Type` interleaves a packing `let` in
    // its leading Π parameter spine) to the pure-Π parameter telescope the
    // kernel's `count_pi_args` arity check and the family-replay metadata
    // builder require. Pure-Π arities — every other inductive — pass through
    // byte-identical (`None`); the constructor is zeta-reduced with the SAME
    // spine reducer, so the parameter prefixes match structurally. The kernel
    // re-checks the reduced declaration (fail closed).
    let arity_had_spine_letin = match zeta_reduce_arity_telescope(&arity_sexp) {
        Some(reduced) => {
            arity_sexp = reduced;
            true
        }
        None => false,
    };
    let mut arity_cic = sexp_to_cic(&arity_sexp)?;
    // Delta-unfold a type-synonym arity codomain (`∀U, Ensemble U` with
    // `Ensemble := λU. U → Prop` → `∀U, U → Prop`) so the checked add_inductive
    // arity check sees a syntactic sort. Only synonym-codomain arities change;
    // every other inductive is byte-identical, and the kernel re-checks.
    if let Some(unfolded) = unfold_arity_synonym_codomain(&arity_cic, ctx) {
        arity_cic = unfolded;
    }
    // Mirror the same δ-unfold on the dialect-SEXP arity that seeds the Case/Fix
    // reconstruction registry (`SerapiIndInfo::arity`). Without it the registry
    // undercounts the index hidden behind the synonym (`Singleton U x :
    // Ensemble U` has one index `a:U`), so an indexed match on the family fails
    // the return-predicate-arity guard even though the KERNEL (which δ-reduces
    // `Ensemble U` to `U → Prop`) sees that index. Cross-file the CIC synonym
    // registry is not seeded, so `arity_cic` stays folded there (the kernel
    // δ-reduces it); the sexp registry IS seeded, keeping `num_indices()` in
    // agreement with the kernel recursor either way.
    let mut arity_synonym_unfolded = false;
    if let Some(unfolded) = unfold_arity_synonym_codomain_sexp(&arity_sexp, ctx) {
        arity_sexp = unfolded;
        arity_synonym_unfolded = true;
    }
    // A zeta-reduced record arity now exposes its full field telescope to the
    // kernel's STRICT per-field universe check, so its collapsed codomain sort
    // must actually bound the fields. Lift an under-collapsed pierced
    // `Type@{Set+n}` codomain to its flat-scale level — the spine-LetIn sibling
    // of the bare-`Sort` let-field lift below. SCOPED to arities this lever
    // zeta-reduced; a no-op for a `Prop` or named-`Type` codomain.
    if arity_had_spine_letin {
        if let Some((lifted_sexp, lifted_cic)) =
            lift_arity_codomain_universe(&arity_sexp, &arity_cic)
        {
            arity_sexp = lifted_sexp;
            arity_cic = lifted_cic;
        }
    }

    // Optional `(NumParams k)` directly after the arity carries the inductive's
    // parameter count for PARAMETERIZED inductives (e.g. `eq` has 1 param: the
    // type `A`). When absent, default to 0 — backward-compatible with the
    // existing num_params=0 datasets (e.g. `nat`, `mynat`). The corpus verifier
    // reads this back via `inductive_decl_num_params()` to build the checked
    // `InductiveDecl { num_params, .. }` it replays through `add_inductive`.
    let (num_params, ctor_items) = parse_inductive_num_params(&items[4..])?;

    // The inductive type's shard name must match how a dependent term's
    // `(Ind name block-idx)` reference lowers in cic_to_flat_expr.
    let ind_const_name = format!("{ind_name}.{block_idx}");

    // Parse constructors first so a malformed entry fails the whole inductive
    // (fail-closed) before any constant is written. ZERO constructors are
    // allowed: empty inductives (`False`, `Empty_set`) are complete family
    // declarations, and the corpus verifier's family replay accepts them
    // because the header carries the `num_params` stamp (written below).
    let mut ctors: Vec<(String, CicTerm)> = Vec::new();
    let mut ctor_type_sexps: Vec<Sexp> = Vec::new();
    let mut ctor_raw_lets: Vec<Option<(Sexp, Vec<bool>)>> = Vec::new();
    for (ctor_idx, item) in ctor_items.iter().enumerate() {
        let cv = match item {
            Sexp::List(v) if v.len() >= 3 => v,
            _ => return Err(coq_err("CoqInductive: malformed Ctor entry")),
        };
        if !matches!(&cv[0], Sexp::Atom(t) if t == "Ctor") {
            return Err(coq_err("CoqInductive: expected Ctor entry"));
        }
        let raw_ty_sexp = normalize_if_serapi_ctx(&cv[2], ctx);
        // Zeta-reduce a LetIn-laced constructor telescope
        // (`Build_ConstructiveReals`: 35 decls = 29 fields + 6 lets) to the
        // pure-Prod field telescope the kernel's recursor generator expects,
        // keeping the raw type + per-decl let flags for Case branch
        // reconstruction. Pure-Prod telescopes — every previously-working
        // inductive — pass through byte-identical (`None`), and the kernel
        // re-checks the reduced declaration either way (fail closed).
        let (ctor_ty_sexp, raw_lets) = match zeta_reduce_ctor_telescope(&raw_ty_sexp) {
            Some((reduced, decl_is_let)) => (reduced, Some((raw_ty_sexp, decl_is_let))),
            None => (raw_ty_sexp, None),
        };
        ctor_raw_lets.push(raw_lets);
        let ctor_ty = sexp_to_cic(&ctor_ty_sexp)?;
        // Constructor `ctor_idx` (0-based) must match how a dependent term's
        // `(Construct name block-idx j)` reference lowers: `name.block.(j-1)`.
        let ctor_const_name = format!("{ind_const_name}.{ctor_idx}");
        ctors.push((ctor_const_name, ctor_ty));
        ctor_type_sexps.push(ctor_ty_sexp);
    }
    // Demote non-uniform leading parameters to indices (Acc/clos_*/Rstar): a
    // Coq "parameter" a constructor re-instantiates in a recursive occurrence
    // is a Lean INDEX, and Clean's strict `add_inductive` rejects it as a
    // parameter. This only ever shrinks `num_params`, and only on a provable
    // uniform-spine violation, so uniform inductives are untouched; the kernel
    // re-checks the result either way. Both the shard header (`num_params`
    // stamp) and the Case/Fix registry read the demoted count from here.
    let num_params = compute_uniform_num_params(&ind_name, block_idx, num_params, &ctor_type_sexps);

    // A zeta-reduced let-field record exposes its FULL field telescope to the
    // kernel's strict per-field universe check, so the arity's collapsed sort
    // must actually bound the fields. `classify_serapi_type_universe`
    // under-collapses `Type@{Set+1}` to `Set` itself (base-0 pierced-`Set`
    // arm; masked before this lever because the LetIn-laced constructor
    // reconstructed as a 0-field family). LIFT the arity to its flat-scale
    // collapse (`Type@{Set+1}` → `Type 2`) — SCOPED to inductives this lever
    // rewrote (any `LetIn` telescope), so every other inductive's arity is
    // byte-identical; the kernel re-checks the lifted declaration (a wrong
    // lift is a loud rejection, never a silent accept).
    let (arity_sexp, arity_cic) = if ctor_raw_lets.iter().any(Option::is_some) {
        match (
            serapi_sort_flat_type_level(&items[3]),
            dialect_sort_concrete_type_level(&arity_sexp),
        ) {
            (Some(flat), Some(collapsed)) if flat > collapsed => (
                Sexp::List(vec![
                    Sexp::Atom("Sort".to_string()),
                    Sexp::List(vec![
                        Sexp::Atom("Type".to_string()),
                        Sexp::Atom(flat.to_string()),
                    ]),
                ]),
                CicTerm::Sort(CicSort::type_at(flat)),
            ),
            _ => (arity_sexp, arity_cic),
        }
    } else {
        (arity_sexp, arity_cic)
    };
    Ok(ParsedSerapiInductive {
        ind_name,
        block_idx,
        num_params,
        arity_sexp,
        arity_cic,
        ctors,
        ctor_type_sexps,
        ctor_raw_lets,
        arity_synonym_unfolded,
    })
}

/// Emit the UNIVERSE-POLYMORPHIC `prod` inductive + its `pair` constructor into
/// the shard (template polymorphism — the eqmx/mxalgebra unlock). Returns the
/// number of constants written (2: the inductive + its one constructor).
///
/// Shape (exactly the kernel-checked declaration pinned by
/// `coq_template_poly_prod_feasibility.rs`):
///   * `prod.{u,v} : Sort u → Sort v → Sort (max u v)` — 2 params, 2 level params
///   * `pair.{u,v} : (A : Sort u)(B : Sort v)(a : A)(b : B) → prod.{u,v} A B`
///
/// On the cumulative (Coq re-verification) lane the checked `add_inductive`
/// replay then generates the LARGE-eliminating recursor
/// `prod.0.rec.{motive,u,v}` (the parametric singleton-elimination unlock), so
/// `prod.{0,0} P Q : Prop` (`eqmx`) and `Type`-motive projections (`fst`/`snd`)
/// both re-verify.
fn emit_template_poly_prod(writer: &mut ShardWriter) -> u32 {
    // Level params `u`, `v` occupy a contiguous string block so the header's
    // `[level_params_start .. +count)` window reconstructs them; the inductive
    // and its constructor point at the SAME block (`Name` equality is by
    // content, so the family replay's level-param match holds).
    let lp_start = writer.add_string_block(&["u", "v"]);
    let lu = writer.add_level(FlatLevel::param(lp_start));
    let lv = writer.add_level(FlatLevel::param(lp_start + 1));
    let lmax = writer.add_level(FlatLevel::max(lu, lv));
    let sort_u = writer.add_expr(FlatExpr::sort(lu));
    let sort_v = writer.add_expr(FlatExpr::sort(lv));
    let sort_max = writer.add_expr(FlatExpr::sort(lmax));

    // Arity `Π (Sort u). Π (Sort v). Sort (max u v)`.
    let arity_inner = writer.add_expr(FlatExpr::pi(0, sort_v, sort_max));
    let arity = writer.add_expr(FlatExpr::pi(0, sort_u, arity_inner));

    let ind_name_idx = writer.add_string(TEMPLATE_POLY_PROD);
    let mut ind_header = MathverseConstantHeader {
        name_idx: ind_name_idx,
        type_idx: arity,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Coq as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Inductive as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: lp_start,
        level_params_count: 2,
        _pad2: [0u8; 26],
    };
    ind_header.set_inductive_decl_num_params(2);
    writer.add_constant(ind_header);

    // Constructor `pair.{u,v} : (A : Sort u)(B : Sort v)(a : A)(b : B) →
    // prod.{u,v} A B`. de Bruijn under binders [A, B, a, b] (innermost = b):
    // in the codomain A = bvar 3, B = bvar 2; the binder types `a : A` and
    // `b : B` are each `bvar 1` in their own scope.
    let prod_lvls = writer.add_level_list(&[lu, lv]);
    let prod_ref = writer.add_expr(FlatExpr::const_ref(ind_name_idx, prod_lvls));
    let bv3 = writer.add_expr(FlatExpr::bvar(3));
    let bv2 = writer.add_expr(FlatExpr::bvar(2));
    let bv1 = writer.add_expr(FlatExpr::bvar(1));
    let prod_a = writer.add_expr(FlatExpr::app(prod_ref, bv3));
    let prod_ab = writer.add_expr(FlatExpr::app(prod_a, bv2));
    let pi_b = writer.add_expr(FlatExpr::pi(0, bv1, prod_ab)); // b : B
    let pi_a = writer.add_expr(FlatExpr::pi(0, bv1, pi_b)); // a : A
    let pi_big_b = writer.add_expr(FlatExpr::pi(0, sort_v, pi_a)); // B : Sort v
    let ctor_ty = writer.add_expr(FlatExpr::pi(0, sort_u, pi_big_b)); // A : Sort u

    let ctor_name_idx = writer.add_string(&format!("{TEMPLATE_POLY_PROD}.0"));
    writer.add_constant(MathverseConstantHeader {
        name_idx: ctor_name_idx,
        type_idx: ctor_ty,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Coq as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Constructor as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: lp_start,
        level_params_count: 2,
        _pad2: [0u8; 26],
    });

    2
}

fn import_serapi_inductive(
    items: &[Sexp],
    writer: &mut ShardWriter,
    ctx: &mut SerapiNormCtx,
) -> MathverseResult<u32> {
    let parsed = parse_serapi_inductive(items, ctx)?;
    let ind_const_name = format!("{}.{}", parsed.ind_name, parsed.block_idx);

    // Template-polymorphism (`prod`, the eqmx/mxalgebra unlock): emit `prod`
    // UNIVERSE-POLYMORPHICALLY (`prod.{u,v} : Sort u → Sort v → Sort (max u v)`)
    // so `prod.{0,0} P Q : Prop` typechecks, instead of the template-collapsed
    // monomorphic `prod : Sort 1 → Sort 1 → Sort 1`. The constructor field
    // shape the registry records for `match`/`fix` reconstruction is
    // universe-agnostic, so it is registered from the (monomorphic) parse
    // unchanged; only the EMITTED kernel declaration goes poly.
    if template_poly_param_count(&ind_const_name).is_some() {
        parsed.register_into(ctx);
        return Ok(emit_template_poly_prod(writer));
    }

    // The inductive type itself: NO_VALUE, but tagged Inductive with explicit
    // num_params so the checked add_inductive replay path engages. Pure axiom
    // profile + KernelVerified confidence keep the fail-closed trust gate honest.
    let arity_idx = cic_to_flat_expr(&parsed.arity_cic, writer);
    let ind_name_idx = writer.add_string(&ind_const_name);
    let mut ind_header = MathverseConstantHeader {
        name_idx: ind_name_idx,
        type_idx: arity_idx,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Coq as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Inductive as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    ind_header.set_inductive_decl_num_params(parsed.num_params);
    writer.add_constant(ind_header);

    for (ctor_const_name, ctor_ty) in &parsed.ctors {
        let ctor_type_idx = cic_to_flat_expr(ctor_ty, writer);
        let ctor_name_idx = writer.add_string(ctor_const_name);
        writer.add_constant(MathverseConstantHeader {
            name_idx: ctor_name_idx,
            type_idx: ctor_type_idx,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Constructor as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
    }

    // Register the inductive's shape for later SerAPI Case/Fix reconstruction
    // in this import session (constructor field types + recursive flags).
    parsed.register_into(ctx);

    Ok(1 + parsed.ctors.len() as u32)
}

/// Compute axiom profile bits for an AXIOMATIZED / valueless Coq constant
/// based on its (fully-qualified) name.
///
/// Value-bearing TRANSLATED definitions do NOT go through this function —
/// they get `AxiomProfile::NONE` at import (the corpus verifier and later
/// trust stamping decide their trust), never a blanket `BRIDGE_AXIOM`.
///
/// Names are keyed on both the module path prefix (via
/// [`classify_coq_module`]) and the final segment, so qualified names like
/// `Coq.Logic.FunctionalExtensionality.functional_extensionality_dep`
/// classify identically to the legacy short forms.
pub(crate) fn compute_coq_axiom_profile(name: &str) -> AxiomProfile {
    let mut bits = AxiomProfile::BRIDGE_AXIOM;
    // Module-path classification on the qualified prefix.
    if let Some((module, _)) = name.rsplit_once('.') {
        bits |= classify_coq_module(module);
    }
    // Univalence-based foundations.
    if name.starts_with("UniMath.") || name.starts_with("HoTT.") {
        bits |= AxiomProfile::UNIVALENCE;
    }
    // Legacy unqualified module prefixes.
    if name.starts_with("Classical.") {
        bits |= AxiomProfile::CHOICE | AxiomProfile::CLASSICAL;
    }
    if name.starts_with("FunctionalExtensionality.") {
        bits |= AxiomProfile::FUNC_EXT;
    }
    // Final-segment classification (works for both bare and qualified names).
    let last = name.rsplit('.').next().unwrap_or(name);
    match last {
        "classic" => bits |= AxiomProfile::CHOICE | AxiomProfile::CLASSICAL,
        "propositional_extensionality" | "prop_ext" => bits |= AxiomProfile::PROP_EXT,
        "functional_extensionality" | "functional_extensionality_dep" => {
            bits |= AxiomProfile::FUNC_EXT;
        }
        _ => {}
    }
    bits
}

/// Coq mutual inductive type definition.
#[derive(Clone, Debug)]
pub struct CoqMutualInductive {
    pub params: Vec<(String, CicTerm)>,
    pub bodies: Vec<CoqInductiveBody>,
}

/// A single inductive body within a mutual inductive block.
#[derive(Clone, Debug)]
pub struct CoqInductiveBody {
    pub name: String,
    pub arity: CicTerm,
    pub constructors: Vec<(String, CicTerm)>,
}

/// Parse a mutual inductive from `(MutualInductive (Params ...) (Body name arity (Ctor ...)...) ...)`.
pub fn sexp_to_mutual_inductive(sexp: &Sexp) -> Result<CoqMutualInductive, MathverseError> {
    let items = match sexp {
        Sexp::List(v) if !v.is_empty() => v,
        _ => return Err(coq_err("expected list")),
    };
    match &items[0] {
        Sexp::Atom(s) if s == "MutualInductive" => {}
        _ => return Err(coq_err("expected MutualInductive")),
    }
    let (mut params, mut bodies) = (Vec::new(), Vec::new());
    for item in &items[1..] {
        let ch = match item {
            Sexp::List(v) if !v.is_empty() => v,
            _ => continue,
        };
        let tag = match &ch[0] {
            Sexp::Atom(s) => s.as_str(),
            _ => continue,
        };
        match tag {
            "Params" => {
                for p in &ch[1..] {
                    if let Sexp::List(pv) = p {
                        if pv.len() >= 2 {
                            let n = match &pv[0] {
                                Sexp::Atom(s) => s.clone(),
                                _ => continue,
                            };
                            params.push((n, sexp_to_cic(&pv[1])?));
                        }
                    }
                }
            }
            "Body" if ch.len() >= 3 => {
                let name = get_str(ch, 1)?;
                let arity = sexp_to_cic(get_at(ch, 2)?)?;
                let mut ctors = Vec::new();
                for c in &ch[3..] {
                    if let Sexp::List(cv) = c {
                        if cv.len() >= 3 && matches!(&cv[0], Sexp::Atom(t) if t == "Ctor") {
                            ctors.push((get_str(cv, 1)?, sexp_to_cic(get_at(cv, 2)?)?));
                        }
                    }
                }
                bodies.push(CoqInductiveBody {
                    name,
                    arity,
                    constructors: ctors,
                });
            }
            _ => {}
        }
    }
    Ok(CoqMutualInductive { params, bodies })
}

/// Import a mutual inductive into a shard. Returns constant indices for
/// all inductive types and their constructors.
pub fn import_mutual_inductive(
    ind: &CoqMutualInductive,
    module_path: &str,
    writer: &mut ShardWriter,
) -> MathverseResult<Vec<u32>> {
    let profile = classify_coq_module(module_path);
    let mut indices = Vec::new();
    let add_ind_const = |name: &str, ty: &CicTerm, kind: DeclKind, w: &mut ShardWriter| -> u32 {
        let type_idx = cic_to_flat_expr(ty, w);
        let name_idx = w.add_string(name);
        w.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::Translated as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: kind as u8,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        })
    };
    for body in &ind.bodies {
        indices.push(add_ind_const(
            &body.name,
            &body.arity,
            DeclKind::Inductive,
            writer,
        ));
        for (ctor_name, ctor_ty) in &body.constructors {
            let mangled = format!("{}.{}", body.name, ctor_name);
            indices.push(add_ind_const(
                &mangled,
                ctor_ty,
                DeclKind::Constructor,
                writer,
            ));
        }
    }
    Ok(indices)
}

/// Coq universe instance (list of levels applied to a universe-polymorphic constant).
#[derive(Clone, Debug)]
pub struct CoqUniverseInstance {
    pub levels: Vec<CoqUniverseLevel>,
}

/// Coq universe level expression.
#[derive(Clone, Debug, PartialEq)]
pub enum CoqUniverseLevel {
    Set,
    Prop,
    Type(u32),
    Var(String),
    Max(Vec<CoqUniverseLevel>),
    Succ(Box<CoqUniverseLevel>),
}

/// Lower a `CoqUniverseLevel` into the `FlatLevel` arena. Returns the arena index.
pub(crate) fn universe_level_to_flat(level: &CoqUniverseLevel, w: &mut ShardWriter) -> u32 {
    match level {
        CoqUniverseLevel::Prop => w.add_level(FlatLevel::zero()),
        CoqUniverseLevel::Set => {
            let z = w.add_level(FlatLevel::zero());
            w.add_level(FlatLevel::succ(z))
        }
        CoqUniverseLevel::Type(n) => {
            let mut idx = w.add_level(FlatLevel::zero());
            for _ in 0..*n {
                idx = w.add_level(FlatLevel::succ(idx));
            }
            idx
        }
        CoqUniverseLevel::Var(name) => {
            let ni = w.add_string(name);
            w.add_level(FlatLevel::param(ni))
        }
        CoqUniverseLevel::Max(children) => {
            if children.is_empty() {
                return w.add_level(FlatLevel::zero());
            }
            let mut cur = universe_level_to_flat(&children[0], w);
            for child in &children[1..] {
                let ci = universe_level_to_flat(child, w);
                cur = w.add_level(FlatLevel::max(cur, ci));
            }
            cur
        }
        CoqUniverseLevel::Succ(inner) => {
            let inner_idx = universe_level_to_flat(inner, w);
            w.add_level(FlatLevel::succ(inner_idx))
        }
    }
}

/// Classify a Coq module path to determine its base axiom profile.
/// Pure modules return `AxiomProfile::NONE`; axiom-carrying modules get `BRIDGE_AXIOM`.
pub(crate) fn classify_coq_module(module_path: &str) -> AxiomProfile {
    if module_path.starts_with("Coq.Init.")
        || module_path == "Coq.Init"
        || module_path == "Coq.Logic.Decidable"
        || module_path == "Coq.Setoids.Setoid"
    {
        return AxiomProfile::NONE;
    }
    let ba = AxiomProfile::BRIDGE_AXIOM;
    match module_path {
        "Coq.Logic.ClassicalEpsilon" => ba | AxiomProfile::CHOICE,
        "Coq.Logic.ClassicalChoice" => ba | AxiomProfile::CHOICE | AxiomProfile::CLASSICAL,
        "Coq.Logic.FunctionalExtensionality" => ba | AxiomProfile::FUNC_EXT,
        "Coq.Logic.PropExtensionality" | "Coq.Logic.ProofIrrelevance" => {
            ba | AxiomProfile::PROP_EXT
        }
        "Coq.Logic.Berardi" => ba | AxiomProfile::UNIVERSE_INCON,
        // Any other Coq.Logic.Classical* module (Classical_Prop,
        // Classical_Pred_Type, Classical, ...) carries classical choice/LEM.
        m if m.starts_with("Coq.Logic.Classical") => {
            ba | AxiomProfile::CHOICE | AxiomProfile::CLASSICAL
        }
        m if m.starts_with("UniMath") || m.starts_with("HoTT") => ba | AxiomProfile::UNIVALENCE,
        _ => ba,
    }
}

// ---------------------------------------------------------------------------
// CIC pattern matching and fixpoint structures
// ---------------------------------------------------------------------------

/// A single branch in a Coq `Case` (pattern match) expression.
///
/// Each branch corresponds to a constructor pattern with bound variables.
/// `constructor` identifies the constructor being matched, `nargs` is the
/// number of pattern variables bound in this branch, and `body` is the
/// branch body (a CIC term with `nargs` additional bound variables).
#[derive(Clone, Debug)]
pub struct CicMatchBranch {
    pub constructor: String,
    pub nargs: u32,
    pub body: CicTerm,
}

/// A single body within a mutual (co)fixpoint definition.
///
/// `name` is the bound name, `type_` is the declared type, `body` is the
/// definition body, and `recursive_arg_idx` identifies which argument is
/// structurally decreasing (for the termination guard).
#[derive(Clone, Debug)]
pub struct CicFixBody {
    pub name: String,
    pub type_: CicTerm,
    pub body: CicTerm,
    pub recursive_arg_idx: u32,
}

/// Coq sort extended with SProp (strict propositions, Coq 8.10+).
#[derive(Clone, Debug, PartialEq)]
pub enum CicSortExt {
    Prop,
    Set,
    SProp,
    Type(u32),
}

/// Parse a richer `Case` s-expression with constructor-annotated branches.
///
/// Accepts `(Case scrutinee return_type (Branch ctor nargs body) ...)` in
/// addition to the basic form already handled by `sexp_to_cic`.
pub(crate) fn sexp_to_cic_match_branches(
    sexp: &Sexp,
) -> Result<Vec<CicMatchBranch>, MathverseError> {
    let items = match sexp {
        Sexp::List(v) if !v.is_empty() => v,
        _ => return Err(coq_err("expected list for Case branches")),
    };
    let head = match &items[0] {
        Sexp::Atom(s) if s == "Case" => s.as_str(),
        _ => return Err(coq_err("expected Case head")),
    };
    let _ = head; // used only for match guard above
    let mut branches = Vec::new();
    // Branches start at index 3 (after Case, scrutinee, return_type)
    for item in items.iter().skip(3) {
        match item {
            Sexp::List(bv) if bv.len() >= 4 => {
                if matches!(&bv[0], Sexp::Atom(t) if t == "Branch") {
                    let ctor = get_str(bv, 1)?;
                    let nargs = get_u32(bv, 2)?;
                    let body = sexp_to_cic(get_at(bv, 3)?)?;
                    branches.push(CicMatchBranch {
                        constructor: ctor,
                        nargs,
                        body,
                    });
                } else {
                    // Fall back to plain body (non-annotated branch)
                    let body = sexp_to_cic(item)?;
                    branches.push(CicMatchBranch {
                        constructor: String::new(),
                        nargs: 0,
                        body,
                    });
                }
            }
            _ => {
                // Plain branch body without Branch wrapper
                let body = sexp_to_cic(item)?;
                branches.push(CicMatchBranch {
                    constructor: String::new(),
                    nargs: 0,
                    body,
                });
            }
        }
    }
    Ok(branches)
}

/// Lower a `CicMatchBranch` into the FlatExpr arena.
///
/// Each branch is encoded as a lambda wrapping `nargs` bound variables
/// around the branch body. If `nargs == 0` the body is emitted directly.
pub(crate) fn match_branch_to_flat(branch: &CicMatchBranch, w: &mut ShardWriter) -> u32 {
    let body_idx = cic_to_flat_expr(&branch.body, w);
    if branch.nargs == 0 {
        return body_idx;
    }
    // Wrap the body in `nargs` lambdas with a placeholder Prop type.
    let prop_level = w.add_level(FlatLevel::zero());
    let prop_sort = w.add_expr(FlatExpr::sort(prop_level));
    let mut cur = body_idx;
    for _ in 0..branch.nargs {
        cur = w.add_expr(FlatExpr::lam(0, prop_sort, cur));
    }
    cur
}

/// Parse a mutual fixpoint definition from s-expression form.
///
/// Accepts `(MutualFix ((name type body rec_arg) ...) focus_idx)`.
pub(crate) fn sexp_to_mutual_fixpoint(
    sexp: &Sexp,
) -> Result<(Vec<CicFixBody>, u32), MathverseError> {
    let items = match sexp {
        Sexp::List(v) if !v.is_empty() => v,
        _ => return Err(coq_err("expected list for MutualFix")),
    };
    let head = match &items[0] {
        Sexp::Atom(s) => s.as_str(),
        _ => return Err(coq_err("expected atom head in MutualFix")),
    };
    if head != "MutualFix" && head != "Fix" {
        return Err(coq_err(&format!("expected MutualFix or Fix, got {head}")));
    }
    let body_list = match get_at(items, 1)? {
        Sexp::List(v) => v,
        _ => return Err(coq_err("MutualFix bodies must be a list")),
    };
    let mut bodies = Vec::new();
    for b in body_list {
        match b {
            Sexp::List(bv) if bv.len() >= 3 => {
                let name = get_str(bv, 0)?;
                let type_ = sexp_to_cic(get_at(bv, 1)?)?;
                let body = sexp_to_cic(get_at(bv, 2)?)?;
                let recursive_arg_idx = if bv.len() > 3 {
                    get_u32(bv, 3).unwrap_or(0)
                } else {
                    0
                };
                bodies.push(CicFixBody {
                    name,
                    type_,
                    body,
                    recursive_arg_idx,
                });
            }
            _ => return Err(coq_err("invalid MutualFix body entry")),
        }
    }
    let focus = get_u32(items, 2)?;
    Ok((bodies, focus))
}

/// Import a mutual fixpoint into a shard.
///
/// Each fixpoint body is lowered to a lambda (type → body) and stored as
/// a constant. The focused body is marked as `Translated`; the rest are
/// `Axiomatized` (they can be resolved by the focused one).
pub fn import_mutual_fixpoint(
    bodies: &[CicFixBody],
    focus: u32,
    module_path: &str,
    writer: &mut ShardWriter,
) -> MathverseResult<Vec<u32>> {
    let profile = classify_coq_module(module_path);
    let mut indices = Vec::new();
    for (i, fb) in bodies.iter().enumerate() {
        let type_idx = cic_to_flat_expr(&fb.type_, writer);
        let body_idx = cic_to_flat_expr(&fb.body, writer);
        let value_idx = writer.add_expr(FlatExpr::lam(0, type_idx, body_idx));
        let name_idx = writer.add_string(&fb.name);
        // Focused body is a Definition (has value); others defer their defining equation and are Axiom.
        let (confidence, dk) = if i as u32 == focus {
            (ImportConfidence::Translated, DeclKind::Definition)
        } else {
            (ImportConfidence::Axiomatized, DeclKind::Axiom)
        };
        let idx = writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Coq as u8,
            import_confidence: confidence as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: dk as u8,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        indices.push(idx);
    }
    Ok(indices)
}

/// Lower a `CicSortExt` (including SProp) into the FlatLevel arena.
pub(crate) fn sort_ext_to_flat(sort: &CicSortExt, w: &mut ShardWriter) -> u32 {
    match sort {
        CicSortExt::Prop | CicSortExt::SProp => w.add_level(FlatLevel::zero()),
        CicSortExt::Set => {
            let z = w.add_level(FlatLevel::zero());
            w.add_level(FlatLevel::succ(z))
        }
        CicSortExt::Type(u) => {
            let mut idx = w.add_level(FlatLevel::zero());
            for _ in 0..*u {
                idx = w.add_level(FlatLevel::succ(idx));
            }
            idx
        }
    }
}

// ---------------------------------------------------------------------------
// Universe instance handling for Const/Ind/Construct
// ---------------------------------------------------------------------------

/// Lower a CIC term to FlatExpr with universe instance support.
///
/// When a `Const`, `Ind`, or `Construct` node carries a universe instance,
/// the levels are lowered into the level arena and a level list offset is
/// constructed for the `const_ref` encoding. This is the universe-aware
/// variant of `cic_to_flat_expr`.
pub(crate) fn cic_to_flat_expr_with_universes(
    term: &CicTerm,
    universes: &Option<CoqUniverseInstance>,
    w: &mut ShardWriter,
) -> u32 {
    // If no universe instance, delegate to standard lowering
    let Some(inst) = universes else {
        return cic_to_flat_expr(term, w);
    };
    match term {
        CicTerm::Const(name) | CicTerm::Var(name) => {
            let ni = w.add_string(name);
            if inst.levels.is_empty() {
                return w.add_expr(FlatExpr::const_ref(ni, u32::MAX));
            }
            // Lower each universe level into the level arena
            let level_indices: Vec<u32> = inst
                .levels
                .iter()
                .map(|l| universe_level_to_flat(l, w))
                .collect();
            // Encode as nested Sort applications to preserve level info.
            // The primary const_ref uses the first level as a tag.
            let first_level = level_indices[0];
            let base = w.add_expr(FlatExpr::const_ref(ni, first_level));
            // For multi-level instances, chain through app nodes with
            // Sort markers so downstream consumers can reconstruct.
            let mut cur = base;
            for &li in &level_indices[1..] {
                let sort_marker = w.add_expr(FlatExpr::sort(li));
                cur = w.add_expr(FlatExpr::app(cur, sort_marker));
            }
            cur
        }
        CicTerm::Ind(name, idx) => {
            let full = format!("{name}.{idx}");
            let ni = w.add_string(&full);
            if inst.levels.is_empty() {
                // Template-poly inductive (`prod`) carries the {1,1} instance
                // even with an empty SerAPI universe instance (template
                // polymorphism stores no explicit `Instance`).
                let levels = match template_poly_param_count(&full) {
                    Some(n) => template_poly_instance_list(n, None, w),
                    None => u32::MAX,
                };
                return w.add_expr(FlatExpr::const_ref(ni, levels));
            }
            let first_li = universe_level_to_flat(&inst.levels[0], w);
            let base = w.add_expr(FlatExpr::const_ref(ni, first_li));
            let mut cur = base;
            for l in &inst.levels[1..] {
                let li = universe_level_to_flat(l, w);
                let sort_marker = w.add_expr(FlatExpr::sort(li));
                cur = w.add_expr(FlatExpr::app(cur, sort_marker));
            }
            cur
        }
        CicTerm::Construct(name, ii, ci) => {
            let ni = w.add_string(&format!("{name}.{ii}.{ci}"));
            if inst.levels.is_empty() {
                // Parent-keyed template-poly instance (see the base lowering).
                let levels = match template_poly_param_count(&format!("{name}.{ii}")) {
                    Some(n) => template_poly_instance_list(n, None, w),
                    None => u32::MAX,
                };
                return w.add_expr(FlatExpr::const_ref(ni, levels));
            }
            let first_li = universe_level_to_flat(&inst.levels[0], w);
            let base = w.add_expr(FlatExpr::const_ref(ni, first_li));
            let mut cur = base;
            for l in &inst.levels[1..] {
                let li = universe_level_to_flat(l, w);
                let sort_marker = w.add_expr(FlatExpr::sort(li));
                cur = w.add_expr(FlatExpr::app(cur, sort_marker));
            }
            cur
        }
        // For non-constant terms, universes don't apply — delegate.
        _ => cic_to_flat_expr(term, w),
    }
}

// ---------------------------------------------------------------------------
// Primitive operations: Int63 and Float64
// ---------------------------------------------------------------------------

/// Coq primitive operation kind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CicPrimOp {
    // Int63 operations
    Int63Add,
    Int63Sub,
    Int63Mul,
    Int63Div,
    Int63Mod,
    Int63Land,
    Int63Lor,
    Int63Lxor,
    Int63Lsl,
    Int63Lsr,
    Int63Eq,
    Int63Lt,
    Int63Le,
    // Float64 operations
    Float64Add,
    Float64Sub,
    Float64Mul,
    Float64Div,
    Float64Eq,
    Float64Lt,
    Float64Le,
    Float64Sqrt,
    Float64Neg,
    // Array operations
    PArrayGet,
    PArraySet,
    PArrayMake,
    PArrayLength,
}

/// Lower a Coq primitive operation to a FlatExpr constant reference.
///
/// Primitive operations are encoded as named constants in the Mathverse format,
/// using the `__coq_prim__` namespace to distinguish them from regular
/// user-defined constants.
pub(crate) fn cic_primitive_to_flat(op: &CicPrimOp, w: &mut ShardWriter) -> u32 {
    let name = match op {
        CicPrimOp::Int63Add => "__coq_prim__.int63.add",
        CicPrimOp::Int63Sub => "__coq_prim__.int63.sub",
        CicPrimOp::Int63Mul => "__coq_prim__.int63.mul",
        CicPrimOp::Int63Div => "__coq_prim__.int63.div",
        CicPrimOp::Int63Mod => "__coq_prim__.int63.mod",
        CicPrimOp::Int63Land => "__coq_prim__.int63.land",
        CicPrimOp::Int63Lor => "__coq_prim__.int63.lor",
        CicPrimOp::Int63Lxor => "__coq_prim__.int63.lxor",
        CicPrimOp::Int63Lsl => "__coq_prim__.int63.lsl",
        CicPrimOp::Int63Lsr => "__coq_prim__.int63.lsr",
        CicPrimOp::Int63Eq => "__coq_prim__.int63.eq",
        CicPrimOp::Int63Lt => "__coq_prim__.int63.lt",
        CicPrimOp::Int63Le => "__coq_prim__.int63.le",
        CicPrimOp::Float64Add => "__coq_prim__.float64.add",
        CicPrimOp::Float64Sub => "__coq_prim__.float64.sub",
        CicPrimOp::Float64Mul => "__coq_prim__.float64.mul",
        CicPrimOp::Float64Div => "__coq_prim__.float64.div",
        CicPrimOp::Float64Eq => "__coq_prim__.float64.eq",
        CicPrimOp::Float64Lt => "__coq_prim__.float64.lt",
        CicPrimOp::Float64Le => "__coq_prim__.float64.le",
        CicPrimOp::Float64Sqrt => "__coq_prim__.float64.sqrt",
        CicPrimOp::Float64Neg => "__coq_prim__.float64.neg",
        CicPrimOp::PArrayGet => "__coq_prim__.parray.get",
        CicPrimOp::PArraySet => "__coq_prim__.parray.set",
        CicPrimOp::PArrayMake => "__coq_prim__.parray.make",
        CicPrimOp::PArrayLength => "__coq_prim__.parray.length",
    };
    let ni = w.add_string(name);
    w.add_expr(FlatExpr::const_ref(ni, u32::MAX))
}

/// Parse a primitive operation name (from SerAPI output) into a `CicPrimOp`.
pub(crate) fn parse_prim_op(name: &str) -> Result<CicPrimOp, MathverseError> {
    match name {
        "Int63add" | "int63_add" => Ok(CicPrimOp::Int63Add),
        "Int63sub" | "int63_sub" => Ok(CicPrimOp::Int63Sub),
        "Int63mul" | "int63_mul" => Ok(CicPrimOp::Int63Mul),
        "Int63div" | "int63_div" => Ok(CicPrimOp::Int63Div),
        "Int63mod" | "int63_mod" => Ok(CicPrimOp::Int63Mod),
        "Int63land" | "int63_land" => Ok(CicPrimOp::Int63Land),
        "Int63lor" | "int63_lor" => Ok(CicPrimOp::Int63Lor),
        "Int63lxor" | "int63_lxor" => Ok(CicPrimOp::Int63Lxor),
        "Int63lsl" | "int63_lsl" => Ok(CicPrimOp::Int63Lsl),
        "Int63lsr" | "int63_lsr" => Ok(CicPrimOp::Int63Lsr),
        "Int63eq" | "int63_eq" => Ok(CicPrimOp::Int63Eq),
        "Int63lt" | "int63_lt" => Ok(CicPrimOp::Int63Lt),
        "Int63le" | "int63_le" => Ok(CicPrimOp::Int63Le),
        "Float64add" | "float64_add" => Ok(CicPrimOp::Float64Add),
        "Float64sub" | "float64_sub" => Ok(CicPrimOp::Float64Sub),
        "Float64mul" | "float64_mul" => Ok(CicPrimOp::Float64Mul),
        "Float64div" | "float64_div" => Ok(CicPrimOp::Float64Div),
        "Float64eq" | "float64_eq" => Ok(CicPrimOp::Float64Eq),
        "Float64lt" | "float64_lt" => Ok(CicPrimOp::Float64Lt),
        "Float64le" | "float64_le" => Ok(CicPrimOp::Float64Le),
        "Float64sqrt" | "float64_sqrt" => Ok(CicPrimOp::Float64Sqrt),
        "Float64neg" | "float64_neg" => Ok(CicPrimOp::Float64Neg),
        "PArrayGet" | "parray_get" => Ok(CicPrimOp::PArrayGet),
        "PArraySet" | "parray_set" => Ok(CicPrimOp::PArraySet),
        "PArrayMake" | "parray_make" => Ok(CicPrimOp::PArrayMake),
        "PArrayLength" | "parray_length" => Ok(CicPrimOp::PArrayLength),
        _ => Err(coq_err(&format!("unknown primitive operation: {name}"))),
    }
}

/// Extract a kernel name from a nested sexp: atom, `(MutConstruct/MutInd "name" ...)`,
/// or `(MPdot/Constant/KerName ... "name")`.
fn extract_kernel_name(sexp: &Sexp) -> Result<String, MathverseError> {
    match sexp {
        Sexp::Atom(s) => Ok(s.clone()),
        Sexp::List(items) if !items.is_empty() => {
            let head = match &items[0] {
                Sexp::Atom(s) => s.as_str(),
                _ => return Err(coq_err("expected atom in kernel name")),
            };
            match head {
                "MutConstruct" | "MutInd" => get_str(items, 1),
                "MPdot" | "Constant" | "KerName" => items
                    .iter()
                    .rev()
                    .find_map(|i| match i {
                        Sexp::Atom(s) if s != head && s != "Relevant" && s != "Anonymous" => {
                            Some(Ok(s.clone()))
                        }
                        _ => None,
                    })
                    .unwrap_or_else(|| Err(coq_err("no name atom found"))),
                _ => Err(coq_err(&format!("unexpected kernel name form: {head}"))),
            }
        }
        _ => Err(coq_err("empty list in kernel name position")),
    }
}

/// Parse `(Fix/CoFix ((name ty body) ...) i)`.
fn parse_fix_bodies(
    items: &[Sexp],
    start: usize,
) -> Result<(Vec<(String, Box<CicTerm>, Box<CicTerm>)>, u32), MathverseError> {
    let body_list = match get_at(items, start)? {
        Sexp::List(v) => v,
        _ => return Err(coq_err("Fix bodies must be a list")),
    };
    let mut bodies = Vec::new();
    for b in body_list {
        match b {
            Sexp::List(bv) if bv.len() >= 3 => {
                bodies.push((
                    get_str(bv, 0)?,
                    Box::new(sexp_to_cic(get_at(bv, 1)?)?),
                    Box::new(sexp_to_cic(get_at(bv, 2)?)?),
                ));
            }
            _ => return Err(coq_err("invalid Fix body entry")),
        }
    }
    Ok((bodies, get_u32(items, start + 1)?))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// β-reduction / arity-synonym unfold de Bruijn correctness (0-based Rel).
    #[test]
    fn test_cic_beta_apply_and_arity_synonym_unfold() {
        // `Ensemble := λU. U → Prop` = Lambda(U, Type, Prod(_, Rel 0, Prop)).
        let ensemble_body = CicTerm::Lambda(
            "U".into(),
            Box::new(CicTerm::Sort(CicSort::type_at(1))),
            Box::new(CicTerm::Prod(
                "_".into(),
                Box::new(CicTerm::Rel(0)),
                Box::new(CicTerm::Sort(CicSort::Prop)),
            )),
        );
        assert!(
            type_synonym_body(&ensemble_body).is_some(),
            "a λ over a Π ending in a sort is a type synonym"
        );
        // A value with a body node (LetIn) is NOT a synonym.
        let not_syn = CicTerm::Lambda(
            "U".into(),
            Box::new(CicTerm::Sort(CicSort::type_at(1))),
            Box::new(CicTerm::LetIn(
                "z".into(),
                Box::new(CicTerm::Rel(0)),
                Box::new(CicTerm::Sort(CicSort::type_at(1))),
                Box::new(CicTerm::Sort(CicSort::Prop)),
            )),
        );
        assert!(type_synonym_body(&not_syn).is_none());

        // CicTerm has no PartialEq; compare Debug reprs (derived).
        let dbg = |t: &CicTerm| format!("{t:?}");

        // β-apply `Ensemble` to `Rel 0`: peels λU, substitutes → `Rel 0 → Prop`.
        let applied = cic_beta_apply(&ensemble_body, &[CicTerm::Rel(0)]);
        let expect_applied = CicTerm::Prod(
            "_".into(),
            Box::new(CicTerm::Rel(0)),
            Box::new(CicTerm::Sort(CicSort::Prop)),
        );
        assert_eq!(
            dbg(&applied),
            dbg(&expect_applied),
            "β must substitute the λ-binder with the argument"
        );

        // Full arity: `Empty_set : ∀U, Ensemble U`
        //   = Prod(U, Type, App(Const Ensemble, [Rel 0])) →
        //     Prod(U, Type, Prod(_, Rel 0, Prop)) = `∀U, U → Prop`.
        let mut ctx = SerapiNormCtx::default();
        // Dialect-sexp form of `λU. U → Prop` for the sexp synonym registry.
        let ensemble_body_sexp = Sexp::List(vec![
            Sexp::Atom("Lambda".into()),
            Sexp::Atom("U".into()),
            Sexp::List(vec![
                Sexp::Atom("Sort".into()),
                Sexp::List(vec![Sexp::Atom("Type".into()), Sexp::Atom("1".into())]),
            ]),
            Sexp::List(vec![
                Sexp::Atom("Prod".into()),
                Sexp::Atom("_".into()),
                Sexp::List(vec![Sexp::Atom("Rel".into()), Sexp::Atom("0".into())]),
                Sexp::List(vec![Sexp::Atom("Sort".into()), Sexp::Atom("Prop".into())]),
            ]),
        ]);
        ctx.register_type_synonym("Ensemble", ensemble_body, ensemble_body_sexp.clone());
        let arity = CicTerm::Prod(
            "U".into(),
            Box::new(CicTerm::Sort(CicSort::type_at(1))),
            Box::new(CicTerm::App(
                Box::new(CicTerm::Const("Ensemble".into())),
                vec![CicTerm::Rel(0)],
            )),
        );
        let unfolded = unfold_arity_synonym_codomain(&arity, &ctx).expect("synonym unfolds");
        let expect_unfolded = CicTerm::Prod(
            "U".into(),
            Box::new(CicTerm::Sort(CicSort::type_at(1))),
            Box::new(CicTerm::Prod(
                "_".into(),
                Box::new(CicTerm::Rel(0)),
                Box::new(CicTerm::Sort(CicSort::Prop)),
            )),
        );
        assert_eq!(
            dbg(&unfolded),
            dbg(&expect_unfolded),
            "arity codomain must delta-unfold to a Π ending in a sort"
        );
        // A non-synonym codomain (bare sort) is left untouched.
        let plain = CicTerm::Prod(
            "A".into(),
            Box::new(CicTerm::Sort(CicSort::type_at(1))),
            Box::new(CicTerm::Sort(CicSort::Prop)),
        );
        assert!(unfold_arity_synonym_codomain(&plain, &ctx).is_none());

        // SEXP mirror: `∀U, Ensemble U` unfolds to `∀U (_:U), Prop` in the
        // dialect, exposing the hidden index for the reconstruction registry.
        let arity_sexp = Sexp::List(vec![
            Sexp::Atom("Prod".into()),
            Sexp::Atom("U".into()),
            Sexp::List(vec![
                Sexp::Atom("Sort".into()),
                Sexp::List(vec![Sexp::Atom("Type".into()), Sexp::Atom("1".into())]),
            ]),
            Sexp::List(vec![
                Sexp::Atom("App".into()),
                Sexp::List(vec![
                    Sexp::Atom("Const".into()),
                    Sexp::Atom("Ensemble".into()),
                ]),
                Sexp::List(vec![Sexp::Atom("Rel".into()), Sexp::Atom("0".into())]),
            ]),
        ]);
        let unfolded_sexp =
            unfold_arity_synonym_codomain_sexp(&arity_sexp, &ctx).expect("sexp synonym unfolds");
        // Two Πs after unfold (the param `U` and the exposed index `_:U`).
        assert_eq!(
            dialect_count_prods(&unfolded_sexp),
            2,
            "sexp arity must expose the index hidden behind the synonym"
        );
        assert_eq!(
            dialect_sort_of(dialect_prod_codomain(&unfolded_sexp)),
            Some(CicSort::Prop),
            "unfolded sexp arity codomain must be the synonym's result sort"
        );
        // A bare-sort codomain in the sexp world is likewise untouched.
        let plain_sexp = Sexp::List(vec![
            Sexp::Atom("Prod".into()),
            Sexp::Atom("A".into()),
            Sexp::List(vec![
                Sexp::Atom("Sort".into()),
                Sexp::List(vec![Sexp::Atom("Type".into()), Sexp::Atom("1".into())]),
            ]),
            Sexp::List(vec![Sexp::Atom("Sort".into()), Sexp::Atom("Prop".into())]),
        ]);
        assert!(unfold_arity_synonym_codomain_sexp(&plain_sexp, &ctx).is_none());
    }

    /// The full dependency closure for the opaque Coq theorem
    /// `refl_n : forall n:nat, n = n`, whose Qed proof term is
    /// `fun n : nat => @eq_refl nat n`, extracted from SerAPI's
    /// `(Query () (Definition refl_n))`:
    ///
    /// - `nat` inductive (num_params=0): `O : nat`, `S : nat -> nat`.
    /// - `eq` inductive (PARAMETERIZED, num_params=1):
    ///   `eq : forall A:Type, A -> A -> Prop` with `eq_refl`.
    /// - `refl_n` definition carrying the genuine proof term as its value.
    ///
    /// In the importer dialect a Coq `Type@{0}` (the universe of `Set`/`nat`)
    /// is one level above `Prop`, encoded `(Sort (Type 1))`, so `@eq nat`
    /// universe-checks.
    const REFL_N_CLOSURE_SEXP: &str = r#"(CoqInductive nat 0 Set
  (Ctor O (Ind nat 0))
  (Ctor S (Prod n (Ind nat 0) (Ind nat 0))))
(CoqInductive eq 0 (Prod A (Sort (Type 1)) (Prod x (Rel 0) (Prod y (Rel 1) (Sort Prop))))
  (NumParams 1)
  (Ctor eq_refl (Prod A (Sort (Type 1)) (Prod x (Rel 0) (App (Ind eq 0) (Rel 1) (Rel 0) (Rel 0))))))
(CoqConstant refl_n
  (Prod n (Ind nat 0) (App (Ind eq 0) (Ind nat 0) (Rel 0) (Rel 0)))
  (Lambda n (Ind nat 0) (App (Construct eq 0 0) (Ind nat 0) (Rel 0))))"#;

    /// Dependency closure for `or_comm : forall A B:Prop, A \/ B -> B \/ A`,
    /// whose `Qed` proof term is a NON-RECURSIVE `match` on the hypothesis:
    /// `fun A B (H : or A B) => match H with or_introl a => or_intror a
    ///   | or_intror b => or_introl b end`.
    ///
    /// The match is encoded in the importer's structured `Case` dialect, which
    /// [`cic_to_flat_expr`] lowers to an application of the inductive's
    /// auto-generated recursor `or.0.rec` (kernel argument order
    /// `params → motive → minors → major`). The kernel typechecks that
    /// elimination, so `or_comm` becomes genuinely `KernelVerified`.
    ///
    /// - `or` inductive (num_params=2): `or_introl : A -> or A B`,
    ///   `or_intror : B -> or A B`. Both ctors quantify their two `Prop`
    ///   params explicitly, so a `(Construct or 0 j)` reference supplies them.
    /// - `or_comm` carries the genuine `match`-using proof term as its value.
    ///
    /// De Bruijn frame inside the proof body `λ A B (h : or A B). …`:
    /// `h = Rel 0`, `B = Rel 1`, `A = Rel 2`. The recursor lowering then threads
    /// each branch's own constructor-field binder, so the indices shift exactly
    /// as a hand-written `or.0.rec` application would (verified against the
    /// explicit-recursor form in `test_case_lowering_matches_manual_recursor`).
    const OR_COMM_CLOSURE_SEXP: &str = r#"(CoqInductive or 0 (Prod A (Sort Prop) (Prod B (Sort Prop) (Sort Prop)))
  (NumParams 2)
  (Ctor or_introl (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod a (Rel 1) (App (Ind or 0) (Rel 2) (Rel 1))))))
  (Ctor or_intror (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod b (Rel 0) (App (Ind or 0) (Rel 2) (Rel 1)))))))
(CoqConstant or_comm
  (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod h (App (Ind or 0) (Rel 1) (Rel 0)) (App (Ind or 0) (Rel 1) (Rel 2)))))
  (Lambda A (Sort Prop) (Lambda B (Sort Prop) (Lambda h (App (Ind or 0) (Rel 1) (Rel 0))
    (Case (Ind or 0)
      (Params (Rel 2) (Rel 1))
      (Motive (Lambda mot (App (Ind or 0) (Rel 2) (Rel 1)) (App (Ind or 0) (Rel 2) (Rel 3))))
      (Discriminant (Rel 0))
      (Branch (Lambda a (Rel 2) (App (Construct or 0 1) (Rel 2) (Rel 3) (Rel 0))))
      (Branch (Lambda b (Rel 1) (App (Construct or 0 0) (Rel 2) (Rel 3) (Rel 0)))))))))"#;

    /// Dependency closure for the RECURSIVE Coq definition
    /// `my_add := fix my_add (n m:nat) {struct n} : nat :=
    ///    match n with O => m | S p => S (my_add p m) end`
    /// (the same structural recursion as `Nat.add`).
    ///
    /// CIC has no primitive recursive definition: structural recursion on `n:nat`
    /// is an application of `nat`'s recursor `nat.0.rec`, where the recursive
    /// self-call `my_add p m` is supplied as the `S` minor premise's induction
    /// hypothesis. The importer encodes this in the structured `StructFix`
    /// dialect, which [`cic_to_flat_expr`] lowers to
    ///   `λ n m. @nat.0.rec.{1} (λ_.nat) m (λ p ih. S ih) n`
    /// (kernel argument order `motive → minors → major`, motive universe `1`
    /// because the motive returns `nat : Set`). The kernel typechecks AND
    /// iota-reduces that elimination, so `my_add` becomes genuinely
    /// `KernelVerified`.
    ///
    /// De Bruijn frame `λ n. λ m. …`: inside the recursor application `m = Rel 0`,
    /// `n = Rel 1`. The `O` branch returns `m = Rel 0`; the `S` branch
    /// `λ p. λ ih. S ih` returns `S` applied to the induction hypothesis
    /// `ih = Rel 0` (which carries `my_add p m`).
    const MY_ADD_CLOSURE_SEXP: &str = r#"(CoqInductive nat 0 Set
  (Ctor O (Ind nat 0))
  (Ctor S (Prod n (Ind nat 0) (Ind nat 0))))
(CoqConstant my_add
  (Prod n (Ind nat 0) (Prod m (Ind nat 0) (Ind nat 0)))
  (StructFix (Ind nat 0)
    (RecLevel 1)
    (StructTy (Ind nat 0))
    (Post (Ind nat 0))
    (Motive (Lambda x (Ind nat 0) (Ind nat 0)))
    (Branch (Rel 0))
    (Branch (Lambda p (Ind nat 0) (Lambda ih (Ind nat 0) (App (Construct nat 0 1) (Rel 0)))))))"#;

    /// The same `nat` + recursive `my_add`, PLUS the computational theorem
    /// `two_plus_two : my_add (S (S O)) (S (S O)) = S (S (S (S O)))` whose proof
    /// is `@eq_refl nat (S (S (S (S O))))`. This only type-checks if the kernel
    /// REDUCES `my_add 2 2` (iota on the imported `nat.0.rec`) to `4` while
    /// checking the `eq` — the real payoff of `Fix` support.
    const TWO_PLUS_TWO_CLOSURE_SEXP: &str = r#"(CoqInductive nat 0 Set
  (Ctor O (Ind nat 0))
  (Ctor S (Prod n (Ind nat 0) (Ind nat 0))))
(CoqInductive eq 0 (Prod A (Sort (Type 1)) (Prod x (Rel 0) (Prod y (Rel 1) (Sort Prop))))
  (NumParams 1)
  (Ctor eq_refl (Prod A (Sort (Type 1)) (Prod x (Rel 0) (App (Ind eq 0) (Rel 1) (Rel 0) (Rel 0))))))
(CoqConstant my_add
  (Prod n (Ind nat 0) (Prod m (Ind nat 0) (Ind nat 0)))
  (StructFix (Ind nat 0)
    (RecLevel 1)
    (StructTy (Ind nat 0))
    (Post (Ind nat 0))
    (Motive (Lambda x (Ind nat 0) (Ind nat 0)))
    (Branch (Rel 0))
    (Branch (Lambda p (Ind nat 0) (Lambda ih (Ind nat 0) (App (Construct nat 0 1) (Rel 0)))))))
(CoqConstant two_plus_two
  (App (Ind eq 0) (Ind nat 0)
    (App (Const my_add) (App (Construct nat 0 1) (App (Construct nat 0 1) (Construct nat 0 0))) (App (Construct nat 0 1) (App (Construct nat 0 1) (Construct nat 0 0))))
    (App (Construct nat 0 1) (App (Construct nat 0 1) (App (Construct nat 0 1) (App (Construct nat 0 1) (Construct nat 0 0))))))
  (App (Construct eq 0 0) (Ind nat 0)
    (App (Construct nat 0 1) (App (Construct nat 0 1) (App (Construct nat 0 1) (App (Construct nat 0 1) (Construct nat 0 0)))))))"#;

    /// The PARAMETERIZED inductive `eq` (one parameter `A`) carries
    /// `num_params=1` in its imported shard header, while the non-parameterized
    /// `nat` carries `num_params=0`. The corpus verifier reads this back to
    /// rebuild the family through checked `add_inductive`.
    #[test]
    fn test_import_parameterized_inductive_num_params() {
        let mut w = ShardWriter::new();
        CoqImporter
            .import_sexp(REFL_N_CLOSURE_SEXP, &mut w)
            .unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let by_name: std::collections::HashMap<&str, &MathverseConstantHeader> = reader
            .constants
            .iter()
            .map(|c| (reader.strings[c.name_idx as usize].as_str(), c))
            .collect();

        // `eq` is parameterized: NumParams 1 round-trips through the shard.
        let eq = by_name["eq.0"];
        assert_eq!(eq.decl_kind, DeclKind::Inductive as u8);
        assert_eq!(eq.inductive_decl_num_params(), Some(1));
        // `nat` defaults to num_params=0 (no NumParams element).
        assert_eq!(by_name["nat.0"].inductive_decl_num_params(), Some(0));
        // The opaque theorem is imported as a value-bearing Definition (its
        // proof term is the value), not an axiom.
        let refl_n = by_name["refl_n"];
        assert_eq!(refl_n.decl_kind, DeclKind::Definition as u8);
        assert!(refl_n.has_value(), "refl_n must carry its proof term");
    }

    /// End-to-end: the opaque Qed theorem `refl_n` plus its full dependency
    /// closure (including the parameterized `eq` inductive) is genuinely
    /// `KernelVerified` by the global corpus verifier — its proof term
    /// typechecks through the real kernel via `add_decl`.
    ///
    /// Negative control: dropping the proof term (importing `refl_n` as a
    /// `CoqAxiom`) must yield `AxiomAccepted`, never `KernelVerified` — proving
    /// it is the proof term, not the type, that the kernel checks.
    #[test]
    fn test_opaque_qed_proof_term_kernel_verifies() {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;

        let verify = |sexp: &str| {
            let mut w = ShardWriter::new();
            CoqImporter.import_sexp(sexp, &mut w).unwrap();
            let mut buf = Vec::new();
            w.write(&mut buf).unwrap();
            let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
            let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
            lib.load_shard(&reader).unwrap();
            let prelude =
                clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
            verify_corpus_incremental(&lib, prelude)
        };

        // Positive: every constant in the closure kernel-verifies, refl_n included.
        let report = verify(REFL_N_CLOSURE_SEXP);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert_eq!(
            report.axiom_fallback, 0,
            "no value may be masked by an axiom"
        );
        assert_eq!(report.kernel_verified, 6, "nat(3) + eq(2) + refl_n(1)");
        assert!(
            report.kernel_verified_names.contains(&"refl_n".to_string()),
            "the opaque Qed theorem refl_n must be genuinely KernelVerified, got {:?}",
            report.kernel_verified_names
        );

        // Negative control: same closure, but refl_n has NO proof term (CoqAxiom).
        // It must be AxiomAccepted (well-formed type, no proof checked), and must
        // NOT appear in the kernel-verified set.
        let axiom_closure = REFL_N_CLOSURE_SEXP
            .rsplit_once("(CoqConstant refl_n")
            .map(|(head, _)| {
                format!(
                    "{head}(CoqAxiom refl_n \
                     (Prod n (Ind nat 0) (App (Ind eq 0) (Ind nat 0) (Rel 0) (Rel 0))))"
                )
            })
            .expect("closure contains refl_n constant");
        let neg = verify(&axiom_closure);
        assert!(
            !neg.kernel_verified_names.contains(&"refl_n".to_string()),
            "without a proof term refl_n must NOT be KernelVerified"
        );
        assert_eq!(
            neg.axiom_accepted, 1,
            "the proofless refl_n axiom is AxiomAccepted, not kernel-checked"
        );
        assert_eq!(neg.kernel_verified, 5, "only the nat+eq family verifies");
    }

    // ---- Dumper-omitted-constant recovery: `NatTrec.add` reconstruction ----

    /// Raw SerAPI `nat` inductive (`Coq.Init.Datatypes.nat`), verbatim.
    const RAW_NAT_IND: &str = "(CoqInductive Coq.Init.Datatypes.nat 0 (Sort Set) (NumParams 0) (Ctor Coq.Init.Datatypes.O (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ()))))) (Ctor Coq.Init.Datatypes.S (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))))))";
    /// Raw SerAPI `eq` inductive (`Coq.Init.Logic.eq`), verbatim.
    const RAW_EQ_IND: &str = "(CoqInductive Coq.Init.Logic.eq 0 (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 739561026853) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 23503782208)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 2) (Sort Prop)))) (NumParams 2) (Ctor Coq.Init.Logic.eq_refl (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 739561026853) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 23503782208)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1) (Rel 1)))))))";

    fn nat_o() -> &'static str {
        "(Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 1) (Instance (() ()))))"
    }
    fn nat_s() -> &'static str {
        "(Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 2) (Instance (() ()))))"
    }
    /// Coq numeral `k` as raw SerAPI `S (S … O)`.
    fn nt_lit(k: u32) -> String {
        let mut t = nat_o().to_string();
        for _ in 0..k {
            t = format!("(App {} ({t}))", nat_s());
        }
        t
    }
    /// `@NatTrec.add a b` as raw SerAPI.
    fn nattrec_add_app(a: &str, b: &str) -> String {
        let f = "(Const ((Constant (KerName (MPdot (MPfile (DirPath ((Id ssrnat) (Id ssreflect) (Id mathcomp)))) (Id NatTrec)) (Id add)) ()) (Instance (() ()))))";
        format!("(App {f} ({a} {b}))")
    }
    fn nat_eq_type(lhs: &str, rhs: &str) -> String {
        let eq = "(Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ()))))";
        let nat = "(Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ()))))";
        format!("(App {eq} ({nat} {lhs} {rhs}))")
    }
    fn nat_eq_refl(v: &str) -> String {
        let refl = "(Construct ((((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) 1) (Instance (() ()))))";
        let nat = "(Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ()))))";
        format!("(App {refl} ({nat} {v}))")
    }

    fn verify_report(sexp: &str) -> crate::verify::incremental::IncrementalVerifyReport {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;
        let mut w = ShardWriter::new();
        CoqImporter.import_sexp(sexp, &mut w).unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).unwrap();
        let prelude =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        verify_corpus_incremental(&lib, prelude)
    }

    /// TEMPLATE-POLYMORPHISM round-trip: the emitted poly `prod` inductive
    /// replays through the checked `add_inductive` family path and — on the
    /// CUMULATIVE (Coq) lane — generates the LARGE-eliminating recursor with
    /// level params `[motive, u, v]` (3). The LEAN-lane control (no cumulativity)
    /// keeps the recursor Prop-only (`[u, v]`, 2), so no `.olean` recursor
    /// expectation changes. Companion to the kernel-level
    /// `coq_template_poly_prod_recursor_boundary.rs`, exercising the SHARD
    /// emission (`emit_template_poly_prod`) + shard→replay→env path.
    #[test]
    fn test_template_poly_prod_replays_large_elim_recursor_cumulative() {
        use crate::library::MathverseLibrary;
        use crate::shard::{ShardReader, ShardWriter};
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::{
            verify_corpus_incremental_with_env_policy, InductiveReplayPolicy,
        };

        let build_reader = || {
            let mut w = ShardWriter::new();
            emit_template_poly_prod(&mut w);
            let mut buf = Vec::new();
            w.write(&mut buf).unwrap();
            ShardReader::from_bytes(&buf).unwrap()
        };
        let replay = |cumulative: bool| {
            let reader = build_reader();
            let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
            lib.load_shard(&reader).unwrap();
            let mut prelude =
                clean_kernel::Environment::try_with_prelude().expect("kernel prelude");
            if cumulative {
                prelude.set_cumulative(true);
            }
            verify_corpus_incremental_with_env_policy(
                &lib,
                prelude,
                InductiveReplayPolicy::Generate,
            )
            .0
        };

        // Cumulative lane: 2 level params on the type, 3 on the recursor.
        let env = replay(true);
        let prod = env
            .get_const(&clean_kernel::Name::from_string(TEMPLATE_POLY_PROD))
            .expect("poly prod inductive replays");
        assert_eq!(
            prod.level_params.len(),
            2,
            "prod.{{u,v}} carries 2 level params"
        );
        let rec = env
            .get_const(&clean_kernel::Name::from_string(&format!(
                "{TEMPLATE_POLY_PROD}.rec"
            )))
            .expect("poly prod recursor generated");
        assert_eq!(
            rec.level_params.len(),
            3,
            "cumulative-lane poly prod recursor large-eliminates ([motive,u,v]); \
             got {:?}",
            rec.level_params
        );

        // Lean-lane control: the recursor stays Prop-only ([u,v], 2).
        let env = replay(false);
        let rec = env
            .get_const(&clean_kernel::Name::from_string(&format!(
                "{TEMPLATE_POLY_PROD}.rec"
            )))
            .expect("poly prod recursor generated on the lean lane too");
        assert_eq!(
            rec.level_params.len(),
            2,
            "lean-lane poly prod recursor stays Prop-only ([u,v]); got {:?}",
            rec.level_params
        );
    }

    /// TEMPLATE-POLYMORPHISM value paths through the cumulative corpus verifier:
    ///   * a `pair` value at the monomorphic `{1,1}` instance re-checks
    ///     `KernelVerified` (Construct + Ind lowering carry `{1,1}`, the poly
    ///     `pair` ctor accepts it);
    ///   * an eqmx-shaped `prod`-of-`Prop`s at a declared `Prop` codomain — which
    ///     the `{1,1}` (`Type`) rendering rejects — FLIPS `{1,1}→{0,0}` via the
    ///     incremental verifier's Prop-collapse retry and lands `KernelVerified`;
    ///   * NEGATIVE CONTROL: an ill-typed `pair` value (`b` field supplied an
    ///     `A`-typed term) is a genuine structural mismatch, NOT a universe
    ///     collapse, so it is withheld at EVERY `prod` instance — the flip never
    ///     launders it to `KernelVerified`.
    #[test]
    fn test_template_poly_prod_pair_kv_eqmx_flip_and_negative_control_cumulative() {
        use crate::library::MathverseLibrary;
        use crate::shard::{ShardReader, ShardWriter};
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::{
            verify_corpus_incremental_with_env_policy, InductiveReplayPolicy,
        };

        fn add_axiom(w: &mut ShardWriter, name: &str, sort: &CicTerm) {
            let ty = cic_to_flat_expr(sort, w);
            let ni = w.add_string(name);
            w.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: ty,
                value_idx: NO_VALUE,
                source_system: SourceSystem::Coq as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Axiom as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }
        fn add_def(w: &mut ShardWriter, name: &str, ty: &CicTerm, val: &CicTerm) {
            let ti = cic_to_flat_expr(ty, w);
            let vi = cic_to_flat_expr(val, w);
            let ni = w.add_string(name);
            w.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: ti,
                value_idx: vi,
                source_system: SourceSystem::Coq as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Definition as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }
        let cst = |n: &str| CicTerm::Const(n.to_string());
        let prod_app = |x: &str, y: &str| {
            CicTerm::App(
                Box::new(CicTerm::Ind("Coq.Init.Datatypes.prod".to_string(), 0)),
                vec![cst(x), cst(y)],
            )
        };
        let pair_app = |a2: &str, b2: &str, x: &str, y: &str| {
            CicTerm::App(
                Box::new(CicTerm::Construct(
                    "Coq.Init.Datatypes.prod".to_string(),
                    0,
                    0,
                )),
                vec![cst(a2), cst(b2), cst(x), cst(y)],
            )
        };

        let mut w = ShardWriter::new();
        emit_template_poly_prod(&mut w);
        add_axiom(&mut w, "P", &CicTerm::Sort(CicSort::Prop));
        add_axiom(&mut w, "Q", &CicTerm::Sort(CicSort::Prop));
        add_axiom(&mut w, "A", &CicTerm::Sort(CicSort::type_at(1)));
        add_axiom(&mut w, "B", &CicTerm::Sort(CicSort::type_at(1)));
        add_axiom(&mut w, "a", &cst("A"));
        add_axiom(&mut w, "b", &cst("B"));
        // pair value at {1,1}: pp : prod A B := pair A B a b  -> KernelVerified.
        add_def(
            &mut w,
            "pp",
            &prod_app("A", "B"),
            &pair_app("A", "B", "a", "b"),
        );
        // eqmx-shaped: E : Prop := prod P Q. Value renders prod.{1,1} P Q : Type,
        // rejected vs Prop -> flip {0,0} -> prod.{0,0} P Q : Prop -> KV.
        add_def(
            &mut w,
            "eqmx_shape",
            &CicTerm::Sort(CicSort::Prop),
            &prod_app("P", "Q"),
        );
        // NEGATIVE CONTROL: ill-typed pair (`b` field given `a : A`, expected B).
        add_def(
            &mut w,
            "bad",
            &prod_app("A", "B"),
            &pair_app("A", "B", "a", "a"),
        );

        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).unwrap();
        let mut prelude = clean_kernel::Environment::try_with_prelude().expect("kernel prelude");
        prelude.set_cumulative(true);
        let (env, _report) = verify_corpus_incremental_with_env_policy(
            &lib,
            prelude,
            InductiveReplayPolicy::Generate,
        );

        // A KernelVerified value-bearing decl is installed WITH its value; a
        // withheld (fallback / stand-in) one is installed value-less.
        let kv = |n: &str| {
            env.get_const(&clean_kernel::Name::from_string(n))
                .map(|c| c.value.is_some())
                .unwrap_or(false)
        };
        assert!(
            kv("pp"),
            "prod at {{1,1}} re-checks KernelVerified (pair value installed)"
        );
        assert!(
            kv("eqmx_shape"),
            "eqmx-shaped prod-of-Props flips {{1,1}}->{{0,0}} to KernelVerified"
        );
        assert!(
            !kv("bad"),
            "NEGATIVE CONTROL: ill-typed pair value is withheld at every prod \
             instance (the flip never launders it to KernelVerified)"
        );
    }

    /// ROUND-3 MIXED INSTANCE (the fix for round 2's 85 regressions): a SINGLE
    /// value carries BOTH a `Prop`-level `prod` (forced into a `Prop` position,
    /// so the `{1,1}` `Type` rendering is genuinely rejected) AND a `Type`-level
    /// `prod`/`pair` carrier that MUST stay `{1,1}`. A GLOBAL flip cannot satisfy
    /// both; the ENV-DIRECTED PER-INSTANCE flip renders each instance at the
    /// universe its own arguments demand and the value `KernelVerified`s.
    ///   * `mixed : prod R1 R2 := let _e : Prop := prod P Q in pair R1 R2 r1 r2`
    ///     — the `let`-value `prod P Q` flips to `{0,0}` (`P Q : Prop`) while the
    ///     body `pair R1 R2 r1 r2` and its `prod R1 R2` type stay `{1,1}`
    ///     (`R1 R2 : Type`). KV.
    ///   * NEGATIVE CONTROL `bad_mixed`: the same mix but the body `pair`'s
    ///     `b`-field is given `r1 : R1` (expected `R2`) — a genuine structural
    ///     mismatch the universe flip cannot repair, withheld at every instance.
    #[test]
    fn test_template_poly_prod_per_instance_mixed_kv_and_negative_control_cumulative() {
        use crate::library::MathverseLibrary;
        use crate::shard::{ShardReader, ShardWriter};
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::{
            verify_corpus_incremental_with_env_policy, InductiveReplayPolicy,
        };

        fn add_axiom(w: &mut ShardWriter, name: &str, sort: &CicTerm) {
            let ty = cic_to_flat_expr(sort, w);
            let ni = w.add_string(name);
            w.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: ty,
                value_idx: NO_VALUE,
                source_system: SourceSystem::Coq as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Axiom as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }
        fn add_def(w: &mut ShardWriter, name: &str, ty: &CicTerm, val: &CicTerm) {
            let ti = cic_to_flat_expr(ty, w);
            let vi = cic_to_flat_expr(val, w);
            let ni = w.add_string(name);
            w.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: ti,
                value_idx: vi,
                source_system: SourceSystem::Coq as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Definition as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }
        let cst = |n: &str| CicTerm::Const(n.to_string());
        let prod_app = |x: &str, y: &str| {
            CicTerm::App(
                Box::new(CicTerm::Ind("Coq.Init.Datatypes.prod".to_string(), 0)),
                vec![cst(x), cst(y)],
            )
        };
        let pair_app = |a2: &str, b2: &str, x: &str, y: &str| {
            CicTerm::App(
                Box::new(CicTerm::Construct(
                    "Coq.Init.Datatypes.prod".to_string(),
                    0,
                    0,
                )),
                vec![cst(a2), cst(b2), cst(x), cst(y)],
            )
        };
        // let _e : Prop := <prop-prod> in <type-body>. `CicTerm::LetIn` is
        // (name, VALUE, TYPE, body): the Prop-prod is the value, `Prop` its type.
        let mix = |body: CicTerm| {
            CicTerm::LetIn(
                "_e".to_string(),
                Box::new(prod_app("P", "Q")),
                Box::new(CicTerm::Sort(CicSort::Prop)),
                Box::new(body),
            )
        };

        let mut w = ShardWriter::new();
        emit_template_poly_prod(&mut w);
        add_axiom(&mut w, "P", &CicTerm::Sort(CicSort::Prop));
        add_axiom(&mut w, "Q", &CicTerm::Sort(CicSort::Prop));
        add_axiom(&mut w, "R1", &CicTerm::Sort(CicSort::type_at(1)));
        add_axiom(&mut w, "R2", &CicTerm::Sort(CicSort::type_at(1)));
        add_axiom(&mut w, "r1", &cst("R1"));
        add_axiom(&mut w, "r2", &cst("R2"));
        // MIXED: the Prop-prod (let value) needs {0,0}; the Type pair/prod (body,
        // declared type) must stay {1,1}. Per-instance flip -> KV.
        add_def(
            &mut w,
            "mixed",
            &prod_app("R1", "R2"),
            &mix(pair_app("R1", "R2", "r1", "r2")),
        );
        // NEGATIVE CONTROL: body pair's b-field is r1 : R1 (expected R2).
        add_def(
            &mut w,
            "bad_mixed",
            &prod_app("R1", "R2"),
            &mix(pair_app("R1", "R2", "r1", "r1")),
        );

        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).unwrap();
        let mut prelude = clean_kernel::Environment::try_with_prelude().expect("kernel prelude");
        prelude.set_cumulative(true);
        let (env, _report) = verify_corpus_incremental_with_env_policy(
            &lib,
            prelude,
            InductiveReplayPolicy::Generate,
        );

        let kv = |n: &str| {
            env.get_const(&clean_kernel::Name::from_string(n))
                .map(|c| c.value.is_some())
                .unwrap_or(false)
        };
        assert!(
            kv("mixed"),
            "MIXED value KVs: the Prop prod flips {{0,0}} while the Type carrier \
             stays {{1,1}} (a global flip could satisfy neither)"
        );
        assert!(
            !kv("bad_mixed"),
            "NEGATIVE CONTROL: the ill-typed Type-level pair is withheld at every \
             instance (the per-instance flip never launders it to KernelVerified)"
        );
    }

    /// The reconstructed `NatTrec.add` genuinely `KernelVerified`s AND reduces
    /// exactly as Coq's tail-recursive `add`: the compute witnesses
    /// `add 2 3 = 5` and `add 0 4 = 4` kernel-check ONLY if the imported `Fix`
    /// iota-reduces to Coq's value. NEGATIVE CONTROL: `add 2 3 = 6` (an off-by-
    /// one accumulator result) MUST fail — guarding the wrong-but-typechecking
    /// failure mode that a mis-threaded accumulator would produce.
    #[test]
    fn test_nattrec_add_reconstruction_computes() {
        let add_2_3 = nattrec_add_app(&nt_lit(2), &nt_lit(3));
        let ok = format!(
            "(CoqConstant test_add_2_3 {} {})",
            nat_eq_type(&add_2_3, &nt_lit(5)),
            nat_eq_refl(&nt_lit(5))
        );
        let add_0_4 = nattrec_add_app(&nt_lit(0), &nt_lit(4));
        let ok0 = format!(
            "(CoqConstant test_add_0_4 {} {})",
            nat_eq_type(&add_0_4, &nt_lit(4)),
            nat_eq_refl(&nt_lit(4))
        );
        let positive =
            format!("{RAW_NAT_IND}\n{RAW_EQ_IND}\n{SYNTH_NATTREC_ADD_SEXP}\n{ok}\n{ok0}");
        let report = verify_report(&positive);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"mathcomp.ssreflect.ssrnat.NatTrec.add".to_string()),
            "reconstructed NatTrec.add must be KernelVerified, got {:?}",
            report.kernel_verified_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"test_add_2_3".to_string())
                && report
                    .kernel_verified_names
                    .contains(&"test_add_0_4".to_string()),
            "compute witnesses (add 2 3 = 5, add 0 4 = 4) must kernel-verify — the Fix \
             must reduce as Coq's add does, got {:?}",
            report.kernel_verified_names
        );

        // NEGATIVE CONTROL: add 2 3 = 6 is FALSE (add 2 3 = 5). The kernel must
        // reject the eq_refl proof — a reconstruction that produced 6 would flip
        // these two assertions and be caught.
        let bad = format!(
            "(CoqConstant test_add_2_3_wrong {} {})",
            nat_eq_type(&add_2_3, &nt_lit(6)),
            nat_eq_refl(&nt_lit(6))
        );
        let negative = format!("{RAW_NAT_IND}\n{RAW_EQ_IND}\n{SYNTH_NATTREC_ADD_SEXP}\n{bad}");
        let neg = verify_report(&negative);
        assert!(
            !neg.kernel_verified_names
                .contains(&"test_add_2_3_wrong".to_string()),
            "add 2 3 = 6 is false and MUST NOT kernel-verify (wrong-but-typechecking guard)"
        );
    }

    /// The recovery detector injects `NatTrec.add` EXACTLY when its anchor
    /// sibling `add_mul` is defined here, `add` is referenced, and `add` is not
    /// already defined — the single-injection guarantee. When `add` is already
    /// present (a hypothetical future re-dump), it injects nothing.
    #[test]
    fn test_recover_omitted_constants_single_injection() {
        // Anchor present + add referenced + add absent → inject exactly one.
        let anchor = "(CoqConstant mathcomp.ssreflect.ssrnat.NatTrec.add_mul (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 1) (Instance (() ())))))";
        let ref_add = format!(
            "(CoqConstant test_uses_add (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) {})",
            nattrec_add_app(&nt_lit(1), &nt_lit(1))
        );
        let forms = parse_sexps(&format!("{anchor}\n{ref_add}")).unwrap();
        let recovered = recover_dumper_omitted_constants(&forms);
        assert_eq!(
            recovered.len(),
            1,
            "add_mul anchor + add ref → inject add once"
        );
        assert_eq!(
            top_level_declared_name(&recovered[0]),
            Some("mathcomp.ssreflect.ssrnat.NatTrec.add"),
            "the injected form is the reconstructed NatTrec.add"
        );

        // A file that references add but LACKS the anchor (like `prime`) injects
        // nothing — it resolves add from the dependency-closed shard instead.
        let no_anchor = parse_sexps(&ref_add).unwrap();
        assert!(
            recover_dumper_omitted_constants(&no_anchor).is_empty(),
            "without the anchor sibling, no injection (avoids duplicate emission)"
        );

        // add already defined → no injection (future re-dump disables recovery).
        let with_add =
            parse_sexps(&format!("{anchor}\n{ref_add}\n{SYNTH_NATTREC_ADD_SEXP}")).unwrap();
        assert!(
            recover_dumper_omitted_constants(&with_add).is_empty(),
            "when add is already defined the recovery is a no-op"
        );
    }

    /// End-to-end: importing a module that DEFINES the anchor and REFERENCES
    /// `NatTrec.add` (but never defines it — the real ssrnat situation) auto-
    /// injects the reconstruction, so both `add` and the referencing witness
    /// become `KernelVerified` with no explicit `add` in the input.
    #[test]
    fn test_nattrec_add_auto_injected_end_to_end() {
        let anchor = "(CoqConstant mathcomp.ssreflect.ssrnat.NatTrec.add_mul (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 1) (Instance (() ())))))";
        let witness = format!(
            "(CoqConstant test_add_via_injection {} {})",
            nat_eq_type(&nattrec_add_app(&nt_lit(2), &nt_lit(3)), &nt_lit(5)),
            nat_eq_refl(&nt_lit(5))
        );
        // NOTE: no explicit NatTrec.add in the stream — it must be injected.
        let module = format!("{RAW_NAT_IND}\n{RAW_EQ_IND}\n{anchor}\n{witness}");
        assert!(
            !module.contains("(CoqConstant mathcomp.ssreflect.ssrnat.NatTrec.add "),
            "test precondition: add is NOT explicitly defined in the module"
        );
        let report = verify_report(&module);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"mathcomp.ssreflect.ssrnat.NatTrec.add".to_string()),
            "the auto-injected NatTrec.add must be KernelVerified, got {:?}",
            report.kernel_verified_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"test_add_via_injection".to_string()),
            "the witness referencing the injected add must kernel-verify"
        );
    }

    /// The RAW SerAPI text of `Coq.ssr.ssreflect.ssr_have_upoly`'s TYPE and
    /// VALUE, verbatim from the corpus dump (the measured sort-polymorphic
    /// decl class: 1,426 fully-quality-specialized mathcomp references),
    /// with only the constant renamed to `SerTop.up`.
    const UPOLY_TYPE_SEXP: &str = "(Prod ((binder_name (Name (Id Plemma))) (binder_relevance Relevant)) (Sort (QSort (Var 0) ((((hash 14) (data (Var 0))) 0)))) (Prod ((binder_name (Name (Id Pgoal))) (binder_relevance Relevant)) (Sort (QSort (Var 1) ((((hash 15) (data (Var 1))) 0)))) (Prod ((binder_name (Name (Id step))) (binder_relevance (RelevanceVar (Var 0)))) (Rel 2) (Prod ((binder_name (Name (Id rest))) (binder_relevance (RelevanceVar (Var 1)))) (Prod ((binder_name Anonymous) (binder_relevance (RelevanceVar (Var 0)))) (Rel 3) (Rel 3)) (Rel 3)))))";
    const UPOLY_VALUE_SEXP: &str = "(Lambda ((binder_name (Name (Id Plemma))) (binder_relevance Relevant)) (Sort (QSort (Var 0) ((((hash 14) (data (Var 0))) 0)))) (Lambda ((binder_name (Name (Id Pgoal))) (binder_relevance Relevant)) (Sort (QSort (Var 1) ((((hash 15) (data (Var 1))) 0)))) (Lambda ((binder_name (Name (Id step))) (binder_relevance (RelevanceVar (Var 0)))) (Rel 2) (Lambda ((binder_name (Name (Id rest))) (binder_relevance (RelevanceVar (Var 1)))) (Prod ((binder_name Anonymous) (binder_relevance (RelevanceVar (Var 0)))) (Rel 3) (Rel 3)) (App (Rel 1) ((Rel 2)))))))";

    /// The fused quality+level pairing derives from the real `ssr_have_upoly`
    /// shapes: quality `Var q` paired 1:1 with level `Var q`, two params.
    #[test]
    fn test_derive_sort_poly_shape_ssr_have_upoly_pairing() {
        let ty = parse_sexp(UPOLY_TYPE_SEXP).expect("type sexp parses");
        let val = parse_sexp(UPOLY_VALUE_SEXP).expect("value sexp parses");
        let shape = derive_sort_poly_shape(&ty, Some(&val))
            .expect("the ssr_have_upoly shape must qualify for the fused encoding");
        assert_eq!(shape.pairing, vec![0, 1], "quality q pairs with level q");
        assert_eq!(shape.level_count, 2);
        assert_eq!(
            shape.param_names(),
            vec!["u0".to_string(), "u1".to_string()],
            "params are synthesized in quality-index order"
        );
    }

    /// Non-qualifying shapes fail closed to `None` (today's behavior): a
    /// nonzero increment, an inconsistent pairing, and a decl that also
    /// mentions a `(Var …)` datum inside a collapsed `(Type …)` payload
    /// (identity split).
    #[test]
    fn test_derive_sort_poly_shape_rejects_nonqualifying() {
        let qsort = |q: u32, k: u32, incr: u32| {
            format!("(Sort (QSort (Var {q}) ((((hash 1) (data (Var {k}))) {incr}))))")
        };
        let prod = |dom: &str, cod: &str| {
            format!("(Prod ((binder_name Anonymous) (binder_relevance Relevant)) {dom} {cod})")
        };
        // Nonzero increment: out of the fused model.
        let t = parse_sexp(&prod(&qsort(0, 0, 1), "(Rel 1)")).unwrap();
        assert!(derive_sort_poly_shape(&t, None).is_none(), "incr != 0");
        // Inconsistent pairing: quality 0 paired with two different levels.
        let t = parse_sexp(&prod(&qsort(0, 0, 0), &prod(&qsort(0, 1, 0), "(Rel 1)"))).unwrap();
        assert!(derive_sort_poly_shape(&t, None).is_none(), "non-functional");
        // Non-injective pairing: two qualities sharing one level var.
        let t = parse_sexp(&prod(&qsort(0, 0, 0), &prod(&qsort(1, 0, 0), "(Rel 1)"))).unwrap();
        assert!(derive_sort_poly_shape(&t, None).is_none(), "non-injective");
        // Non-contiguous quality indices (starts at 1).
        let t = parse_sexp(&prod(&qsort(1, 1, 0), "(Rel 1)")).unwrap();
        assert!(derive_sort_poly_shape(&t, None).is_none(), "gap at q0");
        // A (Var …) datum inside a collapsed (Type …) payload splits identity.
        let t = parse_sexp(&prod(
            &qsort(0, 0, 0),
            &prod("(Sort (Type ((((hash 2) (data (Var 1))) 0))))", "(Rel 1)"),
        ))
        .unwrap();
        assert!(derive_sort_poly_shape(&t, None).is_none(), "Type-Var mix");
        // No QSort at all: nothing to bind.
        let t = parse_sexp("(Sort Prop)").unwrap();
        assert!(derive_sort_poly_shape(&t, None).is_none(), "no QSort");
    }

    /// Instance translation for a registered poly constant: `QProp` fuses to
    /// level 0, `QType` at any in-model atomic datum fuses to level 1;
    /// `QSProp`, quality variables, and arity disagreements fail to `None`.
    #[test]
    fn test_translate_poly_ref_instance_qconstant_shapes() {
        let info = CoqSortPolyShape {
            pairing: vec![0, 1],
            level_count: 2,
        };
        let payload = |quals: &str, levels: &str| {
            parse_sexp(&format!(
                "(((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id up)) ())) \
                 (Instance ({quals} {levels})))"
            ))
            .expect("payload parses")
        };
        // The dominant measured shape: (QType, QProp | Set, Set) -> [1, 0].
        let p = payload(
            "((QConstant QType) (QConstant QProp))",
            "(((hash 9) (data SProp)) ((hash 9) (data SProp)))",
        );
        assert_eq!(translate_poly_ref_instance(&p, &info), Some(vec![1, 0]));
        // Named global level datum under QType also fuses to 1.
        let p = payload(
            "((QConstant QProp) (QConstant QType))",
            "(((hash 9) (data SProp)) ((hash 3) (data (Level ((DirPath ((Id m))) 42)))))",
        );
        assert_eq!(translate_poly_ref_instance(&p, &info), Some(vec![0, 1]));
        // QSProp: out of model.
        let p = payload(
            "((QConstant QSProp) (QConstant QProp))",
            "(((hash 9) (data SProp)) ((hash 9) (data SProp)))",
        );
        assert_eq!(translate_poly_ref_instance(&p, &info), None);
        // Quality VARIABLE: out of model.
        let p = payload(
            "((QVar 0) (QConstant QProp))",
            "(((hash 9) (data SProp)) ((hash 9) (data SProp)))",
        );
        assert_eq!(translate_poly_ref_instance(&p, &info), None);
        // Arity disagreement (1 quality for a 2-param constant): fail closed.
        let p = payload("((QConstant QType))", "(((hash 9) (data SProp)))");
        assert_eq!(translate_poly_ref_instance(&p, &info), None);
    }

    /// END-TO-END sort-polymorphism: the real `ssr_have_upoly` decl imports
    /// with a 2-param `level_params` window whose string-table block is
    /// CONTIGUOUS (the add_string vs add_string_block trap — the fixture
    /// pre-interns `u0` as a constant name so a deduplicating intern would
    /// corrupt the window), a fully-quality-specialized reference translates
    /// to an explicit level instance, and BOTH declarations genuinely
    /// kernel-verify through the corpus verifier.
    #[test]
    fn test_sort_poly_decl_and_reference_kernel_verify() {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;

        let up_ref = "(Const ((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id up)) ()) \
             (Instance (((QConstant QType) (QConstant QProp)) \
             (((hash 9) (data SProp)) ((hash 9) (data SProp)))))))";
        let sexp = format!(
            "(CoqAxiom u0 (Sort Prop))\n\
             (CoqInductive myunit 0 Set (Ctor mytt (Ind myunit 0)))\n\
             (CoqInductive mytrue 0 Prop (Ctor myI (Ind mytrue 0)))\n\
             (CoqConstant SerTop.up {UPOLY_TYPE_SEXP} {UPOLY_VALUE_SEXP})\n\
             (CoqConstant SerTop.uses (Ind mytrue 0) \
              (App {up_ref} ((Ind myunit 0) (Ind mytrue 0) (Construct myunit 0 0) \
               (Lambda x (Ind myunit 0) (Construct mytrue 0 0)))))"
        );

        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&sexp, &mut w).expect("import runs");
        assert_eq!(stats.skipped, 0, "skips: {:?}", stats.skip_reasons);
        assert_eq!(
            stats.value_translation_failed, 0,
            "dropped values: {:?}",
            stats.value_failure_reasons
        );

        let mut buf = Vec::new();
        w.write(&mut buf).expect("shard serializes");
        let reader = crate::shard::ShardReader::from_bytes(&buf).expect("shard reads back");
        let by_name: std::collections::HashMap<&str, &MathverseConstantHeader> = reader
            .constants
            .iter()
            .map(|c| (reader.strings[c.name_idx as usize].as_str(), c))
            .collect();

        // Poly round-trip guard: the window is contiguous and reconstructs to
        // the synthesized names even though "u0" was interned earlier.
        let up = by_name["SerTop.up"];
        assert_eq!(up.level_params_count, 2, "two fused level params");
        let start = up.level_params_start as usize;
        assert_eq!(
            &reader.strings[start..start + 2],
            &["u0".to_string(), "u1".to_string()],
            "the level_params window must be a contiguous add_string_block"
        );
        assert!(
            up.profile().has_bit(AxiomProfile::SPECULATIVE_MOTIVE.0),
            "poly emission is a kernel-arbitrated guess (fail-closed marker)"
        );
        let uses = by_name["SerTop.uses"];
        assert!(
            uses.profile().has_bit(AxiomProfile::SPECULATIVE_MOTIVE.0),
            "translated-instance references carry the fail-closed marker too"
        );
        assert_eq!(
            uses.level_params_count, 0,
            "the REFERRER itself is monomorphic"
        );

        // The kernel is the arbiter: both the generic poly definition and its
        // instantiated use must genuinely verify.
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).expect("library loads");
        let prelude =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        let report = verify_corpus_incremental(&lib, prelude);
        assert_eq!(report.failed, 0, "failures: {:?}", report.failures);
        for name in ["SerTop.up", "SerTop.uses"] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be genuinely KernelVerified, got {:?} (fallbacks: {:?})",
                report.kernel_verified_names,
                report.axiom_fallback_names
            );
        }
    }

    /// RECORD-STAND-IN ALIAS end-to-end (the 2026-07-11 reject census's #1
    /// mathcomp blocker): a SerAPI `(Ind <name> 0)` reference to a poison-crash
    /// record salvaged as a TYPE-ONLY `(CoqAxiom <name> …)` stand-in must
    /// alias to the CONSTANT spelling `<name>` (not the inductive spelling
    /// `<name>.0`, which the corpus can never define), carry the fail-closed
    /// SPECULATIVE marker, and genuinely kernel-verify against the stand-in.
    ///
    /// Negative control: with the stand-in ABSENT the alias must not fire and
    /// the reference keeps today's failing `<name>.0` spelling — proving the
    /// stand-in lookup (not something else) is load-bearing.
    #[test]
    fn test_record_standin_ind_reference_aliases_to_axiom_constant() {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;

        // The real dumps spell record references with an MPdot module path
        // (`mathcomp.ssreflect.fintype.Finite.class_of`); mirror that shape.
        let class_ref = "(Ind (((MutInd (KerName (MPdot (MPfile (DirPath ((Id SerTop)))) \
             (Id M)) (Id class_of)) ()) 0) (Instance (() ()))))";
        // A named-Level SerAPI `Type` payload (collapses to the importer Type 1).
        let ty1 = "(Sort (Type ((((hash 1) (data (Level ((DirPath ((Id SerTop))) 1)))) 0))))";
        let standin = "(CoqAxiom SerTop.M.class_of (Prod _ (Sort (Type 1)) (Sort (Type 1))))";
        let id_class = format!(
            "(CoqConstant SerTop.M.id_class \
             (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) {ty1} \
              (Prod ((binder_name (Name (Id c))) (binder_relevance Relevant)) \
               (App {class_ref} ((Rel 1))) (App {class_ref} ((Rel 2))))) \
             (Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) {ty1} \
              (Lambda ((binder_name (Name (Id c))) (binder_relevance Relevant)) \
               (App {class_ref} ((Rel 1))) (Rel 1))))"
        );

        let verify = |sexp: &str| {
            let mut w = ShardWriter::new();
            let stats = CoqImporter.import_sexp(sexp, &mut w).expect("import runs");
            assert_eq!(stats.skipped, 0, "skips: {:?}", stats.skip_reasons);
            let mut buf = Vec::new();
            w.write(&mut buf).expect("shard serializes");
            let reader = crate::shard::ShardReader::from_bytes(&buf).expect("shard reads back");
            let speculative = reader
                .constants
                .iter()
                .find(|c| reader.strings[c.name_idx as usize] == "SerTop.M.id_class")
                .expect("id_class in shard")
                .profile()
                .has_bit(AxiomProfile::SPECULATIVE_MOTIVE.0);
            let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
            lib.load_shard(&reader).expect("library loads");
            let prelude =
                clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
            (speculative, verify_corpus_incremental(&lib, prelude))
        };

        // Positive: the stand-in is present → the reference aliases, the decl
        // is marked speculative (kernel-arbitrated guess), and the kernel
        // genuinely proof-checks the value against the stand-in.
        let (speculative, report) = verify(&format!("{standin}\n{id_class}"));
        assert!(
            speculative,
            "an aliased reference is a guess and must carry the fail-closed marker"
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"SerTop.M.id_class".to_string()),
            "id_class must genuinely KernelVerify against the stand-in, got {:?} \
             (fallbacks: {:?}, failures: {:?})",
            report.kernel_verified_names,
            report.axiom_fallback_names,
            report.failures
        );

        // Negative: no stand-in → no alias, no marker; the reference keeps the
        // undefined `<name>.0` spelling and the decl is NOT kernel-verified.
        let (speculative, report) = verify(&id_class);
        assert!(!speculative, "without a stand-in the alias must not fire");
        assert!(
            !report
                .kernel_verified_names
                .contains(&"SerTop.M.id_class".to_string()),
            "without the stand-in the reference must keep failing (fail closed)"
        );
    }

    /// ALIAS PRIORITY negative: a reference to a name that IS a registered
    /// inductive must never alias — the inductive spelling `<name>.0` wins
    /// even when a same-named sort-codomain constant also exists.
    #[test]
    fn test_record_standin_alias_never_fires_for_registered_inductive() {
        let t_ref = "(Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id t)) ()) 0) \
             (Instance (() ()))))";
        let sexp = format!(
            "(CoqInductive SerTop.t 0 Set (Ctor SerTop.mk (Ind SerTop.t 0)))\n\
             (CoqAxiom SerTop.t (Prod _ (Sort (Type 1)) (Sort (Type 1))))\n\
             (CoqAxiom SerTop.uses_t {t_ref})"
        );
        let mut w = ShardWriter::new();
        CoqImporter.import_sexp(&sexp, &mut w).expect("import runs");
        let mut buf = Vec::new();
        w.write(&mut buf).expect("shard serializes");
        let reader = crate::shard::ShardReader::from_bytes(&buf).expect("shard reads back");
        let uses_t = reader
            .constants
            .iter()
            .find(|c| reader.strings[c.name_idx as usize] == "SerTop.uses_t")
            .expect("uses_t in shard");
        let ty_str =
            crate::inductive_replay::reconstruct_constant("SerTop.uses_t", &reader, uses_t)
                .expect("uses_t type reconstructs")
                .type_expr
                .to_string();
        assert!(
            ty_str.contains("SerTop.t.0"),
            "a registered inductive keeps its `.0` spelling, got {ty_str}"
        );
    }

    /// FAIL-CLOSED negative: without a qualifying pairing (nonzero increment)
    /// the decl keeps today's behavior exactly — the `QSort` sort is
    /// out-of-model and the constant is SKIPPED with the universe reason.
    #[test]
    fn test_sort_poly_nonqualifying_qsort_still_skips() {
        let bad_type = "(Prod ((binder_name (Name (Id P))) (binder_relevance Relevant)) \
             (Sort (QSort (Var 0) ((((hash 14) (data (Var 0))) 1)))) (Rel 1))";
        let sexp = format!("(CoqConstant SerTop.bad {bad_type})");
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&sexp, &mut w).expect("import runs");
        assert_eq!(stats.skipped, 1, "the decl must stay skipped");
        assert!(
            stats.skip_reasons[0].1.contains("out-of-model (universe)"),
            "reason must stay the loud universe reject: {:?}",
            stats.skip_reasons
        );
    }

    #[test]
    fn test_parse_atoms_and_lists() {
        assert_eq!(parse_sexp("hello").unwrap(), Sexp::Atom("hello".into()));
        assert_eq!(parse_sexp("42").unwrap(), Sexp::Atom("42".into()));
        assert_eq!(parse_sexp("()").unwrap(), Sexp::List(vec![]));
        assert_eq!(
            parse_sexp("(a b c)").unwrap(),
            Sexp::List(vec![
                Sexp::Atom("a".into()),
                Sexp::Atom("b".into()),
                Sexp::Atom("c".into())
            ])
        );
    }

    #[test]
    fn test_parse_nested_and_strings() {
        assert!(matches!(&parse_sexp("(a (b (c d)))").unwrap(), Sexp::List(v) if v.len() == 2));
        assert_eq!(
            parse_sexp(r#"(name "hello world")"#).unwrap(),
            Sexp::List(vec![
                Sexp::Atom("name".into()),
                Sexp::Atom("hello world".into())
            ])
        );
        assert_eq!(parse_sexps("(a) (b c)").unwrap().len(), 2);
    }

    #[test]
    fn test_parse_errors() {
        assert_eq!(
            parse_sexp("(a b").unwrap_err(),
            SexpError::UnmatchedParen(0)
        );
        assert_eq!(
            parse_sexp(")").unwrap_err(),
            SexpError::UnexpectedChar(')', 0)
        );
        assert_eq!(parse_sexp("").unwrap_err(), SexpError::UnexpectedEof);
    }

    #[test]
    fn test_sexp_to_cic_basic() {
        assert!(matches!(
            sexp_to_cic(&parse_sexp("(Rel 3)").unwrap()).unwrap(),
            CicTerm::Rel(3)
        ));
        assert!(matches!(
            sexp_to_cic(&parse_sexp("(Sort Prop)").unwrap()).unwrap(),
            CicTerm::Sort(CicSort::Prop)
        ));
        assert!(matches!(
            sexp_to_cic(&parse_sexp("(Sort (Type 2))").unwrap()).unwrap(),
            CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Type(2)))
        ));
        assert!(
            matches!(sexp_to_cic(&parse_sexp("(Const Nat.add)").unwrap()).unwrap(), CicTerm::Const(n) if n == "Nat.add")
        );
    }

    #[test]
    fn test_normalize_serapi_self_contained_term() {
        // Real `sertop --printer=sertop` output for the polymorphic identity
        // `Definition idpoly : forall A:Type, A -> A := fun (A:Type)(x:A) => x.`
        let src = r#"(Lambda((binder_name(Name(Id A)))(binder_relevance Relevant))(Sort(Type((((hash 1)(data(Level((DirPath((Id SerTop)))1))))0))))(Lambda((binder_name(Name(Id x)))(binder_relevance Relevant))(Rel 1)(Rel 1)))"#;
        let parsed = parse_sexp(src).expect("parse serapi lambda");
        let normalized = normalize_serapi_rec(&parsed, &SerapiNormCtx::default(), &[]);
        let cic = sexp_to_cic(&normalized).expect("normalize+lower serapi term");
        // Outer node is a Lambda binding A : Type.
        match cic {
            CicTerm::Lambda(n, ty, body) => {
                assert_eq!(n, "A");
                // SerAPI `(A : Type)` normalizes to importer `(Type 1)`, the
                // `Set`/`Type@{0}` level (`Sort(Succ Zero)` once lowered).
                assert!(matches!(
                    *ty,
                    CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Type(1)))
                ));
                // Inner: Lambda x : (Rel 0) => (Rel 0). SerAPI Rel 1 -> 0-based 0.
                match *body {
                    CicTerm::Lambda(xn, xty, xbody) => {
                        assert_eq!(xn, "x");
                        assert!(matches!(*xty, CicTerm::Rel(0)));
                        assert!(matches!(*xbody, CicTerm::Rel(0)));
                    }
                    other => panic!("expected inner Lambda, got {other:?}"),
                }
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    #[test]
    fn test_normalize_serapi_kernel_names() {
        let ctx = SerapiNormCtx::default();
        // (Const ((Constant (KerName (MPfile (DirPath ...)) (Id idnat)) ()) (Instance (()()))))
        // — the DirPath is a single segment, so the qualified name is
        // `SerTop.idnat`.
        let const_src = r#"(Const((Constant(KerName(MPfile(DirPath((Id SerTop))))(Id idnat))())(Instance(()()))))"#;
        let c = sexp_to_cic(&normalize_serapi_rec(
            &parse_sexp(const_src).unwrap(),
            &ctx,
            &[],
        ))
        .unwrap();
        assert!(
            matches!(c, CicTerm::Const(ref n) if n == "SerTop.idnat"),
            "got {c:?}"
        );

        // (Ind (((MutInd (KerName ... (Id nat)) ()) 0) (Instance (()())))) —
        // DirPath segments are reversed: Coq.Init.Datatypes.nat.
        let ind_src = r#"(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))"#;
        let i = sexp_to_cic(&normalize_serapi_rec(
            &parse_sexp(ind_src).unwrap(),
            &ctx,
            &[],
        ))
        .unwrap();
        assert!(
            matches!(i, CicTerm::Ind(ref n, 0) if n == "Coq.Init.Datatypes.nat"),
            "got {i:?}"
        );

        // (Construct ((((MutInd ... (Id eq)) ()) 0) 1) (Instance (()()))))
        //  -> Coq.Init.Logic.eq block 0, ctor 0 (SerAPI j is 1-based).
        let ctor_src = r#"(Construct((((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id eq))())0)1)(Instance(()()))))"#;
        let c2 = sexp_to_cic(&normalize_serapi_rec(
            &parse_sexp(ctor_src).unwrap(),
            &ctx,
            &[],
        ))
        .unwrap();
        assert!(
            matches!(c2, CicTerm::Construct(ref n, 0, 0) if n == "Coq.Init.Logic.eq"),
            "got {c2:?}"
        );

        // MPdot module paths append their segment.
        let mpdot_src = r#"(Const((Constant(KerName(MPdot(MPfile(DirPath((Id Init)(Id Coq))))(Id Nat))(Id add))())(Instance(()()))))"#;
        let c3 = sexp_to_cic(&normalize_serapi_rec(
            &parse_sexp(mpdot_src).unwrap(),
            &ctx,
            &[],
        ))
        .unwrap();
        assert!(
            matches!(c3, CicTerm::Const(ref n) if n == "Coq.Init.Nat.add"),
            "got {c3:?}"
        );

        // KerPair Dual (module-alias reference): `(Constant (KerName <user>)
        // ((KerName <canonical>)))`. Resolution is REGISTRY-AWARE
        // (`resolve_kerpair_name`): with an EMPTY known-name registry the USER
        // spelling wins (the historical behavior — measured 2026-07-13:
        // unconditional canonical preference regressed 125 stdlib constants
        // whose canonical target is not dumped). Real measured shape:
        // `Positive_as_OT.mul` (alias) vs `BinPosDef.Pos.mul` (canonical).
        let dual_src = r#"(Const((Constant(KerName(MPdot(MPfile(DirPath((Id POrderedType)(Id PArith)(Id Coq))))(Id Positive_as_OT))(Id mul))((KerName(MPdot(MPfile(DirPath((Id BinPosDef)(Id PArith)(Id Coq))))(Id Pos))(Id mul))))(Instance(()()))))"#;
        let c4 = sexp_to_cic(&normalize_serapi_rec(
            &parse_sexp(dual_src).unwrap(),
            &ctx,
            &[],
        ))
        .unwrap();
        assert!(
            matches!(c4, CicTerm::Const(ref n) if n == "Coq.PArith.POrderedType.Positive_as_OT.mul"),
            "unregistered Dual keeps the user spelling, got {c4:?}"
        );

        // With the CANONICAL name registered (and the user spelling not), the
        // canonical (definition-site) spelling wins — the dumped-under name.
        let mut ctx_canon = SerapiNormCtx::default();
        ctx_canon.register_known_name("Coq.PArith.BinPosDef.Pos.mul");
        let c5 = sexp_to_cic(&normalize_serapi_rec(
            &parse_sexp(dual_src).unwrap(),
            &ctx_canon,
            &[],
        ))
        .unwrap();
        assert!(
            matches!(c5, CicTerm::Const(ref n) if n == "Coq.PArith.BinPosDef.Pos.mul"),
            "canonical-known Dual resolves canonically, got {c5:?}"
        );

        // With the USER spelling registered, it wins even when the canonical
        // is also known (today's resolutions never change).
        let mut ctx_user = SerapiNormCtx::default();
        ctx_user.register_known_name("Coq.PArith.POrderedType.Positive_as_OT.mul");
        ctx_user.register_known_name("Coq.PArith.BinPosDef.Pos.mul");
        let c6 = sexp_to_cic(&normalize_serapi_rec(
            &parse_sexp(dual_src).unwrap(),
            &ctx_user,
            &[],
        ))
        .unwrap();
        assert!(
            matches!(c6, CicTerm::Const(ref n) if n == "Coq.PArith.POrderedType.Positive_as_OT.mul"),
            "user-known Dual keeps the user spelling, got {c6:?}"
        );

        // KerPair Dual on an inductive reference: canonical-known resolves.
        let dual_ind_src = r#"(Ind(((MutInd(KerName(MPdot(MPfile(DirPath((Id X)(Id Coq))))(Id Alias))(Id t))((KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))))0)(Instance(()()))))"#;
        let mut ctx_ind = SerapiNormCtx::default();
        ctx_ind.register_known_name("Coq.Init.Datatypes.nat");
        let i2 = sexp_to_cic(&normalize_serapi_rec(
            &parse_sexp(dual_ind_src).unwrap(),
            &ctx_ind,
            &[],
        ))
        .unwrap();
        assert!(
            matches!(i2, CicTerm::Ind(ref n, 0) if n == "Coq.Init.Datatypes.nat"),
            "canonical-known Dual MutInd resolves canonically, got {i2:?}"
        );

        // (App f (a b)) flattens to two args.
        let app_src = r#"(App(Const((Constant(KerName(MPfile(DirPath((Id SerTop))))(Id idnat))())(Instance(()()))))((Rel 2)(Rel 1)))"#;
        let a = sexp_to_cic(&normalize_serapi_rec(
            &parse_sexp(app_src).unwrap(),
            &ctx,
            &[],
        ))
        .unwrap();
        match a {
            CicTerm::App(_, args) => assert_eq!(args.len(), 2),
            other => panic!("expected App with 2 args, got {other:?}"),
        }
    }

    // Real `sertop-projfix --printer=sertop` payload of the `GRing.add` body's
    // primitive projection (measured live on mathverse-coq-linux after the
    // serlib Projection.Repr layout fix). The record inductive is
    // `GRing.Zmodule.class_of` (proj_ind) and the field index is `proj_arg` 1.
    const SERAPI_PROJ_GRING_ADD: &str = "(Proj(((proj_ind((MutInd(KerName(MPdot(MPdot(MPfile(DirPath((Id ssralg)(Id algebra)(Id mathcomp))))(Id GRing))(Id Zmodule))(Id class_of))())0))(proj_npars 1)(proj_arg 1)(proj_name(Constant(KerName(MPdot(MPdot(MPfile(DirPath((Id ssralg)(Id algebra)(Id mathcomp))))(Id GRing))(Id Zmodule))(Id mixin))())))false)Relevant(App(Const((Constant(KerName(MPdot(MPdot(MPfile(DirPath((Id ssralg)(Id algebra)(Id mathcomp))))(Id GRing))(Id Zmodule))(Id class))())(Instance(()()))))((Rel 1))))";

    #[test]
    fn test_normalize_serapi_proj_faithful_struct_and_index() {
        // The projfix/.vo `Proj` payload normalizes to the importer dialect
        // `(Proj <record-inductive> <field-idx> <record>)` — struct name taken
        // from `proj_ind`, field index taken from Coq's own `proj_arg`.
        let ctx = SerapiNormCtx::default();
        let cic = sexp_to_cic(&normalize_serapi_rec(
            &parse_sexp(SERAPI_PROJ_GRING_ADD).unwrap(),
            &ctx,
            &[],
        ))
        .expect("normalize+lower projfix Proj");
        match cic {
            CicTerm::Proj(name, idx, inner) => {
                // The struct name is proj_ind's record inductive CARRYING ITS
                // BLOCK-INDEX SUFFIX (`.0`), matching the `<name>.<block>`
                // spelling the record inductive is registered under and that an
                // `(Ind <name> <block>)` reference lowers to. Without the suffix
                // the kernel's projection typecheck compared a bare `<name>`
                // against the record's actual `<name>.0` head and rejected every
                // HB accessor with InvalidProjNotStruct.
                assert_eq!(
                    name, "mathcomp.algebra.ssralg.GRing.Zmodule.class_of.0",
                    "struct name must be proj_ind's block-indexed record inductive"
                );
                // NEGATIVE CONTROL: the bare (suffix-less) spelling is the
                // pre-fix bug and must never be emitted.
                assert_ne!(
                    name, "mathcomp.algebra.ssralg.GRing.Zmodule.class_of",
                    "struct name must not drop the block-index suffix"
                );
                // FIDELITY NEGATIVE CONTROL: the field index is Coq's proj_arg
                // (1), NOT the old hardcoded 0. A silent 0 would project the
                // WRONG field (the type-changing failure mode rule 3 guards).
                assert_eq!(idx, 1, "field index must be proj_arg, not defaulted");
                assert_ne!(idx, 0, "proj_arg 1 must never collapse to field 0");
                // The record subterm normalized through (SerAPI Rel 1 -> 0).
                match *inner {
                    CicTerm::App(f, args) => {
                        assert!(matches!(*f, CicTerm::Const(ref n)
                                if n == "mathcomp.algebra.ssralg.GRing.Zmodule.class"));
                        assert_eq!(args.len(), 1);
                        assert!(matches!(args[0], CicTerm::Rel(0)));
                    }
                    other => panic!("expected App record subterm, got {other:?}"),
                }
            }
            other => panic!("expected Proj, got {other:?}"),
        }
    }

    #[test]
    fn test_serapi_proj_marks_speculative_motive() {
        // The proj_arg -> kernel-field-idx identification is a kernel-arbitrated
        // assumption, so the enclosing constant must be flagged SPECULATIVE so
        // a projection the kernel cannot resolve fails closed to a clean
        // type-only axiom (never a masked-failure taint).
        SPECULATIVE_MOTIVE_USED.with(|c| c.set(false));
        let _ = normalize_serapi_rec(
            &parse_sexp(SERAPI_PROJ_GRING_ADD).unwrap(),
            &SerapiNormCtx::default(),
            &[],
        );
        assert!(
            SPECULATIVE_MOTIVE_USED.with(|c| c.get()),
            "Proj translation must mark SPECULATIVE_MOTIVE"
        );
    }

    #[test]
    fn test_serapi_proj_unrecognized_arity_fails_closed() {
        // A `Proj` node whose payload is not the projfix/.vo shape must fail
        // closed (never guess a struct name / field index).
        let bad = parse_sexp("(Proj foo)").unwrap();
        let out = normalize_serapi_rec(&bad, &SerapiNormCtx::default(), &[]);
        // coq_unsupported emits a poison reference the kernel rejects; it must
        // NOT parse into a well-formed CicTerm::Proj.
        assert!(
            !matches!(sexp_to_cic(&out), Ok(CicTerm::Proj(..))),
            "unrecognized Proj arity must not yield a Proj term"
        );
    }

    #[test]
    fn test_proj_lowers_field_index_faithfully() {
        // Lowering must carry the dialect field index verbatim into the kernel
        // Proj node (data[4..6]). NEGATIVE CONTROL: index 2 must lower to field
        // 2, not the historical hardcoded 0.
        let mut w = ShardWriter::new();
        let term = CicTerm::Proj("R".into(), 2, Box::new(CicTerm::Rel(0)));
        let idx = cic_to_flat_expr(&term, &mut w);
        let flat = w.expr_at(idx).expect("proj expr present");
        assert!(matches!(flat.tag(), Ok(clean_kernel::flat::FlatTag::Proj)));
        assert_eq!(
            flat.read_u16(4).expect("read field"),
            2,
            "kernel Proj field must equal the dialect index, not 0"
        );

        // Same node with index 0 lowers to field 0 — proving the index is
        // load-bearing (the two lower to distinct kernel nodes).
        let mut w0 = ShardWriter::new();
        let term0 = CicTerm::Proj("R".into(), 0, Box::new(CicTerm::Rel(0)));
        let idx0 = cic_to_flat_expr(&term0, &mut w0);
        assert_eq!(w0.expr_at(idx0).unwrap().read_u16(4).unwrap(), 0);
    }

    #[test]
    fn test_serapi_proj_dialect_roundtrip_indices_distinct() {
        // The dialect parser preserves distinct field indices (regression guard
        // against re-collapsing to a single arity-2 shape).
        let p1 = sexp_to_cic(&parse_sexp("(Proj R 1 (Rel 0))").unwrap()).unwrap();
        let p0 = sexp_to_cic(&parse_sexp("(Proj R 0 (Rel 0))").unwrap()).unwrap();
        assert!(matches!(p1, CicTerm::Proj(ref n, 1, _) if n == "R"));
        assert!(matches!(p0, CicTerm::Proj(ref n, 0, _) if n == "R"));
    }

    #[test]
    fn test_dialect_map_rels_traverses_proj_preserving_name_and_index() {
        // Regression guard for the secondary rel-remap (`dialect_map_rels` /
        // `dialect_lift`) over a value containing a normalized
        // `(Proj <struct> <field-idx> <record>)`. Before the `Proj` arm was
        // added the walk erred "unsupported head Proj", hard-failing any value
        // whose Proj sat under a Fix/Case/index-promotion rebind and dropping
        // the constant to a type-only stand-in even when the value was
        // otherwise translatable.
        let proj = parse_sexp("(Proj R 3 (Rel 0))").unwrap();
        // Lift free `Rel`s (>= cutoff 0) by 2: the record's `Rel 0` becomes
        // `Rel 2`; the struct name and the NUMERIC field index are payloads,
        // never `Rel`s, so they must be byte-identical afterwards.
        let lifted = dialect_lift(&proj, 2, 0).expect("Proj must traverse the lift");
        match sexp_to_cic(&lifted).expect("lifted Proj lowers") {
            CicTerm::Proj(name, idx, inner) => {
                assert_eq!(name, "R", "struct name preserved verbatim");
                // FIDELITY NEGATIVE CONTROL: had the walk recursed into the
                // field-index atom it would have treated `3` as `Rel 3` and
                // lifted it to `5`, silently projecting the WRONG field.
                assert_eq!(idx, 3, "field index is a payload, never lifted as a Rel");
                assert!(
                    matches!(*inner, CicTerm::Rel(2)),
                    "the record subterm's free Rel is lifted (0 -> 2)"
                );
            }
            other => panic!("expected Proj, got {other:?}"),
        }
        // NEGATIVE CONTROL: a record `Rel` BELOW the cutoff is bound-local and
        // must not move. Lift by 5 at cutoff 1: `Rel 0` (< 1) stays put; the
        // field index still does not participate.
        let lifted_cut = dialect_lift(&proj, 5, 1).expect("lift at cutoff 1");
        match sexp_to_cic(&lifted_cut).expect("lower") {
            CicTerm::Proj(_, idx, inner) => {
                assert_eq!(idx, 3, "field index still a payload at any cutoff");
                assert!(
                    matches!(*inner, CicTerm::Rel(0)),
                    "record Rel below cutoff is untouched"
                );
            }
            other => panic!("expected Proj, got {other:?}"),
        }
    }

    #[test]
    fn test_value_translation_failure_marks_salvaged_standin() {
        // A value we cannot TRANSLATE (here an unstructuralizable `Fix`) is a
        // reconstruction gap — Coq's kernel checked it, the importer simply
        // cannot reproduce it — NOT a value-free Coq axiom. It must carry
        // `SALVAGED_STAND_IN` so verify classifies dependents that reduce
        // through its now-value-less body as STANDIN_BLOCKED (clean, no
        // masked-failure taint) instead of seeding a regression cascade.
        let input = "(CoqConstant SerTop.weird (Sort (Type 1)) (Fix ((f (Sort Prop) (Rel 0))) 0))";
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(input, &mut w).unwrap();
        assert_eq!(stats.value_translation_failed, 1, "value must drop loudly");
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let c = &reader.constants[0];
        assert!(!c.has_value(), "value dropped to type-only");
        assert_eq!(c.decl_kind, DeclKind::Axiom as u8);
        let p = c.profile();
        assert!(
            p.has(AxiomProfile::SALVAGED_STAND_IN),
            "value-translation failure must be a reconstruction-gap stand-in"
        );
        assert!(p.has(AxiomProfile::AXIOMATIZED), "still an axiomatized row");
        // The stand-in bit is a NON_AXIOM_HINT: it adds no axiom dependency and
        // can never itself mint KernelVerified.
        assert_eq!(
            AxiomProfile::SALVAGED_STAND_IN.axiom_count(),
            0,
            "stand-in bit must not change axiom accounting"
        );
    }

    #[test]
    fn test_normalize_serapi_passthrough_existing_dialect() {
        // Importer-dialect nodes must be untouched by the gated adapter: they
        // contain no SerAPI markers, so `normalize_if_serapi_ctx` returns them
        // verbatim (crucially preserving 0-based `Rel` and flat `App`).
        for src in [
            "(Lambda x (Sort Set) (Rel 0))",
            "(Prod x (Sort Prop) (Rel 0))",
            "(App (Const f) (Rel 0) (Rel 1))",
            "(Ind nat 0)",
            "(Construct nat 0 1)",
            "(Const Nat.add)",
        ] {
            let parsed = parse_sexp(src).unwrap();
            assert!(!is_serapi_native(&parsed), "false positive: {src}");
            let normalized = normalize_if_serapi_ctx(&parsed, &SerapiNormCtx::default());
            assert_eq!(parsed, normalized, "dialect node changed: {src}");
        }
    }

    #[test]
    fn test_sexp_to_cic_compound() {
        assert!(
            matches!(sexp_to_cic(&parse_sexp("(App (Const f) (Rel 0) (Rel 1))").unwrap()).unwrap(), CicTerm::App(_, a) if a.len() == 2)
        );
        assert!(
            matches!(sexp_to_cic(&parse_sexp("(Prod x (Sort Prop) (Rel 0))").unwrap()).unwrap(), CicTerm::Prod(n, _, _) if n == "x")
        );
        assert!(
            matches!(sexp_to_cic(&parse_sexp("(Lambda x (Sort Set) (Rel 0))").unwrap()).unwrap(), CicTerm::Lambda(n, _, _) if n == "x")
        );
        assert!(
            matches!(sexp_to_cic(&parse_sexp("(Ind nat 0)").unwrap()).unwrap(), CicTerm::Ind(n, 0) if n == "nat")
        );
        assert!(
            matches!(sexp_to_cic(&parse_sexp("(Construct nat 0 1)").unwrap()).unwrap(), CicTerm::Construct(n, 0, 1) if n == "nat")
        );
    }

    #[test]
    fn test_lowering() {
        let mut w = ShardWriter::new();
        assert_eq!(cic_to_flat_expr(&CicTerm::Rel(5), &mut w), 0);
        let mut w = ShardWriter::new();
        assert_eq!(cic_to_flat_expr(&CicTerm::Sort(CicSort::Prop), &mut w), 0);
        let mut w = ShardWriter::new();
        assert_eq!(cic_to_flat_expr(&CicTerm::Sort(CicSort::Set), &mut w), 0);
        let mut w = ShardWriter::new();
        assert_eq!(cic_to_flat_expr(&CicTerm::Int(42), &mut w), 0);
        let mut w = ShardWriter::new();
        let app = CicTerm::App(
            Box::new(CicTerm::Const("f".into())),
            vec![CicTerm::Rel(0), CicTerm::Rel(1)],
        );
        assert!(cic_to_flat_expr(&app, &mut w) > 0);
        let mut w = ShardWriter::new();
        let prod = CicTerm::Prod(
            "x".into(),
            Box::new(CicTerm::Sort(CicSort::Prop)),
            Box::new(CicTerm::Rel(0)),
        );
        assert!(cic_to_flat_expr(&prod, &mut w) > 0);
    }

    #[test]
    fn test_import_empty() {
        let mut w = ShardWriter::new();
        assert_eq!(CoqImporter.import_sexp("", &mut w).unwrap().total, 0);
    }

    #[test]
    fn test_import_constant_with_value() {
        let mut w = ShardWriter::new();
        let s = CoqImporter
            .import_sexp(
                "(CoqConstant Nat.add (Sort (Type 0)) (Lambda x (Sort (Type 0)) (Rel 0)))",
                &mut w,
            )
            .unwrap();
        assert_eq!((s.total, s.translated, s.axiomatized), (1, 1, 0));
    }

    #[test]
    fn test_import_axiom_and_mixed() {
        let mut w = ShardWriter::new();
        assert_eq!(
            CoqImporter
                .import_sexp("(CoqAxiom classic (Sort Prop))", &mut w)
                .unwrap()
                .axiomatized,
            1
        );
        let mut w = ShardWriter::new();
        let s = CoqImporter.import_sexp("(CoqConstant f (Sort Set) (Rel 0))(CoqAxiom ax (Sort Prop))(CoqConstant g (Sort Prop))", &mut w).unwrap();
        assert_eq!((s.total, s.translated, s.axiomatized), (3, 1, 2));
    }

    #[test]
    fn test_import_coq_inductive_decl_kinds() {
        // `Inductive mynat := O | S (n:mynat).` in the `(CoqInductive ...)` form.
        // The inductive references itself via `(Ind mynat 0)` so its
        // constructors return the inductive type. One inductive + two ctors.
        let input = r#"(CoqInductive mynat 0 (Sort Set)
            (Ctor O (Ind mynat 0))
            (Ctor S (Prod n (Ind mynat 0) (Ind mynat 0))))"#;
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(input, &mut w).unwrap();
        // total counts top-level sexps (1); translated counts written decls (3).
        assert_eq!((stats.total, stats.translated, stats.skipped), (1, 3, 0));

        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(reader.header.constant_count, 3);

        let by_name: std::collections::HashMap<&str, &MathverseConstantHeader> = reader
            .constants
            .iter()
            .map(|c| (reader.strings[c.name_idx as usize].as_str(), c))
            .collect();

        // Inductive constant: named `mynat.0` (matches `(Ind mynat 0)` lowering),
        // DeclKind::Inductive, NO_VALUE, pure, KernelVerified, num_params=0.
        let ind = by_name["mynat.0"];
        assert_eq!(ind.decl_kind, DeclKind::Inductive as u8);
        assert!(!ind.has_value());
        assert!(ind.profile().is_kernel_verified());
        assert_eq!(
            ind.import_confidence,
            ImportConfidence::KernelVerified as u8
        );
        assert_eq!(ind.inductive_decl_num_params(), Some(0));

        // Constructors: named `mynat.0.0` (O) and `mynat.0.1` (S), matching how
        // a dependent `(Construct mynat 0 j)` reference lowers to `mynat.0.(j-1)`.
        for ctor in ["mynat.0.0", "mynat.0.1"] {
            let c = by_name[ctor];
            assert_eq!(c.decl_kind, DeclKind::Constructor as u8, "{ctor}");
            assert!(!c.has_value(), "{ctor}");
            assert!(c.profile().is_kernel_verified(), "{ctor}");
        }
    }

    #[test]
    fn test_import_shard_roundtrip() {
        let mut w = ShardWriter::new();
        CoqImporter
            .import_sexp(
                "(CoqAxiom propositional_extensionality (Sort Prop))",
                &mut w,
            )
            .unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(reader.header.constant_count, 1);
        let c = &reader.constants[0];
        assert_eq!(c.source_system, SourceSystem::Coq as u8);
        assert!(!c.has_value());
        let p = c.profile();
        assert!(
            p.has(AxiomProfile::BRIDGE_AXIOM)
                && p.has(AxiomProfile::PROP_EXT)
                && p.has(AxiomProfile::AXIOMATIZED)
        );
    }

    #[test]
    fn test_import_coq_axiom_standin_marker_sets_salvaged_profile_bit() {
        // Inline dump-salvage marker: a `(CoqAxiom <name> <type> StandIn)` row
        // gains the SALVAGED_STAND_IN provenance hint; an unmarked axiom in the
        // same stream does not. The hint is masked out of every axiom-counting
        // surface (NON_AXIOM_HINTS) — it records provenance, not an axiom dep.
        let mut w = ShardWriter::new();
        CoqImporter
            .import_sexp(
                "(CoqAxiom SerTop.M.class_of (Prod _ (Sort (Type 1)) (Sort (Type 1))) StandIn)\n\
                 (CoqAxiom SerTop.genuine_param (Sort Prop))",
                &mut w,
            )
            .unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(reader.header.constant_count, 2);
        let marked = &reader.constants[0];
        assert_eq!(marked.decl_kind, DeclKind::Axiom as u8);
        assert!(!marked.has_value());
        assert!(
            marked.profile().has(AxiomProfile::SALVAGED_STAND_IN)
                && marked.profile().has(AxiomProfile::AXIOMATIZED),
            "marked row must carry the stand-in hint: 0x{:x}",
            marked.profile().0
        );
        let unmarked = &reader.constants[1];
        assert!(
            !unmarked.profile().has(AxiomProfile::SALVAGED_STAND_IN),
            "genuine axiom must NOT gain the stand-in hint: 0x{:x}",
            unmarked.profile().0
        );
        // Mask discipline: the hint alone never counts as an axiom bit.
        assert!(AxiomProfile::SALVAGED_STAND_IN.is_kernel_verified());
        assert_eq!(AxiomProfile::SALVAGED_STAND_IN.axiom_count(), 0);
    }

    #[test]
    fn test_import_legacy_salvage_set_marks_axiom_rows_only() {
        // Legacy sidecar route: names supplied via the salvage set gain the
        // hint ONLY when they import as value-less `CoqAxiom` rows — a name
        // that imports as a real value-bearing constant (e.g. reconstructed
        // after its salvage note was written) never carries it.
        let mut set = std::collections::HashSet::new();
        set.insert("legacy.standin".to_string());
        set.insert("legacy.realdef".to_string());
        let mut w = ShardWriter::new();
        CoqImporter
            .import_sexp_with_registry_and_standins(
                "(CoqAxiom legacy.standin (Sort Prop))\n\
                 (CoqConstant legacy.realdef (Sort Prop) (Const legacy.standin))",
                &CoqSessionRegistry::default(),
                &set,
                &mut w,
            )
            .unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(reader.header.constant_count, 2);
        let standin = &reader.constants[0];
        assert!(!standin.has_value());
        assert!(
            standin.profile().has(AxiomProfile::SALVAGED_STAND_IN),
            "legacy salvage-set axiom row must gain the hint: 0x{:x}",
            standin.profile().0
        );
        let realdef = &reader.constants[1];
        assert!(realdef.has_value());
        assert!(
            !realdef.profile().has(AxiomProfile::SALVAGED_STAND_IN),
            "value-bearing row must never gain the hint even when named in the \
             salvage set: 0x{:x}",
            realdef.profile().0
        );
    }

    #[test]
    fn test_axiom_profiles() {
        let p = compute_coq_axiom_profile("Classical.choice");
        assert!(
            p.has(AxiomProfile::CHOICE)
                && p.has(AxiomProfile::CLASSICAL)
                && p.has(AxiomProfile::BRIDGE_AXIOM)
        );
        let p = compute_coq_axiom_profile("propositional_extensionality");
        assert!(p.has(AxiomProfile::PROP_EXT) && p.has(AxiomProfile::BRIDGE_AXIOM));
        assert!(compute_coq_axiom_profile("functional_extensionality").has(AxiomProfile::FUNC_EXT));
        let p = compute_coq_axiom_profile("Nat.add");
        assert!(p.has(AxiomProfile::BRIDGE_AXIOM) && !p.has(AxiomProfile::CHOICE));
    }

    #[test]
    fn test_mutual_inductive_parse_and_two_bodies() {
        // Single body with params
        let input = r#"(MutualInductive (Params (x (Sort Prop)))
            (Body nat (Sort (Type 0)) (Ctor O (Sort (Type 0)))
                (Ctor S (Prod n (Ind nat 0) (Sort (Type 0))))))"#;
        let mind = sexp_to_mutual_inductive(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!((mind.params.len(), mind.bodies.len()), (1, 1));
        assert_eq!(
            (mind.params[0].0.as_str(), mind.bodies[0].name.as_str()),
            ("x", "nat")
        );
        assert_eq!(mind.bodies[0].constructors.len(), 2);
        assert_eq!(
            (
                mind.bodies[0].constructors[0].0.as_str(),
                mind.bodies[0].constructors[1].0.as_str()
            ),
            ("O", "S")
        );
        // Two mutual bodies
        let input2 = r#"(MutualInductive (Params)
            (Body even (Sort (Type 0)) (Ctor even_O (Sort (Type 0)))
                (Ctor even_S (Prod n (Ind odd 0) (Sort (Type 0)))))
            (Body odd (Sort (Type 0)) (Ctor odd_S (Prod n (Ind even 0) (Sort (Type 0))))))"#;
        let mind2 = sexp_to_mutual_inductive(&parse_sexp(input2).unwrap()).unwrap();
        assert_eq!(mind2.bodies.len(), 2);
        assert_eq!(
            (
                mind2.bodies[0].constructors.len(),
                mind2.bodies[1].constructors.len()
            ),
            (2, 1)
        );
        // Bad head
        assert!(sexp_to_mutual_inductive(
            &parse_sexp("(NotMutualInductive (Body x (Sort Prop)))").unwrap()
        )
        .is_err());
    }

    #[test]
    fn test_constructor_name_mangling_and_import() {
        let input = r#"(MutualInductive (Params)
            (Body nat (Sort (Type 0)) (Ctor O (Sort (Type 0)))
                (Ctor S (Prod n (Ind nat 0) (Sort (Type 0))))))"#;
        let mind = sexp_to_mutual_inductive(&parse_sexp(input).unwrap()).unwrap();
        let mut w = ShardWriter::new();
        let indices = import_mutual_inductive(&mind, "Coq.Init.Datatypes", &mut w).unwrap();
        assert_eq!(indices.len(), 3); // nat + O + S
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let names: Vec<&str> = reader
            .constants
            .iter()
            .map(|c| reader.strings[c.name_idx as usize].as_str())
            .collect();
        assert_eq!(names, vec!["nat", "nat.O", "nat.S"]);
    }

    #[test]
    fn test_mutual_inductive_import_pipeline() {
        let input = r#"(MutualInductive (Params)
            (Body list (Prod A (Sort (Type 0)) (Sort (Type 0)))
                (Ctor nil (Prod A (Sort (Type 0)) (Ind list 0)))
                (Ctor cons (Prod A (Sort (Type 0)) (Prod x (Rel 0) (Ind list 0))))))"#;
        let mind = sexp_to_mutual_inductive(&parse_sexp(input).unwrap()).unwrap();
        let mut w = ShardWriter::new();
        let indices = import_mutual_inductive(&mind, "Coq.Init.Datatypes", &mut w).unwrap();
        assert_eq!(indices.len(), 3);
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(reader.header.constant_count, 3);
        for c in &reader.constants {
            assert_eq!(c.source_system, SourceSystem::Coq as u8);
            assert!(!c.has_value());
            assert!(c.profile().is_pure(), "Coq.Init constants should be pure");
        }
    }

    #[test]
    fn test_universe_level_lowering() {
        let mut w = ShardWriter::new();
        assert_eq!(universe_level_to_flat(&CoqUniverseLevel::Prop, &mut w), 0);
        let mut w = ShardWriter::new();
        assert!(universe_level_to_flat(&CoqUniverseLevel::Set, &mut w) > 0);
        let mut w = ShardWriter::new();
        assert!(universe_level_to_flat(&CoqUniverseLevel::Type(3), &mut w) > 0);
        let mut w = ShardWriter::new();
        // FlatLevel::zero is pre-seeded at index 0; Var("u") creates
        // a new Param level at index 1.
        assert_eq!(
            universe_level_to_flat(&CoqUniverseLevel::Var("u".into()), &mut w),
            1
        );
        let mut w = ShardWriter::new();
        let max = CoqUniverseLevel::Max(vec![CoqUniverseLevel::Type(1), CoqUniverseLevel::Type(2)]);
        assert!(universe_level_to_flat(&max, &mut w) > 0);
        let mut w = ShardWriter::new();
        assert!(
            universe_level_to_flat(
                &CoqUniverseLevel::Succ(Box::new(CoqUniverseLevel::Prop)),
                &mut w
            ) > 0
        );
        let mut w = ShardWriter::new();
        assert_eq!(
            universe_level_to_flat(&CoqUniverseLevel::Max(vec![]), &mut w),
            0
        );
    }

    #[test]
    fn test_classify_coq_modules() {
        // Pure modules
        assert!(classify_coq_module("Coq.Init.Datatypes").is_pure());
        assert!(classify_coq_module("Coq.Init.Prelude").is_pure());
        assert!(classify_coq_module("Coq.Init").is_pure());
        assert!(classify_coq_module("Coq.Logic.Decidable").is_pure());
        assert!(classify_coq_module("Coq.Setoids.Setoid").is_pure());
        // ClassicalEpsilon: CHOICE (which is the same bit as CLASSICAL) + BRIDGE_AXIOM
        let p = classify_coq_module("Coq.Logic.ClassicalEpsilon");
        assert!(p.has(AxiomProfile::CHOICE) && p.has(AxiomProfile::BRIDGE_AXIOM));
        // ClassicalChoice: CHOICE + CLASSICAL
        let p = classify_coq_module("Coq.Logic.ClassicalChoice");
        assert!(p.has(AxiomProfile::CHOICE) && p.has(AxiomProfile::CLASSICAL));
        // FunctionalExtensionality
        let p = classify_coq_module("Coq.Logic.FunctionalExtensionality");
        assert!(p.has(AxiomProfile::FUNC_EXT) && p.has(AxiomProfile::BRIDGE_AXIOM));
        // PropExtensionality and ProofIrrelevance both map to PROP_EXT
        let p = classify_coq_module("Coq.Logic.PropExtensionality");
        assert!(p.has(AxiomProfile::PROP_EXT) && p.has(AxiomProfile::BRIDGE_AXIOM));
        let p = classify_coq_module("Coq.Logic.ProofIrrelevance");
        assert!(p.has(AxiomProfile::PROP_EXT));
        // Berardi paradox: UNIVERSE_INCON
        let p = classify_coq_module("Coq.Logic.Berardi");
        assert!(p.has(AxiomProfile::UNIVERSE_INCON) && p.has(AxiomProfile::BRIDGE_AXIOM));
        // Unknown module: just BRIDGE_AXIOM
        let p = classify_coq_module("Coq.Arith.PeanoNat");
        assert!(p.has(AxiomProfile::BRIDGE_AXIOM) && !p.has(AxiomProfile::CHOICE));
    }

    #[test]
    fn test_enhanced_sexp_to_cic() {
        // Nested Ind form
        let cic =
            sexp_to_cic(&parse_sexp(r#"(Ind (MutInd "nat" 0) (Instance ()))"#).unwrap()).unwrap();
        assert!(matches!(cic, CicTerm::Ind(n, 0) if n == "nat"));
        // Nested Construct form
        let cic = sexp_to_cic(
            &parse_sexp(r#"(Construct (MutConstruct "nat" 0 1 Relevant) (Instance ()))"#).unwrap(),
        )
        .unwrap();
        assert!(matches!(cic, CicTerm::Construct(n, 0, 1) if n == "nat"));
        // Nested App with Const(MutConstruct ...)
        let cic = sexp_to_cic(
            &parse_sexp(r#"(App (Const (MutConstruct "nat" 0 1 Relevant)) (Rel 0))"#).unwrap(),
        )
        .unwrap();
        assert!(matches!(cic, CicTerm::App(_, args) if args.len() == 1));
        // Fix
        let cic = sexp_to_cic(&parse_sexp("(Fix ((f (Sort Prop) (Rel 0))) 0)").unwrap()).unwrap();
        match cic {
            CicTerm::Fix(b, 0) => {
                assert_eq!(b.len(), 1);
                assert_eq!(b[0].0, "f");
            }
            _ => panic!("expected Fix"),
        }
        // CoFix
        let cic = sexp_to_cic(&parse_sexp("(CoFix ((g (Sort Set) (Rel 0))) 0)").unwrap()).unwrap();
        assert!(matches!(cic, CicTerm::CoFix(b, 0) if b.len() == 1));
        // Case (structured recursor form) with 2 branches.
        let cic = sexp_to_cic(
            &parse_sexp(
                "(Case (Ind or 0) (Params (Rel 1) (Rel 0)) (Motive (Sort Prop)) \
                 (Discriminant (Rel 2)) (Branch (Rel 3)) (Branch (Rel 4)))",
            )
            .unwrap(),
        )
        .unwrap();
        match cic {
            CicTerm::Case(case) => {
                assert_eq!(case.ind_name, "or");
                assert_eq!(case.ind_idx, 0);
                assert_eq!(case.params.len(), 2);
                assert_eq!(case.branches.len(), 2);
            }
            _ => panic!("expected Case"),
        }
    }

    #[test]
    fn test_inductive_shard_roundtrip() {
        let input = r#"(MutualInductive (Params)
            (Body bool (Sort (Type 0)) (Ctor true (Sort (Type 0)))
                (Ctor false (Sort (Type 0)))))"#;
        let mind = sexp_to_mutual_inductive(&parse_sexp(input).unwrap()).unwrap();
        let mut w = ShardWriter::new();
        import_mutual_inductive(&mind, "Coq.Init.Datatypes", &mut w).unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert!(reader.lookup_name("bool").is_some());
        assert!(reader.lookup_name("bool.true").is_some());
        assert!(reader.lookup_name("bool.false").is_some());
        assert!(reader.lookup_name("bool.maybe").is_none());
    }

    // -----------------------------------------------------------------
    // New tests for expanded CIC core translation
    // -----------------------------------------------------------------

    #[test]
    fn test_sprop_sort_parsing() {
        // SProp should parse to Prop (same universe level in our encoding)
        let cic = sexp_to_cic(&parse_sexp("(Sort SProp)").unwrap()).unwrap();
        assert!(matches!(cic, CicTerm::Sort(CicSort::Prop)));
    }

    #[test]
    fn test_sort_ext_to_flat_all_variants() {
        let mut w = ShardWriter::new();
        let prop_idx = sort_ext_to_flat(&CicSortExt::Prop, &mut w);
        assert_eq!(prop_idx, 0); // zero level

        let mut w = ShardWriter::new();
        let sprop_idx = sort_ext_to_flat(&CicSortExt::SProp, &mut w);
        assert_eq!(sprop_idx, 0); // SProp also maps to zero

        let mut w = ShardWriter::new();
        let set_idx = sort_ext_to_flat(&CicSortExt::Set, &mut w);
        assert!(set_idx > 0); // Set = succ(zero)

        let mut w = ShardWriter::new();
        let type3_idx = sort_ext_to_flat(&CicSortExt::Type(3), &mut w);
        assert!(type3_idx > 0); // Type 3 = succ(succ(succ(zero)))
    }

    #[test]
    fn test_match_branch_struct() {
        let branch = CicMatchBranch {
            constructor: "S".into(),
            nargs: 1,
            body: CicTerm::Rel(0),
        };
        assert_eq!(branch.constructor, "S");
        assert_eq!(branch.nargs, 1);
    }

    #[test]
    fn test_match_branch_to_flat_no_args() {
        let mut w = ShardWriter::new();
        let branch = CicMatchBranch {
            constructor: "O".into(),
            nargs: 0,
            body: CicTerm::Int(42),
        };
        let idx = match_branch_to_flat(&branch, &mut w);
        // With nargs==0, should just be the body directly
        assert_eq!(idx, 0);
    }

    #[test]
    fn test_match_branch_to_flat_with_args() {
        let mut w = ShardWriter::new();
        let branch = CicMatchBranch {
            constructor: "S".into(),
            nargs: 2,
            body: CicTerm::Rel(0),
        };
        let idx = match_branch_to_flat(&branch, &mut w);
        // Should have created lambda wrappers, so index > 0
        assert!(idx > 0);
    }

    #[test]
    fn test_sexp_to_cic_match_branches_annotated() {
        let input = "(Case (Rel 0) (Sort Prop) (Branch O 0 (Int 0)) (Branch S 1 (Rel 0)))";
        let branches = sexp_to_cic_match_branches(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(branches.len(), 2);
        assert_eq!(branches[0].constructor, "O");
        assert_eq!(branches[0].nargs, 0);
        assert_eq!(branches[1].constructor, "S");
        assert_eq!(branches[1].nargs, 1);
    }

    #[test]
    fn test_sexp_to_cic_match_branches_plain() {
        // Plain branches (without Branch wrapper) should still work
        let input = "(Case (Rel 0) (Sort Prop) (Int 0) (Rel 1))";
        let branches = sexp_to_cic_match_branches(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(branches.len(), 2);
        assert!(branches[0].constructor.is_empty());
        assert_eq!(branches[0].nargs, 0);
    }

    #[test]
    fn test_sexp_to_cic_match_branches_error() {
        // Not a Case head
        assert!(sexp_to_cic_match_branches(
            &parse_sexp("(Fix ((f (Sort Prop) (Rel 0))) 0)").unwrap()
        )
        .is_err());
        // Empty list
        assert!(sexp_to_cic_match_branches(&parse_sexp("()").unwrap()).is_err());
        // Atom
        assert!(sexp_to_cic_match_branches(&parse_sexp("hello").unwrap()).is_err());
    }

    #[test]
    fn test_cic_fix_body_struct() {
        let fb = CicFixBody {
            name: "add".into(),
            type_: CicTerm::Sort(CicSort::type_at(0)),
            body: CicTerm::Rel(0),
            recursive_arg_idx: 1,
        };
        assert_eq!(fb.name, "add");
        assert_eq!(fb.recursive_arg_idx, 1);
    }

    #[test]
    fn test_sexp_to_mutual_fixpoint_basic() {
        let input = "(MutualFix ((add (Sort (Type 0)) (Rel 0) 1)) 0)";
        let (bodies, focus) = sexp_to_mutual_fixpoint(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(bodies.len(), 1);
        assert_eq!(bodies[0].name, "add");
        assert_eq!(bodies[0].recursive_arg_idx, 1);
        assert_eq!(focus, 0);
    }

    #[test]
    fn test_sexp_to_mutual_fixpoint_multi() {
        let input =
            "(MutualFix ((even (Sort (Type 0)) (Rel 0) 0) (odd (Sort (Type 0)) (Rel 0) 0)) 0)";
        let (bodies, focus) = sexp_to_mutual_fixpoint(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(bodies.len(), 2);
        assert_eq!(bodies[0].name, "even");
        assert_eq!(bodies[1].name, "odd");
        assert_eq!(focus, 0);
    }

    #[test]
    fn test_sexp_to_mutual_fixpoint_errors() {
        // Wrong head
        assert!(
            sexp_to_mutual_fixpoint(&parse_sexp("(Lambda x (Sort Prop) (Rel 0))").unwrap())
                .is_err()
        );
        // Not a list for bodies
        assert!(sexp_to_mutual_fixpoint(&parse_sexp("(MutualFix badatom 0)").unwrap()).is_err());
    }

    #[test]
    fn test_import_mutual_fixpoint_single() {
        let bodies = vec![CicFixBody {
            name: "factorial".into(),
            type_: CicTerm::Prod(
                "n".into(),
                Box::new(CicTerm::Sort(CicSort::type_at(0))),
                Box::new(CicTerm::Sort(CicSort::type_at(0))),
            ),
            body: CicTerm::Rel(0),
            recursive_arg_idx: 0,
        }];
        let mut w = ShardWriter::new();
        let indices = import_mutual_fixpoint(&bodies, 0, "Coq.Init.Nat", &mut w).unwrap();
        assert_eq!(indices.len(), 1);
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(reader.header.constant_count, 1);
        let c = &reader.constants[0];
        assert!(c.has_value()); // focused body gets a value
        assert!(c.profile().is_pure()); // Coq.Init module is pure
    }

    #[test]
    fn test_import_mutual_fixpoint_multi_focus() {
        let bodies = vec![
            CicFixBody {
                name: "even".into(),
                type_: CicTerm::Sort(CicSort::type_at(0)),
                body: CicTerm::Rel(0),
                recursive_arg_idx: 0,
            },
            CicFixBody {
                name: "odd".into(),
                type_: CicTerm::Sort(CicSort::type_at(0)),
                body: CicTerm::Rel(0),
                recursive_arg_idx: 0,
            },
        ];
        let mut w = ShardWriter::new();
        let indices = import_mutual_fixpoint(&bodies, 1, "Coq.Arith.Even", &mut w).unwrap();
        assert_eq!(indices.len(), 2);
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        // Focus body (index 1) should be Translated, others Axiomatized
        assert_eq!(
            reader.constants[0].import_confidence,
            ImportConfidence::Axiomatized as u8
        );
        assert_eq!(
            reader.constants[1].import_confidence,
            ImportConfidence::Translated as u8
        );
    }

    #[test]
    fn test_cic_to_flat_with_universes_no_instance() {
        let mut w = ShardWriter::new();
        let term = CicTerm::Const("Nat.add".into());
        let idx = cic_to_flat_expr_with_universes(&term, &None, &mut w);
        // Should behave identically to cic_to_flat_expr
        let mut w2 = ShardWriter::new();
        let idx2 = cic_to_flat_expr(&term, &mut w2);
        assert_eq!(idx, idx2);
    }

    #[test]
    fn test_cic_to_flat_with_universes_single_level() {
        let mut w = ShardWriter::new();
        let term = CicTerm::Const("List.t".into());
        let inst = CoqUniverseInstance {
            levels: vec![CoqUniverseLevel::Type(1)],
        };
        let idx = cic_to_flat_expr_with_universes(&term, &Some(inst), &mut w);
        // Should produce a const_ref with a non-MAX level reference
        assert!(idx < u32::MAX);
    }

    #[test]
    fn test_cic_to_flat_with_universes_multi_level() {
        let mut w = ShardWriter::new();
        let term = CicTerm::Const("Sigma.t".into());
        let inst = CoqUniverseInstance {
            levels: vec![CoqUniverseLevel::Type(1), CoqUniverseLevel::Type(2)],
        };
        let idx = cic_to_flat_expr_with_universes(&term, &Some(inst), &mut w);
        // Multi-level instance chains through app nodes, so index should be higher
        assert!(idx > 0);
    }

    #[test]
    fn test_cic_to_flat_with_universes_ind() {
        let mut w = ShardWriter::new();
        let term = CicTerm::Ind("list".into(), 0);
        let inst = CoqUniverseInstance {
            levels: vec![CoqUniverseLevel::Set],
        };
        let idx = cic_to_flat_expr_with_universes(&term, &Some(inst), &mut w);
        assert!(idx < u32::MAX);
    }

    #[test]
    fn test_cic_to_flat_with_universes_construct() {
        let mut w = ShardWriter::new();
        let term = CicTerm::Construct("list".into(), 0, 1);
        let inst = CoqUniverseInstance {
            levels: vec![CoqUniverseLevel::Prop, CoqUniverseLevel::Type(1)],
        };
        let idx = cic_to_flat_expr_with_universes(&term, &Some(inst), &mut w);
        assert!(idx > 0);
    }

    #[test]
    fn test_cic_to_flat_with_universes_non_const_delegates() {
        // Non-const terms should delegate to cic_to_flat_expr regardless of instance
        let mut w = ShardWriter::new();
        let term = CicTerm::Rel(3);
        let inst = CoqUniverseInstance {
            levels: vec![CoqUniverseLevel::Type(5)],
        };
        let idx = cic_to_flat_expr_with_universes(&term, &Some(inst), &mut w);
        let mut w2 = ShardWriter::new();
        let idx2 = cic_to_flat_expr(&CicTerm::Rel(3), &mut w2);
        assert_eq!(idx, idx2);
    }

    #[test]
    fn test_primitive_to_flat_int63() {
        let mut w = ShardWriter::new();
        let idx_add = cic_primitive_to_flat(&CicPrimOp::Int63Add, &mut w);
        let idx_sub = cic_primitive_to_flat(&CicPrimOp::Int63Sub, &mut w);
        let idx_mul = cic_primitive_to_flat(&CicPrimOp::Int63Mul, &mut w);
        // Each should produce a distinct constant reference
        assert_ne!(idx_add, idx_sub);
        assert_ne!(idx_sub, idx_mul);
    }

    #[test]
    fn test_primitive_to_flat_float64() {
        let mut w = ShardWriter::new();
        let idx_add = cic_primitive_to_flat(&CicPrimOp::Float64Add, &mut w);
        let idx_sqrt = cic_primitive_to_flat(&CicPrimOp::Float64Sqrt, &mut w);
        let idx_neg = cic_primitive_to_flat(&CicPrimOp::Float64Neg, &mut w);
        assert_ne!(idx_add, idx_sqrt);
        assert_ne!(idx_sqrt, idx_neg);
    }

    #[test]
    fn test_primitive_to_flat_parray() {
        let mut w = ShardWriter::new();
        let idx_get = cic_primitive_to_flat(&CicPrimOp::PArrayGet, &mut w);
        let idx_set = cic_primitive_to_flat(&CicPrimOp::PArraySet, &mut w);
        let idx_make = cic_primitive_to_flat(&CicPrimOp::PArrayMake, &mut w);
        let idx_len = cic_primitive_to_flat(&CicPrimOp::PArrayLength, &mut w);
        // All four should be distinct
        let all = [idx_get, idx_set, idx_make, idx_len];
        for i in 0..all.len() {
            for j in (i + 1)..all.len() {
                assert_ne!(all[i], all[j], "parray ops at {i} and {j} should differ");
            }
        }
    }

    #[test]
    fn test_parse_prim_op_int63() {
        assert_eq!(parse_prim_op("Int63add").unwrap(), CicPrimOp::Int63Add);
        assert_eq!(parse_prim_op("int63_add").unwrap(), CicPrimOp::Int63Add);
        assert_eq!(parse_prim_op("Int63eq").unwrap(), CicPrimOp::Int63Eq);
        assert_eq!(parse_prim_op("Int63lsr").unwrap(), CicPrimOp::Int63Lsr);
    }

    #[test]
    fn test_parse_prim_op_float64() {
        assert_eq!(parse_prim_op("Float64add").unwrap(), CicPrimOp::Float64Add);
        assert_eq!(
            parse_prim_op("float64_sqrt").unwrap(),
            CicPrimOp::Float64Sqrt
        );
        assert_eq!(parse_prim_op("Float64neg").unwrap(), CicPrimOp::Float64Neg);
    }

    #[test]
    fn test_parse_prim_op_parray() {
        assert_eq!(parse_prim_op("PArrayGet").unwrap(), CicPrimOp::PArrayGet);
        assert_eq!(parse_prim_op("parray_set").unwrap(), CicPrimOp::PArraySet);
        assert_eq!(parse_prim_op("PArrayMake").unwrap(), CicPrimOp::PArrayMake);
        assert_eq!(
            parse_prim_op("parray_length").unwrap(),
            CicPrimOp::PArrayLength
        );
    }

    #[test]
    fn test_parse_prim_op_unknown() {
        assert!(parse_prim_op("unknown_op").is_err());
        assert!(parse_prim_op("").is_err());
    }

    #[test]
    fn test_primitive_dedup() {
        // Same primitive op should deduplicate to the same index
        let mut w = ShardWriter::new();
        let idx1 = cic_primitive_to_flat(&CicPrimOp::Int63Add, &mut w);
        let idx2 = cic_primitive_to_flat(&CicPrimOp::Int63Add, &mut w);
        assert_eq!(idx1, idx2);
    }

    #[test]
    fn test_match_branch_lowering_roundtrip() {
        // Build annotated branches and lower them through the full pipeline
        let mut w = ShardWriter::new();
        let branches = [
            CicMatchBranch {
                constructor: "O".into(),
                nargs: 0,
                body: CicTerm::Int(0),
            },
            CicMatchBranch {
                constructor: "S".into(),
                nargs: 1,
                body: CicTerm::Rel(0),
            },
        ];
        let indices: Vec<u32> = branches
            .iter()
            .map(|b| match_branch_to_flat(b, &mut w))
            .collect();
        assert_eq!(indices.len(), 2);
        // O branch has no lambdas, S branch has 1 lambda wrapping
        assert!(indices[1] > indices[0]);
    }

    /// End-to-end: the `match`-using Qed theorem `or_comm` plus its `or`
    /// inductive closure is genuinely `KernelVerified` by the corpus verifier.
    /// The proof term contains a Coq `Case` (pattern match) that
    /// [`cic_to_flat_expr`] lowers to an `or.0.rec` recursor application; the
    /// kernel typechecks that elimination through `add_decl`.
    ///
    /// Negative control: corrupting one branch so it returns the WRONG
    /// constructor (`or_introl` where `or_intror` is required, i.e. a proof of
    /// `or B A`'s left disjunct from a `b : B`) makes the branch ill-typed
    /// against the motive, so the kernel REJECTS the proof and `or_comm` falls
    /// back to an axiom (`axiom_fallback`) instead of `KernelVerified` — proving
    /// the kernel really checks the match branches, not just their shape.
    #[test]
    fn test_case_match_proof_kernel_verifies() {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;

        let verify = |sexp: &str| {
            let mut w = ShardWriter::new();
            CoqImporter.import_sexp(sexp, &mut w).unwrap();
            let mut buf = Vec::new();
            w.write(&mut buf).unwrap();
            let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
            let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
            lib.load_shard(&reader).unwrap();
            let prelude =
                clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
            verify_corpus_incremental(&lib, prelude)
        };

        // Positive: or(3) + or_comm(1) all kernel-verify, no axiom masking.
        let report = verify(OR_COMM_CLOSURE_SEXP);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert_eq!(
            report.axiom_fallback, 0,
            "the match proof must not be masked by an axiom fallback: {:?}",
            report.axiom_fallback_names
        );
        assert_eq!(report.kernel_verified, 4, "or(3) + or_comm(1)");
        assert!(
            report
                .kernel_verified_names
                .contains(&"or_comm".to_string()),
            "the match-using theorem or_comm must be genuinely KernelVerified, got {:?}",
            report.kernel_verified_names
        );

        // Negative control: replace the second branch's body with the bound
        // hypothesis `b` itself (`λ (b : B). b`). The recursor's minor premise
        // for `or_intror` demands a body of type `motive (or_intror …) = or B A`,
        // but `b : B`, and `B` is not definitionally `or B A`. The kernel rejects
        // the branch with a genuine type mismatch, so or_comm must NOT
        // kernel-verify — it falls back to an axiom that records the masked
        // failure. This proves the kernel really typechecks the match branches.
        let bad = OR_COMM_CLOSURE_SEXP.replace(
            "(Branch (Lambda b (Rel 1) (App (Construct or 0 0) (Rel 2) (Rel 3) (Rel 0))))",
            "(Branch (Lambda b (Rel 1) (Rel 0)))",
        );
        assert_ne!(bad, OR_COMM_CLOSURE_SEXP, "negative control must differ");
        let neg = verify(&bad);
        assert!(
            !neg.kernel_verified_names.contains(&"or_comm".to_string()),
            "an ill-typed match branch must be REJECTED, not KernelVerified"
        );
        assert_eq!(
            neg.axiom_fallback, 1,
            "the rejected match proof falls back to an axiom: {:?}",
            neg.axiom_fallback_names
        );
        assert!(
            neg.axiom_fallback_names
                .iter()
                .any(|(name, err)| name == "or_comm" && err.contains("Type mismatch")),
            "or_comm's rejected value must be a kernel TYPE MISMATCH on the bad \
             match branch, got {:?}",
            neg.axiom_fallback_names
        );
    }

    /// The structured `Case` lowering must produce exactly the same recursor
    /// application a hand-written `@or.0.rec …` term would. We compare the
    /// reconstructed kernel `Expr` of `or_comm`'s value built two ways:
    /// once from the `(Case …)` dialect, once from an explicit
    /// `(App (Const or.0.rec) …)` term. Identical kernel `Expr` ⇒ the lowering
    /// is the recursor application, nothing more.
    #[test]
    fn test_case_lowering_matches_manual_recursor() {
        let case_value = r#"(Lambda A (Sort Prop) (Lambda B (Sort Prop) (Lambda h (App (Ind or 0) (Rel 1) (Rel 0))
    (Case (Ind or 0)
      (Params (Rel 2) (Rel 1))
      (Motive (Lambda mot (App (Ind or 0) (Rel 2) (Rel 1)) (App (Ind or 0) (Rel 2) (Rel 3))))
      (Discriminant (Rel 0))
      (Branch (Lambda a (Rel 2) (App (Construct or 0 1) (Rel 2) (Rel 3) (Rel 0))))
      (Branch (Lambda b (Rel 1) (App (Construct or 0 0) (Rel 2) (Rel 3) (Rel 0))))))))"#;
        let manual_value = r#"(Lambda A (Sort Prop) (Lambda B (Sort Prop) (Lambda h (App (Ind or 0) (Rel 1) (Rel 0))
    (App (Const or.0.rec)
      (Rel 2) (Rel 1)
      (Lambda mot (App (Ind or 0) (Rel 2) (Rel 1)) (App (Ind or 0) (Rel 2) (Rel 3)))
      (Lambda a (Rel 2) (App (Construct or 0 1) (Rel 2) (Rel 3) (Rel 0)))
      (Lambda b (Rel 1) (App (Construct or 0 0) (Rel 2) (Rel 3) (Rel 0)))
      (Rel 0)))))"#;

        let reconstruct = |src: &str| {
            let cic = sexp_to_cic(&parse_sexp(src).unwrap()).unwrap();
            let mut w = ShardWriter::new();
            let idx = cic_to_flat_expr(&cic, &mut w);
            let mut buf = Vec::new();
            w.write(&mut buf).unwrap();
            let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
            crate::shard_reconstruct::reconstruct_from_shard_with_level_lists(
                &reader.exprs,
                &reader.levels,
                &reader.strings,
                &reader.level_lists,
                idx,
            )
            .unwrap()
        };

        assert_eq!(
            reconstruct(case_value),
            reconstruct(manual_value),
            "Case lowering must equal the manual or.0.rec recursor application"
        );
    }

    #[test]
    fn test_mutual_fixpoint_sexp_roundtrip() {
        // Parse and then import a mutual fixpoint
        let input =
            "(MutualFix ((even (Sort (Type 0)) (Rel 0) 0) (odd (Sort (Type 0)) (Rel 0) 0)) 1)";
        let (bodies, focus) = sexp_to_mutual_fixpoint(&parse_sexp(input).unwrap()).unwrap();
        assert_eq!(focus, 1);
        let mut w = ShardWriter::new();
        let indices = import_mutual_fixpoint(&bodies, focus, "Coq.Init.Nat", &mut w).unwrap();
        assert_eq!(indices.len(), 2);
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let names: Vec<&str> = reader
            .constants
            .iter()
            .map(|c| reader.strings[c.name_idx as usize].as_str())
            .collect();
        assert_eq!(names, vec!["even", "odd"]);
    }

    /// End-to-end: the RECURSIVE Coq definition `my_add` (structural recursion
    /// on `n:nat`, the same shape as `Nat.add`) plus its `nat` inductive is
    /// genuinely `KernelVerified` by the corpus verifier. The `StructFix` value
    /// lowers to a `nat.0.rec` recursor application; the kernel typechecks the
    /// elimination through `add_decl`, so `my_add` is NOT axiom-masked.
    ///
    /// Negative control: corrupt the `S` minor premise so it returns `S p` (the
    /// constructor field) instead of `S ih` (the induction hypothesis). Now the
    /// body has the right TYPE (`nat`) but the *whole definition still
    /// type-checks* — type alone cannot catch it. So instead the negative
    /// control replaces the `S` branch with an ill-TYPED body (`S` applied to
    /// the motive lambda itself), which the recursor's minor-premise type
    /// rejects, forcing `axiom_fallback`. This proves the kernel really
    /// typechecks the recursor minor premises, not just their shape.
    #[test]
    fn test_recursive_fix_definition_kernel_verifies() {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;

        let verify = |sexp: &str| {
            let mut w = ShardWriter::new();
            CoqImporter.import_sexp(sexp, &mut w).unwrap();
            let mut buf = Vec::new();
            w.write(&mut buf).unwrap();
            let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
            let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
            lib.load_shard(&reader).unwrap();
            let prelude =
                clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
            verify_corpus_incremental(&lib, prelude)
        };

        // Positive: nat(3) + my_add(1) all kernel-verify, no axiom masking.
        let report = verify(MY_ADD_CLOSURE_SEXP);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert_eq!(
            report.axiom_fallback, 0,
            "the recursive definition must not be masked by an axiom fallback: {:?}",
            report.axiom_fallback_names
        );
        assert_eq!(report.kernel_verified, 4, "nat(3) + my_add(1)");
        assert!(
            report.kernel_verified_names.contains(&"my_add".to_string()),
            "the recursive Fix definition my_add must be genuinely KernelVerified, got {:?}",
            report.kernel_verified_names
        );

        // Negative control: corrupt the recursor's motive universe instance
        // (`RecLevel 1` → `RecLevel 0`). The motive `λ_.nat` returns `nat : Set =
        // Sort 1`, so `nat.0.rec` must be instantiated at level 1; at level 0 the
        // recursor application is genuinely ill-typed (the minor premise's
        // expected result sort becomes `Sort 0` while the body lands in `Sort 1`)
        // and the kernel REJECTS it. So my_add must NOT kernel-verify. This
        // proves the kernel really typechecks the recursor application the Fix
        // lowering produces.
        //
        // The mismatch is UNIVERSE-ONLY (`Sort 0` vs `Sort 1` — the same term
        // modulo universe levels), so the verifier recognizes it as a
        // universe-COLLAPSE reconstruction gap (see `types_eq_modulo_universe`)
        // and withholds the value to a CLEAN type-only stand-in rather than a
        // masked-failure taint seed. SOUNDNESS is unchanged and still asserted:
        // my_add is NOT `KernelVerified` (the property this control guards), and
        // the stand-in posits ONLY my_add's kernel-checked TYPE (a Coq-provable
        // statement), never the rejected value — so nothing false can ever rest
        // on it. What changed is only the LANE: `standin_blocked_fallbacks`
        // (clean, no taint) instead of a masked `axiom_fallback_names` seed.
        let bad = MY_ADD_CLOSURE_SEXP.replace("(RecLevel 1)", "(RecLevel 0)");
        assert_ne!(bad, MY_ADD_CLOSURE_SEXP, "negative control must differ");
        let neg = verify(&bad);
        assert!(
            !neg.kernel_verified_names.contains(&"my_add".to_string()),
            "an ill-typed recursor application must be REJECTED, not KernelVerified"
        );
        assert_eq!(
            neg.axiom_fallback, 1,
            "the rejected recursive definition falls back to a value-less row: {:?}",
            neg.standin_blocked_fallbacks
        );
        assert!(
            neg.axiom_fallback_names.is_empty(),
            "a universe-only mismatch is a reconstruction gap, NOT a masked-failure \
             taint seed: {:?}",
            neg.axiom_fallback_names
        );
        assert!(
            neg.standin_blocked_fallbacks
                .iter()
                .any(|(name, err)| name == "my_add" && err.contains("Type mismatch")),
            "my_add's rejected value must be recorded as a universe-collapse \
             reconstruction-gap stand-in carrying the kernel TYPE MISMATCH, got {:?}",
            neg.standin_blocked_fallbacks
        );
    }

    /// Stretch: the computational theorem `two_plus_two : my_add 2 2 = 4` is
    /// genuinely `KernelVerified`. Its `eq_refl` proof only type-checks if the
    /// kernel REDUCES `my_add 2 2` (iota on the imported `nat.0.rec` produced by
    /// the `Fix` lowering) all the way to `4` — the real payoff of `Fix` support.
    ///
    /// Negative control: change the right-hand side to `5` (`S (S (S (S (S
    /// O)))))`). Now `my_add 2 2 = 4 ≠ 5`, so the kernel's iota reduction
    /// produces a value `eq_refl` cannot type against, and the theorem falls back
    /// to an axiom — proving the kernel really computed `my_add`, not just
    /// matched syntax.
    #[test]
    fn test_computational_theorem_two_plus_two_reduces() {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;

        let verify = |sexp: &str| {
            let mut w = ShardWriter::new();
            CoqImporter.import_sexp(sexp, &mut w).unwrap();
            let mut buf = Vec::new();
            w.write(&mut buf).unwrap();
            let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
            let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
            lib.load_shard(&reader).unwrap();
            let prelude =
                clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
            verify_corpus_incremental(&lib, prelude)
        };

        let report = verify(TWO_PLUS_TWO_CLOSURE_SEXP);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert_eq!(
            report.axiom_fallback, 0,
            "the computational theorem must not be masked by an axiom fallback: {:?}",
            report.axiom_fallback_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"two_plus_two".to_string()),
            "the computational theorem two_plus_two (= reduces my_add 2 2 to 4) \
             must be genuinely KernelVerified, got {:?}",
            report.kernel_verified_names
        );
        assert!(
            report.kernel_verified_names.contains(&"my_add".to_string()),
            "the recursive my_add it reduces must also be KernelVerified"
        );

        // Negative control: claim `my_add 2 2 = 5`. The kernel reduces the LHS to
        // `4` and finds `4 ≠ 5`, so eq_refl is ill-typed → axiom fallback.
        let bad = TWO_PLUS_TWO_CLOSURE_SEXP.replace(
            "(App (Construct nat 0 1) (App (Construct nat 0 1) (App (Construct nat 0 1) (App (Construct nat 0 1) (Construct nat 0 0))))))",
            "(App (Construct nat 0 1) (App (Construct nat 0 1) (App (Construct nat 0 1) (App (Construct nat 0 1) (App (Construct nat 0 1) (Construct nat 0 0)))))))",
        );
        assert_ne!(
            bad, TWO_PLUS_TWO_CLOSURE_SEXP,
            "negative control must differ"
        );
        let neg = verify(&bad);
        assert!(
            !neg.kernel_verified_names
                .contains(&"two_plus_two".to_string()),
            "a false computational claim (my_add 2 2 = 5) must be REJECTED, not KernelVerified"
        );
    }

    /// The structured `StructFix` lowering must produce exactly the same
    /// recursor application a hand-written `@nat.0.rec.{1} …` term would. We
    /// compare the reconstructed kernel `Expr` of `my_add`'s value built two
    /// ways: once from the `(StructFix …)` dialect, once from an explicit
    /// `(App (Const nat.0.rec) …)` term wrapped in the binder lambdas. Identical
    /// kernel `Expr` ⇒ the lowering is the recursor application, nothing more.
    #[test]
    fn test_struct_fix_lowering_matches_manual_recursor() {
        let fix_value = r#"(StructFix (Ind nat 0)
    (RecLevel 1)
    (StructTy (Ind nat 0))
    (Post (Ind nat 0))
    (Motive (Lambda x (Ind nat 0) (Ind nat 0)))
    (Branch (Rel 0))
    (Branch (Lambda p (Ind nat 0) (Lambda ih (Ind nat 0) (App (Construct nat 0 1) (Rel 0))))))"#;

        // Build the manual recursor reference WITH the level-1 instance by hand
        // (the importer dialect's `(Const …)` carries no level instance, so we
        // construct the FlatExpr directly), then wrap in `λ n. λ m. …`.
        let reconstruct_manual = || {
            let mut w = ShardWriter::new();
            let nat_ind = |w: &mut ShardWriter| {
                let ni = w.add_string("nat.0");
                w.add_expr(FlatExpr::const_ref(ni, u32::MAX))
            };
            let nat_ty = nat_ind(&mut w);
            let nat_cod = nat_ind(&mut w);
            let motive = w.add_expr(FlatExpr::lam(0, nat_ty, nat_cod));
            let minor_o = w.add_expr(FlatExpr::bvar(0));
            let s_ni = w.add_string("nat.0.1");
            let s_ref = w.add_expr(FlatExpr::const_ref(s_ni, u32::MAX));
            let ih_ref = w.add_expr(FlatExpr::bvar(0));
            let s_app = w.add_expr(FlatExpr::app(s_ref, ih_ref));
            let p_ty = nat_ind(&mut w);
            let ih_ty = nat_ind(&mut w);
            let inner_lam = w.add_expr(FlatExpr::lam(0, ih_ty, s_app));
            let minor_s = w.add_expr(FlatExpr::lam(0, p_ty, inner_lam));
            let major = w.add_expr(FlatExpr::bvar(1));
            let z = w.add_level(FlatLevel::zero());
            let one = w.add_level(FlatLevel::succ(z));
            let lvl_list = w.add_level_list(&[one]);
            let rec_ni = w.add_string("nat.0.rec");
            let rec_ref = w.add_expr(FlatExpr::const_ref(rec_ni, lvl_list));
            let a1 = w.add_expr(FlatExpr::app(rec_ref, motive));
            let a2 = w.add_expr(FlatExpr::app(a1, minor_o));
            let a3 = w.add_expr(FlatExpr::app(a2, minor_s));
            let a4 = w.add_expr(FlatExpr::app(a3, major));
            let m_ty = nat_ind(&mut w);
            let body_m = w.add_expr(FlatExpr::lam(0, m_ty, a4));
            let n_ty = nat_ind(&mut w);
            let idx = w.add_expr(FlatExpr::lam(0, n_ty, body_m));
            let mut buf = Vec::new();
            w.write(&mut buf).unwrap();
            let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
            crate::shard_reconstruct::reconstruct_from_shard_with_level_lists(
                &reader.exprs,
                &reader.levels,
                &reader.strings,
                &reader.level_lists,
                idx,
            )
            .unwrap()
        };

        let reconstruct_dialect = || {
            let cic = sexp_to_cic(&parse_sexp(fix_value).unwrap()).unwrap();
            let mut w = ShardWriter::new();
            let idx = cic_to_flat_expr(&cic, &mut w);
            let mut buf = Vec::new();
            w.write(&mut buf).unwrap();
            let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
            crate::shard_reconstruct::reconstruct_from_shard_with_level_lists(
                &reader.exprs,
                &reader.levels,
                &reader.strings,
                &reader.level_lists,
                idx,
            )
            .unwrap()
        };

        assert_eq!(
            reconstruct_dialect(),
            reconstruct_manual(),
            "StructFix lowering must equal the manual nat.0.rec.{{1}} recursor application"
        );
    }

    // =======================================================================
    // COQ-1a/COQ-2/COQ-3 hardening tests: raw SerAPI 8.20 fidelity, sort
    // model fail-closed behavior, loud value-drop accounting, qualified
    // names, zero-ctor inductives, mutual rejection, profile honesty.
    // All raw fixtures below were captured LIVE from this machine's
    // ~/.opam/mathverse-serapi/bin/sertop (Coq 8.20).
    // =======================================================================

    // REAL sertop 8.20 dump of the `Coq.Sets.Ensembles` singleton closure:
    // the `Ensemble := λU. U → Prop` type synonym, the `In` membership def, the
    // index-carrying `Singleton U x : Ensemble U` inductive (its index hidden
    // behind `Ensemble`), and its `Singleton_ind` eliminator (an indexed match
    // whose return predicate binds that hidden index).
    const RAW_ENSEMBLE_DEF: &str = r#"(CoqConstant Coq.Sets.Ensembles.Ensemble (Prod ((binder_name (Name (Id U))) (binder_relevance Relevant)) (Sort (Type ((((hash 83695642373356708) (data (Level ((DirPath ((Id Ensembles) (Id Sets) (Id Coq))) 19962254116)))) 0)))) (Sort (Type ((((hash 9) (data SProp)) 1) (((hash 83695642373356708) (data (Level ((DirPath ((Id Ensembles) (Id Sets) (Id Coq))) 19962254116)))) 0))))) (Lambda ((binder_name (Name (Id U))) (binder_relevance Relevant)) (Sort (Type ((((hash 83695642373356708) (data (Level ((DirPath ((Id Ensembles) (Id Sets) (Id Coq))) 19962254116)))) 0)))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 1) (Sort Prop))))"#;
    const RAW_IN_DEF: &str = r#"(CoqConstant Coq.Sets.Ensembles.In (Prod ((binder_name (Name (Id U))) (binder_relevance Relevant)) (Sort (Type ((((hash 83695642373356708) (data (Level ((DirPath ((Id Ensembles) (Id Sets) (Id Coq))) 19962254116)))) 0)))) (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Ensembles) (Id Sets) (Id Coq)))) (Id Ensemble)) ()) (Instance (() ())))) ((Rel 1))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 2) (Sort Prop)))) (Lambda ((binder_name (Name (Id U))) (binder_relevance Relevant)) (Sort (Type ((((hash 83695642373356708) (data (Level ((DirPath ((Id Ensembles) (Id Sets) (Id Coq))) 19962254116)))) 0)))) (Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Ensembles) (Id Sets) (Id Coq)))) (Id Ensemble)) ()) (Instance (() ())))) ((Rel 1))) (Lambda ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 2) (App (Rel 2) ((Rel 1)))))))"#;
    const RAW_SINGLETON_IND_DECL: &str = r#"(CoqInductive Coq.Sets.Ensembles.Singleton 0 (Prod ((binder_name (Name (Id U))) (binder_relevance Relevant)) (Sort (Type ((((hash 83695642373356708) (data (Level ((DirPath ((Id Ensembles) (Id Sets) (Id Coq))) 19962254116)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Ensembles) (Id Sets) (Id Coq)))) (Id Ensemble)) ()) (Instance (() ())))) ((Rel 2))))) (NumParams 2) (Ctor Coq.Sets.Ensembles.In_singleton (Prod ((binder_name (Name (Id U))) (binder_relevance Relevant)) (Sort (Type ((((hash 83695642373356708) (data (Level ((DirPath ((Id Ensembles) (Id Sets) (Id Coq))) 19962254116)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Ensembles) (Id Sets) (Id Coq)))) (Id In)) ()) (Instance (() ())))) ((Rel 2) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Ensembles) (Id Sets) (Id Coq)))) (Id Singleton)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1))) (Rel 1)))))))"#;
    const RAW_SINGLETON_IND_ELIM: &str = r#"(CoqConstant Coq.Sets.Ensembles.Singleton_ind (Prod ((binder_name (Name (Id U))) (binder_relevance Relevant)) (Sort (Type ((((hash 83695642373356708) (data (Level ((DirPath ((Id Ensembles) (Id Sets) (Id Coq))) 19962254116)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (Prod ((binder_name (Name (Id P))) (binder_relevance Relevant)) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 2) (Sort Prop)) (Prod ((binder_name (Name (Id f))) (binder_relevance Relevant)) (App (Rel 1) ((Rel 2))) (Prod ((binder_name (Name (Id u))) (binder_relevance Relevant)) (Rel 4) (Prod ((binder_name (Name (Id s))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Ensembles) (Id Sets) (Id Coq)))) (Id Singleton)) ()) 0) (Instance (() ())))) ((Rel 5) (Rel 4) (Rel 1))) (App (Rel 4) ((Rel 2))))))))) (Lambda ((binder_name (Name (Id U))) (binder_relevance Relevant)) (Sort (Type ((((hash 83695642373356708) (data (Level ((DirPath ((Id Ensembles) (Id Sets) (Id Coq))) 19962254116)))) 0)))) (Lambda ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (Lambda ((binder_name (Name (Id P))) (binder_relevance Relevant)) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 2) (Sort Prop)) (Lambda ((binder_name (Name (Id f))) (binder_relevance Relevant)) (App (Rel 1) ((Rel 2))) (Lambda ((binder_name (Name (Id u))) (binder_relevance Relevant)) (Rel 4) (Lambda ((binder_name (Name (Id s))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Ensembles) (Id Sets) (Id Coq)))) (Id Singleton)) ()) 0) (Instance (() ())))) ((Rel 5) (Rel 4) (Rel 1))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Ensembles) (Id Sets) (Id Coq)))) (Id Singleton)) ()) 0)) (ci_npar 2) (ci_cstr_ndecls (0)) (ci_cstr_nargs (0)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 6) (Rel 5)) (((((binder_name (Name (Id u))) (binder_relevance Relevant)) ((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 6) ((Rel 2)))) Relevant) NoInvert (Rel 1) ((() (Rel 3)))))))))))"#;

    /// Ensembles-shaped INDEXED-ELIMINATOR flip: `Singleton U x : Ensemble U`
    /// has an index HIDDEN behind the `Ensemble := λU. U → Prop` synonym. The
    /// arity-synonym δ-unfold exposes it in the reconstruction registry, so the
    /// indexed match in `Singleton_ind` reconstructs into the kernel recursor
    /// and genuinely KernelVerifies — where before the fix it failed the
    /// return-predicate-arity guard and fell back to a type-only axiom.
    #[test]
    fn test_indexed_eliminator_ensembles_synonym_flips_and_wrong_arity_rejects() {
        let good = format!(
            "{RAW_ENSEMBLE_DEF}\n{RAW_IN_DEF}\n{RAW_SINGLETON_IND_DECL}\n{RAW_SINGLETON_IND_ELIM}"
        );
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&good, &mut w).expect("import runs");
        assert!(
            !stats
                .value_failure_reasons
                .iter()
                .any(|(n, _)| n == "Coq.Sets.Ensembles.Singleton_ind"),
            "Singleton_ind value must reconstruct (not drop): {:?}",
            stats.value_failure_reasons
        );
        let report = verify_sexp_cumulative(&good);
        assert!(
            report
                .kernel_verified_names
                .contains(&"Coq.Sets.Ensembles.Singleton_ind".to_string()),
            "Singleton_ind must be KernelVerified (indexed recursor over the \
             synonym-hidden index) — fallbacks: {:?}",
            report.axiom_fallback_names
        );

        // NEGATIVE CONTROL: corrupt the eliminator's return predicate to bind
        // ONE binder (only the scrutinee) instead of the two the index-carrying
        // arity demands. A value-corrupting relaxation would let the wrong-arity
        // motive through; the reconstruction MUST fail closed (never a false KV).
        let bad_elim = RAW_SINGLETON_IND_ELIM.replace(
            "(((((binder_name (Name (Id u))) (binder_relevance Relevant)) ((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 6) ((Rel 2)))) Relevant)",
            "(((((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 6) ((Rel 2)))) Relevant)",
        );
        assert_ne!(
            bad_elim, RAW_SINGLETON_IND_ELIM,
            "corruption must change the term"
        );
        let bad = format!("{RAW_ENSEMBLE_DEF}\n{RAW_IN_DEF}\n{RAW_SINGLETON_IND_DECL}\n{bad_elim}");
        let neg = verify_sexp_cumulative(&bad);
        assert!(
            !neg.kernel_verified_names
                .contains(&"Coq.Sets.Ensembles.Singleton_ind".to_string()),
            "a wrong-arity return predicate must NOT KernelVerify (fail closed)"
        );
    }

    fn verify_sexp(sexp: &str) -> crate::verify::incremental::IncrementalVerifyReport {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;

        let mut w = ShardWriter::new();
        CoqImporter.import_sexp(sexp, &mut w).unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).unwrap();
        let prelude =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        verify_corpus_incremental(&lib, prelude)
    }

    /// Like [`verify_sexp`] but on the CUMULATIVE (Coq re-verification) lane —
    /// exactly what `coq_import_command` uses for the corpus gate
    /// (`prelude.set_cumulative(true)`). Required for anything that depends on
    /// Coq's `Prop ≤ Set ≤ Type` subtyping or on template-polymorphic `prod`'s
    /// parametric-singleton LARGE elimination (`prod.0.rec.{motive,u,v}`), which
    /// is soundly granted ONLY on the cumulative lane.
    fn verify_sexp_cumulative(sexp: &str) -> crate::verify::incremental::IncrementalVerifyReport {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::{
            verify_corpus_incremental_with_env_policy, InductiveReplayPolicy,
        };

        let mut w = ShardWriter::new();
        CoqImporter.import_sexp(sexp, &mut w).unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).unwrap();
        let mut prelude =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        prelude.set_cumulative(true);
        verify_corpus_incremental_with_env_policy(&lib, prelude, InductiveReplayPolicy::Generate).1
    }

    /// RAW SerAPI end-to-end (the COQ-3 proof obligation): the REAL
    /// `sertop`-captured `Fix` term of
    /// `Fixpoint my_add (n m:nat) {struct n} : nat := match n with O => m
    ///  | S p => S (my_add p m) end.` plus the REAL Qed proof term of
    /// `two_plus_two : my_add 2 2 = 4`, imported through
    /// `import_sexp → shard → verify_corpus_incremental`. The kernel must
    /// typecheck the structuralized recursor application AND iota-reduce
    /// `my_add 2 2` to `4` while checking `eq_refl`.
    const RAW_SERAPI_TWO_PLUS_TWO: &str = r#"(CoqInductive Coq.Init.Datatypes.nat 0 Set
  (Ctor O (Ind Coq.Init.Datatypes.nat 0))
  (Ctor S (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))))
(CoqInductive Coq.Init.Logic.eq 0 (Prod A (Sort (Type 1)) (Prod x (Rel 0) (Prod y (Rel 1) (Sort Prop))))
  (NumParams 2)
  (Ctor eq_refl (Prod A (Sort (Type 1)) (Prod x (Rel 0) (App (Ind Coq.Init.Logic.eq 0) (Rel 1) (Rel 0) (Rel 0))))))
(CoqConstant SerTop.my_add
  (Prod((binder_name(Name(Id n)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Prod((binder_name(Name(Id m)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))))
  (Fix(((0)0)((((binder_name(Name(Id my_add)))(binder_relevance Relevant)))((Prod((binder_name(Name(Id n)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Prod((binder_name(Name(Id m)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()())))))))((Lambda((binder_name(Name(Id n)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Lambda((binder_name(Name(Id m)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Case((ci_ind((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0))(ci_npar 0)(ci_cstr_ndecls(0 1))(ci_cstr_nargs(0 1))(ci_pp_info((style RegularStyle))))(Instance(()()))()(((((binder_name(Name(Id n)))(binder_relevance Relevant)))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()())))))Relevant)NoInvert(Rel 2)((()(Rel 1))((((binder_name(Name(Id p)))(binder_relevance Relevant)))(App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((App(Rel 4)((Rel 1)(Rel 2)))))))))))))))
(CoqConstant SerTop.two_plus_two
  (App(Ind(((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id eq))())0)(Instance(()()))))((Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(App(Const((Constant(KerName(MPfile(DirPath((Id SerTop))))(Id my_add))())(Instance(()()))))((App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)1)(Instance(()()))))))))(App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)1)(Instance(()()))))))))))(App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)1)(Instance(()()))))))))))))))
  (App(Construct((((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id eq))())0)1)(Instance(()()))))((Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)1)(Instance(()())))))))))))))))"#;

    #[test]
    fn test_raw_serapi_fix_two_plus_two_kernel_verifies() {
        let report = verify_sexp(RAW_SERAPI_TWO_PLUS_TWO);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert_eq!(
            report.axiom_fallback, 0,
            "no value may be masked by an axiom fallback: {:?}",
            report.axiom_fallback_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"SerTop.my_add".to_string()),
            "the RAW SerAPI Fix must structuralize and kernel-verify, got {:?}",
            report.kernel_verified_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"SerTop.two_plus_two".to_string()),
            "the computational theorem over the RAW Fix must kernel-verify \
             (iota-reduce my_add 2 2 to 4), got {:?}",
            report.kernel_verified_names
        );
    }

    #[test]
    fn test_raw_serapi_fix_import_stats_no_value_drops() {
        let mut w = ShardWriter::new();
        let stats = CoqImporter
            .import_sexp(RAW_SERAPI_TWO_PLUS_TWO, &mut w)
            .unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "no value may be dropped: {:?}",
            stats.value_failure_reasons
        );
        assert_eq!(stats.skipped, 0, "skips: {:?}", stats.skip_reasons);
        assert_eq!(stats.axiomatized, 0);
    }

    /// CROSS-FILE session registry: the RAW_SERAPI_TWO_PLUS_TWO closure split
    /// into a "file A" carrying only the `(CoqInductive ...)` forms and a
    /// "file B" carrying the `Fix`/`Case`-bearing constants. Without the
    /// registry, file B's values drop (`not in import session`); with the
    /// two-pass session registry they translate AND kernel-verify.
    #[test]
    fn test_cross_file_registry_case_translates_and_kernel_verifies() {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;

        let split = RAW_SERAPI_TWO_PLUS_TWO
            .find("(CoqConstant")
            .expect("fixture contains constants");
        let (file_a, file_b) = RAW_SERAPI_TWO_PLUS_TWO.split_at(split);

        // Negative control: file B alone (empty registry) drops my_add's Fix
        // because the matched inductive is not in the import session.
        let mut w_neg = ShardWriter::new();
        let neg = CoqImporter.import_sexp(file_b, &mut w_neg).unwrap();
        assert!(
            neg.value_translation_failed > 0,
            "without the registry the Fix value must drop loudly"
        );
        assert!(
            neg.value_failure_reasons
                .iter()
                .any(|(n, r)| n == "SerTop.my_add" && r.contains("not in import session")),
            "drop reason must name the registry gap: {:?}",
            neg.value_failure_reasons
        );

        // Two-pass session: register BOTH files (order-independent — B first),
        // then import each with the shared registry.
        let mut registry = CoqSessionRegistry::default();
        CoqImporter
            .register_inductive_forms(file_b, &mut registry)
            .expect("pass 1 over file B");
        CoqImporter
            .register_inductive_forms(file_a, &mut registry)
            .expect("pass 1 over file A");
        assert_eq!(registry.len(), 2, "nat + eq registered from file A");

        let mut w = ShardWriter::new();
        let stats_a = CoqImporter
            .import_sexp_with_registry(file_a, &registry, &mut w)
            .expect("import file A");
        let stats_b = CoqImporter
            .import_sexp_with_registry(file_b, &registry, &mut w)
            .expect("import file B");
        assert_eq!(stats_a.value_translation_failed, 0);
        assert_eq!(
            stats_b.value_translation_failed, 0,
            "cross-file Case/Fix must translate: {:?}",
            stats_b.value_failure_reasons
        );
        assert_eq!(stats_b.translated, 2, "my_add + two_plus_two");

        // Golden-style kernel verification of the merged shard.
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).unwrap();
        let prelude =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        let report = verify_corpus_incremental(&lib, prelude);
        assert_eq!(report.failed, 0, "failures: {:?}", report.failures);
        assert_eq!(
            report.axiom_fallback, 0,
            "no value may be masked: {:?}",
            report.axiom_fallback_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"SerTop.my_add".to_string())
                && report
                    .kernel_verified_names
                    .contains(&"SerTop.two_plus_two".to_string()),
            "cross-file Fix + its computational theorem must kernel-verify, got {:?}",
            report.kernel_verified_names
        );
    }

    /// An EMPTY session registry reproduces the historical single-file
    /// behavior byte-for-byte: `import_sexp` == `import_sexp_with_registry`
    /// with a default registry.
    #[test]
    fn test_import_sexp_with_empty_registry_matches_single_file_path() {
        let mut w1 = ShardWriter::new();
        let s1 = CoqImporter
            .import_sexp(RAW_SERAPI_TWO_PLUS_TWO, &mut w1)
            .unwrap();
        let mut w2 = ShardWriter::new();
        let s2 = CoqImporter
            .import_sexp_with_registry(
                RAW_SERAPI_TWO_PLUS_TWO,
                &CoqSessionRegistry::default(),
                &mut w2,
            )
            .unwrap();
        assert_eq!(s1.translated, s2.translated);
        assert_eq!(s1.value_translation_failed, s2.value_translation_failed);
        let (mut b1, mut b2) = (Vec::new(), Vec::new());
        w1.write(&mut b1).unwrap();
        w2.write(&mut b2).unwrap();
        assert_eq!(b1, b2, "shard bytes must be identical");
    }

    // ────────────────────────────────────────────────────────────────────
    // Canonical-first INDUCTIVE Dual resolution (`resolve_ind_family_name`,
    // 2026-07-16): microcosm of the `BinPos.Pos.mask` ← `BinPosDef.Pos.mask`
    // `Include`-duplication. `Orig.mask` is the canonical family; `Copy.mask`
    // is the duplicate whose every reference (its own constructors included)
    // carries the Dual `(user Copy, canonical Orig)`. A theorem MIXING the
    // spellings (statement over `Orig.mask`, one side defined through
    // `Copy.*`) rejects without the flip — the two copies ground in
    // different families — and kernel-verifies with it.
    // ────────────────────────────────────────────────────────────────────

    /// `(MutInd …)` node for `mask`, user-spelled `SerTop.<user>.mask`, with
    /// an optional canonical spelling `SerTop.<canon>.mask`.
    fn mask_mutind(user: &str, canon: Option<&str>) -> String {
        let kn = |m: &str| {
            format!("(KerName (MPdot (MPfile (DirPath ((Id SerTop)))) (Id {m})) (Id mask))")
        };
        match canon {
            Some(c) => format!("(MutInd {} ({}))", kn(user), kn(c)),
            None => format!("(MutInd {} ())", kn(user)),
        }
    }

    fn mask_ind_ref(user: &str, canon: Option<&str>) -> String {
        format!(
            "(Ind ((({}) 0) (Instance (() ()))))",
            mask_mutind(user, canon)
        )
    }

    /// 1-based ctor `j` of the `mask` family.
    fn mask_ctor_ref(user: &str, canon: Option<&str>, j: u32) -> String {
        format!(
            "(Construct (((({}) 0) {j}) (Instance (() ()))))",
            mask_mutind(user, canon)
        )
    }

    /// A two-constructor `Variant mask : Set := IsNul | IsPos`, module
    /// `SerTop.<user>`, whose SELF-references carry `canon` as the Dual.
    fn mask_family(user: &str, canon: Option<&str>) -> String {
        format!(
            "(CoqInductive SerTop.{user}.mask 0 (Sort Set) (NumParams 0) \
             (Ctor SerTop.{user}.IsNul {ind}) (Ctor SerTop.{user}.IsPos {ind}))",
            ind = mask_ind_ref(user, canon)
        )
    }

    fn dual_spelling_input() -> String {
        // REAL `Coq.Init.Logic.eq` dump form (verbatim shape from
        // `Coq.Init.Logic.sexp`) — the session must define `eq` itself.
        let eq_fam = r#"(CoqInductive Coq.Init.Logic.eq 0 (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 739561026853) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 23503782208)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 2) (Sort Prop)))) (NumParams 2) (Ctor Coq.Init.Logic.eq_refl (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 739561026853) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 23503782208)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1) (Rel 1)))))))"#;
        let orig_fam = mask_family("Orig", None);
        let copy_fam = mask_family("Copy", Some("Orig"));
        // c1 : Orig.mask := Orig.IsNul   (pure canonical spellings)
        let c1 = format!(
            "(CoqConstant SerTop.c1 {} {})",
            mask_ind_ref("Orig", None),
            mask_ctor_ref("Orig", None, 1)
        );
        // c2 : Copy.mask := Copy.IsNul   (every reference carries the Dual)
        let c2 = format!(
            "(CoqConstant SerTop.c2 {} {})",
            mask_ind_ref("Copy", Some("Orig")),
            mask_ctor_ref("Copy", Some("Orig"), 1)
        );
        // mixed : @eq Orig.mask c1 c2 := @eq_refl Orig.mask c1
        // Well-typed in Coq (the Dual says the copies are ONE inductive);
        // groundable here only when c2's rendering flips to the canonical
        // family.
        let eq_ind = "(Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ()))))";
        let eq_refl = "(Construct ((((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) 1) (Instance (() ()))))";
        let mixed = format!(
            "(CoqConstant SerTop.mixed (App {eq_ind} ({orig} (Const ((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id c1)) ()) (Instance (() ())))) (Const ((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id c2)) ()) (Instance (() ())))))) (App {eq_refl} ({orig} (Const ((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id c1)) ()) (Instance (() ())))))))",
            orig = mask_ind_ref("Orig", None)
        );
        // NEGATIVE CONTROL: same shape, but c2w picks the OTHER constructor —
        // the statement types under the flip, the proof must still reject.
        let c2w = format!(
            "(CoqConstant SerTop.c2w {} {})",
            mask_ind_ref("Copy", Some("Orig")),
            mask_ctor_ref("Copy", Some("Orig"), 2)
        );
        let mixed_wrong = format!(
            "(CoqConstant SerTop.mixed_wrong (App {eq_ind} ({orig} (Const ((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id c1)) ()) (Instance (() ())))) (Const ((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id c2w)) ()) (Instance (() ())))))) (App {eq_refl} ({orig} (Const ((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id c1)) ()) (Instance (() ())))))))",
            orig = mask_ind_ref("Orig", None)
        );
        // −41 GUARD: a duplicate whose canonical family (`Ghost`) is NOT in
        // the session — every reference must keep the user spelling and
        // verify against the `Lone` family itself.
        let lone_fam = mask_family("Lone", Some("Ghost"));
        let c3 = format!(
            "(CoqConstant SerTop.c3 {} {})",
            mask_ind_ref("Lone", Some("Ghost")),
            mask_ctor_ref("Lone", Some("Ghost"), 1)
        );
        format!(
            "{eq_fam}\n{orig_fam}\n{copy_fam}\n{c1}\n{c2}\n{mixed}\n{c2w}\n{mixed_wrong}\n{lone_fam}\n{c3}"
        )
    }

    /// COMPUTE TEST + NEGATIVE CONTROLS for the canonical-first inductive
    /// Dual resolution (the `sub_mask_succ_r` mixed-spelling class).
    #[test]
    fn test_inductive_dual_canonical_first_grounds_mixed_spellings() {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;

        let input = dual_spelling_input();
        let mut registry = CoqSessionRegistry::default();
        CoqImporter
            .register_inductive_forms(&input, &mut registry)
            .expect("family registration");
        CoqImporter
            .register_constant_shapes(&input, &mut registry)
            .expect("constant registration");
        let mut w = ShardWriter::new();
        CoqImporter
            .import_sexp_with_registry(&input, &registry, &mut w)
            .expect("import");
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).unwrap();
        let prelude =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        let report = verify_corpus_incremental(&lib, prelude);

        // The mixed-spelling theorem grounds in ONE family and verifies —
        // pre-flip its own STATEMENT rejected (`Copy.mask` vs `Orig.mask`).
        for name in ["SerTop.c1", "SerTop.c2", "SerTop.mixed", "SerTop.c3"] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must kernel-verify under the canonical-first flip; \
                 fallbacks: {:?}, failures: {:?}",
                report.axiom_fallback_names,
                report.failures
            );
        }
        // SELF-REFERENCE CARVE-OUT: the duplicate family itself (its
        // baseline-KV rows) still imports and verifies under its OWN name.
        for name in [
            "SerTop.Copy.mask.0",
            "SerTop.Orig.mask.0",
            "SerTop.Lone.mask.0",
        ] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "family row {name} must stay kernel-verified; failures: {:?}",
                report.failures
            );
        }
        // NEGATIVE CONTROL: the flip fixes SPELLINGS, never wrong proofs —
        // `IsNul = IsPos` must stay rejected.
        assert!(
            !report
                .kernel_verified_names
                .contains(&"SerTop.mixed_wrong".to_string()),
            "a wrong mixed-spelling proof must stay rejected under the flip"
        );
    }

    /// PASS-1c INDUCTIVE-REGISTRY CONSISTENCY (2026-07-16): a family whose
    /// constructor references an `Include`-copy (`Copy.mask`, whose Dual points
    /// at the canonical `Orig.mask`) can register — in file order — BEFORE the
    /// canonical copy of that type. The canonical-first flip
    /// ([`resolve_ind_family_name`]) only fires once the canonical block is
    /// registered, so a SINGLE registration pass FREEZES the family's registry
    /// constructor type at the unflipped `Copy.mask` spelling, while the import
    /// re-normalizes every term against the complete registry and flips it to
    /// `Orig.mask`. A `Case`/`Fix` on the family then reconstructs its branch
    /// field types from the stale registry entry
    /// ([`convert_serapi_case`] reads `info.ctor_types`), yielding the measured
    /// `prod positive BinPosDef.Pos.mask`-vs-`…BinPos.Pos.mask` mismatch that
    /// regressed the `Pos`/`Positive_as_DT`/`OrdersEx` `SqrtSpec`/`SubMaskSpec`
    /// eliminators and `N`/`Z.sqrtrem_spec`. The driver's second
    /// `register_inductive_forms` pass (PASS 1c) — with the whole name set
    /// present — flips the registry constructor type EXACTLY as the import does.
    #[test]
    fn test_pass1c_reregistration_flips_stale_include_copy_ctor_field() {
        // `Copy.mask` (Dual → `Orig.mask`) and `spec` (a `mk : Copy.mask →
        // spec` record) are declared BEFORE the canonical `Orig.mask` — the
        // real `BinPos`-before-`BinPosDef` file order in miniature.
        let copy_fam = mask_family("Copy", Some("Orig"));
        let spec = format!(
            "(CoqInductive SerTop.spec 0 (Sort Set) (NumParams 0) \
             (Ctor SerTop.mk (Prod ((binder_name (Name (Id m))) (binder_relevance Relevant)) {field} \
             (Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id spec)) ()) 0) \
             (Instance (() ())))))))",
            field = mask_ind_ref("Copy", Some("Orig"))
        );
        let orig_fam = mask_family("Orig", None);
        let input = format!("{copy_fam}\n{spec}\n{orig_fam}");

        // ONE registration pass: `Orig.mask` is not yet registered when `spec`
        // normalizes, so its field keeps the UNFLIPPED `Copy.mask`.
        let mut reg = CoqSessionRegistry::default();
        CoqImporter
            .register_inductive_forms(&input, &mut reg)
            .expect("first registration pass");
        let after_one = format!(
            "{:?}",
            reg.ctx
                .inductives
                .get("SerTop.spec.0")
                .expect("spec registered")
                .ctor_types[0]
        );
        assert!(
            after_one.contains("SerTop.Copy.mask") && !after_one.contains("SerTop.Orig.mask"),
            "single registration must freeze the stale Include-copy spelling, got: {after_one}"
        );

        // PASS 1c — a SECOND pass, now that every family name is registered,
        // flips the field to the canonical `Orig.mask`, matching the import.
        CoqImporter
            .register_inductive_forms(&input, &mut reg)
            .expect("consistency re-registration pass");
        let after_two = format!(
            "{:?}",
            reg.ctx
                .inductives
                .get("SerTop.spec.0")
                .expect("spec registered")
                .ctor_types[0]
        );
        assert!(
            after_two.contains("SerTop.Orig.mask") && !after_two.contains("SerTop.Copy.mask"),
            "the consistency re-pass must flip the field to the canonical family, got: {after_two}"
        );
    }

    /// Motive universe derivation through Π-chains (the `nat -> nat`-typed
    /// match shape) and its fail-closed boundaries.
    #[test]
    fn test_motive_result_level_prod_chain_derivation() {
        let mut ctx = SerapiNormCtx::default();
        let arity = parse_sexp("(Sort Set)").unwrap();
        let ctors = [
            parse_sexp("(Ind nat 0)").unwrap(),
            parse_sexp("(Prod n (Ind nat 0) (Ind nat 0))").unwrap(),
        ];
        ctx.register("nat", 0, 0, &arity, &ctors);
        let true_arity = parse_sexp("(Sort Prop)").unwrap();
        ctx.register(
            "mytrue",
            0,
            0,
            &true_arity,
            &[parse_sexp("(Ind mytrue 0)").unwrap()],
        );

        let level = |src: &str| motive_result_level_exact(&parse_sexp(src).unwrap(), &ctx, &[]);

        // Registered-inductive result (bare): nat : Set → level 1.
        assert_eq!(level("(Ind nat 0)"), Some(1));
        // Π-chain into a predicative codomain: nat -> nat : Set → max(1,1)=1.
        assert_eq!(level("(Prod x (Ind nat 0) (Ind nat 0))"), Some(1));
        // Deeper chain: nat -> nat -> nat.
        assert_eq!(
            level("(Prod x (Ind nat 0) (Prod y (Ind nat 0) (Ind nat 0)))"),
            Some(1)
        );
        // Impredicative Prop codomain wins regardless of the domain.
        assert_eq!(level("(Prod x (Ind nat 0) (Ind mytrue 0))"), Some(0));
        // Sort-valued codomain: nat -> Prop lives at level 1 (Prop : Type 1).
        assert_eq!(level("(Prod x (Ind nat 0) (Sort Prop))"), Some(1));
        // Unregistered domain with a non-Prop codomain: fail closed.
        assert_eq!(level("(Prod x (Ind mystery 0) (Ind nat 0))"), None);
        // Unregistered codomain: fail closed.
        assert_eq!(level("(Prod x (Ind nat 0) (Ind mystery 0))"), None);
        // Partially-applied inductive head is NOT the codomain sort: fail
        // closed (saturation check).
        let mut ctx2 = SerapiNormCtx::default();
        let list_arity = parse_sexp("(Prod A (Sort (Type 1)) (Sort (Type 1)))").unwrap();
        ctx2.register("list", 0, 1, &list_arity, &[]);
        assert_eq!(
            motive_result_level_exact(&parse_sexp("(Ind list 0)").unwrap(), &ctx2, &[]),
            None
        );
        assert_eq!(
            motive_result_level_exact(
                &parse_sexp("(App (Ind list 0) (Ind list 0))").unwrap(),
                &ctx2,
                &[]
            ),
            Some(1)
        );
        // Wrapper: the same underivable shape gets the speculative Prop default
        // (level 0) instead of `None` — the kernel then filters it (fail-closed).
        assert_eq!(
            motive_result_level(&parse_sexp("(Ind list 0)").unwrap(), &ctx2, &[]),
            Some(0)
        );
    }

    /// RAW SerAPI `Case` whose return predicate is FUNCTION-typed
    /// (`match n with O => fun m => m | S p => fun m => p end : nat -> nat`)
    /// — the motive universe level must now derive THROUGH the Π-chain
    /// (previously "recursor motive universe level underivable" → value
    /// drop), and the resulting recursor application must kernel-verify.
    const RAW_SERAPI_PROD_MOTIVE: &str = r#"(CoqInductive Coq.Init.Datatypes.nat 0 Set
  (Ctor O (Ind Coq.Init.Datatypes.nat 0))
  (Ctor S (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))))
(CoqConstant SerTop.const_swap
  (Prod n (Ind Coq.Init.Datatypes.nat 0) (Prod m (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0)))
  (Lambda((binder_name(Name(Id n)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Case((ci_ind((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0))(ci_npar 0)(ci_cstr_ndecls(0 1))(ci_cstr_nargs(0 1))(ci_pp_info((style RegularStyle))))(Instance(()()))()(((((binder_name(Name(Id n)))(binder_relevance Relevant)))(Prod((binder_name(Name(Id m)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))))Relevant)NoInvert(Rel 1)((()(Lambda((binder_name(Name(Id m)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Rel 1)))((((binder_name(Name(Id p)))(binder_relevance Relevant)))(Lambda((binder_name(Name(Id m)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Rel 2)))))))"#;

    #[test]
    fn test_prod_motive_case_translates_and_kernel_verifies() {
        // Import-level: the value must TRANSLATE (no motive-level drop).
        let mut w = ShardWriter::new();
        let stats = CoqImporter
            .import_sexp(RAW_SERAPI_PROD_MOTIVE, &mut w)
            .unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "Π-chain motive level must derive: {:?}",
            stats.value_failure_reasons
        );
        assert_eq!(stats.translated, 4, "nat family (3) + const_swap");

        // Kernel-level: the reconstructed recursor application typechecks.
        let report = verify_sexp(RAW_SERAPI_PROD_MOTIVE);
        assert_eq!(report.failed, 0, "failures: {:?}", report.failures);
        assert_eq!(
            report.axiom_fallback, 0,
            "no value may be masked: {:?}",
            report.axiom_fallback_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"SerTop.const_swap".to_string()),
            "the function-typed match must kernel-verify, got {:?}",
            report.kernel_verified_names
        );
    }

    /// RAW SerAPI end-to-end for the compact 8.20 `Case`: the REAL
    /// `sertop`-captured proof term of
    /// `Definition my_or_comm (A B:Prop) (h:or A B) : or B A := match h with
    ///  | or_introl a => or_intror a | or_intror b => or_introl b end.`
    /// The branch binder types are reconstructed from the registered `or`
    /// constructor types; the kernel typechecks the or.0.rec elimination.
    const RAW_SERAPI_OR_COMM: &str = r#"(CoqInductive Coq.Init.Logic.or 0 (Prod A (Sort Prop) (Prod B (Sort Prop) (Sort Prop)))
  (NumParams 2)
  (Ctor or_introl (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod a (Rel 1) (App (Ind Coq.Init.Logic.or 0) (Rel 2) (Rel 1))))))
  (Ctor or_intror (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod b (Rel 0) (App (Ind Coq.Init.Logic.or 0) (Rel 2) (Rel 1)))))))
(CoqConstant SerTop.my_or_comm
  (Prod((binder_name(Name(Id A)))(binder_relevance Relevant))(Sort Prop)(Prod((binder_name(Name(Id B)))(binder_relevance Relevant))(Sort Prop)(Prod((binder_name(Name(Id h)))(binder_relevance Relevant))(App(Ind(((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id or))())0)(Instance(()()))))((Rel 2)(Rel 1)))(App(Ind(((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id or))())0)(Instance(()()))))((Rel 2)(Rel 3))))))
  (Lambda((binder_name(Name(Id A)))(binder_relevance Relevant))(Sort Prop)(Lambda((binder_name(Name(Id B)))(binder_relevance Relevant))(Sort Prop)(Lambda((binder_name(Name(Id h)))(binder_relevance Relevant))(App(Ind(((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id or))())0)(Instance(()()))))((Rel 2)(Rel 1)))(Case((ci_ind((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id or))())0))(ci_npar 2)(ci_cstr_ndecls(1 1))(ci_cstr_nargs(1 1))(ci_pp_info((style RegularStyle))))(Instance(()()))((Rel 3)(Rel 2))(((((binder_name(Name(Id h)))(binder_relevance Relevant)))(App(Ind(((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id or))())0)(Instance(()()))))((Rel 3)(Rel 4))))Relevant)NoInvert(Rel 1)(((((binder_name(Name(Id a)))(binder_relevance Relevant)))(App(Construct((((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id or))())0)2)(Instance(()()))))((Rel 3)(Rel 4)(Rel 1))))((((binder_name(Name(Id b)))(binder_relevance Relevant)))(App(Construct((((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id or))())0)1)(Instance(()()))))((Rel 3)(Rel 4)(Rel 1))))))))))"#;

    #[test]
    fn test_raw_serapi_case_or_comm_kernel_verifies() {
        let report = verify_sexp(RAW_SERAPI_OR_COMM);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert_eq!(
            report.axiom_fallback, 0,
            "the RAW Case proof must not be axiom-masked: {:?}",
            report.axiom_fallback_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"SerTop.my_or_comm".to_string()),
            "the RAW SerAPI Case proof term must kernel-verify, got {:?}",
            report.kernel_verified_names
        );
    }

    /// App(`Rel`)-headed indexed-match discriminant recovery — the dominant
    /// residual mathcomp shape (the ssreflect comparison-spec families
    /// `eq_xor_neq`/`leq_xor_gtn`/… eliminated on a locally-bound spec term
    /// `p args…`). `idxar` matches on `h y : @eq nat O O` where the
    /// discriminant `h y` is `App(Rel h, y)`: neither the bare-`Rel` nor the
    /// `Const`-head recovery path fires, so the type is synthesized from `h`'s
    /// binder type (in `bctx`) instantiated at `y` (see
    /// [`synthesize_app_disc_type`]). The recovered index (`z := O`) is what
    /// the kernel's recursor major premise checks against, so the value KVs
    /// ONLY if the recovery is faithful.
    ///
    ///   idxar (h : nat -> @eq nat O O) (y : nat) : nat :=
    ///     match h y in (_ = z) return nat with eq_refl => O end
    const RAW_SERAPI_IDXAR: &str = concat!(
        "(CoqConstant SerTop.idxar ",
        "(Prod h (Prod _ (Ind Coq.Init.Datatypes.nat 0) ",
        "(App (Ind Coq.Init.Logic.eq 0) (Ind Coq.Init.Datatypes.nat 0) ",
        "(Construct Coq.Init.Datatypes.nat 0 0) (Construct Coq.Init.Datatypes.nat 0 0))) ",
        "(Prod y (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))) ",
        "(Lambda ((binder_name (Name (Id h))) (binder_relevance Relevant)) ",
        "(Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind Coq.Init.Datatypes.nat 0) ",
        "(App (Ind Coq.Init.Logic.eq 0) (Ind Coq.Init.Datatypes.nat 0) ",
        "(Construct Coq.Init.Datatypes.nat 0 0) (Construct Coq.Init.Datatypes.nat 0 0))) ",
        "(Lambda ((binder_name (Name (Id y))) (binder_relevance Relevant)) (Ind Coq.Init.Datatypes.nat 0) ",
        "(Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0)) ",
        "(ci_npar 2) (ci_cstr_ndecls (0)) (ci_cstr_nargs (0)) (ci_pp_info ((style RegularStyle)))) ",
        "(Instance (() ())) ",
        "((Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0)) ",
        "(((((binder_name (Name (Id z))) (binder_relevance Relevant)) ",
        "((binder_name Anonymous) (binder_relevance Relevant))) (Ind Coq.Init.Datatypes.nat 0)) Relevant) ",
        "NoInvert ",
        "(App (Rel 2) ((Rel 1))) ",
        "((() (Construct Coq.Init.Datatypes.nat 0 0)))))))",
    );

    /// Closed compute witness: `idxar (fun _ => @eq_refl nat O) O` reduces to
    /// `O`, so `@eq_refl nat O : @eq nat (idxar …) O` kernel-checks.
    const IDXAR_OK: &str = concat!(
        "(CoqConstant SerTop.idxar_ok ",
        "(App (Ind Coq.Init.Logic.eq 0) (Ind Coq.Init.Datatypes.nat 0) ",
        "(App (Const SerTop.idxar) ",
        "(Lambda _ (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Logic.eq 0 0) ",
        "(Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0))) ",
        "(Construct Coq.Init.Datatypes.nat 0 0)) (Construct Coq.Init.Datatypes.nat 0 0)) ",
        "(App (Construct Coq.Init.Logic.eq 0 0) (Ind Coq.Init.Datatypes.nat 0) ",
        "(Construct Coq.Init.Datatypes.nat 0 0)))",
    );

    #[test]
    fn test_app_rel_indexed_match_discriminant_recovers_and_computes() {
        let input = format!("{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_NAT}\n{RAW_SERAPI_IDXAR}\n{IDXAR_OK}");
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "the App(Rel)-headed indexed match must translate: {:?}",
            stats.value_failure_reasons
        );
        let report = verify_sexp(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in ["SerTop.idxar", "SerTop.idxar_ok"] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified (recovered index feeds the recursor major \
                 premise) — fallbacks: {:?}",
                report.axiom_fallback_names
            );
        }

        // NEGATIVE CONTROL (fidelity): claim `idxar (fun _ => eq_refl) O = S O`.
        // `idxar …` genuinely reduces to `O`, so `eq_refl (S O)` must be
        // REJECTED — a mis-recovered index that silently changed the value
        // would (wrongly) let this through.
        let bad_ok = concat!(
            "(CoqConstant SerTop.idxar_ok ",
            "(App (Ind Coq.Init.Logic.eq 0) (Ind Coq.Init.Datatypes.nat 0) ",
            "(App (Const SerTop.idxar) ",
            "(Lambda _ (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Logic.eq 0 0) ",
            "(Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0))) ",
            "(Construct Coq.Init.Datatypes.nat 0 0)) ",
            "(App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0))) ",
            "(App (Construct Coq.Init.Logic.eq 0 0) (Ind Coq.Init.Datatypes.nat 0) ",
            "(App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0))))",
        );
        let bad = format!("{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_NAT}\n{RAW_SERAPI_IDXAR}\n{bad_ok}");
        let neg = verify_sexp(&bad);
        assert!(
            !neg.kernel_verified_names
                .contains(&"SerTop.idxar_ok".to_string()),
            "`idxar (fun _ => eq_refl) O = S O` is FALSE and must be REJECTED"
        );
        // The function itself must still verify in the negative fixture — only
        // the false theorem is rejected.
        assert!(
            neg.kernel_verified_names
                .contains(&"SerTop.idxar".to_string()),
            "idxar itself must remain KernelVerified in the negative fixture"
        );
    }

    // ── ssreflect REFLECTION-ELIMINATION shape: a `Const`-DEFINITION-headed
    // indexed-match discriminant. Mirrors mathcomp `eqP : ∀ T, Equality.axiom
    // (sort T) (eq_op T)` where `Equality.axiom := λ_ _. ∀ x y, reflect …` is a
    // definition whose body carries the matched inductive under an intervening
    // `Π`. Here the reflection lemma `myrefl : ∀ x, myeqax x` has codomain headed
    // by the definition `myeqax := λx. ∀ u, @eq nat x x`; the discriminant
    // `myrefl O O : @eq nat O O` can only be recovered by DELTA-UNFOLDING
    // `myeqax` mid-peel (see `synthesize_app_disc_type`). Uses stdlib `eq`/`nat`
    // so the recovered index feeds the SAME recursor path the App(Rel) test
    // exercises — the discriminant HEAD is the only difference.

    /// `myeqax := λ(x:nat). ∀ (u:nat), @eq nat x x` — the Π-bearing type-former
    /// definition (the `Equality.axiom` analogue) whose body must be delta-
    /// unfolded to expose the `eq` head buried under the `∀ u` binder.
    const REFLECT_MYEQAX: &str = concat!(
        "(CoqConstant SerTop.myeqax ",
        "(Prod x (Ind Coq.Init.Datatypes.nat 0) (Sort Prop)) ",
        "(Lambda x (Ind Coq.Init.Datatypes.nat 0) ",
        "(Prod u (Ind Coq.Init.Datatypes.nat 0) ",
        "(App (Ind Coq.Init.Logic.eq 0) (Ind Coq.Init.Datatypes.nat 0) (Rel 1) (Rel 1)))))",
    );

    /// `myrefl := λ(x u:nat). @eq_refl nat x : ∀ (x:nat), myeqax x` — the
    /// reflection lemma whose codomain heads the `myeqax` DEFINITION (the `eqP`
    /// analogue). `myrefl O O` reduces to `@eq_refl nat O : @eq nat O O`.
    const REFLECT_MYREFL: &str = concat!(
        "(CoqConstant SerTop.myrefl ",
        "(Prod x (Ind Coq.Init.Datatypes.nat 0) (App (Const SerTop.myeqax) (Rel 0))) ",
        "(Lambda x (Ind Coq.Init.Datatypes.nat 0) (Lambda u (Ind Coq.Init.Datatypes.nat 0) ",
        "(App (Construct Coq.Init.Logic.eq 0 0) (Ind Coq.Init.Datatypes.nat 0) (Rel 1)))))",
    );

    /// `elim : nat := match (myrefl O O) in (_ = z) return nat with eq_refl => O`
    /// — the reflection elimination. Its discriminant `myrefl O O` is
    /// `Const`-DEFINITION-headed (through `myeqax`), so the indexed `eq`-match's
    /// index (`z := O`) is recoverable ONLY by delta-unfolding the definition.
    /// `elim` reduces to `O`.
    const REFLECT_ELIM: &str = concat!(
        "(CoqConstant SerTop.elim (Ind Coq.Init.Datatypes.nat 0) ",
        "(Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) ",
        "(Id eq)) ()) 0)) (ci_npar 2) (ci_cstr_ndecls (0)) (ci_cstr_nargs (0)) ",
        "(ci_pp_info ((style RegularStyle)))) (Instance (() ())) ",
        "((Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0)) ",
        "(((((binder_name (Name (Id z))) (binder_relevance Relevant)) ",
        "((binder_name Anonymous) (binder_relevance Relevant))) (Ind Coq.Init.Datatypes.nat 0)) ",
        "Relevant) NoInvert ",
        "(App (Const SerTop.myrefl) (Construct Coq.Init.Datatypes.nat 0 0) ",
        "(Construct Coq.Init.Datatypes.nat 0 0)) ",
        "((() (Construct Coq.Init.Datatypes.nat 0 0)))))",
    );

    /// Closed compute witness: `elim` reduces to `O`, so `@eq_refl nat O :
    /// @eq nat elim O` kernel-checks.
    const REFLECT_ELIM_OK: &str = concat!(
        "(CoqConstant SerTop.elim_ok ",
        "(App (Ind Coq.Init.Logic.eq 0) (Ind Coq.Init.Datatypes.nat 0) ",
        "(Const SerTop.elim) (Construct Coq.Init.Datatypes.nat 0 0)) ",
        "(App (Construct Coq.Init.Logic.eq 0 0) (Ind Coq.Init.Datatypes.nat 0) ",
        "(Construct Coq.Init.Datatypes.nat 0 0)))",
    );

    #[test]
    fn test_const_def_headed_reflection_elim_recovers_and_computes() {
        let defs = format!("{REFLECT_MYEQAX}\n{REFLECT_MYREFL}\n{REFLECT_ELIM}");
        let input = format!("{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_NAT}\n{defs}\n{REFLECT_ELIM_OK}");
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "the Const-definition-headed reflection match must translate \
             (the `myeqax` codomain is delta-unfolded to `eq`): {:?}",
            stats.value_failure_reasons
        );
        let report = verify_sexp(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in [
            "SerTop.myeqax",
            "SerTop.myrefl",
            "SerTop.elim",
            "SerTop.elim_ok",
        ] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified — the reflection-elimination \
                 discriminant type is recovered by delta-unfolding the `myeqax` \
                 definition and its recovered index feeds the recursor. \
                 fallbacks: {:?}",
                report.axiom_fallback_names
            );
        }

        // NEGATIVE CONTROL (fidelity): claim `elim = S O`. `elim` genuinely
        // reduces to `O` through the reconstructed reflection elimination, so
        // `@eq_refl nat (S O) : @eq nat elim (S O)` is FALSE and the kernel must
        // REJECT it. A mis-recovered discriminant index that silently changed the
        // reduction would (wrongly) let this through — the recovery is speculative
        // (`SPECULATIVE_MOTIVE`), so a wrong recovery fails closed here.
        let bad_ok = concat!(
            "(CoqConstant SerTop.elim_ok ",
            "(App (Ind Coq.Init.Logic.eq 0) (Ind Coq.Init.Datatypes.nat 0) ",
            "(Const SerTop.elim) ",
            "(App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0))) ",
            "(App (Construct Coq.Init.Logic.eq 0 0) (Ind Coq.Init.Datatypes.nat 0) ",
            "(App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0))))",
        );
        let bad = format!("{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_NAT}\n{defs}\n{bad_ok}");
        let neg = verify_sexp(&bad);
        assert!(
            !neg.kernel_verified_names
                .contains(&"SerTop.elim_ok".to_string()),
            "`elim = S O` is FALSE (elim reduces to O) and must be REJECTED"
        );
        assert!(
            neg.kernel_verified_names
                .contains(&"SerTop.elim".to_string()),
            "elim itself must remain KernelVerified in the negative fixture"
        );
    }

    #[test]
    fn test_normalize_serapi_cast_dropped() {
        // Real sertop output for `Definition casted : nat := (O : nat).`
        let ctx = SerapiNormCtx::default();
        let src = r#"(Cast(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)1)(Instance(()()))))DEFAULTcast(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()())))))"#;
        let cic = sexp_to_cic(&normalize_serapi_rec(&parse_sexp(src).unwrap(), &ctx, &[])).unwrap();
        assert!(
            matches!(cic, CicTerm::Construct(ref n, 0, 0) if n == "Coq.Init.Datatypes.nat"),
            "Cast must be dropped, keeping the qualified term: {cic:?}"
        );
    }

    #[test]
    fn test_normalize_serapi_letin() {
        // Real sertop output for `Definition letex : nat := let x := O in S x.`
        let ctx = SerapiNormCtx::default();
        let src = r#"(LetIn((binder_name(Name(Id x)))(binder_relevance Relevant))(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)1)(Instance(()()))))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((Rel 1))))"#;
        let cic = sexp_to_cic(&normalize_serapi_rec(&parse_sexp(src).unwrap(), &ctx, &[])).unwrap();
        match cic {
            CicTerm::LetIn(name, val, ty, body) => {
                assert_eq!(name, "x");
                assert!(
                    matches!(*val, CicTerm::Construct(ref n, 0, 0) if n == "Coq.Init.Datatypes.nat")
                );
                assert!(matches!(*ty, CicTerm::Ind(ref n, 0) if n == "Coq.Init.Datatypes.nat"));
                match *body {
                    CicTerm::App(f, args) => {
                        assert!(matches!(
                            *f,
                            CicTerm::Construct(ref n, 0, 1) if n == "Coq.Init.Datatypes.nat"
                        ));
                        assert!(matches!(args.as_slice(), [CicTerm::Rel(0)]));
                    }
                    other => panic!("expected App body, got {other:?}"),
                }
            }
            other => panic!("expected LetIn, got {other:?}"),
        }
    }

    #[test]
    fn test_serapi_sort_model_fail_closed() {
        let ctx = SerapiNormCtx::default();
        // Set is preserved (distinct dialect encoding from Type 1, same level).
        let set = normalize_serapi(&parse_sexp("(Sort Set)").unwrap(), &ctx, &[]).unwrap();
        assert!(matches!(
            sexp_to_cic(&set).unwrap(),
            CicTerm::Sort(CicSort::Set)
        ));
        // Monomorphic single-global-level Type collapses to (Type 1).
        let ty = normalize_serapi(
            &parse_sexp(r#"(Sort(Type((((hash 1)(data(Level((DirPath((Id SerTop)))1))))0))))"#)
                .unwrap(),
            &ctx,
            &[],
        )
        .unwrap();
        assert!(matches!(
            sexp_to_cic(&ty).unwrap(),
            CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Type(1)))
        ));
        // SProp: out of model, loud.
        let sprop = normalize_serapi(&parse_sexp("(Sort SProp)").unwrap(), &ctx, &[]).unwrap();
        let err = sexp_to_cic(&sprop).expect_err("SProp must fail closed");
        assert!(
            err.to_string().contains("out-of-model (SProp)"),
            "got {err}"
        );
        // Algebraic increments are IN model under the increment-aware collapse
        // (`base(Set)=0, base(named)=1, level = max(1, base+incr)`): `Set + 2`
        // and `named + 1` both map to `(Type 2)`, one above the `Type 1` target.
        let set2 = normalize_serapi(
            &parse_sexp(r#"(Sort(Type((((hash 9)(data SProp))2))))"#).unwrap(),
            &ctx,
            &[],
        )
        .unwrap();
        assert!(matches!(
            sexp_to_cic(&set2).unwrap(),
            CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Type(2)))
        ));
        let named_inc = normalize_serapi(
            &parse_sexp(r#"(Sort(Type((((hash 14)(data(Level((DirPath((Id SerTop)))7))))1))))"#)
                .unwrap(),
            &ctx,
            &[],
        )
        .unwrap();
        assert!(matches!(
            sexp_to_cic(&named_inc).unwrap(),
            CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Type(2)))
        ));
        // Bound polymorphic level variable `(Var k)`: now collapses
        // MONOMORPHICALLY to `(Type 1)` (base 1, like a named global level).
        // References to the polymorphic constant are imported monomorphically
        // (instance stripped), so the binder collapse keeps it consistent; the
        // kernel re-checks. This recovers `Unconvertible`/`Proper`/`Morphisms`.
        let var = normalize_serapi(
            &parse_sexp(r#"(Sort(Type((((hash 14)(data(Var 0)))0))))"#).unwrap(),
            &ctx,
            &[],
        )
        .unwrap();
        assert!(matches!(
            sexp_to_cic(&var).unwrap(),
            CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Type(1)))
        ));
    }

    /// A genuinely out-of-model universe-polymorphic constant USE (a sort
    /// QUALITY VARIABLE in the instance — never droppable, unlike the
    /// speculative constant-quality/Set-level drops) drops the VALUE loudly:
    /// the constant stays type-only, axiomatized, trust-gated with
    /// UNIVERSE_INCON, and is COUNTED.
    #[test]
    fn test_serapi_polymorphic_instance_value_dropped_loudly() {
        let input = r#"(CoqInductive Coq.Init.Datatypes.nat 0 Set
  (Ctor O (Ind Coq.Init.Datatypes.nat 0))
  (Ctor S (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))))
(CoqConstant SerTop.usepoly
  (Ind Coq.Init.Datatypes.nat 0)
  (App(Const((Constant(KerName(MPfile(DirPath((Id SerTop))))(Id polyid))())(Instance(((QVar 0))(((hash 9)(data SProp)))))))((Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)1)(Instance(()())))))))"#;
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(input, &mut w).unwrap();
        assert_eq!(stats.value_translation_failed, 1);
        assert_eq!(stats.value_failure_reasons.len(), 1);
        assert_eq!(stats.value_failure_reasons[0].0, "SerTop.usepoly");
        assert!(
            stats.value_failure_reasons[0]
                .1
                .contains("out-of-model (universe)"),
            "reason must name the universe model violation: {:?}",
            stats.value_failure_reasons
        );
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let (_, c) = reader.lookup_name("SerTop.usepoly").unwrap();
        assert!(!c.has_value(), "the polymorphic value must be dropped");
        assert_eq!(c.decl_kind, DeclKind::Axiom as u8);
        assert_eq!(c.import_confidence, ImportConfidence::Axiomatized as u8);
        let p = c.profile();
        assert!(p.has(AxiomProfile::UNIVERSE_INCON), "trust-gate bit");
        assert!(p.has(AxiomProfile::AXIOMATIZED));
        assert!(p.is_trust_gated());
    }

    /// A `Set`-instantiated polymorphic constant USE (single pierced-`Set`
    /// instance, captured live from `Polymorphic Definition polyid@{u} …;
    /// Definition usepoly := polyid nat O.`) now takes the SPECULATIVE
    /// monomorphic drop: the value is EMITTED, the constant is marked
    /// `SPECULATIVE_MOTIVE`, and the kernel arbitrates at verify (accept →
    /// KV, reject → clean type-only axiom) — never a silent axiomatization.
    #[test]
    fn test_serapi_set_instance_value_emits_speculative() {
        let input = r#"(CoqInductive Coq.Init.Datatypes.nat 0 Set
  (Ctor O (Ind Coq.Init.Datatypes.nat 0))
  (Ctor S (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))))
(CoqConstant SerTop.usepoly
  (Ind Coq.Init.Datatypes.nat 0)
  (App(Const((Constant(KerName(MPfile(DirPath((Id SerTop))))(Id polyid))())(Instance(()(((hash 9)(data SProp)))))))((Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)1)(Instance(()())))))))"#;
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "the Set-instantiated value must translate (speculatively): {:?}",
            stats.value_failure_reasons
        );
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let (_, c) = reader.lookup_name("SerTop.usepoly").unwrap();
        assert!(
            c.has_value(),
            "the speculative mono-drop value must be kept"
        );
        assert_eq!(c.import_confidence, ImportConfidence::Translated as u8);
        assert!(
            c.profile().has(AxiomProfile::SPECULATIVE_MOTIVE),
            "the guessed drop must be marked speculative so verify fails closed"
        );
    }

    /// A constant-quality (fully quality-specialized) sort-polymorphic USE —
    /// the dominant measured mathcomp shape — likewise takes the speculative
    /// monomorphic drop with the `SPECULATIVE_MOTIVE` marker.
    #[test]
    fn test_serapi_quality_specialized_instance_value_emits_speculative() {
        let input = r#"(CoqInductive Coq.Init.Datatypes.nat 0 Set
  (Ctor O (Ind Coq.Init.Datatypes.nat 0))
  (Ctor S (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))))
(CoqConstant SerTop.useqpoly
  (Ind Coq.Init.Datatypes.nat 0)
  (App(Const((Constant(KerName(MPfile(DirPath((Id SerTop))))(Id qpolyid))())(Instance(((QConstant QType)(QConstant QProp))(((hash 9)(data SProp))((hash 9)(data SProp)))))))((Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)1)(Instance(()())))))))"#;
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "the quality-specialized value must translate (speculatively): {:?}",
            stats.value_failure_reasons
        );
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let (_, c) = reader.lookup_name("SerTop.useqpoly").unwrap();
        assert!(
            c.has_value(),
            "the speculative mono-drop value must be kept"
        );
        assert_eq!(c.import_confidence, ImportConfidence::Translated as u8);
        assert!(
            c.profile().has(AxiomProfile::SPECULATIVE_MOTIVE),
            "the guessed drop must be marked speculative so verify fails closed"
        );
    }

    /// A SerAPI-native value mentioning SProp drops loudly with the dedicated
    /// COQ_SPROP trust-gate bit (not UNIVERSE_INCON).
    #[test]
    fn test_serapi_sprop_value_dropped_loudly() {
        let input = r#"(CoqConstant SerTop.spropish
  (Sort (Type 1))
  (Lambda((binder_name(Name(Id x)))(binder_relevance Relevant))(Sort SProp)(Rel 1)))"#;
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(input, &mut w).unwrap();
        assert_eq!(stats.value_translation_failed, 1);
        assert!(stats.value_failure_reasons[0]
            .1
            .contains("out-of-model (SProp)"));
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let c = &reader.constants[0];
        assert!(!c.has_value());
        let p = c.profile();
        assert!(p.has(AxiomProfile::COQ_SPROP), "dedicated SProp gate bit");
        assert!(!p.has(AxiomProfile::UNIVERSE_INCON), "no bit collision");
        assert!(p.is_trust_gated());
    }

    /// Task-4 pin: a raw (co)fixpoint value that cannot be structuralized is
    /// NEVER silently lowered (the old code emitted a bare lambda and counted
    /// it `translated`); it is dropped loudly, type-only, and counted.
    #[test]
    fn test_unstructuralizable_fix_and_cofix_values_drop_loudly() {
        for (name, value, needle) in [
            ("weird_fix", "(Fix ((f (Sort Prop) (Rel 0))) 0)", "Fix"),
            (
                "weird_cofix",
                "(CoFix ((g (Sort Prop) (Rel 0))) 0)",
                "CoFix",
            ),
        ] {
            let input = format!("(CoqConstant {name} (Sort (Type 1)) {value})");
            let mut w = ShardWriter::new();
            let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
            assert_eq!(stats.value_translation_failed, 1, "{name} must be counted");
            assert_eq!(stats.translated, 0, "{name} must NOT count as translated");
            assert!(
                stats.value_failure_reasons[0].1.contains(needle),
                "reason must name the construct: {:?}",
                stats.value_failure_reasons
            );
            let mut buf = Vec::new();
            w.write(&mut buf).unwrap();
            let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
            let c = &reader.constants[0];
            assert!(!c.has_value(), "{name}: value must be dropped");
            assert_eq!(c.decl_kind, DeclKind::Axiom as u8);
            assert!(c.profile().has(AxiomProfile::AXIOMATIZED));
        }
    }

    // ---- Coinductive TYPE reconstruction (Streams `Stream`/`EqSt`/`ForAll`) ----

    /// A coinductive TYPE axiom triple (`(CoqAxiom <base>.<N> …)` type former +
    /// self-referential constructor axioms) is reconstructed into ONE
    /// `(CoqInductive …)` form with the parameter count and the constructor
    /// absorbed.
    #[test]
    fn test_reconstruct_coinductive_detects_stream_triple() {
        let input = r#"(CoqAxiom Strm.0 (Prod A Set Set))
(CoqAxiom Strm.0.0 (Prod A Set (Prod h (Rel 0) (Prod t (App (Ind Strm 0) (Rel 1)) (App (Ind Strm 0) (Rel 2))))))
(CoqConstant Strm.other (Sort Prop) (Sort Prop))"#;
        let sexps = parse_sexps(input).expect("parse");
        let (forms, consumed) =
            reconstruct_coinductive_inductives(&sexps, &SerapiNormCtx::default());
        assert_eq!(
            forms.len(),
            1,
            "exactly one coinductive block reconstructed"
        );
        assert!(
            consumed.contains("Strm.0.0"),
            "the constructor axiom is absorbed: {consumed:?}"
        );
        assert!(
            !consumed.contains("Strm.0"),
            "the type former is emitted (not skipped) at its position"
        );
        assert_eq!(
            coinductive_form_former_name(&forms[0]).as_deref(),
            Some("Strm.0"),
            "former name is recoverable so the loop can emit it in place"
        );
        let Sexp::List(items) = &forms[0] else {
            panic!("form must be a list");
        };
        assert!(matches!(&items[0], Sexp::Atom(h) if h == "CoqInductive"));
        assert!(
            matches!(&items[1], Sexp::Atom(h) if h == "Strm"),
            "ind base"
        );
        assert!(matches!(&items[2], Sexp::Atom(h) if h == "0"), "block idx");
        // (NumParams 1): the single leading `A` binder.
        let Sexp::List(np) = &items[4] else {
            panic!("NumParams list");
        };
        assert!(matches!(&np[0], Sexp::Atom(h) if h == "NumParams"));
        assert!(matches!(&np[1], Sexp::Atom(h) if h == "1"));
        assert!(
            matches!(&items[5], Sexp::List(c) if matches!(c.first(), Some(Sexp::Atom(h)) if h == "Ctor")),
            "one Ctor entry"
        );
    }

    /// NEGATIVE CONTROL: a `<base>.<N>` axiom whose constructor concludes in a
    /// DIFFERENT inductive (not self-referential) is NOT reconstructed — the
    /// importer never fabricates an inductive from an unclear shape.
    #[test]
    fn test_reconstruct_coinductive_rejects_non_selfref_ctor() {
        let input = r#"(CoqAxiom Bad.0 (Prod A Set Set))
(CoqAxiom Bad.0.0 (Prod A Set (App (Ind Other 0) (Rel 0))))"#;
        let sexps = parse_sexps(input).expect("parse");
        let (forms, consumed) =
            reconstruct_coinductive_inductives(&sexps, &SerapiNormCtx::default());
        assert!(
            forms.is_empty(),
            "non-self-referential block is not synthesized"
        );
        assert!(consumed.is_empty(), "nothing consumed");
    }

    /// NEGATIVE CONTROL: a plain predicate axiom (Sort codomain but NO
    /// constructor companion) is NOT reconstructed.
    #[test]
    fn test_reconstruct_coinductive_ignores_ctorless_axiom() {
        let input = r#"(CoqAxiom pred.0 (Prod n (Ind nat 0) (Sort Prop)))
(CoqConstant helper (Sort Prop) (Sort Prop))"#;
        let sexps = parse_sexps(input).expect("parse");
        let (forms, _) = reconstruct_coinductive_inductives(&sexps, &SerapiNormCtx::default());
        assert!(
            forms.is_empty(),
            "a lone predicate axiom is not an inductive"
        );
    }

    /// The exact `Coq.Lists.Streams` coinductive TYPE axiom triple as the
    /// dumper emits it (SerAPI kernel forms) — the input the reconstruction
    /// runs on in the live corpus.
    const STREAM_RECON_AXIOMS: &str = r#"(CoqAxiom Coq.Lists.Streams.Stream.0 (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 276717376751823) (data (Level ((DirPath ((Id Streams) (Id Lists) (Id Coq))) 16469698400)))) 0)))) (Sort (Type ((((hash 0) (data (Level ((DirPath ((Id mathverse_template_collapse))) 0)))) 0))))))
(CoqAxiom Coq.Lists.Streams.Stream.0.0 (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 276717376751823) (data (Level ((DirPath ((Id Streams) (Id Lists) (Id Coq))) 16469698400)))) 0)))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 1) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Streams) (Id Lists) (Id Coq)))) (Id Stream)) ()) 0) (Instance (() ())))) ((Rel 2))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Streams) (Id Lists) (Id Coq)))) (Id Stream)) ()) 0) (Instance (() ())))) ((Rel 3)))))))"#;

    /// END-TO-END SEMANTICS: on the EXACT corpus `Stream` triple + the EXACT
    /// corpus `hd` definition (a single-step `Case` observation through the
    /// real SerAPI compact-`Case` path), the reconstructed coinductive TYPE
    /// kernel-verifies as an inductive AND the `hd` destructor kernel-verifies
    /// — the head projection computes through the least-fixpoint recursor the
    /// reconstruction installs, exactly as it must in the live import.
    #[test]
    fn test_coinductive_reconstruction_observer_kernel_verifies() {
        let hd = r#"(CoqConstant Coq.Lists.Streams.hd (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 276717376883021) (data (Level ((DirPath ((Id Streams) (Id Lists) (Id Coq))) 16469698400)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Streams) (Id Lists) (Id Coq)))) (Id Stream)) ()) 0) (Instance (() ())))) ((Rel 1))) (Rel 2))) (Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 276717376883021) (data (Level ((DirPath ((Id Streams) (Id Lists) (Id Coq))) 16469698400)))) 0)))) (Lambda ((binder_name (Name (Id x))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Streams) (Id Lists) (Id Coq)))) (Id Stream)) ()) 0) (Instance (() ())))) ((Rel 1))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Streams) (Id Lists) (Id Coq)))) (Id Stream)) ()) 0)) (ci_npar 1) (ci_cstr_ndecls (2)) (ci_cstr_nargs (2)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 2)) (((((binder_name (Name (Id x))) (binder_relevance Relevant))) (Rel 3)) Relevant) NoInvert (Rel 1) (((((binder_name (Name (Id a))) (binder_relevance Relevant)) ((binder_name (Name (Id s))) (binder_relevance Relevant))) (Rel 2)))))))"#;
        let input = format!("{STREAM_RECON_AXIOMS}\n{hd}");
        let report = verify_sexp(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"Coq.Lists.Streams.Stream.0".to_string()),
            "the reconstructed coinductive TYPE must kernel-verify as an inductive, got {:?}",
            report.kernel_verified_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"Coq.Lists.Streams.hd".to_string()),
            "the `hd` destructor observation must kernel-verify, got {:?}; fallback={:?}",
            report.kernel_verified_names,
            report.axiom_fallback_names
        );
    }

    /// NEGATIVE CONTROL (wrong-but-typechecking is THE failure mode): the EXACT
    /// corpus `hd` with ONE change — its `Case` branch returns the TAIL field
    /// `s` (`Rel 1`, type `Stream A`) instead of the head `a` (`Rel 2`, type
    /// `A`) — is a genuine type error once `Stream` is a real inductive, and
    /// the kernel REJECTS it. This is the guard that the reconstruction did not
    /// merely rubber-stamp: the head/tail confusion is caught, not accepted.
    #[test]
    fn test_coinductive_reconstruction_wrong_observer_rejected() {
        // Same as `hd` but the branch body `(Rel 2)` (head `a`) → `(Rel 1)`
        // (tail `s`), and renamed so it is a fresh constant.
        let hd_wrong = r#"(CoqConstant Coq.Lists.Streams.hd_wrong (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 276717376883021) (data (Level ((DirPath ((Id Streams) (Id Lists) (Id Coq))) 16469698400)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Streams) (Id Lists) (Id Coq)))) (Id Stream)) ()) 0) (Instance (() ())))) ((Rel 1))) (Rel 2))) (Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 276717376883021) (data (Level ((DirPath ((Id Streams) (Id Lists) (Id Coq))) 16469698400)))) 0)))) (Lambda ((binder_name (Name (Id x))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Streams) (Id Lists) (Id Coq)))) (Id Stream)) ()) 0) (Instance (() ())))) ((Rel 1))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Streams) (Id Lists) (Id Coq)))) (Id Stream)) ()) 0)) (ci_npar 1) (ci_cstr_ndecls (2)) (ci_cstr_nargs (2)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 2)) (((((binder_name (Name (Id x))) (binder_relevance Relevant))) (Rel 3)) Relevant) NoInvert (Rel 1) (((((binder_name (Name (Id a))) (binder_relevance Relevant)) ((binder_name (Name (Id s))) (binder_relevance Relevant))) (Rel 1)))))))"#;
        let input = format!("{STREAM_RECON_AXIOMS}\n{hd_wrong}");
        let report = verify_sexp(&input);
        assert!(
            !report
                .kernel_verified_names
                .contains(&"Coq.Lists.Streams.hd_wrong".to_string()),
            "a type-incorrect observation must NOT kernel-verify (kernel is the arbiter); \
             kv={:?}",
            report.kernel_verified_names
        );
    }

    /// Zero-constructor inductives (False/Empty_set) import as complete
    /// families (the num_params stamp engages the checked family replay) and
    /// their eliminator works: `false_elim : forall (P:Prop), False -> P`
    /// via `@False.0.rec.{0}` kernel-verifies.
    #[test]
    fn test_zero_ctor_inductive_imports_and_eliminates() {
        let input = r#"(CoqInductive Coq.Init.Logic.False 0 (Sort Prop))
(CoqConstant SerTop.false_elim
  (Prod P (Sort Prop) (Prod h (Ind Coq.Init.Logic.False 0) (Rel 1)))
  (Lambda P (Sort Prop) (Lambda h (Ind Coq.Init.Logic.False 0)
    (App (StructFix (Ind Coq.Init.Logic.False 0)
           (RecLevel 0)
           (StructTy (Ind Coq.Init.Logic.False 0))
           (Motive (Lambda x (Ind Coq.Init.Logic.False 0) (Rel 3))))
         (Rel 0)))))"#;
        let report = verify_sexp(input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert_eq!(
            report.axiom_fallback, 0,
            "the False elimination must not be axiom-masked: {:?}",
            report.axiom_fallback_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"SerTop.false_elim".to_string()),
            "False elimination must kernel-verify, got {:?}",
            report.kernel_verified_names
        );
    }

    /// Mutual inductive block members are REJECTED loudly, never imported as
    /// independent inductives.
    #[test]
    fn test_mutual_inductive_member_rejected_loudly() {
        let input = "(CoqInductive forest 1 (Sort Set) (Ctor leaf (Ind forest 1)))";
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(input, &mut w).unwrap();
        assert_eq!(stats.skipped, 1);
        assert_eq!(stats.translated, 0);
        assert!(
            stats.skip_reasons[0].1.contains("mutual"),
            "reason must name the mutual rejection: {:?}",
            stats.skip_reasons
        );
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(
            reader.header.constant_count, 0,
            "nothing may be written for a rejected mutual member"
        );
    }

    /// Task-7 pin: value-bearing TRANSLATED definitions carry NO axiom
    /// profile bits at import; axioms keep AXIOMATIZED|BRIDGE_AXIOM plus
    /// name-keyed bits on QUALIFIED names.
    #[test]
    fn test_value_bearing_translated_profile_is_none() {
        let input = "(CoqConstant SerTop.id_prop (Prod x (Sort Prop) (Sort Prop)) \
                     (Lambda x (Sort Prop) (Rel 0)))\
                     (CoqAxiom Coq.Logic.Classical_Prop.classic (Sort Prop))";
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(input, &mut w).unwrap();
        assert_eq!((stats.translated, stats.axiomatized), (1, 1));
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let by_name: std::collections::HashMap<&str, &MathverseConstantHeader> = reader
            .constants
            .iter()
            .map(|c| (reader.strings[c.name_idx as usize].as_str(), c))
            .collect();
        let translated = by_name["SerTop.id_prop"];
        assert!(translated.has_value());
        assert_eq!(
            translated.profile().0,
            AxiomProfile::NONE.0,
            "translated value-bearing constants must NOT be stamped BRIDGE_AXIOM"
        );
        let axiom = by_name["Coq.Logic.Classical_Prop.classic"];
        let p = axiom.profile();
        assert!(p.has(AxiomProfile::AXIOMATIZED));
        assert!(p.has(AxiomProfile::BRIDGE_AXIOM));
        assert!(p.has(AxiomProfile::CHOICE) && p.has(AxiomProfile::CLASSICAL));
    }

    #[test]
    fn test_compute_coq_axiom_profile_qualified_names() {
        let p = compute_coq_axiom_profile(
            "Coq.Logic.FunctionalExtensionality.functional_extensionality_dep",
        );
        assert!(p.has(AxiomProfile::FUNC_EXT) && p.has(AxiomProfile::BRIDGE_AXIOM));
        let p = compute_coq_axiom_profile("Coq.Logic.Classical_Prop.classic");
        assert!(p.has(AxiomProfile::CHOICE) && p.has(AxiomProfile::CLASSICAL));
        let p =
            compute_coq_axiom_profile("Coq.Logic.PropExtensionality.propositional_extensionality");
        assert!(p.has(AxiomProfile::PROP_EXT));
        let p = compute_coq_axiom_profile("UniMath.Foundations.univalenceAxiom");
        assert!(p.has(AxiomProfile::UNIVALENCE));
        let p = compute_coq_axiom_profile("HoTT.Types.Universe.ua");
        assert!(p.has(AxiomProfile::UNIVALENCE));
    }

    /// Prop-elimination negative (sort model): a match on the 2-constructor
    /// Prop inductive `or` with a `Set`-valued motive is LARGE ELIMINATION —
    /// the kernel's or.0.rec motive only accepts Prop, so the proof is
    /// rejected and falls back to an axiom, never KernelVerified.
    #[test]
    fn test_prop_large_elimination_rejected() {
        let input = r#"(CoqInductive nat 0 Set
  (Ctor O (Ind nat 0))
  (Ctor S (Prod n (Ind nat 0) (Ind nat 0))))
(CoqInductive or 0 (Prod A (Sort Prop) (Prod B (Sort Prop) (Sort Prop)))
  (NumParams 2)
  (Ctor or_introl (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod a (Rel 1) (App (Ind or 0) (Rel 2) (Rel 1))))))
  (Ctor or_intror (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod b (Rel 0) (App (Ind or 0) (Rel 2) (Rel 1)))))))
(CoqConstant or_to_nat
  (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod h (App (Ind or 0) (Rel 1) (Rel 0)) (Ind nat 0))))
  (Lambda A (Sort Prop) (Lambda B (Sort Prop) (Lambda h (App (Ind or 0) (Rel 1) (Rel 0))
    (Case (Ind or 0)
      (Params (Rel 2) (Rel 1))
      (Motive (Lambda m (App (Ind or 0) (Rel 2) (Rel 1)) (Ind nat 0)))
      (Discriminant (Rel 0))
      (Branch (Lambda a (Rel 2) (Construct nat 0 0)))
      (Branch (Lambda b (Rel 1) (Construct nat 0 0))))))))"#;
        let report = verify_sexp(input);
        assert!(
            !report
                .kernel_verified_names
                .contains(&"or_to_nat".to_string()),
            "large elimination from Prop `or` must be REJECTED"
        );
        assert_eq!(
            report.axiom_fallback, 1,
            "the rejected large elimination falls back to an axiom: {:?}",
            report.axiom_fallback_names
        );
    }

    /// Negative control pinning the fixed kernel hole (commit dabf7a35): a
    /// proof term whose ill-typedness is buried ONE APPLICATION DEEP inside a
    /// match branch — the branch is `myid (or B A) <arg>` where `<arg>`'s
    /// HEAD type has the right codomain (`or B A`) but its own payload is
    /// ill-typed (a function where a `B` is required). The corpus verifier
    /// must yield axiom_fallback, NOT KernelVerified (see
    /// clean-kernel tc/tests2/soundness_nested_arg.rs for the kernel-side
    /// shape).
    #[test]
    fn test_nested_ill_typed_match_branch_arg_rejected() {
        let input = r#"(CoqInductive or 0 (Prod A (Sort Prop) (Prod B (Sort Prop) (Sort Prop)))
  (NumParams 2)
  (Ctor or_introl (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod a (Rel 1) (App (Ind or 0) (Rel 2) (Rel 1))))))
  (Ctor or_intror (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod b (Rel 0) (App (Ind or 0) (Rel 2) (Rel 1)))))))
(CoqConstant myid
  (Prod P (Sort Prop) (Prod x (Rel 0) (Rel 1)))
  (Lambda P (Sort Prop) (Lambda x (Rel 0) (Rel 0))))
(CoqConstant bad_or_comm
  (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod h (App (Ind or 0) (Rel 1) (Rel 0)) (App (Ind or 0) (Rel 1) (Rel 2)))))
  (Lambda A (Sort Prop) (Lambda B (Sort Prop) (Lambda h (App (Ind or 0) (Rel 1) (Rel 0))
    (Case (Ind or 0)
      (Params (Rel 2) (Rel 1))
      (Motive (Lambda mot (App (Ind or 0) (Rel 2) (Rel 1)) (App (Ind or 0) (Rel 2) (Rel 3))))
      (Discriminant (Rel 0))
      (Branch (Lambda a (Rel 2) (App (Construct or 0 1) (Rel 2) (Rel 3) (Rel 0))))
      (Branch (Lambda b (Rel 1)
        (App (Const myid)
          (App (Ind or 0) (Rel 2) (Rel 3))
          (App (Construct or 0 0) (Rel 2) (Rel 3) (Lambda z (Sort Prop) (Rel 0)))))))))))"#;
        let report = verify_sexp(input);
        assert!(
            report.kernel_verified_names.contains(&"myid".to_string()),
            "the honest helper must verify: {:?}",
            report.kernel_verified_names
        );
        assert!(
            !report
                .kernel_verified_names
                .contains(&"bad_or_comm".to_string()),
            "ill-typedness one application deep inside a match branch must be REJECTED"
        );
        assert!(
            report
                .axiom_fallback_names
                .iter()
                .any(|(name, _)| name == "bad_or_comm"),
            "the rejected proof must be a recorded axiom fallback: {:?}",
            report.axiom_fallback_names
        );
    }

    /// The raw-SerAPI Fix structuralization must produce EXACTLY the dialect
    /// StructFix of the hand-written golden `my_add` (same recursor
    /// application after lowering).
    #[test]
    fn test_raw_serapi_fix_structuralizes_to_golden_struct_fix() {
        let mut ctx = SerapiNormCtx::default();
        // Register `nat` the way import_sexp does (qualified name).
        let arity = parse_sexp("Set").unwrap();
        let ctor_o = parse_sexp("(Ind Coq.Init.Datatypes.nat 0)").unwrap();
        let ctor_s =
            parse_sexp("(Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))")
                .unwrap();
        ctx.register("Coq.Init.Datatypes.nat", 0, 0, &arity, &[ctor_o, ctor_s]);
        let raw_fix = r#"(Fix(((0)0)((((binder_name(Name(Id my_add)))(binder_relevance Relevant)))((Prod((binder_name(Name(Id n)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Prod((binder_name(Name(Id m)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()())))))))((Lambda((binder_name(Name(Id n)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Lambda((binder_name(Name(Id m)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Case((ci_ind((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0))(ci_npar 0)(ci_cstr_ndecls(0 1))(ci_cstr_nargs(0 1))(ci_pp_info((style RegularStyle))))(Instance(()()))()(((((binder_name(Name(Id n)))(binder_relevance Relevant)))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()())))))Relevant)NoInvert(Rel 2)((()(Rel 1))((((binder_name(Name(Id p)))(binder_relevance Relevant)))(App(Construct((((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)2)(Instance(()()))))((App(Rel 4)((Rel 1)(Rel 2)))))))))))))))"#;
        let normalized = normalize_serapi_rec(&parse_sexp(raw_fix).unwrap(), &ctx, &[]);
        let golden = parse_sexp(
            r#"(StructFix (Ind Coq.Init.Datatypes.nat 0)
  (RecLevel 1)
  (Params)
  (Pre)
  (StructTy (Ind Coq.Init.Datatypes.nat 0))
  (Post (Ind Coq.Init.Datatypes.nat 0))
  (Motive (Lambda n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0)))
  (Branch (Rel 0))
  (Branch (Lambda p (Ind Coq.Init.Datatypes.nat 0) (Lambda ih0 (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Rel 0))))))"#,
        )
        .unwrap();
        assert_eq!(
            normalized, golden,
            "raw SerAPI Fix must structuralize to the golden StructFix"
        );
    }

    // =======================================================================
    // Phase B (COQ importer coverage bricks): indexed matches, fielded Prop
    // singletons, universe-instance investigation. Raw fixtures below were
    // captured LIVE from this machine's ~/.opam/mathverse-serapi/bin/sertop
    // (Coq 8.20) or extracted verbatim from mathverse_coq_dump output of the
    // real Coq stdlib (data/corpora/coq-sexp/stdlib).
    // =======================================================================

    /// The dependency closure header shared by the indexed-match fixtures:
    /// `nat` plus the REAL Coq `eq` (TWO parameters `A x`, ONE index `y` —
    /// `Inductive eq (A:Type) (x:A) : A -> Prop`).
    const EQ_NAT_CLOSURE_HEADER: &str = r#"(CoqInductive Coq.Init.Datatypes.nat 0 Set
  (Ctor O (Ind Coq.Init.Datatypes.nat 0))
  (Ctor S (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))))
(CoqInductive Coq.Init.Logic.eq 0 (Prod A (Sort (Type 1)) (Prod x (Rel 0) (Prod y (Rel 1) (Sort Prop))))
  (NumParams 2)
  (Ctor eq_refl (Prod A (Sort (Type 1)) (Prod x (Rel 0) (App (Ind Coq.Init.Logic.eq 0) (Rel 1) (Rel 0) (Rel 0))))))"#;

    /// CRITICAL empirical pin for the indexed `Case` lowering: the kernel
    /// recursor generated by the `add_inductive` replay of the REAL Coq `eq`
    /// (num_params=2) has argument order
    /// `params(A,x) → motive → minor → index(y) → major` with ONE motive
    /// universe level parameter, and the fixed-index promotion
    /// (`fixed_indices_to_params`) does NOT bump `num_params` (the `y` index
    /// is not fixed: `eq_refl`'s arity is below the index position). The
    /// importer-side promotion mirror must agree.
    #[test]
    fn test_kernel_eq_recursor_order_and_no_promotion() {
        use crate::inductive_replay::{
            build_inductive_replay_metadata, reconstruct_constant, NormMode,
        };
        use clean_kernel::Name;

        let mut w = ShardWriter::new();
        CoqImporter
            .import_sexp(EQ_NAT_CLOSURE_HEADER, &mut w)
            .unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let mut env =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        for constant in &reader.constants {
            if constant.decl_kind != DeclKind::Inductive as u8 {
                continue;
            }
            let name = reader.strings[constant.name_idx as usize].as_str();
            let rc = reconstruct_constant(name, &reader, constant).expect("reconstruct");
            let meta = build_inductive_replay_metadata(&reader, constant, &rc, NormMode::Shallow)
                .expect("metadata")
                .expect("inductive metadata present");
            env.add_inductive(meta.decl).expect("add_inductive replay");
        }

        let rec = env
            .get_recursor(&Name::from_string("Coq.Init.Logic.eq.0.rec"))
            .expect("eq recursor generated");
        assert_eq!(rec.num_params, 2, "Coq eq: A and x are PARAMS, unpromoted");
        assert_eq!(rec.num_indices, 1, "Coq eq: y is the single INDEX");
        assert_eq!(rec.num_motives, 1);
        assert_eq!(rec.num_minors, 1);
        assert_eq!(
            rec.arg_order,
            clean_kernel::RecursorArgOrder::MajorAfterMinors,
            "kernel spine must be params → motive → minors → indices → major"
        );
        assert_eq!(
            rec.level_params.len(),
            1,
            "eq large-eliminates: exactly the motive universe parameter"
        );

        // Importer-side promotion mirror agrees: no index is promoted.
        let mut ctx = SerapiNormCtx::default();
        let arity =
            parse_sexp("(Prod A (Sort (Type 1)) (Prod x (Rel 0) (Prod y (Rel 1) (Sort Prop))))")
                .unwrap();
        let ctor = parse_sexp(
            "(Prod A (Sort (Type 1)) (Prod x (Rel 0) (App (Ind Coq.Init.Logic.eq 0) (Rel 1) (Rel 0) (Rel 0))))",
        )
        .unwrap();
        ctx.register("Coq.Init.Logic.eq", 0, 2, &arity, &[ctor]);
        let info = ctx.lookup("Coq.Init.Logic.eq", 0).unwrap();
        assert_eq!(info.num_indices(), Some(1));
        assert_eq!(
            predicted_fixed_index_promotion(info, "Coq.Init.Logic.eq", 0),
            Some(0),
            "promotion mirror: eq's index must NOT be promoted"
        );

        // Contrast: a fixed index IS predicted as promoted (`Inductive foo :
        // nat -> Prop := mk : forall n, foo n` — the kernel promotes n).
        let mut ctx2 = SerapiNormCtx::default();
        let arity2 = parse_sexp("(Prod n (Ind Coq.Init.Datatypes.nat 0) (Sort Prop))").unwrap();
        let ctor2 =
            parse_sexp("(Prod n (Ind Coq.Init.Datatypes.nat 0) (App (Ind SerTop.foo 0) (Rel 0)))")
                .unwrap();
        ctx2.register("SerTop.foo", 0, 0, &arity2, &[ctor2]);
        let info2 = ctx2.lookup("SerTop.foo", 0).unwrap();
        assert_eq!(
            predicted_fixed_index_promotion(info2, "SerTop.foo", 0),
            Some(1),
            "promotion mirror: a fixed index must be predicted as promoted"
        );
    }

    /// RAW end-to-end for the INDEXED match (the eq-rewrite shape): the REAL
    /// `Coq.Init.Logic.eq_sym` proof term extracted VERBATIM from the
    /// mathverse_coq_dump of the Coq 8.20 stdlib (`match H in _ = a return
    /// a = x with eq_refl => eq_refl end`). The importer must recover the
    /// index `y` from the discriminant's binding-site type (lifted to the
    /// Case site) and emit the recursor spine
    /// `@eq.0.rec.{0} A x motive minor y H`, which the kernel typechecks.
    const RAW_SERAPI_EQ_SYM: &str = r#"(CoqConstant Coq.Init.Logic.eq_sym
  (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 739561158051) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 24644632896)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (Prod ((binder_name (Name (Id y))) (binder_relevance Relevant)) (Rel 2) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Rel 3) (Rel 2) (Rel 1))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Rel 4) (Rel 2) (Rel 3)))))))
  (Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 739561158051) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 24644632896)))) 0)))) (Lambda ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (Lambda ((binder_name (Name (Id y))) (binder_relevance Relevant)) (Rel 2) (Lambda ((binder_name (Name (Id H))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Rel 3) (Rel 2) (Rel 1))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0)) (ci_npar 2) (ci_cstr_ndecls (0)) (ci_cstr_nargs (0)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 4) (Rel 3)) (((((binder_name (Name (Id a))) (binder_relevance Relevant)) ((binder_name Anonymous) (binder_relevance Relevant))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Rel 6) (Rel 2) (Rel 5)))) Relevant) NoInvert (Rel 1) ((() (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) 1) (Instance (() ())))) ((Rel 4) (Rel 3)))))))))))"#;

    #[test]
    fn test_raw_serapi_indexed_eq_match_eq_sym_kernel_verifies() {
        let input = format!("{EQ_NAT_CLOSURE_HEADER}\n{RAW_SERAPI_EQ_SYM}");

        // Import stats: the value must NOT be dropped.
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "the indexed eq match must translate: {:?}",
            stats.value_failure_reasons
        );

        // End-to-end kernel verification.
        let report = verify_sexp(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert_eq!(
            report.axiom_fallback, 0,
            "the indexed match proof must not be axiom-masked: {:?}",
            report.axiom_fallback_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"Coq.Init.Logic.eq_sym".to_string()),
            "the REAL stdlib eq_sym (indexed eq match) must kernel-verify, got {:?}",
            report.kernel_verified_names
        );

        // Negative control: make the branch return `@eq_refl A y` instead of
        // `@eq_refl A x`. The minor premise's expected type is
        // `motive x (eq_refl A x) = eq A x x`, and `eq A y y` is not
        // convertible to it, so the kernel REJECTS the proof (axiom
        // fallback) — proving the emitted indexed spine is genuinely
        // typechecked, not shape-matched.
        let bad = input.replace(
            "1) (Instance (() ())))) ((Rel 4) (Rel 3))",
            "1) (Instance (() ())))) ((Rel 4) (Rel 2))",
        );
        assert_ne!(bad, input, "negative control must differ");
        let neg = verify_sexp(&bad);
        assert!(
            !neg.kernel_verified_names
                .contains(&"Coq.Init.Logic.eq_sym".to_string()),
            "an ill-typed indexed-match branch must be REJECTED, not KernelVerified"
        );
        assert!(
            neg.axiom_fallback_names
                .iter()
                .any(|(name, _)| name == "Coq.Init.Logic.eq_sym"),
            "the rejected indexed proof must be a recorded axiom fallback: {:?}",
            neg.axiom_fallback_names
        );
    }

    /// Indexed match whose discriminant sits DEEPER than `Rel 0` (an extra
    /// binder `k` between the hypothesis and the match), captured LIVE from
    /// sertop 8.20 for
    /// `Definition lsym := fun (n m : nat) (H : @eq nat n m) (k : nat) =>
    ///    match H in eq _ a return @eq nat a n with eq_refl => @eq_refl nat n
    ///    end.`
    /// Pins the binding-site → Case-site de Bruijn lift of the recovered
    /// index (`H`'s type `eq nat n m` is recorded under `[n; m]` and must be
    /// lifted by r+1 = 2 so the recovered index is `m`, an OUTER binder).
    const RAW_SERAPI_LSYM: &str = r#"(CoqConstant SerTop.lsym
  (Prod n (Ind Coq.Init.Datatypes.nat 0) (Prod m (Ind Coq.Init.Datatypes.nat 0) (Prod H (App (Ind Coq.Init.Logic.eq 0) (Ind Coq.Init.Datatypes.nat 0) (Rel 1) (Rel 0)) (Prod k (Ind Coq.Init.Datatypes.nat 0) (App (Ind Coq.Init.Logic.eq 0) (Ind Coq.Init.Datatypes.nat 0) (Rel 2) (Rel 3))))))
  (Lambda((binder_name(Name(Id n)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Lambda((binder_name(Name(Id m)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Lambda((binder_name(Name(Id H)))(binder_relevance Relevant))(App(Ind(((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id eq))())0)(Instance(()()))))((Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Rel 2)(Rel 1)))(Lambda((binder_name(Name(Id k)))(binder_relevance Relevant))(Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Case((ci_ind((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id eq))())0))(ci_npar 2)(ci_cstr_ndecls(0))(ci_cstr_nargs(0))(ci_pp_info((style RegularStyle))))(Instance(()()))((Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Rel 4))(((((binder_name(Name(Id a)))(binder_relevance Relevant))((binder_name(Name(Id H)))(binder_relevance Relevant)))(App(Ind(((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id eq))())0)(Instance(()()))))((Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Rel 2)(Rel 6))))Relevant)NoInvert(Rel 2)((()(App(Construct((((MutInd(KerName(MPfile(DirPath((Id Logic)(Id Init)(Id Coq))))(Id eq))())0)1)(Instance(()()))))((Ind(((MutInd(KerName(MPfile(DirPath((Id Datatypes)(Id Init)(Id Coq))))(Id nat))())0)(Instance(()()))))(Rel 4)))))))))))"#;

    #[test]
    fn test_raw_serapi_indexed_match_deep_discriminant_kernel_verifies() {
        let input = format!("{EQ_NAT_CLOSURE_HEADER}\n{RAW_SERAPI_LSYM}");
        let report = verify_sexp(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert_eq!(
            report.axiom_fallback, 0,
            "the deep-discriminant indexed match must not be axiom-masked: {:?}",
            report.axiom_fallback_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"SerTop.lsym".to_string()),
            "lsym (indexed match with discriminant at Rel 1 under an extra binder) \
             must kernel-verify, got {:?}",
            report.kernel_verified_names
        );
    }

    /// The `and` inductive closure (REAL stdlib shape: two Prop params, one
    /// constructor `conj` with two Prop-sorted fields) plus the REAL
    /// `Coq.Init.Logic.proj1` value extracted verbatim from the stdlib dump.
    /// Fielded Prop singletons previously failed closed ("elimination shape
    /// undecidable"); the elim-shape mirror now decides `and` as
    /// level-parameterized (all fields Prop-sorted) and the match
    /// kernel-verifies end-to-end.
    const AND_PROJ1_CLOSURE: &str = r#"(CoqInductive Coq.Init.Logic.and 0 (Prod A (Sort Prop) (Prod B (Sort Prop) (Sort Prop)))
  (NumParams 2)
  (Ctor conj (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod a (Rel 1) (Prod b (Rel 1) (App (Ind Coq.Init.Logic.and 0) (Rel 3) (Rel 2))))))))
(CoqConstant Coq.Init.Logic.proj1
  (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort Prop) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id and)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1))) (Rel 3))))
  (Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort Prop) (Lambda ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort Prop) (Lambda ((binder_name (Name (Id H))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id and)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id and)) ()) 0)) (ci_npar 2) (ci_cstr_ndecls (2)) (ci_cstr_nargs (2)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 3) (Rel 2)) (((((binder_name Anonymous) (binder_relevance Relevant))) (Rel 4)) Relevant) NoInvert (Rel 1) (((((binder_name Anonymous) (binder_relevance Relevant)) ((binder_name Anonymous) (binder_relevance Relevant))) (App (Lambda ((binder_name (Name (Id H))) (binder_relevance Relevant)) (Rel 5) (Lambda ((binder_name (Name (Id H0))) (binder_relevance Relevant)) (Rel 5) (Rel 2))) ((Rel 2) (Rel 1))))))))))"#;

    #[test]
    fn test_raw_serapi_fielded_prop_singleton_and_proj1_kernel_verifies() {
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(AND_PROJ1_CLOSURE, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "the and-match value must translate: {:?}",
            stats.value_failure_reasons
        );

        let report = verify_sexp(AND_PROJ1_CLOSURE);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert_eq!(
            report.axiom_fallback, 0,
            "the and-destructuring proof must not be axiom-masked: {:?}",
            report.axiom_fallback_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"Coq.Init.Logic.proj1".to_string()),
            "the REAL stdlib proj1 (match on the fielded Prop singleton `and`) \
             must kernel-verify, got {:?}",
            report.kernel_verified_names
        );
    }

    /// The REAL stdlib `le` inductive (Prop-sorted, multiple constructors →
    /// Prop-ONLY elimination) plus the REAL `Coq.Init.Peano.le_ind` value,
    /// both verbatim from the corpus dump. The Coq auto-generated induction
    /// scheme's inner `fix F (m : nat) (l : le n m) {struct l}` recurses over
    /// an INDEXED Prop family: the recursor takes NO motive universe
    /// parameter (`(RecLevel Prop)` → empty instance) and the self-call
    /// `F m0 l0` passes the recursive field's OWN index `m0` — an
    /// index-position argument that is dropped in favor of the induction
    /// hypothesis (the kernel IH already sits at the field's indices).
    const LE_IND_CLOSURE: &str = r#"(CoqInductive Coq.Init.Datatypes.nat 0 Set
  (Ctor O (Ind Coq.Init.Datatypes.nat 0))
  (Ctor S (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))))
(CoqInductive Coq.Init.Peano.le 0 (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Sort Prop))) (NumParams 1) (Ctor Coq.Init.Peano.le_n (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Peano) (Id Init) (Id Coq)))) (Id le)) ()) 0) (Instance (() ())))) ((Rel 1) (Rel 1))))) (Ctor Coq.Init.Peano.le_S (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id m))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Peano) (Id Init) (Id Coq)))) (Id le)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Peano) (Id Init) (Id Coq)))) (Id le)) ()) 0) (Instance (() ())))) ((Rel 3) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 2) (Instance (() ())))) ((Rel 2))))))))))
(CoqConstant Coq.Init.Peano.le_ind (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id P))) (binder_relevance Relevant)) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Sort Prop)) (Prod ((binder_name (Name (Id f))) (binder_relevance Relevant)) (App (Rel 1) ((Rel 2))) (Prod ((binder_name (Name (Id f0))) (binder_relevance Relevant)) (Prod ((binder_name (Name (Id m))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Peano) (Id Init) (Id Coq)))) (Id le)) ()) 0) (Instance (() ())))) ((Rel 4) (Rel 1))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (App (Rel 4) ((Rel 2))) (App (Rel 5) ((App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 2) (Instance (() ())))) ((Rel 3)))))))) (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id l))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Peano) (Id Init) (Id Coq)))) (Id le)) ()) 0) (Instance (() ())))) ((Rel 5) (Rel 1))) (App (Rel 5) ((Rel 2))))))))) (Lambda ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Lambda ((binder_name (Name (Id P))) (binder_relevance Relevant)) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Sort Prop)) (Lambda ((binder_name (Name (Id f))) (binder_relevance Relevant)) (App (Rel 1) ((Rel 2))) (Lambda ((binder_name (Name (Id f0))) (binder_relevance Relevant)) (Prod ((binder_name (Name (Id m))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Peano) (Id Init) (Id Coq)))) (Id le)) ()) 0) (Instance (() ())))) ((Rel 4) (Rel 1))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (App (Rel 4) ((Rel 2))) (App (Rel 5) ((App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 2) (Instance (() ())))) ((Rel 3)))))))) (Fix (((1) 0) ((((binder_name (Name (Id F))) (binder_relevance Relevant))) ((Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id l))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Peano) (Id Init) (Id Coq)))) (Id le)) ()) 0) (Instance (() ())))) ((Rel 5) (Rel 1))) (App (Rel 5) ((Rel 2)))))) ((Lambda ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Lambda ((binder_name (Name (Id l))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Peano) (Id Init) (Id Coq)))) (Id le)) ()) 0) (Instance (() ())))) ((Rel 6) (Rel 1))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Peano) (Id Init) (Id Coq)))) (Id le)) ()) 0)) (ci_npar 1) (ci_cstr_ndecls (0 2)) (ci_cstr_nargs (0 2)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 7)) (((((binder_name (Name (Id n))) (binder_relevance Relevant)) ((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 8) ((Rel 2)))) Relevant) NoInvert (Rel 1) ((() (Rel 5)) ((((binder_name (Name (Id m))) (binder_relevance Relevant)) ((binder_name (Name (Id l))) (binder_relevance Relevant))) (App (Rel 6) ((Rel 2) (Rel 1) (App (Rel 5) ((Rel 2) (Rel 1)))))))))))))))))))"#;

    #[test]
    fn test_raw_serapi_prop_only_indexed_fix_le_ind_kernel_verifies() {
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(LE_IND_CLOSURE, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "the le_ind indexed Prop-only fix must translate: {:?}",
            stats.value_failure_reasons
        );

        let report = verify_sexp(LE_IND_CLOSURE);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"Coq.Init.Peano.le_ind".to_string()),
            "the REAL stdlib le_ind (structural recursion over the indexed \
             Prop-only family `le`) must kernel-verify, got {:?} / fallbacks {:?}",
            report.kernel_verified_names,
            report.axiom_fallback_names
        );
    }

    /// Elim-shape mirror ↔ kernel parity: for each registered inductive the
    /// mirror's prediction must match the number of universe level
    /// parameters on the recursor the kernel's `add_inductive` replay
    /// actually generates (`LevelParam` ⇔ 1 motive level param, `PropOnly`
    /// ⇔ 0). Covers: `False` (empty), `eq` (zero-field singleton), `and`
    /// (fielded singleton, all fields Prop-sorted), `ex` (fielded singleton
    /// with a Type-sorted witness field → Prop-only: witness extraction must
    /// NOT be enabled), `or` (multi-ctor), and a Nonempty-like singleton
    /// with a non-index Set field (`PropOnly`).
    #[test]
    fn test_prop_singleton_elim_shape_mirror_matches_kernel() {
        use crate::inductive_replay::{
            build_inductive_replay_metadata, reconstruct_constant, NormMode,
        };
        use clean_kernel::Name;

        let closure = r#"(CoqInductive Coq.Init.Datatypes.nat 0 Set
  (Ctor O (Ind Coq.Init.Datatypes.nat 0))
  (Ctor S (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))))
(CoqInductive Coq.Init.Logic.False 0 (Sort Prop))
(CoqInductive Coq.Init.Logic.eq 0 (Prod A (Sort (Type 1)) (Prod x (Rel 0) (Prod y (Rel 1) (Sort Prop))))
  (NumParams 2)
  (Ctor eq_refl (Prod A (Sort (Type 1)) (Prod x (Rel 0) (App (Ind Coq.Init.Logic.eq 0) (Rel 1) (Rel 0) (Rel 0))))))
(CoqInductive Coq.Init.Logic.and 0 (Prod A (Sort Prop) (Prod B (Sort Prop) (Sort Prop)))
  (NumParams 2)
  (Ctor conj (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod a (Rel 1) (Prod b (Rel 1) (App (Ind Coq.Init.Logic.and 0) (Rel 3) (Rel 2))))))))
(CoqInductive Coq.Init.Logic.ex 0 (Prod A (Sort (Type 1)) (Prod P (Prod x (Rel 0) (Sort Prop)) (Sort Prop)))
  (NumParams 2)
  (Ctor ex_intro (Prod A (Sort (Type 1)) (Prod P (Prod x (Rel 0) (Sort Prop)) (Prod x (Rel 1) (Prod p (App (Rel 1) (Rel 0)) (App (Ind Coq.Init.Logic.ex 0) (Rel 3) (Rel 2))))))))
(CoqInductive Coq.Init.Logic.or 0 (Prod A (Sort Prop) (Prod B (Sort Prop) (Sort Prop)))
  (NumParams 2)
  (Ctor or_introl (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod a (Rel 1) (App (Ind Coq.Init.Logic.or 0) (Rel 2) (Rel 1))))))
  (Ctor or_intror (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod b (Rel 0) (App (Ind Coq.Init.Logic.or 0) (Rel 2) (Rel 1)))))))
(CoqInductive SerTop.wrapped_nat 0 (Sort Prop)
  (Ctor wrap (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind SerTop.wrapped_nat 0))))"#;

        // Import once and replay every family through the kernel.
        let mut w = ShardWriter::new();
        CoqImporter.import_sexp(closure, &mut w).unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let mut env =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        for constant in &reader.constants {
            if constant.decl_kind != DeclKind::Inductive as u8 {
                continue;
            }
            let name = reader.strings[constant.name_idx as usize].as_str();
            let rc = reconstruct_constant(name, &reader, constant).expect("reconstruct");
            let meta = build_inductive_replay_metadata(&reader, constant, &rc, NormMode::Shallow)
                .expect("metadata")
                .expect("inductive metadata present");
            env.add_inductive(meta.decl).expect("add_inductive replay");
        }

        // Rebuild the registry mirror exactly as import_sexp populated it.
        let mut ctx = SerapiNormCtx::default();
        for form in parse_sexps(closure).unwrap() {
            let Sexp::List(items) = &form else {
                panic!("top-level form must be a list")
            };
            if !matches!(&items[0], Sexp::Atom(h) if h == "CoqInductive") {
                continue;
            }
            let Sexp::Atom(name) = &items[1] else {
                panic!("inductive name must be an atom")
            };
            let (np, ctors) = parse_inductive_num_params(&items[4..]).unwrap();
            let ctor_tys: Vec<Sexp> = ctors
                .iter()
                .map(|c| match c {
                    Sexp::List(cv) => cv[2].clone(),
                    _ => panic!("malformed ctor"),
                })
                .collect();
            ctx.register(name, 0, np, &items[3], &ctor_tys);
        }

        let expectations = [
            ("Coq.Init.Datatypes.nat", Some(ElimShape::LevelParam)),
            ("Coq.Init.Logic.False", Some(ElimShape::LevelParam)),
            ("Coq.Init.Logic.eq", Some(ElimShape::LevelParam)),
            ("Coq.Init.Logic.and", Some(ElimShape::LevelParam)),
            ("Coq.Init.Logic.ex", Some(ElimShape::PropOnly)),
            ("Coq.Init.Logic.or", Some(ElimShape::PropOnly)),
            ("SerTop.wrapped_nat", Some(ElimShape::PropOnly)),
        ];
        for (name, expected) in expectations {
            let info = ctx
                .lookup(name, 0)
                .unwrap_or_else(|| panic!("{name} registered"));
            let mirror = info.elim_shape(&ctx);
            assert_eq!(mirror, expected, "mirror prediction for {name}");
            let rec = env
                .get_recursor(&Name::from_string(&format!("{name}.0.rec")))
                .unwrap_or_else(|| panic!("{name} recursor generated"));
            let kernel_shape = if rec.level_params.is_empty() {
                ElimShape::PropOnly
            } else {
                ElimShape::LevelParam
            };
            assert_eq!(
                mirror,
                Some(kernel_shape),
                "mirror/kernel elimination-shape parity for {name} \
                 (kernel level_params = {:?})",
                rec.level_params
            );
        }
    }

    /// Elim-shape mirror ↔ kernel parity on the CUMULATIVE (Coq) lane for the
    /// Berardi `retract` Prop-record class — the measured ELIM-SHAPE MIRROR
    /// divergence (taxonomy: 14 baseline-KV stdlib decls regressing with
    /// `Level count mismatch retract.0.rec: declared 0 level params, got 1`
    /// once the inductive-builder cumulativity companion let the family
    /// replay for real).
    ///
    /// `Record retract (A B : Prop) : Prop := { i : A→B; j : B→A;
    /// inv : ∀ a, j (i a) = a }` is a single-constructor Prop record whose
    /// three fields are all Prop-sorted, but whose `inv` field applies the
    /// collapsed-universe `eq` at a `Prop` argument — well-typed ONLY under
    /// cumulative subtyping. Both sides must agree on LARGE elimination:
    /// the mirror by the And-shaped subsingleton rule, the kernel by running
    /// `elim_only_at_universe_zero`'s field-sort inference under the env's
    /// declared (cumulative) checking mode instead of erring into the
    /// conservative Prop-only arm.
    #[test]
    fn test_retract_prop_record_elim_shape_mirror_matches_kernel_cumulative() {
        use crate::inductive_replay::{
            build_inductive_replay_metadata, reconstruct_constant, NormMode,
        };
        use clean_kernel::Name;

        let closure = r#"(CoqInductive Coq.Init.Logic.eq 0 (Prod A (Sort (Type 1)) (Prod x (Rel 0) (Prod y (Rel 1) (Sort Prop))))
  (NumParams 2)
  (Ctor eq_refl (Prod A (Sort (Type 1)) (Prod x (Rel 0) (App (Ind Coq.Init.Logic.eq 0) (Rel 1) (Rel 0) (Rel 0))))))
(CoqInductive Coq.Logic.Berardi.retract 0 (Prod A (Sort Prop) (Prod B (Sort Prop) (Sort Prop)))
  (NumParams 2)
  (Ctor Build_retract (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod i (Prod x (Rel 1) (Rel 1)) (Prod j (Prod x (Rel 1) (Rel 3)) (Prod inv (Prod a (Rel 3) (App (Ind Coq.Init.Logic.eq 0) (Rel 4) (App (Rel 1) (App (Rel 2) (Rel 0))) (Rel 0))) (App (Ind Coq.Logic.Berardi.retract 0) (Rel 4) (Rel 3)))))))))"#;

        // Import and replay both families through the kernel on a CUMULATIVE
        // env — the exact configuration the Coq corpus verifier uses
        // (`coq_import_command` sets `set_cumulative(true)`).
        let mut w = ShardWriter::new();
        CoqImporter.import_sexp(closure, &mut w).unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let mut env =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        env.set_cumulative(true);
        for constant in &reader.constants {
            if constant.decl_kind != DeclKind::Inductive as u8 {
                continue;
            }
            let name = reader.strings[constant.name_idx as usize].as_str();
            let rc = reconstruct_constant(name, &reader, constant).expect("reconstruct");
            let meta = build_inductive_replay_metadata(&reader, constant, &rc, NormMode::Shallow)
                .expect("metadata")
                .expect("inductive metadata present");
            env.add_inductive(meta.decl)
                .unwrap_or_else(|e| panic!("checked add_inductive replay must accept {name}: {e}"));
        }

        // Rebuild the registry mirror exactly as import_sexp populated it.
        let mut ctx = SerapiNormCtx::default();
        for form in parse_sexps(closure).unwrap() {
            let Sexp::List(items) = &form else {
                panic!("top-level form must be a list")
            };
            let Sexp::Atom(name) = &items[1] else {
                panic!("inductive name must be an atom")
            };
            let (np, ctors) = parse_inductive_num_params(&items[4..]).unwrap();
            let ctor_tys: Vec<Sexp> = ctors
                .iter()
                .map(|c| match c {
                    Sexp::List(cv) => cv[2].clone(),
                    _ => panic!("malformed ctor"),
                })
                .collect();
            ctx.register(name, 0, np, &items[3], &ctor_tys);
        }

        let info = ctx
            .lookup("Coq.Logic.Berardi.retract", 0)
            .expect("retract registered");
        let mirror = info.elim_shape(&ctx);
        assert_eq!(
            mirror,
            Some(ElimShape::LevelParam),
            "retract (single ctor, all fields Prop-sorted) must mirror as \
             large-eliminating"
        );
        let rec = env
            .get_recursor(&Name::from_string("Coq.Logic.Berardi.retract.0.rec"))
            .expect("retract recursor generated");
        assert_eq!(
            rec.level_params.len(),
            1,
            "kernel recursor must carry exactly the motive level param the \
             mirror predicts (got {:?})",
            rec.level_params
        );
    }

    /// Universe-instance investigation pins (Task 3): sertop 8.20 serializes
    /// the runtime `Set` LEVEL as the atom `SProp` (pierced `RawLevel`
    /// encoding, see the module doc — unambiguous: the runtime level type
    /// has no SProp/Prop constructors).
    #[test]
    fn test_serapi_instance_classification_and_pierced_set_level() {
        // Monomorphic instance.
        let mono = parse_sexp(
            r#"((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id c)) ()) (Instance (() ())))"#,
        )
        .unwrap();
        assert_eq!(
            serapi_ref_instance_class(&mono),
            SerapiInstanceClass::Monomorphic
        );
        assert!(serapi_ref_instance_reject_reason(&mono, "constant").is_none());

        // Single Set-level instance (captured live: `pid nat` for
        // `Polymorphic Definition pid (A : Type) := A.`).
        let set = parse_sexp(
            r#"((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id pid)) ()) (Instance (() (((hash 9) (data SProp))))))"#,
        )
        .unwrap();
        assert_eq!(
            serapi_ref_instance_class(&set),
            SerapiInstanceClass::SingleSetLevel
        );
        let reason = serapi_ref_instance_reject_reason(&set, "constant").unwrap();
        assert!(
            reason.contains("out-of-model (universe)") && reason.contains("Set-instantiated"),
            "the Set-instance drop must stay loud with a precise reason: {reason}"
        );

        // Named-level instance (captured live: `pid Prop`): a MONOMORPHIC
        // instantiation at a fixed global universe. Now IN model — the instance
        // is stripped and the reference imports monomorphically, matching the
        // monomorphic import of the referenced constant (the kernel re-checks).
        let named = parse_sexp(
            r#"((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id pid)) ()) (Instance (() (((hash 14398528654109) (data (Level ((DirPath ((Id SerTop))) 2163105280))))))))"#,
        )
        .unwrap();
        assert_eq!(
            serapi_ref_instance_class(&named),
            SerapiInstanceClass::Monomorphic
        );
        assert!(serapi_ref_instance_reject_reason(&named, "constant").is_none());

        // Sort position: `Type@{Set}` (single pierced-Set pair, increment 0)
        // is IN MODEL and collapses to `(Type 1)` = kernel `Sort 1`, exactly
        // like `Set`.
        let ty_at_set = normalize_serapi(
            &parse_sexp(r#"(Sort(Type((((hash 9)(data SProp))0))))"#).unwrap(),
            &SerapiNormCtx::default(),
            &[],
        )
        .unwrap();
        assert!(
            matches!(
                sexp_to_cic(&ty_at_set).unwrap(),
                CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Type(1)))
            ),
            "Type@{{Set}} must collapse to the Set level (Sort 1), got {ty_at_set:?}"
        );
    }

    /// A single pierced-`Set` instance takes the speculative monomorphic drop
    /// at the `Const`/`Ind`/`Construct` emit sites (same guess as the mixed
    /// `MonoDropSpeculative` shape) while the `Case`-node path stays strictly
    /// fail-closed.
    #[test]
    fn test_single_set_level_instance_emits_speculative_case_stays_closed() {
        let set = parse_sexp(
            r#"((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id pid)) ()) (Instance (() (((hash 9) (data SProp))))))"#,
        )
        .unwrap();
        assert_eq!(
            serapi_ref_instance_class(&set),
            SerapiInstanceClass::SingleSetLevel
        );
        assert!(
            matches!(
                serapi_ref_instance_disposition(&set, "constant"),
                InstanceDisposition::EmitSpeculative
            ),
            "single-Set-level reference must take the speculative mono drop"
        );
        assert!(
            serapi_ref_instance_reject_reason(&set, "Case").is_some(),
            "the Case-node path must stay fail-closed for a Set-level instance"
        );
    }

    /// Constant-quality (fully quality-specialized) sort-polymorphic instances
    /// — the dominant measured mathcomp fail-closed shape (2026-07-10) — take
    /// the speculative monomorphic drop; quality VARIABLES stay out of model.
    #[test]
    fn test_quality_specialized_instance_classification() {
        // The dominant measured shape: two constant qualities + two pierced-Set
        // levels (captured live from the mathcomp dump).
        let qconst_set = parse_sexp(
            r#"((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id c)) ()) (Instance (((QConstant QType) (QConstant QProp)) (((hash 9) (data SProp)) ((hash 9) (data SProp))))))"#,
        )
        .unwrap();
        assert_eq!(
            serapi_ref_instance_class(&qconst_set),
            SerapiInstanceClass::MonoDropSpeculative
        );
        assert!(matches!(
            serapi_ref_instance_disposition(&qconst_set, "constant"),
            InstanceDisposition::EmitSpeculative
        ));
        assert!(
            serapi_ref_instance_reject_reason(&qconst_set, "Case").is_some(),
            "the Case-node path must stay fail-closed for quality-specialized instances"
        );

        // Constant qualities over all-NAMED levels: still capped at the
        // speculative drop (the quality specialization itself is the guess),
        // never plain Monomorphic.
        let qconst_named = parse_sexp(
            r#"((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id c)) ()) (Instance (((QConstant QProp)) (((hash 14398528654109) (data (Level ((DirPath ((Id SerTop))) 2163105280))))))))"#,
        )
        .unwrap();
        assert_eq!(
            serapi_ref_instance_class(&qconst_named),
            SerapiInstanceClass::MonoDropSpeculative
        );

        // Constant qualities with EMPTY levels: quality-only specialization,
        // still a speculative drop.
        let qconst_only = parse_sexp(
            r#"((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id c)) ()) (Instance (((QConstant QSProp)) ())))"#,
        )
        .unwrap();
        assert_eq!(
            serapi_ref_instance_class(&qconst_only),
            SerapiInstanceClass::MonoDropSpeculative
        );

        // A quality VARIABLE is genuine sort polymorphism: out of model.
        let qvar = parse_sexp(
            r#"((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id c)) ()) (Instance (((QVar 0)) (((hash 9) (data SProp))))))"#,
        )
        .unwrap();
        assert_eq!(
            serapi_ref_instance_class(&qvar),
            SerapiInstanceClass::OutOfModel
        );
        assert!(matches!(
            serapi_ref_instance_disposition(&qvar, "constant"),
            InstanceDisposition::Reject(_)
        ));

        // Constant qualities over an OUT-OF-MODEL level payload stay out of
        // model — the quality lever never rescues unrecognized levels.
        let qconst_bad_levels = parse_sexp(
            r#"((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id c)) ()) (Instance (((QConstant QType)) (((hash 9) (data (Mystery 3)))))))"#,
        )
        .unwrap();
        assert_eq!(
            serapi_ref_instance_class(&qconst_bad_levels),
            SerapiInstanceClass::OutOfModel
        );
    }

    /// The fielded-Prop-singleton mirror keeps `ex` PROP-ONLY: a witness
    /// extraction (`Set`-valued motive over an `ex` match) is emitted as a
    /// Prop-only `Case` and REJECTED by the kernel's `ex.0.rec`, never
    /// silently accepted.
    #[test]
    fn test_ex_witness_extraction_stays_rejected() {
        let input = r#"(CoqInductive Coq.Init.Datatypes.nat 0 Set
  (Ctor O (Ind Coq.Init.Datatypes.nat 0))
  (Ctor S (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))))
(CoqInductive Coq.Init.Logic.ex 0 (Prod A (Sort (Type 1)) (Prod P (Prod x (Rel 0) (Sort Prop)) (Sort Prop)))
  (NumParams 2)
  (Ctor ex_intro (Prod A (Sort (Type 1)) (Prod P (Prod x (Rel 0) (Sort Prop)) (Prod x (Rel 1) (Prod p (App (Rel 1) (Rel 0)) (App (Ind Coq.Init.Logic.ex 0) (Rel 3) (Rel 2))))))))
(CoqConstant SerTop.extract_witness
  (Prod P (Prod x (Ind Coq.Init.Datatypes.nat 0) (Sort Prop)) (Prod h (App (Ind Coq.Init.Logic.ex 0) (Ind Coq.Init.Datatypes.nat 0) (Rel 0)) (Ind Coq.Init.Datatypes.nat 0)))
  (Lambda P (Prod x (Ind Coq.Init.Datatypes.nat 0) (Sort Prop)) (Lambda h (App (Ind Coq.Init.Logic.ex 0) (Ind Coq.Init.Datatypes.nat 0) (Rel 0))
    (Case (Ind Coq.Init.Logic.ex 0)
      (Params (Ind Coq.Init.Datatypes.nat 0) (Rel 1))
      (Motive (Lambda m (App (Ind Coq.Init.Logic.ex 0) (Ind Coq.Init.Datatypes.nat 0) (Rel 2)) (Ind Coq.Init.Datatypes.nat 0)))
      (Discriminant (Rel 0))
      (Branch (Lambda x (Ind Coq.Init.Datatypes.nat 0) (Lambda p (App (Rel 2) (Rel 0)) (Rel 1))))))))"#;
        let report = verify_sexp(input);
        assert!(
            !report
                .kernel_verified_names
                .contains(&"SerTop.extract_witness".to_string()),
            "witness extraction from `ex` must be REJECTED by the kernel"
        );
        assert!(
            report
                .axiom_fallback_names
                .iter()
                .any(|(name, _)| name == "SerTop.extract_witness"),
            "the rejected witness extraction is a recorded axiom fallback: {:?}",
            report.axiom_fallback_names
        );
    }

    // =======================================================================
    // Template-polymorphic inductives (D1): real dump payloads from
    // data/corpora/coq-sexp/stdlib/Coq.Init.{Datatypes,Logic}.sexp, extracted
    // VERBATIM (mathverse_coq_dump, Coq 8.20 stdlib).
    // =======================================================================

    /// REAL `Coq.Init.Logic.eq` dump form (dependency of
    /// `surjective_pairing`).
    const RAW_DUMP_LOGIC_EQ: &str = r#"(CoqInductive Coq.Init.Logic.eq 0 (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 739561026853) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 24644632896)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 2) (Sort Prop)))) (NumParams 2) (Ctor Coq.Init.Logic.eq_refl (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 739561026853) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 24644632896)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1) (Rel 1)))))))"#;

    /// REAL `Coq.Init.Datatypes.prod` dump form: the TEMPLATE-POLYMORPHIC
    /// arity ends in `Type@{max(l_A, l_B)}` (TWO `(level 0)` pairs in the
    /// `Sort (Type …)` payload).
    const RAW_DUMP_PROD: &str = r#"(CoqInductive Coq.Init.Datatypes.prod 0 (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854232953) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Prod ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854298552) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Sort (Type ((((hash 81821757854232953) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0) (((hash 81821757854298552) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))))) (NumParams 2) (Ctor Coq.Init.Datatypes.pair (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854232953) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Prod ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854298552) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 2) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 2) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) (Instance (() ())))) ((Rel 4) (Rel 3)))))))))"#;

    /// REAL `Coq.Init.Datatypes.fst` dump form (Case on `prod`).
    const RAW_DUMP_FST: &str = r#"(CoqConstant Coq.Init.Datatypes.fst (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854495349) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Prod ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854560948) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Prod ((binder_name (Name (Id p))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1))) (Rel 3)))) (Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854495349) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Lambda ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854560948) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Lambda ((binder_name (Name (Id p))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0)) (ci_npar 2) (ci_cstr_ndecls (2)) (ci_cstr_nargs (2)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 3) (Rel 2)) (((((binder_name (Name (Id p))) (binder_relevance Relevant))) (Rel 4)) Relevant) NoInvert (Rel 1) (((((binder_name (Name (Id x))) (binder_relevance Relevant)) ((binder_name (Name (Id y))) (binder_relevance Relevant))) (Rel 2))))))))"#;

    /// REAL `Coq.Init.Datatypes.snd` dump form (Case on `prod`).
    const RAW_DUMP_SND: &str = r#"(CoqConstant Coq.Init.Datatypes.snd (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854495349) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Prod ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854560948) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Prod ((binder_name (Name (Id p))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1))) (Rel 2)))) (Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854495349) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Lambda ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854560948) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Lambda ((binder_name (Name (Id p))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0)) (ci_npar 2) (ci_cstr_ndecls (2)) (ci_cstr_nargs (2)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 3) (Rel 2)) (((((binder_name (Name (Id p))) (binder_relevance Relevant))) (Rel 3)) Relevant) NoInvert (Rel 1) (((((binder_name (Name (Id x))) (binder_relevance Relevant)) ((binder_name (Name (Id y))) (binder_relevance Relevant))) (Rel 1))))))))"#;

    /// REAL `Coq.Init.Datatypes.surjective_pairing` dump form — the
    /// pair-projection THEOREM (`p = (fst p, snd p)`), whose branch body is
    /// itself a beta redex applied to the constructor fields.
    const RAW_DUMP_SURJECTIVE_PAIRING: &str = r#"(CoqConstant Coq.Init.Datatypes.surjective_pairing (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854888943) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Prod ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854954542) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 25063532692)))) 0)))) (Prod ((binder_name (Name (Id p))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) (Instance (() ())))) ((Rel 3) (Rel 2))) (Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) 1) (Instance (() ())))) ((Rel 3) (Rel 2) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id fst)) ()) (Instance (() ())))) ((Rel 3) (Rel 2) (Rel 1))) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id snd)) ()) (Instance (() ())))) ((Rel 3) (Rel 2) (Rel 1)))))))))) (Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854888943) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 9955912232)))) 0)))) (Lambda ((binder_name (Name (Id B))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757854954542) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 9955912232)))) 0)))) (Lambda ((binder_name (Name (Id p))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0)) (ci_npar 2) (ci_cstr_ndecls (2)) (ci_cstr_nargs (2)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 3) (Rel 2)) (((((binder_name (Name (Id p))) (binder_relevance Relevant))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) (Instance (() ())))) ((Rel 4) (Rel 3))) (Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) 1) (Instance (() ())))) ((Rel 4) (Rel 3) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id fst)) ()) (Instance (() ())))) ((Rel 4) (Rel 3) (Rel 1))) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id snd)) ()) (Instance (() ())))) ((Rel 4) (Rel 3) (Rel 1)))))))) Relevant) NoInvert (Rel 1) (((((binder_name (Name (Id a))) (binder_relevance Relevant)) ((binder_name (Name (Id b))) (binder_relevance Relevant))) (App (Lambda ((binder_name (Name (Id a))) (binder_relevance Relevant)) (Rel 5) (Lambda ((binder_name (Name (Id b))) (binder_relevance Relevant)) (Rel 5) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) 1) (Instance (() ())))) ((App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) (Instance (() ())))) ((Rel 7) (Rel 6))) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) 1) (Instance (() ())))) ((Rel 7) (Rel 6) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id fst)) ()) (Instance (() ())))) ((Rel 7) (Rel 6) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) 1) (Instance (() ())))) ((Rel 7) (Rel 6) (Rel 2) (Rel 1))))) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id snd)) ()) (Instance (() ())))) ((Rel 7) (Rel 6) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) 1) (Instance (() ())))) ((Rel 7) (Rel 6) (Rel 2) (Rel 1))))))))))) ((Rel 2) (Rel 1))))))))))"#;

    /// D1 (template polymorphism): the REAL template-polymorphic `prod`
    /// (arity codomain `Type@{max(l_A, l_B)}`) imports UNIVERSE-POLYMORPHICALLY
    /// (`prod.{u,v} : Sort u → Sort v → Sort (max u v)`, the eqmx unlock) and
    /// registers in the import session; on the CUMULATIVE (Coq re-verification)
    /// lane the checked replay generates the large-eliminating recursor
    /// `prod.0.rec.{motive,u,v}`, so the REAL `fst`/`snd` Cases on it (each a
    /// `Type`-motive projection) plus the REAL pair-projection theorem
    /// `surjective_pairing` kernel-verify end-to-end at the `{1,1}` instance —
    /// byte-identical in type to the former monomorphic rendering.
    #[test]
    fn test_real_dump_template_prod_fst_snd_pairing_kernel_verify() {
        let input = format!(
            "{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_PROD}\n{RAW_DUMP_FST}\n{RAW_DUMP_SND}\n{RAW_DUMP_SURJECTIVE_PAIRING}"
        );

        // Import: prod must not be skipped and no value may drop.
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.skipped, 0,
            "template-polymorphic prod must import: {:?}",
            stats.skip_reasons
        );
        assert_eq!(
            stats.value_translation_failed, 0,
            "fst/snd/surjective_pairing values must translate: {:?}",
            stats.value_failure_reasons
        );

        // End-to-end kernel verification on the CUMULATIVE Coq lane (where the
        // poly prod recursor large-eliminates, exactly like the corpus gate).
        let report = verify_sexp_cumulative(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in [
            "Coq.Init.Datatypes.fst",
            "Coq.Init.Datatypes.snd",
            "Coq.Init.Datatypes.surjective_pairing",
        ] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified, got {:?} (fallbacks: {:?})",
                report.kernel_verified_names,
                report.axiom_fallback_names
            );
        }

        // Negative control: swap the pair components in surjective_pairing's
        // branch (`(pair (snd ..) (fst ..))` shape is ill-typed against the
        // motive) — the kernel must REJECT it, proving the template-collapsed
        // recursor spine is genuinely typechecked.
        let bad = input.replace(
            "(Id eq)) ()) 0) 1) (Instance (() ())))) ((App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) (Instance (() ())))) ((Rel 7) (Rel 6))) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) 1) (Instance (() ())))) ((Rel 7) (Rel 6) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id fst))",
            "(Id eq)) ()) 0) 1) (Instance (() ())))) ((App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) (Instance (() ())))) ((Rel 7) (Rel 6))) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id prod)) ()) 0) 1) (Instance (() ())))) ((Rel 7) (Rel 6) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id snd))",
        );
        assert_ne!(bad, input, "negative control must differ");
        let neg = verify_sexp_cumulative(&bad);
        assert!(
            !neg.kernel_verified_names
                .contains(&"Coq.Init.Datatypes.surjective_pairing".to_string()),
            "an ill-typed pair-projection proof must be REJECTED, not KernelVerified"
        );
    }

    /// D1 unit pin: the template `Type@{max(l1,l2)}` payload (all named
    /// global levels, increments 0) collapses to `(Type 1)`; a max carrying
    /// a `+1` increment or a bound `Var` level stays OUT OF MODEL.
    #[test]
    fn test_template_universe_max_collapse_and_fail_closed() {
        let ctx = SerapiNormCtx::default();
        let max2 = normalize_serapi(
            &parse_sexp(
                r#"(Sort(Type((((hash 1)(data(Level((DirPath((Id SerTop)))1))))0)(((hash 2)(data(Level((DirPath((Id SerTop)))2))))0))))"#,
            )
            .unwrap(),
            &ctx,
            &[],
        )
        .unwrap();
        assert!(matches!(
            sexp_to_cic(&max2).unwrap(),
            CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Type(1)))
        ));
        // max(l1, l2+1): `named + 1 = Type 2`, and `max(Type 1, Type 2) =
        // Type 2` — in model under the increment-aware collapse. This is the
        // `Definition foo := Type` / `Tlist` shape (`Type@{named+1}`).
        let max_inc = normalize_serapi(
            &parse_sexp(
                r#"(Sort(Type((((hash 1)(data(Level((DirPath((Id SerTop)))1))))0)(((hash 2)(data(Level((DirPath((Id SerTop)))2))))1))))"#,
            )
            .unwrap(),
            &ctx,
            &[],
        )
        .unwrap();
        assert!(matches!(
            sexp_to_cic(&max_inc).unwrap(),
            CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Type(2)))
        ));
        // max(l1, Var 0): the bound polymorphic arm now collapses to `Type 1`
        // (base 1), so `max(Type 1, Type 1) = Type 1` — in model.
        let max_var = normalize_serapi(
            &parse_sexp(
                r#"(Sort(Type((((hash 1)(data(Level((DirPath((Id SerTop)))1))))0)(((hash 2)(data(Var 0)))0))))"#,
            )
            .unwrap(),
            &ctx,
            &[],
        )
        .unwrap();
        assert!(matches!(
            sexp_to_cic(&max_var).unwrap(),
            CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Type(1)))
        ));
        // max(l1, Set+1): the pierced-Set arm carries increment 1, i.e.
        // `Set + 1 = Type 1` — the SAME point l1 collapses to, so the whole
        // max is IN model and lands at `Type 1`. This is the shape of
        // `relation A := A -> A -> Prop` (`Type@{max(u, Set+1)}`) that gates
        // the entire Relations/Setoid/Classes hierarchy.
        let max_set1 = normalize_serapi(
            &parse_sexp(
                r#"(Sort(Type((((hash 1)(data(Level((DirPath((Id SerTop)))1))))0)(((hash 9)(data SProp))1))))"#,
            )
            .unwrap(),
            &ctx,
            &[],
        )
        .unwrap();
        assert!(matches!(
            sexp_to_cic(&max_set1).unwrap(),
            CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Type(1)))
        ));
        // max(Set+2): `Set + 2 = Type 2`, in model, maps to `(Type 2)`.
        let max_set2 = normalize_serapi(
            &parse_sexp(r#"(Sort(Type((((hash 9)(data SProp))2))))"#).unwrap(),
            &ctx,
            &[],
        )
        .unwrap();
        assert!(matches!(
            sexp_to_cic(&max_set2).unwrap(),
            CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Type(2)))
        ));
    }

    // =======================================================================
    // General (post-abstracted) Fix structuralization (D5 root cause):
    // real dump payloads from data/corpora/coq-sexp/stdlib, extracted
    // VERBATIM (mathverse_coq_dump, Coq 8.20 stdlib).
    // =======================================================================

    /// REAL `Coq.Init.Decimal.uint` dump form (11 constructors).
    const RAW_DUMP_UINT: &str = r#"(CoqInductive Coq.Init.Decimal.uint 0 (Sort Set) (NumParams 0) (Ctor Coq.Init.Decimal.Nil (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ()))))) (Ctor Coq.Init.Decimal.D0 (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))))) (Ctor Coq.Init.Decimal.D1 (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))))) (Ctor Coq.Init.Decimal.D2 (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))))) (Ctor Coq.Init.Decimal.D3 (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))))) (Ctor Coq.Init.Decimal.D4 (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))))) (Ctor Coq.Init.Decimal.D5 (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))))) (Ctor Coq.Init.Decimal.D6 (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))))) (Ctor Coq.Init.Decimal.D7 (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))))) (Ctor Coq.Init.Decimal.D8 (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))))) (Ctor Coq.Init.Decimal.D9 (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))))))"#;

    /// REAL `Coq.Init.Decimal.revapp` dump form: a fix whose self-call
    /// CHANGES the post-struct argument (`revapp d (D0 d')`) — the shape the
    /// strict encoding rejects ("self-call argument is not the enclosing fix
    /// binder").
    const RAW_DUMP_REVAPP: &str = r#"(CoqConstant Coq.Init.Decimal.revapp (Prod ((binder_name (Name (Id d))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id d'))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))))) (Fix (((0) 0) ((((binder_name (Name (Id revapp))) (binder_relevance Relevant))) ((Prod ((binder_name (Name (Id d))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id d'))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ()))))))) ((Lambda ((binder_name (Name (Id d))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Lambda ((binder_name (Name (Id d'))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1 1 1 1 1 1 1 1 1 1)) (ci_cstr_nargs (0 1 1 1 1 1 1 1 1 1 1)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) () (((((binder_name (Name (Id d))) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Rel 1)) ((((binder_name (Name (Id d))) (binder_relevance Relevant))) (App (Rel 4) ((Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) 2) (Instance (() ())))) ((Rel 2)))))) ((((binder_name (Name (Id d))) (binder_relevance Relevant))) (App (Rel 4) ((Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) 3) (Instance (() ())))) ((Rel 2)))))) ((((binder_name (Name (Id d))) (binder_relevance Relevant))) (App (Rel 4) ((Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) 4) (Instance (() ())))) ((Rel 2)))))) ((((binder_name (Name (Id d))) (binder_relevance Relevant))) (App (Rel 4) ((Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) 5) (Instance (() ())))) ((Rel 2)))))) ((((binder_name (Name (Id d))) (binder_relevance Relevant))) (App (Rel 4) ((Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) 6) (Instance (() ())))) ((Rel 2)))))) ((((binder_name (Name (Id d))) (binder_relevance Relevant))) (App (Rel 4) ((Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) 7) (Instance (() ())))) ((Rel 2)))))) ((((binder_name (Name (Id d))) (binder_relevance Relevant))) (App (Rel 4) ((Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) 8) (Instance (() ())))) ((Rel 2)))))) ((((binder_name (Name (Id d))) (binder_relevance Relevant))) (App (Rel 4) ((Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) 9) (Instance (() ())))) ((Rel 2)))))) ((((binder_name (Name (Id d))) (binder_relevance Relevant))) (App (Rel 4) ((Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) 10) (Instance (() ())))) ((Rel 2)))))) ((((binder_name (Name (Id d))) (binder_relevance Relevant))) (App (Rel 4) ((Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) 11) (Instance (() ())))) ((Rel 2)))))))))))))))"#;

    /// REAL `Coq.Init.Decimal.uint_beq` dump form: a fix whose self-call
    /// sits INSIDE the nested match on the second argument — the shape the
    /// strict encoding rejects ("self-reference inside a nested fixpoint
    /// unsupported"). Its opacity was the root cause of the
    /// `internal_uint_dec_bl` beta-redex kernel mismatch (D5).
    const RAW_DUMP_UINT_BEQ: &str = r#"(CoqConstant Coq.Init.Decimal.uint_beq (Prod ((binder_name (Name (Id X))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id Y))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ())))))) (Fix (((0) 0) ((((binder_name (Name (Id uint_eqrec))) (binder_relevance Relevant))) ((Prod ((binder_name (Name (Id X))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id Y))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))))) ((Lambda ((binder_name (Name (Id X))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Lambda ((binder_name (Name (Id Y))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0) (Instance (() ())))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1 1 1 1 1 1 1 1 1 1)) (ci_cstr_nargs (0 1 1 1 1 1 1 1 1 1 1)) (ci_pp_info ((style MatchStyle)))) (Instance (() ())) () (((((binder_name Anonymous) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1 1 1 1 1 1 1 1 1 1)) (ci_cstr_nargs (0 1 1 1 1 1 1 1 1 1 1)) (ci_pp_info ((style MatchStyle)))) (Instance (() ())) () (((((binder_name Anonymous) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 1) ((() (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 1) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ())))))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1 1 1 1 1 1 1 1 1 1)) (ci_cstr_nargs (0 1 1 1 1 1 1 1 1 1 1)) (ci_pp_info ((style MatchStyle)))) (Instance (() ())) () (((((binder_name Anonymous) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 5) ((Rel 2) (Rel 1)))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ())))))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1 1 1 1 1 1 1 1 1 1)) (ci_cstr_nargs (0 1 1 1 1 1 1 1 1 1 1)) (ci_pp_info ((style MatchStyle)))) (Instance (() ())) () (((((binder_name Anonymous) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 5) ((Rel 2) (Rel 1)))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ())))))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1 1 1 1 1 1 1 1 1 1)) (ci_cstr_nargs (0 1 1 1 1 1 1 1 1 1 1)) (ci_pp_info ((style MatchStyle)))) (Instance (() ())) () (((((binder_name Anonymous) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 5) ((Rel 2) (Rel 1)))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ())))))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1 1 1 1 1 1 1 1 1 1)) (ci_cstr_nargs (0 1 1 1 1 1 1 1 1 1 1)) (ci_pp_info ((style MatchStyle)))) (Instance (() ())) () (((((binder_name Anonymous) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 5) ((Rel 2) (Rel 1)))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ())))))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1 1 1 1 1 1 1 1 1 1)) (ci_cstr_nargs (0 1 1 1 1 1 1 1 1 1 1)) (ci_pp_info ((style MatchStyle)))) (Instance (() ())) () (((((binder_name Anonymous) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 5) ((Rel 2) (Rel 1)))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ())))))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1 1 1 1 1 1 1 1 1 1)) (ci_cstr_nargs (0 1 1 1 1 1 1 1 1 1 1)) (ci_pp_info ((style MatchStyle)))) (Instance (() ())) () (((((binder_name Anonymous) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 5) ((Rel 2) (Rel 1)))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ())))))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1 1 1 1 1 1 1 1 1 1)) (ci_cstr_nargs (0 1 1 1 1 1 1 1 1 1 1)) (ci_pp_info ((style MatchStyle)))) (Instance (() ())) () (((((binder_name Anonymous) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 5) ((Rel 2) (Rel 1)))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ())))))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1 1 1 1 1 1 1 1 1 1)) (ci_cstr_nargs (0 1 1 1 1 1 1 1 1 1 1)) (ci_pp_info ((style MatchStyle)))) (Instance (() ())) () (((((binder_name Anonymous) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 5) ((Rel 2) (Rel 1)))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ())))))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1 1 1 1 1 1 1 1 1 1)) (ci_cstr_nargs (0 1 1 1 1 1 1 1 1 1 1)) (ci_pp_info ((style MatchStyle)))) (Instance (() ())) () (((((binder_name Anonymous) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 5) ((Rel 2) (Rel 1)))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ())))))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Decimal) (Id Init) (Id Coq)))) (Id uint)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1 1 1 1 1 1 1 1 1 1)) (ci_cstr_nargs (0 1 1 1 1 1 1 1 1 1 1)) (ci_pp_info ((style MatchStyle)))) (Instance (() ())) () (((((binder_name Anonymous) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) 2) (Instance (() ()))))) ((((binder_name Anonymous) (binder_relevance Relevant))) (App (Rel 5) ((Rel 2) (Rel 1))))))))))))))))"#;

    /// REAL `Coq.Init.Datatypes.bool` dump form.
    const RAW_DUMP_BOOL: &str = r#"(CoqInductive Coq.Init.Datatypes.bool 0 (Sort Set) (NumParams 0) (Ctor Coq.Init.Datatypes.true (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) (Ctor Coq.Init.Datatypes.false (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))))"#;

    /// D5 general fix encoding — varying post-struct argument: the REAL
    /// `revapp` translates, kernel-verifies, and COMPUTES correctly through
    /// TWO recursive unfoldings with a different accumulator each time
    /// (`revapp (D1 (D2 Nil)) Nil = D2 (D1 Nil)`), which only holds if the
    /// minor premises genuinely rebind the accumulator (a frozen-argument
    /// mistranslation yields a different value and the negative control
    /// below would pass instead).
    #[test]
    fn test_real_dump_revapp_general_fix_computes() {
        let theorem = r#"(CoqConstant SerTop.revapp_computes
  (App (Ind Coq.Init.Logic.eq 0) (Ind Coq.Init.Decimal.uint 0)
    (App (Const Coq.Init.Decimal.revapp) (App (Construct Coq.Init.Decimal.uint 0 2) (App (Construct Coq.Init.Decimal.uint 0 3) (Construct Coq.Init.Decimal.uint 0 0))) (Construct Coq.Init.Decimal.uint 0 0))
    (App (Construct Coq.Init.Decimal.uint 0 3) (App (Construct Coq.Init.Decimal.uint 0 2) (Construct Coq.Init.Decimal.uint 0 0))))
  (App (Construct Coq.Init.Logic.eq 0 0) (Ind Coq.Init.Decimal.uint 0) (App (Construct Coq.Init.Decimal.uint 0 3) (App (Construct Coq.Init.Decimal.uint 0 2) (Construct Coq.Init.Decimal.uint 0 0)))))"#;
        let input = format!("{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_UINT}\n{RAW_DUMP_REVAPP}\n{theorem}");
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "revapp must translate through the general encoding: {:?}",
            stats.value_failure_reasons
        );
        let report = verify_sexp(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in ["Coq.Init.Decimal.revapp", "SerTop.revapp_computes"] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified (fallbacks: {:?})",
                report.axiom_fallback_names
            );
        }
        // Negative control: claim the NON-reversed result. If the encoding
        // froze the accumulator (the strict encoding's bug class), this is
        // what the mistranslated function would compute — it must be
        // REJECTED.
        let bad_theorem = r#"(CoqConstant SerTop.revapp_computes
  (App (Ind Coq.Init.Logic.eq 0) (Ind Coq.Init.Decimal.uint 0)
    (App (Const Coq.Init.Decimal.revapp) (App (Construct Coq.Init.Decimal.uint 0 2) (App (Construct Coq.Init.Decimal.uint 0 3) (Construct Coq.Init.Decimal.uint 0 0))) (Construct Coq.Init.Decimal.uint 0 0))
    (App (Construct Coq.Init.Decimal.uint 0 2) (App (Construct Coq.Init.Decimal.uint 0 3) (Construct Coq.Init.Decimal.uint 0 0))))
  (App (Construct Coq.Init.Logic.eq 0 0) (Ind Coq.Init.Decimal.uint 0) (App (Construct Coq.Init.Decimal.uint 0 2) (App (Construct Coq.Init.Decimal.uint 0 3) (Construct Coq.Init.Decimal.uint 0 0)))))"#;
        let bad = format!("{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_UINT}\n{RAW_DUMP_REVAPP}\n{bad_theorem}");
        let neg = verify_sexp(&bad);
        assert!(
            !neg.kernel_verified_names
                .contains(&"SerTop.revapp_computes".to_string()),
            "the un-reversed result must be REJECTED — revapp must genuinely vary its accumulator"
        );
    }

    /// REAL `Coq.Init.Nat.add` dump form (recursive fix over the first arg).
    const RAW_DUMP_NAT_ADD: &str = r#"(CoqConstant Coq.Init.Nat.add (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id m))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))))) (Fix (((0) 0) ((((binder_name (Name (Id add))) (binder_relevance Relevant))) ((Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id m))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ()))))))) ((Lambda ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Lambda ((binder_name (Name (Id m))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1)) (ci_cstr_nargs (0 1)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) () (((((binder_name (Name (Id n))) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Rel 1)) ((((binder_name (Name (Id p))) (binder_relevance Relevant))) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 2) (Instance (() ())))) ((App (Rel 4) ((Rel 1) (Rel 2)))))))))))))))"#;

    /// REAL `Coq.Vectors.VectorDef.t` (length-indexed vectors) dump form.
    const RAW_DUMP_VECTOR_T: &str = r#"(CoqInductive Coq.Vectors.VectorDef.t 0 (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 102343447329548675) (data (Level ((DirPath ((Id VectorDef) (Id Vectors) (Id Coq))) 17981660420)))) 0)))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Sort (Type ((((hash 0) (data (Level ((DirPath ((Id mathverse_template_collapse))) 0)))) 0)))))) (NumParams 1) (Ctor Coq.Vectors.VectorDef.nil (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 102343447329548675) (data (Level ((DirPath ((Id VectorDef) (Id Vectors) (Id Coq))) 17981660420)))) 0)))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 1) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 1) (Instance (() ())))))))) (Ctor Coq.Vectors.VectorDef.cons (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 102343447329548675) (data (Level ((DirPath ((Id VectorDef) (Id Vectors) (Id Coq))) 17981660420)))) 0)))) (Prod ((binder_name (Name (Id h))) (binder_relevance Relevant)) (Rel 1) (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 3) (Rel 1))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 4) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 2) (Instance (() ())))) ((Rel 2)))))))))))"#;

    /// REAL `Coq.Vectors.VectorDef.append` dump form — a structural fix over an
    /// INDEXED family whose inductive index (`n`) is a NON-trailing pre-struct
    /// binder (the length parameter `p` sits between `n` and the struct arg
    /// `v`). The strict encoder's precise index-position identification is what
    /// makes it structuralize.
    const RAW_DUMP_VECTOR_APPEND: &str = r#"(CoqConstant Coq.Vectors.VectorDef.append (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 102343447336305372) (data (Level ((DirPath ((Id VectorDef) (Id Vectors) (Id Coq))) 17981660420)))) 0)))) (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id p))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id v))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 3) (Rel 2))) (Prod ((binder_name (Name (Id w))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 4) (Rel 2))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 5) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Nat) (Id Init) (Id Coq)))) (Id add)) ()) (Instance (() ())))) ((Rel 4) (Rel 3)))))))))) (Fix (((3) 0) ((((binder_name (Name (Id append))) (binder_relevance Relevant))) ((Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 102343447336305372) (data (Level ((DirPath ((Id VectorDef) (Id Vectors) (Id Coq))) 17981660420)))) 0)))) (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id p))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id v))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 3) (Rel 2))) (Prod ((binder_name (Name (Id w))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 4) (Rel 2))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 5) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Nat) (Id Init) (Id Coq)))) (Id add)) ()) (Instance (() ())))) ((Rel 4) (Rel 3))))))))))) ((Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 102343447336305372) (data (Level ((DirPath ((Id VectorDef) (Id Vectors) (Id Coq))) 17981660420)))) 0)))) (Lambda ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Lambda ((binder_name (Name (Id p))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Lambda ((binder_name (Name (Id v))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 3) (Rel 2))) (Lambda ((binder_name (Name (Id w))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 4) (Rel 2))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0)) (ci_npar 1) (ci_cstr_ndecls (0 3)) (ci_cstr_nargs (0 3)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 5)) (((((binder_name (Name (Id n))) (binder_relevance Relevant)) ((binder_name (Name (Id v))) (binder_relevance Relevant))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 7) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Nat) (Id Init) (Id Coq)))) (Id add)) ()) (Instance (() ())))) ((Rel 2) (Rel 5)))))) Relevant) NoInvert (Rel 2) ((() (Rel 1)) ((((binder_name (Name (Id a))) (binder_relevance Relevant)) ((binder_name (Name (Id n0))) (binder_relevance Relevant)) ((binder_name (Name (Id v'))) (binder_relevance Relevant))) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) 2) (Instance (() ())))) ((Rel 8) (Rel 3) (App (Const ((Constant (KerName (MPfile (DirPath ((Id Nat) (Id Init) (Id Coq)))) (Id add)) ()) (Instance (() ())))) ((Rel 2) (Rel 6))) (App (Rel 9) ((Rel 8) (Rel 2) (Rel 6) (Rel 1) (Rel 4))))))))))))))))))"#;

    const RAW_DUMP_NAT_SHORT: &str = r#"(CoqInductive Coq.Init.Datatypes.nat 0 Set
  (Ctor O (Ind Coq.Init.Datatypes.nat 0))
  (Ctor S (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))))"#;
    const RAW_DUMP_EQ_SHORT: &str = r#"(CoqInductive Coq.Init.Logic.eq 0 (Prod A (Sort (Type 1)) (Prod x (Rel 0) (Prod y (Rel 1) (Sort Prop))))
  (NumParams 2)
  (Ctor eq_refl (Prod A (Sort (Type 1)) (Prod x (Rel 0) (App (Ind Coq.Init.Logic.eq 0) (Rel 1) (Rel 0) (Rel 0))))))"#;

    /// GOOD computational theorem: `append [O] [S O] = [O; S O]` (`t nat 2`).
    const APPEND_COMPUTES_GOOD: &str = r#"(CoqConstant SerTop.append_computes
  (App (Ind Coq.Init.Logic.eq 0) (App (Ind Coq.Vectors.VectorDef.t 0) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)))) (App (Const Coq.Vectors.VectorDef.append) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0))) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0)))) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0)))))
  (App (Construct Coq.Init.Logic.eq 0 0) (App (Ind Coq.Vectors.VectorDef.t 0) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)))) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0))))))"#;
    /// NEGATIVE control: the swapped result `[S O; O]` is FALSE.
    const APPEND_COMPUTES_BAD: &str = r#"(CoqConstant SerTop.append_computes
  (App (Ind Coq.Init.Logic.eq 0) (App (Ind Coq.Vectors.VectorDef.t 0) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)))) (App (Const Coq.Vectors.VectorDef.append) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0))) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0)))) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0)))))
  (App (Construct Coq.Init.Logic.eq 0 0) (App (Ind Coq.Vectors.VectorDef.t 0) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)))) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0))))))"#;

    /// FIDELITY (index-position fix): the REAL `Vector.append` structuralizes,
    /// kernel-verifies, AND COMPUTES the genuine concatenation through the
    /// indexed recursor — `append [O] [S O] = [O; S O]` (`t nat 2`) reduces via
    /// index-carrying iota steps. The historical trailing-`[r-n_idx, r)` index
    /// heuristic dropped the WRONG pre-struct argument (`p` instead of `n`, the
    /// length parameter sits between the index and the struct), so `append`
    /// stayed a type-only stand-in; the precise index-position identification
    /// structuralizes it. Types are checked, so the concrete reduction is
    /// pinned (the `sub 1 1` fidelity discipline for indexed families).
    #[test]
    fn test_real_dump_vector_append_indexed_fix_computes() {
        let good = format!(
            "{RAW_DUMP_NAT_SHORT}\n{RAW_DUMP_EQ_SHORT}\n{RAW_DUMP_NAT_ADD}\n{RAW_DUMP_VECTOR_T}\n{RAW_DUMP_VECTOR_APPEND}\n{APPEND_COMPUTES_GOOD}"
        );
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&good, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "append + the computational theorem must translate: {:?}",
            stats.value_failure_reasons
        );
        let report = verify_sexp(&good);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in ["Coq.Vectors.VectorDef.append", "SerTop.append_computes"] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified (indexed recursor over t A n) — fallbacks: {:?}",
                report.axiom_fallback_names
            );
        }

        // NEGATIVE CONTROL: `append [O] [S O] = [S O; O]` is FALSE (the
        // concatenation is `[O; S O]`). It must be REJECTED — a value-corrupting
        // index/field mistranslation would let it through.
        let bad = format!(
            "{RAW_DUMP_NAT_SHORT}\n{RAW_DUMP_EQ_SHORT}\n{RAW_DUMP_NAT_ADD}\n{RAW_DUMP_VECTOR_T}\n{RAW_DUMP_VECTOR_APPEND}\n{APPEND_COMPUTES_BAD}"
        );
        assert_ne!(bad, good, "negative control must differ");
        let neg = verify_sexp(&bad);
        assert!(
            !neg.kernel_verified_names
                .contains(&"SerTop.append_computes".to_string()),
            "`append [O] [S O] = [S O; O]` is FALSE and must be REJECTED"
        );
        assert!(
            neg.kernel_verified_names
                .contains(&"Coq.Vectors.VectorDef.append".to_string()),
            "append itself must remain KernelVerified in the negative fixture"
        );
    }

    /// REAL `Coq.Vectors.VectorDef.shiftin` dump form — a structural fix over
    /// the INDEXED family `t A n` whose index `n` is a NON-trailing pre-struct
    /// binder (the element `a` sits between `n` and the struct arg `v`).
    const RAW_DUMP_VECTOR_SHIFTIN: &str = r#"(CoqConstant Coq.Vectors.VectorDef.shiftin (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 102343447335321387) (data (Level ((DirPath ((Id VectorDef) (Id Vectors) (Id Coq))) 17981660420)))) 0)))) (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id a))) (binder_relevance Relevant)) (Rel 2) (Prod ((binder_name (Name (Id v))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 3) (Rel 2))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 4) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 2) (Instance (() ())))) ((Rel 3))))))))) (Fix (((3) 0) ((((binder_name (Name (Id shiftin))) (binder_relevance Relevant))) ((Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 102343447335321387) (data (Level ((DirPath ((Id VectorDef) (Id Vectors) (Id Coq))) 17981660420)))) 0)))) (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id a))) (binder_relevance Relevant)) (Rel 2) (Prod ((binder_name (Name (Id v))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 3) (Rel 2))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 4) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 2) (Instance (() ())))) ((Rel 3)))))))))) ((Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 102343447335321387) (data (Level ((DirPath ((Id VectorDef) (Id Vectors) (Id Coq))) 17981660420)))) 0)))) (Lambda ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Lambda ((binder_name (Name (Id a))) (binder_relevance Relevant)) (Rel 2) (Lambda ((binder_name (Name (Id v))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 3) (Rel 2))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0)) (ci_npar 1) (ci_cstr_ndecls (0 3)) (ci_cstr_nargs (0 3)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 4)) (((((binder_name (Name (Id n))) (binder_relevance Relevant)) ((binder_name (Name (Id v))) (binder_relevance Relevant))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) (Instance (() ())))) ((Rel 6) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 2) (Instance (() ())))) ((Rel 2)))))) Relevant) NoInvert (Rel 1) ((() (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) 2) (Instance (() ())))) ((Rel 4) (Rel 2) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 1) (Instance (() ())))) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) 1) (Instance (() ())))) ((Rel 4)))))) ((((binder_name (Name (Id h))) (binder_relevance Relevant)) ((binder_name (Name (Id n0))) (binder_relevance Relevant)) ((binder_name (Name (Id t))) (binder_relevance Relevant))) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id VectorDef) (Id Vectors) (Id Coq)))) (Id t)) ()) 0) 2) (Instance (() ())))) ((Rel 7) (Rel 3) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 2) (Instance (() ())))) ((Rel 2))) (App (Rel 8) ((Rel 7) (Rel 2) (Rel 5) (Rel 1)))))))))))))))))"#;

    /// GOOD: `shiftin O [S O] = [S O; O]` (append at the end), `t nat 2`.
    const SHIFTIN_COMPUTES_GOOD: &str = r#"(CoqConstant SerTop.shiftin_computes
  (App (Ind Coq.Init.Logic.eq 0) (App (Ind Coq.Vectors.VectorDef.t 0) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)))) (App (Const Coq.Vectors.VectorDef.shiftin) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0)))) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0)))))
  (App (Construct Coq.Init.Logic.eq 0 0) (App (Ind Coq.Vectors.VectorDef.t 0) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)))) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0))))))"#;
    /// NEGATIVE control: `[O; S O]` (front-insert) is FALSE.
    const SHIFTIN_COMPUTES_BAD: &str = r#"(CoqConstant SerTop.shiftin_computes
  (App (Ind Coq.Init.Logic.eq 0) (App (Ind Coq.Vectors.VectorDef.t 0) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)))) (App (Const Coq.Vectors.VectorDef.shiftin) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0)))) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0)))))
  (App (Construct Coq.Init.Logic.eq 0 0) (App (Ind Coq.Vectors.VectorDef.t 0) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)))) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (App (Construct Coq.Vectors.VectorDef.t 0 1) (Ind Coq.Init.Datatypes.nat 0) (App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0)) (Construct Coq.Init.Datatypes.nat 0 0) (App (Construct Coq.Vectors.VectorDef.t 0 0) (Ind Coq.Init.Datatypes.nat 0))))))"#;

    /// FIDELITY (index-position fix, second constructed value): `shiftin`
    /// appends its argument at the END of an indexed vector; it structuralizes
    /// and COMPUTES `shiftin O [S O] = [S O; O]` through the indexed recursor
    /// (the index `n` flows through pre-struct position 1, with the element `a`
    /// in between — the exact non-trailing shape the old heuristic mis-handled).
    #[test]
    fn test_real_dump_vector_shiftin_indexed_fix_computes() {
        let good = format!(
            "{RAW_DUMP_NAT_SHORT}\n{RAW_DUMP_EQ_SHORT}\n{RAW_DUMP_VECTOR_T}\n{RAW_DUMP_VECTOR_SHIFTIN}\n{SHIFTIN_COMPUTES_GOOD}"
        );
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&good, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "shiftin + the computational theorem must translate: {:?}",
            stats.value_failure_reasons
        );
        let report = verify_sexp(&good);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in ["Coq.Vectors.VectorDef.shiftin", "SerTop.shiftin_computes"] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified — fallbacks: {:?}",
                report.axiom_fallback_names
            );
        }
        let bad = format!(
            "{RAW_DUMP_NAT_SHORT}\n{RAW_DUMP_EQ_SHORT}\n{RAW_DUMP_VECTOR_T}\n{RAW_DUMP_VECTOR_SHIFTIN}\n{SHIFTIN_COMPUTES_BAD}"
        );
        assert_ne!(bad, good, "negative control must differ");
        let neg = verify_sexp(&bad);
        assert!(
            !neg.kernel_verified_names
                .contains(&"SerTop.shiftin_computes".to_string()),
            "`shiftin O [S O] = [O; S O]` is FALSE and must be REJECTED"
        );
        assert!(
            neg.kernel_verified_names
                .contains(&"Coq.Vectors.VectorDef.shiftin".to_string()),
            "shiftin itself must remain KernelVerified in the negative fixture"
        );
    }

    /// D5 general fix encoding — self-call inside the nested match on the
    /// second argument: the REAL `uint_beq` translates, kernel-verifies, and
    /// COMPUTES (`uint_beq (D0 Nil) (D0 Nil) = true` iota/delta-reduces
    /// through the nested recursor spine; `uint_beq (D0 Nil) (D1 Nil) = true`
    /// is rejected because it computes to `false`).
    #[test]
    fn test_real_dump_uint_beq_nested_case_fix_computes() {
        let tru = "(Construct Coq.Init.Datatypes.bool 0 0)";
        let theorem = format!(
            r#"(CoqConstant SerTop.uint_beq_computes
  (App (Ind Coq.Init.Logic.eq 0) (Ind Coq.Init.Datatypes.bool 0)
    (App (Const Coq.Init.Decimal.uint_beq) (App (Construct Coq.Init.Decimal.uint 0 1) (Construct Coq.Init.Decimal.uint 0 0)) (App (Construct Coq.Init.Decimal.uint 0 1) (Construct Coq.Init.Decimal.uint 0 0)))
    {tru})
  (App (Construct Coq.Init.Logic.eq 0 0) (Ind Coq.Init.Datatypes.bool 0) {tru}))"#
        );
        let input = format!(
            "{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_BOOL}\n{RAW_DUMP_UINT}\n{RAW_DUMP_UINT_BEQ}\n{theorem}"
        );
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "uint_beq must translate through the general encoding: {:?}",
            stats.value_failure_reasons
        );
        let report = verify_sexp(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in ["Coq.Init.Decimal.uint_beq", "SerTop.uint_beq_computes"] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified (fallbacks: {:?})",
                report.axiom_fallback_names
            );
        }
        // Negative control: uint_beq (D0 Nil) (D1 Nil) computes to `false`,
        // so claiming `= true` must be REJECTED.
        let bad_theorem = format!(
            r#"(CoqConstant SerTop.uint_beq_computes
  (App (Ind Coq.Init.Logic.eq 0) (Ind Coq.Init.Datatypes.bool 0)
    (App (Const Coq.Init.Decimal.uint_beq) (App (Construct Coq.Init.Decimal.uint 0 1) (Construct Coq.Init.Decimal.uint 0 0)) (App (Construct Coq.Init.Decimal.uint 0 2) (Construct Coq.Init.Decimal.uint 0 0)))
    {tru})
  (App (Construct Coq.Init.Logic.eq 0 0) (Ind Coq.Init.Datatypes.bool 0) {tru}))"#
        );
        let bad = format!(
            "{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_BOOL}\n{RAW_DUMP_UINT}\n{RAW_DUMP_UINT_BEQ}\n{bad_theorem}"
        );
        let neg = verify_sexp(&bad);
        assert!(
            !neg.kernel_verified_names
                .contains(&"SerTop.uint_beq_computes".to_string()),
            "uint_beq (D0 Nil) (D1 Nil) = true must be REJECTED (it computes to false)"
        );
    }

    /// REAL `Coq.Init.Datatypes.nat` dump form.
    const RAW_DUMP_NAT: &str = r#"(CoqInductive Coq.Init.Datatypes.nat 0 (Sort Set) (NumParams 0) (Ctor Coq.Init.Datatypes.O (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ()))))) (Ctor Coq.Init.Datatypes.S (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))))))"#;

    /// REAL `Coq.Init.Datatypes.list` dump form.
    const RAW_DUMP_LIST: &str = r#"(CoqInductive Coq.Init.Datatypes.list 0 (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757856266522) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 27366926484)))) 0)))) (Sort (Type ((((hash 0) (data (Level ((DirPath ((Id mathverse_template_collapse))) 0)))) 0))))) (NumParams 1) (Ctor Coq.Init.Datatypes.nil (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757856266522) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 27366926484)))) 0)))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0) (Instance (() ())))) ((Rel 1))))) (Ctor Coq.Init.Datatypes.cons (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 81821757856266522) (data (Level ((DirPath ((Id Datatypes) (Id Init) (Id Coq))) 27366926484)))) 0)))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 1) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0) (Instance (() ())))) ((Rel 2))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0) (Instance (() ())))) ((Rel 3))))))))"#;

    /// REAL `Coq.Lists.List.nth` dump form: a fixpoint recursing on `l`
    /// (argument 1) whose OUTER match is on `n` (argument 0), with
    /// Rel-bearing match shells (`A`, the enclosing type-parameter binder) —
    /// the relaxed match-commutation shape ("Fix: match discriminant is not
    /// the structural argument" fail class).
    const RAW_DUMP_LIST_NTH: &str = r#"(CoqConstant Coq.Lists.List.nth (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 738407140443) (data (Level ((DirPath ((Id List) (Id Lists) (Id Coq))) 18336402176)))) 0)))) (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id l))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0) (Instance (() ())))) ((Rel 2))) (Prod ((binder_name (Name (Id default))) (binder_relevance Relevant)) (Rel 3) (Rel 4))))) (Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 738407140443) (data (Level ((DirPath ((Id List) (Id Lists) (Id Coq))) 18336402176)))) 0)))) (Fix (((1) 0) ((((binder_name (Name (Id nth))) (binder_relevance Relevant))) ((Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id l))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0) (Instance (() ())))) ((Rel 2))) (Prod ((binder_name (Name (Id default))) (binder_relevance Relevant)) (Rel 3) (Rel 4))))) ((Lambda ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Lambda ((binder_name (Name (Id l))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0) (Instance (() ())))) ((Rel 3))) (Lambda ((binder_name (Name (Id default))) (binder_relevance Relevant)) (Rel 4) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1)) (ci_cstr_nargs (0 1)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) () (((((binder_name (Name (Id n))) (binder_relevance Relevant))) (Rel 6)) Relevant) NoInvert (Rel 3) ((() (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0)) (ci_npar 1) (ci_cstr_ndecls (0 2)) (ci_cstr_nargs (0 2)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 5)) (((((binder_name (Name (Id l))) (binder_relevance Relevant))) (Rel 6)) Relevant) NoInvert (Rel 2) ((() (Rel 1)) ((((binder_name (Name (Id x))) (binder_relevance Relevant)) ((binder_name (Name (Id l'))) (binder_relevance Relevant))) (Rel 2))))) ((((binder_name (Name (Id m))) (binder_relevance Relevant))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0)) (ci_npar 1) (ci_cstr_ndecls (0 2)) (ci_cstr_nargs (0 2)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 6)) (((((binder_name (Name (Id l))) (binder_relevance Relevant))) (Rel 7)) Relevant) NoInvert (Rel 3) ((() (Rel 2)) ((((binder_name (Name (Id x))) (binder_relevance Relevant)) ((binder_name (Name (Id t))) (binder_relevance Relevant))) (App (Rel 7) ((Rel 3) (Rel 1) (Rel 4))))))))))))))))))"#;

    /// Relaxed match-commutation — Rel-bearing shells + argument reorder
    /// under an enclosing binder: the REAL `List.nth` translates,
    /// kernel-verifies, and COMPUTES (`nth nat 1 [O; S O] O = S O`
    /// iota/delta-reduces through the projected recursor spine; claiming
    /// `= O` is rejected because the call computes to `S O`). Exercises the
    /// relocated-shell lifting, the position-shifted argument types, and the
    /// `project_arg_permutation` free-reference lift over the projection
    /// binders.
    #[test]
    fn test_real_dump_list_nth_commute_relaxed_shells_computes() {
        let nat_t = "(Ind Coq.Init.Datatypes.nat 0)";
        let o = "(Construct Coq.Init.Datatypes.nat 0 0)";
        let so =
            "(App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0))";
        let nil = "(App (Construct Coq.Init.Datatypes.list 0 0) (Ind Coq.Init.Datatypes.nat 0))";
        let l_tail = format!("(App (Construct Coq.Init.Datatypes.list 0 1) {nat_t} {so} {nil})");
        let l = format!("(App (Construct Coq.Init.Datatypes.list 0 1) {nat_t} {o} {l_tail})");
        let call = format!("(App (Const Coq.Lists.List.nth) {nat_t} {so} {l} {o})");
        let theorem = format!(
            "(CoqConstant SerTop.nth_computes (App (Ind Coq.Init.Logic.eq 0) {nat_t} {call} {so}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} {so}))"
        );
        let input = format!(
            "{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_NAT}\n{RAW_DUMP_LIST}\n{RAW_DUMP_LIST_NTH}\n{theorem}"
        );
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "nth must translate through the relaxed commute: {:?}",
            stats.value_failure_reasons
        );
        let report = verify_sexp(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in ["Coq.Lists.List.nth", "SerTop.nth_computes"] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified (fallbacks: {:?})",
                report.axiom_fallback_names
            );
        }
        // Negative control: `nth nat 1 [O; S O] O` computes to `S O`, so
        // claiming `= O` must be REJECTED — a commute that scrambled the
        // branch bodies or the argument order would compute differently.
        let bad_theorem = format!(
            "(CoqConstant SerTop.nth_computes (App (Ind Coq.Init.Logic.eq 0) {nat_t} {call} {o}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} {o}))"
        );
        let bad = format!(
            "{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_NAT}\n{RAW_DUMP_LIST}\n{RAW_DUMP_LIST_NTH}\n{bad_theorem}"
        );
        let neg = verify_sexp(&bad);
        assert!(
            !neg.kernel_verified_names
                .contains(&"SerTop.nth_computes".to_string()),
            "nth nat 1 [O; S O] O = O must be REJECTED (it computes to S O)"
        );
    }

    /// The REAL `sertop` dump of `Coq.Init.Nat.sub` — the `| _, _ => n`
    /// struct-binder-referencing branch shape (`fix sub n m := match n with
    /// O => n | S k => match m with O => n | S l => sub k l end end`).
    const RAW_DUMP_NAT_SUB: &str = r#"(CoqConstant Coq.Init.Nat.sub (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id m))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))))) (Fix (((0) 0) ((((binder_name (Name (Id sub))) (binder_relevance Relevant))) ((Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id m))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ()))))))) ((Lambda ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Lambda ((binder_name (Name (Id m))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1)) (ci_cstr_nargs (0 1)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) () (((((binder_name (Name (Id n))) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Rel 2)) ((((binder_name (Name (Id k))) (binder_relevance Relevant))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1)) (ci_cstr_nargs (0 1)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) () (((((binder_name (Name (Id m))) (binder_relevance Relevant))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ()))))) Relevant) NoInvert (Rel 2) ((() (Rel 3)) ((((binder_name (Name (Id l))) (binder_relevance Relevant))) (App (Rel 5) ((Rel 2) (Rel 1))))))))))))))))"#;

    /// STRUCT-BINDER references inside fix branches (the `Nat.sub`
    /// `| _, _ => n` idiom) must be substituted with the branch's OWN
    /// reconstructed constructor application (see [`StructBinderRecon`]).
    /// The stale-capture encoding this replaces made the imported `sub`
    /// compute `sub 1 1 ↝ 1` (the reused O-branch minor returned the
    /// ORIGINAL argument) — semantically NOT Coq's `sub` — and broke the
    /// one-step reduction parity (`sub (S x) (S x) ≡ sub x x`) that the
    /// whole `ssrnat`/`seq` masked-seed cluster rests on (2026-07-12).
    ///
    /// Pins BOTH directions: `sub 1 1 = 0` (Coq-true, needs depth-1
    /// recursion through the reused minors) kernel-verifies, and the
    /// mistranslation's own artifact `sub 1 1 = 1` is REJECTED.
    #[test]
    fn test_real_dump_nat_sub_struct_binder_branch_computes() {
        let nat_t = "(Ind Coq.Init.Datatypes.nat 0)";
        let zero = "(Construct Coq.Init.Datatypes.nat 0 0)";
        let one =
            "(App (Construct Coq.Init.Datatypes.nat 0 1) (Construct Coq.Init.Datatypes.nat 0 0))";
        let call = format!("(App (Const Coq.Init.Nat.sub) {one} {one})");
        let theorem = format!(
            "(CoqConstant SerTop.sub_one_one (App (Ind Coq.Init.Logic.eq 0) {nat_t} {call} {zero}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} {zero}))"
        );
        let input = format!("{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_NAT}\n{RAW_DUMP_NAT_SUB}\n{theorem}");
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "Nat.sub must translate: {:?}",
            stats.value_failure_reasons
        );
        let report = verify_sexp(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in ["Coq.Init.Nat.sub", "SerTop.sub_one_one"] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified (fallbacks: {:?})",
                report.axiom_fallback_names
            );
        }
        // Negative control: the stale-capture artifact. `sub 1 1 = 1` is
        // Coq-FALSE; an encoding whose reused minors capture the original
        // argument computes exactly this — it must be REJECTED.
        let bad_theorem = format!(
            "(CoqConstant SerTop.sub_one_one (App (Ind Coq.Init.Logic.eq 0) {nat_t} {call} {one}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} {one}))"
        );
        let bad = format!("{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_NAT}\n{RAW_DUMP_NAT_SUB}\n{bad_theorem}");
        let neg = verify_sexp(&bad);
        assert!(
            !neg.kernel_verified_names
                .contains(&"SerTop.sub_one_one".to_string()),
            "sub 1 1 = 1 must be REJECTED (the stale-capture mistranslation computed it)"
        );
    }

    /// The REAL `sertop` dump of `mathcomp.ssreflect.seq.drop` — a
    /// PRE-STRUCT-VARYING structural fixpoint: it recurses on the SECOND
    /// argument `s` (the struct) while the FIRST argument `n` (a pre-struct
    /// binder) VARIES across the recursion (`drop n' s'`, where `n'` is bound
    /// by the inner `nat` match). Both the strict and general fix encoders fix
    /// every pre-struct binder as a recursor parameter, so this shape reaches
    /// [`try_rotate_struct_to_front_fix`], which rotates `s` to the front so
    /// `n` becomes POST-struct (varying) and projects back. Pins reduction
    /// parity: `drop 1 [0;1] = [1]` kernel-verifies; the no-op identity
    /// mistranslation `drop 1 [0;1] = [0;1]` is REJECTED (negative control).
    const RAW_DUMP_SEQ_DROP: &str = r#"(CoqConstant mathcomp.ssreflect.seq.drop (Prod ((binder_name (Name (Id T))) (binder_relevance Relevant)) (Sort (Type ((((hash 141945045061975389) (data (Level ((DirPath ((Id seq) (Id ssreflect) (Id mathcomp))) 137711406679872)))) 0)))) (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id s))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0) (Instance (() ())))) ((Rel 2))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0) (Instance (() ())))) ((Rel 3)))))) (Lambda ((binder_name (Name (Id T))) (binder_relevance Relevant)) (Sort (Type ((((hash 141945045061975389) (data (Level ((DirPath ((Id seq) (Id ssreflect) (Id mathcomp))) 137711406679872)))) 0)))) (Fix (((1) 0) ((((binder_name (Name (Id drop))) (binder_relevance Relevant))) ((Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Prod ((binder_name (Name (Id s))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0) (Instance (() ())))) ((Rel 2))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0) (Instance (() ())))) ((Rel 3)))))) ((Lambda ((binder_name (Name (Id n))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Lambda ((binder_name (Name (Id s))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0) (Instance (() ())))) ((Rel 3))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0)) (ci_npar 1) (ci_cstr_ndecls (0 2)) (ci_cstr_nargs (0 2)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) ((Rel 4)) (((((binder_name (Name (Id s))) (binder_relevance Relevant))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0) (Instance (() ())))) ((Rel 5)))) Relevant) NoInvert (Rel 1) ((() (Rel 1)) ((((binder_name (Name (Id t))) (binder_relevance Relevant)) ((binder_name (Name (Id s'))) (binder_relevance Relevant))) (Case ((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1)) (ci_cstr_nargs (0 1)) (ci_pp_info ((style RegularStyle)))) (Instance (() ())) () (((((binder_name (Name (Id n))) (binder_relevance Relevant))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id list)) ()) 0) (Instance (() ())))) ((Rel 7)))) Relevant) NoInvert (Rel 4) ((() (Rel 3)) ((((binder_name (Name (Id n'))) (binder_relevance Relevant))) (App (Rel 6) ((Rel 1) (Rel 2)))))))))))))))))"#;

    #[test]
    fn test_real_dump_seq_drop_prestruct_varying_computes() {
        let nat_t = "(Ind Coq.Init.Datatypes.nat 0)";
        let o = "(Construct Coq.Init.Datatypes.nat 0 0)";
        let s1 = format!("(App (Construct Coq.Init.Datatypes.nat 0 1) {o})"); // S O = 1
        let listnat = format!("(App (Ind Coq.Init.Datatypes.list 0) {nat_t})");
        let nil = format!("(App (Construct Coq.Init.Datatypes.list 0 0) {nat_t})");
        let cons = |h: &str, t: &str| {
            format!("(App (Construct Coq.Init.Datatypes.list 0 1) {nat_t} {h} {t})")
        };
        // [0; 1] = cons O (cons (S O) nil)
        let lst = cons(o, &cons(&s1, &nil));
        // [1] = cons (S O) nil
        let expected = cons(&s1, &nil);
        // drop nat (S O) [0;1]  ↝  [1]
        let call = format!("(App (Const mathcomp.ssreflect.seq.drop) {nat_t} {s1} {lst})");
        let theorem = format!(
            "(CoqConstant SerTop.drop_computes (App (Ind Coq.Init.Logic.eq 0) {listnat} {call} {expected}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {listnat} {expected}))"
        );
        let input = format!(
            "{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_NAT}\n{RAW_DUMP_LIST}\n{RAW_DUMP_SEQ_DROP}\n{theorem}"
        );
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "drop must translate: {:?}",
            stats.value_failure_reasons
        );
        let report = verify_sexp(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in ["mathcomp.ssreflect.seq.drop", "SerTop.drop_computes"] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified (fallbacks: {:?})",
                report.axiom_fallback_names
            );
        }
        // Negative control: `drop 1 [0;1] = [0;1]` (the no-op identity artifact
        // a rotation/projection off-by-one would compute) is Coq-FALSE.
        let bad_theorem = format!(
            "(CoqConstant SerTop.drop_computes (App (Ind Coq.Init.Logic.eq 0) {listnat} {call} {lst}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {listnat} {lst}))"
        );
        let bad = format!(
            "{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_NAT}\n{RAW_DUMP_LIST}\n{RAW_DUMP_SEQ_DROP}\n{bad_theorem}"
        );
        let neg = verify_sexp(&bad);
        assert!(
            !neg.kernel_verified_names
                .contains(&"SerTop.drop_computes".to_string()),
            "drop 1 [0;1] = [0;1] must be REJECTED (no-op identity mistranslation)"
        );
    }

    /// Reduction parity on an OPEN successor — the exact conversion the
    /// `ssrnat` masked-seed cluster needs (`leqnn`/`ltnS`/`subSS`: one
    /// fix/iota step `sub (S n) (S n) → sub n n` where the successor head
    /// is over a LOCAL variable). With the constructor-reconstruction
    /// substitution the two sides reduce to recursor applications with
    /// IDENTICAL (closed) minors, so `eq_refl (sub n n)` checks against
    /// `sub (S n) (S n) = sub n n`.
    #[test]
    fn test_real_dump_nat_sub_open_successor_reduction_parity() {
        let nat_t = "(Ind Coq.Init.Datatypes.nat 0)";
        let s_of_rel0 = "(App (Construct Coq.Init.Datatypes.nat 0 1) (Rel 0))";
        let theorem = format!(
            "(CoqConstant SerTop.sub_succ_succ \
             (Prod n {nat_t} (App (Ind Coq.Init.Logic.eq 0) {nat_t} \
             (App (Const Coq.Init.Nat.sub) {s_of_rel0} {s_of_rel0}) \
             (App (Const Coq.Init.Nat.sub) (Rel 0) (Rel 0)))) \
             (Lambda n {nat_t} (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} \
             (App (Const Coq.Init.Nat.sub) (Rel 0) (Rel 0)))))"
        );
        let input = format!("{RAW_DUMP_LOGIC_EQ}\n{RAW_DUMP_NAT}\n{RAW_DUMP_NAT_SUB}\n{theorem}");
        let report = verify_sexp(&input);
        assert!(
            report
                .kernel_verified_names
                .contains(&"SerTop.sub_succ_succ".to_string()),
            "sub (S n) (S n) = sub n n by eq_refl must be KernelVerified \
             (fallbacks: {:?})",
            report.axiom_fallback_names
        );
    }

    /// Select corpus-dump declarations BY NAME from
    /// `data/corpora/coq-sexp/<dir>` (one decl per line; name-keyed so a
    /// re-dump inserting siblings cannot silently shift the pick). Returns
    /// `None` (callers SKIP loudly) when the local corpus is absent.
    fn corpus_pick(dir: &str, module: &str, names: &[&str]) -> Option<String> {
        let data = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../data/corpora/coq-sexp")
                .join(dir)
                .join(format!("{module}.sexp")),
        )
        .ok()?;
        Some(
            names
                .iter()
                .map(|&want| {
                    data.lines()
                        .find(|l| {
                            l.strip_prefix("(CoqConstant ")
                                .or_else(|| l.strip_prefix("(CoqInductive "))
                                .or_else(|| l.strip_prefix("(CoqAxiom "))
                                .and_then(|rest| rest.strip_prefix(want))
                                .is_some_and(|after| after.starts_with(' '))
                        })
                        .unwrap_or_else(|| panic!("decl {want} not found in {dir}/{module}"))
                        .to_string()
                })
                .collect::<Vec<_>>()
                .join("\n"),
        )
    }

    /// Compact-dialect closed `nat` numeral (`S^n O`).
    fn nat_lit(n: u64) -> String {
        let mut out = "(Construct Coq.Init.Datatypes.nat 0 0)".to_string();
        for _ in 0..n {
            out = format!("(App (Construct Coq.Init.Datatypes.nat 0 1) {out})");
        }
        out
    }

    /// Semantically-faithful raw stand-in for `mathcomp.ssreflect.ssrnat.leq`
    /// (`λ m n. eqn (subn m n) O` — mathcomp's `m - n == 0` with the raw
    /// nat decidable equality in place of the generic `eq_op`, whose
    /// `eqtype`/Hierarchy-Builder closure is out of scope for a unit-test
    /// fixture; extensionally identical, and `modn`'s guard only needs it to
    /// REDUCE on closed input). The real corpus imports the real chain.
    const LEQ_STANDIN: &str = "(CoqConstant mathcomp.ssreflect.ssrnat.leq \
        (Prod ((binder_name (Name (Id m))) (binder_relevance Relevant)) \
          (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) \
          (Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) \
            (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) \
            (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ())))))) \
        (Lambda ((binder_name (Name (Id m))) (binder_relevance Relevant)) \
          (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) \
          (Lambda ((binder_name (Name (Id n))) (binder_relevance Relevant)) \
            (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) \
            (App (Const ((Constant (KerName (MPfile (DirPath ((Id ssrnat) (Id ssreflect) (Id mathcomp)))) (Id eqn)) ()) (Instance (() ())))) \
              ((App (Const ((Constant (KerName (MPfile (DirPath ((Id ssrnat) (Id ssreflect) (Id mathcomp)))) (Id subn)) ()) (Instance (() ())))) \
                 ((Rel 2) (Rel 1))) \
               (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) 1) (Instance (() ())))))))))";

    /// Dependency closure for the mathcomp `div` measure-recursion tower
    /// (`edivn_rec`/`modn_rec`/`modn`/`gcdn_rec`), stdlib prefix first.
    /// `None` = local corpus absent.
    fn mathcomp_div_measure_closure() -> Option<String> {
        Some(format!(
            "{}\n{}\n{}\n{}\n{}\n{}",
            corpus_pick(
                "stdlib",
                "Coq.Init.Datatypes",
                &[
                    "Coq.Init.Datatypes.nat",
                    "Coq.Init.Datatypes.bool",
                    "Coq.Init.Datatypes.unit",
                    "Coq.Init.Datatypes.prod",
                ],
            )?,
            corpus_pick("stdlib", "Coq.Init.Logic", &["Coq.Init.Logic.eq"])?,
            corpus_pick(
                "stdlib",
                "Coq.Init.Nat",
                &["Coq.Init.Nat.sub", "Coq.Init.Nat.pred"],
            )?,
            corpus_pick(
                "mathcomp",
                "mathcomp.ssreflect.ssrnat",
                &[
                    "mathcomp.ssreflect.ssrnat.subn_rec",
                    "mathcomp.ssreflect.ssrnat.subn",
                    "mathcomp.ssreflect.ssrnat.eqn",
                ],
            )?,
            LEQ_STANDIN,
            corpus_pick(
                "mathcomp",
                "mathcomp.ssreflect.div",
                &[
                    "mathcomp.ssreflect.div.edivn_rec",
                    "mathcomp.ssreflect.div.modn_rec",
                    "mathcomp.ssreflect.div.modn",
                    "mathcomp.ssreflect.div.gcdn_rec",
                ],
            )?,
        ))
    }

    /// MEASURE→FUEL (shape A): the REAL `mathcomp.ssreflect.div.edivn_rec` /
    /// `modn_rec` — `Fixpoint … := if m - d is m'.+1 then …` recursion on the
    /// predecessor of a COMPUTED subtraction (the prior value-less wall
    /// "Fix: match discriminant is not the structural argument") — translate
    /// through the fuel encoding, kernel-verify, and COMPUTE Coq's values:
    /// `edivn_rec 1 7 0 = (3, 1)` (euclidean 7 ÷ 2, four iterations threading
    /// the quotient accumulator) and `modn_rec 1 7 = 1`. Negative control:
    /// the wrong quotient `(2, 1)` must be REJECTED — semantic (extensional)
    /// correctness is exactly what the kernel cannot arbitrate, so the
    /// compute pin is mandatory (the `sub 1 1` fidelity lesson).
    #[test]
    fn test_real_dump_edivn_modn_rec_measure_fuel_computes() {
        let Some(closure) = mathcomp_div_measure_closure() else {
            println!("SKIP: local Coq corpus dump not present");
            return;
        };
        let nat_t = "(Ind Coq.Init.Datatypes.nat 0)";
        let pair_t = format!("(App (Ind Coq.Init.Datatypes.prod 0) {nat_t} {nat_t})");
        let pair = |a: &str, b: &str| {
            format!("(App (Construct Coq.Init.Datatypes.prod 0 0) {nat_t} {nat_t} {a} {b})")
        };
        let (zero, one, seven) = (nat_lit(0), nat_lit(1), nat_lit(7));
        let ediv_call =
            format!("(App (Const mathcomp.ssreflect.div.edivn_rec) {one} {seven} {zero})");
        let good_pair = pair(&nat_lit(3), &one);
        let theorem = format!(
            "(CoqConstant SerTop.edivn_rec_computes \
             (App (Ind Coq.Init.Logic.eq 0) {pair_t} {ediv_call} {good_pair}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {pair_t} {good_pair}))"
        );
        let modn_call = format!("(App (Const mathcomp.ssreflect.div.modn_rec) {one} {seven})");
        let theorem2 = format!(
            "(CoqConstant SerTop.modn_rec_computes \
             (App (Ind Coq.Init.Logic.eq 0) {nat_t} {modn_call} {one}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} {one}))"
        );
        let input = format!("{closure}\n{theorem}\n{theorem2}");
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "the div-tower closure must translate: {:?}",
            stats.value_failure_reasons
        );
        let report = verify_sexp(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in [
            "mathcomp.ssreflect.div.edivn_rec",
            "mathcomp.ssreflect.div.modn_rec",
            "SerTop.edivn_rec_computes",
            "SerTop.modn_rec_computes",
        ] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified (fallbacks: {:?})",
                report.axiom_fallback_names
            );
        }
        // Negative control: the WRONG quotient. A fuel translation that
        // mis-threads the accumulator or bottoms out early computes a
        // different pair — only Coq's (3, 1) may check.
        let bad_pair = pair(&nat_lit(2), &one);
        let bad_theorem = format!(
            "(CoqConstant SerTop.edivn_rec_computes \
             (App (Ind Coq.Init.Logic.eq 0) {pair_t} {ediv_call} {bad_pair}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {pair_t} {bad_pair}))"
        );
        let neg = verify_sexp(&format!("{closure}\n{bad_theorem}"));
        assert!(
            !neg.kernel_verified_names
                .contains(&"SerTop.edivn_rec_computes".to_string()),
            "edivn_rec 1 7 0 = (2, 1) must be REJECTED (Coq computes (3, 1))"
        );
    }

    /// MEASURE→FUEL (LetIn + chained certificate): the REAL
    /// `mathcomp.ssreflect.div.gcdn_rec` —
    /// `let n' := n %% m in if n' is 0 then m else
    ///  if m - n'.-1 is m'.+1 then gcdn_rec (m' %% n') n' else n'`
    /// (self-call on a modulo of the predecessor of a computed subtraction;
    /// the certificate chains `subn ≤` → `S`-branch `<` → `modn ≤`) —
    /// translates, kernel-verifies, and COMPUTES `gcdn_rec 6 4 = 2` through
    /// the fuel-encoded `modn_rec` beneath it. Negative control:
    /// `gcdn_rec 6 4 = 3` must be REJECTED.
    #[test]
    fn test_real_dump_gcdn_rec_measure_fuel_computes() {
        let Some(closure) = mathcomp_div_measure_closure() else {
            println!("SKIP: local Coq corpus dump not present");
            return;
        };
        let nat_t = "(Ind Coq.Init.Datatypes.nat 0)";
        let call = format!(
            "(App (Const mathcomp.ssreflect.div.gcdn_rec) {} {})",
            nat_lit(6),
            nat_lit(4)
        );
        let two = nat_lit(2);
        let theorem = format!(
            "(CoqConstant SerTop.gcdn_rec_computes \
             (App (Ind Coq.Init.Logic.eq 0) {nat_t} {call} {two}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} {two}))"
        );
        let input = format!("{closure}\n{theorem}");
        let report = verify_sexp(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in [
            "mathcomp.ssreflect.div.gcdn_rec",
            "SerTop.gcdn_rec_computes",
        ] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified (fallbacks: {:?})",
                report.axiom_fallback_names
            );
        }
        let three = nat_lit(3);
        let bad_theorem = format!(
            "(CoqConstant SerTop.gcdn_rec_computes \
             (App (Ind Coq.Init.Logic.eq 0) {nat_t} {call} {three}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} {three}))"
        );
        let neg = verify_sexp(&format!("{closure}\n{bad_theorem}"));
        assert!(
            !neg.kernel_verified_names
                .contains(&"SerTop.gcdn_rec_computes".to_string()),
            "gcdn_rec 6 4 = 3 must be REJECTED (Coq computes 2)"
        );
    }

    /// MEASURE→FUEL (shape B): the REAL `Coq.Init.Nat.gcd` — the match IS on
    /// the struct argument but the self-call recurses on the COMPUTED
    /// `b mod a'.+1` (the prior wall "Fix: self-call struct argument is not
    /// a recursive field"; the certificate uses the modulo-by-manifest-
    /// successor rule) — translates, kernel-verifies, and COMPUTES:
    /// `gcd 6 4 = 2`, and `gcd 0 5 = 5` pins the FUEL-0 arm (the dummy fills
    /// only the unreachable S-branch; the O-branch value flows through
    /// unchanged — a dummy leak would return 0 here). Negative control:
    /// `gcd 6 4 = 1` must be REJECTED.
    #[test]
    fn test_real_dump_nat_gcd_measure_fuel_computes() {
        let closure = (|| {
            Some(format!(
                "{}\n{}\n{}",
                corpus_pick(
                    "stdlib",
                    "Coq.Init.Datatypes",
                    &[
                        "Coq.Init.Datatypes.nat",
                        "Coq.Init.Datatypes.prod",
                        "Coq.Init.Datatypes.snd",
                    ],
                )?,
                corpus_pick("stdlib", "Coq.Init.Logic", &["Coq.Init.Logic.eq"])?,
                corpus_pick(
                    "stdlib",
                    "Coq.Init.Nat",
                    &[
                        "Coq.Init.Nat.sub",
                        "Coq.Init.Nat.divmod",
                        "Coq.Init.Nat.modulo",
                        "Coq.Init.Nat.gcd",
                    ],
                )?,
            ))
        })();
        let Some(closure) = closure else {
            println!("SKIP: local Coq corpus dump not present");
            return;
        };
        let nat_t = "(Ind Coq.Init.Datatypes.nat 0)";
        let two = nat_lit(2);
        let call = format!(
            "(App (Const Coq.Init.Nat.gcd) {} {})",
            nat_lit(6),
            nat_lit(4)
        );
        let theorem = format!(
            "(CoqConstant SerTop.gcd_computes \
             (App (Ind Coq.Init.Logic.eq 0) {nat_t} {call} {two}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} {two}))"
        );
        let five = nat_lit(5);
        let call0 = format!("(App (Const Coq.Init.Nat.gcd) {} {five})", nat_lit(0));
        let theorem0 = format!(
            "(CoqConstant SerTop.gcd_zero_computes \
             (App (Ind Coq.Init.Logic.eq 0) {nat_t} {call0} {five}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} {five}))"
        );
        let input = format!("{closure}\n{theorem}\n{theorem0}");
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "the gcd closure must translate: {:?}",
            stats.value_failure_reasons
        );
        // CUMULATIVE lane (the corpus gate's lane, `prelude.set_cumulative(true)`):
        // `modulo` projects the `nat * nat` result of `divmod` through `snd`,
        // which eliminates the template-poly `prod` recursor at a `Type` motive.
        // That large elimination is granted ONLY on Coq's cumulative
        // re-verification lane (parametric singleton elimination); the
        // non-cumulative `verify_sexp` renders the poly `prod` recursor
        // Prop-only, so `snd`/`modulo` fall to a masked fallback there. The
        // computational `gcd` assertions below are lane-independent.
        let report = verify_sexp_cumulative(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in [
            "Coq.Init.Nat.gcd",
            "SerTop.gcd_computes",
            "SerTop.gcd_zero_computes",
        ] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified (fallbacks: {:?})",
                report.axiom_fallback_names
            );
        }
        let one = nat_lit(1);
        let bad_theorem = format!(
            "(CoqConstant SerTop.gcd_computes \
             (App (Ind Coq.Init.Logic.eq 0) {nat_t} {call} {one}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} {one}))"
        );
        let neg = verify_sexp_cumulative(&format!("{closure}\n{bad_theorem}"));
        assert!(
            !neg.kernel_verified_names
                .contains(&"SerTop.gcd_computes".to_string()),
            "gcd 6 4 = 1 must be REJECTED (Coq computes 2)"
        );
    }

    /// MEASURE→FUEL through a KerPair ALIAS: the REAL
    /// `Coq.Arith.PeanoNat.Nat.gcd` — the same Fix as `Coq.Init.Nat.gcd` but
    /// expanded from `Include Coq.Init.Nat`, so its `b mod a'.+1` self-call
    /// references `modulo` under the USER spelling
    /// `Coq.Arith.PeanoNat.Nat.modulo` (canonical `Coq.Init.Nat.modulo`). The
    /// measure certificate's head match is canonical-aware
    /// ([`raw_const_head_in`]), so the modulo-by-manifest-successor rule fires
    /// on the alias, the fuel translation lands, and it COMPUTES: `gcd 6 4 = 2`
    /// (accepts) with `gcd 0 5 = 5` pinning the FUEL-0 arm (no dummy leak).
    /// Negative control: `gcd 6 4 = 1` must be REJECTED. This is the exact
    /// census shape that fell to a clean type-only stand-in before the
    /// canonical head match.
    #[test]
    fn test_real_dump_peanonat_aliased_gcd_measure_fuel_computes() {
        let closure = (|| {
            Some(format!(
                "{}\n{}\n{}\n{}",
                corpus_pick(
                    "stdlib",
                    "Coq.Init.Datatypes",
                    &[
                        "Coq.Init.Datatypes.nat",
                        "Coq.Init.Datatypes.prod",
                        "Coq.Init.Datatypes.snd",
                    ],
                )?,
                corpus_pick("stdlib", "Coq.Init.Logic", &["Coq.Init.Logic.eq"])?,
                corpus_pick(
                    "stdlib",
                    "Coq.Init.Nat",
                    &[
                        "Coq.Init.Nat.sub",
                        "Coq.Init.Nat.divmod",
                        "Coq.Init.Nat.modulo",
                    ],
                )?,
                // The ALIASED copy — its inner `modulo` carries the
                // `Coq.Arith.PeanoNat.Nat.modulo` user spelling, which
                // `resolve_kerpair_name` maps to the provided canonical
                // `Coq.Init.Nat.modulo`.
                corpus_pick(
                    "stdlib",
                    "Coq.Arith.PeanoNat",
                    &["Coq.Arith.PeanoNat.Nat.gcd"],
                )?,
            ))
        })();
        let Some(closure) = closure else {
            println!("SKIP: local Coq corpus dump not present");
            return;
        };
        let nat_t = "(Ind Coq.Init.Datatypes.nat 0)";
        let two = nat_lit(2);
        let call = format!(
            "(App (Const Coq.Arith.PeanoNat.Nat.gcd) {} {})",
            nat_lit(6),
            nat_lit(4)
        );
        let theorem = format!(
            "(CoqConstant SerTop.pgcd_computes \
             (App (Ind Coq.Init.Logic.eq 0) {nat_t} {call} {two}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} {two}))"
        );
        let five = nat_lit(5);
        let call0 = format!(
            "(App (Const Coq.Arith.PeanoNat.Nat.gcd) {} {five})",
            nat_lit(0)
        );
        let theorem0 = format!(
            "(CoqConstant SerTop.pgcd_zero_computes \
             (App (Ind Coq.Init.Logic.eq 0) {nat_t} {call0} {five}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} {five}))"
        );
        let input = format!("{closure}\n{theorem}\n{theorem0}");
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "the aliased gcd closure must translate: {:?}",
            stats.value_failure_reasons
        );
        // CUMULATIVE lane — see `test_real_dump_nat_gcd_measure_fuel_computes`:
        // `modulo`'s `snd` projection large-eliminates the template-poly `prod`
        // recursor at a `Type` motive, granted only on Coq's cumulative lane.
        let report = verify_sexp_cumulative(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        for name in [
            "Coq.Arith.PeanoNat.Nat.gcd",
            "SerTop.pgcd_computes",
            "SerTop.pgcd_zero_computes",
        ] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must be KernelVerified (fallbacks: {:?})",
                report.axiom_fallback_names
            );
        }
        let one = nat_lit(1);
        let bad_theorem = format!(
            "(CoqConstant SerTop.pgcd_computes \
             (App (Ind Coq.Init.Logic.eq 0) {nat_t} {call} {one}) \
             (App (Construct Coq.Init.Logic.eq 0 0) {nat_t} {one}))"
        );
        let neg = verify_sexp_cumulative(&format!("{closure}\n{bad_theorem}"));
        assert!(
            !neg.kernel_verified_names
                .contains(&"SerTop.pgcd_computes".to_string()),
            "aliased gcd 6 4 = 1 must be REJECTED (Coq computes 2)"
        );
    }

    /// FAIL-CLOSED: the fuel translation fires ONLY behind the strict-
    /// decrease certificate. `modn_rec` with its `subn` discriminant head
    /// swapped to a head OUTSIDE the pinned arithmetic-fact table (`addn` —
    /// no `≤`-first-argument fact) must translate to NO value (the honest
    /// discriminant reject → clean type-only axiom), never a fabricated
    /// fuel encoding.
    #[test]
    fn test_measure_fuel_requires_decrease_certificate() {
        let picked = corpus_pick("stdlib", "Coq.Init.Datatypes", &["Coq.Init.Datatypes.nat"]).zip(
            corpus_pick(
                "mathcomp",
                "mathcomp.ssreflect.div",
                &["mathcomp.ssreflect.div.modn_rec"],
            ),
        );
        let Some((nat, modn_rec)) = picked else {
            println!("SKIP: local Coq corpus dump not present");
            return;
        };
        let swapped = modn_rec.replace("(Id subn)", "(Id addn)");
        assert_ne!(swapped, modn_rec, "the discriminant head swap must hit");
        let input = format!("{nat}\n{swapped}");
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 1,
            "the non-decreasing variant must DROP its value: {:?}",
            stats.value_failure_reasons
        );
        assert!(
            stats
                .value_failure_reasons
                .iter()
                .any(|(name, reason)| name.contains("modn_rec") && reason.contains("discriminant")),
            "the honest discriminant reject must surface: {:?}",
            stats.value_failure_reasons
        );
    }

    /// D5 acceptance — the ORIGINAL failing constant: the REAL
    /// `Coq.Init.Decimal.internal_uint_dec_bl` (whose kernel check needs
    /// `uint_beq` to genuinely reduce) kernel-verifies once `uint_beq`
    /// translates through the general fix encoding. Reads the local corpus
    /// dump (`data/corpora/coq-sexp/stdlib`, not in git) and SKIPS loudly
    /// when it is absent.
    #[test]
    fn test_real_dump_internal_uint_dec_bl_kernel_verifies() {
        let base = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../data/corpora/coq-sexp/stdlib");
        if !base.join("Coq.Init.Decimal.sexp").exists() {
            println!("SKIP: local Coq corpus dump not present");
            return;
        }
        // Select declarations BY NAME (not line number): the dump writes one
        // decl per line, but a re-dump can insert siblings (e.g. the `Variant`
        // inductives `signed_int`/`decimal`) and shift every line, so a
        // line-indexed pick silently grabs the wrong constant.
        let pick = |module: &str, names: &[&str]| -> String {
            let data = std::fs::read_to_string(base.join(format!("{module}.sexp")))
                .expect("corpus module readable");
            names
                .iter()
                .map(|&want| {
                    data.lines()
                        .find(|l| {
                            l.strip_prefix("(CoqConstant ")
                                .or_else(|| l.strip_prefix("(CoqInductive "))
                                .or_else(|| l.strip_prefix("(CoqAxiom "))
                                .and_then(|rest| rest.strip_prefix(want))
                                .is_some_and(|after| after.starts_with(' '))
                        })
                        .unwrap_or_else(|| panic!("decl {want} not found in {module}"))
                        .to_string()
                })
                .collect::<Vec<_>>()
                .join("\n")
        };
        let input = format!(
            "{}\n{}\n{}",
            pick("Coq.Init.Datatypes", &["Coq.Init.Datatypes.bool"]),
            pick(
                "Coq.Init.Logic",
                &[
                    "Coq.Init.Logic.True",
                    "Coq.Init.Logic.False",
                    "Coq.Init.Logic.False_ind",
                    "Coq.Init.Logic.eq",
                    "Coq.Init.Logic.eq_ind",
                ],
            ),
            pick(
                "Coq.Init.Decimal",
                &[
                    "Coq.Init.Decimal.uint",
                    "Coq.Init.Decimal.uint_rect",
                    "Coq.Init.Decimal.uint_ind",
                    "Coq.Init.Decimal.uint_rec",
                    "Coq.Init.Decimal.uint_beq",
                    "Coq.Init.Decimal.internal_uint_dec_bl",
                ],
            ),
        );
        let report = verify_sexp(&input);
        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"Coq.Init.Decimal.internal_uint_dec_bl".to_string()),
            "internal_uint_dec_bl must be KernelVerified (fallbacks: {:?})",
            report.axiom_fallback_names
        );
    }

    /// PIN (well-founded recursion lane — non-uniform-parameter demotion,
    /// landed 2026-07-05, see the module doc): the REAL `Coq.Init.Wf.Acc` dump
    /// declares `NumParams 3` (`A`, `R`, **`x`**) where `x` is NON-UNIFORM —
    /// `Acc_intro`'s recursive field ends in `Acc A R y`, `y ≠ x`. The importer
    /// now DEMOTES `x` to an index (`num_params 3 → 2`, the Lean-shaped `Acc`),
    /// so the checked `add_inductive` family replay ACCEPTS it and `Acc.0` mints
    /// KernelVerified with a foundational-only axiom profile. The exact-
    /// parameter-spine rejection (`does not match declared parameter`) must no
    /// longer appear. Reads the local corpus dump (not in git); SKIPS loudly
    /// when absent.
    #[test]
    fn test_real_dump_acc_nonuniform_param_demotes_and_verifies() {
        let base = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../data/corpora/coq-sexp/stdlib");
        let path = base.join("Coq.Init.Wf.sexp");
        if !path.exists() {
            println!("SKIP: local Coq corpus dump not present");
            return;
        }
        let data = std::fs::read_to_string(&path).expect("corpus module readable");
        // Acc inductive + its constructor, selected by name (re-dump-robust).
        let line_of = |want: &str| -> &str {
            data.lines()
                .find(|l| {
                    l.strip_prefix("(CoqConstant ")
                        .or_else(|| l.strip_prefix("(CoqInductive "))
                        .and_then(|rest| rest.strip_prefix(want))
                        .is_some_and(|after| after.starts_with(' '))
                })
                .unwrap_or_else(|| panic!("decl {want} not found in Coq.Init.Wf"))
        };
        let report = verify_sexp(line_of("Coq.Init.Wf.Acc"));
        // The parameter-spine rejection must be gone: the demotion turned the
        // non-uniform `x` into an index, so the replay no longer complains.
        assert!(
            !report
                .failures
                .iter()
                .any(|(_, reason)| reason.contains("does not match declared parameter")),
            "non-uniform-parameter demotion must eliminate the exact-parameter-\
             spine rejection, got: {:?}",
            report.failures
        );
        // Acc now replays cleanly and mints KernelVerified.
        assert!(
            report
                .kernel_verified_names
                .contains(&"Coq.Init.Wf.Acc.0".to_string()),
            "Acc.0 must be KernelVerified after the demotion (failures: {:?}, \
             fallbacks: {:?})",
            report.failures,
            report.axiom_fallback_names
        );
    }

    #[test]
    fn test_zeta_reduce_ctor_telescope_pure_prod_is_none() {
        // A pure-Prod telescope (every previously-working constructor) must
        // pass through untouched.
        let ty = parse_sexp("(Prod A (Sort Set) (Prod x (Rel 0) (Ind I 0)))")
            .expect("should parse dialect ctor type");
        assert!(
            zeta_reduce_ctor_telescope(&ty).is_none(),
            "pure-Prod telescope must not be rewritten"
        );
    }

    #[test]
    fn test_zeta_reduce_ctor_telescope_letin_substituted() {
        // (Prod A Set (LetIn b := Rel 0 : Set in (Prod c (Rel 0) (Ind I 0))))
        // — the let binds `b := A`; field `c : b` must become `c : A`.
        let ty = parse_sexp(
            "(Prod A (Sort Set) (LetIn b (Rel 0) (Sort Set) (Prod c (Rel 0) (Ind I 0))))",
        )
        .expect("should parse dialect ctor type");
        let (reduced, flags) =
            zeta_reduce_ctor_telescope(&ty).expect("LetIn telescope must reduce");
        assert_eq!(flags, vec![false, true, false], "decl_is_let flags");
        let expected = parse_sexp("(Prod A (Sort Set) (Prod c (Rel 0) (Ind I 0)))")
            .expect("should parse expected reduction");
        assert_eq!(reduced, expected, "zeta must inline the let into the field");
    }

    #[test]
    fn test_zeta_reduce_arity_telescope_pure_prod_is_none() {
        // A pure-Π arity (every non-HB-record inductive) must pass through
        // untouched — byte-identical, add-only scope.
        let arity = parse_sexp("(Prod A (Sort Set) (Prod n (Rel 0) (Sort Set)))")
            .expect("should parse dialect arity");
        assert!(
            zeta_reduce_arity_telescope(&arity).is_none(),
            "pure-Π arity must not be rewritten"
        );
    }

    #[test]
    fn test_zeta_reduce_arity_telescope_spine_letin_matches_ctor_prefix() {
        // The HB `mixin_of` shape: a packing `let` interleaved in the leading Π
        // PARAMETER spine (`∀ A, let b := A in ∀ (c : b), Set`, num_params = 2).
        // count_pi_args stops at the LetIn (arity 1) but num_params is 2; the
        // arity must ζ-reduce to a pure 2-Π telescope, and its parameter prefix
        // must match the identically-reduced constructor's — the consistency
        // `check_block_agreement` demands.
        let arity = parse_sexp(
            "(Prod A (Sort Set) (LetIn b (Rel 0) (Sort Set) (Prod c (Rel 0) (Sort Set))))",
        )
        .expect("should parse spine-LetIn arity");
        let reduced_arity =
            zeta_reduce_arity_telescope(&arity).expect("spine-LetIn arity must reduce");
        let expected_arity = parse_sexp("(Prod A (Sort Set) (Prod c (Rel 0) (Sort Set)))")
            .expect("expected pure-Π arity");
        assert_eq!(
            reduced_arity, expected_arity,
            "arity ζ must drop the spine let"
        );

        // The constructor is reduced by the SAME shared spine reducer; its first
        // num_params (2) Π binders must equal the arity's parameter prefix.
        let ctor = parse_sexp(
            "(Prod A (Sort Set) (LetIn b (Rel 0) (Sort Set) \
             (Prod c (Rel 0) (App (Ind Wrap 0) (Rel 2) (Rel 0)))))",
        )
        .expect("should parse spine-LetIn ctor");
        let (reduced_ctor, _flags) =
            zeta_reduce_ctor_telescope(&ctor).expect("spine-LetIn ctor must reduce");
        // Peel the leading 2 params of both and require identical binder domains.
        let arity_params = dialect_peel_prods(&reduced_arity).0;
        let ctor_params = dialect_peel_prods(&reduced_ctor).0;
        assert!(
            arity_params.len() >= 2 && ctor_params.len() >= 2,
            "both must expose ≥ num_params leading Π binders"
        );
        assert_eq!(
            arity_params[..2].iter().map(|(_, t)| t).collect::<Vec<_>>(),
            ctor_params[..2].iter().map(|(_, t)| t).collect::<Vec<_>>(),
            "arity and ctor must ζ-reduce IDENTICAL parameter domains"
        );
    }

    #[test]
    fn test_lift_arity_codomain_universe_prop_and_named_noop() {
        // A `Prop` codomain is never a Type over-collapse → no lift (Num.mixin_of).
        let prop_arity = parse_sexp("(Prod A (Sort Set) (Prod c (Rel 0) (Sort Prop)))")
            .expect("should parse Prop-codomain arity");
        let prop_cic = sexp_to_cic(&prop_arity).expect("cic");
        assert!(
            lift_arity_codomain_universe(&prop_arity, &prop_cic).is_none(),
            "Prop codomain must not be lifted"
        );
        // A plain `Set` codomain collapses to a concrete level equal to its flat
        // scale → no strict excess → no lift.
        let set_arity =
            parse_sexp("(Prod A (Sort Set) (Sort Set))").expect("should parse Set-codomain arity");
        let set_cic = sexp_to_cic(&set_arity).expect("cic");
        assert!(
            lift_arity_codomain_universe(&set_arity, &set_cic).is_none(),
            "a faithfully-collapsed Set codomain must not be lifted"
        );
    }

    /// End-to-end kernel-arbitrated compute test for the spine-LetIn arity
    /// lever: a synthetic HB-record-shaped inductive whose arity interleaves a
    /// packing `let` in its leading Π parameter spine imports, ζ-reduces, and
    /// its whole family genuinely `KernelVerified`s through checked
    /// `add_inductive` (the family-replay guard `num_params > arity` no longer
    /// trips). Without the lever this family falls to a stand-in (never KV).
    #[test]
    fn test_spine_letin_record_family_kernel_verifies() {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;

        // `Wrap (A : Set) (c : A) : Set` with a spine `let b := A` before the
        // second parameter, and `Wrap.mk : (A : Set) (c : A) -> Wrap A c`.
        let sexp = "(CoqInductive Wrap 0 \
            (Prod A (Sort Set) (LetIn b (Rel 0) (Sort Set) (Prod c (Rel 0) (Sort Set)))) \
            (NumParams 2) \
            (Ctor Wrap.mk (Prod A (Sort Set) (LetIn b (Rel 0) (Sort Set) \
              (Prod c (Rel 0) (App (Ind Wrap 0) (Rel 2) (Rel 0)))))))";
        let mut w = ShardWriter::new();
        CoqImporter.import_sexp(sexp, &mut w).expect("import");
        let mut buf = Vec::new();
        w.write(&mut buf).expect("write shard");
        let reader = crate::shard::ShardReader::from_bytes(&buf).expect("read shard");

        // Sanity: the imported arity is a pure 2-Π telescope (spine let dropped).
        let ind = reader
            .constants
            .iter()
            .find(|c| reader.strings[c.name_idx as usize] == "Wrap.0")
            .expect("Wrap.0 present");
        assert_eq!(ind.inductive_decl_num_params(), Some(2));

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).expect("load shard");
        let prelude =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        let report = verify_corpus_incremental(&lib, prelude);

        assert_eq!(
            report.failed, 0,
            "no constant may fail: {:?}",
            report.failures
        );
        assert!(
            report.kernel_verified_names.contains(&"Wrap.0".to_string()),
            "the spine-LetIn record type must be genuinely KernelVerified, got {:?}",
            report.kernel_verified_names
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"Wrap.0.0".to_string()),
            "the constructor must be genuinely KernelVerified, got {:?}",
            report.kernel_verified_names
        );
    }

    /// Negative control (the soundness floor of the lever): if the arity and the
    /// constructor ζ-reduce INCONSISTENT lets (here the constructor binds
    /// `b := Set` where the arity binds `b := A`), the reconstructed parameter
    /// prefixes disagree and the kernel REJECTS the family (`add_inductive`
    /// fails, clean stand-in fallback) — a corrupted ζ-substitution never
    /// silently produces a wrong-but-accepted KernelVerified decl.
    #[test]
    fn test_spine_letin_record_inconsistent_lets_rejected() {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;

        // Arity: `let b := A` so `c : A`. Ctor: `let b := Set` so `c : Set` —
        // the parameter `c`'s domain disagrees with the arity's.
        let sexp = "(CoqInductive Wrap 0 \
            (Prod A (Sort Set) (LetIn b (Rel 0) (Sort Set) (Prod c (Rel 0) (Sort Set)))) \
            (NumParams 2) \
            (Ctor Wrap.mk (Prod A (Sort Set) (LetIn b (Sort Set) (Sort Set) \
              (Prod c (Rel 0) (App (Ind Wrap 0) (Rel 2) (Rel 0)))))))";
        let mut w = ShardWriter::new();
        CoqImporter.import_sexp(sexp, &mut w).expect("import");
        let mut buf = Vec::new();
        w.write(&mut buf).expect("write shard");
        let reader = crate::shard::ShardReader::from_bytes(&buf).expect("read shard");

        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).expect("load shard");
        let prelude =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        let report = verify_corpus_incremental(&lib, prelude);

        assert!(
            !report.kernel_verified_names.contains(&"Wrap.0".to_string()),
            "inconsistent ζ-reduced lets must NOT yield a KernelVerified family: {:?}",
            report.kernel_verified_names
        );
    }

    #[test]
    fn test_zeta_expand_letbound_branch_body_remapped() {
        // Raw telescope: f1 : Set, l := f1 : Set, f2 : l. Raw branch body
        // references the LET binder (SerAPI 1-based `Rel 2` = dialect Rel 1 =
        // `l` under [f1; l; f2]); after zeta the body must reference f1
        // (dialect Rel 1 under the two field binders [f1; f2]).
        let raw_ty = parse_sexp(
            "(Prod f1 (Sort Set) (LetIn l (Rel 0) (Sort Set) (Prod f2 (Rel 0) (Ind I 0))))",
        )
        .expect("should parse raw ctor type");
        let raw_body = parse_sexp("(Rel 2)").expect("should parse raw branch body");
        let names: Vec<String> = ["f1", "l", "f2"].iter().map(|s| s.to_string()).collect();
        let ctx = SerapiNormCtx::default();
        let (field_names, body) = zeta_expand_letbound_branch(
            &raw_ty,
            &[false, true, false],
            &names,
            &[],
            &raw_body,
            &ctx,
            &[],
            2,
        )
        .expect("let-bound branch should zeta-expand");
        assert_eq!(field_names, vec!["f1".to_string(), "f2".to_string()]);
        let expected = parse_sexp("(Rel 1)").expect("should parse expected body");
        assert_eq!(body, expected, "let reference must land on f1");
    }

    #[test]
    fn test_zeta_expand_letbound_branch_binder_count_mismatch_errors() {
        let raw_ty = parse_sexp(
            "(Prod f1 (Sort Set) (LetIn l (Rel 0) (Sort Set) (Prod f2 (Rel 0) (Ind I 0))))",
        )
        .expect("should parse raw ctor type");
        let raw_body = parse_sexp("(Rel 1)").expect("should parse raw branch body");
        let ctx = SerapiNormCtx::default();
        let err = zeta_expand_letbound_branch(
            &raw_ty,
            &[false, true, false],
            &["f1".to_string(), "f2".to_string()], // 2 binders for 3 decls
            &[],
            &raw_body,
            &ctx,
            &[],
            2,
        )
        .expect_err("binder/decl count mismatch must fail closed");
        assert!(
            err.contains("branch binder count"),
            "unexpected error: {err}"
        );
    }

    // -- Nested-match split (`div2` / `even` two-level recursion) ------------

    /// The raw SerAPI `nat` inductive head used inside `Fix` values.
    const RAW_NAT: &str = "(Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) \
         (Id Coq)))) (Id nat)) ()) 0) (Instance (() ()))))";
    /// The raw case-info block for a `nat` match.
    const RAW_NAT_CI: &str = "((ci_ind ((MutInd (KerName (MPfile (DirPath ((Id Datatypes) \
         (Id Init) (Id Coq)))) (Id nat)) ()) 0)) (ci_npar 0) (ci_cstr_ndecls (0 1)) \
         (ci_cstr_nargs (0 1)) (ci_pp_info ((style RegularStyle))))";
    /// Raw `O` / `S` constructors (SerAPI constructor indices are 1-based).
    const RAW_NAT_O: &str = "(Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) \
         (Id Init) (Id Coq)))) (Id nat)) ()) 0) 1) (Instance (() ()))))";
    const RAW_NAT_S: &str = "(Construct ((((MutInd (KerName (MPfile (DirPath ((Id Datatypes) \
         (Id Init) (Id Coq)))) (Id nat)) ()) 0) 2) (Instance (() ()))))";

    /// Build the verbatim corpus `Fix` for `div2 := fix div2 n := match n
    /// with 0 => 0 | S n0 => match n0 with 0 => 0 | S n' => S (div2 n')`,
    /// with the inner self-call's struct argument overridable (`Rel 1` = the
    /// inner field `n'`; `Rel 3` = the outer struct binder `n`).
    fn raw_div2_fix(self_arg: &str) -> String {
        let binder =
            |x: &str| format!("((binder_name (Name (Id {x}))) (binder_relevance Relevant))");
        let rp = format!("((({}) {RAW_NAT}) Relevant)", binder("n"));
        let inner = format!(
            "(Case {RAW_NAT_CI} (Instance (() ())) () {rp} NoInvert (Rel 1) \
             ((() {RAW_NAT_O}) ((({})) (App {RAW_NAT_S} ((App (Rel 4) (({self_arg}))))))))",
            binder("n'")
        );
        let outer = format!(
            "(Case {RAW_NAT_CI} (Instance (() ())) () {rp} NoInvert (Rel 1) \
             ((() {RAW_NAT_O}) ((({})) {inner})))",
            binder("n0")
        );
        format!(
            "(Fix (((0) 0) (({}) ((Prod {} {RAW_NAT} {RAW_NAT})) \
             ((Lambda {} {RAW_NAT} {outer})))))",
            binder("div2"),
            binder("n"),
            binder("n")
        )
    }

    /// Extract `(header, payload)` from a parsed raw `(Fix (h p))`.
    fn raw_fix_parts(fix: &Sexp) -> (Sexp, Sexp) {
        let Sexp::List(items) = fix else {
            panic!("fix must be a list");
        };
        let Sexp::List(hp) = &items[1] else {
            panic!("fix payload must be a list");
        };
        (hp[0].clone(), hp[1].clone())
    }

    /// The `div2` two-level shape splits into the expected 2-body mutual
    /// block: member 0 calls `g` on the outer field, member 1 is the inner
    /// match with the self-call intact on ITS direct field.
    #[test]
    fn test_split_nested_match_fix_div2_builds_mutual_block() {
        let fix = parse_sexp(&raw_div2_fix("Rel 1")).expect("div2 fix must parse");
        let (header, payload) = raw_fix_parts(&fix);
        let (mh, mp) = try_split_nested_match_fix(&header, &payload)
            .expect("div2 shape must split into a mutual block");
        assert_eq!(mh, parse_sexp("((0 0) 0)").unwrap(), "mutual header");
        let Sexp::List(pv) = &mp else {
            panic!("mutual payload must be a list");
        };
        // Shared signature, duplicated verbatim.
        let expect_ty = parse_sexp(&format!(
            "((Prod ((binder_name (Name (Id n))) (binder_relevance Relevant)) \
             {RAW_NAT} {RAW_NAT}) (Prod ((binder_name (Name (Id n))) \
             (binder_relevance Relevant)) {RAW_NAT} {RAW_NAT}))"
        ))
        .unwrap();
        assert_eq!(pv[1], expect_ty, "both members share the fix signature");
        let bodies = match &pv[2] {
            Sexp::List(b) if b.len() == 2 => b,
            other => panic!("expected two mutual bodies, got {other:?}"),
        };
        // Member 0's S-branch: `g n0` — the field in the struct slot, `g` at
        // `Rel(1 + k + 1) = Rel 3` from the branch root.
        let s_branch_body = |body: &Sexp| -> Sexp {
            let Sexp::List(lv) = body else { panic!("body") };
            let Sexp::List(cv) = &lv[3] else {
                panic!("case under the lambda")
            };
            let Sexp::List(bs) = &cv[7] else {
                panic!("branches")
            };
            let Sexp::List(bv) = &bs[1] else {
                panic!("S branch")
            };
            bv[1].clone()
        };
        assert_eq!(
            s_branch_body(&bodies[0]),
            parse_sexp("(App (Rel 3) ((Rel 1)))").unwrap(),
            "member 0 must delegate the nested match to `g` on the field"
        );
        // Member 1: the inner match relocated — self-call on ITS direct field
        // (`f` keeps `Rel 4`: the inserted `g` cancels the removed field).
        assert_eq!(
            s_branch_body(&bodies[1]),
            parse_sexp(&format!("(App {RAW_NAT_S} ((App (Rel 4) ((Rel 1)))))")).unwrap(),
            "member 1 must keep the self-call on the inner field"
        );
    }

    /// An inner match that references the OUTER struct binder cannot be
    /// split (its slot is rebound to the inner scrutinee): fail closed.
    #[test]
    fn test_split_nested_match_fix_rejects_outer_struct_reference() {
        // `Rel 3` at the self-call site is the outer struct binder `n`.
        let fix = parse_sexp(&raw_div2_fix("Rel 3")).expect("fix must parse");
        let (header, payload) = raw_fix_parts(&fix);
        assert!(
            try_split_nested_match_fix(&header, &payload).is_none(),
            "an outer-struct-binder reference inside the inner match must refuse the split"
        );
    }

    /// A nested match WITHOUT a self-call inside it is not a split candidate
    /// (nothing to gain; the general encoder already handles it).
    #[test]
    fn test_split_nested_match_fix_ignores_self_free_nested_match() {
        // Replace the self-call `(App (Rel 4) ((Rel 1)))` with the plain field.
        let src = raw_div2_fix("Rel 1").replace("(App (Rel 4) ((Rel 1)))", "(Rel 1)");
        let fix = parse_sexp(&src).expect("fix must parse");
        let (header, payload) = raw_fix_parts(&fix);
        assert!(
            try_split_nested_match_fix(&header, &payload).is_none(),
            "a self-free nested match must not trigger the split"
        );
    }

    /// End-to-end: the corpus-verbatim `div2` value TRANSLATES through the
    /// nested-match split (no dropped value) and is stamped speculative so
    /// verification fails closed if the kernel rejects the composition.
    #[test]
    fn test_import_div2_two_level_fix_translates_speculatively() {
        let input = format!(
            "(CoqInductive Coq.Init.Datatypes.nat 0 Set\n\
             (Ctor O (Ind Coq.Init.Datatypes.nat 0))\n\
             (Ctor S (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))))\n\
             (CoqConstant SerTop.div2\n\
             (Prod n (Ind Coq.Init.Datatypes.nat 0) (Ind Coq.Init.Datatypes.nat 0))\n\
             {})",
            raw_div2_fix("Rel 1")
        );
        let mut w = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&input, &mut w).unwrap();
        assert_eq!(
            stats.value_translation_failed, 0,
            "div2's value must convert: {:?}",
            stats.value_failure_reasons
        );
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        let (_, c) = reader.lookup_name("SerTop.div2").unwrap();
        assert!(c.has_value(), "div2 must carry the split-encoded value");
        assert!(
            c.profile().has(AxiomProfile::SPECULATIVE_MOTIVE),
            "the split composition must be stamped speculative (fail-closed)"
        );
    }

    #[test]
    fn test_import_functor_speculative_marker_forces_speculative_keeps_value() {
        // A value-bearing `(CoqConstant … <value> Speculative)` — the
        // instantiated-module (functor-application) member marker emitted by
        // the dumper's enumeration prong. The trailing `Speculative` atom must:
        //   (a) NOT change the parsed value (semantic fidelity — the marker is
        //       a pure appended atom; the constant stays a value-bearing
        //       Definition, identical `value_idx` to the unmarked form), and
        //   (b) force `AxiomProfile::SPECULATIVE_MOTIVE` so verify arbitrates it
        //       fail-closed (kernel accepts → KV, rejects → clean type-only).
        let ty = "(Prod x (Sort Prop) (Sort Prop))";
        let value = "(Lambda x (Sort Prop) (Rel 0))";
        let plain = format!("(CoqConstant SerTop.myid {ty} {value})");
        let marked = format!("(CoqConstant SerTop.myid {ty} {value} Speculative)");

        let read_one = |input: &str| {
            let mut w = ShardWriter::new();
            let stats = CoqImporter.import_sexp(input, &mut w).unwrap();
            assert_eq!(
                stats.value_translation_failed, 0,
                "value must convert regardless of the marker: {:?}",
                stats.value_failure_reasons
            );
            let mut buf = Vec::new();
            w.write(&mut buf).unwrap();
            let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
            let (_, c) = reader.lookup_name("SerTop.myid").unwrap();
            (c.has_value(), c.value_idx, c.profile())
        };

        let (plain_hasval, plain_vidx, plain_prof) = read_one(&plain);
        let (marked_hasval, marked_vidx, marked_prof) = read_one(&marked);

        assert!(
            plain_hasval && marked_hasval,
            "both stay value-bearing Definitions"
        );
        assert_eq!(
            plain_vidx, marked_vidx,
            "the marker must NOT change the emitted value (identical value_idx)"
        );
        assert!(
            !plain_prof.has(AxiomProfile::SPECULATIVE_MOTIVE),
            "the unmarked form is NOT speculative"
        );
        assert!(
            marked_prof.has(AxiomProfile::SPECULATIVE_MOTIVE),
            "the Speculative-marked form must be stamped SPECULATIVE_MOTIVE"
        );
    }
}
