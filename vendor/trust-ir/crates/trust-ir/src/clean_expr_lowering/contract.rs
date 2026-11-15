// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! R-L1 Step 3 (verified reflection R, L1 contract tier): the per-kind `Expr`
//! encoder for **L1 contract obligations** — the `Precondition` /
//! `Postcondition` / `LoopInvariant` / `RefinementType` predicate formulas
//! carried on a [`crate::proof::ProofObligation`].
//!
//! This is the contract sibling of the L0 safety encoders
//! ([`crate::clean_expr_lowering::overflow_goal`],
//! [`crate::clean_expr_lowering::divnonzero::divnonzero_goal`], …). Where an L0
//! encoder grounds a node's OWN fields, an L1 encoder grounds a contract
//! obligation's predicate FORMULA: it takes the obligation's
//! [`crate::proof::ProofFormula`] — its ONE SMT-LIB2 text
//! ([`crate::proof::ProofFormula::smtlib_text`]: an `smtlib2` payload, e.g.
//! `(> x 0)`, `(not (= result 0))`, `(and (>= x 0) (<= x 10))`) — and returns
//! the obligation as a `clean_kernel::Expr` so the contract claim is expressed in
//! the kernel's own AST — exactly the CIC grounding the L0 path performs.
//!
//! ## The goal shape (mirrors the L0 `@Eq Bool _ Bool.true` shape)
//!
//! A contract predicate `P` is grounded to a kernel-checkable Bool decision
//!
//! ```text
//! @Eq Bool (<decision procedure for P>) Bool.true
//! ```
//!
//! built only from native prelude reducers (`Nat.ble`, `Nat.beq`, `Bool.and`,
//! `Bool.or`, `Bool.not`) over `Nat` literals — the SAME primitives the L0
//! encoders rely on, so discharge is a kernel reduction with no extra lemmas.
//! The hand proof term `@Eq.refl Bool Bool.true` is accepted by the kernel iff
//! the decision genuinely reduces to `Bool.true`; a predicate that does not hold
//! reduces it to `Bool.false` and the kernel REFUSES — the de Bruijn criterion,
//! no external `.lean`.
//!
//! ## SOUNDNESS — fail-closed
//!
//! Grounding is the path that ultimately stamps `Certified` / `ProofEvidence::
//! CleanCic`, the strictly-stronger-than-`Trusted` tier. It is therefore
//! **fail-closed**: every step returns `None` (no Certified stamp) on anything
//! it cannot fully establish —
//!
//! 1. an obligation kind outside the L1 contract set;
//! 2. a missing predicate formula, one declared of a sort other than `Bool`,
//!    or one that states no single SMT-LIB text (an opaque schema, or an
//!    `smtlib2` payload its `smtlib` rendering contradicts);
//! 3. an SMT-LIB2 shape outside the supported decidable fragment (any unknown
//!    head symbol, a non-literal operand, a wrong arity, free variables, …);
//! 4. a predicate that grounds but the kernel REFUSES to discharge.
//!
//! Only when the predicate fully grounds AND the trusted `clean-kernel` kernel
//! accepts `@Eq.refl Bool Bool.true` against the grounded goal does
//! [`contract_clean_cic_certificate`] mint a `CleanCic` certificate. There is no
//! code path that produces a `CleanCic`/`Certified` result for an ungroundable
//! or undischarged predicate. This mirrors the L0 encoders' `Result<_, _Error>`
//! envelope: an unsupported shape never yields a (wrong or vacuous) goal.
//!
//! ## Module-free vs module-bound grounding
//!
//! Two entry families, split on purpose (WS1.1, finding F-001):
//!
//! * **Module-free** — [`contract_goal`], [`contract_clean_cic_certificate`] and
//!   the [`crate::proof::CleanCicRechecker`] impl of [`KernelCleanCicRechecker`]
//!   ground **literal-only** predicates. A clause containing any non-literal
//!   atom is [`ContractLoweringError::UnsupportedPredicate`]: without the module
//!   there is no way to know what a free name denotes.
//! * **Module-bound** — [`contract_goal_in`], [`contract_clean_cic_certificate_in`],
//!   [`contract_nat_nonneg_obligation_in`] and the
//!   [`crate::proof::ModuleCleanCicRechecker`] impl are the ONLY paths that may
//!   produce the single free-name tautology `∀ x : Nat, Nat.ble 0 x = true`, and
//!   only after [`bind_nat_nonneg`] has bound the clause symbol to an unsigned
//!   integer IR place read at sort `Int`. Before that split the closed goal was
//!   produced from the clause TEXT alone, so `fn f() -> i64 { -1 }` with
//!   `ensures (>= result 0)` reached kernel-`Certified`.
//!
//! The whole module is gated on `clean-expr` (via the parent module in lib.rs)
//! so the default zero-dependency trust-ir format build never references
//! clean-kernel.

use crate::Module;
use crate::proof::clause_typing::{is_smt_simple_symbol, resolve_clause_place, smt_free_symbols};
use crate::proof::{
    ClausePlace, ClauseSort, ExprObligation, ObligationKind, OwnedFormulaSchema, ProofCertificate,
    ProofEvidence, ProofFormula, ProofObligation, SmtSexp, clean_cic_lineage_digest,
    decode_clean_expr_v1, encode_clean_expr_v1, read_smtlib_term,
};
use crate::spec_surface::linked_var_name_problem;
use crate::ty::Ty;
use crate::value::FuncId;
use clean_kernel::{BinderInfo, Expr, Level, Name};

/// Encode one proof term with the exact codec the consumer uses.
fn encode_proof_term(term: &Expr) -> Option<Vec<u8>> {
    encode_clean_expr_v1(term).ok()
}

/// Decode an untrusted proof term canonically and within explicit resource
/// bounds. Whole-slice decode rejects suffix smuggling; re-encoding rejects any
/// alternate wire spelling accepted by serde/bincode.
fn decode_proof_term(bytes: &[u8]) -> Option<Expr> {
    decode_clean_expr_v1(bytes).ok()
}

/// Errors the contract (L1) encoder fails closed with, rather than minting a
/// wrong or vacuous goal for an unsupported obligation kind or predicate shape.
///
/// Manual `Display`/`Error` impls (not `thiserror`): the `trust-ir` crate keeps
/// zero required external dependencies; the `clean-expr` feature adds only
/// `clean-kernel`. Mirrors the sibling per-kind encoders' self-contained error
/// enums (`LoweringError`, `DivNonZeroLoweringError`, …).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ContractLoweringError {
    /// The obligation kind is not one of the L1 contract kinds this encoder
    /// grounds (`Precondition` / `Postcondition` / `LoopInvariant` /
    /// `RefinementType`). Fails closed: a safety / translation-validation
    /// obligation is not a contract predicate and must not reuse this path.
    NotAContractKind(ObligationKind),
    /// The obligation carries no predicate formula at all, so there is nothing
    /// to ground. Fails closed rather than mint a vacuous `true` goal.
    NoFormula,
    /// The predicate s-expression is outside the supported decidable fragment
    /// (unknown head symbol, non-literal operand, wrong arity, free variable,
    /// malformed parse, …). The carried string is the offending sub-expression,
    /// for diagnostics only. Fails closed — the cornerstone of the soundness
    /// argument: an ungroundable predicate yields NO goal and therefore NO
    /// Certified stamp.
    UnsupportedPredicate(String),
}

impl core::fmt::Display for ContractLoweringError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ContractLoweringError::NotAContractKind(kind) => {
                write!(
                    f,
                    "contract obligation: kind {kind:?} is not an L1 contract kind"
                )
            }
            ContractLoweringError::NoFormula => {
                write!(f, "contract obligation: no predicate formula to ground")
            }
            ContractLoweringError::UnsupportedPredicate(s) => {
                write!(
                    f,
                    "contract obligation: predicate {s:?} is outside the grounded fragment"
                )
            }
        }
    }
}

impl std::error::Error for ContractLoweringError {}

/// True iff `kind` is one of the L1 contract kinds whose predicate formula this
/// encoder grounds. A safety / translation / temporal obligation is NOT a
/// contract predicate and must fail closed.
///
/// The table, and why `Termination` / `Ownership` are outside it BY DECISION
/// (WS1.9 DECIDE A), is [`crate::proof::ObligationKindShape::is_grounded_contract_kind`],
/// whose every cell is a proved Trust contract (gate 13). The two-language row
/// `b2.gap.termination_not_kernel_certifiable` holds the same shape, so a
/// grounder that started certifying either kind trips it.
fn is_contract_kind(kind: &ObligationKind) -> bool {
    kind.shape().is_grounded_contract_kind()
}

// ---------------------------------------------------------------------------
// Kernel Bool constructors — the SAME native prelude reducers the L0 encoders
// use, so a grounded contract goal discharges by kernel reduction with no extra
// lemmas.
// ---------------------------------------------------------------------------

/// `Nat.ble a b` — boolean `a <= b` on `Nat`, a native prelude reducer.
fn nat_ble(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.ble"), [a, b])
}

/// `Nat.beq a b` — boolean equality on `Nat`, a native prelude reducer.
fn nat_beq(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.beq"), [a, b])
}

/// `Bool.and a b` — native prelude reducer.
fn bool_and(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.and"), [a, b])
}

/// `Bool.or a b` — native prelude reducer.
fn bool_or(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.or"), [a, b])
}

/// `Bool.not a` — native prelude reducer.
fn bool_not(a: Expr) -> Expr {
    Expr::app(Expr::const_str("Bool.not"), a)
}

/// The "is `Bool.true`" wrapper: `@Eq Bool inner Bool.true`.
///
/// Identical in shape to the L0 encoders' `@Eq Bool _ Bool.{true,false}` goals —
/// the kernel-checkable claim that a Bool decision holds, the same shape
/// trust-certify's "kernel proves the obligation" gate accepts and that
/// `@Eq.refl Bool Bool.true` discharges.
fn bool_is_true(inner: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_str("Bool"), inner, Expr::const_str("Bool.true")],
    )
}

// ---------------------------------------------------------------------------
// The supported fragment, read by trust-ir's ONE SMT-LIB2 reader
// ([`read_smtlib_term`]): a text it refuses (a non-SMT-LIB character such as
// U+3000 or VT, a `'` in a name, a leading-zero numeral, a string, quoted
// symbol or comment, a nesting past the depth bound) grounds NOTHING. This
// module used to tokenize on its own, splitting on Rust `char::is_whitespace`
// and taking any run of other characters as an atom, so
// `(>=\u{3000}5\u{3000}0)` and `(>= x' 0)` were grounded and kernel-replayed
// although no SMT-LIB2 reader reads either text.
//
//   pred  := '(' BOOLOP pred+ ')' | cmp
//   cmp   := '(' CMPOP nat nat ')'           ; CMPOP ∈ { =, <, <=, >, >= }
//   BOOLOP∈ { and, or, not }
//   nat   := SMT-LIB2 numeral
//
// Only ground (literal-operand) comparisons are grounded: a contract predicate
// is groundable iff every leaf is a Nat literal. A free program variable (e.g.
// `x`, `result`) is NOT a literal, so the predicate fails closed — exactly the
// L0 envelope, where the goal is born from concrete node facts and an
// unsupported shape yields no goal.
// ---------------------------------------------------------------------------

/// Read a predicate text as one SMT-LIB2 term, or `None` (fail-closed) for any
/// text [`read_smtlib_term`] refuses.
fn parse_predicate(s: &str) -> Option<SmtSexp<'_>> {
    read_smtlib_term(s).ok()
}

/// A non-negative decimal `Nat` literal, or `None` (fail-closed) for a symbol,
/// a negative number, or anything non-numeric. Free program variables land here
/// and so make the whole predicate ungroundable.
///
/// ASCII DIGITS ONLY. `u64::from_str` also accepts a leading `+`, but in
/// SMT-LIB2 `+1` is a simple SYMBOL (only a leading digit makes a numeral), so
/// reading it as the numeral 1 would let the literal-only path certify
/// `(>= +1 0)` while a consumer that honours the clause's bindings reads it as
/// `<bound place> >= 0` — the F-001 hole through the module-free door.
fn parse_nat_literal(atom: &str) -> Option<u64> {
    if atom.is_empty() || !atom.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    atom.parse::<u64>().ok()
}

// ---------------------------------------------------------------------------
// R-L1 goal item #4, slice 1: a SINGLE free-name Nat non-negativity tautology.
//
// The literal-fixture path above grounds only predicates whose leaves are all
// `Nat` literals. This adds the one predicate over a single free NAME —
//
//     s >= 0        (SMT `(>= s 0)`)  or its normal form
//     0 <= s        (SMT `(<= 0 s)`)
//
// Both ground to the SAME closed kernel proposition
// `∀ x : Nat, @Eq Bool (Nat.ble 0 x) Bool.true`, which the kernel discharges
// with `fun x => @Eq.refl Bool Bool.true` because `Nat.ble 0 x` reduces to
// `Bool.true` for EVERY `x : Nat` (and the kernel REFUSES `Nat.ble 5 x = true`,
// so `s >= 5` cannot mint anything).
//
// WHAT THE KERNEL DOES NOT SEE (finding F-001). The closed proposition
// quantifies over `Nat` and discards the clause symbol, so the kernel judgment
// is true whatever `s` denotes. It is the denotation of the clause only when
// `s` IS a Nat-valued IR place. That is established OUTSIDE the kernel, by
// `bind_nat_nonneg`, from the obligation's owning function, its `FuncTy`, and
// the clause's `bindings`: exactly one binding, naming `s`, at a
// `Param`/`ResultSlot`/`MutParamExit`/`ParamPointeeEntry` place whose IR type
// is an unsigned integer, read at sort `Int`. Only the module-bound entry points run it, so
// only they may produce this goal; the module-free ones refuse the shape.
// The residual denotation lemma — "the Int value of an unsigned w-bit place
// is a Nat" — is recorded in TRUST.md (item 11).
//
// FAIL-CLOSED: the recognizer returns `Some` ONLY for exactly this shape over
// one free name. Anything else — a non-zero bound (`s >= 5`), the wrong
// operator (`s <= 0`, `s = 0`, `s > 0`), a literal on the var side, two
// distinct names, a nested boolean, an atom that is not an SMT simple symbol
// (`-5`, `+1`, `#x00`, `true`) or is a theory function symbol (`and`, `abs`)
// — returns `None`.
// ---------------------------------------------------------------------------

/// The canonical free-var name of the single-var Nat non-negativity tautology.
/// The var is a syntactic SMT symbol; we only ever bind ONE, at type `Nat`.
const NAT_NONNEG_VAR_KEY: &str = "x";

/// True iff `atom` is a syntactic free name: a name trust-ir's one reader
/// reads as a variable ([`linked_var_name_problem`]). That is an SMT simple
/// symbol under the shared grammar `[A-Za-z_][A-Za-z0-9_.]*` and not a
/// reserved word ([`is_smt_simple_symbol`]) — so `-5`, `+1`, `#x00` and
/// `true`, which the former "does not parse as a `u64`" test admitted as free
/// variables, are refused — and no function symbol of the theories the
/// surface draws on (`and`, `not`, `distinct`, `div`, `abs`, `bvadd`,
/// `concat`, …). A clause `(>= and 0)` bound `and` -> a u64 param used to be
/// minted, kernel-replayed and its coverage established, although the Linked
/// spec surface refuses `and` as a variable and z3 refuses
/// `(declare-const and Int)` ("invalid declaration, builtin symbol").
fn is_free_var_atom(atom: &str) -> bool {
    linked_var_name_problem(atom).is_none()
}

/// The operand of a `(>= a 0)` / `(<= 0 a)` comparison whose `a` is an atom
/// that is NOT a `Nat` literal, whatever else it is. This is the SHAPE the
/// binding rule diagnoses; [`recognize_nat_nonneg`] additionally requires the
/// operand to be a simple symbol.
fn nat_nonneg_operand<'a>(sexp: &SmtSexp<'a>) -> Option<&'a str> {
    let SmtSexp::List(items) = sexp else {
        return None;
    };
    let [SmtSexp::Atom(op), SmtSexp::Atom(lhs), SmtSexp::Atom(rhs)] = items[..] else {
        return None;
    };
    let non_literal = |atom: &str| !atom.is_empty() && parse_nat_literal(atom).is_none();
    match op {
        // s >= 0 : operand on the left, literal 0 on the right.
        ">=" if non_literal(lhs) && parse_nat_literal(rhs) == Some(0) => Some(lhs),
        // 0 <= s : literal 0 on the left, operand on the right.
        "<=" if parse_nat_literal(lhs) == Some(0) && non_literal(rhs) => Some(rhs),
        _ => None,
    }
}

/// Recognize EXACTLY the single-free-name Nat non-negativity tautology
/// `s >= 0` / `0 <= s`, returning the symbol. Returns `None` (fail-closed) for
/// every other shape — the recognizer is the syntactic half of the soundness
/// argument, so it is deliberately narrow:
///
///  * `(>= <sym> 0)`  — symbol on the left, literal `0` on the right, OR
///  * `(<= 0 <sym>)`  — literal `0` on the left, symbol on the right,
///
/// where `<sym>` is a free name ([`is_free_var_atom`]). The SEMANTIC
/// half — what `<sym>` denotes — is [`bind_nat_nonneg`].
fn recognize_nat_nonneg<'a>(sexp: &SmtSexp<'a>) -> Option<&'a str> {
    nat_nonneg_operand(sexp).filter(|operand| is_free_var_atom(operand))
}

/// Ground a comparison `(OP a b)` over two `Nat` literals into a kernel Bool
/// decision. `<`/`<=`/`>`/`>=` reduce to `Nat.ble` (the native reducer the L0
/// in-bounds encoder uses); `=` to `Nat.beq`. Returns `None` (fail-closed) for
/// any non-literal operand.
fn ground_comparison(op: &str, a: &SmtSexp<'_>, b: &SmtSexp<'_>) -> Option<Expr> {
    let (SmtSexp::Atom(a), SmtSexp::Atom(b)) = (a, b) else {
        return None;
    };
    let a = Expr::nat_lit(parse_nat_literal(a)?);
    let b = Expr::nat_lit(parse_nat_literal(b)?);
    match op {
        // a = b  ->  Nat.beq a b
        "=" => Some(nat_beq(a, b)),
        // a <= b ->  Nat.ble a b
        "<=" => Some(nat_ble(a, b)),
        // a >= b ->  Nat.ble b a
        ">=" => Some(nat_ble(b, a)),
        // a < b  ->  Nat.ble (a+1) b
        "<" => Some(nat_ble(
            Expr::apps(Expr::const_str("Nat.add"), [a, Expr::nat_lit(1)]),
            b,
        )),
        // a > b  ->  Nat.ble (b+1) a
        ">" => Some(nat_ble(
            Expr::apps(Expr::const_str("Nat.add"), [b, Expr::nat_lit(1)]),
            a,
        )),
        _ => None,
    }
}

/// Ground a predicate term into a kernel Bool decision `Expr`, or `None`
/// (fail-closed) for any shape outside the supported fragment. The recursion
/// is bounded by the reader's depth bound.
fn ground_sexp(sexp: &SmtSexp<'_>) -> Option<Expr> {
    let SmtSexp::List(items) = sexp else {
        // A bare atom (`x`, `true`, `42`) is not a predicate shape we ground.
        return None;
    };
    // The empty list `()` has no head: it is no predicate. (This slice was
    // `&items[1..]`, which panicked on `()`, aborting the validator on a
    // two-byte formula.)
    let [SmtSexp::Atom(head), rest @ ..] = items.as_slice() else {
        return None;
    };
    match *head {
        "=" | "<" | "<=" | ">" | ">=" => {
            if rest.len() != 2 {
                return None;
            }
            ground_comparison(head, &rest[0], &rest[1])
        }
        "not" => {
            if rest.len() != 1 {
                return None;
            }
            Some(bool_not(ground_sexp(&rest[0])?))
        }
        // SMT-LIB2 Core declares `and` / `or` `:left-assoc` over two or more
        // arguments, and trust-ir's one reader refuses fewer ("takes at least
        // 2 argument(s)"). `(and (>= 5 0))` used to ground as `(>= 5 0)`, so
        // its certificate replayed and established coverage for a text no
        // strict SMT-LIB2 reader reads.
        "and" => {
            if rest.len() < 2 {
                return None;
            }
            let mut it = rest.iter();
            let mut acc = ground_sexp(it.next()?)?;
            for s in it {
                acc = bool_and(acc, ground_sexp(s)?);
            }
            Some(acc)
        }
        "or" => {
            if rest.len() < 2 {
                return None;
            }
            let mut it = rest.iter();
            let mut acc = ground_sexp(it.next()?)?;
            for s in it {
                acc = bool_or(acc, ground_sexp(s)?);
            }
            Some(acc)
        }
        _ => None,
    }
}

/// The ONE SMT-LIB2 text of a contract formula ([`ProofFormula::smtlib_text`]):
/// the payload of an `smtlib2` formula whose `smtlib` rendering, if any, is
/// that payload. Every grounding in this module reads this text and nothing
/// else, so what the kernel re-checks is the obligation's own formula.
///
/// A formula that states no single SMT-LIB text grounds NOTHING
/// ([`ContractLoweringError::UnsupportedPredicate`]), whatever its schema
/// (decided exhaustively over [`OwnedFormulaSchema`]; an unowned schema is
/// never grounded). (This used to prefer the rendering whatever the schema: a
/// certificate replaying a true `smtlib` was admitted for an obligation whose
/// `smtlib2` payload was false, and an opaque payload was grounded as
/// SMT-LIB.) The text is then read by [`read_smtlib_term`] alone, so a text
/// that is not SMT-LIB2 source grounds nothing either.
fn predicate_text(formula: &ProofFormula) -> Result<&str, ContractLoweringError> {
    // A formula declared of another sort is no predicate, whatever its text
    // reads as: grounding `(>= 5 0)` of sort `Int` as a Bool decision proves a
    // claim the obligation does not state.
    if let Some(sort) = formula.sort.as_deref().filter(|sort| *sort != "Bool") {
        return Err(ContractLoweringError::UnsupportedPredicate(format!(
            "the formula is declared of sort `{sort}`, so it states no predicate"
        )));
    }
    formula.smtlib_text().ok_or_else(|| {
        let why = match formula.owned_schema() {
            Some(OwnedFormulaSchema::Smtlib2) => "its `smtlib` rendering differs from its payload",
            Some(OwnedFormulaSchema::Pred) => {
                "a `pred.N` citation states a refinement predicate over `self`, which no \
                 contract clause grounds"
            }
            Some(
                OwnedFormulaSchema::BvBlastGoal
                | OwnedFormulaSchema::SatRes
                | OwnedFormulaSchema::LineageTransformBinding,
            ) => "a claim schema states no SMT-LIB text",
            None => "trust-ir does not own the schema, so its payload is opaque",
        };
        ContractLoweringError::UnsupportedPredicate(format!(
            "the formula states no single SMT-LIB text (schema {:?}: {why}): only an `smtlib2` \
             payload whose `smtlib` rendering is absent or identical is grounded",
            formula.schema
        ))
    })
}

/// [`read_smtlib_term`] of a predicate text, its refusal named.
fn read_predicate(text: &str) -> Result<SmtSexp<'_>, ContractLoweringError> {
    read_smtlib_term(text).map_err(|defect| {
        ContractLoweringError::UnsupportedPredicate(format!("predicate {text:?} {defect}"))
    })
}

/// Build the kernel Bool-decision goal `Expr` for an L1 contract obligation from
/// its kind + predicate formula — **module-free, literal-only**.
///
/// Returns the proposition `@Eq Bool (<decision for the predicate>) Bool.true`.
/// Fails closed for a non-contract kind ([`ContractLoweringError::NotAContractKind`]),
/// a missing formula ([`ContractLoweringError::NoFormula`]), or a predicate
/// outside the grounded fragment
/// ([`ContractLoweringError::UnsupportedPredicate`]) — never minting a vacuous
/// goal, mirroring the L0 encoders' fail-closed envelope.
///
/// Every leaf must be a `Nat` literal. A clause over a free name — including
/// the `(>= s 0)` tautology shape — is `UnsupportedPredicate` here, because
/// without the module nothing says what the name denotes; use
/// [`contract_goal_in`].
pub fn contract_goal(
    kind: &ObligationKind,
    formula: Option<&ProofFormula>,
) -> Result<Expr, ContractLoweringError> {
    if !is_contract_kind(kind) {
        return Err(ContractLoweringError::NotAContractKind(kind.clone()));
    }
    let formula = formula.ok_or(ContractLoweringError::NoFormula)?;
    let text = predicate_text(formula)?;
    let sexp = read_predicate(text)?;
    let decision = ground_sexp(&sexp)
        .ok_or_else(|| ContractLoweringError::UnsupportedPredicate(text.to_string()))?;
    Ok(bool_is_true(decision))
}

/// What [`bind_nat_nonneg`] established about a `(>= s 0)` clause: the symbol,
/// the owning function, the place the symbol's binding names, and that place's
/// IR type (always an unsigned integer).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NatNonnegBinding {
    pub symbol: String,
    pub function: FuncId,
    pub place: ClausePlace,
    pub ty: Ty,
}

/// True iff `formula` has the `(>= a 0)` / `(<= 0 a)` shape with a non-literal
/// operand `a` — the shape [`bind_nat_nonneg`] decides. (Whether `a` is a legal
/// symbol, and what it denotes, is the binding rule's job, not this test's.)
pub fn is_nat_nonneg_shape(formula: &ProofFormula) -> bool {
    predicate_text(formula)
        .ok()
        .and_then(parse_predicate)
        .as_ref()
        .and_then(nat_nonneg_operand)
        .is_some()
}

/// **The binding rule** for the single-symbol nonneg clause `(>= s 0)` /
/// `(<= 0 s)`: the check that makes the closed kernel proposition
/// `∀ x : Nat, Nat.ble 0 x = true` a faithful denotation of the clause.
///
/// Every failure is [`ContractLoweringError::UnsupportedPredicate`] carrying the
/// reason, so it FAILS CLOSED. In order:
///
/// * (a) the obligation is a contract kind — `Postcondition` /
///   `RefinementType` (proved) or `Precondition` / `LoopInvariant` (assumed);
/// * (b) the operand `s` is an SMT simple symbol (`[A-Za-z_][A-Za-z0-9_.]*`,
///   not `true`/`false`/`let`/`forall`/`exists`/`as`/`!`/`_`), and it is the
///   clause's only free symbol;
/// * (c) `obligation.function == Some(f)`, `f` resolves uniquely, and its
///   `FuncTy` resolves;
/// * (d) `formula.bindings` has exactly one entry, and its name is `s`;
/// * (e) the place resolves to a type: `Param{i}` → `params[i]`,
///   `ResultSlot{i}` → `returns[i]`, `MutParamExit{i}` → `T` of a `&mut T` /
///   `*mut T` parameter, `ParamPointeeEntry{i}` (v62) → `T` of a `&T` /
///   `&mut T` parameter; `Value`, `World` and `Unwind` are refused, and a
///   `Precondition` may not name a result or exit place (it may name the
///   entry pointee, which exists before the call);
/// * (f) that type is `U8`/`U16`/`U32`/`U64`/`U128`, or `Usize` when the module
///   carries `target_info` (a `Ty::Handle` place is refused by name);
/// * (g) the binding's sort is `ClauseSort::Int` — `BitVec(w)` is refused
///   (SMT `>=` is ill-sorted on bit-vectors), as are `Float`, `Bool`,
///   `RoundingMode`, `Array` and `Datatype`.
///
/// The one fact left outside every check is the denotation lemma "the Int
/// value of an unsigned w-bit place is a Nat" (TRUST.md item 11). The
/// certificate LINEAGE already binds the bindings; this rule binds the
/// `FuncTy` side, which lineage cannot see.
pub fn bind_nat_nonneg(
    module: &Module,
    obligation: &ProofObligation,
) -> Result<NatNonnegBinding, ContractLoweringError> {
    let refuse = |reason: String| Err(ContractLoweringError::UnsupportedPredicate(reason));
    // (a) kind.
    if !is_contract_kind(&obligation.kind) {
        return refuse(format!(
            "obligation kind {:?} neither proves nor assumes a contract clause",
            obligation.kind
        ));
    }
    let Some(formula) = obligation.formula.as_ref() else {
        return refuse("the obligation carries no predicate formula".to_string());
    };
    let text = predicate_text(formula)?;
    let sexp = read_predicate(text)?;
    let Some(operand) = nat_nonneg_operand(&sexp) else {
        return refuse(format!(
            "predicate {text:?} is not the single-symbol nonneg shape `(>= s 0)` / `(<= 0 s)`"
        ));
    };
    // (b) the operand is a free name, and the clause's only free name.
    if !is_smt_simple_symbol(operand) {
        return refuse(format!(
            "clause operand `{operand}` is not an SMT simple symbol"
        ));
    }
    if let Some(problem) = linked_var_name_problem(operand) {
        return refuse(format!(
            "clause operand `{operand}` is no free name: {problem}"
        ));
    }
    if smt_free_symbols(text).is_none_or(|free| free.len() != 1 || !free.contains(operand)) {
        return refuse(format!(
            "clause {text:?} does not have `{operand}` as its only free symbol"
        ));
    }
    // (c) the owning function.
    let Some(function) = obligation.function else {
        return refuse("the obligation has no owning function (`function` is None)".to_string());
    };
    // (d) exactly one binding, naming the clause symbol.
    let [(name, binding)] = &formula.bindings[..] else {
        return refuse(format!(
            "the clause must bind exactly its one symbol `{operand}`, but carries {} bindings",
            formula.bindings.len()
        ));
    };
    if name != operand {
        return refuse(format!(
            "binding `{name}` does not name the clause symbol `{operand}`"
        ));
    }
    // (e) the place resolves to an IR type (function + signature resolution
    // included — the (c) half that needs the module).
    if obligation.kind == ObligationKind::Precondition
        && matches!(
            binding.place,
            ClausePlace::ResultSlot { .. } | ClausePlace::MutParamExit { .. }
        )
    {
        return refuse(format!(
            "a Precondition cannot name the result or exit place {:?}",
            binding.place
        ));
    }
    let ty = match resolve_clause_place(module, function, &binding.place) {
        Ok(ty) => ty,
        Err(error) => return refuse(error.to_string()),
    };
    // (f) the place is an unsigned integer.
    match &ty {
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 => {}
        Ty::Usize if module.target_info.is_some() => {}
        Ty::Usize => {
            return refuse(
                "a usize place has no fixed width without the module's target_info".to_string(),
            );
        }
        Ty::Handle(_) => {
            return refuse(format!(
                "place {:?} is the runtime handle {ty}, which has no machine value a nonneg \
                 clause can denote",
                binding.place
            ));
        }
        _ => {
            return refuse(format!(
                "place {:?} has IR type {ty}, which is not an unsigned integer",
                binding.place
            ));
        }
    }
    // (g) the clause reads the place at sort Int.
    if binding.sort != ClauseSort::Int {
        return refuse(format!(
            "binding sort {:?} is not Int (the Nat reading of `>=` needs the mathematical \
             integer value of the place)",
            binding.sort
        ));
    }
    Ok(NatNonnegBinding {
        symbol: operand.to_string(),
        function,
        place: binding.place,
        ty,
    })
}

/// Build the kernel goal for an L1 contract obligation **with its module in
/// scope** — the only path that may produce the free-name nonneg tautology.
///
/// A `(>= s 0)` / `(<= 0 s)` clause grounds to the closed proposition
/// `∀ x : Nat, @Eq Bool (Nat.ble 0 x) Bool.true` exactly when
/// [`bind_nat_nonneg`] binds `s` to an unsigned integer IR place read at sort
/// `Int`; any binding failure is that rule's `UnsupportedPredicate`. Every other
/// clause is grounded module-free by [`contract_goal`] (literal-only).
pub fn contract_goal_in(
    module: &Module,
    obligation: &ProofObligation,
) -> Result<Expr, ContractLoweringError> {
    if !is_contract_kind(&obligation.kind) {
        return Err(ContractLoweringError::NotAContractKind(
            obligation.kind.clone(),
        ));
    }
    let formula = obligation
        .formula
        .as_ref()
        .ok_or(ContractLoweringError::NoFormula)?;
    if is_nat_nonneg_shape(formula) {
        bind_nat_nonneg(module, obligation)?;
        // Closing over `x : Nat` makes the serialized claim replayable without
        // relying on process-local FVar ids or an omitted LocalContext.
        return Ok(nat_nonneg_closed_goal());
    }
    contract_goal(&obligation.kind, Some(formula))
}

/// Build the full [`ExprObligation`] for an L1 contract obligation, ready to
/// stamp as [`crate::proof::ProofAnnotation::Goal`]. The grounded goal carries
/// no operand hypotheses — a contract predicate over literals is closed —
/// mirroring how an L0 goal over concrete facts is self-contained.
pub fn contract_obligation(
    kind: &ObligationKind,
    formula: Option<&ProofFormula>,
) -> Result<ExprObligation, ContractLoweringError> {
    Ok(ExprObligation::new(contract_goal(kind, formula)?))
}

/// The hand proof term `@Eq.refl Bool Bool.true` — the SAME term that discharges
/// the L0 in-bounds goal. Proves `@Eq Bool x Bool.true` exactly when `x` reduces
/// to `Bool.true`; the kernel does the `Nat.ble` / `Bool.and` reduction.
fn refl_true() -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Bool"), Expr::const_str("Bool.true")],
    )
}

/// Kernel-discharge a grounded contract obligation: `check_type(refl_true, goal)`
/// under the kernel-owned ordinary prelude ONLY — the same vocabulary the L0
/// encoders' `discharge` helper uses, no external `.lean`. Only the immutable
/// baseline is reused; every attempt has a fresh context and checker. Returns
/// true iff the kernel accepts; unavailable construction fails closed.
fn kernel_discharges(goal: &Expr) -> bool {
    use clean_kernel::{Environment, LocalContext, TypeChecker};
    Environment::with_reusable_prelude(|env| {
        let tc = TypeChecker::with_context(env, LocalContext::new());
        tc.check_type(&refl_true(), goal).is_ok()
    })
    .unwrap_or(false)
}

/// PROVE the single-free-var Nat non-negativity tautology `x >= 0` at the KERNEL
/// level, returning a CLOSED `(goal, proof)` pair iff the kernel actually
/// discharges it. This is the free-var analogue of the literal
/// `kernel_discharges` gate:
///
///  * build `∀ x : Nat, @Eq Bool (Nat.ble 0 x) Bool.true`;
///  * build the matching lambda proof `fun x : Nat => @Eq.refl Bool Bool.true`;
///  * require the kernel to accept that closed judgment in an empty context.
///
/// The kernel discharges this exactly because `Nat.ble 0 x` reduces
/// definitionally to `Bool.true` for every `Nat` `x` — a genuine tautology, not
/// a literal fixture. Returns `None` (fail-closed) if the kernel refuses (it
/// does for any non-tautology, e.g. the `x >= 5` shape which never reaches this
/// helper because [`recognize_nat_nonneg`] rejects it first, AND would be
/// refused here even if it did). Closing the binder is essential: serialized
/// proof evidence cannot rely on a process-local `FVarId` or an omitted local
/// context.
fn nat_nonneg_closed_goal() -> Expr {
    let nat = Expr::const_str("Nat");
    let body = bool_is_true(nat_ble(Expr::nat_lit(0), Expr::bvar(0)));
    Expr::pi(BinderInfo::Default, nat, body)
}

fn nat_nonneg_closed_proof() -> Expr {
    Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), refl_true())
}

fn prove_nat_nonneg_free_var() -> Option<(Expr, Expr)> {
    use clean_kernel::{Environment, LocalContext, TypeChecker};
    let goal = nat_nonneg_closed_goal();
    let proof = nat_nonneg_closed_proof();
    Environment::with_reusable_prelude(|env| {
        let tc = TypeChecker::with_context(env, LocalContext::new());
        if tc.check_type(&proof, &goal).is_ok() {
            Some((goal, proof))
        } else {
            // Fail-closed: the kernel refused, so NO proof, NO Certified.
            None
        }
    })
    .ok()
    .flatten()
}

/// ASSUME the single-free-var Nat non-negativity predicate `x >= 0`: build the
/// grounded goal `@Eq Bool (Nat.ble 0 x) Bool.true` over a fresh `x : Nat`
/// WITHOUT requiring a proof term. A PRECONDITION is *assumed* into the caller's
/// context — adding `h : P(x)` is sound with no proof obligation, because the
/// caller is only ever entitled to reason under it, never to conclude it. This
/// returns the goal `Expr` (the hypothesis shape) but performs NO kernel
/// discharge — assuming is not proving.
///
/// This helper is only ever reached for a PRECONDITION / LoopInvariant kind (the
/// ObligationKind gate in the certificate path keys on that); a POSTCONDITION
/// NEVER routes here — it must go through [`prove_nat_nonneg_free_var`].
fn assume_nat_nonneg_free_var() -> Expr {
    use clean_kernel::{BinderInfo, LocalContext};
    let mut ctx = LocalContext::new();
    let x = ctx.push(
        Name::from_string(NAT_NONNEG_VAR_KEY),
        Expr::const_str("Nat"),
        BinderInfo::Default,
    );
    bool_is_true(nat_ble(Expr::nat_lit(0), Expr::fvar(x)))
}

/// Whether an obligation kind is *proved* (needs a real proof term) vs *assumed*
/// (adds a hypothesis with no proof term) when its predicate is a free-var
/// tautology.
///
/// SOUNDNESS — this is the single most important classification in the slice:
///
///  * A **PRECONDITION** (and, by the same reasoning, a **LoopInvariant** at
///    entry) is ASSUMED: the function body may reason *under* it, so introducing
///    `h : P` with no proof term is sound — the caller is on the hook to
///    establish `P`, not this obligation.
///  * A **POSTCONDITION** / **RefinementType** is PROVED: it is a claim the
///    function makes to its caller, so it demands a real proof term. Assuming it
///    would let an UNPROVEN postcondition mint `Certified` — the exact soundness
///    hole this slice must not open.
///
/// Getting this backwards is the catastrophic failure mode; keying strictly on
/// `ObligationKind` here (available on every `ProofObligation`) is what keeps an
/// unproven postcondition from ever being stamped. The table is
/// [`crate::proof::ObligationKindShape::free_var_is_proved`], every cell of
/// which is a proved Trust contract (gate 13): `Postcondition` and
/// `RefinementType` PROVED, `Precondition` and `LoopInvariant` ASSUMED, and
/// every non-contract kind (which never reaches here) `false`.
fn free_var_kind_is_proved(kind: &ObligationKind) -> bool {
    kind.shape().free_var_is_proved()
}

/// Encode the kernel proof TERM of a grounded contract goal to the opaque
/// `term` bytes of a [`ProofEvidence::CleanCic`] payload.
///
/// The bytes are the canonical, bounded bincode representation of the
/// `clean_kernel::Expr` proof term (a reflexivity proof for a ground goal, or a
/// closed lambda for the free-variable tautology) — a **decodable** proof, not
/// a `Display` string. This lets the
/// consumer-side [`KernelCleanCicRechecker`] DECODE the term and have the Clean
/// kernel re-check that it inhabits the obligation's own re-grounded goal (the
/// de Bruijn criterion), rather than trusting the bytes on read. Returns `None`
/// (fail-closed) if the term does not serialize (it always does for a
/// well-formed `Expr`, but no `unwrap` in production). Never empty (the floor
/// `obligation_has_matching_clean_cic` requires a non-empty term).
fn proof_term_bytes(proof_term: &Expr) -> Option<Vec<u8>> {
    encode_proof_term(proof_term)
}

/// Mint a `CleanCic` certificate carrying `proof`, lineage-bound to
/// `obligation`. Fail-closed on encode.
fn mint_clean_cic(
    obligation: &ProofObligation,
    prover: impl Into<String>,
    proof: &Expr,
) -> Option<ProofCertificate> {
    // Serialize the DECODABLE proof term so the consumer-side kernel
    // re-checker can independently re-validate it (fail-closed on encode).
    let term = proof_term_bytes(proof)?;
    Some(ProofCertificate {
        assurance: None,
        obligation: obligation.id,
        prover: prover.into(),
        evidence: ProofEvidence::CleanCic {
            term,
            context: Vec::new(),
            lineage: clean_cic_lineage_digest(obligation),
            kernel_recheck: None,
        },
    })
}

/// **Ground an L1 contract obligation to a kernel-checkable `CleanCic`
/// certificate — the `Certified` tier — or return `None` (fail-closed).**
/// Module-free, so **literal-only**: see [`contract_clean_cic_certificate_in`]
/// for a clause over a free name.
///
/// This is the L1 analogue of the L0 certify path: it grounds the obligation's
/// predicate into a CIC term and, *only when the trusted kernel actually
/// discharges that term*, mints a [`ProofEvidence::CleanCic`] certificate whose
/// `lineage` is bound to this exact obligation via
/// [`clean_cic_lineage_digest`] (so the certificate cannot be replayed onto a
/// different obligation).
///
/// SOUNDNESS — returns `None` (NO Certified stamp) when:
///  * the predicate is not groundable ([`contract_goal`] errs — every clause
///    with a non-literal leaf does), OR
///  * the kernel REFUSES to discharge the grounded goal.
///
/// There is no path that yields a `CleanCic` for an ungroundable or
/// kernel-rejected predicate, so an ungroundable contract predicate produces no
/// false `Certified` evidence. The caller stamps `ProofStatus::Certified` only
/// for an obligation for which this returns `Some`.
pub fn contract_clean_cic_certificate(
    obligation: &ProofObligation,
    prover: impl Into<String>,
) -> Option<ProofCertificate> {
    // 1. Ground the predicate into a CIC term (literal-fixture path). Fail-closed
    //    on any unsupported kind / missing formula / unsupported predicate shape.
    let goal = contract_goal(&obligation.kind, obligation.formula.as_ref()).ok()?;
    // 2. The trusted kernel must ACTUALLY discharge it. A grounded-but-false
    //    predicate is rejected here — no Certified stamp for an unproven claim.
    if !kernel_discharges(&goal) {
        return None;
    }
    // 3. Mint the kernel-checkable certificate, lineage-bound to this obligation.
    mint_clean_cic(obligation, prover, &refl_true())
}

/// [`contract_clean_cic_certificate`] **with the module in scope**: the only
/// minter of a `CleanCic` for the free-name nonneg tautology `(>= s 0)` /
/// `(<= 0 s)`.
///
/// For that shape, `ObligationKind` decides prove-vs-assume:
///
///  * PROVED kind (Postcondition / RefinementType): [`bind_nat_nonneg`] must
///    bind `s` to an unsigned integer IR place read at sort `Int`, and the
///    kernel must ACTUALLY discharge the closed tautology — only then is a
///    certificate minted.
///  * ASSUMED kind (Precondition / LoopInvariant): assuming is not proving, so
///    NO certificate (the hypothesis is [`contract_nat_nonneg_obligation_in`]).
///
/// Every other clause falls through to the literal-only
/// [`contract_clean_cic_certificate`].
pub fn contract_clean_cic_certificate_in(
    module: &Module,
    obligation: &ProofObligation,
    prover: impl Into<String>,
) -> Option<ProofCertificate> {
    if is_contract_kind(&obligation.kind)
        && let Some(formula) = obligation.formula.as_ref()
        && is_nat_nonneg_shape(formula)
    {
        // KEY ON ObligationKind — the assume-vs-prove split.
        if !free_var_kind_is_proved(&obligation.kind) {
            return None;
        }
        // The clause must denote a Nat-valued IR place — or nothing is minted.
        bind_nat_nonneg(module, obligation).ok()?;
        // PROVED: the kernel must ACTUALLY discharge the tautology.
        let (_goal, proof) = prove_nat_nonneg_free_var()?;
        return mint_clean_cic(obligation, prover, &proof);
    }
    contract_clean_cic_certificate(obligation, prover)
}

/// [`contract_clean_cic_certificate_in`], BOUND (roadmap WS1.12a): the same
/// grounding and the same kernel discharge, but the certificate carries a
/// [`KERNEL_ANCHOR_TRUST_IR_CONTRACT`] directive whose
/// [`CertificateBinding`] names the environment and the statement it was
/// checked in, and its `lineage` is the symbol-keyed v8 form
/// ([`clean_cic_lineage_digest_v8`]), so it survives an id renumbering.
///
/// * `environment_digest` = [`kernel_environment_digest`] of the kernel-owned
///   ordinary prelude — exactly the environment `kernel_accepts_term`
///   re-checks in;
/// * `statement_digest` = [`clean_cic_statement_digest`] of
///   [`contract_goal_in`]'s goal — exactly the statement the re-checker
///   re-grounds;
/// * `origin_module = None` (minted here), `source = None`, `callees = []`.
///
/// Returns `None` (no certificate, never a partial one) when the legacy
/// minter would, when a digest cannot be computed, or when the obligation's
/// owning function does not resolve to one link symbol (a lineage that cannot
/// be keyed is not minted).
///
/// The legacy minters stay directive-less on purpose. A binding has had a
/// binary carrier since v61 (`binary::CERTIFICATE_BINDING_FORMAT_VERSION`),
/// so a module carrying this certificate is written at v61 or later; before
/// it, such a module travelled in JSON / MessagePack only.
///
/// [`CertificateBinding`]: crate::proof::CertificateBinding
/// [`KERNEL_ANCHOR_TRUST_IR_CONTRACT`]: crate::proof::KERNEL_ANCHOR_TRUST_IR_CONTRACT
/// [`clean_cic_lineage_digest_v8`]: crate::proof::clean_cic_lineage_digest_v8
/// [`kernel_environment_digest`]: crate::proof::kernel_environment_digest
/// [`clean_cic_statement_digest`]: crate::proof::clean_cic_statement_digest
pub fn contract_clean_cic_certificate_bound_in(
    module: &Module,
    obligation: &ProofObligation,
    prover: impl Into<String>,
) -> Option<ProofCertificate> {
    use crate::proof::{
        CertificateBinding, CleanCicKernelRecheck, KERNEL_ANCHOR_TRUST_IR_CONTRACT,
        KERNEL_ANCHOR_TRUST_IR_CONTRACT_MODULE, clean_cic_lineage_digest_v8,
        clean_cic_statement_digest, kernel_environment_digest,
    };
    use clean_kernel::Environment;
    if !is_contract_kind(&obligation.kind) {
        return None;
    }
    let formula = obligation.formula.as_ref()?;
    // The same prove-vs-assume split and the same kernel discharge as the
    // legacy minters: a proof term exists only for what the kernel accepts.
    let proof = if is_nat_nonneg_shape(formula) {
        if !free_var_kind_is_proved(&obligation.kind) {
            return None;
        }
        bind_nat_nonneg(module, obligation).ok()?;
        prove_nat_nonneg_free_var()?.1
    } else {
        let goal = contract_goal(&obligation.kind, Some(formula)).ok()?;
        if !kernel_discharges(&goal) {
            return None;
        }
        refl_true()
    };
    // The statement the re-checker re-grounds, and the environment it
    // re-checks in — both computed HERE, never asserted.
    let goal = contract_goal_in(module, obligation).ok()?;
    let statement_digest = clean_cic_statement_digest(&goal).ok()?;
    let environment_digest = Environment::with_reusable_prelude(kernel_environment_digest)
        .ok()?
        .ok()?;
    let binding = CertificateBinding::new(environment_digest, statement_digest);
    let resolve = |id: crate::value::FuncId| module.function_by_id(id).map(|f| f.name.clone());
    let lineage = clean_cic_lineage_digest_v8(obligation, &resolve, Some(&binding))?;
    let term = proof_term_bytes(&proof)?;
    Some(ProofCertificate {
        assurance: None,
        obligation: obligation.id,
        prover: prover.into(),
        evidence: ProofEvidence::CleanCic {
            term,
            context: Vec::new(),
            lineage,
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: KERNEL_ANCHOR_TRUST_IR_CONTRACT_MODULE.to_string(),
                theorems: Vec::new(),
                anchor: KERNEL_ANCHOR_TRUST_IR_CONTRACT.to_string(),
                allowed_axioms: Vec::new(),
                binding: Some(Box::new(binding)),
            }),
        },
    })
}

/// Ground the single-free-name Nat non-negativity predicate `s >= 0` /
/// `0 <= s` into an [`ExprObligation`], for the **ASSUME** case (a
/// PRECONDITION / LoopInvariant). The obligation carries the tautology's
/// Bool-decision goal `@Eq Bool (Nat.ble 0 x) Bool.true` AND a named hypothesis
/// of the same shape — the assumed predicate `h : P(x)` introduced into the
/// caller's context.
///
/// Returns `None` (fail-closed) unless:
///  * the kind is an ASSUMED contract kind (Precondition / LoopInvariant), AND
///  * the predicate is EXACTLY the recognized single-symbol `s >= 0` shape, AND
///  * [`bind_nat_nonneg`] binds `s` to an unsigned integer IR place of
///    `module` read at sort `Int`.
///
/// There is no module-free form: without the module nothing says the symbol
/// denotes a `Nat`, so the hypothesis could not be justified.
///
/// SOUNDNESS: this is the assume side — it introduces a hypothesis with NO proof
/// term, which is sound for a precondition (the caller owes its establishment).
/// It deliberately does NOT mint a `Certified` certificate; assuming is not
/// proving. A POSTCONDITION never routes here (it must be *proved* via
/// [`contract_clean_cic_certificate_in`]).
pub fn contract_nat_nonneg_obligation_in(
    module: &Module,
    obligation: &ProofObligation,
) -> Option<ExprObligation> {
    if !is_contract_kind(&obligation.kind) {
        return None;
    }
    // Only the ASSUMED kinds ground a hypothesis here; a PROVED kind must go
    // through the proof path, not the assume path.
    if free_var_kind_is_proved(&obligation.kind) {
        return None;
    }
    let formula = obligation.formula.as_ref()?;
    let sexp = parse_predicate(predicate_text(formula).ok()?)?;
    recognize_nat_nonneg(&sexp)?;
    bind_nat_nonneg(module, obligation).ok()?;
    // Ground the assumed predicate: the goal shape IS the hypothesis shape.
    let assumed = assume_nat_nonneg_free_var();
    Some(ExprObligation::new(assumed.clone()).with_hypothesis("h_precond", assumed))
}

/// The Clean kernel accepts the decoded proof `term` bytes as an inhabitant of
/// `goal`, in a fresh checker and local context under the kernel-owned
/// ordinary prelude. Fail-closed on decode or construction failure.
fn kernel_accepts_term(term: &[u8], goal: &Expr) -> bool {
    use clean_kernel::{Environment, LocalContext, TypeChecker};
    // Decode the certificate's serialized proof TERM (untrusted bytes) with the
    // same canonical, bounded, whole-slice codec as the minter.
    let Some(proof_term) = decode_proof_term(term) else {
        return false;
    };
    // The TRUSTED Clean kernel must accept that the decoded term inhabits the
    // canonical goal. This is the de Bruijn criterion: a tampered or forged
    // term, or a term proving some *other* proposition, is rejected.
    Environment::with_reusable_prelude(|env| {
        let tc = TypeChecker::with_context(env, LocalContext::new());
        tc.check_type(&proof_term, goal).is_ok()
    })
    .unwrap_or(false)
}

/// The **real** Clean-kernel re-validator for L1 contract
/// [`ProofEvidence::CleanCic`] certificates — the consumer-side de Bruijn
/// criterion that closes the trusted-on-read surface at
/// [`crate::proof::obligation_has_kernel_rechecked_clean_cic`].
///
/// Given a `Certified` obligation and its lineage-bound `CleanCic` certificate,
/// the module-free `kernel_rechecks_clean_cic` and the module-bound
/// `kernel_rechecks_clean_cic_in`:
///
/// 1. **re-ground the canonical goal from the OBLIGATION** (`kind` + `formula`)
///    via [`contract_goal`] (literal-only) or [`contract_goal_in`] (the module
///    in scope, the only path that binds a free-name nonneg clause to its IR
///    place) — never from the certificate's bytes, so a term that proves some
///    *other* proposition cannot be substituted in;
/// 2. **decodes the certificate's serialized proof TERM** (untrusted `term`
///    bytes) with a canonical, whole-slice, byte/node/depth-bounded codec; and
/// 3. has the **trusted `clean-kernel` type-checker** confirm the decoded term
///    inhabits that re-grounded goal
///    (`TypeChecker::check_type(term, &goal)` in a fresh checker/local context
///    under the kernel-owned ordinary prelude — the same gate the minter uses).
///    The baseline environment may be reused, never the proof-checking result.
///
/// Every step is fail-closed: an ungroundable obligation, undecodable bytes, or
/// a term the kernel refuses all yield `false`. A tampered/forged term (one that
/// does not inhabit the re-grounded goal) is REJECTED even though its lineage
/// digest still matches — that is exactly the surface the lineage-only floor
/// [`crate::proof::obligation_has_matching_clean_cic`] leaves open.
#[derive(Debug, Clone, Copy, Default)]
pub struct KernelCleanCicRechecker;

impl crate::proof::CleanCicRechecker for KernelCleanCicRechecker {
    /// Module-free: re-checks only LITERAL goals ([`contract_goal`]). A clause
    /// over a free name — the nonneg tautology included — returns `false`,
    /// because nothing here can say what the name denotes; see the
    /// [`crate::proof::ModuleCleanCicRechecker`] impl.
    fn kernel_rechecks_clean_cic(
        &self,
        obligation: &ProofObligation,
        cert: &ProofCertificate,
    ) -> bool {
        let ProofEvidence::CleanCic { term, .. } = &cert.evidence else {
            return false;
        };
        // Reconstruct the obligation's canonical claim from the OBLIGATION's own
        // data — never the (untrusted) certificate bytes.
        let Ok(goal) = contract_goal(&obligation.kind, obligation.formula.as_ref()) else {
            return false;
        };
        kernel_accepts_term(term, &goal)
    }
}

impl crate::proof::ModuleCleanCicRechecker for KernelCleanCicRechecker {
    /// Module-bound: re-grounds the claim with [`contract_goal_in`], so a
    /// free-name nonneg clause re-checks only when [`bind_nat_nonneg`] binds it
    /// to an unsigned integer place of `module`; literal clauses re-check
    /// exactly as the module-free impl does.
    fn kernel_rechecks_clean_cic_in(
        &self,
        module: &Module,
        obligation: &ProofObligation,
        cert: &ProofCertificate,
    ) -> bool {
        let ProofEvidence::CleanCic { term, .. } = &cert.evidence else {
            return false;
        };
        let Ok(goal) = contract_goal_in(module, obligation) else {
            return false;
        };
        kernel_accepts_term(term, &goal)
    }

    /// Everything this rechecker accepts is a [`contract_goal_in`] goal — a
    /// closed ground Bool decision, or the free-name nonneg tautology bound to
    /// an unsigned place — so an accepted certificate re-checked the
    /// [`KernelClaimFamily::ContractGroundDecision`] family. Classified ONLY
    /// when the certificate claims that path itself: no directive, or the
    /// [`KERNEL_ANCHOR_TRUST_IR_CONTRACT`] anchor in its canonical form (the
    /// contract module, no theorems, no admitted axioms). A certificate that
    /// names any other anchor was minted to prove something else; that its
    /// term also inhabits the contract goal is not what its producer claimed,
    /// so it stays unclassified and confers no coverage.
    ///
    /// Pure classification: the caller
    /// ([`crate::proof::CleanCicModuleProofAuthority`]) has already required
    /// the kernel re-check to accept.
    ///
    /// [`KernelClaimFamily::ContractGroundDecision`]: crate::proof::KernelClaimFamily::ContractGroundDecision
    /// [`KERNEL_ANCHOR_TRUST_IR_CONTRACT`]: crate::proof::KERNEL_ANCHOR_TRUST_IR_CONTRACT
    fn rechecked_claim_family(
        &self,
        _module: &Module,
        obligation: &ProofObligation,
        cert: &ProofCertificate,
    ) -> Option<crate::proof::KernelClaimFamily> {
        use crate::proof::{
            KERNEL_ANCHOR_TRUST_IR_CONTRACT, KERNEL_ANCHOR_TRUST_IR_CONTRACT_MODULE,
            KernelClaimFamily,
        };
        if !is_contract_kind(&obligation.kind) {
            return None;
        }
        let ProofEvidence::CleanCic { kernel_recheck, .. } = &cert.evidence else {
            return None;
        };
        match kernel_recheck {
            None => Some(KernelClaimFamily::ContractGroundDecision),
            Some(directive)
                if directive.anchor == KERNEL_ANCHOR_TRUST_IR_CONTRACT
                    && directive.module == KERNEL_ANCHOR_TRUST_IR_CONTRACT_MODULE
                    && directive.theorems.is_empty()
                    && directive.allowed_axioms.is_empty() =>
            {
                Some(KernelClaimFamily::ContractGroundDecision)
            }
            Some(_) => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof::{
        ProofStatus, RejectingCleanCicRechecker, obligation_has_kernel_rechecked_clean_cic,
        obligation_has_matching_clean_cic,
    };
    use crate::value::ProofId;

    fn obligation(kind: ObligationKind, smtlib: &str) -> ProofObligation {
        ProofObligation::new(ProofId::new(0), kind, ProofStatus::Pending, "contract")
            .with_formula(ProofFormula::smtlib2(smtlib, "Bool"))
    }

    #[test]
    fn test_contract_goal_shape_is_eq_bool_true() {
        // (> x 0) with x bound to a concrete fact 5: grounds to
        // @Eq Bool (Nat.ble (Nat.add 0 1) 5) Bool.true.
        let goal = contract_goal(
            &ObligationKind::Precondition,
            Some(&ProofFormula::smtlib2("(> 5 0)", "Bool")),
        )
        .expect("(> 5 0) is groundable");
        let eq_args = goal.get_app_args();
        assert_eq!(eq_args.len(), 3, "@Eq takes (Bool, decision, Bool.true)");
        assert_eq!(eq_args[0], &Expr::const_str("Bool"), "Eq is over Bool");
        assert_eq!(
            eq_args[2],
            &Expr::const_str("Bool.true"),
            "the contract decision must be claimed true"
        );
    }

    #[test]
    fn test_groundable_contract_produces_certified_clean_cic() {
        // (a) A groundable, TRUE contract predicate produces a kernel-checkable
        // CleanCic certificate (the Certified tier), and the certificate is
        // genuinely bound to this obligation (the admissibility floor accepts it).
        let ob = obligation(ObligationKind::Postcondition, "(and (>= 7 0) (< 7 10))");
        let cert = contract_clean_cic_certificate(&ob, "trust-ir.R-L1")
            .expect("groundable+true => Certified");

        // It is CleanCic evidence (the Certified tier), not Trusted/SMT.
        assert!(
            matches!(cert.evidence, ProofEvidence::CleanCic { .. }),
            "must be CleanCic evidence"
        );
        // And the lineage binds it to THIS obligation: the admissibility gate
        // used by the validator accepts it as a real kernel-checkable cert.
        assert!(
            obligation_has_matching_clean_cic(&ob, std::slice::from_ref(&cert)),
            "the CleanCic cert must be lineage-bound to its obligation"
        );
        // And — the SOUND gate — the Clean kernel re-checks the certificate's
        // own serialized proof TERM against the re-grounded goal and accepts it.
        assert!(
            obligation_has_kernel_rechecked_clean_cic(
                &ob,
                std::slice::from_ref(&cert),
                &KernelCleanCicRechecker,
            ),
            "the genuine cert's proof term must kernel-re-check against the obligation"
        );
    }

    #[test]
    fn test_warm_prelude_rechecks_good_forged_good_certificate_terms() {
        let ob = obligation(ObligationKind::Postcondition, "(= 1 1)");
        let good = contract_clean_cic_certificate(&ob, "trust-ir.R-L1")
            .expect("true contract has an actual kernel proof");
        let mut forged = good.clone();
        let ProofEvidence::CleanCic { term, .. } = &mut forged.evidence else {
            unreachable!("minter produces CleanCic")
        };
        // Keep the obligation, lineage, context and all metadata identical.
        // This canonical expression decodes but is not a proof of the goal.
        *term = encode_proof_term(&Expr::const_str("Bool.true")).expect("canonical expression");
        assert!(obligation_has_matching_clean_cic(
            &ob,
            std::slice::from_ref(&forged),
        ));
        for (certificate, accepted) in [(&good, true), (&forged, false), (&good, true)] {
            assert_eq!(
                obligation_has_kernel_rechecked_clean_cic(
                    &ob,
                    std::slice::from_ref(certificate),
                    &KernelCleanCicRechecker,
                ),
                accepted,
                "a warmed baseline must neither cache a verdict nor retain failed-check state",
            );
        }
    }

    #[test]
    fn test_kernel_recheck_rejects_tampered_term_that_lineage_floor_accepts() {
        // THE TRUSTED-ON-READ GAP, CLOSED. The lineage-only floor
        // (`obligation_has_matching_clean_cic`) admits a `CleanCic` certificate on
        // a lineage-digest match + non-empty term, WITHOUT re-checking the term
        // bytes. The sound gate (`obligation_has_kernel_rechecked_clean_cic` with
        // the real `KernelCleanCicRechecker`) DECODES the proof term and has the
        // Clean kernel re-check it — so a tampered term is rejected.
        let ob = obligation(ObligationKind::Postcondition, "(and (>= 7 0) (< 7 10))");
        let good = contract_clean_cic_certificate(&ob, "trust-ir.R-L1")
            .expect("groundable+true => genuine cert");

        // TAMPER: keep the (publicly recomputable) lineage, but swap the proof
        // TERM bytes for a well-formed `Expr` encoding a *different* term that
        // does NOT inhabit the goal — `Bool.true : Bool`, not a proof of
        // `@Eq Bool _ Bool.true`. It still decodes; only the KERNEL can catch it.
        let bogus_term = encode_proof_term(&Expr::const_str("Bool.true")).expect("Expr serializes");
        let (lineage, context, kernel_recheck) = match good.evidence.clone() {
            ProofEvidence::CleanCic {
                lineage,
                context,
                kernel_recheck,
                ..
            } => (lineage, context, kernel_recheck),
            _ => unreachable!("minter produces CleanCic"),
        };
        let tampered = ProofCertificate {
            obligation: ob.id,
            prover: "attacker".to_string(),
            evidence: ProofEvidence::CleanCic {
                term: bogus_term,
                context,
                lineage,
                kernel_recheck,
            },

            assurance: None,
        };

        // (1) The lineage-only FLOOR still ACCEPTS the tampered cert — the gap.
        assert!(
            obligation_has_matching_clean_cic(&ob, std::slice::from_ref(&tampered)),
            "the weak floor accepts on lineage + non-empty term alone (the gap)"
        );

        // (2) The SOUND gate REJECTS it: the decoded term does not prove the goal.
        assert!(
            !obligation_has_kernel_rechecked_clean_cic(
                &ob,
                std::slice::from_ref(&tampered),
                &KernelCleanCicRechecker,
            ),
            "the kernel re-check must REJECT a term that does not prove the obligation"
        );

        // (3) Undecodable garbage bytes are likewise rejected (fail-closed decode),
        // even though the floor accepts them (non-empty + bound lineage).
        let garbage = ProofCertificate {
            obligation: ob.id,
            prover: "attacker".to_string(),
            evidence: ProofEvidence::CleanCic {
                term: vec![0xFF, 0xFF, 0xFF, 0xFF],
                context: Vec::new(),
                lineage: clean_cic_lineage_digest(&ob),
                kernel_recheck: None,
            },

            assurance: None,
        };
        assert!(
            obligation_has_matching_clean_cic(&ob, std::slice::from_ref(&garbage)),
            "floor accepts non-empty garbage bytes"
        );
        assert!(
            !obligation_has_kernel_rechecked_clean_cic(
                &ob,
                std::slice::from_ref(&garbage),
                &KernelCleanCicRechecker,
            ),
            "undecodable term bytes must be rejected fail-closed"
        );

        // (4) A valid proof followed by a suffix is not the same proof carrier.
        // Whole-slice canonical decode rejects the smuggling channel.
        let mut suffixed = good.clone();
        let ProofEvidence::CleanCic { term, .. } = &mut suffixed.evidence else {
            unreachable!("minter produces CleanCic")
        };
        term.push(0);
        assert!(
            !obligation_has_kernel_rechecked_clean_cic(
                &ob,
                std::slice::from_ref(&suffixed),
                &KernelCleanCicRechecker,
            ),
            "a canonical proof with trailing bytes must be rejected"
        );

        // (5) The fail-closed default rechecker rejects even the GENUINE cert:
        // a consumer with no kernel must NOT promote Certified on lineage alone.
        assert!(
            !obligation_has_kernel_rechecked_clean_cic(
                &ob,
                std::slice::from_ref(&good),
                &RejectingCleanCicRechecker,
            ),
            "the fail-closed default rechecker admits nothing"
        );
    }

    #[test]
    fn test_ungroundable_contract_is_fail_closed_no_certified() {
        // (b) An UNGROUNDABLE predicate shape must NOT yield a Certified stamp.
        // A free program variable (`x`) is not a literal, so the predicate is
        // outside the grounded fragment: contract_goal errs and the certificate
        // path returns None — fail-closed, NO false Certified.
        let ob_freevar = obligation(ObligationKind::Precondition, "(> x 0)");
        assert!(
            matches!(
                contract_goal(&ob_freevar.kind, ob_freevar.formula.as_ref()),
                Err(ContractLoweringError::UnsupportedPredicate(_))
            ),
            "a free variable is outside the grounded fragment"
        );
        assert!(
            contract_clean_cic_certificate(&ob_freevar, "trust-ir.R-L1").is_none(),
            "ungroundable predicate => NO Certified stamp (fail-closed)"
        );

        // An unknown head symbol is likewise fail-closed.
        let ob_unknown = obligation(ObligationKind::Postcondition, "(mod 6 2)");
        assert!(
            contract_clean_cic_certificate(&ob_unknown, "trust-ir.R-L1").is_none(),
            "unknown head symbol => NO Certified stamp"
        );

        // A non-contract kind is fail-closed even with a groundable formula.
        let ob_safety = ProofObligation::new(
            ProofId::new(0),
            ObligationKind::MemorySafety,
            ProofStatus::Pending,
            "not a contract",
        )
        .with_formula(ProofFormula::smtlib2("(> 5 0)", "Bool"));
        assert_eq!(
            contract_goal(&ob_safety.kind, ob_safety.formula.as_ref()),
            Err(ContractLoweringError::NotAContractKind(
                ObligationKind::MemorySafety
            )),
            "a non-contract kind must not be grounded by the contract encoder"
        );
        assert!(
            contract_clean_cic_certificate(&ob_safety, "trust-ir.R-L1").is_none(),
            "non-contract kind => NO Certified stamp"
        );

        // A missing formula is fail-closed.
        let ob_noformula = ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "no formula",
        );
        assert_eq!(
            contract_goal(&ob_noformula.kind, ob_noformula.formula.as_ref()),
            Err(ContractLoweringError::NoFormula),
            "no formula => NoFormula error, no goal"
        );
        assert!(
            contract_clean_cic_certificate(&ob_noformula, "trust-ir.R-L1").is_none(),
            "missing formula => NO Certified stamp"
        );
    }

    #[test]
    fn test_grounded_but_false_predicate_is_not_certified() {
        // A predicate that GROUNDS but is FALSE: the kernel must refuse to
        // discharge it, so no Certified stamp. This is the kernel-level
        // fail-closed gate (distinct from the parse-level one above).
        let ob_false = obligation(ObligationKind::Precondition, "(> 0 5)");
        // It grounds (it is a valid comparison over literals) ...
        assert!(
            contract_goal(&ob_false.kind, ob_false.formula.as_ref()).is_ok(),
            "(> 0 5) is a well-formed groundable comparison"
        );
        // ... but it is FALSE, so the kernel refuses => None.
        assert!(
            contract_clean_cic_certificate(&ob_false, "trust-ir.R-L1").is_none(),
            "a grounded-but-false predicate must NOT be Certified (kernel refuses)"
        );
    }

    #[test]
    fn test_change_coupling_predicate_field() {
        // CHANGE-COUPLING: mutate ONLY the predicate (true -> false) and both the
        // goal Expr AND the certify verdict move, because the goal is
        // materialized from the formula text.
        let ob_true = obligation(ObligationKind::LoopInvariant, "(<= 3 10)");
        let ob_false = obligation(ObligationKind::LoopInvariant, "(<= 10 3)");
        let goal_true = contract_goal(&ob_true.kind, ob_true.formula.as_ref()).unwrap();
        let goal_false = contract_goal(&ob_false.kind, ob_false.formula.as_ref()).unwrap();
        assert_ne!(
            goal_true, goal_false,
            "the goal Expr is change-coupled to the predicate field"
        );
        assert!(
            contract_clean_cic_certificate(&ob_true, "p").is_some(),
            "(<= 3 10) => Certified"
        );
        assert!(
            contract_clean_cic_certificate(&ob_false, "p").is_none(),
            "(<= 10 3) => NOT Certified: verdict flipped with the field edit"
        );
    }

    // -----------------------------------------------------------------------
    // R-L1 goal item #4, slice 1: single-free-name Nat non-negativity tautology
    // `s >= 0`. These tests are the teeth of the assume-vs-prove split, the
    // tautology-only gating, and (WS1.1) the binding rule: the tautology is
    // produced ONLY with the module in scope and the symbol bound to an
    // unsigned integer IR place read at sort Int.
    // -----------------------------------------------------------------------

    use crate::proof::{ClauseBinding, ClausePlace, ClauseSort};
    use crate::ty::FuncTy;
    use crate::value::{BlockId, FuncTyId};
    use crate::{Function, Module};

    /// `f0 : (u64, &mut u16, i64) -> u64`, the owning function of every bound
    /// fixture below.
    fn signature_module() -> Module {
        let mut module = Module::new("contract_binding");
        module.func_types.push(FuncTy {
            params: vec![Ty::U64, Ty::RefMut(Box::new(Ty::U16)), Ty::I64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        });
        module.functions.push(Function::new(
            FuncId::new(0),
            "f0",
            FuncTyId::new(0),
            BlockId::new(0),
        ));
        module
    }

    /// `obligation(kind, smtlib)` scoped to `f0` with ONE binding `name`.
    fn bound(
        kind: ObligationKind,
        smtlib: &str,
        name: &str,
        sort: ClauseSort,
        place: ClausePlace,
    ) -> ProofObligation {
        let mut formula = ProofFormula::smtlib2(smtlib, "Bool");
        formula.bindings = vec![(name.to_string(), ClauseBinding { sort, place })];
        ProofObligation::new(ProofId::new(0), kind, ProofStatus::Pending, "contract")
            .with_function(FuncId::new(0))
            .with_formula(formula)
    }

    fn result_u64(kind: ObligationKind, smtlib: &str, name: &str) -> ProofObligation {
        bound(
            kind,
            smtlib,
            name,
            ClauseSort::Int,
            ClausePlace::ResultSlot { index: 0 },
        )
    }

    fn unsupported_reason(result: Result<NatNonnegBinding, ContractLoweringError>) -> String {
        match result {
            Err(ContractLoweringError::UnsupportedPredicate(reason)) => reason,
            other => panic!("expected an UnsupportedPredicate refusal, got {other:?}"),
        }
    }

    /// (1) A POSTCONDITION `(>= s 0)` is NOT groundable module-free — nothing
    /// there says what `s` denotes — and IS proved `Certified` through the
    /// module-bound path once `s` binds to the u64 result at sort Int. The
    /// proof is a real closed lambda re-checked by the kernel, not a fixture.
    #[test]
    fn test_postcondition_nat_nonneg_free_var_proves_certified() {
        let module = signature_module();
        let ob = result_u64(ObligationKind::Postcondition, "(>= result 0)", "result");

        // Module-free: refused at every entry point.
        assert!(
            matches!(
                contract_goal(&ob.kind, ob.formula.as_ref()),
                Err(ContractLoweringError::UnsupportedPredicate(_))
            ),
            "the module-free grounder is literal-only"
        );
        assert!(
            contract_clean_cic_certificate(&ob, "trust-ir.R-L1").is_none(),
            "no module, no binding, no certificate"
        );

        // Module-bound: minted, and a closed lambda.
        let cert = contract_clean_cic_certificate_in(&module, &ob, "trust-ir.R-L1")
            .expect("(>= result 0) over a u64 result bound at Int => proved Certified");
        let ProofEvidence::CleanCic { term, .. } = &cert.evidence else {
            panic!("must be CleanCic evidence (the Certified tier)");
        };
        let decoded = decode_proof_term(term).expect("canonical proof term decodes");
        assert!(
            matches!(decoded.kind(), clean_kernel::ExprKind::Lam(..)),
            "the free-name proof must close x with a lambda, got {decoded:?}"
        );
        assert!(
            obligation_has_matching_clean_cic(&ob, std::slice::from_ref(&cert)),
            "the CleanCic cert must be lineage-bound to its obligation"
        );
        // The module-bound rechecker replays it; the module-free one refuses.
        assert!(crate::proof::obligation_has_kernel_rechecked_clean_cic_in(
            &module,
            &ob,
            std::slice::from_ref(&cert),
            &KernelCleanCicRechecker,
        ));
        assert!(
            !obligation_has_kernel_rechecked_clean_cic(
                &ob,
                std::slice::from_ref(&cert),
                &KernelCleanCicRechecker,
            ),
            "the module-free rechecker must refuse a free-name clause"
        );
        let goal = contract_goal_in(&module, &ob).expect("closed goal");
        assert!(
            matches!(goal.kind(), clean_kernel::ExprKind::Pi(..)),
            "the re-derived claim must close x with a Pi, got {goal:?}"
        );

        // The normal form `(<= 0 s)`, a u64 Param, and the `&mut u16` exit value
        // prove identically; a RefinementType is PROVED too.
        for ob in [
            result_u64(ObligationKind::Postcondition, "(<= 0 result)", "result"),
            bound(
                ObligationKind::Postcondition,
                "(>= x 0)",
                "x",
                ClauseSort::Int,
                ClausePlace::Param { index: 0 },
            ),
            bound(
                ObligationKind::Postcondition,
                "(>= y_exit 0)",
                "y_exit",
                ClauseSort::Int,
                ClausePlace::MutParamExit { index: 1 },
            ),
            // v62: the `&mut u16`'s value at ENTRY is a Nat-valued place too.
            bound(
                ObligationKind::Postcondition,
                "(>= y_entry 0)",
                "y_entry",
                ClauseSort::Int,
                ClausePlace::ParamPointeeEntry { index: 1 },
            ),
            result_u64(ObligationKind::RefinementType, "(>= result 0)", "result"),
        ] {
            assert!(
                contract_clean_cic_certificate_in(&module, &ob, "trust-ir.R-L1").is_some(),
                "{:?} must be proved Certified",
                ob.formula
            );
        }
        // The exit value spelled `y'` is no SMT-LIB2 token (a `'` is in none):
        // the one reader refuses the text, so nothing is minted for it.
        let primed = bound(
            ObligationKind::Postcondition,
            "(>= y' 0)",
            "y'",
            ClauseSort::Int,
            ClausePlace::MutParamExit { index: 1 },
        );
        assert!(contract_clean_cic_certificate_in(&module, &primed, "trust-ir.R-L1").is_none());
        assert!(matches!(
            bind_nat_nonneg(&module, &primed),
            Err(ContractLoweringError::UnsupportedPredicate(reason))
                if reason.contains("no SMT-LIB2 token")
        ));
    }

    /// (1b) The binding rule refuses, with a named reason, every way the clause
    /// can fail to denote a Nat-valued IR place — and the certificate path
    /// mints nothing for any of them.
    #[test]
    fn test_nat_nonneg_binding_rule_refusals() {
        let module = signature_module();
        let post = ObligationKind::Postcondition;
        let cases: Vec<(ProofObligation, &str)> = vec![
            (
                bound(
                    post.clone(),
                    "(>= z 0)",
                    "z",
                    ClauseSort::Int,
                    ClausePlace::Param { index: 2 },
                ),
                "is not an unsigned integer",
            ),
            (
                bound(
                    post.clone(),
                    "(>= x 0)",
                    "x",
                    ClauseSort::BitVec(64),
                    ClausePlace::Param { index: 0 },
                ),
                "is not Int",
            ),
            (
                bound(
                    post.clone(),
                    "(>= x 0)",
                    "x",
                    ClauseSort::Bool,
                    ClausePlace::Param { index: 0 },
                ),
                "is not Int",
            ),
            (
                bound(
                    post.clone(),
                    "(>= x 0)",
                    "result",
                    ClauseSort::Int,
                    ClausePlace::ResultSlot { index: 0 },
                ),
                "does not name the clause symbol",
            ),
            (
                bound(
                    post.clone(),
                    "(>= x 0)",
                    "x",
                    ClauseSort::Int,
                    ClausePlace::MutParamExit { index: 0 },
                ),
                "not a &mut / *mut",
            ),
            // v62: the by-value `x: u64` has no entry pointee.
            (
                bound(
                    post.clone(),
                    "(>= x 0)",
                    "x",
                    ClauseSort::Int,
                    ClausePlace::ParamPointeeEntry { index: 0 },
                ),
                "not a & / &mut reference",
            ),
            // v62: an entry pointee past the three-parameter signature.
            (
                bound(
                    post.clone(),
                    "(>= y_entry 0)",
                    "y_entry",
                    ClauseSort::Int,
                    ClausePlace::ParamPointeeEntry { index: 3 },
                ),
                "out of range",
            ),
            (
                bound(
                    post.clone(),
                    "(>= x 0)",
                    "x",
                    ClauseSort::Int,
                    ClausePlace::World,
                ),
                "denotes ambient state",
            ),
            (
                bound(
                    post.clone(),
                    "(>= -5 0)",
                    "-5",
                    ClauseSort::Int,
                    ClausePlace::ResultSlot { index: 0 },
                ),
                "is not an SMT simple symbol",
            ),
            (
                bound(
                    post.clone(),
                    "(>= true 0)",
                    "true",
                    ClauseSort::Int,
                    ClausePlace::ResultSlot { index: 0 },
                ),
                "is not an SMT simple symbol",
            ),
            (
                bound(
                    ObligationKind::Precondition,
                    "(>= result 0)",
                    "result",
                    ClauseSort::Int,
                    ClausePlace::ResultSlot { index: 0 },
                ),
                "cannot name the result or exit place",
            ),
        ];
        for (ob, needle) in cases {
            let reason = unsupported_reason(bind_nat_nonneg(&module, &ob));
            assert!(reason.contains(needle), "{:?}: {reason}", ob.formula);
            assert!(contract_clean_cic_certificate_in(&module, &ob, "p").is_none());
            assert!(contract_goal_in(&module, &ob).is_err());
        }

        // No owning function.
        let mut unscoped = result_u64(ObligationKind::Postcondition, "(>= result 0)", "result");
        unscoped.function = None;
        assert!(
            unsupported_reason(bind_nat_nonneg(&module, &unscoped)).contains("no owning function")
        );
        // Empty bindings: UNBINDABLE, never a wildcard.
        let mut unbound = result_u64(ObligationKind::Postcondition, "(>= result 0)", "result");
        unbound.formula.as_mut().unwrap().bindings.clear();
        assert!(
            unsupported_reason(bind_nat_nonneg(&module, &unbound)).contains("carries 0 bindings")
        );
        // A usize place needs target_info to have a width at all.
        let mut usize_module = signature_module();
        usize_module.func_types[0].returns = vec![Ty::Usize];
        let ob = result_u64(ObligationKind::Postcondition, "(>= result 0)", "result");
        assert!(unsupported_reason(bind_nat_nonneg(&usize_module, &ob)).contains("target_info"));
        usize_module.target_info = Some(crate::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: crate::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        assert!(bind_nat_nonneg(&usize_module, &ob).is_ok());
    }

    /// (2) A PRECONDITION `(>= s 0)` is ASSUMED: with the module in scope it
    /// GROUNDS to an obligation with the hypothesis added — but it does NOT
    /// mint a Certified certificate (assuming is not proving).
    #[test]
    fn test_precondition_nat_nonneg_free_var_is_assumed() {
        let module = signature_module();
        let pre = |kind| {
            bound(
                kind,
                "(>= x 0)",
                "x",
                ClauseSort::Int,
                ClausePlace::Param { index: 0 },
            )
        };
        let ob = pre(ObligationKind::Precondition);

        let assumed = contract_nat_nonneg_obligation_in(&module, &ob)
            .expect("precondition (>= x 0) over a u64 param grounds as an assumed hypothesis");
        assert_eq!(
            assumed.hypotheses.len(),
            1,
            "the assumed predicate is introduced as a hypothesis"
        );
        assert_eq!(
            &assumed.hypotheses[0].1, &assumed.goal,
            "the assumed hypothesis IS the grounded predicate"
        );
        assert!(
            contract_clean_cic_certificate_in(&module, &ob, "trust-ir.R-L1").is_none(),
            "a PRECONDITION is ASSUMED, not PROVED => NO Certified stamp"
        );

        // An unbindable precondition is not assumed either: the hypothesis
        // would claim a Nat the place does not hold.
        let signed = bound(
            ObligationKind::Precondition,
            "(>= z 0)",
            "z",
            ClauseSort::Int,
            ClausePlace::Param { index: 2 },
        );
        assert!(contract_nat_nonneg_obligation_in(&module, &signed).is_none());

        // A LoopInvariant is likewise assumed at entry.
        let ob_inv = pre(ObligationKind::LoopInvariant);
        assert!(contract_nat_nonneg_obligation_in(&module, &ob_inv).is_some());
        assert!(contract_clean_cic_certificate_in(&module, &ob_inv, "trust-ir.R-L1").is_none());

        // A POSTCONDITION never routes through the assume path.
        let ob_post = pre(ObligationKind::Postcondition);
        assert!(
            contract_nat_nonneg_obligation_in(&module, &ob_post).is_none(),
            "a POSTCONDITION is PROVED, not ASSUMED — the assume path rejects it"
        );
    }

    /// (3) NEGATIVE: a POSTCONDITION `(>= s 5)` FAILS CLOSED even when bound —
    /// `s >= 5` is NOT a tautology, so neither the recognizer (non-zero bound)
    /// nor the literal path (free name) grounds it.
    #[test]
    fn test_postcondition_nat_nonneg_nontautology_fails_closed() {
        let module = signature_module();
        let ob_ge5 = result_u64(ObligationKind::Postcondition, "(>= result 5)", "result");
        assert!(
            recognize_nat_nonneg(&parse_predicate("(>= result 5)").unwrap()).is_none(),
            "(>= result 5) is NOT the s>=0 tautology shape (non-zero bound)"
        );
        assert!(contract_clean_cic_certificate_in(&module, &ob_ge5, "trust-ir.R-L1").is_none());

        let ob_pre5 = result_u64(ObligationKind::Precondition, "(>= result 5)", "result");
        assert!(contract_nat_nonneg_obligation_in(&module, &ob_pre5).is_none());

        // Wrong operators over the free name are non-tautologies too.
        for pred in ["(<= result 0)", "(= result 0)", "(> result 0)"] {
            let ob = result_u64(ObligationKind::Postcondition, pred, "result");
            assert!(
                contract_clean_cic_certificate_in(&module, &ob, "trust-ir.R-L1").is_none(),
                "POSTCONDITION {pred} is not the s>=0 tautology => FAIL CLOSED"
            );
        }
    }

    /// (4) FAIL-CLOSED on the everything-else set: multi-name predicates,
    /// nested booleans, the wrong side, non-contract kinds, and atoms that are
    /// not SMT simple symbols all mint nothing, bound or not.
    #[test]
    fn test_nat_nonneg_fail_closed_on_everything_else() {
        let module = signature_module();
        for pred in [
            "(>= x y)",
            "(and (>= x 0) (>= y 0))",
            "(>= 0 x)",
            "(<= x 0)",
        ] {
            assert!(
                recognize_nat_nonneg(&parse_predicate(pred).unwrap()).is_none(),
                "{pred} is not the bare s>=0 shape"
            );
            let ob = bound(
                ObligationKind::Postcondition,
                pred,
                "x",
                ClauseSort::Int,
                ClausePlace::Param { index: 0 },
            );
            assert!(
                contract_clean_cic_certificate_in(&module, &ob, "trust-ir.R-L1").is_none(),
                "{pred} => FAIL CLOSED"
            );
        }

        // Atoms the former "does not parse as a u64" test admitted as free
        // variables are not symbols under the shared grammar.
        for atom in ["-5", "+1", "#x00", "true", "false", "_"] {
            let pred = format!("(>= {atom} 0)");
            assert!(
                recognize_nat_nonneg(&parse_predicate(&pred).unwrap()).is_none(),
                "{pred} must not be recognized"
            );
        }

        // ...nor numerals: an SMT numeral is ASCII digits only, so a `+`-signed
        // atom (an SMT SYMBOL) never grounds on the literal-only path.
        for pred in ["(>= +1 0)", "(<= 0 +1)", "(= +1 1)", "(>= 5 +0)"] {
            assert!(
                matches!(
                    contract_goal(
                        &ObligationKind::Postcondition,
                        Some(&ProofFormula::smtlib2(pred, "Bool"))
                    ),
                    Err(ContractLoweringError::UnsupportedPredicate(_))
                ),
                "{pred} must not ground module-free"
            );
        }
        assert_eq!(parse_nat_literal("007"), Some(7));
        assert_eq!(parse_nat_literal("+1"), None);
        assert_eq!(parse_nat_literal(""), None);

        // A non-contract kind with the tautology formula still mints nothing.
        let ob_safety = bound(
            ObligationKind::MemorySafety,
            "(>= x 0)",
            "x",
            ClauseSort::Int,
            ClausePlace::Param { index: 0 },
        );
        assert!(contract_clean_cic_certificate_in(&module, &ob_safety, "trust-ir.R-L1").is_none());
        assert!(contract_nat_nonneg_obligation_in(&module, &ob_safety).is_none());
        assert_eq!(
            contract_goal_in(&module, &ob_safety),
            Err(ContractLoweringError::NotAContractKind(
                ObligationKind::MemorySafety
            ))
        );
    }

    /// (5) Literal clauses are unaffected by the split: the module-bound path
    /// grounds them exactly as the module-free one does.
    #[test]
    fn test_literal_clauses_agree_across_entry_points() {
        let module = signature_module();
        let ob = obligation(ObligationKind::Postcondition, "(= 1 1)");
        assert_eq!(
            contract_goal_in(&module, &ob),
            contract_goal(&ob.kind, ob.formula.as_ref())
        );
        assert_eq!(
            contract_clean_cic_certificate_in(&module, &ob, "p"),
            contract_clean_cic_certificate(&ob, "p")
        );
        assert!(contract_clean_cic_certificate(&ob, "p").is_some());
    }
}
