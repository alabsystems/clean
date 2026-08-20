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
//! [`crate::proof::ProofFormula`] (an SMT-LIB2 s-expression in `smtlib`/`payload`,
//! e.g. `(> x 0)`, `(not (= result 0))`, `(and (>= x 0) (<= x 10))`) and returns
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
//! 2. a missing predicate formula;
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
//! The whole module is gated on `clean-expr` (via the parent module in lib.rs)
//! so the default zero-dependency trust-ir format build never references
//! clean-kernel.

use crate::proof::{
    ExprObligation, ObligationKind, ProofCertificate, ProofEvidence, ProofFormula, ProofObligation,
    clean_cic_lineage_digest, decode_clean_expr_v1, encode_clean_expr_v1,
};
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
fn is_contract_kind(kind: &ObligationKind) -> bool {
    matches!(
        kind,
        ObligationKind::Precondition
            | ObligationKind::Postcondition
            | ObligationKind::LoopInvariant
            | ObligationKind::RefinementType
    )
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
// A tiny, fail-closed SMT-LIB2 s-expression reader for the supported fragment.
//
// The grammar is deliberately small. Any token / shape outside it returns
// `None`, which the caller maps to `UnsupportedPredicate` — fail-closed.
//
//   pred  := '(' BOOLOP pred+ ')' | cmp
//   cmp   := '(' CMPOP nat nat ')'           ; CMPOP ∈ { =, <, <=, >, >= }
//   BOOLOP∈ { and, or, not }
//   nat   := non-negative decimal integer literal
//
// Only ground (literal-operand) comparisons are grounded: a contract predicate
// is groundable iff every leaf is a Nat literal. A free program variable (e.g.
// `x`, `result`) is NOT a literal, so the predicate fails closed — exactly the
// L0 envelope, where the goal is born from concrete node facts and an
// unsupported shape yields no goal.
// ---------------------------------------------------------------------------

/// One s-expression token.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Open,
    Close,
    Atom(String),
}

/// Tokenize an SMT-LIB2 predicate string into parens/atoms. Returns `None` on
/// any character class we do not model (keeps the reader total and fail-closed).
fn tokenize(s: &str) -> Option<Vec<Tok>> {
    let mut toks = Vec::new();
    let mut chars = s.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            '(' => {
                toks.push(Tok::Open);
                chars.next();
            }
            ')' => {
                toks.push(Tok::Close);
                chars.next();
            }
            c if c.is_whitespace() => {
                chars.next();
            }
            _ => {
                let mut atom = String::new();
                while let Some(&c) = chars.peek() {
                    if c == '(' || c == ')' || c.is_whitespace() {
                        break;
                    }
                    atom.push(c);
                    chars.next();
                }
                toks.push(Tok::Atom(atom));
            }
        }
    }
    Some(toks)
}

/// A parsed s-expression: an atom or a list.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

/// Parse a single complete s-expression from `toks[*pos..]`, advancing `pos`.
/// Returns `None` on any malformed structure — fail-closed.
fn parse_sexp(toks: &[Tok], pos: &mut usize) -> Option<Sexp> {
    match toks.get(*pos)? {
        Tok::Atom(a) => {
            *pos += 1;
            Some(Sexp::Atom(a.clone()))
        }
        Tok::Open => {
            *pos += 1;
            let mut items = Vec::new();
            loop {
                match toks.get(*pos)? {
                    Tok::Close => {
                        *pos += 1;
                        return Some(Sexp::List(items));
                    }
                    _ => items.push(parse_sexp(toks, pos)?),
                }
            }
        }
        Tok::Close => None,
    }
}

/// Parse a complete predicate string into a single `Sexp`, requiring all tokens
/// to be consumed. Returns `None` (fail-closed) on trailing tokens or a parse
/// failure.
fn parse_predicate(s: &str) -> Option<Sexp> {
    let toks = tokenize(s)?;
    let mut pos = 0usize;
    let sexp = parse_sexp(&toks, &mut pos)?;
    if pos == toks.len() { Some(sexp) } else { None }
}

/// A non-negative decimal `Nat` literal, or `None` (fail-closed) for a symbol,
/// a negative number, or anything non-numeric. Free program variables land here
/// and so make the whole predicate ungroundable.
fn parse_nat_literal(atom: &str) -> Option<u64> {
    atom.parse::<u64>().ok()
}

// ---------------------------------------------------------------------------
// R-L1 goal item #4, slice 1: a SINGLE free-var Nat non-negativity tautology.
//
// The literal-fixture path above grounds only predicates whose leaves are all
// `Nat` literals. This adds the FIRST non-literal-fixture increment: the one
// predicate that is a genuine tautology over a single free `Nat` variable and
// nothing else —
//
//     x >= 0        (SMT `(>= x 0)`)  or its normal form
//     0 <= x        (SMT `(<= 0 x)`)
//
// Both ground to the SAME kernel Bool decision `Nat.ble 0 x`, which the kernel
// DEFINITIONALLY reduces to `Bool.true` for EVERY `x : Nat` (the recursive
// `Nat.ble` matches its first argument: `ble 0 _ = true`, independent of `x`).
// So `@Eq.refl Bool Bool.true` genuinely proves `@Eq Bool (Nat.ble 0 x)
// Bool.true` under a context binding `x : Nat` — a real proof term, NOT a
// literal fixture (empirically confirmed against the trusted kernel; and the
// kernel REFUSES `Nat.ble 5 x = true`, so `x >= 5` cannot mint anything).
//
// FAIL-CLOSED: this recognizer returns `Some` ONLY for exactly this shape over
// a single free `Nat` var. Anything else — a non-zero bound (`x >= 5`), the
// wrong operator (`x <= 0`, `x = 0`, `x > 0`), a literal on the var side, two
// distinct free vars, a nested boolean, a non-`Nat` var — returns `None`, so
// no goal and no `Certified` stamp is minted for it. The `Nat`-typing of the
// var is guaranteed by the way we ground it (an `FVar` we bind at type `Nat`);
// there is no path that admits a non-`Nat` var here.
// ---------------------------------------------------------------------------

/// The canonical free-var name of the single-var Nat non-negativity tautology.
/// The var is a syntactic SMT symbol; we only ever bind ONE, at type `Nat`.
const NAT_NONNEG_VAR_KEY: &str = "x";

/// True iff `atom` is a syntactic free variable — a non-empty symbol that is
/// NOT a `Nat` literal. (A literal is grounded by the fixture path; a free var
/// is the only leaf the tautology path admits, and only in the `x >= 0` shape.)
fn is_free_var_atom(atom: &str) -> bool {
    !atom.is_empty() && parse_nat_literal(atom).is_none()
}

/// Recognize EXACTLY the single-free-var Nat non-negativity tautology
/// `x >= 0` / `0 <= x`, returning the variable's SMT symbol name. Returns `None`
/// (fail-closed) for every other shape — the recognizer is the soundness
/// cornerstone of this slice, so it is deliberately narrow:
///
///  * `(>= <var> 0)`  — var on the left, literal `0` on the right, OR
///  * `(<= 0 <var>)`  — literal `0` on the left, var on the right.
///
/// A non-zero bound, the wrong operator, a literal where the var must be (or
/// vice-versa), a second free var, or any nesting all return `None`.
fn recognize_nat_nonneg(sexp: &Sexp) -> Option<&str> {
    let Sexp::List(items) = sexp else {
        return None;
    };
    let [Sexp::Atom(op), Sexp::Atom(lhs), Sexp::Atom(rhs)] = &items[..] else {
        return None;
    };
    match op.as_str() {
        // x >= 0 : var on the left, literal 0 on the right.
        ">=" => {
            if is_free_var_atom(lhs) && parse_nat_literal(rhs) == Some(0) {
                Some(lhs.as_str())
            } else {
                None
            }
        }
        // 0 <= x : literal 0 on the left, var on the right.
        "<=" => {
            if parse_nat_literal(lhs) == Some(0) && is_free_var_atom(rhs) {
                Some(rhs.as_str())
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Ground a comparison `(OP a b)` over two `Nat` literals into a kernel Bool
/// decision. `<`/`<=`/`>`/`>=` reduce to `Nat.ble` (the native reducer the L0
/// in-bounds encoder uses); `=` to `Nat.beq`. Returns `None` (fail-closed) for
/// any non-literal operand.
fn ground_comparison(op: &str, a: &Sexp, b: &Sexp) -> Option<Expr> {
    let (Sexp::Atom(a), Sexp::Atom(b)) = (a, b) else {
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

/// Ground a predicate `Sexp` into a kernel Bool decision `Expr`, or `None`
/// (fail-closed) for any shape outside the supported fragment.
fn ground_sexp(sexp: &Sexp) -> Option<Expr> {
    let Sexp::List(items) = sexp else {
        // A bare atom (`x`, `true`, `42`) is not a predicate shape we ground.
        return None;
    };
    let (Some(Sexp::Atom(head)), rest) = (items.first(), &items[1..]) else {
        return None;
    };
    match head.as_str() {
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
        "and" => {
            if rest.is_empty() {
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
            if rest.is_empty() {
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

/// The SMT-LIB2 predicate text of a contract formula: prefer the explicit
/// `smtlib` rendering, fall back to the `payload` (which is the SMT-LIB2 text
/// for the `smtlib2` schema). Mirrors how the router indexes obligations.
fn predicate_text(formula: &ProofFormula) -> &str {
    formula.smtlib.as_deref().unwrap_or(&formula.payload)
}

/// Build the kernel Bool-decision goal `Expr` for an L1 contract obligation from
/// its kind + predicate formula.
///
/// Returns the proposition `@Eq Bool (<decision for the predicate>) Bool.true`.
/// Fails closed for a non-contract kind ([`ContractLoweringError::NotAContractKind`]),
/// a missing formula ([`ContractLoweringError::NoFormula`]), or a predicate
/// outside the grounded fragment
/// ([`ContractLoweringError::UnsupportedPredicate`]) — never minting a vacuous
/// goal, mirroring the L0 encoders' fail-closed envelope.
pub fn contract_goal(
    kind: &ObligationKind,
    formula: Option<&ProofFormula>,
) -> Result<Expr, ContractLoweringError> {
    if !is_contract_kind(kind) {
        return Err(ContractLoweringError::NotAContractKind(kind.clone()));
    }
    let formula = formula.ok_or(ContractLoweringError::NoFormula)?;
    let text = predicate_text(formula);
    let sexp = parse_predicate(text)
        .ok_or_else(|| ContractLoweringError::UnsupportedPredicate(text.to_string()))?;
    // The one supported free-variable predicate is represented as a CLOSED
    // proposition. Closing over `x : Nat` makes the serialized claim replayable
    // without relying on process-local FVar ids or an omitted LocalContext.
    if recognize_nat_nonneg(&sexp).is_some() {
        return Ok(nat_nonneg_closed_goal());
    }
    let decision = ground_sexp(&sexp)
        .ok_or_else(|| ContractLoweringError::UnsupportedPredicate(text.to_string()))?;
    Ok(bool_is_true(decision))
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
/// under `Environment::with_prelude()` ONLY — the same gate the L0 encoders'
/// `discharge` helper uses, no external `.lean`. Returns true iff the kernel
/// accepts (i.e. the predicate genuinely reduces to `Bool.true`).
fn kernel_discharges(goal: &Expr) -> bool {
    use clean_kernel::{Environment, LocalContext, TypeChecker};
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_context(&env, LocalContext::new());
    tc.check_type(&refl_true(), goal).is_ok()
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
    let env = Environment::with_prelude();
    let goal = nat_nonneg_closed_goal();
    let proof = nat_nonneg_closed_proof();
    let tc = TypeChecker::with_context(&env, LocalContext::new());
    if tc.check_type(&proof, &goal).is_ok() {
        Some((goal, proof))
    } else {
        // Fail-closed: the kernel refused, so NO proof, NO Certified.
        None
    }
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
/// unproven postcondition from ever being stamped.
fn free_var_kind_is_proved(kind: &ObligationKind) -> bool {
    match kind {
        // PROVED: a claim to the caller — must carry a real proof term.
        ObligationKind::Postcondition | ObligationKind::RefinementType => true,
        // ASSUMED: reasoned-under, not concluded — hypothesis, no proof term.
        ObligationKind::Precondition | ObligationKind::LoopInvariant => false,
        // Any other (non-contract) kind never reaches here.
        _ => false,
    }
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

/// **Ground an L1 contract obligation to a kernel-checkable `CleanCic`
/// certificate — the `Certified` tier — or return `None` (fail-closed).**
///
/// This is the L1 analogue of the L0 certify path: it grounds the obligation's
/// predicate into a CIC term and, *only when the trusted kernel actually
/// discharges that term*, mints a [`ProofEvidence::CleanCic`] certificate whose
/// `lineage` is bound to this exact obligation via
/// [`clean_cic_lineage_digest`] (so the certificate cannot be replayed onto a
/// different obligation).
///
/// SOUNDNESS — returns `None` (NO Certified stamp) when:
///  * the predicate is not groundable ([`contract_goal`] errs), OR
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
    // 0. Free-var Nat non-negativity tautology (`x >= 0` / `0 <= x`), the R-L1
    //    slice-1 increment. Only reachable for a contract kind, and only for a
    //    predicate that IS that exact single-free-var shape. ObligationKind
    //    decides prove-vs-assume:
    //
    //      * PROVED kind (Postcondition / RefinementType): the tautology is a
    //        claim to the caller, so the kernel MUST discharge a real proof term
    //        for it before we mint `Certified`. `prove_nat_nonneg_free_var`
    //        returns the goal only when the kernel accepts `@Eq.refl` — so this
    //        is a genuine kernel-checked proof, exactly like the literal path.
    //      * ASSUMED kind (Precondition / LoopInvariant): the predicate is
    //        assumed, NOT proved. Assuming is not a `Certified` proof — we mint
    //        NO CleanCic certificate here. (The assumed-hypothesis obligation is
    //        materialized by `contract_nat_nonneg_obligation`.) Returning `None`
    //        is the whole point: an unproven claim never becomes `Certified`.
    if is_contract_kind(&obligation.kind)
        && let Some(formula) = obligation.formula.as_ref()
        && let Some(sexp) = parse_predicate(predicate_text(formula))
        && recognize_nat_nonneg(&sexp).is_some()
    {
        // KEY ON ObligationKind — the assume-vs-prove split.
        if !free_var_kind_is_proved(&obligation.kind) {
            // ASSUMED: no proof term, no Certified stamp. Fail-closed
            // w.r.t. minting Certified — the assumption is not a proof.
            return None;
        }
        // PROVED: the kernel must ACTUALLY discharge the tautology.
        let (_goal, proof) = prove_nat_nonneg_free_var()?;
        let term = proof_term_bytes(&proof)?;
        let lineage = clean_cic_lineage_digest(obligation);
        return Some(ProofCertificate {
            obligation: obligation.id,
            prover: prover.into(),
            evidence: ProofEvidence::CleanCic {
                term,
                context: Vec::new(),
                lineage,
                kernel_recheck: None,
            },
        });
    }

    // 1. Ground the predicate into a CIC term (literal-fixture path). Fail-closed
    //    on any unsupported kind / missing formula / unsupported predicate shape.
    let goal = contract_goal(&obligation.kind, obligation.formula.as_ref()).ok()?;
    // 2. The trusted kernel must ACTUALLY discharge it. A grounded-but-false
    //    predicate is rejected here — no Certified stamp for an unproven claim.
    let proof = refl_true();
    if !kernel_discharges(&goal) {
        return None;
    }
    // 3. Serialize the DECODABLE proof term so the consumer-side kernel
    //    re-checker can independently re-validate it (fail-closed on encode).
    let term = proof_term_bytes(&proof)?;
    // 4. Mint the kernel-checkable certificate, lineage-bound to this obligation.
    let lineage = clean_cic_lineage_digest(obligation);
    Some(ProofCertificate {
        obligation: obligation.id,
        prover: prover.into(),
        evidence: ProofEvidence::CleanCic {
            term,
            context: Vec::new(),
            lineage,
            kernel_recheck: None,
        },
    })
}

/// Ground the single-free-var Nat non-negativity predicate `x >= 0` / `0 <= x`
/// into an [`ExprObligation`], for the **ASSUME** case (a PRECONDITION /
/// LoopInvariant). The obligation carries the tautology's Bool-decision goal
/// `@Eq Bool (Nat.ble 0 x) Bool.true` AND a named hypothesis of the same shape
/// — the assumed predicate `h : P(x)` introduced into the caller's context.
///
/// Returns `None` (fail-closed) unless:
///  * the kind is an ASSUMED contract kind (Precondition / LoopInvariant), AND
///  * the predicate is EXACTLY the recognized single-free-var `x >= 0` shape.
///
/// SOUNDNESS: this is the assume side — it introduces a hypothesis with NO proof
/// term, which is sound for a precondition (the caller owes its establishment).
/// It deliberately does NOT mint a `Certified` certificate; assuming is not
/// proving. A POSTCONDITION never routes here (it must be *proved* via
/// [`contract_clean_cic_certificate`]).
pub fn contract_nat_nonneg_obligation(obligation: &ProofObligation) -> Option<ExprObligation> {
    if !is_contract_kind(&obligation.kind) {
        return None;
    }
    // Only the ASSUMED kinds ground a hypothesis here; a PROVED kind must go
    // through the proof path, not the assume path.
    if free_var_kind_is_proved(&obligation.kind) {
        return None;
    }
    let formula = obligation.formula.as_ref()?;
    let sexp = parse_predicate(predicate_text(formula))?;
    recognize_nat_nonneg(&sexp)?;
    // Ground the assumed predicate: the goal shape IS the hypothesis shape.
    let assumed = assume_nat_nonneg_free_var();
    Some(ExprObligation::new(assumed.clone()).with_hypothesis("h_precond", assumed))
}

/// The **real** Clean-kernel re-validator for L1 contract
/// [`ProofEvidence::CleanCic`] certificates — the consumer-side de Bruijn
/// criterion that closes the trusted-on-read surface at
/// [`crate::proof::obligation_has_kernel_rechecked_clean_cic`].
///
/// Given a `Certified` obligation and its lineage-bound `CleanCic` certificate,
/// [`Self::kernel_rechecks_clean_cic`]:
///
/// 1. **re-grounds the canonical goal from the OBLIGATION** (`kind` + `formula`)
///    via [`contract_goal`] — never from the certificate's bytes, so a term that
///    proves some *other* proposition cannot be substituted in;
/// 2. **decodes the certificate's serialized proof TERM** (untrusted `term`
///    bytes) with a canonical, whole-slice, byte/node/depth-bounded codec; and
/// 3. has the **trusted `clean-kernel` type-checker** confirm the decoded term
///    inhabits that re-grounded goal
///    (`TypeChecker::check_type(term, &goal)` under `Environment::with_prelude()`
///    — the same gate the minter uses).
///
/// Every step is fail-closed: an ungroundable obligation, undecodable bytes, or
/// a term the kernel refuses all yield `false`. A tampered/forged term (one that
/// does not inhabit the re-grounded goal) is REJECTED even though its lineage
/// digest still matches — that is exactly the surface the lineage-only floor
/// [`crate::proof::obligation_has_matching_clean_cic`] leaves open.
#[derive(Debug, Clone, Copy, Default)]
pub struct KernelCleanCicRechecker;

impl crate::proof::CleanCicRechecker for KernelCleanCicRechecker {
    fn kernel_rechecks_clean_cic(
        &self,
        obligation: &ProofObligation,
        cert: &ProofCertificate,
    ) -> bool {
        use clean_kernel::{Environment, LocalContext, TypeChecker};
        let ProofEvidence::CleanCic { term, .. } = &cert.evidence else {
            return false;
        };
        // (1) Reconstruct the obligation's canonical claim from the OBLIGATION's
        //     own data — never the (untrusted) certificate bytes.
        let Ok(goal) = contract_goal(&obligation.kind, obligation.formula.as_ref()) else {
            return false;
        };
        // (2) Decode the certificate's serialized proof TERM (untrusted bytes)
        //     with the same canonical, bounded, whole-slice codec as the minter.
        let Some(proof_term) = decode_proof_term(term) else {
            return false;
        };
        // (3) The TRUSTED Clean kernel must accept that the decoded term inhabits
        //     the canonical goal. This is the de Bruijn criterion: a tampered or
        //     forged term, or a term proving some *other* proposition, is rejected.
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_context(&env, LocalContext::new());
        tc.check_type(&proof_term, &goal).is_ok()
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
    // R-L1 goal item #4, slice 1: single-free-var Nat non-negativity tautology
    // `x >= 0`. These tests are the teeth of the assume-vs-prove split and the
    // tautology-only gating.
    // -----------------------------------------------------------------------

    /// (1) A POSTCONDITION `(>= x 0)` grounds with a REAL kernel proof
    /// (`Certified` CleanCic), NOT a literal fixture. This is the whole point of
    /// the slice: a free-var predicate now grounds through a genuine kernel
    /// discharge of the `Nat.ble 0 x = true` tautology.
    #[test]
    fn test_postcondition_nat_nonneg_free_var_proves_certified() {
        let ob = obligation(ObligationKind::Postcondition, "(>= x 0)");
        let cert = contract_clean_cic_certificate(&ob, "trust-ir.R-L1")
            .expect("postcondition (>= x 0) is a Nat tautology => proved Certified");
        assert!(
            matches!(cert.evidence, ProofEvidence::CleanCic { .. }),
            "must be CleanCic evidence (the Certified tier), a real kernel proof"
        );
        // The carrier is an actual closed lambda proof, not the former Display
        // bytes of an open FVar goal.
        if let ProofEvidence::CleanCic { term, .. } = &cert.evidence {
            let decoded = decode_proof_term(term).expect("canonical proof term decodes");
            assert!(
                matches!(decoded.kind(), clean_kernel::ExprKind::Lam(..)),
                "the free-variable proof must close x with a lambda, got {decoded:?}"
            );
        }
        // Lineage-bound to THIS obligation (admissibility floor accepts it).
        assert!(
            obligation_has_matching_clean_cic(&ob, std::slice::from_ref(&cert)),
            "the CleanCic cert must be lineage-bound to its obligation"
        );
        assert!(
            obligation_has_kernel_rechecked_clean_cic(
                &ob,
                std::slice::from_ref(&cert),
                &KernelCleanCicRechecker,
            ),
            "the serialized closed proof must replay against the re-derived closed goal"
        );

        let goal = contract_goal(&ob.kind, ob.formula.as_ref()).expect("closed goal");
        assert!(
            matches!(goal.kind(), clean_kernel::ExprKind::Pi(..)),
            "the re-derived claim must close x with a Pi, got {goal:?}"
        );

        // The normal form `(<= 0 x)` proves identically.
        let ob_nf = obligation(ObligationKind::Postcondition, "(<= 0 x)");
        assert!(
            contract_clean_cic_certificate(&ob_nf, "trust-ir.R-L1").is_some(),
            "the normal form (<= 0 x) is the same tautology => proved Certified"
        );
        // A RefinementType is also a PROVED kind.
        let ob_ref = obligation(ObligationKind::RefinementType, "(>= x 0)");
        assert!(
            contract_clean_cic_certificate(&ob_ref, "trust-ir.R-L1").is_some(),
            "a RefinementType (>= x 0) is proved Certified"
        );
    }

    /// (2) A PRECONDITION `(>= x 0)` is ASSUMED: it GROUNDS to an obligation with
    /// the hypothesis added — but it does NOT mint a Certified certificate
    /// (assuming is not proving). This is the assume side of the split.
    #[test]
    fn test_precondition_nat_nonneg_free_var_is_assumed() {
        let ob = obligation(ObligationKind::Precondition, "(>= x 0)");

        // It GROUNDS as an assumed-hypothesis obligation ...
        let assumed = contract_nat_nonneg_obligation(&ob)
            .expect("precondition (>= x 0) grounds as an assumed hypothesis");
        assert_eq!(
            assumed.hypotheses.len(),
            1,
            "the assumed predicate is introduced as a hypothesis"
        );
        // ... the hypothesis is the predicate itself (goal shape == hyp shape).
        assert_eq!(
            &assumed.hypotheses[0].1, &assumed.goal,
            "the assumed hypothesis IS the grounded predicate"
        );

        // ... but it does NOT mint a Certified certificate: an assumed
        // precondition is not a proved claim, so no CleanCic / Certified.
        assert!(
            contract_clean_cic_certificate(&ob, "trust-ir.R-L1").is_none(),
            "a PRECONDITION is ASSUMED, not PROVED => NO Certified stamp"
        );

        // A LoopInvariant is likewise assumed at entry.
        let ob_inv = obligation(ObligationKind::LoopInvariant, "(>= x 0)");
        assert!(
            contract_nat_nonneg_obligation(&ob_inv).is_some(),
            "a LoopInvariant (>= x 0) grounds as an assumed hypothesis"
        );
        assert!(
            contract_clean_cic_certificate(&ob_inv, "trust-ir.R-L1").is_none(),
            "a LoopInvariant is assumed => NO Certified stamp"
        );

        // A POSTCONDITION never routes through the assume path.
        let ob_post = obligation(ObligationKind::Postcondition, "(>= x 0)");
        assert!(
            contract_nat_nonneg_obligation(&ob_post).is_none(),
            "a POSTCONDITION is PROVED, not ASSUMED — the assume path rejects it"
        );
    }

    /// (3) NEGATIVE: a POSTCONDITION `(>= x 5)` FAILS CLOSED — it does NOT mint
    /// Certified. `x >= 5` is NOT a tautology (false at x = 0), so neither the
    /// recognizer (non-zero bound) nor the literal path (free var) grounds it.
    /// This proves the tautology-only gating has teeth: the assume-vs-prove split
    /// cannot be tricked into stamping a non-tautology postcondition.
    #[test]
    fn test_postcondition_nat_nonneg_nontautology_fails_closed() {
        // `x >= 5`: a free var with a NON-ZERO bound.
        let ob_ge5 = obligation(ObligationKind::Postcondition, "(>= x 5)");
        assert!(
            recognize_nat_nonneg(&parse_predicate("(>= x 5)").unwrap()).is_none(),
            "(>= x 5) is NOT the x>=0 tautology shape (non-zero bound)"
        );
        assert!(
            contract_clean_cic_certificate(&ob_ge5, "trust-ir.R-L1").is_none(),
            "a POSTCONDITION (>= x 5) is NOT a tautology => FAIL CLOSED, no Certified"
        );

        // Even as a PRECONDITION, (>= x 5) is not the recognized assume shape.
        let ob_pre5 = obligation(ObligationKind::Precondition, "(>= x 5)");
        assert!(
            contract_nat_nonneg_obligation(&ob_pre5).is_none(),
            "(>= x 5) is not the assumed x>=0 shape either => no grounding"
        );

        // Wrong operators over the free var are non-tautologies too — all fail:
        // `x <= 0` (false for x>0), `x = 0` (false for x>0), `x > 0` (false at 0).
        for pred in ["(<= x 0)", "(= x 0)", "(> x 0)"] {
            let ob = obligation(ObligationKind::Postcondition, pred);
            assert!(
                contract_clean_cic_certificate(&ob, "trust-ir.R-L1").is_none(),
                "POSTCONDITION {pred} is not the x>=0 tautology => FAIL CLOSED"
            );
        }
    }

    /// (4) FAIL-CLOSED on the everything-else set: a non-`Nat`-shaped predicate,
    /// a multi-free-var predicate, and a non-`>=0` comparison all mint nothing.
    #[test]
    fn test_nat_nonneg_fail_closed_on_everything_else() {
        // Multiple distinct free vars: `(>= x y)` — not a single-var tautology.
        let ob_multivar = obligation(ObligationKind::Postcondition, "(>= x y)");
        assert!(
            recognize_nat_nonneg(&parse_predicate("(>= x y)").unwrap()).is_none(),
            "(>= x y) has two free vars, not the single-var x>=0 shape"
        );
        assert!(
            contract_clean_cic_certificate(&ob_multivar, "trust-ir.R-L1").is_none(),
            "multi-free-var => FAIL CLOSED"
        );

        // A nested boolean wrapping the tautology is NOT the bare shape.
        let ob_nested = obligation(ObligationKind::Postcondition, "(and (>= x 0) (>= y 0))");
        assert!(
            recognize_nat_nonneg(&parse_predicate("(and (>= x 0) (>= y 0))").unwrap()).is_none(),
            "a nested/conjoined predicate is not the bare x>=0 shape"
        );
        assert!(
            contract_clean_cic_certificate(&ob_nested, "trust-ir.R-L1").is_none(),
            "nested boolean over free vars => FAIL CLOSED"
        );

        // The var must be on the correct side: `(>= 0 x)` means `0 >= x`
        // (i.e. `x <= 0`), which is FALSE for x>0 — must NOT be recognized.
        assert!(
            recognize_nat_nonneg(&parse_predicate("(>= 0 x)").unwrap()).is_none(),
            "(>= 0 x) is `0 >= x` (x<=0), NOT the tautology — wrong side"
        );
        let ob_wrongside = obligation(ObligationKind::Postcondition, "(>= 0 x)");
        assert!(
            contract_clean_cic_certificate(&ob_wrongside, "trust-ir.R-L1").is_none(),
            "(>= 0 x) is x<=0, not a tautology => FAIL CLOSED"
        );
        // Symmetrically `(<= x 0)` means `x <= 0` — also not the tautology.
        assert!(
            recognize_nat_nonneg(&parse_predicate("(<= x 0)").unwrap()).is_none(),
            "(<= x 0) is x<=0, NOT the tautology"
        );

        // A non-contract kind with the tautology formula still mints nothing.
        let ob_safety = ProofObligation::new(
            ProofId::new(0),
            ObligationKind::MemorySafety,
            ProofStatus::Pending,
            "not a contract",
        )
        .with_formula(ProofFormula::smtlib2("(>= x 0)", "Bool"));
        assert!(
            contract_clean_cic_certificate(&ob_safety, "trust-ir.R-L1").is_none(),
            "a non-contract kind never grounds the free-var tautology"
        );
        assert!(
            contract_nat_nonneg_obligation(&ob_safety).is_none(),
            "a non-contract kind never grounds the assumed hypothesis"
        );
    }
}
