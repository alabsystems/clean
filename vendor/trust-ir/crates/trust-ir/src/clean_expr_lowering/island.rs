// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The pinned STATEMENT GROUNDER of the `clean_island` anchor (roadmap
//! WS1.13, slice 1; finding F-012).
//!
//! A user theorem travels as a `Custom { namespace: "lean.theorem", name }`
//! obligation whose first-order [`ProofFormula`] says what was proved, plus a
//! `CleanCic` certificate that carries the island of Clean declarations the
//! theorem lives in. The kernel proves a CIC proposition about island
//! constants; the obligation states an SMT-LIB formula. This module is the one
//! place that says which kernel proposition a formula MEANS, so that the
//! validator can require `type_of(theorem) ≡ G` by definitional equality and
//! a producer can compute the same `G` (and its statement digest) without
//! re-implementing the rule.
//!
//! # The slice-1 grammar (anything else is refused, fail-closed)
//!
//! ```text
//! stmt   := '(' 'forall' '(' binder+ ')' eq ')' | eq
//! binder := '(' SYM sort ')'           ; SYM a simple symbol, distinct,
//!                                      ; never an island constant's name
//!                                      ; and never a theory spelling
//! sort   := 'Bool'                     ; => kernel Bool
//!         | '(' '_' 'BitVec' W ')'     ; => kernel Nat, 1 <= W <= 128
//! eq     := '(' '=' term term ')'      ; => @Eq T lhs rhs, T = whnf(type lhs)
//!                                      ;    and T must be Nat or Bool
//! term   := NUMERAL                    ; => Nat literal (ASCII digits)
//!         | '(' '_' bvN W ')'          ; => Nat literal N, N < 2^W
//!         | 'true' | 'false'           ; => Bool.true / Bool.false
//!         | SYM                        ; a binder, or a 0-ary island constant
//!         | '(' SYM term+ ')'          ; an island constant applied
//!
//! ; an island constant (and a binder) is named only by an SMT simple symbol
//! ; that no SMT-LIB theory spells as a function symbol (`and`, `ite`, `mod`,
//! ; `fp`, `ubv_to_int`, …) or reserves as a family prefix (`bv*`, `fp.*`,
//! ; `str.*`, `re.*`, `seq.*`, …), so the text never reads, as SMT-LIB, as a
//! ; claim about a theory operator
//! ```
//!
//! The formula carries NO clause `bindings` and the obligation is scoped to
//! no function and no site: slice 1 states CLOSED theorems about island
//! constants. A contract clause over IR places is slice 2 and is refused.
//!
//! # Why a `BitVec` binder may be read over `Nat`
//!
//! A kernel theorem `∀ x : Nat, P x` is STRONGER than the formula's
//! `∀ x : BitVec w, P x`: every `w`-bit pattern is a `Nat` below `2^w`, and a
//! `clean_backend_tv` certificate states the emitted function's denotation
//! for EVERY `Nat` argument (the shared `Nat`-mod-`2^w` vocabulary). So the
//! over-approximation is sound for the universally quantified binders of
//! slice 1 (and would NOT be for an existential, which the grammar has not).
//! `Int` is refused outright: `∀ x : Nat` is WEAKER than `∀ x : Int`.
//!
//! # What this module does not decide
//!
//! It never checks that the kernel ACCEPTS `G` beyond well-typedness, and it
//! never decides which emitted function an island constant stands for. The
//! validator does both: the theorem's type must be definitionally equal to
//! `G`, and every constant in [`IslandStatement::cited`] must be the source
//! declaration of a function whose `clean_backend_tv` certificate is bound
//! to the SAME island.

use std::collections::{BTreeMap, BTreeSet};

use crate::proof::clause_typing::is_smt_simple_symbol;
use crate::proof::{ProofObligation, SmtSexp as Sexp, is_lean_theorem_kind, read_smtlib_term};
use clean_kernel::env::Environment;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, LocalContext, Name, TypeChecker};

/// Why a `lean.theorem` formula does not ground. Every variant is a refusal:
/// an ungroundable statement yields no goal, so nothing can be certified
/// against it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IslandStatementError {
    /// The obligation is not a `Custom { namespace: "lean.theorem", .. }` row.
    NotALeanTheorem,
    /// The obligation carries no formula.
    NoFormula,
    /// The formula or the obligation's scope is outside the slice-1 grammar.
    Unsupported(String),
    /// The formula grounds syntactically but the kernel refuses the result as
    /// a well-typed proposition.
    IllTyped(String),
}

impl core::fmt::Display for IslandStatementError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NotALeanTheorem => write!(
                f,
                "island statement: the obligation is not a `lean.theorem` row"
            ),
            Self::NoFormula => write!(f, "island statement: the obligation carries no formula"),
            Self::Unsupported(detail) => {
                write!(f, "island statement outside the slice-1 grammar: {detail}")
            }
            Self::IllTyped(detail) => write!(
                f,
                "island statement is not a well-typed kernel proposition: {detail}"
            ),
        }
    }
}

impl std::error::Error for IslandStatementError {}

/// A grounded `lean.theorem` statement.
#[derive(Debug, Clone)]
pub struct IslandStatement {
    /// The closed kernel proposition `G` the formula means.
    pub goal: Expr,
    /// The island constants `G` cites (by their kernel name's display form).
    /// The validator requires each to be the source declaration of a
    /// function whose translation-validation certificate is bound to the
    /// same island.
    pub cited: BTreeSet<String>,
}

fn unsupported(detail: impl Into<String>) -> IslandStatementError {
    IslandStatementError::Unsupported(detail.into())
}

/// Ground a `lean.theorem` obligation's formula into the kernel proposition
/// it means, in `env` (the anchor environment WITH the island installed).
/// `island` lists the names the island itself declares: they are the only
/// constants a statement may cite.
pub fn island_statement_goal(
    obligation: &ProofObligation,
    env: &Environment,
    island: &[Name],
) -> Result<IslandStatement, IslandStatementError> {
    if !is_lean_theorem_kind(&obligation.kind) {
        return Err(IslandStatementError::NotALeanTheorem);
    }
    if obligation.function.is_some() || obligation.site.is_some() {
        return Err(unsupported(
            "a slice-1 `lean.theorem` row states a CLOSED theorem: it is scoped to no function \
             and no site (a clause over IR places is slice 2)",
        ));
    }
    let formula = obligation
        .formula
        .as_ref()
        .ok_or(IslandStatementError::NoFormula)?;
    if !formula.bindings.is_empty() {
        return Err(unsupported(
            "a slice-1 statement binds no clause name to an IR place; its only names are \
             `forall` binders and island constants",
        ));
    }
    let text = formula.smtlib_text().ok_or_else(|| {
        unsupported(format!(
            "the formula states no single SMT-LIB text (schema {:?})",
            formula.schema
        ))
    })?;
    // The ONE SMT-LIB2 reader every trust-ir consumer reads formula text with
    // (`crate::proof::read_smtlib_term`): a text it refuses grounds nothing.
    let sexp = read_smtlib_term(text).map_err(|defect| {
        unsupported(format!(
            "the formula is not one SMT-LIB2 term trust-ir reads: it {defect}"
        ))
    })?;

    let island: BTreeMap<String, Name> = island
        .iter()
        .map(|name| (name.to_string(), name.clone()))
        .collect();
    let (binders, body) = split_forall(&sexp, &island)?;
    let mut cited = BTreeSet::new();
    let (lhs, rhs) = match body {
        Sexp::List(items) => match items.as_slice() {
            [Sexp::Atom(eq), lhs, rhs] if *eq == "=" => (lhs, rhs),
            _ => {
                return Err(unsupported(
                    "the statement body must be one equation `(= lhs rhs)`",
                ));
            }
        },
        Sexp::Atom(_) => {
            return Err(unsupported(
                "the statement body must be one equation `(= lhs rhs)`",
            ));
        }
    };
    let names: Vec<&str> = binders.iter().map(|(name, _)| name.as_str()).collect();
    let lhs = ground_term(lhs, &names, &island, env, &mut cited)?;
    let rhs = ground_term(rhs, &names, &island, env, &mut cited)?;

    let tc = TypeChecker::with_context(env, LocalContext::new());
    // The equation's carrier: the type of `lhs` under the binders, which must
    // not depend on them and must reduce to `Nat` or `Bool`.
    let lhs_closed = close(&binders, lhs.clone(), Binder::Lam);
    let mut ty = tc.infer_type(&lhs_closed).map_err(|error| {
        IslandStatementError::IllTyped(format!("the left-hand side has no type: {error:?}"))
    })?;
    for _ in &binders {
        ty = match ty.kind() {
            ExprKind::Pi(_, _, body) => body.as_ref().clone(),
            _ => {
                return Err(IslandStatementError::IllTyped(
                    "the left-hand side's type does not bind the statement's binders".to_string(),
                ));
            }
        };
    }
    if ty.has_loose_bvars() {
        return Err(unsupported(
            "the equation's carrier depends on a binder (a dependent type is not slice 1)",
        ));
    }
    let carrier = tc.whnf(&ty);
    let carrier_name = match carrier.kind() {
        ExprKind::Const(name, levels) if levels.is_empty() => name.to_string(),
        _ => String::new(),
    };
    if carrier_name != "Nat" && carrier_name != "Bool" {
        return Err(unsupported(format!(
            "the equation's carrier must reduce to `Nat` or `Bool`, got {carrier:?}"
        )));
    }
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [carrier, lhs, rhs],
    );
    let goal = close(&binders, eq, Binder::Pi);
    // FULL check (never `infer_only`): the goal is a well-typed proposition,
    // so a definitional-equality comparison against it is meaningful.
    tc.check_type(&goal, &Expr::prop()).map_err(|error| {
        IslandStatementError::IllTyped(format!("the grounded goal is not a Prop: {error:?}"))
    })?;
    Ok(IslandStatement { goal, cited })
}

#[derive(Clone, Copy)]
enum Binder {
    Lam,
    Pi,
}

fn close(binders: &[(String, Expr)], body: Expr, binder: Binder) -> Expr {
    binders
        .iter()
        .rev()
        .fold(body, |acc, (_, ty)| match binder {
            Binder::Lam => Expr::lam(BinderInfo::Default, ty.clone(), acc),
            Binder::Pi => Expr::pi(BinderInfo::Default, ty.clone(), acc),
        })
}

/// The `forall` binders of a statement, outermost first: each binder's name
/// and the kernel type its sort grounds to.
type Binders = Vec<(String, Expr)>;

/// Split an optional top-level `(forall (binders) body)`.
fn split_forall<'s, 't>(
    sexp: &'s Sexp<'t>,
    island: &BTreeMap<String, Name>,
) -> Result<(Binders, &'s Sexp<'t>), IslandStatementError> {
    let Sexp::List(items) = sexp else {
        return Ok((Vec::new(), sexp));
    };
    let [Sexp::Atom(head), Sexp::List(binders), body] = items.as_slice() else {
        return Ok((Vec::new(), sexp));
    };
    if *head != "forall" {
        return Ok((Vec::new(), sexp));
    }
    if binders.is_empty() {
        return Err(unsupported("`forall` binds nothing"));
    }
    let mut out: Binders = Vec::new();
    for binder in binders {
        let Sexp::List(pair) = binder else {
            return Err(unsupported("a `forall` binder must be `(name sort)`"));
        };
        let [Sexp::Atom(name), sort] = pair.as_slice() else {
            return Err(unsupported("a `forall` binder must be `(name sort)`"));
        };
        if !is_smt_simple_symbol(name) {
            return Err(unsupported(format!(
                "binder `{name}` is not an SMT simple symbol"
            )));
        }
        if smt_theory_spelling(name) {
            return Err(unsupported(format!(
                "binder `{name}` is spelled like an SMT-LIB theory function symbol: a slice-1 \
                 statement binds only names that read the same as SMT-LIB as they do grounded"
            )));
        }
        if island.contains_key(*name) {
            return Err(unsupported(format!(
                "binder `{name}` shadows the island constant of the same name"
            )));
        }
        if out.iter().any(|(seen, _)| seen == *name) {
            return Err(unsupported(format!("binder `{name}` is bound twice")));
        }
        out.push(((*name).to_string(), ground_sort(sort)?));
    }
    Ok((out, body))
}

/// `Bool` → kernel `Bool`; `(_ BitVec W)` → kernel `Nat` (see the module docs
/// for why that over-approximation is sound here); anything else is refused.
fn ground_sort(sort: &Sexp<'_>) -> Result<Expr, IslandStatementError> {
    match sort {
        Sexp::Atom(name) if *name == "Bool" => Ok(Expr::const_str("Bool")),
        Sexp::List(items) => match items.as_slice() {
            [
                Sexp::Atom(underscore),
                Sexp::Atom(bitvec),
                Sexp::Atom(width),
            ] if *underscore == "_" && *bitvec == "BitVec" => {
                if !ascii_u128(width).is_some_and(|w| (1..=128).contains(&w)) {
                    return Err(unsupported(format!(
                        "BitVec width `{width}` is not 1..=128"
                    )));
                }
                Ok(Expr::const_str("Nat"))
            }
            _ => Err(unsupported(format!(
                "sort {sort:?} is not `Bool` or `(_ BitVec W)`"
            ))),
        },
        Sexp::Atom(other) => Err(unsupported(format!(
            "sort `{other}` is not `Bool` or `(_ BitVec W)` (an `Int` binder would be \
             over-approximated in the UNSOUND direction)"
        ))),
    }
}

/// ASCII decimal digits only (a leading `+` is an SMT symbol, never a numeral).
fn ascii_u128(atom: &str) -> Option<u128> {
    if atom.is_empty() || !atom.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    atom.parse().ok()
}

fn nat_literal(n: u128) -> Expr {
    u64::try_from(n).map_or_else(|_| Expr::nat_lit_u128(n), Expr::nat_lit)
}

/// SMT-LIB theory function symbols (and reserved words) with a simple-symbol
/// spelling: Core, Ints, Reals_Ints, FixedSizeBitVectors (every `bv*` name
/// besides, and the 2.7 `ubv_to_int` / `sbv_to_int` / `int_to_bv`
/// conversions), ArraysEx, FloatingPoint (`fp` and the rounding-mode
/// constants; every `fp.*` name besides) and the solver-extension aliases the
/// common solvers accept (`implies`, `iff`, `if`, `int2bv`, `nat2bv`). A name
/// spelled like one is never cited — neither as an island constant nor as a
/// `forall` binder: the formula would then read, to anyone who reads it as
/// SMT-LIB, as a statement about the theory operator, while the kernel proves
/// one about the island constant (or a shadowing binder a reader may not
/// honour).
const SMT_THEORY_FUNCTION_SYMBOLS: &[&str] = &[
    "BINARY",
    "DECIMAL",
    "HEXADECIMAL",
    "NUMERAL",
    "RNA",
    "RNE",
    "RTN",
    "RTP",
    "RTZ",
    "STRING",
    "abs",
    "and",
    "char",
    "concat",
    "const",
    "distinct",
    "div",
    "divisible",
    "extract",
    "fp",
    "if",
    "iff",
    "implies",
    "int2bv",
    "int_to_bv",
    "is_int",
    "ite",
    "match",
    "mod",
    "nat2bv",
    "not",
    "or",
    "par",
    "repeat",
    "rotate_left",
    "rotate_right",
    "roundNearestTiesToAway",
    "roundNearestTiesToEven",
    "roundTowardNegative",
    "roundTowardPositive",
    "roundTowardZero",
    "sbv_to_int",
    "select",
    "sign_extend",
    "store",
    "to_fp",
    "to_fp_unsigned",
    "to_int",
    "to_real",
    "ubv_to_int",
    "xor",
    "zero_extend",
];

/// Name prefixes every symbol of an SMT-LIB theory (or a common solver
/// extension) begins with: FixedSizeBitVectors' `bv*`, FloatingPoint's
/// `fp.*`, Strings' `str.*` / `re.*` / `char.*`, and the sequence, set, bag,
/// integer-extension and finite-field families (`seq.*`, `set.*`, `bag.*`,
/// `int.*`, `ff.*`).
const SMT_THEORY_SYMBOL_PREFIXES: &[&str] = &[
    "bv", "fp.", "str.", "re.", "char.", "seq.", "set.", "bag.", "int.", "ff.",
];

/// Whether `name` is spelled like an SMT-LIB theory function symbol, a
/// reserved word, or a member of a theory's symbol family.
fn smt_theory_spelling(name: &str) -> bool {
    SMT_THEORY_FUNCTION_SYMBOLS.contains(&name)
        || SMT_THEORY_SYMBOL_PREFIXES
            .iter()
            .any(|prefix| name.starts_with(prefix))
}

/// Whether `name` may be cited as an island constant (or bound by a slice-1
/// `forall`): an SMT simple symbol (never `=`, `+`, a numeral, a reserved
/// word, …) that no SMT-LIB theory spells as a function symbol.
fn citable_island_constant_name(name: &str) -> bool {
    is_smt_simple_symbol(name) && !smt_theory_spelling(name)
}

fn island_constant(
    name: &str,
    island: &BTreeMap<String, Name>,
    env: &Environment,
    cited: &mut BTreeSet<String>,
) -> Result<Expr, IslandStatementError> {
    if !citable_island_constant_name(name) {
        return Err(unsupported(format!(
            "`{name}` is not a citable island-constant spelling: a slice-1 statement cites an \
             island constant only by an SMT simple symbol that no SMT-LIB theory spells as a \
             function symbol, so the formula means the same thing read as SMT-LIB as it does \
             grounded"
        )));
    }
    let kernel_name = island.get(name).ok_or_else(|| {
        unsupported(format!(
            "`{name}` is neither a binder nor a constant the island declares (a slice-1 \
             statement cites island constants and literals only)"
        ))
    })?;
    let info = env.get_const(kernel_name).ok_or_else(|| {
        IslandStatementError::IllTyped(format!(
            "island constant `{name}` is not in the environment"
        ))
    })?;
    if !info.level_params.is_empty() {
        return Err(unsupported(format!(
            "island constant `{name}` is universe-polymorphic (slice 1 cites monomorphic \
             constants only)"
        )));
    }
    cited.insert(name.to_string());
    Ok(Expr::const_(kernel_name.clone(), vec![]))
}

fn ground_term(
    term: &Sexp<'_>,
    binders: &[&str],
    island: &BTreeMap<String, Name>,
    env: &Environment,
    cited: &mut BTreeSet<String>,
) -> Result<Expr, IslandStatementError> {
    match term {
        Sexp::Atom(atom) => {
            if let Some(n) = ascii_u128(atom) {
                return Ok(nat_literal(n));
            }
            match *atom {
                "true" => return Ok(Expr::const_str("Bool.true")),
                "false" => return Ok(Expr::const_str("Bool.false")),
                _ => {}
            }
            if let Some(position) = binders.iter().position(|b| b == atom) {
                let depth = u32::try_from(binders.len() - 1 - position)
                    .map_err(|_| unsupported("too many binders"))?;
                return Ok(Expr::bvar(depth));
            }
            island_constant(atom, island, env, cited)
        }
        Sexp::List(items) => {
            let Some((Sexp::Atom(head), args)) = items.split_first() else {
                return Err(unsupported(format!("term {term:?} has no symbol head")));
            };
            if *head == "_" {
                // `(_ bvN W)`: an SMT bit-vector literal, read as the Nat N.
                let [Sexp::Atom(value), Sexp::Atom(width)] = args else {
                    return Err(unsupported(format!(
                        "indexed term {term:?} is not `(_ bvN W)`"
                    )));
                };
                let n = value
                    .strip_prefix("bv")
                    .and_then(ascii_u128)
                    .ok_or_else(|| {
                        unsupported(format!("indexed term {term:?} is not `(_ bvN W)`"))
                    })?;
                let width = ascii_u128(width)
                    .filter(|w| (1..=128).contains(w))
                    .ok_or_else(|| {
                        unsupported(format!("BitVec width in {term:?} is not 1..=128"))
                    })?;
                if width < 128 && n >> width != 0 {
                    return Err(unsupported(format!(
                        "bit-vector literal {term:?} does not fit its width"
                    )));
                }
                return Ok(nat_literal(n));
            }
            if args.is_empty() {
                return Err(unsupported(format!("`({head})` applies nothing")));
            }
            if binders.contains(head) {
                return Err(unsupported(format!(
                    "`{head}` is a binder, not a function (slice 1 has no higher-order binders)"
                )));
            }
            let function = island_constant(head, island, env, cited)?;
            let args = args
                .iter()
                .map(|arg| ground_term(arg, binders, island, env, cited))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::apps(function, args))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof::{ObligationKind, ProofFormula, ProofStatus};
    use crate::value::ProofId;
    use clean_kernel::env::Declaration;

    fn nat() -> Expr {
        Expr::const_str("Nat")
    }

    fn env_with_fst3() -> (Environment, Vec<Name>) {
        let mut env = Environment::with_prelude();
        let name = Name::from_string("Lib.fst3");
        let ty = Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(
                BinderInfo::Default,
                nat(),
                Expr::pi(BinderInfo::Default, nat(), nat()),
            ),
        );
        let value = Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::lam(BinderInfo::Default, nat(), Expr::bvar(2)),
            ),
        );
        env.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .expect("fst3 is well-typed");
        (env, vec![name])
    }

    fn theorem(text: &str) -> ProofObligation {
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Custom {
                namespace: "lean.theorem".to_string(),
                name: "Lib.fst3_eq".to_string(),
            },
            ProofStatus::Pending,
            "Lib.fst3_eq",
        )
        .with_formula(ProofFormula::smtlib2(text, "Bool"))
    }

    const FST3_EQ: &str =
        "(forall ((a (_ BitVec 64)) (b (_ BitVec 64)) (c (_ BitVec 64))) (= (Lib.fst3 a b c) a))";

    #[test]
    fn fst3_eq_grounds_to_a_closed_nat_equation_citing_fst3() {
        let (env, island) = env_with_fst3();
        let statement = island_statement_goal(&theorem(FST3_EQ), &env, &island).expect("grounds");
        assert_eq!(
            statement
                .cited
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            ["Lib.fst3"]
        );
        assert!(!statement.goal.has_loose_bvars());
    }

    #[test]
    fn slice_one_refusals_are_named() {
        let (env, island) = env_with_fst3();
        let refuse = |text: &str| island_statement_goal(&theorem(text), &env, &island);
        // An `Int` binder over-approximates in the unsound direction.
        assert!(matches!(
            refuse("(forall ((a Int)) (= (Lib.fst3 a a a) a))"),
            Err(IslandStatementError::Unsupported(d)) if d.contains("UNSOUND")
        ));
        // A prelude function is not an island constant.
        assert!(matches!(
            refuse("(forall ((a (_ BitVec 8))) (= (Nat.add a 0) a))"),
            Err(IslandStatementError::Unsupported(d)) if d.contains("island declares")
        ));
        // A binder may not shadow an island constant.
        assert!(matches!(
            refuse("(forall ((Lib.fst3 Bool)) (= Lib.fst3 Lib.fst3))"),
            Err(IslandStatementError::Unsupported(d)) if d.contains("shadows")
        ));
        // Not an equation.
        assert!(refuse("(forall ((a Bool)) (and a a))").is_err());
        // `+1` is a symbol, never the numeral 1.
        assert!(refuse("(= (Lib.fst3 +1 0 0) 1)").is_err());
        // An over-wide bit-vector literal.
        assert!(refuse("(= (Lib.fst3 (_ bv256 8) 0 0) 0)").is_err());
        // An island constant spelled like an SMT-LIB theory function symbol.
        let mut spelled = env.clone();
        let bvadd = Name::from_string("bvadd");
        spelled
            .add_decl(Declaration::Definition {
                name: bvadd.clone(),
                level_params: vec![],
                type_: Expr::pi(
                    BinderInfo::Default,
                    nat(),
                    Expr::pi(BinderInfo::Default, nat(), nat()),
                ),
                value: Expr::lam(
                    BinderInfo::Default,
                    nat(),
                    Expr::lam(BinderInfo::Default, nat(), Expr::bvar(1)),
                ),
                is_reducible: true,
            })
            .expect("bvadd is well-typed");
        let mut with_bvadd = island.clone();
        with_bvadd.push(bvadd);
        assert!(matches!(
            island_statement_goal(&theorem("(= (bvadd 1 2) 1)"), &spelled, &with_bvadd),
            Err(IslandStatementError::Unsupported(d)) if d.contains("citable")
        ));
        // Ill-typed: Bool compared with Nat.
        assert!(matches!(
            refuse("(= (Lib.fst3 1 2 3) true)"),
            Err(IslandStatementError::IllTyped(_))
        ));
        // Review (WS1.13): the theory-spelling rule covers every SMT-LIB theory
        // the formula could be read under, not only Core/Ints/BV/Arrays —
        // FloatingPoint (`fp`, `fp.*`, a rounding-mode constant), Strings
        // (`str.*`), the 2.7 bit-vector conversions (`ubv_to_int`) and the
        // solver aliases (`implies`). Each is a well-typed island constant the
        // island declares, refused BY NAME, never as ill-typed.
        for (spelled, arity) in [
            ("fp", 1usize),
            ("fp.add", 2),
            ("str.len", 1),
            ("seq.nth", 2),
            ("ubv_to_int", 1),
            ("sbv_to_int", 1),
            ("implies", 2),
            ("RNE", 0),
            ("roundTowardZero", 0),
        ] {
            let mut spelled_env = env.clone();
            let name = Name::from_string(spelled);
            let type_ = (0..arity).fold(nat(), |acc, _| Expr::pi(BinderInfo::Default, nat(), acc));
            let value = (0..arity).fold(Expr::nat_lit(0), |acc, _| {
                Expr::lam(BinderInfo::Default, nat(), acc)
            });
            spelled_env
                .add_decl(Declaration::Definition {
                    name: name.clone(),
                    level_params: vec![],
                    type_,
                    value,
                    is_reducible: true,
                })
                .unwrap_or_else(|e| panic!("{spelled} is well-typed: {e:?}"));
            let mut with_spelled = island.clone();
            with_spelled.push(name);
            let applied = if arity == 0 {
                spelled.to_string()
            } else {
                format!("({spelled}{})", " 1".repeat(arity))
            };
            let text = format!("(= {applied} 0)");
            assert!(
                matches!(
                    island_statement_goal(&theorem(&text), &spelled_env, &with_spelled),
                    Err(IslandStatementError::Unsupported(d)) if d.contains("citable")
                ),
                "`{spelled}` must be refused as an uncitable theory spelling: {text}"
            );
        }
        // The same rule binds a `forall` binder: a binder spelled like a theory
        // operator would be read, by a solver that does not honour shadowing, as
        // the operator.
        for binder in ["and", "ite", "bvx", "fp.x", "str.x", "implies", "RNE"] {
            let text =
                format!("(forall (({binder} (_ BitVec 8))) (= (Lib.fst3 {binder} 0 0) {binder}))");
            assert!(
                matches!(
                    refuse(&text),
                    Err(IslandStatementError::Unsupported(d)) if d.contains("spelled like an SMT-LIB theory")
                ),
                "binder `{binder}` must be refused by the theory-spelling rule: {:?}",
                refuse(&text)
            );
        }
        // Control: an ordinary binder name still grounds (the rule is the
        // spelling, not the shape of the statement).
        assert!(refuse("(forall ((x (_ BitVec 8))) (= (Lib.fst3 x 0 0) x))").is_ok());
        // Scoped to a function: slice 2.
        let scoped = theorem(FST3_EQ).with_function(crate::value::FuncId::new(0));
        assert!(matches!(
            island_statement_goal(&scoped, &env, &island),
            Err(IslandStatementError::Unsupported(d)) if d.contains("CLOSED")
        ));
    }
}
