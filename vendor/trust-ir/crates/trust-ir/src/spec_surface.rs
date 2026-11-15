// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The typed surface of a [`SpecEnforcementMode::Linked`] spec module.
//!
//! [`SpecVar::ty`](crate::SpecVar::ty) and
//! [`SpecInvariant::formula`](crate::SpecInvariant::formula) are `String`s on
//! the wire (a typed invariant carrier is a later wire version). Under
//! [`SpecEnforcementMode::DesignOnly`] they stay opaque, descriptive text. A
//! `Linked` module is a CERTIFICATION claim, and a certification claim over a
//! formula nobody can read is decorative: garbage syntax, an undeclared
//! variable and an ill-sorted comparison all used to validate and certify
//! exactly like a meaningful invariant (roadmap WS1.10, finding F-014). So
//! under `Linked`, and only there, this module reads both strings and FAILS
//! CLOSED on anything outside the surface below.
//!
//! **Variable types** ([`parse_spec_var_sort`]), exact text, no whitespace:
//!
//! * `Bool` → [`SpecSort::Bool`];
//! * `Int` → [`SpecSort::Int`];
//! * `BitVec(<w>)`, `<w>` a positive decimal with no leading zero →
//!   [`SpecSort::BitVec`];
//! * `<lo>..<hi>`, each an optionally `-`-signed decimal with no leading zero
//!   and `lo <= hi` → [`SpecSort::Int`] (an integer range; the bounds are the
//!   model's domain, the sort is `Int`).
//!
//! **Invariant formulas** ([`check_linked_invariant`]) are one quantifier-free
//! SMT-LIB2 term of sort `Bool`, read by trust-ir's one SMT-LIB2 reader
//! ([`read_smtlib_term`], which the contract grounder and
//! [`smt_free_symbols`] read with too) and then sort-checked:
//!
//! * every free symbol is a declared variable of the machine. A primed `x'`
//!   is no SMT-LIB2 token and is refused by the reader: a successor value is
//!   named through a [`ClausePlace::SpecVarNext`](crate::proof::ClausePlace::SpecVarNext)
//!   binding, and only an action relation has one;
//! * core: `true`, `false`, `not`, `and`, `or`, `xor`, `=>` (Bool), `=` and
//!   `distinct` (two or more arguments of one sort), `ite` (a Bool condition
//!   and two branches of one sort);
//! * integers: numerals (no leading zero), `+` `*` (two or more), `-` (one
//!   or more), `div` `mod` (exactly two), `abs` (one), and the chainable
//!   comparisons `<=` `<` `>=` `>` over `Int` only;
//! * bit-vectors: `#x…` / `#b…` literals, the binary operators `bvadd bvsub
//!   bvmul bvudiv bvurem bvsdiv bvsrem bvsmod bvand bvor bvxor bvshl bvlshr
//!   bvashr` and the unary `bvnot` `bvneg` over one width, and the
//!   comparisons `bvult bvule bvugt bvuge bvslt bvsle bvsgt bvsge` over one
//!   width.
//!
//! Everything else — TLA+ surface syntax, binders, indexed identifiers,
//! decimals (there is no `Real` variable type), uninterpreted functions, a
//! mixed-sort comparison, and every text the reader refuses (a character
//! outside printable ASCII and the SMT-LIB2 whitespace set — a no-break space
//! is NOT whitespace to a solver —, an atom that is no SMT-LIB2 token, nesting
//! deeper than [`MAX_LINKED_FORMULA_DEPTH`]) — is a refusal with a specific
//! detail. A variable may not be named after any function symbol of the
//! `Core` / `Ints` / `FixedSizeBitVectors` theories, admitted or not. The surface is
//! deliberately the SMT-LIB2 subset `ProofFormula` shares (roadmap DECIDE
//! option A), not a TLA+ parser.

use std::collections::{BTreeMap, BTreeSet};

use crate::proof::clause_typing::{is_smt_simple_symbol, smt_free_symbols};
use crate::proof::{MAX_SMTLIB_TERM_DEPTH, SmtSexp, read_smtlib_term};

/// The sort of a `Linked` spec variable or invariant subterm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SpecSort {
    /// Booleans.
    Bool,
    /// Mathematical integers (also the sort of an integer range `lo..hi`).
    Int,
    /// Fixed-width bit-vectors of the given positive width.
    BitVec(u32),
}

impl core::fmt::Display for SpecSort {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SpecSort::Bool => f.write_str("Bool"),
            SpecSort::Int => f.write_str("Int"),
            SpecSort::BitVec(width) => write!(f, "(_ BitVec {width})"),
        }
    }
}

/// A canonical decimal: ASCII digits, no leading zero unless it is `0`.
fn is_canonical_decimal(text: &str) -> bool {
    !text.is_empty()
        && text.chars().all(|c| c.is_ascii_digit())
        && (text == "0" || !text.starts_with('0'))
}

/// A canonical, optionally `-`-signed decimal integer (`-0` is refused), as
/// `(negative, digits)`. Deliberately NOT narrowed to a machine integer: the
/// range is a mathematical `Int` domain, so a bound beyond `i128` is still a
/// well-formed range, never a parse failure.
fn parse_signed_decimal(text: &str) -> Option<(bool, &str)> {
    let (negative, digits) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    if !is_canonical_decimal(digits) || (negative && digits == "0") {
        return None;
    }
    Some((negative, digits))
}

/// `lo <= hi` over canonical signed decimals of any magnitude.
fn signed_decimal_le(lo: (bool, &str), hi: (bool, &str)) -> bool {
    // Canonical digits (no leading zero) order by length, then lexically.
    let magnitude = |a: &str, b: &str| a.len().cmp(&b.len()).then_with(|| a.cmp(b));
    match (lo, hi) {
        ((true, _), (false, _)) => true,
        ((false, _), (true, _)) => false,
        ((false, a), (false, b)) => magnitude(a, b).is_le(),
        ((true, a), (true, b)) => magnitude(b, a).is_le(),
    }
}

/// Parse a `Linked` [`SpecVar::ty`](crate::SpecVar::ty) into its sort, or say
/// exactly why it is outside the surface (see the module docs).
pub fn parse_spec_var_sort(text: &str) -> Result<SpecSort, String> {
    match text {
        "Bool" => return Ok(SpecSort::Bool),
        "Int" => return Ok(SpecSort::Int),
        _ => {}
    }
    if let Some(width) = text
        .strip_prefix("BitVec(")
        .and_then(|rest| rest.strip_suffix(')'))
    {
        return match width.parse::<u32>() {
            Ok(w) if w > 0 && is_canonical_decimal(width) => Ok(SpecSort::BitVec(w)),
            _ => Err(format!(
                "type {text:?}: a bit-vector width must be a positive decimal u32 with no \
                 leading zero"
            )),
        };
    }
    if let Some((lo, hi)) = text.split_once("..") {
        return match (parse_signed_decimal(lo), parse_signed_decimal(hi)) {
            (Some(lo), Some(hi)) if signed_decimal_le(lo, hi) => Ok(SpecSort::Int),
            (Some(_), Some(_)) => Err(format!("type {text:?}: an empty integer range (lo > hi)")),
            _ => Err(format!(
                "type {text:?}: range bounds must be canonical decimal integers"
            )),
        };
    }
    Err(format!(
        "type {text:?} is not one of `Bool`, `Int`, `BitVec(<w>)` or `<lo>..<hi>`"
    ))
}

/// Why a `Linked` variable NAME cannot be denoted by an invariant, if it
/// cannot: it must be an SMT simple symbol ([`is_smt_simple_symbol`], which a
/// primed `x'` is not), and must not be an operator of the surface (`and`,
/// `bvadd`, `ite`, …) or another function symbol of its theories (`concat`,
/// `bvcomp`, … — a variable may not shadow a theory symbol, as in SMT-LIB2
/// itself).
pub fn linked_var_name_problem(name: &str) -> Option<String> {
    if !is_smt_simple_symbol(name) {
        return Some(format!(
            "name {name:?} is not an SMT simple symbol, so no invariant can denote it"
        ));
    }
    if is_surface_operator(name) {
        return Some(format!(
            "name {name:?} is an operator of the Linked invariant surface (or a function \
             symbol of its SMT-LIB2 theories) and cannot also be a variable"
        ));
    }
    None
}

/// A variable environment for [`check_linked_invariant`]: each declared name
/// and its sort. A name mapped to `None` is declared more than once (already
/// refused structurally) and is refused again at every use rather than
/// resolved to either declaration.
pub type SpecVarEnv<'a> = BTreeMap<&'a str, Option<SpecSort>>;

/// Check one `Linked` invariant formula against the machine's variables:
/// it must read as one quantifier-free SMT-LIB2 term of sort `Bool` under the
/// surface in the module docs. Returns the specific reason on refusal.
///
/// A variable whose declared type did not parse must be absent from `vars`
/// (its declaration is refused on its own); a use of it is then refused as
/// undeclared-in-the-surface rather than guessed.
pub fn check_linked_invariant(formula: &str, vars: &SpecVarEnv<'_>) -> Result<(), String> {
    let term = read_smtlib_term(formula).map_err(|defect| {
        format!("formula {formula:?} is not one quantifier-free SMT-LIB2 term: it {defect}")
    })?;
    let Some(free) = smt_free_symbols(formula) else {
        return Err(format!(
            "formula {formula:?} is not one quantifier-free SMT-LIB2 term (a binder, an indexed \
             or annotated identifier, the empty list, or an argument that is neither a name nor \
             a literal)"
        ));
    };
    for name in &free {
        resolve_variable(name, vars)?;
    }
    match sort_of(&term, vars)? {
        SpecSort::Bool => Ok(()),
        other => Err(format!(
            "formula {formula:?} has sort {other}, but an invariant is a Bool term"
        )),
    }
}

/// The deepest parenthesis nesting a `Linked` invariant may use: the one
/// reader's bound ([`MAX_SMTLIB_TERM_DEPTH`]). The sort checker recurses once
/// per level, so an unbounded depth is a validator stack overflow (a process
/// abort, not a refusal) on hostile input.
pub const MAX_LINKED_FORMULA_DEPTH: usize = MAX_SMTLIB_TERM_DEPTH;

fn resolve_variable(name: &str, vars: &SpecVarEnv<'_>) -> Result<SpecSort, String> {
    match vars.get(name) {
        Some(Some(sort)) => Ok(*sort),
        Some(None) => Err(format!(
            "variable `{name}` is declared more than once, so its sort is ambiguous"
        )),
        None => Err(format!(
            "undeclared variable `{name}` (every free symbol must be a declared SpecVar with a \
             parsed type)"
        )),
    }
}

fn literal_sort(atom: &str) -> Option<Result<SpecSort, String>> {
    if let Some(hex) = atom.strip_prefix("#x") {
        let width = u32::try_from(hex.len())
            .ok()
            .and_then(|n| n.checked_mul(4))
            .filter(|w| *w > 0 && hex.chars().all(|c| c.is_ascii_hexdigit()));
        return Some(
            width
                .map(SpecSort::BitVec)
                .ok_or_else(|| format!("`{atom}` is not a hexadecimal bit-vector literal")),
        );
    }
    if let Some(bin) = atom.strip_prefix("#b") {
        let width = u32::try_from(bin.len())
            .ok()
            .filter(|w| *w > 0 && bin.chars().all(|c| c == '0' || c == '1'));
        return Some(
            width
                .map(SpecSort::BitVec)
                .ok_or_else(|| format!("`{atom}` is not a binary bit-vector literal")),
        );
    }
    // The reader admitted the atom, so a leading digit makes it a numeral
    // (never a leading zero) or a decimal.
    if atom.starts_with(|c: char| c.is_ascii_digit()) {
        return Some(if atom.contains('.') {
            Err(format!(
                "decimal `{atom}` is a Real literal; the Linked surface has no Real sort"
            ))
        } else {
            Ok(SpecSort::Int)
        });
    }
    None
}

const INT_NARY: &[&str] = &["+", "*"];
const INT_BINARY: &[&str] = &["div", "mod"];
const INT_COMPARE: &[&str] = &["<=", "<", ">=", ">"];
const BOOL_NARY: &[&str] = &["and", "or", "xor", "=>"];
const BV_BINARY: &[&str] = &[
    "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvand", "bvor",
    "bvxor", "bvshl", "bvlshr", "bvashr",
];
const BV_UNARY: &[&str] = &["bvnot", "bvneg"];
const BV_COMPARE: &[&str] = &[
    "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
];

/// Function symbols of the SMT-LIB2 `Core`, `Ints` and `FixedSizeBitVectors`
/// theories (with the `QF_BV` logic extensions) that the surface does NOT
/// admit as operators. A variable may not take one of these names either:
/// SMT-LIB2 forbids declaring a constant whose name is already in the logic's
/// signature, so such a module would validate here and then be unloadable by
/// every conforming consumer of the invariant.
const THEORY_RESERVED: &[&str] = &[
    "divisible",
    "concat",
    "extract",
    "repeat",
    "zero_extend",
    "sign_extend",
    "rotate_left",
    "rotate_right",
    "bvnand",
    "bvnor",
    "bvxnor",
    "bvcomp",
];

/// True iff `name` is an operator symbol of the `Linked` invariant surface,
/// or another function symbol of the theories it draws on
/// ([`THEORY_RESERVED`]).
fn is_surface_operator(name: &str) -> bool {
    matches!(name, "not" | "=" | "distinct" | "ite" | "-" | "abs")
        || THEORY_RESERVED.contains(&name)
        || [
            INT_NARY,
            INT_BINARY,
            INT_COMPARE,
            BOOL_NARY,
            BV_BINARY,
            BV_UNARY,
            BV_COMPARE,
        ]
        .iter()
        .any(|table| table.contains(&name))
}

fn sort_of(term: &SmtSexp<'_>, vars: &SpecVarEnv<'_>) -> Result<SpecSort, String> {
    let render = SmtSexp::canonical;
    let items = match term {
        SmtSexp::Atom(atom) => {
            return match *atom {
                "true" | "false" => Ok(SpecSort::Bool),
                _ => match literal_sort(atom) {
                    Some(sort) => sort,
                    None => resolve_variable(atom, vars),
                },
            };
        }
        SmtSexp::List(items) => items,
    };
    let Some((SmtSexp::Atom(op), args)) = items.split_first() else {
        return Err(format!(
            "`{}`: an application's head must be an operator symbol",
            render(term)
        ));
    };
    let op = *op;
    let sorts = args
        .iter()
        .map(|arg| sort_of(arg, vars))
        .collect::<Result<Vec<_>, _>>()?;
    let whole = || render(term);
    let arity = |ok: bool, expected: &str| -> Result<(), String> {
        if ok {
            Ok(())
        } else {
            Err(format!(
                "`{}`: `{op}` takes {expected} argument(s), got {}",
                whole(),
                args.len()
            ))
        }
    };
    let all = |want: SpecSort| -> Result<(), String> {
        match sorts.iter().position(|sort| *sort != want) {
            None => Ok(()),
            Some(index) => Err(format!(
                "ill-sorted `{}`: `{op}` expects {want} arguments, but argument {} `{}` has \
                 sort {}",
                whole(),
                index + 1,
                render(&args[index]),
                sorts[index]
            )),
        }
    };
    let same = || -> Result<SpecSort, String> {
        let first = sorts[0];
        match sorts.iter().position(|sort| *sort != first) {
            None => Ok(first),
            Some(index) => Err(format!(
                "ill-sorted `{}`: `{op}` needs arguments of one sort, but argument 1 has sort \
                 {first} and argument {} `{}` has sort {}",
                whole(),
                index + 1,
                render(&args[index]),
                sorts[index]
            )),
        }
    };
    let bitvec = || -> Result<u32, String> {
        match same()? {
            SpecSort::BitVec(width) => Ok(width),
            other => Err(format!(
                "ill-sorted `{}`: `{op}` expects bit-vector arguments, got {other}",
                whole()
            )),
        }
    };
    match op {
        "not" => {
            arity(args.len() == 1, "exactly 1")?;
            all(SpecSort::Bool)?;
            Ok(SpecSort::Bool)
        }
        _ if BOOL_NARY.contains(&op) => {
            arity(args.len() >= 2, "at least 2")?;
            all(SpecSort::Bool)?;
            Ok(SpecSort::Bool)
        }
        "=" | "distinct" => {
            arity(args.len() >= 2, "at least 2")?;
            same()?;
            Ok(SpecSort::Bool)
        }
        "ite" => {
            arity(args.len() == 3, "exactly 3")?;
            if sorts[0] != SpecSort::Bool {
                return Err(format!(
                    "ill-sorted `{}`: the `ite` condition `{}` has sort {}, not Bool",
                    whole(),
                    render(&args[0]),
                    sorts[0]
                ));
            }
            if sorts[1] != sorts[2] {
                return Err(format!(
                    "ill-sorted `{}`: the `ite` branches have sorts {} and {}",
                    whole(),
                    sorts[1],
                    sorts[2]
                ));
            }
            Ok(sorts[1])
        }
        _ if INT_NARY.contains(&op) => {
            arity(args.len() >= 2, "at least 2")?;
            all(SpecSort::Int)?;
            Ok(SpecSort::Int)
        }
        "-" => {
            arity(!args.is_empty(), "at least 1")?;
            all(SpecSort::Int)?;
            Ok(SpecSort::Int)
        }
        "abs" => {
            arity(args.len() == 1, "exactly 1")?;
            all(SpecSort::Int)?;
            Ok(SpecSort::Int)
        }
        _ if INT_BINARY.contains(&op) => {
            arity(args.len() == 2, "exactly 2")?;
            all(SpecSort::Int)?;
            Ok(SpecSort::Int)
        }
        _ if INT_COMPARE.contains(&op) => {
            arity(args.len() >= 2, "at least 2")?;
            all(SpecSort::Int)?;
            Ok(SpecSort::Bool)
        }
        _ if BV_BINARY.contains(&op) => {
            arity(args.len() == 2, "exactly 2")?;
            Ok(SpecSort::BitVec(bitvec()?))
        }
        _ if BV_UNARY.contains(&op) => {
            arity(args.len() == 1, "exactly 1")?;
            Ok(SpecSort::BitVec(bitvec()?))
        }
        _ if BV_COMPARE.contains(&op) => {
            arity(args.len() == 2, "exactly 2")?;
            bitvec()?;
            Ok(SpecSort::Bool)
        }
        _ => Err(format!(
            "`{}`: `{op}` is not an operator of the Linked invariant surface (no \
             uninterpreted functions, no TLA+ operators)",
            whole()
        )),
    }
}

/// The declared-variable environment of one `Linked` machine: every variable
/// whose name and type both parse, a duplicated name mapped to `None`.
pub fn linked_var_env<'a>(vars: impl IntoIterator<Item = (&'a str, &'a str)>) -> SpecVarEnv<'a> {
    let mut env: SpecVarEnv<'a> = BTreeMap::new();
    let mut seen = BTreeSet::new();
    for (name, ty) in vars {
        if !seen.insert(name) {
            env.insert(name, None);
            continue;
        }
        if linked_var_name_problem(name).is_some() {
            continue;
        }
        if let Ok(sort) = parse_spec_var_sort(ty) {
            env.insert(name, Some(sort));
        }
    }
    env
}

/// Whether a typed carrier's SMT-LIB2 rendering and the string `formula` it
/// claims to type are the SAME term (v46, S3 under `Linked`).
///
/// `rename` maps each of the carrier's bound names to the state variable it
/// indexes; the carrier is read with those names substituted (simultaneously,
/// atoms only — a bound name can never be an operator, since
/// [`linked_var_name_problem`] refuses one) and compared STRUCTURALLY with
/// `formula`: the same s-expression, whitespace aside. Two renderings that
/// differ are two predicates, and a module carrying both has not said which
/// one its invariant is.
///
/// Either text that does not read as one term is that text's own refusal
/// ([`check_linked_invariant`]) and is reported as agreeing here, so a garbage
/// rendering is named once, by its own rule.
pub fn linked_renderings_agree(
    typed: &str,
    rename: &BTreeMap<&str, &str>,
    formula: &str,
) -> Result<(), String> {
    let (Ok(typed_term), Ok(formula_term)) = (read_smtlib_term(typed), read_smtlib_term(formula))
    else {
        return Ok(());
    };
    let over_vars = typed_term.canonical_with(|atom| rename.get(atom).copied().unwrap_or(atom));
    let expected = formula_term.canonical();
    if over_vars == expected {
        Ok(())
    } else {
        Err(format!(
            "the typed carrier reads as {over_vars} over the machine's variables, but the \
             invariant's `formula` reads as {expected}; a module carrying two different \
             predicates has not said which one the invariant is"
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn env(vars: &[(&'static str, &'static str)]) -> SpecVarEnv<'static> {
        linked_var_env(vars.iter().copied())
    }

    #[test]
    fn renderings_agree_structurally_after_renaming_bound_names() {
        let rename: BTreeMap<&str, &str> = [("s", "seq"), ("e", "empty")].into_iter().collect();
        assert_eq!(
            linked_renderings_agree(
                "(and (<= s 7) (not e))",
                &rename,
                "(and (<= seq 7) (not empty))"
            ),
            Ok(())
        );
        // Whitespace is not content.
        assert_eq!(
            linked_renderings_agree("( <= s   7 )", &rename, "(<= seq 7)"),
            Ok(())
        );
        // A different constant is a different predicate.
        let err = linked_renderings_agree("(<= s 8)", &rename, "(<= seq 7)").unwrap_err();
        assert!(
            err.contains("(<= seq 8)") && err.contains("(<= seq 7)"),
            "{err}"
        );
        // A different variable is a different predicate, even at the same sort.
        let err = linked_renderings_agree("(<= e 7)", &rename, "(<= seq 7)").unwrap_err();
        assert!(err.contains("(<= empty 7)"), "{err}");
        // Only bound names are renamed: an unbound `seq` in the carrier is
        // compared as spelled (S3's undeclared-symbol refusal owns it).
        let only_s: BTreeMap<&str, &str> = [("s", "seq")].into_iter().collect();
        assert!(linked_renderings_agree("(<= seq 7)", &only_s, "(<= seq 7)").is_ok());
        // Text that does not read as one term is its own refusal, not a
        // disagreement.
        assert_eq!(
            linked_renderings_agree("(<= s", &rename, "(<= seq 7)"),
            Ok(())
        );
        assert_eq!(
            linked_renderings_agree("(<= s 7)", &rename, "(<= seq"),
            Ok(())
        );
    }

    #[test]
    fn var_types_parse_only_the_four_forms() {
        assert_eq!(parse_spec_var_sort("Bool"), Ok(SpecSort::Bool));
        assert_eq!(parse_spec_var_sort("Int"), Ok(SpecSort::Int));
        assert_eq!(parse_spec_var_sort("BitVec(8)"), Ok(SpecSort::BitVec(8)));
        assert_eq!(parse_spec_var_sort("0..7"), Ok(SpecSort::Int));
        assert_eq!(parse_spec_var_sort("-3..-3"), Ok(SpecSort::Int));
        for bad in [
            "",
            "Nat",
            "BOOLEAN",
            " Int",
            "Int ",
            "bool",
            "BitVec(0)",
            "BitVec(08)",
            "BitVec()",
            "BitVec(x)",
            "7..0",
            "0..",
            "..7",
            "00..7",
            "-0..1",
            "+1..2",
            "0...7",
            "this is not a type",
        ] {
            assert!(parse_spec_var_sort(bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn well_sorted_invariants_are_admitted() {
        let vars = env(&[("seq", "0..7"), ("full", "Bool"), ("b", "BitVec(8)")]);
        for ok in [
            "(<= seq 7)",
            "(and (<= 0 seq) (<= seq 7))",
            "(=> full (= seq 7))",
            "(<= 0 seq 7)",
            "(= (ite full seq 0) (- seq 0))",
            "(bvule b #xff)",
            "(= (bvadd b #b00000001) b)",
            "(distinct seq (+ seq 1))",
            "true",
            "full",
            "(not (xor full full))",
            "(>= (abs (- seq)) (mod seq 2))",
        ] {
            assert_eq!(check_linked_invariant(ok, &vars), Ok(()), "{ok}");
        }
    }

    #[test]
    fn each_refusal_names_its_reason() {
        let vars = env(&[("n", "0..7"), ("flag", "Bool"), ("b", "BitVec(8)")]);
        let refused = |formula: &str, needle: &str| {
            let err = check_linked_invariant(formula, &vars).expect_err(formula);
            assert!(err.contains(needle), "{formula}: {err}");
        };
        refused(")))( @@ [] <> not a formula", "not one quantifier-free");
        refused("[](n >= 0)", "not one quantifier-free");
        refused("n >= 0", "not one quantifier-free");
        refused(
            "(>= zzz_undeclared 0)",
            "undeclared variable `zzz_undeclared`",
        );
        refused("(>= n' 0)", "`n'` at byte 4, which is no SMT-LIB2 token");
        refused("(>= flag 3)", "ill-sorted");
        refused("(= n flag)", "ill-sorted");
        refused("(bvult b #x0000)", "ill-sorted");
        refused("(+ n 1)", "has sort Int");
        refused("(>= n 0.5)", "Real literal");
        refused("(>= n 007)", "`007` at byte 6, which is no SMT-LIB2 token");
        refused("(f n)", "not an operator");
        refused("(\\in n 3)", "no SMT-LIB2 token");
        refused("(\\in n Nat)", "no SMT-LIB2 token");
        refused("(in n 3)", "not an operator");
        refused("(in n Nat)", "undeclared variable `Nat`");
        refused("((bvnot b) flag)", "head must be an operator");
        refused("(not flag flag)", "exactly 1");
        refused("(ite n n n)", "condition");
        refused("(forall ((x Int)) (>= x 0))", "not one quantifier-free");
    }

    #[test]
    fn unparsed_or_duplicate_variables_are_not_resolved() {
        let vars = env(&[
            ("n", "not a type"),
            ("d", "Int"),
            ("d", "Bool"),
            ("x'", "Int"),
        ]);
        assert!(
            check_linked_invariant("(>= n 0)", &vars)
                .unwrap_err()
                .contains("undeclared variable `n`")
        );
        assert!(
            check_linked_invariant("(>= d 0)", &vars)
                .unwrap_err()
                .contains("declared more than once")
        );
        assert!(check_linked_invariant("(>= x' 0)", &vars).is_err());
        assert!(linked_var_name_problem("x'").is_some());
        assert!(linked_var_name_problem("my var").is_some());
        assert!(linked_var_name_problem("seq").is_none());
        for operator in [
            "and", "not", "ite", "div", "abs", "bvadd", "bvult", "distinct",
        ] {
            assert!(linked_var_name_problem(operator).is_some(), "{operator}");
        }
        let shadowing = env(&[("and", "Bool")]);
        assert!(check_linked_invariant("(and and and)", &shadowing).is_err());
    }

    /// [review] Rust's `split_whitespace` splits on characters SMT-LIB2 does
    /// not treat as whitespace; each used to be admitted as a separator.
    #[test]
    fn non_smt_whitespace_and_non_ascii_are_refused() {
        let vars = env(&[("flag", "Bool")]);
        assert_eq!(check_linked_invariant("(and\tflag\r\nflag)", &vars), Ok(()));
        for separator in [
            '\u{a0}', '\u{2003}', '\u{0b}', '\u{0c}', '\u{85}', '\u{3000}',
        ] {
            let formula = format!("(and{separator}flag flag)");
            let err = check_linked_invariant(&formula, &vars).expect_err(&formula);
            assert!(err.contains("neither printable ASCII"), "{err}");
        }
        let err = check_linked_invariant("(and fl\u{e4}g flag)", &vars).unwrap_err();
        assert!(err.contains("neither printable ASCII"), "{err}");
    }

    /// [review] the sort checker recurses per nesting level; an unbounded
    /// depth aborted the validating process with a stack overflow instead of
    /// refusing.
    #[test]
    fn nesting_beyond_the_depth_bound_is_refused_not_a_stack_overflow() {
        let vars = env(&[("flag", "Bool")]);
        let nested = |n: usize| format!("{}flag{}", "(not ".repeat(n), ")".repeat(n));
        assert_eq!(
            check_linked_invariant(&nested(MAX_LINKED_FORMULA_DEPTH), &vars),
            Ok(())
        );
        let err = check_linked_invariant(&nested(MAX_LINKED_FORMULA_DEPTH + 1), &vars)
            .expect_err("depth bound");
        assert!(err.contains("deeper than 256"), "{err}");
        let err = check_linked_invariant(&nested(1_000_000), &vars).expect_err("deep");
        assert!(err.contains("deeper than 256"), "{err}");
    }

    /// [review] a variable named after a theory function the surface does not
    /// admit (`concat`, `bvcomp`, …) used to be accepted; SMT-LIB2 refuses to
    /// declare such a constant, so the module was unloadable downstream.
    #[test]
    fn theory_function_symbols_are_not_variable_names() {
        for name in THEORY_RESERVED {
            let problem = linked_var_name_problem(name).expect(name);
            assert!(problem.contains("SMT-LIB2 theories"), "{problem}");
        }
        assert!(linked_var_name_problem("concatenated").is_none());
    }

    /// [review] an integer range is a mathematical domain: bounds beyond
    /// `i128` are well-formed (they used to be refused as "not canonical"),
    /// and the order check is exact at every magnitude and sign.
    #[test]
    fn range_bounds_are_unbounded_decimals_ordered_exactly() {
        let huge = "999999999999999999999999999999999999999999";
        for ok in [
            format!("0..{huge}"),
            format!("-{huge}..{huge}"),
            format!("-{huge}..-{huge}"),
            "-10..-9".to_string(),
            "-1..0".to_string(),
            "9..10".to_string(),
        ] {
            assert_eq!(parse_spec_var_sort(&ok), Ok(SpecSort::Int), "{ok}");
        }
        for empty in [
            format!("{huge}..0"),
            format!("{huge}..-{huge}"),
            "-9..-10".to_string(),
            "0..-1".to_string(),
            "10..9".to_string(),
        ] {
            let err = parse_spec_var_sort(&empty).expect_err(&empty);
            assert!(err.contains("empty integer range"), "{empty}: {err}");
        }
    }
}
