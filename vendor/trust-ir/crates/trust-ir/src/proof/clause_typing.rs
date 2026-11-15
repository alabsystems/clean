// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typing a contract clause's free names against the IR they denote.
//!
//! A [`ProofFormula`](crate::proof::ProofFormula) carries `bindings` (v41): for
//! each free name of the clause, a [`ClauseSort`] (the arithmetic domain the
//! clause reads the name in) and a [`ClausePlace`] (which IR value it denotes).
//! Those bindings are what make a carried clause CHECKABLE rather than
//! decorative — but only if something actually compares them with the IR. The
//! helpers here are that comparison's shared vocabulary:
//!
//! * [`resolve_clause_place`] — the IR [`Ty`] a place denotes on its owning
//!   function, or a named refusal;
//! * [`clause_sort_admits`] — whether a sort is a faithful reading of an IR type;
//! * [`smt_free_symbols`] / [`is_smt_simple_symbol`] — the free names of a
//!   quantifier-free SMT-LIB2 clause, read by trust-ir's one SMT-LIB2 reader
//!   ([`crate::proof::read_smtlib_term`]) under the one free-name grammar every
//!   consumer uses.
//!
//! Every helper FAILS CLOSED: a place, sort or clause shape it cannot decide is
//! a refusal, never a default. They live in the zero-dependency core so the
//! contract grounder (`clean_expr_lowering::contract`) and the validator cannot
//! disagree about what a binding denotes.

use std::collections::BTreeSet;

use crate::Module;
use crate::proof::{ClausePlace, ClauseSort, SmtSexp, read_smtlib_term};
use crate::ty::Ty;
use crate::value::FuncId;

mod observed;
pub use observed::{
    ObservedClauseTypingError, clause_sort_admits_observed, resolve_clause_place_borrowed_observed,
};

/// Why a [`ClausePlace`] does not resolve to an IR type on its owning function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClauseTypingError {
    /// The owning function id matches `matches` functions, not exactly one.
    FunctionUnresolved { function: FuncId, matches: usize },
    /// The owning function's `FuncTy` does not resolve in the module.
    SignatureUnresolved { function: FuncId },
    /// `Param { index }` / `MutParamExit { index }` / `ParamPointeeEntry {
    /// index }` is past the parameter list.
    ParamOutOfRange { index: u32, arity: usize },
    /// `ResultSlot { index }` is past the return list.
    ResultOutOfRange { index: u32, arity: usize },
    /// `MutParamExit { index }` names a parameter that is not `&mut T` /
    /// `*mut T`, so it has no exit value distinct from its entry value.
    MutParamExitNotMutable { index: u32, ty: Ty },
    /// `ParamPointeeEntry { index }` (v62) names a parameter that is not a
    /// reference (`&T` / `&mut T`), so it has no pointee a clause can read at
    /// entry: a by-value parameter has none, and a raw pointer, an untyped
    /// `Ptr`, a fat pointer or an `Rc` does not carry the premise that its
    /// pointee exists.
    ParamPointeeNotReference { index: u32, ty: Ty },
    /// `World` / `Unwind` denote ambient state, not an IR value with a type.
    PlaceHasNoIrType(ClausePlace),
    /// `Value(v)` needs the owning function's SSA value-type map, which this
    /// helper does not compute; it is refused rather than guessed.
    ValuePlaceUnsupported(ClausePlace),
}

impl core::fmt::Display for ClauseTypingError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ClauseTypingError::FunctionUnresolved { function, matches } => write!(
                f,
                "owning function f{} does not resolve uniquely ({matches} functions carry that id)",
                function.index()
            ),
            ClauseTypingError::SignatureUnresolved { function } => write!(
                f,
                "the signature of owning function f{} does not resolve",
                function.index()
            ),
            ClauseTypingError::ParamOutOfRange { index, arity } => write!(
                f,
                "parameter place {index} is out of range (the function has {arity} parameters)"
            ),
            ClauseTypingError::ResultOutOfRange { index, arity } => write!(
                f,
                "result slot {index} is out of range (the function has {arity} results)"
            ),
            ClauseTypingError::MutParamExitNotMutable { index, ty } => write!(
                f,
                "MutParamExit {{ index: {index} }} names a parameter of type {ty}, not a &mut / *mut"
            ),
            ClauseTypingError::ParamPointeeNotReference { index, ty } => write!(
                f,
                "ParamPointeeEntry {{ index: {index} }} names a parameter of type {ty}, not a \
                 & / &mut reference"
            ),
            ClauseTypingError::PlaceHasNoIrType(place) => {
                write!(
                    f,
                    "place {place:?} denotes ambient state, not a typed IR value"
                )
            }
            ClauseTypingError::ValuePlaceUnsupported(place) => write!(
                f,
                "place {place:?} is an SSA value place; resolving it needs the function's \
                 value-type map, which this check does not have"
            ),
        }
    }
}

impl std::error::Error for ClauseTypingError {}

/// The IR type the clause place `place` denotes on function `function`.
///
/// * `Param { i }` → `FuncTy::params[i]`;
/// * `ResultSlot { i }` → `FuncTy::returns[i]`;
/// * `MutParamExit { i }` → `T` where `FuncTy::params[i]` is `&mut T` or
///   `*mut T` (the value behind the pointer at exit);
/// * `ParamPointeeEntry { i }` (v62) → `T` where `FuncTy::params[i]` is `&T`
///   or `&mut T` (the value behind the reference at entry); a raw pointer is
///   refused, as is every non-reference;
/// * `World`, `Unwind` and `Value(_)` are refused.
///
/// `function` must name EXACTLY one function of `module` and its signature
/// must resolve; anything else is a refusal.
pub fn resolve_clause_place(
    module: &Module,
    function: FuncId,
    place: &ClausePlace,
) -> Result<Ty, ClauseTypingError> {
    let candidates: Vec<&crate::Function> = module
        .functions
        .iter()
        .filter(|func| func.id == function)
        .collect();
    let [func] = candidates[..] else {
        return Err(ClauseTypingError::FunctionUnresolved {
            function,
            matches: candidates.len(),
        });
    };
    let signature = module
        .func_type(func.ty)
        .ok_or(ClauseTypingError::SignatureUnresolved { function })?;
    let param = |index: u32| {
        signature
            .params
            .get(index as usize)
            .ok_or(ClauseTypingError::ParamOutOfRange {
                index,
                arity: signature.params.len(),
            })
    };
    match place {
        ClausePlace::Param { index } => param(*index).cloned(),
        ClausePlace::ResultSlot { index } => signature.returns.get(*index as usize).cloned().ok_or(
            ClauseTypingError::ResultOutOfRange {
                index: *index,
                arity: signature.returns.len(),
            },
        ),
        ClausePlace::MutParamExit { index } => match param(*index)? {
            Ty::RefMut(pointee) | Ty::PtrMut(pointee) => Ok((**pointee).clone()),
            other => Err(ClauseTypingError::MutParamExitNotMutable {
                index: *index,
                ty: other.clone(),
            }),
        },
        // v62: the entry-state pointee of a REFERENCE parameter. A raw
        // pointer is refused with every other non-reference: nothing in its
        // type says a pointee exists at entry, and a clause read of one would
        // be a claim about memory the format cannot vouch for.
        ClausePlace::ParamPointeeEntry { index } => match param(*index)? {
            Ty::Ref(pointee) | Ty::RefMut(pointee) => Ok((**pointee).clone()),
            other => Err(ClauseTypingError::ParamPointeeNotReference {
                index: *index,
                ty: other.clone(),
            }),
        },
        // v59: the world epochs are ambient state exactly as `World` is.
        ClausePlace::World
        | ClausePlace::WorldPre
        | ClausePlace::WorldPost
        | ClausePlace::Unwind => Err(ClauseTypingError::PlaceHasNoIrType(*place)),
        ClausePlace::Value(_) => Err(ClauseTypingError::ValuePlaceUnsupported(*place)),
        // v46: a spec-variable place has no IR type on ANY function — the
        // index space is a `SpecModule`'s `vars`, not a signature. Refused by
        // name here so the contract grounder can never silently resolve one to
        // whatever parameter shares the number.
        ClausePlace::SpecVar { .. } | ClausePlace::SpecVarNext { .. } => {
            Err(ClauseTypingError::PlaceHasNoIrType(*place))
        }
    }
}

/// Whether reading an IR value of type `ty` in SMT sort `sort` is faithful.
///
/// Conservative by construction — every pair not listed is `false`:
///
/// * `Bool` ⇐ `Ty::Bool`;
/// * `Int` ⇐ any fixed-width integer (`I*`, `U*`, `Isize`, `Usize`) and `Char`
///   (the mathematical value of the place, signedness included);
/// * `BitVec(w)` ⇐ an integer of exactly `w` bits (`Isize`/`Usize` only when
///   `pointer_bits` is known) and `Char` at `w == 32`;
/// * `Float { eb, sb }` ⇐ the IEEE format of exactly that shape (`F16` = 5/11,
///   `F32` = 8/24, `F64` = 11/53);
/// * `RoundingMode`, `Array` and `Datatype` admit no IR type here, and no sort
///   admits a `Ty::Handle` (an opaque runtime word has no machine sort).
pub fn clause_sort_admits(sort: &ClauseSort, ty: &Ty, pointer_bits: Option<u32>) -> bool {
    match sort {
        ClauseSort::Bool => matches!(ty, Ty::Bool),
        ClauseSort::Int => ty.is_integer() || matches!(ty, Ty::Char),
        ClauseSort::BitVec(width) => match ty {
            Ty::Char => *width == 32,
            Ty::Isize | Ty::Usize => pointer_bits == Some(*width),
            _ if ty.is_integer() => ty.bit_width() == Some(*width),
            _ => false,
        },
        ClauseSort::Float { eb, sb } => matches!(
            (ty, eb, sb),
            (Ty::F16, 5, 11) | (Ty::F32, 8, 24) | (Ty::F64, 11, 53)
        ),
        ClauseSort::RoundingMode | ClauseSort::Array(..) | ClauseSort::Datatype { .. } => false,
    }
}

/// SMT-LIB2 (2.6, §3.1) reserved words — which are no symbols at all, so no
/// free name either (`(>= par 0)` is not SMT-LIB2, though z3 reads it) —
/// the plain command names 2.6 also reserves, and `true`/`false`, which are
/// `Core` constants rather than names.
const SMT_RESERVED: &[&str] = &[
    "true",
    "false",
    "let",
    "forall",
    "exists",
    "as",
    "!",
    "_",
    "match",
    "par",
    "BINARY",
    "DECIMAL",
    "HEXADECIMAL",
    "NUMERAL",
    "STRING",
    "assert",
    "echo",
    "exit",
    "pop",
    "push",
    "reset",
];

/// True iff `atom` is a free name under the grammar every trust-ir consumer
/// uses: `[A-Za-z_][A-Za-z0-9_.]*`, and not a reserved word (`true`,
/// `false`, SMT-LIB2's reserved words `let`, `forall`, `exists`, `as`, `!`,
/// `_`, `match`, `par`, `NUMERAL`, … and its plain command names).
///
/// Narrower than SMT-LIB2's own simple-symbol class on purpose: `-5`, `+1`,
/// `#x00`, a numeral, or a quoted `|..|` symbol are never a free name here.
/// It is never WIDER: a `'` is in no SMT-LIB2 token, so `x'` is no name (this
/// grammar admitted it, and a `(>= x' 0)` clause was kernel-replayed although
/// z3 reads `x'` as "unexpected character" and drops the assertion). The
/// successor value of a `&mut` parameter is a [`ClausePlace::MutParamExit`]
/// binding under a plain name, e.g. `p_exit`.
pub fn is_smt_simple_symbol(atom: &str) -> bool {
    let mut chars = atom.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.'))
        && !SMT_RESERVED.contains(&atom)
}

/// True iff `atom` is an SMT literal this reader recognizes: a decimal numeral,
/// a decimal, a `#x` hexadecimal or a `#b` binary.
fn is_smt_literal(atom: &str) -> bool {
    let digits = |s: &str, ok: fn(char) -> bool| !s.is_empty() && s.chars().all(ok);
    if let Some(hex) = atom.strip_prefix("#x") {
        return digits(hex, |c| c.is_ascii_hexdigit());
    }
    if let Some(bin) = atom.strip_prefix("#b") {
        return digits(bin, |c| c == '0' || c == '1');
    }
    match atom.split_once('.') {
        Some((whole, frac)) => {
            digits(whole, |c| c.is_ascii_digit()) && digits(frac, |c| c.is_ascii_digit())
        }
        None => digits(atom, |c| c.is_ascii_digit()),
    }
}

/// The free names of a QUANTIFIER-FREE SMT-LIB2 clause, or `None` when the
/// text is outside what this reader decides.
///
/// The text is read by trust-ir's one SMT-LIB2 reader
/// ([`read_smtlib_term`]): a text it refuses — a character outside SMT-LIB2
/// source, a string, quoted symbol or comment, an atom that is no token, not
/// exactly one balanced term — has no free names. A free name is then an
/// atom in argument (non-head) position that is a free name under
/// [`is_smt_simple_symbol`]. Head atoms are operators, and literals
/// (numerals, decimals, `#x..`, `#b..`) and `true`/`false` are not names.
/// Returns `None` — never a partial set — on a binder (`let`, `forall`,
/// `exists`), an annotation or indexed identifier (`!`, `_`, `as`), the empty
/// list `()`, or any argument atom that is neither a name nor a literal
/// (`-5`, `+1`, a keyword).
pub fn smt_free_symbols(text: &str) -> Option<BTreeSet<String>> {
    fn collect(term: &SmtSexp<'_>, is_head: bool, symbols: &mut BTreeSet<String>) -> Option<()> {
        match term {
            SmtSexp::Atom(atom) => {
                let atom = *atom;
                if SMT_RESERVED.contains(&atom) && !matches!(atom, "true" | "false") {
                    return None;
                }
                if is_head {
                    return Some(());
                }
                if is_smt_simple_symbol(atom) {
                    symbols.insert(atom.to_string());
                } else if !(is_smt_literal(atom) || matches!(atom, "true" | "false")) {
                    return None;
                }
                Some(())
            }
            SmtSexp::List(items) => {
                // `()` is not a term.
                let (head, args) = items.split_first()?;
                collect(head, true, symbols)?;
                args.iter().try_for_each(|arg| collect(arg, false, symbols))
            }
        }
    }
    let term = read_smtlib_term(text).ok()?;
    let mut symbols = BTreeSet::new();
    collect(&term, false, &mut symbols)?;
    Some(symbols)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::FuncTy;
    use crate::value::{BlockId, FuncTyId, ValueId};
    use crate::{Function, Module};

    fn module_with(params: Vec<Ty>, returns: Vec<Ty>) -> Module {
        let mut module = Module::new("clause_typing");
        module.func_types.push(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        });
        module.functions.push(Function::new(
            FuncId::new(0),
            "f",
            FuncTyId::new(0),
            BlockId::new(0),
        ));
        module
    }

    #[test]
    fn places_resolve_to_their_signature_types() {
        let m = module_with(
            vec![Ty::U32, Ty::RefMut(Box::new(Ty::U16)), Ty::U8],
            vec![Ty::U64],
        );
        let f = FuncId::new(0);
        assert_eq!(
            resolve_clause_place(&m, f, &ClausePlace::Param { index: 0 }),
            Ok(Ty::U32)
        );
        assert_eq!(
            resolve_clause_place(&m, f, &ClausePlace::ResultSlot { index: 0 }),
            Ok(Ty::U64)
        );
        assert_eq!(
            resolve_clause_place(&m, f, &ClausePlace::MutParamExit { index: 1 }),
            Ok(Ty::U16)
        );
        assert_eq!(
            resolve_clause_place(&m, f, &ClausePlace::MutParamExit { index: 2 }),
            Err(ClauseTypingError::MutParamExitNotMutable {
                index: 2,
                ty: Ty::U8
            })
        );
        assert_eq!(
            resolve_clause_place(&m, f, &ClausePlace::Param { index: 3 }),
            Err(ClauseTypingError::ParamOutOfRange { index: 3, arity: 3 })
        );
        assert_eq!(
            resolve_clause_place(&m, f, &ClausePlace::ResultSlot { index: 1 }),
            Err(ClauseTypingError::ResultOutOfRange { index: 1, arity: 1 })
        );
        for place in [
            ClausePlace::World,
            ClausePlace::WorldPre,
            ClausePlace::WorldPost,
            ClausePlace::Unwind,
            ClausePlace::Value(ValueId::new(0)),
        ] {
            assert!(resolve_clause_place(&m, f, &place).is_err(), "{place:?}");
        }
        assert_eq!(
            resolve_clause_place(&m, FuncId::new(9), &ClausePlace::Param { index: 0 }),
            Err(ClauseTypingError::FunctionUnresolved {
                function: FuncId::new(9),
                matches: 0
            })
        );
        let mut twice = m.clone();
        twice.functions.push(twice.functions[0].clone());
        assert_eq!(
            resolve_clause_place(&twice, f, &ClausePlace::Param { index: 0 }),
            Err(ClauseTypingError::FunctionUnresolved {
                function: f,
                matches: 2
            })
        );
        let mut unsigned = m.clone();
        unsigned.func_types.clear();
        assert_eq!(
            resolve_clause_place(&unsigned, f, &ClausePlace::Param { index: 0 }),
            Err(ClauseTypingError::SignatureUnresolved { function: f })
        );
    }

    /// v62 (roadmap DG-63): `ParamPointeeEntry { i }` types against the
    /// pointee `T` of a `&T` / `&mut T` parameter, and refuses by name every
    /// parameter that is not a reference: a by-value one, a raw pointer (even
    /// `*mut T`, which `MutParamExit` admits), an untyped `Ptr`, a fat
    /// pointer and an `Rc`.
    #[test]
    fn param_pointee_entry_reads_only_a_reference() {
        use crate::ty::FatPtrKind;
        let params = vec![
            Ty::Ref(Box::new(Ty::U32)),
            Ty::RefMut(Box::new(Ty::I16)),
            Ty::U8,
            Ty::PtrMut(Box::new(Ty::U64)),
            Ty::PtrConst(Box::new(Ty::U64)),
            Ty::Ptr,
            Ty::FatPtr(FatPtrKind::Str),
            Ty::Rc(Box::new(Ty::U64)),
            Ty::Ref(Box::new(Ty::Ref(Box::new(Ty::U8)))),
        ];
        let m = module_with(params.clone(), vec![]);
        let f = FuncId::new(0);
        let pointee =
            |index| resolve_clause_place(&m, f, &ClausePlace::ParamPointeeEntry { index });
        assert_eq!(pointee(0), Ok(Ty::U32));
        assert_eq!(pointee(1), Ok(Ty::I16));
        // A reference to a reference reads the inner reference, which no
        // clause sort admits: the sort check refuses it, not this resolver.
        assert_eq!(pointee(8), Ok(Ty::Ref(Box::new(Ty::U8))));
        assert!(!clause_sort_admits(
            &ClauseSort::BitVec(64),
            &Ty::Ref(Box::new(Ty::U8)),
            Some(64)
        ));
        for index in 2..=7 {
            assert_eq!(
                pointee(index),
                Err(ClauseTypingError::ParamPointeeNotReference {
                    index,
                    ty: params[index as usize].clone(),
                }),
                "parameter {index}"
            );
        }
        assert_eq!(
            pointee(9),
            Err(ClauseTypingError::ParamOutOfRange { index: 9, arity: 9 })
        );
        // The entry pointee is not the parameter: the same index as `Param`
        // is the reference itself.
        assert_eq!(
            resolve_clause_place(&m, f, &ClausePlace::Param { index: 0 }),
            Ok(Ty::Ref(Box::new(Ty::U32)))
        );
    }

    #[test]
    fn sorts_admit_only_faithful_types() {
        assert!(clause_sort_admits(&ClauseSort::Int, &Ty::I64, None));
        assert!(clause_sort_admits(&ClauseSort::Int, &Ty::U8, None));
        assert!(clause_sort_admits(&ClauseSort::BitVec(64), &Ty::U64, None));
        assert!(!clause_sort_admits(&ClauseSort::BitVec(8), &Ty::U64, None));
        assert!(!clause_sort_admits(
            &ClauseSort::BitVec(64),
            &Ty::Usize,
            None
        ));
        assert!(clause_sort_admits(
            &ClauseSort::BitVec(64),
            &Ty::Usize,
            Some(64)
        ));
        assert!(clause_sort_admits(&ClauseSort::Bool, &Ty::Bool, None));
        assert!(!clause_sort_admits(&ClauseSort::Bool, &Ty::U8, None));
        assert!(!clause_sort_admits(&ClauseSort::Int, &Ty::Bool, None));
        assert!(!clause_sort_admits(&ClauseSort::Int, &Ty::F64, None));
        assert!(clause_sort_admits(
            &ClauseSort::Float { eb: 11, sb: 53 },
            &Ty::F64,
            None
        ));
        assert!(!clause_sort_admits(
            &ClauseSort::Float { eb: 8, sb: 24 },
            &Ty::F64,
            None
        ));
        assert!(!clause_sort_admits(
            &ClauseSort::RoundingMode,
            &Ty::U8,
            None
        ));
    }

    #[test]
    fn simple_symbol_grammar_is_narrow() {
        for ok in ["x", "result", "_tmp", "a.b", "v0"] {
            assert!(is_smt_simple_symbol(ok), "{ok}");
        }
        for bad in [
            "", "-5", "+1", "#x00", "5", "true", "false", "let", "forall", "exists", "as", "!",
            "_", "|x|", "x-y", "0x", "x'", "x''", "match", "par", "NUMERAL", "STRING", "push",
        ] {
            assert!(!is_smt_simple_symbol(bad), "{bad}");
        }
    }

    #[test]
    fn free_symbols_of_quantifier_free_clauses() {
        let set = |names: &[&str]| names.iter().map(|s| s.to_string()).collect::<BTreeSet<_>>();
        assert_eq!(smt_free_symbols("(>= result 0)"), Some(set(&["result"])));
        assert_eq!(
            smt_free_symbols("(and (<= 0 x) (< x_exit #x10) true)"),
            Some(set(&["x", "x_exit"]))
        );
        assert_eq!(smt_free_symbols("(= 1 1)"), Some(set(&[])));
        assert_eq!(smt_free_symbols("x"), Some(set(&["x"])));
        for refused in [
            "(>= -5 0)",
            "(forall ((x Int)) (>= x 0))",
            "(let ((y 1)) y)",
            "((_ extract 7 0) x)",
            "(! x :named a)",
            "(>= x 0",
            "(>= x 0))",
            "(>= x 0) (>= y 0)",
            "(= |x| 0)",
            "()",
            "",
            "(>= x' 0)",
            "(>=\u{3000}x\u{3000}0)",
            "(>=\u{0b}x 0)",
            "(>= x 0) ; comment",
            "(= s \"a\")",
            "(>= x 007)",
            "(>= par 0)",
            "(<= 0 NUMERAL)",
            "(match x 0)",
        ] {
            assert_eq!(smt_free_symbols(refused), None, "{refused}");
        }
    }
}
