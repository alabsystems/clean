// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Builtin simproc names and source-world-sensitive execution scope.
//!
//! `elabSimpArgs` (`Lean/Elab/Tactic/Simp.lean`, `resolveSimpIdTheorem?`)
//! reads an identifier element as a local or a constant first
//! (`Term.resolveId?`); when it is neither, it tries the literal name as a
//! builtin simproc (`Simp.isBuiltinSimproc`), then as a simp-set extension,
//! and otherwise elaborates it as a term, which fails with "unknown
//! identifier". Builtin simprocs are registered by the Lean binary itself
//! (`builtin_simproc`), so `simp only [↓reduceIte]` resolves in a file that
//! imports nothing but `Init`, where no constant `reduceIte` exists.
//!
//! The table is every key of `builtinSimprocDeclsRef` in the pinned
//! `leanprover/lean4:v4.8.0` binary (193), minus the 20 whose declared name
//! carries macro scopes (`UInt8.reduceEq._@.Lean.Meta.Tactic.Simp.BuiltinSimprocs.UInt._hyg.7781`
//! and its kin): no identifier spells those, and pinned Lean answers
//! `simp only [↓UInt8.reduceEq]` with "unknown constant". Regenerate with
//!
//! ```text
//! import Lean.Meta.Tactic.Simp.BuiltinSimprocs
//! open Lean Meta Simp
//! #eval show IO Unit from do
//!   let s ← builtinSimprocDeclsRef.get
//!   for n in (s.keys.toList.map (·.1.toString)).toArray.qsort (· < ·) do IO.println n
//! ```
//!
//! # What naming one does
//!
//! `mkSimpContext` starts `simp only` from NO simprocs (`simprocs ← if
//! simpOnly then pure {} else Simp.getSimprocs`) and plain `simp` from the
//! default set; `elabSimpArgs` then adds each named simproc
//! (`simprocs.add declName post`) and removes each `-`erased one
//! (`simprocs.erase`). So under `simp only`, naming a simproc is what makes it
//! run: pinned Lean 4.8.0 closes `(if False then a else b) = b` by `simp only
//! [↓reduceIte]` and answers `simp only [↓Nat.reduceAdd]` on the same goal
//! with "simp made no progress".
//!
//! Clean honours a named simproc or refuses it by name — it never accepts one
//! and skips it ([`simproc_scope`]):
//!
//! * `reduceIte` and `reduceDite` are implemented: they are the `ite`/`dite`
//!   collapse in `expr.rs`, and a `simp only` list naming any simproc runs
//!   exactly the named ones ([`SimprocScope::Named`]).
//! * Named literal comparisons are supported by `simproc_builtins_cmp`.
//!   Other procedures are refused under `simp only` (Clean's general
//!   arithmetic table does not implement Lean's exact named scope).
//! * In the qualified Lean 4.30 world, `reduceCtorEq` runs the checked
//!   distinct-constructor rewrite. Unlike 4.8's always-on `simpCtorEq`, it
//!   must be named under `only`, and its ordered erasure is supported.
//! * Under plain `simp`, naming a simproc of Lean's default set changes
//!   nothing in Lean (it already runs), so it changes nothing here either;
//!   naming one OUTSIDE that set (`[seval]`-only: [`LEAN_4_8_SEVAL_ONLY`])
//!   would add it, and is refused. Erasures other than the qualified 4.30
//!   `reduceCtorEq` are refused because Clean cannot mirror their scope.
//!
//! A `simp only` whose list names no simproc runs none of them
//! ([`SimprocScope::Named`] with nothing named), as in Lean; until review r4t
//! it ran Clean's whole simproc table ([`SimprocScope::CleanBuiltins`]), a
//! documented divergence that accepted arithmetic Lean's `simp only` leaves
//! alone.

use std::collections::HashSet;
use std::sync::OnceLock;

use clean_kernel::{Expr, ExprKind, LeanWorld, Name};
use clean_parser::SurfaceName;

use super::types::SimprocScope;
use crate::tactic::registry::TacticEval;
use crate::tactic::{ProofState, TacticError};

/// Follow the selected file even before its first import. Direct tactic
/// clients instead use their environment's declared world, then the oracle.
pub(crate) fn source_world(
    eval: &dyn TacticEval,
    ps: &ProofState,
) -> Result<LeanWorld, TacticError> {
    if let Some(world) = eval.source_world() {
        return Ok(world);
    }
    match clean_olean::environment_world(ps.env()) {
        Some(tag) => tag
            .parse()
            .map_err(|error: clean_kernel::lean_world::UnknownLeanWorld| {
                TacticError::InvalidTarget {
                    tactic: "simp".into(),
                    detail: error.to_string(),
                }
            }),
        None => Ok(LeanWorld::ORACLE),
    }
}

/// This change qualifies the pinned 4.30 oracle. Other known worlds retain
/// their previous constructor step until separately measured; no version
/// ordering silently grants an unmeasured feature to a different world.
pub(crate) const fn has_named_ctor_eq(world: LeanWorld) -> bool {
    match world {
        LeanWorld::Lean430Rc2 => true,
        LeanWorld::Lean408
        | LeanWorld::Lean413
        | LeanWorld::Lean426
        | LeanWorld::Lean435
        | LeanWorld::Lean436Rc2 => false,
    }
}

fn is_builtin_in_world(world: LeanWorld, name: &Name) -> bool {
    is_lean_builtin_simproc(name)
        || (has_named_ctor_eq(world) && *name == Name::from_string("reduceCtorEq"))
}

/// Lean 4.30's constructor step is an ordinary default simproc, so `only`
/// starts without it and an ordered erasure removes it even from plain simp.
pub(crate) fn ctor_eq_enabled(world: LeanWorld, only: bool, named: &NamedSimprocs) -> bool {
    if !has_named_ctor_eq(world) {
        return true;
    }
    let name = Name::from_string("reduceCtorEq");
    if only {
        named.added.contains(&name)
    } else {
        !named.erased.contains(&name)
    }
}

/// What an identifier element of a simp list names, in the order Lean's
/// `resolveSimpIdTheorem?` tries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SimpIdent {
    /// A local of the current goal, or a constant of the environment that is
    /// not a simproc.
    LocalOrConstant,
    /// A simproc: the literal name of a source-world builtin simproc that names
    /// nothing else (`isBuiltinSimproc`), or a constant whose type is
    /// `Lean.Meta.Simp.Simproc` / `DSimproc` (`isSimproc?`: a builtin simproc
    /// declaration imported with `Lean`, or a library `simproc`). Carries the
    /// name the simproc is registered under.
    Simproc(Name),
    /// None of these: Lean elaborates it as a term and reports "unknown
    /// identifier".
    Unknown,
}

/// Classify the identifier `name` of a simp list element.
pub(crate) fn resolve_simp_ident(
    ps: &ProofState,
    name: &SurfaceName,
    world: LeanWorld,
) -> SimpIdent {
    let is_local = ps.current_goal().is_some_and(|goal| {
        goal.local_ctx
            .iter()
            .any(|decl| crate::tactic::pattern::names::hypothesis_named(&decl.name, name))
    });
    if is_local {
        return SimpIdent::LocalOrConstant;
    }
    let constant = crate::tactic::core::resolve_global_name(ps, name)
        .ok()
        .and_then(|global| ps.env().get_const(&global).map(|info| (global, info)));
    match constant {
        Some((global, info))
            if is_simproc_type(&info.type_) || is_builtin_in_world(world, &global) =>
        {
            SimpIdent::Simproc(global)
        }
        Some(_) => SimpIdent::LocalOrConstant,
        None if is_builtin_in_world(world, name.name()) => SimpIdent::Simproc(name.name().clone()),
        None => SimpIdent::Unknown,
    }
}

/// Whether a constant of type `ty` is a simproc declaration: Lean's
/// `simproc`/`dsimproc` commands declare it at `Lean.Meta.Simp.Simproc` /
/// `Lean.Meta.Simp.DSimproc`.
fn is_simproc_type(ty: &Expr) -> bool {
    matches!(ty.kind(), ExprKind::Const(head, _)
        if *head == Name::from_string("Lean.Meta.Simp.Simproc")
            || *head == Name::from_string("Lean.Meta.Simp.DSimproc"))
}

/// The simprocs one simp list names, after Lean's in-order `-` erasures.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct NamedSimprocs {
    /// Each simproc an element adds, in list order, minus those a LATER `-`
    /// element erased (an add after an erase stands).
    pub(crate) added: Vec<Name>,
    /// Each simproc a `-` element erased that no later element re-added.
    pub(crate) erased: Vec<Name>,
}

impl NamedSimprocs {
    /// An element naming simproc `name` (`simprocs.add`).
    pub(crate) fn add(&mut self, name: Name) {
        self.erased.retain(|n| *n != name);
        if !self.added.contains(&name) {
            self.added.push(name);
        }
    }

    /// A `-name` element (`simprocs.erase`).
    pub(crate) fn erase(&mut self, name: Name) {
        self.added.retain(|n| *n != name);
        if !self.erased.contains(&name) {
            self.erased.push(name);
        }
    }
}

/// The simproc scope of one simp call — `only` or not — whose list names
/// `named`, or the refusal of a named simproc Clean cannot honour (see the
/// module docs).
pub(crate) fn simproc_scope(
    world: LeanWorld,
    only: bool,
    named: &NamedSimprocs,
) -> Result<SimprocScope, TacticError> {
    let reduce_ite = Name::from_string("reduceIte");
    let reduce_dite = Name::from_string("reduceDite");
    let implemented = |name: &Name| {
        *name == reduce_ite
            || *name == reduce_dite
            || (has_named_ctor_eq(world) && *name == Name::from_string("reduceCtorEq"))
            || super::simproc_builtins_cmp::literal_cmp_simproc(name).is_some()
    };
    let refuse = |detail: String| TacticError::InvalidTarget {
        tactic: "simp".into(),
        detail,
    };
    for name in &named.added {
        if implemented(name) || (!only && in_lean_default_simp_set(name)) {
            continue;
        }
        let why = if only {
            "the supported simprocs are `reduceIte`, `reduceDite`, the literal comparisons, and `reduceCtorEq` in the qualified Lean 4.30 world"
        } else {
            "naming it adds it to Lean's default simp set, which does not hold it"
        };
        return Err(refuse(format!(
            "simproc `{name}` is not implemented by Clean ({why})"
        )));
    }
    if !only {
        if let Some(name) = named
            .erased
            .iter()
            .find(|name| !(has_named_ctor_eq(world) && **name == Name::from_string("reduceCtorEq")))
        {
            return Err(refuse(format!(
                "erasing simproc `{name}` from the default simp set is not supported by Clean"
            )));
        }
        return Ok(SimprocScope::CleanBuiltins);
    }
    // Lean's `mkSimpContext`: `simprocs ← if simpOnly then pure {} else …`.
    // A `simp only` naming no simproc runs none — not Clean's table, whose
    // arithmetic used to decide `h : x = 2 + 2` into `x = 4` where pinned Lean
    // 4.8.0 says "simp made no progress" (review r4t l4-l7), and with
    // `simpOnlyBuiltins` (`eq_self`), whose absence left `h : a = a ∧ P`
    // unmoved by `simp only [true_and] at h` (m9).
    Ok(SimprocScope::Named {
        reduce_ite: named.added.contains(&reduce_ite),
        reduce_dite: named.added.contains(&reduce_dite),
        literal_cmps: named
            .added
            .iter()
            .filter_map(super::simproc_builtins_cmp::literal_cmp_simproc)
            .fold(0, |acc, bit| acc | bit),
    })
}

/// Lean 4.8.0's builtin simprocs registered for `seval` only, not `simp`
/// (`builtin_dsimproc [seval] isValue ((OfNat.ofNat _ : Nat))` and
/// `Int.isPosValue`): the only spellable ones outside the default simp set.
const LEAN_4_8_SEVAL_ONLY: &[&str] = &["Int.isPosValue", "Nat.isValue"];

/// Whether `name` is a builtin simproc Lean 4.8.0's default `simp` set
/// already runs, so that naming it in a non-`only` simp list adds nothing.
fn in_lean_default_simp_set(name: &Name) -> bool {
    is_lean_builtin_simproc(name)
        && !LEAN_4_8_SEVAL_ONLY
            .iter()
            .any(|text| Name::from_string(text) == *name)
}

/// Lean 4.8.0's spellable builtin simproc names (see the module docs).
const LEAN_4_8_BUILTIN_SIMPROCS: &[&str] = &[
    "BitVec.reduceAbs",
    "BitVec.reduceAdd",
    "BitVec.reduceAllOnes",
    "BitVec.reduceAnd",
    "BitVec.reduceAppend",
    "BitVec.reduceBitVecOfFin",
    "BitVec.reduceBitVecToFin",
    "BitVec.reduceCast",
    "BitVec.reduceDiv",
    "BitVec.reduceExtracLsb'",
    "BitVec.reduceGE",
    "BitVec.reduceGT",
    "BitVec.reduceGetLsb",
    "BitVec.reduceGetMsb",
    "BitVec.reduceHShiftLeft",
    "BitVec.reduceHShiftRight",
    "BitVec.reduceLE",
    "BitVec.reduceLT",
    "BitVec.reduceMod",
    "BitVec.reduceMul",
    "BitVec.reduceNeg",
    "BitVec.reduceNot",
    "BitVec.reduceOfInt",
    "BitVec.reduceOfNat",
    "BitVec.reduceOr",
    "BitVec.reduceReplicate",
    "BitVec.reduceRotateLeft",
    "BitVec.reduceRotateRight",
    "BitVec.reduceSDiv",
    "BitVec.reduceSLE",
    "BitVec.reduceSLT",
    "BitVec.reduceSMTSDiv",
    "BitVec.reduceSMTUDiv",
    "BitVec.reduceSMod",
    "BitVec.reduceSRem",
    "BitVec.reduceSShiftRight",
    "BitVec.reduceShiftLeft",
    "BitVec.reduceShiftLeftZeroExtend",
    "BitVec.reduceSignExtend",
    "BitVec.reduceSub",
    "BitVec.reduceToInt",
    "BitVec.reduceToNat",
    "BitVec.reduceUDiv",
    "BitVec.reduceULE",
    "BitVec.reduceULT",
    "BitVec.reduceUMod",
    "BitVec.reduceUShiftRight",
    "BitVec.reduceXOr",
    "BitVec.reduceZeroExtend",
    "BitVec.reduceZeroExtend'",
    "Char.isValue",
    "Char.reduceBEq",
    "Char.reduceBNe",
    "Char.reduceDefault",
    "Char.reduceEq",
    "Char.reduceIsAlpha",
    "Char.reduceIsAlphaNum",
    "Char.reduceIsDigit",
    "Char.reduceIsLower",
    "Char.reduceIsUpper",
    "Char.reduceIsWhitespace",
    "Char.reduceNe",
    "Char.reduceOfNatAux",
    "Char.reduceToLower",
    "Char.reduceToNat",
    "Char.reduceToString",
    "Char.reduceToUpper",
    "Char.reduceVal",
    "Fin.isValue",
    "Fin.reduceAdd",
    "Fin.reduceBEq",
    "Fin.reduceBNe",
    "Fin.reduceDiv",
    "Fin.reduceEq",
    "Fin.reduceFinMk",
    "Fin.reduceGE",
    "Fin.reduceGT",
    "Fin.reduceLE",
    "Fin.reduceLT",
    "Fin.reduceMod",
    "Fin.reduceMul",
    "Fin.reduceNe",
    "Fin.reduceSub",
    "Int.isPosValue",
    "Int.reduceAbs",
    "Int.reduceAdd",
    "Int.reduceBEq",
    "Int.reduceBNe",
    "Int.reduceDiv",
    "Int.reduceEq",
    "Int.reduceGE",
    "Int.reduceGT",
    "Int.reduceLE",
    "Int.reduceLT",
    "Int.reduceMod",
    "Int.reduceMul",
    "Int.reduceNe",
    "Int.reduceNeg",
    "Int.reduceNegSucc",
    "Int.reduceOfNat",
    "Int.reducePow",
    "Int.reduceSub",
    "Int.reduceToNat",
    "Nat.isValue",
    "Nat.reduceAdd",
    "Nat.reduceBEq",
    "Nat.reduceBNe",
    "Nat.reduceBeqDiff",
    "Nat.reduceBneDiff",
    "Nat.reduceDiv",
    "Nat.reduceEqDiff",
    "Nat.reduceGT",
    "Nat.reduceGcd",
    "Nat.reduceLT",
    "Nat.reduceLeDiff",
    "Nat.reduceMod",
    "Nat.reduceMul",
    "Nat.reducePow",
    "Nat.reduceSub",
    "Nat.reduceSubDiff",
    "Nat.reduceSucc",
    "String.reduceAppend",
    "String.reduceMk",
    "UInt16.reduceAdd",
    "UInt16.reduceDiv",
    "UInt16.reduceGE",
    "UInt16.reduceGT",
    "UInt16.reduceLE",
    "UInt16.reduceLT",
    "UInt16.reduceMod",
    "UInt16.reduceMul",
    "UInt16.reduceOfNat",
    "UInt16.reduceOfNatCore",
    "UInt16.reduceSub",
    "UInt16.reduceToNat",
    "UInt32.reduceAdd",
    "UInt32.reduceDiv",
    "UInt32.reduceGE",
    "UInt32.reduceGT",
    "UInt32.reduceLE",
    "UInt32.reduceLT",
    "UInt32.reduceMod",
    "UInt32.reduceMul",
    "UInt32.reduceOfNat",
    "UInt32.reduceOfNatCore",
    "UInt32.reduceSub",
    "UInt32.reduceToNat",
    "UInt64.reduceAdd",
    "UInt64.reduceDiv",
    "UInt64.reduceGE",
    "UInt64.reduceGT",
    "UInt64.reduceLE",
    "UInt64.reduceLT",
    "UInt64.reduceMod",
    "UInt64.reduceMul",
    "UInt64.reduceOfNat",
    "UInt64.reduceOfNatCore",
    "UInt64.reduceSub",
    "UInt64.reduceToNat",
    "UInt8.reduceAdd",
    "UInt8.reduceDiv",
    "UInt8.reduceGE",
    "UInt8.reduceGT",
    "UInt8.reduceLE",
    "UInt8.reduceLT",
    "UInt8.reduceMod",
    "UInt8.reduceMul",
    "UInt8.reduceOfNat",
    "UInt8.reduceOfNatCore",
    "UInt8.reduceSub",
    "UInt8.reduceToNat",
    "reduceDite",
    "reduceIte",
];

/// Whether `name`, exactly as written, is a Lean 4.8.0 builtin simproc.
pub(crate) fn is_lean_builtin_simproc(name: &Name) -> bool {
    static TABLE: OnceLock<HashSet<Name>> = OnceLock::new();
    TABLE
        .get_or_init(|| {
            LEAN_4_8_BUILTIN_SIMPROCS
                .iter()
                .copied()
                .map(Name::from_string)
                .collect()
        })
        .contains(name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lean_builtin_simproc_table_holds_the_core_and_nat_simprocs() {
        for text in [
            "reduceIte",
            "reduceDite",
            "Nat.reduceAdd",
            "BitVec.reduceExtracLsb'",
        ] {
            assert!(
                is_lean_builtin_simproc(&Name::from_string(text)),
                "{text} is a Lean 4.8.0 builtin simproc"
            );
        }
        assert_eq!(LEAN_4_8_BUILTIN_SIMPROCS.len(), 173);
    }

    #[test]
    fn test_lean_builtin_simproc_table_refuses_lookalikes() {
        // `reduceDIte` is not Lean's spelling (`reduceDite`); a theorem name
        // is not a simproc; a namespace-stripped `reduceAdd` resolves only
        // through `Nat.`; the hygienic `UInt8.reduceEq` is unspellable.
        for text in [
            "reduceDIte",
            "ite_true",
            "reduceAdd",
            "UInt8.reduceEq",
            "no_such_rule",
        ] {
            assert!(
                !is_lean_builtin_simproc(&Name::from_string(text)),
                "{text} is not a Lean 4.8.0 builtin simproc"
            );
        }
    }

    fn named(added: &[&str], erased: &[&str]) -> NamedSimprocs {
        let mut named = NamedSimprocs::default();
        for text in erased {
            named.erase(Name::from_string(text));
        }
        for text in added {
            named.add(Name::from_string(text));
        }
        named
    }

    fn refusal(only: bool, list: &NamedSimprocs) -> String {
        match simproc_scope(LeanWorld::Lean408, only, list) {
            Err(err) => err.to_string(),
            Ok(scope) => panic!("{list:?} (only = {only}) must be refused, got {scope:?}"),
        }
    }

    #[test]
    fn test_simproc_scope_simp_only_runs_exactly_the_named_collapses() {
        assert_eq!(
            simproc_scope(LeanWorld::Lean408, true, &named(&["reduceIte"], &[])).ok(),
            Some(SimprocScope::Named {
                reduce_ite: true,
                reduce_dite: false,
                literal_cmps: 0
            })
        );
        assert_eq!(
            simproc_scope(LeanWorld::Lean408, true, &named(&["reduceDite"], &[])).ok(),
            Some(SimprocScope::Named {
                reduce_ite: false,
                reduce_dite: true,
                literal_cmps: 0
            })
        );
        // `-reduceIte` after `↓reduceIte` erases it (Lean walks the list in
        // order): a simproc was named, so the scope is still `Named`, and it
        // runs nothing — never Clean's whole table.
        let mut erased_after = NamedSimprocs::default();
        erased_after.add(Name::from_string("reduceIte"));
        erased_after.erase(Name::from_string("reduceIte"));
        assert_eq!(
            simproc_scope(LeanWorld::Lean408, true, &erased_after).ok(),
            Some(SimprocScope::Named {
                reduce_ite: false,
                reduce_dite: false,
                literal_cmps: 0
            })
        );
        // No simproc named: none runs, as in Lean (`simpOnly → {}`); never
        // Clean's table (the divergence closed by review r4t).
        assert_eq!(
            simproc_scope(LeanWorld::Lean408, true, &NamedSimprocs::default()).ok(),
            Some(SimprocScope::Named {
                reduce_ite: false,
                reduce_dite: false,
                literal_cmps: 0
            })
        );
    }

    #[test]
    fn test_simproc_scope_refuses_an_unimplemented_simproc_by_name() {
        let err = refusal(true, &named(&["reduceIte", "Nat.reduceAdd"], &[]));
        assert!(
            err.contains("`Nat.reduceAdd`") && err.contains("not implemented"),
            "the refusal must name the simproc: {err}"
        );
        // A library simproc (not a Lean builtin) is refused in either mode.
        let err = refusal(false, &named(&["Finset.reduceSum"], &[]));
        assert!(err.contains("`Finset.reduceSum`"), "{err}");
    }

    #[test]
    fn test_simproc_scope_plain_simp_takes_default_set_simprocs_as_no_ops() {
        assert_eq!(
            simproc_scope(
                LeanWorld::Lean408,
                false,
                &named(&["Nat.reduceAdd", "reduceIte"], &[])
            )
            .ok(),
            Some(SimprocScope::CleanBuiltins)
        );
        // `[seval]`-only: naming it ADDS it in Lean, so it is refused.
        let err = refusal(false, &named(&["Nat.isValue"], &[]));
        assert!(err.contains("`Nat.isValue`"), "{err}");
        // Erasing from the default set cannot be mirrored.
        let err = refusal(false, &named(&[], &["reduceIte"]));
        assert!(
            err.contains("erasing simproc `reduceIte`"),
            "the refusal must name the erased simproc: {err}"
        );
    }
}
