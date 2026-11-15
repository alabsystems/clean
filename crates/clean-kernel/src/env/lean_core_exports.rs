// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.8.0 core's `export` aliases for the builtin prelude (trust-ir gap
//! G44, ledger class (114)).
//!
//! Lean's `export C (x)` declares no constant: it adds `x ↦ C.x` to the
//! environment's alias table (`aliasExtension`, `addAlias`), which name
//! resolution consults at every namespace prefix. `forIn` is such an alias
//! (`Init/Core.lean`: `export ForIn (forIn)`), so trust-ir's
//! `(forIn xs acc body : Sem β)` and `simp only [forIn, List.forIn, …]`
//! resolved nothing under the builtin prelude ("Unknown identifier: forIn"),
//! which modelled `ForIn.forIn` but not its alias.
//!
//! [`LEAN_CORE_EXPORT_ALIASES`] is Lean 4.8.0's whole `Init` alias table,
//! measured with the pinned toolchain (a `MetaM` walk of
//! `aliasExtension.getState` keeping every target whose module is under
//! `Init`; 107 rows). The prelude registers a row only when its TARGET is a
//! constant the prelude declares, and only when the alias is not itself a
//! declared constant: several Lean aliases (`decide`, `min`, `pure`, …) are
//! modelled as root definitions, and an alias beside a same-named constant
//! would make that name ambiguous. A row whose target the prelude lacks is
//! inert until the target lands, so the table never invents a name.
//!
//! The `.olean` import lane does not need this: an imported module brings its
//! own `aliasExtension` rows (`load_register.rs`), and the import prelude is
//! left byte-identical.

use crate::env::Environment;
use crate::name::Name;

/// Lean 4.8.0's `Init` `export` aliases, `(alias, target)`, in the order the
/// pinned toolchain's sorted dump prints them.
pub(crate) const LEAN_CORE_EXPORT_ALIASES: &[(&str, &str)] = &[
    ("Lean.CharLit", "Lean.Syntax.CharLit"),
    ("Lean.Command", "Lean.Syntax.Command"),
    ("Lean.Format", "Std.Format"),
    ("Lean.Format.align", "Std.Format.align"),
    ("Lean.Format.bracket", "Std.Format.bracket"),
    ("Lean.Format.fill", "Std.Format.fill"),
    ("Lean.Format.group", "Std.Format.group"),
    ("Lean.Format.join", "Std.Format.join"),
    ("Lean.Format.joinSep", "Std.Format.joinSep"),
    ("Lean.Format.line", "Std.Format.line"),
    ("Lean.Format.nest", "Std.Format.nest"),
    ("Lean.Format.nil", "Std.Format.nil"),
    ("Lean.Format.paren", "Std.Format.paren"),
    ("Lean.Format.pretty", "Std.Format.pretty"),
    ("Lean.Format.sbracket", "Std.Format.sbracket"),
    ("Lean.Format.tag", "Std.Format.tag"),
    ("Lean.HygieneInfo", "Lean.Syntax.HygieneInfo"),
    ("Lean.Ident", "Lean.Syntax.Ident"),
    ("Lean.NameLit", "Lean.Syntax.NameLit"),
    ("Lean.NumLit", "Lean.Syntax.NumLit"),
    ("Lean.Prec", "Lean.Syntax.Prec"),
    ("Lean.Prio", "Lean.Syntax.Prio"),
    ("Lean.ScientificLit", "Lean.Syntax.ScientificLit"),
    ("Lean.StrLit", "Lean.Syntax.StrLit"),
    ("Lean.Term", "Lean.Syntax.Term"),
    ("Lean.ToFormat", "Std.ToFormat"),
    ("Lean.expandMacro?", "Lean.Macro.expandMacro?"),
    ("Lean.format", "Std.ToFormat.format"),
    (
        "Lean.getCurrMacroScope",
        "Lean.MonadQuotation.getCurrMacroScope",
    ),
    ("Lean.getMainModule", "Lean.MonadQuotation.getMainModule"),
    ("Lean.getNGen", "Lean.MonadNameGenerator.getNGen"),
    ("Lean.getRef", "Lean.MonadRef.getRef"),
    ("Lean.quote", "Lean.Quote.quote"),
    ("Lean.setNGen", "Lean.MonadNameGenerator.setNGen"),
    (
        "Lean.withFreshMacroScope",
        "Lean.MonadQuotation.withFreshMacroScope",
    ),
    ("SSubset", "HasSSubset.SSubset"),
    ("Std.format", "Std.ToFormat.format"),
    ("Subset", "HasSubset.Subset"),
    ("and_or_imp", "Classical.and_or_imp"),
    ("bind", "Bind.bind"),
    ("bind_assoc", "LawfulMonad.bind_assoc"),
    ("bind_map", "LawfulMonad.bind_map"),
    ("bind_pure_comp", "LawfulMonad.bind_pure_comp"),
    ("comp_map", "LawfulFunctor.comp_map"),
    ("compare", "Ord.compare"),
    ("cond_eq_if", "Bool.cond_eq_if"),
    ("decide", "Decidable.decide"),
    ("default", "Inhabited.default"),
    ("discard", "Functor.discard"),
    ("eq_of_beq", "LawfulBEq.eq_of_beq"),
    ("failure", "Alternative.failure"),
    ("false", "Bool.false"),
    ("forIn", "ForIn.forIn"),
    ("forIn'", "ForIn'.forIn'"),
    ("forM", "ForM.forM"),
    ("get", "MonadState.get"),
    ("getElem", "GetElem.getElem"),
    ("getElem!", "GetElem.getElem!"),
    ("getElem!_def", "LawfulGetElem.getElem!_def"),
    ("getElem?", "GetElem.getElem?"),
    ("getElem?_def", "LawfulGetElem.getElem?_def"),
    ("hash", "Hashable.hash"),
    ("id_map", "LawfulFunctor.id_map"),
    ("imp_and_neg_imp_iff", "Classical.imp_and_neg_imp_iff"),
    ("imp_iff_right_iff", "Classical.imp_iff_right_iff"),
    ("insert", "Insert.insert"),
    ("insert_emptyc_eq", "IsLawfulSingleton.insert_emptyc_eq"),
    ("isFalse", "Decidable.isFalse"),
    ("isTrue", "Decidable.isTrue"),
    ("liftWith", "MonadControlT.liftWith"),
    ("map_const", "LawfulFunctor.map_const"),
    ("map_pure", "LawfulApplicative.map_pure"),
    ("max", "Max.max"),
    ("min", "Min.min"),
    ("mkArray", "Array.mkArray"),
    ("modifyGet", "MonadState.modifyGet"),
    ("monadLift", "MonadLiftT.monadLift"),
    ("monadMap", "MonadFunctorT.monadMap"),
    ("none", "Option.none"),
    ("not_imp", "Classical.not_imp"),
    ("not_imp_self", "Decidable.not_imp_self"),
    ("ofExcept", "MonadExcept.ofExcept"),
    ("pure", "Pure.pure"),
    ("pure_bind", "LawfulMonad.pure_bind"),
    ("pure_seq", "LawfulApplicative.pure_seq"),
    ("read", "MonadReader.read"),
    ("reprPrec", "Repr.reprPrec"),
    ("reprTuple", "ReprTuple.reprTuple"),
    ("restoreM", "MonadControlT.restoreM"),
    ("seqLeft_eq", "LawfulApplicative.seqLeft_eq"),
    ("seqRight_eq", "LawfulApplicative.seqRight_eq"),
    ("seq_assoc", "LawfulApplicative.seq_assoc"),
    ("seq_pure", "LawfulApplicative.seq_pure"),
    ("set", "MonadStateOf.set"),
    ("singleton", "Singleton.singleton"),
    ("sizeOf", "SizeOf.sizeOf"),
    ("some", "Option.some"),
    ("stM", "MonadControlT.stM"),
    ("throw", "MonadExcept.throw"),
    ("toBool", "ToBool.toBool"),
    ("toStream", "ToStream.toStream"),
    ("toString", "ToString.toString"),
    ("trans", "Trans.trans"),
    ("true", "Bool.true"),
    ("tryCatch", "MonadExcept.tryCatch"),
    ("tryFinally'", "MonadFinally.tryFinally'"),
    ("withReader", "MonadWithReader.withReader"),
];

impl Environment {
    /// Register every [`LEAN_CORE_EXPORT_ALIASES`] row whose target this
    /// environment declares and whose alias it does not (see the module doc).
    /// Idempotent: [`Self::register_export_alias`] ignores a repeated row.
    pub(crate) fn register_lean_core_export_aliases(&mut self) {
        for (alias, target) in LEAN_CORE_EXPORT_ALIASES {
            let alias = Name::from_string(alias);
            let target = Name::from_string(target);
            if self.get_const(&target).is_none() || self.get_const(&alias).is_some() {
                continue;
            }
            self.register_export_alias(alias, target);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::LEAN_CORE_EXPORT_ALIASES;
    use crate::env::Environment;
    use crate::name::Name;

    /// The measured table is Lean 4.8.0's: 107 rows, no alias repeated.
    #[test]
    fn test_lean_core_export_table_is_the_measured_one() {
        assert_eq!(LEAN_CORE_EXPORT_ALIASES.len(), 107);
        let mut aliases: Vec<&str> = LEAN_CORE_EXPORT_ALIASES.iter().map(|(a, _)| *a).collect();
        aliases.sort_unstable();
        aliases.dedup();
        assert_eq!(aliases.len(), 107, "an alias appears twice in the table");
    }

    /// G44: the default prelude resolves `forIn` to `ForIn.forIn`, as Lean's
    /// `export ForIn (forIn)` does, without declaring a constant `forIn`.
    #[test]
    fn test_default_prelude_registers_for_in_export_alias() {
        let env = Environment::try_with_prelude().expect("default prelude");
        let alias = Name::from_string("forIn");
        assert!(
            env.get_const(&alias).is_none(),
            "`forIn` is an alias in Lean 4.8.0, never a constant"
        );
        assert_eq!(
            env.export_alias_targets(&alias),
            vec![&Name::from_string("ForIn.forIn")]
        );
    }

    /// A row whose target the prelude lacks registers nothing, and a row whose
    /// alias the prelude declares as a constant is left to the constant.
    #[test]
    fn test_default_prelude_skips_absent_targets_and_declared_aliases() {
        let env = Environment::try_with_prelude().expect("default prelude");
        for (alias, target) in LEAN_CORE_EXPORT_ALIASES {
            let alias = Name::from_string(alias);
            let target = Name::from_string(target);
            let registered = !env.export_alias_targets(&alias).is_empty();
            if env.get_const(&target).is_none() || env.get_const(&alias).is_some() {
                assert!(!registered, "`{alias}` must not be aliased here");
            } else {
                assert!(registered, "`{alias}` ↦ `{target}` must be aliased");
            }
        }
    }

    /// The import prelude is left byte-identical: an imported module brings
    /// its own alias rows.
    #[test]
    fn test_import_prelude_registers_no_core_export_alias() {
        let env = Environment::try_with_prelude_for_import().expect("import prelude");
        assert!(env
            .export_alias_targets(&Name::from_string("forIn"))
            .is_empty());
    }
}
