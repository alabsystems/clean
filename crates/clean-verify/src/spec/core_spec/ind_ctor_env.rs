// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Stored, name-keyed inductive and constructor metadata for the existing
//! reduction environment. These are the projection-relevant images of actual
//! `InductiveVal`/`ConstructorVal` records, not an admission certificate or the
//! complete inductive record (recursive/nested/elimination flags are omitted).
//! Both signatures retain their own ordered universe parameters and schematic
//! types. Their agreement, parent association, and namespace validity are
//! separate environment invariants, not invented projection runtime checks.
//! The ordered block names are the final stored `all_names`, not necessarily
//! the pre-restoration block on which strict admission ran.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Requires only stored signatures, OptionType, and name_eqb. In particular,
    /// neither reduction nor a typing judgment is needed to represent records.
    pub(super) fn add_ind_ctor_env(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive KIndMeta : Type\n\
             | mk : KConstSig -> Nat -> Nat -> ListType Name -> ListType Name -> KIndMeta",
            "Inductive metadata: stored signature, parameter count, index count, ordered constructor names, and final stored ordered block names. No admission or pre-restoration-context proof is asserted.",
        )?;
        self.add_inductive(
            "inductive KCtorMeta : Type\n\
             | mk : KConstSig -> Name -> Nat -> Nat -> Nat -> KCtorMeta",
            "Constructor metadata: stored signature, parent name, parameter count, field count, and constructor index. These are source record fields, not assumed typing evidence.",
        )?;

        for (name, result_type, field) in [
            ("kind_sig", "KConstSig", "sig"),
            ("kind_num_params", "Nat", "np"),
            ("kind_num_indices", "Nat", "ni"),
            ("kind_ctor_names", "ListType Name", "ctors"),
            ("kind_all_names", "ListType Name", "all_names"),
        ] {
            self.add_recursive_def(
                &format!(
                    "def {name} (meta : KIndMeta) : {result_type} := @KIndMeta.rec (fun (_ : KIndMeta) => {result_type}) (fun (sig : KConstSig) (np : Nat) (ni : Nat) (ctors : ListType Name) (all_names : ListType Name) => {field}) meta"
                ),
                "Project one stored inductive metadata field without changing its representation.",
            )?;
        }
        for (name, result_type, field) in [
            ("kctor_sig", "KConstSig", "sig"),
            ("kctor_parent", "Name", "parent"),
            ("kctor_num_params", "Nat", "np"),
            ("kctor_num_fields", "Nat", "nf"),
            ("kctor_index", "Nat", "idx"),
        ] {
            self.add_recursive_def(
                &format!(
                    "def {name} (meta : KCtorMeta) : {result_type} := @KCtorMeta.rec (fun (_ : KCtorMeta) => {result_type}) (fun (sig : KConstSig) (parent : Name) (np : Nat) (nf : Nat) (idx : Nat) => {field}) meta"
                ),
                "Project one stored constructor metadata field without changing its representation.",
            )?;
        }

        self.add_inductive(
            "inductive IndCtorEnv : Type\n\
             | empty : IndCtorEnv\n\
             | addInd : IndCtorEnv -> Name -> KIndMeta -> IndCtorEnv\n\
             | addCtor : IndCtorEnv -> Name -> KCtorMeta -> IndCtorEnv",
            "One tagged, name-keyed declaration table for inductive and constructor metadata. Newest entries shadow across kinds; valid source admission separately forbids duplicate names.",
        )?;
        // The function-valued recursor motive makes the lookup target explicit
        // at every recursive call. A same-name entry of the other kind hides an
        // older value, matching a kind check after declaration lookup.
        self.add_recursive_def(
            r"def kind_for (env : IndCtorEnv) (target : Name) : OptionType KIndMeta :=
@IndCtorEnv.rec (fun (_ : IndCtorEnv) => Name -> OptionType KIndMeta)
  (fun (_ : Name) => @OptionType.none KIndMeta)
  (fun (_tail : IndCtorEnv) (n : Name) (meta : KIndMeta) (ih : Name -> OptionType KIndMeta) => fun (q : Name) => @Bool.rec (fun (_ : Bool) => OptionType KIndMeta) (ih q) (@OptionType.some KIndMeta meta) (name_eqb n q))
  (fun (_tail : IndCtorEnv) (n : Name) (_meta : KCtorMeta) (ih : Name -> OptionType KIndMeta) => fun (q : Name) => @Bool.rec (fun (_ : Bool) => OptionType KIndMeta) (ih q) (@OptionType.none KIndMeta) (name_eqb n q)) env target",
            "Computed inductive lookup in the shared metadata table, with missing/wrong-kind results and newest-name shadowing.",
        )?;
        self.add_recursive_def(
            r"def kctor_for (env : IndCtorEnv) (target : Name) : OptionType KCtorMeta :=
@IndCtorEnv.rec (fun (_ : IndCtorEnv) => Name -> OptionType KCtorMeta)
  (fun (_ : Name) => @OptionType.none KCtorMeta)
  (fun (_tail : IndCtorEnv) (n : Name) (_meta : KIndMeta) (ih : Name -> OptionType KCtorMeta) => fun (q : Name) => @Bool.rec (fun (_ : Bool) => OptionType KCtorMeta) (ih q) (@OptionType.none KCtorMeta) (name_eqb n q))
  (fun (_tail : IndCtorEnv) (n : Name) (meta : KCtorMeta) (ih : Name -> OptionType KCtorMeta) => fun (q : Name) => @Bool.rec (fun (_ : Bool) => OptionType KCtorMeta) (ih q) (@OptionType.some KCtorMeta meta) (name_eqb n q)) env target",
            "Computed constructor lookup in the shared metadata table, retaining actual parameter/field/index/signature data.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::Specification;
    use crate::test_utils::run_with_stack;
    use clean_kernel::Name;

    fn seed() -> Specification {
        Specification::new_red_env_reflection_seed().expect("artifact-independent metadata seed")
    }

    fn check(spec: &mut Specification, name: &str, ty: &str, body: &str) {
        spec.add_recursive_def(
            &format!("def {name} : {ty} := {body}"),
            "Metadata regression",
        )
        .expect("actual kernel-checked metadata equation");
        spec.verify_definition(name).expect("equation rechecks");
        assert!(spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .expect("domain closure")
            .is_empty());
        assert!(spec
            .env()
            .foundational_axiom_deps(&Name::from_string(name))
            .expect("foundation closure")
            .is_empty());
    }

    #[test]
    fn metadata_carriers_preserve_every_stored_field() {
        run_with_stack(|| {
            let mut spec = seed();
            for (field, ty, expected) in [
                ("kind_sig", "KConstSig", "sig"),
                ("kind_num_params", "Nat", "np"),
                ("kind_num_indices", "Nat", "ni"),
                ("kind_ctor_names", "ListType Name", "ctors"),
                ("kind_all_names", "ListType Name", "all_names"),
            ] {
                check(&mut spec, &format!("metadata_test_{field}"),
                    &format!("forall (sig : KConstSig) (np : Nat) (ni : Nat) (ctors : ListType Name) (all_names : ListType Name), @Eq ({ty}) ({field} (KIndMeta.mk sig np ni ctors all_names)) {expected}"),
                    &format!("fun (sig : KConstSig) (np : Nat) (ni : Nat) (ctors : ListType Name) (all_names : ListType Name) => @Eq.refl ({ty}) {expected}"));
            }
            for (field, ty, expected) in [
                ("kctor_sig", "KConstSig", "sig"),
                ("kctor_parent", "Name", "parent"),
                ("kctor_num_params", "Nat", "np"),
                ("kctor_num_fields", "Nat", "nf"),
                ("kctor_index", "Nat", "idx"),
            ] {
                check(&mut spec, &format!("metadata_test_{field}"),
                    &format!("forall (sig : KConstSig) (parent : Name) (np : Nat) (nf : Nat) (idx : Nat), @Eq ({ty}) ({field} (KCtorMeta.mk sig parent np nf idx)) {expected}"),
                    &format!("fun (sig : KConstSig) (parent : Name) (np : Nat) (nf : Nat) (idx : Nat) => @Eq.refl ({ty}) {expected}"));
            }
        });
    }

    #[test]
    fn metadata_lookup_checks_kind_and_traverses_other_names() {
        run_with_stack(|| {
            let mut spec = seed();
            for (suffix, lookup, result_ty, env, expected) in [
                ("ind", "kind_for", "KIndMeta", "(IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous im)", "@OptionType.some KIndMeta im"),
                ("ctor", "kctor_for", "KCtorMeta", "(IndCtorEnv.addCtor IndCtorEnv.empty Name.anonymous cm)", "@OptionType.some KCtorMeta cm"),
                ("ctor_hides_ind", "kind_for", "KIndMeta", "(IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous im) Name.anonymous cm)", "@OptionType.none KIndMeta"),
                ("ind_hides_ctor", "kctor_for", "KCtorMeta", "(IndCtorEnv.addInd (IndCtorEnv.addCtor IndCtorEnv.empty Name.anonymous cm) Name.anonymous im)", "@OptionType.none KCtorMeta"),
                ("other_ctor", "kind_for", "KIndMeta", "(IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous im) (Name.str Name.anonymous Nat.zero) cm)", "@OptionType.some KIndMeta im"),
                ("other_ind", "kctor_for", "KCtorMeta", "(IndCtorEnv.addInd (IndCtorEnv.addCtor IndCtorEnv.empty Name.anonymous cm) (Name.str Name.anonymous Nat.zero) im)", "@OptionType.some KCtorMeta cm"),
                ("missing_ind", "kind_for", "KIndMeta", "IndCtorEnv.empty", "@OptionType.none KIndMeta"),
                ("missing_ctor", "kctor_for", "KCtorMeta", "IndCtorEnv.empty", "@OptionType.none KCtorMeta"),
            ] {
                check(&mut spec, &format!("metadata_lookup_{suffix}"),
                    &format!("forall (im : KIndMeta) (cm : KCtorMeta), @Eq (OptionType {result_ty}) ({lookup} {env} Name.anonymous) ({expected})"),
                    &format!("fun (im : KIndMeta) (cm : KCtorMeta) => @Eq.refl (OptionType {result_ty}) ({expected})"));
            }
        });
    }

    #[test]
    fn metadata_does_not_change_existing_delta_or_iota_lookups() {
        run_with_stack(|| {
            let mut spec = seed();
            for (suffix, ty, lhs, rhs) in [
                ("rec", "RecEnv", "red_rec (RedEnv.mk r d ic)", "r"),
                ("def", "DefEnv", "red_def (RedEnv.mk r d ic)", "d"),
                (
                    "metadata",
                    "IndCtorEnv",
                    "red_ind_ctor (RedEnv.mk r d ic)",
                    "ic",
                ),
                (
                    "delta",
                    "OptionType KExpr",
                    "delta_reduct (red_def (RedEnv.mk r d ic)) e",
                    "delta_reduct d e",
                ),
                (
                    "iota",
                    "OptionType KExpr",
                    "iota_reduct (red_rec (RedEnv.mk r d ic)) e",
                    "iota_reduct r e",
                ),
            ] {
                check(&mut spec, &format!("metadata_preserves_{suffix}"),
                    &format!("forall (r : RecEnv) (d : DefEnv) (ic : IndCtorEnv) (e : KExpr), @Eq ({ty}) ({lhs}) ({rhs})"),
                    &format!("fun (r : RecEnv) (d : DefEnv) (ic : IndCtorEnv) (e : KExpr) => @Eq.refl ({ty}) ({rhs})"));
            }
        });
    }

    #[test]
    fn metadata_rejects_wrong_kind_and_fabricated_field_count() {
        run_with_stack(|| {
            let mut spec = seed();
            for (name, ty, value) in [
                ("metadata_bad_kind", "forall (cm : KCtorMeta) (im : KIndMeta), @Eq (OptionType KIndMeta) (kind_for (IndCtorEnv.addCtor IndCtorEnv.empty Name.anonymous cm) Name.anonymous) (@OptionType.some KIndMeta im)", "fun (cm : KCtorMeta) (im : KIndMeta) => @Eq.refl (OptionType KIndMeta) (@OptionType.some KIndMeta im)"),
                ("metadata_bad_fields", "forall (sig : KConstSig), @Eq Nat (kctor_num_fields (KCtorMeta.mk sig Name.anonymous Nat.zero Nat.zero Nat.zero)) (Nat.succ Nat.zero)", "fun (sig : KConstSig) => @Eq.refl Nat (Nat.succ Nat.zero)"),
                ("metadata_bad_parent", "forall (sig : KConstSig), @Eq Name (kctor_parent (KCtorMeta.mk sig Name.anonymous Nat.zero Nat.zero Nat.zero)) (Name.str Name.anonymous Nat.zero)", "fun (sig : KConstSig) => @Eq.refl Name (Name.str Name.anonymous Nat.zero)"),
                ("metadata_bad_all_names", "forall (sig : KConstSig) (ctors : ListType Name), @Eq (ListType Name) (kind_all_names (KIndMeta.mk sig Nat.zero Nat.zero ctors (@ListType.cons Name Name.anonymous (@ListType.nil Name)))) (@ListType.nil Name)", "fun (sig : KConstSig) (ctors : ListType Name) => @Eq.refl (ListType Name) (@ListType.nil Name)"),
                ("metadata_bad_block_order", "forall (sig : KConstSig), @Eq (ListType Name) (kind_all_names (KIndMeta.mk sig Nat.zero Nat.zero (@ListType.nil Name) (@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous Nat.zero) (@ListType.nil Name))))) (@ListType.cons Name (Name.str Name.anonymous Nat.zero) (@ListType.cons Name Name.anonymous (@ListType.nil Name)))", "fun (sig : KConstSig) => @Eq.refl (ListType Name) (@ListType.cons Name (Name.str Name.anonymous Nat.zero) (@ListType.cons Name Name.anonymous (@ListType.nil Name)))"),
            ] {
                let source = format!("def {name} : {ty} := {value}");
                clean_parser::parse_decl(&source).expect("false equation is syntactically valid");
                let error = spec.add_recursive_def(&source, "Deliberately false metadata control")
                    .expect_err("false metadata equation must fail");
                assert!(format!("{error:?}").contains("Type mismatch"), "{error:?}");
                assert!(!spec.definitions().contains_key(name), "failed control must not register");
                assert!(spec.env().get_const(&Name::from_string(name)).is_none());
            }
        });
    }
}
