// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared schematic declaration records for constant typing and delta reduction.
//!
//! A definition stores its signature once, so type and value instantiation use
//! the same ordered universe parameters. These are data and raw operations, not
//! typing, admission, well-formedness, or production-source refinement theorems.
//! In particular, arity is an explicit proposition: the total instantiation
//! functions do not enforce it or prevent the existing missing-argument default.
//! The separate kdecl_type_at lookup checks arity before exposing an instantiated
//! type; its introduction/inversion proofs register in the later lookup stage.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Same foundational proof formerly registered by the late schema stage.
    /// It depends only on rec_env's nat_eqb and foundation's nat_sub_self.
    ///
    /// REGISTRATION PATH MATTERS HERE. This is the FIRST registration of
    /// `nat_eqb_refl` in the full spec, and `kexpr_beq.rs` re-registers the
    /// same lemma through `add_definition_if_absent`, which keeps whatever
    /// status the first registration recorded. 31fa57c00 moved this
    /// registration onto `add_recursive_def`, which stamps EVERY definition
    /// DerivedPending by construction (declaration_registration.rs, "not
    /// verified through the kernel promote pipeline") and nothing later
    /// promotes it -- so the kexpr_beq keystone
    /// (`test_kexpr_beq_decls_kernel_check_and_proved`) read a kernel-checked,
    /// zero-closure lemma as DerivedPending. It goes through `add_definition`,
    /// which kernel-checks the value at `add_decl` and records the
    /// DerivedProved status that registration actually earned. Same type, same
    /// proof term as the kexpr_beq spelling (byte-identical value; the
    /// `add_definition_if_absent` soundness condition holds).
    pub(super) fn add_declaration_lookup_reflexivity(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "nat_eqb_refl".to_string(),
            type_src: "forall (n : Nat), @Eq Bool (nat_eqb n n) Bool.true".to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Nat) => ",
                    "@Eq.cong Nat Bool ",
                    "(fun (s : Nat) => nat_is_zero (Nat.add s s)) ",
                    "(Nat.sub n n) Nat.zero ",
                    "(nat_sub_self n)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "nat_eqb n n = true (Eq.cong transport of nat_sub_self through \
                          nat_is_zero (Nat.add s s)). Unchanged proof moved before \
                          computed-lookup consumers. DerivedProved; zero axiom_deps. \
                          Foundational closure."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "nat_sub_self".to_string(),
                "nat_is_zero".to_string(),
                "nat_eqb".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })
    }

    /// Pure stored data, available before RecMeta and raw instantiation.
    /// Requires only the foundation and expression/list syntax.
    pub(super) fn add_declaration_signature_carrier(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive KConstSig : Type\n\
             | mk : ListType Name -> KExpr -> KConstSig",
            "A constant signature: ordered universe parameter names and its schematic type. The record itself establishes no typing or admission invariant.",
        )?;
        for (source, description) in [
            (
                "def kconst_params (sig : KConstSig) : ListType Name := @KConstSig.rec (fun (_ : KConstSig) => ListType Name) (fun (params : ListType Name) (_ty : KExpr) => params) sig",
                "Project the ordered universe parameter names from the constant signature.",
            ),
            (
                "def kconst_type (sig : KConstSig) : KExpr := @KConstSig.rec (fun (_ : KConstSig) => KExpr) (fun (_params : ListType Name) (ty : KExpr) => ty) sig",
                "Project the schematic, not yet instantiated, constant type.",
            ),
        ] {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }

    /// Requires the early KConstSig carrier, OptionType and raw instantiation.
    /// Safe before iota, delta and every typing judgment.
    pub(super) fn add_declaration_signatures(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive KDefSig : Type\n\
             | mk : KConstSig -> KExpr -> KDefSig",
            "A definition's shared constant signature and schematic value. Its type and value use one stored parameter list; their typing relationship is a separate obligation.",
        )?;
        for (source, description) in [
            (
                "def KDeclEnv : Type := Name -> OptionType KConstSig",
                "Partial declaration-signature lookup. This carrier alone imposes no environment well-formedness or source correspondence.",
            ),
            (
                "def kdef_signature (defn : KDefSig) : KConstSig := @KDefSig.rec (fun (_ : KDefSig) => KConstSig) (fun (sig : KConstSig) (_value : KExpr) => sig) defn",
                "Project the single signature shared by definition typing and value instantiation.",
            ),
            (
                "def kdef_value (defn : KDefSig) : KExpr := @KDefSig.rec (fun (_ : KDefSig) => KExpr) (fun (_sig : KConstSig) (value : KExpr) => value) defn",
                "Project a definition's schematic, not yet instantiated, value.",
            ),
            (
                "def kconst_inst_type (sig : KConstSig) (us : ListType Level) : KExpr := instLevels (kconst_params sig) (kconst_type sig) us",
                "Instantiate the constant type with the signature's ordered universe parameters. Total raw operation; callers must require kconst_arity separately.",
            ),
            (
                "def kdef_inst_value (defn : KDefSig) (us : ListType Level) : KExpr := instLevels (kconst_params (kdef_signature defn)) (kdef_value defn) us",
                "Instantiate the definition value with the same parameter list used to instantiate its signature's type. No second value-specific parameter list exists.",
            ),
            (
                "def kconst_arity (sig : KConstSig) (us : ListType Level) : Prop := @Eq Nat (name_list_len (kconst_params sig)) (level_list_len us)",
                "Explicit exact-arity premise: declared parameter count equals supplied level count. This proposition is not automatically checked by the raw instantiation operations.",
            ),
            (
                "def kdecl_type_at (env : KDeclEnv) (n : Name) (us : ListType Level) : OptionType KExpr := @OptionType.rec KConstSig (fun (_found : OptionType KConstSig) => OptionType KExpr) (@OptionType.none KExpr) (fun (sig : KConstSig) => @Bool.rec (fun (_guard : Bool) => OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr (kconst_inst_type sig us)) (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us))) (env n)",
                "Computed universe-aware declaration lookup: missing name or mismatched arity returns none; otherwise returns the signature's instantiated type. No uninterpreted lookup or assumed guard reflection.",
            ),
        ] {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::Specification;
    use crate::test_utils::run_with_stack;

    fn signature_carrier_spec() -> Specification {
        let mut spec = Specification::new_empty();
        spec.add_foundation_types().expect("foundation types");
        spec.add_foundation_arith_lemmas()
            .expect("arithmetic lemmas");
        spec.add_foundation_arith_witnesses()
            .expect("arithmetic witnesses");
        spec.add_foundation_arith_positivity()
            .expect("arithmetic positivity");
        spec.add_foundation_arith_transport()
            .expect("arithmetic transport");
        spec.add_expr_model().expect("expression model");
        spec.add_declaration_signature_carrier()
            .expect("pure signature carrier before recursor environment");
        spec
    }

    fn signature_spec() -> Specification {
        let mut spec = signature_carrier_spec();
        spec.add_rec_env().expect("OptionType and name comparison");
        spec.add_univ_instantiation_syntax()
            .expect("raw universe instantiation");
        spec.add_declaration_signatures()
            .expect("declaration signature records");
        spec
    }

    #[test]
    fn stored_signature_carrier_registers_without_reduction_or_instantiation() {
        run_with_stack(|| {
            let mut spec = signature_carrier_spec();
            for later_name in [
                "OptionType",
                "RecMeta",
                "instLevels",
                "iota_reduct",
                "KDefSig",
            ] {
                assert!(
                    !spec.definitions().contains_key(later_name),
                    "pure stored signatures must not require {later_name}"
                );
            }
            spec.add_recursive_def(
                "def early_signature_params (ps : ListType Name) (ty : KExpr) : @Eq (ListType Name) (kconst_params (KConstSig.mk ps ty)) ps := @Eq.refl (ListType Name) ps",
                "Stored ordered parameters project before recursor or instantiation registration.",
            ).expect("early parameter projection");
            spec.add_recursive_def(
                "def early_signature_type (ps : ListType Name) (ty : KExpr) : @Eq KExpr (kconst_type (KConstSig.mk ps ty)) ty := @Eq.refl KExpr ty",
                "Stored schematic type projects before recursor or instantiation registration.",
            ).expect("early type projection");
            for name in ["early_signature_params", "early_signature_type"] {
                assert_checked_without_axioms(&spec, name);
            }
        });
    }

    fn add_sort_definition(spec: &mut Specification) {
        for (source, description) in [
            (
                "def signature_test_u : Name := Name.str Name.anonymous Nat.zero",
                "Test universe parameter u; this name is model syntax, not a source-name correspondence claim.",
            ),
            (
                "def signature_test_params : ListType Name := @ListType.cons Name signature_test_u (@ListType.nil Name)",
                "One declared universe parameter.",
            ),
            (
                "def signature_test_const : KConstSig := KConstSig.mk signature_test_params (KExpr.sort (Level.succ (Level.param signature_test_u)))",
                "Schematic signature with type Sort (succ u).",
            ),
            (
                "def signature_test_def : KDefSig := KDefSig.mk signature_test_const (KExpr.sort (Level.param signature_test_u))",
                "Definition fixture with value Sort u and type Sort (succ u). The tests check instantiation computations, not a typing judgment.",
            ),
            (
                "def signature_test_env : KDeclEnv := fun (_name : Name) => @OptionType.some KConstSig signature_test_const",
                "A value of the declaration-environment carrier; no well-formedness claim.",
            ),
        ] {
            spec.add_recursive_def(source, description)
                .expect("definition fixture");
        }
    }

    fn assert_checked_without_axioms(spec: &Specification, name: &str) {
        let definition = spec.definitions().get(name).expect("registered definition");
        assert!(!definition.is_axiom, "{name} must not be an axiom");
        assert!(
            definition.elaborated_value.is_some(),
            "{name} must have a kernel-checked value"
        );
        assert!(
            crate::spec_axiom_closure::computed_axiom_closure(spec, name).is_empty(),
            "{name} must have empty actual transitive axiom closure"
        );
    }

    #[test]
    fn declaration_signatures_share_params_and_instantiate_type_and_value() {
        run_with_stack(|| {
            let mut spec = signature_spec();
            for later_name in ["DefEnv", "delta_step", "evalL", "Typing", "TypingCtx"] {
                assert!(
                    !spec.definitions().contains_key(later_name),
                    "signature records must not require later stage {later_name}"
                );
            }
            add_sort_definition(&mut spec);
            for name in [
                "KDeclEnv",
                "kconst_params",
                "kconst_type",
                "kdef_signature",
                "kdef_value",
                "kconst_inst_type",
                "kdef_inst_value",
                "kconst_arity",
                "kdecl_type_at",
            ] {
                assert_checked_without_axioms(&spec, name);
            }
            for (suffix, level) in [("zero", "Level.zero"), ("one", "(Level.succ Level.zero)")] {
                let args = format!("(@ListType.cons Level {level} (@ListType.nil Level))");
                for (component, lhs, rhs) in [
                    (
                        "type",
                        format!("kconst_inst_type (kdef_signature signature_test_def) {args}"),
                        format!("KExpr.sort (Level.succ {level})"),
                    ),
                    (
                        "value",
                        format!("kdef_inst_value signature_test_def {args}"),
                        format!("KExpr.sort {level}"),
                    ),
                ] {
                    let name = format!("signature_test_{component}_{suffix}");
                    spec.add_recursive_def(
                        &format!(
                            "def {name} : @Eq KExpr ({lhs}) ({rhs}) := @Eq.refl KExpr ({rhs})"
                        ),
                        "Checked computation for a shared-signature universe instantiation.",
                    )
                    .expect("type/value instantiation must compute");
                    assert_checked_without_axioms(&spec, &name);
                }
                let name = format!("signature_test_arity_{suffix}");
                spec.add_recursive_def(
                    &format!("def {name} : kconst_arity signature_test_const {args} := @Eq.refl Nat (Nat.succ Nat.zero)"),
                    "One argument satisfies the fixture's one-parameter arity premise.",
                )
                .expect("matching arity");
                assert_checked_without_axioms(&spec, &name);
                let name = format!("signature_test_checked_lookup_{suffix}");
                spec.add_recursive_def(
                    &format!("def {name} : @Eq (OptionType KExpr) (kdecl_type_at signature_test_env signature_test_u {args}) (@OptionType.some KExpr (KExpr.sort (Level.succ {level}))) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ {level})))"),
                    "Computed lookup at this universe argument returns its actual instantiated type.",
                )
                .expect("arity-checked universe-aware lookup");
                assert_checked_without_axioms(&spec, &name);
            }
            for (name, source) in [
                (
                    "signature_test_shared_params",
                    "def signature_test_shared_params : @Eq (ListType Name) (kconst_params (kdef_signature signature_test_def)) signature_test_params := @Eq.refl (ListType Name) signature_test_params",
                ),
                (
                    "signature_test_shared_signature",
                    "def signature_test_shared_signature : @Eq KConstSig (kdef_signature signature_test_def) signature_test_const := @Eq.refl KConstSig signature_test_const",
                ),
                (
                    "signature_test_env_lookup",
                    "def signature_test_env_lookup : @Eq (OptionType KConstSig) (signature_test_env signature_test_u) (@OptionType.some KConstSig signature_test_const) := @Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig signature_test_const)",
                ),
            ] {
                spec.add_recursive_def(source, "Checked signature projection or lookup computation.")
                    .expect("signature projections");
                assert_checked_without_axioms(&spec, name);
            }
        });
    }

    #[test]
    fn declaration_signatures_refute_missing_argument_arity() {
        run_with_stack(|| {
            let mut spec = signature_spec();
            add_sort_definition(&mut spec);
            spec.add_recursive_def(
                "def signature_test_missing_arity_refuted : kconst_arity signature_test_const (@ListType.nil Level) -> Empty := fun (h : kconst_arity signature_test_const (@ListType.nil Level)) => @Eq.substType Nat (fun (n : Nat) => @Nat.rec (fun (_ : Nat) => Type) Empty (fun (_ : Nat) (_ : Type) => Nat) n) (Nat.succ Nat.zero) Nat.zero h Nat.zero",
                "An actual refutation of one parameter with zero arguments, using only equality transport and Nat's constructors.",
            )
            .expect("missing-argument arity must be refutable");
            assert_checked_without_axioms(&spec, "signature_test_missing_arity_refuted");
            assert!(spec
                .add_recursive_def(
                    "def signature_test_forged_missing_arity : kconst_arity signature_test_const (@ListType.nil Level) := @Eq.refl Nat Nat.zero",
                    "Negative control: the raw instantiation default cannot forge exact arity.",
                )
                .is_err());
            assert!(!spec
                .definitions()
                .contains_key("signature_test_forged_missing_arity"));
            spec.add_recursive_def(
                "def signature_test_raw_missing_argument_default : @Eq KExpr (kdef_inst_value signature_test_def (@ListType.nil Level)) (KExpr.sort Level.zero) := @Eq.refl KExpr (KExpr.sort Level.zero)",
                "The raw operation retains its zero default even though the separate arity proposition is refuted. Future typing and delta callers must require the premise.",
            )
            .expect("raw instantiation is deliberately total");
            assert_checked_without_axioms(&spec, "signature_test_raw_missing_argument_default");
            for (name, source) in [
                (
                    "signature_test_lookup_missing_argument",
                    "def signature_test_lookup_missing_argument : @Eq (OptionType KExpr) (kdecl_type_at signature_test_env signature_test_u (@ListType.nil Level)) (@OptionType.none KExpr) := @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
                ),
                (
                    "signature_test_lookup_extra_argument",
                    "def signature_test_lookup_extra_argument : @Eq (OptionType KExpr) (kdecl_type_at signature_test_env signature_test_u (@ListType.cons Level Level.zero (@ListType.cons Level Level.zero (@ListType.nil Level)))) (@OptionType.none KExpr) := @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
                ),
                (
                    "signature_test_lookup_missing_name",
                    "def signature_test_lookup_missing_name : @Eq (OptionType KExpr) (kdecl_type_at (fun (_name : Name) => @OptionType.none KConstSig) signature_test_u (@ListType.cons Level Level.zero (@ListType.nil Level))) (@OptionType.none KExpr) := @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
                ),
            ] {
                spec.add_recursive_def(source, "Computed lookup refuses missing declarations and incorrect argument counts.")
                    .expect("fail-closed lookup computation");
                assert_checked_without_axioms(&spec, name);
            }
            assert!(spec
                .add_recursive_def(
                    "def signature_test_forged_short_lookup : @Eq (OptionType KExpr) (kdecl_type_at signature_test_env signature_test_u (@ListType.nil Level)) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero))) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
                    "Negative control: raw instantiation's default must not escape the lookup's arity check.",
                )
                .is_err());
            assert!(spec
                .add_recursive_def(
                    "def signature_test_type_value_confusion : @Eq KExpr (kconst_inst_type signature_test_const (@ListType.cons Level Level.zero (@ListType.nil Level))) (KExpr.sort Level.zero) := @Eq.refl KExpr (KExpr.sort Level.zero)",
                    "Negative control: the instantiated type is Sort (succ zero), not the definition's Sort zero value.",
                )
                .is_err());
        });
    }
}
