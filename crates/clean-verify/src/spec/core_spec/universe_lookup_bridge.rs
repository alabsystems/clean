// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arity-checked agreement of the two existing parameter-lookup models.
//!
//! Ports the exact-export guide
//! scratch/self-verification-param-lookup-2026-09-08.lean. The source-shaped
//! model zips lists and preserves an unmatched parameter; paramSubstN uses a
//! positional index with zero as the out-of-range default. Equal arity is
//! consumed in the proof. Both models use first-match lookup; this does not
//! establish the production hash-map branch, NoDup admission, structural
//! Rust-name fidelity, or smart-level-constructor correspondence.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn lookup_theorem(
    spec: &mut Specification,
    name: &str,
    type_src: &str,
    value_src: &str,
    description: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: type_src.to_string(),
        value_src: Some(value_src.to_string()),
        is_axiom: false,
        description: description.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: None,
        axiom_deps: HashSet::new(),
    })
}

impl Specification {
    /// Full-only: consumes the early universe substrate and impl_infer_syntax.
    pub(super) fn add_universe_lookup_bridge(&mut self) -> Result<(), SpecError> {
        // These helpers must remain reducible: the cons equations below use
        // their stored bodies, not an asserted relationship to opaque values.
        self.add_recursive_def(
            "def univ_lookup_idx_shift (r : OptionType Nat) : OptionType Nat := OptionType.rec Nat (fun (_ : OptionType Nat) => OptionType Nat) (OptionType.none Nat) (fun (i : Nat) => OptionType.some Nat (Nat.succ i)) r",
            "Successor-map for a positional lookup index.",
        )?;
        self.add_recursive_def(
            "def univ_lookup_idx_get (n : Name) (us : ListType Level) (r : OptionType Nat) : Level := OptionType.rec Nat (fun (_ : OptionType Nat) => Level) (Level.param n) (fun (i : Nat) => list_getD us i) r",
            "Resolve a positional index with the existing list_getD default.",
        )?;
        self.add_recursive_def(
            "def univ_lookup_get (n : Name) (r : OptionType Level) : Level := OptionType.rec Level (fun (_ : OptionType Level) => Level) (Level.param n) (fun (u : Level) => u) r",
            "Resolve zipped lookup while preserving an unmatched parameter.",
        )?;

        lookup_theorem(
            self,
            "name_eqb_symm",
            r"forall (p : Name) (q : Name), Eq Bool (name_eqb p q) (name_eqb q p)",
            r"fun (p : Name) (q : Name) =>
  Name.rec (fun (p0 : Name) => forall (q0 : Name), Eq Bool (name_eqb p0 q0) (name_eqb q0 p0))
    (fun (q0 : Name) =>
      Name.rec (fun (q1 : Name) => Eq Bool (name_eqb Name.anonymous q1) (name_eqb q1 Name.anonymous))
        (Eq.refl Bool Bool.true)
        (fun (r : Name) (n : Nat)
          (_ih : Eq Bool (name_eqb Name.anonymous r) (name_eqb r Name.anonymous)) =>
          Eq.refl Bool Bool.false) q0)
    (fun (p0 : Name) (m : Nat)
      (ih : forall (q0 : Name), Eq Bool (name_eqb p0 q0) (name_eqb q0 p0))
      (q0 : Name) =>
      Name.rec (fun (q1 : Name) =>
        Eq Bool (name_eqb (Name.str p0 m) q1) (name_eqb q1 (Name.str p0 m)))
        (Eq.refl Bool Bool.false)
        (fun (r : Name) (n : Nat)
          (_ih : Eq Bool (name_eqb (Name.str p0 m) r) (name_eqb r (Name.str p0 m))) =>
          Eq.trans Bool
            (Bool.and (name_eqb p0 r) (nat_eqb m n))
            (Bool.and (name_eqb r p0) (nat_eqb m n))
            (Bool.and (name_eqb r p0) (nat_eqb n m))
            (Eq.cong Bool Bool (fun (b : Bool) => Bool.and b (nat_eqb m n))
              (name_eqb p0 r) (name_eqb r p0) (ih r))
            (Eq.cong Bool Bool (fun (b : Bool) => Bool.and (name_eqb r p0) b)
              (nat_eqb m n) (nat_eqb n m) (nat_eqb_symm m n))) q0)
    p q",
            "Symmetry of the existing reflected name comparison, derived by Name recursion and the checked nat_eqb symmetry theorem; not a structural Rust-name representation claim.",
        )?;

        lookup_theorem(
            self,
            "univ_lookup_param_cons_compute",
            r"forall (n : Name) (u : Level) (us : ListType Level) (r : OptionType Nat) (b : Bool),
 Eq Level
   (univ_lookup_idx_get n (ListType.cons Level u us)
     (Bool.rec (fun (_ : Bool) => OptionType Nat)
       (univ_lookup_idx_shift r) (OptionType.some Nat Nat.zero) b))
   (Bool.rec (fun (_ : Bool) => Level) (univ_lookup_idx_get n us r) u b)",
            r"fun (n : Name) (u : Level) (us : ListType Level) (r : OptionType Nat) (b : Bool) =>
 Bool.rec (fun (b0 : Bool) => Eq Level
   (univ_lookup_idx_get n (ListType.cons Level u us)
     (Bool.rec (fun (_ : Bool) => OptionType Nat)
       (univ_lookup_idx_shift r) (OptionType.some Nat Nat.zero) b0))
   (Bool.rec (fun (_ : Bool) => Level) (univ_lookup_idx_get n us r) u b0))
   (OptionType.rec Nat (fun (r0 : OptionType Nat) => Eq Level
      (univ_lookup_idx_get n (ListType.cons Level u us) (univ_lookup_idx_shift r0))
      (univ_lookup_idx_get n us r0))
     (Eq.refl Level (Level.param n))
     (fun (i : Nat) => Eq.refl Level (list_getD us i)) r)
   (Eq.refl Level u) b",
            "Positional parameter lookup under one matched name/level pair, by Bool and Option recursion.",
        )?;

        lookup_theorem(
            self,
            "univ_lookup_cons_compute",
            r"forall (n : Name) (u : Level) (r : OptionType Level) (b : Bool),
 Eq Level
   (univ_lookup_get n (Bool.rec (fun (_ : Bool) => OptionType Level) r (OptionType.some Level u) b))
   (Bool.rec (fun (_ : Bool) => Level) (univ_lookup_get n r) u b)",
            r"fun (n : Name) (u : Level) (r : OptionType Level) (b : Bool) =>
 Bool.rec (fun (b0 : Bool) => Eq Level
   (univ_lookup_get n (Bool.rec (fun (_ : Bool) => OptionType Level) r (OptionType.some Level u) b0))
   (Bool.rec (fun (_ : Bool) => Level) (univ_lookup_get n r) u b0))
   (Eq.refl Level (univ_lookup_get n r)) (Eq.refl Level u) b",
            "Zipped lookup under one matched name/level pair, by Bool recursion.",
        )?;

        lookup_theorem(
            self,
            "univ_lookup_cons",
            r"forall (p : Name) (ps : ListType Name) (u : Level) (us : ListType Level) (n : Name)
 (ih : Eq Level (paramSubstN ps us n) (level_subst ps us (Level.param n))),
 Eq Level (paramSubstN (ListType.cons Name p ps) (ListType.cons Level u us) n)
   (level_subst (ListType.cons Name p ps) (ListType.cons Level u us) (Level.param n))",
            r"fun (p : Name) (ps : ListType Name) (u : Level) (us : ListType Level) (n : Name)
 (ih : Eq Level (paramSubstN ps us n) (level_subst ps us (Level.param n))) =>
 Eq.trans Level
   (paramSubstN (ListType.cons Name p ps) (ListType.cons Level u us) n)
   (Bool.rec (fun (_ : Bool) => Level) (paramSubstN ps us n) u (name_eqb n p))
   (level_subst (ListType.cons Name p ps) (ListType.cons Level u us) (Level.param n))
   (univ_lookup_param_cons_compute n u us (nameIdx ps n) (name_eqb n p))
   (Eq.trans Level
     (Bool.rec (fun (_ : Bool) => Level) (paramSubstN ps us n) u (name_eqb n p))
     (Bool.rec (fun (_ : Bool) => Level) (level_subst ps us (Level.param n)) u (name_eqb n p))
     (level_subst (ListType.cons Name p ps) (ListType.cons Level u us) (Level.param n))
     (Eq.cong Level Level
       (fun (v : Level) => Bool.rec (fun (_ : Bool) => Level) v u (name_eqb n p))
       (paramSubstN ps us n) (level_subst ps us (Level.param n)) ih)
     (Eq.trans Level
       (Bool.rec (fun (_ : Bool) => Level) (level_subst ps us (Level.param n)) u (name_eqb n p))
       (Bool.rec (fun (_ : Bool) => Level) (level_subst ps us (Level.param n)) u (name_eqb p n))
       (level_subst (ListType.cons Name p ps) (ListType.cons Level u us) (Level.param n))
       (Eq.cong Bool Level
         (fun (b : Bool) => Bool.rec (fun (_ : Bool) => Level) (level_subst ps us (Level.param n)) u b)
         (name_eqb n p) (name_eqb p n) (name_eqb_symm n p))
       (Eq.symm Level
         (level_subst (ListType.cons Name p ps) (ListType.cons Level u us) (Level.param n))
         (Bool.rec (fun (_ : Bool) => Level) (level_subst ps us (Level.param n)) u (name_eqb p n))
         (univ_lookup_cons_compute n u (level_lookup ps us n) (name_eqb p n)))))",
            "Extend lookup agreement by one matching name/level pair, explicitly transporting across reversed name-comparison argument order.",
        )?;

        lookup_theorem(
            self,
            "univ_lookup_succ_zero_absurd",
            r"forall (m : Nat) (h : Eq Nat (Nat.succ m) Nat.zero) (P : Prop), P",
            r"fun (m : Nat) (h : Eq Nat (Nat.succ m) Nat.zero) (P : Prop) =>
 Eq.rec Nat (Nat.succ m)
   (fun (k : Nat) (_h : Eq Nat (Nat.succ m) k) =>
     Nat.rec (fun (_ : Nat) => Prop) P
       (fun (_ : Nat) (_ : Prop) => Eq Nat Nat.zero Nat.zero) k)
   (Eq.refl Nat Nat.zero) Nat.zero h",
            "Primitive equality elimination excludes successor-equals-zero arity; no new arithmetic axiom.",
        )?;

        lookup_theorem(
            self,
            "paramSubstN_eq_level_lookup",
            r"forall (names : ListType Name) (us : ListType Level) (n : Name)
 (arity : Eq Nat (name_list_len names) (level_list_len us)),
 Eq Level (paramSubstN names us n) (level_subst names us (Level.param n))",
            r"fun (names : ListType Name) (us : ListType Level) (n : Name)
 (arity : Eq Nat (name_list_len names) (level_list_len us)) =>
 ListType.rec Name (fun (names0 : ListType Name) =>
   forall (us0 : ListType Level) (n0 : Name),
     Eq Nat (name_list_len names0) (level_list_len us0) ->
     Eq Level (paramSubstN names0 us0 n0) (level_subst names0 us0 (Level.param n0)))
   (fun (us0 : ListType Level) (n0 : Name)
     (_arity : Eq Nat (name_list_len (ListType.nil Name)) (level_list_len us0)) =>
     Eq.refl Level (Level.param n0))
   (fun (p : Name) (ps : ListType Name)
     (ih : forall (us0 : ListType Level) (n0 : Name),
       Eq Nat (name_list_len ps) (level_list_len us0) ->
       Eq Level (paramSubstN ps us0 n0) (level_subst ps us0 (Level.param n0)))
     (us0 : ListType Level) =>
     ListType.rec Level (fun (us1 : ListType Level) => forall (n0 : Name),
       Eq Nat (name_list_len (ListType.cons Name p ps)) (level_list_len us1) ->
       Eq Level (paramSubstN (ListType.cons Name p ps) us1 n0)
         (level_subst (ListType.cons Name p ps) us1 (Level.param n0)))
       (fun (n0 : Name)
         (h : Eq Nat (name_list_len (ListType.cons Name p ps)) (level_list_len (ListType.nil Level))) =>
         univ_lookup_succ_zero_absurd (name_list_len ps) h
           (Eq Level (paramSubstN (ListType.cons Name p ps) (ListType.nil Level) n0)
             (level_subst (ListType.cons Name p ps) (ListType.nil Level) (Level.param n0))))
       (fun (u : Level) (us1 : ListType Level)
         (_ih : forall (n0 : Name),
           Eq Nat (name_list_len (ListType.cons Name p ps)) (level_list_len us1) ->
           Eq Level (paramSubstN (ListType.cons Name p ps) us1 n0)
             (level_subst (ListType.cons Name p ps) us1 (Level.param n0)))
         (n0 : Name)
         (h : Eq Nat (name_list_len (ListType.cons Name p ps)) (level_list_len (ListType.cons Level u us1))) =>
         univ_lookup_cons p ps u us1 n0
           (ih us1 n0
             (Eq.cong Nat Nat Nat.pred
               (name_list_len (ListType.cons Name p ps))
               (level_list_len (ListType.cons Level u us1)) h))) us0)
   names us n arity",
            "Checked equal arity makes existing positional/default and zipped/parameter-preserving model lookup agree. List induction consumes the arity proof; no desired-result equality is assumed.",
        )?;

        lookup_theorem(
            self,
            "paramSubstN_eq_lookup_result",
            r"forall (names : ListType Name) (us : ListType Level) (n : Name)
 (arity : Eq Nat (name_list_len names) (level_list_len us)),
 Eq Level (paramSubstN names us n)
   (OptionType.rec Level (fun (_ : OptionType Level) => Level)
     (Level.param n) (fun (u : Level) => u) (level_lookup names us n))",
            r"fun (names : ListType Name) (us : ListType Level) (n : Name)
 (arity : Eq Nat (name_list_len names) (level_list_len us)) =>
 paramSubstN_eq_level_lookup names us n arity",
            "The arity theorem stated directly against the existing zipped lookup/default expression.",
        )?;

        lookup_theorem(
            self,
            "param_lookup_hit_witness",
            r"Eq Level
 (paramSubstN (ListType.cons Name Name.anonymous (ListType.nil Name))
   (ListType.cons Level (Level.succ Level.zero) (ListType.nil Level)) Name.anonymous)
 (level_subst (ListType.cons Name Name.anonymous (ListType.nil Name))
   (ListType.cons Level (Level.succ Level.zero) (ListType.nil Level)) (Level.param Name.anonymous))",
            r"paramSubstN_eq_level_lookup
 (ListType.cons Name Name.anonymous (ListType.nil Name))
 (ListType.cons Level (Level.succ Level.zero) (ListType.nil Level))
 Name.anonymous (Eq.refl Nat (Nat.succ Nat.zero))",
            "Non-vacuity witness: a matching parameter is instantiated to a nonzero level.",
        )?;

        lookup_theorem(
            self,
            "param_lookup_short_lists_differ",
            r"Eq Level
 (paramSubstN (ListType.cons Name Name.anonymous (ListType.nil Name))
   (ListType.nil Level) Name.anonymous)
 (level_subst (ListType.cons Name Name.anonymous (ListType.nil Name))
   (ListType.nil Level) (Level.param Name.anonymous)) -> Empty",
            r"fun (h : Eq Level
 (paramSubstN (ListType.cons Name Name.anonymous (ListType.nil Name))
   (ListType.nil Level) Name.anonymous)
 (level_subst (ListType.cons Name Name.anonymous (ListType.nil Name))
   (ListType.nil Level) (Level.param Name.anonymous))) =>
 Eq.rec Level Level.zero
   (fun (l : Level) (_h : Eq Level Level.zero l) =>
     Level.rec (fun (_ : Level) => Type) Nat
       (fun (_ : Level) (_ : Type) => Nat)
       (fun (_ : Level) (_ : Level) (_ : Type) (_ : Type) => Nat)
       (fun (_ : Level) (_ : Level) (_ : Type) (_ : Type) => Nat)
       (fun (_ : Name) => Empty) l)
   Nat.zero (Level.param Name.anonymous) h",
            "Constructive negative control: a short argument list exposes the two models' different defaults. The arity premise cannot be silently removed.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::lookup_theorem;
    use crate::spec::types::ProofStatus;
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn registered_lookup_terms_have_checked_values_and_empty_axiom_residuals() {
        let spec = build_spec_with_stack();
        for name in [
            "name_eqb_symm",
            "univ_lookup_param_cons_compute",
            "univ_lookup_cons_compute",
            "univ_lookup_cons",
            "univ_lookup_succ_zero_absurd",
            "paramSubstN_eq_level_lookup",
            "paramSubstN_eq_lookup_result",
            "param_lookup_hit_witness",
            "param_lookup_short_lists_differ",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .expect("registered lookup theorem");
            assert!(!def.is_axiom, "{name} must carry a proof");
            assert_eq!(def.proof_status, ProofStatus::DerivedProved);
            assert!(def.elaborated_value.is_some(), "{name} must be elaborated");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name} must have no transitive axiom residual"
            );
        }
    }

    #[test]
    fn lookup_arity_samples_and_mismatch_controls_are_kernel_checked() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            // These exercise the model theorem at, and beyond, the production
            // branch threshold. They do NOT establish HashMap correspondence.
            for count in [0, 1, 4, 5] {
                let mut names = "ListType.nil Name".to_string();
                let mut levels = "ListType.nil Level".to_string();
                let mut tag = "Nat.zero".to_string();
                for _ in 0..count {
                    names =
                        format!("ListType.cons Name (Name.str Name.anonymous ({tag})) ({names})");
                    levels = format!("ListType.cons Level (Level.succ Level.zero) ({levels})");
                    tag = format!("Nat.succ ({tag})");
                }
                let query = "Name.str Name.anonymous Nat.zero";
                let name = format!("param_lookup_arity_{count}_regression");
                lookup_theorem(
                    &mut spec,
                    &name,
                    &format!("Eq Level (paramSubstN ({names}) ({levels}) ({query})) (level_subst ({names}) ({levels}) (Level.param ({query})))"),
                    &format!("paramSubstN_eq_level_lookup ({names}) ({levels}) ({query}) (Eq.refl Nat (name_list_len ({names})))"),
                    "Regression: the arity theorem accepts matching lists of this length using actual checked length computation.",
                )
                .expect("matching-arity lookup witness");
                assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, &name).is_empty());
            }

            assert!(lookup_theorem(
                &mut spec,
                "param_lookup_false_arity_must_fail",
                "Eq Nat (Nat.succ Nat.zero) Nat.zero",
                "Eq.refl Nat Nat.zero",
                "Negative control: the checked arity obligation is not a fabricated equality.",
            )
            .is_err());
            assert!(
                lookup_theorem(
                    &mut spec,
                    "param_lookup_short_equality_must_fail",
                    concat!(
                        "Eq Level (paramSubstN ",
                        "(ListType.cons Name Name.anonymous (ListType.nil Name)) ",
                        "(ListType.nil Level) Name.anonymous) ",
                        "(level_subst (ListType.cons Name Name.anonymous (ListType.nil Name)) ",
                        "(ListType.nil Level) (Level.param Name.anonymous))"
                    ),
                    "Eq.refl Level Level.zero",
                    "Negative control: short-list positional and zipped defaults are genuinely unequal.",
                )
                .is_err()
            );
        });
    }
}
