// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Early raw universe-instantiation syntax shared by declaration typing and delta.
//!
//! This stage is a mechanical relocation of existing definitions, not a change
//! to their terms or a proof of production smart-substitution correspondence.
//! It needs only the foundation, expression model, and rec_env primitives.
//! In particular, instLevels is total and does not enforce arity: callers must
//! check it, and a missing positional argument retains the existing zero default.
//! Semantic universe theory and substitution proofs stay in univ_poly.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Safe after rec_env; staged before iota_step and delta_step_core.
    pub(super) fn add_univ_instantiation_syntax(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def substL (s : Name -> Level) (l : Level) : Level := Level.rec (fun (_ : Level) => Level) Level.zero (fun (l0 : Level) (ih : Level) => Level.succ ih) (fun (a : Level) (b : Level) (iha : Level) (ihb : Level) => Level.max iha ihb) (fun (a : Level) (b : Level) (iha : Level) (ihb : Level) => Level.imax iha ihb) (fun (n : Name) => s n) l",
            "substL s l: level substitution (param n -> s n, homomorphic elsewhere). The instantiation operation of universe polymorphism. UnivPoly rung.",
        )?;

        self.add_recursive_def(
            "def mapLL (f : Level -> Level) (l : ListType Level) : ListType Level := ListType.rec Level (fun (_ : ListType Level) => ListType Level) (ListType.nil Level) (fun (x : Level) (rest : ListType Level) (ih : ListType Level) => ListType.cons Level (f x) ih) l",
            "mapLL f l: map over a Level list (the Level companion of mapLT). UnivPoly rung A2.",
        )?;

        self.add_recursive_def(
            "def list_getD (l : ListType Level) (i : Nat) : Level := ListType.rec Level (fun (_ : ListType Level) => Nat -> Level) (fun (i0 : Nat) => Level.zero) (fun (x : Level) (rest : ListType Level) (ih : Nat -> Level) => fun (i0 : Nat) => Nat.rec (fun (_ : Nat) => Level) x (fun (i1 : Nat) (_ : Level) => ih i1) i0) l i",
            "list_getD l i: positional Level-list lookup defaulting to zero out of range (unreachable for well-formed consts — the typing rule pins the length). UnivPoly rung A2.",
        )?;

        self.add_recursive_def(
            "def nameIdx (names : ListType Name) (n : Name) : OptionType Nat := ListType.rec Name (fun (_ : ListType Name) => OptionType Nat) (OptionType.none Nat) (fun (x : Name) (rest : ListType Name) (ih : OptionType Nat) => Bool.rec (fun (_ : Bool) => OptionType Nat) (OptionType.rec Nat (fun (_ : OptionType Nat) => OptionType Nat) (OptionType.none Nat) (fun (i : Nat) => OptionType.some Nat (Nat.succ i)) ih) (OptionType.some Nat Nat.zero) (name_eqb n x)) names",
            "nameIdx names n: position of n in a param-name list (Bool.rec on name_eqb; hit -> some 0, miss -> succ-mapped tail lookup). UnivPoly rung A2.",
        )?;

        self.add_recursive_def(
            "def paramSubstN (names : ListType Name) (us : ListType Level) (n : Name) : Level := OptionType.rec Nat (fun (_ : OptionType Nat) => Level) (Level.param n) (fun (i : Nat) => list_getD us i) (nameIdx names n)",
            "paramSubstN names us: the level substitution a const's level list induces — param n -> us[position of n in names], unknown params untouched (the kernel's instantiate_level_params semantics at spec shape). UnivPoly rung A2.",
        )?;

        self.add_recursive_def(
            "def instL (s : Name -> Level) (e : KExpr) : KExpr := KExpr.rec (fun (_ : KExpr) => KExpr) (fun (u : Level) => KExpr.sort (substL s u)) (fun (i : Nat) => KExpr.bvar i) (fun (f : KExpr) (a : KExpr) (ihf : KExpr) (iha : KExpr) => KExpr.app ihf iha) (fun (A : KExpr) (b : KExpr) (ihA : KExpr) (ihb : KExpr) => KExpr.lam ihA ihb) (fun (A : KExpr) (B : KExpr) (ihA : KExpr) (ihB : KExpr) => KExpr.pi ihA ihB) (fun (n : Name) (us : ListType Level) => KExpr.const n (mapLL (substL s) us)) (fun (A : KExpr) (v : KExpr) (b : KExpr) (ihA : KExpr) (ihv : KExpr) (ihb : KExpr) => KExpr.let_ ihA ihv ihb) (fun (sn : Name) (i : Nat) (sub : KExpr) (ihsub : KExpr) => KExpr.proj sn i ihsub) (fun (v : Nat) => KExpr.lit v) e",
            "instL s e: level instantiation over the FULL 9-ctor KExpr (substL on sorts and const level lists, homomorphic elsewhere; bvar/lit untouched). The spec shape of the kernel's level instantiation. UnivPoly rung A2.",
        )?;

        self.add_recursive_def(
            "def instLevels (names : ListType Name) (T : KExpr) (us : ListType Level) : KExpr := instL (paramSubstN names us) T",
            "instLevels names T us: instantiate a declared level-schematic type at a const's level list (the kernel's type.instantiate_level_params(decl.params, us) at spec shape). UnivPoly rung A2.",
        )?;

        self.add_recursive_def(
            r"def name_list_len (xs : ListType Name) : Nat := ListType.rec Name (fun (_ : ListType Name) => Nat) Nat.zero (fun (y : Name) (rest : ListType Name) (ih : Nat) => Nat.succ ih) xs",
            "Length of a Name list — the `info.level_params.len()` side of the \
             release Const arm's arity check (tc/infer.rs:383).",
        )?;

        self.add_recursive_def(
            r"def level_list_len (xs : ListType Level) : Nat := ListType.rec Level (fun (_ : ListType Level) => Nat) Nat.zero (fun (u : Level) (rest : ListType Level) (ih : Nat) => Nat.succ ih) xs",
            "Length of a Level list — the `levels.len()` side of the release Const \
             arm's arity check (tc/infer.rs:383).",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::Specification;
    use crate::test_utils::run_with_stack;

    #[test]
    fn raw_universe_syntax_registers_before_delta_and_semantic_proofs() {
        run_with_stack(|| {
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
                .expect("pure stored signature carrier");
            spec.add_rec_env().expect("OptionType and name comparison");
            spec.add_univ_instantiation_syntax()
                .expect("early raw operations");
            spec.add_recursor_rhs_instantiation_syntax()
                .expect("guarded RHS operation before iota");
            spec.add_recursor_rhs_instantiation_guard_views()
                .expect("Boolean views before arithmetic reflection");

            for name in [
                "substL",
                "mapLL",
                "list_getD",
                "nameIdx",
                "paramSubstN",
                "instL",
                "instLevels",
                "name_list_len",
                "level_list_len",
            ] {
                let def = spec.definitions().get(name).expect("moved definition");
                assert!(!def.is_axiom);
                assert!(def.elaborated_value.is_some(), "{name} must be checked");
            }
            for later_name in [
                "iota_reduct",
                "nat_eqb_eq",
                "DefEnv",
                "natMax",
                "evalL",
                "TypingCtx",
            ] {
                assert!(
                    !spec.definitions().contains_key(later_name),
                    "the early raw stage must not require {later_name}"
                );
            }

            spec.add_recursive_def(
                concat!(
                    "def early_raw_instantiation_witness : Eq KExpr ",
                    "(instLevels (ListType.cons Name Name.anonymous (ListType.nil Name)) ",
                    "(KExpr.sort (Level.param Name.anonymous)) ",
                    "(ListType.cons Level (Level.succ Level.zero) (ListType.nil Level))) ",
                    "(KExpr.sort (Level.succ Level.zero)) := ",
                    "Eq.refl KExpr (KExpr.sort (Level.succ Level.zero))"
                ),
                "Early-stage regression: raw instantiation computes on a nonzero universe argument.",
            )
            .expect("early instantiation computation");
            spec.add_recursive_def(
                concat!(
                    "def early_raw_short_list_witness : Eq KExpr ",
                    "(instLevels (ListType.cons Name Name.anonymous (ListType.nil Name)) ",
                    "(KExpr.sort (Level.param Name.anonymous)) (ListType.nil Level)) ",
                    "(KExpr.sort Level.zero) := Eq.refl KExpr (KExpr.sort Level.zero)"
                ),
                "Early-stage regression: the moved raw function retains its zero default; it does not silently gain an arity check.",
            )
            .expect("unchanged short-list default");
            spec.add_recursive_def(
                "def early_rhs_view_without_late_reflection : Eq Nat (recursor_rhs_at_guard_inv (KConstSig.mk (ListType.nil Name) (KExpr.sort Level.zero)) (KExpr.sort Level.zero) (ListType.nil Level) (KExpr.sort Level.zero) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort Level.zero))) Nat (fun (_guard : Eq Bool (nat_eqb Nat.zero Nat.zero) Bool.true) (_returned : Eq KExpr (KExpr.sort Level.zero) (KExpr.sort Level.zero)) => Nat.zero)) Nat.zero := Eq.refl Nat Nat.zero",
                "The actual early Boolean CPS view computes before iota, arithmetic equality reflection, and semantic proofs.",
            ).expect("early RHS guard view has a real caller");
            for name in [
                "early_raw_instantiation_witness",
                "early_raw_short_list_witness",
                "early_rhs_view_without_late_reflection",
            ] {
                assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty());
            }
        });
    }
}
