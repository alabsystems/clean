// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semantic-universe equivalence preserves de Bruijn closedness, allowing the
//! schematic constant-signature invariant to reach actual inferred results.
//! This does not assert preservation of syntactic universe-parameter support,
//! valid production admission, a complete environment invariant or Rust refinement.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_semantic_closedness(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def kexprUniverseEq_preserves_closed_at (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2) :
 forall (d : Nat), is_closed_at e d -> is_closed_at e2 d :=
 KExprUniverseEq.rec
 (fun (x : KExpr) (y : KExpr) (_h : KExprUniverseEq x y) =>
 forall (d : Nat), is_closed_at x d -> is_closed_at y d)
 (fun (u : Level) (v : Level) (_h : levelEqSem u v) => fun (d : Nat) (_hc : is_closed_at (KExpr.sort u) d) => is_closed_at.sort v d)
 (fun (i : Nat) => fun (d : Nat) (hc : is_closed_at (KExpr.bvar i) d) => hc)
 (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr)
 (_hf : KExprUniverseEq f f2) (_ha : KExprUniverseEq a a2)
 (ihf : forall (d : Nat), is_closed_at f d -> is_closed_at f2 d) (iha : forall (d : Nat), is_closed_at a d -> is_closed_at a2 d) =>
 fun (d : Nat) (hc : is_closed_at (KExpr.app f a) d) =>
 is_closed_at.app f2 a2 d (ihf d (is_closed_at_app_fun f a d hc)) (iha d (is_closed_at_app_arg f a d hc)))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr)
 (_hA : KExprUniverseEq A A2) (_hb : KExprUniverseEq b b2)
 (ihA : forall (d : Nat), is_closed_at A d -> is_closed_at A2 d) (ihb : forall (d : Nat), is_closed_at b d -> is_closed_at b2 d) =>
 fun (d : Nat) (hc : is_closed_at (KExpr.lam A b) d) =>
 is_closed_at.lam A2 b2 d (ihA d (is_closed_at_lam_type A b d hc)) (ihb (Nat.succ d) (is_closed_at_lam_body A b d hc)))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr)
 (_hA : KExprUniverseEq A A2) (_hb : KExprUniverseEq b b2)
 (ihA : forall (d : Nat), is_closed_at A d -> is_closed_at A2 d) (ihb : forall (d : Nat), is_closed_at b d -> is_closed_at b2 d) =>
 fun (d : Nat) (hc : is_closed_at (KExpr.pi A b) d) =>
 is_closed_at.pi A2 b2 d (ihA d (is_closed_at_pi_type A b d hc)) (ihb (Nat.succ d) (is_closed_at_pi_body A b d hc)))
 (fun (n : Name) (us : ListType Level) (vs : ListType Level) (_h : LevelListEqSem us vs) => fun (d : Nat) (_hc : is_closed_at (KExpr.const n us) d) => is_closed_at.const n vs d)
 (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr)
 (_hA : KExprUniverseEq A A2) (_hv : KExprUniverseEq v v2) (_hb : KExprUniverseEq b b2)
 (ihA : forall (d : Nat), is_closed_at A d -> is_closed_at A2 d) (ihv : forall (d : Nat), is_closed_at v d -> is_closed_at v2 d) (ihb : forall (d : Nat), is_closed_at b d -> is_closed_at b2 d) =>
 fun (d : Nat) (hc : is_closed_at (KExpr.let_ A v b) d) =>
 is_closed_at.let_ A2 v2 b2 d (ihA d (is_closed_at_let_ty A v b d hc)) (ihv d (is_closed_at_let_val A v b d hc)) (ihb (Nat.succ d) (is_closed_at_let_body A v b d hc)))
 (fun (n : Name) (i : Nat) (b : KExpr) (b2 : KExpr) (_h : KExprUniverseEq b b2)
 (ih : forall (d : Nat), is_closed_at b d -> is_closed_at b2 d) =>
 fun (d : Nat) (hc : is_closed_at (KExpr.proj n i b) d) =>
 is_closed_at.proj n i b2 d (ih d (is_closed_at_proj_sub n i b d hc)))
 (fun (n : Nat) => fun (d : Nat) (hc : is_closed_at (KExpr.lit n) d) => hc) e e2 h",
            "Universe equivalence preserves actual de Bruijn closedness at any depth; all nine expression cases use existing closedness constructors and inverters. This is not syntactic universe-parameter support preservation.",
        )?;
        self.add_recursive_def(
            r"def kernel_infers_in_constant_result_closed (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (n : Name) (us : ListType Level) (T : KExpr)
 (stored : forall (sig : KConstSig), Eq (OptionType KConstSig) (tenv n) (OptionType.some KConstSig sig) ->
 is_closed_at (kconst_type sig) Nat.zero)
 (h : KernelInfersIn R tenv G (KExpr.const n us) T) : is_closed_at T Nat.zero :=
 kernel_infers_in_constant_inv R tenv G n us T h (is_closed_at T Nat.zero)
 (fun (A : KExpr) (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A))
 (related : KExprUniverseEq A T) =>
 kexprUniverseEq_preserves_closed_at A T related Nat.zero
 (kdecl_type_at_closed tenv n us A stored lookup))",
            "Derive closedness of an actual semantic constant inference result from schematic stored-type closedness, guarded lookup inversion, and semantic closedness preservation. No per-instantiated-result closedness or typing assumption.",
        )?;
        self.add_recursive_def(
            r"def kernel_infers_in_constant_loose_result_refused (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (n : Name) (us : ListType Level) (i : Nat)
 (stored : forall (sig : KConstSig), Eq (OptionType KConstSig) (tenv n) (OptionType.some KConstSig sig) ->
 is_closed_at (kconst_type sig) Nat.zero)
 (h : KernelInfersIn R tenv G (KExpr.const n us) (KExpr.bvar i)) : Empty :=
 not_lt_zero i
 (is_closed_at_bvar_inv i Nat.zero
 (kernel_infers_in_constant_result_closed R tenv G n us (KExpr.bvar i) stored h))",
            "Under the same schematic stored-type invariant, no semantic constant inference can return a loose de Bruijn variable.",
        )?;
        self.add_recursive_def(
            r"def semantic_constant_imax_stored_closed (sig : KConstSig)
 (found : Eq (OptionType KConstSig) (acceptance_constant_imax_tenv Name.anonymous) (OptionType.some KConstSig sig)) :
 is_closed_at (kconst_type sig) Nat.zero :=
 Eq.substType KConstSig (fun (s : KConstSig) => is_closed_at (kconst_type s) Nat.zero)
 acceptance_constant_imax_sig sig
 (option_some_inj KConstSig acceptance_constant_imax_sig sig found)
 (is_closed_at.sort (Level.imax (Level.param Name.anonymous) Level.zero) Nat.zero)",
            "The existing polymorphic imax fixture actually discharges the stored schematic type closedness premise by computed record lookup and exact projection.",
        )?;
        self.add_recursive_def(
            r"def semantic_constant_imax_result_closed (R : RedEnv) (G : ListType KExpr) (u : Level) :
 is_closed_at (KExpr.sort Level.zero) Nat.zero :=
 kernel_infers_in_constant_result_closed R acceptance_constant_imax_tenv G Name.anonymous
 (ListType.cons Level u (ListType.nil Level)) (KExpr.sort Level.zero)
 semantic_constant_imax_stored_closed (kernel_infers_in_constant_imax_zero R G u)",
            "Concrete caller connects actual semantic constant inference, its stored signature invariant and the derived output closedness theorem, with all premises discharged.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn semantic_closedness_and_actual_constant_results_are_kernel_checked() {
        let spec = crate::test_utils::build_spec_with_stack();
        for name in [
            "kexprUniverseEq_preserves_closed_at",
            "kernel_infers_in_constant_result_closed",
            "kernel_infers_in_constant_loose_result_refused",
            "semantic_constant_imax_stored_closed",
            "semantic_constant_imax_result_closed",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered closedness proof");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }
}
