// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guarded schematic RHS instantiation for the direct recursor migration.
//!
//! The operator takes the existing KConstSig, an actual stored RHS, and the
//! actual head universes. It does not introduce RecEnvU or depend on DefEnv.
//! Its signature type is retained by the caller; only its ordered parameters
//! participate in RHS instantiation. Neither the operator nor its proofs assert
//! typing, a source lambda-branch decision, or production smart-level fidelity.
//!
//! Registration is deliberately split: the operation can precede iota/delta;
//! Boolean CPS views need only early Option helpers; exact-arity proofs need
//! existing signature guard reflection. Fusion/closure
//! and semantic transport follow their existing generic proof dependencies.
//! The helpers are registered; their direct iota caller remains a migration task.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SYNTAX: &[(&str, &str)] = &[
    (
        r"def recursor_rhs_instance (sig : KConstSig) (rhs : KExpr) (us : ListType Level) : KExpr :=
 instLevels (kconst_params sig) rhs us",
        "Raw RHS instance using the actual recursor signature's ordered universe parameters. This total helper does not itself check arity or establish typing.",
    ),
    (
        r"def recursor_rhs_at (sig : KConstSig) (rhs : KExpr) (us : ListType Level) : OptionType KExpr :=
 @Bool.rec (fun (_guard : Bool) => OptionType KExpr)
  (@OptionType.none KExpr) (@OptionType.some KExpr (recursor_rhs_instance sig rhs us))
  (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us))",
        "Actual guarded RHS operation: exact universe arity returns the computed raw instance; a mismatch returns none before a missing-position default can escape. Designed for direct use by the migrated iota operation.",
    ),
];

const EARLY_GUARD_PROOFS: &[(&str, &str)] = &[
    (
        r"def recursor_rhs_at_guard_inv (sig : KConstSig) (rhs : KExpr) (us : ListType Level)
 (result : KExpr)
 (accepted : @Eq (OptionType KExpr) (recursor_rhs_at sig rhs us) (@OptionType.some KExpr result))
 (C : Type)
 (consume : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true -> @Eq KExpr result (recursor_rhs_instance sig rhs us) -> C) : C :=
 @Bool.rec
  (fun (b : Bool) =>
    @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) b ->
    @Eq (OptionType KExpr) (@Bool.rec (fun (_ : Bool) => OptionType KExpr)
      (@OptionType.none KExpr) (@OptionType.some KExpr (recursor_rhs_instance sig rhs us)) b)
      (@OptionType.some KExpr result) -> C)
  (fun (_guard : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.false)
    (bad : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr result)) =>
    @Empty.rec (fun (_ : Empty) => C)
      (@Eq.substType (OptionType KExpr)
        (fun (o : OptionType KExpr) =>
          @OptionType.rec KExpr (fun (_ : OptionType KExpr) => Type)
            Nat (fun (_ : KExpr) => Empty) o)
        (@OptionType.none KExpr) (@OptionType.some KExpr result) bad Nat.zero))
  (fun (guard : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true)
    (found : @Eq (OptionType KExpr) (@OptionType.some KExpr (recursor_rhs_instance sig rhs us))
      (@OptionType.some KExpr result)) =>
    consume guard
      (@Eq.symm KExpr (recursor_rhs_instance sig rhs us) result
        (option_some_inj KExpr (recursor_rhs_instance sig rhs us) result found)))
  (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us))
  (@Eq.refl Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us))) accepted",
        "Type-valued early CPS view exposes the actual true Boolean arity guard and computed RHS equality. Explicit Option discrimination needs no Nat equality reflection or later Option no-confusion theorem.",
    ),
    (
        r"def recursor_rhs_at_guard_inv_prop (sig : KConstSig) (rhs : KExpr) (us : ListType Level)
 (result : KExpr)
 (accepted : @Eq (OptionType KExpr) (recursor_rhs_at sig rhs us) (@OptionType.some KExpr result))
 (C : Prop)
 (consume : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true -> @Eq KExpr result (recursor_rhs_instance sig rhs us) -> C) : C :=
 @Bool.rec
  (fun (b : Bool) =>
    @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) b ->
    @Eq (OptionType KExpr) (@Bool.rec (fun (_ : Bool) => OptionType KExpr)
      (@OptionType.none KExpr) (@OptionType.some KExpr (recursor_rhs_instance sig rhs us)) b)
      (@OptionType.some KExpr result) -> C)
  (fun (_guard : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.false)
    (bad : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr result)) =>
    @Empty.rec (fun (_ : Empty) => C)
      (@Eq.substType (OptionType KExpr)
        (fun (o : OptionType KExpr) =>
          @OptionType.rec KExpr (fun (_ : OptionType KExpr) => Type)
            Nat (fun (_ : KExpr) => Empty) o)
        (@OptionType.none KExpr) (@OptionType.some KExpr result) bad Nat.zero))
  (fun (guard : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true)
    (found : @Eq (OptionType KExpr) (@OptionType.some KExpr (recursor_rhs_instance sig rhs us))
      (@OptionType.some KExpr result)) =>
    consume guard
      (@Eq.symm KExpr (recursor_rhs_instance sig rhs us) result
        (option_some_inj KExpr (recursor_rhs_instance sig rhs us) result found)))
  (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us))
  (@Eq.refl Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us))) accepted",
        "Prop-valued early CPS view exposes the actual true Boolean arity guard and computed RHS equality. Explicit Option discrimination needs no Nat equality reflection or later Option no-confusion theorem.",
    ),
];

const GUARD_PROOFS: &[(&str, &str)] = &[
    (
        r"def recursor_rhs_at_intro (sig : KConstSig) (rhs : KExpr) (us : ListType Level)
 (arity : kconst_arity sig us) :
 @Eq (OptionType KExpr) (recursor_rhs_at sig rhs us)
  (@OptionType.some KExpr (recursor_rhs_instance sig rhs us)) :=
 @Eq.cong Bool (OptionType KExpr)
  (fun (b : Bool) => @Bool.rec (fun (_ : Bool) => OptionType KExpr)
    (@OptionType.none KExpr) (@OptionType.some KExpr (recursor_rhs_instance sig rhs us)) b)
  (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true
  (kconst_arity_check_true sig us arity)",
        "Exact arity makes the actual guard true, reusing proved signature guard reflection rather than assuming a lookup result.",
    ),
    (
        r"def recursor_rhs_at_wrong_arity (sig : KConstSig) (rhs : KExpr) (us : ListType Level)
 (bad : kconst_arity sig us -> Empty) :
 @Eq (OptionType KExpr) (recursor_rhs_at sig rhs us) (@OptionType.none KExpr) :=
 @Eq.cong Bool (OptionType KExpr)
  (fun (b : Bool) => @Bool.rec (fun (_ : Bool) => OptionType KExpr)
    (@OptionType.none KExpr) (@OptionType.some KExpr (recursor_rhs_instance sig rhs us)) b)
  (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.false
  (kconst_arity_check_false sig us bad)",
        "A genuinely refuted arity returns none, by the existing proved false-guard theorem.",
    ),
    (
        r"def recursor_rhs_at_some_inv (sig : KConstSig) (rhs : KExpr) (us : ListType Level)
 (result : KExpr)
 (accepted : @Eq (OptionType KExpr) (recursor_rhs_at sig rhs us) (@OptionType.some KExpr result))
 (C : Type)
 (consume : kconst_arity sig us -> @Eq KExpr result (recursor_rhs_instance sig rhs us) -> C) : C :=
 recursor_rhs_at_guard_inv sig rhs us result accepted C
  (fun (guard : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true)
    (returned : @Eq KExpr result (recursor_rhs_instance sig rhs us)) =>
    consume (nat_eqb_eq (name_list_len (kconst_params sig)) (level_list_len us) guard) returned)",
        "Type-valued CPS inversion of the actual Bool.rec graph. Success exposes genuine exact arity and equality with the computed instance; the false arm is eliminated by OptionType no-confusion.",
    ),
    (
        r"def recursor_rhs_at_some_inv_prop (sig : KConstSig) (rhs : KExpr) (us : ListType Level)
 (result : KExpr)
 (accepted : @Eq (OptionType KExpr) (recursor_rhs_at sig rhs us) (@OptionType.some KExpr result))
 (C : Prop)
 (consume : kconst_arity sig us -> @Eq KExpr result (recursor_rhs_instance sig rhs us) -> C) : C :=
 recursor_rhs_at_guard_inv_prop sig rhs us result accepted C
  (fun (guard : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true)
    (returned : @Eq KExpr result (recursor_rhs_instance sig rhs us)) =>
    consume (nat_eqb_eq (name_list_len (kconst_params sig)) (level_list_len us) guard) returned)",
        "Prop-valued companion with the identical exposed arity/result facts. No Type-versus-Prop elimination is hidden in the interface.",
    ),
];

const STRUCTURAL_PROOFS: &[(&str, &str)] = &[
    (
        r"def recursor_rhs_at_instL_supported (sig : KConstSig) (rhs : KExpr)
 (us : ListType Level) (result : KExpr)
 (accepted : @Eq (OptionType KExpr) (recursor_rhs_at sig rhs us) (@OptionType.some KExpr result))
 (supported : KExprParamSupport (kconst_params sig) rhs) (s : Name -> Level) :
 @Eq (OptionType KExpr) (recursor_rhs_at sig rhs (mapLL (substL s) us))
  (@OptionType.some KExpr (instL s result)) :=
 recursor_rhs_at_some_inv_prop sig rhs us result accepted
  (@Eq (OptionType KExpr) (recursor_rhs_at sig rhs (mapLL (substL s) us))
    (@OptionType.some KExpr (instL s result)))
  (fun (arity : kconst_arity sig us)
    (returned : @Eq KExpr result (recursor_rhs_instance sig rhs us)) =>
    @Eq.trans (OptionType KExpr) (recursor_rhs_at sig rhs (mapLL (substL s) us))
      (@OptionType.some KExpr (recursor_rhs_instance sig rhs (mapLL (substL s) us)))
      (@OptionType.some KExpr (instL s result))
      (recursor_rhs_at_intro sig rhs (mapLL (substL s) us)
        (arity_mapLL (kconst_params sig) us arity (substL s)))
      (@Eq.cong KExpr (OptionType KExpr) (fun (e : KExpr) => @OptionType.some KExpr e)
        (recursor_rhs_instance sig rhs (mapLL (substL s) us)) (instL s result)
        (@Eq.trans KExpr (recursor_rhs_instance sig rhs (mapLL (substL s) us))
          (instL s (recursor_rhs_instance sig rhs us)) (instL s result)
          (@Eq.symm KExpr (instL s (recursor_rhs_instance sig rhs us))
            (recursor_rhs_instance sig rhs (mapLL (substL s) us))
            (instL_instLevels_supported (kconst_params sig) rhs us supported s))
          (@Eq.cong KExpr KExpr (fun (e : KExpr) => instL s e)
            (recursor_rhs_instance sig rhs us) result
            (@Eq.symm KExpr result (recursor_rhs_instance sig rhs us) returned)))))",
        "Derive actual guarded RHS lookup under raw universe substitution from support of the stored RHS. Inversion, preserved arity and the existing support-sensitive fusion theorem supply the new output; no per-output equality is assumed.",
    ),
    (
        r"def recursor_rhs_instance_closed_at (sig : KConstSig) (rhs : KExpr)
 (us : ListType Level) (d : Nat) (closed : is_closed_at rhs d) :
 is_closed_at (recursor_rhs_instance sig rhs us) d :=
 instL_preserves_closed_at (paramSubstN (kconst_params sig) us) rhs d closed",
        "Raw instantiation preserves the actual de Bruijn closedness predicate at every depth. This structural fact needs no arity or universe-parameter support premise.",
    ),
    (
        r"def recursor_rhs_at_preserves_closed_at (sig : KConstSig) (rhs : KExpr)
 (us : ListType Level) (result : KExpr)
 (accepted : @Eq (OptionType KExpr) (recursor_rhs_at sig rhs us) (@OptionType.some KExpr result))
 (d : Nat) (closed : is_closed_at rhs d) : is_closed_at result d :=
 recursor_rhs_at_some_inv sig rhs us result accepted (is_closed_at result d)
  (fun (_arity : kconst_arity sig us)
    (returned : @Eq KExpr result (recursor_rhs_instance sig rhs us)) =>
    @Eq.substType KExpr (fun (e : KExpr) => is_closed_at e d)
      (recursor_rhs_instance sig rhs us) result
      (@Eq.symm KExpr result (recursor_rhs_instance sig rhs us) returned)
      (recursor_rhs_instance_closed_at sig rhs us d closed))",
        "An actually returned guarded RHS is closed whenever its one stored schematic RHS is closed. Uses Type-valued inversion and derived instance closedness, not an instance-closure environment field.",
    ),
];

const SEMANTIC_PROOFS: &[(&str, &str)] = &[
    (
        r"def recursor_rhs_at_semantic_values (sig : KConstSig) (rhs : KExpr)
 (us : ListType Level) (vs : ListType Level) (result : KExpr)
 (accepted : @Eq (OptionType KExpr) (recursor_rhs_at sig rhs us) (@OptionType.some KExpr result))
 (related : LevelListEqSem us vs) (C : Type)
 (consume : forall (result2 : KExpr),
   @Eq (OptionType KExpr) (recursor_rhs_at sig rhs vs) (@OptionType.some KExpr result2) ->
   KExprUniverseEq result result2 -> C) : C :=
 recursor_rhs_at_some_inv sig rhs us result accepted C
  (fun (arity : kconst_arity sig us)
    (returned : @Eq KExpr result (recursor_rhs_instance sig rhs us)) =>
    consume (recursor_rhs_instance sig rhs vs)
      (recursor_rhs_at_intro sig rhs vs
        (@Eq.trans Nat (name_list_len (kconst_params sig)) (level_list_len us) (level_list_len vs)
          arity (levelListEqSem_length us vs related)))
      (@Eq.substType KExpr
        (fun (e : KExpr) => KExprUniverseEq e (recursor_rhs_instance sig rhs vs))
        (recursor_rhs_instance sig rhs us) result
        (@Eq.symm KExpr result (recursor_rhs_instance sig rhs us) returned)
        (instLevels_semantic_values (kconst_params sig) rhs us vs related)))",
        "Related actual head-level lists preserve the computed arity guard and produce semantically related RHS instances. Reuses the generic delta instantiation substrate; no RHS support, NoDup, typing, output-step or source smart-substitution premise is assumed.",
    ),
];

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def recursor_rhs_fixture_params : ListType Name := @ListType.cons Name Name.anonymous (@ListType.nil Name)",
        "A model-local singleton parameter list, not an assertion about the actual source Nat.rec parameter name.",
    ),
    (
        r"def recursor_rhs_fixture_sig : KConstSig := KConstSig.mk recursor_rhs_fixture_params
 (KExpr.pi (KExpr.sort (Level.param Name.anonymous)) (KExpr.sort (Level.param Name.anonymous)))",
        "Schematic model-local signature; its type is data, not a typing theorem or reflected source recursor record.",
    ),
    (
        r"def recursor_rhs_fixture_body : KExpr :=
 KExpr.lam (KExpr.sort (Level.param Name.anonymous)) (KExpr.bvar Nat.zero)",
        "A genuinely schematic lambda RHS whose domain universe must change at a nonzero instance.",
    ),
    (
        r"def recursor_rhs_fixture_output (u : Level) : KExpr := KExpr.lam (KExpr.sort u) (KExpr.bvar Nat.zero)",
        "The explicit raw instantiated lambda, retaining its bound variable.",
    ),
    (
        r"def recursor_rhs_fixture_supported : KExprParamSupport recursor_rhs_fixture_params recursor_rhs_fixture_body :=
 @KExprParamSupport.lam recursor_rhs_fixture_params (KExpr.sort (Level.param Name.anonymous)) (KExpr.bvar Nat.zero)
  (@KExprParamSupport.sort recursor_rhs_fixture_params (Level.param Name.anonymous)
    (@LevelParamSupport.param recursor_rhs_fixture_params Name.anonymous Nat.zero
      (@Eq.refl (OptionType Nat) (@OptionType.some Nat Nat.zero))))
  (@KExprParamSupport.bvar recursor_rhs_fixture_params Nat.zero)",
        "Stored RHS support constructed from actual singleton nameIdx membership, not assumed from lookup success.",
    ),
    (
        r"def recursor_rhs_fixture_closed : is_closed_at recursor_rhs_fixture_body Nat.zero :=
 is_closed_at.lam (KExpr.sort (Level.param Name.anonymous)) (KExpr.bvar Nat.zero) Nat.zero
  (is_closed_at.sort (Level.param Name.anonymous) Nat.zero)
  (is_closed_at.bvar Nat.zero (Nat.succ Nat.zero) (Lt.zero_lt_succ Nat.zero))",
        "One schematic de Bruijn closure witness with an actual bound variable.",
    ),
    (
        r"def recursor_rhs_fixture_step (u : Level) :
 @Eq (OptionType KExpr)
  (recursor_rhs_at recursor_rhs_fixture_sig recursor_rhs_fixture_body (@ListType.cons Level u (@ListType.nil Level)))
  (@OptionType.some KExpr (recursor_rhs_fixture_output u)) :=
 recursor_rhs_at_intro recursor_rhs_fixture_sig recursor_rhs_fixture_body
  (@ListType.cons Level u (@ListType.nil Level)) (@Eq.refl Nat (Nat.succ Nat.zero))",
        "Actual guarded computation at an arbitrary supplied universe, using the generic exact-arity introduction theorem.",
    ),
    (
        r"def recursor_rhs_nonzero :
 @Eq (OptionType KExpr)
  (recursor_rhs_at recursor_rhs_fixture_sig recursor_rhs_fixture_body
    (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level)))
  (@OptionType.some KExpr (recursor_rhs_fixture_output (Level.succ Level.zero))) :=
 recursor_rhs_fixture_step (Level.succ Level.zero)",
        "Nonzero caller: the stored lambda's schematic universe really becomes successor zero, not zero or the unchanged parameter.",
    ),
    (
        r"def recursor_rhs_missing : @Eq (OptionType KExpr)
 (recursor_rhs_at recursor_rhs_fixture_sig recursor_rhs_fixture_body (@ListType.nil Level))
 (@OptionType.none KExpr) := @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
        "The actual guard refuses a missing argument despite raw instLevels having a missing-position default.",
    ),
    (
        r"def recursor_rhs_extra : @Eq (OptionType KExpr)
 (recursor_rhs_at recursor_rhs_fixture_sig recursor_rhs_fixture_body
  (@ListType.cons Level Level.zero (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))))
 (@OptionType.none KExpr) := @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
        "The same actual guard refuses an extra argument; arity is exact, not a lower bound.",
    ),
    (
        r"def recursor_rhs_prop_inversion :
 kconst_arity recursor_rhs_fixture_sig (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level)) :=
 recursor_rhs_at_some_inv_prop recursor_rhs_fixture_sig recursor_rhs_fixture_body
  (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))
  (recursor_rhs_fixture_output (Level.succ Level.zero)) recursor_rhs_nonzero
  (kconst_arity recursor_rhs_fixture_sig (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level)))
  (fun (arity : kconst_arity recursor_rhs_fixture_sig (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level)))
    (_returned : @Eq KExpr (recursor_rhs_fixture_output (Level.succ Level.zero))
      (recursor_rhs_instance recursor_rhs_fixture_sig recursor_rhs_fixture_body
        (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level)))) => arity)",
        "Concrete Prop-valued inversion caller consumes the actual successful guarded result.",
    ),
    (
        r"def recursor_rhs_closed_nonzero : is_closed_at (recursor_rhs_fixture_output (Level.succ Level.zero)) Nat.zero :=
 recursor_rhs_at_preserves_closed_at recursor_rhs_fixture_sig recursor_rhs_fixture_body
  (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))
  (recursor_rhs_fixture_output (Level.succ Level.zero)) recursor_rhs_nonzero Nat.zero recursor_rhs_fixture_closed",
        "Concrete Type-valued inversion/closedness caller derives the accepted nonzero instance's closure from the one schematic closure proof.",
    ),
    (
        r"def recursor_rhs_fusion_nonzero : @Eq (OptionType KExpr)
 (recursor_rhs_at recursor_rhs_fixture_sig recursor_rhs_fixture_body
  (mapLL (substL (fun (_n : Name) => Level.succ Level.zero))
    (@ListType.cons Level (Level.param Name.anonymous) (@ListType.nil Level))))
 (@OptionType.some KExpr (recursor_rhs_fixture_output (Level.succ Level.zero))) :=
 recursor_rhs_at_instL_supported recursor_rhs_fixture_sig recursor_rhs_fixture_body
  (@ListType.cons Level (Level.param Name.anonymous) (@ListType.nil Level))
  (recursor_rhs_fixture_output (Level.param Name.anonymous)) (recursor_rhs_fixture_step (Level.param Name.anonymous))
  recursor_rhs_fixture_supported (fun (_n : Name) => Level.succ Level.zero)",
        "The generic fusion proof drives a real nonidentity substitution of a successful schematic RHS lookup.",
    ),
    (
        r"def recursor_rhs_semantic_nonzero : KExprUniverseEq
 (recursor_rhs_fixture_output (Level.imax (Level.succ Level.zero) (Level.succ Level.zero)))
 (recursor_rhs_fixture_output (Level.succ Level.zero)) :=
 recursor_rhs_at_semantic_values recursor_rhs_fixture_sig recursor_rhs_fixture_body
  (@ListType.cons Level (Level.imax (Level.succ Level.zero) (Level.succ Level.zero)) (@ListType.nil Level))
  (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))
  (recursor_rhs_fixture_output (Level.imax (Level.succ Level.zero) (Level.succ Level.zero)))
  (recursor_rhs_fixture_step (Level.imax (Level.succ Level.zero) (Level.succ Level.zero)))
  (LevelListEqSem.cons (Level.imax (Level.succ Level.zero) (Level.succ Level.zero)) (Level.succ Level.zero)
    (@ListType.nil Level) (@ListType.nil Level)
    (fun (_rho : Name -> Nat) => @Eq.refl Nat (Nat.succ Nat.zero)) LevelListEqSem.nil)
  (KExprUniverseEq
    (recursor_rhs_fixture_output (Level.imax (Level.succ Level.zero) (Level.succ Level.zero)))
    (recursor_rhs_fixture_output (Level.succ Level.zero)))
  (fun (result : KExpr)
    (found : @Eq (OptionType KExpr)
      (recursor_rhs_at recursor_rhs_fixture_sig recursor_rhs_fixture_body
        (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level)))
      (@OptionType.some KExpr result))
    (related : KExprUniverseEq
      (recursor_rhs_fixture_output (Level.imax (Level.succ Level.zero) (Level.succ Level.zero))) result) =>
    @Eq.substType KExpr (fun (e : KExpr) => KExprUniverseEq
      (recursor_rhs_fixture_output (Level.imax (Level.succ Level.zero) (Level.succ Level.zero))) e)
      result (recursor_rhs_fixture_output (Level.succ Level.zero))
      (@Eq.symm KExpr (recursor_rhs_fixture_output (Level.succ Level.zero)) result
        (option_some_inj KExpr (recursor_rhs_fixture_output (Level.succ Level.zero)) result found)) related)",
        "Actual guarded semantic transport between nonzero but syntactically different head levels; the new result and its relation are derived, not supplied.",
    ),
    (
        r"def recursor_rhs_unsupported_fusion_fails :
 @Eq (OptionType KExpr)
  (recursor_rhs_at (KConstSig.mk (@ListType.nil Name) (KExpr.sort Level.zero))
    (KExpr.sort (Level.param Name.anonymous)) (@ListType.nil Level))
  (@OptionType.some KExpr (instL (fun (_n : Name) => Level.zero) (KExpr.sort (Level.param Name.anonymous)))) -> Empty :=
 fun (bad : @Eq (OptionType KExpr)
  (recursor_rhs_at (KConstSig.mk (@ListType.nil Name) (KExpr.sort Level.zero))
    (KExpr.sort (Level.param Name.anonymous)) (@ListType.nil Level))
  (@OptionType.some KExpr (instL (fun (_n : Name) => Level.zero) (KExpr.sort (Level.param Name.anonymous))))) =>
 unsupported_fusion_fails
  (@Eq.symm Level (Level.param Name.anonymous) Level.zero
    (kexpr_sort_inj (Level.param Name.anonymous) Level.zero
      (option_some_inj KExpr (KExpr.sort (Level.param Name.anonymous)) (KExpr.sort Level.zero) bad)))",
        "Exact arity and de Bruijn-closedness do not establish parameter support: this unsupported RHS makes the proposed unguarded fusion equation contradictory.",
    ),
];

fn register(spec: &mut Specification, declarations: &[(&str, &str)]) -> Result<(), SpecError> {
    for (source, description) in declarations {
        spec.add_recursive_def(source, description)?;
    }
    Ok(())
}

impl Specification {
    /// KConstSig/projectors, raw instantiation, OptionType and nat_eqb only.
    pub(super) fn add_recursor_rhs_instantiation_syntax(&mut self) -> Result<(), SpecError> {
        register(self, SYNTAX)
    }

    /// Syntax plus early option_some_inj and Eq/Option elimination; no Nat reflection.
    pub(super) fn add_recursor_rhs_instantiation_guard_views(&mut self) -> Result<(), SpecError> {
        register(self, EARLY_GUARD_PROOFS)
    }

    /// Early Boolean views plus existing signature guard reflection and nat_eqb_eq.
    pub(super) fn add_recursor_rhs_instantiation_guards(&mut self) -> Result<(), SpecError> {
        register(self, GUARD_PROOFS)
    }

    /// Guard proofs plus arity_mapLL, supported fusion and instL closedness.
    pub(super) fn add_recursor_rhs_instantiation_structural(&mut self) -> Result<(), SpecError> {
        register(self, STRUCTURAL_PROOFS)
    }

    /// Semantic level-list length and instLevels_semantic_values.
    pub(super) fn add_recursor_rhs_instantiation_semantic(&mut self) -> Result<(), SpecError> {
        register(self, SEMANTIC_PROOFS)
    }

    /// Late controls include the existing unsupported-fusion counterexample.
    pub(super) fn add_recursor_rhs_instantiation_controls(&mut self) -> Result<(), SpecError> {
        register(self, CONTROLS)
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn guarded_recursor_rhs_proofs_have_empty_actual_axiom_closures() {
        let spec = build_spec_with_stack();
        for name in [
            "recursor_rhs_at_guard_inv",
            "recursor_rhs_at_guard_inv_prop",
            "recursor_rhs_at_intro",
            "recursor_rhs_at_wrong_arity",
            "recursor_rhs_at_some_inv",
            "recursor_rhs_at_some_inv_prop",
            "recursor_rhs_at_instL_supported",
            "recursor_rhs_instance_closed_at",
            "recursor_rhs_at_preserves_closed_at",
            "recursor_rhs_at_semantic_values",
            "recursor_rhs_fixture_supported",
            "recursor_rhs_fixture_closed",
            "recursor_rhs_fixture_step",
            "recursor_rhs_nonzero",
            "recursor_rhs_missing",
            "recursor_rhs_extra",
            "recursor_rhs_prop_inversion",
            "recursor_rhs_closed_nonzero",
            "recursor_rhs_fusion_nonzero",
            "recursor_rhs_semantic_nonzero",
            "recursor_rhs_unsupported_fusion_fails",
        ] {
            let definition = spec.definitions().get(name).expect("registered RHS proof");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }

    #[test]
    fn guarded_recursor_rhs_refuses_wrong_arity_and_erased_nonzero_result() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in [
                "def recursor_rhs_forged_missing : @Eq (OptionType KExpr) (recursor_rhs_at recursor_rhs_fixture_sig recursor_rhs_fixture_body (@ListType.nil Level)) (@OptionType.some KExpr (recursor_rhs_fixture_output Level.zero)) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (recursor_rhs_fixture_output Level.zero))",
                "def recursor_rhs_forged_extra : @Eq (OptionType KExpr) (recursor_rhs_at recursor_rhs_fixture_sig recursor_rhs_fixture_body (@ListType.cons Level Level.zero (@ListType.cons Level Level.zero (@ListType.nil Level)))) (@OptionType.some KExpr (recursor_rhs_fixture_output Level.zero)) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (recursor_rhs_fixture_output Level.zero))",
                "def recursor_rhs_forged_erasure : @Eq (OptionType KExpr) (recursor_rhs_at recursor_rhs_fixture_sig recursor_rhs_fixture_body (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))) (@OptionType.some KExpr (recursor_rhs_fixture_output Level.zero)) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (recursor_rhs_fixture_output Level.zero))",
            ] {
                assert!(spec.add_recursive_def(source, "Planted RHS forgery must be rejected").is_err());
            }
        });
    }
}
