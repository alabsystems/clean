// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural schematic-RHS closure for recursor environments.
//!
//! Both nominal interfaces carry the same depth-zero no-loose-BVar predicate.
//! Their historical substitution/lift projectors are derived from that predicate.
//! Universe instantiation preserves it, so instance invariance is proved rather
//! than carried as a per-instance assumption. This is a model theorem, not a
//! proof that production admission or reflected RHS construction establishes it.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// The disjointness fact carried by `RecEnvCtorRecDisjoint env`: any term whose
/// head is a constructor `cname` of some recursor rule (`recrule_for env recname
/// cname = some _`) is itself NOT an iota redex (`iota_reduct env major = none`).
/// A constructor carries no recursor metadata, so `iota_reduct` short-circuits at
/// the `recmeta_for` lookup; constructors and recursors occupy disjoint name slots
/// in the kernel env. This is the residual side-condition of the (a) minimal
/// (iota,app) join: the major premise of a minimal iota redex is constructor-headed
/// and hence not a nested recursor redex.
const DISJOINT_FACT: &str = concat!(
    "forall (recname : Name) (cname : Name) (rule : RecRule) (major : KExpr), ",
    "@Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (@OptionType.some Name cname) -> ",
    "@Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.some RecRule rule) -> ",
    "@Eq (OptionType KExpr) (iota_reduct env major) (@OptionType.none KExpr)"
);

/// The SHARPENED disjointness fact carried by `RecEnvCtorNoRecMeta env`: the head
/// name `cname` of a constructor-headed term that is a constructor of some recursor
/// rule (`recrule_for env recname cname = some _`) carries NO recursor metadata
/// (`recmeta_for env cname = none`). Strictly sharper than `DISJOINT_FACT` (which
/// only yields `iota_reduct env major = none`): `iota_reduct major = none` can hold
/// for many reasons (major out of range, no rule, …) and does NOT decompose to
/// `recmeta_for(head major) = none`, so the constructor-headed-major spine
/// congruence (`par_reduces_p_spine_cong_no_recmeta`) — whose iota_p arm fires on the
/// REDUCED premise, not the source, so it CANNOT be guarded by a source
/// `iota_reduct = none` (design §11) — needs this `recmeta_for(cname) = none` form
/// directly. A faithful RecEnv property: constructor names and recursor names occupy
/// disjoint slots, so a constructor `cname` is never a recursor and never resolves to
/// recmeta. The (iota,app) BOTH-FIRE join's major spine congruence consumes its
/// projector.
const NO_RECMETA_FACT: &str = concat!(
    "forall (recname : Name) (cname : Name) (rule : RecRule) (major : KExpr), ",
    "@Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (@OptionType.some Name cname) -> ",
    "@Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.some RecRule rule) -> ",
    "@Eq (OptionType RecMeta) (recmeta_for env cname) (@OptionType.none RecMeta)"
);

impl Specification {
    pub(super) fn add_rec_env_closed(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def RecEnvRhsClosed (env : RecEnv) : Type :=
 forall (rname : Name) (cname : Name) (rule : RecRule),
 @Eq (OptionType RecRule) (recrule_for env rname cname) (@OptionType.some RecRule rule) ->
 is_closed_at (recrule_rhs rule) Nat.zero",
            "Shared schematic structural closedness field. Universe parameters are allowed; loose term bound variables are not.",
        )?;

        self.add_inductive(
            r"inductive RecEnvClosed (env : RecEnv) : Type
| mk : RecEnvRhsClosed env -> RecEnvClosed env",
            "Nominal substitution-closure interface carrying schematic structural closedness.",
        )?;

        self.add_inductive(
            r"inductive RecEnvLiftClosed (env : RecEnv) : Type
| mk : RecEnvRhsClosed env -> RecEnvLiftClosed env",
            "Nominal lift-closure interface carrying the same schematic structural closedness.",
        )?;

        self.add_recursive_def(
            r"def recenv_closed_raw_rhs (env : RecEnv) (rname : Name) (cname : Name) (rule : RecRule)
 (w : RecEnvClosed env)
 (hlk : @Eq (OptionType RecRule) (recrule_for env rname cname) (@OptionType.some RecRule rule)) :
 is_closed_at (recrule_rhs rule) Nat.zero :=
 @RecEnvClosed.rec env
  (fun (_ : RecEnvClosed env) => is_closed_at (recrule_rhs rule) Nat.zero)
  (fun (hc : RecEnvRhsClosed env) => hc rname cname rule hlk) w",
            "Projects actual structural closedness of the looked-up schematic RHS.",
        )?;

        self.add_recursive_def(
            r"def recenv_lift_closed_raw_rhs (env : RecEnv) (rname : Name) (cname : Name) (rule : RecRule)
 (w : RecEnvLiftClosed env)
 (hlk : @Eq (OptionType RecRule) (recrule_for env rname cname) (@OptionType.some RecRule rule)) :
 is_closed_at (recrule_rhs rule) Nat.zero :=
 @RecEnvLiftClosed.rec env
  (fun (_ : RecEnvLiftClosed env) => is_closed_at (recrule_rhs rule) Nat.zero)
  (fun (hc : RecEnvRhsClosed env) => hc rname cname rule hlk) w",
            "Projects actual structural closedness of the looked-up schematic RHS.",
        )?;

        self.add_recursive_def(
            r"def recenv_closed_to_lift_closed (env : RecEnv) (w : RecEnvClosed env) : RecEnvLiftClosed env :=
 @RecEnvLiftClosed.mk env (fun (rname : Name) (cname : Name) (rule : RecRule) =>
  recenv_closed_raw_rhs env rname cname rule w)",
            "Constructive conversion between the nominal interfaces sharing the raw field.",
        )?;

        self.add_recursive_def(
            r"def recenv_lift_closed_to_closed (env : RecEnv) (w : RecEnvLiftClosed env) : RecEnvClosed env :=
 @RecEnvClosed.mk env (fun (rname : Name) (cname : Name) (rule : RecRule) =>
  recenv_lift_closed_raw_rhs env rname cname rule w)",
            "Reverse constructive conversion of the same raw field.",
        )?;

        self.add_recursive_def(
            r"def recenv_closed_rhs (env : RecEnv) (rname : Name) (cname : Name) (rule : RecRule)
 (val : KExpr) (depth : Nat) (w : RecEnvClosed env)
 (hlk : @Eq (OptionType RecRule) (recrule_for env rname cname) (@OptionType.some RecRule rule)) :
 @Eq KExpr (instantiate_at (recrule_rhs rule) val depth) (recrule_rhs rule) :=
 inst_closed_at_id (recrule_rhs rule) Nat.zero
  (recenv_closed_raw_rhs env rname cname rule w hlk) val depth (le_zero_n depth)",
            "Preserves the historical public argument order and conclusion, now derived from structural closedness.",
        )?;

        self.add_recursive_def(
            r"def recenv_closed_rhs_instance (env : RecEnv) (rname : Name) (cname : Name) (rule : RecRule)
 (sig : KConstSig) (us : ListType Level) (val : KExpr) (depth : Nat)
 (w : RecEnvClosed env)
 (hlk : @Eq (OptionType RecRule) (recrule_for env rname cname) (@OptionType.some RecRule rule)) :
 @Eq KExpr (instantiate_at (recursor_rhs_instance sig (recrule_rhs rule) us) val depth)
  (recursor_rhs_instance sig (recrule_rhs rule) us) :=
 inst_closed_at_id (recursor_rhs_instance sig (recrule_rhs rule) us) Nat.zero
  (instL_preserves_closed_at (paramSubstN (kconst_params sig) us)
   (recrule_rhs rule) Nat.zero (recenv_closed_raw_rhs env rname cname rule w hlk))
  val depth (le_zero_n depth)",
            "Derives instance invariance from the raw stored RHS; no per-instance closure, parameter-support, or output-step premise. The caller binds the signature to its actual metadata.",
        )?;

        self.add_recursive_def(
            r"def recenv_closed_rhs_at (env : RecEnv) (rname : Name) (cname : Name) (rule : RecRule)
 (sig : KConstSig) (us : ListType Level) (returned : KExpr) (val : KExpr) (depth : Nat)
 (w : RecEnvClosed env)
 (hlk : @Eq (OptionType RecRule) (recrule_for env rname cname) (@OptionType.some RecRule rule))
 (accepted : @Eq (OptionType KExpr) (recursor_rhs_at sig (recrule_rhs rule) us)
  (@OptionType.some KExpr returned)) :
 @Eq KExpr (instantiate_at returned val depth) returned :=
 recursor_rhs_at_guard_inv_prop sig (recrule_rhs rule) us returned accepted
  (@Eq KExpr (instantiate_at returned val depth) returned)
  (fun (_arity : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true)
    (hresult : @Eq KExpr returned (recursor_rhs_instance sig (recrule_rhs rule) us)) =>
    @Eq.subst KExpr (fun (rhs : KExpr) => @Eq KExpr (instantiate_at rhs val depth) rhs)
     (recursor_rhs_instance sig (recrule_rhs rule) us) returned
     (@Eq.symm KExpr returned (recursor_rhs_instance sig (recrule_rhs rule) us) hresult)
     (recenv_closed_rhs_instance env rname cname rule sig us val depth w hlk))",
            "A successful actual guarded RHS lookup inherits invariance by genuine guard/result inversion; no guard reflection is assumed.",
        )?;

        self.add_recursive_def(
            r"def recenv_lift_closed_rhs (env : RecEnv) (rname : Name) (cname : Name) (rule : RecRule)
 (cutoff : Nat) (amount : Nat) (w : RecEnvLiftClosed env)
 (hlk : @Eq (OptionType RecRule) (recrule_for env rname cname) (@OptionType.some RecRule rule)) :
 @Eq KExpr (lift_at (recrule_rhs rule) cutoff amount) (recrule_rhs rule) :=
 lift_closed_at_id (recrule_rhs rule) Nat.zero
  (recenv_lift_closed_raw_rhs env rname cname rule w hlk) cutoff amount (le_zero_n cutoff)",
            "Preserves the historical public argument order and conclusion, now derived from structural closedness.",
        )?;

        self.add_recursive_def(
            r"def recenv_lift_closed_rhs_instance (env : RecEnv) (rname : Name) (cname : Name) (rule : RecRule)
 (sig : KConstSig) (us : ListType Level) (cutoff : Nat) (amount : Nat)
 (w : RecEnvLiftClosed env)
 (hlk : @Eq (OptionType RecRule) (recrule_for env rname cname) (@OptionType.some RecRule rule)) :
 @Eq KExpr (lift_at (recursor_rhs_instance sig (recrule_rhs rule) us) cutoff amount)
  (recursor_rhs_instance sig (recrule_rhs rule) us) :=
 lift_closed_at_id (recursor_rhs_instance sig (recrule_rhs rule) us) Nat.zero
  (instL_preserves_closed_at (paramSubstN (kconst_params sig) us)
   (recrule_rhs rule) Nat.zero (recenv_lift_closed_raw_rhs env rname cname rule w hlk))
  cutoff amount (le_zero_n cutoff)",
            "Derives instance invariance from the raw stored RHS; no per-instance closure, parameter-support, or output-step premise. The caller binds the signature to its actual metadata.",
        )?;

        self.add_recursive_def(
            r"def recenv_lift_closed_rhs_at (env : RecEnv) (rname : Name) (cname : Name) (rule : RecRule)
 (sig : KConstSig) (us : ListType Level) (returned : KExpr) (cutoff : Nat) (amount : Nat)
 (w : RecEnvLiftClosed env)
 (hlk : @Eq (OptionType RecRule) (recrule_for env rname cname) (@OptionType.some RecRule rule))
 (accepted : @Eq (OptionType KExpr) (recursor_rhs_at sig (recrule_rhs rule) us)
  (@OptionType.some KExpr returned)) :
 @Eq KExpr (lift_at returned cutoff amount) returned :=
 recursor_rhs_at_guard_inv_prop sig (recrule_rhs rule) us returned accepted
  (@Eq KExpr (lift_at returned cutoff amount) returned)
  (fun (_arity : @Eq Bool (nat_eqb (name_list_len (kconst_params sig)) (level_list_len us)) Bool.true)
    (hresult : @Eq KExpr returned (recursor_rhs_instance sig (recrule_rhs rule) us)) =>
    @Eq.subst KExpr (fun (rhs : KExpr) => @Eq KExpr (lift_at rhs cutoff amount) rhs)
     (recursor_rhs_instance sig (recrule_rhs rule) us) returned
     (@Eq.symm KExpr returned (recursor_rhs_instance sig (recrule_rhs rule) us) hresult)
     (recenv_lift_closed_rhs_instance env rname cname rule sig us cutoff amount w hlk))",
            "A successful actual guarded RHS lookup inherits invariance by genuine guard/result inversion; no guard reflection is assumed.",
        )?;

        // RecEnvCtorRecDisjoint env: the constructor/recursor-disjointness interface.
        // Any constructor-headed term that is a constructor of some recursor (its head
        // name cname satisfies recrule_for env recname cname = some _) is NOT itself an
        // iota redex (iota_reduct env major = none) — a constructor carries no recursor
        // metadata, so iota_reduct short-circuits at the recmeta_for lookup. A faithful
        // RecEnv property (constructors and recursors occupy disjoint name slots),
        // captured as a real inductive (proper recursor, NOT an axiom), the mirror of
        // RecEnvClosed. Its witness for the kernel env is discharged at the end of the
        // track (a constructor's head never resolves to recmeta). The (a) minimal join
        // of the (iota,app) diamond consumes its projector to learn the constructor-
        // headed major premise is not a nested recursor redex.
        self.add_inductive(
            &format!(
                "inductive RecEnvCtorRecDisjoint (env : RecEnv) : Type\n| mk : ({DISJOINT_FACT}) → RecEnvCtorRecDisjoint env"
            ),
            "Constructor/recursor-disjointness interface for a recursor environment: any \
             constructor-headed term whose head name is a constructor of some recursor rule \
             (recrule_for env recname cname = some _) is not itself an iota redex \
             (iota_reduct env major = none). A defined hypothesis (NOT an axiom); its witness for \
             the kernel env is discharged at the end of the track. The (a) minimal join of the \
             (iota,app) diamond uses it to learn the constructor-headed major premise of a minimal \
             iota redex is not a nested recursor redex. Part of #2859 (Increment F capstone).",
        )?;

        // recenv_ctor_rec_disjoint_major: the projector the (a) minimal join consumes.
        // Given the env is ctor/rec-disjoint and a term's head is a constructor cname of
        // recursor recname (recrule_for env recname cname = some rule), the term is not
        // an iota redex. Mirror of recenv_closed_rhs.
        self.add_definition(SpecDefinition {
            name: "recenv_ctor_rec_disjoint_major".to_string(),
            type_src: "forall (env : RecEnv) (recname : Name) (cname : Name) (rule : RecRule) \
                 (major : KExpr), \
                 RecEnvCtorRecDisjoint env -> \
                 @Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (@OptionType.some Name cname) -> \
                 @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.some RecRule rule) -> \
                 @Eq (OptionType KExpr) (iota_reduct env major) (@OptionType.none KExpr)"
                .to_string(),
            value_src: Some(format!(
                "fun (env : RecEnv) (recname : Name) (cname : Name) (rule : RecRule) \
                 (major : KExpr) \
                 (w : RecEnvCtorRecDisjoint env) \
                 (hhead : @Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (@OptionType.some Name cname)) \
                 (hrule : @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.some RecRule rule)) => \
                 @RecEnvCtorRecDisjoint.rec env \
                 (fun (_ : RecEnvCtorRecDisjoint env) => \
                 @Eq (OptionType KExpr) (iota_reduct env major) (@OptionType.none KExpr)) \
                 (fun (hc : {DISJOINT_FACT}) => hc recname cname rule major hhead hrule) \
                 w"
            )),
            is_axiom: false,
            description: concat!(
                "Projector for RecEnvCtorRecDisjoint: in a ctor/rec-disjoint recursor environment, a ",
                "term whose head is a constructor cname of recursor recname (recrule_for env recname cname ",
                "= some rule) is not itself an iota redex (iota_reduct env major = none). Projects the single ",
                "disjointness fact via RecEnvCtorRecDisjoint.rec and applies it to the head + rule witnesses. ",
                "The interface the (a) minimal (iota,app) join consumes to discharge its constructor-headed-",
                "major-is-not-a-redex side-condition. Mirror of recenv_closed_rhs. DerivedProved; zero ",
                "axiom_deps. Part of #2859 (Increment F capstone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvCtorRecDisjoint".to_string(),
                "RecEnvCtorRecDisjoint.rec".to_string(),
                "recrule_for".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "iota_reduct".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // RecEnvCtorNoRecMeta env: the SHARPENED constructor/recursor-disjointness
        // interface. The head name cname of a constructor-headed term that is a
        // constructor of some recursor rule (recrule_for env recname cname = some _)
        // carries NO recursor metadata (recmeta_for env cname = none). Strictly sharper
        // than RecEnvCtorRecDisjoint (which only yields iota_reduct env major = none):
        // iota_reduct major = none does NOT decompose to recmeta_for(head major) = none,
        // so the constructor-headed-major spine congruence par_reduces_p_spine_cong_no_recmeta
        // — whose iota_p arm fires on the REDUCED premise (not the source), so it CANNOT
        // be guarded by a source iota_reduct = none (design §11) — requires this
        // recmeta_for(cname) = none form directly. A defined hypothesis (NOT an axiom);
        // its witness for the kernel env is discharged at the end of the track (a
        // constructor name is never a recursor name). The (iota,app) BOTH-FIRE join's
        // major spine congruence uses it.
        self.add_inductive(
            &format!(
                "inductive RecEnvCtorNoRecMeta (env : RecEnv) : Type\n| mk : ({NO_RECMETA_FACT}) → RecEnvCtorNoRecMeta env"
            ),
            "Sharpened constructor/recursor-disjointness interface for a recursor environment: the head \
             name cname of a constructor-headed term that is a constructor of some recursor rule \
             (recrule_for env recname cname = some _) carries NO recursor metadata (recmeta_for env cname \
             = none). Strictly sharper than RecEnvCtorRecDisjoint (iota_reduct env major = none does not \
             decompose to recmeta_for(head) = none). A defined hypothesis (NOT an axiom); its witness for \
             the kernel env is discharged at the end of the track. The (iota,app) both-fire join's major \
             spine congruence (par_reduces_p_spine_cong_no_recmeta) consumes it. Part of #2859 (Increment F++ keystone).",
        )?;

        // recenv_ctor_no_recmeta_cname: the projector the (iota,app) both-fire join's
        // major spine congruence consumes. Given the env is ctor/no-recmeta and a term's
        // head is a constructor cname of recursor recname (recrule_for env recname cname =
        // some rule), the constructor cname carries no recursor metadata. Mirror of
        // recenv_ctor_rec_disjoint_major (sharpened to the recmeta_for = none conclusion).
        self.add_definition(SpecDefinition {
            name: "recenv_ctor_no_recmeta_cname".to_string(),
            type_src: "forall (env : RecEnv) (recname : Name) (cname : Name) (rule : RecRule) \
                 (major : KExpr), \
                 RecEnvCtorNoRecMeta env -> \
                 @Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (@OptionType.some Name cname) -> \
                 @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.some RecRule rule) -> \
                 @Eq (OptionType RecMeta) (recmeta_for env cname) (@OptionType.none RecMeta)"
                .to_string(),
            value_src: Some(format!(
                "fun (env : RecEnv) (recname : Name) (cname : Name) (rule : RecRule) \
                 (major : KExpr) \
                 (w : RecEnvCtorNoRecMeta env) \
                 (hhead : @Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (@OptionType.some Name cname)) \
                 (hrule : @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.some RecRule rule)) => \
                 @RecEnvCtorNoRecMeta.rec env \
                 (fun (_ : RecEnvCtorNoRecMeta env) => \
                 @Eq (OptionType RecMeta) (recmeta_for env cname) (@OptionType.none RecMeta)) \
                 (fun (hc : {NO_RECMETA_FACT}) => hc recname cname rule major hhead hrule) \
                 w"
            )),
            is_axiom: false,
            description: concat!(
                "Projector for RecEnvCtorNoRecMeta: in a ctor/no-recmeta recursor environment, the head ",
                "name cname of a term whose head is a constructor of recursor recname (recrule_for env recname ",
                "cname = some rule) carries no recursor metadata (recmeta_for env cname = none). Projects the ",
                "single sharpened-disjointness fact via RecEnvCtorNoRecMeta.rec and applies it to the head + ",
                "rule witnesses. The interface the (iota,app) both-fire join's major spine congruence ",
                "(par_reduces_p_spine_cong_no_recmeta) consumes. Sharpened mirror of recenv_ctor_rec_disjoint_major. ",
                "DerivedProved; zero axiom_deps. Part of #2859 (Increment F++ keystone)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvCtorNoRecMeta.rec".to_string(),
                "recrule_for".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "recmeta_for".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    const POSITIVE: &[&str] = &[
        r"def recenv_schematic_test_rule : RecRule :=
 RecRule.mk Name.anonymous Nat.zero recursor_rhs_fixture_body",
        r"def recenv_schematic_test_env : RecEnv :=
 RecEnv.addRec RecEnv.empty Name.anonymous
  (RecMeta.mk Nat.zero Nat.zero Nat.zero Nat.zero Bool.true recursor_rhs_fixture_sig Nat.zero)
  (RecRules.cons recenv_schematic_test_rule RecRules.nil)",
        r"def recenv_schematic_test_closed : RecEnvClosed recenv_schematic_test_env :=
 rec_env_closed_of_b2 recenv_schematic_test_env (@Eq.refl Bool Bool.true)",
        r"def recenv_schematic_test_lift_closed : RecEnvLiftClosed recenv_schematic_test_env :=
 recenv_closed_to_lift_closed recenv_schematic_test_env recenv_schematic_test_closed",
        r"def recenv_schematic_test_lookup :
 @Eq (OptionType RecRule) (recrule_for recenv_schematic_test_env Name.anonymous Name.anonymous)
  (@OptionType.some RecRule recenv_schematic_test_rule) :=
 @Eq.refl (OptionType RecRule) (@OptionType.some RecRule recenv_schematic_test_rule)",
        r"def recenv_schematic_test_inst :
 @Eq KExpr
  (instantiate_at (recursor_rhs_fixture_output (Level.succ Level.zero))
    (KExpr.bvar Nat.zero) Nat.zero)
  (recursor_rhs_fixture_output (Level.succ Level.zero)) :=
 recenv_closed_rhs_at recenv_schematic_test_env Name.anonymous Name.anonymous
  recenv_schematic_test_rule recursor_rhs_fixture_sig
  (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))
  (recursor_rhs_fixture_output (Level.succ Level.zero)) (KExpr.bvar Nat.zero) Nat.zero
  recenv_schematic_test_closed recenv_schematic_test_lookup
  (recursor_rhs_fixture_step (Level.succ Level.zero))",
        r"def recenv_schematic_test_lift :
 @Eq KExpr
  (lift_at (recursor_rhs_fixture_output (Level.succ Level.zero)) Nat.zero (Nat.succ Nat.zero))
  (recursor_rhs_fixture_output (Level.succ Level.zero)) :=
 recenv_lift_closed_rhs_at recenv_schematic_test_env Name.anonymous Name.anonymous
  recenv_schematic_test_rule recursor_rhs_fixture_sig
  (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))
  (recursor_rhs_fixture_output (Level.succ Level.zero)) Nat.zero (Nat.succ Nat.zero)
  recenv_schematic_test_lift_closed recenv_schematic_test_lookup
  (recursor_rhs_fixture_step (Level.succ Level.zero))",
    ];

    #[test]
    fn schematic_recenv_closure_derives_actual_nonzero_rhs_invariance() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in POSITIVE {
                spec.add_recursive_def(source, "Actual schematic binder / nonzero RHS regression")
                    .expect("structural checker and guarded result must compose");
            }
            for name in [
                "RecEnvRhsClosed",
                "recenv_closed_raw_rhs",
                "recenv_lift_closed_raw_rhs",
                "recenv_closed_to_lift_closed",
                "recenv_lift_closed_to_closed",
                "recenv_closed_rhs",
                "recenv_lift_closed_rhs",
                "recenv_closed_rhs_instance",
                "recenv_lift_closed_rhs_instance",
                "recenv_closed_rhs_at",
                "recenv_lift_closed_rhs_at",
                "rec_env_closed_of_b",
                "rec_env_lift_closed_of_b",
                "rec_env_closed_of_b2",
                "rec_env_lift_closed_of_b2",
                "faithful_rec_env_closed",
                "faithful_rec_env_lift_closed",
                "kernel_core_red_env_rec_closed_via_checker_b2",
                "kernel_core_red_env_rec_lift_closed_via_checker_b2",
                "recenv_schematic_test_inst",
                "recenv_schematic_test_lift",
            ] {
                let definition = spec
                    .definitions()
                    .get(name)
                    .expect("registered closure result");
                assert!(!definition.is_axiom, "{name}");
                assert!(definition.elaborated_value.is_some(), "{name}");
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name}"
                );
            }
        });
    }

    #[test]
    fn schematic_recenv_closure_rejects_loose_bvars_and_wrong_arity() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in [
                r"def recenv_schematic_forged_closed : is_closed_at (KExpr.bvar Nat.zero) Nat.zero :=
 is_closed_at.bvar Nat.zero Nat.zero (Lt.zero_lt_succ Nat.zero)",
                r"def recenv_schematic_forged_missing :
 @Eq (OptionType KExpr) (recursor_rhs_at recursor_rhs_fixture_sig recursor_rhs_fixture_body (@ListType.nil Level))
  (@OptionType.some KExpr (recursor_rhs_fixture_output Level.zero)) :=
 @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (recursor_rhs_fixture_output Level.zero))",
                r"def recenv_schematic_forged_identity :
 @Eq KExpr (instantiate_at (KExpr.bvar Nat.zero) (KExpr.sort Level.zero) Nat.zero) (KExpr.bvar Nat.zero) :=
 @Eq.refl KExpr (KExpr.bvar Nat.zero)",
            ] {
                assert!(
                    spec.add_recursive_def(source, "Planted missing closure/arity premise")
                        .is_err(),
                    "a structural or guard premise cannot be silently discarded"
                );
            }
        });
    }
}
