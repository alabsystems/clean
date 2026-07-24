// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment E (#2859 computational-iota/delta track): the `RecEnvClosed`
//! faithful-interface predicate.
//!
//! E-core (`iota_subst_commutes`) commutes `instantiate_at` past `iota_reduct`.
//! The reduct is `apply_spine extras (apply_spine fields (apply_spine prefix
//! rhs))`, where `rhs = recrule_rhs rule` comes from the (unchanged) env, not
//! from `e`. So `iota_reduct (instantiate_at e v d)` rebuilds with the BARE env
//! `rhs`, while `instantiate_at (iota_reduct e) v d` yields `instantiate_at rhs
//! v d`. They agree only if `rhs` is CLOSED (`instantiate_at rhs v d = rhs`). The
//! kernel's recursor rules produce closed rhs (closed lambda templates), so this
//! is a faithful condition, captured by `RecEnvClosed env` — a real inductive
//! (proper recursor, NOT an axiom), mirroring `RecEnvWellformed`
//! (`iota_step_bridge.rs`). Its witness for the kernel env is discharged at the
//! end of the track by modeling `build_recursor_rule_rhs`.
//!
//! Designed + drafted by the adversarially-verified design workflow (GO, highest
//! certainty). See `designs/2026-06-14-computational-iota-delta-track.md`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// The closure fact carried by `RecEnvClosed env`: every rule reachable via
/// `recrule_for` has a `recrule_rhs` invariant under `instantiate_at`.
const CLOSED_FACT: &str = concat!(
    "forall (rname : Name) (cname : Name) (rule : RecRule) (val : KExpr) (depth : Nat), ",
    "Eq (OptionType RecRule) (recrule_for env rname cname) (OptionType.some RecRule rule) -> ",
    "Eq KExpr (instantiate_at (recrule_rhs rule) val depth) (recrule_rhs rule)"
);

/// The lift-closure fact carried by `RecEnvLiftClosed env`: every rule reachable
/// via `recrule_for` has a `recrule_rhs` invariant under `lift_at`. The lift
/// analogue of `CLOSED_FACT`; the kernel's recursor rules produce closed rhs
/// (closed lambda templates), so the rhs is fixed by lift as well as inst.
const LIFT_CLOSED_FACT: &str = concat!(
    "forall (rname : Name) (cname : Name) (rule : RecRule) (cutoff : Nat) (amount : Nat), ",
    "Eq (OptionType RecRule) (recrule_for env rname cname) (OptionType.some RecRule rule) -> ",
    "Eq KExpr (lift_at (recrule_rhs rule) cutoff amount) (recrule_rhs rule)"
);

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
    "Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> ",
    "Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> ",
    "Eq (OptionType KExpr) (iota_reduct env major) (OptionType.none KExpr)"
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
    "Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> ",
    "Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> ",
    "Eq (OptionType RecMeta) (recmeta_for env cname) (OptionType.none RecMeta)"
);

impl Specification {
    pub(super) fn add_rec_env_closed(&mut self) -> Result<(), SpecError> {
        // RecEnvClosed env: every looked-up rule's rhs is closed (instantiate_at-
        // invariant). Real inductive, mirror of RecEnvWellformed.
        self.add_inductive(
            &format!(
                "inductive RecEnvClosed (env : RecEnv) : Type\n| mk : ({CLOSED_FACT}) → RecEnvClosed env"
            ),
            "Closure interface for a recursor environment: every rule reachable via recrule_for has \
             an instantiate_at-invariant rhs (rhs is closed, so substitution leaves it fixed). A \
             defined hypothesis (NOT an axiom); its witness for the kernel env is discharged at the \
             end of the track. E-core uses it so iota_reduct(inst e) and inst(iota_reduct e) agree on \
             the rule rhs. Part of #2859 (Increment E).",
        )?;

        // recenv_closed_rhs: the projector E-core consumes. Given the env is closed
        // and a rule was looked up, the rule's rhs is fixed by instantiate_at.
        self.add_definition(SpecDefinition {
            name: "recenv_closed_rhs".to_string(),
            type_src: "forall (env : RecEnv) (rname : Name) (cname : Name) (rule : RecRule) \
                 (val : KExpr) (depth : Nat), \
                 RecEnvClosed env -> \
                 Eq (OptionType RecRule) (recrule_for env rname cname) (OptionType.some RecRule rule) -> \
                 Eq KExpr (instantiate_at (recrule_rhs rule) val depth) (recrule_rhs rule)"
                .to_string(),
            value_src: Some(format!(
                "fun (env : RecEnv) (rname : Name) (cname : Name) (rule : RecRule) \
                 (val : KExpr) (depth : Nat) \
                 (w : RecEnvClosed env) \
                 (hlk : Eq (OptionType RecRule) (recrule_for env rname cname) (OptionType.some RecRule rule)) => \
                 RecEnvClosed.rec env \
                 (fun (_ : RecEnvClosed env) => \
                 Eq KExpr (instantiate_at (recrule_rhs rule) val depth) (recrule_rhs rule)) \
                 (fun (hc : {CLOSED_FACT}) => hc rname cname rule val depth hlk) \
                 w"
            )),
            is_axiom: false,
            description: concat!(
                "Projector for RecEnvClosed: in a closed recursor environment, a looked-up rule's rhs ",
                "is invariant under instantiate_at at any (val, depth). Projects the single closure fact ",
                "via RecEnvClosed.rec and applies it to the lookup witness. The interface E-core consumes ",
                "to commute instantiate_at past iota_reduct on the rule-rhs slot. DerivedProved; zero ",
                "axiom_deps. Part of #2859 (Increment E)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvClosed".to_string(),
                "RecEnvClosed.rec".to_string(),
                "recrule_for".to_string(),
                "recrule_rhs".to_string(),
                "instantiate_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // RecEnvLiftClosed env: the lift analogue — every looked-up rule's rhs is
        // closed under lift_at (lift-invariant). Real inductive (NOT an axiom), the
        // lift mirror of RecEnvClosed. The LIFT E-core consumes its projector so
        // iota_reduct(lift e) and lift(iota_reduct e) agree on the rule rhs.
        self.add_inductive(
            &format!(
                "inductive RecEnvLiftClosed (env : RecEnv) : Type\n| mk : ({LIFT_CLOSED_FACT}) → RecEnvLiftClosed env"
            ),
            "Lift-closure interface for a recursor environment: every rule reachable via recrule_for has \
             a lift_at-invariant rhs (rhs is closed, so lifting leaves it fixed). A defined hypothesis \
             (NOT an axiom); the lift analogue of RecEnvClosed. The LIFT E-core uses it so \
             iota_reduct(lift e) and lift(iota_reduct e) agree on the rule rhs. Part of #2859 (LIFT E-core).",
        )?;

        // recenv_lift_closed_rhs: the projector the LIFT E-core consumes. Given the
        // env is lift-closed and a rule was looked up, the rule's rhs is fixed by
        // lift_at. The lift mirror of recenv_closed_rhs.
        self.add_definition(SpecDefinition {
            name: "recenv_lift_closed_rhs".to_string(),
            type_src: "forall (env : RecEnv) (rname : Name) (cname : Name) (rule : RecRule) \
                 (cutoff : Nat) (amount : Nat), \
                 RecEnvLiftClosed env -> \
                 Eq (OptionType RecRule) (recrule_for env rname cname) (OptionType.some RecRule rule) -> \
                 Eq KExpr (lift_at (recrule_rhs rule) cutoff amount) (recrule_rhs rule)"
                .to_string(),
            value_src: Some(format!(
                "fun (env : RecEnv) (rname : Name) (cname : Name) (rule : RecRule) \
                 (cutoff : Nat) (amount : Nat) \
                 (w : RecEnvLiftClosed env) \
                 (hlk : Eq (OptionType RecRule) (recrule_for env rname cname) (OptionType.some RecRule rule)) => \
                 RecEnvLiftClosed.rec env \
                 (fun (_ : RecEnvLiftClosed env) => \
                 Eq KExpr (lift_at (recrule_rhs rule) cutoff amount) (recrule_rhs rule)) \
                 (fun (hc : {LIFT_CLOSED_FACT}) => hc rname cname rule cutoff amount hlk) \
                 w"
            )),
            is_axiom: false,
            description: concat!(
                "Projector for RecEnvLiftClosed: in a lift-closed recursor environment, a looked-up ",
                "rule's rhs is invariant under lift_at at any (cutoff, amount). Projects the single ",
                "lift-closure fact via RecEnvLiftClosed.rec and applies it to the lookup witness. The ",
                "interface the LIFT E-core consumes to commute lift_at past iota_reduct on the rule-rhs ",
                "slot. The lift mirror of recenv_closed_rhs. DerivedProved; zero axiom_deps. Part of #2859 (LIFT E-core)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvLiftClosed".to_string(),
                "RecEnvLiftClosed.rec".to_string(),
                "recrule_for".to_string(),
                "recrule_rhs".to_string(),
                "lift_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

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
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
                 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
                 Eq (OptionType KExpr) (iota_reduct env major) (OptionType.none KExpr)"
                .to_string(),
            value_src: Some(format!(
                "fun (env : RecEnv) (recname : Name) (cname : Name) (rule : RecRule) \
                 (major : KExpr) \
                 (w : RecEnvCtorRecDisjoint env) \
                 (hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (hrule : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) => \
                 RecEnvCtorRecDisjoint.rec env \
                 (fun (_ : RecEnvCtorRecDisjoint env) => \
                 Eq (OptionType KExpr) (iota_reduct env major) (OptionType.none KExpr)) \
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
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
                 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
                 Eq (OptionType RecMeta) (recmeta_for env cname) (OptionType.none RecMeta)"
                .to_string(),
            value_src: Some(format!(
                "fun (env : RecEnv) (recname : Name) (cname : Name) (rule : RecRule) \
                 (major : KExpr) \
                 (w : RecEnvCtorNoRecMeta env) \
                 (hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (hrule : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) => \
                 RecEnvCtorNoRecMeta.rec env \
                 (fun (_ : RecEnvCtorNoRecMeta env) => \
                 Eq (OptionType RecMeta) (recmeta_for env cname) (OptionType.none RecMeta)) \
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
