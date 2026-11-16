// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment B (#2859 computational-iota/delta track): the spec-level recursor
//! environment data model.
//!
//! A computational `iota_step` (Increment C) replaces the abstract `iota_reduces`
//! axiom family with a directed, deterministic reduct, retiring the false
//! `church_rosser_whnf`. To recognize and reduce an iota redex — a recursor-`const`
//! applied to a constructor-headed major premise — it needs a model of the
//! recursor rules. This module adds, purely additively (mirroring the existing
//! `CtorDecl`/`CtorDecls`/`KEnv` model at `env_extensions.rs:35-54`):
//!
//! - `OptionType α` — partiality carrier for the reduct (`none` = non-redex).
//! - `option_some_inj` — `some x = some y -> x = y` (the determinism ingredient;
//!   mirrors `pi_inj_fst`).
//! - `RecRule` / `RecRules` — a per-constructor reduction rule (constructor name,
//!   `num_fields`, opaque `rhs`) and a list thereof. Name-keyed (NOT index-keyed:
//!   the spec has no ctor-name->index map; the kernel's `env.get_constructor` has
//!   no spec equivalent — see the adversarial design review).
//! - `RecMeta` — the recursor argument-order counts (params/motives/minors/indices
//!   + a `major_after_minors` flag) and its stored `KConstSig`. The signature
//!   records ordered universe parameters and schematic type, not their validity.
//!   The active iota operation still models only the old MajorAfterMinors path;
//!   use of the signature for its universe guard/instantiation is the next stage.
//! - `RecEnv` — a name-keyed association of recursors to their `RecMeta` + rules.
//!
//! `rhs` is OPAQUE data: confluence is generic over any deterministic rule set;
//! faithfulness to the kernel's actual recursor rules is a separate
//! env-wellformedness obligation, NOT a confluence axiom. So this adds the
//! determinism capability the abstract `iota_reduces.mk` lacks; it does not yet
//! remove the axiom. See `designs/2026-06-14-computational-iota-delta-track.md`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_rec_env(&mut self) -> Result<(), SpecError> {
        // ---------------------------------------------------------------
        // OptionType: partiality carrier (mirrors ListType, expr_model.rs:31-36)
        // ---------------------------------------------------------------
        self.add_inductive(
            r"inductive OptionType (α : Type) : Type
| none : OptionType α
| some : α → OptionType α",
            "Optional value: OptionType α is none or some a. Models the partiality of an \
             iota_step reduct (none = non-redex). Part of #2859 (Increment B).",
        )?;

        // option_some_inj: some x = some y -> x = y. The determinism ingredient
        // (iota_step_deterministic reduces to this). Mirrors pi_inj_fst
        // (expr_model_discrimination_pi.rs:225-254): an OptionType.rec projector
        // extracting the payload on `some` (dummy on `none`), transported through
        // Eq.cong. The `some`-arm iota-reduces on a literal `some`, so Eq.cong
        // yields Eq α x y. Zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "option_some_inj".to_string(),
            type_src: concat!(
                "forall (α : Type) (x : α) (y : α), ",
                "@Eq (OptionType α) (@OptionType.some α x) (@OptionType.some α y) -> @Eq α x y"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (α : Type) (x : α) (y : α) ",
                    "(h : @Eq (OptionType α) (@OptionType.some α x) (@OptionType.some α y)) => ",
                    "@Eq.cong (OptionType α) α ",
                    "(fun (o : OptionType α) => @OptionType.rec α (fun (_ : OptionType α) => α) ",
                    "x (fun (a : α) => a) o) ",
                    "(@OptionType.some α x) (@OptionType.some α y) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "OptionType.some injectivity: some x = some y -> x = y. The determinism ",
                "ingredient for iota_step. DerivedProved via an OptionType.rec payload projector ",
                "+ Eq.cong (mirrors pi_inj_fst). Zero axiom_deps. Part of #2859 (Increment B)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "OptionType.rec".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ---------------------------------------------------------------
        // RecRule / RecRules: per-constructor reduction rule + list (name-keyed).
        // RecRule.mk carries (constructor_name, num_fields, rhs). rhs is opaque
        // data (kernel RecursorRule.rhs is a pre-built lambda; faithfulness is a
        // separate obligation). Mirrors CtorDecl/CtorDecls (env_extensions.rs:35-46).
        // ---------------------------------------------------------------
        self.add_inductive(
            r"inductive RecRule : Type
| mk : Name → Nat → KExpr → RecRule",
            "Recursor reduction rule for one constructor: (constructor_name, num_fields, rhs). \
             rhs is the opaque pre-built reduct lambda. Part of #2859 (Increment B).",
        )?;

        self.add_inductive(
            r"inductive RecRules : Type
| nil : RecRules
| cons : RecRule → RecRules → RecRules",
            "List of per-constructor recursor rules (one per constructor of the inductive). \
             Part of #2859 (Increment B).",
        )?;

        // ---------------------------------------------------------------
        // RecMeta: argument-order counts and the recursor's stored signature.
        // Appending data preserves the existing projections and old iota
        // behavior. It does not yet establish universe-sensitive reduction,
        // signature validity, RHS typing, or the deferred source branches.
        // ---------------------------------------------------------------
        self.add_inductive(
            r"inductive RecMeta : Type
| mk : Nat → Nat → Nat → Nat → Bool → KConstSig → Nat → RecMeta",
            "Recursor argument-order metadata: (num_params, num_motives, num_minors, \
             num_indices, major_after_minors, stored signature, K flag). The ordered \
             universe parameters and schematic type are data, not a typing/admission \
             proof. The K flag is the kernel's `rec_val.is_k` (1 = K-like, 0 = not), \
             stored as a Nat: a Bool field adds nine `Bool` occurrences to the reflected \
             foundation core and ties `Bool` with `OptionType` in the interning order, \
             renumbering tags hand-written spec code cites.",
        )?;

        // ---------------------------------------------------------------
        // RecEnv: name-keyed association recursor-name -> (RecMeta, RecRules).
        // Mirrors KEnv (empty | addInductive ...) at env_extensions.rs:48-53.
        // ---------------------------------------------------------------
        self.add_inductive(
            r"inductive RecEnv : Type
| empty : RecEnv
| addRec : RecEnv → Name → RecMeta → RecRules → RecEnv",
            "Recursor environment: empty, or a recursor (by Name) with its RecMeta and RecRules \
             added to a tail environment. Name-keyed lookup. Part of #2859 (Increment B).",
        )?;

        // ===============================================================
        // Increment B.2a — decidable equality + field projectors.
        // All via explicit recursors (non-self-recursive), the proven
        // `instantiate_bvar_geq` pattern (expr_model.rs:83). No nested match,
        // no self-recursion, no equation form.
        // ===============================================================

        // nat_is_zero / nat_eqb: Nat boolean equality WITHOUT nested match —
        // a == b iff (a - b) + (b - a) == 0 under truncated subtraction.
        self.add_recursive_def(
            r"def nat_is_zero (n : Nat) : Bool := @Nat.rec (fun (_ : Nat) => Bool) Bool.true (fun (k : Nat) (_ : Bool) => Bool.false) n",
            "nat_is_zero n = true iff n = 0 (single Nat.rec). Part of #2859 (Increment B).",
        )?;
        self.add_recursive_def(
            r"def nat_eqb (a : Nat) (b : Nat) : Bool := nat_is_zero (Nat.add (Nat.sub a b) (Nat.sub b a))",
            "Boolean Nat equality via truncated symmetric difference being zero. Part of #2859 (Increment B).",
        )?;

        // name_eqb: Name boolean equality. Recursion via Name.rec's IH (motive
        // `Name -> Bool`), inner dispatch via a second Name.rec — both explicit
        // recursor applications (NOT nested match, NOT self-recursion).
        self.add_recursive_def(
            r"def name_eqb (m : Name) (n : Name) : Bool := @Name.rec (fun (_ : Name) => Name -> Bool) (fun (n2 : Name) => @Name.rec (fun (_ : Name) => Bool) Bool.true (fun (np : Name) (ns : Nat) (_ : Bool) => Bool.false) n2) (fun (mp : Name) (ms : Nat) (ih : Name -> Bool) => fun (n2 : Name) => @Name.rec (fun (_ : Name) => Bool) Bool.false (fun (np : Name) (ns : Nat) (_ : Bool) => Bool.and (ih np) (nat_eqb ms ns)) n2) m n",
            "Boolean Name equality (Name = anonymous | str Name Nat). Recurses on the first name via Name.rec's IH; inner dispatch on the second via Name.rec. Part of #2859 (Increment B).",
        )?;

        // RecRule field projectors (RecRule.mk constructor_name num_fields rhs).
        self.add_recursive_def(
            r"def recrule_ctor_name (r : RecRule) : Name := @RecRule.rec (fun (_ : RecRule) => Name) (fun (c : Name) (nf : Nat) (rhs : KExpr) => c) r",
            "Constructor name of a recursor rule. Part of #2859 (Increment B).",
        )?;
        self.add_recursive_def(
            r"def recrule_num_fields (r : RecRule) : Nat := @RecRule.rec (fun (_ : RecRule) => Nat) (fun (c : Name) (nf : Nat) (rhs : KExpr) => nf) r",
            "Field count of a recursor rule's constructor. Part of #2859 (Increment B).",
        )?;
        self.add_recursive_def(
            r"def recrule_rhs (r : RecRule) : KExpr := @RecRule.rec (fun (_ : RecRule) => KExpr) (fun (c : Name) (nf : Nat) (rhs : KExpr) => rhs) r",
            "The (opaque) reduct lambda of a recursor rule. Part of #2859 (Increment B).",
        )?;

        // RecMeta field projectors (mk counts major_after_minors signature).
        self.add_recursive_def(
            r"def recmeta_num_params (mta : RecMeta) : Nat := @RecMeta.rec (fun (_ : RecMeta) => Nat) (fun (np : Nat) (nm : Nat) (nmin : Nat) (nidx : Nat) (maj : Bool) (_sig : KConstSig) (_kf : Nat) => np) mta",
            "num_params of recursor metadata. Part of #2859 (Increment B).",
        )?;
        self.add_recursive_def(
            r"def recmeta_num_motives (mta : RecMeta) : Nat := @RecMeta.rec (fun (_ : RecMeta) => Nat) (fun (np : Nat) (nm : Nat) (nmin : Nat) (nidx : Nat) (maj : Bool) (_sig : KConstSig) (_kf : Nat) => nm) mta",
            "num_motives of recursor metadata. Part of #2859 (Increment B).",
        )?;
        self.add_recursive_def(
            r"def recmeta_num_minors (mta : RecMeta) : Nat := @RecMeta.rec (fun (_ : RecMeta) => Nat) (fun (np : Nat) (nm : Nat) (nmin : Nat) (nidx : Nat) (maj : Bool) (_sig : KConstSig) (_kf : Nat) => nmin) mta",
            "num_minors of recursor metadata. Part of #2859 (Increment B).",
        )?;
        self.add_recursive_def(
            r"def recmeta_num_indices (mta : RecMeta) : Nat := @RecMeta.rec (fun (_ : RecMeta) => Nat) (fun (np : Nat) (nm : Nat) (nmin : Nat) (nidx : Nat) (maj : Bool) (_sig : KConstSig) (_kf : Nat) => nidx) mta",
            "num_indices of recursor metadata. Part of #2859 (Increment B).",
        )?;
        self.add_recursive_def(
            r"def recmeta_major_after_minors (mta : RecMeta) : Bool := @RecMeta.rec (fun (_ : RecMeta) => Bool) (fun (np : Nat) (nm : Nat) (nmin : Nat) (nidx : Nat) (maj : Bool) (_sig : KConstSig) (_kf : Nat) => maj) mta",
            "major_after_minors flag of recursor metadata. Part of #2859 (Increment B).",
        )?;
        self.add_recursive_def(
            r"def recmeta_signature (mta : RecMeta) : KConstSig := @RecMeta.rec (fun (_ : RecMeta) => KConstSig) (fun (_np : Nat) (_nm : Nat) (_nmin : Nat) (_nidx : Nat) (_maj : Bool) (sig : KConstSig) (_kf : Nat) => sig) mta",
            "The same stored ordered universe parameters and schematic recursor type. Projecting this record does not prove its validity or RHS typing.",
        )?;
        self.add_recursive_def(
            r"def recmeta_signature_mk (np : Nat) (nm : Nat) (nmin : Nat) (nidx : Nat) (maj : Bool) (sig : KConstSig) (kf : Nat) : @Eq KConstSig (recmeta_signature (RecMeta.mk np nm nmin nidx maj sig kf)) sig := @Eq.refl KConstSig sig",
            "The actual metadata projector preserves the complete signature, including ordered parameters and schematic type, for arbitrary counts and layouts.",
        )?;
        self.add_recursive_def(
            r"def recmeta_k_flag (mta : RecMeta) : Nat := @RecMeta.rec (fun (_ : RecMeta) => Nat) (fun (_np : Nat) (_nm : Nat) (_nmin : Nat) (_nidx : Nat) (_maj : Bool) (_sig : KConstSig) (kf : Nat) => kf) mta",
            "The K flag of recursor metadata (the kernel's rec_val.is_k: 1 = K-like). Stored data; what a K flag means is stated by the admission predicate RecKAdmitIn, not by this projector.",
        )?;

        // ===============================================================
        // Increment B.2b — name-keyed lookups. The structural self-call is a
        // plain ARGUMENT to a `pick` helper (the proven `lift_at` app-arm shape,
        // expr_model.rs:68), never a varying leading accumulator and never nested
        // in a recursor minor. Bool dispatch is factored into `opt_pick`/`bool_pick`.
        // ===============================================================

        // opt_pick α b x cont = if b then (some x) else cont.
        self.add_recursive_def(
            r"def opt_pick (α : Type) (b : Bool) (x : α) (cont : OptionType α) : OptionType α := @Bool.rec (fun (_ : Bool) => OptionType α) cont (@OptionType.some α x) b",
            "Branch helper: opt_pick b x cont = some x if b else cont. Part of #2859 (Increment B).",
        )?;

        // bool_pick b cont = if b then true else cont.
        self.add_recursive_def(
            r"def bool_pick (b : Bool) (cont : Bool) : Bool := @Bool.rec (fun (_ : Bool) => Bool) cont Bool.true b",
            "Branch helper: bool_pick b cont = true if b else cont. Part of #2859 (Increment B).",
        )?;

        // recrule_in_rules: find the rule whose constructor_name matches `target`.
        self.add_recursive_def(
            r"def recrule_in_rules (rs : RecRules) (target : Name) : OptionType RecRule := match rs with
| RecRules.nil => @OptionType.none RecRule
| RecRules.cons r rest => opt_pick RecRule (name_eqb (recrule_ctor_name r) target) r (recrule_in_rules rest target)",
            "Look up a recursor rule in a RecRules list by constructor name. Part of #2859 (Increment B).",
        )?;

        // recrules_for: the rule list of recursor `target` in the environment.
        self.add_recursive_def(
            r"def recrules_for (env : RecEnv) (target : Name) : OptionType RecRules := match env with
| RecEnv.empty => @OptionType.none RecRules
| RecEnv.addRec tail rname mta rules => opt_pick RecRules (name_eqb rname target) rules (recrules_for tail target)",
            "Look up a recursor's rule list by recursor name. Part of #2859 (Increment B).",
        )?;

        // recmeta_for: the metadata of recursor `target` in the environment.
        self.add_recursive_def(
            r"def recmeta_for (env : RecEnv) (target : Name) : OptionType RecMeta := match env with
| RecEnv.empty => @OptionType.none RecMeta
| RecEnv.addRec tail rname mta rules => opt_pick RecMeta (name_eqb rname target) mta (recmeta_for tail target)",
            "Look up a recursor's argument-order metadata by recursor name. Part of #2859 (Increment B).",
        )?;

        // is_recursor: whether `target` is a registered recursor.
        self.add_recursive_def(
            r"def is_recursor (env : RecEnv) (target : Name) : Bool := match env with
| RecEnv.empty => Bool.false
| RecEnv.addRec tail rname mta rules => bool_pick (name_eqb rname target) (is_recursor tail target)",
            "Whether `target` is a registered recursor in the environment. Part of #2859 (Increment B).",
        )?;

        // recrule_for: the rule for (recursor name, constructor name). Composes
        // recrules_for then recrule_in_rules via OptionType.rec (non-recursive).
        self.add_recursive_def(
            r"def recrule_for (env : RecEnv) (rname : Name) (cname : Name) : OptionType RecRule := @OptionType.rec RecRules (fun (_ : OptionType RecRules) => OptionType RecRule) (@OptionType.none RecRule) (fun (rules : RecRules) => recrule_in_rules rules cname) (recrules_for env rname)",
            "Look up the recursor rule for (recursor name, constructor name). Part of #2859 (Increment B).",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::Specification;
    use crate::test_utils::run_with_stack;

    #[test]
    fn stored_recursor_signature_preserves_order_type_and_old_projections() {
        run_with_stack(|| {
            let mut spec = Specification::new_red_env_reflection_seed()
                .expect("artifact-independent early metadata seed");
            let params = "(@ListType.cons Name Name.anonymous (@ListType.cons Name (Name.str Name.anonymous Nat.zero) (@ListType.nil Name)))";
            let ty = "(KExpr.pi (KExpr.sort (Level.param (Name.str Name.anonymous Nat.zero))) (KExpr.sort (Level.param Name.anonymous)))";
            let signature = format!("(KConstSig.mk {params} {ty})");
            let metadata = format!("(RecMeta.mk Nat.zero (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero)) Nat.zero Bool.false {signature} Nat.zero)");
            for (name, carrier, expression, expected) in [
                (
                    "metadata_signature_exact",
                    "KConstSig",
                    format!("(recmeta_signature {metadata})"),
                    signature.clone(),
                ),
                (
                    "metadata_parameters_ordered",
                    "ListType Name",
                    format!("(kconst_params (recmeta_signature {metadata}))"),
                    params.to_owned(),
                ),
                (
                    "metadata_type_schematic",
                    "KExpr",
                    format!("(kconst_type (recmeta_signature {metadata}))"),
                    ty.to_owned(),
                ),
                (
                    "metadata_params_unchanged",
                    "Nat",
                    format!("(recmeta_num_params {metadata})"),
                    "Nat.zero".to_owned(),
                ),
                (
                    "metadata_motives_unchanged",
                    "Nat",
                    format!("(recmeta_num_motives {metadata})"),
                    "(Nat.succ Nat.zero)".to_owned(),
                ),
                (
                    "metadata_minors_unchanged",
                    "Nat",
                    format!("(recmeta_num_minors {metadata})"),
                    "(Nat.succ (Nat.succ Nat.zero))".to_owned(),
                ),
                (
                    "metadata_indices_unchanged",
                    "Nat",
                    format!("(recmeta_num_indices {metadata})"),
                    "Nat.zero".to_owned(),
                ),
                (
                    "metadata_layout_unchanged",
                    "Bool",
                    format!("(recmeta_major_after_minors {metadata})"),
                    "Bool.false".to_owned(),
                ),
            ] {
                spec.add_recursive_def(
                    &format!("def {name} : @Eq ({carrier}) {expression} {expected} := @Eq.refl ({carrier}) {expected}"),
                    "Actual metadata carrier computation; no signature validity or reduction claim.",
                ).expect("metadata computation proof must check");
                assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty());
            }
            assert!(crate::spec_axiom_closure::computed_axiom_closure(
                &spec,
                "recmeta_signature_mk"
            )
            .is_empty());
            let reversed = "(@ListType.cons Name (Name.str Name.anonymous Nat.zero) (@ListType.cons Name Name.anonymous (@ListType.nil Name)))";
            for source in [
                format!("def metadata_forged_order : @Eq (ListType Name) (kconst_params (recmeta_signature {metadata})) {reversed} := @Eq.refl (ListType Name) {reversed}"),
                format!("def metadata_forged_erasure : @Eq KExpr (kconst_type (recmeta_signature {metadata})) (KExpr.sort Level.zero) := @Eq.refl KExpr (KExpr.sort Level.zero)"),
            ] {
                assert!(spec.add_recursive_def(&source, "Deliberately false signature control.").is_err());
            }
        });
    }
}
